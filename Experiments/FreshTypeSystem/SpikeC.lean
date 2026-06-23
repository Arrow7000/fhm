import Experiments.FreshTypeSystem.Core

/-! # SPIKE C: a *kept* recursion scheme referencing an enclosing-scope type var

Question (the make-or-break "C" feature): can the codebase's type-ERASURE safety
architecture support a `letRecAnn` whose scheme references a type variable bound by
an ENCLOSING scope (ScopedTypeVariables on a polymorphic-recursive helper)?

The only erasure-compatible idea on the table was **freeze-and-re-generalise**:
erase the enclosing binder's `∀a`, "freeze" `a` to a fresh free `fvar Z` inside the
kept recursion scheme, and let the now-unannotated enclosing binder *re-generalise*
`Z` to recover the outer function's polymorphism.

This file tests the crux of that idea on the REAL `TypeOfHM.letRecAnn` node:
a kept scheme carrying a free `fvar Z` is **rigid** in `Z`. If it is rigid, the
enclosing binder canNOT re-generalise `Z`, so freeze-and-re-generalise cannot
recover the outer polymorphism — i.e. C is *not* supported by pure type-erasure. -/

namespace SpikeC

/-- `Z → Z`, a (monomorphic, `paramCount = 0`) recursion scheme mentioning the
    free type variable `Z` — the "frozen" form of an enclosing scoped variable. -/
def sigZ (Z : Nat) : PolyTy := ⟨0, .arrow (.fvar Z) (.fvar Z)⟩

/-- `λx. f x`, self-recursive (the binding `f` is `var 1` under the λ). -/
def rhs : Expr := .lambda none (.app (.var 1) (.var 0))

/-- `let rec (f : Z → Z) = λx. f x in f`. -/
def cTerm (Z : Nat) : Expr := .letRecAnn [sigZ Z] [rhs] (.var 0)

/-- POSITIVE — Feature B: with `Z` a *top-level* rigid constant, the term types at
    `Z → Z`, and this is erasure-safe (free `fvar`s never dangle). -/
theorem cTerm_typeable (Z : Nat) :
    TypeOfHM ⟨[], []⟩ (cTerm Z) (.arrow (.fvar Z) (.fvar Z)) := by
  refine TypeOfHM.letRecAnn (schemes := [sigZ Z]) (L := []) rfl ?_ ?_ rfl ?_
  · intro σ hσ; simp only [List.mem_singleton] at hσ; subst hσ
    exact .arrow .fvar .fvar
  · intro Xs hfresh p hp
    obtain rfl : Xs = [] := List.eq_nil_of_length_eq_zero hfresh.length
    have hog : PolyTy.openGroup [sigZ Z] [] = [(Ty.fvar Z).arrow (Ty.fvar Z)] := rfl
    rw [hog] at hp
    simp only [List.zip_cons_cons, List.zip_nil_right, List.mem_singleton] at hp
    subst hp
    refine TypeOfHM.lambda .fvar (fun T h => Option.noConfusion h) rfl ?_
    refine TypeOfHM.app (argTy := .fvar Z) ?_ ?_
    · exact TypeOfHM.var (polyTy := sigZ Z) (tyArgs := []) rfl
        (by intro t ht; cases ht) (.arrow .fvar .fvar)
    · exact TypeOfHM.var (polyTy := PolyTy.mkTrivial (.fvar Z)) (tyArgs := []) rfl
        (by intro t ht; cases ht) .fvar
  · exact TypeOfHM.var (polyTy := sigZ Z) (tyArgs := []) rfl
      (by intro t ht; cases ht) (.arrow .fvar .fvar)

/-- NEGATIVE — the obstruction: the kept scheme `Z → Z` is **rigid** in `Z`. The
    term does NOT type at `X → X` for any `X ≠ Z`, so it is *not* polymorphic in
    `Z`. Hence an enclosing (unannotated) binder cannot generalise `Z`, and
    freeze-and-re-generalise cannot recover the outer function's polymorphism in a
    type-erasure setting. Supporting C therefore needs the type *application*
    structure to survive (type-passing), not be erased. -/
theorem cTerm_rigid (Z X : Nat) (hne : X ≠ Z) :
    ¬ TypeOfHM ⟨[], []⟩ (cTerm Z) (.arrow (.fvar X) (.fvar X)) := by
  intro h
  cases h with
  | letRecAnn hlen hwf hcofin heq hbody =>
    subst heq
    cases hbody with
    | var hlook _htyargs hinst =>
      simp only [List.append_nil, List.getElem?_cons_zero, Option.some.injEq] at hlook
      subst hlook
      simp only [sigZ] at hinst
      cases hinst with
      | arrow hfst hsnd =>
        cases hfst
        exact hne rfl

/-! ## Mutual annotated polymorphic recursion is FULLY supported (Feature A)

Mutual recursion is NOT the hard case. Each member of a mutual group carries its
OWN `∀`-quantified scheme; cross-calls instantiate the *other* member's scheme
freshly. No member references another's bound variable, so every scheme is closed
(own binders only) — exactly the erasure-safe Feature-A case Stage 1 handles. The
"C" obstruction above is orthogonal: it is about a scheme referencing a variable
bound by an ENCLOSING scope (ScopedTypeVariables), not about mutuality. -/

/-- `∀a. a`. -/
def polyA : PolyTy := ⟨1, .bvar 0⟩

/-- `let rec f = g and g = f in f`, both annotated `∀a. a` — the mutual loop, now
    annotated. `f` is `var 0`, `g` is `var 1` inside the group. -/
def mutualTerm : Expr := .letRecAnn [polyA, polyA] [.var 1, .var 0] (.var 0)

theorem mutual_typeable : TypeOfHM ⟨[], []⟩ mutualTerm (.fvar 0) := by
  refine TypeOfHM.letRecAnn (schemes := [polyA, polyA]) (L := []) rfl ?_ ?_ rfl ?_
  · intro σ hσ
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hσ
    rcases hσ with rfl | rfl <;>
      exact (show ContainsBvarsUpTo 1 (Ty.bvar 0) from .bvar (by omega))
  · intro Xs hfresh p hp
    obtain ⟨X0, X1, rfl⟩ : ∃ X0 X1, Xs = [X0, X1] := by
      have hl : Xs.length = 2 := hfresh.length
      rcases Xs with _ | ⟨X0, _ | ⟨X1, _ | _⟩⟩ <;> simp_all
    have hog : PolyTy.openGroup [polyA, polyA] [X0, X1] = [Ty.fvar X0, Ty.fvar X1] := rfl
    rw [hog] at hp
    rw [show ([Expr.var 1, Expr.var 0]).zip [Ty.fvar X0, Ty.fvar X1]
          = [(Expr.var 1, Ty.fvar X0), (Expr.var 0, Ty.fvar X1)] from rfl] at hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl
    · exact TypeOfHM.var (polyTy := polyA) (tyArgs := [Ty.fvar X0]) rfl
        (by intro t ht; simp only [List.mem_singleton] at ht; subst ht; exact .fvar)
        (.bvar rfl)
    · exact TypeOfHM.var (polyTy := polyA) (tyArgs := [Ty.fvar X1]) rfl
        (by intro t ht; simp only [List.mem_singleton] at ht; subst ht; exact .fvar)
        (.bvar rfl)
  · exact TypeOfHM.var (polyTy := polyA) (tyArgs := [Ty.fvar 0]) rfl
      (by intro t ht; simp only [List.mem_singleton] at ht; subst ht; exact .fvar)
      (.bvar rfl)

end SpikeC
