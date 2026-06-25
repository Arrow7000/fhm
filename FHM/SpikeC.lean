import FHM.Core

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
def rhs : Expr := .lambda none (.app (.var 1 []) (.var 0 []))

/-- `let rec (f : Z → Z) = λx. f x in f`. -/
def cTerm (Z : Nat) : Expr := .letRecAnn [sigZ Z] [rhs] (.var 0 [])

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
        (by intro t ht; cases ht) rfl (.arrow .fvar .fvar)
    · exact TypeOfHM.var (polyTy := PolyTy.mkTrivial (.fvar Z)) (tyArgs := []) rfl
        (by intro t ht; cases ht) rfl .fvar
  · exact TypeOfHM.var (polyTy := sigZ Z) (tyArgs := []) rfl
      (by intro t ht; cases ht) rfl (.arrow .fvar .fvar)

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
    | var hlook _htyargs _hlen hinst =>
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

/-- `∀a. a → a` — an *inhabitable* own-`∀` scheme. (Pre-migration this witness
    used the degenerate `∀a. a`; under type-passing that is unusable here, because
    `∀a. a` is uninhabited, so a binding's RHS could only be typed by instantiating
    the sibling at the binding's OWN fresh skolem — a type the fixed term cannot
    name. Switching to the inhabited `∀a. a → a` lets each RHS produce its opened
    type via its `λ`, exactly as `Core.LetRecAnnSmokeTest.polyRecRhs` does.) -/
def selfSig : PolyTy := ⟨1, .arrow (.bvar 0) (.bvar 0)⟩

/-- `f`'s RHS: `λx. let _ = g [Int] 0 in x`. Genuinely mutual (it calls the
    sibling `g`) and polymorphic-recursive (the cross-call instantiates `g`'s OWN
    scheme at the concrete `Int`, independent of `f`'s parameter). Under the group's
    two binders `f = var 0`, `g = var 1`; beneath the `λ` they shift to `1`/`2`. -/
def fRhs : Expr :=
  .lambda none (.letIn none (.app (.var 2 [.prim .int]) (.primLit (.int 0))) (.var 1 []))

/-- `g`'s RHS: `λx. let _ = f [Int] 0 in x`, the symmetric cross-call to `f`. -/
def gRhs : Expr :=
  .lambda none (.letIn none (.app (.var 1 [.prim .int]) (.primLit (.int 0))) (.var 1 []))

/-- `let rec (f : ∀a.a→a) = λx. … g[Int] … and (g : ∀a.a→a) = λx. … f[Int] … in f`,
    the annotated mutual group. `f` is `var 0`, `g` is `var 1` inside the group. -/
def mutualTerm : Expr := .letRecAnn [selfSig, selfSig] [fRhs, gRhs] (.var 0 [.fvar 0])

/-- Mutual annotated polymorphic recursion types at `f`'s principal-ish instance
    `(fvar 0) → (fvar 0)` (Feature A). Each binding is checked at its own fresh
    skolem opening; the cross-calls instantiate the sibling's scheme at `Int`. -/
theorem mutual_typeable :
    TypeOfHM ⟨[], []⟩ mutualTerm ((Ty.fvar 0).arrow (Ty.fvar 0)) := by
  refine TypeOfHM.letRecAnn (schemes := [selfSig, selfSig]) (L := []) rfl ?_ ?_ rfl ?_
  · intro σ hσ
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hσ
    rcases hσ with rfl | rfl <;>
      exact (show ContainsBvarsUpTo 1 ((Ty.bvar 0).arrow (Ty.bvar 0)) from
        .arrow (.bvar (by omega)) (.bvar (by omega)))
  · intro Xs hfresh p hp
    obtain ⟨X0, X1, rfl⟩ : ∃ X0 X1, Xs = [X0, X1] := by
      have hl : Xs.length = 2 := hfresh.length
      rcases Xs with _ | ⟨X0, _ | ⟨X1, _ | _⟩⟩ <;> simp_all
    have hog : PolyTy.openGroup [selfSig, selfSig] [X0, X1]
        = [(Ty.fvar X0).arrow (Ty.fvar X0), (Ty.fvar X1).arrow (Ty.fvar X1)] := rfl
    rw [hog] at hp
    rw [show ([fRhs, gRhs]).zip [(Ty.fvar X0).arrow (Ty.fvar X0), (Ty.fvar X1).arrow (Ty.fvar X1)]
          = [(fRhs, (Ty.fvar X0).arrow (Ty.fvar X0)), (gRhs, (Ty.fvar X1).arrow (Ty.fvar X1))]
          from rfl] at hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl
    · -- `fRhs` types at `(fvar X0) → (fvar X0)`
      refine TypeOfHM.lambda .fvar (fun T h => Option.noConfusion h) rfl ?_
      refine TypeOfHM.letIn (M := PolyTy.mkTrivial (.prim .int)) (L := [])
        .prim (fun σ h => Option.noConfusion h) ?_ rfl ?_
      · intro Ys hfreshY
        obtain rfl : Ys = [] := List.eq_nil_of_length_eq_zero hfreshY.length
        refine TypeOfHM.app ?_ TypeOfHM.primLitInt
        exact TypeOfHM.var (polyTy := selfSig) (tyArgs := [.prim .int]) rfl
          (by intro t ht; simp only [List.mem_singleton] at ht; subst ht; exact .prim) rfl
          (.arrow (.bvar rfl) (.bvar rfl))
      exact TypeOfHM.var (polyTy := PolyTy.mkTrivial (.fvar X0)) (tyArgs := []) rfl
        (by intro t ht; cases ht) rfl .fvar
    · -- `gRhs` types at `(fvar X1) → (fvar X1)`
      refine TypeOfHM.lambda .fvar (fun T h => Option.noConfusion h) rfl ?_
      refine TypeOfHM.letIn (M := PolyTy.mkTrivial (.prim .int)) (L := [])
        .prim (fun σ h => Option.noConfusion h) ?_ rfl ?_
      · intro Ys hfreshY
        obtain rfl : Ys = [] := List.eq_nil_of_length_eq_zero hfreshY.length
        refine TypeOfHM.app ?_ TypeOfHM.primLitInt
        exact TypeOfHM.var (polyTy := selfSig) (tyArgs := [.prim .int]) rfl
          (by intro t ht; simp only [List.mem_singleton] at ht; subst ht; exact .prim) rfl
          (.arrow (.bvar rfl) (.bvar rfl))
      exact TypeOfHM.var (polyTy := PolyTy.mkTrivial (.fvar X1)) (tyArgs := []) rfl
        (by intro t ht; cases ht) rfl .fvar
  · -- body `f [fvar 0]` types at `(fvar 0) → (fvar 0)`
    exact TypeOfHM.var (polyTy := selfSig) (tyArgs := [Ty.fvar 0]) rfl
      (by intro t ht; simp only [List.mem_singleton] at ht; subst ht; exact .fvar) rfl
      (.arrow (.bvar rfl) (.bvar rfl))

end SpikeC
