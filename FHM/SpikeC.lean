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
  · intro p hp Xs hfresh
    simp only [List.zip_cons_cons, List.zip_nil_right, List.mem_singleton] at hp
    subst hp
    obtain rfl : Xs = [] := List.eq_nil_of_length_eq_zero hfresh.length
    show TypeOfHM ⟨[sigZ Z], []⟩ (rhs.openTyVars []) ((Ty.fvar Z).arrow (Ty.fvar Z))
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

/-! ## Mutual OWN-variable annotated polymorphic recursion is supported

Each member of a `[∀a.a→a, ∀a.a→a]` group cross-calls the sibling **at its own
type variable** `a` (stored scheme-relatively as `arrow (bvar 0) (bvar 0)`, the own
var at `bvar 0`), and the recursive result is genuinely *used* (applied to the
parameter). Under the OLD un-shielded `instTy` this failed subject reduction (see
`SpikeSchemeRelMutual.preservation_fails`); with the scheme-relative opened rule
plus `instTy`/`openTyVars` depth-shielding now in Core, it both types and reduces
soundly (it is covered by `TypeOfHM.preservation`). -/

/-- `∀a. a → a`. -/
def selfSig : PolyTy := ⟨1, .arrow (.bvar 0) (.bvar 0)⟩

/-- `f`'s RHS: `λx. ((g [a→a]) (λy. y)) x`. Member 0 cross-calls the sibling `g`
    (`= var 2` under the λ) at member 0's OWN type variable `a` (`arrow (bvar 0)
    (bvar 0)`), and *uses* the result `(g[a→a]) (λy.y) : a→a` by applying it to
    `x : a`, giving `a`. So `f : a → a`. -/
def fRhs : Expr :=
  .lambda none
    (.app (.app (.var 2 [.arrow (.bvar 0) (.bvar 0)]) (.lambda none (.var 0 [])))
      (.var 0 []))

/-- `g`'s RHS: `λx. ((f [a→a]) (λy. y)) x`, the symmetric own-variable cross-call
    to `f` (`= var 1` under the λ). -/
def gRhs : Expr :=
  .lambda none
    (.app (.app (.var 1 [.arrow (.bvar 0) (.bvar 0)]) (.lambda none (.var 0 [])))
      (.var 0 []))

/-- `let rec (f : ∀a.a→a) = λx. (g[a→a] id) x and (g : ∀a.a→a) = λx. (f[a→a] id) x
    in f [Int]`, the mutual OWN-variable polymorphic-recursion group. -/
def mutualTerm : Expr := .letRecAnn [selfSig, selfSig] [fRhs, gRhs] (.var 0 [.prim .int])

theorem fRhs_opened_types (X : Nat) :
    TypeOfHM ⟨[selfSig, selfSig], []⟩ (fRhs.openTyVars [X]) ((Ty.fvar X).arrow (Ty.fvar X)) := by
  show TypeOfHM ⟨[selfSig, selfSig], []⟩
    (.lambda none
      (.app (.app (.var 2 [.arrow (.fvar X) (.fvar X)]) (.lambda none (.var 0 [])))
        (.var 0 [])))
    ((Ty.fvar X).arrow (Ty.fvar X))
  refine TypeOfHM.lambda (paramTy := .fvar X) .fvar (fun T h => Option.noConfusion h) rfl ?_
  refine TypeOfHM.app (argTy := .fvar X) ?_ ?_
  · refine TypeOfHM.app (argTy := .arrow (.fvar X) (.fvar X)) ?_ ?_
    · exact TypeOfHM.var (polyTy := selfSig) rfl
        (by intro t ht; simp only [List.mem_singleton] at ht; subst ht; exact .arrow .fvar .fvar)
        rfl (.arrow (.bvar rfl) (.bvar rfl))
    · refine TypeOfHM.lambda (paramTy := .fvar X) .fvar (fun T h => Option.noConfusion h) rfl ?_
      exact TypeOfHM.var (polyTy := PolyTy.mkTrivial (.fvar X)) rfl
        (by intro t ht; cases ht) rfl .fvar
  · exact TypeOfHM.var (polyTy := PolyTy.mkTrivial (.fvar X)) rfl
      (by intro t ht; cases ht) rfl .fvar

theorem gRhs_opened_types (X : Nat) :
    TypeOfHM ⟨[selfSig, selfSig], []⟩ (gRhs.openTyVars [X]) ((Ty.fvar X).arrow (Ty.fvar X)) := by
  show TypeOfHM ⟨[selfSig, selfSig], []⟩
    (.lambda none
      (.app (.app (.var 1 [.arrow (.fvar X) (.fvar X)]) (.lambda none (.var 0 [])))
        (.var 0 [])))
    ((Ty.fvar X).arrow (Ty.fvar X))
  refine TypeOfHM.lambda (paramTy := .fvar X) .fvar (fun T h => Option.noConfusion h) rfl ?_
  refine TypeOfHM.app (argTy := .fvar X) ?_ ?_
  · refine TypeOfHM.app (argTy := .arrow (.fvar X) (.fvar X)) ?_ ?_
    · exact TypeOfHM.var (polyTy := selfSig) rfl
        (by intro t ht; simp only [List.mem_singleton] at ht; subst ht; exact .arrow .fvar .fvar)
        rfl (.arrow (.bvar rfl) (.bvar rfl))
    · refine TypeOfHM.lambda (paramTy := .fvar X) .fvar (fun T h => Option.noConfusion h) rfl ?_
      exact TypeOfHM.var (polyTy := PolyTy.mkTrivial (.fvar X)) rfl
        (by intro t ht; cases ht) rfl .fvar
  · exact TypeOfHM.var (polyTy := PolyTy.mkTrivial (.fvar X)) rfl
      (by intro t ht; cases ht) rfl .fvar

/-- **Mutual own-variable polymorphic recursion types** under Core's fixed
    `TypeOfHM.letRecAnn`: each binding is checked scheme-relatively at its own fresh
    `X` (its own-var cross-call becomes the closed `X → X`); the body uses `f` at
    `Int`. -/
theorem mutual_typeable :
    TypeOfHM ⟨[], []⟩ mutualTerm ((Ty.prim .int).arrow (.prim .int)) := by
  refine TypeOfHM.letRecAnn (schemes := [selfSig, selfSig]) (L := []) rfl ?_ ?_ rfl ?_
  · intro σ hσ
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hσ
    rcases hσ with rfl | rfl <;>
      exact (show ContainsBvarsUpTo 1 ((Ty.bvar 0).arrow (Ty.bvar 0)) from
        .arrow (.bvar (by omega)) (.bvar (by omega)))
  · intro p hp Xs hfresh
    have hzip : [fRhs, gRhs].zip [selfSig, selfSig] = [(fRhs, selfSig), (gRhs, selfSig)] := rfl
    rw [hzip] at hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl
    · obtain ⟨X, rfl⟩ : ∃ X, Xs = [X] := List.length_eq_one_iff.mp hfresh.length
      exact fRhs_opened_types X
    · obtain ⟨X, rfl⟩ : ∃ X, Xs = [X] := List.length_eq_one_iff.mp hfresh.length
      exact gRhs_opened_types X
  · exact TypeOfHM.var (polyTy := selfSig) rfl
      (by intro t ht; simp only [List.mem_singleton] at ht; subst ht; exact .prim)
      rfl (.arrow (.bvar rfl) (.bvar rfl))

end SpikeC
