import FHM.Core

/-! # SPIKE C: a *kept* recursion scheme referencing an enclosing-scope type var

Question (the make-or-break "C" feature): can the codebase's type-ERASURE safety
architecture support a `letRecAnn` whose scheme references a type variable bound by
an ENCLOSING scope (ScopedTypeVariables on a polymorphic-recursive helper)?

The only erasure-compatible idea on the table was **freeze-and-re-generalise**:
erase the enclosing binder's `∀a`, "freeze" `a` to a fresh free `fvar Z` inside the
kept recursion scheme, and let the now-unannotated enclosing binder *re-generalise*
`Z` to recover the outer function's polymorphism.

This file tests the crux of that idea on the REAL `TypeOfElabHM.letRecAnn` node:
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
def cTerm (Z : Nat) : Expr := .letRec [some (sigZ Z)] [rhs] (.var 0 [])

/-- POSITIVE — Feature B: with `Z` a *top-level* rigid constant, the term types at
    `Z → Z`, and this is erasure-safe (free `fvar`s never dangle). -/
theorem cTerm_typeable (Z : Nat) :
    TypeOfElabHM ⟨[], []⟩ (cTerm Z) (.arrow (.fvar Z) (.fvar Z)) := by
  refine TypeOfElabHM.letRec (specs := [.poly (sigZ Z)]) (G := []) (L := [])
    ⟨rfl, rfl, List.nodup_nil, fun τ hτ => by simp at hτ, ?_⟩ ?_ ?_ rfl ?_
  · intro σ hσ; simp only [List.mem_singleton, RecSpec.poly.injEq] at hσ; subst hσ
    exact .arrow .fvar .fvar
  · intro Xs _hfresh p hp τ hτ
    simp only [List.zip_cons_cons, List.zip_nil_right, List.mem_singleton] at hp
    subst hp
    exact RecSpec.noConfusion hτ
  · intro Xs _hfresh p hp σ hσ Ys hYs
    simp only [List.zip_cons_cons, List.zip_nil_right, List.mem_singleton] at hp
    subst hp
    injection hσ with hσσ
    subst hσσ
    obtain rfl : Ys = [] := List.eq_nil_of_length_eq_zero hYs.length
    show TypeOfElabHM ⟨[sigZ Z], []⟩ (rhs.openTyVars []) ((Ty.fvar Z).arrow (Ty.fvar Z))
    refine TypeOfElabHM.lambda .fvar (fun T h => Option.noConfusion h) rfl ?_
    refine TypeOfElabHM.app (argTy := .fvar Z) ?_ ?_
    · exact TypeOfElabHM.var (polyTy := sigZ Z) (tyArgs := []) rfl
        ⟨rfl, by intro t ht; cases ht⟩ (.arrow .fvar .fvar)
    · exact TypeOfElabHM.var (polyTy := PolyTy.mkTrivial (.fvar Z)) (tyArgs := []) rfl
        ⟨rfl, by intro t ht; cases ht⟩ .fvar
  · exact TypeOfElabHM.var (polyTy := sigZ Z) (tyArgs := []) rfl
      ⟨rfl, by intro t ht; cases ht⟩ (.arrow .fvar .fvar)

/-- NEGATIVE — the obstruction: the kept scheme `Z → Z` is **rigid** in `Z`. The
    term does NOT type at `X → X` for any `X ≠ Z`, so it is *not* polymorphic in
    `Z`. Hence an enclosing (unannotated) binder cannot generalise `Z`, and
    freeze-and-re-generalise cannot recover the outer function's polymorphism in a
    type-erasure setting. Supporting C therefore needs the type *application*
    structure to survive (type-passing), not be erased. -/
theorem cTerm_rigid (Z X : Nat) (hne : X ≠ Z) :
    ¬ TypeOfElabHM ⟨[], []⟩ (cTerm Z) (.arrow (.fvar X) (.fvar X)) := by
  intro h
  cases h with
  | letRec hwf hmono hpoly heq hbody =>
    subst heq
    expose_names
    -- The spec list is forced: `[.poly (sigZ Z)]` by the stored annotation.
    match specs, hwf.anns_eq with
    | [s], hanns =>
      simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hanns
      cases RecSpec.ann_eq_some hanns
      cases hbody with
      | var hlook _hlc hinst =>
        simp only [RecSpecs.bodyCtx, List.map_cons, List.map_nil, RecSpec.bodyScheme,
          List.append_nil, List.getElem?_cons_zero, Option.some.injEq] at hlook
        subst hlook
        simp only [PolyTy.InstantiatesTo, sigZ] at hinst
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
soundly (it is covered by `TypeOfElabHM.preservation`). -/

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
def mutualTerm : Expr :=
  .letRec [some selfSig, some selfSig] [fRhs, gRhs] (.var 0 [.prim .int])

theorem fRhs_opened_types (X : Nat) :
    TypeOfElabHM ⟨[selfSig, selfSig], []⟩ (fRhs.openTyVars [X]) ((Ty.fvar X).arrow (Ty.fvar X)) := by
  show TypeOfElabHM ⟨[selfSig, selfSig], []⟩
    (.lambda none
      (.app (.app (.var 2 [.arrow (.fvar X) (.fvar X)]) (.lambda none (.var 0 [])))
        (.var 0 [])))
    ((Ty.fvar X).arrow (Ty.fvar X))
  refine TypeOfElabHM.lambda (paramTy := .fvar X) .fvar (fun T h => Option.noConfusion h) rfl ?_
  refine TypeOfElabHM.app (argTy := .fvar X) ?_ ?_
  · refine TypeOfElabHM.app (argTy := .arrow (.fvar X) (.fvar X)) ?_ ?_
    · exact TypeOfElabHM.var (polyTy := selfSig) rfl
        ⟨rfl, by intro t ht; simp only [List.mem_singleton] at ht; subst ht; exact .arrow .fvar .fvar⟩
        (.arrow (.bvar rfl) (.bvar rfl))
    · refine TypeOfElabHM.lambda (paramTy := .fvar X) .fvar (fun T h => Option.noConfusion h) rfl ?_
      exact TypeOfElabHM.var (polyTy := PolyTy.mkTrivial (.fvar X)) rfl
        ⟨rfl, by intro t ht; cases ht⟩ .fvar
  · exact TypeOfElabHM.var (polyTy := PolyTy.mkTrivial (.fvar X)) rfl
      ⟨rfl, by intro t ht; cases ht⟩ .fvar

theorem gRhs_opened_types (X : Nat) :
    TypeOfElabHM ⟨[selfSig, selfSig], []⟩ (gRhs.openTyVars [X]) ((Ty.fvar X).arrow (Ty.fvar X)) := by
  show TypeOfElabHM ⟨[selfSig, selfSig], []⟩
    (.lambda none
      (.app (.app (.var 1 [.arrow (.fvar X) (.fvar X)]) (.lambda none (.var 0 [])))
        (.var 0 [])))
    ((Ty.fvar X).arrow (Ty.fvar X))
  refine TypeOfElabHM.lambda (paramTy := .fvar X) .fvar (fun T h => Option.noConfusion h) rfl ?_
  refine TypeOfElabHM.app (argTy := .fvar X) ?_ ?_
  · refine TypeOfElabHM.app (argTy := .arrow (.fvar X) (.fvar X)) ?_ ?_
    · exact TypeOfElabHM.var (polyTy := selfSig) rfl
        ⟨rfl, by intro t ht; simp only [List.mem_singleton] at ht; subst ht; exact .arrow .fvar .fvar⟩
        (.arrow (.bvar rfl) (.bvar rfl))
    · refine TypeOfElabHM.lambda (paramTy := .fvar X) .fvar (fun T h => Option.noConfusion h) rfl ?_
      exact TypeOfElabHM.var (polyTy := PolyTy.mkTrivial (.fvar X)) rfl
        ⟨rfl, by intro t ht; cases ht⟩ .fvar
  · exact TypeOfElabHM.var (polyTy := PolyTy.mkTrivial (.fvar X)) rfl
      ⟨rfl, by intro t ht; cases ht⟩ .fvar

/-- **Mutual own-variable polymorphic recursion types** under the fused
    `TypeOfElabHM.letRec` (all-`some` degenerate case): each binding is checked
    scheme-relatively at its own fresh `X` (its own-var cross-call becomes the
    closed `X → X`); the body uses `f` at `Int`. -/
theorem mutual_typeable :
    TypeOfElabHM ⟨[], []⟩ mutualTerm ((Ty.prim .int).arrow (.prim .int)) := by
  refine TypeOfElabHM.letRec (specs := [.poly selfSig, .poly selfSig]) (G := []) (L := [])
    ⟨rfl, rfl, List.nodup_nil, fun τ hτ => by simp at hτ, ?_⟩ ?_ ?_ rfl ?_
  · intro σ hσ
    simp only [List.mem_cons, List.not_mem_nil, or_false, RecSpec.poly.injEq] at hσ
    rcases hσ with rfl | rfl <;>
      exact (show ContainsBvarsUpTo 1 ((Ty.bvar 0).arrow (Ty.bvar 0)) from
        .arrow (.bvar (by omega)) (.bvar (by omega)))
  · intro Xs _hfresh p hp τ hτ
    have hzip : [fRhs, gRhs].zip [RecSpec.poly selfSig, RecSpec.poly selfSig]
        = [(fRhs, RecSpec.poly selfSig), (gRhs, RecSpec.poly selfSig)] := rfl
    rw [hzip] at hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl <;> exact RecSpec.noConfusion hτ
  · intro Xs _hfresh p hp σ hσ Ys hYs
    have hzip : [fRhs, gRhs].zip [RecSpec.poly selfSig, RecSpec.poly selfSig]
        = [(fRhs, RecSpec.poly selfSig), (gRhs, RecSpec.poly selfSig)] := rfl
    rw [hzip] at hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl <;>
      (injection hσ with hσσ; subst hσσ)
    · obtain ⟨X, rfl⟩ : ∃ X, Ys = [X] := List.length_eq_one_iff.mp hYs.length
      exact fRhs_opened_types X
    · obtain ⟨X, rfl⟩ : ∃ X, Ys = [X] := List.length_eq_one_iff.mp hYs.length
      exact gRhs_opened_types X
  · exact TypeOfElabHM.var (polyTy := selfSig) rfl
      ⟨rfl, by intro t ht; simp only [List.mem_singleton] at ht; subst ht; exact .prim⟩
      (.arrow (.bvar rfl) (.bvar rfl))

end SpikeC

/-! ## SPIKE (de-risk): let-generalisation by elaboration to an annotated + closed `let`

Validates the InferW elaboration design: an *unannotated* source `let` whose rhs
uses a polymorphic variable should elaborate to an *annotated + closed* core `let`,
which `TypeOfElabHM.letIn` (it opens the bound expression per-opening) accepts at full
polymorphism — refuting the prior session's "must stay monomorphic" conclusion.

  Source skeleton :  let g = λx. id x in g 5         (id : ∀a.a→a at de Bruijn 0)
  Elaboration     :  let g : ∀a.a→a = λx. id[bvar0] x in g[Int] 5
-/
namespace SpikeLetInElab

/-- `∀a. a → a` — both `id`'s scheme and `g`'s inferred scheme. -/
def polyId : PolyTy := ⟨1, .arrow (.bvar 0) (.bvar 0)⟩

/-- Elaborated `let g = λx. id x in g 5`: `g`'s rhs is stored scheme-relatively
    (its generalised variable closed to `bvar 0`, so `id`'s tyArg is `[bvar 0]`). -/
def elabTerm : Expr :=
  .letIn (some polyId)
    (.lambda none (.app (.var 1 [.bvar 0]) (.var 0 [])))   -- closed rhs: λx. id[bvar0] x
    (.app (.var 0 [.prim .int]) (.primLit (.int 5)))        -- body: g[Int] 5

/-- The closed rhs, opened at any `X`, types at `X → X` — i.e. at EVERY opening of
    `g`'s scheme `∀a.a→a`. This is the cofinite premise of `TypeOfElabHM.letIn`. -/
theorem elabRhs_opened_typeable (X : Nat) :
    TypeOfElabHM ⟨[polyId], []⟩
      ((Expr.lambda none (.app (.var 1 [.bvar 0]) (.var 0 []))).openTyVars [X])
      ((Ty.fvar X).arrow (.fvar X)) := by
  show TypeOfElabHM ⟨[polyId], []⟩
    (.lambda none (.app (.var 1 [.fvar X]) (.var 0 [])))
    ((Ty.fvar X).arrow (.fvar X))
  refine TypeOfElabHM.lambda (paramTy := .fvar X) .fvar (fun T h => Option.noConfusion h) rfl ?_
  refine TypeOfElabHM.app (argTy := .fvar X) ?_ ?_
  · exact TypeOfElabHM.var (polyTy := polyId) rfl
      ⟨rfl, by intro t ht; simp only [List.mem_singleton] at ht; subst ht; exact .fvar⟩
      (.arrow (.bvar rfl) (.bvar rfl))
  · exact TypeOfElabHM.var (polyTy := PolyTy.mkTrivial (.fvar X)) rfl
      ⟨rfl, by intro t ht; cases ht⟩ .fvar

/-- **De-risk headline.** The elaborated term types at `Int` with `g` generalised
    to the full `∀a.a→a` — the let-polymorphism the prior session declared
    impossible. Sound (the annotated `letIn` rule opens the closed rhs per-opening)
    AND principal. -/
theorem elabTerm_typeable :
    TypeOfElabHM ⟨[polyId], []⟩ elabTerm (.prim .int) := by
  refine TypeOfElabHM.letIn (M := polyId) (L := [])
    ?_ (fun σ h => Option.some.inj h) ?_ rfl ?_
  · show ContainsBvarsUpTo 1 (Ty.arrow (Ty.bvar 0) (Ty.bvar 0))
    exact .arrow (.bvar (by omega)) (.bvar (by omega))
  · intro Xs hfresh
    obtain ⟨X, rfl⟩ : ∃ X, Xs = [X] := List.length_eq_one_iff.mp hfresh.length
    exact elabRhs_opened_typeable X
  · refine TypeOfElabHM.app (argTy := .prim .int) ?_ TypeOfElabHM.primLitInt
    exact TypeOfElabHM.var (polyTy := polyId) rfl
      ⟨rfl, by intro t ht; simp only [List.mem_singleton] at ht; subst ht; exact .prim⟩
      (.arrow (.bvar rfl) (.bvar rfl))

end SpikeLetInElab
