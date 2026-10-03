import FHM.Core

/-!
# Typing for fully erased runtime terms

`TypeOfHM` specifies which annotated source programs the checker accepts.
`RunWT` instead types machine terms after every annotation has disappeared.
Its recursive schemes are proof-only witnesses: they are not recoverable from,
and do not occur in, the `Expr` being evaluated.

The recursive rule is deliberately mixed:

* `.poly σ` members are available at the complete scheme `σ` inside the SCC;
* `.mono τ` members share one monotype inside the SCC and are generalized only
  in the enclosing body; and
* the runtime node stores only `none` annotations.

This module initially fixes the production judgment and a real-`Expr` witness.
Erasure soundness and operational preservation are proved in subsequent
checkpoints, using the completed small-calculus proofs as their template.
-/

namespace RuntimeTyping

/-- Runtime group evidence has no source-annotation alignment premise: those
annotations have already erased. -/
structure RecSpecsWF (bindings : List Expr) (specs : List RecSpec)
    (G : List Nat) : Prop where
  length : bindings.length = specs.length
  nodup : G.Nodup
  mono_lc : ∀ τ, .mono τ ∈ specs → τ.IsLC
  poly_wf : ∀ σ, .poly σ ∈ specs → σ.WF

/-- Ordinary HM members share one opening of the group's generalisation pool. -/
def MonoTyped (TypeOf : Ctx → Expr → Ty → Prop) (ctx : Ctx)
    (bindings : List Expr) (specs : List RecSpec) (G avoid : List Nat) : Prop :=
  ∀ Xs, FreshNames avoid G.length Xs →
    ∀ pair ∈ bindings.zip specs, ∀ τ, pair.2 = .mono τ →
      TypeOf (RecSpecs.rhsCtx ctx specs G Xs) pair.1 (Ty.renameG G Xs τ)

/-- Complete annotations enable scheme-polymorphic recursive use. Runtime terms
contain no type syntax, so only the expected type is opened at the member's
fresh rigid names. -/
def PolyTyped (TypeOf : Ctx → Expr → Ty → Prop) (ctx : Ctx)
    (bindings : List Expr) (specs : List RecSpec) (G avoid : List Nat) : Prop :=
  ∀ Xs, FreshNames avoid G.length Xs →
    ∀ pair ∈ bindings.zip specs, ∀ σ, pair.2 = .poly σ →
      ∀ Ys, FreshNames (avoid ++ Xs) σ.paramCount Ys →
        TypeOf (RecSpecs.rhsCtx ctx specs G Xs) pair.1 (σ.openVars Ys)

def GeneralisesTo (TypeOf : Ctx → Expr → Ty → Prop) (ctx : Ctx)
    (rhs : Expr) (scheme : PolyTy) (avoid : List Nat) : Prop :=
  ∀ Xs, FreshNames avoid scheme.paramCount Xs →
    TypeOf ctx rhs (scheme.openVars Xs)

mutual

/-- Typing for annotation-free machine terms. -/
inductive RunWT : Ctx → Expr → Ty → Prop
  | primLitUnit : RunWT ctx (.primLit .unit) (.prim .unit)
  | primLitInt : RunWT ctx (.primLit (.int n)) (.prim .int)
  | primLitNat : RunWT ctx (.primLit (.nat n)) (.prim .nat)
  | primLitChar : RunWT ctx (.primLit (.char c)) (.prim .char)
  | primBinOpIntAdd :
      RunWT ctx (.primBinOp .intAdd)
        (.arrow (.prim .int) (.arrow (.prim .int) (.prim .int)))
  | primBinOpIntSub :
      RunWT ctx (.primBinOp .intSub)
        (.arrow (.prim .int) (.arrow (.prim .int) (.prim .int)))
  | primBinOpIntLt :
      RunWT ctx (.ctor ⟨"True"⟩) (.customTy ⟨"Bool"⟩ []) →
      RunWT ctx (.ctor ⟨"False"⟩) (.customTy ⟨"Bool"⟩ []) →
      RunWT ctx (.primBinOp .intLt)
        (.arrow (.prim .int) (.arrow (.prim .int) (.customTy ⟨"Bool"⟩ [])))
  | primBinOpCharLt :
      RunWT ctx (.ctor ⟨"True"⟩) (.customTy ⟨"Bool"⟩ []) →
      RunWT ctx (.ctor ⟨"False"⟩) (.customTy ⟨"Bool"⟩ []) →
      RunWT ctx (.primBinOp .charLt)
        (.arrow (.prim .char) (.arrow (.prim .char) (.customTy ⟨"Bool"⟩ [])))
  | lambda :
      paramTy.IsLC →
      RunWT { ctx with env := PolyTy.mkTrivial paramTy :: ctx.env }
        body bodyTy →
      RunWT ctx (.lambda none body) (.arrow paramTy bodyTy)
  | app :
      RunWT ctx fn (.arrow argTy resultTy) →
      RunWT ctx arg argTy →
      RunWT ctx (.app fn arg) resultTy
  | letIn {scheme : PolyTy} {avoid : List Nat} :
      scheme.WF →
      GeneralisesTo RunWT ctx rhs scheme avoid →
      RunWT { ctx with env := scheme :: ctx.env } body resultTy →
      RunWT ctx (.letIn none rhs body) resultTy
  | var :
      ctx.env[index]? = some scheme →
      (∀ arg ∈ args, arg.IsLC) →
      scheme.InstantiatesTo args ty →
      RunWT ctx (.var index) ty
  | ctor :
      LookupList.get? ctx.ctors name = some ctor →
      (∀ arg ∈ args, arg.IsLC) →
      ctor.toTy.InstantiatesTo args ty →
      RunWT ctx (.ctor name) ty
  | match_ :
      RunWT ctx scrutinee scrutTy →
      branches ≠ [] →
      (∀ branch ∈ branches,
        RunWTMatchBranch ctx branch scrutTy resultTy) →
      RunWT ctx (.match_ scrutinee branches) resultTy
  | letRec {specs : List RecSpec} {G avoid : List Nat} :
      RecSpecsWF bindings specs G →
      MonoTyped RunWT ctx bindings specs G avoid →
      PolyTyped RunWT ctx bindings specs G avoid →
      RunWT (RecSpecs.bodyCtx ctx specs G) body resultTy →
      RunWT ctx (.letRec (bindings.map (fun _ => none)) bindings body) resultTy

/-- Match-branch typing for erased terms. -/
inductive RunWTMatchBranch :
    Ctx → (MatchPattern × Expr) → Ty → Ty → Prop
  | mk {ctor : Ctor} {ctx : Ctx} {c : CtorName} {n : Nat}
      {tyArgs instContents : List Ty} :
      BranchCtorSpec ctx.ctors c n scrutTy ctor tyArgs instContents →
      RunWT { ctx with env := instContents.map PolyTy.mkTrivial ++ ctx.env }
        body resultTy →
      RunWTMatchBranch ctx (.named c n, body) scrutTy resultTy
  | wildcard :
      RunWT ctx body resultTy →
      RunWTMatchBranch ctx (.wildcard, body) scrutTy resultTy

end


/-! ## A real-Core erased polymorphic-recursion witness -/

def polyId : PolyTy := ⟨1, .arrow (.bvar 0) (.bvar 0)⟩

/-- `fun x => (fun _ => x) (self 0)`: the current call is at a rigid `a`,
while the recursive occurrence is independently instantiated at `Int`. -/
def polySelfRhs : Expr :=
  .lambda none
    (.app (.lambda none (.var 1)) (.app (.var 1) (.primLit (.int 0))))

def polySelfBindings : List Expr := [polySelfRhs]

theorem polyId_wf : polyId.WF := by
  show ContainsBvarsUpTo 1 (.arrow (.bvar 0) (.bvar 0))
  exact .arrow (.bvar (by omega)) (.bvar (by omega))

theorem polySelf_specs_wf :
    RecSpecsWF polySelfBindings [.poly polyId] [] := by
  refine ⟨by simp [polySelfBindings], by simp, ?_, ?_⟩
  · intro ty hty
    simp at hty
  · intro scheme hscheme
    simp only [List.mem_singleton, RecSpec.poly.injEq] at hscheme
    subst scheme
    exact polyId_wf

theorem polySelf_mono :
    MonoTyped RunWT ⟨[], []⟩ polySelfBindings [.poly polyId] [] [] := by
  intro Xs hXs pair hpair ty hmono
  have hXsNil : Xs = [] := List.length_eq_zero_iff.mp hXs.length
  subst Xs
  simp [polySelfBindings] at hpair
  subst pair
  simp at hmono

private theorem singleton_of_fresh_one {avoid names : List Nat}
    (h : FreshNames avoid 1 names) : ∃ name, names = [name] := by
  exact List.length_eq_one_iff.mp h.length

theorem polySelf_poly :
    PolyTyped RunWT ⟨[], []⟩ polySelfBindings [.poly polyId] [] [] := by
  intro Xs hXs pair hpair scheme hscheme Ys hYs
  have hXsNil : Xs = [] := List.length_eq_zero_iff.mp hXs.length
  subst Xs
  simp [polySelfBindings] at hpair
  subst pair
  simp only [RecSpec.poly.injEq] at hscheme
  subst scheme
  obtain ⟨Y, rfl⟩ := singleton_of_fresh_one hYs
  change RunWT ⟨[polyId], []⟩ polySelfRhs
    (.arrow (.fvar Y) (.fvar Y))
  apply RunWT.lambda .fvar
  apply RunWT.app (argTy := .prim .int)
  · apply RunWT.lambda .prim
    exact RunWT.var (index := 1) (scheme := PolyTy.mkTrivial (.fvar Y))
      (args := []) rfl (by simp) .fvar
  · apply RunWT.app (argTy := .prim .int)
    · exact RunWT.var (index := 1) (scheme := polyId)
        (args := [.prim .int]) rfl (by simp; exact .prim)
        (.arrow (.bvar rfl) (.bvar rfl))
    · exact .primLitInt

theorem polySelf_body :
    RunWT (RecSpecs.bodyCtx ⟨[], []⟩ [.poly polyId] [])
      (.var 0) (.arrow (.prim .unit) (.prim .unit)) := by
  exact RunWT.var (index := 0) (scheme := polyId)
    (args := [.prim .unit]) rfl (by simp; exact .prim)
    (.arrow (.bvar rfl) (.bvar rfl))

/-- No scheme or type application occurs anywhere in this runtime expression. -/
theorem erased_polySelf_typed :
    RunWT ⟨[], []⟩
      (.letRec (polySelfBindings.map (fun _ => none))
        polySelfBindings (.var 0))
      (.arrow (.prim .unit) (.prim .unit)) := by
  exact .letRec polySelf_specs_wf polySelf_mono polySelf_poly polySelf_body

#print axioms erased_polySelf_typed

end RuntimeTyping
