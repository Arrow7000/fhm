import EPL.Unify
import EPL.Typing

/-!
# Inference

`inferAt sig k ctx src store` infers a type and an elaboration for `src` at
rigid depth `k`, extending `store`. It recurses structurally on `src`.

The store's length is the allocation frontier: `?store.length` is the next
fresh metavariable.
-/

namespace EPL

/-- A fresh unsolved metavariable at `level`. -/
def MStore.fresh (store : MStore) (level : Nat) : InfTy × MStore :=
  (.var store.length, store ++ [⟨level, none⟩])

/-- `count` fresh unsolved metavariables at `level`. -/
def MStore.freshMany (store : MStore) (level count : Nat) : List InfTy × MStore :=
  ((List.range count).map fun i => .var (store.length + i),
    store ++ List.replicate count ⟨level, none⟩)

/-- Resolve a template's holes to fresh metavariables at `level`, one per
distinct name. -/
def MStore.allocate (store : MStore) (level : Nat) (template : Template) : InfTy × MStore :=
  let names := template.vars.dedup
  (template.bind fun name => .var (store.length + names.idxOf name),
    store ++ List.replicate names.length ⟨level, none⟩)

/-- Resolve every annotation of an internal elaboration. -/
def MStore.applyElab (store : MStore) (elaboration : Expr InfTy) : Expr InfTy :=
  elaboration.mapAnn store.apply

structure Inferred where
  ty : InfTy
  elaboration : Expr InfTy
  store : MStore

/-- The type of a lambda parameter or a `fix` binder: a fresh metavariable,
or the annotation with its holes allocated. -/
def paramTy (k : Nat) (store : MStore) : Option Template → Option (InfTy × MStore)
  | none => some (store.fresh k)
  | some template => if template.WF k then some (store.allocate k template) else none

def inferAt (sig : Signature) (k : Nat) (ctx : Ctx Nat) : Source → MStore → Option Inferred
  | .lit literal, store => some ⟨literal.ty, .lit literal, store⟩
  | .primOp op, store => do
      let ty ← op.ty sig
      some ⟨ty, .primOp op, store⟩
  | .const c, store => do
      let scheme ← sig.schemeOf c
      let (args, store) := store.freshMany k scheme.arity
      some ⟨scheme.lift.inst args, .const c, store⟩
  | .var index, store => do
      let scheme ← ctx[index]?
      let (args, store) := store.freshMany k scheme.arity
      some ⟨scheme.inst args, .var index, store⟩
  | .lambda param body, store => do
      let (paramTy, store) ← paramTy k store param
      let bodyResult ← inferAt sig k (.mono paramTy :: ctx) body store
      some ⟨.arrow paramTy bodyResult.ty, .lambda (some paramTy) bodyResult.elaboration,
        bodyResult.store⟩
  | .app function argument, store => do
      let functionResult ← inferAt sig k ctx function store
      let argumentResult ← inferAt sig k ctx argument functionResult.store
      let (resultTy, store) := argumentResult.store.fresh k
      let store ← store.unify functionResult.ty (.arrow argumentResult.ty resultTy)
      some ⟨resultTy, .app functionResult.elaboration argumentResult.elaboration, store⟩
  | .letIn none rhs body, store => do
      let rhsResult ← inferAt sig k ctx rhs store
      let bodyResult ← inferAt sig k (.mono rhsResult.ty :: ctx) body rhsResult.store
      some ⟨bodyResult.ty, .letIn none rhsResult.elaboration bodyResult.elaboration, bodyResult.store⟩
  | .letIn (some ann) rhs body, store => do
      -- Check the right-hand side generically, at the fresh rigid levels
      -- `k, ..., inner - 1`. The annotation's holes may mention them, so they
      -- start at the inner level.
      let inner := k + ann.arity
      if ¬ ann.body.WF inner then none
      let (annTy, store) := store.allocate inner ann.body
      let rhsResult ← inferAt sig inner ctx rhs store
      let store ← rhsResult.store.unify rhsResult.ty annTy
      let completed := store.apply annTy
      -- A metavariable still at an inner level is not determined by the
      -- definition and its context: it could equally be a binder.
      if ¬ completed.vars.all (store.levelOf · ≤ k) then none
      let scheme : Scheme Nat := ⟨ann.arity, completed.closeRigids k ann.arity⟩
      let bodyResult ← inferAt sig k (scheme :: ctx) body store
      some ⟨bodyResult.ty, .letIn (some ⟨ann.arity, completed⟩) rhsResult.elaboration bodyResult.elaboration,
        bodyResult.store⟩
  | .fix self body, store => do
      let (selfTy, store) ← paramTy k store self
      let bodyResult ← inferAt sig k (.mono selfTy :: ctx) body store
      let store ← bodyResult.store.unify bodyResult.ty selfTy
      some ⟨selfTy, .fix (some selfTy) bodyResult.elaboration, store⟩

structure InferenceResult where
  elaboration : Elab
  ty : SemTy
  deriving DecidableEq, Repr

/-- Infer a closed program. It is accepted exactly when its type and every
implicit type of its elaboration are determined. -/
def infer (sig : Signature) (src : Source) : Option InferenceResult := do
  let result ← inferAt sig 0 [] src []
  let ty ← (result.store.apply result.ty).ground
  let elaboration ← (result.store.applyElab result.elaboration).traverseAnn Ty.ground
  some ⟨elaboration, ty⟩

end EPL
