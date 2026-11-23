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

/-- The type inference found for each node of a term, in the term's shape: a
node's children are its children's trees, in `ExprStep` order (`lambdaBody`;
`appFunction`, `appArgument`; `letRhs`, `letBody`; `fixBody`;
`matchScrutinee`, then each `matchBranch`). A branch's tree is a node of its
own, typed as the match, whose children are a leaf per field (the type of the
variable the pattern binds for it) and then the body's tree. It is for tools
such as editors: no theorem is stated about it. -/
inductive TypeTree where
  | node (ty : InfTy) (children : List TypeTree)
  deriving Repr

instance : Inhabited TypeTree := ⟨.node (.prim .unit) []⟩

mutual
def TypeTree.map (f : InfTy → InfTy) : TypeTree → TypeTree
  | .node ty children => .node (f ty) (TypeTree.mapList f children)

def TypeTree.mapList (f : InfTy → InfTy) : List TypeTree → List TypeTree
  | [] => []
  | tree :: rest => tree.map f :: TypeTree.mapList f rest
end

structure Inferred where
  ty : InfTy
  elaboration : Expr InfTy
  store : MStore
  /-- The type of every node, as inferred so far (see `TypeTree`). -/
  types : TypeTree

/-! ## Errors -/

/-- A step from an expression to one of its children. -/
inductive ExprStep where
  | lambdaBody
  | appFunction
  | appArgument
  | letRhs
  | letBody
  | fixBody
  | matchScrutinee
  /-- The body of branch `index`, counting from 0. -/
  | matchBranch (index : Nat)
  deriving DecidableEq, Repr

/-- Why inference rejected the expression an `InferError` points at. A reason
carries only what the source does not already show. -/
inductive InferErrorReason where
  /-- A variable with no binder. -/
  | unboundVar
  /-- A constructor the signature does not declare, or whose declaration is
  ill formed. -/
  | unknownCtor
  /-- A comparison operator, but the signature declares no `Bool`. -/
  | noBool
  /-- An annotation mentions a type variable that is not in scope. -/
  | illScopedAnnotation
  /-- A match without branches. -/
  | emptyMatch
  /-- The type of the match's first pattern has no well-formed declaration. -/
  | unknownType
  /-- This branch's pattern is not a constructor of the first pattern's type. -/
  | foreignPattern
  /-- This branch's pattern binds a different number of variables than its
  constructor has fields. -/
  | patternArity
  /-- Two types that must be equal are not; `cause` is the clash within them.
  At an application, `actual` is the function's type and `expected` is
  `argument -> ?result`; at an explicit let, the right-hand side's type against
  the annotation; at a `fix`, the body's type against the binder's; at a
  scrutinee, its type against its pattern's; at a branch, the body's type
  against the match's. -/
  | mismatch (expected actual : InfTy) (cause : UnifyError)
  /-- An explicit let's definition and context leave these holes of its
  annotation undetermined: each could equally be one of its binders. -/
  | ambiguousSignature (holes : List String)
  /-- The program's type is not determined. -/
  | undeterminedType (ty : InfTy)
  /-- The type of the binder at this node (a lambda's parameter, a `fix`'s
  binder, or an explicit let's annotation) is not determined. -/
  | undeterminedAnnotation (ty : InfTy)
  deriving DecidableEq, Repr

/-- A rejection: the reason, and the path from the program's root to the
expression it concerns. -/
structure InferError where
  path : List ExprStep
  reason : InferErrorReason
  deriving DecidableEq, Repr

/-- An error at the current expression. -/
def InferError.here (reason : InferErrorReason) : InferError := ⟨[], reason⟩

/-- An error found in the child `step`, seen from its parent. -/
def InferError.under (step : ExprStep) (error : InferError) : InferError :=
  ⟨step :: error.path, error.reason⟩

/-- An error in branch `i` of a branch list's tail is in branch `i + 1` of the
whole list. -/
def InferError.nextBranch : InferError → InferError
  | ⟨.matchBranch index :: path, reason⟩ => ⟨.matchBranch (index + 1) :: path, reason⟩
  | error => error

/-- Unify `actual` with `expected`, reporting a failure as a mismatch at `path`. -/
def MStore.unifyAt (store : MStore) (path : List ExprStep) (actual expected : InfTy) :
    Except InferError MStore :=
  (store.unify actual expected).mapError fun cause =>
    ⟨path, .mismatch (store.apply expected) (store.apply actual) cause⟩

/-- The holes of an explicit let's annotation `template`, allocated from
`?base`, whose resolution still mentions a metavariable above level `k`. -/
def MStore.ambiguousHoles (store : MStore) (template : Template) (base k : Nat) :
    List String :=
  let names := template.vars.dedup
  names.filter fun name =>
    (store.apply (.var (base + names.idxOf name))).vars.any (store.levelOf · > k)

/-- The type of a lambda parameter or a `fix` binder: a fresh metavariable,
or the annotation with its holes allocated. -/
def paramTy (k : Nat) (store : MStore) : Option Template → Option (InfTy × MStore)
  | none => some (store.fresh k)
  | some template => if template.WF k then some (store.allocate k template) else none

/-! ## The algorithm -/

mutual
/-- Infer a type and an elaboration for `src` at rigid depth `k` in `ctx`,
extending `store`, or report the first error. -/
def inferAt (sig : Signature) (k : Nat) (ctx : Ctx Nat) :
    Source → MStore → Except InferError Inferred
  | .lit literal, store => pure ⟨literal.ty, .lit literal, store, .node literal.ty []⟩
  | .primOp op, store => do
      let ty ← (op.ty sig).getDM (throw (.here .noBool))
      pure ⟨ty, .primOp op, store, .node ty []⟩
  | .ctor ref, store => do
      let scheme ← (sig.ctorScheme ref).getDM (throw (.here .unknownCtor))
      let (args, store) := store.freshMany k scheme.arity
      pure ⟨scheme.lift.inst args, .ctor ref, store, .node (scheme.lift.inst args) []⟩
  | .var index, store => do
      let scheme ← ctx[index]?.getDM (throw (.here .unboundVar))
      let (args, store) := store.freshMany k scheme.arity
      pure ⟨scheme.inst args, .var index, store, .node (scheme.inst args) []⟩
  | .lambda param body, store => do
      let (paramTy, store) ← (paramTy k store param).getDM (throw (.here .illScopedAnnotation))
      let bodyResult ← (inferAt sig k (.mono paramTy :: ctx) body store).mapError
        (.under .lambdaBody)
      pure ⟨.arrow paramTy bodyResult.ty, .lambda (some paramTy) bodyResult.elaboration,
        bodyResult.store, .node (.arrow paramTy bodyResult.ty) [bodyResult.types]⟩
  | .app function argument, store => do
      let functionResult ← (inferAt sig k ctx function store).mapError (.under .appFunction)
      let argumentResult ← (inferAt sig k ctx argument functionResult.store).mapError
        (.under .appArgument)
      let (resultTy, store) := argumentResult.store.fresh k
      let store ← store.unifyAt [] functionResult.ty (.arrow argumentResult.ty resultTy)
      pure ⟨resultTy, .app functionResult.elaboration argumentResult.elaboration, store,
        .node resultTy [functionResult.types, argumentResult.types]⟩
  | .letIn none rhs body, store => do
      let rhsResult ← (inferAt sig k ctx rhs store).mapError (.under .letRhs)
      let bodyResult ← (inferAt sig k (.mono rhsResult.ty :: ctx) body rhsResult.store).mapError
        (.under .letBody)
      pure ⟨bodyResult.ty, .letIn none rhsResult.elaboration bodyResult.elaboration,
        bodyResult.store, .node bodyResult.ty [rhsResult.types, bodyResult.types]⟩
  | .letIn (some ann) rhs body, store => do
      -- Check the right-hand side generically, at the fresh rigid levels
      -- `k, ..., inner - 1`. The annotation's holes may mention them, so they
      -- start at the inner level.
      let inner := k + ann.arity
      if ¬ ann.body.WF inner then throw (.here .illScopedAnnotation)
      let (annTy, allocated) := store.allocate inner ann.body
      let rhsResult ← (inferAt sig inner ctx rhs allocated).mapError (.under .letRhs)
      let unified ← rhsResult.store.unifyAt [] rhsResult.ty annTy
      let completed := unified.apply annTy
      -- A metavariable still at an inner level is not determined by the
      -- definition and its context: it could equally be a binder.
      if ¬ completed.vars.all (unified.levelOf · ≤ k) then
        throw (.here (.ambiguousSignature (unified.ambiguousHoles ann.body store.length k)))
      let scheme : Scheme Nat := ⟨ann.arity, completed.closeRigids k ann.arity⟩
      let bodyResult ← (inferAt sig k (scheme :: ctx) body unified).mapError (.under .letBody)
      pure ⟨bodyResult.ty,
        .letIn (some ⟨ann.arity, completed⟩) rhsResult.elaboration bodyResult.elaboration,
        bodyResult.store, .node bodyResult.ty [rhsResult.types, bodyResult.types]⟩
  | .fix self body, store => do
      let (selfTy, store) ← (paramTy k store self).getDM (throw (.here .illScopedAnnotation))
      let bodyResult ← (inferAt sig k (.mono selfTy :: ctx) body store).mapError
        (.under .fixBody)
      let store ← bodyResult.store.unifyAt [] bodyResult.ty selfTy
      pure ⟨selfTy, .fix (some selfTy) bodyResult.elaboration, store,
        .node selfTy [bodyResult.types]⟩
  | .match scrutinee branches, store => do
      -- The first pattern names the type; every pattern must be one of its
      -- constructors.
      let (first, _) ← branches.head?.getDM (throw (.here .emptyMatch))
      let decl ← (sig.decl? first.ctor.type).getDM (throw ⟨[.matchBranch 0], .unknownType⟩)
      if ¬ branches.all (fun branch =>
          branch.1.ctor.type == first.ctor.type &&
            decide (branch.1.ctor.index < decl.ctors.length)) then
        throw ⟨[.matchBranch (branches.findIdx fun branch =>
          !(branch.1.ctor.type == first.ctor.type &&
            decide (branch.1.ctor.index < decl.ctors.length)))],
          .foreignPattern⟩
      -- Every pattern binds one variable per field.
      if ¬ branches.all (fun branch => decl.ctors[branch.1.ctor.index]?.all fun ctor =>
          branch.1.binders == ctor.fields.length) then
        throw ⟨[.matchBranch (branches.findIdx fun branch =>
          !(decl.ctors[branch.1.ctor.index]?.all fun ctor =>
            branch.1.binders == ctor.fields.length))],
          .patternArity⟩
      let scrutineeResult ← (inferAt sig k ctx scrutinee store).mapError
        (.under .matchScrutinee)
      let (args, store) := scrutineeResult.store.freshMany k decl.params
      let store ← store.unifyAt [.matchScrutinee] scrutineeResult.ty
        (Ty.apps (.con first.ctor.type) args)
      let (resultTy, store) := store.fresh k
      let ((branchesElab, store), branchTypes) ←
        inferBranches sig k ctx decl args resultTy branches store
      pure ⟨resultTy, .match scrutineeResult.elaboration branchesElab, store,
        .node resultTy (scrutineeResult.types :: branchTypes)⟩

/-- Infer each branch body in turn, with its constructor's fields in the
context, and unify its type with `resultTy`. The fields are instantiated at
`args` and, for the constructor's own variables, at fresh rigid levels. Error
paths start at the failing branch. Also returns each branch's `TypeTree`. -/
def inferBranches (sig : Signature) (k : Nat) (ctx : Ctx Nat) (decl : DataDecl)
    (args : List InfTy) (resultTy : InfTy) :
    List (Pattern × Source) → MStore →
      Except InferError ((List (Pattern × Expr InfTy) × MStore) × List TypeTree)
  | [], store => pure (([], store), [])
  | (pattern, body) :: rest, store => do
      let ctor ← decl.ctors[pattern.ctor.index]?.getDM
        (throw ⟨[.matchBranch 0], .foreignPattern⟩)
      -- The constructor's own variables are the fresh rigid levels
      -- `k, ..., inner - 1`, and the body is inferred at the inner depth.
      -- `resultTy`, `args` and the context's metavariables are at level `k` or
      -- below, so unification cannot solve them to a type that mentions the
      -- fresh levels: that is the escape check.
      let inner := k + ctor.existentials
      let fieldTys := ctor.fields.map fun field =>
        field.lift.instantiate (args ++ rigidBlock k ctor.existentials)
      let bodyResult ← (inferAt sig inner ((fieldTys.map .mono).reverse ++ ctx) body store).mapError
        (.under (.matchBranch 0))
      let store ← bodyResult.store.unifyAt [.matchBranch 0] bodyResult.ty resultTy
      let ((restElab, store), restTypes) ←
        (inferBranches sig k ctx decl args resultTy rest store).mapError InferError.nextBranch
      pure (((pattern, bodyResult.elaboration) :: restElab, store),
        .node resultTy (fieldTys.map (.node · []) ++ [bodyResult.types]) :: restTypes)
end

/-! ## Closed programs -/

/-- An annotation that is not ground, as an error at `path`. -/
def undeterminedAt (path : List ExprStep) : Option InfTy → Option InferError
  | some ty => if ty.ground.isNone then some ⟨path, .undeterminedAnnotation ty⟩ else none
  | none => none

mutual
/-- The first annotation of a resolved elaboration that is not ground, as an
error at its binder. -/
def Expr.firstUndetermined : Expr InfTy → Option InferError
  | .lit _ | .primOp _ | .ctor _ | .var _ => none
  | .lambda param body =>
      undeterminedAt [] param <|> (body.firstUndetermined.map (.under .lambdaBody))
  | .app function argument =>
      (function.firstUndetermined.map (.under .appFunction)) <|>
        (argument.firstUndetermined.map (.under .appArgument))
  | .letIn ann rhs body =>
      undeterminedAt [] (ann.map (·.body)) <|>
        (rhs.firstUndetermined.map (.under .letRhs)) <|>
          (body.firstUndetermined.map (.under .letBody))
  | .fix self body =>
      undeterminedAt [] self <|> (body.firstUndetermined.map (.under .fixBody))
  | .match scrutinee branches =>
      (scrutinee.firstUndetermined.map (.under .matchScrutinee)) <|>
        Expr.firstUndeterminedBranches 0 branches

/-- `Expr.firstUndetermined` on the branch bodies, the first numbered `index`. -/
def Expr.firstUndeterminedBranches (index : Nat) :
    List (Pattern × Expr InfTy) → Option InferError
  | [] => none
  | (_, body) :: rest =>
      (body.firstUndetermined.map (.under (.matchBranch index))) <|>
        Expr.firstUndeterminedBranches (index + 1) rest
end

structure InferenceResult where
  elaboration : Elab
  ty : SemTy
  deriving DecidableEq, Repr

/-- Infer a closed program. It is accepted exactly when its type and every
implicit type of its elaboration are determined. -/
def infer (sig : Signature) (src : Source) : Except InferError InferenceResult := do
  let result ← inferAt sig 0 [] src []
  let resolved := result.store.apply result.ty
  let ty ← resolved.ground.getDM (throw (.here (.undeterminedType resolved)))
  let elaboration := result.store.applyElab result.elaboration
  let ground ← (elaboration.traverseAnn Ty.ground).getDM
    -- `firstUndetermined` finds the annotation that `traverseAnn` failed on.
    (throw (elaboration.firstUndetermined.getD (.here (.undeterminedType resolved))))
  pure ⟨ground, ty⟩

/-- `infer`, also returning the type of every node of `src`, resolved (see
`TypeTree`; parts the program leaves undetermined stay metavariables). -/
def inferWithTypes (sig : Signature) (src : Source) :
    Except InferError (InferenceResult × TypeTree) := do
  let result ← inferAt sig 0 [] src []
  let resolved := result.store.apply result.ty
  let ty ← resolved.ground.getDM (throw (.here (.undeterminedType resolved)))
  let elaboration := result.store.applyElab result.elaboration
  let ground ← (elaboration.traverseAnn Ty.ground).getDM
    (throw (elaboration.firstUndetermined.getD (.here (.undeterminedType resolved))))
  pure (⟨ground, ty⟩, result.types.map result.store.apply)

/-- `inferWithTypes` accepts and rejects exactly as `infer` does, with the
same result. -/
theorem inferWithTypes_fst (sig : Signature) (src : Source) :
    (inferWithTypes sig src).map Prod.fst = infer sig src := by
  unfold inferWithTypes infer
  cases inferAt sig 0 [] src [] with
  | error => rfl
  | ok result =>
      simp only [bind, Except.bind]
      cases (result.store.apply result.ty).ground <;> simp [Option.getDM, Except.map, pure, Except.pure]
      cases (result.store.applyElab result.elaboration).traverseAnn Ty.ground <;> rfl

end EPL
