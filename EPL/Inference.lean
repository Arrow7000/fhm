import EPL.Unification
import EPL.Typing

namespace EPL

def Template.names : Template → List String
  | .fixed _ | .hole => []
  | .named name => [name]
  | .arrow domain codomain => domain.names ++ codomain.names
  | .app function argument => function.names ++ argument.names

def namedHoleTable (names : List String) (frontier : Nat) : HoleAssignment :=
  let keys := names.dedup
  keys.zip ((List.range keys.length).map fun offset => .mvar (frontier + offset))

/-- Resolve a template after its complete local named-hole table has been
allocated. `frontier` is reserved for anonymous holes only. -/
def Template.allocateWith (holes : HoleAssignment) : Nat → Template → Nat × Ty
  | frontier, .fixed ty => (frontier, ty)
  | frontier, .hole => (frontier + 1, .mvar frontier)
  | frontier, .named name =>
      (frontier, (holes.lookup name).getD (.mvar frontier))
  | frontier, .arrow domain codomain =>
      let domainResult := domain.allocateWith holes frontier
      let codomainResult := codomain.allocateWith holes domainResult.1
      (codomainResult.1, .arrow domainResult.2 codomainResult.2)
  | frontier, .app function argument =>
      let functionResult := function.allocateWith holes frontier
      let argumentResult := argument.allocateWith holes functionResult.1
      (argumentResult.1, .app functionResult.2 argumentResult.2)

structure Template.Allocation where
  next : Nat
  ty : Ty
  holes : HoleAssignment
  deriving Repr

/-- Allocate one metavariable per distinct local name, followed by one fresh
metavariable for each anonymous occurrence. Every call starts a new name table. -/
def Template.allocate (frontier : Nat) (template : Template) : Template.Allocation :=
  let keys := template.names.dedup
  let holes := namedHoleTable keys frontier
  let resolved := template.allocateWith holes (frontier + keys.length)
  ⟨resolved.1, resolved.2, holes⟩

end EPL

namespace EPL

def Ty.metaFreeB : Ty → Bool
  | .prim _ | .bvar _ | .rigid _ | .con _ => true
  | .arrow domain codomain => domain.metaFreeB && codomain.metaFreeB
  | .mvar _ => false
  | .app function argument => function.metaFreeB && argument.metaFreeB

def Ty.wfB (rigidCount binderCount : Nat) (ty : Ty) : Bool :=
  ty.scopedB rigidCount binderCount && ty.metaFreeB

def Template.scopedB (rigidCount binderCount : Nat) : Template → Bool
  | .fixed ty => ty.wfB rigidCount binderCount
  | .hole | .named _ => true
  | .arrow domain codomain =>
      domain.scopedB rigidCount binderCount &&
        codomain.scopedB rigidCount binderCount
  | .app function argument =>
      function.scopedB rigidCount binderCount &&
        argument.scopedB rigidCount binderCount

def Expr.typeScopedB (rigidCount binderCount : Nat) : Source → Bool
  | .primLit _ | .primOp _ | .var _ | .const _ => true
  | .lambda ann body =>
      ann.all (Template.scopedB rigidCount binderCount) &&
        body.typeScopedB rigidCount binderCount
  | .app function argument =>
      function.typeScopedB rigidCount binderCount &&
        argument.typeScopedB rigidCount binderCount
  | .letIn none rhs body =>
      rhs.typeScopedB rigidCount binderCount &&
        body.typeScopedB rigidCount binderCount
  | .letIn (some written) rhs body =>
      written.body.scopedB rigidCount (binderCount + written.paramCount) &&
        rhs.typeScopedB rigidCount (binderCount + written.paramCount) &&
        body.typeScopedB rigidCount binderCount
  | .fix ann body =>
      ann.scopedB rigidCount binderCount &&
        body.typeScopedB rigidCount binderCount

def Ty.mvarsBelow (cutoff : Nat) (ty : Ty) : Bool :=
  ty.mvars.all (· < cutoff)

def PolyTy.wfB (rigidCount : Nat) (scheme : PolyTy) : Bool :=
  scheme.body.scopedB rigidCount scheme.paramCount && scheme.body.metaFreeB

/-- Close one contiguous rigid block back into scheme-bound variables. Rigid
levels above the removed block shift down. -/
def Ty.closeRigids (base count : Nat) : Ty → Ty
  | .prim p => .prim p
  | .arrow domain codomain =>
      .arrow (domain.closeRigids base count) (codomain.closeRigids base count)
  | .bvar index => .bvar index
  | .rigid level =>
      if level < base then .rigid level
      else if level - base < count then .bvar (level - base)
      else .rigid (level - count)
  | .mvar id => .mvar id
  | .con id => .con id
  | .app function argument =>
      .app (function.closeRigids base count) (argument.closeRigids base count)

structure InferState where
  next : Nat
  solutions : MStore
  deriving Repr

/-- Resolve every annotation of an elaborated expression through the store. -/
def MStore.applyExpr (store : MStore) (expr : Expr Ty) : Expr Ty :=
  expr.mapAnn store.apply

/-- The internal result: the type and the elaboration may still mention
metavariables, to be resolved by later constraints. -/
structure InferResult where
  state : InferState
  ty : Ty
  elaborated : Expr Ty
  deriving Repr

/-- A successful public result: a closed type and the source program with
every implicit type filled in. -/
structure InferenceResult where
  ty : Ty
  elaborated : Expr Ty
  deriving DecidableEq, Repr

/-- Allocate an unsolved metavariable at `level`. -/
def InferState.fresh (state : InferState) (level : Nat) : InferState × Ty :=
  ({ next := state.next + 1
     solutions := state.solutions ++ [⟨level, none⟩] },
    .mvar state.next)

def InferState.freshMany (level : Nat) : Nat → InferState → InferState × List Ty
  | 0, state => (state, [])
  | count + 1, state =>
      let first := state.fresh level
      let rest := freshMany level count first.1
      (rest.1, first.2 :: rest.2)

/-- Resolve a template's holes to fresh metavariables at `level`. -/
def InferState.allocate (state : InferState) (level : Nat) (template : Template) :
    InferState × Ty :=
  let allocation := template.allocate state.next
  ({ next := allocation.next
     solutions := state.solutions ++
       List.replicate (allocation.next - state.next) ⟨level, none⟩ },
    allocation.ty)

def InferState.constrain (state : InferState) (left right : Ty) : Option InferState :=
  (state.solutions.unify left right).map fun solutions => { state with solutions }

def Expr.inferSize : Source → Nat
  | .primLit _ | .primOp _ | .var _ | .const _ => 1
  | .lambda _ body | .fix _ body => body.inferSize + 1
  | .app function argument => function.inferSize + argument.inferSize + 1
  | .letIn _ rhs body => rhs.inferSize + body.inferSize + 1

/-- Infer a type and an elaboration. `fuel` bounds the recursion depth;
`input.inferSize + 1` is always enough, since opening a scheme's rigid
variables does not change an expression's size. -/
def inferFuel (sig : Signature) : Nat → Nat → Ctx → Source → InferState → Option InferResult
  | 0, _, _, _, _ => none
  | fuel + 1, rigidCount, ctx, input, state =>
      match input with
      | .primLit literal => some ⟨state, literal.ty, .primLit literal⟩
      | .primOp op => some ⟨state, op.ty, .primOp op⟩
      | .var index => do
          let scheme ← ctx[index]?
          let scheme := state.solutions.applyScheme scheme
          let fresh := state.freshMany rigidCount scheme.paramCount
          some ⟨fresh.1, scheme.openWith fresh.2, .var index⟩
      | .lambda ann body => do
          let seeded := match ann with
            | none => state.fresh rigidCount
            | some template => state.allocate rigidCount template
          let bodyResult ← inferFuel sig fuel rigidCount
            (PolyTy.mono seeded.2 :: ctx) body seeded.1
          let paramTy := bodyResult.state.solutions.apply seeded.2
          some ⟨bodyResult.state, .arrow paramTy bodyResult.ty,
            .lambda (some seeded.2) bodyResult.elaborated⟩
      | .app function argument => do
          let functionResult ← inferFuel sig fuel rigidCount ctx function state
          let argumentResult ← inferFuel sig fuel rigidCount ctx argument functionResult.state
          let fresh := argumentResult.state.fresh rigidCount
          let checked ← fresh.1.constrain functionResult.ty
            (.arrow argumentResult.ty fresh.2)
          some ⟨checked, checked.solutions.apply fresh.2,
            .app functionResult.elaborated argumentResult.elaborated⟩
      | .letIn none rhs body => do
          let rhsResult ← inferFuel sig fuel rigidCount ctx rhs state
          let rhsTy := rhsResult.state.solutions.apply rhsResult.ty
          let bodyResult ← inferFuel sig fuel rigidCount
            (PolyTy.mono rhsTy :: ctx) body rhsResult.state
          some ⟨bodyResult.state, bodyResult.ty,
            .letIn none rhsResult.elaborated bodyResult.elaborated⟩
      | .letIn (some written) rhs body => do
          -- Check the right-hand side generically, at a fresh block of rigid
          -- levels standing for the scheme's binders. The template's holes
          -- live at the inner level, since they may mention those binders.
          let count := written.paramCount
          let inner := rigidCount + count
          let openedTemplate := written.body.openRigidsFrom 0 rigidCount count
          let seeded := state.allocate inner openedTemplate
          let rhsResult ← inferFuel sig fuel inner ctx
            (rhs.openRigids rigidCount count) seeded.1
          let checked ← rhsResult.state.constrain rhsResult.ty seeded.2
          let completedOpen := checked.solutions.apply seeded.2
          -- An unknown still at the inner level is undetermined by the
          -- definition and its context: it could equally be a binder.
          if !(completedOpen.mvars.all fun id =>
              checked.solutions.levelOf id ≤ rigidCount) then none
          else
            let completed : PolyTy :=
              ⟨count, completedOpen.closeRigids rigidCount count⟩
            let bodyResult ← inferFuel sig fuel rigidCount (completed :: ctx) body checked
            some ⟨bodyResult.state, bodyResult.ty,
              .letIn (some completed) rhsResult.elaborated bodyResult.elaborated⟩
      | .fix ann body => do
          let seeded := state.allocate rigidCount ann
          let bodyResult ← inferFuel sig fuel rigidCount
            (PolyTy.mono seeded.2 :: ctx) body seeded.1
          let checked ← bodyResult.state.constrain bodyResult.ty seeded.2
          some ⟨checked, checked.solutions.apply seeded.2,
            .fix seeded.2 bodyResult.elaborated⟩
      | .const c => do
          let scheme ← sig.schemeOf c
          if !scheme.wfB 0 then none
          let fresh := state.freshMany rigidCount scheme.paramCount
          some ⟨fresh.1, scheme.openWith fresh.2, .const c⟩

/-- Infer a closed program. It is accepted exactly when its type and every
implicit type in its elaboration are fully determined. -/
def infer (sig : Signature) (input : Source) : Option InferenceResult := do
  if !input.typeScopedB 0 0 then none
  let result ← inferFuel sig (input.inferSize + 1) 0 [] input ⟨0, []⟩
  let ty := result.state.solutions.apply result.ty
  let elaborated := result.state.solutions.applyExpr result.elaborated
  if ty.wfB 0 0 && elaborated.annotations.all Ty.metaFreeB then
    some ⟨ty, elaborated⟩
  else none

end EPL
