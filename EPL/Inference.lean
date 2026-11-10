import EPL.AnnotationAllocation
import EPL.Typing

namespace EPL

def Ty.scopedB (rigidCount binderCount : Nat) : Ty → Bool
  | .prim _ => true
  | .arrow domain codomain =>
      domain.scopedB rigidCount binderCount &&
        codomain.scopedB rigidCount binderCount
  | .bvar index => index < binderCount
  | .rigid level => level < rigidCount
  | .mvar _ => true

def Ty.metaFreeB : Ty → Bool
  | .prim _ | .bvar _ | .rigid _ => true
  | .arrow domain codomain => domain.metaFreeB && codomain.metaFreeB
  | .mvar _ => false

def Ty.wfB (rigidCount binderCount : Nat) (ty : Ty) : Bool :=
  ty.scopedB rigidCount binderCount && ty.metaFreeB

def Template.scopedB (rigidCount binderCount : Nat) : Template → Bool
  | .fixed ty => ty.wfB rigidCount binderCount
  | .hole | .named _ => true
  | .arrow domain codomain =>
      domain.scopedB rigidCount binderCount &&
        codomain.scopedB rigidCount binderCount

def Expr.typeScopedB (rigidCount binderCount : Nat) : Source → Bool
  | .primLit _ | .primOp _ | .var _ => true
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

/-- Keep solutions for older metavariables, normalize their images through the
whole local run, and discard bindings whose targets were allocated locally. -/
def MSubst.projectBelow (cutoff : Nat) (subst : MSubst) : MSubst :=
  subst.filterMap fun binding =>
    if binding.1 < cutoff then some (binding.1, subst.apply binding.2) else none

def MSubst.safeToLeave (rigidCount cutoff : Nat) (subst : MSubst) : Bool :=
  subst.all fun binding =>
    binding.2.scopedB rigidCount 0 && binding.2.mvarsBelow cutoff

structure InferState where
  next : Nat
  subst : MSubst
  required : List Nat
  deriving Repr

structure InferResult where
  state : InferState
  ty : Ty
  deriving Repr

structure InferenceResult where
  ty : Ty
  deriving Repr

/-- Every inference obligation still live at the public boundary has a closed
semantic solution. Ordinary scheme-instantiation metavariables need not be
solved when their binders are phantom; annotation holes and omitted lambda
parameter types do. Metavariables local to an explicit-scheme check are
removed, and its frontier restored, before inference continues. -/
def InferState.solvedB (rigidCount : Nat) (state : InferState) : Bool :=
  state.required.all fun id =>
    (state.subst.apply (.mvar id)).wfB rigidCount 0

def InferState.solvedFromB
    (rigidCount cutoff : Nat) (state : InferState) : Bool :=
  state.required.all fun id =>
    id < cutoff || (state.subst.apply (.mvar id)).wfB rigidCount 0

def InferState.fresh (state : InferState) : InferState × Ty :=
  ({ state with next := state.next + 1 }, .mvar state.next)

def InferState.freshRequired (state : InferState) : InferState × Ty :=
  ({ state with
      next := state.next + 1
      required := state.next :: state.required },
    .mvar state.next)

def InferState.freshMany : Nat → InferState → InferState × List Ty
  | 0, state => (state, [])
  | count + 1, state =>
      let first := state.fresh
      let rest := freshMany count first.1
      (rest.1, first.2 :: rest.2)

def InferState.allocate (state : InferState) (template : Template) : InferState × Ty :=
  let allocation := template.allocate state.next
  let required := List.range' state.next (allocation.next - state.next)
  ({ state with
      next := allocation.next
      required := required ++ state.required },
    allocation.ty)

def InferState.constrain (state : InferState) (left right : Ty) : Option InferState :=
  match unify (state.subst.apply left) (state.subst.apply right) with
  | none => none
  | some delta => some { state with subst := state.subst ++ delta }

def Expr.inferSize : Source → Nat
  | .primLit _ | .primOp _ | .var _ => 1
  | .lambda _ body | .fix _ body => body.inferSize + 1
  | .app function argument => function.inferSize + argument.inferSize + 1
  | .letIn _ rhs body => rhs.inferSize + body.inferSize + 1

mutual

def inferFuel : Nat → Nat → Ctx → Source → InferState → Option InferResult
  | 0, _, _, _, _ => none
  | fuel + 1, rigidCount, ctx, input, state =>
      match input with
      | .primLit literal => some ⟨state, literal.ty⟩
      | .primOp op => some ⟨state, op.ty⟩
      | .var index => do
          let scheme ← ctx[index]?
          let scheme := state.subst.applyScheme scheme
          let fresh := state.freshMany scheme.paramCount
          some ⟨fresh.1, scheme.openWith fresh.2⟩
      | .lambda ann body => do
          let seeded := match ann with
            | none => state.freshRequired
            | some template => state.allocate template
          let bodyResult ← inferFuel fuel rigidCount
            (PolyTy.mono seeded.2 :: ctx) body seeded.1
          let paramTy := bodyResult.state.subst.apply seeded.2
          some ⟨bodyResult.state, .arrow paramTy bodyResult.ty⟩
      | .app function argument => do
          let functionResult ← inferFuel fuel rigidCount ctx function state
          let argumentResult ← inferFuel fuel rigidCount ctx argument functionResult.state
          let fresh := argumentResult.state.fresh
          let checked ← fresh.1.constrain functionResult.ty
            (.arrow argumentResult.ty fresh.2)
          some ⟨checked, checked.subst.apply fresh.2⟩
      | .letIn none rhs body => do
          let rhsResult ← inferFuel fuel rigidCount ctx rhs state
          let rhsTy := rhsResult.state.subst.apply rhsResult.ty
          inferFuel fuel rigidCount (PolyTy.mono rhsTy :: ctx) body rhsResult.state
      | .letIn (some written) rhs body => do
          let localStart := state.next
          let count := written.paramCount
          let openedTemplate := written.body.openRigidsFrom 0 rigidCount count
          let seeded := state.allocate openedTemplate
          let rhsResult ← inferFuel fuel (rigidCount + count) ctx
            (rhs.openRigids rigidCount count) seeded.1
          let checked ← rhsResult.state.constrain rhsResult.ty seeded.2
          let completedOpen := checked.subst.apply seeded.2
          if !completedOpen.metaFreeB || !completedOpen.scopedB (rigidCount + count) 0 then
            none
          else if !checked.solvedFromB (rigidCount + count) localStart then
            none
          else
            let completed : PolyTy :=
              ⟨count, completedOpen.closeRigids rigidCount count⟩
            if !completed.wfB rigidCount then none
            else
              let projected := checked.subst.projectBelow localStart
              if !projected.safeToLeave rigidCount localStart then none
              else
                let outerState : InferState :=
                  { next := localStart
                    subst := projected
                    required := checked.required.filter (· < localStart) }
                inferFuel fuel rigidCount (completed :: ctx) body outerState
      | .fix ann body => do
          let seeded := state.allocate ann
          let bodyResult ← inferFuel fuel rigidCount
            (PolyTy.mono seeded.2 :: ctx) body seeded.1
          let checked ← bodyResult.state.constrain bodyResult.ty seeded.2
          some ⟨checked, checked.subst.apply seeded.2⟩

end

def infer (input : Source) : Option InferenceResult := do
  if !input.typeScopedB 0 0 then none
  let result ← inferFuel (input.inferSize + 1) 0 [] input ⟨0, [], []⟩
  let ty := result.state.subst.apply result.ty
  if result.state.solvedB 0 && ty.wfB 0 0 then
    some ⟨ty⟩
  else none

end EPL
