import EPL.Core

namespace EPL

/-- Ordered metavariable substitutions. Applying the list left-to-right makes
`older ++ newer` the composition that first applies `older`, then `newer`. -/
abbrev MSubst := List (Nat × Ty)

def Ty.substMVar (ty : Ty) (target : Nat) (replacement : Ty) : Ty :=
  match ty with
  | .prim p => .prim p
  | .arrow domain codomain =>
      .arrow (domain.substMVar target replacement)
        (codomain.substMVar target replacement)
  | .bvar index => .bvar index
  | .rigid level => .rigid level
  | .mvar id => if id = target then replacement else .mvar id

def MSubst.apply (subst : MSubst) (ty : Ty) : Ty :=
  subst.foldl (fun current binding =>
    current.substMVar binding.1 binding.2) ty

def MSubst.applyScheme (subst : MSubst) (scheme : PolyTy) : PolyTy :=
  ⟨scheme.paramCount, subst.apply scheme.body⟩

def MSubst.applyCtx (subst : MSubst) (ctx : Ctx) : Ctx :=
  ctx.map subst.applyScheme

def Ty.occursMVar (ty : Ty) (target : Nat) : Bool :=
  match ty with
  | .prim _ | .bvar _ | .rigid _ => false
  | .arrow domain codomain =>
      domain.occursMVar target || codomain.occursMVar target
  | .mvar id => id == target

def Ty.size : Ty → Nat
  | .prim _ | .bvar _ | .rigid _ | .mvar _ => 1
  | .arrow domain codomain => 1 + domain.size + codomain.size

def Ty.mvars : Ty → List Nat
  | .prim _ | .bvar _ | .rigid _ => []
  | .arrow domain codomain => (domain.mvars ++ codomain.mvars).dedup
  | .mvar id => [id]

abbrev Constraint := Ty × Ty

def MSubst.Solves (subst : MSubst) (constraints : List Constraint) : Prop :=
  ∀ constraint ∈ constraints,
    subst.apply constraint.1 = subst.apply constraint.2

def MSubst.Scoped (rigidCount : Nat) (subst : MSubst) : Prop :=
  ∀ binding ∈ subst, binding.2.Scoped rigidCount 0

/-- Applying a reachable substitution twice has no further effect. Public
unification begins from `[]` and preserves this invariant; arbitrary preloaded
association lists are not assumed stable. -/
def MSubst.Stable (subst : MSubst) : Prop :=
  ∀ ty, subst.apply (subst.apply ty) = subst.apply ty

def Constraints.Scoped (rigidCount : Nat)
    (constraints : List Constraint) : Prop :=
  ∀ constraint ∈ constraints,
    constraint.1.Scoped rigidCount 0 ∧ constraint.2.Scoped rigidCount 0

/-- Sound but deliberately fuelled first-order unification. Exhausting fuel is
ordinary rejection: EPL initially claims soundness, not inference completeness.

Every constraint is normalized by the accumulated substitution. A flexible
metavariable may be bound only when the occurs check succeeds. Bound variables,
rigid variables, primitives, and arrows are never mistaken for flexible
metavariables. -/
def unifyFuel : Nat → List Constraint → MSubst → Option MSubst
  | 0, [], subst => some subst
  | 0, _ :: _, _ => none
  | _ + 1, [], subst => some subst
  | fuel + 1, (left, right) :: rest, subst =>
      let left := subst.apply left
      let right := subst.apply right
      if left = right then
        unifyFuel fuel rest subst
      else
        match left, right with
        | .mvar id, ty | ty, .mvar id =>
            if ty.occursMVar id then none
            else unifyFuel fuel rest (subst ++ [(id, ty)])
        | .arrow leftDomain leftCodomain, .arrow rightDomain rightCodomain =>
            unifyFuel fuel
              ((leftDomain, rightDomain) :: (leftCodomain, rightCodomain) :: rest)
              subst
        | _, _ => none

/-- A conservative deterministic budget. Failure from budget exhaustion is
allowed by the initial language contract. -/
def unifyBudget (left right : Ty) : Nat :=
  let structural := left.size + right.size + 1
  let flexible := (left.mvars ++ right.mvars).dedup.length + 1
  structural * flexible * 2

def unify (left right : Ty) : Option MSubst :=
  unifyFuel (unifyBudget left right) [(left, right)] []

end EPL
