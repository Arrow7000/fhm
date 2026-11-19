import EPL.Syntax

/-!
# The metavariable store and unification

Inference keeps one dense table of metavariables, `MStore`: entry `i` holds
`?i`'s *level* and, once solved, its solution. A metavariable at level `L`
may only be solved to a type whose rigid variables are below `L`; binding it
lowers the metavariables of the solution to `L` (Rémy-style levels, as in
OCaml). This is the whole rigid-escape check.

Solutions are kept normalized (they mention only unsolved metavariables), so
resolving a type is one lookup per metavariable.

Unification is Robinson's algorithm with the store as its solved form. It
recurses structurally, so `decide` can evaluate it, with fuel that is proved
sufficient (`unifyPhase_ne_outOfFuel`, `unifyPhase_bound_unsolved_lt`): a
phase runs until its first binding, shrinking `Constraints.size` at every
other step; each binding solves one more metavariable. The fuel is internal:
`MStore.unify` takes none.
-/

namespace EPL

structure MEntry where
  level : Nat
  solution : Option InfTy
  deriving DecidableEq, Repr

/-- Entry `i` is metavariable `?i`. -/
abbrev MStore := List MEntry

def MStore.lookup (store : MStore) (id : Nat) : Option InfTy :=
  (store[id]?).bind (·.solution)

/-- `?id`'s level (0 if unallocated). -/
def MStore.levelOf (store : MStore) (id : Nat) : Nat :=
  ((store[id]?).map (·.level)).getD 0

/-- Resolve every solved metavariable. -/
def MStore.apply (store : MStore) (ty : InfTy) : InfTy :=
  ty.bind fun id => (store.lookup id).getD (.var id)

def MStore.unsolved (store : MStore) : Nat :=
  store.countP (·.solution.isNone)

/-- Replace `?target` by `replacement`. -/
def Ty.substVar (ty : InfTy) (target : Nat) (replacement : InfTy) : InfTy :=
  ty.bind fun id => if id = target then replacement else .var id

/-- `?id` may be bound to `ty`: allocated, unsolved, not occurring in `ty`, and
`ty`'s rigid variables are visible at `?id`'s level. -/
def MStore.canBind (store : MStore) (id : Nat) (ty : InfTy) : Bool :=
  match store[id]? with
  | some entry => entry.solution.isNone && !(ty.vars.contains id) && decide (ty.WF entry.level)
  | none => false

/-- Record `?id := ty`, eliminate `?id` from every other solution, and lower
each metavariable of `ty` to `?id`'s level. -/
def MStore.solve (store : MStore) (id : Nat) (ty : InfTy) : MStore :=
  let level := store.levelOf id
  store.mapIdx fun index entry =>
    if index = id then { entry with solution := some ty }
    else
      { level := if index ∈ ty.vars then min entry.level level else entry.level
        solution := entry.solution.map (·.substVar id ty) }

/-- Why two types do not unify. -/
inductive UnifyError where
  /-- Two types with different outermost forms, e.g. `Int` and `?a -> ?b`:
  the innermost such pair found. -/
  | clash (left right : InfTy)
  /-- `?id` occurs in `ty`: solving it would make an infinite type. -/
  | occurs (id : Nat) (ty : InfTy)
  /-- `ty` mentions a type variable not in scope at `?id`'s level. -/
  | escape (id : Nat) (ty : InfTy)
  /-- Unreachable: unification always has enough fuel
  (`MStore.unify_complete`). -/
  | outOfFuel
  deriving DecidableEq, Repr

/-- Why `?id` cannot be bound to `ty`, given that `MStore.canBind` refused. -/
def MStore.bindError (id : Nat) (ty : InfTy) : UnifyError :=
  if ty.vars.contains id then .occurs id ty else .escape id ty

abbrev Constraint := InfTy × InfTy

def Constraint.substVar (target : Nat) (replacement : InfTy) (constraint : Constraint) :
    Constraint :=
  (constraint.1.substVar target replacement, constraint.2.substVar target replacement)

def Constraints.size (constraints : List Constraint) : Nat :=
  (constraints.map fun constraint => constraint.1.size + constraint.2.size).sum

inductive UnifyPhase where
  /-- Every constraint was discharged without a new binding. -/
  | finished (store : MStore)
  /-- One metavariable was bound; these constraints remain. -/
  | bound (store : MStore) (rest : List Constraint)
  | failed (error : UnifyError)
  | outOfFuel

/-- Simplify resolved constraints until one binds an unsolved metavariable. -/
def unifyPhase (store : MStore) : Nat → List Constraint → UnifyPhase
  | _, [] => .finished store
  | 0, _ :: _ => .outOfFuel
  | fuel + 1, (left, right) :: rest =>
      if left = right then unifyPhase store fuel rest
      else
        match left, right with
        | .var id, ty | ty, .var id =>
            if store.canBind id ty then
              .bound (store.solve id ty) (rest.map (Constraint.substVar id ty))
            else .failed (MStore.bindError id ty)
        | .arrow leftDomain leftCodomain, .arrow rightDomain rightCodomain =>
            unifyPhase store fuel
              ((leftDomain, rightDomain) :: (leftCodomain, rightCodomain) :: rest)
        | .app leftFunction leftArgument, .app rightFunction rightArgument =>
            unifyPhase store fuel
              ((leftFunction, rightFunction) :: (leftArgument, rightArgument) :: rest)
        | _, _ => .failed (.clash left right)

def unifyLoop : Nat → MStore → List Constraint → Except UnifyError MStore
  | 0, _, _ => .error .outOfFuel
  | fuel + 1, store, constraints =>
      match unifyPhase store (Constraints.size constraints) constraints with
      | .finished store => .ok store
      | .bound store rest => unifyLoop fuel store rest
      | .failed error => .error error
      | .outOfFuel => .error .outOfFuel

/-- Extend the store so that `left` and `right` resolve to the same type, or
say why they cannot. -/
def MStore.unify (store : MStore) (left right : InfTy) : Except UnifyError MStore :=
  unifyLoop (store.unsolved + 1) store [(store.apply left, store.apply right)]

end EPL
