import EPL.Core

/-!
# Unification against the metavariable store

Inference keeps one dense table of metavariables, `MStore`. Entry `i` records
`?i`'s *level* and, once solved, its solution.

The level is the number of rigid variables in scope where `?i` lives: `?i`
may only be solved to a type whose rigid variables are below its level. An
unknown created while checking an explicit scheme starts at the scheme's
inner rigid count; as soon as it becomes part of an outer unknown's solution
its level is lowered to that unknown's level (Rémy-style levels, as in OCaml).
This is how rigid variables are kept from escaping their scheme, and how
inference recognises scheme holes that the scheme's own definition leaves
undetermined.

Solved entries are kept *normalized*: they never mention a solved
metavariable (`MStore.Normalized`). Resolving a type is therefore a single
lookup per metavariable, with no chains to follow and no possibility of
cycles.

Unification is Robinson's algorithm with the store as its solved form. Each
constraint is kept resolved through the current store. Binding `?id := ty`
writes the solution into the store, eliminates `?id` from every other
solution and from the remaining constraints, and lowers the levels of the
metavariables of `ty`.

Recursion is structural, so `decide` can evaluate unification, and the fuel is
provably sufficient rather than a heuristic budget:

* `unifyPhase` runs until the first new binding. Every step that does not bind
  shrinks `Constraints.size`, so that size is enough fuel
  (`unifyPhase_ne_outOfFuel`).
* `unifyLoop` runs phases. Each phase that binds solves one previously unsolved
  metavariable, so `store.unsolved + 1` phases are enough
  (`unifyPhase_bound_unsolved_lt`).
-/

namespace EPL

/-- One metavariable: its level and, once solved, its solution. -/
structure MEntry where
  level : Nat
  solution : Option Ty
  deriving DecidableEq, Repr

/-- The dense metavariable table; `?i` is entry `i`. -/
abbrev MStore := List MEntry

/-- The current solution of `?id`, if allocated and solved. -/
def MStore.lookup (store : MStore) (id : Nat) : Option Ty :=
  (store[id]?).bind (·.solution)

/-- The level of `?id` (0 if unallocated). -/
def MStore.levelOf (store : MStore) (id : Nat) : Nat :=
  ((store[id]?).map (·.level)).getD 0

/-- Resolve every solved metavariable in a type. -/
def MStore.apply (store : MStore) : Ty → Ty
  | .prim p => .prim p
  | .arrow domain codomain =>
      .arrow (store.apply domain) (store.apply codomain)
  | .bvar index => .bvar index
  | .rigid level => .rigid level
  | .mvar id => (store.lookup id).getD (.mvar id)
  | .con id => .con id
  | .app function argument => .app (store.apply function) (store.apply argument)

def MStore.applyScheme (store : MStore) (scheme : PolyTy) : PolyTy :=
  ⟨scheme.paramCount, store.apply scheme.body⟩

/-- The number of allocated but unsolved metavariables. -/
def MStore.unsolved (store : MStore) : Nat :=
  store.countP (·.solution.isNone)

/-- Executable scoping: bound and rigid variables are in range;
metavariables may occur. -/
def Ty.scopedB (rigidCount binderCount : Nat) : Ty → Bool
  | .prim _ => true
  | .arrow domain codomain =>
      domain.scopedB rigidCount binderCount &&
        codomain.scopedB rigidCount binderCount
  | .bvar index => index < binderCount
  | .rigid level => level < rigidCount
  | .mvar _ => true
  | .con _ => true
  | .app function argument =>
      function.scopedB rigidCount binderCount &&
        argument.scopedB rigidCount binderCount

def Ty.substMVar (ty : Ty) (target : Nat) (replacement : Ty) : Ty :=
  match ty with
  | .prim p => .prim p
  | .arrow domain codomain =>
      .arrow (domain.substMVar target replacement)
        (codomain.substMVar target replacement)
  | .bvar index => .bvar index
  | .rigid level => .rigid level
  | .mvar id => if id = target then replacement else .mvar id
  | .con id => .con id
  | .app function argument =>
      .app (function.substMVar target replacement)
        (argument.substMVar target replacement)

def Ty.occursMVar (ty : Ty) (target : Nat) : Bool :=
  match ty with
  | .prim _ | .bvar _ | .rigid _ | .con _ => false
  | .arrow domain codomain =>
      domain.occursMVar target || codomain.occursMVar target
  | .mvar id => id == target
  | .app function argument =>
      function.occursMVar target || argument.occursMVar target

def Ty.size : Ty → Nat
  | .prim _ | .bvar _ | .rigid _ | .mvar _ | .con _ => 1
  | .arrow domain codomain => 1 + domain.size + codomain.size
  | .app function argument => 1 + function.size + argument.size

def Ty.mvars : Ty → List Nat
  | .prim _ | .bvar _ | .rigid _ | .con _ => []
  | .arrow domain codomain => (domain.mvars ++ codomain.mvars).dedup
  | .mvar id => [id]
  | .app function argument => (function.mvars ++ argument.mvars).dedup

/-- `?id` may be bound to `ty`: it is allocated and unsolved, `ty` does not
mention it, and `ty` only mentions rigid variables visible at its level. -/
def MStore.canBind (store : MStore) (id : Nat) (ty : Ty) : Bool :=
  match store[id]? with
  | some entry =>
      entry.solution.isNone && !ty.occursMVar id && ty.scopedB entry.level 0
  | none => false

/-- Record `?id := ty`, eliminate `?id` from every other solution, and lower
each metavariable of `ty` to `?id`'s level. -/
def MStore.solve (store : MStore) (id : Nat) (ty : Ty) : MStore :=
  let level := store.levelOf id
  store.mapIdx fun index entry =>
    if index = id then { entry with solution := some ty }
    else
      { level := if index ∈ ty.mvars then min entry.level level else entry.level
        solution := entry.solution.map (·.substMVar id ty) }

abbrev Constraint := Ty × Ty

def Constraint.substMVar (target : Nat) (replacement : Ty)
    (constraint : Constraint) : Constraint :=
  (constraint.1.substMVar target replacement,
    constraint.2.substMVar target replacement)

def Constraints.size (constraints : List Constraint) : Nat :=
  (constraints.map fun constraint =>
    constraint.1.size + constraint.2.size).sum

/-- How one unification phase ended. -/
inductive UnifyPhase where
  /-- Every constraint was discharged without a new binding. -/
  | finished (store : MStore)
  /-- One metavariable was bound; these constraints remain. -/
  | bound (store : MStore) (rest : List Constraint)
  | failed
  | outOfFuel

/-- Simplify resolved constraints until one binds an unsolved metavariable
(subject to `MStore.canBind`). Rigid and bound variables are never bound. -/
def unifyPhase (store : MStore) : Nat → List Constraint → UnifyPhase
  | _, [] => .finished store
  | 0, _ :: _ => .outOfFuel
  | fuel + 1, (left, right) :: rest =>
      if left = right then unifyPhase store fuel rest
      else
        match left, right with
        | .mvar id, ty | ty, .mvar id =>
            if store.canBind id ty then
              .bound (store.solve id ty) (rest.map (Constraint.substMVar id ty))
            else .failed
        | .arrow leftDomain leftCodomain, .arrow rightDomain rightCodomain =>
            unifyPhase store fuel
              ((leftDomain, rightDomain) :: (leftCodomain, rightCodomain) :: rest)
        | .app leftFunction leftArgument, .app rightFunction rightArgument =>
            unifyPhase store fuel
              ((leftFunction, rightFunction) :: (leftArgument, rightArgument) :: rest)
        | _, _ => .failed

/-- Run phases until all constraints are discharged. -/
def unifyLoop : Nat → MStore → List Constraint → Option MStore
  | 0, _, _ => none
  | fuel + 1, store, constraints =>
      match unifyPhase store (Constraints.size constraints) constraints with
      | .finished store => some store
      | .bound store rest => unifyLoop fuel store rest
      | .failed | .outOfFuel => none

/-- Extend the store so that `left` and `right` resolve to the same type. -/
def MStore.unify (store : MStore) (left right : Ty) : Option MStore :=
  unifyLoop (store.unsolved + 1) store [(store.apply left, store.apply right)]

end EPL
