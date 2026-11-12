import EPL.Core

/-!
# Unification against the metavariable store

Inference keeps one dense table of metavariable solutions, `MStore`. Entry `i`
is `none` while `?i` is unsolved and `some ty` once solved. Solved entries are
kept *normalized*: they never mention a solved metavariable
(`MStore.Normalized`). Resolving a type is therefore a single lookup per
metavariable, with no chains to follow and no possibility of cycles.

Unification is Robinson's algorithm with the store as its solved form. Each
constraint is kept resolved through the current store. Binding `?id := ty`
writes the solution into the store and eliminates `?id` from every other
solution and from the remaining constraints.

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

/-- The dense metavariable solution table. -/
abbrev MStore := List (Option Ty)

/-- The current solution of `?id`, if allocated and solved. -/
def MStore.lookup (store : MStore) (id : Nat) : Option Ty :=
  (store[id]?).join

/-- Resolve every solved metavariable in a type. -/
def MStore.apply (store : MStore) : Ty → Ty
  | .prim p => .prim p
  | .arrow domain codomain =>
      .arrow (store.apply domain) (store.apply codomain)
  | .bvar index => .bvar index
  | .rigid level => .rigid level
  | .mvar id => (store.lookup id).getD (.mvar id)

def MStore.applyScheme (store : MStore) (scheme : PolyTy) : PolyTy :=
  ⟨scheme.paramCount, store.apply scheme.body⟩

/-- The number of allocated but unsolved metavariables. -/
def MStore.unsolved (store : MStore) : Nat :=
  store.countP (·.isNone)

def Ty.substMVar (ty : Ty) (target : Nat) (replacement : Ty) : Ty :=
  match ty with
  | .prim p => .prim p
  | .arrow domain codomain =>
      .arrow (domain.substMVar target replacement)
        (codomain.substMVar target replacement)
  | .bvar index => .bvar index
  | .rigid level => .rigid level
  | .mvar id => if id = target then replacement else .mvar id

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

/-- Record `?id := ty` and eliminate `?id` from every other solution. -/
def MStore.solve (store : MStore) (id : Nat) (ty : Ty) : MStore :=
  (store.map (Option.map (·.substMVar id ty))).set id (some ty)

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

/-- Simplify resolved constraints until one binds an unsolved metavariable.
A metavariable may be bound only if it is allocated, unsolved, and passes the
occurs check. Rigid and bound variables are never bound. -/
def unifyPhase (store : MStore) : Nat → List Constraint → UnifyPhase
  | _, [] => .finished store
  | 0, _ :: _ => .outOfFuel
  | fuel + 1, (left, right) :: rest =>
      if left = right then unifyPhase store fuel rest
      else
        match left, right with
        | .mvar id, ty | ty, .mvar id =>
            if store[id]? = some none ∧ ty.occursMVar id = false then
              .bound (store.solve id ty) (rest.map (Constraint.substMVar id ty))
            else .failed
        | .arrow leftDomain leftCodomain, .arrow rightDomain rightCodomain =>
            unifyPhase store fuel
              ((leftDomain, rightDomain) :: (leftCodomain, rightCodomain) :: rest)
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
