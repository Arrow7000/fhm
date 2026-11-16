import EPL2.Spec.Syntax
import EPL2.Unify

/-!
# The store: semantics and invariants

A *valuation* gives every metavariable a semantic type. It *models* a store
when it gives each allocated metavariable a type well-formed at that
metavariable's level and satisfies every solution. Everything inference
does is specified by how it changes the set of models.
-/

namespace EPL2

abbrev Valuation := Nat → SemTy

def Ty.realize (ty : InfTy) (valuation : Valuation) : SemTy := ty.bind valuation

def Scheme.realize (scheme : Scheme Nat) (valuation : Valuation) : Scheme Empty :=
  scheme.bind valuation

def Ctx.realize (ctx : Ctx Nat) (valuation : Valuation) : Ctx Empty :=
  ctx.map (·.realize valuation)

def Expr.realize (expr : Expr InfTy) (valuation : Valuation) : Elab :=
  expr.mapAnn (·.realize valuation)

/-- Two valuations agree on the metavariables allocated before `frontier`. -/
def Agree (frontier : Nat) (first second : Valuation) : Prop :=
  ∀ id < frontier, first id = second id

structure MStore.Models (store : MStore) (valuation : Valuation) : Prop where
  wf : ∀ (id : Nat) (entry : MEntry), store[id]? = some entry →
    (valuation id).WF entry.level
  equation : ∀ (id : Nat) (ty : InfTy), store.lookup id = some ty →
    valuation id = ty.realize valuation

/-- Every metavariable of `ty` is allocated. -/
def Ty.Allocated (store : MStore) (ty : InfTy) : Prop := ∀ id ∈ ty.vars, id < store.length

/-- Every metavariable of `ty` lives at or below `level`. -/
def Ty.LevelBounded (store : MStore) (level : Nat) (ty : InfTy) : Prop :=
  ∀ id ∈ ty.vars, store.levelOf id ≤ level

/-- The store's invariants. -/
structure MStore.Safe (store : MStore) : Prop where
  /-- A solution respects its metavariable's level: it mentions only rigid
  variables below it and only metavariables at or below it. -/
  leveled : ∀ (id : Nat) (entry : MEntry) (ty : InfTy), store[id]? = some entry →
    entry.solution = some ty →
    ty.WF entry.level ∧ ty.LevelBounded store entry.level
  /-- Solutions mention only allocated metavariables... -/
  allocated : ∀ (id : Nat) (ty : InfTy), store.lookup id = some ty → ty.Allocated store
  /-- ...which are unsolved. -/
  normalized : ∀ (id : Nat) (ty : InfTy), store.lookup id = some ty →
    ∀ m ∈ ty.vars, store.lookup m = none

/-- Every unsolved metavariable allocated from `start` on, at or below
`level`, occurs in the solution of a metavariable allocated before `start`.
(Inside an explicit let's right-hand side, at depth above `level`, every new
metavariable starts above `level`; it can only reach `level` by being unified
into an older metavariable's solution.) -/
def MStore.Anchored (store : MStore) (start level : Nat) : Prop :=
  ∀ id, start ≤ id → id < store.length → store.levelOf id ≤ level → store.lookup id = none →
    ∃ outer ty, outer < start ∧ store.lookup outer = some ty ∧ id ∈ ty.vars

theorem MStore.safe_nil : MStore.Safe [] := by
  sorry

/-! ## Valuations -/

theorem Ty.realize_lift (ty : SemTy) (valuation : Valuation) :
    (ty.lift : InfTy).realize valuation = ty := by
  sorry

theorem Ty.realize_congr {ty : InfTy} {first second : Valuation} {frontier : Nat}
    (allocated : ∀ id ∈ ty.vars, id < frontier) (agree : Agree frontier first second) :
    ty.realize first = ty.realize second := by
  sorry

/-- If two realizations coincide, the valuations agree on the type's
metavariables. -/
theorem Ty.realize_eq_vars {ty : InfTy} {first second : Valuation}
    (equal : ty.realize first = ty.realize second) : ∀ id ∈ ty.vars, first id = second id := by
  sorry

theorem Expr.realize_congr {expr : Expr InfTy} {first second : Valuation} {frontier : Nat}
    (allocated : ∀ ann ∈ expr.anns, ∀ id ∈ ann.vars, id < frontier)
    (agree : Agree frontier first second) : expr.realize first = expr.realize second := by
  sorry

/-- If two realizations of an elaboration coincide, the valuations agree on
the metavariables of every annotation. -/
theorem Expr.realize_eq_vars {expr : Expr InfTy} {first second : Valuation}
    (equal : expr.realize first = expr.realize second) :
    ∀ ann ∈ expr.anns, ∀ id ∈ ann.vars, first id = second id := by
  sorry

theorem Ty.realize_wf {ty : InfTy} {valuation : Valuation} (wf : ty.WF k)
    (images : ∀ id ∈ ty.vars, (valuation id).WF k) : (ty.realize valuation).WF k := by
  sorry

theorem MStore.Models.realize_apply {store : MStore} {valuation : Valuation}
    (models : store.Models valuation) (ty : InfTy) :
    (store.apply ty).realize valuation = ty.realize valuation := by
  sorry

/-- Resolving keeps a type's scope and level, and leaves only unsolved,
allocated metavariables. -/
theorem MStore.apply_wf {store : MStore} {ty : InfTy} (safe : store.Safe) (wf : ty.WF k)
    (levels : ty.LevelBounded store k) :
    (store.apply ty).WF k ∧ (store.apply ty).LevelBounded store k := by
  sorry

theorem MStore.apply_allocated {store : MStore} {ty : InfTy} (safe : store.Safe)
    (allocated : ty.Allocated store) : (store.apply ty).Allocated store := by
  sorry

theorem MStore.apply_vars_unsolved {store : MStore} {ty : InfTy} (safe : store.Safe) :
    ∀ id ∈ (store.apply ty).vars, store.lookup id = none := by
  sorry

/-- A metavariable's image is well-formed at its level. -/
theorem MStore.Models.image_wf {store : MStore} {id : Nat} {valuation : Valuation}
    (models : store.Models valuation) (allocated : id < store.length) :
    (valuation id).WF (store.levelOf id) := by
  sorry

/-- Models only see allocated metavariables. -/
theorem MStore.Models.congr {store : MStore} {first second : Valuation} (safe : store.Safe)
    (models : store.Models first) (agree : Agree store.length first second) :
    store.Models second := by
  sorry

/-- Appending unsolved metavariables at `level` adds exactly their
well-formedness constraints. (Covers `fresh`, `freshMany` and `allocate`.) -/
theorem MStore.models_append_unsolved {store : MStore} {valuation : Valuation} :
    (store ++ List.replicate count (⟨level, none⟩ : MEntry)).Models valuation ↔
      store.Models valuation ∧ ∀ i < count, (valuation (store.length + i)).WF level := by
  sorry

/-- Every safe store has a model: map each unsolved metavariable to `Unit`. -/
theorem MStore.has_model {store : MStore} (safe : store.Safe) : ∃ valuation, store.Models valuation := by
  sorry

/-- An unsolved metavariable can be given any type well-formed at its level;
the other unsolved metavariables keep their values. -/
theorem MStore.Models.reassign {store : MStore} {id : Nat} {valuation : Valuation} (safe : store.Safe)
    (models : store.Models valuation) (allocated : id < store.length)
    (unsolved : store.lookup id = none) (wf : ty.WF (store.levelOf id)) :
    ∃ updated, store.Models updated ∧ updated id = ty ∧
      ∀ other, store.lookup other = none → other ≠ id → updated other = valuation other := by
  sorry

/-- An unsolved metavariable can always be given a different type. (One of
`Unit` and `Unit -> Unit` differs from its current value.) -/
theorem MStore.Models.exists_different {store : MStore} {id : Nat} {valuation : Valuation}
    (safe : store.Safe) (models : store.Models valuation) (allocated : id < store.length)
    (unsolved : store.lookup id = none) :
    ∃ updated, store.Models updated ∧ updated id ≠ valuation id ∧
      ∀ other, store.lookup other = none → other ≠ id → updated other = valuation other := by
  sorry

/-- Anchored metavariables are determined by the older ones: models that
agree before `start` agree on every metavariable at or below `level`. -/
theorem MStore.Anchored.agree {store : MStore} {first second : Valuation} (safe : store.Safe)
    (anchored : store.Anchored start level)
    (firstModels : store.Models first) (secondModels : store.Models second)
    (agree : Agree start first second) :
    ∀ id < store.length, store.levelOf id ≤ level → first id = second id := by
  sorry

/-- Models that agree on the unsolved metavariables at or below `level` agree
on every metavariable at or below `level`: a solution mentions only unsolved
metavariables at or below its own level. -/
theorem MStore.Models.agree_below {store : MStore} {first second : Valuation} (safe : store.Safe)
    (firstModels : store.Models first) (secondModels : store.Models second)
    (agree : ∀ id, store.lookup id = none → store.levelOf id ≤ level → first id = second id) :
    ∀ id, store.levelOf id ≤ level → first id = second id := by
  sorry

end EPL2
