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

namespace MStore

private theorem lt_of_getElem? {store : MStore} {id : Nat} {entry : MEntry}
    (h : store[id]? = some entry) : id < store.length := by
  by_contra hlt
  rw [List.getElem?_eq_none_iff.mpr (by omega)] at h
  simp at h

private theorem getElem?_of_lt {store : MStore} {id : Nat} (lt : id < store.length) :
    ∃ entry, store[id]? = some entry := by
  cases h : store[id]? with
  | none =>
      rw [List.getElem?_eq_none_iff] at h
      omega
  | some entry => exact ⟨entry, rfl⟩

private theorem levelOf_eq_of_getElem? {store : MStore} {id : Nat} {entry : MEntry}
    (h : store[id]? = some entry) : store.levelOf id = entry.level := by
  simp [MStore.levelOf, h]

private theorem lookup_some_getElem? {store : MStore} {id : Nat} {ty : InfTy}
    (h : store.lookup id = some ty) :
    ∃ entry, store[id]? = some entry ∧ entry.solution = some ty := by
  unfold MStore.lookup at h
  cases hg : store[id]? with
  | none => simp [hg] at h
  | some entry => exact ⟨entry, rfl, by simpa [hg] using h⟩

private theorem lookup_eq_none_of_getElem?_solution_none {store : MStore} {id : Nat}
    {entry : MEntry} (h : store[id]? = some entry) (sol : entry.solution = none) :
    store.lookup id = none := by
  simp [MStore.lookup, h, sol]

private theorem lookup_eq_some_of_getElem?_solution_some {store : MStore} {id : Nat}
    {entry : MEntry} {ty : InfTy} (h : store[id]? = some entry)
    (sol : entry.solution = some ty) : store.lookup id = some ty := by
  simp [MStore.lookup, h, sol]

private theorem lt_of_lookup_some {store : MStore} {id : Nat} {ty : InfTy}
    (h : store.lookup id = some ty) : id < store.length := by
  obtain ⟨entry, hget, _⟩ := lookup_some_getElem? h
  exact lt_of_getElem? hget

/-- Looking up an index of an extended store: either in the original store or
one of the appended unsolved entries. -/
private theorem getElem?_append_replicate {store : MStore} {count level id : Nat} :
    (store ++ List.replicate count (⟨level, none⟩ : MEntry))[id]? =
      if id < store.length then store[id]?
      else if id - store.length < count then some ⟨level, none⟩ else none := by
  rw [List.getElem?_append]
  by_cases h : id < store.length
  · rw [if_pos h, if_pos h]
  · rw [if_neg h, if_neg h, List.getElem?_replicate]

private theorem lookup_append_replicate {store : MStore} {count level id : Nat} :
    (store ++ List.replicate count (⟨level, none⟩ : MEntry)).lookup id =
      if id < store.length then store.lookup id else none := by
  unfold MStore.lookup
  rw [List.getElem?_append]
  by_cases h : id < store.length
  · rw [if_pos h, if_pos h]
  · rw [if_neg h, if_neg h, List.getElem?_replicate]
    split <;> simp

end MStore

theorem MStore.safe_nil : MStore.Safe [] := by
  refine ⟨?_, ?_, ?_⟩
  · intro id entry ty h; simp at h
  all_goals intro id ty h; unfold MStore.lookup at h; simp at h

/-! ## Valuations -/

theorem Ty.realize_lift (ty : SemTy) (valuation : Valuation) :
    (ty.lift : InfTy).realize valuation = ty := by
  rw [Ty.realize, Ty.lift_bind, Ty.lift_self]

theorem Ty.realize_congr {ty : InfTy} {first second : Valuation} {frontier : Nat}
    (allocated : ∀ id ∈ ty.vars, id < frontier) (agree : Agree frontier first second) :
    ty.realize first = ty.realize second := by
  unfold Ty.realize
  exact Ty.bind_congr fun id h => agree id (allocated id h)

/-- If two realizations coincide, the valuations agree on the type's
metavariables. -/
theorem Ty.realize_eq_vars {ty : InfTy} {first second : Valuation}
    (equal : ty.realize first = ty.realize second) : ∀ id ∈ ty.vars, first id = second id :=
  Ty.bind_eq_bind_vars equal

theorem Expr.realize_congr {expr : Expr InfTy} {first second : Valuation} {frontier : Nat}
    (allocated : ∀ ann ∈ expr.anns, ∀ id ∈ ann.vars, id < frontier)
    (agree : Agree frontier first second) : expr.realize first = expr.realize second := by
  unfold Expr.realize
  exact Expr.mapAnn_congr fun ann hann =>
    Ty.realize_congr (fun id hid => allocated ann hann id hid) agree

/-- If two realizations of an elaboration coincide, the valuations agree on
the metavariables of every annotation. -/
theorem Expr.realize_eq_vars {expr : Expr InfTy} {first second : Valuation}
    (equal : expr.realize first = expr.realize second) :
    ∀ ann ∈ expr.anns, ∀ id ∈ ann.vars, first id = second id := by
  unfold Expr.realize at equal
  intro ann hann id hid
  exact Ty.realize_eq_vars (Expr.mapAnn_eq_anns equal ann hann) id hid

theorem Ty.realize_wf {ty : InfTy} {valuation : Valuation} (wf : ty.WF k)
    (images : ∀ id ∈ ty.vars, (valuation id).WF k) : (ty.realize valuation).WF k := by
  unfold Ty.realize
  exact Ty.scoped_bind wf images

theorem MStore.Models.realize_apply {store : MStore} {valuation : Valuation}
    (models : store.Models valuation) (ty : InfTy) :
    (store.apply ty).realize valuation = ty.realize valuation := by
  unfold MStore.apply Ty.realize
  rw [Ty.bind_bind]
  apply Ty.bind_congr
  intro id _
  rcases h : store.lookup id with _ | sol
  · rfl
  · exact (models.equation id sol h).symm

/-- A metavariable of a resolved type comes from one of the original
metavariables, either unchanged (unsolved) or through its solution. -/
private theorem exists_of_mem_vars_apply {store : MStore} {ty : InfTy} {id : Nat}
    (h : id ∈ (store.apply ty).vars) :
    ∃ v ∈ ty.vars,
      (store.lookup v = none ∧ id = v) ∨
        ∃ sol, store.lookup v = some sol ∧ id ∈ sol.vars := by
  rw [MStore.apply, Ty.mem_vars_bind] at h
  obtain ⟨v, hv, hidv⟩ := h
  refine ⟨v, hv, ?_⟩
  cases hlookup : store.lookup v with
  | none => exact Or.inl ⟨rfl, by simpa [hlookup, Ty.vars] using hidv⟩
  | some sol => exact Or.inr ⟨sol, rfl, by simpa [hlookup] using hidv⟩

/-- Resolving keeps a type's scope and level, and leaves only unsolved,
allocated metavariables. -/
theorem MStore.apply_wf {store : MStore} {ty : InfTy} (safe : store.Safe) (wf : ty.WF k)
    (levels : ty.LevelBounded store k) :
    (store.apply ty).WF k ∧ (store.apply ty).LevelBounded store k := by
  constructor
  · rw [MStore.apply]
    apply Ty.scoped_bind wf
    intro id hid
    rcases h : store.lookup id with _ | sol
    · exact trivial
    · obtain ⟨entry, hget, hsol⟩ := MStore.lookup_some_getElem? h
      exact Ty.Scoped.mono (safe.leveled id entry sol hget hsol).1
        (by rw [← MStore.levelOf_eq_of_getElem? hget]; exact levels id hid) (Nat.zero_le 0)
  · intro id hid
    obtain ⟨v, hv, ⟨_, rfl⟩ | ⟨sol, hlookup, hidv⟩⟩ := exists_of_mem_vars_apply hid
    · exact levels id hv
    · obtain ⟨entry, hget, hsol⟩ := MStore.lookup_some_getElem? hlookup
      have hle : entry.level ≤ k := by
        rw [← MStore.levelOf_eq_of_getElem? hget]; exact levels v hv
      exact le_trans ((safe.leveled v entry sol hget hsol).2 id hidv) hle

theorem MStore.apply_allocated {store : MStore} {ty : InfTy} (safe : store.Safe)
    (allocated : ty.Allocated store) : (store.apply ty).Allocated store := by
  intro id hid
  obtain ⟨v, hv, ⟨_, rfl⟩ | ⟨sol, hlookup, hidv⟩⟩ := exists_of_mem_vars_apply hid
  · exact allocated id hv
  · exact safe.allocated v sol hlookup id hidv

theorem MStore.apply_vars_unsolved {store : MStore} {ty : InfTy} (safe : store.Safe) :
    ∀ id ∈ (store.apply ty).vars, store.lookup id = none := by
  intro id hid
  obtain ⟨v, _hv, ⟨hlookup, rfl⟩ | ⟨sol, hlookup, hidv⟩⟩ := exists_of_mem_vars_apply hid
  · exact hlookup
  · exact safe.normalized v sol hlookup id hidv

/-- A metavariable's image is well-formed at its level. -/
theorem MStore.Models.image_wf {store : MStore} {id : Nat} {valuation : Valuation}
    (models : store.Models valuation) (allocated : id < store.length) :
    (valuation id).WF (store.levelOf id) := by
  obtain ⟨entry, hget⟩ := MStore.getElem?_of_lt allocated
  have hlevel := MStore.levelOf_eq_of_getElem? hget
  rw [hlevel]
  exact models.wf id entry hget

/-- Models only see allocated metavariables. -/
theorem MStore.Models.congr {store : MStore} {first second : Valuation} (safe : store.Safe)
    (models : store.Models first) (agree : Agree store.length first second) :
    store.Models second := by
  refine ⟨?_, ?_⟩
  · intro id entry hget
    rw [← agree id (MStore.lt_of_getElem? hget)]
    exact models.wf id entry hget
  · intro id ty lookup
    rw [← agree id (MStore.lt_of_lookup_some lookup), models.equation id ty lookup]
    exact Ty.realize_congr (fun m hm => safe.allocated id ty lookup m hm) agree

/-- Appending unsolved metavariables at `level` adds exactly their
well-formedness constraints. (Covers `fresh`, `freshMany` and `allocate`.) -/
theorem MStore.models_append_unsolved {store : MStore} {valuation : Valuation} :
    (store ++ List.replicate count (⟨level, none⟩ : MEntry)).Models valuation ↔
      store.Models valuation ∧ ∀ i < count, (valuation (store.length + i)).WF level := by
  constructor
  · intro models
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · intro id entry hget
      exact models.wf id entry
        (by rwa [MStore.getElem?_append_replicate, if_pos (MStore.lt_of_getElem? hget)])
    · intro id ty lookup
      exact models.equation id ty
        (by rwa [MStore.lookup_append_replicate, if_pos (MStore.lt_of_lookup_some lookup)])
    · intro i hi
      have hget : (store ++ List.replicate count (⟨level, none⟩ : MEntry))[store.length + i]? =
          some (⟨level, none⟩ : MEntry) := by
        rw [List.getElem?_append_right (by omega), List.getElem?_replicate, if_pos (by omega)]
      exact models.wf (store.length + i) ⟨level, none⟩ hget
  · intro ⟨models, freshWF⟩
    refine ⟨?_, ?_⟩
    · intro id entry hget
      by_cases hlt : id < store.length
      · have hstore : store[id]? = some entry := by
          rwa [MStore.getElem?_append_replicate, if_pos hlt] at hget
        exact models.wf id entry hstore
      · have hidx : id - store.length < count := by
          by_contra hcount
          rw [MStore.getElem?_append_replicate, if_neg hlt, if_neg hcount] at hget
          simp at hget
        have hsample : (store ++ List.replicate count (⟨level, none⟩ : MEntry))[id]? =
            some (⟨level, none⟩ : MEntry) := by
          rw [MStore.getElem?_append_replicate, if_neg hlt, if_pos hidx]
        rw [hsample] at hget
        cases hget
        have hidEq : id = store.length + (id - store.length) := by omega
        rw [hidEq]
        exact freshWF (id - store.length) hidx
    · intro id ty lookup
      have hlt : id < store.length := by
        by_contra hlt
        rw [MStore.lookup_append_replicate, if_neg hlt] at lookup
        simp at lookup
      have hstore : store.lookup id = some ty := by
        rwa [MStore.lookup_append_replicate, if_pos hlt] at lookup
      exact models.equation id ty hstore

/-- Every safe store has a model: map each unsolved metavariable to `Unit`. -/
theorem MStore.has_model {store : MStore} (safe : store.Safe) : ∃ valuation, store.Models valuation := by
  let valuation : Valuation := fun id =>
    match store.lookup id with
    | some sol => sol.bind fun _ => (.prim .unit : SemTy)
    | none => .prim .unit
  refine ⟨valuation, ?_, ?_⟩
  · intro id entry hget
    cases hsol : entry.solution with
    | none =>
        have hval : valuation id = .prim .unit := by
          simp [valuation, MStore.lookup_eq_none_of_getElem?_solution_none hget hsol]
        rw [hval]
        exact trivial
    | some sol =>
        have hval : valuation id = sol.bind (fun _ => (.prim .unit : SemTy)) := by
          simp [valuation, MStore.lookup_eq_some_of_getElem?_solution_some hget hsol]
        rw [hval]
        exact Ty.scoped_bind (safe.leveled id entry sol hget hsol).1 (fun _ _ => trivial)
  · intro id ty lookup
    have hval : valuation id = ty.bind (fun _ => (.prim .unit : SemTy)) := by
      simp [valuation, lookup]
    rw [hval]
    unfold Ty.realize
    apply Ty.bind_congr
    intro m hm
    simp [valuation, safe.normalized id ty lookup m hm]

/-- An unsolved metavariable can be given any type well-formed at its level;
the other unsolved metavariables keep their values. -/
theorem MStore.Models.reassign {store : MStore} {id : Nat} {valuation : Valuation} (safe : store.Safe)
    (models : store.Models valuation) (unsolved : store.lookup id = none)
    (wf : ty.WF (store.levelOf id)) :
    ∃ updated, store.Models updated ∧ updated id = ty ∧
      ∀ other, store.lookup other = none → other ≠ id → updated other = valuation other := by
  let base : Valuation := fun other => if other = id then ty else valuation other
  let updated : Valuation := fun other =>
    match store.lookup other with
    | some solution => solution.realize base
    | none => base other
  have updatedUnsolved : ∀ m, store.lookup m = none → updated m = base m := by
    intro m h
    dsimp only [updated]
    rw [h]
  have updatedSolved : ∀ {m : Nat} {solution : InfTy}, store.lookup m = some solution →
      updated m = solution.realize base := by
    intro m solution h
    dsimp only [updated]
    rw [h]
  refine ⟨updated, ?_, ?_, ?_⟩
  · constructor
    · intro m entry hget
      have hlevelEq : store.levelOf m = entry.level := MStore.levelOf_eq_of_getElem? hget
      cases hsol : entry.solution with
      | none =>
          have lookupNone := MStore.lookup_eq_none_of_getElem?_solution_none hget hsol
          rw [updatedUnsolved m lookupNone]
          dsimp only [base]
          by_cases same : m = id
          · rw [if_pos same, ← hlevelEq, same]
            exact wf
          · rw [if_neg same]
            exact models.wf m entry hget
      | some sol =>
          have lookupSome := MStore.lookup_eq_some_of_getElem?_solution_some hget hsol
          rw [updatedSolved lookupSome]
          obtain ⟨solWF, solLevels⟩ := safe.leveled m entry sol hget hsol
          apply Ty.realize_wf solWF
          intro u hu
          have uAlloc : u < store.length := safe.allocated m sol lookupSome u hu
          have uLevel : store.levelOf u ≤ entry.level := solLevels u hu
          dsimp only [base]
          by_cases same : u = id
          · rw [if_pos same]
            rw [same] at uLevel
            exact Ty.Scoped.mono wf uLevel (le_refl 0)
          · rw [if_neg same]
            exact Ty.Scoped.mono (models.image_wf uAlloc) uLevel (le_refl 0)
    · intro m solution lookupSome
      rw [updatedSolved lookupSome]
      unfold Ty.realize
      exact Ty.bind_congr
        (fun u hu => (updatedUnsolved u (safe.normalized m solution lookupSome u hu)).symm)
  · rw [updatedUnsolved id unsolved]
    dsimp only [base]
    rw [if_pos rfl]
  · intro other lookupNone different
    rw [updatedUnsolved other lookupNone]
    dsimp only [base]
    rw [if_neg different]

/-- An unsolved metavariable can always be given a different type. (One of
`Unit` and `Unit -> Unit` differs from its current value.) -/
theorem MStore.Models.exists_different {store : MStore} {id : Nat} {valuation : Valuation}
    (safe : store.Safe) (models : store.Models valuation) (unsolved : store.lookup id = none) :
    ∃ updated, store.Models updated ∧ updated id ≠ valuation id ∧
      ∀ other, store.lookup other = none → other ≠ id → updated other = valuation other := by
  let newTy : SemTy :=
    if valuation id = .prim .unit then .arrow (.prim .unit) (.prim .unit) else .prim .unit
  have hwf : newTy.WF (store.levelOf id) := by
    dsimp only [newTy]
    split
    · exact ⟨trivial, trivial⟩
    · exact trivial
  obtain ⟨updated, hmodels, hid, hagree⟩ :=
    MStore.Models.reassign (ty := newTy) safe models unsolved hwf
  refine ⟨updated, hmodels, ?_, hagree⟩
  rw [hid]
  by_cases h : valuation id = .prim .unit
  · simp [newTy, h]
  · simp only [newTy, if_neg h]
    exact fun heq => h heq.symm

/-- Two models agree on a solution once they agree on the unsolved
metavariables at or below `level`. -/
private theorem realize_solution_eq {store : MStore} {first second : Valuation}
    (safe : store.Safe) {id : Nat} {entry : MEntry} {solved : InfTy} {level : Nat}
    (hget : store[id]? = some entry) (hsol : entry.solution = some solved)
    (hlevel : store.levelOf id ≤ level)
    (agree : ∀ m, m < store.length → store.lookup m = none → store.levelOf m ≤ level →
      first m = second m) :
    solved.realize first = solved.realize second := by
  have lookupSome := MStore.lookup_eq_some_of_getElem?_solution_some hget hsol
  unfold Ty.realize
  apply Ty.bind_congr
  intro m hm
  have lookupNone := safe.normalized id solved lookupSome m hm
  have mBound := safe.allocated id solved lookupSome m hm
  have mLevel := (safe.leveled id entry solved hget hsol).2 m hm
  rw [MStore.levelOf_eq_of_getElem? hget] at hlevel
  exact agree m mBound lookupNone (le_trans mLevel hlevel)

/-- Models agree at a metavariable whose solution lives at or below `level`,
given agreement on the unsolved metavariables there. -/
private theorem agree_of_lookup {store : MStore} {first second : Valuation}
    (safe : store.Safe) (firstModels : store.Models first) (secondModels : store.Models second)
    {id level : Nat} {entry : MEntry} (hget : store[id]? = some entry)
    (hlevel : store.levelOf id ≤ level)
    (agree : ∀ m, m < store.length → store.lookup m = none → store.levelOf m ≤ level →
      first m = second m) :
    first id = second id := by
  cases hsol : entry.solution with
  | none =>
      have lookupNone := MStore.lookup_eq_none_of_getElem?_solution_none hget hsol
      exact agree id (MStore.lt_of_getElem? hget) lookupNone hlevel
  | some solved =>
      have lookupSome := MStore.lookup_eq_some_of_getElem?_solution_some hget hsol
      have firstEq := firstModels.equation id solved lookupSome
      have secondEq := secondModels.equation id solved lookupSome
      have realizeEq := realize_solution_eq safe hget hsol hlevel agree
      rw [firstEq, secondEq, realizeEq]

/-- Anchored metavariables are determined by the older ones: models that
agree before `start` agree on every metavariable at or below `level`. -/
theorem MStore.Anchored.agree {store : MStore} {first second : Valuation} (safe : store.Safe)
    (anchored : store.Anchored start level)
    (firstModels : store.Models first) (secondModels : store.Models second)
    (agree : Agree start first second) :
    ∀ id < store.length, store.levelOf id ≤ level → first id = second id := by
  have unsolvedAgree : ∀ id, id < store.length → store.lookup id = none →
      store.levelOf id ≤ level → first id = second id := by
    intro id hid lookupNone hlevel
    by_cases below : id < start
    · exact agree id below
    · obtain ⟨outer, ty, outerLt, outerLookup, idMem⟩ :=
        anchored id (by omega) hid hlevel lookupNone
      have firstOuter := firstModels.equation outer ty outerLookup
      have secondOuter := secondModels.equation outer ty outerLookup
      have realizeEq : ty.realize first = ty.realize second := by
        rw [← firstOuter, ← secondOuter, agree outer outerLt]
      exact Ty.realize_eq_vars realizeEq id idMem
  intro id hid hlevel
  cases hget : store[id]? with
  | none =>
      rw [List.getElem?_eq_none_iff] at hget
      omega
  | some entry => exact agree_of_lookup safe firstModels secondModels hget hlevel unsolvedAgree

/-- Models that agree on the unsolved metavariables at or below `level` agree
on every metavariable at or below `level`: a solution mentions only unsolved
metavariables at or below its own level. -/
theorem MStore.Models.agree_below {store : MStore} {first second : Valuation} (safe : store.Safe)
    (firstModels : store.Models first) (secondModels : store.Models second)
    (agree : ∀ id, store.lookup id = none → store.levelOf id ≤ level → first id = second id) :
    ∀ id, store.levelOf id ≤ level → first id = second id := by
  intro id hlevel
  cases hget : store[id]? with
  | none => exact agree id (by simp [MStore.lookup, hget]) hlevel
  | some entry =>
      exact agree_of_lookup safe firstModels secondModels hget hlevel (fun m _ => agree m)

end EPL2
