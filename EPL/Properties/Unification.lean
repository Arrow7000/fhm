import EPL.Unification

/-!
# Unification: invariants, soundness, and completeness

Store invariants are stated over solved entries and levels.

Semantics is given by valuations. A valuation `models` a store when it gives
every allocated metavariable a semantic type well-formed at its level and
satisfies every solution's equation. Soundness says every model of the result is a model
of the input that equates the two types. Completeness says the converse:
every model of the input that equates the two types is a model of the
result. Together they say the result's models are exactly the input's
unifying models, so `MStore.unify` computes a most general unifier.
-/

namespace EPL

/-- Every metavariable in a type was allocated below `frontier`. -/
def Ty.MVarBounded (frontier : Nat) (ty : Ty) : Prop :=
  ∀ id ∈ ty.mvars, id < frontier

/-- Every metavariable of `ty` lives at or below `level`. -/
def Ty.LevelBounded (store : MStore) (level : Nat) (ty : Ty) : Prop :=
  ∀ id ∈ ty.mvars, store.levelOf id ≤ level

/-- Every solution respects its metavariable's level: it mentions only rigid
variables below that level and only metavariables at or below it. -/
def MStore.Leveled (store : MStore) : Prop :=
  ∀ (id : Nat) (entry : MEntry) (ty : Ty), store[id]? = some entry →
    entry.solution = some ty →
    ty.Scoped entry.level 0 ∧ ty.LevelBounded store entry.level

def MStore.Bounded (store : MStore) (frontier : Nat) : Prop :=
  ∀ (id : Nat) (ty : Ty), store.lookup id = some ty → ty.MVarBounded frontier

/-- Solutions mention only unsolved metavariables. (In particular no
solution of `?id` is `?id` itself.) -/
def MStore.Normalized (store : MStore) : Prop :=
  ∀ (id : Nat) (ty : Ty), store.lookup id = some ty →
    ∀ m ∈ ty.mvars, store.lookup m = none

abbrev MValuation := Nat → Ty

/-- Interpret every inference metavariable through a valuation. The
valuation's images are required separately to be well-formed semantic
types. -/
def Ty.realize (valuation : MValuation) : Ty → Ty
  | .prim p => .prim p
  | .arrow domain codomain =>
      .arrow (domain.realize valuation) (codomain.realize valuation)
  | .bvar index => .bvar index
  | .rigid level => .rigid level
  | .mvar id => valuation id

def MValuation.WF
    (valuation : MValuation) (rigidCount frontier : Nat) : Prop :=
  ∀ id, id < frontier → (valuation id).WF rigidCount 0

/-- A valuation models a store when it gives every allocated metavariable a
semantic type well-formed at that metavariable's level and satisfies every
solution. -/
structure MStore.Models (store : MStore) (valuation : MValuation) : Prop where
  valuationWF : ∀ (id : Nat) (entry : MEntry), store[id]? = some entry →
    (valuation id).WF entry.level 0
  equation : ∀ (id : Nat) (ty : Ty), store.lookup id = some ty →
    valuation id = ty.realize valuation

/-! ## Elementary helpers -/

private theorem Ty.size_pos (ty : Ty) : 0 < ty.size := by
  cases ty <;> simp [Ty.size] <;> omega

private theorem Constraints.size_cons (constraint : Constraint)
    (rest : List Constraint) :
    Constraints.size (constraint :: rest) =
      constraint.1.size + constraint.2.size + Constraints.size rest := by
  simp [Constraints.size]

private theorem Constraints.size_tail (constraint : Constraint)
    (rest : List Constraint) :
    Constraints.size rest ≤ Constraints.size (constraint :: rest) := by
  rw [Constraints.size_cons]
  have left := Ty.size_pos constraint.1
  have right := Ty.size_pos constraint.2
  omega

private theorem Constraints.size_nonempty {constraints : List Constraint}
    (nonempty : constraints ≠ []) : 0 < Constraints.size constraints := by
  cases constraints with
  | nil => contradiction
  | cons constraint rest =>
      rw [Constraints.size_cons]
      have left := Ty.size_pos constraint.1
      have right := Ty.size_pos constraint.2
      omega

/-! ## Scoping helpers -/

private theorem Ty.scopedB_iff_scoped (ty : Ty) (rigidCount binderCount : Nat) :
    ty.scopedB rigidCount binderCount = true ↔ ty.Scoped rigidCount binderCount := by
  induction ty with
  | prim => exact ⟨fun _ => Ty.Scoped.prim, fun _ => rfl⟩
  | bvar index =>
      simp only [Ty.scopedB, decide_eq_true_eq]
      exact ⟨fun h => Ty.Scoped.bvar h, fun h => by cases h with | bvar h => exact h⟩
  | rigid level =>
      simp only [Ty.scopedB, decide_eq_true_eq]
      exact ⟨fun h => Ty.Scoped.rigid h, fun h => by cases h with | rigid h => exact h⟩
  | mvar id => exact ⟨fun _ => Ty.Scoped.mvar id, fun _ => rfl⟩
  | arrow domain codomain ihd ihc =>
      simp only [Ty.scopedB, Bool.and_eq_true, ihd, ihc]
      exact ⟨fun h => Ty.Scoped.arrow h.1 h.2,
        fun h => by cases h with | arrow hd hc => exact ⟨hd, hc⟩⟩

private theorem Ty.Scoped.mono {ty : Ty} {rigidCount rigidCount' binderCount : Nat}
    (h : ty.Scoped rigidCount binderCount) (le : rigidCount ≤ rigidCount') :
    ty.Scoped rigidCount' binderCount := by
  induction h with
  | prim => exact Ty.Scoped.prim
  | arrow _ _ ihd ihc => exact Ty.Scoped.arrow ihd ihc
  | bvar h => exact Ty.Scoped.bvar h
  | rigid h => exact Ty.Scoped.rigid (by omega)
  | mvar id => exact Ty.Scoped.mvar id

private theorem Ty.MVarBounded.left {frontier : Nat} {domain codomain : Ty}
    (bounded : (Ty.arrow domain codomain).MVarBounded frontier) :
    domain.MVarBounded frontier := by
  intro id member
  exact bounded id (by simp [Ty.mvars, List.mem_dedup, member])

private theorem Ty.MVarBounded.right {frontier : Nat} {domain codomain : Ty}
    (bounded : (Ty.arrow domain codomain).MVarBounded frontier) :
    codomain.MVarBounded frontier := by
  intro id member
  exact bounded id (by simp [Ty.mvars, List.mem_dedup, member])

private theorem Ty.substMVar_scoped {ty replacement : Ty}
    {rigidCount target : Nat}
    (typeScoped : ty.Scoped rigidCount 0)
    (replacementScoped : replacement.Scoped rigidCount 0) :
    (ty.substMVar target replacement).Scoped rigidCount 0 := by
  induction typeScoped with
  | prim => exact Ty.Scoped.prim
  | arrow _ _ domainIH codomainIH => exact Ty.Scoped.arrow domainIH codomainIH
  | bvar h => omega
  | rigid h => exact Ty.Scoped.rigid h
  | mvar id =>
      simp only [Ty.substMVar]
      split
      · exact replacementScoped
      · exact Ty.Scoped.mvar id

private theorem Ty.mem_mvars_substMVar {ty replacement : Ty}
    {target id : Nat}
    (member : id ∈ (ty.substMVar target replacement).mvars) :
    id ∈ ty.mvars ∨ id ∈ replacement.mvars := by
  induction ty with
  | prim => simp [Ty.substMVar, Ty.mvars] at member
  | bvar => simp [Ty.substMVar, Ty.mvars] at member
  | rigid => simp [Ty.substMVar, Ty.mvars] at member
  | arrow domain codomain domainIH codomainIH =>
      have split :
          id ∈ (domain.substMVar target replacement).mvars ∨
            id ∈ (codomain.substMVar target replacement).mvars := by
        simpa [Ty.substMVar, Ty.mvars, List.mem_dedup, List.mem_append] using member
      rcases split with inside | inside
      · rcases domainIH inside with old | new
        · exact Or.inl (by simp [Ty.mvars, List.mem_dedup, old])
        · exact Or.inr new
      · rcases codomainIH inside with old | new
        · exact Or.inl (by simp [Ty.mvars, List.mem_dedup, old])
        · exact Or.inr new
  | mvar id' =>
      by_cases selected : id' = target
      · simp [Ty.substMVar, selected] at member
        exact Or.inr member
      · simp [Ty.substMVar, selected, Ty.mvars] at member
        subst member
        exact Or.inl (by simp [Ty.mvars])

private theorem Ty.mem_mvars_substMVar' {ty replacement : Ty}
    {target id : Nat}
    (member : id ∈ (ty.substMVar target replacement).mvars) :
    (id ≠ target ∧ id ∈ ty.mvars) ∨ id ∈ replacement.mvars := by
  induction ty with
  | prim => simp [Ty.substMVar, Ty.mvars] at member
  | bvar => simp [Ty.substMVar, Ty.mvars] at member
  | rigid => simp [Ty.substMVar, Ty.mvars] at member
  | arrow domain codomain domainIH codomainIH =>
      have split :
          id ∈ (domain.substMVar target replacement).mvars ∨
            id ∈ (codomain.substMVar target replacement).mvars := by
        simpa [Ty.substMVar, Ty.mvars, List.mem_dedup, List.mem_append] using member
      rcases split with inside | inside
      · rcases domainIH inside with ⟨different, old⟩ | new
        · exact Or.inl ⟨different, by simp [Ty.mvars, List.mem_dedup, old]⟩
        · exact Or.inr new
      · rcases codomainIH inside with ⟨different, old⟩ | new
        · exact Or.inl ⟨different, by simp [Ty.mvars, List.mem_dedup, old]⟩
        · exact Or.inr new
  | mvar other =>
      by_cases selected : other = target
      · simp [Ty.substMVar, selected] at member
        exact Or.inr member
      · simp [Ty.substMVar, selected, Ty.mvars] at member
        subst member
        exact Or.inl ⟨selected, by simp [Ty.mvars]⟩

private theorem Ty.mem_mvars_substMVar_subset {previous replacement : Ty}
    {target id : Nat}
    (member : id ∈ (previous.substMVar target replacement).mvars) :
    id ∈ previous.mvars ∨ (target ∈ previous.mvars ∧ id ∈ replacement.mvars) := by
  induction previous with
  | prim => simp [Ty.substMVar, Ty.mvars] at member
  | bvar => simp [Ty.substMVar, Ty.mvars] at member
  | rigid => simp [Ty.substMVar, Ty.mvars] at member
  | mvar other =>
      by_cases same : other = target
      · subst same
        simp only [Ty.substMVar, Ty.mvars, List.mem_singleton] at member
        exact Or.inr ⟨by simp [Ty.mvars], member⟩
      · simp only [Ty.substMVar, if_neg same, Ty.mvars, List.mem_singleton] at member
        subst member
        exact Or.inl (by simp [Ty.mvars])
  | arrow domain codomain ihd ihc =>
      have split : id ∈ (domain.substMVar target replacement).mvars ∨
          id ∈ (codomain.substMVar target replacement).mvars := by
        simpa [Ty.substMVar, Ty.mvars, List.mem_dedup, List.mem_append] using member
      rcases split with inside | inside
      · rcases ihd inside with old | ⟨targetIn, replacementIn⟩
        · exact Or.inl (by simp [Ty.mvars, List.mem_dedup, old])
        · exact Or.inr ⟨by simp [Ty.mvars, List.mem_dedup, targetIn], replacementIn⟩
      · rcases ihc inside with old | ⟨targetIn, replacementIn⟩
        · exact Or.inl (by simp [Ty.mvars, List.mem_dedup, old])
        · exact Or.inr ⟨by simp [Ty.mvars, List.mem_dedup, targetIn], replacementIn⟩

private theorem Ty.substMVar_eq_self_of_not_mem {ty : Ty} {target : Nat} {replacement : Ty}
    (absent : target ∉ ty.mvars) :
    ty.substMVar target replacement = ty := by
  induction ty with
  | prim => rfl
  | bvar => rfl
  | rigid => rfl
  | mvar id =>
      by_cases same : id = target
      · subst same
        exact absurd (by simp [Ty.mvars]) absent
      · simp [Ty.substMVar, same]
  | arrow domain codomain ihd ihc =>
      simp only [Ty.mvars, List.mem_dedup, List.mem_append, not_or] at absent
      rw [Ty.substMVar, ihd absent.1, ihc absent.2]

private theorem Ty.substMVar_mvarBounded {ty replacement : Ty}
    {target frontier : Nat}
    (typeBounded : ty.MVarBounded frontier)
    (replacementBounded : replacement.MVarBounded frontier) :
    (ty.substMVar target replacement).MVarBounded frontier := by
  intro id member
  rcases Ty.mem_mvars_substMVar member with old | new
  · exact typeBounded id old
  · exact replacementBounded id new

private theorem Ty.occursMVar_iff_mem (ty : Ty) (id : Nat) :
    ty.occursMVar id = true ↔ id ∈ ty.mvars := by
  induction ty with
  | prim => simp [Ty.occursMVar, Ty.mvars]
  | bvar => simp [Ty.occursMVar, Ty.mvars]
  | rigid => simp [Ty.occursMVar, Ty.mvars]
  | arrow domain codomain domainIH codomainIH =>
      simp only [Ty.occursMVar, Ty.mvars, Bool.or_eq_true, List.mem_dedup,
        List.mem_append]
      rw [domainIH, codomainIH]
  | mvar other =>
      simp only [Ty.occursMVar, Ty.mvars, List.mem_singleton, beq_iff_eq]
      exact eq_comm

private theorem Ty.scoped_of_realize_scoped {ty : Ty} {valuation : MValuation} {level : Nat}
    (hscoped : (ty.realize valuation).Scoped level 0) :
    ty.Scoped level 0 := by
  induction ty with
  | prim => exact Ty.Scoped.prim
  | bvar index =>
      cases hscoped with
      | bvar h => exact absurd h (by omega)
  | rigid level' =>
      cases hscoped with
      | rigid h => exact Ty.Scoped.rigid h
  | mvar id => exact Ty.Scoped.mvar id
  | arrow domain codomain ihd ihc =>
      cases hscoped with
      | arrow hd hc => exact Ty.Scoped.arrow (ihd hd) (ihc hc)

/-! ## Solving: elementary structure -/

private theorem MStore.lookup_none_of_apply_mvar_eq {store : MStore}
    (norm : store.Normalized) {id : Nat}
    (equal : store.apply (.mvar id) = .mvar id) :
    store.lookup id = none := by
  cases lookupEq : store.lookup id with
  | none => rfl
  | some replacement =>
      have applied : store.apply (.mvar id) = replacement := by
        simp only [MStore.apply]
        rw [lookupEq]
        rfl
      have replacementEq : replacement = .mvar id := by
        rw [applied] at equal
        exact equal
      have member : id ∈ replacement.mvars := by
        rw [replacementEq]
        simp [Ty.mvars]
      have noneLookup := norm id replacement lookupEq id member
      rw [lookupEq] at noneLookup
      exact nomatch noneLookup

private theorem MStore.lookup_none_of_resolved {store : MStore} {ty : Ty}
    (norm : store.Normalized) (resolved : store.apply ty = ty)
    {id : Nat} (member : id ∈ ty.mvars) :
    store.lookup id = none := by
  induction ty with
  | prim => simp [Ty.mvars] at member
  | bvar => simp [Ty.mvars] at member
  | rigid => simp [Ty.mvars] at member
  | arrow domain codomain domainIH codomainIH =>
      have split : id ∈ domain.mvars ∨ id ∈ codomain.mvars := by
        simpa [Ty.mvars, List.mem_dedup, List.mem_append] using member
      have components : store.apply domain = domain ∧
          store.apply codomain = codomain := by
        simpa [MStore.apply] using resolved
      rcases split with inside | inside
      · exact domainIH components.1 inside
      · exact codomainIH components.2 inside
  | mvar other =>
      have same : id = other := by simpa [Ty.mvars] using member
      subst same
      exact MStore.lookup_none_of_apply_mvar_eq norm resolved

private theorem MStore.solve_getElem? (store : MStore) (id : Nat) (ty : Ty) (j : Nat) :
    (store.solve id ty)[j]? =
      (store[j]?).map (fun entry =>
        if j = id then { entry with solution := some ty }
        else
          { level := if j ∈ ty.mvars then min entry.level (store.levelOf id) else entry.level,
            solution := entry.solution.map (·.substMVar id ty) }) := by
  simp only [MStore.solve, List.getElem?_mapIdx]

private theorem MStore.solve_length (store : MStore) (id : Nat) (ty : Ty) :
    (store.solve id ty).length = store.length := by
  simp [MStore.solve]

private theorem MStore.lookup_solve_of_ne (store : MStore) (id j : Nat) (ty : Ty)
    (different : j ≠ id) :
    (store.solve id ty).lookup j =
      (store.lookup j).map (·.substMVar id ty) := by
  unfold MStore.lookup
  rw [MStore.solve_getElem?]
  cases h : store[j]? with
  | none => simp
  | some entry => simp [different, h]

private theorem MStore.lookup_solve_self (store : MStore) (id : Nat) (ty : Ty)
    {e : MEntry} (entry : store[id]? = some e) :
    (store.solve id ty).lookup id = some ty := by
  unfold MStore.lookup
  rw [MStore.solve_getElem?]
  simp [entry]

private theorem MStore.levelOf_solve (store : MStore) (id j : Nat) (ty : Ty) :
    (store.solve id ty).levelOf j =
      if j = id then store.levelOf id
      else if j ∈ ty.mvars then min (store.levelOf j) (store.levelOf id)
      else store.levelOf j := by
  by_cases same : j = id
  · subst same
    unfold MStore.levelOf
    rw [MStore.solve_getElem?]
    cases h : store[j]? <;> simp [h]
  · unfold MStore.levelOf
    rw [MStore.solve_getElem?]
    cases h : store[j]? <;> simp [h, same, MStore.levelOf]

private theorem MStore.levelOf_solve_le (store : MStore) (id j : Nat) (ty : Ty) :
    (store.solve id ty).levelOf j ≤ store.levelOf j := by
  rw [MStore.levelOf_solve]
  by_cases same : j = id
  · simp [same]
  · by_cases mem : j ∈ ty.mvars
    · simp only [same, mem, if_true, if_false]
      exact Nat.min_le_left _ _
    · simp [same, mem]

private theorem MStore.canBind_iff {store : MStore} {id : Nat} {ty : Ty} :
    store.canBind id ty = true ↔
      ∃ entry, store[id]? = some entry ∧ entry.solution = none ∧
        ty.occursMVar id = false ∧ ty.scopedB entry.level 0 := by
  unfold MStore.canBind
  cases h : store[id]? with
  | none => simp
  | some entry =>
      simp only [h, Bool.and_eq_true, Option.isNone_iff_eq_none, Option.some.injEq]
      constructor
      · rintro ⟨⟨hsol, hocc⟩, hscoped⟩
        exact ⟨entry, rfl, hsol, by simpa using hocc, hscoped⟩
      · rintro ⟨entry', rfl, hsol, hocc, hscoped⟩
        exact ⟨⟨hsol, by simpa using hocc⟩, hscoped⟩

private theorem MStore.unsolved_solve_lt (store : MStore) (id : Nat) (ty : Ty)
    {e : MEntry} (entry : store[id]? = some e) (hsol : e.solution = none) :
    (store.solve id ty).unsolved < store.unsolved := by
  have bound : id < store.length := by
    by_contra h
    rw [List.getElem?_eq_none_iff.mpr (by omega)] at entry
    exact nomatch entry
  have hidmap : id < (store.map (fun e : MEntry => e.solution.isNone)).length := by
    simpa using bound
  have hval : (store.map (fun e => e.solution.isNone))[id] = true := by
    have h : (store.map (fun e => e.solution.isNone))[id]? = some true := by
      rw [List.getElem?_map, entry]
      simp [hsol]
    rw [List.getElem?_eq_getElem hidmap] at h
    exact Option.some.inj h
  have hflags : (store.solve id ty).map (fun e => e.solution.isNone) =
      (store.map (fun e => e.solution.isNone)).set id false := by
    apply List.ext_getElem?
    intro j
    rw [List.getElem?_map, MStore.solve_getElem?]
    by_cases same : j = id
    · subst same
      rw [List.getElem?_set_self (by simpa using bound)]
      cases h : store[j]? with
      | none => rw [h] at entry; exact nomatch entry
      | some e' => simp [h]
    · rw [List.getElem?_set_ne (Ne.symm same), List.getElem?_map]
      cases h : store[j]? <;> simp [h, same]
  have hcount := List.countP_set (p := fun b : Bool => b)
    (l := store.map (fun e => e.solution.isNone)) (i := id) (a := false) hidmap
  have hcount' : ((store.map (fun e => e.solution.isNone)).set id false).countP
      (fun b : Bool => b) =
      (store.map (fun e => e.solution.isNone)).countP (fun b : Bool => b) - 1 := by
    rw [hcount, hval]
    simp
  have hpos : 0 < (store.map (fun e => e.solution.isNone)).countP (fun b : Bool => b) := by
    rw [List.countP_pos_iff]
    exact ⟨true, by
      rw [List.mem_map]
      exact ⟨e, List.mem_of_getElem? entry, by simp [hsol]⟩, rfl⟩
  have lhsEq : (store.solve id ty).countP (fun e => e.solution.isNone) =
      ((store.solve id ty).map (fun e => e.solution.isNone)).countP (fun b : Bool => b) := by
    rw [List.countP_map]
    rfl
  have storeEq : (store.map (fun e => e.solution.isNone)).countP (fun b : Bool => b) =
      store.countP (fun e => e.solution.isNone) := by
    rw [List.countP_map]
    rfl
  unfold MStore.unsolved
  rw [lhsEq, hflags, hcount', ← storeEq]
  omega

private theorem MStore.solve_leveled {store : MStore} {id : Nat} {ty : Ty}
    (leveled : store.Leveled) (norm : store.Normalized)
    (guard : store.canBind id ty = true)
    (resolved : store.apply ty = ty) :
    (store.solve id ty).Leveled := by
  obtain ⟨entry, hentry, hsolNone, hocc, hscopedB⟩ := MStore.canBind_iff.mp guard
  have hlevel : store.levelOf id = entry.level := by
    unfold MStore.levelOf
    rw [hentry]
    rfl
  intro j entry' solution hEntry hSol
  by_cases same : j = id
  · subst j
    rw [MStore.solve_getElem?] at hEntry
    rw [hentry] at hEntry
    simp only [Option.map_some, if_pos rfl, reduceDIte] at hEntry
    injection hEntry with hEntryEq
    have hlevelEq : entry'.level = entry.level := by
      rw [← hEntryEq]
      simp
    have hsolEq : solution = ty := by
      rw [← hEntryEq] at hSol
      simpa using hSol.symm
    refine ⟨?_, ?_⟩
    · rw [hlevelEq, hsolEq]
      exact (Ty.scopedB_iff_scoped ty entry.level 0).mp hscopedB
    · rw [hlevelEq, hsolEq]
      intro m hm
      have hmne : m ≠ id := by
        intro sameId
        subst m
        have htrue : ty.occursMVar id = true :=
          (Ty.occursMVar_iff_mem ty id).mpr hm
        rw [hocc] at htrue
        exact nomatch htrue
      rw [MStore.levelOf_solve]
      simp only [hmne, if_false, hm, if_true]
      rw [hlevel]
      exact Nat.min_le_right _ _
  · rw [MStore.solve_getElem?] at hEntry
    cases hj : store[j]? with
    | none => rw [hj] at hEntry; simp at hEntry
    | some entry0 =>
        rw [hj] at hEntry
        simp only [Option.map_some, if_neg same, reduceDIte] at hEntry
        injection hEntry with hEntryEq
        have hsol0 : entry0.solution.map (·.substMVar id ty) = some solution := by
          rw [← hEntryEq] at hSol
          simpa using hSol
        obtain ⟨previous, hprevSol, hprevEq⟩ := Option.map_eq_some_iff.mp hsol0
        obtain ⟨hprevScoped, hprevBounded⟩ := leveled j entry0 previous hj hprevSol
        have hnotmem : j ∉ ty.mvars := by
          intro hjmem
          have hnone := MStore.lookup_none_of_resolved norm resolved hjmem
          have hsome : store.lookup j = some previous := by
            unfold MStore.lookup
            rw [hj]
            simp [hprevSol]
          rw [hsome] at hnone
          exact nomatch hnone
        have hlevelEq : entry'.level = entry0.level := by
          rw [← hEntryEq]
          simp [hnotmem]
        refine ⟨?_, ?_⟩
        · rw [hlevelEq, ← hprevEq]
          by_cases hid : id ∈ previous.mvars
          · have hle : store.levelOf id ≤ entry0.level := hprevBounded id hid
            have htyScoped : ty.Scoped entry0.level 0 := by
              have hscoped := (Ty.scopedB_iff_scoped ty entry.level 0).mp hscopedB
              have hle' : entry.level ≤ entry0.level := by
                rw [← hlevel]
                exact hle
              exact Ty.Scoped.mono hscoped hle'
            exact Ty.substMVar_scoped hprevScoped htyScoped
          · rw [Ty.substMVar_eq_self_of_not_mem hid]
            exact hprevScoped
        · rw [hlevelEq, ← hprevEq]
          intro m hm
          rcases Ty.mem_mvars_substMVar_subset hm with hold | ⟨hidmem, hmty⟩
          · exact le_trans (MStore.levelOf_solve_le store id m ty) (hprevBounded m hold)
          · have hmne : m ≠ id := by
              intro sameId
              subst m
              have htrue : ty.occursMVar id = true :=
                (Ty.occursMVar_iff_mem ty id).mpr hmty
              rw [hocc] at htrue
              exact nomatch htrue
            have hle : store.levelOf id ≤ entry0.level := hprevBounded id hidmem
            rw [MStore.levelOf_solve]
            simp only [hmne, if_false, hmty, if_true]
            exact le_trans (Nat.min_le_right _ _) hle

private theorem MStore.solve_normalized {store : MStore} {id : Nat} {ty : Ty}
    (norm : store.Normalized) (guard : store.canBind id ty = true)
    (resolved : store.apply ty = ty) :
    (store.solve id ty).Normalized := by
  obtain ⟨entry, hentry, hsolNone, hocc, hscopedB⟩ := MStore.canBind_iff.mp guard
  intro j solution hlookup m hm
  by_cases same : j = id
  · subst j
    rw [MStore.lookup_solve_self store id ty hentry] at hlookup
    injection hlookup with hsol
    subst hsol
    have hmne : m ≠ id := by
      intro sameId
      subst m
      have htrue : ty.occursMVar id = true :=
        (Ty.occursMVar_iff_mem ty id).mpr hm
      rw [hocc] at htrue
      exact nomatch htrue
    have hnone := MStore.lookup_none_of_resolved norm resolved hm
    rw [MStore.lookup_solve_of_ne store id m ty hmne, hnone]
    rfl
  · rw [MStore.lookup_solve_of_ne store id j ty same] at hlookup
    rw [Option.map_eq_some_iff] at hlookup
    obtain ⟨previous, hprevLookup, hprevEq⟩ := hlookup
    rw [← hprevEq] at hm
    rcases Ty.mem_mvars_substMVar' hm with ⟨hmne, hmprev⟩ | hmty
    · have hnone := norm j previous hprevLookup m hmprev
      rw [MStore.lookup_solve_of_ne store id m ty hmne, hnone]
      rfl
    · have hmne : m ≠ id := by
        intro sameId
        subst m
        have htrue : ty.occursMVar id = true :=
          (Ty.occursMVar_iff_mem ty id).mpr hmty
        rw [hocc] at htrue
        exact nomatch htrue
      have hnone := MStore.lookup_none_of_resolved norm resolved hmty
      rw [MStore.lookup_solve_of_ne store id m ty hmne, hnone]
      rfl

private theorem MStore.solve_bounded {store : MStore} {id : Nat} {ty : Ty}
    {frontier : Nat} (storeBounded : store.Bounded frontier)
    (tyBounded : ty.MVarBounded frontier) :
    (store.solve id ty).Bounded frontier := by
  intro j solution hlookup
  by_cases same : j = id
  · subst j
    unfold MStore.lookup at hlookup
    rw [MStore.solve_getElem?] at hlookup
    cases hj : store[id]? with
    | none => rw [hj] at hlookup; simp at hlookup
    | some entry =>
        rw [hj] at hlookup
        simp only [Option.map_some, if_pos rfl, reduceDIte, Option.bind_some] at hlookup
        injection hlookup with hsol
        rw [← hsol]
        exact tyBounded
  · rw [MStore.lookup_solve_of_ne store id j ty same] at hlookup
    rw [Option.map_eq_some_iff] at hlookup
    obtain ⟨previous, hprevLookup, hprevEq⟩ := hlookup
    rw [← hprevEq]
    exact Ty.substMVar_mvarBounded (storeBounded j previous hprevLookup) tyBounded

/-! ## Phase structure -/

/-- The defining equation of one non-final phase step. -/
private theorem unifyPhase_cons_eq (store : MStore) (fuel : Nat)
    (left right : Ty) (rest : List Constraint) :
    unifyPhase store (fuel + 1) ((left, right) :: rest) =
      if left = right then unifyPhase store fuel rest
      else
        match left, right with
        | .mvar id, ty | ty, .mvar id =>
            if store.canBind id ty then
              (UnifyPhase.bound (store.solve id ty)
                (rest.map (Constraint.substMVar id ty)) : UnifyPhase)
            else .failed
        | .arrow leftDomain leftCodomain,
          .arrow rightDomain rightCodomain =>
            unifyPhase store fuel
              ((leftDomain, rightDomain) :: (leftCodomain, rightCodomain) :: rest)
        | _, _ => .failed := by
  rfl

/-- A successful binding lowers the number of unsolved entries. -/
private theorem bound_of_guard_if (store result : MStore) (id : Nat) (ty : Ty)
    (rest rest' : List Constraint)
    (run : (if store.canBind id ty then
              (UnifyPhase.bound (store.solve id ty)
                (rest.map (Constraint.substMVar id ty)) : UnifyPhase)
            else .failed) = .bound result rest') :
    result.unsolved < store.unsolved := by
  by_cases h : store.canBind id ty
  · rw [if_pos h] at run
    injection run with resultEq _
    subst resultEq
    obtain ⟨entry, hentry, hsol, _, _⟩ := MStore.canBind_iff.mp h
    exact MStore.unsolved_solve_lt store id ty hentry hsol
  · rw [if_neg h] at run
    exact nomatch run

/-- A phase given at least the constraints' total size as fuel never runs
out: every step that does not bind removes at least one constructor. -/
theorem unifyPhase_ne_outOfFuel
    {store : MStore} {fuel : Nat} {constraints : List Constraint}
    (enough : Constraints.size constraints ≤ fuel) :
    unifyPhase store fuel constraints ≠ .outOfFuel := by
  induction fuel generalizing constraints with
  | zero =>
      cases constraints with
      | nil => simp [unifyPhase]
      | cons constraint rest =>
          have positive :=
            Constraints.size_nonempty (constraints := constraint :: rest) (by simp)
          omega
  | succ fuel ih =>
      cases constraints with
      | nil => simp [unifyPhase]
      | cons constraint rest =>
          obtain ⟨left, right⟩ := constraint
          rw [unifyPhase_cons_eq]
          by_cases equal : left = right
          · rw [if_pos equal]
            refine ih ?_
            have h := enough
            rw [Constraints.size_cons] at h
            simp only [Prod.fst, Prod.snd] at h
            have l := Ty.size_pos left
            have r := Ty.size_pos right
            omega
          · rw [if_neg equal]
            cases left <;> cases right <;> simp only []
            all_goals first
              | (exact ih (by
                  simp only [Constraints.size_cons, Ty.size] at enough ⊢
                  omega))
              | (split <;> simp)
              | (simp)

/-- A phase that binds solves a previously unsolved metavariable. -/
theorem unifyPhase_bound_unsolved_lt
    {store result : MStore} {fuel : Nat} {constraints rest : List Constraint}
    (run : unifyPhase store fuel constraints = .bound result rest) :
    result.unsolved < store.unsolved := by
  induction fuel generalizing constraints with
  | zero =>
      cases constraints with
      | nil => simp [unifyPhase] at run
      | cons constraint rest => simp [unifyPhase] at run
  | succ fuel ih =>
      cases constraints with
      | nil => simp [unifyPhase] at run
      | cons constraint rest =>
          obtain ⟨left, right⟩ := constraint
          rw [unifyPhase_cons_eq] at run
          by_cases equal : left = right
          · rw [if_pos equal] at run
            exact ih run
          · rw [if_neg equal] at run
            cases left <;> cases right <;> simp only [] at run
            all_goals first
              | (exact bound_of_guard_if store result _ _ _ _ run)
              | (exact ih run)
              | (exact nomatch run)

/-! ## Structural invariants -/

private theorem not_finished_of_bound_if {p : Prop} [Decidable p]
    {store : MStore} {id : Nat} {ty : Ty} {rest : List Constraint}
    {result : MStore}
    (run : (if p then
              (UnifyPhase.bound (store.solve id ty)
                (rest.map (Constraint.substMVar id ty)) : UnifyPhase)
            else .failed) = .finished result) : False := by
  by_cases h : p
  · rw [if_pos h] at run
    exact nomatch run
  · rw [if_neg h] at run
    exact nomatch run

private theorem bound_if_length {p : Prop} [Decidable p]
    {store result : MStore} {id : Nat} {ty : Ty}
    {rest rest' : List Constraint}
    (run : (if p then
              (UnifyPhase.bound (store.solve id ty)
                (rest.map (Constraint.substMVar id ty)) : UnifyPhase)
            else .failed) = .bound result rest') :
    result.length = store.length := by
  by_cases h : p
  · rw [if_pos h] at run
    injection run with resultEq _
    subst resultEq
    simp [MStore.solve_length]
  · rw [if_neg h] at run
    exact nomatch run

private theorem unifyPhase_finished_length
    {store result : MStore} {fuel : Nat} {constraints : List Constraint}
    (run : unifyPhase store fuel constraints = .finished result) :
    result.length = store.length := by
  induction fuel generalizing constraints with
  | zero =>
      cases constraints with
      | nil =>
          simp only [unifyPhase, UnifyPhase.finished.injEq] at run
          subst result
          rfl
      | cons constraint rest => simp [unifyPhase] at run
  | succ fuel ih =>
      cases constraints with
      | nil =>
          simp only [unifyPhase, UnifyPhase.finished.injEq] at run
          subst result
          rfl
      | cons constraint rest =>
          obtain ⟨left, right⟩ := constraint
          rw [unifyPhase_cons_eq] at run
          by_cases equal : left = right
          · rw [if_pos equal] at run
            exact ih run
          · rw [if_neg equal] at run
            cases left <;> cases right <;> simp only [] at run
            all_goals first
              | (exact ih run)
              | (exact (not_finished_of_bound_if run).elim)
              | (cases run)

private theorem unifyPhase_bound_length
    {store result : MStore} {fuel : Nat}
    {constraints rest : List Constraint}
    (run : unifyPhase store fuel constraints = .bound result rest) :
    result.length = store.length := by
  induction fuel generalizing constraints with
  | zero =>
      cases constraints with
      | nil => simp [unifyPhase] at run
      | cons constraint rest => simp [unifyPhase] at run
  | succ fuel ih =>
      cases constraints with
      | nil => simp [unifyPhase] at run
      | cons constraint rest =>
          obtain ⟨left, right⟩ := constraint
          rw [unifyPhase_cons_eq] at run
          by_cases equal : left = right
          · rw [if_pos equal] at run
            exact ih run
          · rw [if_neg equal] at run
            cases left <;> cases right <;> simp only [] at run
            all_goals first
              | (exact ih run)
              | (exact bound_if_length run)
              | (cases run)

private theorem unifyLoop_succ (fuel : Nat) (store : MStore)
    (constraints : List Constraint) :
    unifyLoop (fuel + 1) store constraints =
      match unifyPhase store (Constraints.size constraints) constraints with
      | .finished result => some result
      | .bound result rest => unifyLoop fuel result rest
      | .failed | .outOfFuel => none := by
  rfl

private theorem unifyLoop_length
    {fuel : Nat} {store : MStore} {constraints : List Constraint}
    {result : MStore}
    (run : unifyLoop fuel store constraints = some result) :
    result.length = store.length := by
  induction fuel generalizing store constraints with
  | zero => simp [unifyLoop] at run
  | succ fuel ih =>
      rw [unifyLoop_succ] at run
      split at run
      · rename_i finishedRun
        injection run with resultEq
        subst resultEq
        exact unifyPhase_finished_length finishedRun
      · rename_i boundRun
        rw [ih run]
        exact unifyPhase_bound_length boundRun
      · exact nomatch run
      · exact nomatch run

theorem MStore.unify_length
    {store result : MStore} {left right : Ty}
    (run : store.unify left right = some result) :
    result.length = store.length := by
  exact unifyLoop_length run

private theorem unifyPhase_finished_eq
    {store result : MStore} {fuel : Nat} {constraints : List Constraint}
    (run : unifyPhase store fuel constraints = .finished result) :
    result = store := by
  induction fuel generalizing constraints with
  | zero =>
      cases constraints with
      | nil =>
          simp only [unifyPhase, UnifyPhase.finished.injEq] at run
          subst result
          rfl
      | cons constraint rest => simp [unifyPhase] at run
  | succ fuel ih =>
      cases constraints with
      | nil =>
          simp only [unifyPhase, UnifyPhase.finished.injEq] at run
          subst result
          rfl
      | cons constraint rest =>
          obtain ⟨left, right⟩ := constraint
          rw [unifyPhase_cons_eq] at run
          by_cases equal : left = right
          · rw [if_pos equal] at run
            exact ih run
          · rw [if_neg equal] at run
            cases left <;> cases right <;> simp only [] at run
            all_goals first
              | (exact ih run)
              | (exact (not_finished_of_bound_if run).elim)
              | (cases run)

/-! ## Resolved constraints -/

private abbrev ConstraintsResolved (store : MStore)
    (constraints : List Constraint) : Prop :=
  ∀ constraint ∈ constraints,
    store.apply constraint.1 = constraint.1 ∧
      store.apply constraint.2 = constraint.2

private theorem ConstraintsResolved.arrows {store : MStore}
    {leftDomain leftCodomain rightDomain rightCodomain : Ty}
    {rest : List Constraint}
    (resolved : ConstraintsResolved store
      ((Ty.arrow leftDomain leftCodomain,
        Ty.arrow rightDomain rightCodomain) :: rest)) :
    ConstraintsResolved store
      ((leftDomain, rightDomain) :: (leftCodomain, rightCodomain) :: rest) := by
  intro constraint member
  have head := resolved
    (Ty.arrow leftDomain leftCodomain, Ty.arrow rightDomain rightCodomain)
    (by simp)
  have leftParts : store.apply leftDomain = leftDomain ∧
      store.apply leftCodomain = leftCodomain := by
    simpa [MStore.apply] using head.1
  have rightParts : store.apply rightDomain = rightDomain ∧
      store.apply rightCodomain = rightCodomain := by
    simpa [MStore.apply] using head.2
  rcases List.mem_cons.mp member with rfl | member
  · exact ⟨leftParts.1, rightParts.1⟩
  · rcases List.mem_cons.mp member with rfl | member
    · exact ⟨leftParts.2, rightParts.2⟩
    · exact resolved constraint (by simp [member])

private theorem MStore.apply_eq_self_of_mvars_unsolved (store : MStore) (ty : Ty)
    (unsolved : ∀ id ∈ ty.mvars, store.lookup id = none) :
    store.apply ty = ty := by
  induction ty with
  | prim => rfl
  | bvar => rfl
  | rigid => rfl
  | arrow domain codomain domainIH codomainIH =>
      have domainUnsolved : ∀ id ∈ domain.mvars, store.lookup id = none := by
        intro id inside
        apply unsolved id
        simp only [Ty.mvars, List.mem_dedup, List.mem_append]
        exact Or.inl inside
      have codomainUnsolved : ∀ id ∈ codomain.mvars, store.lookup id = none := by
        intro id inside
        apply unsolved id
        simp only [Ty.mvars, List.mem_dedup, List.mem_append]
        exact Or.inr inside
      simp only [MStore.apply]
      rw [domainIH domainUnsolved, codomainIH codomainUnsolved]
  | mvar id =>
      have noneLookup := unsolved id (by simp [Ty.mvars])
      simp only [MStore.apply, noneLookup]
      rfl

private theorem MStore.apply_idem {store : MStore} (norm : store.Normalized)
    (ty : Ty) : store.apply (store.apply ty) = store.apply ty := by
  induction ty with
  | prim => rfl
  | bvar => rfl
  | rigid => rfl
  | arrow domain codomain domainIH codomainIH =>
      simp only [MStore.apply]
      rw [domainIH, codomainIH]
  | mvar id =>
      simp only [MStore.apply]
      cases lookupEq : store.lookup id with
      | none => simp [MStore.apply, lookupEq]
      | some replacement =>
          change store.apply replacement = replacement
          apply MStore.apply_eq_self_of_mvars_unsolved
          intro key member
          exact norm id replacement lookupEq key member

private theorem MStore.apply_subst_resolved {store : MStore} {id : Nat} {ty : Ty}
    (norm : store.Normalized) (occurs : ty.occursMVar id = false)
    (tyResolved : store.apply ty = ty) {source : Ty}
    (sourceResolved : store.apply source = source) :
    (store.solve id ty).apply (source.substMVar id ty) =
      source.substMVar id ty := by
  apply MStore.apply_eq_self_of_mvars_unsolved
  intro key member
  rcases Ty.mem_mvars_substMVar' member with ⟨different, oldMember⟩ | newMember
  · have hnone := MStore.lookup_none_of_resolved norm sourceResolved oldMember
    rw [MStore.lookup_solve_of_ne store id key ty different, hnone]
    rfl
  · have keyLookup := MStore.lookup_none_of_resolved norm tyResolved newMember
    have different : key ≠ id := by
      intro same
      subst same
      have occursTrue := (Ty.occursMVar_iff_mem ty key).mpr newMember
      rw [occurs] at occursTrue
      exact nomatch occursTrue
    rw [MStore.lookup_solve_of_ne store id key ty different, keyLookup]
    rfl

private theorem bound_branch_normalized
    {store result : MStore} {id : Nat} {ty : Ty}
    {rest rest' : List Constraint}
    (norm : store.Normalized)
    (run : (if store.canBind id ty then
              (UnifyPhase.bound (store.solve id ty)
                (rest.map (Constraint.substMVar id ty)) : UnifyPhase)
            else .failed) = .bound result rest')
    (tyResolved : store.apply ty = ty)
    (restResolved : ConstraintsResolved store rest) :
    result.Normalized ∧ ConstraintsResolved result rest' := by
  by_cases h : store.canBind id ty
  · rw [if_pos h] at run
    injection run with resultEq restEq
    subst resultEq
    subst restEq
    obtain ⟨_, _, _, hocc, _⟩ := MStore.canBind_iff.mp h
    refine ⟨MStore.solve_normalized norm h tyResolved, ?_⟩
    intro current inRest
    rcases List.mem_map.mp inRest with ⟨old, inOld, rfl⟩
    exact ⟨MStore.apply_subst_resolved norm hocc tyResolved
             (restResolved old inOld).1,
           MStore.apply_subst_resolved norm hocc tyResolved
             (restResolved old inOld).2⟩
  · rw [if_neg h] at run
    exact nomatch run

private theorem unifyPhase_finished_normalized
    {store result : MStore} {fuel : Nat} {constraints : List Constraint}
    (norm : store.Normalized)
    (_resolved : ConstraintsResolved store constraints)
    (run : unifyPhase store fuel constraints = .finished result) :
    result.Normalized := by
  rw [unifyPhase_finished_eq run]
  exact norm

private theorem unifyPhase_bound_normalized
    {store result : MStore} {fuel : Nat}
    {constraints rest : List Constraint}
    (norm : store.Normalized)
    (resolved : ConstraintsResolved store constraints)
    (run : unifyPhase store fuel constraints = .bound result rest) :
    result.Normalized ∧ ConstraintsResolved result rest := by
  induction fuel generalizing constraints with
  | zero =>
      cases constraints with
      | nil => simp [unifyPhase] at run
      | cons constraint rest => simp [unifyPhase] at run
  | succ fuel ih =>
      cases constraints with
      | nil => simp [unifyPhase] at run
      | cons constraint rest =>
          obtain ⟨left, right⟩ := constraint
          have head := resolved (left, right) (by simp)
          have restResolved : ConstraintsResolved store rest := by
            intro current inRest
            exact resolved current (by simp [inRest])
          rw [unifyPhase_cons_eq] at run
          by_cases equal : left = right
          · rw [if_pos equal] at run
            exact ih restResolved run
          · rw [if_neg equal] at run
            cases left <;> cases right <;> simp only [] at run
            all_goals first
              | (exact ih (ConstraintsResolved.arrows resolved) run)
              | (exact bound_branch_normalized norm run
                  (by first | exact head.1 | exact head.2) restResolved)
              | (cases run)

private theorem unifyLoop_normalized
    {fuel : Nat} {store : MStore} {constraints : List Constraint}
    {result : MStore}
    (norm : store.Normalized)
    (resolved : ConstraintsResolved store constraints)
    (run : unifyLoop fuel store constraints = some result) :
    result.Normalized := by
  induction fuel generalizing store constraints with
  | zero => simp [unifyLoop] at run
  | succ fuel ih =>
      rw [unifyLoop_succ] at run
      split at run
      · rename_i finishedRun
        injection run with resultEq
        subst resultEq
        exact unifyPhase_finished_normalized norm resolved finishedRun
      · rename_i boundRun
        obtain ⟨resultNorm, restResolved⟩ :=
          unifyPhase_bound_normalized norm resolved boundRun
        exact ih resultNorm restResolved run
      · exact nomatch run
      · exact nomatch run

theorem MStore.unify_normalized
    {store result : MStore} {left right : Ty}
    (normalized : store.Normalized)
    (run : store.unify left right = some result) :
    result.Normalized := by
  change unifyLoop (store.unsolved + 1) store
    [(store.apply left, store.apply right)] = some result at run
  refine unifyLoop_normalized normalized ?_ run
  intro constraint member
  simp only [List.mem_singleton] at member
  subst member
  exact ⟨MStore.apply_idem normalized left, MStore.apply_idem normalized right⟩

/-! ## Allocation bounds -/

private abbrev ConstraintsBounded (frontier : Nat)
    (constraints : List Constraint) : Prop :=
  ∀ constraint ∈ constraints,
    constraint.1.MVarBounded frontier ∧ constraint.2.MVarBounded frontier

private theorem ConstraintsBounded.arrows {frontier : Nat}
    {leftDomain leftCodomain rightDomain rightCodomain : Ty}
    {rest : List Constraint}
    (head : (Ty.arrow leftDomain leftCodomain).MVarBounded frontier ∧
      (Ty.arrow rightDomain rightCodomain).MVarBounded frontier)
    (restBounded : ConstraintsBounded frontier rest) :
    ConstraintsBounded frontier
      ((leftDomain, rightDomain) :: (leftCodomain, rightCodomain) :: rest) := by
  intro constraint member
  rcases List.mem_cons.mp member with rfl | member
  · exact ⟨Ty.MVarBounded.left head.1, Ty.MVarBounded.left head.2⟩
  · rcases List.mem_cons.mp member with rfl | member
    · exact ⟨Ty.MVarBounded.right head.1, Ty.MVarBounded.right head.2⟩
    · exact restBounded constraint member

private theorem MStore.apply_bounded {store : MStore} {ty : Ty}
    {frontier : Nat}
    (storeBounded : store.Bounded frontier)
    (typeBounded : ty.MVarBounded frontier) :
    (store.apply ty).MVarBounded frontier := by
  induction ty with
  | prim => exact typeBounded
  | arrow domain codomain domainIH codomainIH =>
      intro id member
      have split : id ∈ (store.apply domain).mvars ∨
          id ∈ (store.apply codomain).mvars := by
        simpa [MStore.apply, Ty.mvars, List.mem_dedup, List.mem_append] using member
      rcases split with inside | inside
      · exact domainIH (Ty.MVarBounded.left typeBounded) id inside
      · exact codomainIH (Ty.MVarBounded.right typeBounded) id inside
  | bvar => exact typeBounded
  | rigid => exact typeBounded
  | mvar id =>
      simp only [MStore.apply]
      cases lookupEq : store.lookup id with
      | none =>
          simp only [lookupEq, Option.getD_none]
          exact typeBounded
      | some replacement =>
          simp only [lookupEq, Option.getD_some]
          exact storeBounded id replacement lookupEq

private theorem bound_if_eq {p : Prop} [Decidable p]
    {store result : MStore} {id : Nat} {ty : Ty}
    {rest rest' : List Constraint}
    (run : (if p then
              (UnifyPhase.bound (store.solve id ty)
                (rest.map (Constraint.substMVar id ty)) : UnifyPhase)
            else .failed) = .bound result rest') :
    store.solve id ty = result ∧
      rest.map (Constraint.substMVar id ty) = rest' := by
  by_cases h : p
  · rw [if_pos h] at run
    injection run with resultEq restEq
    exact ⟨resultEq, restEq⟩
  · rw [if_neg h] at run
    exact nomatch run

private theorem unifyPhase_finished_bounded
    {store result : MStore} {fuel : Nat} {constraints : List Constraint}
    {frontier : Nat}
    (storeBounded : store.Bounded frontier)
    (constraintsBounded : ConstraintsBounded frontier constraints)
    (run : unifyPhase store fuel constraints = .finished result) :
    result.Bounded frontier := by
  rw [unifyPhase_finished_eq run]
  exact storeBounded

private theorem unifyPhase_bound_bounded
    {store result : MStore} {fuel : Nat}
    {constraints rest : List Constraint} {frontier : Nat}
    (storeBounded : store.Bounded frontier)
    (constraintsBounded : ConstraintsBounded frontier constraints)
    (run : unifyPhase store fuel constraints = .bound result rest) :
    result.Bounded frontier ∧ ConstraintsBounded frontier rest := by
  induction fuel generalizing constraints with
  | zero =>
      cases constraints with
      | nil => simp [unifyPhase] at run
      | cons constraint rest => simp [unifyPhase] at run
  | succ fuel ih =>
      cases constraints with
      | nil => simp [unifyPhase] at run
      | cons constraint rest =>
          obtain ⟨left, right⟩ := constraint
          have head := constraintsBounded (left, right) (by simp)
          have restBounded : ConstraintsBounded frontier rest := by
            intro current inRest
            exact constraintsBounded current (by simp [inRest])
          rw [unifyPhase_cons_eq] at run
          by_cases equal : left = right
          · rw [if_pos equal] at run
            exact ih restBounded run
          · rw [if_neg equal] at run
            cases left <;> cases right <;> simp only [] at run
            all_goals first
              | (exact ih (ConstraintsBounded.arrows head restBounded) run)
              | (obtain ⟨rfl, rfl⟩ := bound_if_eq run
                 refine ⟨MStore.solve_bounded storeBounded ?_, ?_⟩
                 · first | exact head.1 | exact head.2
                 · intro current inRest
                   rcases List.mem_map.mp inRest with ⟨old, inOld, rfl⟩
                   exact ⟨Ty.substMVar_mvarBounded (restBounded old inOld).1
                            (by first | exact head.1 | exact head.2),
                          Ty.substMVar_mvarBounded (restBounded old inOld).2
                            (by first | exact head.1 | exact head.2)⟩)
              | (cases run)

private theorem unifyLoop_bounded
    {fuel : Nat} {store : MStore} {constraints : List Constraint}
    {result : MStore} {frontier : Nat}
    (storeBounded : store.Bounded frontier)
    (constraintsBounded : ConstraintsBounded frontier constraints)
    (run : unifyLoop fuel store constraints = some result) :
    result.Bounded frontier := by
  induction fuel generalizing store constraints with
  | zero => simp [unifyLoop] at run
  | succ fuel ih =>
      rw [unifyLoop_succ] at run
      split at run
      · rename_i finishedRun
        injection run with resultEq
        subst resultEq
        exact unifyPhase_finished_bounded storeBounded constraintsBounded finishedRun
      · rename_i boundRun
        obtain ⟨resultBounded, restBounded⟩ :=
          unifyPhase_bound_bounded storeBounded constraintsBounded boundRun
        exact ih resultBounded restBounded run
      · exact nomatch run
      · exact nomatch run

theorem MStore.unify_bounded
    {store result : MStore} {left right : Ty} {frontier : Nat}
    (storeBounded : store.Bounded frontier)
    (leftBounded : left.MVarBounded frontier)
    (rightBounded : right.MVarBounded frontier)
    (run : store.unify left right = some result) :
    result.Bounded frontier := by
  change unifyLoop (store.unsolved + 1) store
    [(store.apply left, store.apply right)] = some result at run
  refine unifyLoop_bounded storeBounded ?_ run
  intro constraint member
  simp only [List.mem_singleton] at member
  subst member
  exact ⟨MStore.apply_bounded storeBounded leftBounded,
    MStore.apply_bounded storeBounded rightBounded⟩

/-! ## Levels only decrease -/

private theorem unifyPhase_finished_levelOf_le
    {store result : MStore} {fuel : Nat} {constraints : List Constraint}
    (run : unifyPhase store fuel constraints = .finished result) (id : Nat) :
    result.levelOf id ≤ store.levelOf id := by
  rw [unifyPhase_finished_eq run]

private theorem unifyPhase_bound_levelOf_le
    {store result : MStore} {fuel : Nat}
    {constraints rest : List Constraint}
    (run : unifyPhase store fuel constraints = .bound result rest) (id : Nat) :
    result.levelOf id ≤ store.levelOf id := by
  induction fuel generalizing constraints with
  | zero =>
      cases constraints with
      | nil => simp [unifyPhase] at run
      | cons constraint rest => simp [unifyPhase] at run
  | succ fuel ih =>
      cases constraints with
      | nil => simp [unifyPhase] at run
      | cons constraint rest =>
          obtain ⟨left, right⟩ := constraint
          rw [unifyPhase_cons_eq] at run
          by_cases equal : left = right
          · rw [if_pos equal] at run
            exact ih run
          · rw [if_neg equal] at run
            cases left <;> cases right <;> simp only [] at run
            all_goals first
              | (exact ih run)
              | (obtain ⟨solutionEq, _⟩ := bound_if_eq run
                 rw [← solutionEq]
                 exact MStore.levelOf_solve_le store _ _ _)
              | (cases run)

private theorem unifyLoop_levelOf_le
    {fuel : Nat} {store : MStore} {constraints : List Constraint}
    {result : MStore}
    (run : unifyLoop fuel store constraints = some result) (id : Nat) :
    result.levelOf id ≤ store.levelOf id := by
  induction fuel generalizing store constraints with
  | zero => simp [unifyLoop] at run
  | succ fuel ih =>
      rw [unifyLoop_succ] at run
      split at run
      · rename_i finishedRun
        injection run with resultEq
        subst resultEq
        exact unifyPhase_finished_levelOf_le finishedRun id
      · rename_i boundRun
        exact le_trans (ih run) (unifyPhase_bound_levelOf_le boundRun id)
      · exact nomatch run
      · exact nomatch run

/-- Unification only ever lowers levels. -/
theorem MStore.unify_levelOf_le
    {store result : MStore} {left right : Ty}
    (run : store.unify left right = some result) (id : Nat) :
    result.levelOf id ≤ store.levelOf id := by
  change unifyLoop (store.unsolved + 1) store
    [(store.apply left, store.apply right)] = some result at run
  exact unifyLoop_levelOf_le run id

/-! ## Leveled solutions -/

private theorem bound_guard_data {store result : MStore} {id : Nat} {ty : Ty}
    {rest rest' : List Constraint}
    (run : (if store.canBind id ty then
              (UnifyPhase.bound (store.solve id ty)
                (rest.map (Constraint.substMVar id ty)) : UnifyPhase)
            else .failed) = .bound result rest') :
    store.canBind id ty = true ∧ store.solve id ty = result ∧
      rest.map (Constraint.substMVar id ty) = rest' := by
  by_cases h : store.canBind id ty
  · rw [if_pos h] at run
    injection run with resultEq restEq
    exact ⟨h, resultEq, restEq⟩
  · rw [if_neg h] at run
    exact nomatch run

private theorem unifyPhase_finished_leveled
    {store result : MStore} {fuel : Nat} {constraints : List Constraint}
    (leveled : store.Leveled)
    (norm : store.Normalized)
    (resolved : ConstraintsResolved store constraints)
    (run : unifyPhase store fuel constraints = .finished result) :
    result.Leveled := by
  rw [unifyPhase_finished_eq run]
  exact leveled

private theorem unifyPhase_bound_leveled
    {store result : MStore} {fuel : Nat}
    {constraints rest : List Constraint}
    (leveled : store.Leveled)
    (norm : store.Normalized)
    (resolved : ConstraintsResolved store constraints)
    (run : unifyPhase store fuel constraints = .bound result rest) :
    result.Leveled := by
  induction fuel generalizing constraints with
  | zero =>
      cases constraints with
      | nil => simp [unifyPhase] at run
      | cons constraint rest => simp [unifyPhase] at run
  | succ fuel ih =>
      cases constraints with
      | nil => simp [unifyPhase] at run
      | cons constraint rest =>
          obtain ⟨left, right⟩ := constraint
          have headResolved := resolved (left, right) (by simp)
          have restResolved : ConstraintsResolved store rest := by
            intro current inRest
            exact resolved current (by simp [inRest])
          rw [unifyPhase_cons_eq] at run
          by_cases equal : left = right
          · rw [if_pos equal] at run
            exact ih restResolved run
          · rw [if_neg equal] at run
            cases left <;> cases right <;> simp only [] at run
            all_goals first
              | (exact ih (ConstraintsResolved.arrows resolved) run)
              | (obtain ⟨guard, resultEq, _⟩ := bound_guard_data run
                 subst resultEq
                 exact MStore.solve_leveled leveled norm guard
                   (by first | exact headResolved.1 | exact headResolved.2))
              | (cases run)

private theorem unifyLoop_leveled
    {fuel : Nat} {store : MStore} {constraints : List Constraint}
    {result : MStore}
    (leveled : store.Leveled)
    (norm : store.Normalized)
    (resolved : ConstraintsResolved store constraints)
    (run : unifyLoop fuel store constraints = some result) :
    result.Leveled := by
  induction fuel generalizing store constraints with
  | zero => simp [unifyLoop] at run
  | succ fuel ih =>
      rw [unifyLoop_succ] at run
      split at run
      · rename_i finishedRun
        injection run with resultEq
        subst resultEq
        exact unifyPhase_finished_leveled leveled norm resolved finishedRun
      · rename_i boundRun
        obtain ⟨resultNorm, restResolved⟩ :=
          unifyPhase_bound_normalized norm resolved boundRun
        exact ih (unifyPhase_bound_leveled leveled norm resolved boundRun)
          resultNorm restResolved run
      · exact nomatch run
      · exact nomatch run

theorem MStore.unify_leveled
    {store result : MStore} {left right : Ty}
    (leveled : store.Leveled)
    (normalized : store.Normalized)
    (run : store.unify left right = some result) :
    result.Leveled := by
  change unifyLoop (store.unsolved + 1) store
    [(store.apply left, store.apply right)] = some result at run
  refine unifyLoop_leveled leveled normalized ?_ run
  intro constraint member
  simp only [List.mem_singleton] at member
  subst member
  exact ⟨MStore.apply_idem normalized left, MStore.apply_idem normalized right⟩

/-! ## Solved form -/

private def MStore.Extends (store result : MStore) : Prop :=
  ∀ ty, result.apply (store.apply ty) = result.apply ty

private theorem MStore.extends_refl {store : MStore} (norm : store.Normalized) :
    MStore.Extends store store :=
  fun ty => MStore.apply_idem norm ty

private theorem MStore.extends_trans {first second third : MStore}
    (firstSecond : MStore.Extends first second)
    (secondThird : MStore.Extends second third) :
    MStore.Extends first third := by
  intro ty
  calc
    third.apply (first.apply ty) =
        third.apply (second.apply (first.apply ty)) :=
      (secondThird (first.apply ty)).symm
    _ = third.apply (second.apply ty) := by rw [firstSecond ty]
    _ = third.apply ty := secondThird ty

private theorem MStore.solve_apply {store : MStore}
    {id : Nat} {ty : Ty} (guard : store.canBind id ty = true) (source : Ty) :
    (store.solve id ty).apply source =
      (store.apply source).substMVar id ty := by
  obtain ⟨entry, hentry, hsolNone, hocc, hscopedB⟩ := MStore.canBind_iff.mp guard
  induction source with
  | prim => rfl
  | bvar => rfl
  | rigid => rfl
  | arrow domain codomain domainIH codomainIH =>
      simp only [MStore.apply, Ty.substMVar, domainIH, codomainIH]
  | mvar key =>
      by_cases same : key = id
      · subst key
        have solveLookup := MStore.lookup_solve_self store id ty hentry
        have oldLookup : store.lookup id = none := by
          unfold MStore.lookup
          rw [hentry]
          simp [hsolNone]
        simp only [MStore.apply]
        rw [solveLookup, oldLookup]
        simp [Ty.substMVar]
      · cases hlookup : store.lookup key with
        | none =>
            have solveLookup : (store.solve id ty).lookup key = none := by
              rw [MStore.lookup_solve_of_ne store id key ty same, hlookup]
              rfl
            simp [MStore.apply, hlookup, solveLookup, Ty.substMVar, same]
        | some previous =>
            have solveLookup : (store.solve id ty).lookup key =
                some (previous.substMVar id ty) := by
              rw [MStore.lookup_solve_of_ne store id key ty same, hlookup]
              rfl
            simp [MStore.apply, hlookup, solveLookup, Ty.substMVar, same]

private theorem MStore.extends_solve {store : MStore} (norm : store.Normalized)
    {id : Nat} {ty : Ty} (guard : store.canBind id ty = true) :
    MStore.Extends store (store.solve id ty) := by
  intro source
  rw [MStore.solve_apply guard (store.apply source),
    MStore.solve_apply guard source, MStore.apply_idem norm source]

private theorem MStore.solve_apply_eq_self {store : MStore} (norm : store.Normalized)
    {id : Nat} {ty : Ty} (occurs : ty.occursMVar id = false)
    (resolved : store.apply ty = ty) :
    (store.solve id ty).apply ty = ty := by
  apply MStore.apply_eq_self_of_mvars_unsolved
  intro key member
  have keyLookup := MStore.lookup_none_of_resolved norm resolved member
  have different : key ≠ id := by
    intro same
    subst same
    have occursTrue := (Ty.occursMVar_iff_mem ty key).mpr member
    rw [occurs] at occursTrue
    exact nomatch occursTrue
  rw [MStore.lookup_solve_of_ne store id key ty different, keyLookup]
  rfl

private theorem MStore.apply_subst_eq {store result : MStore}
    (extension : MStore.Extends store result) {id : Nat} {ty : Ty}
    (solveEntry : store.apply (.mvar id) = ty) (source : Ty) :
    result.apply (source.substMVar id ty) = result.apply source := by
  induction source with
  | prim => rfl
  | bvar => rfl
  | rigid => rfl
  | arrow domain codomain domainIH codomainIH =>
      simp only [Ty.substMVar, MStore.apply, domainIH, codomainIH]
  | mvar key =>
      by_cases same : key = id
      · subst key
        simp only [Ty.substMVar, if_pos rfl]
        have extended := extension (Ty.mvar id)
        rw [solveEntry] at extended
        exact extended
      · simp only [Ty.substMVar, if_neg same]

private theorem MStore.apply_arrow_eq_of_forall {result : MStore}
    {leftDomain leftCodomain rightDomain rightCodomain : Ty}
    {rest : List Constraint}
    (solves : ∀ constraint ∈
      ((leftDomain, rightDomain) :: (leftCodomain, rightCodomain) :: rest),
      result.apply constraint.1 = result.apply constraint.2) :
    result.apply (Ty.arrow leftDomain leftCodomain) =
      result.apply (Ty.arrow rightDomain rightCodomain) := by
  have domainEq := solves (leftDomain, rightDomain) (by simp)
  have codomainEq := solves (leftCodomain, rightCodomain) (by simp)
  simp only [MStore.apply, domainEq, codomainEq]

private theorem unifyPhase_finished_solves
    {store result : MStore} {fuel : Nat} {constraints : List Constraint}
    (run : unifyPhase store fuel constraints = .finished result) :
    ∀ constraint ∈ constraints,
      store.apply constraint.1 = store.apply constraint.2 := by
  induction fuel generalizing constraints with
  | zero =>
      cases constraints with
      | nil => simp
      | cons constraint rest => simp [unifyPhase] at run
  | succ fuel ih =>
      cases constraints with
      | nil => simp
      | cons constraint rest =>
          obtain ⟨left, right⟩ := constraint
          rw [unifyPhase_cons_eq] at run
          by_cases equal : left = right
          · rw [if_pos equal] at run
            intro current member
            rcases List.mem_cons.mp member with rfl | member
            · rw [equal]
            · exact ih run current member
          · rw [if_neg equal] at run
            cases left <;> cases right <;> simp only [] at run
            all_goals first
              | (exact (not_finished_of_bound_if run).elim)
              | (intro current member
                 rcases List.mem_cons.mp member with rfl | member
                 · exact MStore.apply_arrow_eq_of_forall
                     (result := store) (solves := ih run)
                 · exact ih run current (by simp [member]))
              | (cases run)

private theorem bound_branch_solves_left
    {store current result : MStore} {id : Nat} {ty : Ty}
    {rest rest' : List Constraint}
    (norm : store.Normalized)
    (run : (if store.canBind id ty then
              (UnifyPhase.bound (store.solve id ty)
                (rest.map (Constraint.substMVar id ty)) : UnifyPhase)
            else .failed) = .bound current rest')
    (tyResolved : store.apply ty = ty)
    (extension : MStore.Extends current result)
    (restSolves : ∀ constraint ∈ rest',
      result.apply constraint.1 = result.apply constraint.2) :
    ∀ constraint ∈ ((Ty.mvar id, ty) :: rest),
      result.apply constraint.1 = result.apply constraint.2 := by
  obtain ⟨guard, currentEq, restEq⟩ := bound_guard_data run
  obtain ⟨entry, hentry, hsolNone, hocc, hscopedB⟩ := MStore.canBind_iff.mp guard
  subst currentEq
  subst restEq
  have fixed := MStore.solve_apply_eq_self norm hocc tyResolved
  have solveEntry : (store.solve id ty).apply (.mvar id) = ty := by
    simp [MStore.apply, MStore.lookup_solve_self store id ty hentry]
  intro constraint member
  rcases List.mem_cons.mp member with rfl | member
  · have extended := extension (Ty.mvar id)
    rw [solveEntry] at extended
    exact extended.symm
  · have substituted := restSolves (Constraint.substMVar id ty constraint)
      (List.mem_map_of_mem member)
    simp only [Constraint.substMVar] at substituted
    rw [MStore.apply_subst_eq extension solveEntry constraint.1,
      MStore.apply_subst_eq extension solveEntry constraint.2] at substituted
    exact substituted

private theorem bound_branch_solves_right
    {store current result : MStore} {id : Nat} {ty : Ty}
    {rest rest' : List Constraint}
    (norm : store.Normalized)
    (run : (if store.canBind id ty then
              (UnifyPhase.bound (store.solve id ty)
                (rest.map (Constraint.substMVar id ty)) : UnifyPhase)
            else .failed) = .bound current rest')
    (tyResolved : store.apply ty = ty)
    (extension : MStore.Extends current result)
    (restSolves : ∀ constraint ∈ rest',
      result.apply constraint.1 = result.apply constraint.2) :
    ∀ constraint ∈ ((ty, Ty.mvar id) :: rest),
      result.apply constraint.1 = result.apply constraint.2 := by
  obtain ⟨guard, currentEq, restEq⟩ := bound_guard_data run
  obtain ⟨entry, hentry, hsolNone, hocc, hscopedB⟩ := MStore.canBind_iff.mp guard
  subst currentEq
  subst restEq
  have fixed := MStore.solve_apply_eq_self norm hocc tyResolved
  have solveEntry : (store.solve id ty).apply (.mvar id) = ty := by
    simp [MStore.apply, MStore.lookup_solve_self store id ty hentry]
  intro constraint member
  rcases List.mem_cons.mp member with rfl | member
  · have extended := extension (Ty.mvar id)
    rw [solveEntry] at extended
    exact extended
  · have substituted := restSolves (Constraint.substMVar id ty constraint)
      (List.mem_map_of_mem member)
    simp only [Constraint.substMVar] at substituted
    rw [MStore.apply_subst_eq extension solveEntry constraint.1,
      MStore.apply_subst_eq extension solveEntry constraint.2] at substituted
    exact substituted

private theorem unifyPhase_bound_solves
    {store current : MStore} {fuel : Nat}
    {constraints rest : List Constraint} {result : MStore}
    (norm : store.Normalized)
    (resolved : ConstraintsResolved store constraints)
    (run : unifyPhase store fuel constraints = .bound current rest)
    (extension : MStore.Extends current result)
    (restSolves : ∀ constraint ∈ rest,
      result.apply constraint.1 = result.apply constraint.2) :
    ∀ constraint ∈ constraints,
      result.apply constraint.1 = result.apply constraint.2 := by
  induction fuel generalizing constraints with
  | zero =>
      cases constraints with
      | nil => simp [unifyPhase] at run
      | cons constraint rest => simp [unifyPhase] at run
  | succ fuel ih =>
      cases constraints with
      | nil => simp [unifyPhase] at run
      | cons constraint rest =>
          obtain ⟨left, right⟩ := constraint
          have headResolved := resolved (left, right) (by simp)
          have restResolved : ConstraintsResolved store rest := by
            intro current inRest
            exact resolved current (by simp [inRest])
          rw [unifyPhase_cons_eq] at run
          by_cases equal : left = right
          · rw [if_pos equal] at run
            intro current member
            rcases List.mem_cons.mp member with rfl | member
            · rw [equal]
            · exact ih restResolved run current member
          · rw [if_neg equal] at run
            cases left <;> cases right <;> simp only [] at run
            all_goals first
              | (intro current member
                 rcases List.mem_cons.mp member with rfl | member
                 · exact MStore.apply_arrow_eq_of_forall
                     (result := result)
                     (solves := ih (ConstraintsResolved.arrows resolved) run)
                 · exact ih (ConstraintsResolved.arrows resolved) run
                     current (by simp [member]))
              | (exact bound_branch_solves_left norm run
                  (by first | exact headResolved.1 | exact headResolved.2)
                  extension restSolves)
              | (exact bound_branch_solves_right norm run
                  headResolved.1 extension restSolves)
              | (cases run)

private theorem unifyPhase_bound_extends
    {store current : MStore} {fuel : Nat}
    {constraints rest : List Constraint}
    (norm : store.Normalized)
    (resolved : ConstraintsResolved store constraints)
    (run : unifyPhase store fuel constraints = .bound current rest) :
    MStore.Extends store current := by
  induction fuel generalizing constraints with
  | zero =>
      cases constraints with
      | nil => simp [unifyPhase] at run
      | cons constraint rest => simp [unifyPhase] at run
  | succ fuel ih =>
      cases constraints with
      | nil => simp [unifyPhase] at run
      | cons constraint rest =>
          obtain ⟨left, right⟩ := constraint
          have restResolved : ConstraintsResolved store rest := by
            intro current inRest
            exact resolved current (by simp [inRest])
          rw [unifyPhase_cons_eq] at run
          by_cases equal : left = right
          · rw [if_pos equal] at run
            exact ih restResolved run
          · rw [if_neg equal] at run
            cases left <;> cases right <;> simp only [] at run
            all_goals first
              | (exact ih (ConstraintsResolved.arrows resolved) run)
              | (obtain ⟨guard, currentEq, _⟩ := bound_guard_data run
                 subst currentEq
                 exact MStore.extends_solve norm guard)
              | (cases run)

private theorem unifyLoop_correct
    {fuel : Nat} {store : MStore} {constraints : List Constraint}
    {result : MStore}
    (norm : store.Normalized)
    (resolved : ConstraintsResolved store constraints)
    (run : unifyLoop fuel store constraints = some result) :
    MStore.Extends store result ∧
      ∀ constraint ∈ constraints,
        result.apply constraint.1 = result.apply constraint.2 := by
  induction fuel generalizing store constraints with
  | zero => simp [unifyLoop] at run
  | succ fuel ih =>
      rw [unifyLoop_succ] at run
      split at run
      · rename_i finishedRun
        injection run with resultEq
        subst resultEq
        have storeEq := unifyPhase_finished_eq finishedRun
        subst storeEq
        exact ⟨MStore.extends_refl norm,
          unifyPhase_finished_solves finishedRun⟩
      · rename_i boundRun
        obtain ⟨currentNorm, restResolved⟩ :=
          unifyPhase_bound_normalized norm resolved boundRun
        have extendsStoreCurrent := unifyPhase_bound_extends norm resolved boundRun
        obtain ⟨extendsCurrentResult, restSolves⟩ :=
          ih currentNorm restResolved run
        exact ⟨MStore.extends_trans extendsStoreCurrent extendsCurrentResult,
          unifyPhase_bound_solves norm resolved boundRun
            extendsCurrentResult restSolves⟩
      · exact nomatch run
      · exact nomatch run

/-- Solved form: after unifying, both sides resolve to the same type. -/
theorem MStore.unify_apply_eq
    {store result : MStore} {left right : Ty}
    (normalized : store.Normalized)
    (run : store.unify left right = some result) :
    result.apply left = result.apply right := by
  change unifyLoop (store.unsolved + 1) store
    [(store.apply left, store.apply right)] = some result at run
  have resolved : ConstraintsResolved store
      [(store.apply left, store.apply right)] := by
    intro constraint member
    simp only [List.mem_singleton] at member
    subst member
    exact ⟨MStore.apply_idem normalized left, MStore.apply_idem normalized right⟩
  obtain ⟨extension, solves⟩ := unifyLoop_correct normalized resolved run
  have equation := solves (store.apply left, store.apply right) (by simp)
  rw [extension left, extension right] at equation
  exact equation

/-! ## Semantics -/

private theorem Ty.WF.mono {ty : Ty} {rigidCount rigidCount' binderCount : Nat}
    (wf : ty.WF rigidCount binderCount) (le : rigidCount ≤ rigidCount') :
    ty.WF rigidCount' binderCount := by
  obtain ⟨hscoped, hfree⟩ := wf
  exact ⟨Ty.Scoped.mono hscoped le, hfree⟩

private theorem Ty.realize_substMVar {valuation : MValuation}
    {ty replacement : Ty} {target : Nat}
    (agrees : valuation target = replacement.realize valuation) :
    (ty.substMVar target replacement).realize valuation =
      ty.realize valuation := by
  induction ty with
  | prim => rfl
  | arrow domain codomain domainIH codomainIH =>
      simp only [Ty.substMVar, Ty.realize]
      rw [domainIH, codomainIH]
  | bvar => rfl
  | rigid => rfl
  | mvar id =>
      by_cases selected : id = target
      · subst selected
        simp only [Ty.substMVar, Ty.realize]
        exact agrees.symm
      · simp only [Ty.substMVar, if_neg selected, Ty.realize]

private theorem Ty.realize_apply_eq {store : MStore} {valuation : MValuation}
    (models : store.Models valuation) {id : Nat} {replacement : Ty}
    (lookup : store.lookup id = some replacement) :
    replacement.realize valuation = valuation id :=
  (models.equation id replacement lookup).symm

/-- Resolving through the store is invisible in every model of it. -/
theorem MStore.Models.realize_apply
    {store : MStore} {valuation : MValuation}
    (models : store.Models valuation) (ty : Ty) :
    (store.apply ty).realize valuation = ty.realize valuation := by
  induction ty with
  | prim => rfl
  | arrow domain codomain domainIH codomainIH =>
      simp only [MStore.apply, Ty.realize]
      rw [domainIH, codomainIH]
  | bvar => rfl
  | rigid => rfl
  | mvar id =>
      simp only [MStore.apply]
      cases lookupEq : store.lookup id with
      | none => simp [lookupEq, Ty.realize]
      | some replacement =>
          simp only [lookupEq, Option.getD_some, Ty.realize]
          exact Ty.realize_apply_eq models lookupEq

private abbrev ConstraintsRealized (valuation : MValuation)
    (constraints : List Constraint) : Prop :=
  ∀ constraint ∈ constraints,
    constraint.1.realize valuation = constraint.2.realize valuation

private theorem ConstraintsRealized.cons_of_equal {valuation : MValuation}
    {left right : Ty} {rest : List Constraint}
    (equal : left = right)
    (restRealized : ConstraintsRealized valuation rest) :
    ConstraintsRealized valuation ((left, right) :: rest) := by
  intro constraint member
  rcases List.mem_cons.mp member with rfl | member
  · simp [equal]
  · exact restRealized constraint member

private theorem ConstraintsRealized.arrows {valuation : MValuation}
    {leftDomain leftCodomain rightDomain rightCodomain : Ty}
    {rest : List Constraint}
    (realized : ConstraintsRealized valuation
      ((leftDomain, rightDomain) :: (leftCodomain, rightCodomain) :: rest)) :
    ConstraintsRealized valuation
      ((Ty.arrow leftDomain leftCodomain,
        Ty.arrow rightDomain rightCodomain) :: rest) := by
  intro constraint member
  rcases List.mem_cons.mp member with rfl | member
  · have domainRealized := realized (leftDomain, rightDomain) (by simp)
    have codomainRealized := realized (leftCodomain, rightCodomain) (by simp)
    simp only [Ty.realize, domainRealized, codomainRealized]
  · exact realized constraint (by simp [member])

private theorem ConstraintsRealized.tail {valuation : MValuation}
    {constraint : Constraint} {rest : List Constraint}
    (realized : ConstraintsRealized valuation (constraint :: rest)) :
    ConstraintsRealized valuation rest := by
  intro current member
  exact realized current (by simp [member])

private theorem Ty.WF.arrow_parts {level binderCount : Nat} {domain codomain : Ty}
    (wf : (Ty.arrow domain codomain).WF level binderCount) :
    domain.WF level binderCount ∧ codomain.WF level binderCount := by
  obtain ⟨hscoped, hfree⟩ := wf
  cases hscoped with
  | arrow hd hc =>
      cases hfree with
      | arrow fd fc => exact ⟨⟨hd, fd⟩, ⟨hc, fc⟩⟩

private theorem Ty.realize_wf_subterm {ty : Ty} {valuation : MValuation} {level : Nat}
    (wf : (ty.realize valuation).WF level 0) {id : Nat} (member : id ∈ ty.mvars) :
    (valuation id).WF level 0 := by
  induction ty with
  | prim => simp [Ty.mvars] at member
  | bvar => simp [Ty.mvars] at member
  | rigid => simp [Ty.mvars] at member
  | mvar other =>
      have same : id = other := by simpa [Ty.mvars] using member
      subst same
      exact wf
  | arrow domain codomain ihd ihc =>
      have split : id ∈ domain.mvars ∨ id ∈ codomain.mvars := by
        simpa [Ty.mvars, List.mem_dedup, List.mem_append] using member
      have parts := Ty.WF.arrow_parts wf
      rcases split with inside | inside
      · exact ihd parts.1 inside
      · exact ihc parts.2 inside

private theorem MStore.models_solve {store : MStore} {id : Nat} {ty : Ty}
    {valuation : MValuation}
    (models : store.Models valuation)
    (guard : store.canBind id ty = true)
    (agrees : valuation id = ty.realize valuation) :
    (store.solve id ty).Models valuation := by
  obtain ⟨entry, hentry, hsolNone, hocc, hscopedB⟩ := MStore.canBind_iff.mp guard
  have hlevel : store.levelOf id = entry.level := by
    unfold MStore.levelOf
    rw [hentry]
    rfl
  refine ⟨?_, ?_⟩
  · intro j entry' hentry'
    by_cases same : j = id
    · subst j
      rw [MStore.solve_getElem?] at hentry'
      rw [hentry] at hentry'
      simp only [Option.map_some, if_pos rfl] at hentry'
      injection hentry' with hEq
      have levelEq : entry'.level = entry.level := by
        rw [← hEq]
        simp
      rw [levelEq]
      exact models.valuationWF id entry hentry
    · rw [MStore.solve_getElem?] at hentry'
      cases hj : store[j]? with
      | none => rw [hj] at hentry'; simp at hentry'
      | some old =>
          rw [hj] at hentry'
          simp only [Option.map_some, if_neg same] at hentry'
          injection hentry' with hEq
          have levelEq : entry'.level =
              (if j ∈ ty.mvars then min old.level (store.levelOf id) else old.level) := by
            rw [← hEq]
          rw [levelEq]
          by_cases mem : j ∈ ty.mvars
          · simp only [mem, if_true]
            have wfId : (valuation id).WF (store.levelOf id) 0 := by
              have := models.valuationWF id entry hentry
              rwa [← hlevel] at this
            have wfRealize : (ty.realize valuation).WF (store.levelOf id) 0 := by
              rwa [← agrees]
            have wfVal := Ty.realize_wf_subterm wfRealize mem
            by_cases hle : store.levelOf id ≤ old.level
            · rw [Nat.min_eq_right hle]
              exact wfVal
            · rw [Nat.min_eq_left (by omega)]
              exact models.valuationWF j old hj
          · simp [mem]
            exact models.valuationWF j old hj
  · intro j solution hlookup
    by_cases same : j = id
    · subst j
      rw [MStore.lookup_solve_self store id ty hentry] at hlookup
      injection hlookup with hsol
      rw [← hsol]
      exact agrees
    · rw [MStore.lookup_solve_of_ne store id j ty same] at hlookup
      rw [Option.map_eq_some_iff] at hlookup
      obtain ⟨previous, hprev, hprevEq⟩ := hlookup
      rw [← hprevEq]
      rw [Ty.realize_substMVar agrees]
      exact models.equation j previous hprev

private theorem MStore.models_of_solve {store : MStore} {id : Nat} {ty : Ty}
    {valuation : MValuation}
    (models : (store.solve id ty).Models valuation)
    (guard : store.canBind id ty = true)
    (agrees : valuation id = ty.realize valuation) :
    store.Models valuation := by
  obtain ⟨entry, hentry, hsolNone, hocc, hscopedB⟩ := MStore.canBind_iff.mp guard
  refine ⟨?_, ?_⟩
  · intro j old hj
    by_cases same : j = id
    · subst j
      have entryEq : (store.solve id ty)[id]? = some { entry with solution := some ty } := by
        rw [MStore.solve_getElem?]
        rw [hentry]
        simp
      have wfNew := models.valuationWF id { entry with solution := some ty } entryEq
      have entryOld : entry = old := by
        rw [hentry] at hj
        exact Option.some.inj hj
      rw [entryOld] at wfNew
      exact wfNew
    · have entryEq : (store.solve id ty)[j]? =
          some { level := if j ∈ ty.mvars then min old.level (store.levelOf id) else old.level,
                 solution := old.solution.map (·.substMVar id ty) } := by
        rw [MStore.solve_getElem?, hj]
        simp [same]
      have wfNew := models.valuationWF j _ entryEq
      have levelLe : (if j ∈ ty.mvars then min old.level (store.levelOf id)
          else old.level) ≤ old.level := by
        by_cases mem : j ∈ ty.mvars
        · simp only [mem, if_true]
          exact Nat.min_le_left _ _
        · simp [mem]
      exact Ty.WF.mono wfNew levelLe
  · intro j previous hprev
    by_cases same : j = id
    · subst j
      have noneLookup : store.lookup id = none := by
        unfold MStore.lookup
        rw [hentry]
        simp [hsolNone]
      rw [noneLookup] at hprev
      exact nomatch hprev
    · have solveLookup : (store.solve id ty).lookup j =
          some (previous.substMVar id ty) := by
        rw [MStore.lookup_solve_of_ne store id j ty same, hprev]
        rfl
      have solved := models.equation j (previous.substMVar id ty) solveLookup
      rw [Ty.realize_substMVar agrees] at solved
      exact solved

private theorem bound_branch_sound_left
    {store result : MStore} {id : Nat} {ty : Ty}
    {rest rest' : List Constraint}
    {valuation : MValuation}
    (run : (if store.canBind id ty then
              (UnifyPhase.bound (store.solve id ty)
                (rest.map (Constraint.substMVar id ty)) : UnifyPhase)
            else .failed) = .bound result rest')
    (models : result.Models valuation)
    (restRealized : ConstraintsRealized valuation rest') :
    store.Models valuation ∧
      ConstraintsRealized valuation ((Ty.mvar id, ty) :: rest) := by
  obtain ⟨guard, resultEq, restEq⟩ := bound_guard_data run
  obtain ⟨entry, hentry, hsolNone, hocc, hscopedB⟩ := MStore.canBind_iff.mp guard
  subst resultEq
  subst restEq
  have agrees : valuation id = ty.realize valuation :=
    models.equation id ty (MStore.lookup_solve_self store id ty hentry)
  refine ⟨MStore.models_of_solve models guard agrees, ?_⟩
  intro constraint member
  rcases List.mem_cons.mp member with rfl | member
  · simpa [Ty.realize] using agrees
  · have substituted := restRealized (Constraint.substMVar id ty constraint)
      (List.mem_map_of_mem member)
    simp only [Constraint.substMVar] at substituted
    rw [Ty.realize_substMVar agrees, Ty.realize_substMVar agrees] at substituted
    exact substituted

private theorem bound_branch_sound_right
    {store result : MStore} {id : Nat} {ty : Ty}
    {rest rest' : List Constraint}
    {valuation : MValuation}
    (run : (if store.canBind id ty then
              (UnifyPhase.bound (store.solve id ty)
                (rest.map (Constraint.substMVar id ty)) : UnifyPhase)
            else .failed) = .bound result rest')
    (models : result.Models valuation)
    (restRealized : ConstraintsRealized valuation rest') :
    store.Models valuation ∧
      ConstraintsRealized valuation ((ty, Ty.mvar id) :: rest) := by
  obtain ⟨guard, resultEq, restEq⟩ := bound_guard_data run
  obtain ⟨entry, hentry, hsolNone, hocc, hscopedB⟩ := MStore.canBind_iff.mp guard
  subst resultEq
  subst restEq
  have agrees : valuation id = ty.realize valuation :=
    models.equation id ty (MStore.lookup_solve_self store id ty hentry)
  refine ⟨MStore.models_of_solve models guard agrees, ?_⟩
  intro constraint member
  rcases List.mem_cons.mp member with rfl | member
  · simpa [Ty.realize] using agrees.symm
  · have substituted := restRealized (Constraint.substMVar id ty constraint)
      (List.mem_map_of_mem member)
    simp only [Constraint.substMVar] at substituted
    rw [Ty.realize_substMVar agrees, Ty.realize_substMVar agrees] at substituted
    exact substituted

private theorem unifyPhase_sound_finished
    {store result : MStore} {fuel : Nat} {constraints : List Constraint}
    {valuation : MValuation}
    (run : unifyPhase store fuel constraints = .finished result)
    (models : result.Models valuation) :
    store.Models valuation ∧
      ConstraintsRealized valuation constraints := by
  induction fuel generalizing constraints with
  | zero =>
      cases constraints with
      | nil =>
          simp only [unifyPhase, UnifyPhase.finished.injEq] at run
          subst result
          exact ⟨models, by intro constraint member; simp at member⟩
      | cons constraint rest => simp [unifyPhase] at run
  | succ fuel ih =>
      cases constraints with
      | nil =>
          simp only [unifyPhase, UnifyPhase.finished.injEq] at run
          subst result
          exact ⟨models, by intro constraint member; simp at member⟩
      | cons constraint rest =>
          obtain ⟨left, right⟩ := constraint
          rw [unifyPhase_cons_eq] at run
          by_cases equal : left = right
          · rw [if_pos equal] at run
            obtain ⟨storeModels, restRealized⟩ := ih run
            exact ⟨storeModels,
              ConstraintsRealized.cons_of_equal equal restRealized⟩
          · rw [if_neg equal] at run
            cases left <;> cases right <;> simp only [] at run
            all_goals first
              | (obtain ⟨storeModels, realized⟩ := ih run
                 exact ⟨storeModels, ConstraintsRealized.arrows realized⟩)
              | (exact (not_finished_of_bound_if run).elim)
              | (cases run)

private theorem unifyPhase_sound_bound
    {store result : MStore} {fuel : Nat}
    {constraints rest : List Constraint}
    {valuation : MValuation}
    (run : unifyPhase store fuel constraints = .bound result rest)
    (models : result.Models valuation)
    (restRealized : ConstraintsRealized valuation rest) :
    store.Models valuation ∧
      ConstraintsRealized valuation constraints := by
  induction fuel generalizing constraints with
  | zero =>
      cases constraints with
      | nil => simp [unifyPhase] at run
      | cons constraint rest => simp [unifyPhase] at run
  | succ fuel ih =>
      cases constraints with
      | nil => simp [unifyPhase] at run
      | cons constraint rest =>
          obtain ⟨left, right⟩ := constraint
          rw [unifyPhase_cons_eq] at run
          by_cases equal : left = right
          · rw [if_pos equal] at run
            obtain ⟨storeModels, restRealized'⟩ := ih run
            exact ⟨storeModels,
              ConstraintsRealized.cons_of_equal equal restRealized'⟩
          · rw [if_neg equal] at run
            cases left <;> cases right <;> simp only [] at run
            all_goals first
              | (obtain ⟨storeModels, realized⟩ := ih run
                 exact ⟨storeModels, ConstraintsRealized.arrows realized⟩)
              | (exact bound_branch_sound_left run models restRealized)
              | (exact bound_branch_sound_right run models restRealized)
              | (cases run)

private theorem unifyLoop_sound
    {fuel : Nat} {store : MStore} {constraints : List Constraint}
    {result : MStore} {valuation : MValuation}
    (run : unifyLoop fuel store constraints = some result)
    (models : result.Models valuation) :
    store.Models valuation ∧
      ConstraintsRealized valuation constraints := by
  induction fuel generalizing store constraints with
  | zero => simp [unifyLoop] at run
  | succ fuel ih =>
      rw [unifyLoop_succ] at run
      split at run
      · rename_i finishedRun
        injection run with resultEq
        subst resultEq
        exact unifyPhase_sound_finished finishedRun models
      · rename_i boundRun
        obtain ⟨boundModels, restRealized⟩ := ih run
        exact unifyPhase_sound_bound boundRun boundModels restRealized
      · exact nomatch run
      · exact nomatch run

/-- Soundness: every model of the result models the input store and equates
the two types. -/
theorem MStore.unify_sound
    {store result : MStore} {left right : Ty} {valuation : MValuation}
    (run : store.unify left right = some result)
    (models : result.Models valuation) :
    store.Models valuation ∧
      left.realize valuation = right.realize valuation := by
  change unifyLoop (store.unsolved + 1) store
    [(store.apply left, store.apply right)] = some result at run
  obtain ⟨storeModels, realized⟩ := unifyLoop_sound run models
  refine ⟨storeModels, ?_⟩
  have equation := realized (store.apply left, store.apply right) (by simp)
  have leftEq := MStore.Models.realize_apply storeModels left
  have rightEq := MStore.Models.realize_apply storeModels right
  rw [leftEq, rightEq] at equation
  exact equation

/-! ## Completeness -/

private theorem Ty.size_realize_ge_of_mem {ty : Ty} {id : Nat}
    {valuation : MValuation} (member : id ∈ ty.mvars) :
    (valuation id).size ≤ (ty.realize valuation).size := by
  induction ty with
  | prim => simp [Ty.mvars] at member
  | bvar => simp [Ty.mvars] at member
  | rigid => simp [Ty.mvars] at member
  | mvar other =>
      have same : id = other := by simpa [Ty.mvars] using member
      subst same
      simp [Ty.realize]
  | arrow domain codomain domainIH codomainIH =>
      have split : id ∈ domain.mvars ∨ id ∈ codomain.mvars := by
        simpa [Ty.mvars, List.mem_dedup, List.mem_append] using member
      rcases split with inside | inside
      · have bounded := domainIH inside
        simp only [Ty.realize, Ty.size]
        omega
      · have bounded := codomainIH inside
        simp only [Ty.realize, Ty.size]
        omega

private theorem Ty.size_realize_gt_of_mem_of_ne {ty : Ty} {id : Nat}
    {valuation : MValuation} (member : id ∈ ty.mvars)
    (different : ty ≠ .mvar id) :
    (valuation id).size < (ty.realize valuation).size := by
  induction ty with
  | prim => simp [Ty.mvars] at member
  | bvar => simp [Ty.mvars] at member
  | rigid => simp [Ty.mvars] at member
  | mvar other =>
      have same : id = other := by simpa [Ty.mvars] using member
      subst same
      exact absurd rfl different
  | arrow domain codomain domainIH codomainIH =>
      have split : id ∈ domain.mvars ∨ id ∈ codomain.mvars := by
        simpa [Ty.mvars, List.mem_dedup, List.mem_append] using member
      have positivity : 0 < (codomain.realize valuation).size := Ty.size_pos _
      simp only [Ty.realize, Ty.size]
      rcases split with inside | inside
      · have bounded := Ty.size_realize_ge_of_mem (valuation := valuation) inside
        omega
      · have bounded := Ty.size_realize_ge_of_mem (valuation := valuation) inside
        omega

private theorem MStore.entry_of_lookup_none {store : MStore} {id : Nat}
    (bound : id < store.length) (lookup : store.lookup id = none) :
    ∃ entry, store[id]? = some entry ∧ entry.solution = none := by
  cases entry : store[id]? with
  | none =>
      exfalso
      have outOfRange := List.getElem?_eq_none_iff.mp entry
      omega
  | some e =>
      refine ⟨e, rfl, ?_⟩
      cases solution : e.solution with
      | none => rfl
      | some replacement =>
          exfalso
          unfold MStore.lookup at lookup
          simp [entry, solution] at lookup

private theorem unifyPhase_cons_eq_mvar_left (store : MStore) (fuel : Nat)
    (id : Nat) (ty : Ty) (rest : List Constraint)
    (different : (Ty.mvar id) ≠ ty) :
    unifyPhase store (fuel + 1) ((Ty.mvar id, ty) :: rest) =
      (if store.canBind id ty then
        (UnifyPhase.bound (store.solve id ty)
          (rest.map (Constraint.substMVar id ty)) : UnifyPhase)
      else .failed) := by
  rw [unifyPhase_cons_eq, if_neg different]

private theorem unifyPhase_cons_eq_mvar_right (store : MStore) (fuel : Nat)
    (left : Ty) (id : Nat) (rest : List Constraint)
    (different : left ≠ .mvar id)
    (notMVar : ∀ j, left ≠ .mvar j) :
    unifyPhase store (fuel + 1) ((left, Ty.mvar id) :: rest) =
      (if store.canBind id left then
        (UnifyPhase.bound (store.solve id left)
          (rest.map (Constraint.substMVar id left)) : UnifyPhase)
      else .failed) := by
  rw [unifyPhase_cons_eq, if_neg different]
  cases left with
  | mvar j => exact absurd rfl (notMVar j)
  | prim => rfl
  | bvar => rfl
  | rigid => rfl
  | arrow => rfl

private theorem unifyPhase_cons_eq_arrow (store : MStore) (fuel : Nat)
    (leftDomain leftCodomain rightDomain rightCodomain : Ty)
    (rest : List Constraint)
    (different : (Ty.arrow leftDomain leftCodomain) ≠
      (Ty.arrow rightDomain rightCodomain)) :
    unifyPhase store (fuel + 1)
        ((Ty.arrow leftDomain leftCodomain,
          Ty.arrow rightDomain rightCodomain) :: rest) =
      unifyPhase store fuel
        ((leftDomain, rightDomain) :: (leftCodomain, rightCodomain) :: rest) := by
  rw [unifyPhase_cons_eq, if_neg different]

private theorem mvar_guard_left {store : MStore} {id : Nat} {ty : Ty}
    {valuation : MValuation}
    (different : (Ty.mvar id) ≠ ty)
    (resolvedId : store.apply (.mvar id) = .mvar id)
    (boundedId : id < store.length)
    (headSolves : valuation id = ty.realize valuation)
    (normalized : store.Normalized)
    (models : store.Models valuation) :
    store.canBind id ty = true := by
  have allocatedLookup : store.lookup id = none :=
    MStore.lookup_none_of_apply_mvar_eq normalized resolvedId
  obtain ⟨entry, hentry, hsolNone⟩ :=
    MStore.entry_of_lookup_none boundedId allocatedLookup
  have occurs : ty.occursMVar id = false := by
    cases occurrence : ty.occursMVar id with
    | false => rfl
    | true =>
        exfalso
        have member : id ∈ ty.mvars :=
          (Ty.occursMVar_iff_mem ty id).mp occurrence
        have strict := Ty.size_realize_gt_of_mem_of_ne
          (valuation := valuation) member (Ne.symm different)
        rw [← headSolves] at strict
        exact absurd strict (lt_irrefl _)
  have wf := models.valuationWF id entry hentry
  rw [headSolves] at wf
  have scopedTy : ty.Scoped entry.level 0 := Ty.scoped_of_realize_scoped wf.1
  have scopedB : ty.scopedB entry.level 0 = true :=
    (Ty.scopedB_iff_scoped ty entry.level 0).mpr scopedTy
  exact MStore.canBind_iff.mpr ⟨entry, hentry, hsolNone, occurs, scopedB⟩

private theorem mvar_guard_right {store : MStore} {id : Nat} {ty : Ty}
    {valuation : MValuation}
    (different : ty ≠ (Ty.mvar id))
    (resolvedId : store.apply (.mvar id) = .mvar id)
    (boundedId : id < store.length)
    (headSolves : ty.realize valuation = valuation id)
    (normalized : store.Normalized)
    (models : store.Models valuation) :
    store.canBind id ty = true := by
  have allocatedLookup : store.lookup id = none :=
    MStore.lookup_none_of_apply_mvar_eq normalized resolvedId
  obtain ⟨entry, hentry, hsolNone⟩ :=
    MStore.entry_of_lookup_none boundedId allocatedLookup
  have occurs : ty.occursMVar id = false := by
    cases occurrence : ty.occursMVar id with
    | false => rfl
    | true =>
        exfalso
        have member : id ∈ ty.mvars :=
          (Ty.occursMVar_iff_mem ty id).mp occurrence
        have strict := Ty.size_realize_gt_of_mem_of_ne
          (valuation := valuation) member different
        rw [headSolves] at strict
        exact absurd strict (lt_irrefl _)
  have wf := models.valuationWF id entry hentry
  have wfTy : (ty.realize valuation).WF entry.level 0 := by
    rw [headSolves]
    exact wf
  have scopedTy : ty.Scoped entry.level 0 := Ty.scoped_of_realize_scoped wfTy.1
  have scopedB : ty.scopedB entry.level 0 = true :=
    (Ty.scopedB_iff_scoped ty entry.level 0).mpr scopedTy
  exact MStore.canBind_iff.mpr ⟨entry, hentry, hsolNone, occurs, scopedB⟩

private theorem phase_bound_left_complete {store : MStore} {fuel : Nat}
    {id : Nat} {ty : Ty} {rest : List Constraint}
    {valuation : MValuation}
    (different : (Ty.mvar id) ≠ ty)
    (resolvedId : store.apply (.mvar id) = .mvar id)
    (resolvedTy : store.apply ty = ty)
    (boundedId : id < store.length)
    (boundedTy : ty.MVarBounded store.length)
    (headSolves : valuation id = ty.realize valuation)
    (normalized : store.Normalized)
    (models : store.Models valuation)
    (storeBounded : store.Bounded store.length)
    (restResolved : ConstraintsResolved store rest)
    (restBounded : ConstraintsBounded store.length rest)
    (restSolves : ConstraintsRealized valuation rest) :
    ∃ result rest', unifyPhase store (fuel + 1) ((Ty.mvar id, ty) :: rest) =
        .bound result rest' ∧
      result.Models valuation ∧ result.Normalized ∧
      result.Bounded result.length ∧ ConstraintsResolved result rest' ∧
      ConstraintsBounded result.length rest' ∧
      ConstraintsRealized valuation rest' ∧
      result.unsolved < store.unsolved := by
  have guard : store.canBind id ty = true :=
    mvar_guard_left different resolvedId boundedId headSolves normalized models
  obtain ⟨entry, hentry, hsolNone, hocc, hscopedB⟩ := MStore.canBind_iff.mp guard
  refine ⟨store.solve id ty, rest.map (Constraint.substMVar id ty), ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_⟩
  · rw [unifyPhase_cons_eq, if_neg different]
    simp [guard]
  · exact MStore.models_solve models guard headSolves
  · exact MStore.solve_normalized normalized guard resolvedTy
  · have boundedSolve := MStore.solve_bounded (id := id) storeBounded boundedTy
    simpa [MStore.solve_length] using boundedSolve
  · intro constraint member
    rcases List.mem_map.mp member with ⟨old, inOld, rfl⟩
    exact ⟨MStore.apply_subst_resolved normalized hocc resolvedTy
             (restResolved old inOld).1,
           MStore.apply_subst_resolved normalized hocc resolvedTy
             (restResolved old inOld).2⟩
  · intro constraint member
    rcases List.mem_map.mp member with ⟨old, inOld, rfl⟩
    have oldBounded := restBounded old inOld
    rw [MStore.solve_length]
    exact ⟨Ty.substMVar_mvarBounded oldBounded.1 boundedTy,
      Ty.substMVar_mvarBounded oldBounded.2 boundedTy⟩
  · intro constraint member
    rcases List.mem_map.mp member with ⟨old, inOld, rfl⟩
    have oldSolves := restSolves old inOld
    simpa only [Constraint.substMVar, Ty.realize_substMVar headSolves] using oldSolves
  · exact MStore.unsolved_solve_lt store id ty hentry hsolNone

private theorem phase_bound_right_complete {store : MStore} {fuel : Nat}
    {id : Nat} {ty : Ty} {rest : List Constraint}
    {valuation : MValuation}
    (different : ty ≠ (Ty.mvar id))
    (resolvedTy : store.apply ty = ty)
    (resolvedId : store.apply (.mvar id) = .mvar id)
    (boundedId : id < store.length)
    (boundedTy : ty.MVarBounded store.length)
    (headSolves : ty.realize valuation = valuation id)
    (phaseBase : unifyPhase store (fuel + 1) ((ty, Ty.mvar id) :: rest) =
      (if store.canBind id ty then
        (UnifyPhase.bound (store.solve id ty)
          (rest.map (Constraint.substMVar id ty)) : UnifyPhase)
      else .failed))
    (normalized : store.Normalized)
    (models : store.Models valuation)
    (storeBounded : store.Bounded store.length)
    (restResolved : ConstraintsResolved store rest)
    (restBounded : ConstraintsBounded store.length rest)
    (restSolves : ConstraintsRealized valuation rest) :
    ∃ result rest', unifyPhase store (fuel + 1) ((ty, Ty.mvar id) :: rest) =
        .bound result rest' ∧
      result.Models valuation ∧ result.Normalized ∧
      result.Bounded result.length ∧ ConstraintsResolved result rest' ∧
      ConstraintsBounded result.length rest' ∧
      ConstraintsRealized valuation rest' ∧
      result.unsolved < store.unsolved := by
  have guard : store.canBind id ty = true :=
    mvar_guard_right different resolvedId boundedId headSolves normalized models
  obtain ⟨entry, hentry, hsolNone, hocc, hscopedB⟩ := MStore.canBind_iff.mp guard
  have agrees : valuation id = ty.realize valuation := headSolves.symm
  refine ⟨store.solve id ty, rest.map (Constraint.substMVar id ty), ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_⟩
  · rw [phaseBase, if_pos guard]
  · exact MStore.models_solve models guard agrees
  · exact MStore.solve_normalized normalized guard resolvedTy
  · have boundedSolve := MStore.solve_bounded (id := id) storeBounded boundedTy
    simpa [MStore.solve_length] using boundedSolve
  · intro constraint member
    rcases List.mem_map.mp member with ⟨old, inOld, rfl⟩
    exact ⟨MStore.apply_subst_resolved normalized hocc resolvedTy
             (restResolved old inOld).1,
           MStore.apply_subst_resolved normalized hocc resolvedTy
             (restResolved old inOld).2⟩
  · intro constraint member
    rcases List.mem_map.mp member with ⟨old, inOld, rfl⟩
    have oldBounded := restBounded old inOld
    rw [MStore.solve_length]
    exact ⟨Ty.substMVar_mvarBounded oldBounded.1 boundedTy,
      Ty.substMVar_mvarBounded oldBounded.2 boundedTy⟩
  · intro constraint member
    rcases List.mem_map.mp member with ⟨old, inOld, rfl⟩
    have oldSolves := restSolves old inOld
    simpa only [Constraint.substMVar, Ty.realize_substMVar agrees] using oldSolves
  · exact MStore.unsolved_solve_lt store id ty hentry hsolNone

private theorem ConstraintsRealized.arrow_parts {valuation : MValuation}
    {leftDomain leftCodomain rightDomain rightCodomain : Ty}
    {rest : List Constraint}
    (head : (Ty.arrow leftDomain leftCodomain).realize valuation =
      (Ty.arrow rightDomain rightCodomain).realize valuation)
    (restSolves : ConstraintsRealized valuation rest) :
    ConstraintsRealized valuation
      ((leftDomain, rightDomain) :: (leftCodomain, rightCodomain) :: rest) := by
  have parts := head
  simp only [Ty.realize, Ty.arrow.injEq] at parts
  intro constraint member
  rcases List.mem_cons.mp member with rfl | member
  · exact parts.1
  · rcases List.mem_cons.mp member with rfl | member
    · exact parts.2
    · exact restSolves constraint member

private theorem unifyPhase_complete {store : MStore} {fuel : Nat}
    {constraints : List Constraint}
    {valuation : MValuation}
    (enough : Constraints.size constraints ≤ fuel)
    (normalized : store.Normalized)
    (bounded : store.Bounded store.length)
    (models : store.Models valuation)
    (resolved : ConstraintsResolved store constraints)
    (constraintsBounded : ConstraintsBounded store.length constraints)
    (solves : ConstraintsRealized valuation constraints) :
    (∃ result, unifyPhase store fuel constraints = .finished result ∧
        result.Models valuation) ∨
    (∃ result rest, unifyPhase store fuel constraints = .bound result rest ∧
        result.Models valuation ∧ result.Normalized ∧
        result.Bounded result.length ∧ ConstraintsResolved result rest ∧
        ConstraintsBounded result.length rest ∧
        ConstraintsRealized valuation rest ∧
        result.unsolved < store.unsolved) := by
  induction fuel generalizing constraints with
  | zero =>
      have empty : constraints = [] := by
        cases constraints with
        | nil => rfl
        | cons constraint rest =>
            have positive := Constraints.size_nonempty
              (constraints := constraint :: rest) (by simp)
            omega
      subst empty
      exact Or.inl ⟨store, rfl, models⟩
  | succ fuel ih =>
      cases constraints with
      | nil => exact Or.inl ⟨store, rfl, models⟩
      | cons constraint rest =>
          obtain ⟨left, right⟩ := constraint
          have headResolved := resolved (left, right) (by simp)
          have restResolved : ConstraintsResolved store rest := by
            intro current member
            exact resolved current (by simp [member])
          have headBounded := constraintsBounded (left, right) (by simp)
          have restBounded : ConstraintsBounded store.length rest := by
            intro current member
            exact constraintsBounded current (by simp [member])
          have headSolves := solves (left, right) (by simp)
          have restSolves : ConstraintsRealized valuation rest :=
            ConstraintsRealized.tail solves
          by_cases equal : left = right
          · rw [unifyPhase_cons_eq, if_pos equal]
            refine ih ?_ restResolved restBounded restSolves
            have h : left.size + right.size + Constraints.size rest ≤ fuel + 1 := by
              simpa [Constraints.size_cons] using enough
            have leftPos := Ty.size_pos left
            have rightPos := Ty.size_pos right
            omega
          · cases left with
            | mvar id =>
                exact Or.inr (phase_bound_left_complete
                  (ty := right) (by simpa using equal)
                  headResolved.1 headResolved.2
                  (headBounded.1 id (by simp [Ty.mvars])) headBounded.2
                  (by simpa [Ty.realize] using headSolves)
                  normalized models bounded restResolved restBounded restSolves)
            | prim name =>
                cases right with
                | mvar id =>
                    have phaseBase := unifyPhase_cons_eq_mvar_right store fuel
                      (.prim name) id rest (by simpa using equal)
                      (fun j impossible => nomatch impossible)
                    exact Or.inr (phase_bound_right_complete
                      (ty := .prim name) (by simpa using equal)
                      headResolved.1 headResolved.2
                      (headBounded.2 id (by simp [Ty.mvars])) headBounded.1
                      (by simpa [Ty.realize] using headSolves)
                      phaseBase normalized models bounded restResolved
                      restBounded restSolves)
                | prim other =>
                  exfalso
                  have head := headSolves
                  simp only [Ty.realize] at head
                  exact equal head
                | bvar index =>
                  exfalso
                  have head := headSolves
                  simp only [Ty.realize] at head
                  cases head
                | rigid level =>
                  exfalso
                  have head := headSolves
                  simp only [Ty.realize] at head
                  cases head
                | arrow rd rc =>
                  exfalso
                  have head := headSolves
                  simp only [Ty.realize] at head
                  cases head
            | bvar index =>
                cases right with
                | mvar id =>
                    have phaseBase := unifyPhase_cons_eq_mvar_right store fuel
                      (.bvar index) id rest (by simpa using equal)
                      (fun j impossible => nomatch impossible)
                    exact Or.inr (phase_bound_right_complete
                      (ty := .bvar index) (by simpa using equal)
                      headResolved.1 headResolved.2
                      (headBounded.2 id (by simp [Ty.mvars])) headBounded.1
                      (by simpa [Ty.realize] using headSolves)
                      phaseBase normalized models bounded restResolved
                      restBounded restSolves)
                | prim other =>
                  exfalso
                  have head := headSolves
                  simp only [Ty.realize] at head
                  cases head
                | bvar other =>
                  exfalso
                  have head := headSolves
                  simp only [Ty.realize] at head
                  exact equal head
                | rigid level =>
                  exfalso
                  have head := headSolves
                  simp only [Ty.realize] at head
                  cases head
                | arrow rd rc =>
                  exfalso
                  have head := headSolves
                  simp only [Ty.realize] at head
                  cases head
            | rigid level =>
                cases right with
                | mvar id =>
                    have phaseBase := unifyPhase_cons_eq_mvar_right store fuel
                      (.rigid level) id rest (by simpa using equal)
                      (fun j impossible => nomatch impossible)
                    exact Or.inr (phase_bound_right_complete
                      (ty := .rigid level) (by simpa using equal)
                      headResolved.1 headResolved.2
                      (headBounded.2 id (by simp [Ty.mvars])) headBounded.1
                      (by simpa [Ty.realize] using headSolves)
                      phaseBase normalized models bounded restResolved
                      restBounded restSolves)
                | prim other =>
                  exfalso
                  have head := headSolves
                  simp only [Ty.realize] at head
                  cases head
                | bvar index =>
                  exfalso
                  have head := headSolves
                  simp only [Ty.realize] at head
                  cases head
                | rigid other =>
                  exfalso
                  have head := headSolves
                  simp only [Ty.realize] at head
                  exact equal head
                | arrow rd rc =>
                  exfalso
                  have head := headSolves
                  simp only [Ty.realize] at head
                  cases head
            | arrow ld lc =>
                cases right with
                | mvar id =>
                    have phaseBase := unifyPhase_cons_eq_mvar_right store fuel
                      (.arrow ld lc) id rest (by simpa using equal)
                      (fun j impossible => nomatch impossible)
                    exact Or.inr (phase_bound_right_complete
                      (ty := .arrow ld lc) (by simpa using equal)
                      headResolved.1 headResolved.2
                      (headBounded.2 id (by simp [Ty.mvars])) headBounded.1
                      (by simpa [Ty.realize] using headSolves)
                      phaseBase normalized models bounded restResolved
                      restBounded restSolves)
                | prim other =>
                  exfalso
                  have head := headSolves
                  simp only [Ty.realize] at head
                  cases head
                | bvar index =>
                  exfalso
                  have head := headSolves
                  simp only [Ty.realize] at head
                  cases head
                | rigid level =>
                  exfalso
                  have head := headSolves
                  simp only [Ty.realize] at head
                  cases head
                | arrow rd rc =>
                    have phaseEq := unifyPhase_cons_eq_arrow store fuel
                      ld lc rd rc rest (by simpa using equal)
                    rw [phaseEq]
                    have enoughNew : Constraints.size
                        ((ld, rd) :: (lc, rc) :: rest) ≤ fuel := by
                      simp only [Constraints.size_cons, Ty.size] at enough ⊢
                      omega
                    exact ih enoughNew (ConstraintsResolved.arrows resolved)
                      (ConstraintsBounded.arrows headBounded restBounded)
                      (ConstraintsRealized.arrow_parts headSolves restSolves)

private theorem unifyLoop_complete {fuel : Nat} {store : MStore}
    {constraints : List Constraint}
    {valuation : MValuation}
    (fuelEnough : store.unsolved + 1 ≤ fuel)
    (normalized : store.Normalized)
    (bounded : store.Bounded store.length)
    (models : store.Models valuation)
    (resolved : ConstraintsResolved store constraints)
    (constraintsBounded : ConstraintsBounded store.length constraints)
    (solves : ConstraintsRealized valuation constraints) :
    ∃ result, unifyLoop fuel store constraints = some result ∧
      result.Models valuation := by
  induction fuel generalizing store constraints with
  | zero => omega
  | succ fuel ih =>
      rw [unifyLoop_succ]
      have phase := unifyPhase_complete (le_refl (Constraints.size constraints))
        normalized bounded models resolved constraintsBounded solves
      rcases phase with
        ⟨result, finishedRun, resultModels⟩ |
        ⟨result, rest, boundRun, resultModels, resultNorm, resultBounded,
          restResolved, restBounded, restSolves, resultUnsolved⟩
      · rw [finishedRun]
        exact ⟨result, rfl, resultModels⟩
      · rw [boundRun]
        refine ih ?_ resultNorm resultBounded resultModels restResolved
          restBounded restSolves
        omega

/-- Completeness: if some model of a normalized, allocated store equates the
two types, unification succeeds and that model also models the result. -/
theorem MStore.unify_complete
    {store : MStore} {left right : Ty} {valuation : MValuation}
    (normalized : store.Normalized)
    (bounded : store.Bounded store.length)
    (leftBounded : left.MVarBounded store.length)
    (rightBounded : right.MVarBounded store.length)
    (models : store.Models valuation)
    (unifies : left.realize valuation = right.realize valuation) :
    ∃ result, store.unify left right = some result ∧
      result.Models valuation := by
  change ∃ result, unifyLoop (store.unsolved + 1) store
    [(store.apply left, store.apply right)] = some result ∧
      result.Models valuation
  have resolved : ConstraintsResolved store
      [(store.apply left, store.apply right)] := by
    intro constraint member
    simp only [List.mem_singleton] at member
    subst member
    exact ⟨MStore.apply_idem normalized left, MStore.apply_idem normalized right⟩
  have constraintsBounded : ConstraintsBounded store.length
      [(store.apply left, store.apply right)] := by
    intro constraint member
    simp only [List.mem_singleton] at member
    subst member
    exact ⟨MStore.apply_bounded bounded leftBounded,
      MStore.apply_bounded bounded rightBounded⟩
  have solves : ConstraintsRealized valuation
      [(store.apply left, store.apply right)] := by
    intro constraint member
    simp only [List.mem_singleton] at member
    subst member
    have leftEq := MStore.Models.realize_apply models left
    have rightEq := MStore.Models.realize_apply models right
    rw [leftEq, rightEq]
    exact unifies
  exact unifyLoop_complete le_rfl normalized bounded models resolved
    constraintsBounded solves

end EPL
