import EPL2.Spec.Models

/-!
# Unification computes most general unifiers

The models of `MStore.unify`'s result are exactly the models of its input
that equate the two types (`unify_sound`, `unify_complete`). The remaining
theorems are the invariants inference needs.

**Proof guidance.** Port `EPL/Properties/Unification.lean`, which proves all
of these for the previous representation of the same algorithm (there
`Ty.mvar`, `MVarBounded`, a deduplicated `Ty.mvars`, `occursMVar`, `scopedB`,
separate `Leveled`/`Bounded`/`Normalized`; here `Ty.var`, `Ty.Allocated`,
plain `Ty.vars`, `vars.contains`, `decide (ty.WF _)`, one `MStore.Safe`).
`unify_anchored` ports from `MStore.solve_anchored_of_canBind` and its
neighbours in `EPL/Properties/InferenceSound.lean`. Prove each property for
`MStore.solve` first, then for one `unifyPhase`, then for `unifyLoop` by
induction on the fuel.
-/

namespace EPL2

/-! ## Unfolding lemmas

`Ty.substVar`, `MStore.apply` and `Ty.realize` are `Ty.bind` instances; these
equations hold by definition and let the old-style structural proofs go
through. They are local simp lemmas so that nothing leaks into importers. -/

private theorem Ty.bind_prim (name : PrimTy) (f : Nat → InfTy) :
    (Ty.prim name).bind f = .prim name := rfl
private theorem Ty.bind_arrow_eq (domain codomain : InfTy) (f : Nat → InfTy) :
    (Ty.arrow domain codomain).bind f = .arrow (domain.bind f) (codomain.bind f) := rfl
private theorem Ty.bind_con (id : Nat) (f : Nat → InfTy) :
    (Ty.con id).bind f = .con id := rfl
private theorem Ty.bind_app_eq (function argument : InfTy) (f : Nat → InfTy) :
    (Ty.app function argument).bind f = .app (function.bind f) (argument.bind f) := rfl
private theorem Ty.bind_bvar_eq (index : Nat) (f : Nat → InfTy) :
    (Ty.bvar index).bind f = .bvar index := rfl
private theorem Ty.bind_rigid_eq (level : Nat) (f : Nat → InfTy) :
    (Ty.rigid level).bind f = .rigid level := rfl
private theorem Ty.bind_var_eq {V W : Type} (id : V) (f : V → Ty W) :
    (Ty.var id).bind f = f id := rfl

private theorem Ty.substVar_prim (name : PrimTy) (target : Nat) (replacement : InfTy) :
    (Ty.prim name).substVar target replacement = .prim name := rfl
private theorem Ty.substVar_arrow (domain codomain : InfTy) (target : Nat) (replacement : InfTy) :
    (Ty.arrow domain codomain).substVar target replacement =
      .arrow (domain.substVar target replacement) (codomain.substVar target replacement) := rfl
private theorem Ty.substVar_con (id : Nat) (target : Nat) (replacement : InfTy) :
    (Ty.con id).substVar target replacement = .con id := rfl
private theorem Ty.substVar_app (function argument : InfTy) (target : Nat) (replacement : InfTy) :
    (Ty.app function argument).substVar target replacement =
      .app (function.substVar target replacement) (argument.substVar target replacement) := rfl
private theorem Ty.substVar_bvar (index : Nat) (target : Nat) (replacement : InfTy) :
    (Ty.bvar index).substVar target replacement = .bvar index := rfl
private theorem Ty.substVar_rigid (level : Nat) (target : Nat) (replacement : InfTy) :
    (Ty.rigid level).substVar target replacement = .rigid level := rfl
private theorem Ty.substVar_var (id : Nat) (target : Nat) (replacement : InfTy) :
    (Ty.var id).substVar target replacement = if id = target then replacement else .var id := rfl

private theorem Ty.realize_prim (name : PrimTy) (valuation : Valuation) :
    (Ty.prim name).realize valuation = .prim name := rfl
private theorem Ty.realize_arrow (domain codomain : InfTy) (valuation : Valuation) :
    (Ty.arrow domain codomain).realize valuation =
      .arrow (domain.realize valuation) (codomain.realize valuation) := rfl
private theorem Ty.realize_con (id : Nat) (valuation : Valuation) :
    (Ty.con id).realize valuation = .con id := rfl
private theorem Ty.realize_app (function argument : InfTy) (valuation : Valuation) :
    (Ty.app function argument).realize valuation =
      .app (function.realize valuation) (argument.realize valuation) := rfl
private theorem Ty.realize_bvar (index : Nat) (valuation : Valuation) :
    (Ty.bvar index).realize valuation = .bvar index := rfl
private theorem Ty.realize_rigid (level : Nat) (valuation : Valuation) :
    (Ty.rigid level).realize valuation = .rigid level := rfl
private theorem Ty.realize_var (id : Nat) (valuation : Valuation) :
    (Ty.var id).realize valuation = valuation id := rfl

private theorem MStore.apply_prim (store : MStore) (name : PrimTy) :
    store.apply (.prim name) = .prim name := rfl
private theorem MStore.apply_arrow (store : MStore) (domain codomain : InfTy) :
    store.apply (.arrow domain codomain) = .arrow (store.apply domain) (store.apply codomain) := rfl
private theorem MStore.apply_con (store : MStore) (id : Nat) :
    store.apply (.con id) = .con id := rfl
private theorem MStore.apply_app (store : MStore) (function argument : InfTy) :
    store.apply (.app function argument) = .app (store.apply function) (store.apply argument) := rfl
private theorem MStore.apply_bvar (store : MStore) (index : Nat) :
    store.apply (.bvar index) = .bvar index := rfl
private theorem MStore.apply_rigid (store : MStore) (level : Nat) :
    store.apply (.rigid level) = .rigid level := rfl
private theorem MStore.apply_var (store : MStore) (id : Nat) :
    store.apply (.var id) = (store.lookup id).getD (.var id) := rfl

attribute [local simp] Ty.bind_prim Ty.bind_arrow_eq Ty.bind_con Ty.bind_app_eq
  Ty.bind_bvar_eq Ty.bind_rigid_eq Ty.bind_var_eq
  Ty.substVar_prim Ty.substVar_arrow Ty.substVar_con Ty.substVar_app
  Ty.substVar_bvar Ty.substVar_rigid Ty.substVar_var
  Ty.realize_prim Ty.realize_arrow Ty.realize_con Ty.realize_app
  Ty.realize_bvar Ty.realize_rigid Ty.realize_var
  MStore.apply_prim MStore.apply_arrow MStore.apply_con MStore.apply_app
  MStore.apply_bvar MStore.apply_rigid MStore.apply_var

/-! ## Component views of the store invariants

`Safe` bundles the three properties the algorithm preserves; the phases need
them separately, so we name their types. -/

private abbrev MStore.Normalized (store : MStore) : Prop :=
  ∀ (id : Nat) (ty : InfTy), store.lookup id = some ty →
    ∀ m ∈ ty.vars, store.lookup m = none

private abbrev MStore.Leveled (store : MStore) : Prop :=
  ∀ (id : Nat) (entry : MEntry) (ty : InfTy), store[id]? = some entry →
    entry.solution = some ty →
    ty.WF entry.level ∧ ty.LevelBounded store entry.level

private abbrev MStore.Allocates (store : MStore) : Prop :=
  ∀ (id : Nat) (ty : InfTy), store.lookup id = some ty → ty.Allocated store

/-! ## Elementary helpers -/

private theorem Ty.size_pos {V : Type} (ty : Ty V) : 0 < ty.size := by
  cases ty <;> simp [Ty.size]

private theorem Constraints.size_cons (constraint : Constraint) (rest : List Constraint) :
    Constraints.size (constraint :: rest) =
      constraint.1.size + constraint.2.size + Constraints.size rest := by
  simp [Constraints.size]

private theorem Constraints.size_tail (constraint : Constraint) (rest : List Constraint) :
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

/-! ## Scoping and allocation helpers -/

private theorem Ty.Allocated.left {store : MStore} {domain codomain : InfTy}
    (bounded : (Ty.arrow domain codomain).Allocated store) : domain.Allocated store := by
  intro id member
  exact bounded id (by simp [Ty.vars, member])

private theorem Ty.Allocated.right {store : MStore} {domain codomain : InfTy}
    (bounded : (Ty.arrow domain codomain).Allocated store) : codomain.Allocated store := by
  intro id member
  exact bounded id (by simp [Ty.vars, member])

private theorem Ty.Allocated.appLeft {store : MStore} {function argument : InfTy}
    (bounded : (Ty.app function argument).Allocated store) : function.Allocated store := by
  intro id member
  exact bounded id (by simp [Ty.vars, member])

private theorem Ty.Allocated.appRight {store : MStore} {function argument : InfTy}
    (bounded : (Ty.app function argument).Allocated store) : argument.Allocated store := by
  intro id member
  exact bounded id (by simp [Ty.vars, member])

private theorem Ty.substVar_wf {ty replacement : InfTy} {level target : Nat}
    (typeWf : ty.WF level) (replacementWf : replacement.WF level) :
    (ty.substVar target replacement).WF level := by
  rw [Ty.substVar]
  refine Ty.scoped_bind typeWf ?_
  intro v _
  by_cases selected : v = target
  · simp [selected, replacementWf]
  · simp [Ty.Scoped, selected]

private theorem Ty.mem_vars_substVar {ty replacement : InfTy} {target id : Nat}
    (member : id ∈ (ty.substVar target replacement).vars) :
    id ∈ ty.vars ∨ id ∈ replacement.vars := by
  rw [Ty.substVar] at member
  rw [Ty.mem_vars_bind] at member
  obtain ⟨v, inTy, inImage⟩ := member
  by_cases selected : v = target
  · exact Or.inr (by simpa [selected] using inImage)
  · have idEq : id = v := by simpa [selected, Ty.vars] using inImage
    subst idEq
    exact Or.inl inTy

private theorem Ty.mem_vars_substVar' {ty replacement : InfTy} {target id : Nat}
    (member : id ∈ (ty.substVar target replacement).vars) :
    (id ≠ target ∧ id ∈ ty.vars) ∨ id ∈ replacement.vars := by
  rw [Ty.substVar] at member
  rw [Ty.mem_vars_bind] at member
  obtain ⟨v, inTy, inImage⟩ := member
  by_cases selected : v = target
  · exact Or.inr (by simpa [selected] using inImage)
  · have idEq : id = v := by simpa [selected, Ty.vars] using inImage
    subst idEq
    exact Or.inl ⟨selected, inTy⟩

private theorem Ty.mem_vars_substVar_subset {previous replacement : InfTy} {target id : Nat}
    (member : id ∈ (previous.substVar target replacement).vars) :
    id ∈ previous.vars ∨ (target ∈ previous.vars ∧ id ∈ replacement.vars) := by
  rw [Ty.substVar] at member
  rw [Ty.mem_vars_bind] at member
  obtain ⟨v, inPrevious, inImage⟩ := member
  by_cases selected : v = target
  · subst selected
    exact Or.inr ⟨inPrevious, by simpa using inImage⟩
  · have idEq : id = v := by simpa [selected, Ty.vars] using inImage
    subst idEq
    exact Or.inl inPrevious

private theorem Ty.substVar_eq_self_of_not_mem {ty : InfTy} {target : Nat} {replacement : InfTy}
    (absent : target ∉ ty.vars) :
    ty.substVar target replacement = ty := by
  change ty.bind (fun v => if v = target then replacement else .var v) = ty
  refine (Ty.bind_congr (ty := ty)
    (f := fun v => if v = target then replacement else .var v) (g := .var) ?_).trans
    (Ty.bind_var ty)
  intro v member
  have different : v ≠ target := fun same => absent (same ▸ member)
  simp [different]

private theorem Ty.contains_iff_mem (ty : InfTy) (id : Nat) :
    ty.vars.contains id = true ↔ id ∈ ty.vars :=
  List.contains_iff_mem

private theorem Ty.scoped_of_realize_scoped {ty : InfTy} {valuation : Valuation} {level : Nat}
    (wf : (ty.realize valuation).WF level) : ty.WF level :=
  (Ty.scoped_of_bind (f := valuation) wf).1

/-! ## Solving: elementary structure -/

private theorem MStore.lookup_none_of_apply_var_eq {store : MStore}
    (norm : store.Normalized) {id : Nat}
    (equal : store.apply (.var id) = .var id) :
    store.lookup id = none := by
  cases lookupEq : store.lookup id with
  | none => rfl
  | some replacement =>
      have applied : store.apply (.var id) = replacement := by
        simp [lookupEq]
      have replacementEq : replacement = .var id := by
        rw [applied] at equal
        exact equal
      have member : id ∈ replacement.vars := by
        rw [replacementEq]
        simp [Ty.vars]
      have noneLookup := norm id replacement lookupEq id member
      rw [lookupEq] at noneLookup
      exact nomatch noneLookup

private theorem MStore.lookup_none_of_resolved {store : MStore} {ty : InfTy}
    (norm : store.Normalized) (resolved : store.apply ty = ty)
    {id : Nat} (member : id ∈ ty.vars) :
    store.lookup id = none := by
  induction ty with
  | prim => simp [Ty.vars] at member
  | bvar => simp [Ty.vars] at member
  | rigid => simp [Ty.vars] at member
  | arrow domain codomain domainIH codomainIH =>
      have split : id ∈ domain.vars ∨ id ∈ codomain.vars := by
        simpa [Ty.vars] using member
      have components : store.apply domain = domain ∧ store.apply codomain = codomain := by
        simpa using resolved
      rcases split with inside | inside
      · exact domainIH components.1 inside
      · exact codomainIH components.2 inside
  | con => simp [Ty.vars] at member
  | app function argument functionIH argumentIH =>
      have split : id ∈ function.vars ∨ id ∈ argument.vars := by
        simpa [Ty.vars] using member
      have components : store.apply function = function ∧ store.apply argument = argument := by
        simpa using resolved
      rcases split with inside | inside
      · exact functionIH components.1 inside
      · exact argumentIH components.2 inside
  | var other =>
      have same : id = other := by simpa [Ty.vars] using member
      subst same
      exact MStore.lookup_none_of_apply_var_eq norm resolved

private theorem MStore.solve_getElem? (store : MStore) (id : Nat) (ty : InfTy) (j : Nat) :
    (store.solve id ty)[j]? =
      (store[j]?).map (fun entry =>
        if j = id then { entry with solution := some ty }
        else
          { level := if j ∈ ty.vars then min entry.level (store.levelOf id) else entry.level,
            solution := entry.solution.map (·.substVar id ty) }) := by
  simp only [MStore.solve, List.getElem?_mapIdx]

private theorem MStore.solve_length (store : MStore) (id : Nat) (ty : InfTy) :
    (store.solve id ty).length = store.length := by
  simp [MStore.solve]

private theorem MStore.lookup_solve_of_ne (store : MStore) (id j : Nat) (ty : InfTy)
    (different : j ≠ id) :
    (store.solve id ty).lookup j =
      (store.lookup j).map (·.substVar id ty) := by
  unfold MStore.lookup
  rw [MStore.solve_getElem?]
  cases h : store[j]? with
  | none => simp
  | some entry => simp [different]

private theorem MStore.lookup_solve_self (store : MStore) (id : Nat) (ty : InfTy)
    {e : MEntry} (entry : store[id]? = some e) :
    (store.solve id ty).lookup id = some ty := by
  unfold MStore.lookup
  rw [MStore.solve_getElem?]
  simp [entry]

private theorem MStore.levelOf_solve (store : MStore) (id j : Nat) (ty : InfTy) :
    (store.solve id ty).levelOf j =
      if j = id then store.levelOf id
      else if j ∈ ty.vars then min (store.levelOf j) (store.levelOf id)
      else store.levelOf j := by
  by_cases same : j = id
  · subst same
    unfold MStore.levelOf
    rw [MStore.solve_getElem?]
    cases h : store[j]? <;> simp
  · unfold MStore.levelOf
    rw [MStore.solve_getElem?]
    cases h : store[j]? <;> simp [same, MStore.levelOf]

private theorem MStore.levelOf_solve_le (store : MStore) (id j : Nat) (ty : InfTy) :
    (store.solve id ty).levelOf j ≤ store.levelOf j := by
  rw [MStore.levelOf_solve]
  by_cases same : j = id
  · simp [same]
  · by_cases mem : j ∈ ty.vars
    · simp only [same, mem, if_true, if_false]
      exact Nat.min_le_left _ _
    · simp [same, mem]

private theorem MStore.canBind_iff {store : MStore} {id : Nat} {ty : InfTy} :
    store.canBind id ty = true ↔
      ∃ entry, store[id]? = some entry ∧ entry.solution = none ∧
        ty.vars.contains id = false ∧ ty.WF entry.level := by
  unfold MStore.canBind
  cases h : store[id]? with
  | none => simp
  | some entry =>
      simp only [Bool.and_eq_true, Option.isNone_iff_eq_none,
        Option.some.injEq, decide_eq_true_eq]
      constructor
      · rintro ⟨⟨hsol, hocc⟩, hscoped⟩
        exact ⟨entry, rfl, hsol, by simpa using hocc, hscoped⟩
      · rintro ⟨entry', rfl, hsol, hocc, hscoped⟩
        exact ⟨⟨hsol, by simpa using hocc⟩, hscoped⟩

private theorem MStore.unsolved_solve_lt (store : MStore) (id : Nat) (ty : InfTy)
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
      | some e' => simp
    · rw [List.getElem?_set_ne (Ne.symm same), List.getElem?_map]
      cases h : store[j]? <;> simp [same]
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

private theorem MStore.solve_leveled {store : MStore} {id : Nat} {ty : InfTy}
    (leveled : store.Leveled) (norm : store.Normalized)
    (guard : store.canBind id ty = true)
    (resolved : store.apply ty = ty) :
    (store.solve id ty).Leveled := by
  obtain ⟨entry, hentry, hsolNone, hocc, hwf⟩ := MStore.canBind_iff.mp guard
  have hlevel : store.levelOf id = entry.level := by
    unfold MStore.levelOf
    rw [hentry]
    rfl
  intro j entry' solution hEntry hSol
  by_cases same : j = id
  · subst j
    rw [MStore.solve_getElem?] at hEntry
    rw [hentry] at hEntry
    simp only [Option.map_some] at hEntry
    injection hEntry with hEntryEq
    have hlevelEq : entry'.level = entry.level := by
      rw [← hEntryEq]
      simp
    have hsolEq : solution = ty := by
      rw [← hEntryEq] at hSol
      simpa using hSol.symm
    refine ⟨?_, ?_⟩
    · rw [hlevelEq, hsolEq]
      exact hwf
    · rw [hlevelEq, hsolEq]
      intro m hm
      have hmne : m ≠ id := by
        intro sameId
        subst m
        have htrue : ty.vars.contains id = true :=
          (Ty.contains_iff_mem ty id).mpr hm
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
        simp only [Option.map_some, if_neg same] at hEntry
        injection hEntry with hEntryEq
        have hsol0 : entry0.solution.map (·.substVar id ty) = some solution := by
          rw [← hEntryEq] at hSol
          simpa using hSol
        obtain ⟨previous, hprevSol, hprevEq⟩ := Option.map_eq_some_iff.mp hsol0
        obtain ⟨hprevWf, hprevBounded⟩ := leveled j entry0 previous hj hprevSol
        have hnotmem : j ∉ ty.vars := by
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
          by_cases hid : id ∈ previous.vars
          · have hle : store.levelOf id ≤ entry0.level := hprevBounded id hid
            have htyWf : ty.WF entry0.level := by
              have hle' : entry.level ≤ entry0.level := by
                rw [← hlevel]
                exact hle
              exact Ty.Scoped.mono hwf hle' (le_refl 0)
            exact Ty.substVar_wf hprevWf htyWf
          · rw [Ty.substVar_eq_self_of_not_mem hid]
            exact hprevWf
        · rw [hlevelEq, ← hprevEq]
          intro m hm
          rcases Ty.mem_vars_substVar_subset hm with hold | ⟨hidmem, hmty⟩
          · exact le_trans (MStore.levelOf_solve_le store id m ty) (hprevBounded m hold)
          · have hmne : m ≠ id := by
              intro sameId
              subst m
              have htrue : ty.vars.contains id = true :=
                (Ty.contains_iff_mem ty id).mpr hmty
              rw [hocc] at htrue
              exact nomatch htrue
            have hle : store.levelOf id ≤ entry0.level := hprevBounded id hidmem
            rw [MStore.levelOf_solve]
            simp only [hmne, if_false, hmty, if_true]
            exact le_trans (Nat.min_le_right _ _) hle

private theorem MStore.solve_normalized {store : MStore} {id : Nat} {ty : InfTy}
    (norm : store.Normalized) (guard : store.canBind id ty = true)
    (resolved : store.apply ty = ty) :
    (store.solve id ty).Normalized := by
  obtain ⟨entry, hentry, hsolNone, hocc, hwf⟩ := MStore.canBind_iff.mp guard
  intro j solution hlookup m hm
  by_cases same : j = id
  · subst j
    rw [MStore.lookup_solve_self store id ty hentry] at hlookup
    injection hlookup with hsol
    subst hsol
    have hmne : m ≠ id := by
      intro sameId
      subst m
      have htrue : ty.vars.contains id = true :=
        (Ty.contains_iff_mem ty id).mpr hm
      rw [hocc] at htrue
      exact nomatch htrue
    have hnone := MStore.lookup_none_of_resolved norm resolved hm
    rw [MStore.lookup_solve_of_ne store id m ty hmne, hnone]
    rfl
  · rw [MStore.lookup_solve_of_ne store id j ty same] at hlookup
    rw [Option.map_eq_some_iff] at hlookup
    obtain ⟨previous, hprevLookup, hprevEq⟩ := hlookup
    rw [← hprevEq] at hm
    rcases Ty.mem_vars_substVar' hm with ⟨hmne, hmprev⟩ | hmty
    · have hnone := norm j previous hprevLookup m hmprev
      rw [MStore.lookup_solve_of_ne store id m ty hmne, hnone]
      rfl
    · have hmne : m ≠ id := by
        intro sameId
        subst m
        have htrue : ty.vars.contains id = true :=
          (Ty.contains_iff_mem ty id).mpr hmty
        rw [hocc] at htrue
        exact nomatch htrue
      have hnone := MStore.lookup_none_of_resolved norm resolved hmty
      rw [MStore.lookup_solve_of_ne store id m ty hmne, hnone]
      rfl

private theorem MStore.solve_allocated {store : MStore} {id : Nat} {ty : InfTy}
    (allocated : store.Allocates) (tyAllocated : ty.Allocated store) :
    (store.solve id ty).Allocates := by
  intro j solution hlookup
  by_cases same : j = id
  · subst j
    unfold MStore.lookup at hlookup
    rw [MStore.solve_getElem?] at hlookup
    cases hj : store[id]? with
    | none => rw [hj] at hlookup; simp at hlookup
    | some entry =>
        rw [hj] at hlookup
        simp only [Option.map_some, Option.bind_some] at hlookup
        injection hlookup with hsol
        rw [← hsol]
        intro m hm
        have hbound := tyAllocated m hm
        simpa [MStore.solve_length] using hbound
  · unfold MStore.lookup at hlookup
    rw [MStore.solve_getElem?] at hlookup
    cases hj : store[j]? with
    | none => rw [hj] at hlookup; simp at hlookup
    | some entry =>
        rw [hj] at hlookup
        simp only [Option.map_some, if_neg same, Option.bind_some] at hlookup
        obtain ⟨previous, hprevSol, hprevEq⟩ := Option.map_eq_some_iff.mp hlookup
        rw [← hprevEq]
        intro m hm
        rcases Ty.mem_vars_substVar hm with old | new
        · have hprevLookup : store.lookup j = some previous := by
            unfold MStore.lookup
            rw [hj]
            simp [hprevSol]
          have hbound := allocated j previous hprevLookup m old
          simpa [MStore.solve_length] using hbound
        · have hbound := tyAllocated m new
          simpa [MStore.solve_length] using hbound

private theorem MStore.solve_safe {store : MStore} {id : Nat} {ty : InfTy}
    (safe : store.Safe) (guard : store.canBind id ty = true)
    (tyAllocated : ty.Allocated store) (resolved : store.apply ty = ty) :
    (store.solve id ty).Safe := by
  refine ⟨?_, ?_, ?_⟩
  · exact MStore.solve_leveled safe.leveled safe.normalized guard resolved
  · exact MStore.solve_allocated safe.allocated tyAllocated
  · exact MStore.solve_normalized safe.normalized guard resolved

/-! ## Phase structure -/

/-- The defining equation of one non-final phase step. -/
private theorem unifyPhase_cons_eq (store : MStore) (fuel : Nat)
    (left right : InfTy) (rest : List Constraint) :
    unifyPhase store (fuel + 1) ((left, right) :: rest) =
      if left = right then unifyPhase store fuel rest
      else
        match left, right with
        | .var id, ty | ty, .var id =>
            if store.canBind id ty then
              (UnifyPhase.bound (store.solve id ty)
                (rest.map (Constraint.substVar id ty)) : UnifyPhase)
            else .failed
        | .arrow leftDomain leftCodomain,
          .arrow rightDomain rightCodomain =>
            unifyPhase store fuel
              ((leftDomain, rightDomain) :: (leftCodomain, rightCodomain) :: rest)
        | .app leftFunction leftArgument,
          .app rightFunction rightArgument =>
            unifyPhase store fuel
              ((leftFunction, rightFunction) :: (leftArgument, rightArgument) :: rest)
        | _, _ => .failed := by
  rfl

/-- A successful binding lowers the number of unsolved entries. -/
private theorem bound_of_guard_if (store result : MStore) (id : Nat) (ty : InfTy)
    (rest rest' : List Constraint)
    (run : (if store.canBind id ty then
              (UnifyPhase.bound (store.solve id ty)
                (rest.map (Constraint.substVar id ty)) : UnifyPhase)
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

/-- The phase fuel `Constraints.size` is enough. -/
theorem unifyPhase_ne_outOfFuel {store : MStore} {constraints : List Constraint}
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

/-- Each binding phase solves one more metavariable, so `unsolved + 1` phases
are enough. -/
theorem unifyPhase_bound_unsolved_lt {store result : MStore}
    {constraints rest : List Constraint}
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

/-! ## Structural invariants: length -/

private theorem not_finished_of_bound_if {p : Prop} [Decidable p]
    {store : MStore} {id : Nat} {ty : InfTy} {rest : List Constraint}
    {result : MStore}
    (run : (if p then
              (UnifyPhase.bound (store.solve id ty)
                (rest.map (Constraint.substVar id ty)) : UnifyPhase)
            else .failed) = .finished result) : False := by
  by_cases h : p
  · rw [if_pos h] at run
    exact nomatch run
  · rw [if_neg h] at run
    exact nomatch run

private theorem bound_if_length {p : Prop} [Decidable p]
    {store result : MStore} {id : Nat} {ty : InfTy}
    {rest rest' : List Constraint}
    (run : (if p then
              (UnifyPhase.bound (store.solve id ty)
                (rest.map (Constraint.substVar id ty)) : UnifyPhase)
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

theorem MStore.unify_length {store result : MStore} {left right : InfTy}
    (run : store.unify left right = some result) : result.length = store.length := by
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
    {leftDomain leftCodomain rightDomain rightCodomain : InfTy}
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
    simpa using head.1
  have rightParts : store.apply rightDomain = rightDomain ∧
      store.apply rightCodomain = rightCodomain := by
    simpa using head.2
  rcases List.mem_cons.mp member with rfl | member
  · exact ⟨leftParts.1, rightParts.1⟩
  · rcases List.mem_cons.mp member with rfl | member
    · exact ⟨leftParts.2, rightParts.2⟩
    · exact resolved constraint (by simp [member])

private theorem ConstraintsResolved.apps {store : MStore}
    {leftFunction leftArgument rightFunction rightArgument : InfTy}
    {rest : List Constraint}
    (resolved : ConstraintsResolved store
      ((Ty.app leftFunction leftArgument,
        Ty.app rightFunction rightArgument) :: rest)) :
    ConstraintsResolved store
      ((leftFunction, rightFunction) :: (leftArgument, rightArgument) :: rest) := by
  intro constraint member
  have head := resolved
    (Ty.app leftFunction leftArgument, Ty.app rightFunction rightArgument)
    (by simp)
  have leftParts : store.apply leftFunction = leftFunction ∧
      store.apply leftArgument = leftArgument := by
    simpa using head.1
  have rightParts : store.apply rightFunction = rightFunction ∧
      store.apply rightArgument = rightArgument := by
    simpa using head.2
  rcases List.mem_cons.mp member with rfl | member
  · exact ⟨leftParts.1, rightParts.1⟩
  · rcases List.mem_cons.mp member with rfl | member
    · exact ⟨leftParts.2, rightParts.2⟩
    · exact resolved constraint (by simp [member])

private theorem MStore.apply_eq_self_of_vars_unsolved (store : MStore) (ty : InfTy)
    (unsolved : ∀ id ∈ ty.vars, store.lookup id = none) :
    store.apply ty = ty := by
  induction ty with
  | prim => rfl
  | bvar => rfl
  | rigid => rfl
  | arrow domain codomain domainIH codomainIH =>
      have domainUnsolved : ∀ id ∈ domain.vars, store.lookup id = none := by
        intro id inside
        apply unsolved id
        simp only [Ty.vars, List.mem_append]
        exact Or.inl inside
      have codomainUnsolved : ∀ id ∈ codomain.vars, store.lookup id = none := by
        intro id inside
        apply unsolved id
        simp only [Ty.vars, List.mem_append]
        exact Or.inr inside
      simp only [MStore.apply_arrow]
      rw [domainIH domainUnsolved, codomainIH codomainUnsolved]
  | con => rfl
  | app function argument functionIH argumentIH =>
      have functionUnsolved : ∀ id ∈ function.vars, store.lookup id = none := by
        intro id inside
        apply unsolved id
        simp only [Ty.vars, List.mem_append]
        exact Or.inl inside
      have argumentUnsolved : ∀ id ∈ argument.vars, store.lookup id = none := by
        intro id inside
        apply unsolved id
        simp only [Ty.vars, List.mem_append]
        exact Or.inr inside
      simp only [MStore.apply_app]
      rw [functionIH functionUnsolved, argumentIH argumentUnsolved]
  | var id =>
      have noneLookup := unsolved id (by simp [Ty.vars])
      simp only [MStore.apply_var, noneLookup, Option.getD_none]

private theorem MStore.apply_idem {store : MStore} (norm : store.Normalized)
    (ty : InfTy) : store.apply (store.apply ty) = store.apply ty := by
  induction ty with
  | prim => rfl
  | bvar => rfl
  | rigid => rfl
  | arrow domain codomain domainIH codomainIH =>
      simp only [MStore.apply_arrow]
      rw [domainIH, codomainIH]
  | con => rfl
  | app function argument functionIH argumentIH =>
      simp only [MStore.apply_app]
      rw [functionIH, argumentIH]
  | var id =>
      simp only [MStore.apply_var]
      cases lookupEq : store.lookup id with
      | none => simp [lookupEq]
      | some replacement =>
          change store.apply replacement = replacement
          apply MStore.apply_eq_self_of_vars_unsolved
          intro key member
          exact norm id replacement lookupEq key member

private theorem MStore.apply_subst_resolved {store : MStore} {id : Nat} {ty : InfTy}
    (norm : store.Normalized) (occurs : ty.vars.contains id = false)
    (tyResolved : store.apply ty = ty) {source : InfTy}
    (sourceResolved : store.apply source = source) :
    (store.solve id ty).apply (source.substVar id ty) =
      source.substVar id ty := by
  apply MStore.apply_eq_self_of_vars_unsolved
  intro key member
  rcases Ty.mem_vars_substVar' member with ⟨different, oldMember⟩ | newMember
  · have hnone := MStore.lookup_none_of_resolved norm sourceResolved oldMember
    rw [MStore.lookup_solve_of_ne store id key ty different, hnone]
    rfl
  · have keyLookup := MStore.lookup_none_of_resolved norm tyResolved newMember
    have different : key ≠ id := by
      intro same
      subst same
      have occursTrue := (Ty.contains_iff_mem ty key).mpr newMember
      rw [occurs] at occursTrue
      exact nomatch occursTrue
    rw [MStore.lookup_solve_of_ne store id key ty different, keyLookup]
    rfl

private theorem bound_guard_data {store result : MStore} {id : Nat} {ty : InfTy}
    {rest rest' : List Constraint}
    (run : (if store.canBind id ty then
              (UnifyPhase.bound (store.solve id ty)
                (rest.map (Constraint.substVar id ty)) : UnifyPhase)
            else .failed) = .bound result rest') :
    store.canBind id ty = true ∧ store.solve id ty = result ∧
      rest.map (Constraint.substVar id ty) = rest' := by
  by_cases h : store.canBind id ty
  · rw [if_pos h] at run
    injection run with resultEq restEq
    exact ⟨h, resultEq, restEq⟩
  · rw [if_neg h] at run
    exact nomatch run

/-! ## Allocation of constraints -/

private abbrev ConstraintsAllocated (store : MStore)
    (constraints : List Constraint) : Prop :=
  ∀ constraint ∈ constraints,
    constraint.1.Allocated store ∧ constraint.2.Allocated store

private theorem ConstraintsAllocated.arrows {store : MStore}
    {leftDomain leftCodomain rightDomain rightCodomain : InfTy}
    {rest : List Constraint}
    (head : (Ty.arrow leftDomain leftCodomain).Allocated store ∧
      (Ty.arrow rightDomain rightCodomain).Allocated store)
    (restAllocated : ConstraintsAllocated store rest) :
    ConstraintsAllocated store
      ((leftDomain, rightDomain) :: (leftCodomain, rightCodomain) :: rest) := by
  intro constraint member
  rcases List.mem_cons.mp member with rfl | member
  · exact ⟨head.1.left, head.2.left⟩
  · rcases List.mem_cons.mp member with rfl | member
    · exact ⟨head.1.right, head.2.right⟩
    · exact restAllocated constraint member

private theorem ConstraintsAllocated.apps {store : MStore}
    {leftFunction leftArgument rightFunction rightArgument : InfTy}
    {rest : List Constraint}
    (head : (Ty.app leftFunction leftArgument).Allocated store ∧
      (Ty.app rightFunction rightArgument).Allocated store)
    (restAllocated : ConstraintsAllocated store rest) :
    ConstraintsAllocated store
      ((leftFunction, rightFunction) :: (leftArgument, rightArgument) :: rest) := by
  intro constraint member
  rcases List.mem_cons.mp member with rfl | member
  · exact ⟨head.1.appLeft, head.2.appLeft⟩
  · rcases List.mem_cons.mp member with rfl | member
    · exact ⟨head.1.appRight, head.2.appRight⟩
    · exact restAllocated constraint member

private theorem Ty.substVar_allocated {store : MStore} {previous replacement : InfTy}
    {target : Nat} (previousAllocated : previous.Allocated store)
    (replacementAllocated : replacement.Allocated store) :
    (previous.substVar target replacement).Allocated store := by
  intro id member
  rcases Ty.mem_vars_substVar member with old | new
  · exact previousAllocated id old
  · exact replacementAllocated id new

/-! ## Safety -/

private theorem bound_branch_safe {store result : MStore} {id : Nat} {ty : InfTy}
    {rest rest' : List Constraint}
    (safe : store.Safe) (allocated : ConstraintsAllocated store rest)
    (resolved : ConstraintsResolved store rest)
    (tyResolved : store.apply ty = ty) (tyAllocated : ty.Allocated store)
    (run : (if store.canBind id ty then
              (UnifyPhase.bound (store.solve id ty)
                (rest.map (Constraint.substVar id ty)) : UnifyPhase)
            else .failed) = .bound result rest') :
    result.Safe ∧ ConstraintsResolved result rest' ∧
      ConstraintsAllocated result rest' := by
  obtain ⟨guard, resultEq, restEq⟩ := bound_guard_data run
  obtain ⟨entry, hentry, hsolNone, hocc, hwf⟩ := MStore.canBind_iff.mp guard
  subst resultEq
  subst restEq
  refine ⟨MStore.solve_safe safe guard tyAllocated tyResolved, ?_, ?_⟩
  · intro current inRest
    rcases List.mem_map.mp inRest with ⟨old, inOld, rfl⟩
    exact ⟨MStore.apply_subst_resolved safe.normalized hocc tyResolved
             (resolved old inOld).1,
           MStore.apply_subst_resolved safe.normalized hocc tyResolved
             (resolved old inOld).2⟩
  · intro current inRest
    rcases List.mem_map.mp inRest with ⟨old, inOld, rfl⟩
    have oldAllocated := allocated old inOld
    have newAllocated : (old.1.substVar id ty).Allocated store :=
      Ty.substVar_allocated (target := id) (previous := old.1) (replacement := ty)
        oldAllocated.1 tyAllocated
    have newAllocated' : (old.2.substVar id ty).Allocated store :=
      Ty.substVar_allocated (target := id) (previous := old.2) (replacement := ty)
        oldAllocated.2 tyAllocated
    refine ⟨?_, ?_⟩
    · intro m hm
      have hbound := newAllocated m hm
      simpa [MStore.solve_length] using hbound
    · intro m hm
      have hbound := newAllocated' m hm
      simpa [MStore.solve_length] using hbound

private theorem unifyPhase_finished_safe
    {store result : MStore} {fuel : Nat} {constraints : List Constraint}
    (safe : store.Safe)
    (run : unifyPhase store fuel constraints = .finished result) :
    result.Safe := by
  rw [unifyPhase_finished_eq run]
  exact safe

private theorem unifyPhase_bound_safe
    {store result : MStore} {fuel : Nat}
    {constraints rest : List Constraint}
    (safe : store.Safe)
    (allocated : ConstraintsAllocated store constraints)
    (resolved : ConstraintsResolved store constraints)
    (run : unifyPhase store fuel constraints = .bound result rest) :
    result.Safe ∧ ConstraintsResolved result rest ∧
      ConstraintsAllocated result rest := by
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
          have headAllocated := allocated (left, right) (by simp)
          have restAllocated : ConstraintsAllocated store rest := by
            intro current inRest
            exact allocated current (by simp [inRest])
          rw [unifyPhase_cons_eq] at run
          by_cases equal : left = right
          · rw [if_pos equal] at run
            exact ih restAllocated restResolved run
          · rw [if_neg equal] at run
            cases left <;> cases right <;> simp only [] at run
            all_goals first
              | (exact ih (ConstraintsAllocated.arrows headAllocated restAllocated)
                  (ConstraintsResolved.arrows resolved) run)
              | (exact ih (ConstraintsAllocated.apps headAllocated restAllocated)
                  (ConstraintsResolved.apps resolved) run)
              | (exact bound_branch_safe safe restAllocated restResolved
                  (by first | exact headResolved.1 | exact headResolved.2)
                  (by first | exact headAllocated.1 | exact headAllocated.2)
                  run)
              | (cases run)

private theorem unifyLoop_safe
    {fuel : Nat} {store : MStore} {constraints : List Constraint}
    {result : MStore}
    (safe : store.Safe)
    (allocated : ConstraintsAllocated store constraints)
    (resolved : ConstraintsResolved store constraints)
    (run : unifyLoop fuel store constraints = some result) :
    result.Safe := by
  induction fuel generalizing store constraints with
  | zero => simp [unifyLoop] at run
  | succ fuel ih =>
      rw [unifyLoop_succ] at run
      split at run
      · rename_i finishedRun
        injection run with resultEq
        subst resultEq
        exact unifyPhase_finished_safe safe finishedRun
      · rename_i boundRun
        obtain ⟨resultSafe, restResolved, restAllocated⟩ :=
          unifyPhase_bound_safe safe allocated resolved boundRun
        exact ih resultSafe restAllocated restResolved run
      · exact nomatch run
      · exact nomatch run

theorem MStore.unify_safe {store result : MStore} {left right : InfTy} (safe : store.Safe)
    (leftAllocated : left.Allocated store) (rightAllocated : right.Allocated store)
    (run : store.unify left right = some result) : result.Safe := by
  change unifyLoop (store.unsolved + 1) store
    [(store.apply left, store.apply right)] = some result at run
  refine unifyLoop_safe safe ?_ ?_ run
  · intro constraint member
    simp only [List.mem_singleton] at member
    subst member
    exact ⟨MStore.apply_allocated safe leftAllocated,
      MStore.apply_allocated safe rightAllocated⟩
  · intro constraint member
    simp only [List.mem_singleton] at member
    subst member
    exact ⟨MStore.apply_idem safe.normalized left,
      MStore.apply_idem safe.normalized right⟩

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
              | (obtain ⟨_, solutionEq, _⟩ := bound_guard_data run
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

/-- Levels only decrease. -/
theorem MStore.unify_levelOf_le {store result : MStore} {left right : InfTy}
    (run : store.unify left right = some result) (id : Nat) :
    result.levelOf id ≤ store.levelOf id := by
  change unifyLoop (store.unsolved + 1) store
    [(store.apply left, store.apply right)] = some result at run
  exact unifyLoop_levelOf_le run id

/-! ## Semantics -/

private theorem Ty.realize_wf_subterm {ty : InfTy} {valuation : Valuation} {level : Nat}
    (wf : (ty.realize valuation).WF level) {id : Nat} (member : id ∈ ty.vars) :
    (valuation id).WF level :=
  (Ty.scoped_of_bind (f := valuation) wf).2 id member

private theorem Ty.realize_substVar {valuation : Valuation}
    {ty replacement : InfTy} {target : Nat}
    (agrees : valuation target = replacement.realize valuation) :
    (ty.substVar target replacement).realize valuation =
      ty.realize valuation := by
  change (ty.bind (fun v => if v = target then replacement else .var v)).bind valuation =
    ty.bind valuation
  rw [Ty.bind_bind]
  refine Ty.bind_congr (ty := ty)
    (f := fun v => (if v = target then replacement else .var v).bind valuation)
    (g := valuation) ?_
  intro v _
  by_cases selected : v = target
  · subst selected
    simpa using agrees.symm
  · simp [selected]

private abbrev ConstraintsRealized (valuation : Valuation)
    (constraints : List Constraint) : Prop :=
  ∀ constraint ∈ constraints,
    constraint.1.realize valuation = constraint.2.realize valuation

private theorem ConstraintsRealized.cons_of_equal {valuation : Valuation}
    {left right : InfTy} {rest : List Constraint}
    (equal : left = right)
    (restRealized : ConstraintsRealized valuation rest) :
    ConstraintsRealized valuation ((left, right) :: rest) := by
  intro constraint member
  rcases List.mem_cons.mp member with rfl | member
  · simp [equal]
  · exact restRealized constraint member

private theorem ConstraintsRealized.arrows {valuation : Valuation}
    {leftDomain leftCodomain rightDomain rightCodomain : InfTy}
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
    simp only [Ty.realize_arrow, domainRealized, codomainRealized]
  · exact realized constraint (by simp [member])

private theorem ConstraintsRealized.apps {valuation : Valuation}
    {leftFunction leftArgument rightFunction rightArgument : InfTy}
    {rest : List Constraint}
    (realized : ConstraintsRealized valuation
      ((leftFunction, rightFunction) :: (leftArgument, rightArgument) :: rest)) :
    ConstraintsRealized valuation
      ((Ty.app leftFunction leftArgument,
        Ty.app rightFunction rightArgument) :: rest) := by
  intro constraint member
  rcases List.mem_cons.mp member with rfl | member
  · have functionRealized := realized (leftFunction, rightFunction) (by simp)
    have argumentRealized := realized (leftArgument, rightArgument) (by simp)
    simp only [Ty.realize_app, functionRealized, argumentRealized]
  · exact realized constraint (by simp [member])

private theorem ConstraintsRealized.tail {valuation : Valuation}
    {constraint : Constraint} {rest : List Constraint}
    (realized : ConstraintsRealized valuation (constraint :: rest)) :
    ConstraintsRealized valuation rest := by
  intro current member
  exact realized current (by simp [member])

private theorem MStore.models_solve {store : MStore} {id : Nat} {ty : InfTy}
    {valuation : Valuation}
    (models : store.Models valuation)
    (guard : store.canBind id ty = true)
    (agrees : valuation id = ty.realize valuation) :
    (store.solve id ty).Models valuation := by
  obtain ⟨entry, hentry, hsolNone, hocc, hwf⟩ := MStore.canBind_iff.mp guard
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
      simp only [Option.map_some] at hentry'
      injection hentry' with hEq
      have levelEq : entry'.level = entry.level := by
        rw [← hEq]
        simp
      rw [levelEq]
      exact models.wf id entry hentry
    · rw [MStore.solve_getElem?] at hentry'
      cases hj : store[j]? with
      | none => rw [hj] at hentry'; simp at hentry'
      | some old =>
          rw [hj] at hentry'
          simp only [Option.map_some, if_neg same] at hentry'
          injection hentry' with hEq
          have levelEq : entry'.level =
              (if j ∈ ty.vars then min old.level (store.levelOf id) else old.level) := by
            rw [← hEq]
          rw [levelEq]
          by_cases mem : j ∈ ty.vars
          · simp only [mem, if_true]
            have wfId : (valuation id).WF (store.levelOf id) := by
              have := models.wf id entry hentry
              rwa [← hlevel] at this
            have wfRealize : (ty.realize valuation).WF (store.levelOf id) := by
              rwa [← agrees]
            have wfVal := Ty.realize_wf_subterm wfRealize mem
            by_cases hle : store.levelOf id ≤ old.level
            · rw [Nat.min_eq_right hle]
              exact wfVal
            · rw [Nat.min_eq_left (by omega)]
              exact models.wf j old hj
          · simp [mem]
            exact models.wf j old hj
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
      rw [Ty.realize_substVar agrees]
      exact models.equation j previous hprev

private theorem MStore.models_of_solve {store : MStore} {id : Nat} {ty : InfTy}
    {valuation : Valuation}
    (models : (store.solve id ty).Models valuation)
    (guard : store.canBind id ty = true)
    (agrees : valuation id = ty.realize valuation) :
    store.Models valuation := by
  obtain ⟨entry, hentry, hsolNone, hocc, hwf⟩ := MStore.canBind_iff.mp guard
  refine ⟨?_, ?_⟩
  · intro j old hj
    by_cases same : j = id
    · subst j
      have entryEq : (store.solve id ty)[id]? = some { entry with solution := some ty } := by
        rw [MStore.solve_getElem?]
        rw [hentry]
        simp
      have wfNew := models.wf id { entry with solution := some ty } entryEq
      have entryOld : entry = old := by
        rw [hentry] at hj
        exact Option.some.inj hj
      rw [entryOld] at wfNew
      exact wfNew
    · have entryEq : (store.solve id ty)[j]? =
          some { level := if j ∈ ty.vars then min old.level (store.levelOf id) else old.level,
                 solution := old.solution.map (·.substVar id ty) } := by
        rw [MStore.solve_getElem?, hj]
        simp [same]
      have wfNew := models.wf j _ entryEq
      have levelLe : (if j ∈ ty.vars then min old.level (store.levelOf id)
          else old.level) ≤ old.level := by
        by_cases mem : j ∈ ty.vars
        · simp only [mem, if_true]
          exact Nat.min_le_left _ _
        · simp [mem]
      exact Ty.Scoped.mono wfNew levelLe (le_refl 0)
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
          some (previous.substVar id ty) := by
        rw [MStore.lookup_solve_of_ne store id j ty same, hprev]
        rfl
      have solved := models.equation j (previous.substVar id ty) solveLookup
      rw [Ty.realize_substVar agrees] at solved
      exact solved

private theorem bound_branch_sound_left
    {store result : MStore} {id : Nat} {ty : InfTy}
    {rest rest' : List Constraint}
    {valuation : Valuation}
    (run : (if store.canBind id ty then
              (UnifyPhase.bound (store.solve id ty)
                (rest.map (Constraint.substVar id ty)) : UnifyPhase)
            else .failed) = .bound result rest')
    (models : result.Models valuation)
    (restRealized : ConstraintsRealized valuation rest') :
    store.Models valuation ∧
      ConstraintsRealized valuation ((Ty.var id, ty) :: rest) := by
  obtain ⟨guard, resultEq, restEq⟩ := bound_guard_data run
  obtain ⟨entry, hentry, hsolNone, hocc, hwf⟩ := MStore.canBind_iff.mp guard
  subst resultEq
  subst restEq
  have agrees : valuation id = ty.realize valuation :=
    models.equation id ty (MStore.lookup_solve_self store id ty hentry)
  refine ⟨MStore.models_of_solve models guard agrees, ?_⟩
  intro constraint member
  rcases List.mem_cons.mp member with rfl | member
  · simpa using agrees
  · have substituted := restRealized (Constraint.substVar id ty constraint)
      (List.mem_map_of_mem member)
    simp only [Constraint.substVar] at substituted
    rw [Ty.realize_substVar agrees, Ty.realize_substVar agrees] at substituted
    exact substituted

private theorem bound_branch_sound_right
    {store result : MStore} {id : Nat} {ty : InfTy}
    {rest rest' : List Constraint}
    {valuation : Valuation}
    (run : (if store.canBind id ty then
              (UnifyPhase.bound (store.solve id ty)
                (rest.map (Constraint.substVar id ty)) : UnifyPhase)
            else .failed) = .bound result rest')
    (models : result.Models valuation)
    (restRealized : ConstraintsRealized valuation rest') :
    store.Models valuation ∧
      ConstraintsRealized valuation ((ty, Ty.var id) :: rest) := by
  obtain ⟨guard, resultEq, restEq⟩ := bound_guard_data run
  obtain ⟨entry, hentry, hsolNone, hocc, hwf⟩ := MStore.canBind_iff.mp guard
  subst resultEq
  subst restEq
  have agrees : valuation id = ty.realize valuation :=
    models.equation id ty (MStore.lookup_solve_self store id ty hentry)
  refine ⟨MStore.models_of_solve models guard agrees, ?_⟩
  intro constraint member
  rcases List.mem_cons.mp member with rfl | member
  · simpa using agrees.symm
  · have substituted := restRealized (Constraint.substVar id ty constraint)
      (List.mem_map_of_mem member)
    simp only [Constraint.substVar] at substituted
    rw [Ty.realize_substVar agrees, Ty.realize_substVar agrees] at substituted
    exact substituted

private theorem unifyPhase_sound_finished
    {store result : MStore} {fuel : Nat} {constraints : List Constraint}
    {valuation : Valuation}
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
              | (obtain ⟨storeModels, realized⟩ := ih run
                 exact ⟨storeModels, ConstraintsRealized.apps realized⟩)
              | (exact (not_finished_of_bound_if run).elim)
              | (cases run)

private theorem unifyPhase_sound_bound
    {store result : MStore} {fuel : Nat}
    {constraints rest : List Constraint}
    {valuation : Valuation}
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
              | (obtain ⟨storeModels, realized⟩ := ih run
                 exact ⟨storeModels, ConstraintsRealized.apps realized⟩)
              | (exact bound_branch_sound_left run models restRealized)
              | (exact bound_branch_sound_right run models restRealized)
              | (cases run)

private theorem unifyLoop_sound
    {fuel : Nat} {store : MStore} {constraints : List Constraint}
    {result : MStore} {valuation : Valuation}
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

/-- Every model of the result is a model of the input that unifies the two
types. -/
theorem MStore.unify_sound {store result : MStore} {left right : InfTy} {valuation : Valuation}
    (run : store.unify left right = some result) (models : result.Models valuation) :
    store.Models valuation ∧ left.realize valuation = right.realize valuation := by
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

private theorem Ty.size_realize_ge_of_mem {ty : InfTy} {id : Nat}
    {valuation : Valuation} (member : id ∈ ty.vars) :
    (valuation id).size ≤ (ty.realize valuation).size := by
  induction ty with
  | prim => simp [Ty.vars] at member
  | bvar => simp [Ty.vars] at member
  | rigid => simp [Ty.vars] at member
  | var other =>
      have same : id = other := by simpa [Ty.vars] using member
      subst same
      simp [Ty.realize_var]
  | arrow domain codomain domainIH codomainIH =>
      have split : id ∈ domain.vars ∨ id ∈ codomain.vars := by
        simpa [Ty.vars] using member
      rcases split with inside | inside
      · have bounded := domainIH inside
        simp only [Ty.realize_arrow, Ty.size]
        omega
      · have bounded := codomainIH inside
        simp only [Ty.realize_arrow, Ty.size]
        omega
  | con => simp [Ty.vars] at member
  | app function argument functionIH argumentIH =>
      have split : id ∈ function.vars ∨ id ∈ argument.vars := by
        simpa [Ty.vars] using member
      rcases split with inside | inside
      · have bounded := functionIH inside
        simp only [Ty.realize_app, Ty.size]
        omega
      · have bounded := argumentIH inside
        simp only [Ty.realize_app, Ty.size]
        omega

private theorem Ty.size_realize_gt_of_mem_of_ne {ty : InfTy} {id : Nat}
    {valuation : Valuation} (member : id ∈ ty.vars)
    (different : ty ≠ .var id) :
    (valuation id).size < (ty.realize valuation).size := by
  induction ty with
  | prim => simp [Ty.vars] at member
  | bvar => simp [Ty.vars] at member
  | rigid => simp [Ty.vars] at member
  | var other =>
      have same : id = other := by simpa [Ty.vars] using member
      subst same
      exact absurd rfl different
  | arrow domain codomain domainIH codomainIH =>
      have split : id ∈ domain.vars ∨ id ∈ codomain.vars := by
        simpa [Ty.vars] using member
      have positivity : 0 < (codomain.realize valuation).size := Ty.size_pos _
      simp only [Ty.realize_arrow, Ty.size]
      rcases split with inside | inside
      · have bounded := Ty.size_realize_ge_of_mem (valuation := valuation) inside
        omega
      · have bounded := Ty.size_realize_ge_of_mem (valuation := valuation) inside
        omega
  | con => simp [Ty.vars] at member
  | app function argument functionIH argumentIH =>
      have split : id ∈ function.vars ∨ id ∈ argument.vars := by
        simpa [Ty.vars] using member
      have positivity : 0 < (argument.realize valuation).size := Ty.size_pos _
      simp only [Ty.realize_app, Ty.size]
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

private theorem unifyPhase_cons_eq_var_left (store : MStore) (fuel : Nat)
    (id : Nat) (ty : InfTy) (rest : List Constraint)
    (different : (Ty.var id) ≠ ty) :
    unifyPhase store (fuel + 1) ((Ty.var id, ty) :: rest) =
      (if store.canBind id ty then
        (UnifyPhase.bound (store.solve id ty)
          (rest.map (Constraint.substVar id ty)) : UnifyPhase)
      else .failed) := by
  rw [unifyPhase_cons_eq, if_neg different]

private theorem unifyPhase_cons_eq_var_right (store : MStore) (fuel : Nat)
    (left : InfTy) (id : Nat) (rest : List Constraint)
    (different : left ≠ .var id)
    (notVar : ∀ j, left ≠ .var j) :
    unifyPhase store (fuel + 1) ((left, Ty.var id) :: rest) =
      (if store.canBind id left then
        (UnifyPhase.bound (store.solve id left)
          (rest.map (Constraint.substVar id left)) : UnifyPhase)
      else .failed) := by
  rw [unifyPhase_cons_eq, if_neg different]
  cases left with
  | var j => exact absurd rfl (notVar j)
  | prim => rfl
  | bvar => rfl
  | rigid => rfl
  | arrow => rfl
  | con => rfl
  | app => rfl

private theorem unifyPhase_cons_eq_arrow (store : MStore) (fuel : Nat)
    (leftDomain leftCodomain rightDomain rightCodomain : InfTy)
    (rest : List Constraint)
    (different : (Ty.arrow leftDomain leftCodomain) ≠
      (Ty.arrow rightDomain rightCodomain)) :
    unifyPhase store (fuel + 1)
        ((Ty.arrow leftDomain leftCodomain,
          Ty.arrow rightDomain rightCodomain) :: rest) =
      unifyPhase store fuel
        ((leftDomain, rightDomain) :: (leftCodomain, rightCodomain) :: rest) := by
  rw [unifyPhase_cons_eq, if_neg different]

private theorem unifyPhase_cons_eq_app (store : MStore) (fuel : Nat)
    (leftFunction leftArgument rightFunction rightArgument : InfTy)
    (rest : List Constraint)
    (different : (Ty.app leftFunction leftArgument) ≠
      (Ty.app rightFunction rightArgument)) :
    unifyPhase store (fuel + 1)
        ((Ty.app leftFunction leftArgument,
          Ty.app rightFunction rightArgument) :: rest) =
      unifyPhase store fuel
        ((leftFunction, rightFunction) :: (leftArgument, rightArgument) :: rest) := by
  rw [unifyPhase_cons_eq, if_neg different]

private theorem var_guard_left {store : MStore} {id : Nat} {ty : InfTy}
    {valuation : Valuation}
    (different : (Ty.var id) ≠ ty)
    (resolvedId : store.apply (.var id) = .var id)
    (boundedId : id < store.length)
    (headSolves : valuation id = ty.realize valuation)
    (normalized : store.Normalized)
    (models : store.Models valuation) :
    store.canBind id ty = true := by
  have allocatedLookup : store.lookup id = none :=
    MStore.lookup_none_of_apply_var_eq normalized resolvedId
  obtain ⟨entry, hentry, hsolNone⟩ :=
    MStore.entry_of_lookup_none boundedId allocatedLookup
  have occurs : ty.vars.contains id = false := by
    cases occurrence : ty.vars.contains id with
    | false => rfl
    | true =>
        exfalso
        have member : id ∈ ty.vars :=
          (Ty.contains_iff_mem ty id).mp occurrence
        have strict := Ty.size_realize_gt_of_mem_of_ne
          (valuation := valuation) member (Ne.symm different)
        rw [← headSolves] at strict
        exact absurd strict (lt_irrefl _)
  have wf := models.wf id entry hentry
  rw [headSolves] at wf
  have scopedTy : ty.WF entry.level := Ty.scoped_of_realize_scoped wf
  exact MStore.canBind_iff.mpr ⟨entry, hentry, hsolNone, occurs, scopedTy⟩

private theorem var_guard_right {store : MStore} {id : Nat} {ty : InfTy}
    {valuation : Valuation}
    (different : ty ≠ (Ty.var id))
    (resolvedId : store.apply (.var id) = .var id)
    (boundedId : id < store.length)
    (headSolves : ty.realize valuation = valuation id)
    (normalized : store.Normalized)
    (models : store.Models valuation) :
    store.canBind id ty = true := by
  have allocatedLookup : store.lookup id = none :=
    MStore.lookup_none_of_apply_var_eq normalized resolvedId
  obtain ⟨entry, hentry, hsolNone⟩ :=
    MStore.entry_of_lookup_none boundedId allocatedLookup
  have occurs : ty.vars.contains id = false := by
    cases occurrence : ty.vars.contains id with
    | false => rfl
    | true =>
        exfalso
        have member : id ∈ ty.vars :=
          (Ty.contains_iff_mem ty id).mp occurrence
        have strict := Ty.size_realize_gt_of_mem_of_ne
          (valuation := valuation) member different
        rw [headSolves] at strict
        exact absurd strict (lt_irrefl _)
  have wf := models.wf id entry hentry
  have wfTy : (ty.realize valuation).WF entry.level := by
    rw [headSolves]
    exact wf
  have scopedTy : ty.WF entry.level := Ty.scoped_of_realize_scoped wfTy
  exact MStore.canBind_iff.mpr ⟨entry, hentry, hsolNone, occurs, scopedTy⟩

private theorem phase_bound_left_complete {store : MStore} {fuel : Nat}
    {id : Nat} {ty : InfTy} {rest : List Constraint}
    {valuation : Valuation}
    (different : (Ty.var id) ≠ ty)
    (resolvedId : store.apply (.var id) = .var id)
    (resolvedTy : store.apply ty = ty)
    (boundedId : id < store.length)
    (tyAllocated : ty.Allocated store)
    (headSolves : valuation id = ty.realize valuation)
    (safe : store.Safe)
    (models : store.Models valuation)
    (restResolved : ConstraintsResolved store rest)
    (restAllocated : ConstraintsAllocated store rest)
    (restSolves : ConstraintsRealized valuation rest) :
    ∃ result rest', unifyPhase store (fuel + 1) ((Ty.var id, ty) :: rest) =
        .bound result rest' ∧
      result.Models valuation ∧ result.Safe ∧
      ConstraintsResolved result rest' ∧ ConstraintsAllocated result rest' ∧
      ConstraintsRealized valuation rest' ∧
      result.unsolved < store.unsolved := by
  have guard : store.canBind id ty = true :=
    var_guard_left different resolvedId boundedId headSolves safe.normalized models
  obtain ⟨entry, hentry, hsolNone, hocc, hwf⟩ := MStore.canBind_iff.mp guard
  refine ⟨store.solve id ty, rest.map (Constraint.substVar id ty), ?_, ?_, ?_,
    ?_, ?_, ?_, ?_⟩
  · rw [unifyPhase_cons_eq_var_left store fuel id ty rest different]
    simp [guard]
  · exact MStore.models_solve models guard headSolves
  · exact MStore.solve_safe safe guard tyAllocated resolvedTy
  · intro constraint member
    rcases List.mem_map.mp member with ⟨old, inOld, rfl⟩
    exact ⟨MStore.apply_subst_resolved safe.normalized hocc resolvedTy
             (restResolved old inOld).1,
           MStore.apply_subst_resolved safe.normalized hocc resolvedTy
             (restResolved old inOld).2⟩
  · intro constraint member
    rcases List.mem_map.mp member with ⟨old, inOld, rfl⟩
    have oldAllocated := restAllocated old inOld
    have newFirst : (old.1.substVar id ty).Allocated store :=
      Ty.substVar_allocated (target := id) (previous := old.1) (replacement := ty)
        oldAllocated.1 tyAllocated
    have newSecond : (old.2.substVar id ty).Allocated store :=
      Ty.substVar_allocated (target := id) (previous := old.2) (replacement := ty)
        oldAllocated.2 tyAllocated
    refine ⟨?_, ?_⟩
    · intro m hm
      have hbound := newFirst m hm
      simpa [MStore.solve_length] using hbound
    · intro m hm
      have hbound := newSecond m hm
      simpa [MStore.solve_length] using hbound
  · intro constraint member
    rcases List.mem_map.mp member with ⟨old, inOld, rfl⟩
    have oldSolves := restSolves old inOld
    simpa only [Constraint.substVar, Ty.realize_substVar headSolves] using oldSolves
  · exact MStore.unsolved_solve_lt store id ty hentry hsolNone

private theorem phase_bound_right_complete {store : MStore} {fuel : Nat}
    {id : Nat} {ty : InfTy} {rest : List Constraint}
    {valuation : Valuation}
    (different : ty ≠ (Ty.var id))
    (resolvedTy : store.apply ty = ty)
    (resolvedId : store.apply (.var id) = .var id)
    (boundedId : id < store.length)
    (tyAllocated : ty.Allocated store)
    (headSolves : ty.realize valuation = valuation id)
    (phaseBase : unifyPhase store (fuel + 1) ((ty, Ty.var id) :: rest) =
      (if store.canBind id ty then
        (UnifyPhase.bound (store.solve id ty)
          (rest.map (Constraint.substVar id ty)) : UnifyPhase)
      else .failed))
    (safe : store.Safe)
    (models : store.Models valuation)
    (restResolved : ConstraintsResolved store rest)
    (restAllocated : ConstraintsAllocated store rest)
    (restSolves : ConstraintsRealized valuation rest) :
    ∃ result rest', unifyPhase store (fuel + 1) ((ty, Ty.var id) :: rest) =
        .bound result rest' ∧
      result.Models valuation ∧ result.Safe ∧
      ConstraintsResolved result rest' ∧ ConstraintsAllocated result rest' ∧
      ConstraintsRealized valuation rest' ∧
      result.unsolved < store.unsolved := by
  have guard : store.canBind id ty = true :=
    var_guard_right different resolvedId boundedId headSolves safe.normalized models
  obtain ⟨entry, hentry, hsolNone, hocc, hwf⟩ := MStore.canBind_iff.mp guard
  have agrees : valuation id = ty.realize valuation := headSolves.symm
  refine ⟨store.solve id ty, rest.map (Constraint.substVar id ty), ?_, ?_, ?_,
    ?_, ?_, ?_, ?_⟩
  · rw [phaseBase, if_pos guard]
  · exact MStore.models_solve models guard agrees
  · exact MStore.solve_safe safe guard tyAllocated resolvedTy
  · intro constraint member
    rcases List.mem_map.mp member with ⟨old, inOld, rfl⟩
    exact ⟨MStore.apply_subst_resolved safe.normalized hocc resolvedTy
             (restResolved old inOld).1,
           MStore.apply_subst_resolved safe.normalized hocc resolvedTy
             (restResolved old inOld).2⟩
  · intro constraint member
    rcases List.mem_map.mp member with ⟨old, inOld, rfl⟩
    have oldAllocated := restAllocated old inOld
    have newFirst : (old.1.substVar id ty).Allocated store :=
      Ty.substVar_allocated (target := id) (previous := old.1) (replacement := ty)
        oldAllocated.1 tyAllocated
    have newSecond : (old.2.substVar id ty).Allocated store :=
      Ty.substVar_allocated (target := id) (previous := old.2) (replacement := ty)
        oldAllocated.2 tyAllocated
    refine ⟨?_, ?_⟩
    · intro m hm
      have hbound := newFirst m hm
      simpa [MStore.solve_length] using hbound
    · intro m hm
      have hbound := newSecond m hm
      simpa [MStore.solve_length] using hbound
  · intro constraint member
    rcases List.mem_map.mp member with ⟨old, inOld, rfl⟩
    have oldSolves := restSolves old inOld
    simpa only [Constraint.substVar, Ty.realize_substVar agrees] using oldSolves
  · exact MStore.unsolved_solve_lt store id ty hentry hsolNone

private theorem ConstraintsRealized.arrow_parts {valuation : Valuation}
    {leftDomain leftCodomain rightDomain rightCodomain : InfTy}
    {rest : List Constraint}
    (head : (Ty.arrow leftDomain leftCodomain).realize valuation =
      (Ty.arrow rightDomain rightCodomain).realize valuation)
    (restSolves : ConstraintsRealized valuation rest) :
    ConstraintsRealized valuation
      ((leftDomain, rightDomain) :: (leftCodomain, rightCodomain) :: rest) := by
  have parts := head
  simp only [Ty.realize_arrow, Ty.arrow.injEq] at parts
  intro constraint member
  rcases List.mem_cons.mp member with rfl | member
  · exact parts.1
  · rcases List.mem_cons.mp member with rfl | member
    · exact parts.2
    · exact restSolves constraint member

private theorem ConstraintsRealized.app_parts {valuation : Valuation}
    {leftFunction leftArgument rightFunction rightArgument : InfTy}
    {rest : List Constraint}
    (head : (Ty.app leftFunction leftArgument).realize valuation =
      (Ty.app rightFunction rightArgument).realize valuation)
    (restSolves : ConstraintsRealized valuation rest) :
    ConstraintsRealized valuation
      ((leftFunction, rightFunction) :: (leftArgument, rightArgument) :: rest) := by
  have parts := head
  simp only [Ty.realize_app, Ty.app.injEq] at parts
  intro constraint member
  rcases List.mem_cons.mp member with rfl | member
  · exact parts.1
  · rcases List.mem_cons.mp member with rfl | member
    · exact parts.2
    · exact restSolves constraint member

private theorem unifyPhase_complete {store : MStore} {fuel : Nat}
    {constraints : List Constraint}
    {valuation : Valuation}
    (enough : Constraints.size constraints ≤ fuel)
    (safe : store.Safe)
    (models : store.Models valuation)
    (resolved : ConstraintsResolved store constraints)
    (allocated : ConstraintsAllocated store constraints)
    (solves : ConstraintsRealized valuation constraints) :
    (∃ result, unifyPhase store fuel constraints = .finished result ∧
        result.Models valuation) ∨
    (∃ result rest, unifyPhase store fuel constraints = .bound result rest ∧
        result.Models valuation ∧ result.Safe ∧
        ConstraintsResolved result rest ∧ ConstraintsAllocated result rest ∧
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
          have headAllocated := allocated (left, right) (by simp)
          have restAllocated : ConstraintsAllocated store rest := by
            intro current member
            exact allocated current (by simp [member])
          have headSolves := solves (left, right) (by simp)
          have restSolves : ConstraintsRealized valuation rest :=
            ConstraintsRealized.tail solves
          by_cases equal : left = right
          · rw [unifyPhase_cons_eq, if_pos equal]
            refine ih ?_ restResolved restAllocated restSolves
            have h : left.size + right.size + Constraints.size rest ≤ fuel + 1 := by
              simpa [Constraints.size_cons] using enough
            have leftPos := Ty.size_pos left
            have rightPos := Ty.size_pos right
            omega
          · cases left with
            | var id =>
                exact Or.inr (phase_bound_left_complete
                  (ty := right) (by simpa using equal)
                  headResolved.1 headResolved.2
                  (headAllocated.1 id (by simp [Ty.vars])) headAllocated.2
                  (by simpa using headSolves)
                  safe models restResolved restAllocated restSolves)
            | prim name =>
                cases right with
                | var id =>
                    have phaseBase := unifyPhase_cons_eq_var_right store fuel
                      (.prim name) id rest (by simpa using equal)
                      (fun j impossible => nomatch impossible)
                    exact Or.inr (phase_bound_right_complete
                      (ty := .prim name) (by simpa using equal)
                      headResolved.1 headResolved.2
                      (headAllocated.2 id (by simp [Ty.vars])) headAllocated.1
                      (by simpa using headSolves)
                      phaseBase safe models restResolved restAllocated restSolves)
                | prim other =>
                    exfalso
                    have head := headSolves
                    simp only [Ty.realize_prim] at head
                    injection head with payload
                    exact equal (by rw [payload])
                | bvar index =>
                    exfalso
                    have head := headSolves
                    simp only [Ty.realize_prim, Ty.realize_bvar] at head
                    cases head
                | rigid level =>
                    exfalso
                    have head := headSolves
                    simp only [Ty.realize_prim, Ty.realize_rigid] at head
                    cases head
                | arrow rd rc =>
                    exfalso
                    have head := headSolves
                    simp only [Ty.realize_prim, Ty.realize_arrow] at head
                    cases head
                | con other =>
                    exfalso
                    have head := headSolves
                    simp only [Ty.realize_prim, Ty.realize_con] at head
                    cases head
                | app rf ra =>
                    exfalso
                    have head := headSolves
                    simp only [Ty.realize_prim, Ty.realize_app] at head
                    cases head
            | bvar index =>
                cases right with
                | var id =>
                    have phaseBase := unifyPhase_cons_eq_var_right store fuel
                      (.bvar index) id rest (by simpa using equal)
                      (fun j impossible => nomatch impossible)
                    exact Or.inr (phase_bound_right_complete
                      (ty := .bvar index) (by simpa using equal)
                      headResolved.1 headResolved.2
                      (headAllocated.2 id (by simp [Ty.vars])) headAllocated.1
                      (by simpa using headSolves)
                      phaseBase safe models restResolved restAllocated restSolves)
                | prim other =>
                    exfalso
                    have head := headSolves
                    simp only [Ty.realize_bvar, Ty.realize_prim] at head
                    cases head
                | bvar other =>
                    exfalso
                    have head := headSolves
                    simp only [Ty.realize_bvar] at head
                    injection head with payload
                    exact equal (by rw [payload])
                | rigid level =>
                    exfalso
                    have head := headSolves
                    simp only [Ty.realize_bvar, Ty.realize_rigid] at head
                    cases head
                | arrow rd rc =>
                    exfalso
                    have head := headSolves
                    simp only [Ty.realize_bvar, Ty.realize_arrow] at head
                    cases head
                | con other =>
                    exfalso
                    have head := headSolves
                    simp only [Ty.realize_bvar, Ty.realize_con] at head
                    cases head
                | app rf ra =>
                    exfalso
                    have head := headSolves
                    simp only [Ty.realize_bvar, Ty.realize_app] at head
                    cases head
            | rigid level =>
                cases right with
                | var id =>
                    have phaseBase := unifyPhase_cons_eq_var_right store fuel
                      (.rigid level) id rest (by simpa using equal)
                      (fun j impossible => nomatch impossible)
                    exact Or.inr (phase_bound_right_complete
                      (ty := .rigid level) (by simpa using equal)
                      headResolved.1 headResolved.2
                      (headAllocated.2 id (by simp [Ty.vars])) headAllocated.1
                      (by simpa using headSolves)
                      phaseBase safe models restResolved restAllocated restSolves)
                | prim other =>
                    exfalso
                    have head := headSolves
                    simp only [Ty.realize_rigid, Ty.realize_prim] at head
                    cases head
                | bvar index =>
                    exfalso
                    have head := headSolves
                    simp only [Ty.realize_rigid, Ty.realize_bvar] at head
                    cases head
                | rigid other =>
                    exfalso
                    have head := headSolves
                    simp only [Ty.realize_rigid] at head
                    injection head with payload
                    exact equal (by rw [payload])
                | arrow rd rc =>
                    exfalso
                    have head := headSolves
                    simp only [Ty.realize_rigid, Ty.realize_arrow] at head
                    cases head
                | con other =>
                    exfalso
                    have head := headSolves
                    simp only [Ty.realize_rigid, Ty.realize_con] at head
                    cases head
                | app rf ra =>
                    exfalso
                    have head := headSolves
                    simp only [Ty.realize_rigid, Ty.realize_app] at head
                    cases head
            | arrow ld lc =>
                cases right with
                | var id =>
                    have phaseBase := unifyPhase_cons_eq_var_right store fuel
                      (.arrow ld lc) id rest (by simpa using equal)
                      (fun j impossible => nomatch impossible)
                    exact Or.inr (phase_bound_right_complete
                      (ty := .arrow ld lc) (by simpa using equal)
                      headResolved.1 headResolved.2
                      (headAllocated.2 id (by simp [Ty.vars])) headAllocated.1
                      (by simpa using headSolves)
                      phaseBase safe models restResolved restAllocated restSolves)
                | prim other =>
                    exfalso
                    have head := headSolves
                    simp only [Ty.realize_arrow, Ty.realize_prim] at head
                    cases head
                | bvar index =>
                    exfalso
                    have head := headSolves
                    simp only [Ty.realize_arrow, Ty.realize_bvar] at head
                    cases head
                | rigid level =>
                    exfalso
                    have head := headSolves
                    simp only [Ty.realize_arrow, Ty.realize_rigid] at head
                    cases head
                | arrow rd rc =>
                    have phaseEq := unifyPhase_cons_eq_arrow store fuel
                      ld lc rd rc rest (by simpa using equal)
                    rw [phaseEq]
                    have enoughNew : Constraints.size
                        ((ld, rd) :: (lc, rc) :: rest) ≤ fuel := by
                      simp only [Constraints.size_cons, Ty.size] at enough ⊢
                      omega
                    exact ih enoughNew
                      (ConstraintsResolved.arrows resolved)
                      (ConstraintsAllocated.arrows headAllocated restAllocated)
                      (ConstraintsRealized.arrow_parts headSolves restSolves)
                | con other =>
                    exfalso
                    have head := headSolves
                    simp only [Ty.realize_arrow, Ty.realize_con] at head
                    cases head
                | app rf ra =>
                    exfalso
                    have head := headSolves
                    simp only [Ty.realize_arrow, Ty.realize_app] at head
                    cases head
            | con id =>
                cases right with
                | var other =>
                    have phaseBase := unifyPhase_cons_eq_var_right store fuel
                      (.con id) other rest (by simpa using equal)
                      (fun j impossible => nomatch impossible)
                    exact Or.inr (phase_bound_right_complete
                      (ty := .con id) (by simpa using equal)
                      headResolved.1 headResolved.2
                      (headAllocated.2 other (by simp [Ty.vars])) headAllocated.1
                      (by simpa using headSolves)
                      phaseBase safe models restResolved restAllocated restSolves)
                | prim other =>
                    exfalso
                    have head := headSolves
                    simp only [Ty.realize_con, Ty.realize_prim] at head
                    cases head
                | bvar index =>
                    exfalso
                    have head := headSolves
                    simp only [Ty.realize_con, Ty.realize_bvar] at head
                    cases head
                | rigid level =>
                    exfalso
                    have head := headSolves
                    simp only [Ty.realize_con, Ty.realize_rigid] at head
                    cases head
                | con other =>
                    exfalso
                    have head := headSolves
                    simp only [Ty.realize_con] at head
                    injection head with payload
                    exact equal (by rw [payload])
                | arrow rd rc =>
                    exfalso
                    have head := headSolves
                    simp only [Ty.realize_con, Ty.realize_arrow] at head
                    cases head
                | app rf ra =>
                    exfalso
                    have head := headSolves
                    simp only [Ty.realize_con, Ty.realize_app] at head
                    cases head
            | app lf la =>
                cases right with
                | var id =>
                    have phaseBase := unifyPhase_cons_eq_var_right store fuel
                      (.app lf la) id rest (by simpa using equal)
                      (fun j impossible => nomatch impossible)
                    exact Or.inr (phase_bound_right_complete
                      (ty := .app lf la) (by simpa using equal)
                      headResolved.1 headResolved.2
                      (headAllocated.2 id (by simp [Ty.vars])) headAllocated.1
                      (by simpa using headSolves)
                      phaseBase safe models restResolved restAllocated restSolves)
                | prim other =>
                    exfalso
                    have head := headSolves
                    simp only [Ty.realize_app, Ty.realize_prim] at head
                    cases head
                | bvar index =>
                    exfalso
                    have head := headSolves
                    simp only [Ty.realize_app, Ty.realize_bvar] at head
                    cases head
                | rigid level =>
                    exfalso
                    have head := headSolves
                    simp only [Ty.realize_app, Ty.realize_rigid] at head
                    cases head
                | con other =>
                    exfalso
                    have head := headSolves
                    simp only [Ty.realize_app, Ty.realize_con] at head
                    cases head
                | arrow rd rc =>
                    exfalso
                    have head := headSolves
                    simp only [Ty.realize_app, Ty.realize_arrow] at head
                    cases head
                | app rf ra =>
                    have phaseEq := unifyPhase_cons_eq_app store fuel
                      lf la rf ra rest (by simpa using equal)
                    rw [phaseEq]
                    have enoughNew : Constraints.size
                        ((lf, rf) :: (la, ra) :: rest) ≤ fuel := by
                      simp only [Constraints.size_cons, Ty.size] at enough ⊢
                      omega
                    exact ih enoughNew
                      (ConstraintsResolved.apps resolved)
                      (ConstraintsAllocated.apps headAllocated restAllocated)
                      (ConstraintsRealized.app_parts headSolves restSolves)

private theorem unifyLoop_complete {fuel : Nat} {store : MStore}
    {constraints : List Constraint}
    {valuation : Valuation}
    (fuelEnough : store.unsolved + 1 ≤ fuel)
    (safe : store.Safe)
    (models : store.Models valuation)
    (resolved : ConstraintsResolved store constraints)
    (allocated : ConstraintsAllocated store constraints)
    (solves : ConstraintsRealized valuation constraints) :
    ∃ result, unifyLoop fuel store constraints = some result ∧
      result.Models valuation := by
  induction fuel generalizing store constraints with
  | zero => omega
  | succ fuel ih =>
      rw [unifyLoop_succ]
      have phase := unifyPhase_complete (le_refl (Constraints.size constraints))
        safe models resolved allocated solves
      rcases phase with
        ⟨result, finishedRun, resultModels⟩ |
        ⟨result, rest, boundRun, resultModels, resultSafe, restResolved,
          restAllocated, restSolves, resultUnsolved⟩
      · rw [finishedRun]
        exact ⟨result, rfl, resultModels⟩
      · rw [boundRun]
        refine ih ?_ resultSafe resultModels restResolved restAllocated restSolves
        omega

/-- Every model of the input that unifies the two types is a model of the
result (in particular, unification succeeds). -/
theorem MStore.unify_complete {store : MStore} {left right : InfTy} {valuation : Valuation}
    (safe : store.Safe) (leftAllocated : left.Allocated store)
    (rightAllocated : right.Allocated store) (models : store.Models valuation)
    (unifies : left.realize valuation = right.realize valuation) :
    ∃ result, store.unify left right = some result ∧ result.Models valuation := by
  change ∃ result, unifyLoop (store.unsolved + 1) store
    [(store.apply left, store.apply right)] = some result ∧
      result.Models valuation
  have resolved : ConstraintsResolved store
      [(store.apply left, store.apply right)] := by
    intro constraint member
    simp only [List.mem_singleton] at member
    subst member
    exact ⟨MStore.apply_idem safe.normalized left,
      MStore.apply_idem safe.normalized right⟩
  have allocated : ConstraintsAllocated store
      [(store.apply left, store.apply right)] := by
    intro constraint member
    simp only [List.mem_singleton] at member
    subst member
    exact ⟨MStore.apply_allocated safe leftAllocated,
      MStore.apply_allocated safe rightAllocated⟩
  have solves : ConstraintsRealized valuation
      [(store.apply left, store.apply right)] := by
    intro constraint member
    simp only [List.mem_singleton] at member
    subst member
    have leftEq := MStore.Models.realize_apply models left
    have rightEq := MStore.Models.realize_apply models right
    rw [leftEq, rightEq]
    exact unifies
  exact unifyLoop_complete le_rfl safe models resolved allocated solves

/-! ## Anchored metavariables -/

/-- Substitution preserves a metavariable that is not the substituted one. -/
private theorem Ty.mem_vars_substVar_of_mem_of_ne {ty replacement : InfTy}
    {m target : Nat} (member : m ∈ ty.vars) (different : m ≠ target) :
    m ∈ (ty.substVar target replacement).vars := by
  induction ty with
  | prim => simp [Ty.vars] at member
  | arrow domain codomain ihDomain ihCodomain =>
      simp only [Ty.substVar_arrow, Ty.vars, List.mem_append] at member ⊢
      rcases member with member | member
      · exact Or.inl (ihDomain member)
      · exact Or.inr (ihCodomain member)
  | bvar => simp [Ty.vars] at member
  | rigid => simp [Ty.vars] at member
  | var id =>
      have idEq : m = id := by simpa [Ty.vars] using member
      subst idEq
      simp [Ty.vars, different]
  | con => simp [Ty.vars] at member
  | app function argument ihFunction ihArgument =>
      simp only [Ty.substVar_app, Ty.vars, List.mem_append] at member ⊢
      rcases member with member | member
      · exact Or.inl (ihFunction member)
      · exact Or.inr (ihArgument member)

/-- Substitution preserves every metavariable of the replacement, when the
substituted metavariable actually occurs in the type. -/
private theorem Ty.mem_vars_substVar_of_mem_replacement {ty replacement : InfTy}
    {m target : Nat} (occurs : target ∈ ty.vars)
    (member : m ∈ replacement.vars) :
    m ∈ (ty.substVar target replacement).vars := by
  induction ty with
  | prim => simp [Ty.vars] at occurs
  | arrow domain codomain ihDomain ihCodomain =>
      simp only [Ty.vars, List.mem_append] at occurs
      rcases occurs with occurs | occurs
      · simp only [Ty.substVar_arrow, Ty.vars, List.mem_append]
        exact Or.inl (ihDomain occurs)
      · simp only [Ty.substVar_arrow, Ty.vars, List.mem_append]
        exact Or.inr (ihCodomain occurs)
  | bvar => simp [Ty.vars] at occurs
  | rigid => simp [Ty.vars] at occurs
  | var id =>
      have idEq : target = id := by simpa [Ty.vars] using occurs
      subst idEq
      simpa using member
  | con => simp [Ty.vars] at occurs
  | app function argument ihFunction ihArgument =>
      simp only [Ty.vars, List.mem_append] at occurs
      rcases occurs with occurs | occurs
      · simp only [Ty.substVar_app, Ty.vars, List.mem_append]
        exact Or.inl (ihFunction occurs)
      · simp only [Ty.substVar_app, Ty.vars, List.mem_append]
        exact Or.inr (ihArgument occurs)

private theorem MStore.canBind_data {store : MStore} {id : Nat} {ty : InfTy}
    (guard : store.canBind id ty = true) :
    ∃ entry, store[id]? = some entry ∧ entry.solution = none := by
  obtain ⟨entry, hentry, hsol, _, _⟩ := MStore.canBind_iff.mp guard
  exact ⟨entry, hentry, hsol⟩

private theorem MStore.solve_anchored_of_canBind
    {store : MStore} {id : Nat} {ty : InfTy} {start level : Nat}
    (anchored : store.Anchored start level)
    (guard : store.canBind id ty = true) :
    (store.solve id ty).Anchored start level := by
  obtain ⟨entry, hentry, hnone⟩ := MStore.canBind_data guard
  have allocated : id < store.length := by
    by_contra hge
    have noneEq : store[id]? = none :=
      List.getElem?_eq_none_iff.mpr (by omega)
    rw [noneEq] at hentry
    exact Option.noConfusion hentry
  have unsolved : store.lookup id = none := by
    simp [MStore.lookup, hentry, hnone]
  intro j hstart hjlen hlevel hlookup
  have different : j ≠ id := by
    intro same
    subst j
    have selfLookup := MStore.lookup_solve_self store id ty hentry
    rw [selfLookup] at hlookup
    exact Option.noConfusion hlookup
  have jLen : j < store.length := by
    rw [MStore.solve_length] at hjlen
    exact hjlen
  have jLookupNone : store.lookup j = none := by
    cases h : store.lookup j with
    | none => rfl
    | some value =>
        rw [MStore.lookup_solve_of_ne store id j ty different, h] at hlookup
        exact Option.noConfusion hlookup
  have jLevel : (store.solve id ty).levelOf j ≤ level := hlevel
  rw [MStore.levelOf_solve] at jLevel
  simp only [different, if_false] at jLevel
  by_cases jMem : j ∈ ty.vars
  · by_cases oldLevel : store.levelOf j ≤ level
    · obtain ⟨outer, solution, outerLt, outerLookup, jMemSolution⟩ :=
        anchored j hstart jLen oldLevel jLookupNone
      have outerNe : outer ≠ id := by
        intro same
        subst same
        rw [outerLookup] at unsolved
        exact Option.noConfusion unsolved
      refine ⟨outer, solution.substVar id ty, outerLt, ?_, ?_⟩
      · rw [MStore.lookup_solve_of_ne store id outer ty outerNe]
        simp [outerLookup]
      · exact Ty.mem_vars_substVar_of_mem_of_ne jMemSolution different
    · have jLevelLe : min (store.levelOf j) (store.levelOf id) ≤ level := by
        simpa [jMem] using jLevel
      have idLevel : store.levelOf id ≤ level := by
        by_contra idNot
        have minEq : min (store.levelOf j) (store.levelOf id) = store.levelOf j :=
          Nat.min_eq_left (by omega)
        rw [minEq] at jLevelLe
        omega
      by_cases idBelow : id < start
      · refine ⟨id, ty, idBelow, ?_, jMem⟩
        exact MStore.lookup_solve_self store id ty hentry
      · obtain ⟨outer, solution, outerLt, outerLookup, idMemSolution⟩ :=
          anchored id (by omega) allocated idLevel unsolved
        have outerNe : outer ≠ id := by
          intro same
          subst same
          rw [outerLookup] at unsolved
          exact Option.noConfusion unsolved
        refine ⟨outer, solution.substVar id ty, outerLt, ?_, ?_⟩
        · rw [MStore.lookup_solve_of_ne store id outer ty outerNe]
          simp [outerLookup]
        · exact Ty.mem_vars_substVar_of_mem_replacement idMemSolution jMem
  · have oldLevel : store.levelOf j ≤ level := by
      simpa [jMem] using jLevel
    obtain ⟨outer, solution, outerLt, outerLookup, jMemSolution⟩ :=
      anchored j hstart jLen oldLevel jLookupNone
    have outerNe : outer ≠ id := by
      intro same
      subst same
      rw [outerLookup] at unsolved
      exact Option.noConfusion unsolved
    refine ⟨outer, solution.substVar id ty, outerLt, ?_, ?_⟩
    · rw [MStore.lookup_solve_of_ne store id outer ty outerNe]
      simp [outerLookup]
    · exact Ty.mem_vars_substVar_of_mem_of_ne jMemSolution different

private theorem match_bound_anchored
    {store : MStore} {id : Nat} {ty : InfTy} {rest : List Constraint}
    {start level : Nat}
    (anchored : store.Anchored start level)
    (guard : store.canBind id ty = true) :
    (match (UnifyPhase.bound (store.solve id ty) rest : UnifyPhase) with
     | .finished result => result.Anchored start level
     | .bound result _ => result.Anchored start level
     | .failed | .outOfFuel => True) := by
  simpa using MStore.solve_anchored_of_canBind anchored guard

private theorem ite_bound_anchored
    {store : MStore} {id : Nat} {ty : InfTy} {rest : List Constraint}
    {start level : Nat}
    (anchored : store.Anchored start level) :
    (match (if store.canBind id ty = true then
              (UnifyPhase.bound (store.solve id ty) rest : UnifyPhase)
            else .failed) with
     | .finished result => result.Anchored start level
     | .bound result _ => result.Anchored start level
     | .failed | .outOfFuel => True) := by
  by_cases guard : store.canBind id ty = true
  · rw [if_pos guard]
    exact match_bound_anchored (rest := rest) anchored guard
  · rw [if_neg guard]
    trivial

private theorem unifyPhase_anchored
    {store : MStore} {fuel : Nat} {constraints : List Constraint}
    {start level : Nat}
    (anchored : store.Anchored start level) :
    (match unifyPhase store fuel constraints with
     | .finished result => result.Anchored start level
     | .bound result _ => result.Anchored start level
     | .failed | .outOfFuel => True) := by
  induction fuel generalizing constraints with
  | zero =>
      cases constraints with
      | nil => simp [unifyPhase, anchored]
      | cons _ _ => simp [unifyPhase]
  | succ fuel ih =>
      cases constraints with
      | nil => simp [unifyPhase, anchored]
      | cons constraint rest =>
          obtain ⟨left, right⟩ := constraint
          rw [unifyPhase_cons_eq]
          by_cases equal : left = right
          · rw [if_pos equal]
            exact ih
          · rw [if_neg equal]
            cases left <;> cases right <;> simp only []
            all_goals first
              | exact ih
              | exact ite_bound_anchored anchored
              | simp

private theorem unifyPhase_finished_anchored
    {store result : MStore} {fuel : Nat} {constraints : List Constraint}
    {start level : Nat}
    (anchored : store.Anchored start level)
    (run : unifyPhase store fuel constraints = .finished result) :
    result.Anchored start level := by
  have h := unifyPhase_anchored (fuel := fuel) (constraints := constraints)
    (start := start) (level := level) anchored
  rw [run] at h
  exact h

private theorem unifyPhase_bound_anchored
    {store result : MStore} {fuel : Nat} {constraints rest : List Constraint}
    {start level : Nat}
    (anchored : store.Anchored start level)
    (run : unifyPhase store fuel constraints = .bound result rest) :
    result.Anchored start level := by
  have h := unifyPhase_anchored (fuel := fuel) (constraints := constraints)
    (start := start) (level := level) anchored
  rw [run] at h
  exact h

private theorem unifyLoop_anchored
    {fuel : Nat} {store result : MStore} {constraints : List Constraint}
    {start level : Nat}
    (anchored : store.Anchored start level)
    (run : unifyLoop fuel store constraints = some result) :
    result.Anchored start level := by
  induction fuel generalizing store constraints with
  | zero => simp [unifyLoop] at run
  | succ fuel ih =>
      rw [unifyLoop_succ] at run
      split at run
      · rename_i finishedRun
        injection run with resultEq
        subst resultEq
        exact unifyPhase_finished_anchored anchored finishedRun
      · rename_i boundRun
        exact ih (unifyPhase_bound_anchored anchored boundRun) run
      · exact nomatch run
      · exact nomatch run

/-- A metavariable lowered to `level` or below by a binding enters the
solution of whatever it was unified with, which is anchored. -/
theorem MStore.unify_anchored {store result : MStore} {left right : InfTy}
    (anchored : store.Anchored start level) (run : store.unify left right = some result) :
    result.Anchored start level := by
  change unifyLoop (store.unsolved + 1) store
    [(store.apply left, store.apply right)] = some result at run
  exact unifyLoop_anchored anchored run

end EPL2
