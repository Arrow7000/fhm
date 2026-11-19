import EPL.Spec.Models
import EPL.Infer

/-!
# Store operations and the inference invariant

Each store operation of inference (`fresh`, `freshMany`, `allocate`,
`paramTy`; `unify` is in `EPL.Spec.Unify`) is specified by how it changes
the set of models:

* *sound*: every model of the new store is a model of the old one, with some
  property of the returned type;
* *principal*: every model of the old store and every choice the declarative
  rule could make extends to a model of the new store that agrees on the old
  metavariables and realizes the returned type as that choice.

`InferPre`/`InferPost`/`InferSpec` state the same for a whole run of
`inferAt`.
-/

namespace EPL

/-! ## Errors

Error values carry no meaning in the specification: these lemmas reduce runs
that wrap errors to the runs they wrap. -/

@[simp] theorem Except.mapError_eq_ok_iff {f : ε → ε'} {run : Except ε α} {a : α} :
    run.mapError f = .ok a ↔ run = .ok a := by
  cases run <;> simp [Except.mapError]

theorem Except.mapError_eq_error {f : ε → ε'} {run : Except ε α} {error : ε}
    (failed : run = .error error) : run.mapError f = .error (f error) := by
  subst failed; rfl

@[simp] theorem MStore.unifyAt_eq_ok_iff {store result : MStore} {path : List ExprStep}
    {actual expected : InfTy} :
    store.unifyAt path actual expected = .ok result ↔ store.unify actual expected = .ok result :=
  Except.mapError_eq_ok_iff

theorem MStore.unifyAt_eq_error {store : MStore} {path : List ExprStep} {actual expected : InfTy}
    {cause : UnifyError} (failed : store.unify actual expected = .error cause) :
    store.unifyAt path actual expected = .error
      ⟨path, .mismatch (store.apply expected) (store.apply actual) cause⟩ :=
  Except.mapError_eq_error failed

@[simp] theorem Option.getDM_eq_ok_iff {option : Option α} {error : ε} {a : α} :
    (option.getDM (throw error : Except ε α)) = .ok a ↔ option = some a := by
  cases option <;> simp [Option.getDM, throw, throwThe, MonadExceptOf.throw, pure, Except.pure]

/-! ## Store operations -/

/-- Lookup in an appended block of unsolved entries: either it is an old
entry or it is one of the appended ones. -/
private theorem MStore.append_replicate_getElem? {store : MStore} {count level : Nat} {id : Nat}
    {entry : MEntry}
    (h : (store ++ List.replicate count (⟨level, none⟩ : MEntry))[id]? = some entry) :
    store[id]? = some entry ∨ (entry = ⟨level, none⟩ ∧ id - store.length < count) := by
  rw [List.getElem?_append] at h
  by_cases hlt : id < store.length
  · rw [if_pos hlt] at h
    exact Or.inl h
  · rw [if_neg hlt] at h
    right
    rw [List.getElem?_replicate] at h
    by_cases hc : id - store.length < count
    · rw [if_pos hc] at h
      exact ⟨(Option.some.inj h).symm, hc⟩
    · rw [if_neg hc] at h
      exact absurd h (by simp)

theorem MStore.append_unsolved_levelOf (store : MStore) (id : Nat) :
    (store ++ List.replicate count (⟨level, none⟩ : MEntry)).levelOf id =
      if id < store.length then store.levelOf id
      else if id < store.length + count then level else 0 := by
  unfold MStore.levelOf
  rw [List.getElem?_append]
  by_cases h1 : id < store.length
  · rw [if_pos h1, if_pos h1]
  · rw [if_neg h1, if_neg h1]
    rw [List.getElem?_replicate]
    by_cases h2 : id - store.length < count
    · rw [if_pos h2, if_pos (by omega)]
      simp
    · rw [if_neg h2, if_neg (by omega)]
      simp

theorem MStore.append_unsolved_lookup (store : MStore) (id : Nat) :
    (store ++ List.replicate count (⟨level, none⟩ : MEntry)).lookup id =
      if id < store.length then store.lookup id else none := by
  unfold MStore.lookup
  rw [List.getElem?_append]
  by_cases h1 : id < store.length <;> simp [h1, List.getElem?_replicate]

/-- Appending unsolved entries adds no solutions. -/
private theorem MStore.lookup_append_unsolved_some {store : MStore} {count level id : Nat}
    {ty : InfTy}
    (h : (store ++ List.replicate count (⟨level, none⟩ : MEntry)).lookup id = some ty) :
    store.lookup id = some ty := by
  by_cases hlt : id < store.length
  · simpa [MStore.append_unsolved_lookup, hlt] using h
  · rw [MStore.append_unsolved_lookup, if_neg hlt] at h
    simp at h

/-- Structural facts about appending unsolved metavariables. -/
theorem MStore.append_unsolved_safe {store : MStore} (safe : store.Safe) :
    (store ++ List.replicate count (⟨level, none⟩ : MEntry)).Safe := by
  refine ⟨?_, ?_, ?_⟩
  · intro id entry ty hfind hsol
    rcases MStore.append_replicate_getElem? hfind with h | ⟨rfl, _⟩
    · obtain ⟨hwf, hlev⟩ := safe.leveled id entry ty h hsol
      refine ⟨hwf, fun v hv => ?_⟩
      have hvlt : v < store.length :=
        safe.allocated id ty (by simp [MStore.lookup, h, hsol]) v hv
      rw [MStore.append_unsolved_levelOf, if_pos hvlt]
      exact hlev v hv
    · simp at hsol
  · intro id ty hlookup v hv
    simp only [List.length_append, List.length_replicate]
    have hbound := safe.allocated id ty (MStore.lookup_append_unsolved_some hlookup) v hv
    omega
  · intro id ty hlookup m hm
    have hold := safe.normalized id ty (MStore.lookup_append_unsolved_some hlookup) m hm
    rw [MStore.append_unsolved_lookup]
    split <;> simp [hold]

theorem MStore.freshMany_fst (store : MStore) (level count : Nat) :
    (store.freshMany level count).1 = (List.range count).map fun i => .var (store.length + i) :=
  rfl

theorem MStore.freshMany_snd (store : MStore) (level count : Nat) :
    (store.freshMany level count).2 = store ++ List.replicate count ⟨level, none⟩ :=
  rfl

theorem MStore.fresh_eq (store : MStore) (level : Nat) :
    store.fresh level = (.var store.length, store ++ List.replicate 1 ⟨level, none⟩) :=
  rfl

/-- Reading a list at every index of `List.range` gives the list back. -/
private theorem List.map_range_getD {α : Type} (l : List α) (d : α) :
    (List.range l.length).map (fun i => l.getD i d) = l := by
  apply List.ext_getElem?
  intro j
  rw [List.getElem?_map]
  by_cases hj : j < l.length
  · rw [List.getElem?_range hj]
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]
  · have hj' : l.length ≤ j := Nat.le_of_not_lt hj
    have hnone : (List.range l.length)[j]? = none :=
      List.getElem?_eq_none_iff.mpr (by simpa using hj')
    rw [hnone, List.getElem?_eq_none_iff.mpr hj']
    simp

/-- A model extends over appended unsolved entries, given well-formed images
for them. -/
private theorem models_append_unsolved_extend {store : MStore} {valuation : Valuation}
    {count level : Nat} (safe : store.Safe) (models : store.Models valuation)
    {image : Nat → SemTy} (wf : ∀ i < count, (image i).WF level) :
    (store ++ List.replicate count (⟨level, none⟩ : MEntry)).Models
        (fun id => if id < store.length then valuation id else image (id - store.length)) ∧
      Agree store.length valuation
        (fun id => if id < store.length then valuation id else image (id - store.length)) := by
  refine ⟨?_, fun id hid => by simp [hid]⟩
  rw [MStore.models_append_unsolved]
  refine ⟨MStore.Models.congr safe models (fun id hid => by simp [hid]), ?_⟩
  intro i hi
  rw [if_neg (by omega : ¬ store.length + i < store.length), Nat.add_sub_cancel_left]
  exact wf i hi

/-- Any arguments well-formed at the level can be chosen for fresh
metavariables. -/
theorem MStore.freshMany_principal {store : MStore} {valuation : Valuation} (safe : store.Safe)
    (models : store.Models valuation) (length : args.length = count)
    (argsWF : ∀ arg ∈ args, arg.WF level) :
    ∃ extended, (store.freshMany level count).2.Models extended ∧
      Agree store.length valuation extended ∧
      (store.freshMany level count).1.map (·.realize extended) = args := by
  let extended : Valuation := fun id =>
    if id < store.length then valuation id else args.getD (id - store.length) (.prim .unit)
  have himage : ∀ i < count, (args.getD i (.prim .unit)).WF level := by
    intro i hi
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]
    exact argsWF _ (List.getElem_mem (by omega))
  obtain ⟨hmodels, hagree⟩ := models_append_unsolved_extend
    (image := fun i => args.getD i (.prim .unit)) safe models himage
  refine ⟨extended, ?_, ?_, ?_⟩
  · rw [MStore.freshMany_snd]
    exact hmodels
  · exact hagree
  · rw [MStore.freshMany_fst, show count = args.length from length.symm, List.map_map]
    trans (List.range args.length).map (fun i => args.getD i (.prim .unit))
    · apply List.map_congr_left
      intro i _
      show extended (store.length + i) = args.getD i (.prim .unit)
      simp only [extended, Nat.add_sub_cancel_left]
      rw [if_neg (by omega)]
    · exact List.map_range_getD args (.prim .unit)

theorem MStore.allocate_snd (store : MStore) (level : Nat) (template : Template) :
    (store.allocate level template).2 =
      store ++ List.replicate template.vars.dedup.length ⟨level, none⟩ :=
  rfl

/-- `allocate` is `bind` with a fresh metavariable for every hole. -/
private theorem allocate_fst (store : MStore) (level : Nat) (template : Template) :
    (store.allocate level template).1 =
      template.bind (fun name =>
        (Ty.var (store.length + template.vars.dedup.idxOf name) : InfTy)) :=
  rfl

/-- The metavariables of an allocated template are exactly the fresh ones. -/
private theorem allocate_vars {store : MStore} {template : Template} {level id : Nat}
    (hid : id ∈ (store.allocate level template).1.vars) :
    store.length ≤ id ∧ id < (store.allocate level template).2.length := by
  rw [MStore.allocate_snd]
  rw [allocate_fst] at hid
  obtain ⟨name, hname, hid'⟩ := Ty.mem_vars_bind.mp hid
  simp only [Ty.vars, List.mem_singleton] at hid'
  have hidx : template.vars.dedup.idxOf name < template.vars.dedup.length := by
    rw [List.idxOf_lt_length_iff]
    exact List.mem_dedup.mpr hname
  rw [List.length_append, List.length_replicate]
  omega

/-- Realizing an allocated template substitutes its fresh metavariables. -/
private theorem allocate_realize (store : MStore) (level : Nat) (template : Template)
    (valuation : Valuation) :
    (store.allocate level template).1.realize valuation =
      template.bind (fun name => valuation (store.length + template.vars.dedup.idxOf name)) := by
  rw [Ty.realize, allocate_fst, Ty.bind_bind]
  rfl

/-- The allocated type is the template with holes replaced by fresh
metavariables. -/
theorem MStore.allocate_wf {store : MStore} {template : Template} (wf : template.WF level) :
    (store.allocate level template).1.WF level ∧
      (store.allocate level template).1.Allocated (store.allocate level template).2 ∧
      ∀ id ∈ (store.allocate level template).1.vars, store.length ≤ id := by
  refine ⟨?_, ?_, ?_⟩
  · rw [allocate_fst]
    exact Ty.scoped_bind wf (fun _ _ => trivial)
  · intro id hid
    exact (allocate_vars hid).2
  · intro id hid
    exact (allocate_vars hid).1

/-- Every realization of an allocated template matches the template. -/
theorem MStore.allocate_sound (store : MStore) (level : Nat) (template : Template)
    (valuation : Valuation) :
    template.Matches ((store.allocate level template).1.realize valuation) :=
  ⟨fun name => valuation (store.length + template.vars.dedup.idxOf name),
    (allocate_realize store level template valuation).symm⟩

/-- Every type the template matches, well-formed at the level, is a
realization of the allocated template. -/
theorem MStore.allocate_principal {store : MStore} {valuation : Valuation} {template : Template}
    {ty : SemTy} (safe : store.Safe) (models : store.Models valuation)
    (fits : template.Matches ty) (wf : ty.WF level) :
    ∃ extended, (store.allocate level template).2.Models extended ∧
      Agree store.length valuation extended ∧
      (store.allocate level template).1.realize extended = ty := by
  obtain ⟨holes, hbind⟩ := fits
  let extended : Valuation := fun id =>
    if id < store.length then valuation id
    else holes (template.vars.dedup.getD (id - store.length) "")
  have himage : ∀ name ∈ template.vars, (holes name).WF level := by
    have hscoped : (template.bind holes).Scoped level 0 := by rw [hbind]; exact wf
    exact (Ty.scoped_of_bind hscoped).2
  have hfresh : ∀ i < template.vars.dedup.length,
      (holes (template.vars.dedup.getD i "")).WF level := by
    intro i hi
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
    exact himage _ (List.mem_dedup.mp (List.getElem_mem hi))
  obtain ⟨hmodels, hagree⟩ := models_append_unsolved_extend
    (image := fun i => holes (template.vars.dedup.getD i "")) safe models hfresh
  refine ⟨extended, ?_, ?_, ?_⟩
  · rw [MStore.allocate_snd]
    exact hmodels
  · exact hagree
  · rw [allocate_realize, ← hbind]
    apply Ty.bind_congr
    intro name hname
    show extended (store.length + template.vars.dedup.idxOf name) = holes name
    simp only [extended, Nat.add_sub_cancel_left]
    rw [if_neg (by omega), List.getD_eq_getElem?_getD,
      List.getElem?_idxOf (List.mem_dedup.mpr hname)]
    simp

/-- The parameter type of a lambda: a fresh metavariable or an allocated
annotation. Fails exactly on an annotation with an out-of-scope variable. -/
theorem paramTy_spec {store : MStore} (safe : store.Safe) :
    match paramTy k store param with
    | some (ty, store') =>
        store' = store ++ List.replicate (store'.length - store.length) ⟨k, none⟩ ∧
        ty.WF k ∧ ty.Allocated store' ∧ (∀ id ∈ ty.vars, store.length ≤ id) ∧
        (∀ valuation, Template.MatchesOpt param (ty.realize valuation)) ∧
        ∀ valuation paramSem, store.Models valuation → Template.MatchesOpt param paramSem →
          paramSem.WF k →
          ∃ extended, store'.Models extended ∧ Agree store.length valuation extended ∧
            ty.realize extended = paramSem
    | none => ∀ paramSem : SemTy, Template.MatchesOpt param paramSem → ¬ paramSem.WF k := by
  cases param with
  | none =>
    dsimp only [paramTy]
    rw [MStore.fresh_eq]
    refine ⟨by simp, trivial, ?_, ?_, fun _ => trivial, ?_⟩
    · simp [Ty.Allocated, Ty.vars]
    · simp [Ty.vars]
    · intro valuation paramSem hmodels hmatch hwf
      let extended : Valuation := fun id =>
        if id < store.length then valuation id else paramSem
      obtain ⟨hmodels', hagree⟩ := models_append_unsolved_extend (count := 1) (level := k)
        (image := fun _ => paramSem) safe hmodels (fun _ _ => hwf)
      refine ⟨extended, ?_, ?_, ?_⟩
      · exact hmodels'
      · exact hagree
      · show extended store.length = paramSem
        simp only [extended]
        rw [if_neg (by omega)]
  | some template =>
    by_cases hwf : template.WF k
    · dsimp only [paramTy]
      rw [if_pos hwf]
      obtain ⟨hWF, halloc, hbound⟩ := MStore.allocate_wf hwf
      exact ⟨by simp [List.length_append, List.length_replicate], hWF, halloc, hbound,
        fun valuation => MStore.allocate_sound store k template valuation,
        fun _ _ hmodels hmatch hsem => MStore.allocate_principal safe hmodels hmatch hsem⟩
    · dsimp only [paramTy]
      rw [if_neg hwf]
      intro paramSem hmatch hsem
      exact hwf (Template.Matches.wf hmatch hsem)

/-! ## Anchoring -/

/-- Nothing is allocated from the frontier on. -/
theorem MStore.Anchored.of_length (store : MStore) (level : Nat) :
    store.Anchored store.length level := by
  intro id hstart _ _ _
  omega

/-- Metavariables appended above `level` are not `Anchored`'s concern. -/
theorem MStore.Anchored.append_unsolved {store : MStore} (anchored : store.Anchored start level)
    (above : level < level') :
    (store ++ List.replicate count (⟨level', none⟩ : MEntry)).Anchored start level := by
  intro id hstart hlen hlev hlookup
  rw [List.length_append, List.length_replicate] at hlen
  rw [MStore.append_unsolved_lookup] at hlookup
  by_cases hlt : id < store.length
  · rw [if_pos hlt] at hlookup
    rw [MStore.append_unsolved_levelOf, if_pos hlt] at hlev
    obtain ⟨outer, ty, houter, hlook, hmem⟩ := anchored id hstart hlt hlev hlookup
    exact ⟨outer, ty, houter, by
      rw [MStore.append_unsolved_lookup, if_pos (by omega)]
      exact hlook, hmem⟩
  · rw [MStore.append_unsolved_levelOf, if_neg hlt, if_pos hlen] at hlev
    omega

/-! ## Contexts and schemes -/

theorem Ctx.realize_cons (scheme : Scheme Nat) (ctx : Ctx Nat) (valuation : Valuation) :
    Ctx.realize (scheme :: ctx) valuation = scheme.realize valuation :: ctx.realize valuation :=
  rfl

theorem Scheme.realize_mono (ty : InfTy) (valuation : Valuation) :
    (Scheme.mono ty).realize valuation = .mono (ty.realize valuation) :=
  rfl

theorem Ctx.realize_getElem? (ctx : Ctx Nat) (valuation : Valuation) (index : Nat) :
    (ctx.realize valuation)[index]? = (ctx[index]?).map (·.realize valuation) := by
  unfold Ctx.realize
  rw [List.getElem?_map]

/-- A signature's scheme has no metavariables. -/
theorem Scheme.realize_lift (scheme : Scheme Empty) (valuation : Valuation) :
    (scheme.lift : Scheme Nat).realize valuation = scheme := by
  obtain ⟨arity, body⟩ := scheme
  show (⟨arity, (body.lift).bind valuation⟩ : Scheme Empty) = ⟨arity, body⟩
  rw [Ty.lift_bind, Ty.lift_self]

/-- Realizing an instance: realize the scheme and the arguments. The scheme's
metavariables must have `bvar`-free images, as they do under any model. -/
theorem Scheme.realize_inst (scheme : Scheme Nat) (args : List InfTy) {valuation : Valuation}
    (closed : ∀ id ∈ scheme.body.vars, (valuation id).WF k) :
    (scheme.inst args).realize valuation =
      (scheme.realize valuation).inst (args.map (·.realize valuation)) := by
  unfold Scheme.realize Ty.realize
  exact Scheme.inst_bind scheme args closed

theorem Ctx.realize_congr {ctx : Ctx Nat} {first second : Valuation} {frontier : Nat}
    (allocated : ∀ scheme ∈ ctx, ∀ id ∈ scheme.body.vars, id < frontier)
    (agree : Agree frontier first second) : ctx.realize first = ctx.realize second := by
  unfold Ctx.realize
  apply List.map_congr_left
  intro scheme hscheme
  obtain ⟨arity, body⟩ := scheme
  simpa [Scheme.realize, Scheme.bind, Ty.realize] using
    Ty.realize_congr (ty := body) (allocated ⟨arity, body⟩ hscheme) agree

/-- Valuations that agree on the metavariables at or below `level` realize a
context whose metavariables are all at or below `level` alike. -/
theorem Ctx.realize_congr_levels {ctx : Ctx Nat} {store : MStore} {first second : Valuation}
    (levels : ∀ scheme ∈ ctx, scheme.body.LevelBounded store level)
    (agree : ∀ id, store.levelOf id ≤ level → first id = second id) :
    ctx.realize first = ctx.realize second := by
  unfold Ctx.realize
  apply List.map_congr_left
  intro scheme hscheme
  have hb : scheme.body.bind first = scheme.body.bind second :=
    Ty.bind_congr fun v hv => agree v (levels scheme hscheme v hv)
  simpa [Scheme.realize, Scheme.bind] using hb

theorem Ctx.realize_wf {ctx : Ctx Nat} {store : MStore} {valuation : Valuation}
    (models : store.Models valuation) (wf : ∀ scheme ∈ ctx, scheme.WF k)
    (allocated : ∀ scheme ∈ ctx, scheme.body.Allocated store)
    (levels : ∀ scheme ∈ ctx, scheme.body.LevelBounded store k) :
    (ctx.realize valuation).WF k := by
  unfold Ctx.realize Ctx.WF
  intro realized hrealized
  obtain ⟨scheme, hscheme, rfl⟩ := List.mem_map.mp hrealized
  show (scheme.body.bind valuation).Scoped k scheme.arity
  exact Ty.scoped_bind (wf scheme hscheme) (fun v hv =>
    Ty.Scoped.mono (MStore.Models.image_wf models (allocated scheme hscheme v hv))
      (levels scheme hscheme v hv) (Nat.zero_le _))

/-- The scheme an explicit let binds: the completed generic type, closed. Its
realization is the closed realization, when the completed type's
metavariables are outer (images well-formed at the outer depth `k`). -/
theorem Scheme.realize_closeRigids {ty : InfTy} {valuation : Valuation}
    (images : ∀ id ∈ ty.vars, (valuation id).WF k) :
    (⟨n, ty.closeRigids k n⟩ : Scheme Nat).realize valuation =
      ⟨n, (ty.realize valuation).closeRigids k n⟩ := by
  show (⟨n, (ty.closeRigids k n).bind valuation⟩ : Scheme Empty) =
    ⟨n, (ty.realize valuation).closeRigids k n⟩
  rw [Ty.realize, Ty.closeRigids_bind images]

/-! ## The inference invariant -/

/-- What a run at depth `k` assumes of its context and store. -/
structure InferPre (k : Nat) (ctx : Ctx Nat) (store : MStore) : Prop where
  safe : store.Safe
  ctxWF : ∀ scheme ∈ ctx, scheme.WF k
  ctxAllocated : ∀ scheme ∈ ctx, scheme.body.Allocated store
  ctxLevels : ∀ scheme ∈ ctx, scheme.body.LevelBounded store k

/-- `InferPre` survives any extension of the store that lowers no level. -/
theorem InferPre.extend {store store' : MStore} (pre : InferPre k ctx store) (safe : store'.Safe)
    (grows : store.length ≤ store'.length)
    (levels : ∀ id < store.length, store'.levelOf id ≤ store.levelOf id) :
    InferPre k ctx store' := by
  refine ⟨safe, pre.ctxWF, ?_, ?_⟩
  · intro scheme hscheme id hid
    exact lt_of_lt_of_le (pre.ctxAllocated scheme hscheme id hid) grows
  · intro scheme hscheme id hid
    have hi : id < store.length := pre.ctxAllocated scheme hscheme id hid
    exact le_trans (levels id hi) (pre.ctxLevels scheme hscheme id hid)

/-- A run one explicit let deeper sees the same context. -/
theorem InferPre.deeper (pre : InferPre k ctx store) (le : k ≤ k') : InferPre k' ctx store := by
  refine ⟨pre.safe, ?_, pre.ctxAllocated, ?_⟩
  · intro scheme hscheme
    exact Ty.Scoped.mono (pre.ctxWF scheme hscheme) le (Nat.le_refl _)
  · intro scheme hscheme id hid
    exact le_trans (pre.ctxLevels scheme hscheme id hid) le

/-- A context entry for a type of the run's own depth. -/
theorem InferPre.cons_mono (pre : InferPre k ctx store) (wf : ty.WF k)
    (allocated : ty.Allocated store) (levels : ty.LevelBounded store k) :
    InferPre k (.mono ty :: ctx) store := by
  refine ⟨pre.safe, ?_, ?_, ?_⟩ <;>
    intro scheme hscheme <;>
    rcases List.mem_cons.mp hscheme with rfl | h
  · exact wf
  · exact pre.ctxWF scheme h
  · exact allocated
  · exact pre.ctxAllocated scheme h
  · exact levels
  · exact pre.ctxLevels scheme h

/-- What a successful run at depth `k` guarantees. -/
structure InferPost (sig : Signature) (k : Nat) (ctx : Ctx Nat) (src : Source)
    (store : MStore) (result : Inferred) : Prop where
  safe : result.store.Safe
  grows : store.length ≤ result.store.length
  levels : ∀ id < store.length, result.store.levelOf id ≤ store.levelOf id
  tyWF : result.ty.WF k
  tyAllocated : result.ty.Allocated result.store
  tyLevels : result.ty.LevelBounded result.store k
  elabAllocated : ∀ ann ∈ result.elaboration.anns, ann.Allocated result.store
  /-- Runs deeper than `level` keep the store anchored at `level`. -/
  anchored : ∀ start level, level < k → start ≤ store.length →
    store.Anchored start level → result.store.Anchored start level
  /-- Every model of the result is a model of the input under which the
  program elaborates as inferred. -/
  sound : ∀ valuation, result.store.Models valuation →
    store.Models valuation ∧
      Elaborates sig k (ctx.realize valuation) src (result.elaboration.realize valuation)
        (result.ty.realize valuation)
  /-- Every typing, under any model of the input, is a realization of the
  result. -/
  principal : ∀ valuation, store.Models valuation →
    ∀ elaboration ty, Typing sig k (ctx.realize valuation) src elaboration ty →
      ∃ extended, result.store.Models extended ∧ Agree store.length valuation extended ∧
        result.elaboration.realize extended = elaboration ∧ result.ty.realize extended = ty

/-- The specification of one run: it either succeeds with `InferPost`, or
fails, whatever the error, and the program elaborates under no model of the
input store. -/
def InferSpec (sig : Signature) (k : Nat) (ctx : Ctx Nat) (src : Source) (store : MStore) : Prop :=
  match inferAt sig k ctx src store with
  | .ok result => InferPost sig k ctx src store result
  | .error _ => ∀ valuation, store.Models valuation →
      ∀ elaboration ty, ¬ Elaborates sig k (ctx.realize valuation) src elaboration ty

end EPL
