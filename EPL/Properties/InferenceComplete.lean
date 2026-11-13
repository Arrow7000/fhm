import EPL.Properties.InferenceSound

/-!
# Completeness of inference

`infer` accepts exactly the programs with a unique elaboration (and type),
and returns that elaboration (`infer_eq_some_iff`). An elaboration records
every implicit type: lambda parameter types, `fix` types and completed
schemes. Unknowns that only instantiate a scheme are not recorded, so they
need not be determined.

The internal facts are principality (every elaboration is an instance of the
inferred one) and success (inference does not fail on an elaborable program).
-/

namespace EPL

/-- Every primitive operator's result type is semantic and scoped (it is a
closed type built from primitives, arrows, and possibly `Bool`). -/
private theorem primOpTy_wf {sig : Signature} {op : PrimOp} {ty : Ty}
    (hty : op.ty sig = some ty) {rigidCount : Nat} : ty.WF rigidCount 0 := by
  cases op with
  | intAdd | intSub =>
      simp only [PrimOp.ty, Option.some.injEq] at hty
      subst hty
      exact ⟨Ty.Scoped.arrow Ty.Scoped.prim
          (Ty.Scoped.arrow Ty.Scoped.prim Ty.Scoped.prim),
        Ty.MetaFree.arrow Ty.MetaFree.prim
          (Ty.MetaFree.arrow Ty.MetaFree.prim Ty.MetaFree.prim)⟩
  | intLt =>
      by_cases hb : sig.HasBool
      · simp only [PrimOp.ty, hb, if_true, Option.some.injEq] at hty
        subst hty
        exact ⟨Ty.Scoped.arrow Ty.Scoped.prim
            (Ty.Scoped.arrow Ty.Scoped.prim (Ty.Scoped.con 0)),
          Ty.MetaFree.arrow Ty.MetaFree.prim
            (Ty.MetaFree.arrow Ty.MetaFree.prim Ty.MetaFree.con)⟩
      · simp [PrimOp.ty, hb] at hty
  | charLt =>
      by_cases hb : sig.HasBool
      · simp only [PrimOp.ty, hb, if_true, Option.some.injEq] at hty
        subst hty
        exact ⟨Ty.Scoped.arrow Ty.Scoped.prim
            (Ty.Scoped.arrow Ty.Scoped.prim (Ty.Scoped.con 0)),
          Ty.MetaFree.arrow Ty.MetaFree.prim
            (Ty.MetaFree.arrow Ty.MetaFree.prim Ty.MetaFree.con)⟩
      · simp [PrimOp.ty, hb] at hty

private theorem primOpTy_metaFree {sig : Signature} {op : PrimOp} {ty : Ty}
    (hty : op.ty sig = some ty) : ty.MetaFree :=
  (primOpTy_wf (rigidCount := 0) hty).2

/-! ## Realizing the store under extended valuations -/

private theorem Ty.realize_congr {ty : Ty} {first second : MValuation}
    (agree : ∀ id ∈ ty.mvars, first id = second id) :
    ty.realize first = ty.realize second := by
  induction ty with
  | prim name => rfl
  | arrow domain codomain ihDomain ihCodomain =>
      simp only [Ty.realize]
      rw [ihDomain (fun id member => agree id (by simp [Ty.mvars, member])),
        ihCodomain (fun id member => agree id (by simp [Ty.mvars, member]))]
  | bvar index => rfl
  | rigid level => rfl
  | mvar id => simpa [Ty.realize] using agree id (by simp [Ty.mvars])
  | con id => rfl
  | app function argument ihFunction ihArgument =>
      simp only [Ty.realize]
      rw [ihFunction (fun id member => agree id (by simp [Ty.mvars, member])),
        ihArgument (fun id member => agree id (by simp [Ty.mvars, member]))]

private theorem Ty.WF.arrow_parts {domain codomain : Ty} {rigidCount binderCount : Nat}
    (wf : (Ty.arrow domain codomain).WF rigidCount binderCount) :
    domain.WF rigidCount binderCount ∧ codomain.WF rigidCount binderCount := by
  rcases wf with ⟨hscoped, hfree⟩
  cases hscoped with
  | arrow domainScoped codomainScoped =>
      cases hfree with
      | arrow domainFree codomainFree =>
          exact ⟨⟨domainScoped, domainFree⟩, ⟨codomainScoped, codomainFree⟩⟩

private theorem Ty.WF.app_parts {function argument : Ty} {rigidCount binderCount : Nat}
    (wf : (Ty.app function argument).WF rigidCount binderCount) :
    function.WF rigidCount binderCount ∧ argument.WF rigidCount binderCount := by
  rcases wf with ⟨hscoped, hfree⟩
  cases hscoped with
  | app functionScoped argumentScoped =>
      cases hfree with
      | app functionFree argumentFree =>
          exact ⟨⟨functionScoped, functionFree⟩,
            ⟨argumentScoped, argumentFree⟩⟩

private theorem Ty.WF.mono_rigid {ty : Ty} {rigid rigid' binder : Nat}
    (wf : ty.WF rigid binder) (le : rigid ≤ rigid') : ty.WF rigid' binder := by
  have scopedMono : ∀ {candidate : Ty}, candidate.Scoped rigid binder →
      candidate.Scoped rigid' binder := by
    intro candidate h
    induction h with
    | prim => exact .prim
    | arrow _ _ ihDomain ihCodomain => exact .arrow ihDomain ihCodomain
    | bvar hlt => exact .bvar hlt
    | rigid hlt => exact .rigid (lt_of_lt_of_le hlt le)
    | mvar id => exact .mvar id
    | con id => exact .con id
    | app _ _ ihFunction ihArgument => exact .app ihFunction ihArgument
  exact ⟨scopedMono wf.1, wf.2⟩

private theorem MStore.lookup_append_new_none {store extra : MStore} {id : Nat}
    (ge : store.length ≤ id)
    (unsolved : ∀ entry ∈ extra, entry.solution = none) :
    (store ++ extra).lookup id = none := by
  unfold MStore.lookup
  rw [List.getElem?_append_right ge]
  cases hget : extra[id - store.length]? with
  | none => rfl
  | some entry =>
      have member : entry ∈ extra := List.mem_of_getElem? hget
      simp only [hget, Option.bind]
      rw [unsolved entry member]

private theorem MStore.lookup_append_old {store extra : MStore} {id : Nat}
    (lt : id < store.length) :
    (store ++ extra).lookup id = store.lookup id := by
  unfold MStore.lookup
  rw [List.getElem?_append_left lt]

/-- Append unsolved entries to a modelled store, provided the new valuation
agrees on the old part and is well-formed on the new entries. -/
private theorem MStore.Models.append_unsolved
    {store extra : MStore} {valuation updated : MValuation}
    (models : store.Models valuation)
    (bounded : store.Bounded store.length)
    (unsolved : ∀ entry ∈ extra, entry.solution = none)
    (agree : ∀ id, id < store.length → updated id = valuation id)
    (wfExtra : ∀ (id : Nat) (entry : MEntry), store.length ≤ id →
      extra[id - store.length]? = some entry → (updated id).WF entry.level 0) :
    (store ++ extra).Models updated := by
  constructor
  · intro id entry hget
    by_cases hid : id < store.length
    · have oldGet : store[id]? = some entry := by
        rw [List.getElem?_append_left hid] at hget
        exact hget
      have oldWF := models.valuationWF id entry oldGet
      rw [agree id hid]
      exact oldWF
    · have ge : store.length ≤ id := by omega
      rw [List.getElem?_append_right ge] at hget
      exact wfExtra id entry ge hget
  · intro id ty hlookup
    by_cases hid : id < store.length
    · have oldLookup : store.lookup id = some ty := by
        rw [MStore.lookup_append_old hid] at hlookup
        exact hlookup
      have equation := models.equation id ty oldLookup
      have boundedTy : ty.MVarBounded store.length := bounded id ty oldLookup
      have realizeEq : ty.realize updated = ty.realize valuation :=
        Ty.realize_congr (fun m member => agree m (boundedTy m member))
      rw [agree id hid, equation, realizeEq]
    · have ge : store.length ≤ id := by omega
      have noneLookup := MStore.lookup_append_new_none ge unsolved
      rw [noneLookup] at hlookup
      exact Option.noConfusion hlookup

/-- Interpreting a fresh metavariable at an arbitrary well-formed type. -/
private theorem InferState.fresh_models
    {state : InferState} {valuation : MValuation} {level : Nat}
    (safe : state.Safe) (models : state.Models valuation) {ty : Ty}
    (wf : ty.WF level 0) :
    (state.fresh level).1.Models
        (fun id => if id = state.next then ty else valuation id) ∧
      (∀ id, id < state.next →
        (fun id => if id = state.next then ty else valuation id) id =
          valuation id) := by
  rcases safe with ⟨length, leveled, bounded, normalized⟩
  simp only [InferState.fresh]
  have boundedLength : state.solutions.Bounded state.solutions.length := by
    simpa [length] using bounded
  have unsolvedNew : ∀ entry ∈ ([(⟨level, none⟩ : MEntry)] : MStore),
      entry.solution = none := by
    intro entry member
    simp only [List.mem_singleton] at member
    subst member
    rfl
  refine ⟨MStore.Models.append_unsolved models boundedLength unsolvedNew ?_ ?_, ?_⟩
  · intro id hid
    split_ifs with same
    · exact absurd same (by omega)
    · rfl
  · intro id entry ge hget
    have idEq : id = state.next := by
      have jlt : id - state.solutions.length < 1 := by
        by_contra hge
        have noneEq : ([(⟨level, none⟩ : MEntry)] : MStore)[id - state.solutions.length]? = none :=
          List.getElem?_eq_none_iff.mpr (by
            have := Nat.le_of_not_lt hge
            simpa using this)
        rw [noneEq] at hget
        exact Option.noConfusion hget
      have lengthEq : state.solutions.length = state.next := length
      omega
    subst idEq
    have hget' : ([((⟨level, none⟩ : MEntry))] : MStore)[0]? = some entry := by
      have hzero : state.next - state.solutions.length = 0 := by
        rw [length]
        omega
      rwa [hzero] at hget
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hget'
    subst entry
    simpa using wf
  · intro id hid
    rw [if_neg (Nat.ne_of_lt hid)]

/-- Interpreting the metavariables freshly allocated by `freshMany` according
to a list of semantic types of matching length. -/
private theorem InferState.freshMany_models
    {state : InferState} {valuation : MValuation} {level count : Nat}
    (safe : state.Safe) (models : state.Models valuation)
    (assigned : List Ty) (length : assigned.length = count)
    (wf : ∀ ty ∈ assigned, ty.WF level 0) :
    ∃ updated,
      (state.freshMany level count).1.Models updated ∧
        (∀ id, id < state.next → updated id = valuation id) ∧
        (state.freshMany level count).2.map (·.realize updated) = assigned := by
  induction count generalizing state valuation assigned with
  | zero =>
      have assignedNil : assigned = [] := List.eq_nil_of_length_eq_zero length
      subst assignedNil
      refine ⟨valuation, ?_, ?_, ?_⟩
      · simpa [InferState.freshMany] using models
      · intro id hid
        rfl
      · rfl
  | succ count ih =>
      cases assigned with
      | nil => simp at length
      | cons head tail =>
          have tailLength : tail.length = count := by simpa using length
          have headWF : head.WF level 0 := wf head (by simp)
          have tailWF : ∀ ty ∈ tail, ty.WF level 0 := by
            intro ty member
            exact wf ty (by simp [member])
          have firstSafe := InferState.fresh_safe (level := level) safe
          let firstValuation : MValuation :=
            fun id => if id = state.next then head else valuation id
          have firstModels : (state.fresh level).1.Models firstValuation :=
            (InferState.fresh_models safe models headWF).1
          have newLt : state.next < (state.fresh level).1.next := by
            simp [InferState.fresh]
          obtain ⟨restUpdated, restModels, restAgree, restMap⟩ :=
            ih firstSafe.1 firstModels (assigned := tail) tailLength tailWF
          have sameNew : restUpdated state.next = head := by
            rw [restAgree state.next newLt]
            simp [firstValuation]
          refine ⟨restUpdated, ?_, ?_, ?_⟩
          · simpa [InferState.freshMany] using restModels
          · intro id hid
            rw [restAgree id (lt_of_lt_of_le hid (le_of_lt newLt))]
            simp [firstValuation, Nat.ne_of_lt hid]
          · simp only [InferState.freshMany, List.map_cons]
            have headRealize : (state.fresh level).2.realize restUpdated = head := by
              simp only [InferState.fresh, Ty.realize]
              exact sameNew
            rw [headRealize, restMap]

/-- Extending a model through `allocate`: every newly allocated metavariable
is interpreted by `assigned` when it occurs in the allocated type and by `Unit`
otherwise. -/
private theorem InferState.allocate_models
    {state : InferState} {valuation : MValuation} {level : Nat}
    (safe : state.Safe) (models : state.Models valuation)
    {template : Template} (templateScoped : template.Scoped level 0)
    {assigned : Nat → Ty}
    (wfAssigned : ∀ id ∈ (state.allocate level template).2.mvars,
      (assigned id).WF level 0) :
    ∃ updated,
      (state.allocate level template).1.Models updated ∧
        (∀ id, id < state.next → updated id = valuation id) ∧
        (state.allocate level template).2.realize updated =
          (state.allocate level template).2.realize assigned := by
  rcases safe with ⟨length, leveled, bounded, normalized⟩
  simp only [InferState.allocate]
  let allocation := template.allocate state.next
  let count := allocation.next - state.next
  let updated : MValuation := fun id =>
    if id < state.next then valuation id
    else if id ∈ allocation.ty.mvars then assigned id else .prim .unit
  have allocationNext : state.next ≤ allocation.next :=
    Template.allocate_next_le template state.next
  have countEq : state.next + count = allocation.next := by
    simp only [count]
    omega
  have lengthEq : state.solutions.length = state.next := length
  have boundedLength : state.solutions.Bounded state.solutions.length := by
    simpa [lengthEq] using bounded
  have unsolvedNew : ∀ entry ∈ List.replicate count (⟨level, none⟩ : MEntry),
      entry.solution = none := by
    intro entry member
    rw [List.eq_of_mem_replicate member]
  have mvarsBounds := Template.allocate_mvars templateScoped
    (frontier := state.next)
  have agree : ∀ id, id < state.solutions.length → updated id = valuation id := by
    intro id hid
    have hid' : id < state.next := by simpa [lengthEq] using hid
    simp [updated, hid']
  have wfExtra : ∀ (id : Nat) (entry : MEntry),
      state.solutions.length ≤ id →
        (List.replicate count (⟨level, none⟩ : MEntry))[id - state.solutions.length]? =
          some entry → (updated id).WF entry.level 0 := by
    intro id entry ge hget
    have indexLt : id - state.solutions.length <
        (List.replicate count (⟨level, none⟩ : MEntry)).length :=
      (List.getElem?_eq_some_iff.mp hget).1
    have mem : entry ∈ List.replicate count (⟨level, none⟩ : MEntry) :=
      List.mem_of_getElem? hget
    have entryEq : entry = (⟨level, none⟩ : MEntry) :=
      List.eq_of_mem_replicate mem
    subst entryEq
    have idLtAllocation : id < allocation.next := by
      have hlen : (List.replicate count (⟨level, none⟩ : MEntry)).length = count :=
        List.length_replicate
      have : id - state.next < count := by
        rw [lengthEq] at indexLt
        simpa [hlen] using indexLt
      omega
    by_cases memberTy : id ∈ allocation.ty.mvars
    · have notLt : ¬ id < state.next := by
        have := (mvarsBounds id memberTy).1
        omega
      have wf := wfAssigned id (by simpa [allocation, InferState.allocate] using memberTy)
      simpa [updated, memberTy, notLt] using wf
    · have notLt : ¬ id < state.next := by
        rw [lengthEq] at ge
        omega
      have unitWF : (Ty.prim .unit).WF level 0 := ⟨.prim, .prim⟩
      simpa [updated, memberTy, notLt] using unitWF
  have newModels : (state.solutions ++ List.replicate count (⟨level, none⟩ : MEntry)).Models updated :=
    MStore.Models.append_unsolved models boundedLength unsolvedNew agree wfExtra
  refine ⟨updated, ?_, ?_, ?_⟩
  · simpa [allocation, count] using newModels
  · intro id hid
    simp [updated, hid]
  · apply Ty.realize_congr
    intro id member
    have memberAllocation : id ∈ allocation.ty.mvars := by
      simpa [allocation, InferState.allocate] using member
    have baseLe : state.next ≤ id := (mvarsBounds id member).1
    have notLt : ¬ id < state.next := by omega
    simp [updated, notLt, memberAllocation]

private theorem Ty.MetaFree.mvars_eq_nil {ty : Ty} (free : ty.MetaFree) :
    ty.mvars = [] := by
  induction free with
  | prim => rfl
  | arrow _ _ ihDomain ihCodomain =>
      simp [Ty.mvars, ihDomain, ihCodomain]
  | bvar => rfl
  | rigid => rfl
  | con => rfl
  | app _ _ ihFunction ihArgument =>
      simp [Ty.mvars, ihFunction, ihArgument]

private theorem List.lookup_deterministic {entries : List (String × Ty)}
    {name : String} {first second : Ty}
    (hfirst : entries.lookup name = some first)
    (hsecond : entries.lookup name = some second) : first = second := by
  rw [hfirst] at hsecond
  exact Option.some.inj hsecond

private def HoleAssignment.openRigidsFrom (holes : HoleAssignment)
    (depth base count : Nat) : HoleAssignment :=
  holes.map fun entry => (entry.1, entry.2.openRigidsFrom depth base count)

private theorem HoleAssignment.openRigidsFrom_lookup (holes : HoleAssignment)
    (name : String) (depth base count : Nat) :
    (holes.openRigidsFrom depth base count).lookup name =
      (holes.lookup name).map (·.openRigidsFrom depth base count) := by
  induction holes with
  | nil => rfl
  | cons entry rest ih =>
      rcases entry with ⟨key, value⟩
      simp only [HoleAssignment.openRigidsFrom, List.map_cons, List.lookup]
      split
      · rfl
      · simpa [HoleAssignment.openRigidsFrom] using ih

private theorem HoleAssignment.unique_openRigidsFrom {holes : HoleAssignment}
    (unique : holes.Unique) (depth base count : Nat) :
    (holes.openRigidsFrom depth base count).Unique := by
  simpa [HoleAssignment.Unique, HoleAssignment.openRigidsFrom, List.map_map,
    Function.comp_def] using unique

private theorem Template.Fits.names_lookup
    {template : Template} {holes : HoleAssignment} {target : Ty}
    (fits : template.Fits holes target) :
    ∀ name ∈ template.names, ∃ ty, holes.lookup name = some ty := by
  induction template generalizing target with
  | fixed ty =>
      cases fits
      intro name member
      simp [Template.names] at member
  | hole =>
      cases fits
      intro name member
      simp [Template.names] at member
  | named name =>
      cases fits with
      | named hlookup =>
          intro other member
          simp only [Template.names, List.mem_singleton] at member
          subst member
          exact ⟨_, hlookup⟩
  | arrow domain codomain ihDomain ihCodomain =>
      cases fits with
      | arrow domainFit codomainFit =>
          intro name member
          simp only [Template.names, List.mem_append] at member
          rcases member with member | member
          · exact ihDomain domainFit name member
          · exact ihCodomain codomainFit name member
  | app function argument ihFunction ihArgument =>
      cases fits with
      | app functionFit argumentFit =>
          intro name member
          simp only [Template.names, List.mem_append] at member
          rcases member with member | member
          · exact ihFunction functionFit name member
          · exact ihArgument argumentFit name member

private theorem Template.Fits.lookup_wf
    {template : Template} {holes : HoleAssignment} {target : Ty}
    (fits : template.Fits holes target) {rigid : Nat}
    (targetWF : target.WF rigid 0) :
    ∀ name ∈ template.names, ∀ ty, holes.lookup name = some ty → ty.WF rigid 0 := by
  induction template generalizing target with
  | fixed ty =>
      cases fits
      intro name member
      simp [Template.names] at member
  | hole =>
      cases fits
      intro name member
      simp [Template.names] at member
  | named name =>
      cases fits with
      | named hlookup =>
          intro other member ty lookup
          simp only [Template.names, List.mem_singleton] at member
          subst member
          have same : ty = target := List.lookup_deterministic lookup hlookup
          rw [same]
          exact targetWF
  | arrow domain codomain ihDomain ihCodomain =>
      cases fits with
      | arrow domainFit codomainFit =>
          obtain ⟨domainWF, codomainWF⟩ := Ty.WF.arrow_parts targetWF
          intro name member ty lookup
          simp only [Template.names, List.mem_append] at member
          rcases member with member | member
          · exact ihDomain domainFit domainWF name member ty lookup
          · exact ihCodomain codomainFit codomainWF name member ty lookup
  | app function argument ihFunction ihArgument =>
      cases fits with
      | app functionFit argumentFit =>
          obtain ⟨functionWF, argumentWF⟩ := Ty.WF.app_parts targetWF
          intro name member ty lookup
          simp only [Template.names, List.mem_append] at member
          rcases member with member | member
          · exact ihFunction functionFit functionWF name member ty lookup
          · exact ihArgument argumentFit argumentWF name member ty lookup

private theorem Template.Fits.openRigidsFrom
    {template : Template} {holes : HoleAssignment} {target : Ty}
    (fits : template.Fits holes target) (depth base count : Nat) :
    (template.openRigidsFrom depth base count).Fits
      (holes.openRigidsFrom depth base count)
      (target.openRigidsFrom depth base count) := by
  induction template generalizing target with
  | fixed ty =>
      cases fits
      exact .fixed
  | hole =>
      cases fits
      exact .hole
  | named name =>
      cases fits with
      | named hlookup =>
          apply Template.Fits.named
          rw [HoleAssignment.openRigidsFrom_lookup, hlookup]
          rfl
  | arrow domain codomain ihDomain ihCodomain =>
      cases fits with
      | arrow domainFit codomainFit =>
          exact .arrow (ihDomain domainFit) (ihCodomain codomainFit)
  | app function argument ihFunction ihArgument =>
      cases fits with
      | app functionFit argumentFit =>
          exact .app (ihFunction functionFit) (ihArgument argumentFit)

private theorem Template.Matches.openRigidsFrom
    {template : Template} {target : Ty}
    (hmatches : template.Matches target) (depth base count : Nat) :
    (template.openRigidsFrom depth base count).Matches
      (target.openRigidsFrom depth base count) := by
  rcases hmatches with ⟨holes, unique, fits⟩
  exact ⟨holes.openRigidsFrom depth base count,
    HoleAssignment.unique_openRigidsFrom unique depth base count,
    fits.openRigidsFrom depth base count⟩

private theorem Template.allocateWith_next_le
    (template : Template) (holes : HoleAssignment) (start : Nat) :
    start ≤ (template.allocateWith holes start).1 := by
  induction template generalizing start with
  | fixed ty => simp [Template.allocateWith]
  | hole => simp [Template.allocateWith]
  | named name => simp [Template.allocateWith]
  | arrow domain codomain ihDomain ihCodomain =>
      simp only [Template.allocateWith]
      exact le_trans (ihDomain start)
        (ihCodomain (domain.allocateWith holes start).1)
  | app function argument ihFunction ihArgument =>
      simp only [Template.allocateWith]
      exact le_trans (ihFunction start)
        (ihArgument (function.allocateWith holes start).1)

/-- Realizing an allocated template at a target type it fits. Named holes use
their values from the fitting assignment; anonymous holes take the target
subterm at their occurrence. -/
private theorem Template.allocateWith_realizes
    {template : Template} {rigid binder : Nat} {target : Ty}
    {assign holes : HoleAssignment} {base : MValuation}
    (fits : template.Fits assign target)
    (templateScoped : template.Scoped rigid binder)
    (targetWF : target.WF rigid 0)
    (holesMvar : ∀ name ty, holes.lookup name = some ty → ∃ id, ty = .mvar id)
    (holesCover : ∀ name ∈ template.names, ∃ ty, holes.lookup name = some ty)
    (start : Nat)
    (holesBefore : ∀ (name : String) (ty : Ty) (id : Nat),
      holes.lookup name = some (.mvar id) → id < start)
    (namedValue : ∀ (name : String) (ty : Ty) (id : Nat),
      holes.lookup name = some (.mvar id) → assign.lookup name = some ty →
        base id = ty ∧ (base id).WF rigid 0) :
    ∃ updated,
      (∀ id, id < start → updated id = base id) ∧
      (template.allocateWith holes start).2.realize updated = target ∧
      (∀ id ∈ (template.allocateWith holes start).2.mvars,
        (updated id).WF rigid 0) ∧
      (∀ id ∈ (template.allocateWith holes start).2.mvars,
        id < (template.allocateWith holes start).1) := by
  induction template generalizing target start base with
  | fixed ty =>
      cases fits
      cases templateScoped with
      | fixed wf =>
          refine ⟨base, ?_, ?_, ?_, ?_⟩
          · intro id hid; rfl
          · simp only [Template.allocateWith]
            exact Ty.realize_eq_self wf.2 base
          · intro id member
            have empty := Ty.MetaFree.mvars_eq_nil wf.2
            simp [Template.allocateWith, empty] at member
          · intro id member
            have empty := Ty.MetaFree.mvars_eq_nil wf.2
            simp [Template.allocateWith, empty] at member
  | hole =>
      cases fits
      let updated : MValuation := fun id => if id = start then target else base id
      refine ⟨updated, ?_, ?_, ?_, ?_⟩
      · intro id hid
        change (if id = start then target else base id) = base id
        rw [if_neg (Nat.ne_of_lt hid)]
      · simp only [Template.allocateWith, Ty.realize]
        simp [updated]
      · intro id member
        simp only [Template.allocateWith, Ty.mvars, List.mem_singleton] at member
        subst member
        simpa [updated] using targetWF
      · intro id member
        simp only [Template.allocateWith, Ty.mvars, List.mem_singleton] at member
        subst member
        simp [Template.allocateWith]
  | named name =>
      cases fits with
      | named hlookup =>
          obtain ⟨lookupTy, holeLookup⟩ := holesCover name (by simp [Template.names])
          obtain ⟨holeId, idEq⟩ := holesMvar name lookupTy holeLookup
          have holeLookup' : holes.lookup name = some (.mvar holeId) := by
            rw [idEq] at holeLookup
            exact holeLookup
          obtain ⟨valueEq, valueWF⟩ :=
            namedValue name target holeId holeLookup' hlookup
          refine ⟨base, ?_, ?_, ?_, ?_⟩
          · intro other hother; rfl
          · simp only [Template.allocateWith, holeLookup', Option.getD_some]
            exact valueEq
          · intro other member
            simp only [Template.allocateWith, holeLookup', Option.getD_some,
              Ty.mvars, List.mem_singleton] at member
            have otherEq : other = holeId := by simpa using member
            subst otherEq
            exact valueWF
          · intro other member
            simp only [Template.allocateWith, holeLookup', Option.getD_some,
              Ty.mvars, List.mem_singleton] at member
            have hidBound : holeId < start :=
              holesBefore name target holeId holeLookup'
            have otherEq : other = holeId := by simpa using member
            subst otherEq
            exact hidBound
  | arrow domain codomain ihDomain ihCodomain =>
      cases fits with
      | arrow domainFit codomainFit =>
          cases templateScoped with
          | arrow domainScoped codomainScoped =>
              obtain ⟨domainTargetWF, codomainTargetWF⟩ :=
                Ty.WF.arrow_parts targetWF
              obtain ⟨domainUpdated, domainAgree, domainRealize, domainWFResult,
                domainBound⟩ := ihDomain domainFit domainScoped domainTargetWF
                  (by
                    intro name member
                    exact holesCover name (List.mem_append_left _ member))
                  start holesBefore namedValue
              let start' := (domain.allocateWith holes start).1
              have startLe : start ≤ start' := by
                simpa [start'] using Template.allocateWith_next_le domain holes start
              have namedValue' : ∀ (name : String) (ty : Ty) (id : Nat),
                  holes.lookup name = some (.mvar id) → assign.lookup name = some ty →
                    domainUpdated id = ty ∧ (domainUpdated id).WF rigid 0 := by
                intro name ty id holeLookup assignLookup
                obtain ⟨valueEq, valueWF⟩ :=
                  namedValue name ty id holeLookup assignLookup
                have idBefore : id < start := holesBefore name ty id holeLookup
                have agree := domainAgree id idBefore
                exact ⟨agree.trans valueEq, agree ▸ valueWF⟩
              have holesBefore' : ∀ (name : String) (ty : Ty) (id : Nat),
                  holes.lookup name = some (.mvar id) → id < start' := by
                intro name ty id holeLookup
                exact lt_of_lt_of_le (holesBefore name ty id holeLookup) startLe
              obtain ⟨updated, codomainAgree, codomainRealize, codomainWFResult,
                codomainBound⟩ := ihCodomain (base := domainUpdated)
                  codomainFit codomainScoped codomainTargetWF
                  (by
                    intro name member
                    exact holesCover name (List.mem_append_right _ member))
                  start' holesBefore' namedValue'
              refine ⟨updated, ?_, ?_, ?_, ?_⟩
              · intro id hid
                have idStart' : id < start' := lt_of_lt_of_le hid startLe
                exact (codomainAgree id idStart').trans (domainAgree id hid)
              · simp only [Template.allocateWith, Ty.realize]
                rw [Ty.realize_congr (first := updated) (second := domainUpdated)
                  (ty := (domain.allocateWith holes start).2)]
                · rw [domainRealize, codomainRealize]
                · intro id member
                  exact codomainAgree id (domainBound id member)
              · intro id member
                simp only [Template.allocateWith, Ty.mvars, List.mem_dedup,
                  List.mem_append] at member
                rcases member with member | member
                · have idBefore : id < start' := domainBound id member
                  rw [codomainAgree id idBefore]
                  exact domainWFResult id member
                · exact codomainWFResult id member
              · intro id member
                simp only [Template.allocateWith, Ty.mvars, List.mem_dedup,
                  List.mem_append] at member
                rcases member with member | member
                · exact lt_of_lt_of_le (domainBound id member)
                    (by simpa [start'] using
                      Template.allocateWith_next_le codomain holes start')
                · exact codomainBound id member
  | app function argument ihFunction ihArgument =>
      cases fits with
      | app functionFit argumentFit =>
          cases templateScoped with
          | app functionScoped argumentScoped =>
              obtain ⟨functionTargetWF, argumentTargetWF⟩ :=
                Ty.WF.app_parts targetWF
              obtain ⟨functionUpdated, functionAgree, functionRealize, functionWFResult,
                functionBound⟩ := ihFunction functionFit functionScoped functionTargetWF
                  (by
                    intro name member
                    exact holesCover name (List.mem_append_left _ member))
                  start holesBefore namedValue
              let start' := (function.allocateWith holes start).1
              have startLe : start ≤ start' := by
                simpa [start'] using Template.allocateWith_next_le function holes start
              have namedValue' : ∀ (name : String) (ty : Ty) (id : Nat),
                  holes.lookup name = some (.mvar id) → assign.lookup name = some ty →
                    functionUpdated id = ty ∧ (functionUpdated id).WF rigid 0 := by
                intro name ty id holeLookup assignLookup
                obtain ⟨valueEq, valueWF⟩ :=
                  namedValue name ty id holeLookup assignLookup
                have idBefore : id < start := holesBefore name ty id holeLookup
                have agree := functionAgree id idBefore
                exact ⟨agree.trans valueEq, agree ▸ valueWF⟩
              have holesBefore' : ∀ (name : String) (ty : Ty) (id : Nat),
                  holes.lookup name = some (.mvar id) → id < start' := by
                intro name ty id holeLookup
                exact lt_of_lt_of_le (holesBefore name ty id holeLookup) startLe
              obtain ⟨updated, argumentAgree, argumentRealize, argumentWFResult,
                argumentBound⟩ := ihArgument (base := functionUpdated)
                  argumentFit argumentScoped argumentTargetWF
                  (by
                    intro name member
                    exact holesCover name (List.mem_append_right _ member))
                  start' holesBefore' namedValue'
              refine ⟨updated, ?_, ?_, ?_, ?_⟩
              · intro id hid
                have idStart' : id < start' := lt_of_lt_of_le hid startLe
                exact (argumentAgree id idStart').trans (functionAgree id hid)
              · simp only [Template.allocateWith, Ty.realize]
                rw [Ty.realize_congr (first := updated) (second := functionUpdated)
                  (ty := (function.allocateWith holes start).2)]
                · rw [functionRealize, argumentRealize]
                · intro id member
                  exact argumentAgree id (functionBound id member)
              · intro id member
                simp only [Template.allocateWith, Ty.mvars, List.mem_dedup,
                  List.mem_append] at member
                rcases member with member | member
                · have idBefore : id < start' := functionBound id member
                  rw [argumentAgree id idBefore]
                  exact functionWFResult id member
                · exact argumentWFResult id member
              · intro id member
                simp only [Template.allocateWith, Ty.mvars, List.mem_dedup,
                  List.mem_append] at member
                rcases member with member | member
                · exact lt_of_lt_of_le (functionBound id member)
                    (by simpa [start'] using
                      Template.allocateWith_next_le argument holes start')
                · exact argumentBound id member

private theorem namedHoleTable_lookup_mvar {names : List String} {frontier : Nat}
    {name : String} {id : Nat}
    (hlookup : (namedHoleTable names frontier).lookup name = some (.mvar id)) :
    ∃ k, k < (names.dedup).length ∧ (names.dedup)[k]? = some name ∧
      id = frontier + k := by
  let keys := names.dedup
  have hzip : (keys.zip ((List.range keys.length).map
      fun k => Ty.mvar (frontier + k))).lookup name = some (.mvar id) := by
    simpa [namedHoleTable, keys] using hlookup
  have pairMem : (name, Ty.mvar id) ∈
      keys.zip ((List.range keys.length).map fun k => Ty.mvar (frontier + k)) := by
    rcases List.lookup_eq_some_iff.mp hzip with ⟨first, second, heq, _⟩
    rw [heq]
    simp
  obtain ⟨k, hk⟩ := List.getElem?_of_mem pairMem
  obtain ⟨keysGet, valuesGet⟩ := List.getElem?_zip_eq_some.mp hk
  rw [List.getElem?_map] at valuesGet
  rcases Option.map_eq_some_iff.mp valuesGet with ⟨value, valueGet, valueEq⟩
  obtain ⟨hkLen, hvalue⟩ := List.getElem?_eq_some_iff.mp valueGet
  have valueEqId : Ty.mvar (frontier + value) = Ty.mvar id := by
    simpa using valueEq
  have valueEq' : Ty.mvar (frontier + k) = Ty.mvar id := by
    rw [← valueEqId]
    congr 1
    rw [← hvalue]
    simp [List.getElem_range]
  have idEq : id = frontier + k := by
    injection valueEq' with same
    exact same.symm
  exact ⟨k, by simpa using hkLen, by simpa using keysGet, idEq⟩

private theorem namedHoleTable_mvar {names : List String} {frontier : Nat} :
    ∀ name ty, (namedHoleTable names frontier).lookup name = some ty →
      ∃ id, ty = .mvar id := by
  intro name ty hlookup
  let keys := names.dedup
  have hzip : (keys.zip ((List.range keys.length).map
      fun k => Ty.mvar (frontier + k))).lookup name = some ty := by
    simpa [namedHoleTable, keys] using hlookup
  rcases List.lookup_eq_some_iff.mp hzip with ⟨first, second, heq, _⟩
  have pairMem : (name, ty) ∈
      keys.zip ((List.range keys.length).map fun k => Ty.mvar (frontier + k)) := by
    rw [heq]
    simp
  obtain ⟨_, valueMem⟩ := List.of_mem_zip pairMem
  rcases List.mem_map.mp valueMem with ⟨k, _, valueEq⟩
  exact ⟨frontier + k, valueEq.symm⟩

private theorem namedHoleTable_covers {names : List String} {frontier : Nat}
    {name : String} (member : name ∈ names) :
    ∃ ty, (namedHoleTable names frontier).lookup name = some ty := by
  let keys := names.dedup
  have keyMem : name ∈ keys := List.mem_dedup.mpr member
  obtain ⟨k, keysGet⟩ := List.mem_iff_getElem?.mp keyMem
  have valuesGet : ((List.range keys.length).map
      fun j => Ty.mvar (frontier + j))[k]? = some (Ty.mvar (frontier + k)) := by
    rw [List.getElem?_map]
    rcases List.getElem?_eq_some_iff.mp keysGet with ⟨hkLen, _⟩
    simp [List.getElem?_range hkLen]
  have pairGet : (keys.zip ((List.range keys.length).map
      fun j => Ty.mvar (frontier + j)))[k]? =
      some (name, Ty.mvar (frontier + k)) := by
    rw [List.getElem?_zip_eq_some]
    exact ⟨keysGet, valuesGet⟩
  have someLookup : ((keys.zip ((List.range keys.length).map
      fun j => Ty.mvar (frontier + j))).lookup name).isSome := by
    apply List.lookup_isSome_iff.mpr
    refine ⟨(name, Ty.mvar (frontier + k)), List.mem_of_getElem? pairGet, ?_⟩
    simp
  obtain ⟨ty, lookupEq⟩ := Option.isSome_iff_exists.mp someLookup
  exact ⟨ty, by simpa [namedHoleTable, keys] using lookupEq⟩

/-- Realizing an allocated template at a matching target type. -/
private theorem Template.allocate_realizes
    {template : Template} {rigid binder frontier : Nat} {target : Ty}
    {base : MValuation}
    (hmatches : template.Matches target)
    (templateScoped : template.Scoped rigid binder)
    (targetWF : target.WF rigid 0) :
    ∃ holeVal : MValuation,
      (∀ id, id < frontier → holeVal id = base id) ∧
      (template.allocate frontier).ty.realize holeVal = target ∧
      (∀ id ∈ (template.allocate frontier).ty.mvars, (holeVal id).WF rigid 0) := by
  rcases hmatches with ⟨assign, unique, fits⟩
  let keys := template.names.dedup
  let holes := namedHoleTable keys frontier
  let start := frontier + keys.length
  have keyNodup : keys.Nodup := by
    simp only [keys]
    exact List.nodup_dedup _
  have keysDedup : keys.dedup = keys := List.dedup_eq_self.mpr keyNodup
  let namedValueOf : String → Ty := fun name =>
    (assign.lookup name).getD (.prim .unit)
  let namedBase : MValuation := fun id =>
    if id < frontier then base id
    else ((keys[id - frontier]?).map namedValueOf).getD (.prim .unit)
  have holesMvar : ∀ name ty, holes.lookup name = some ty → ∃ id, ty = .mvar id := by
    intro name ty lookup
    exact namedHoleTable_mvar (names := keys) (frontier := frontier) name ty
      (by simpa [holes] using lookup)
  have holesCover : ∀ name ∈ template.names, ∃ ty, holes.lookup name = some ty := by
    intro name member
    exact namedHoleTable_covers (names := keys) (frontier := frontier)
      (by simpa [keys] using List.mem_dedup.mpr member)
  have holesBefore : ∀ (name : String) (ty : Ty) (id : Nat),
      holes.lookup name = some (.mvar id) → id < start := by
    intro name ty id lookup
    obtain ⟨k, hkLen, _, idEq⟩ := namedHoleTable_lookup_mvar
      (names := keys) (frontier := frontier) (by simpa [holes] using lookup)
    have hkLen' : k < keys.length := by simpa [keysDedup] using hkLen
    rw [idEq]
    simp only [start]
    omega
  have namedValueSpec : ∀ (name : String) (ty : Ty) (id : Nat),
      holes.lookup name = some (.mvar id) → assign.lookup name = some ty →
        namedBase id = ty ∧ (namedBase id).WF rigid 0 := by
    intro name ty id lookup assignLookup
    obtain ⟨k, hkLen, keysGet, idEq⟩ := namedHoleTable_lookup_mvar
      (names := keys) (frontier := frontier) (by simpa [holes] using lookup)
    have hkLen' : k < keys.length := by simpa [keysDedup] using hkLen
    have keysGet' : keys[k]? = some name := by
      simpa [keysDedup] using keysGet
    have notLt : ¬ id < frontier := by omega
    have indexEq : id - frontier = k := by omega
    have valueEq : namedBase id = ty := by
      simp only [namedBase]
      rw [if_neg notLt, indexEq, keysGet']
      simp [namedValueOf, assignLookup]
    have nameMember : name ∈ template.names := by
      have : name ∈ keys := List.mem_of_getElem? keysGet'
      simpa [keys] using List.mem_dedup.mp this
    have valueWF := fits.lookup_wf targetWF name nameMember ty assignLookup
    exact ⟨valueEq, valueEq ▸ valueWF⟩
  obtain ⟨holeVal, agree, realize, wfResult, _⟩ :=
    Template.allocateWith_realizes fits templateScoped targetWF holesMvar
      holesCover start holesBefore namedValueSpec
  refine ⟨holeVal, ?_, ?_, ?_⟩
  · intro id hid
    exact (agree id (by simp only [start]; omega)).trans (by
      simp only [namedBase]
      rw [if_pos hid])
  · simpa [Template.allocate, keys, holes, start] using realize
  · simpa [Template.allocate, keys, holes, start] using wfResult

private theorem Ty.LevelBounded.mono_le {ty : Ty} {store store' : MStore} {level : Nat}
    (bounded : ty.LevelBounded store level)
    (le : ∀ id, store'.levelOf id ≤ store.levelOf id) :
    ty.LevelBounded store' level := by
  intro id member
  exact le_trans (le id) (bounded id member)

private theorem Ty.LevelBounded.mono_le_on
    {ty : Ty} {store store' : MStore} {level : Nat}
    (bounded : ty.LevelBounded store level)
    (le : ∀ id ∈ ty.mvars, store'.levelOf id ≤ store.levelOf id) :
    ty.LevelBounded store' level := by
  intro id member
  exact le_trans (le id member) (bounded id member)

private theorem Ty.openWith_scoped
    {ty : Ty} {rigidCount binderCount : Nat} {args : List Ty}
    (hscoped : ty.Scoped rigidCount binderCount)
    (hlen : args.length = binderCount)
    (hargs : ∀ arg ∈ args, arg.Scoped rigidCount 0) :
    (ty.openWith args).Scoped rigidCount 0 := by
  induction ty generalizing binderCount with
  | prim p => exact .prim
  | arrow domain codomain ihDomain ihCodomain =>
      cases hscoped with
      | arrow domainScoped codomainScoped =>
          exact .arrow (ihDomain domainScoped hlen)
            (ihCodomain codomainScoped hlen)
  | bvar index =>
      cases hscoped with
      | bvar hindex =>
          have hindex' : index < args.length := by simpa [hlen] using hindex
          have hget : args[index]? = some args[index] :=
            List.getElem?_eq_getElem hindex'
          simp only [Ty.openWith, hget, Option.getD_some]
          exact hargs args[index] (List.getElem_mem hindex')
  | rigid level =>
      cases hscoped with
      | rigid hlevel => exact .rigid hlevel
  | mvar id => exact .mvar id
  | con id =>
      cases hscoped with
      | con _ => exact .con id
  | app function argument ihFunction ihArgument =>
      cases hscoped with
      | app functionScoped argumentScoped =>
          exact .app (ihFunction functionScoped hlen)
            (ihArgument argumentScoped hlen)

private theorem Ty.openWith_metaFree
    {ty : Ty} {args : List Ty}
    (free : ty.MetaFree)
    (hargs : ∀ arg ∈ args, arg.MetaFree) :
    (ty.openWith args).MetaFree := by
  induction ty with
  | prim p => exact .prim
  | arrow domain codomain ihDomain ihCodomain =>
      cases free with
      | arrow domainFree codomainFree =>
          exact .arrow (ihDomain domainFree) (ihCodomain codomainFree)
  | bvar index =>
      simp only [Ty.openWith]
      cases hget : args[index]? with
      | none => exact .bvar
      | some arg =>
          exact hargs arg (List.mem_of_getElem? hget)
  | rigid level => exact .rigid
  | mvar id => cases free
  | con id => exact .con
  | app function argument ihFunction ihArgument =>
      cases free with
      | app functionFree argumentFree =>
          exact .app (ihFunction functionFree) (ihArgument argumentFree)

private theorem Ty.openWith_wf
    {ty : Ty} {rigidCount binderCount : Nat} {args : List Ty}
    (wf : ty.WF rigidCount binderCount)
    (hlen : args.length = binderCount)
    (hargs : ∀ arg ∈ args, arg.WF rigidCount 0) :
    (ty.openWith args).WF rigidCount 0 :=
  ⟨Ty.openWith_scoped wf.1 hlen (fun arg harg => (hargs arg harg).1),
    Ty.openWith_metaFree wf.2 (fun arg harg => (hargs arg harg).2)⟩

private theorem Ty.openWith_rigidBlock_eq_openRigidsFrom {ty : Ty}
    {rigid count : Nat} (hscoped : ty.Scoped rigid count) :
    ty.openWith (rigidBlock rigid count) = ty.openRigidsFrom 0 rigid count := by
  induction hscoped with
  | prim => rfl
  | arrow _ _ ihDomain ihCodomain =>
      simp only [Ty.openWith, Ty.openRigidsFrom, ihDomain, ihCodomain]
  | bvar hlt =>
      rename_i index
      have hget : (rigidBlock rigid count)[index]? = some (.rigid (rigid + index)) := by
        simp [rigidBlock, List.getElem?_map, List.getElem?_range hlt]
      simp only [Ty.openWith, Ty.openRigidsFrom, hget, Option.getD_some]
      simp [hlt]
  | rigid => rfl
  | mvar => rfl
  | con => rfl
  | app _ _ ihFunction ihArgument =>
      simp only [Ty.openWith, Ty.openRigidsFrom, ihFunction, ihArgument]

private theorem PolyTy.openRigids_eq_openRigidsFrom {scheme : PolyTy} {rigid : Nat}
    (wf : scheme.WF rigid) :
    scheme.openRigids rigid =
      scheme.body.openRigidsFrom 0 rigid scheme.paramCount := by
  unfold PolyTy.openRigids
  exact Ty.openWith_rigidBlock_eq_openRigidsFrom wf.1

private theorem PolyTy.openRigids_wf {scheme : PolyTy} {rigid : Nat}
    (wf : scheme.WF rigid) :
    (scheme.openRigids rigid).WF (rigid + scheme.paramCount) 0 := by
  unfold PolyTy.openRigids
  apply Ty.openWith_wf
    (rigidCount := rigid + scheme.paramCount) (binderCount := scheme.paramCount)
  · exact Ty.WF.mono_rigid wf (Nat.le_add_right rigid scheme.paramCount)
  · simp [rigidBlock]
  · intro arg member
    obtain ⟨offset, hoffset, rfl⟩ := List.mem_map.mp member
    exact ⟨.rigid (by
        have := List.mem_range.mp hoffset
        omega), .rigid⟩

private theorem Ty.InferWF.mono_frontier {ty : Ty} {rigidCount binder frontier frontier' : Nat}
    (wf : ty.InferWF rigidCount binder frontier) (le : frontier ≤ frontier') :
    ty.InferWF rigidCount binder frontier' :=
  ⟨wf.1, fun id member => lt_of_lt_of_le (wf.2 id member) le⟩

private theorem Ty.InferWF.mono_rigid {ty : Ty} {rigidCount rigidCount' binder frontier : Nat}
    (wf : ty.InferWF rigidCount binder frontier) (le : rigidCount ≤ rigidCount') :
    ty.InferWF rigidCount' binder frontier := by
  have scopedMono : ∀ {candidate : Ty}, candidate.Scoped rigidCount binder →
      candidate.Scoped rigidCount' binder := by
    intro candidate h
    induction h with
    | prim => exact .prim
    | arrow _ _ ihDomain ihCodomain => exact .arrow ihDomain ihCodomain
    | bvar hlt => exact .bvar hlt
    | rigid hlt => exact .rigid (lt_of_lt_of_le hlt le)
    | mvar id => exact .mvar id
    | con id => exact .con id
    | app _ _ ihFunction ihArgument => exact .app ihFunction ihArgument
  exact ⟨scopedMono wf.1, wf.2⟩

private theorem PolyTy.InferWF.mono_frontier {scheme : PolyTy}
    {rigidCount frontier frontier' : Nat}
    (wf : scheme.InferWF rigidCount frontier) (le : frontier ≤ frontier') :
    scheme.InferWF rigidCount frontier' :=
  Ty.InferWF.mono_frontier wf le

private theorem Ctx.InferWF.mono_frontier {context : Ctx}
    {rigidCount frontier frontier' : Nat}
    (wf : context.InferWF rigidCount frontier) (le : frontier ≤ frontier') :
    context.InferWF rigidCount frontier' := by
  intro scheme member
  exact PolyTy.InferWF.mono_frontier (wf scheme member) le

private theorem Ctx.InferWF.mono_rigid {context : Ctx}
    {rigidCount rigidCount' frontier : Nat}
    (wf : context.InferWF rigidCount frontier) (le : rigidCount ≤ rigidCount') :
    context.InferWF rigidCount' frontier := by
  intro scheme member
  exact Ty.InferWF.mono_rigid (wf scheme member) le

private theorem Ty.closeRigids_scoped_zero {ty : Ty} {base count : Nat}
    (typeScoped : ty.Scoped (base + count) 0) :
    (ty.closeRigids base count).Scoped base count := by
  induction typeScoped with
  | prim => exact .prim
  | arrow _ _ ihDomain ihCodomain =>
      exact .arrow ihDomain ihCodomain
  | bvar hlt => exact .bvar (by omega)
  | rigid hlt =>
      simp only [Ty.closeRigids]
      split
      next hbase => exact .rigid hbase
      next hbase =>
        split
        next hin => exact .bvar hin
        next hout => omega
  | mvar id => exact .mvar id
  | con id => exact .con id
  | app _ _ ihFunction ihArgument => exact .app ihFunction ihArgument

private theorem Ty.closeRigids_openRigids {ty : Ty} {base count : Nat}
    (typeScoped : ty.Scoped base count) :
    (ty.openRigidsFrom 0 base count).closeRigids base count = ty := by
  induction typeScoped with
  | prim => rfl
  | arrow _ _ ihDomain ihCodomain =>
      simp only [Ty.openRigidsFrom, Ty.closeRigids, ihDomain, ihCodomain]
  | bvar hlt =>
      simp [Ty.openRigidsFrom, Ty.closeRigids, hlt]
  | rigid hlt =>
      simp [Ty.openRigidsFrom, Ty.closeRigids, hlt]
  | mvar id => rfl
  | con id => rfl
  | app _ _ ihFunction ihArgument =>
      simp only [Ty.openRigidsFrom, Ty.closeRigids, ihFunction, ihArgument]

private theorem Ty.closeRigids_metaFree {ty : Ty} {base count : Nat}
    (free : ty.MetaFree) :
    (ty.closeRigids base count).MetaFree := by
  induction free with
  | prim => exact .prim
  | arrow _ _ ihDomain ihCodomain =>
      exact .arrow ihDomain ihCodomain
  | bvar => exact .bvar
  | rigid =>
      simp only [Ty.closeRigids]
      split
      · exact .rigid
      · split
        · exact .bvar
        · exact .rigid
  | con => exact .con
  | app _ _ ihFunction ihArgument => exact .app ihFunction ihArgument

private theorem Ty.mvars_closeRigids (ty : Ty) (base count : Nat) :
    (ty.closeRigids base count).mvars = ty.mvars := by
  induction ty with
  | prim name => rfl
  | arrow domain codomain ihDomain ihCodomain =>
      simp [Ty.closeRigids, Ty.mvars, ihDomain, ihCodomain]
  | bvar index => rfl
  | rigid level =>
      simp only [Ty.closeRigids]
      split
      · rfl
      · split <;> rfl
  | mvar id => rfl
  | con id => rfl
  | app function argument ihFunction ihArgument =>
      simp [Ty.closeRigids, Ty.mvars, ihFunction, ihArgument]

private theorem Ty.closeRigids_mvarBounded
    {ty : Ty} {base count frontier : Nat}
    (bounded : ty.MVarBounded frontier) :
    (ty.closeRigids base count).MVarBounded frontier := by
  intro id member
  rw [Ty.mvars_closeRigids] at member
  exact bounded id member

private theorem Ty.closeRigids_levelBounded
    {ty : Ty} {base count : Nat} {store : MStore} {level : Nat}
    (bounded : ty.LevelBounded store level) :
    (ty.closeRigids base count).LevelBounded store level := by
  intro id member
  rw [Ty.mvars_closeRigids] at member
  exact bounded id member

private theorem Ty.closeRigids_wf {ty : Ty} {base count : Nat}
    (wf : ty.WF (base + count) 0) :
    (ty.closeRigids base count).WF base count :=
  ⟨Ty.closeRigids_scoped_zero wf.1, Ty.closeRigids_metaFree wf.2⟩

private theorem PolyTy.realize_congr {scheme : PolyTy}
    {first second : MValuation}
    (agree : ∀ id ∈ scheme.body.mvars, first id = second id) :
    scheme.realize first = scheme.realize second := by
  cases scheme with
  | mk count body =>
      simpa [PolyTy.realize] using Ty.realize_congr agree

private theorem MStore.apply_mvarBounded {store : MStore} {ty : Ty} {frontier : Nat}
    (storeBounded : store.Bounded frontier)
    (typeBounded : ty.MVarBounded frontier) :
    (store.apply ty).MVarBounded frontier := by
  induction ty with
  | prim => exact typeBounded
  | arrow domain codomain ihDomain ihCodomain =>
      intro id member
      have split : id ∈ (store.apply domain).mvars ∨
          id ∈ (store.apply codomain).mvars := by
        simpa [MStore.apply, Ty.mvars, List.mem_dedup, List.mem_append] using member
      rcases split with inside | inside
      · exact ihDomain (fun m h => typeBounded m (by simp [Ty.mvars, h])) id inside
      · exact ihCodomain (fun m h => typeBounded m (by simp [Ty.mvars, h])) id inside
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
  | con id => exact typeBounded
  | app function argument ihFunction ihArgument =>
      intro id member
      have split : id ∈ (store.apply function).mvars ∨
          id ∈ (store.apply argument).mvars := by
        simpa [MStore.apply, Ty.mvars, List.mem_dedup, List.mem_append] using member
      rcases split with inside | inside
      · exact ihFunction (fun m h => typeBounded m (by simp [Ty.mvars, h])) id inside
      · exact ihArgument (fun m h => typeBounded m (by simp [Ty.mvars, h])) id inside

private theorem Expr.inferSize_openRigidsFrom (expr : Source) (depth base count : Nat) :
    (expr.openRigidsFrom depth base count).inferSize = expr.inferSize := by
  induction expr generalizing depth with
  | primLit literal => rfl
  | primOp op => rfl
  | var index => rfl
  | lambda ann body ih =>
      simp only [Expr.openRigidsFrom, Expr.inferSize, ih]
  | app function argument ihFunction ihArgument =>
      simp only [Expr.openRigidsFrom, Expr.inferSize, ihFunction, ihArgument]
  | letIn ann rhs body ihRhs ihBody =>
      cases ann with
      | none =>
          simp only [Expr.openRigidsFrom, Option.map_none, Expr.inferSize,
            ihRhs, ihBody]
      | some written =>
          simp only [Expr.openRigidsFrom, Option.map_some, Expr.inferSize,
            ihRhs, ihBody]
  | fix ann body ih =>
      simp only [Expr.openRigidsFrom, Expr.inferSize, ih]
  | const c => rfl

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
  | arrow domain codomain ihDomain ihCodomain =>
      have split : id ∈ domain.mvars ∨ id ∈ codomain.mvars := by
        simpa [Ty.mvars, List.mem_dedup, List.mem_append] using member
      rcases Ty.WF.arrow_parts wf with ⟨domainWF, codomainWF⟩
      rcases split with inside | inside
      · exact ihDomain domainWF inside
      · exact ihCodomain codomainWF inside
  | con => simp [Ty.mvars] at member
  | app function argument ihFunction ihArgument =>
      have split : id ∈ function.mvars ∨ id ∈ argument.mvars := by
        simpa [Ty.mvars, List.mem_dedup, List.mem_append] using member
      rcases Ty.WF.app_parts wf with ⟨functionWF, argumentWF⟩
      rcases split with inside | inside
      · exact ihFunction functionWF inside
      · exact ihArgument argumentWF inside

private theorem Ty.realize_ne_of_mem_mvars {ty : Ty} {first second : MValuation}
    {id : Nat} (member : id ∈ ty.mvars) (different : first id ≠ second id) :
    ty.realize first ≠ ty.realize second := by
  induction ty with
  | prim name => simp [Ty.mvars] at member
  | bvar index => simp [Ty.mvars] at member
  | rigid level => simp [Ty.mvars] at member
  | mvar other =>
      have same : id = other := by simpa [Ty.mvars] using member
      subst same
      simpa [Ty.realize] using different
  | arrow domain codomain ihDomain ihCodomain =>
      have split : id ∈ domain.mvars ∨ id ∈ codomain.mvars := by
        simpa [Ty.mvars, List.mem_dedup, List.mem_append] using member
      intro equal
      simp only [Ty.realize] at equal
      injection equal with domainEq codomainEq
      rcases split with inside | inside
      · exact ihDomain inside domainEq
      · exact ihCodomain inside codomainEq
  | con index => simp [Ty.mvars] at member
  | app function argument ihFunction ihArgument =>
      have split : id ∈ function.mvars ∨ id ∈ argument.mvars := by
        simpa [Ty.mvars, List.mem_dedup, List.mem_append] using member
      intro equal
      simp only [Ty.realize] at equal
      injection equal with functionEq argumentEq
      rcases split with inside | inside
      · exact ihFunction inside functionEq
      · exact ihArgument inside argumentEq

private theorem MStore.lookup_none_of_mem_apply_mvars {store : MStore} {ty : Ty}
    {id : Nat} (normalized : store.Normalized)
    (member : id ∈ (store.apply ty).mvars) :
    store.lookup id = none := by
  induction ty with
  | prim name => simp [MStore.apply, Ty.mvars] at member
  | arrow domain codomain ihDomain ihCodomain =>
      simp only [MStore.apply, Ty.mvars, List.mem_dedup, List.mem_append] at member
      rcases member with member | member
      · exact ihDomain member
      · exact ihCodomain member
  | bvar index => simp [MStore.apply, Ty.mvars] at member
  | rigid level => simp [MStore.apply, Ty.mvars] at member
  | mvar =>
      rename_i other
      cases lookup : store.lookup other with
      | none =>
          have applied : store.apply (.mvar other) = .mvar other := by
            simp [MStore.apply, lookup]
          rw [applied] at member
          have same : id = other := by simpa [Ty.mvars] using member
          rw [same]
          exact lookup
      | some solution =>
          have applied : store.apply (.mvar other) = solution := by
            simp [MStore.apply, lookup]
          rw [applied] at member
          exact normalized other solution lookup id member
  | con index => simp [MStore.apply, Ty.mvars] at member
  | app function argument ihFunction ihArgument =>
      simp only [MStore.apply, Ty.mvars, List.mem_dedup, List.mem_append] at member
      rcases member with member | member
      · exact ihFunction member
      · exact ihArgument member

private theorem MStore.Models.agree_of_unsolved_agree
    {store : MStore} {first second : MValuation} {level : Nat}
    (leveled : store.Leveled) (normalized : store.Normalized)
    (firstModels : store.Models first) (secondModels : store.Models second)
    (unsolvedAgree : ∀ id, store.lookup id = none → store.levelOf id ≤ level →
      first id = second id) :
    ∀ id, id < store.length → store.levelOf id ≤ level → first id = second id := by
  intro id hid hlevel
  cases get : store[id]? with
  | none =>
      have lookupNone : store.lookup id = none := by simp [MStore.lookup, get]
      exact unsolvedAgree id lookupNone hlevel
  | some entry =>
      cases solution : entry.solution with
      | none =>
          have lookupNone : store.lookup id = none := by
            simp [MStore.lookup, get, solution]
          exact unsolvedAgree id lookupNone hlevel
      | some ty =>
          have lookupSome : store.lookup id = some ty := by
            simp [MStore.lookup, get, solution]
          have firstEq := firstModels.equation id ty lookupSome
          have secondEq := secondModels.equation id ty lookupSome
          have realizeEq : ty.realize first = ty.realize second := by
            apply Ty.realize_congr
            intro m member
            have unsolved : store.lookup m = none :=
              normalized id ty lookupSome m member
            have levelLe : store.levelOf m ≤ store.levelOf id := by
              have levelEq : store.levelOf id = entry.level := by
                simp [MStore.levelOf, get]
              rw [levelEq]
              exact (leveled id entry ty get solution).2 m member
            exact unsolvedAgree m unsolved (le_trans levelLe hlevel)
          rw [firstEq, secondEq, realizeEq]

private theorem Ctx.realize_congr {ctx : Ctx} {first second : MValuation}
    (agree : ∀ scheme ∈ ctx, ∀ id ∈ scheme.body.mvars, first id = second id) :
    Ctx.realize ctx first = Ctx.realize ctx second := by
  unfold Ctx.realize
  apply List.map_congr_left
  intro scheme member
  exact PolyTy.realize_congr (agree scheme member)

private theorem Expr.mapAnn_congr {expr : Expr Ty} {f g : Ty → Ty}
    (pointwise : ∀ ty ∈ expr.annotations, f ty = g ty) :
    expr.mapAnn f = expr.mapAnn g := by
  induction expr with
  | primLit literal => rfl
  | primOp op => rfl
  | var index => rfl
  | lambda paramTy body ih =>
      have bodyPoint : ∀ ty ∈ body.annotations, f ty = g ty := by
        intro ty member
        exact pointwise ty (by simp [Expr.annotations, member])
      simp only [Expr.mapAnn]
      rw [ih bodyPoint]
      cases paramTy with
      | none => rfl
      | some ty =>
          have h := pointwise ty (by simp [Expr.annotations])
          simp [h]
  | app function argument ihFunction ihArgument =>
      have functionPoint : ∀ ty ∈ function.annotations, f ty = g ty := by
        intro ty member
        exact pointwise ty (by simp [Expr.annotations, member])
      have argumentPoint : ∀ ty ∈ argument.annotations, f ty = g ty := by
        intro ty member
        exact pointwise ty (by simp [Expr.annotations, member])
      simp only [Expr.mapAnn, ihFunction functionPoint,
        ihArgument argumentPoint]
  | letIn scheme rhs body ihRhs ihBody =>
      have rhsPoint : ∀ ty ∈ rhs.annotations, f ty = g ty := by
        intro ty member
        exact pointwise ty (by simp [Expr.annotations, member])
      have bodyPoint : ∀ ty ∈ body.annotations, f ty = g ty := by
        intro ty member
        exact pointwise ty (by simp [Expr.annotations, member])
      cases scheme with
      | none =>
          simp [Expr.mapAnn, ihRhs rhsPoint, ihBody bodyPoint]
      | some written =>
          have bodyEq : f written.body = g written.body := by
            apply pointwise
            simp [Expr.annotations]
          simp only [Expr.mapAnn, ihRhs rhsPoint, ihBody bodyPoint]
          cases written with
          | mk count ty => simp [Scheme.map, bodyEq]
  | fix ty body ih =>
      have bodyPoint : ∀ ty ∈ body.annotations, f ty = g ty := by
        intro ty member
        exact pointwise ty (by simp [Expr.annotations, member])
      simp only [Expr.mapAnn, ih bodyPoint]
      have selfEq := pointwise ty (by simp [Expr.annotations])
      simp [selfEq]
  | const c => rfl

private theorem MStore.exists_different_model
    {store : MStore} {valuation : MValuation} {u : Nat}
    (leveled : store.Leveled) (normalized : store.Normalized)
    (bounded : store.Bounded store.length) (models : store.Models valuation)
    (allocated : u < store.length) (unsolved : store.lookup u = none) :
    ∃ updated, store.Models updated ∧ updated u ≠ valuation u ∧
      ∀ other, store.lookup other = none → other ≠ u →
        updated other = valuation other := by
  let newTy : Ty :=
    if valuation u = .prim .int then .prim .unit else .prim .int
  have zeroWF : newTy.WF 0 0 := by
    by_cases same : valuation u = .prim .int
    · have newEq : newTy = .prim .unit := by simp [newTy, same]
      rw [newEq]
      exact ⟨.prim, .prim⟩
    · have newEq : newTy = .prim .int := by simp [newTy, same]
      rw [newEq]
      exact ⟨.prim, .prim⟩
  have wf : newTy.WF (store.levelOf u) 0 :=
    Ty.WF.mono_rigid zeroWF (Nat.zero_le _)
  obtain ⟨updated, updatedModels, updatedU, updatedAgree⟩ :=
    MStore.Models.reassign leveled normalized bounded models allocated unsolved wf
  refine ⟨updated, updatedModels, ?_, updatedAgree⟩
  rw [updatedU]
  by_cases same : valuation u = .prim .int
  · have newEq : newTy = .prim .unit := by simp [newTy, same]
    rw [newEq]
    simp [same]
  · have newEq : newTy = .prim .int := by simp [newTy, same]
    rw [newEq]
    exact fun equal => same equal.symm

private theorem Ty.metaFree_of_mvars_eq_nil {ty : Ty} (empty : ty.mvars = []) :
    ty.MetaFree := by
  induction ty with
  | prim => exact .prim
  | bvar => exact .bvar
  | rigid => exact .rigid
  | mvar id => simp [Ty.mvars] at empty
  | arrow domain codomain ihDomain ihCodomain =>
      simp only [Ty.mvars] at empty
      have appendNil : domain.mvars ++ codomain.mvars = [] := by
        apply List.eq_nil_iff_forall_not_mem.mpr
        intro x member
        have : x ∈ (domain.mvars ++ codomain.mvars).dedup :=
          List.mem_dedup.mpr member
        rw [empty] at this
        exact List.not_mem_nil this
      have parts := List.append_eq_nil_iff.mp appendNil
      exact .arrow (ihDomain parts.1) (ihCodomain parts.2)
  | con => exact .con
  | app function argument ihFunction ihArgument =>
      simp only [Ty.mvars] at empty
      have appendNil : function.mvars ++ argument.mvars = [] := by
        apply List.eq_nil_iff_forall_not_mem.mpr
        intro x member
        have : x ∈ (function.mvars ++ argument.mvars).dedup :=
          List.mem_dedup.mpr member
        rw [empty] at this
        exact List.not_mem_nil this
      have parts := List.append_eq_nil_iff.mp appendNil
      exact .app (ihFunction parts.1) (ihArgument parts.2)

private theorem Expr.annotations_mapAnn (expr : Expr Ty) (f : Ty → Ty) :
    (expr.mapAnn f).annotations = expr.annotations.map f := by
  induction expr with
  | primLit literal => rfl
  | primOp op => rfl
  | var index => rfl
  | lambda ann body ih =>
      simp only [Expr.mapAnn, Expr.annotations, ih]
      cases ann with
      | none => rfl
      | some ty => rfl
  | app function argument ihFunction ihArgument =>
      simp only [Expr.mapAnn, Expr.annotations, ihFunction, ihArgument,
        List.map_append]
  | letIn scheme rhs body ihRhs ihBody =>
      cases scheme with
      | none =>
          simp [Expr.mapAnn, Expr.annotations, ihRhs, ihBody, List.map_append]
      | some written =>
          simp [Expr.mapAnn, Expr.annotations, ihRhs, ihBody, List.map_append,
            Scheme.map]
  | fix selfTy body ih =>
      simp [Expr.mapAnn, Expr.annotations, ih]
  | const c => rfl

private theorem Expr.realize_ne_of_annotation_mvars {expr : Expr Ty}
    {first second : MValuation} {u : Nat}
    (member : ∃ annotation ∈ expr.annotations, u ∈ annotation.mvars)
    (different : first u ≠ second u) :
    expr.realize first ≠ expr.realize second := by
  induction expr with
  | primLit literal => simp [Expr.annotations] at member
  | primOp op => simp [Expr.annotations] at member
  | var index => simp [Expr.annotations] at member
  | lambda ann body ih =>
      obtain ⟨annotation, annotationMem, uMem⟩ := member
      cases ann with
      | none =>
          intro equal
          simp only [Expr.realize, Expr.mapAnn, Option.map_none] at equal
          injection equal with _ bodyEq
          simp [Expr.annotations] at annotationMem
          exact ih ⟨annotation, annotationMem, uMem⟩ bodyEq
      | some paramTy =>
          intro equal
          simp only [Expr.realize, Expr.mapAnn, Option.map_some] at equal
          injection equal with paramEq bodyEq
          have paramEq' : Ty.realize first paramTy = Ty.realize second paramTy := by
            injection paramEq with inner
          simp only [Expr.annotations, Option.toList, List.mem_append,
            List.mem_singleton] at annotationMem
          rcases annotationMem with rfl | bodyMem
          · exact (Ty.realize_ne_of_mem_mvars uMem different) paramEq'
          · exact ih ⟨annotation, bodyMem, uMem⟩ bodyEq
  | app function argument ihFunction ihArgument =>
      obtain ⟨annotation, annotationMem, uMem⟩ := member
      simp only [Expr.annotations, List.mem_append] at annotationMem
      intro equal
      simp only [Expr.realize, Expr.mapAnn] at equal
      injection equal with functionEq argumentEq
      rcases annotationMem with functionMem | argumentMem
      · exact ihFunction ⟨annotation, functionMem, uMem⟩ functionEq
      · exact ihArgument ⟨annotation, argumentMem, uMem⟩ argumentEq
  | letIn scheme rhs body ihRhs ihBody =>
      obtain ⟨annotation, annotationMem, uMem⟩ := member
      cases scheme with
      | none =>
          intro equal
          simp only [Expr.realize, Expr.mapAnn, Option.map_none] at equal
          injection equal with schemeEq rhsEq bodyEq
          simp [Expr.annotations] at annotationMem
          rcases annotationMem with rhsMem | bodyMem
          · exact ihRhs ⟨annotation, rhsMem, uMem⟩ rhsEq
          · exact ihBody ⟨annotation, bodyMem, uMem⟩ bodyEq
      | some written =>
          intro equal
          simp only [Expr.realize, Expr.mapAnn, Option.map_some,
            Scheme.map, PolyTy.realize] at equal
          injection equal with schemeEq rhsEq bodyEq
          have schemeBodyEq : Ty.realize first written.body =
              Ty.realize second written.body := by
            injection schemeEq with schemeEq'
            injection schemeEq' with bodyEq'
          simp [Expr.annotations] at annotationMem
          rcases annotationMem with rfl | rest
          · exact (Ty.realize_ne_of_mem_mvars uMem different) schemeBodyEq
          · rcases rest with rhsMem | bodyMem
            · exact ihRhs ⟨annotation, rhsMem, uMem⟩ rhsEq
            · exact ihBody ⟨annotation, bodyMem, uMem⟩ bodyEq
  | fix selfTy body ih =>
      obtain ⟨annotation, annotationMem, uMem⟩ := member
      simp only [Expr.annotations, List.mem_cons] at annotationMem
      intro equal
      simp only [Expr.realize, Expr.mapAnn] at equal
      injection equal with selfEq bodyEq
      rcases annotationMem with rfl | bodyMem
      · exact (Ty.realize_ne_of_mem_mvars uMem different) selfEq
      · exact ih ⟨annotation, bodyMem, uMem⟩ bodyEq
  | const c => simp [Expr.annotations] at member

private theorem Expr.mapAnn_mapAnn (expr : Expr Ty) (f g : Ty → Ty) :
    (expr.mapAnn f).mapAnn g = expr.mapAnn fun ty => g (f ty) := by
  induction expr with
  | primLit literal => rfl
  | primOp op => rfl
  | var index => rfl
  | lambda paramTy body ih =>
      simp only [Expr.mapAnn]
      rw [ih]
      cases paramTy with
      | none => rfl
      | some ty => rfl
  | app function argument ihFunction ihArgument =>
      simp only [Expr.mapAnn, ihFunction, ihArgument]
  | letIn scheme rhs body ihRhs ihBody =>
      cases scheme with
      | none => simp [Expr.mapAnn, ihRhs, ihBody]
      | some written =>
          simp only [Expr.mapAnn]
          rw [ihRhs, ihBody]
          cases written with
          | mk count ty => rfl
  | fix selfTy body ih =>
      simp only [Expr.mapAnn]
      rw [ih]
  | const c => rfl

private theorem Expr.mapAnn_id (expr : Expr Ty) : expr.mapAnn id = expr := by
  induction expr with
  | primLit literal => rfl
  | primOp op => rfl
  | var index => rfl
  | lambda ann body ih =>
      simp only [Expr.mapAnn]
      rw [ih]
      cases ann with
      | none => rfl
      | some ty => rfl
  | app function argument ihFunction ihArgument =>
      simp only [Expr.mapAnn, ihFunction, ihArgument]
  | letIn scheme rhs body ihRhs ihBody =>
      cases scheme with
      | none => simp [Expr.mapAnn, ihRhs, ihBody]
      | some written =>
          simp only [Expr.mapAnn, ihRhs, ihBody]
          cases written with
          | mk count ty => rfl
  | fix selfTy body ih =>
      simp only [Expr.mapAnn]
      rw [ih]
      rfl
  | const c => rfl

private theorem Expr.realize_eq_self_of_annotations {expr : Expr Ty}
    {valuation : MValuation}
    (free : ∀ ty ∈ expr.annotations, ty.MetaFree) :
    expr.realize valuation = expr := by
  change expr.mapAnn (fun ty => ty.realize valuation) = expr
  conv_rhs => rw [← Expr.mapAnn_id expr]
  apply Expr.mapAnn_congr
  intro ty member
  exact Ty.realize_eq_self (free ty member) valuation

private theorem Expr.realize_applyExpr {store : MStore} {valuation : MValuation}
    (models : store.Models valuation) (expr : Expr Ty) :
    (store.applyExpr expr).realize valuation = expr.realize valuation := by
  change (expr.mapAnn store.apply).mapAnn (fun ty => ty.realize valuation) =
    expr.mapAnn (fun ty => ty.realize valuation)
  rw [Expr.mapAnn_mapAnn]
  apply Expr.mapAnn_congr
  intro ty _
  exact models.realize_apply ty

private theorem Expr.realize_congr {expr : Expr Ty} {first second : MValuation}
    (agree : ∀ ty ∈ expr.annotations, ∀ id ∈ ty.mvars, first id = second id) :
    expr.realize first = expr.realize second := by
  have pointwise : ∀ ty ∈ expr.annotations, ty.realize first = ty.realize second := by
    intro ty member
    exact Ty.realize_congr (agree ty member)
  simpa [Expr.realize] using Expr.mapAnn_congr pointwise

/-- Strengthened principality: the realized elaboration matches the given one,
and every recorded annotation is still allocated in the final state. -/
private theorem inferFuel_principal_elab_aux
    {fuel rigidCount : Nat} {ctx : Ctx} {input : Source}
    {state : InferState} {result : InferResult}
    {valuation : MValuation} {elaborated : Expr Ty} {ty : Ty}
    (stateSafe : state.Safe)
    (ctxWF : ctx.InferWF rigidCount state.next)
    (ctxLevels : ∀ scheme ∈ ctx, scheme.body.LevelBounded state.solutions rigidCount)
    (inputScoped : input.TypeScoped rigidCount 0)
    (run : inferFuel sig fuel rigidCount ctx input state = some result)
    (models : state.Models valuation)
    (elaborates : Elaborates sig rigidCount (ctx.realize valuation) input elaborated ty) :
    ∃ extended, result.state.Models extended ∧
      (∀ id, id < state.next → extended id = valuation id) ∧
      result.elaborated.realize extended = elaborated ∧
      result.ty.realize extended = ty ∧
      (∀ annotation ∈ result.elaborated.annotations,
        annotation.MVarBounded result.state.next) := by
  induction fuel generalizing rigidCount ctx input state result valuation elaborated ty with
  | zero => simp [inferFuel] at run
  | succ fuel ih =>
      cases input with
      | primLit literal =>
          simp only [inferFuel, Option.some.injEq] at run
          subst result
          cases elaborates
          cases literal with
          | unit =>
              exact ⟨valuation, models, by intro id hid; rfl, rfl, rfl,
                by intro annotation member; simp [Expr.annotations] at member⟩
          | int value =>
              exact ⟨valuation, models, by intro id hid; rfl, rfl, rfl,
                by intro annotation member; simp [Expr.annotations] at member⟩
          | char value =>
              exact ⟨valuation, models, by intro id hid; rfl, rfl, rfl,
                by intro annotation member; simp [Expr.annotations] at member⟩
      | primOp op =>
          cases hty : op.ty sig with
          | none => simp [inferFuel, hty] at run
          | some primTy =>
              simp [inferFuel, hty] at run
              subst result
              cases elaborates with
              | primOp htyD =>
                  have hEq : primTy = ty := Option.some.inj (hty.symm.trans htyD)
                  subst hEq
                  exact ⟨valuation, models, by intro id hid; rfl, rfl,
                    Ty.realize_eq_self (primOpTy_metaFree htyD) valuation,
                    by intro annotation member; simp [Expr.annotations] at member⟩
      | var index =>
          simp only [inferFuel] at run
          cases lookup : ctx[index]? with
          | none => simp [lookup] at run
          | some scheme =>
              simp only [lookup] at run
              let fresh := state.freshMany rigidCount scheme.paramCount
              have resultEq : result =
                  ⟨fresh.1, (state.solutions.applyScheme scheme).openWith fresh.2,
                    .var index⟩ := Option.some.inj run.symm
              subst result
              cases elaborates with
              | var hlookupD hwfD hlenD hargsD =>
                  rename_i schemeD argsD
                  have schemeMember : scheme ∈ ctx := List.mem_of_getElem? lookup
                  have schemeWF := ctxWF scheme schemeMember
                  have schemeLevels := ctxLevels scheme schemeMember
                  have lookupRealize : (ctx.realize valuation)[index]? =
                      some (scheme.realize valuation) := by
                    simp [Ctx.realize, lookup]
                  have schemeDEq : schemeD = scheme.realize valuation := by
                    rw [lookupRealize] at hlookupD
                    exact (Option.some.inj hlookupD).symm
                  have argsLen : argsD.length = scheme.paramCount := by
                    rw [schemeDEq] at hlenD
                    simpa [PolyTy.realize] using hlenD
                  obtain ⟨extended, extModels, extAgree, extMap⟩ :=
                    InferState.freshMany_models (state := state)
                      (valuation := valuation) (level := rigidCount)
                      (count := scheme.paramCount) stateSafe models argsD argsLen hargsD
                  have applied := MStore.apply_inferWF stateSafe.solutionsLeveled
                    stateSafe.solutionsBounded schemeWF schemeLevels
                  have oldModels : state.Models extended :=
                    (InferState.freshMany_refines (state := state)
                      (level := rigidCount) (count := scheme.paramCount))
                      extended extModels
                  have opened := Ty.realize_openWith (args := fresh.2)
                    (MStore.Models.images_scoped oldModels stateSafe.solutions_length
                      applied.1.2 applied.2)
                  have appliedEq :
                      (state.solutions.apply scheme.body).realize extended =
                        (scheme.body).realize valuation := by
                    rw [oldModels.realize_apply scheme.body]
                    apply Ty.realize_congr
                    intro id member
                    exact extAgree id (schemeWF.2 id member)
                  have resultTyEq :
                      ((state.solutions.applyScheme scheme).openWith fresh.2).realize
                          extended =
                        (scheme.realize valuation).openWith argsD := by
                    rw [extMap] at opened
                    simpa [PolyTy.openWith, PolyTy.realize, MStore.applyScheme,
                      appliedEq] using opened
                  refine ⟨extended, extModels, extAgree, rfl, ?_, ?_⟩
                  · rw [resultTyEq]
                    rw [← schemeDEq]
                  · intro annotation member
                    simp [Expr.annotations] at member
      | lambda ann body =>
          cases inputScoped with
          | lambda annScoped bodyScoped =>
            cases ann with
            | none =>
                simp only [inferFuel] at run
                let seeded := state.fresh rigidCount
                cases bodyRun : inferFuel sig fuel rigidCount
                    (PolyTy.mono seeded.2 :: ctx) body seeded.1 with
                | none => simp [seeded, bodyRun] at run
                | some bodyResult =>
                    dsimp [seeded] at bodyRun
                    rw [bodyRun] at run
                    have resultEq : result =
                        ⟨bodyResult.state,
                          .arrow (bodyResult.state.solutions.apply seeded.2)
                            bodyResult.ty,
                          .lambda (some seeded.2) bodyResult.elaborated⟩ :=
                      Option.some.inj run.symm
                    subst result
                    cases elaborates with
                    | lambda paramWF paramMatches bodyElaborates =>
                        rename_i paramTy bodyElabD bodyTy
                        have seededSafe := InferState.fresh_safe
                          (level := rigidCount) stateSafe
                        let firstValuation : MValuation :=
                          fun id => if id = state.next then paramTy else valuation id
                        have seedModels : seeded.1.Models firstValuation :=
                          (InferState.fresh_models stateSafe models paramWF).1
                        have bodyCtxWF : Ctx.InferWF
                            (PolyTy.mono seeded.2 :: ctx) rigidCount seeded.1.next := by
                          intro scheme member
                          simp only [List.mem_cons] at member
                          rcases member with rfl | member
                          · exact seededSafe.2.1
                          · exact Ctx.InferWF.mono_frontier ctxWF
                              seededSafe.2.2.2.1 scheme member
                        have bodyCtxLevels :
                            ∀ scheme ∈ PolyTy.mono seeded.2 :: ctx,
                              scheme.body.LevelBounded seeded.1.solutions rigidCount := by
                          intro scheme member
                          simp only [List.mem_cons] at member
                          rcases member with rfl | member
                          · exact seededSafe.2.2.1
                          · intro id hid
                            have idBound : id < state.next :=
                              (ctxWF scheme member).2 id hid
                            rw [seededSafe.2.2.2.2 id idBound]
                            exact ctxLevels scheme member id hid
                        have bodySafe := inferFuel_safe seededSafe.1 bodyCtxWF
                          bodyCtxLevels bodyScoped bodyRun
                        have seedRealize : seeded.2.realize firstValuation = paramTy := by
                          simp [seeded, firstValuation, InferState.fresh, Ty.realize]
                        have firstAgree : ∀ id, id < state.next →
                            firstValuation id = valuation id := by
                          intro id hid
                          simp [firstValuation, Nat.ne_of_lt hid]
                        have ctxRealizeEq : Ctx.realize ctx firstValuation =
                            Ctx.realize ctx valuation :=
                          Ctx.realize_congr (fun scheme member id idMem =>
                            firstAgree id ((ctxWF scheme member).2 id idMem))
                        have bodyElaborates' : Elaborates sig rigidCount
                            (Ctx.realize (PolyTy.mono seeded.2 :: ctx) firstValuation)
                            body bodyElabD bodyTy := by
                          have ctxEq : Ctx.realize (PolyTy.mono seeded.2 :: ctx)
                              firstValuation =
                              PolyTy.mono paramTy :: Ctx.realize ctx valuation := by
                            change PolyTy.mono (seeded.2.realize firstValuation) ::
                                Ctx.realize ctx firstValuation =
                              PolyTy.mono paramTy :: Ctx.realize ctx valuation
                            rw [seedRealize, ctxRealizeEq]
                          rwa [ctxEq]
                        obtain ⟨extended, bodyModels, bodyAgree, bodyElabEq,
                          bodyTyEq, bodyAnnBound⟩ :=
                          ih seededSafe.1 bodyCtxWF bodyCtxLevels bodyScoped bodyRun
                            seedModels bodyElaborates'
                        have seedLt : state.next < seeded.1.next := by
                          simp [seeded, InferState.fresh]
                        have paramEq : seeded.2.realize extended = paramTy := by
                          have h := bodyAgree state.next seedLt
                          simpa [seeded, firstValuation, InferState.fresh, Ty.realize]
                            using h
                        refine ⟨extended, bodyModels, ?_, ?_, ?_, ?_⟩
                        · intro id hid
                          exact (bodyAgree id (lt_trans hid seedLt)).trans (by
                            simp [firstValuation, Nat.ne_of_lt hid])
                        · change Expr.lambda (some (seeded.2.realize extended))
                              (bodyResult.elaborated.realize extended) =
                            Expr.lambda (some paramTy) bodyElabD
                          rw [paramEq, bodyElabEq]
                        · change Ty.arrow (Ty.realize extended (bodyResult.state.solutions.apply seeded.2))
                              (Ty.realize extended bodyResult.ty) =
                            Ty.arrow paramTy bodyTy
                          rw [bodyModels.realize_apply seeded.2, paramEq, bodyTyEq]
                        · intro annotation member
                          simp only [Expr.annotations, Option.toList_some,
                            List.mem_append, List.mem_singleton] at member
                          rcases member with rfl | member
                          · show (Ty.mvar state.next).MVarBounded bodyResult.state.next
                            intro id idMember
                            simp only [Ty.mvars, List.mem_singleton] at idMember
                            subst idMember
                            exact lt_of_lt_of_le seedLt bodySafe.2.2.2.1
                          · exact bodyAnnBound annotation member
            | some template =>
                have templateScoped := annScoped template rfl
                simp only [inferFuel] at run
                let seeded := state.allocate rigidCount template
                cases bodyRun : inferFuel sig fuel rigidCount
                    (PolyTy.mono seeded.2 :: ctx) body seeded.1 with
                | none => simp [seeded, bodyRun] at run
                | some bodyResult =>
                    dsimp [seeded] at bodyRun
                    rw [bodyRun] at run
                    have resultEq : result =
                        ⟨bodyResult.state,
                          .arrow (bodyResult.state.solutions.apply seeded.2)
                            bodyResult.ty,
                          .lambda (some seeded.2) bodyResult.elaborated⟩ :=
                      Option.some.inj run.symm
                    subst result
                    cases elaborates with
                    | lambda paramWF paramMatches bodyElaborates =>
                        rename_i paramTy bodyElabD bodyTy
                        have seededSafe := InferState.allocate_safe
                          (level := rigidCount) (rigidCount := rigidCount)
                          stateSafe templateScoped
                        obtain ⟨holeVal, holeAgree, holeRealize, holeWF⟩ :=
                          Template.allocate_realizes
                            (template := template) (rigid := rigidCount)
                            (binder := 0) (frontier := state.next)
                            (target := paramTy) (base := valuation)
                            (paramMatches template rfl) templateScoped paramWF
                        obtain ⟨firstValuation, seedModels, seedAgree, seedRealizeEq⟩ :=
                          InferState.allocate_models stateSafe models templateScoped
                            (assigned := holeVal) holeWF
                        have seedRealize : seeded.2.realize firstValuation = paramTy := by
                          simpa [seeded] using seedRealizeEq.trans holeRealize
                        have ctxRealizeEq : Ctx.realize ctx firstValuation =
                            Ctx.realize ctx valuation :=
                          Ctx.realize_congr (fun scheme member id idMem =>
                            seedAgree id ((ctxWF scheme member).2 id idMem))
                        have bodyCtxWF : Ctx.InferWF
                            (PolyTy.mono seeded.2 :: ctx) rigidCount seeded.1.next := by
                          intro scheme member
                          simp only [List.mem_cons] at member
                          rcases member with rfl | member
                          · exact seededSafe.2.1
                          · exact Ctx.InferWF.mono_frontier ctxWF
                              seededSafe.2.2.2.1 scheme member
                        have bodyCtxLevels :
                            ∀ scheme ∈ PolyTy.mono seeded.2 :: ctx,
                              scheme.body.LevelBounded seeded.1.solutions rigidCount := by
                          intro scheme member
                          simp only [List.mem_cons] at member
                          rcases member with rfl | member
                          · exact seededSafe.2.2.1
                          · intro id hid
                            have idBound : id < state.next :=
                              (ctxWF scheme member).2 id hid
                            rw [seededSafe.2.2.2.2 id idBound]
                            exact ctxLevels scheme member id hid
                        have bodySafe := inferFuel_safe seededSafe.1 bodyCtxWF
                          bodyCtxLevels bodyScoped bodyRun
                        have bodyElaborates' : Elaborates sig rigidCount
                            (Ctx.realize (PolyTy.mono seeded.2 :: ctx) firstValuation)
                            body bodyElabD bodyTy := by
                          have ctxEq : Ctx.realize (PolyTy.mono seeded.2 :: ctx)
                              firstValuation =
                              PolyTy.mono paramTy :: Ctx.realize ctx valuation := by
                            change PolyTy.mono (seeded.2.realize firstValuation) ::
                                Ctx.realize ctx firstValuation =
                              PolyTy.mono paramTy :: Ctx.realize ctx valuation
                            rw [seedRealize, ctxRealizeEq]
                          rwa [ctxEq]
                        obtain ⟨extended, bodyModels, bodyAgree, bodyElabEq,
                          bodyTyEq, bodyAnnBound⟩ :=
                          ih seededSafe.1 bodyCtxWF bodyCtxLevels bodyScoped bodyRun
                            seedModels bodyElaborates'
                        have allocateBound : ∀ id ∈ seeded.2.mvars,
                            id < seeded.1.next := by
                          intro id member
                          exact (Template.allocate_mvars templateScoped
                            (frontier := state.next) id (by simpa [seeded] using member)).2
                        have paramEq : seeded.2.realize extended = paramTy := by
                          rw [show seeded.2.realize extended =
                              seeded.2.realize firstValuation by
                            apply Ty.realize_congr
                            intro id member
                            exact bodyAgree id (allocateBound id member)]
                          exact seedRealize
                        refine ⟨extended, bodyModels, ?_, ?_, ?_, ?_⟩
                        · intro id hid
                          exact (bodyAgree id
                            (lt_of_lt_of_le hid seededSafe.2.2.2.1)).trans
                            (seedAgree id hid)
                        · change Expr.lambda (some (seeded.2.realize extended))
                              (bodyResult.elaborated.realize extended) =
                            Expr.lambda (some paramTy) bodyElabD
                          rw [paramEq, bodyElabEq]
                        · change Ty.arrow (Ty.realize extended (bodyResult.state.solutions.apply seeded.2))
                              (Ty.realize extended bodyResult.ty) =
                            Ty.arrow paramTy bodyTy
                          rw [bodyModels.realize_apply seeded.2, paramEq, bodyTyEq]
                        · intro annotation member
                          simp only [Expr.annotations, Option.toList_some,
                            List.mem_append, List.mem_singleton] at member
                          rcases member with rfl | member
                          · intro id idMember
                            exact lt_of_lt_of_le (allocateBound id idMember)
                              bodySafe.2.2.2.1
                          · exact bodyAnnBound annotation member
      | app function argument =>
          cases inputScoped with
          | app functionScoped argumentScoped =>
            simp only [inferFuel] at run
            cases functionRun : inferFuel sig fuel rigidCount ctx function state with
            | none => simp [functionRun] at run
            | some functionResult =>
              have functionSafe := inferFuel_safe stateSafe ctxWF ctxLevels
                functionScoped functionRun
              have argumentCtxWF := Ctx.InferWF.mono_frontier ctxWF
                functionSafe.2.2.2.1
              have argumentCtxLevels :
                  ∀ scheme ∈ ctx,
                    scheme.body.LevelBounded
                      functionResult.state.solutions rigidCount := by
                intro scheme member id hid
                have idBound : id < state.next :=
                  (ctxWF scheme member).2 id hid
                exact le_trans (functionSafe.2.2.2.2 id idBound)
                  (ctxLevels scheme member id hid)
              cases argumentRun : inferFuel sig fuel rigidCount ctx argument
                  functionResult.state with
              | none => simp [functionRun, argumentRun] at run
              | some argumentResult =>
                have argumentSafe := inferFuel_safe functionSafe.1 argumentCtxWF
                  argumentCtxLevels argumentScoped argumentRun
                let fresh := argumentResult.state.fresh rigidCount
                have freshSafe := InferState.fresh_safe
                  (level := rigidCount) argumentSafe.1
                cases checkedRun : fresh.1.constrain functionResult.ty
                    (.arrow argumentResult.ty fresh.2) with
                | none =>
                    dsimp [fresh] at checkedRun
                    simp [functionRun, argumentRun, checkedRun] at run
                | some checked =>
                    dsimp [fresh] at checkedRun
                    have resultEq : result =
                        ⟨checked, checked.solutions.apply fresh.2,
                          .app functionResult.elaborated
                            argumentResult.elaborated⟩ := by
                      simpa [functionRun, argumentRun, checkedRun] using run.symm
                    subst result
                    have wholeTyWF : ty.WF rigidCount 0 :=
                      Typing.regular (Elaborates.typing elaborates)
                    cases elaborates with
                    | app functionElaborates argumentElaborates =>
                        rename_i functionElabD argumentTyD argumentElabED
                        obtain ⟨ext1, functionModels, functionAgree, functionElabEq,
                          functionTyEq, functionAnnBound⟩ :=
                          ih stateSafe ctxWF ctxLevels functionScoped functionRun
                            models functionElaborates
                        have argumentElaborates' : Elaborates sig rigidCount
                            (Ctx.realize ctx ext1) argument argumentElabED argumentTyD := by
                          have ctxEq := Ctx.realize_congr
                            (ctx := ctx)
                            (first := ext1) (second := valuation)
                            (fun scheme member id idMem =>
                              functionAgree id ((ctxWF scheme member).2 id idMem))
                          simpa [ctxEq] using argumentElaborates
                        obtain ⟨ext2, argumentModels, argumentAgree, argumentElabEq,
                          argumentTyEq, argumentAnnBound⟩ :=
                          ih functionSafe.1 argumentCtxWF argumentCtxLevels
                            argumentScoped argumentRun functionModels argumentElaborates'
                        let extFresh : MValuation := fun id =>
                          if id = argumentResult.state.next then ty else ext2 id
                        have freshModels :
                            (argumentResult.state.fresh rigidCount).1.Models extFresh := by
                          simpa [fresh, extFresh] using
                            (InferState.fresh_models argumentSafe.1 argumentModels
                              (ty := ty) (level := rigidCount)
                              (by simpa using wholeTyWF)).1
                        have freshAgree : ∀ id, id < argumentResult.state.next →
                            extFresh id = ext2 id := by
                          intro id hid
                          simp [extFresh, Nat.ne_of_lt hid]
                        have functionExt : functionResult.ty.realize extFresh =
                            functionResult.ty.realize ext2 := by
                          apply Ty.realize_congr
                          intro id member
                          exact freshAgree id (lt_of_lt_of_le
                            (functionSafe.2.1.2 id member)
                            argumentSafe.2.2.2.1)
                        have argumentExt : argumentResult.ty.realize extFresh =
                            argumentResult.ty.realize ext2 := by
                          apply Ty.realize_congr
                          intro id member
                          exact freshAgree id (argumentSafe.2.1.2 id member)
                        have freshVal : extFresh argumentResult.state.next = ty := by
                          change (if argumentResult.state.next = argumentResult.state.next
                            then ty else ext2 argumentResult.state.next) = ty
                          simp
                        have leftBounded : functionResult.ty.MVarBounded
                            fresh.1.next :=
                          fun id member => lt_of_lt_of_le
                            (functionSafe.2.1.2 id member)
                            (le_trans argumentSafe.2.2.2.1 freshSafe.2.2.2.1)
                        have rightBounded : (Ty.arrow argumentResult.ty fresh.2).MVarBounded
                            fresh.1.next := by
                          intro id member
                          simp only [Ty.mvars, List.mem_dedup, List.mem_append,
                            List.mem_singleton] at member
                          rcases member with member | member
                          · exact lt_of_lt_of_le (argumentSafe.2.1.2 id member)
                              freshSafe.2.2.2.1
                          · have idEq : id = argumentResult.state.next := by
                              simpa [Ty.mvars, fresh, InferState.fresh,
                                List.mem_singleton] using member
                            rw [idEq]
                            simpa [fresh, InferState.fresh] using
                              freshSafe.2.2.2.1
                        have functionTyAtFresh : functionResult.ty.realize extFresh =
                            Ty.arrow argumentTyD ty := by
                          rw [show functionResult.ty.realize extFresh =
                              functionResult.ty.realize ext1 by
                            apply Ty.realize_congr
                            intro id member
                            have idBound := functionSafe.2.1.2 id member
                            exact (freshAgree id (lt_of_lt_of_le idBound
                              argumentSafe.2.2.2.1)).trans
                              (argumentAgree id idBound)]
                          exact functionTyEq
                        have unifies : functionResult.ty.realize extFresh =
                            (Ty.arrow argumentResult.ty fresh.2).realize extFresh := by
                          rw [functionTyAtFresh]
                          simp only [Ty.realize]
                          rw [argumentExt, argumentTyEq]
                          change Ty.arrow argumentTyD ty =
                            Ty.arrow argumentTyD (extFresh argumentResult.state.next)
                          rw [freshVal]
                        obtain ⟨unified, unifiedRun, unifiedModels⟩ :=
                          MStore.unify_complete
                            (store := fresh.1.solutions)
                            (left := functionResult.ty)
                            (right := Ty.arrow argumentResult.ty fresh.2)
                            (valuation := extFresh)
                            freshSafe.1.solutionsNormalized
                            (by simpa [fresh, freshSafe.1.solutions_length] using
                              freshSafe.1.solutionsBounded)
                            (by simpa [fresh, freshSafe.1.solutions_length] using leftBounded)
                            (by simpa [fresh, freshSafe.1.solutions_length] using rightBounded)
                            freshModels unifies
                        have checkedEq : ({ fresh.1 with solutions := unified } :
                            InferState) = checked := by
                          unfold InferState.constrain at checkedRun
                          rw [unifiedRun] at checkedRun
                          exact Option.some.inj checkedRun
                        have checkedModels :
                            ({ fresh.1 with solutions := unified } : InferState).Models
                              extFresh := by simpa using unifiedModels
                        cases checkedEq
                        have functionFreshEq :
                            functionResult.elaborated.realize extFresh =
                              functionResult.elaborated.realize ext1 := by
                          apply Expr.realize_congr
                          intro annotation member id idMember
                          have idBound := functionAnnBound annotation member id idMember
                          rw [freshAgree id (lt_of_lt_of_le idBound
                            argumentSafe.2.2.2.1)]
                          exact argumentAgree id idBound
                        have argumentFreshEq :
                            argumentResult.elaborated.realize extFresh =
                              argumentResult.elaborated.realize ext2 := by
                          apply Expr.realize_congr
                          intro annotation member id idMember
                          exact freshAgree id (argumentAnnBound annotation member id idMember)
                        refine ⟨extFresh, checkedModels, ?_, ?_, ?_, ?_⟩
                        · intro id hid
                          exact (freshAgree id (lt_of_lt_of_le
                            (lt_of_lt_of_le hid functionSafe.2.2.2.1)
                            argumentSafe.2.2.2.1)).trans
                            ((argumentAgree id (lt_of_lt_of_le hid
                              functionSafe.2.2.2.1)).trans
                              (functionAgree id hid))
                        · change Expr.app (functionResult.elaborated.realize extFresh)
                              (argumentResult.elaborated.realize extFresh) =
                            Expr.app functionElabD argumentElabED
                          rw [functionFreshEq, argumentFreshEq, functionElabEq,
                            argumentElabEq]
                        · change Ty.realize extFresh
                              (({ fresh.1 with solutions := unified } : InferState).solutions.apply
                                fresh.2) = ty
                          rw [checkedModels.realize_apply fresh.2]
                          exact freshVal
                        · intro annotation member id idMem
                          simp only [Expr.annotations, List.mem_append] at member
                          rcases member with member | member
                          · exact lt_of_lt_of_le (functionAnnBound annotation member id idMem)
                              (le_trans argumentSafe.2.2.2.1 freshSafe.2.2.2.1)
                          · exact lt_of_lt_of_le (argumentAnnBound annotation member id idMem)
                              freshSafe.2.2.2.1
      | letIn ann rhs body =>
          cases ann with
          | none =>
              cases inputScoped with
              | letMono rhsScoped bodyScoped =>
                  simp only [inferFuel] at run
                  cases rhsRun : inferFuel sig fuel rigidCount ctx rhs state with
                  | none => simp [rhsRun] at run
                  | some rhsResult =>
                      have rhsSafe := inferFuel_safe stateSafe ctxWF ctxLevels
                        rhsScoped rhsRun
                      let rhsTy := rhsResult.state.solutions.apply rhsResult.ty
                      cases bodyRun : inferFuel sig fuel rigidCount
                          (PolyTy.mono rhsTy :: ctx) body rhsResult.state with
                      | none => simp [rhsTy, rhsRun, bodyRun] at run
                      | some bodyResult =>
                          have resultEq : result =
                              ⟨bodyResult.state, bodyResult.ty,
                                .letIn none rhsResult.elaborated
                                  bodyResult.elaborated⟩ := by
                            simpa [rhsTy, rhsRun, bodyRun] using run.symm
                          subst result
                          cases elaborates with
                          | letMono rhsWF rhsElaborates bodyElaborates =>
                              rename_i rhsElabD rhsTyD bodyElabD
                              obtain ⟨ext1, rhsModels, rhsAgree, rhsElabEq,
                                rhsTyEq, rhsAnnBound⟩ :=
                                ih stateSafe ctxWF ctxLevels rhsScoped rhsRun
                                  models rhsElaborates
                              have rhsApplied := MStore.apply_inferWF
                                rhsSafe.1.solutionsLeveled rhsSafe.1.solutionsBounded
                                rhsSafe.2.1 rhsSafe.2.2.1
                              have bodyCtxWF : Ctx.InferWF (PolyTy.mono rhsTy :: ctx)
                                  rigidCount rhsResult.state.next := by
                                intro scheme member
                                simp only [List.mem_cons] at member
                                rcases member with rfl | member
                                · exact rhsApplied.1
                                · exact Ctx.InferWF.mono_frontier ctxWF
                                    rhsSafe.2.2.2.1 scheme member
                              have bodyCtxLevels :
                                  ∀ scheme ∈ PolyTy.mono rhsTy :: ctx,
                                    scheme.body.LevelBounded
                                      rhsResult.state.solutions rigidCount := by
                                intro scheme member
                                simp only [List.mem_cons] at member
                                rcases member with rfl | member
                                · exact rhsApplied.2
                                · intro id hid
                                  have idBound : id < state.next :=
                                    (ctxWF scheme member).2 id hid
                                  exact le_trans (rhsSafe.2.2.2.2 id idBound)
                                    (ctxLevels scheme member id hid)
                              have bodySafe := inferFuel_safe rhsSafe.1 bodyCtxWF
                                bodyCtxLevels bodyScoped bodyRun
                              have bodyElaborates' : Elaborates sig rigidCount
                                  (Ctx.realize (PolyTy.mono rhsTy :: ctx) ext1)
                                  body bodyElabD ty := by
                                have ctxEq : Ctx.realize (PolyTy.mono rhsTy :: ctx) ext1 =
                                    PolyTy.mono rhsTyD :: Ctx.realize ctx valuation := by
                                  change PolyTy.mono (rhsTy.realize ext1) ::
                                      Ctx.realize ctx ext1 =
                                    PolyTy.mono rhsTyD :: Ctx.realize ctx valuation
                                  rw [show Ty.realize ext1 rhsTy =
                                      rhsResult.ty.realize ext1 by
                                    simpa [rhsTy] using
                                      rhsModels.realize_apply rhsResult.ty,
                                    rhsTyEq]
                                  congr 1
                                  exact Ctx.realize_congr (fun scheme member id idMem =>
                                    rhsAgree id ((ctxWF scheme member).2 id idMem))
                                rwa [ctxEq]
                              obtain ⟨ext2, bodyModels, bodyAgree, bodyElabEq,
                                tyEq, bodyAnnBound⟩ :=
                                ih rhsSafe.1 bodyCtxWF bodyCtxLevels bodyScoped bodyRun
                                  rhsModels bodyElaborates'
                              have rhsAtExt2 :
                                  rhsResult.elaborated.realize ext2 =
                                    rhsResult.elaborated.realize ext1 := by
                                apply Expr.realize_congr
                                intro annotation member id idMem
                                exact bodyAgree id
                                  (rhsAnnBound annotation member id idMem)
                              refine ⟨ext2, bodyModels, ?_, ?_, ?_, ?_⟩
                              · intro id hid
                                exact (bodyAgree id (lt_of_lt_of_le hid
                                  rhsSafe.2.2.2.1)).trans (rhsAgree id hid)
                              · change Expr.letIn none (rhsResult.elaborated.realize ext2)
                                    (bodyResult.elaborated.realize ext2) =
                                  Expr.letIn none rhsElabD bodyElabD
                                rw [rhsAtExt2, bodyElabEq, rhsElabEq]
                              · change Ty.realize ext2 bodyResult.ty = ty
                                exact tyEq
                              · intro annotation member id idMem
                                simp [Expr.annotations] at member
                                rcases member with member | member
                                · exact lt_of_lt_of_le
                                    (rhsAnnBound annotation member id idMem)
                                    bodySafe.2.2.2.1
                                · exact bodyAnnBound annotation member id idMem
          | some written =>
              cases inputScoped with
              | letPoly writtenScoped rhsScoped bodyScoped =>
                  cases elaborates with
                  | letPoly schemeMatches schemeWF ctxWFD rhsScopedD rhsElaborates
                      uniqueness bodyElaborates =>
                      rename_i scheme rhsElabD bodyElabD
                      simp only [inferFuel] at run
                      let localStart := state.next
                      let count := written.paramCount
                      let inner := rigidCount + count
                      let openedTemplate :=
                        written.body.openRigidsFrom 0 rigidCount count
                      have openedTemplateScoped : openedTemplate.Scoped inner 0 := by
                        simpa [openedTemplate, inner, count, Nat.zero_add] using
                          (Template.openRigidsFrom_scoped
                            (rigidCount := rigidCount) (depth := 0)
                            (count := count) writtenScoped)
                      let seeded := state.allocate inner openedTemplate
                      have seededSafe := InferState.allocate_safe
                        (level := inner) (rigidCount := inner)
                        stateSafe openedTemplateScoped
                      have openedRhsScoped :
                          (rhs.openRigids rigidCount count).TypeScoped inner 0 := by
                        simpa [Expr.openRigids, inner, count, Nat.zero_add] using
                          (Expr.openRigidsFrom_typeScoped
                            (rigidCount := rigidCount) (depth := 0)
                            (count := count) rhsScoped)
                      have rhsCtxWF : ctx.InferWF inner seeded.1.next :=
                        Ctx.InferWF.mono_frontier
                          (Ctx.InferWF.mono_rigid ctxWF (by omega))
                          seededSafe.2.2.2.1
                      have rhsCtxLevels :
                          ∀ scheme ∈ ctx,
                            scheme.body.LevelBounded seeded.1.solutions inner := by
                        intro scheme member id hid
                        have idBound : id < state.next :=
                          (ctxWF scheme member).2 id hid
                        rw [seededSafe.2.2.2.2 id idBound]
                        exact le_trans (ctxLevels scheme member id hid) (by omega)
                      have countEq : scheme.paramCount = count := schemeMatches.paramCount_eq
                      have targetEq : scheme.openRigids rigidCount =
                          scheme.body.openRigidsFrom 0 rigidCount count := by
                        simpa [countEq] using
                          PolyTy.openRigids_eq_openRigidsFrom schemeWF
                      have targetWF : (scheme.openRigids rigidCount).WF inner 0 := by
                        rw [targetEq]
                        have bodyWF : scheme.body.WF rigidCount scheme.paramCount := schemeWF
                        simpa [inner, count, countEq, Nat.zero_add] using
                          (Ty.openRigidsFrom_wf (ty := scheme.body)
                            (rigidCount := rigidCount) (depth := 0)
                            (count := scheme.paramCount)
                            (by simpa [Nat.zero_add] using bodyWF))
                      have hmatchesOpened :
                          openedTemplate.Matches (scheme.openRigids rigidCount) := by
                        rw [targetEq]
                        simpa [openedTemplate] using
                          (schemeMatches.body_matches.openRigidsFrom 0 rigidCount count)
                      obtain ⟨holeVal, holeAgree, holeRealize, holeWF⟩ :=
                        Template.allocate_realizes
                          (template := openedTemplate) (rigid := inner) (binder := 0)
                          (frontier := state.next) (target := scheme.openRigids rigidCount)
                          (base := valuation) hmatchesOpened openedTemplateScoped targetWF
                      obtain ⟨firstValuation, seedModels, seedAgree, seedRealizeEq⟩ :=
                        InferState.allocate_models stateSafe models openedTemplateScoped
                          (assigned := holeVal) holeWF
                      have seedRealize : seeded.2.realize firstValuation =
                          scheme.openRigids rigidCount := by
                        simpa [seeded] using seedRealizeEq.trans holeRealize
                      cases rhsRun : inferFuel sig fuel inner ctx
                          (rhs.openRigids rigidCount count) seeded.1 with
                      | none =>
                          dsimp [seeded, openedTemplate, count, inner] at rhsRun
                          simp [rhsRun] at run
                      | some rhsResult =>
                          dsimp [seeded, openedTemplate, count, inner] at rhsRun
                          have rhsSafe := inferFuel_safe seededSafe.1 rhsCtxWF
                            rhsCtxLevels openedRhsScoped rhsRun
                          have rhsElaborates' : Elaborates sig inner (ctx.realize firstValuation)
                              (rhs.openRigids rigidCount count) rhsElabD
                              (scheme.openRigids rigidCount) := by
                            have ctxEq : Ctx.realize ctx firstValuation =
                                Ctx.realize ctx valuation :=
                              Ctx.realize_congr (fun scheme member id idMem =>
                                seedAgree id ((ctxWF scheme member).2 id idMem))
                            have base := rhsElaborates
                            rw [countEq] at base
                            simpa [ctxEq] using base
                          obtain ⟨ext1, rhsModels, rhsAgree, rhsElabEq, rhsTyEq,
                            rhsAnnBound⟩ :=
                            ih seededSafe.1 rhsCtxWF rhsCtxLevels openedRhsScoped
                              rhsRun seedModels rhsElaborates'
                          have seededExt : seeded.2.realize ext1 =
                              scheme.openRigids rigidCount := by
                            rw [show seeded.2.realize ext1 =
                                seeded.2.realize firstValuation by
                              apply Ty.realize_congr
                              intro id member
                              exact rhsAgree id (seededSafe.2.1.2 id member)]
                            exact seedRealize
                          have seededTyAtRhs : seeded.2.InferWF inner 0
                              rhsResult.state.next :=
                            Ty.InferWF.mono_frontier seededSafe.2.1 rhsSafe.2.2.2.1
                          have seededLevelsRhs : seeded.2.LevelBounded
                              rhsResult.state.solutions inner :=
                            Ty.LevelBounded.mono_le_on seededSafe.2.2.1 (fun id member =>
                              rhsSafe.2.2.2.2 id (seededSafe.2.1.2 id member))
                          cases checkedRun : rhsResult.state.constrain
                              rhsResult.ty seeded.2 with
                          | none =>
                              dsimp [seeded, openedTemplate, count, inner] at checkedRun
                              simp [rhsRun, checkedRun] at run
                          | some checked =>
                              dsimp [seeded, openedTemplate, count, inner] at checkedRun
                              have checkedSafe := InferState.constrain_safe rhsSafe.1
                                rhsSafe.2.1 seededTyAtRhs checkedRun
                              have checkedRefines : rhsResult.state.Refines checked :=
                                InferState.constrain_refines rhsSafe.1 checkedRun
                              let completedOpen := checked.solutions.apply seeded.2
                              let completed : PolyTy :=
                                ⟨count, completedOpen.closeRigids rigidCount count⟩
                              simp [rhsRun, checkedRun] at run
                              have good :
                                  completedOpen.mvars.all
                                    (fun id => checked.solutions.levelOf id ≤
                                      rigidCount) = true := by
                                refine List.all_eq_true.mpr ?_
                                intro id mem
                                simpa [completedOpen] using run.1 id mem
                              have completedOpenLevelsRigid : completedOpen.LevelBounded
                                  checked.solutions rigidCount := by
                                simpa [Ty.LevelBounded] using (List.all_eq_true.mp good)
                              have localStartLe : localStart ≤ checked.next := by
                                rw [checkedSafe.2.1]
                                exact le_trans seededSafe.2.2.2.1 rhsSafe.2.2.2.1
                              have checkedLevelLeState :
                                  ∀ id, id < state.next →
                                    checked.solutions.levelOf id ≤
                                      state.solutions.levelOf id := by
                                intro id hid
                                have hidSeeded : id < seeded.1.next :=
                                  lt_of_lt_of_le hid seededSafe.2.2.2.1
                                have hidRhs : id < rhsResult.state.next :=
                                  lt_of_lt_of_le hidSeeded rhsSafe.2.2.2.1
                                calc checked.solutions.levelOf id
                                    ≤ rhsResult.state.solutions.levelOf id :=
                                      checkedSafe.2.2.2 id
                                  _ ≤ seeded.1.solutions.levelOf id :=
                                      rhsSafe.2.2.2.2 id hidSeeded
                                  _ = state.solutions.levelOf id :=
                                      seededSafe.2.2.2.2 id hid
                              have seededAtChecked : seeded.2.InferWF inner 0
                                  checked.next := by
                                rw [checkedSafe.2.1]
                                exact seededTyAtRhs
                              have seededLevelsChecked : seeded.2.LevelBounded
                                  checked.solutions inner :=
                                Ty.LevelBounded.mono_le seededLevelsRhs
                                  (fun id => checkedSafe.2.2.2 id)
                              have completedOpenApplied := MStore.apply_inferWF
                                checkedSafe.1.solutionsLeveled
                                checkedSafe.1.solutionsBounded
                                seededAtChecked seededLevelsChecked
                              have completedOpenWF : completedOpen.InferWF inner 0
                                  checked.next := completedOpenApplied.1
                              have completedOpenLevelsInner : completedOpen.LevelBounded
                                  checked.solutions inner := completedOpenApplied.2
                              have completedBodyScoped :
                                  completed.body.Scoped rigidCount count := by
                                simpa [completed, inner] using
                                  Ty.closeRigids_scoped_zero completedOpenWF.1
                              have completedBodyBounded :
                                  completed.body.MVarBounded checked.next := by
                                simpa [completed] using
                                  Ty.closeRigids_mvarBounded completedOpenWF.2
                              have completedInferWF : completed.InferWF
                                  rigidCount checked.next :=
                                ⟨completedBodyScoped, completedBodyBounded⟩
                              have completedLevels : completed.body.LevelBounded
                                  checked.solutions rigidCount := by
                                simpa [completed] using
                                  Ty.closeRigids_levelBounded completedOpenLevelsRigid
                              have ctxWFChecked : ctx.InferWF rigidCount checked.next :=
                                Ctx.InferWF.mono_frontier ctxWF localStartLe
                              have ctxLevelsChecked :
                                  ∀ scheme ∈ ctx, scheme.body.LevelBounded
                                    checked.solutions rigidCount := by
                                intro scheme member id hid
                                have idBound : id < state.next :=
                                  (ctxWF scheme member).2 id hid
                                exact le_trans (checkedLevelLeState id idBound)
                                  (ctxLevels scheme member id hid)
                              have unifies : rhsResult.ty.realize ext1 =
                                  seeded.2.realize ext1 :=
                                rhsTyEq.trans seededExt.symm
                              obtain ⟨unified, unifiedRun, unifiedModels⟩ :=
                                MStore.unify_complete
                                  (store := rhsResult.state.solutions)
                                  (left := rhsResult.ty) (right := seeded.2)
                                  (valuation := ext1)
                                  rhsSafe.1.solutionsNormalized
                                  (by simpa [rhsSafe.1.solutions_length] using
                                    rhsSafe.1.solutionsBounded)
                                  (by simpa [rhsSafe.1.solutions_length] using
                                    rhsSafe.2.1.2)
                                  (by simpa [rhsSafe.1.solutions_length] using
                                    seededTyAtRhs.2)
                                  rhsModels unifies
                              have checkedEq : ({ rhsResult.state with solutions := unified } :
                                  InferState) = checked := by
                                unfold InferState.constrain at checkedRun
                                rw [unifiedRun] at checkedRun
                                exact Option.some.inj checkedRun
                              have checkedModels : checked.Models ext1 := by
                                rw [← checkedEq]
                                exact unifiedModels
                              have completedOpenRealize : completedOpen.realize ext1 =
                                  scheme.openRigids rigidCount := by
                                rw [show completedOpen = checked.solutions.apply seeded.2 from rfl,
                                  checkedModels.realize_apply seeded.2]
                                exact seededExt
                              have completedOpenRealizedWF :
                                  (completedOpen.realize ext1).WF inner 0 :=
                                Ty.realize_inferWF_model checkedModels
                                  checkedSafe.1.solutions_length completedOpenWF
                                  completedOpenLevelsInner
                              have imagesScoped : ∀ id ∈ completedOpen.mvars,
                                  (ext1 id).Scoped rigidCount 0 :=
                                MStore.Models.images_scoped checkedModels
                                  checkedSafe.1.solutions_length completedOpenWF.2
                                  completedOpenLevelsRigid
                              have completedRealize : completed.realize ext1 =
                                  ⟨count, (completedOpen.realize ext1).closeRigids
                                    rigidCount count⟩ := by
                                simp only [completed, PolyTy.realize]
                                rw [Ty.realize_closeRigids imagesScoped]
                              have completedOpenEq :
                                  (completed.realize ext1).openRigids rigidCount =
                                    completedOpen.realize ext1 := by
                                rw [completedRealize]
                                exact PolyTy.openRigids_closeRigids
                                  completedOpenRealizedWF.1
                              have openedMatches : openedTemplate.Matches
                                  (completedOpen.realize ext1) := by
                                have seedEq := checkedModels.realize_apply seeded.2
                                have allocated := Template.allocate_matches_realize
                                  (valuation := ext1) (frontier := state.next)
                                  openedTemplateScoped
                                simpa [seeded, completedOpen, seedEq] using allocated
                              have writtenBodyScoped : written.body.Scoped
                                  rigidCount count := by
                                simpa [count] using writtenScoped
                              have closedMatches := Template.matches_closeRigids
                                writtenBodyScoped completedOpenRealizedWF.1 openedMatches
                              have schemeMatchesCompleted : SchemeTemplateMatches written
                                  (completed.realize ext1) := by
                                constructor
                                · simp [completed, count, PolyTy.realize]
                                · rw [completedRealize]
                                  exact closedMatches
                              have completedWF : (completed.realize ext1).WF rigidCount := by
                                rw [completedRealize]
                                exact Ty.closeRigids_wf completedOpenRealizedWF
                              have completedTyping : Typing sig inner (ctx.realize valuation)
                                  (rhs.openRigids rigidCount count)
                                  ((completed.realize ext1).openRigids rigidCount) := by
                                have base := Elaborates.typing rhsElaborates
                                rw [countEq] at base
                                simpa [completedOpenEq, completedOpenRealize] using base
                              have completedEq : completed.realize ext1 = scheme := by
                                rw [completedRealize, completedOpenRealize]
                                cases scheme with
                                | mk schemeCount schemeBody =>
                                    have countEq' : count = schemeCount :=
                                      schemeMatches.paramCount_eq.symm
                                    have scopedCount : schemeBody.Scoped
                                        rigidCount count := by
                                      rw [countEq']
                                      exact schemeWF.1
                                    have closeOpen : (schemeBody.openRigidsFrom 0
                                        rigidCount count).closeRigids rigidCount count =
                                          schemeBody :=
                                      Ty.closeRigids_openRigids scopedCount
                                    rw [targetEq]
                                    simp only [Scheme.mk.injEq]
                                    constructor
                                    · exact countEq'
                                    · simpa [countEq'] using closeOpen
                              have bodyCtxWF : Ctx.InferWF (completed :: ctx)
                                  rigidCount checked.next := by
                                intro scheme member
                                simp only [List.mem_cons] at member
                                rcases member with rfl | member
                                · exact completedInferWF
                                · exact ctxWFChecked scheme member
                              have bodyCtxLevels :
                                  ∀ scheme ∈ completed :: ctx,
                                    scheme.body.LevelBounded
                                      checked.solutions rigidCount := by
                                intro scheme member
                                simp only [List.mem_cons] at member
                                rcases member with rfl | member
                                · exact completedLevels
                                · exact ctxLevelsChecked scheme member
                              cases bodyRun : inferFuel sig fuel rigidCount
                                  (completed :: ctx) body checked with
                              | none =>
                                  simp [completed, completedOpen, count, inner,
                                    seeded, openedTemplate, bodyRun] at run
                              | some bodyResult =>
                                  have resultEq : result =
                                      ⟨bodyResult.state, bodyResult.ty,
                                        .letIn (some completed) rhsResult.elaborated
                                          bodyResult.elaborated⟩ := by
                                    have h : some result = some
                                        ⟨bodyResult.state, bodyResult.ty,
                                          .letIn (some completed) rhsResult.elaborated
                                            bodyResult.elaborated⟩ := by
                                      simpa [completed, completedOpen, count, inner,
                                        seeded, openedTemplate, bodyRun] using run.2.symm
                                    exact Option.some.inj h
                                  subst result
                                  have bodySafe := inferFuel_safe checkedSafe.1 bodyCtxWF
                                    bodyCtxLevels bodyScoped bodyRun
                                  have bodyElaborates' : Elaborates sig rigidCount
                                      (Ctx.realize (completed :: ctx) ext1)
                                      body bodyElabD ty := by
                                    have ctxEq : Ctx.realize (completed :: ctx) ext1 =
                                        scheme :: Ctx.realize ctx valuation := by
                                      change completed.realize ext1 :: Ctx.realize ctx ext1 =
                                        scheme :: Ctx.realize ctx valuation
                                      rw [completedEq]
                                      congr 1
                                      exact Ctx.realize_congr (fun s m id hid =>
                                        (rhsAgree id (lt_of_lt_of_le
                                          ((ctxWF s m).2 id hid) seededSafe.2.2.2.1)).trans
                                          (seedAgree id ((ctxWF s m).2 id hid)))
                                    rwa [ctxEq]
                                  obtain ⟨ext2, bodyModels, bodyAgree, bodyElabEq,
                                    tyEq, bodyAnnBound⟩ :=
                                    ih checkedSafe.1 bodyCtxWF bodyCtxLevels bodyScoped
                                      bodyRun checkedModels bodyElaborates'
                                  have completedAtExt2 : completed.realize ext2 =
                                      completed.realize ext1 := by
                                    apply PolyTy.realize_congr
                                    intro id member
                                    exact bodyAgree id (completedInferWF.2 id member)
                                  have rhsAtExt2 : rhsResult.elaborated.realize ext2 =
                                      rhsResult.elaborated.realize ext1 := by
                                    apply Expr.realize_congr
                                    intro annotation member id idMem
                                    have idBound := rhsAnnBound annotation member id idMem
                                    have idChecked : id < checked.next := by
                                      rwa [checkedSafe.2.1]
                                    exact bodyAgree id idChecked
                                  refine ⟨ext2, bodyModels, ?_, ?_, ?_, ?_⟩
                                  · intro id hid
                                    have idChecked : id < checked.next := by
                                      rw [checkedSafe.2.1]
                                      exact lt_of_lt_of_le
                                        (lt_of_lt_of_le hid seededSafe.2.2.2.1)
                                        rhsSafe.2.2.2.1
                                    exact (bodyAgree id idChecked).trans
                                      ((rhsAgree id (lt_of_lt_of_le hid
                                        seededSafe.2.2.2.1)).trans (seedAgree id hid))
                                  · change Expr.letIn (some (completed.realize ext2))
                                        (rhsResult.elaborated.realize ext2)
                                        (bodyResult.elaborated.realize ext2) =
                                      Expr.letIn (some scheme) rhsElabD bodyElabD
                                    rw [completedAtExt2, completedEq, rhsAtExt2, rhsElabEq,
                                      bodyElabEq]
                                  · change Ty.realize ext2 bodyResult.ty = ty
                                    exact tyEq
                                  · intro annotation member id idMem
                                    have member' : annotation ∈ [completed.body] ++
                                        rhsResult.elaborated.annotations ++
                                          bodyResult.elaborated.annotations := by
                                      simpa [Expr.annotations, completed] using member
                                    simp only [List.mem_append, List.mem_singleton] at member'
                                    rcases member' with (rfl | member) | member
                                    · exact lt_of_lt_of_le
                                        (completedInferWF.2 id idMem) bodySafe.2.2.2.1
                                    · have idBound := rhsAnnBound annotation member id idMem
                                      have idChecked : id < checked.next := by
                                        rwa [checkedSafe.2.1]
                                      exact lt_of_lt_of_le idChecked bodySafe.2.2.2.1
                                    · exact bodyAnnBound annotation member id idMem

      | fix ann body =>
          cases inputScoped with
          | fix annScoped bodyScoped =>
              simp only [inferFuel] at run
              let seeded := state.allocate rigidCount ann
              have seededSafe := InferState.allocate_safe
                (level := rigidCount) (rigidCount := rigidCount)
                stateSafe annScoped
              cases bodyRun : inferFuel sig fuel rigidCount
                  (PolyTy.mono seeded.2 :: ctx) body seeded.1 with
              | none =>
                  dsimp [seeded] at bodyRun
                  simp [bodyRun] at run
              | some bodyResult =>
                  dsimp [seeded] at bodyRun
                  rw [bodyRun] at run
                  change (bodyResult.state.constrain bodyResult.ty
                    seeded.2).bind (fun checked =>
                      some ⟨checked, checked.solutions.apply seeded.2,
                        .fix seeded.2 bodyResult.elaborated⟩) = some result at run
                  have bodyCtxWF : Ctx.InferWF (PolyTy.mono seeded.2 :: ctx)
                      rigidCount seeded.1.next := by
                    intro scheme member
                    simp only [List.mem_cons] at member
                    rcases member with rfl | member
                    · exact seededSafe.2.1
                    · exact Ctx.InferWF.mono_frontier ctxWF
                        seededSafe.2.2.2.1 scheme member
                  have bodyCtxLevels :
                      ∀ scheme ∈ PolyTy.mono seeded.2 :: ctx,
                        scheme.body.LevelBounded seeded.1.solutions rigidCount := by
                    intro scheme member
                    simp only [List.mem_cons] at member
                    rcases member with rfl | member
                    · exact seededSafe.2.2.1
                    · intro id hid
                      have idBound : id < state.next :=
                        (ctxWF scheme member).2 id hid
                      rw [seededSafe.2.2.2.2 id idBound]
                      exact ctxLevels scheme member id hid
                  have bodySafe := inferFuel_safe seededSafe.1 bodyCtxWF
                    bodyCtxLevels bodyScoped bodyRun
                  have seededSelfAtBody : seeded.2.InferWF rigidCount 0
                      bodyResult.state.next :=
                    Ty.InferWF.mono_frontier seededSafe.2.1 bodySafe.2.2.2.1
                  cases checkedRun : bodyResult.state.constrain
                      bodyResult.ty seeded.2 with
                  | none =>
                      rw [checkedRun] at run
                      simp at run
                  | some checked =>
                      have checkedSafe := InferState.constrain_safe bodySafe.1
                        bodySafe.2.1 seededSelfAtBody checkedRun
                      rw [checkedRun] at run
                      simp only [Option.bind_some, Option.some.injEq] at run
                      subst result
                      cases elaborates with
                      | fix selfWF annMatches bodyElaborates =>
                          rename_i bodyElabD
                          obtain ⟨holeVal, holeAgree, holeRealize, holeWF⟩ :=
                            Template.allocate_realizes
                              (template := ann) (rigid := rigidCount) (binder := 0)
                              (frontier := state.next) (target := ty)
                              (base := valuation) (annMatches) annScoped selfWF
                          obtain ⟨firstValuation, seedModels, seedAgree, seedRealizeEq⟩ :=
                            InferState.allocate_models stateSafe models annScoped
                              (assigned := holeVal) holeWF
                          have seedRealize : seeded.2.realize firstValuation = ty := by
                            simpa [seeded] using seedRealizeEq.trans holeRealize
                          have bodyElaborates' : Elaborates sig rigidCount
                              (Ctx.realize (PolyTy.mono seeded.2 :: ctx) firstValuation)
                              body bodyElabD ty := by
                            have ctxEq : Ctx.realize (PolyTy.mono seeded.2 :: ctx)
                                firstValuation =
                                PolyTy.mono ty :: Ctx.realize ctx valuation := by
                              change PolyTy.mono (seeded.2.realize firstValuation) ::
                                  Ctx.realize ctx firstValuation =
                                PolyTy.mono ty :: Ctx.realize ctx valuation
                              rw [seedRealize]
                              congr 1
                              exact Ctx.realize_congr (fun s m id hid =>
                                seedAgree id ((ctxWF s m).2 id hid))
                            rwa [ctxEq]
                          obtain ⟨ext1, bodyModels, bodyAgree, bodyElabEq,
                            bodyTyEq, bodyAnnBound⟩ :=
                            ih seededSafe.1 bodyCtxWF bodyCtxLevels bodyScoped
                              bodyRun seedModels bodyElaborates'
                          have seededExt : seeded.2.realize ext1 = ty := by
                            rw [show seeded.2.realize ext1 =
                                seeded.2.realize firstValuation by
                              apply Ty.realize_congr
                              intro id member
                              exact bodyAgree id (seededSafe.2.1.2 id member)]
                            exact seedRealize
                          have selfWFAtBody : seeded.2.InferWF rigidCount 0
                              bodyResult.state.next :=
                            Ty.InferWF.mono_frontier seededSafe.2.1 bodySafe.2.2.2.1
                          have selfLevelsBody : seeded.2.LevelBounded
                              bodyResult.state.solutions rigidCount :=
                            Ty.LevelBounded.mono_le_on seededSafe.2.2.1 (fun id member =>
                              bodySafe.2.2.2.2 id (seededSafe.2.1.2 id member))
                          have unifies : bodyResult.ty.realize ext1 =
                              seeded.2.realize ext1 :=
                            bodyTyEq.trans seededExt.symm
                          obtain ⟨unified, unifiedRun, unifiedModels⟩ :=
                            MStore.unify_complete
                              (store := bodyResult.state.solutions)
                              (left := bodyResult.ty) (right := seeded.2)
                              (valuation := ext1)
                              bodySafe.1.solutionsNormalized
                              (by simpa [bodySafe.1.solutions_length] using
                                bodySafe.1.solutionsBounded)
                              (by simpa [bodySafe.1.solutions_length] using
                                bodySafe.2.1.2)
                              (by simpa [bodySafe.1.solutions_length] using
                                selfWFAtBody.2)
                              bodyModels unifies
                          have checkedEq : ({ bodyResult.state with solutions := unified } :
                              InferState) = checked := by
                            unfold InferState.constrain at checkedRun
                            rw [unifiedRun] at checkedRun
                            exact Option.some.inj checkedRun
                          have checkedModels : checked.Models ext1 := by
                            rw [← checkedEq]
                            exact unifiedModels
                          have allocateBound : ∀ id ∈ seeded.2.mvars,
                              id < checked.next := by
                            intro id member
                            have idSeeded := (Template.allocate_mvars annScoped
                              (frontier := state.next) id (by simpa [seeded] using member)).2
                            rw [checkedSafe.2.1]
                            exact lt_of_lt_of_le idSeeded bodySafe.2.2.2.1
                          refine ⟨ext1, checkedModels, ?_, ?_, ?_, ?_⟩
                          · intro id hid
                            exact (bodyAgree id (lt_of_lt_of_le hid
                              seededSafe.2.2.2.1)).trans (seedAgree id hid)
                          · change Expr.fix (seeded.2.realize ext1)
                                (bodyResult.elaborated.realize ext1) =
                              Expr.fix ty bodyElabD
                            rw [seededExt, bodyElabEq]
                          · change Ty.realize ext1
                                (checked.solutions.apply seeded.2) = ty
                            rw [checkedModels.realize_apply seeded.2]
                            exact seededExt
                          · intro annotation member id idMem
                            have member' : annotation = seeded.2 ∨
                                annotation ∈ bodyResult.elaborated.annotations := by
                              simpa [Expr.annotations] using member
                            rcases member' with rfl | member
                            · exact allocateBound id idMem
                            · exact lt_of_lt_of_le
                                (bodyAnnBound annotation member id idMem)
                                (le_of_eq checkedSafe.2.1.symm)
      | const c =>
          simp only [inferFuel] at run
          cases lookup : sig.schemeOf c with
          | none => simp [lookup] at run
          | some scheme =>
              simp only [lookup] at run
              cases hb : scheme.wfB 0 with
              | false =>
                  cases elaborates with
                  | const hlookupD hwfD hlenD hargsD =>
                      rename_i schemeD argsD
                      rw [lookup] at hlookupD
                      have schemeDEq : schemeD = scheme :=
                        (Option.some.inj hlookupD).symm
                      subst schemeD
                      have hwfTrue : scheme.wfB 0 = true :=
                        Ty.wfB_eq_true_iff.mpr hwfD
                      rw [hb] at hwfTrue
                      exact Bool.noConfusion hwfTrue
              | true =>
                  have schemeWF0 : scheme.WF 0 := Ty.wfB_eq_true_iff.mp hb
                  let fresh := state.freshMany rigidCount scheme.paramCount
                  have resultEq : result =
                      ⟨fresh.1, scheme.openWith fresh.2, .const c⟩ := by
                    simpa [fresh, hb] using run.symm
                  subst result
                  cases elaborates with
                  | const hlookupD hwfD hlenD hargsD =>
                      rename_i schemeD argsD
                      rw [lookup] at hlookupD
                      have schemeDEq : schemeD = scheme :=
                        (Option.some.inj hlookupD).symm
                      subst schemeD
                      obtain ⟨extended, extModels, extAgree, extMap⟩ :=
                        InferState.freshMany_models (state := state)
                          (valuation := valuation) (level := rigidCount)
                          (count := scheme.paramCount) stateSafe models
                          argsD hlenD hargsD
                      have imagesScoped : ∀ id ∈ scheme.body.mvars,
                          (extended id).Scoped rigidCount 0 := by
                        intro id member
                        rw [Ty.MetaFree.mvars_eq_nil schemeWF0.2] at member
                        exact absurd member (List.not_mem_nil)
                      have opened := Ty.realize_openWith (ty := scheme.body)
                        (args := fresh.2) (valuation := extended) imagesScoped
                      have bodyRealize : scheme.body.realize extended = scheme.body :=
                        Ty.realize_eq_self schemeWF0.2 extended
                      have resultTyEq :
                          (scheme.openWith fresh.2).realize extended =
                            scheme.openWith argsD := by
                        simpa [PolyTy.openWith, bodyRealize, extMap, fresh] using opened
                      refine ⟨extended, extModels, extAgree, rfl, resultTyEq, ?_⟩
                      intro annotation member
                      simp [Expr.annotations] at member

/-- Principality with elaborations: when inference succeeds, every
elaboration of the input is an instance of the inferred elaboration and
type. -/
theorem inferFuel_principal_elab
    {fuel rigidCount : Nat} {ctx : Ctx} {input : Source}
    {state : InferState} {result : InferResult}
    {valuation : MValuation} {elaborated : Expr Ty} {ty : Ty}
    (stateSafe : state.Safe)
    (ctxWF : ctx.InferWF rigidCount state.next)
    (ctxLevels : ∀ scheme ∈ ctx, scheme.body.LevelBounded state.solutions rigidCount)
    (inputScoped : input.TypeScoped rigidCount 0)
    (run : inferFuel sig fuel rigidCount ctx input state = some result)
    (models : state.Models valuation)
    (elaborates : Elaborates sig rigidCount (ctx.realize valuation) input elaborated ty) :
    ∃ extended, result.state.Models extended ∧
      (∀ id, id < state.next → extended id = valuation id) ∧
      result.elaborated.realize extended = elaborated ∧
      result.ty.realize extended = ty := by
  obtain ⟨extended, hmodels, hagree, helab, hty, _⟩ :=
    inferFuel_principal_elab_aux stateSafe ctxWF ctxLevels inputScoped run models
      elaborates
  exact ⟨extended, hmodels, hagree, helab, hty⟩

/-- Inference does not fail on an elaborable program, given enough fuel. -/
theorem inferFuel_complete
    {fuel rigidCount : Nat} {ctx : Ctx} {input : Source}
    {state : InferState} {valuation : MValuation}
    {elaborated : Expr Ty} {ty : Ty}
    (stateSafe : state.Safe)
    (ctxWF : ctx.InferWF rigidCount state.next)
    (ctxLevels : ∀ scheme ∈ ctx, scheme.body.LevelBounded state.solutions rigidCount)
    (inputScoped : input.TypeScoped rigidCount 0)
    (enough : input.inferSize < fuel)
    (models : state.Models valuation)
    (elaborates : Elaborates sig rigidCount (ctx.realize valuation) input elaborated ty) :
    ∃ result, inferFuel sig fuel rigidCount ctx input state = some result := by
  induction fuel generalizing rigidCount ctx input state valuation elaborated ty with
  | zero => omega
  | succ fuel ih =>
      cases input with
      | primLit literal =>
          exact ⟨⟨state, literal.ty, .primLit literal⟩, rfl⟩
      | primOp op =>
          cases elaborates with
          | primOp htyD =>
              refine ⟨⟨state, ty, .primOp op⟩, ?_⟩
              simp [inferFuel, htyD]
      | var index =>
          simp only [inferFuel]
          cases lookup : ctx[index]? with
          | none =>
              cases elaborates with
              | var hlookupD _ _ _ =>
                  simp [Ctx.realize, lookup] at hlookupD
          | some scheme =>
              exact ⟨⟨(state.freshMany rigidCount scheme.paramCount).1,
                (state.solutions.applyScheme scheme).openWith
                  (state.freshMany rigidCount scheme.paramCount).2,
                .var index⟩, rfl⟩
      | lambda ann body =>
          cases inputScoped with
          | lambda annScoped bodyScoped =>
            have bodyEnough : body.inferSize < fuel := by
              simp [Expr.inferSize] at enough
              omega
            cases ann with
            | none =>
                cases elaborates with
                | lambda paramWF paramMatches bodyElaborates =>
                    rename_i paramTy bodyElabD bodyTy
                    let seeded := state.fresh rigidCount
                    have seededSafe := InferState.fresh_safe
                      (level := rigidCount) stateSafe
                    let firstValuation : MValuation :=
                      fun id => if id = state.next then paramTy else valuation id
                    have seedModels : seeded.1.Models firstValuation :=
                      (InferState.fresh_models stateSafe models paramWF).1
                    have bodyCtxWF : Ctx.InferWF
                        (PolyTy.mono seeded.2 :: ctx) rigidCount seeded.1.next := by
                      intro scheme member
                      simp only [List.mem_cons] at member
                      rcases member with rfl | member
                      · exact seededSafe.2.1
                      · exact Ctx.InferWF.mono_frontier ctxWF
                          seededSafe.2.2.2.1 scheme member
                    have bodyCtxLevels :
                        ∀ scheme ∈ PolyTy.mono seeded.2 :: ctx,
                          scheme.body.LevelBounded seeded.1.solutions rigidCount := by
                      intro scheme member
                      simp only [List.mem_cons] at member
                      rcases member with rfl | member
                      · exact seededSafe.2.2.1
                      · intro id hid
                        have idBound : id < state.next :=
                          (ctxWF scheme member).2 id hid
                        rw [seededSafe.2.2.2.2 id idBound]
                        exact ctxLevels scheme member id hid
                    have seedRealize : seeded.2.realize firstValuation = paramTy := by
                      simp [seeded, firstValuation, InferState.fresh, Ty.realize]
                    have bodyElaborates' : Elaborates sig rigidCount
                        (Ctx.realize (PolyTy.mono seeded.2 :: ctx) firstValuation)
                        body bodyElabD bodyTy := by
                      have ctxEq : Ctx.realize (PolyTy.mono seeded.2 :: ctx)
                          firstValuation =
                          PolyTy.mono paramTy :: Ctx.realize ctx valuation := by
                        change PolyTy.mono (seeded.2.realize firstValuation) ::
                            Ctx.realize ctx firstValuation =
                          PolyTy.mono paramTy :: Ctx.realize ctx valuation
                        rw [seedRealize]
                        congr 1
                        exact Ctx.realize_congr (fun s m id hid =>
                          (by
                            have h : id < state.next := (ctxWF s m).2 id hid
                            simp [firstValuation, Nat.ne_of_lt h]))
                      rwa [ctxEq]
                    obtain ⟨bodyResult, bodyRun⟩ :=
                      ih seededSafe.1 bodyCtxWF bodyCtxLevels bodyScoped
                        bodyEnough seedModels bodyElaborates'
                    refine ⟨⟨bodyResult.state,
                      .arrow (bodyResult.state.solutions.apply seeded.2) bodyResult.ty,
                      .lambda (some seeded.2) bodyResult.elaborated⟩, ?_⟩
                    simp [inferFuel, seeded, bodyRun]
            | some template =>
                have templateScoped := annScoped template rfl
                cases elaborates with
                | lambda paramWF paramMatches bodyElaborates =>
                    rename_i paramTy bodyElabD bodyTy
                    let seeded := state.allocate rigidCount template
                    have seededSafe := InferState.allocate_safe
                      (level := rigidCount) (rigidCount := rigidCount)
                      stateSafe templateScoped
                    obtain ⟨holeVal, holeAgree, holeRealize, holeWF⟩ :=
                      Template.allocate_realizes
                        (template := template) (rigid := rigidCount) (binder := 0)
                        (frontier := state.next) (target := paramTy)
                        (base := valuation) (paramMatches template rfl) templateScoped paramWF
                    obtain ⟨firstValuation, seedModels, seedAgree, seedRealizeEq⟩ :=
                      InferState.allocate_models stateSafe models templateScoped
                        (assigned := holeVal) holeWF
                    have seedRealize : seeded.2.realize firstValuation = paramTy := by
                      simpa [seeded] using seedRealizeEq.trans holeRealize
                    have bodyCtxWF : Ctx.InferWF
                        (PolyTy.mono seeded.2 :: ctx) rigidCount seeded.1.next := by
                      intro scheme member
                      simp only [List.mem_cons] at member
                      rcases member with rfl | member
                      · exact seededSafe.2.1
                      · exact Ctx.InferWF.mono_frontier ctxWF
                          seededSafe.2.2.2.1 scheme member
                    have bodyCtxLevels :
                        ∀ scheme ∈ PolyTy.mono seeded.2 :: ctx,
                          scheme.body.LevelBounded seeded.1.solutions rigidCount := by
                      intro scheme member
                      simp only [List.mem_cons] at member
                      rcases member with rfl | member
                      · exact seededSafe.2.2.1
                      · intro id hid
                        have idBound : id < state.next :=
                          (ctxWF scheme member).2 id hid
                        rw [seededSafe.2.2.2.2 id idBound]
                        exact ctxLevels scheme member id hid
                    have bodyElaborates' : Elaborates sig rigidCount
                        (Ctx.realize (PolyTy.mono seeded.2 :: ctx) firstValuation)
                        body bodyElabD bodyTy := by
                      have ctxEq : Ctx.realize (PolyTy.mono seeded.2 :: ctx)
                          firstValuation =
                          PolyTy.mono paramTy :: Ctx.realize ctx valuation := by
                        change PolyTy.mono (seeded.2.realize firstValuation) ::
                            Ctx.realize ctx firstValuation =
                          PolyTy.mono paramTy :: Ctx.realize ctx valuation
                        rw [seedRealize]
                        congr 1
                        exact Ctx.realize_congr (fun s m id hid =>
                          seedAgree id ((ctxWF s m).2 id hid))
                      rwa [ctxEq]
                    obtain ⟨bodyResult, bodyRun⟩ :=
                      ih seededSafe.1 bodyCtxWF bodyCtxLevels bodyScoped
                        bodyEnough seedModels bodyElaborates'
                    refine ⟨⟨bodyResult.state,
                      .arrow (bodyResult.state.solutions.apply seeded.2) bodyResult.ty,
                      .lambda (some seeded.2) bodyResult.elaborated⟩, ?_⟩
                    simp [inferFuel, seeded, bodyRun]
      | const c =>
          cases elaborates with
          | const hlookupD hwfD hlenD hargsD =>
              rename_i schemeD argsD
              cases lookup : sig.schemeOf c with
              | none =>
                  rw [lookup] at hlookupD
                  cases hlookupD
              | some scheme =>
                  rw [lookup] at hlookupD
                  have schemeDEq : schemeD = scheme :=
                    (Option.some.inj hlookupD).symm
                  subst schemeD
                  have hb : scheme.wfB 0 = true := Ty.wfB_eq_true_iff.mpr hwfD
                  refine ⟨⟨(state.freshMany rigidCount scheme.paramCount).1,
                    scheme.openWith (state.freshMany rigidCount scheme.paramCount).2,
                    .const c⟩, ?_⟩
                  simp [inferFuel, lookup, hb]
      | app function argument =>
          cases inputScoped with
          | app functionScoped argumentScoped =>
            have functionEnough : function.inferSize < fuel := by
              simp [Expr.inferSize] at enough
              omega
            have argumentEnough : argument.inferSize < fuel := by
              simp [Expr.inferSize] at enough
              omega
            cases elaborates with
            | app functionElaborates argumentElaborates =>
                rename_i functionElabD argumentTyD argumentElabED
                have wholeTyWF : ty.WF rigidCount 0 :=
                  Typing.regular (Elaborates.typing (.app functionElaborates argumentElaborates))
                obtain ⟨functionResult, functionRun⟩ :=
                  ih stateSafe ctxWF ctxLevels functionScoped functionEnough
                    models functionElaborates
                have functionSafe := inferFuel_safe stateSafe ctxWF ctxLevels
                  functionScoped functionRun
                obtain ⟨ext1, functionModels, functionAgree, _, functionTyEq, _⟩ :=
                  inferFuel_principal_elab_aux stateSafe ctxWF ctxLevels functionScoped
                    functionRun models functionElaborates
                have argumentCtxWF := Ctx.InferWF.mono_frontier ctxWF
                  functionSafe.2.2.2.1
                have argumentCtxLevels :
                    ∀ scheme ∈ ctx,
                      scheme.body.LevelBounded
                        functionResult.state.solutions rigidCount := by
                  intro scheme member id hid
                  have idBound : id < state.next :=
                    (ctxWF scheme member).2 id hid
                  exact le_trans (functionSafe.2.2.2.2 id idBound)
                    (ctxLevels scheme member id hid)
                have argumentElaborates' : Elaborates sig rigidCount
                    (Ctx.realize ctx ext1) argument argumentElabED argumentTyD := by
                  have ctxEq := Ctx.realize_congr (ctx := ctx)
                    (first := ext1) (second := valuation)
                    (fun scheme member id idMem =>
                      functionAgree id ((ctxWF scheme member).2 id idMem))
                  simpa [ctxEq] using argumentElaborates
                obtain ⟨argumentResult, argumentRun⟩ :=
                  ih functionSafe.1 argumentCtxWF argumentCtxLevels argumentScoped
                    argumentEnough functionModels argumentElaborates'
                have argumentSafe := inferFuel_safe functionSafe.1 argumentCtxWF
                  argumentCtxLevels argumentScoped argumentRun
                obtain ⟨ext2, argumentModels, argumentAgree, _, argumentTyEq, _⟩ :=
                  inferFuel_principal_elab_aux functionSafe.1 argumentCtxWF
                    argumentCtxLevels argumentScoped argumentRun functionModels
                    argumentElaborates'
                let fresh := argumentResult.state.fresh rigidCount
                have freshSafe := InferState.fresh_safe
                  (level := rigidCount) argumentSafe.1
                let extFresh : MValuation := fun id =>
                  if id = argumentResult.state.next then ty else ext2 id
                have freshModels :
                    (argumentResult.state.fresh rigidCount).1.Models extFresh := by
                  simpa [fresh, extFresh] using
                    (InferState.fresh_models argumentSafe.1 argumentModels
                      (ty := ty) (level := rigidCount)
                      (by simpa using wholeTyWF)).1
                have freshAgree : ∀ id, id < argumentResult.state.next →
                    extFresh id = ext2 id := by
                  intro id hid
                  simp [extFresh, Nat.ne_of_lt hid]
                have functionExt : functionResult.ty.realize extFresh =
                    functionResult.ty.realize ext2 := by
                  apply Ty.realize_congr
                  intro id member
                  exact freshAgree id (lt_of_lt_of_le
                    (functionSafe.2.1.2 id member) argumentSafe.2.2.2.1)
                have argumentExt : argumentResult.ty.realize extFresh =
                    argumentResult.ty.realize ext2 := by
                  apply Ty.realize_congr
                  intro id member
                  exact freshAgree id (argumentSafe.2.1.2 id member)
                have freshVal : extFresh argumentResult.state.next = ty := by
                  change (if argumentResult.state.next = argumentResult.state.next
                    then ty else ext2 argumentResult.state.next) = ty
                  simp
                have functionTyAtFresh : functionResult.ty.realize extFresh =
                    Ty.arrow argumentTyD ty := by
                  rw [show functionResult.ty.realize extFresh =
                      functionResult.ty.realize ext1 by
                    apply Ty.realize_congr
                    intro id member
                    have idBound := functionSafe.2.1.2 id member
                    exact (freshAgree id (lt_of_lt_of_le idBound
                      argumentSafe.2.2.2.1)).trans (argumentAgree id idBound)]
                  exact functionTyEq
                have leftBounded : functionResult.ty.MVarBounded fresh.1.next :=
                  fun id member => lt_of_lt_of_le
                    (functionSafe.2.1.2 id member)
                    (le_trans argumentSafe.2.2.2.1 freshSafe.2.2.2.1)
                have rightBounded : (Ty.arrow argumentResult.ty fresh.2).MVarBounded
                    fresh.1.next := by
                  intro id member
                  simp only [Ty.mvars, List.mem_dedup, List.mem_append] at member
                  rcases member with member | member
                  · exact lt_of_lt_of_le (argumentSafe.2.1.2 id member)
                      freshSafe.2.2.2.1
                  · have idEq : id = argumentResult.state.next := by
                      simpa [Ty.mvars, fresh, InferState.fresh, List.mem_singleton]
                        using member
                    rw [idEq]
                    simpa [fresh, InferState.fresh] using freshSafe.2.2.2.1
                have unifies : functionResult.ty.realize extFresh =
                    (Ty.arrow argumentResult.ty fresh.2).realize extFresh := by
                  rw [functionTyAtFresh]
                  simp only [Ty.realize]
                  rw [argumentExt, argumentTyEq]
                  change Ty.arrow argumentTyD ty =
                    Ty.arrow argumentTyD (extFresh argumentResult.state.next)
                  rw [freshVal]
                obtain ⟨unified, unifiedRun, _⟩ :=
                  MStore.unify_complete
                    (store := fresh.1.solutions)
                    (left := functionResult.ty)
                    (right := Ty.arrow argumentResult.ty fresh.2)
                    (valuation := extFresh)
                    freshSafe.1.solutionsNormalized
                    (by simpa [fresh, freshSafe.1.solutions_length] using
                      freshSafe.1.solutionsBounded)
                    (by simpa [fresh, freshSafe.1.solutions_length] using leftBounded)
                    (by simpa [fresh, freshSafe.1.solutions_length] using rightBounded)
                    freshModels unifies
                have checkedEq : ({ fresh.1 with solutions := unified } : InferState) =
                    { fresh.1 with solutions := unified } := rfl
                refine ⟨⟨{ fresh.1 with solutions := unified },
                  ({ fresh.1 with solutions := unified }).solutions.apply fresh.2,
                  .app functionResult.elaborated argumentResult.elaborated⟩, ?_⟩
                simp [inferFuel, functionRun, argumentRun, InferState.constrain,
                  unifiedRun, fresh]
      | letIn ann rhs body =>
          cases ann with
          | none =>
              cases inputScoped with
              | letMono rhsScoped bodyScoped =>
                  cases elaborates with
                  | letMono rhsWF rhsElaborates bodyElaborates =>
                      rename_i rhsElabD rhsTyD bodyElabD
                      have rhsEnough : rhs.inferSize < fuel := by
                        simp [Expr.inferSize] at enough
                        omega
                      have bodyEnough : body.inferSize < fuel := by
                        simp [Expr.inferSize] at enough
                        omega
                      obtain ⟨rhsResult, rhsRun⟩ :=
                        ih stateSafe ctxWF ctxLevels rhsScoped rhsEnough
                          models rhsElaborates
                      have rhsSafe := inferFuel_safe stateSafe ctxWF ctxLevels
                        rhsScoped rhsRun
                      obtain ⟨ext1, rhsModels, rhsAgree, _, rhsTyEq, _⟩ :=
                        inferFuel_principal_elab_aux stateSafe ctxWF ctxLevels
                          rhsScoped rhsRun models rhsElaborates
                      let rhsTy := rhsResult.state.solutions.apply rhsResult.ty
                      have rhsApplied := MStore.apply_inferWF
                        rhsSafe.1.solutionsLeveled rhsSafe.1.solutionsBounded
                        rhsSafe.2.1 rhsSafe.2.2.1
                      have bodyCtxWF : Ctx.InferWF (PolyTy.mono rhsTy :: ctx)
                          rigidCount rhsResult.state.next := by
                        intro scheme member
                        simp only [List.mem_cons] at member
                        rcases member with rfl | member
                        · exact rhsApplied.1
                        · exact Ctx.InferWF.mono_frontier ctxWF
                            rhsSafe.2.2.2.1 scheme member
                      have bodyCtxLevels :
                          ∀ scheme ∈ PolyTy.mono rhsTy :: ctx,
                            scheme.body.LevelBounded
                              rhsResult.state.solutions rigidCount := by
                        intro scheme member
                        simp only [List.mem_cons] at member
                        rcases member with rfl | member
                        · exact rhsApplied.2
                        · intro id hid
                          have idBound : id < state.next :=
                            (ctxWF scheme member).2 id hid
                          exact le_trans (rhsSafe.2.2.2.2 id idBound)
                            (ctxLevels scheme member id hid)
                      have bodyElaborates' : Elaborates sig rigidCount
                          (Ctx.realize (PolyTy.mono rhsTy :: ctx) ext1)
                          body bodyElabD ty := by
                        have ctxEq : Ctx.realize (PolyTy.mono rhsTy :: ctx) ext1 =
                            PolyTy.mono rhsTyD :: Ctx.realize ctx valuation := by
                          change PolyTy.mono (rhsTy.realize ext1) ::
                              Ctx.realize ctx ext1 =
                            PolyTy.mono rhsTyD :: Ctx.realize ctx valuation
                          rw [show rhsTy.realize ext1 = rhsResult.ty.realize ext1 by
                            simpa [rhsTy] using rhsModels.realize_apply rhsResult.ty,
                            rhsTyEq]
                          congr 1
                          exact Ctx.realize_congr (fun s m id hid =>
                            rhsAgree id ((ctxWF s m).2 id hid))
                        rwa [ctxEq]
                      obtain ⟨bodyResult, bodyRun⟩ :=
                        ih rhsSafe.1 bodyCtxWF bodyCtxLevels bodyScoped
                          bodyEnough rhsModels bodyElaborates'
                      refine ⟨⟨bodyResult.state, bodyResult.ty,
                        .letIn none rhsResult.elaborated bodyResult.elaborated⟩, ?_⟩
                      simp [inferFuel, rhsTy, rhsRun, bodyRun]
          | some written =>
              cases inputScoped with
              | letPoly writtenScoped rhsScoped bodyScoped =>
                  cases elaborates with
                  | letPoly schemeMatches schemeWF ctxWFD rhsScopedD rhsElaborates
                      uniqueness bodyElaborates =>
                      rename_i scheme rhsElabD bodyElabD
                      have rhsEnough : rhs.inferSize < fuel := by
                        simp [Expr.inferSize] at enough
                        omega
                      have bodyEnough : body.inferSize < fuel := by
                        simp [Expr.inferSize] at enough
                        omega
                      let count := written.paramCount
                      let inner := rigidCount + count
                      let openedTemplate :=
                        written.body.openRigidsFrom 0 rigidCount count
                      have openedTemplateScoped : openedTemplate.Scoped inner 0 := by
                        simpa [openedTemplate, inner, count, Nat.zero_add] using
                          (Template.openRigidsFrom_scoped
                            (rigidCount := rigidCount) (depth := 0)
                            (count := count) writtenScoped)
                      let seeded := state.allocate inner openedTemplate
                      have seededSafe := InferState.allocate_safe
                        (level := inner) (rigidCount := inner)
                        stateSafe openedTemplateScoped
                      have openedRhsScoped :
                          (rhs.openRigids rigidCount count).TypeScoped inner 0 := by
                        simpa [Expr.openRigids, inner, count, Nat.zero_add] using
                          (Expr.openRigidsFrom_typeScoped
                            (rigidCount := rigidCount) (depth := 0)
                            (count := count) rhsScoped)
                      have rhsCtxWF : ctx.InferWF inner seeded.1.next :=
                        Ctx.InferWF.mono_frontier
                          (Ctx.InferWF.mono_rigid ctxWF (by omega))
                          seededSafe.2.2.2.1
                      have rhsCtxLevels :
                          ∀ scheme ∈ ctx,
                            scheme.body.LevelBounded seeded.1.solutions inner := by
                        intro scheme member id hid
                        have idBound : id < state.next :=
                          (ctxWF scheme member).2 id hid
                        rw [seededSafe.2.2.2.2 id idBound]
                        exact le_trans (ctxLevels scheme member id hid) (by omega)
                      have countEq : scheme.paramCount = count := schemeMatches.paramCount_eq
                      have targetEq : scheme.openRigids rigidCount =
                          scheme.body.openRigidsFrom 0 rigidCount count := by
                        simpa [countEq] using
                          PolyTy.openRigids_eq_openRigidsFrom schemeWF
                      have targetWF : (scheme.openRigids rigidCount).WF inner 0 := by
                        rw [targetEq]
                        have bodyWF : scheme.body.WF rigidCount scheme.paramCount := schemeWF
                        simpa [inner, count, countEq, Nat.zero_add] using
                          (Ty.openRigidsFrom_wf (ty := scheme.body)
                            (rigidCount := rigidCount) (depth := 0)
                            (count := scheme.paramCount)
                            (by simpa [Nat.zero_add] using bodyWF))
                      have hmatchesOpened :
                          openedTemplate.Matches (scheme.openRigids rigidCount) := by
                        rw [targetEq]
                        simpa [openedTemplate] using
                          (schemeMatches.body_matches.openRigidsFrom 0 rigidCount count)
                      obtain ⟨holeVal, holeAgree, holeRealize, holeWF⟩ :=
                        Template.allocate_realizes
                          (template := openedTemplate) (rigid := inner) (binder := 0)
                          (frontier := state.next) (target := scheme.openRigids rigidCount)
                          (base := valuation) hmatchesOpened openedTemplateScoped targetWF
                      obtain ⟨firstValuation, seedModels, seedAgree, seedRealizeEq⟩ :=
                        InferState.allocate_models stateSafe models openedTemplateScoped
                          (assigned := holeVal) holeWF
                      have seedRealize : seeded.2.realize firstValuation =
                          scheme.openRigids rigidCount := by
                        simpa [seeded] using seedRealizeEq.trans holeRealize
                      have rhsElaborates' : Elaborates sig inner (ctx.realize firstValuation)
                          (rhs.openRigids rigidCount count) rhsElabD
                          (scheme.openRigids rigidCount) := by
                        have ctxEq : Ctx.realize ctx firstValuation =
                            Ctx.realize ctx valuation :=
                          Ctx.realize_congr (fun scheme member id idMem =>
                            seedAgree id ((ctxWF scheme member).2 id idMem))
                        have base := rhsElaborates
                        rw [countEq] at base
                        simpa [ctxEq] using base
                      have rhsEnough' : (rhs.openRigids rigidCount count).inferSize <
                          fuel := by
                        simpa [Expr.openRigids, Expr.inferSize_openRigidsFrom]
                          using rhsEnough
                      obtain ⟨rhsResult, rhsRun⟩ :=
                        ih seededSafe.1 rhsCtxWF rhsCtxLevels openedRhsScoped
                          rhsEnough' seedModels rhsElaborates'
                      have rhsSafe := inferFuel_safe seededSafe.1 rhsCtxWF
                        rhsCtxLevels openedRhsScoped rhsRun
                      obtain ⟨ext1, rhsModels, rhsAgree, _, rhsTyEq, _⟩ :=
                        inferFuel_principal_elab_aux seededSafe.1 rhsCtxWF rhsCtxLevels
                          openedRhsScoped rhsRun seedModels rhsElaborates'
                      have seededExt : seeded.2.realize ext1 =
                          scheme.openRigids rigidCount := by
                        rw [show seeded.2.realize ext1 =
                            seeded.2.realize firstValuation by
                          apply Ty.realize_congr
                          intro id member
                          exact rhsAgree id (seededSafe.2.1.2 id member)]
                        exact seedRealize
                      have seededTyAtRhs : seeded.2.InferWF inner 0
                          rhsResult.state.next :=
                        Ty.InferWF.mono_frontier seededSafe.2.1 rhsSafe.2.2.2.1
                      have seededLevelsRhs : seeded.2.LevelBounded
                          rhsResult.state.solutions inner :=
                        Ty.LevelBounded.mono_le_on seededSafe.2.2.1 (fun id member =>
                          rhsSafe.2.2.2.2 id (seededSafe.2.1.2 id member))
                      obtain ⟨unified, unifiedRun, unifiedModels⟩ :=
                        MStore.unify_complete
                          (store := rhsResult.state.solutions)
                          (left := rhsResult.ty) (right := seeded.2)
                          (valuation := ext1)
                          rhsSafe.1.solutionsNormalized
                          (by simpa [rhsSafe.1.solutions_length] using
                            rhsSafe.1.solutionsBounded)
                          (by simpa [rhsSafe.1.solutions_length] using rhsSafe.2.1.2)
                          (by simpa [rhsSafe.1.solutions_length] using seededTyAtRhs.2)
                          rhsModels (rhsTyEq.trans seededExt.symm)
                      let checked : InferState :=
                        { rhsResult.state with solutions := unified }
                      have checkedSafe : checked.Safe := by
                        constructor
                        · simp [checked, rhsSafe.1.solutions_length,
                            MStore.unify_length unifiedRun]
                        · simpa [checked] using MStore.unify_leveled
                            rhsSafe.1.solutionsLeveled rhsSafe.1.solutionsNormalized
                            unifiedRun
                        · simpa [checked] using MStore.unify_bounded
                            rhsSafe.1.solutionsBounded rhsSafe.2.1.2 seededTyAtRhs.2
                            unifiedRun
                        · simpa [checked] using MStore.unify_normalized
                            rhsSafe.1.solutionsNormalized unifiedRun
                      have checkedNext : checked.next = rhsResult.state.next := rfl
                      have checkedModels : checked.Models ext1 := by
                        simpa [checked] using unifiedModels
                      let completedOpen := checked.solutions.apply seeded.2
                      let completed : PolyTy :=
                        ⟨count, completedOpen.closeRigids rigidCount count⟩
                      let localStart := state.next
                      have localStartLe : localStart ≤ checked.next := by
                        rw [checkedNext]
                        exact le_trans seededSafe.2.2.2.1 rhsSafe.2.2.2.1
                      have stateLeChecked : state.next ≤ checked.next := by
                        rw [checkedNext]
                        exact le_trans seededSafe.2.2.2.1 rhsSafe.2.2.2.1
                      have checkedLevelLeState :
                          ∀ id, id < state.next →
                            checked.solutions.levelOf id ≤
                              state.solutions.levelOf id := by
                        intro id hid
                        have hidSeeded : id < seeded.1.next :=
                          lt_of_lt_of_le hid seededSafe.2.2.2.1
                        have hidRhs : id < rhsResult.state.next :=
                          lt_of_lt_of_le hidSeeded rhsSafe.2.2.2.1
                        have hidChecked : id < rhsResult.state.solutions.length := by
                          simpa [rhsSafe.1.solutions_length] using hidRhs
                        calc checked.solutions.levelOf id
                            ≤ rhsResult.state.solutions.levelOf id :=
                              MStore.unify_levelOf_le unifiedRun id
                          _ ≤ seeded.1.solutions.levelOf id :=
                              rhsSafe.2.2.2.2 id hidSeeded
                          _ = state.solutions.levelOf id :=
                              seededSafe.2.2.2.2 id hid
                      have seededAtChecked : seeded.2.InferWF inner 0
                          checked.next := by
                        rw [checkedNext]
                        exact seededTyAtRhs
                      have seededLevelsChecked : seeded.2.LevelBounded
                          checked.solutions inner :=
                        Ty.LevelBounded.mono_le seededLevelsRhs
                          (fun id => MStore.unify_levelOf_le unifiedRun id)
                      have completedOpenApplied := MStore.apply_inferWF
                        checkedSafe.solutionsLeveled
                        checkedSafe.solutionsBounded
                        seededAtChecked seededLevelsChecked
                      have completedOpenWF : completedOpen.InferWF inner 0
                          checked.next := completedOpenApplied.1
                      have completedOpenLevelsInner : completedOpen.LevelBounded
                          checked.solutions inner := completedOpenApplied.2
                      have completedOpenRealizedWFExt1 :
                          (completedOpen.realize ext1).WF inner 0 :=
                        Ty.realize_inferWF_model checkedModels
                          checkedSafe.solutions_length completedOpenWF
                          completedOpenLevelsInner
                      have writtenBodyScoped : written.body.Scoped rigidCount count := by
                        simpa [count] using writtenScoped
                      have goodNonzero : scheme.paramCount ≠ 0 →
                          completedOpen.mvars.all
                            (fun id => checked.solutions.levelOf id ≤ rigidCount) = true := by
                        intro hnonzero
                        have huniq := uniqueness.elim
                          (fun hzero => absurd hzero hnonzero) id
                        by_contra hbad
                        have hfalse : completedOpen.mvars.all
                            (fun id => checked.solutions.levelOf id ≤ rigidCount) = false := by
                          cases h : completedOpen.mvars.all
                              (fun id => checked.solutions.levelOf id ≤ rigidCount) <;>
                            simp_all
                        obtain ⟨u, hu, hlevel⟩ := List.all_eq_false.mp hfalse
                        have uLevel : rigidCount < checked.solutions.levelOf u := by
                          have h : ¬ checked.solutions.levelOf u ≤ rigidCount := by
                            simpa using hlevel
                          exact not_le.mp h
                        have uLookup : checked.solutions.lookup u = none :=
                          MStore.lookup_none_of_mem_apply_mvars
                            checkedSafe.solutionsNormalized hu
                        have uBounded : u < checked.solutions.length := by
                          have applyBounded := MStore.apply_mvarBounded
                            (store := checked.solutions) (ty := seeded.2)
                            (frontier := checked.next) checkedSafe.solutionsBounded
                            seededAtChecked.2
                          have idBound := applyBounded u hu
                          simpa [checkedSafe.solutions_length] using idBound
                        let newTy : Ty :=
                          if ext1 u = .prim .int then .prim .unit else .prim .int
                        have newTyZero : newTy.WF 0 0 := by
                          by_cases same : ext1 u = .prim .int
                          · have newEq : newTy = .prim .unit := by simp [newTy, same]
                            rw [newEq]
                            exact ⟨.prim, .prim⟩
                          · have newEq : newTy = .prim .int := by simp [newTy, same]
                            rw [newEq]
                            exact ⟨.prim, .prim⟩
                        have newTyWF : newTy.WF (checked.solutions.levelOf u) 0 :=
                          Ty.WF.mono_rigid newTyZero (Nat.zero_le _)
                        have newTyDifferent : ext1 u ≠ newTy := by
                          by_cases same : ext1 u = .prim .int
                          · have newEq : newTy = .prim .unit := by simp [newTy, same]
                            rw [newEq]
                            simp [same]
                          · have newEq : newTy = .prim .int := by simp [newTy, same]
                            rw [newEq]
                            exact same
                        obtain ⟨updated, updatedModels, updatedU, updatedAgree⟩ :=
                          MStore.Models.reassign checkedSafe.solutionsLeveled
                            checkedSafe.solutionsNormalized
                            (by simpa [checkedSafe.solutions_length] using
                              checkedSafe.solutionsBounded)
                            checkedModels uBounded uLookup newTyWF
                        have unsolvedAgree : ∀ id, checked.solutions.lookup id = none →
                            checked.solutions.levelOf id ≤ rigidCount → updated id = ext1 id := by
                          intro id lookupId levelId
                          by_cases same : id = u
                          · subst same
                            exact absurd levelId (by omega)
                          · exact updatedAgree id lookupId same
                        have stateAgree : ∀ id, id < checked.solutions.length →
                            checked.solutions.levelOf id ≤ rigidCount →
                              updated id = ext1 id :=
                          MStore.Models.agree_of_unsolved_agree
                            checkedSafe.solutionsLeveled
                            checkedSafe.solutionsNormalized
                            updatedModels checkedModels unsolvedAgree
                        have ctxExt1 : Ctx.realize ctx updated =
                            Ctx.realize ctx ext1 := by
                          apply Ctx.realize_congr
                          intro scheme member id idMem
                          have idLevel : checked.solutions.levelOf id ≤ rigidCount := by
                            have idBound : id < state.next :=
                              (ctxWF scheme member).2 id idMem
                            exact le_trans (checkedLevelLeState id idBound)
                              (ctxLevels scheme member id idMem)
                          have idAlloc : id < checked.solutions.length := by
                            rw [checkedSafe.solutions_length]
                            exact lt_of_lt_of_le ((ctxWF scheme member).2 id idMem)
                              stateLeChecked
                          exact stateAgree id idAlloc idLevel
                        have ext1Val : Ctx.realize ctx ext1 =
                            Ctx.realize ctx valuation :=
                          Ctx.realize_congr (fun scheme member id idMem =>
                            (rhsAgree id (lt_of_lt_of_le
                              ((ctxWF scheme member).2 id idMem) seededSafe.2.2.2.1)).trans
                              (seedAgree id ((ctxWF scheme member).2 id idMem)))
                        have updatedCtx : Ctx.realize ctx updated =
                            Ctx.realize ctx valuation :=
                          ctxExt1.trans ext1Val
                        have rhsUpdated : rhsResult.state.Models updated :=
                          (MStore.unify_sound unifiedRun updatedModels).1
                        have soundUpdated := (inferFuel_sound_model seededSafe.1
                          rhsCtxWF rhsCtxLevels openedRhsScoped rhsRun).2 updated rhsUpdated
                        have rhsTypingUpdated := soundUpdated.typing
                        have completedOpenRealizeUpdated :
                            completedOpen.realize updated = rhsResult.ty.realize updated := by
                          have applyEq := MStore.unify_apply_eq
                            rhsSafe.1.solutionsNormalized unifiedRun
                          rw [show completedOpen = unified.apply seeded.2 from rfl,
                            ← applyEq]
                          simpa [checked] using
                            (updatedModels.realize_apply rhsResult.ty)
                        have completedOpenRealizedWFUpdated :
                            (completedOpen.realize updated).WF inner 0 :=
                          Ty.realize_inferWF_model updatedModels
                            checkedSafe.solutions_length completedOpenWF
                            completedOpenLevelsInner
                        have openedMatchesUpdated : openedTemplate.Matches
                            (completedOpen.realize updated) := by
                          have seedEq := updatedModels.realize_apply seeded.2
                          have allocated := Template.allocate_matches_realize
                            (valuation := updated) (frontier := state.next)
                            openedTemplateScoped
                          simpa [seeded, completedOpen, seedEq] using allocated
                        let other : PolyTy :=
                          ⟨count, (completedOpen.realize updated).closeRigids
                            rigidCount count⟩
                        have otherMatches : SchemeTemplateMatches written other := by
                          constructor
                          · simp [other, count, PolyTy.realize]
                          · exact Template.matches_closeRigids writtenBodyScoped
                              completedOpenRealizedWFUpdated.1 openedMatchesUpdated
                        have otherWF : other.WF rigidCount := by
                          simpa [other] using
                            Ty.closeRigids_wf completedOpenRealizedWFUpdated
                        have otherOpen : other.openRigids rigidCount =
                            completedOpen.realize updated := by
                          simpa [other] using
                            PolyTy.openRigids_closeRigids completedOpenRealizedWFUpdated.1
                        have otherTyping : Typing sig inner (ctx.realize valuation)
                            (rhs.openRigids rigidCount count)
                            (other.openRigids rigidCount) := by
                          have base := rhsTypingUpdated
                          rw [updatedCtx] at base
                          simpa [countEq, otherOpen, completedOpenRealizeUpdated]
                            using base
                        have otherEq : other = scheme :=
                          huniq other otherMatches otherWF otherTyping
                        have completedOpenExt1 : completedOpen.realize ext1 =
                            scheme.openRigids rigidCount := by
                          rw [show completedOpen = checked.solutions.apply seeded.2 from rfl,
                            checkedModels.realize_apply seeded.2]
                          exact seededExt
                        have different : completedOpen.realize updated ≠
                            completedOpen.realize ext1 :=
                          Ty.realize_ne_of_mem_mvars hu (by
                            rw [updatedU]
                            exact Ne.symm newTyDifferent)
                        have contradiction : False := by
                          have openEq := congrArg
                            (fun scheme => scheme.openRigids rigidCount) otherEq
                          change other.openRigids rigidCount =
                            scheme.openRigids rigidCount at openEq
                          rw [otherOpen, ← completedOpenExt1] at openEq
                          exact different openEq
                        exact contradiction.elim
                      have good : completedOpen.mvars.all
                          (fun id => checked.solutions.levelOf id ≤ rigidCount) = true := by
                        by_cases hzero : scheme.paramCount = 0
                        · have countZero : count = 0 := by omega
                          have innerEq : inner = rigidCount := by
                            simp [inner, countZero]
                          apply List.all_eq_true.mpr
                          intro id mem
                          simpa [innerEq] using completedOpenLevelsInner id mem
                        · exact goodNonzero hzero
                      have completedOpenLevelsRigid : completedOpen.LevelBounded
                          checked.solutions rigidCount := by
                        simpa [Ty.LevelBounded] using (List.all_eq_true.mp good)
                      have completedBodyScoped :
                          completed.body.Scoped rigidCount count := by
                        simpa [completed, inner] using
                          Ty.closeRigids_scoped_zero completedOpenWF.1
                      have completedBodyBounded :
                          completed.body.MVarBounded checked.next := by
                        simpa [completed] using
                          Ty.closeRigids_mvarBounded completedOpenWF.2
                      have completedInferWF : completed.InferWF
                          rigidCount checked.next :=
                        ⟨completedBodyScoped, completedBodyBounded⟩
                      have completedLevels : completed.body.LevelBounded
                          checked.solutions rigidCount := by
                        simpa [completed] using
                          Ty.closeRigids_levelBounded completedOpenLevelsRigid
                      have ctxWFChecked : ctx.InferWF rigidCount checked.next :=
                        Ctx.InferWF.mono_frontier ctxWF localStartLe
                      have ctxLevelsChecked :
                          ∀ scheme ∈ ctx, scheme.body.LevelBounded
                            checked.solutions rigidCount := by
                        intro scheme member id hid
                        have idBound : id < state.next :=
                          (ctxWF scheme member).2 id hid
                        exact le_trans (checkedLevelLeState id idBound)
                          (ctxLevels scheme member id hid)
                      have bodyCtxWF : Ctx.InferWF (completed :: ctx)
                          rigidCount checked.next := by
                        intro scheme member
                        simp only [List.mem_cons] at member
                        rcases member with rfl | member
                        · exact completedInferWF
                        · exact ctxWFChecked scheme member
                      have bodyCtxLevels :
                          ∀ scheme ∈ completed :: ctx,
                            scheme.body.LevelBounded checked.solutions rigidCount := by
                        intro scheme member
                        simp only [List.mem_cons] at member
                        rcases member with rfl | member
                        · exact completedLevels
                        · exact ctxLevelsChecked scheme member
                      have completedOpenRealizeExt1 : completedOpen.realize ext1 =
                          scheme.openRigids rigidCount := by
                        rw [show completedOpen = checked.solutions.apply seeded.2 from rfl,
                          checkedModels.realize_apply seeded.2]
                        exact seededExt
                      have completedOpenRealizedWF : (completedOpen.realize ext1).WF inner 0 :=
                        Ty.realize_inferWF_model checkedModels
                          checkedSafe.solutions_length completedOpenWF
                          completedOpenLevelsInner
                      have imagesScoped : ∀ id ∈ completedOpen.mvars,
                          (ext1 id).Scoped rigidCount 0 :=
                        MStore.Models.images_scoped checkedModels
                          checkedSafe.solutions_length completedOpenWF.2
                          completedOpenLevelsRigid
                      have completedRealizeExt1 : completed.realize ext1 =
                          ⟨count, (completedOpen.realize ext1).closeRigids
                            rigidCount count⟩ := by
                        simp only [completed, PolyTy.realize]
                        rw [Ty.realize_closeRigids imagesScoped]
                      have completedOpenEqExt1 :
                          (completed.realize ext1).openRigids rigidCount =
                            completedOpen.realize ext1 := by
                        rw [completedRealizeExt1]
                        exact PolyTy.openRigids_closeRigids completedOpenRealizedWF.1
                      have openedMatchesExt1 : openedTemplate.Matches
                          (completedOpen.realize ext1) := by
                        have seedEq := checkedModels.realize_apply seeded.2
                        have allocated := Template.allocate_matches_realize
                          (valuation := ext1) (frontier := state.next)
                          openedTemplateScoped
                        simpa [seeded, completedOpen, seedEq] using allocated
                      have closedMatchesExt1 := Template.matches_closeRigids
                        writtenBodyScoped completedOpenRealizedWF.1 openedMatchesExt1
                      have schemeMatchesCompleted : SchemeTemplateMatches written
                          (completed.realize ext1) := by
                        constructor
                        · simp [completed, count, PolyTy.realize]
                        · rw [completedRealizeExt1]
                          exact closedMatchesExt1
                      have completedWFExt1 : (completed.realize ext1).WF rigidCount := by
                        rw [completedRealizeExt1]
                        exact Ty.closeRigids_wf completedOpenRealizedWF
                      have completedTypingExt1 : Typing sig inner (ctx.realize valuation)
                          (rhs.openRigids rigidCount count)
                          ((completed.realize ext1).openRigids rigidCount) := by
                        have base := Elaborates.typing rhsElaborates
                        simpa [countEq, completedOpenEqExt1,
                          completedOpenRealizeExt1] using base
                      have completedEqExt1 : completed.realize ext1 = scheme := by
                        rw [completedRealizeExt1, completedOpenRealizeExt1]
                        cases scheme with
                        | mk schemeCount schemeBody =>
                            have countEq' : count = schemeCount :=
                              schemeMatches.paramCount_eq.symm
                            have scopedCount : schemeBody.Scoped
                                rigidCount count := by
                              rw [countEq']
                              exact schemeWF.1
                            have closeOpen : (schemeBody.openRigidsFrom 0
                                rigidCount count).closeRigids rigidCount count =
                                  schemeBody :=
                              Ty.closeRigids_openRigids scopedCount
                            rw [targetEq]
                            simp only [Scheme.mk.injEq]
                            constructor
                            · exact countEq'
                            · simpa [countEq'] using closeOpen
                      have bodyElaborates' : Elaborates sig rigidCount
                          (Ctx.realize (completed :: ctx) ext1)
                          body bodyElabD ty := by
                        have ctxEq : Ctx.realize (completed :: ctx) ext1 =
                            scheme :: Ctx.realize ctx valuation := by
                          change completed.realize ext1 :: Ctx.realize ctx ext1 =
                            scheme :: Ctx.realize ctx valuation
                          rw [completedEqExt1]
                          congr 1
                          exact Ctx.realize_congr (fun s m id hid =>
                            (rhsAgree id (lt_of_lt_of_le
                              ((ctxWF s m).2 id hid) seededSafe.2.2.2.1)).trans
                              (seedAgree id ((ctxWF s m).2 id hid)))
                        rwa [ctxEq]
                      obtain ⟨bodyResult, bodyRun⟩ :=
                        ih checkedSafe bodyCtxWF bodyCtxLevels bodyScoped
                          bodyEnough checkedModels bodyElaborates'
                      refine ⟨⟨bodyResult.state, bodyResult.ty,
                        .letIn (some completed) rhsResult.elaborated
                          bodyResult.elaborated⟩, ?_⟩
                      simp [inferFuel, seeded, openedTemplate, count, inner, completed,
                        completedOpen, checked, rhsRun, InferState.constrain, unifiedRun,
                        good, bodyRun]
                      simpa [completedOpen, checked, seeded, InferState.allocate]
                        using (List.all_eq_true.mp good)
      | fix ann body =>
          cases inputScoped with
          | fix annScoped bodyScoped =>
              cases elaborates with
              | fix selfWF annMatches bodyElaborates =>
                  rename_i bodyElabD
                  have bodyEnough : body.inferSize < fuel := by
                    simp [Expr.inferSize] at enough
                    omega
                  let seeded := state.allocate rigidCount ann
                  have seededSafe := InferState.allocate_safe
                    (level := rigidCount) (rigidCount := rigidCount)
                    stateSafe annScoped
                  obtain ⟨holeVal, holeAgree, holeRealize, holeWF⟩ :=
                    Template.allocate_realizes
                      (template := ann) (rigid := rigidCount) (binder := 0)
                      (frontier := state.next) (target := ty)
                      (base := valuation) annMatches annScoped selfWF
                  obtain ⟨firstValuation, seedModels, seedAgree, seedRealizeEq⟩ :=
                    InferState.allocate_models stateSafe models annScoped
                      (assigned := holeVal) holeWF
                  have seedRealize : seeded.2.realize firstValuation = ty := by
                    simpa [seeded] using seedRealizeEq.trans holeRealize
                  have bodyCtxWF : Ctx.InferWF (PolyTy.mono seeded.2 :: ctx)
                      rigidCount seeded.1.next := by
                    intro scheme member
                    simp only [List.mem_cons] at member
                    rcases member with rfl | member
                    · exact seededSafe.2.1
                    · exact Ctx.InferWF.mono_frontier ctxWF
                        seededSafe.2.2.2.1 scheme member
                  have bodyCtxLevels :
                      ∀ scheme ∈ PolyTy.mono seeded.2 :: ctx,
                        scheme.body.LevelBounded seeded.1.solutions rigidCount := by
                    intro scheme member
                    simp only [List.mem_cons] at member
                    rcases member with rfl | member
                    · exact seededSafe.2.2.1
                    · intro id hid
                      have idBound : id < state.next :=
                        (ctxWF scheme member).2 id hid
                      rw [seededSafe.2.2.2.2 id idBound]
                      exact ctxLevels scheme member id hid
                  have bodyElaborates' : Elaborates sig rigidCount
                      (Ctx.realize (PolyTy.mono seeded.2 :: ctx) firstValuation)
                      body bodyElabD ty := by
                    have ctxEq : Ctx.realize (PolyTy.mono seeded.2 :: ctx)
                        firstValuation =
                        PolyTy.mono ty :: Ctx.realize ctx valuation := by
                      change PolyTy.mono (seeded.2.realize firstValuation) ::
                          Ctx.realize ctx firstValuation =
                        PolyTy.mono ty :: Ctx.realize ctx valuation
                      rw [seedRealize]
                      congr 1
                      exact Ctx.realize_congr (fun s m id hid =>
                        seedAgree id ((ctxWF s m).2 id hid))
                    rwa [ctxEq]
                  obtain ⟨bodyResult, bodyRun⟩ :=
                    ih seededSafe.1 bodyCtxWF bodyCtxLevels bodyScoped bodyEnough
                      seedModels bodyElaborates'
                  have bodySafe := inferFuel_safe seededSafe.1 bodyCtxWF
                    bodyCtxLevels bodyScoped bodyRun
                  obtain ⟨ext1, bodyModels, bodyAgree, _, bodyTyEq, _⟩ :=
                    inferFuel_principal_elab_aux seededSafe.1 bodyCtxWF bodyCtxLevels
                      bodyScoped bodyRun seedModels bodyElaborates'
                  have seededExt : seeded.2.realize ext1 = ty := by
                    rw [show seeded.2.realize ext1 =
                        seeded.2.realize firstValuation by
                      apply Ty.realize_congr
                      intro id member
                      exact bodyAgree id (seededSafe.2.1.2 id member)]
                    exact seedRealize
                  have selfWFAtBody : seeded.2.InferWF rigidCount 0
                      bodyResult.state.next :=
                    Ty.InferWF.mono_frontier seededSafe.2.1 bodySafe.2.2.2.1
                  have selfLevelsBody : seeded.2.LevelBounded
                      bodyResult.state.solutions rigidCount :=
                    Ty.LevelBounded.mono_le_on seededSafe.2.2.1 (fun id member =>
                      bodySafe.2.2.2.2 id (seededSafe.2.1.2 id member))
                  have unifies : bodyResult.ty.realize ext1 =
                      seeded.2.realize ext1 :=
                    bodyTyEq.trans seededExt.symm
                  obtain ⟨unified, unifiedRun, _⟩ :=
                    MStore.unify_complete
                      (store := bodyResult.state.solutions)
                      (left := bodyResult.ty) (right := seeded.2)
                      (valuation := ext1)
                      bodySafe.1.solutionsNormalized
                      (by simpa [bodySafe.1.solutions_length] using
                        bodySafe.1.solutionsBounded)
                      (by simpa [bodySafe.1.solutions_length] using
                        bodySafe.2.1.2)
                      (by simpa [bodySafe.1.solutions_length] using
                        selfWFAtBody.2)
                      bodyModels unifies
                  refine ⟨⟨{ bodyResult.state with solutions := unified },
                    ({ bodyResult.state with solutions := unified }).solutions.apply seeded.2,
                    .fix seeded.2 bodyResult.elaborated⟩, ?_⟩
                  simp [inferFuel, seeded, bodyRun, InferState.constrain, unifiedRun]

private theorem infer_run_data {input : Source} {result : InferenceResult}
    (run : infer sig input = some result) :
    ∃ internal : InferResult,
      inferFuel sig (input.inferSize + 1) 0 [] input ⟨0, []⟩ = some internal ∧
      result.ty = internal.state.solutions.apply internal.ty ∧
      result.elaborated =
        internal.state.solutions.applyExpr internal.elaborated ∧
      Ty.wfB 0 0 (internal.state.solutions.apply internal.ty) = true ∧
      (∀ ty ∈ (internal.state.solutions.applyExpr internal.elaborated).annotations,
        ty.MetaFree) ∧
      input.TypeScoped 0 0 := by
  unfold infer at run
  by_cases sourceBad : (!input.typeScopedB 0 0) = true
  · rw [if_pos sourceBad] at run
    simp at run
  · rw [if_neg sourceBad] at run
    have sourceScopedB : input.typeScopedB 0 0 = true := by
      cases h : input.typeScopedB 0 0 <;> simp_all
    have inputScoped : input.TypeScoped 0 0 :=
      Expr.typeScopedB_eq_true_iff.mp sourceScopedB
    cases internalRun : inferFuel sig (input.inferSize + 1) 0 [] input ⟨0, []⟩ with
    | none => simp [internalRun] at run
    | some internal =>
        rw [internalRun] at run
        by_cases finalGood : (Ty.wfB 0 0 (internal.state.solutions.apply internal.ty) &&
            (internal.state.solutions.applyExpr internal.elaborated).annotations.all
              Ty.metaFreeB) = true
        · simp at run
          rcases run with ⟨guardParts, resultEq⟩
          subst result
          exact ⟨internal, rfl, rfl, rfl, guardParts.1,
            fun ty member => Ty.metaFreeB_eq_true_iff.mp (guardParts.2 ty member),
            inputScoped⟩
        · simp at run
          exact False.elim (finalGood (by
            rw [Bool.and_eq_true, List.all_eq_true]
            exact run.1))

/-- An accepted program has exactly one type. -/
theorem infer_type_unique
    {input : Source} {result : InferenceResult} {ty : Ty}
    (run : infer sig input = some result)
    (typing : Typing sig 0 [] input ty) :
    ty = result.ty := by
  obtain ⟨internal, internalRun, publicTyEq, _, publicWFb, _, inputScoped⟩ :=
    infer_run_data run
  have internalSafe := inferFuel_safe InferState.initial_safe
    (by simp [Ctx.InferWF]) (by intro scheme member; simp at member)
    inputScoped internalRun
  have emptyCtxWF : Ctx.InferWF [] 0 0 := by simp [Ctx.InferWF]
  have emptyCtxLevels : ∀ scheme ∈ ([] : Ctx),
      scheme.body.LevelBounded (⟨0, []⟩ : InferState).solutions 0 := by
    intro scheme member
    simp at member
  obtain ⟨valuation, models⟩ := InferState.has_model InferState.initial_safe
  obtain ⟨extended, extendedModels, _, extendedTy⟩ :=
    inferFuel_principal InferState.initial_safe emptyCtxWF emptyCtxLevels
      inputScoped internalRun models typing
  have publicWF : (internal.state.solutions.apply internal.ty).WF 0 0 :=
    Ty.wfB_eq_true_iff.mp publicWFb
  have applyEq := extendedModels.realize_apply internal.ty
  have realizeSelf := Ty.realize_eq_self publicWF.2 extended
  rw [publicTyEq]
  rw [← extendedTy, ← applyEq, realizeSelf]

/-- Soundness and completeness: `infer` accepts exactly the programs with a
unique elaboration and type, and returns them. -/
theorem infer_eq_some_iff {input : Source} {result : InferenceResult} :
    infer sig input = some result ↔
      Elaborates sig 0 [] input result.elaborated result.ty ∧
        ∀ elaborated ty, Elaborates sig 0 [] input elaborated ty →
          elaborated = result.elaborated ∧ ty = result.ty := by
  constructor
  · intro run
    refine ⟨infer_sound run, ?_⟩
    intro elaborated tyD elaborates
    obtain ⟨internal, internalRun, publicTyEq, publicElabEq, publicWFb,
      publicAnn, inputScoped⟩ := infer_run_data run
    have initialSafe : (⟨0, []⟩ : InferState).Safe := InferState.initial_safe
    have emptyCtxWF : Ctx.InferWF [] 0 0 := by simp [Ctx.InferWF]
    have emptyCtxLevels : ∀ scheme ∈ ([] : Ctx),
        scheme.body.LevelBounded (⟨0, []⟩ : InferState).solutions 0 := by
      intro scheme member
      simp at member
    obtain ⟨valuation, models⟩ := InferState.has_model initialSafe
    obtain ⟨extended, extendedModels, _, elabExt, tyExt⟩ :=
      inferFuel_principal_elab initialSafe emptyCtxWF emptyCtxLevels inputScoped
        internalRun models elaborates
    have publicWF : (internal.state.solutions.apply internal.ty).WF 0 0 :=
      Ty.wfB_eq_true_iff.mp publicWFb
    have publicElabSelf : (internal.state.solutions.applyExpr internal.elaborated).realize extended =
        internal.state.solutions.applyExpr internal.elaborated :=
      Expr.realize_eq_self_of_annotations (valuation := extended) publicAnn
    have applyRel := Expr.realize_applyExpr extendedModels internal.elaborated
    have publicElabEq' : internal.state.solutions.applyExpr internal.elaborated =
        elaborated := by
      rw [← publicElabSelf, applyRel, elabExt]
    constructor
    · rw [publicElabEq, ← publicElabEq']
    · exact infer_type_unique run (Elaborates.typing elaborates)
  · rintro ⟨baseElaborates, unique⟩
    have inputScoped : input.TypeScoped 0 0 :=
      Typing.sourceScoped (Elaborates.typing baseElaborates)
    have initialSafe : (⟨0, []⟩ : InferState).Safe := InferState.initial_safe
    have emptyCtxWF : Ctx.InferWF [] 0 0 := by simp [Ctx.InferWF]
    have emptyCtxLevels : ∀ scheme ∈ ([] : Ctx),
        scheme.body.LevelBounded (⟨0, []⟩ : InferState).solutions 0 := by
      intro scheme member
      simp at member
    obtain ⟨valuation, models⟩ := InferState.has_model initialSafe
    obtain ⟨internal, internalRun⟩ :=
      inferFuel_complete (fuel := input.inferSize + 1) initialSafe emptyCtxWF
        emptyCtxLevels inputScoped (by omega) models baseElaborates
    have internalSafe := inferFuel_safe initialSafe emptyCtxWF emptyCtxLevels
      inputScoped internalRun
    obtain ⟨extended, extendedModels, _, elabExt, tyExt, annBound⟩ :=
      inferFuel_principal_elab_aux initialSafe emptyCtxWF emptyCtxLevels
        inputScoped internalRun models baseElaborates
    have applied := MStore.apply_inferWF internalSafe.1.solutionsLeveled
      internalSafe.1.solutionsBounded internalSafe.2.1 internalSafe.2.2.1
    have publicMvarsNil : (internal.state.solutions.apply internal.ty).mvars = [] := by
      apply List.eq_nil_iff_forall_not_mem.mpr
      intro u member
      have uLookup := MStore.lookup_none_of_mem_apply_mvars
        internalSafe.1.solutionsNormalized member
      have uBounded : u < internal.state.solutions.length := by
        have bounded := MStore.apply_mvarBounded
          (store := internal.state.solutions) (ty := internal.ty)
          (frontier := internal.state.next) internalSafe.1.solutionsBounded
          internalSafe.2.1.2
        have := bounded u member
        simpa [internalSafe.1.solutions_length] using this
      obtain ⟨updated, updatedModels, updatedDifferent, updatedAgree⟩ :=
        MStore.exists_different_model internalSafe.1.solutionsLeveled
          internalSafe.1.solutionsNormalized
          (by simpa [internalSafe.1.solutions_length] using
            internalSafe.1.solutionsBounded)
          extendedModels uBounded uLookup
      have sound := (inferFuel_sound_model initialSafe emptyCtxWF emptyCtxLevels
        inputScoped internalRun).2 updated updatedModels
      have uniqueTy := (unique _ _ sound).2
      have realizeNe : (internal.ty.realize updated) ≠
          (internal.ty.realize extended) := by
        rw [← updatedModels.realize_apply internal.ty,
          ← extendedModels.realize_apply internal.ty]
        exact Ty.realize_ne_of_mem_mvars member updatedDifferent
      exact realizeNe (uniqueTy.trans tyExt.symm)
    have publicMetaFree := Ty.metaFree_of_mvars_eq_nil publicMvarsNil
    have publicWF : (internal.state.solutions.apply internal.ty).WF 0 0 :=
      ⟨applied.1.1, publicMetaFree⟩
    have publicAnn : ∀ annotation ∈
        (internal.state.solutions.applyExpr internal.elaborated).annotations,
        annotation.MetaFree := by
      intro annotation member
      apply Ty.metaFree_of_mvars_eq_nil
      apply List.eq_nil_iff_forall_not_mem.mpr
      intro u uMem
      have mapped : annotation ∈
          internal.elaborated.annotations.map internal.state.solutions.apply := by
        simpa [MStore.applyExpr, Expr.annotations_mapAnn] using member
      rcases List.mem_map.mp mapped with ⟨original, originalMem, rfl⟩
      have uBoundedNext := MStore.apply_mvarBounded
        (store := internal.state.solutions) (ty := original)
        (frontier := internal.state.next) internalSafe.1.solutionsBounded
        (annBound original originalMem) u uMem
      have uBounded : u < internal.state.solutions.length := by
        simpa [internalSafe.1.solutions_length] using uBoundedNext
      have uLookup := MStore.lookup_none_of_mem_apply_mvars
        internalSafe.1.solutionsNormalized uMem
      obtain ⟨updated, updatedModels, updatedDifferent, updatedAgree⟩ :=
        MStore.exists_different_model (valuation := extended)
          internalSafe.1.solutionsLeveled
          internalSafe.1.solutionsNormalized
          (by simpa [internalSafe.1.solutions_length] using
            internalSafe.1.solutionsBounded)
          extendedModels uBounded uLookup
      have sound := (inferFuel_sound_model initialSafe emptyCtxWF emptyCtxLevels
        inputScoped internalRun).2 updated updatedModels
      have uniqueElab := (unique _ _ sound).1
      have neApply : internal.elaborated.realize updated ≠
          internal.elaborated.realize extended := by
        rw [← Expr.realize_applyExpr updatedModels internal.elaborated,
          ← Expr.realize_applyExpr extendedModels internal.elaborated]
        exact Expr.realize_ne_of_annotation_mvars
          ⟨internal.state.solutions.apply original, member, uMem⟩ updatedDifferent
      exact neApply (by rw [uniqueElab, elabExt])
    have publicWFb : Ty.wfB 0 0 (internal.state.solutions.apply internal.ty) = true :=
      Ty.wfB_eq_true_iff.mpr publicWF
    have publicAnnB : (internal.state.solutions.applyExpr
        internal.elaborated).annotations.all Ty.metaFreeB = true :=
      List.all_eq_true.mpr (fun annotation member =>
        Ty.metaFreeB_eq_true_iff.mpr (publicAnn annotation member))
    have resultTyEq : internal.state.solutions.apply internal.ty = result.ty := by
      calc
        internal.state.solutions.apply internal.ty =
            (internal.state.solutions.apply internal.ty).realize extended :=
          (Ty.realize_eq_self publicWF.2 extended).symm
        _ = internal.ty.realize extended :=
          extendedModels.realize_apply internal.ty
        _ = result.ty := tyExt
    have resultElabEq : internal.state.solutions.applyExpr internal.elaborated =
        result.elaborated := by
      calc
        internal.state.solutions.applyExpr internal.elaborated =
            (internal.state.solutions.applyExpr internal.elaborated).realize
              extended :=
          (Expr.realize_eq_self_of_annotations (valuation := extended) publicAnn).symm
        _ = internal.elaborated.realize extended :=
          Expr.realize_applyExpr extendedModels internal.elaborated
        _ = result.elaborated := elabExt
    have sourceScopedB : input.typeScopedB 0 0 = true :=
      Expr.typeScopedB_eq_true_iff.mpr inputScoped
    unfold infer
    rw [if_neg (by simpa using sourceScopedB)]
    simp [internalRun, resultTyEq, resultElabEq]
    constructor
    · rw [← resultTyEq]
      exact publicWFb
    · intro annotation member
      exact List.all_eq_true.mp publicAnnB annotation (by
        rwa [← resultElabEq] at member)

/-- `infer` rejects exactly the programs without a unique elaboration. -/
theorem infer_eq_none_iff {input : Source} :
    infer sig input = none ↔
      ¬ ∃ elaborated ty, Elaborates sig 0 [] input elaborated ty ∧
        ∀ elaborated' ty', Elaborates sig 0 [] input elaborated' ty' →
          elaborated' = elaborated ∧ ty' = ty := by
  constructor
  · intro noneRun
    rintro ⟨elaborated, ty, elaborates, unique⟩
    have someRun : infer sig input = some ⟨ty, elaborated⟩ :=
      infer_eq_some_iff.mpr ⟨elaborates, unique⟩
    rw [noneRun] at someRun
    exact Option.noConfusion someRun
  · intro notExists
    cases run : infer sig input with
    | none => rfl
    | some result =>
        have data := infer_eq_some_iff.mp run
        exact absurd ⟨result.elaborated, result.ty, data.1, data.2⟩ notExists

end EPL
