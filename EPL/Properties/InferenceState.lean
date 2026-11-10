import EPL.Properties.AnnotationAllocation
import EPL.Properties.InferenceScope
import EPL.Properties.UnificationBounded
import EPL.Properties.UnificationScope
import EPL.Properties.UnificationSound

namespace EPL

/-- Algorithmic types are rigid/bound scoped and mention only allocated
metavariables. Unlike declarative `Ty.WF`, they may still be flexible. -/
def Ty.InferWF
    (ty : Ty) (rigidCount binderCount frontier : Nat) : Prop :=
  ty.Scoped rigidCount binderCount ∧ ty.MVarBounded frontier

def PolyTy.InferWF
    (scheme : PolyTy) (rigidCount frontier : Nat) : Prop :=
  scheme.body.InferWF rigidCount scheme.paramCount frontier

def Ctx.InferWF (ctx : Ctx) (rigidCount frontier : Nat) : Prop :=
  ∀ scheme ∈ ctx, scheme.InferWF rigidCount frontier

def MStore.Scoped (store : MStore) (rigidCount : Nat) : Prop :=
  ∀ ty ∈ store, ty.Scoped rigidCount 0

def MStore.Bounded (store : MStore) (frontier : Nat) : Prop :=
  ∀ ty ∈ store, ty.MVarBounded frontier

def MStore.Normalized (store : MStore) : Prop :=
  ∀ ty ∈ store, store.apply ty = ty

/-- The dense solution table agrees with its allocation frontier, contains no
out-of-scope or forged type, and tracks only allocated obligations. -/
structure InferState.Safe (state : InferState) (rigidCount : Nat) : Prop where
  solutions_length : state.solutions.length = state.next
  solutionsScoped : state.solutions.Scoped rigidCount
  solutionsBounded : state.solutions.Bounded state.next
  solutionsNormalized : state.solutions.Normalized
  requiredBounded : ∀ id ∈ state.required, id < state.next

theorem MStore.apply_inferWF
    {store : MStore} {ty : Ty} {rigidCount binderCount frontier : Nat}
    (storeScoped : store.Scoped rigidCount)
    (storeBounded : store.Bounded frontier)
    (typeWF : ty.InferWF rigidCount binderCount frontier) :
    (store.apply ty).InferWF rigidCount binderCount frontier := by
  have scoped_mono_binder :
      ∀ {candidate : Ty}, candidate.Scoped rigidCount 0 →
        candidate.Scoped rigidCount binderCount := by
    intro candidate h
    induction h with
    | prim => exact .prim
    | arrow _ _ ihDomain ihCodomain => exact .arrow ihDomain ihCodomain
    | bvar hlt => omega
    | rigid hlt => exact .rigid hlt
    | mvar id => exact .mvar id
  induction ty generalizing binderCount with
  | prim name =>
      exact ⟨.prim, by
        intro id member
        simp [MStore.apply, Ty.mvars] at member⟩
  | arrow domain codomain ihDomain ihCodomain =>
      have scopedParts :
          domain.Scoped rigidCount binderCount ∧
            codomain.Scoped rigidCount binderCount := by
        cases typeWF.1 with
        | arrow hDomain hCodomain => exact ⟨hDomain, hCodomain⟩
      have domainWF : domain.InferWF rigidCount binderCount frontier := by
        exact ⟨scopedParts.1, fun id member =>
          typeWF.2 id (by simp [Ty.mvars, member])⟩
      have codomainWF : codomain.InferWF rigidCount binderCount frontier := by
        exact ⟨scopedParts.2, fun id member =>
          typeWF.2 id (by simp [Ty.mvars, member])⟩
      have domainResult := ihDomain domainWF scoped_mono_binder
      have codomainResult := ihCodomain codomainWF scoped_mono_binder
      constructor
      · exact .arrow domainResult.1 codomainResult.1
      · intro id member
        simp only [MStore.apply, Ty.mvars, List.mem_dedup,
          List.mem_append] at member
        rcases member with member | member
        · exact domainResult.2 id member
        · exact codomainResult.2 id member
  | bvar index =>
      exact ⟨typeWF.1, by
        intro id member
        simp [MStore.apply, Ty.mvars] at member⟩
  | rigid level =>
      exact ⟨typeWF.1, by
        intro id member
        simp [MStore.apply, Ty.mvars] at member⟩
  | mvar id =>
      cases hget : store[id]? with
      | none =>
          simpa [MStore.apply, hget] using typeWF
      | some result =>
          have member : result ∈ store := List.mem_of_getElem? hget
          simpa [MStore.apply, hget] using
            And.intro (scoped_mono_binder (storeScoped result member))
              (storeBounded result member)

theorem InferState.initial_safe {rigidCount : Nat} :
    (⟨0, [], []⟩ : InferState).Safe rigidCount := by
  constructor <;> simp [MStore.Scoped, MStore.Bounded, MStore.Normalized]

theorem InferState.fresh_safe
    {state : InferState} {rigidCount : Nat}
    (safe : state.Safe rigidCount) :
    state.fresh.1.Safe rigidCount ∧
      state.fresh.2.InferWF rigidCount 0 state.fresh.1.next ∧
      state.next ≤ state.fresh.1.next := by
  rcases safe with ⟨length, storeScoped, bounded, normalized, required⟩
  have apply_append_identity :
      ∀ {ty : Ty}, ty.MVarBounded state.next →
        (state.solutions ++ [Ty.mvar state.next]).apply ty =
          state.solutions.apply ty := by
    intro ty typeBounded
    induction ty with
    | prim name => rfl
    | arrow domain codomain ihDomain ihCodomain =>
        simp only [MStore.apply]
        rw [ihDomain (by
          intro id member
          exact typeBounded id (by simp [Ty.mvars, member]))]
        rw [ihCodomain (by
          intro id member
          exact typeBounded id (by simp [Ty.mvars, member]))]
    | bvar index => rfl
    | rigid level => rfl
    | mvar id =>
        have idBounded : id < state.next :=
          typeBounded id (by simp [Ty.mvars])
        have idInSolutions : id < state.solutions.length := by
          simpa [length] using idBounded
        simp only [MStore.apply]
        rw [List.getElem?_append_left idInSolutions]
  simp only [InferState.fresh]
  refine ⟨?_, ?_, by omega⟩
  · refine ⟨by simp [length], ?_, ?_, ?_, ?_⟩
    · intro ty member
      rcases List.mem_append.mp member with old | new
      · exact storeScoped ty old
      · simp only [List.mem_singleton] at new
        subst ty
        exact .mvar _
    · intro ty member
      rcases List.mem_append.mp member with old | new
      · intro id idMember
        exact Nat.lt_succ_of_lt (bounded ty old id idMember)
      · simp only [List.mem_singleton] at new
        subst ty
        intro id idMember
        simp only [Ty.mvars, List.mem_singleton] at idMember
        subst id
        change state.next < state.next + 1
        omega
    · intro ty member
      rcases List.mem_append.mp member with old | new
      · rw [apply_append_identity (bounded ty old), normalized ty old]
      · simp only [List.mem_singleton] at new
        subst ty
        simp [MStore.apply, length]
    · intro id member
      exact Nat.lt_succ_of_lt (required id member)
  · exact ⟨.mvar _, by
      intro id member
      simp only [Ty.mvars, List.mem_singleton] at member
      subst id
      omega⟩

theorem InferState.freshRequired_safe
    {state : InferState} {rigidCount : Nat}
    (safe : state.Safe rigidCount) :
    state.freshRequired.1.Safe rigidCount ∧
      state.freshRequired.2.InferWF rigidCount 0
        state.freshRequired.1.next ∧
      state.next ≤ state.freshRequired.1.next := by
  have ordinary := InferState.fresh_safe safe
  refine ⟨?_, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [InferState.freshRequired, InferState.fresh] using
        ordinary.1.solutions_length
    · simpa [InferState.freshRequired, InferState.fresh] using
        ordinary.1.solutionsScoped
    · simpa [InferState.freshRequired, InferState.fresh] using
        ordinary.1.solutionsBounded
    · simpa [InferState.freshRequired, InferState.fresh] using
        ordinary.1.solutionsNormalized
    · intro id member
      simp only [InferState.freshRequired, List.mem_cons] at member ⊢
      rcases member with rfl | old
      · omega
      · exact Nat.lt_succ_of_lt (safe.requiredBounded id old)
  · simpa [InferState.freshRequired, InferState.fresh] using ordinary.2.1
  · simp [InferState.freshRequired]

theorem InferState.freshMany_safe
    {state : InferState} {rigidCount count : Nat}
    (safe : state.Safe rigidCount) :
    (state.freshMany count).1.Safe rigidCount ∧
      (∀ ty ∈ (state.freshMany count).2,
        ty.InferWF rigidCount 0 (state.freshMany count).1.next) ∧
      (state.freshMany count).2.length = count ∧
      state.next ≤ (state.freshMany count).1.next := by
  have inferWF_mono :
      ∀ {ty : Ty} {smaller larger : Nat},
        ty.InferWF rigidCount 0 smaller → smaller ≤ larger →
          ty.InferWF rigidCount 0 larger := by
    intro ty smaller larger wf le
    exact ⟨wf.1, fun id member => lt_of_lt_of_le (wf.2 id member) le⟩
  induction count generalizing state with
  | zero =>
      simp only [InferState.freshMany]
      refine ⟨safe, ?_, rfl, le_refl state.next⟩
      intro ty member
      simp at member
  | succ count ih =>
      have first := InferState.fresh_safe safe
      have rest := ih first.1
      simp only [InferState.freshMany]
      refine ⟨rest.1, ?_, ?_, le_trans first.2.2 rest.2.2.2⟩
      · intro ty member
        simp only [List.mem_cons] at member
        rcases member with rfl | member
        · exact inferWF_mono first.2.1 rest.2.2.2
        · exact rest.2.1 ty member
      · simp [rest.2.2.1]

/-- Allocation never moves its frontier backwards. -/
theorem Template.allocate_next_le
    (template : Template) (frontier : Nat) :
    frontier ≤ (template.allocate frontier).next := by
  have allocateWith_next_le :
      ∀ (candidate : Template) (holes : HoleAssignment) (start : Nat),
        start ≤ (candidate.allocateWith holes start).1 := by
    intro candidate
    induction candidate with
    | fixed ty =>
        intro holes start
        simp [Template.allocateWith]
    | hole =>
        intro holes start
        simp [Template.allocateWith]
    | named name =>
        intro holes start
        simp [Template.allocateWith]
    | arrow domain codomain ihDomain ihCodomain =>
        intro holes start
        simp only [Template.allocateWith]
        exact le_trans (ihDomain holes start)
          (ihCodomain holes (domain.allocateWith holes start).1)
  simp only [Template.allocate]
  exact le_trans (Nat.le_add_right frontier _)
    (allocateWith_next_le template
      (namedHoleTable template.names.dedup frontier)
      (frontier + template.names.dedup.length))

/-- Under a valid authored template, every metavariable in the allocated type
belongs to the fresh interval reserved by this allocation. -/
theorem Template.allocate_mvars
    {template : Template} {rigidCount binderCount frontier : Nat}
    (templateScoped : template.Scoped rigidCount binderCount) :
    ∀ id ∈ (template.allocate frontier).ty.mvars,
      frontier ≤ id ∧ id < (template.allocate frontier).next := by
  have metaFree_mvars : ∀ {ty : Ty}, ty.MetaFree → ty.mvars = [] := by
    intro ty h
    induction h with
    | prim => rfl
    | arrow _ _ ihDomain ihCodomain => simp [Ty.mvars, ihDomain, ihCodomain]
    | bvar => rfl
    | rigid => rfl
  have lookup_bound :
      ∀ {holes : HoleAssignment} {name : String} {ty : Ty} {limit : Nat},
        (∀ entry ∈ holes, ∀ id ∈ entry.2.mvars,
          frontier ≤ id ∧ id < limit) →
        holes.lookup name = some ty →
        ∀ id ∈ ty.mvars, frontier ≤ id ∧ id < limit := by
    intro holes name ty limit hall hlookup
    induction holes with
    | nil => simp [List.lookup] at hlookup
    | cons entry rest ih =>
        rcases entry with ⟨key, value⟩
        by_cases hkey : name = key
        · subst key
          simp [List.lookup] at hlookup
          subst ty
          exact hall (name, value) (by simp)
        · have hbeq : (name == key) = false := beq_false_of_ne hkey
          apply ih
          · intro entry hmem
            exact hall entry (by simp [hmem])
          · simpa [List.lookup, hbeq] using hlookup
  have lookup_of_mem_key :
      ∀ {holes : HoleAssignment} {name : String},
        name ∈ holes.map Prod.fst → ∃ ty, holes.lookup name = some ty := by
    intro holes name hmem
    induction holes with
    | nil => simp at hmem
    | cons entry rest ih =>
        rcases entry with ⟨key, value⟩
        simp only [List.map_cons, List.mem_cons] at hmem
        rcases hmem with hkey | hrest
        · subst key
          exact ⟨value, by simp [List.lookup]⟩
        · obtain ⟨ty, hlookup⟩ := ih hrest
          by_cases hkey : name = key
          · subst key
            exact ⟨value, by simp [List.lookup]⟩
          · have hbeq : (name == key) = false := beq_false_of_ne hkey
            exact ⟨ty, by simpa [List.lookup, hbeq] using hlookup⟩
  have allocateWith_bounds :
      ∀ {candidate : Template} {r b : Nat},
        candidate.Scoped r b →
        ∀ {holes : HoleAssignment} {current : Nat},
          (∀ entry ∈ holes, ∀ id ∈ entry.2.mvars,
            frontier ≤ id ∧ id < current) →
          (∀ name ∈ candidate.names,
            ∃ ty, holes.lookup name = some ty) →
          frontier ≤ current →
          current ≤ (candidate.allocateWith holes current).1 ∧
            ∀ id ∈ (candidate.allocateWith holes current).2.mvars,
              frontier ≤ id ∧
                id < (candidate.allocateWith holes current).1 := by
    intro candidate r b hs holes current hholes hcover hcurrent
    induction candidate generalizing r b holes current with
    | fixed ty =>
        cases hs with
        | fixed hwf =>
          constructor
          · simp [Template.allocateWith]
          · intro id hmem
            have hempty := metaFree_mvars hwf.2
            simp [Template.allocateWith, hempty] at hmem
    | hole =>
        constructor
        · simp [Template.allocateWith]
        · intro id hmem
          simp only [Template.allocateWith, Ty.mvars,
            List.mem_singleton] at hmem ⊢
          subst id
          omega
    | named name =>
        obtain ⟨ty, hlookup⟩ := hcover name (by simp [Template.names])
        simp only [Template.allocateWith, hlookup, Option.getD_some]
        exact ⟨le_rfl, lookup_bound hholes hlookup⟩
    | arrow domain codomain ihDomain ihCodomain =>
        cases hs with
        | arrow hDomain hCodomain =>
          have domainCover : ∀ name ∈ domain.names,
              ∃ ty, holes.lookup name = some ty := by
            intro name hmem
            exact hcover name (List.mem_append_left _ hmem)
          obtain ⟨hDomainNext, hDomainBounds⟩ :=
            ihDomain hDomain hholes domainCover hcurrent
          have holesLater :
              ∀ entry ∈ holes, ∀ id ∈ entry.2.mvars,
                frontier ≤ id ∧
                  id < (domain.allocateWith holes current).1 := by
            intro entry hentry id hid
            obtain ⟨hbase, hlt⟩ := hholes entry hentry id hid
            exact ⟨hbase, lt_of_lt_of_le hlt hDomainNext⟩
          have codomainCover : ∀ name ∈ codomain.names,
              ∃ ty, holes.lookup name = some ty := by
            intro name hmem
            exact hcover name (List.mem_append_right _ hmem)
          obtain ⟨hCodomainNext, hCodomainBounds⟩ :=
            ihCodomain hCodomain holesLater codomainCover
              (le_trans hcurrent hDomainNext)
          constructor
          · exact le_trans hDomainNext hCodomainNext
          · intro id hmem
            simp only [Template.allocateWith, Ty.mvars,
              List.mem_dedup, List.mem_append] at hmem ⊢
            rcases hmem with hmem | hmem
            · obtain ⟨hbase, hlt⟩ := hDomainBounds id hmem
              exact ⟨hbase, lt_of_lt_of_le hlt hCodomainNext⟩
            · exact hCodomainBounds id hmem
  let keys := template.names.dedup
  let holes := namedHoleTable keys frontier
  let start := frontier + keys.length
  have keysNodup : keys.Nodup := by
    exact List.nodup_dedup _
  have keysDedup : keys.dedup = keys := List.dedup_eq_self.mpr keysNodup
  have holesBound :
      ∀ entry ∈ holes, ∀ id ∈ entry.2.mvars,
        frontier ≤ id ∧ id < start := by
    intro entry hmem id hid
    simp only [holes, namedHoleTable, keysDedup] at hmem
    have hsecond := (List.of_mem_zip hmem).2
    obtain ⟨offset, hoffset, hentry⟩ := List.mem_map.mp hsecond
    have hsid : entry.2 = .mvar (frontier + offset) := hentry.symm
    rw [hsid] at hid
    simp only [Ty.mvars, List.mem_singleton] at hid
    subst id
    have hlt := List.mem_range.mp hoffset
    exact ⟨Nat.le_add_right frontier offset,
      by simpa [start] using Nat.add_lt_add_left hlt frontier⟩
  have holesCover :
      ∀ name ∈ template.names, ∃ ty, holes.lookup name = some ty := by
    intro name hmem
    apply lookup_of_mem_key
    simp only [holes, namedHoleTable, keysDedup]
    rw [List.map_fst_zip]
    · simpa [keys] using List.mem_dedup.mpr hmem
    · simp
  have startBase : frontier ≤ start := by
    simp [start]
  obtain ⟨_, resultBounds⟩ :=
    allocateWith_bounds templateScoped holesBound holesCover startBase
  simpa [Template.allocate, keys, holes, start] using resultBounds

theorem InferState.allocate_safe
    {state : InferState} {template : Template} {rigidCount : Nat}
    (safe : state.Safe rigidCount)
    (templateScoped : template.Scoped rigidCount 0) :
    (state.allocate template).1.Safe rigidCount ∧
      (state.allocate template).2.InferWF rigidCount 0
        (state.allocate template).1.next ∧
      state.next ≤ (state.allocate template).1.next := by
  simp only [InferState.allocate]
  let allocation := template.allocate state.next
  let count := allocation.next - state.next
  have nextLe : state.next ≤ allocation.next :=
    Template.allocate_next_le template state.next
  have countEq : state.next + count = allocation.next := by
    simp only [count]
    omega
  have rangeLength : (mvarRange state.next count).length = count := by
    simp [mvarRange]
  have rangeMember :
      ∀ ty ∈ mvarRange state.next count,
        ∃ offset < count, ty = .mvar (state.next + offset) := by
    intro ty hmem
    obtain ⟨id, hid, rfl⟩ := List.mem_map.mp hmem
    obtain ⟨offset, hlt, hid⟩ := List.mem_range'.mp hid
    subst id
    exact ⟨offset, hlt, by simp⟩
  have apply_append_of_bounded :
      ∀ {ty : Ty}, ty.MVarBounded state.solutions.length →
        (state.solutions ++ mvarRange state.next count).apply ty =
          state.solutions.apply ty := by
    intro ty bounded
    induction ty with
    | prim p => rfl
    | arrow domain codomain ihDomain ihCodomain =>
        simp only [MStore.apply]
        rw [ihDomain, ihCodomain]
        · intro id hmem
          exact bounded id (by simp [Ty.mvars, hmem])
        · intro id hmem
          exact bounded id (by simp [Ty.mvars, hmem])
    | bvar index => rfl
    | rigid level => rfl
    | mvar id =>
        simp only [MStore.apply]
        have hlt : id < state.solutions.length :=
          bounded id (by simp [Ty.mvars])
        rw [List.getElem?_append_left hlt]
  have rangeNormalized :
      ∀ ty ∈ mvarRange state.next count,
        (state.solutions ++ mvarRange state.next count).apply ty = ty := by
    intro ty hmem
    obtain ⟨offset, hlt, rfl⟩ := rangeMember ty hmem
    simp only [MStore.apply]
    rw [List.getElem?_append_right (by
      rw [safe.solutions_length]
      omega)]
    simp [mvarRange, safe.solutions_length, hlt]
  have newSafe :
      ({ next := allocation.next,
          solutions := state.solutions ++ mvarRange state.next count,
          required := List.range' state.next count ++ state.required } :
        InferState).Safe rigidCount := by
    constructor
    · simp [safe.solutions_length, rangeLength, countEq]
    · intro ty hmem
      rcases List.mem_append.mp hmem with hOld | hNew
      · exact safe.solutionsScoped ty hOld
      · obtain ⟨offset, _, rfl⟩ := rangeMember ty hNew
        exact .mvar _
    · intro ty hmem id hid
      rcases List.mem_append.mp hmem with hOld | hNew
      · have oldBound := safe.solutionsBounded ty hOld id hid
        exact lt_of_lt_of_le oldBound nextLe
      · obtain ⟨offset, hlt, rfl⟩ := rangeMember ty hNew
        simp only [Ty.mvars, List.mem_singleton] at hid
        subst id
        change state.next + offset < allocation.next
        omega
    · intro ty hmem
      rcases List.mem_append.mp hmem with hOld | hNew
      · rw [apply_append_of_bounded]
        · exact safe.solutionsNormalized ty hOld
        · intro id hid
          rw [safe.solutions_length]
          exact safe.solutionsBounded ty hOld id hid
      · exact rangeNormalized ty hNew
    · intro id hmem
      rcases List.mem_append.mp hmem with hNew | hOld
      · obtain ⟨offset, hlt, hid⟩ := List.mem_range'.mp hNew
        subst id
        change state.next + 1 * offset < allocation.next
        omega
      · exact lt_of_lt_of_le (safe.requiredBounded id hOld) nextLe
  refine ⟨?_, ?_, nextLe⟩
  · simpa [allocation, count] using newSafe
  · constructor
    · exact Template.allocate_scoped templateScoped
    · intro id hmem
      exact (Template.allocate_mvars templateScoped id hmem).2

/-- A solver run over store-normalized inputs preserves every allocated type
already fixed by that store. This is the sole compatibility contract between
the ordered unifier and inference's dense solution table. -/
theorem MStore.unify_preserves_fixed
    {store : MStore} {left right : Ty} {delta : MSubst} {frontier : Nat}
    (length : store.length = frontier)
    (storeBounded : store.Bounded frontier)
    (storeNormalized : store.Normalized)
    (leftBounded : left.MVarBounded frontier)
    (rightBounded : right.MVarBounded frontier)
    (run : unify (store.apply left) (store.apply right) = some delta) :
    ∀ ty, ty.MVarBounded frontier → store.apply ty = ty →
      store.apply (delta.apply ty) = delta.apply ty := by
  have _storeBounded := storeBounded
  have storeApplyFixed : ∀ {ty : Ty}, ty.MVarBounded frontier →
      store.apply (store.apply ty) = store.apply ty := by
    intro ty bounded
    induction ty with
    | prim name => rfl
    | arrow domain codomain ihDomain ihCodomain =>
        have domainBounded : domain.MVarBounded frontier := by
          intro id member
          exact bounded id (by simp [Ty.mvars, member])
        have codomainBounded : codomain.MVarBounded frontier := by
          intro id member
          exact bounded id (by simp [Ty.mvars, member])
        simp only [MStore.apply, ihDomain domainBounded, ihCodomain codomainBounded]
    | bvar index => rfl
    | rigid level => rfl
    | mvar id =>
        have idBounded : id < frontier := bounded id (by simp [Ty.mvars])
        have idInStore : id < store.length := by simpa [length] using idBounded
        rw [MStore.apply, List.getElem?_eq_getElem idInStore, Option.getD_some]
        exact storeNormalized store[id] (List.getElem_mem ..)
  have substMVarFixed : ∀ {ty replacement : Ty} {target : Nat},
      store.apply ty = ty → store.apply replacement = replacement →
        store.apply (ty.substMVar target replacement) =
          ty.substMVar target replacement := by
    intro ty replacement target typeFixed replacementFixed
    induction ty with
    | prim name => rfl
    | arrow domain codomain ihDomain ihCodomain =>
        simp only [MStore.apply, Ty.substMVar] at typeFixed ⊢
        injection typeFixed with domainFixed codomainFixed
        rw [ihDomain domainFixed, ihCodomain codomainFixed]
    | bvar index => rfl
    | rigid level => rfl
    | mvar id =>
        simp only [Ty.substMVar]
        split
        · exact replacementFixed
        · exact typeFixed
  have substApplyFixed : ∀ {subst : MSubst} {ty : Ty},
      (∀ binding ∈ subst, store.apply binding.2 = binding.2) →
      store.apply ty = ty →
      store.apply (subst.apply ty) = subst.apply ty := by
    intro subst ty substFixed typeFixed
    induction subst generalizing ty with
    | nil => simpa [MSubst.apply] using typeFixed
    | cons binding rest ih =>
        have replacementFixed : store.apply binding.2 = binding.2 :=
          substFixed binding (by simp)
        have restFixed : ∀ item ∈ rest, store.apply item.2 = item.2 := by
          intro item member
          exact substFixed item (by simp [member])
        simpa [MSubst.apply, List.foldl] using
          ih restFixed (substMVarFixed typeFixed replacementFixed)
  have unifyFuelFixed : ∀ {fuel : Nat} {constraints : List Constraint}
      {initial result : MSubst},
      (∀ binding ∈ initial, store.apply binding.2 = binding.2) →
      (∀ constraint ∈ constraints,
        store.apply constraint.1 = constraint.1 ∧
          store.apply constraint.2 = constraint.2) →
      unifyFuel fuel constraints initial = some result →
      ∀ binding ∈ result, store.apply binding.2 = binding.2 := by
    intro fuel
    induction fuel with
    | zero =>
        intro constraints initial result initialFixed constraintsFixed runFuel
        cases constraints with
        | nil =>
            simp only [unifyFuel, Option.some.injEq] at runFuel
            subst result
            exact initialFixed
        | cons constraint rest => simp [unifyFuel] at runFuel
    | succ fuel ih =>
        intro constraints initial result initialFixed constraintsFixed runFuel
        cases constraints with
        | nil =>
            simp only [unifyFuel, Option.some.injEq] at runFuel
            subst result
            exact initialFixed
        | cons constraint rest =>
            rcases constraint with ⟨constraintLeft, constraintRight⟩
            have headFixed := constraintsFixed
              (constraintLeft, constraintRight) (by simp)
            have restFixed : ∀ constraint ∈ rest,
                store.apply constraint.1 = constraint.1 ∧
                  store.apply constraint.2 = constraint.2 := by
              intro constraint member
              exact constraintsFixed constraint (List.mem_cons_of_mem _ member)
            have normalizedLeftFixed :
                store.apply (initial.apply constraintLeft) =
                  initial.apply constraintLeft :=
              substApplyFixed initialFixed headFixed.1
            have normalizedRightFixed :
                store.apply (initial.apply constraintRight) =
                  initial.apply constraintRight :=
              substApplyFixed initialFixed headFixed.2
            simp only [unifyFuel] at runFuel
            by_cases equal :
                initial.apply constraintLeft = initial.apply constraintRight
            · rw [if_pos equal] at runFuel
              exact ih initialFixed restFixed runFuel
            · rw [if_neg equal] at runFuel
              generalize leftEq : initial.apply constraintLeft = normalizedLeft at normalizedLeftFixed runFuel
              generalize rightEq : initial.apply constraintRight = normalizedRight at normalizedRightFixed runFuel
              have bindCase (id : Nat) (assigned : Ty)
                  (assignedFixed : store.apply assigned = assigned)
                  (bindRun :
                    (if assigned.occursMVar id = true then none
                      else unifyFuel fuel rest (initial ++ [(id, assigned)])) =
                        some result) :
                  ∀ binding ∈ result, store.apply binding.2 = binding.2 := by
                by_cases occurs : assigned.occursMVar id = true
                · simp [occurs] at bindRun
                · apply ih
                    (initial := initial ++ [(id, assigned)])
                    (result := result)
                  · intro binding member
                    rcases List.mem_append.mp member with old | new
                    · exact initialFixed binding old
                    · simp only [List.mem_singleton] at new
                      subst binding
                      exact assignedFixed
                  · exact restFixed
                  · simpa [occurs] using bindRun
              cases normalizedLeft with
              | prim leftPrim =>
                  cases normalizedRight with
                  | prim rightPrim => simp at runFuel
                  | arrow _ _ => simp at runFuel
                  | bvar _ => simp at runFuel
                  | rigid _ => simp at runFuel
                  | mvar id =>
                      exact bindCase id (.prim leftPrim) normalizedLeftFixed runFuel
              | arrow leftDomain leftCodomain =>
                  cases normalizedRight with
                  | prim _ => simp at runFuel
                  | arrow rightDomain rightCodomain =>
                      have leftParts := Ty.arrow.inj normalizedLeftFixed
                      have rightParts := Ty.arrow.inj normalizedRightFixed
                      have splitFixed : ∀ constraint ∈
                          ((leftDomain, rightDomain) ::
                            (leftCodomain, rightCodomain) :: rest),
                          store.apply constraint.1 = constraint.1 ∧
                            store.apply constraint.2 = constraint.2 := by
                        rintro ⟨a, b⟩ member
                        simp only [List.mem_cons, Prod.mk.injEq] at member
                        rcases member with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | inRest
                        · exact ⟨leftParts.1, rightParts.1⟩
                        · exact ⟨leftParts.2, rightParts.2⟩
                        · exact restFixed (a, b) inRest
                      exact ih initialFixed splitFixed runFuel
                  | bvar _ => simp at runFuel
                  | rigid _ => simp at runFuel
                  | mvar id =>
                      exact bindCase id (.arrow leftDomain leftCodomain)
                        normalizedLeftFixed runFuel
              | bvar leftIndex =>
                  cases normalizedRight with
                  | prim _ => simp at runFuel
                  | arrow _ _ => simp at runFuel
                  | bvar _ => simp at runFuel
                  | rigid _ => simp at runFuel
                  | mvar id =>
                      exact bindCase id (.bvar leftIndex) normalizedLeftFixed runFuel
              | rigid leftLevel =>
                  cases normalizedRight with
                  | prim _ => simp at runFuel
                  | arrow _ _ => simp at runFuel
                  | bvar _ => simp at runFuel
                  | rigid _ => simp at runFuel
                  | mvar id =>
                      exact bindCase id (.rigid leftLevel)
                        normalizedLeftFixed runFuel
              | mvar id =>
                  cases normalizedRight with
                  | prim rightPrim =>
                      exact bindCase id (.prim rightPrim)
                        normalizedRightFixed runFuel
                  | arrow rightDomain rightCodomain =>
                      exact bindCase id (.arrow rightDomain rightCodomain)
                        normalizedRightFixed runFuel
                  | bvar rightIndex =>
                      exact bindCase id (.bvar rightIndex)
                        normalizedRightFixed runFuel
                  | rigid rightLevel =>
                      exact bindCase id (.rigid rightLevel)
                        normalizedRightFixed runFuel
                  | mvar rightId =>
                      exact bindCase id (.mvar rightId)
                        normalizedRightFixed runFuel
  have deltaFixed : ∀ binding ∈ delta,
      store.apply binding.2 = binding.2 := by
    apply unifyFuelFixed
      (fuel := unifyBudget (store.apply left) (store.apply right))
      (constraints := [(store.apply left, store.apply right)])
      (initial := []) (result := delta)
    · simp
    · intro constraint member
      have constraintEq := List.mem_singleton.mp member
      cases constraintEq
      exact ⟨storeApplyFixed leftBounded, storeApplyFixed rightBounded⟩
    · simpa [unify] using run
  intro ty _ typeFixed
  exact substApplyFixed deltaFixed typeFixed

/-- Unifying types already normalized by a dense solution table and applying
the solver result pointwise produces another normalized table. -/
theorem MStore.map_unify_normalized
    {store : MStore} {left right : Ty} {delta : MSubst} {frontier : Nat}
    (length : store.length = frontier)
    (storeBounded : store.Bounded frontier)
    (storeNormalized : store.Normalized)
    (leftBounded : left.MVarBounded frontier)
    (rightBounded : right.MVarBounded frontier)
    (run : unify (store.apply left) (store.apply right) = some delta) :
    MStore.Normalized (store.map delta.apply) := by
  have storeApplyBounded : ∀ {ty : Ty}, ty.MVarBounded frontier →
      (store.apply ty).MVarBounded frontier := by
    intro ty bounded
    induction ty with
    | prim name => simp [MStore.apply, Ty.MVarBounded, Ty.mvars]
    | arrow domain codomain ihDomain ihCodomain =>
        have domainBounded : domain.MVarBounded frontier := by
          intro id member
          exact bounded id (by simp [Ty.mvars, member])
        have codomainBounded : codomain.MVarBounded frontier := by
          intro id member
          exact bounded id (by simp [Ty.mvars, member])
        intro id member
        simp only [MStore.apply, Ty.mvars, List.mem_dedup,
          List.mem_append] at member
        rcases member with member | member
        · exact ihDomain domainBounded id member
        · exact ihCodomain codomainBounded id member
    | bvar index => simp [MStore.apply, Ty.MVarBounded, Ty.mvars]
    | rigid level => simp [MStore.apply, Ty.MVarBounded, Ty.mvars]
    | mvar id =>
        have idBounded : id < frontier := bounded id (by simp [Ty.mvars])
        have idInStore : id < store.length := by simpa [length] using idBounded
        rw [MStore.apply, List.getElem?_eq_getElem idInStore, Option.getD_some]
        exact storeBounded store[id] (List.getElem_mem ..)
  have substMVarBounded : ∀ {ty replacement : Ty} {target : Nat},
      ty.MVarBounded frontier → replacement.MVarBounded frontier →
        (ty.substMVar target replacement).MVarBounded frontier := by
    intro ty replacement target typeBounded replacementBounded
    induction ty with
    | prim name => simpa [Ty.substMVar] using typeBounded
    | arrow domain codomain ihDomain ihCodomain =>
        have domainBounded : domain.MVarBounded frontier := by
          intro id member
          exact typeBounded id (by simp [Ty.mvars, member])
        have codomainBounded : codomain.MVarBounded frontier := by
          intro id member
          exact typeBounded id (by simp [Ty.mvars, member])
        intro id member
        simp only [Ty.substMVar, Ty.mvars, List.mem_dedup,
          List.mem_append] at member
        rcases member with member | member
        · exact ihDomain domainBounded id member
        · exact ihCodomain codomainBounded id member
    | bvar index => simpa [Ty.substMVar] using typeBounded
    | rigid level => simpa [Ty.substMVar] using typeBounded
    | mvar id =>
        simp only [Ty.substMVar]
        split
        · exact replacementBounded
        · exact typeBounded
  have substApplyBounded : ∀ {subst : MSubst} {ty : Ty},
      subst.Bounded frontier → ty.MVarBounded frontier →
        (subst.apply ty).MVarBounded frontier := by
    intro subst ty substBounded typeBounded
    induction subst generalizing ty with
    | nil => simpa [MSubst.apply] using typeBounded
    | cons binding rest ih =>
        have bindingBounded := substBounded binding (by simp)
        have restBounded : MSubst.Bounded frontier rest := by
          intro item member
          exact substBounded item (by simp [member])
        simpa [MSubst.apply, List.foldl] using
          ih restBounded (substMVarBounded typeBounded bindingBounded.2)
  have leftAppliedBounded := storeApplyBounded leftBounded
  have rightAppliedBounded := storeApplyBounded rightBounded
  have deltaBounded : delta.Bounded frontier :=
    unify_bounded leftAppliedBounded rightAppliedBounded run
  have deltaStable : delta.Stable := unify_stable run
  have substApplyArrow : ∀ (subst : MSubst) (domain codomain : Ty),
      subst.apply (.arrow domain codomain) =
        .arrow (subst.apply domain) (subst.apply codomain) := by
    intro subst domain codomain
    induction subst generalizing domain codomain with
    | nil => rfl
    | cons binding rest ih =>
        simp only [MSubst.apply, List.foldl_cons, Ty.substMVar]
        exact ih _ _
  have substApplyPrim : ∀ (subst : MSubst) (name : PrimTy),
      subst.apply (.prim name) = .prim name := by
    intro subst name
    induction subst with
    | nil => rfl
    | cons binding rest ih =>
        simpa [MSubst.apply, List.foldl_cons, Ty.substMVar] using ih
  have substApplyBVar : ∀ (subst : MSubst) (index : Nat),
      subst.apply (.bvar index) = .bvar index := by
    intro subst index
    induction subst with
    | nil => rfl
    | cons binding rest ih =>
        simpa [MSubst.apply, List.foldl_cons, Ty.substMVar] using ih
  have substApplyRigid : ∀ (subst : MSubst) (level : Nat),
      subst.apply (.rigid level) = .rigid level := by
    intro subst level
    induction subst with
    | nil => rfl
    | cons binding rest ih =>
        simpa [MSubst.apply, List.foldl_cons, Ty.substMVar] using ih
  have mapApply : ∀ {ty : Ty}, ty.MVarBounded frontier →
      MStore.apply (store.map delta.apply) ty =
        delta.apply (store.apply ty) := by
    intro ty bounded
    induction ty with
    | prim name => simpa [MStore.apply] using (substApplyPrim delta name).symm
    | arrow domain codomain ihDomain ihCodomain =>
        have domainBounded : domain.MVarBounded frontier := by
          intro id member
          exact bounded id (by simp [Ty.mvars, member])
        have codomainBounded : codomain.MVarBounded frontier := by
          intro id member
          exact bounded id (by simp [Ty.mvars, member])
        simp only [MStore.apply]
        rw [ihDomain domainBounded, ihCodomain codomainBounded,
          substApplyArrow]
    | bvar index => simpa [MStore.apply] using (substApplyBVar delta index).symm
    | rigid level => simpa [MStore.apply] using (substApplyRigid delta level).symm
    | mvar id =>
        have idBounded : id < frontier := bounded id (by simp [Ty.mvars])
        have idInStore : id < store.length := by simpa [length] using idBounded
        simp only [MStore.apply, List.getElem?_map,
          List.getElem?_eq_getElem idInStore, Option.map_some,
          Option.getD_some]
  intro ty member
  obtain ⟨oldTy, oldMember, rfl⟩ := List.mem_map.mp member
  have oldBounded := storeBounded oldTy oldMember
  have updatedBounded : (delta.apply oldTy).MVarBounded frontier :=
    substApplyBounded deltaBounded oldBounded
  rw [mapApply updatedBounded]
  have oldFixed : store.apply oldTy = oldTy := storeNormalized oldTy oldMember
  have deltaOldFixed : store.apply (delta.apply oldTy) = delta.apply oldTy :=
    MStore.unify_preserves_fixed length storeBounded storeNormalized
      leftBounded rightBounded run oldTy oldBounded oldFixed
  rw [deltaOldFixed, deltaStable]

/-- Constraining two allocated, scoped types preserves state safety and makes
the equation true in the resulting dense solution table. -/
theorem InferState.constrain_safe
    {state checked : InferState} {left right : Ty} {rigidCount : Nat}
    (safe : state.Safe rigidCount)
    (leftWF : left.InferWF rigidCount 0 state.next)
    (rightWF : right.InferWF rigidCount 0 state.next)
    (run : state.constrain left right = some checked) :
    checked.Safe rigidCount ∧
      checked.next = state.next ∧
      checked.required = state.required ∧
      checked.solutions.apply left = checked.solutions.apply right := by
  unfold InferState.constrain at run
  cases hdelta : unify (state.solutions.apply left)
      (state.solutions.apply right) with
  | none => simp [hdelta] at run
  | some delta =>
      simp only [hdelta, Option.some.injEq] at run
      subst checked
      have leftAppliedWF := MStore.apply_inferWF
        safe.solutionsScoped safe.solutionsBounded leftWF
      have rightAppliedWF := MStore.apply_inferWF
        safe.solutionsScoped safe.solutionsBounded rightWF
      have deltaScoped : delta.Scoped rigidCount :=
        unify_scoped leftAppliedWF.1 rightAppliedWF.1 hdelta
      have deltaBounded : delta.Bounded state.next :=
        unify_bounded leftAppliedWF.2 rightAppliedWF.2 hdelta
      have substMVarScoped : ∀ {ty replacement : Ty} {target : Nat},
          ty.Scoped rigidCount 0 → replacement.Scoped rigidCount 0 →
            (ty.substMVar target replacement).Scoped rigidCount 0 := by
        intro ty replacement target typeScoped replacementScoped
        induction typeScoped with
        | prim => exact .prim
        | arrow _ _ ihDomain ihCodomain => exact .arrow ihDomain ihCodomain
        | bvar hlt => omega
        | rigid hlt => exact .rigid hlt
        | mvar id =>
            simp only [Ty.substMVar]
            split
            · exact replacementScoped
            · exact .mvar _
      have substApplyScoped : ∀ {subst : MSubst} {ty : Ty},
          subst.Scoped rigidCount → ty.Scoped rigidCount 0 →
            (subst.apply ty).Scoped rigidCount 0 := by
        intro subst ty substScoped typeScoped
        induction subst generalizing ty with
        | nil => simpa [MSubst.apply] using typeScoped
        | cons binding rest ih =>
            have bindingScoped : binding.2.Scoped rigidCount 0 :=
              substScoped binding (by simp)
            have restScoped : MSubst.Scoped rigidCount rest := by
              intro item member
              exact substScoped item (by simp [member])
            simpa [MSubst.apply, List.foldl] using
              ih restScoped (substMVarScoped typeScoped bindingScoped)
      have substMVarBounded : ∀ {ty replacement : Ty} {target : Nat},
          ty.MVarBounded state.next → replacement.MVarBounded state.next →
            (ty.substMVar target replacement).MVarBounded state.next := by
        intro ty replacement target typeBounded replacementBounded
        induction ty with
        | prim name => simpa [Ty.substMVar] using typeBounded
        | arrow domain codomain ihDomain ihCodomain =>
            have domainBounded : domain.MVarBounded state.next := by
              intro id member
              exact typeBounded id (by simp [Ty.mvars, member])
            have codomainBounded : codomain.MVarBounded state.next := by
              intro id member
              exact typeBounded id (by simp [Ty.mvars, member])
            intro id member
            simp only [Ty.substMVar, Ty.mvars, List.mem_dedup,
              List.mem_append] at member
            rcases member with member | member
            · exact ihDomain domainBounded id member
            · exact ihCodomain codomainBounded id member
        | bvar index => simpa [Ty.substMVar] using typeBounded
        | rigid level => simpa [Ty.substMVar] using typeBounded
        | mvar id =>
            simp only [Ty.substMVar]
            split
            · exact replacementBounded
            · exact typeBounded
      have substApplyBounded : ∀ {subst : MSubst} {ty : Ty},
          subst.Bounded state.next → ty.MVarBounded state.next →
            (subst.apply ty).MVarBounded state.next := by
        intro subst ty substBounded typeBounded
        induction subst generalizing ty with
        | nil => simpa [MSubst.apply] using typeBounded
        | cons binding rest ih =>
            have bindingBounded := substBounded binding (by simp)
            have restBounded : MSubst.Bounded state.next rest := by
              intro item member
              exact substBounded item (by simp [member])
            simpa [MSubst.apply, List.foldl] using
              ih restBounded (substMVarBounded typeBounded bindingBounded.2)
      have substApplyArrow : ∀ (subst : MSubst) (domain codomain : Ty),
          subst.apply (.arrow domain codomain) =
            .arrow (subst.apply domain) (subst.apply codomain) := by
        intro subst domain codomain
        induction subst generalizing domain codomain with
        | nil => rfl
        | cons binding rest ih =>
            simp only [MSubst.apply, List.foldl_cons, Ty.substMVar]
            exact ih _ _
      have substApplyPrim : ∀ (subst : MSubst) (name : PrimTy),
          subst.apply (.prim name) = .prim name := by
        intro subst name
        induction subst with
        | nil => rfl
        | cons binding rest ih =>
            simpa [MSubst.apply, List.foldl_cons, Ty.substMVar] using ih
      have substApplyBVar : ∀ (subst : MSubst) (index : Nat),
          subst.apply (.bvar index) = .bvar index := by
        intro subst index
        induction subst with
        | nil => rfl
        | cons binding rest ih =>
            simpa [MSubst.apply, List.foldl_cons, Ty.substMVar] using ih
      have substApplyRigid : ∀ (subst : MSubst) (level : Nat),
          subst.apply (.rigid level) = .rigid level := by
        intro subst level
        induction subst with
        | nil => rfl
        | cons binding rest ih =>
            simpa [MSubst.apply, List.foldl_cons, Ty.substMVar] using ih
      have mapApply : ∀ {ty : Ty}, ty.MVarBounded state.next →
          MStore.apply (state.solutions.map delta.apply) ty =
            delta.apply (state.solutions.apply ty) := by
        intro ty bounded
        induction ty with
        | prim name =>
            simpa [MStore.apply] using (substApplyPrim delta name).symm
        | arrow domain codomain ihDomain ihCodomain =>
            have domainBounded : domain.MVarBounded state.next := by
              intro id member
              exact bounded id (by simp [Ty.mvars, member])
            have codomainBounded : codomain.MVarBounded state.next := by
              intro id member
              exact bounded id (by simp [Ty.mvars, member])
            simp only [MStore.apply]
            rw [ihDomain domainBounded, ihCodomain codomainBounded,
              substApplyArrow]
        | bvar index =>
            simpa [MStore.apply] using (substApplyBVar delta index).symm
        | rigid level =>
            simpa [MStore.apply] using (substApplyRigid delta level).symm
        | mvar id =>
            have idBounded : id < state.next := bounded id (by simp [Ty.mvars])
            have idInStore : id < state.solutions.length := by
              simpa [safe.solutions_length] using idBounded
            simp only [MStore.apply, List.getElem?_map,
              List.getElem?_eq_getElem idInStore, Option.map_some,
              Option.getD_some]
      have mappedScoped : MStore.Scoped
          (state.solutions.map delta.apply) rigidCount := by
        intro ty member
        obtain ⟨oldTy, oldMember, rfl⟩ := List.mem_map.mp member
        exact substApplyScoped deltaScoped
          (safe.solutionsScoped oldTy oldMember)
      have mappedBounded : MStore.Bounded
          (state.solutions.map delta.apply) state.next := by
        intro ty member
        obtain ⟨oldTy, oldMember, rfl⟩ := List.mem_map.mp member
        exact substApplyBounded deltaBounded
          (safe.solutionsBounded oldTy oldMember)
      have mappedNormalized : MStore.Normalized
          (state.solutions.map delta.apply) :=
        MStore.map_unify_normalized safe.solutions_length
          safe.solutionsBounded safe.solutionsNormalized
          leftWF.2 rightWF.2 hdelta
      refine ⟨?_, rfl, rfl, ?_⟩
      · exact ⟨by simpa using safe.solutions_length,
          mappedScoped, mappedBounded, mappedNormalized,
          safe.requiredBounded⟩
      · rw [mapApply leftWF.2, mapApply rightWF.2,
          unify_sound hdelta]

/-- A checked prefix is a safe solution table at the restored outer frontier. -/
theorem MStore.take_safe
    {store : MStore} {rigidCount cutoff : Nat}
    (length : cutoff ≤ store.length)
    (normalized : store.Normalized)
    (escape : MStore.safeToLeave rigidCount cutoff (store.take cutoff) = true) :
    (store.take cutoff).length = cutoff ∧
      MStore.Scoped (store.take cutoff) rigidCount ∧
      MStore.Bounded (store.take cutoff) cutoff ∧
      MStore.Normalized (store.take cutoff) := by
  have prefixApply : ∀ {ty : Ty}, ty.MVarBounded cutoff →
      MStore.apply (store.take cutoff) ty = store.apply ty := by
    intro ty bounded
    induction ty with
    | prim name => rfl
    | arrow domain codomain ihDomain ihCodomain =>
        have domainBounded : domain.MVarBounded cutoff := by
          intro id member
          exact bounded id (by simp [Ty.mvars, member])
        have codomainBounded : codomain.MVarBounded cutoff := by
          intro id member
          exact bounded id (by simp [Ty.mvars, member])
        simp only [MStore.apply, ihDomain domainBounded, ihCodomain codomainBounded]
    | bvar index => rfl
    | rigid level => rfl
    | mvar id =>
        have idBounded : id < cutoff := bounded id (by simp [Ty.mvars])
        simp only [MStore.apply, List.getElem?_take_of_lt idBounded]
  have escaped := MStore.safeToLeave_eq_true_iff.mp escape
  refine ⟨List.length_take_of_le length, ?_, ?_, ?_⟩
  · intro ty member
    exact (escaped ty member).1
  · intro ty member
    exact (Ty.mvarBounded_iff_mvarsBelow.mpr <| by
      exact Ty.mvarsBelow_eq_true_iff.mpr (escaped ty member).2)
  · intro ty member
    have bounded : ty.MVarBounded cutoff :=
      Ty.mvarBounded_iff_mvarsBelow.mpr <|
        Ty.mvarsBelow_eq_true_iff.mpr (escaped ty member).2
    rw [prefixApply bounded]
    exact normalized ty (List.mem_of_mem_take member)

end EPL
