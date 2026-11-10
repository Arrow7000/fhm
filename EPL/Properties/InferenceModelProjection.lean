import EPL.Properties.InferenceModelRefinement

namespace EPL

/-- A model of a checked outer prefix extends to a model of the whole local
scheme-checking table. The extension agrees on every outer metavariable; only
discarded local IDs receive fresh semantic meanings. -/
theorem MStore.Models.extend_checkedPrefix
    {store : MStore} {outerValuation : MValuation}
    {rigidCount count cutoff : Nat}
    (length : cutoff ≤ store.length)
    (storeScoped : store.Scoped (rigidCount + count))
    (storeBounded : store.Bounded store.length)
    (storeNormalized : store.Normalized)
    (escape : MStore.safeToLeave rigidCount cutoff
      (store.take cutoff) = true)
    (outerModels : MStore.Models (store.take cutoff)
      rigidCount outerValuation) :
    ∃ localValuation,
      store.Models (rigidCount + count) localValuation ∧
        ∀ id, id < cutoff → localValuation id = outerValuation id := by
  have prefixLength : (store.take cutoff).length = cutoff :=
    List.length_take_of_le length
  have escaped := MStore.safeToLeave_eq_true_iff.mp escape
  let baseValuation : MValuation := fun id =>
    if id < cutoff then outerValuation id else .prim .unit
  let localValuation : MValuation := fun id =>
    (store[id]?).map (·.realize baseValuation) |>.getD (.prim .unit)
  have wf_mono_rigid : ∀ {ty : Ty},
      ty.WF rigidCount 0 → ty.WF (rigidCount + count) 0 := by
    intro ty typeWF
    have scoped_mono : ∀ {candidate : Ty},
        candidate.Scoped rigidCount 0 →
          candidate.Scoped (rigidCount + count) 0 := by
      intro candidate candidateScoped
      induction candidateScoped with
      | prim => exact .prim
      | arrow _ _ ihDomain ihCodomain => exact .arrow ihDomain ihCodomain
      | bvar hlt => omega
      | rigid hlt => exact .rigid (lt_of_lt_of_le hlt (Nat.le_add_right _ _))
      | mvar id => exact .mvar id
    exact ⟨scoped_mono typeWF.1, typeWF.2⟩
  have baseWF : baseValuation.WF (rigidCount + count) store.length := by
    intro id idBounded
    dsimp [baseValuation]
    split
    · rename_i idOuter
      apply wf_mono_rigid
      apply outerModels.valuationWF id
      simpa [prefixLength] using idOuter
    · exact ⟨.prim, .prim⟩
  have realize_congr_on : ∀ (ty : Ty) (first second : MValuation),
      (∀ id ∈ ty.mvars, first id = second id) →
        ty.realize first = ty.realize second := by
    intro ty first second agree
    induction ty with
    | prim name => rfl
    | arrow domain codomain ihDomain ihCodomain =>
        have domainAgree : ∀ id ∈ domain.mvars, first id = second id := by
          intro id member
          exact agree id (by simp [Ty.mvars, member])
        have codomainAgree : ∀ id ∈ codomain.mvars, first id = second id := by
          intro id member
          exact agree id (by simp [Ty.mvars, member])
        simp only [Ty.realize, ihDomain domainAgree, ihCodomain codomainAgree]
    | bvar index => rfl
    | rigid level => rfl
    | mvar id => exact agree id (by simp [Ty.mvars])
  have fixed_mvar : ∀ {ty : Ty} {id : Nat},
      store.apply ty = ty → id ∈ ty.mvars →
        store.apply (.mvar id) = .mvar id := by
    intro ty id typeFixed member
    induction ty with
    | prim name => simp [Ty.mvars] at member
    | arrow domain codomain ihDomain ihCodomain =>
        simp only [MStore.apply] at typeFixed
        injection typeFixed with domainFixed codomainFixed
        simp only [Ty.mvars, List.mem_dedup, List.mem_append] at member
        rcases member with member | member
        · exact ihDomain domainFixed member
        · exact ihCodomain codomainFixed member
    | bvar index => simp [Ty.mvars] at member
    | rigid level => simp [Ty.mvars] at member
    | mvar current =>
        simp only [Ty.mvars, List.mem_singleton] at member
        subst current
        exact typeFixed
  have local_eq_base_of_mem : ∀ {ty : Ty}, ty ∈ store →
      ∀ {id : Nat}, id ∈ ty.mvars → localValuation id = baseValuation id := by
    intro ty typeMember id idMember
    have idBounded : id < store.length :=
      storeBounded ty typeMember id idMember
    have idFixed : store.apply (.mvar id) = .mvar id :=
      fixed_mvar (storeNormalized ty typeMember) idMember
    have entryIdentity : store[id] = .mvar id := by
      simpa [MStore.apply, List.getElem?_eq_getElem idBounded] using idFixed
    simp [localValuation, List.getElem?_eq_getElem idBounded,
      entryIdentity, Ty.realize]
  have entry_realize_eq : ∀ {ty : Ty}, ty ∈ store →
      ty.realize localValuation = ty.realize baseValuation := by
    intro ty typeMember
    apply realize_congr_on
    intro id idMember
    exact local_eq_base_of_mem typeMember idMember
  refine ⟨localValuation, ?_, ?_⟩
  · constructor
    · intro id idBounded
      have entryMember : store[id] ∈ store := List.getElem_mem ..
      have entryWF : store[id].InferWF
          (rigidCount + count) 0 store.length :=
        ⟨storeScoped store[id] entryMember,
          storeBounded store[id] entryMember⟩
      simpa [localValuation, List.getElem?_eq_getElem idBounded] using
        Ty.realize_inferWF entryWF baseWF
    · intro id idBounded
      have entryMember : store[id] ∈ store := List.getElem_mem ..
      simpa [localValuation, List.getElem?_eq_getElem idBounded] using
        (entry_realize_eq entryMember).symm
  · intro id idOuter
    have idStore : id < store.length := lt_of_lt_of_le idOuter length
    have idPrefix : id < (store.take cutoff).length := by
      simpa [prefixLength] using idOuter
    have entryEq : (store.take cutoff)[id] = store[id] := by
      have gets := List.getElem?_take_of_lt (l := store) idOuter
      simpa [List.getElem?_eq_getElem idPrefix,
        List.getElem?_eq_getElem idStore] using gets
    have entryMemberPrefix : store[id] ∈ store.take cutoff := by
      rw [← entryEq]
      exact List.getElem_mem ..
    have entryBounded : ∀ candidate ∈ store[id].mvars, candidate < cutoff :=
      (escaped store[id] entryMemberPrefix).2
    have realizeOuter : store[id].realize baseValuation =
        store[id].realize outerValuation := by
      apply realize_congr_on
      intro candidate candidateMember
      simp [baseValuation, entryBounded candidate candidateMember]
    calc
      localValuation id = store[id].realize baseValuation := by
        simp [localValuation, List.getElem?_eq_getElem idStore]
      _ = store[id].realize outerValuation := realizeOuter
      _ = (store.take cutoff)[id].realize outerValuation := by rw [entryEq]
      _ = outerValuation id := (outerModels.equation id idPrefix).symm

end EPL
