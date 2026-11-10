import EPL.Properties.InferenceModel

namespace EPL

/-- A concrete semantic completion for an unconstrained metavariable. -/
def Ty.defaultMVars : Ty → Ty
  | .prim p => .prim p
  | .arrow domain codomain =>
      .arrow domain.defaultMVars codomain.defaultMVars
  | .bvar index => .bvar index
  | .rigid level => .rigid level
  | .mvar _ => .prim .unit

def MStore.defaultValuation (store : MStore) : MValuation :=
  fun id => (store[id]?).map Ty.defaultMVars |>.getD (.prim .unit)

theorem Ty.defaultMVars_wf
    {ty : Ty} {rigidCount binderCount : Nat}
    (typeScoped : ty.Scoped rigidCount binderCount) :
    ty.defaultMVars.WF rigidCount binderCount := by
  induction typeScoped with
  | prim => exact ⟨.prim, .prim⟩
  | arrow _ _ ihDomain ihCodomain =>
      exact ⟨.arrow ihDomain.1 ihCodomain.1,
        .arrow ihDomain.2 ihCodomain.2⟩
  | bvar hlt => exact ⟨.bvar hlt, .bvar⟩
  | rigid hlt => exact ⟨.rigid hlt, .rigid⟩
  | mvar id => exact ⟨.prim, .prim⟩

/-- Every safe normalized table has a concrete semantic model: solved entries
keep their semantic structure and genuinely unconstrained variables default to
`Unit`. -/
theorem MStore.defaultValuation_models
    {store : MStore} {rigidCount frontier : Nat}
    (length : store.length = frontier)
    (storeScoped : store.Scoped rigidCount)
    (storeBounded : store.Bounded frontier)
    (storeNormalized : store.Normalized) :
    store.Models rigidCount store.defaultValuation := by
  have realize_eq_default : ∀ {ty : Ty},
      ty.MVarBounded frontier → store.apply ty = ty →
        ty.realize store.defaultValuation = ty.defaultMVars := by
    intro ty typeBounded typeFixed
    induction ty with
    | prim name => rfl
    | arrow domain codomain ihDomain ihCodomain =>
        have domainBounded : domain.MVarBounded frontier := by
          intro id member
          exact typeBounded id (by simp [Ty.mvars, member])
        have codomainBounded : codomain.MVarBounded frontier := by
          intro id member
          exact typeBounded id (by simp [Ty.mvars, member])
        simp only [MStore.apply, Ty.realize, Ty.defaultMVars] at typeFixed ⊢
        injection typeFixed with domainFixed codomainFixed
        rw [ihDomain domainBounded domainFixed,
          ihCodomain codomainBounded codomainFixed]
    | bvar index => rfl
    | rigid level => rfl
    | mvar id =>
        have idBounded : id < frontier :=
          typeBounded id (by simp [Ty.mvars])
        have idInStore : id < store.length := by
          simpa [length] using idBounded
        have entryIdentity : store[id] = .mvar id := by
          simpa [MStore.apply, List.getElem?_eq_getElem idInStore] using typeFixed
        simp [Ty.realize, MStore.defaultValuation,
          List.getElem?_eq_getElem idInStore, entryIdentity, Ty.defaultMVars]
  refine ⟨?_, ?_⟩
  · intro id idBounded
    have entryScoped : store[id].Scoped rigidCount 0 :=
      storeScoped store[id] (List.getElem_mem ..)
    simpa [MStore.defaultValuation,
      List.getElem?_eq_getElem idBounded] using
        Ty.defaultMVars_wf entryScoped
  · intro id idBounded
    have entryMember : store[id] ∈ store := List.getElem_mem ..
    have entryBounded := storeBounded store[id] entryMember
    have entryFixed := storeNormalized store[id] entryMember
    simpa [MStore.defaultValuation,
      List.getElem?_eq_getElem idBounded] using
        (realize_eq_default entryBounded entryFixed).symm

theorem InferState.has_model
    {state : InferState} {rigidCount : Nat}
    (safe : state.Safe rigidCount) :
    ∃ valuation, state.Models rigidCount valuation := by
  refine ⟨state.solutions.defaultValuation, ?_⟩
  exact MStore.defaultValuation_models safe.solutions_length
    safe.solutionsScoped safe.solutionsBounded safe.solutionsNormalized

end EPL
