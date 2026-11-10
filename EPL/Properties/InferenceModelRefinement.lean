import EPL.Properties.InferenceModelAnnotations

namespace EPL

/-- Every semantic model of `newer` is already a model of `older`. -/
def MStore.Refines
    (older newer : MStore) (rigidCount : Nat) : Prop :=
  ∀ valuation, newer.Models rigidCount valuation →
    older.Models rigidCount valuation

def InferState.Refines
    (older newer : InferState) (rigidCount : Nat) : Prop :=
  older.solutions.Refines newer.solutions rigidCount

theorem MStore.Refines.refl (store : MStore) (rigidCount : Nat) :
    store.Refines store rigidCount := by
  intro valuation models
  exact models

theorem MStore.Refines.trans
    {first second third : MStore} {rigidCount : Nat}
    (firstSecond : first.Refines second rigidCount)
    (secondThird : second.Refines third rigidCount) :
    first.Refines third rigidCount := by
  intro valuation thirdModels
  exact firstSecond valuation (secondThird valuation thirdModels)

/-- A model of a table also models any literal prefix of that table. -/
theorem MStore.Models.prefix
    {older newer : MStore} {valuation : MValuation} {rigidCount : Nat}
    (models : newer.Models rigidCount valuation)
    (prefixEq : newer.take older.length = older) :
    older.Models rigidCount valuation := by
  have lengthLe : older.length ≤ newer.length := by
    have lengths := congrArg List.length prefixEq
    simp only [List.length_take] at lengths
    omega
  constructor
  · intro id idLt
    exact models.valuationWF id (lt_of_lt_of_le idLt lengthLe)
  · intro id idLt
    have idNewer : id < newer.length := lt_of_lt_of_le idLt lengthLe
    have entryEq : newer[id] = older[id] := by
      have gets := congrArg (fun entries => entries[id]?) prefixEq
      simp only [List.getElem?_take_of_lt idLt,
        List.getElem?_eq_getElem idNewer,
        List.getElem?_eq_getElem idLt] at gets
      exact Option.some.inj gets
    rw [← entryEq]
    exact models.equation id idNewer

theorem InferState.fresh_refines
    {state : InferState} {rigidCount : Nat} :
    state.Refines state.fresh.1 rigidCount := by
  intro valuation models
  apply models.prefix
  simp [InferState.fresh]

theorem InferState.freshRequired_refines
    {state : InferState} {rigidCount : Nat} :
    state.Refines state.freshRequired.1 rigidCount := by
  intro valuation models
  apply models.prefix
  simp [InferState.freshRequired]

theorem InferState.freshMany_refines
    {state : InferState} {rigidCount count : Nat} :
    state.Refines (state.freshMany count).1 rigidCount := by
  induction count generalizing state with
  | zero => exact MStore.Refines.refl state.solutions rigidCount
  | succ count ih =>
      have first : state.Refines state.fresh.1 rigidCount :=
        InferState.fresh_refines
      have rest : state.fresh.1.Refines
          (state.fresh.1.freshMany count).1 rigidCount := ih
      simpa [InferState.freshMany] using first.trans rest

theorem InferState.allocate_refines
    {state : InferState} {template : Template} {rigidCount : Nat} :
    state.Refines (state.allocate template).1 rigidCount := by
  intro valuation models
  apply models.prefix
  simp [InferState.allocate]

/-- Solving a constraint only restricts the set of semantic models; it never
changes the meaning of any previously allocated metavariable. -/
theorem InferState.constrain_refines
    {state checked : InferState} {left right : Ty} {rigidCount : Nat}
    (safe : state.Safe rigidCount)
    (run : state.constrain left right = some checked) :
    state.Refines checked rigidCount := by
  simp only [InferState.constrain] at run
  cases hdelta : unify (state.solutions.apply left)
      (state.solutions.apply right) with
  | none => simp [hdelta] at run
  | some delta =>
      rw [hdelta] at run
      simp only [Option.some.injEq] at run
      subst checked
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
            have idBounded : id < state.next :=
              bounded id (by simp [Ty.mvars])
            have idInStore : id < state.solutions.length := by
              simpa [safe.solutions_length] using idBounded
            simp only [MStore.apply, List.getElem?_map,
              List.getElem?_eq_getElem idInStore, Option.map_some,
              Option.getD_some]
      intro valuation models
      constructor
      · intro id idBounded
        exact models.valuationWF id (by simpa using idBounded)
      · intro id idBounded
        have idInStore : id < state.solutions.length := by
          simpa using idBounded
        let oldTy := state.solutions[id]
        have oldMember : oldTy ∈ state.solutions := by
          exact List.getElem_mem ..
        have oldBounded : oldTy.MVarBounded state.next :=
          safe.solutionsBounded oldTy oldMember
        have oldFixed : state.solutions.apply oldTy = oldTy :=
          safe.solutionsNormalized oldTy oldMember
        have semanticFixed := models.realize_apply oldTy
        rw [mapApply oldBounded, oldFixed] at semanticFixed
        have checkedEquation := models.equation id (by simpa using idBounded)
        have checkedEquation' : valuation id =
            (delta.apply oldTy).realize valuation := by
          simpa [oldTy] using checkedEquation
        exact checkedEquation'.trans semanticFixed

end EPL
