import EPL.Properties.InferenceModelProjection

namespace EPL

def MValuation.AgreeBelow
    (first second : MValuation) (frontier : Nat) : Prop :=
  ∀ id, id < frontier → first id = second id

theorem MValuation.AgreeBelow.refl
    (valuation : MValuation) (frontier : Nat) :
    valuation.AgreeBelow valuation frontier := by
  intro id _
  rfl

theorem Ty.realize_eq_of_agree
    {ty : Ty} {first second : MValuation} {frontier : Nat}
    (bounded : ty.MVarBounded frontier)
    (agree : first.AgreeBelow second frontier) :
    ty.realize first = ty.realize second := by
  induction ty with
  | prim name => rfl
  | arrow domain codomain ihDomain ihCodomain =>
      have domainBounded : domain.MVarBounded frontier := by
        intro id member
        exact bounded id (by simp [Ty.mvars, member])
      have codomainBounded : codomain.MVarBounded frontier := by
        intro id member
        exact bounded id (by simp [Ty.mvars, member])
      simp only [Ty.realize, ihDomain domainBounded, ihCodomain codomainBounded]
  | bvar index => rfl
  | rigid level => rfl
  | mvar id =>
      exact agree id (bounded id (by simp [Ty.mvars]))

theorem PolyTy.realize_eq_of_agree
    {scheme : PolyTy} {first second : MValuation} {frontier : Nat}
    (bounded : scheme.body.MVarBounded frontier)
    (agree : first.AgreeBelow second frontier) :
    scheme.realize first = scheme.realize second := by
  cases scheme with
  | mk count body =>
      simp only [PolyTy.realize, Scheme.mk.injEq, true_and]
      exact Ty.realize_eq_of_agree bounded agree

theorem Ctx.realize_eq_of_agree
    {ctx : Ctx} {first second : MValuation} {frontier : Nat}
    (bounded : ∀ scheme ∈ ctx, scheme.body.MVarBounded frontier)
    (agree : first.AgreeBelow second frontier) :
    ctx.realize first = ctx.realize second := by
  induction ctx with
  | nil => rfl
  | cons scheme tail ih =>
      have schemeBounded : scheme.body.MVarBounded frontier :=
        bounded scheme (by simp)
      have tailBounded : ∀ candidate ∈ tail,
          candidate.body.MVarBounded frontier := by
        intro candidate member
        exact bounded candidate (by simp [member])
      have tailEq := ih tailBounded
      simp only [Ctx.realize] at tailEq
      simp only [Ctx.realize, List.map_cons]
      rw [PolyTy.realize_eq_of_agree schemeBounded agree, tailEq]

/-- A model can be transported to an agreeing semantic valuation when the
table itself is bounded by the agreement frontier. -/
theorem MStore.Models.of_agree
    {store : MStore} {first second : MValuation}
    {rigidCount frontier : Nat}
    (length : store.length = frontier)
    (storeBounded : store.Bounded frontier)
    (firstModels : store.Models rigidCount first)
    (secondWF : second.WF rigidCount frontier)
    (agree : first.AgreeBelow second frontier) :
    store.Models rigidCount second := by
  constructor
  · intro id idBounded
    exact secondWF id (by simpa [length] using idBounded)
  · intro id idBounded
    have idFrontier : id < frontier := by simpa [length] using idBounded
    have entryBounded : store[id].MVarBounded frontier :=
      storeBounded store[id] (List.getElem_mem ..)
    calc
      second id = first id := (agree id idFrontier).symm
      _ = store[id].realize first := firstModels.equation id idBounded
      _ = store[id].realize second :=
        Ty.realize_eq_of_agree entryBounded agree

end EPL
