import EPL.Properties.InferenceSafety

namespace EPL

abbrev MValuation := Nat → Ty

/-- Interpret every inference metavariable through a semantic valuation. The
valuation's images are required separately to be well-formed semantic types. -/
def Ty.realize (valuation : MValuation) : Ty → Ty
  | .prim p => .prim p
  | .arrow domain codomain =>
      .arrow (domain.realize valuation) (codomain.realize valuation)
  | .bvar index => .bvar index
  | .rigid level => .rigid level
  | .mvar id => valuation id

def PolyTy.realize (scheme : PolyTy) (valuation : MValuation) : PolyTy :=
  ⟨scheme.paramCount, scheme.body.realize valuation⟩

def Ctx.realize (ctx : Ctx) (valuation : MValuation) : Ctx :=
  ctx.map (·.realize valuation)

def HoleAssignment.realize
    (holes : HoleAssignment) (valuation : MValuation) : HoleAssignment :=
  holes.map fun entry => (entry.1, entry.2.realize valuation)

def MValuation.WF
    (valuation : MValuation) (rigidCount frontier : Nat) : Prop :=
  ∀ id, id < frontier → (valuation id).WF rigidCount 0

/-- A valuation models a dense table when it gives semantic meanings to every
allocated ID and satisfies every table equation simultaneously. -/
structure MStore.Models
    (store : MStore) (rigidCount : Nat) (valuation : MValuation) : Prop where
  valuationWF : valuation.WF rigidCount store.length
  equation : ∀ id, (h : id < store.length) →
    valuation id = (store[id]).realize valuation

def InferState.Models
    (state : InferState) (rigidCount : Nat) (valuation : MValuation) : Prop :=
  state.solutions.Models rigidCount valuation

theorem Ty.realize_eq_self
    {ty : Ty} (metaFree : ty.MetaFree) (valuation : MValuation) :
    ty.realize valuation = ty := by
  induction metaFree with
  | prim => rfl
  | arrow _ _ ihDomain ihCodomain =>
      simp only [Ty.realize, ihDomain, ihCodomain]
  | bvar => rfl
  | rigid => rfl

theorem Ty.realize_inferWF
    {ty : Ty} {valuation : MValuation}
    {rigidCount binderCount frontier : Nat}
    (typeWF : ty.InferWF rigidCount binderCount frontier)
    (valuationWF : valuation.WF rigidCount frontier) :
    (ty.realize valuation).WF rigidCount binderCount := by
  induction ty with
  | prim name =>
      exact ⟨.prim, .prim⟩
  | arrow domain codomain ihDomain ihCodomain =>
      cases typeWF.1 with
      | arrow domainScoped codomainScoped =>
        have domainBounded : domain.MVarBounded frontier := by
          intro id member
          exact typeWF.2 id (by simp [Ty.mvars, member])
        have codomainBounded : codomain.MVarBounded frontier := by
          intro id member
          exact typeWF.2 id (by simp [Ty.mvars, member])
        have domainWF := ihDomain ⟨domainScoped, domainBounded⟩
        have codomainWF := ihCodomain ⟨codomainScoped, codomainBounded⟩
        exact ⟨.arrow domainWF.1 codomainWF.1,
          .arrow domainWF.2 codomainWF.2⟩
  | bvar index =>
      cases typeWF.1 with
      | bvar hlt => exact ⟨.bvar hlt, .bvar⟩
  | rigid level =>
      cases typeWF.1 with
      | rigid hlt => exact ⟨.rigid hlt, .rigid⟩
  | mvar id =>
      have idBounded : id < frontier :=
        typeWF.2 id (by simp [Ty.mvars])
      have realizedWF := valuationWF id idBounded
      have scoped_mono_binder : ∀ {candidate : Ty},
          candidate.Scoped rigidCount 0 →
            candidate.Scoped rigidCount binderCount := by
        intro candidate candidateScoped
        induction candidateScoped with
        | prim => exact .prim
        | arrow _ _ ihDomain ihCodomain => exact .arrow ihDomain ihCodomain
        | bvar hlt => omega
        | rigid hlt => exact .rigid hlt
        | mvar id => exact .mvar id
      exact ⟨scoped_mono_binder realizedWF.1, realizedWF.2⟩

theorem PolyTy.realize_wf
    {scheme : PolyTy} {valuation : MValuation}
    {rigidCount frontier : Nat}
    (schemeWF : scheme.InferWF rigidCount frontier)
    (valuationWF : valuation.WF rigidCount frontier) :
    (scheme.realize valuation).WF rigidCount := by
  exact Ty.realize_inferWF schemeWF valuationWF

theorem Ctx.realize_wf
    {ctx : Ctx} {valuation : MValuation}
    {rigidCount frontier : Nat}
    (ctxWF : ctx.InferWF rigidCount frontier)
    (valuationWF : valuation.WF rigidCount frontier) :
    (ctx.realize valuation).WF rigidCount := by
  intro scheme member
  rcases List.mem_map.mp member with ⟨original, originalMember, rfl⟩
  exact PolyTy.realize_wf (ctxWF original originalMember) valuationWF

theorem Ty.realize_openWith
    {ty : Ty} {args : List Ty} {valuation : MValuation}
    {rigidCount binderCount frontier : Nat}
    (typeWF : ty.InferWF rigidCount binderCount frontier)
    (valuationWF : valuation.WF rigidCount frontier) :
    (ty.openWith args).realize valuation =
      (ty.realize valuation).openWith (args.map (·.realize valuation)) := by
  have openWith_eq_self : ∀ {candidate : Ty},
      candidate.Scoped rigidCount 0 →
        candidate.openWith (args.map (·.realize valuation)) = candidate := by
    intro candidate candidateScoped
    induction candidateScoped with
    | prim => rfl
    | arrow _ _ ihDomain ihCodomain =>
        simp only [Ty.openWith, ihDomain, ihCodomain]
    | bvar hlt => omega
    | rigid => rfl
    | mvar id => rfl
  induction ty with
  | prim name => rfl
  | arrow domain codomain ihDomain ihCodomain =>
      cases typeWF.1 with
      | arrow domainScoped codomainScoped =>
        have domainWF : domain.InferWF rigidCount binderCount frontier :=
          ⟨domainScoped, fun id member => typeWF.2 id (by
            simp [Ty.mvars, member])⟩
        have codomainWF : codomain.InferWF rigidCount binderCount frontier :=
          ⟨codomainScoped, fun id member => typeWF.2 id (by
            simp [Ty.mvars, member])⟩
        simp only [Ty.openWith, Ty.realize, ihDomain domainWF,
          ihCodomain codomainWF]
  | bvar index =>
      simp only [Ty.openWith, Ty.realize, List.getElem?_map]
      cases args[index]? <;> rfl
  | rigid level => rfl
  | mvar id =>
      have idBounded : id < frontier := typeWF.2 id (by simp [Ty.mvars])
      simpa [Ty.openWith, Ty.realize] using
        (openWith_eq_self (valuationWF id idBounded).1).symm

theorem Ty.realize_openRigidsFrom
    {ty : Ty} {valuation : MValuation}
    {rigidCount depth count frontier : Nat}
    (typeWF : ty.InferWF rigidCount (depth + count) frontier)
    (valuationWF : valuation.WF rigidCount frontier) :
    (ty.openRigidsFrom depth rigidCount count).realize valuation =
      (ty.realize valuation).openRigidsFrom depth rigidCount count := by
  have open_eq_self : ∀ {candidate : Ty},
      candidate.Scoped rigidCount 0 →
        candidate.openRigidsFrom depth rigidCount count = candidate := by
    intro candidate candidateScoped
    induction candidateScoped with
    | prim => rfl
    | arrow _ _ ihDomain ihCodomain =>
        simp only [Ty.openRigidsFrom, ihDomain, ihCodomain]
    | bvar hlt => omega
    | rigid => rfl
    | mvar id => rfl
  induction ty with
  | prim name => rfl
  | arrow domain codomain ihDomain ihCodomain =>
      cases typeWF.1 with
      | arrow domainScoped codomainScoped =>
        have domainWF : domain.InferWF rigidCount (depth + count) frontier :=
          ⟨domainScoped, fun id member => typeWF.2 id (by
            simp [Ty.mvars, member])⟩
        have codomainWF : codomain.InferWF rigidCount (depth + count) frontier :=
          ⟨codomainScoped, fun id member => typeWF.2 id (by
            simp [Ty.mvars, member])⟩
        simp only [Ty.openRigidsFrom, Ty.realize, ihDomain domainWF,
          ihCodomain codomainWF]
  | bvar index =>
      simp only [Ty.openRigidsFrom, Ty.realize]
      split
      · rfl
      · split <;> rfl
  | rigid level => rfl
  | mvar id =>
      have idBounded : id < frontier := typeWF.2 id (by simp [Ty.mvars])
      simpa [Ty.openRigidsFrom, Ty.realize] using
        (open_eq_self (valuationWF id idBounded).1).symm

theorem Ty.realize_closeRigids
    {ty : Ty} {valuation : MValuation}
    {rigidCount count frontier : Nat}
    (typeWF : ty.InferWF (rigidCount + count) 0 frontier)
    (valuationWF : valuation.WF rigidCount frontier) :
    (ty.closeRigids rigidCount count).realize valuation =
      (ty.realize valuation).closeRigids rigidCount count := by
  have close_eq_self : ∀ {candidate : Ty},
      candidate.Scoped rigidCount 0 →
        candidate.closeRigids rigidCount count = candidate := by
    intro candidate candidateScoped
    induction candidateScoped with
    | prim => rfl
    | arrow _ _ ihDomain ihCodomain =>
        simp only [Ty.closeRigids, ihDomain, ihCodomain]
    | bvar hlt => omega
    | rigid hlt => simp [Ty.closeRigids, hlt]
    | mvar id => rfl
  induction ty with
  | prim name => rfl
  | arrow domain codomain ihDomain ihCodomain =>
      cases typeWF.1 with
      | arrow domainScoped codomainScoped =>
        have domainWF : domain.InferWF (rigidCount + count) 0 frontier :=
          ⟨domainScoped, fun id member => typeWF.2 id (by
            simp [Ty.mvars, member])⟩
        have codomainWF : codomain.InferWF (rigidCount + count) 0 frontier :=
          ⟨codomainScoped, fun id member => typeWF.2 id (by
            simp [Ty.mvars, member])⟩
        simp only [Ty.closeRigids, Ty.realize, ihDomain domainWF,
          ihCodomain codomainWF]
  | bvar index =>
      cases typeWF.1 with
      | bvar hlt => omega
  | rigid level =>
      simp only [Ty.closeRigids, Ty.realize]
      split
      · rfl
      · split <;> rfl
  | mvar id =>
      have idBounded : id < frontier := typeWF.2 id (by simp [Ty.mvars])
      simpa [Ty.closeRigids, Ty.realize] using
        (close_eq_self (valuationWF id idBounded).1).symm

/-- Looking up algorithmic solutions is semantically invisible in every model
of the dense table. -/
theorem MStore.Models.realize_apply
    {store : MStore} {valuation : MValuation} {rigidCount : Nat}
    (models : store.Models rigidCount valuation) (ty : Ty) :
    (store.apply ty).realize valuation = ty.realize valuation := by
  induction ty with
  | prim name => rfl
  | arrow domain codomain ihDomain ihCodomain =>
      simp only [MStore.apply, Ty.realize, ihDomain, ihCodomain]
  | bvar index => rfl
  | rigid level => rfl
  | mvar id =>
      by_cases inStore : id < store.length
      · rw [MStore.apply, List.getElem?_eq_getElem inStore, Option.getD_some,
          Ty.realize]
        exact (models.equation id inStore).symm
      · rw [MStore.apply,
          List.getElem?_eq_none_iff.mpr (Nat.le_of_not_gt inStore),
          Option.getD_none]

end EPL
