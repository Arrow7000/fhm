import EPL.Properties.InferenceState
import EPL.Properties.Declarative

namespace EPL

def PolyTy.realize (scheme : PolyTy) (valuation : MValuation) : PolyTy :=
  ⟨scheme.paramCount, scheme.body.realize valuation⟩

def Ctx.realize (ctx : Ctx) (valuation : MValuation) : Ctx :=
  ctx.map (·.realize valuation)

def HoleAssignment.realize
    (holes : HoleAssignment) (valuation : MValuation) : HoleAssignment :=
  holes.map fun entry => (entry.1, entry.2.realize valuation)

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

end EPL

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
  fun id => (store.apply (.mvar id)).defaultMVars

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

/-- If every metavariable mentioned by a type is still unsolved, resolving it
through the store leaves it unchanged. -/
private theorem MStore.apply_eq_self_of_lookup_none (store : MStore) (ty : Ty)
    (unsolved : ∀ id ∈ ty.mvars, store.lookup id = none) :
    store.apply ty = ty := by
  induction ty with
  | prim name => rfl
  | arrow domain codomain ihDomain ihCodomain =>
      have domainUnsolved : ∀ id ∈ domain.mvars, store.lookup id = none := by
        intro id inside
        exact unsolved id (by
          simp only [Ty.mvars, List.mem_dedup, List.mem_append]
          exact Or.inl inside)
      have codomainUnsolved : ∀ id ∈ codomain.mvars, store.lookup id = none := by
        intro id inside
        exact unsolved id (by
          simp only [Ty.mvars, List.mem_dedup, List.mem_append]
          exact Or.inr inside)
      simp only [MStore.apply]
      rw [ihDomain domainUnsolved, ihCodomain codomainUnsolved]
  | bvar index => rfl
  | rigid level => rfl
  | mvar id =>
      have noneLookup := unsolved id (by simp [Ty.mvars])
      simp only [MStore.apply, noneLookup]
      rfl

/-- A solved lookup witnesses a solved entry in the table. -/
private theorem MStore.entry_of_lookup_eq_some {store : MStore} {id : Nat} {ty : Ty}
    (lookupEq : store.lookup id = some ty) : store[id]? = some (some ty) := by
  simp only [MStore.lookup] at lookupEq
  cases entry : store[id]? with
  | none => simp [entry] at lookupEq
  | some option =>
      cases option with
      | none => simp [entry] at lookupEq
      | some ty' => simpa [entry] using lookupEq

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
        simp only [Ty.realize, MStore.defaultValuation]
        rw [typeFixed]
  refine ⟨?_, ?_⟩
  · intro id idBounded
    cases entry : store[id]? with
    | none =>
        have lookupNone : store.lookup id = none := by
          simp [MStore.lookup, entry]
        simp only [MStore.defaultValuation, MStore.apply, lookupNone,
          Option.getD_none, Ty.defaultMVars]
        exact ⟨.prim, .prim⟩
    | some option =>
        cases option with
        | none =>
            have lookupNone : store.lookup id = none := by
              simp [MStore.lookup, entry]
            simp only [MStore.defaultValuation, MStore.apply, lookupNone,
              Option.getD_none, Ty.defaultMVars]
            exact ⟨.prim, .prim⟩
        | some ty =>
            have solvedEntry : store[id]? = some (some ty) := entry
            have tyMember : some ty ∈ store := List.mem_of_getElem? solvedEntry
            have lookupSome : store.lookup id = some ty := by
              simp [MStore.lookup, entry]
            simpa [MStore.defaultValuation, MStore.apply, lookupSome] using
              Ty.defaultMVars_wf (storeScoped ty tyMember)
  · intro id ty entry
    have tyMember : some ty ∈ store := List.mem_of_getElem? entry
    have tyBounded : ty.MVarBounded frontier := storeBounded ty tyMember
    have tyFixed : store.apply ty = ty :=
      MStore.apply_eq_self_of_lookup_none store ty
        (storeNormalized ty tyMember)
    have realizeEq : ty.realize store.defaultValuation = ty.defaultMVars :=
      realize_eq_default tyBounded tyFixed
    have lookupSome : store.lookup id = some ty := by
      simp [MStore.lookup, entry]
    simp only [MStore.defaultValuation, MStore.apply, lookupSome,
      Option.getD_some]
    rw [realizeEq]

theorem InferState.has_model
    {state : InferState} {rigidCount : Nat}
    (safe : state.Safe rigidCount) :
    ∃ valuation, state.Models rigidCount valuation := by
  refine ⟨state.solutions.defaultValuation, ?_⟩
  exact MStore.defaultValuation_models safe.solutions_length
    safe.solutionsScoped safe.solutionsBounded safe.solutionsNormalized

end EPL

namespace EPL

theorem HoleAssignment.realize_unique
    {holes : HoleAssignment} {valuation : MValuation}
    (unique : holes.Unique) :
    (holes.realize valuation).Unique := by
  simpa [HoleAssignment.Unique, HoleAssignment.realize, List.map_map,
    Function.comp_def] using unique

/-- Realizing flexible types preserves a fit against an authored, meta-free
template; named-hole sharing is transported through the same local table. -/
theorem Template.Fits.realize
    {holes : HoleAssignment} {template : Template} {ty : Ty}
    {valuation : MValuation} {rigidCount binderCount : Nat}
    (templateScoped : template.Scoped rigidCount binderCount)
    (fits : template.Fits holes ty) :
    template.Fits (holes.realize valuation) (ty.realize valuation) := by
  have lookup_realize : ∀ (assignments : HoleAssignment) (name : String),
      (assignments.realize valuation).lookup name =
        (assignments.lookup name).map (·.realize valuation) := by
    intro assignments name
    induction assignments with
    | nil => rfl
    | cons entry rest ih =>
        rcases entry with ⟨key, value⟩
        simp only [HoleAssignment.realize, List.map_cons, List.lookup]
        split
        · rfl
        · simpa [HoleAssignment.realize] using ih
  induction fits with
  | fixed =>
      cases templateScoped with
      | fixed typeWF =>
          rw [Ty.realize_eq_self typeWF.2 valuation]
          exact .fixed
  | hole => exact .hole
  | named lookup =>
      cases templateScoped
      apply Template.Fits.named
      rw [lookup_realize, lookup]
      rfl
  | arrow domainFit codomainFit domainIH codomainIH =>
      cases templateScoped with
      | arrow domainScoped codomainScoped =>
          exact .arrow (domainIH domainScoped) (codomainIH codomainScoped)

theorem Template.matches_realize
    {template : Template} {ty : Ty} {valuation : MValuation}
    {rigidCount binderCount : Nat}
    (templateScoped : template.Scoped rigidCount binderCount)
    (hMatches : template.Matches ty) :
    template.Matches (ty.realize valuation) := by
  have hmatches : template.Matches ty := by assumption
  rcases hmatches with ⟨holes, unique, fits⟩
  exact ⟨holes.realize valuation,
    HoleAssignment.realize_unique unique,
    Template.Fits.realize templateScoped fits⟩

theorem ParamAnn.matches_realize
    {ann : ParamAnn} {ty : Ty} {valuation : MValuation}
    {rigidCount binderCount : Nat}
    (annScoped : ∀ template, ann = some template →
      template.Scoped rigidCount binderCount)
    (hMatches : ann.Matches ty) :
    ann.Matches (ty.realize valuation) := by
  have hmatches : ann.Matches ty := by assumption
  intro template annEq
  exact Template.matches_realize (annScoped template annEq)
    (hmatches template annEq)

/-- Allocation followed by any semantic realization is a declarative match of
the original annotation. -/
theorem Template.allocate_matches_realize
    {template : Template} {valuation : MValuation}
    {rigidCount binderCount frontier : Nat}
    (templateScoped : template.Scoped rigidCount binderCount) :
    template.Matches ((template.allocate frontier).ty.realize valuation) := by
  exact Template.matches_realize templateScoped
    ⟨(template.allocate frontier).holes,
      Template.allocate_unique template frontier,
      Template.allocate_fits template frontier⟩

end EPL

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
  · intro id ty entry
    have idLt : id < older.length := by
      by_contra outOfRange
      have noneEq : older[id]? = none :=
        List.getElem?_eq_none_iff.mpr (by omega)
      rw [noneEq] at entry
      exact Option.noConfusion entry
    have idNewer : id < newer.length := lt_of_lt_of_le idLt lengthLe
    have prefixAt : newer[id]? = older[id]? := by
      have gets : (newer.take older.length)[id]? = older[id]? :=
        congrArg (fun entries => entries[id]?) prefixEq
      rw [List.getElem?_take_of_lt idLt] at gets
      exact gets
    exact models.equation id ty (by rw [prefixAt]; exact entry)

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
  unfold InferState.constrain at run
  cases hunify : state.solutions.unify left right with
  | none => simp [hunify] at run
  | some solutions =>
      simp only [hunify, Option.map_some, Option.some.injEq] at run
      subst checked
      intro valuation models
      exact (MStore.unify_sound hunify models).1

end EPL

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
    ((store.lookup id).map (·.realize baseValuation)).getD (baseValuation id)
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
  have local_eq_base_of_mem : ∀ {ty : Ty}, some ty ∈ store →
      ∀ {id : Nat}, id ∈ ty.mvars → localValuation id = baseValuation id := by
    intro ty tyMember id idMember
    have lookupNone := storeNormalized ty tyMember id idMember
    simp [localValuation, lookupNone]
  have entry_realize_eq : ∀ {ty : Ty}, some ty ∈ store →
      ty.realize localValuation = ty.realize baseValuation := by
    intro ty tyMember
    apply realize_congr_on
    intro id idMember
    exact local_eq_base_of_mem tyMember idMember
  refine ⟨localValuation, ?_, ?_⟩
  · constructor
    · intro id idBounded
      cases lookupEq : store.lookup id with
      | none =>
          have localEq : localValuation id = baseValuation id := by
            simp [localValuation, lookupEq]
          rw [localEq]
          exact baseWF id idBounded
      | some ty =>
          have entry : store[id]? = some (some ty) := by
            exact MStore.entry_of_lookup_eq_some lookupEq
          have tyMember : some ty ∈ store := List.mem_of_getElem? entry
          have entryWF : ty.InferWF (rigidCount + count) 0 store.length :=
            ⟨storeScoped ty tyMember, storeBounded ty tyMember⟩
          have localEq : localValuation id = ty.realize baseValuation := by
            simp [localValuation, lookupEq]
          rw [localEq]
          exact Ty.realize_inferWF entryWF baseWF
    · intro id ty entry
      have tyMember : some ty ∈ store := List.mem_of_getElem? entry
      have lookupSome : store.lookup id = some ty := by
        simp [MStore.lookup, entry]
      have localAt : localValuation id = ty.realize baseValuation := by
        simp [localValuation, lookupSome]
      rw [localAt]
      exact (entry_realize_eq tyMember).symm
  · intro id idOuter
    cases lookupEq : store.lookup id with
    | none =>
        have localEq : localValuation id = baseValuation id := by
          simp [localValuation, lookupEq]
        have baseEq : baseValuation id = outerValuation id := by
          simp [baseValuation, idOuter]
        rw [localEq, baseEq]
    | some ty =>
        have entry : store[id]? = some (some ty) := by
          exact MStore.entry_of_lookup_eq_some lookupEq
        have entryTake : (store.take cutoff)[id]? = some (some ty) := by
          have gets := List.getElem?_take_of_lt (l := store) idOuter
          rw [entry] at gets
          exact gets
        have outerEq := outerModels.equation id ty entryTake
        have tyMemberTake : some ty ∈ store.take cutoff :=
          List.mem_of_getElem? entryTake
        have tyBoundedCut : ∀ candidate ∈ ty.mvars, candidate < cutoff :=
          (escaped ty tyMemberTake).2
        have baseAgree : ty.realize baseValuation =
            ty.realize outerValuation := by
          apply realize_congr_on
          intro candidate candidateMember
          simp [baseValuation, tyBoundedCut candidate candidateMember]
        have localEq : localValuation id = ty.realize baseValuation := by
          simp [localValuation, lookupEq]
        rw [localEq, baseAgree, ← outerEq]

end EPL

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
  · intro id ty entry
    have idBounded : id < store.length := by
      by_contra outOfRange
      have noneEq : store[id]? = none :=
        List.getElem?_eq_none_iff.mpr (by omega)
      rw [noneEq] at entry
      exact Option.noConfusion entry
    have idFrontier : id < frontier := by simpa [length] using idBounded
    have tyMember : some ty ∈ store := List.mem_of_getElem? entry
    have entryBounded : ty.MVarBounded frontier := storeBounded ty tyMember
    calc
      second id = first id := (agree id idFrontier).symm
      _ = ty.realize first := firstModels.equation id ty entry
      _ = ty.realize second :=
        Ty.realize_eq_of_agree entryBounded agree

end EPL

namespace EPL

/-- Closing the fresh rigid block used to check a written scheme is inverse to
opening the resulting scheme at that same outer boundary. -/
theorem PolyTy.openRigids_closeRigids
    {openTy : Ty} {rigidCount count : Nat}
    (openScoped : openTy.Scoped (rigidCount + count) 0) :
    PolyTy.openRigids
      (⟨count, openTy.closeRigids rigidCount count⟩ : PolyTy)
      rigidCount = openTy := by
  change (openTy.closeRigids rigidCount count).openWith
    (rigidBlock rigidCount count) = openTy
  induction openScoped with
  | prim => rfl
  | arrow _ _ ihDomain ihCodomain =>
      simp only [Ty.closeRigids, Ty.openWith, ihDomain, ihCodomain]
  | bvar hlt => omega
  | rigid hlt =>
      rename_i level
      simp only [Ty.closeRigids]
      by_cases hOuter : level < rigidCount
      · rw [if_pos hOuter]
        rfl
      · rw [if_neg hOuter]
        have hLocal : level - rigidCount < count := by omega
        rw [if_pos hLocal]
        simp only [Ty.openWith, rigidBlock, List.getElem?_map]
        have hIndex : level - rigidCount < (List.range count).length := by
          simpa using hLocal
        rw [List.getElem?_eq_getElem hIndex, Option.map_some,
          Option.getD_some, List.getElem_range]
        congr
        omega
  | mvar id => rfl

/-- A match against an opened written template closes back to a match against
the original template, preserving local named-hole coherence. -/
theorem Template.matches_closeRigids
    {template : Template} {openTy : Ty} {rigidCount count : Nat}
    (templateScoped : template.Scoped rigidCount count)
    (openScoped : openTy.Scoped (rigidCount + count) 0)
    (openedMatches :
      (template.openRigidsFrom 0 rigidCount count).Matches openTy) :
    template.Matches (openTy.closeRigids rigidCount count) := by
  let closeHoles : HoleAssignment → HoleAssignment :=
    List.map fun entry =>
      (entry.1, entry.2.closeRigids rigidCount count)
  have closeHoles_unique : ∀ {holes : HoleAssignment},
      holes.Unique → (closeHoles holes).Unique := by
    intro holes unique
    simpa [HoleAssignment.Unique, closeHoles, List.map_map,
      Function.comp_def] using unique
  have closeHoles_lookup : ∀ (holes : HoleAssignment) (name : String),
      (closeHoles holes).lookup name =
        (holes.lookup name).map (Ty.closeRigids rigidCount count) := by
    intro holes name
    induction holes with
    | nil => rfl
    | cons entry rest ih =>
        rcases entry with ⟨key, ty⟩
        simp only [closeHoles, List.map_cons, List.lookup]
        split
        · rfl
        · simpa [closeHoles] using ih
  have close_open : ∀ {ty : Ty}, ty.Scoped rigidCount count →
      (ty.openRigidsFrom 0 rigidCount count).closeRigids
        rigidCount count = ty := by
    intro ty typeScoped
    induction typeScoped with
    | prim => rfl
    | arrow _ _ ihDomain ihCodomain =>
        simp only [Ty.openRigidsFrom, Ty.closeRigids, ihDomain, ihCodomain]
    | bvar hlt =>
        simp [Ty.openRigidsFrom, Ty.closeRigids, hlt]
    | rigid hlt =>
        simp [Ty.openRigidsFrom, Ty.closeRigids, hlt]
    | mvar id => rfl
  rcases openedMatches with ⟨holes, holesUnique, fits⟩
  refine ⟨closeHoles holes, closeHoles_unique holesUnique, ?_⟩
  induction templateScoped generalizing openTy holes with
  | fixed typeWF =>
      cases fits
      rw [close_open typeWF.1]
      exact .fixed
  | hole =>
      cases fits
      exact .hole
  | named =>
      cases fits with
      | named lookup =>
          apply Template.Fits.named
          rw [closeHoles_lookup, lookup]
          rfl
  | arrow _ _ ihDomain ihCodomain =>
      cases fits with
      | arrow domainFits codomainFits =>
          cases openScoped with
          | arrow domainOpenScoped codomainOpenScoped =>
              exact .arrow
                (ihDomain domainOpenScoped holes holesUnique domainFits)
                (ihCodomain codomainOpenScoped holes holesUnique codomainFits)

end EPL

namespace EPL

/-- Strong semantic soundness of the internal engine. A successful run both
refines its input state and yields a declarative typing derivation under every
semantic model of the result state. -/
theorem inferFuel_sound_model
    {fuel rigidCount : Nat} {ctx : Ctx} {input : Source}
    {state : InferState} {result : InferResult}
    (stateSafe : state.Safe rigidCount)
    (ctxWF : ctx.InferWF rigidCount state.next)
    (inputScoped : input.TypeScoped rigidCount 0)
    (run : inferFuel fuel rigidCount ctx input state = some result) :
    state.Refines result.state rigidCount ∧
      ∀ valuation, result.state.Models rigidCount valuation →
        Typing rigidCount (ctx.realize valuation) input
          (result.ty.realize valuation) := by
  have modelWF : ∀ {candidate : InferState} {valuation : MValuation}
      {rigid : Nat}, candidate.Safe rigid → candidate.Models rigid valuation →
        valuation.WF rigid candidate.next := by
    intro candidate valuation rigid safe models
    simpa [safe.solutions_length] using models.valuationWF
  have ctx_mono : ∀ {context : Ctx} {rigid smaller larger : Nat},
      context.InferWF rigid smaller → smaller ≤ larger →
        context.InferWF rigid larger := by
    intro context rigid smaller larger h le scheme member
    exact ⟨(h scheme member).1,
      fun id idMem => lt_of_lt_of_le ((h scheme member).2 id idMem) le⟩
  have inferWF_mono : ∀ {ty : Ty} {rigid binder smaller larger : Nat},
      ty.InferWF rigid binder smaller → smaller ≤ larger →
        ty.InferWF rigid binder larger := by
    intro ty rigid binder smaller larger h le
    exact ⟨h.1, fun id idMem => lt_of_lt_of_le (h.2 id idMem) le⟩
  have scoped_mono_rigid : ∀ {ty : Ty} {binder smaller larger : Nat},
      ty.Scoped smaller binder → smaller ≤ larger → ty.Scoped larger binder := by
    intro ty binder smaller larger h le
    induction h with
    | prim => exact .prim
    | arrow _ _ ihDomain ihCodomain => exact .arrow ihDomain ihCodomain
    | bvar hlt => exact .bvar hlt
    | rigid hlt => exact .rigid (lt_of_lt_of_le hlt le)
    | mvar id => exact .mvar id
  have ctx_mono_rigid : ∀ {context : Ctx} {frontier smaller larger : Nat},
      context.InferWF smaller frontier → smaller ≤ larger →
        context.InferWF larger frontier := by
    intro context frontier smaller larger h le scheme member
    exact ⟨scoped_mono_rigid (h scheme member).1 le, (h scheme member).2⟩
  have state_mono_rigid : ∀ {candidate : InferState} {smaller larger : Nat},
      candidate.Safe smaller → smaller ≤ larger → candidate.Safe larger := by
    intro candidate smaller larger h le
    exact ⟨h.solutions_length,
      (fun ty member => scoped_mono_rigid (h.solutionsScoped ty member) le),
      h.solutionsBounded, h.solutionsNormalized, h.requiredBounded⟩
  have metaFree_bounded : ∀ {ty : Ty} {frontier : Nat},
      ty.MetaFree → ty.MVarBounded frontier := by
    intro ty frontier h
    induction h with
    | prim => simp [Ty.MVarBounded, Ty.mvars]
    | arrow _ _ ihDomain ihCodomain =>
        intro id member
        simp only [Ty.mvars, List.mem_dedup, List.mem_append] at member
        exact member.elim (ihDomain id) (ihCodomain id)
    | bvar => simp [Ty.MVarBounded, Ty.mvars]
    | rigid => simp [Ty.MVarBounded, Ty.mvars]
  have wf_inferWF : ∀ {ty : Ty} {rigid binder frontier : Nat},
      ty.WF rigid binder → ty.InferWF rigid binder frontier := by
    intro ty rigid binder frontier h
    exact ⟨h.1, metaFree_bounded h.2⟩
  induction fuel generalizing rigidCount ctx input state result with
  | zero => simp [inferFuel] at run
  | succ fuel ih =>
      cases input with
      | primLit literal =>
          simp only [inferFuel, Option.some.injEq] at run
          subst result
          refine ⟨MStore.Refines.refl _ _, ?_⟩
          intro valuation models
          cases literal <;> exact Typing.primLit
      | primOp op =>
          simp only [inferFuel, Option.some.injEq] at run
          subst result
          refine ⟨MStore.Refines.refl _ _, ?_⟩
          intro valuation models
          cases op
          exact Typing.primOp
      | var index =>
          simp only [inferFuel] at run
          cases lookup : ctx[index]? with
          | none => simp [lookup] at run
          | some scheme =>
              simp only [lookup] at run
              let fresh := state.freshMany scheme.paramCount
              have resultEq : result =
                  ⟨fresh.1, (state.solutions.applyScheme scheme).openWith fresh.2⟩ :=
                Option.some.inj run.symm
              subst result
              have freshSafe := InferState.freshMany_safe
                (count := scheme.paramCount) stateSafe
              refine ⟨InferState.freshMany_refines, ?_⟩
              intro valuation models
              have stateModels : state.Models rigidCount valuation :=
                InferState.freshMany_refines valuation models
              have valuationWF : valuation.WF rigidCount fresh.1.next :=
                modelWF freshSafe.1 models
              have schemeMember : scheme ∈ ctx := List.mem_of_getElem? lookup
              have schemeWF := ctxWF scheme schemeMember
              have appliedWF : (state.solutions.applyScheme scheme).InferWF
                  rigidCount state.next :=
                MStore.apply_inferWF stateSafe.solutionsScoped
                  stateSafe.solutionsBounded schemeWF
              have argsWF : ∀ arg ∈ fresh.2,
                  (arg.realize valuation).WF rigidCount 0 := by
                intro arg member
                exact Ty.realize_inferWF
                  (freshSafe.2.1 arg member) valuationWF
              have resultTyEq :
                  ((state.solutions.applyScheme scheme).openWith fresh.2).realize
                      valuation =
                    (scheme.realize valuation).openWith
                      (fresh.2.map (·.realize valuation)) := by
                have opened := Ty.realize_openWith (args := fresh.2) appliedWF
                  (modelWF stateSafe stateModels)
                have appliedEq := stateModels.realize_apply scheme.body
                simpa [PolyTy.openWith, PolyTy.realize, MStore.applyScheme,
                  appliedEq] using opened
              rw [resultTyEq]
              apply Typing.var (scheme := scheme.realize valuation)
                  (args := fresh.2.map (·.realize valuation))
              · simp [Ctx.realize, lookup]
              · exact PolyTy.realize_wf schemeWF
                  (modelWF stateSafe stateModels)
              · simpa using freshSafe.2.2.1
              · intro arg member
                rcases List.mem_map.mp member with ⟨original, originalMem, rfl⟩
                exact argsWF original originalMem
      | lambda ann body =>
          cases inputScoped with
          | lambda annScoped bodyScoped =>
            cases ann with
            | none =>
                simp only [inferFuel] at run
                let seeded := state.freshRequired
                cases bodyRun : inferFuel fuel rigidCount
                    (PolyTy.mono seeded.2 :: ctx) body seeded.1 with
                | none => simp [seeded, bodyRun] at run
                | some bodyResult =>
                    have seededSafe := InferState.freshRequired_safe stateSafe
                    have bodyCtxWF : Ctx.InferWF
                        (PolyTy.mono seeded.2 :: ctx) rigidCount seeded.1.next := by
                      intro scheme member
                      simp only [List.mem_cons] at member
                      rcases member with rfl | member
                      · exact seededSafe.2.1
                      · exact ctx_mono ctxWF seededSafe.2.2 scheme member
                    have bodySound := ih seededSafe.1 bodyCtxWF bodyScoped bodyRun
                    dsimp [seeded] at bodyRun
                    rw [bodyRun] at run
                    have run := Option.some.inj run
                    subst result
                    refine ⟨InferState.freshRequired_refines.trans bodySound.1, ?_⟩
                    intro valuation models
                    have seededModels : seeded.1.Models rigidCount valuation :=
                      bodySound.1 valuation models
                    have paramWF := Ty.realize_inferWF seededSafe.2.1
                      (modelWF seededSafe.1 seededModels)
                    have bodyTyping := bodySound.2 valuation models
                    have annMatches : ParamAnn.Matches none
                        (seeded.2.realize valuation) := by
                      intro template impossible
                      cases impossible
                    have realizedBody : Typing rigidCount
                        (PolyTy.mono (seeded.2.realize valuation) ::
                          ctx.realize valuation) body
                        (bodyResult.ty.realize valuation) := by
                      simpa [Ctx.realize, PolyTy.realize, PolyTy.mono] using
                        bodyTyping
                    have lambdaTyping := Typing.lambda
                      (ann := none) (body := body) (ctx := ctx.realize valuation)
                      (bodyTy := bodyResult.ty.realize valuation)
                      paramWF annMatches realizedBody
                    simp only [Ty.realize]
                    rw [models.realize_apply seeded.2]
                    exact lambdaTyping
            | some template =>
                have templateScoped := annScoped template rfl
                simp only [inferFuel] at run
                let seeded := state.allocate template
                cases bodyRun : inferFuel fuel rigidCount
                    (PolyTy.mono seeded.2 :: ctx) body seeded.1 with
                | none => simp [seeded, bodyRun] at run
                | some bodyResult =>
                    have seededSafe := InferState.allocate_safe stateSafe templateScoped
                    have bodyCtxWF : Ctx.InferWF
                        (PolyTy.mono seeded.2 :: ctx) rigidCount seeded.1.next := by
                      intro scheme member
                      simp only [List.mem_cons] at member
                      rcases member with rfl | member
                      · exact seededSafe.2.1
                      · exact ctx_mono ctxWF seededSafe.2.2 scheme member
                    have bodySound := ih seededSafe.1 bodyCtxWF bodyScoped bodyRun
                    dsimp [seeded] at bodyRun
                    rw [bodyRun] at run
                    have run := Option.some.inj run
                    subst result
                    refine ⟨InferState.allocate_refines.trans bodySound.1, ?_⟩
                    intro valuation models
                    have seededModels : seeded.1.Models rigidCount valuation :=
                      bodySound.1 valuation models
                    have paramWF := Ty.realize_inferWF seededSafe.2.1
                      (modelWF seededSafe.1 seededModels)
                    have bodyTyping := bodySound.2 valuation models
                    have annMatches : ParamAnn.Matches (some template)
                        (seeded.2.realize valuation) := by
                      intro candidate annEq
                      cases annEq
                      exact Template.allocate_matches_realize templateScoped
                    have realizedBody : Typing rigidCount
                        (PolyTy.mono (seeded.2.realize valuation) ::
                          ctx.realize valuation) body
                        (bodyResult.ty.realize valuation) := by
                      simpa [Ctx.realize, PolyTy.realize, PolyTy.mono] using
                        bodyTyping
                    have lambdaTyping := Typing.lambda
                      (ann := some template) (body := body)
                      (bodyTy := bodyResult.ty.realize valuation)
                      (ctx := ctx.realize valuation) paramWF annMatches realizedBody
                    simp only [Ty.realize]
                    rw [models.realize_apply seeded.2]
                    exact lambdaTyping
      | app function argument =>
          cases inputScoped with
          | app functionScoped argumentScoped =>
            simp only [inferFuel] at run
            cases functionRun : inferFuel fuel rigidCount ctx function state with
            | none => simp [functionRun] at run
            | some functionResult =>
              have functionSafe := inferFuel_safe stateSafe ctxWF
                functionScoped functionRun
              have functionSound := ih stateSafe ctxWF functionScoped functionRun
              have argumentCtxWF := ctx_mono ctxWF functionSafe.2.2
              cases argumentRun : inferFuel fuel rigidCount ctx argument
                  functionResult.state with
              | none => simp [functionRun, argumentRun] at run
              | some argumentResult =>
                have argumentSafe := inferFuel_safe functionSafe.1 argumentCtxWF
                  argumentScoped argumentRun
                have argumentSound := ih functionSafe.1 argumentCtxWF
                  argumentScoped argumentRun
                let fresh := argumentResult.state.fresh
                have freshSafe := InferState.fresh_safe argumentSafe.1
                have functionTyWF : functionResult.ty.InferWF rigidCount 0
                    fresh.1.next := inferWF_mono functionSafe.2.1
                      (le_trans argumentSafe.2.2 freshSafe.2.2)
                have argumentTyWF : argumentResult.ty.InferWF rigidCount 0
                    fresh.1.next := inferWF_mono argumentSafe.2.1 freshSafe.2.2
                have arrowWF : (Ty.arrow argumentResult.ty fresh.2).InferWF
                    rigidCount 0 fresh.1.next := by
                  exact ⟨.arrow argumentTyWF.1 freshSafe.2.1.1,
                    by
                      intro id member
                      simp only [Ty.mvars, List.mem_dedup, List.mem_append] at member
                      exact member.elim (argumentTyWF.2 id) (freshSafe.2.1.2 id)⟩
                cases checkedRun : fresh.1.constrain functionResult.ty
                    (.arrow argumentResult.ty fresh.2) with
                | none =>
                    dsimp [fresh] at checkedRun
                    simp [functionRun, argumentRun, checkedRun] at run
                | some checked =>
                    dsimp [fresh] at checkedRun
                    have checkedSafe := InferState.constrain_safe freshSafe.1
                      functionTyWF arrowWF checkedRun
                    have resultEq : result =
                        ⟨checked, checked.solutions.apply fresh.2⟩ := by
                      simpa [functionRun, argumentRun, checkedRun] using run.symm
                    subst result
                    have checkedRefines : fresh.1.Refines checked rigidCount :=
                      InferState.constrain_refines freshSafe.1 checkedRun
                    refine ⟨functionSound.1.trans <| argumentSound.1.trans <|
                      InferState.fresh_refines.trans checkedRefines, ?_⟩
                    intro valuation models
                    have argumentModels : argumentResult.state.Models
                        rigidCount valuation :=
                      (InferState.fresh_refines.trans checkedRefines) valuation models
                    have functionModels : functionResult.state.Models
                        rigidCount valuation := argumentSound.1 valuation argumentModels
                    have functionTyping := functionSound.2 valuation functionModels
                    have argumentTyping := argumentSound.2 valuation argumentModels
                    have checkedEq := checkedSafe.2.2.2
                    have semanticEq := congrArg (Ty.realize valuation) checkedEq
                    rw [models.realize_apply functionResult.ty,
                      models.realize_apply (.arrow argumentResult.ty fresh.2)] at semanticEq
                    simp only [Ty.realize] at semanticEq
                    rw [semanticEq] at functionTyping
                    have applied := Typing.app functionTyping argumentTyping
                    rw [models.realize_apply fresh.2]
                    exact applied
      | letIn ann rhs body =>
          cases ann with
          | none =>
            cases inputScoped with
            | letMono rhsScoped bodyScoped =>
              simp only [inferFuel] at run
              cases rhsRun : inferFuel fuel rigidCount ctx rhs state with
              | none => simp [rhsRun] at run
              | some rhsResult =>
                have rhsSafe := inferFuel_safe stateSafe ctxWF rhsScoped rhsRun
                have rhsSound := ih stateSafe ctxWF rhsScoped rhsRun
                let rhsTy := rhsResult.state.solutions.apply rhsResult.ty
                have rhsTyWF : rhsTy.InferWF rigidCount 0 rhsResult.state.next :=
                  MStore.apply_inferWF rhsSafe.1.solutionsScoped
                    rhsSafe.1.solutionsBounded rhsSafe.2.1
                have bodyCtxWF : Ctx.InferWF (PolyTy.mono rhsTy :: ctx)
                    rigidCount rhsResult.state.next := by
                  intro scheme member
                  simp only [List.mem_cons] at member
                  rcases member with rfl | member
                  · exact rhsTyWF
                  · exact ctx_mono ctxWF rhsSafe.2.2 scheme member
                have bodyRun : inferFuel fuel rigidCount
                    (PolyTy.mono rhsTy :: ctx) body rhsResult.state = some result := by
                  simpa [rhsTy, rhsRun] using run
                have bodySound := ih rhsSafe.1 bodyCtxWF bodyScoped bodyRun
                refine ⟨rhsSound.1.trans bodySound.1, ?_⟩
                intro valuation models
                have rhsModels := bodySound.1 valuation models
                have rhsTyping := rhsSound.2 valuation rhsModels
                have bodyTyping := bodySound.2 valuation models
                have rhsSemanticWF := Ty.realize_inferWF rhsSafe.2.1
                  (modelWF rhsSafe.1 rhsModels)
                apply Typing.letMono rhsSemanticWF rhsTyping
                have rhsEq := rhsModels.realize_apply rhsResult.ty
                simpa [rhsTy, Ctx.realize, PolyTy.realize, PolyTy.mono,
                  rhsEq] using bodyTyping
          | some written =>
            cases inputScoped with
            | letPoly writtenScoped rhsScoped bodyScoped =>
              simp only [inferFuel] at run
              let localStart := state.next
              let count := written.paramCount
              let openedTemplate :=
                written.body.openRigidsFrom 0 rigidCount count
              have openedTemplateScoped :
                  openedTemplate.Scoped (rigidCount + count) 0 := by
                simpa [openedTemplate, Nat.zero_add] using
                  (Template.openRigidsFrom_scoped
                    (rigidCount := rigidCount) (depth := 0)
                    (count := count) writtenScoped)
              have localStateSafe : state.Safe (rigidCount + count) :=
                state_mono_rigid stateSafe (by omega)
              let seeded := state.allocate openedTemplate
              have seededSafe := InferState.allocate_safe localStateSafe
                openedTemplateScoped
              have openedRhsScoped :
                  (rhs.openRigids rigidCount count).TypeScoped
                    (rigidCount + count) 0 := by
                simpa [Expr.openRigids, count, Nat.zero_add] using
                  (Expr.openRigidsFrom_typeScoped
                    (rigidCount := rigidCount) (depth := 0)
                    (count := count) rhsScoped)
              have rhsCtxWF : ctx.InferWF (rigidCount + count) seeded.1.next :=
                ctx_mono (ctx_mono_rigid ctxWF (by omega)) seededSafe.2.2
              cases rhsRun : inferFuel fuel (rigidCount + count) ctx
                  (rhs.openRigids rigidCount count) seeded.1 with
              | none =>
                  dsimp [seeded, openedTemplate, count] at rhsRun
                  simp [rhsRun] at run
              | some rhsResult =>
                  dsimp [seeded, openedTemplate, count] at rhsRun
                  have rhsSafe := inferFuel_safe seededSafe.1 rhsCtxWF
                    openedRhsScoped rhsRun
                  have rhsSound := ih seededSafe.1 rhsCtxWF openedRhsScoped rhsRun
                  have seededTyAtRhs : seeded.2.InferWF
                      (rigidCount + count) 0 rhsResult.state.next :=
                    inferWF_mono seededSafe.2.1 rhsSafe.2.2
                  cases checkedRun : rhsResult.state.constrain
                      rhsResult.ty seeded.2 with
                  | none =>
                      dsimp [seeded, openedTemplate, count] at checkedRun
                      simp [rhsRun, checkedRun] at run
                  | some checked =>
                      dsimp [seeded, openedTemplate, count] at checkedRun
                      have checkedSafe := InferState.constrain_safe rhsSafe.1
                        rhsSafe.2.1 seededTyAtRhs checkedRun
                      have checkedRefines : rhsResult.state.Refines checked
                          (rigidCount + count) :=
                        InferState.constrain_refines rhsSafe.1 checkedRun
                      simp [rhsRun, checkedRun] at run
                      rcases run with ⟨completionProof, obligationsProof,
                        schemeWFB, escapeRaw, bodyRunRaw⟩
                      let completedOpen := checked.solutions.apply seeded.2
                      let completed : PolyTy :=
                        ⟨count, completedOpen.closeRigids rigidCount count⟩
                      let projected := checked.solutions.take localStart
                      have escape : MStore.safeToLeave rigidCount
                          localStart projected = true := by
                        simpa [projected, localStart] using escapeRaw
                      have localStartLe : localStart ≤ checked.solutions.length := by
                        rw [checkedSafe.1.solutions_length, checkedSafe.2.1]
                        exact le_trans seededSafe.2.2 rhsSafe.2.2
                      have projectedSafe := MStore.take_safe localStartLe
                        checkedSafe.1.solutionsNormalized escape
                      let outerState : InferState :=
                        { next := localStart
                          solutions := projected
                          required := checked.required.filter (· < localStart) }
                      have outerSafe : outerState.Safe rigidCount := by
                        refine ⟨?_, ?_, ?_, ?_, ?_⟩
                        · simpa [outerState, projected] using projectedSafe.1
                        · simpa [outerState, projected] using projectedSafe.2.1
                        · simpa [outerState, projected] using projectedSafe.2.2.1
                        · simpa [outerState, projected] using projectedSafe.2.2.2
                        · intro id member
                          have filtered := List.mem_filter.mp member
                          simpa [outerState] using filtered.2
                      have completedWFB : completed.wfB rigidCount = true := by
                        simpa [completed, completedOpen, count] using schemeWFB
                      have completedParts :
                          completed.body.scopedB rigidCount
                              completed.paramCount = true ∧
                            completed.body.metaFreeB = true := by
                        simpa [PolyTy.wfB, Bool.and_eq_true] using completedWFB
                      have completedScoped :
                          completed.body.Scoped rigidCount completed.paramCount :=
                        Ty.scopedB_eq_true_iff.mp completedParts.1
                      have completedFree : completed.body.MetaFree :=
                        Ty.metaFreeB_eq_true_iff.mp completedParts.2
                      have completedWF : completed.WF rigidCount :=
                        ⟨completedScoped, completedFree⟩
                      have bodyCtxWF : Ctx.InferWF (completed :: ctx)
                          rigidCount outerState.next := by
                        intro scheme member
                        simp only [List.mem_cons] at member
                        rcases member with rfl | member
                        · exact wf_inferWF completedWF
                        · simpa [outerState, localStart] using ctxWF scheme member
                      have bodyRun : inferFuel fuel rigidCount
                          (completed :: ctx) body outerState = some result := by
                        simpa [completed, completedOpen, count, outerState,
                          projected, localStart] using bodyRunRaw
                      have bodySound := ih outerSafe bodyCtxWF bodyScoped bodyRun
                      have outerRefines : state.Refines outerState rigidCount := by
                        intro outerVal outerModels
                        obtain ⟨localVal, localModels, agree⟩ :=
                          MStore.Models.extend_checkedPrefix localStartLe
                            checkedSafe.1.solutionsScoped
                            (by simpa [checkedSafe.1.solutions_length] using
                              checkedSafe.1.solutionsBounded)
                            checkedSafe.1.solutionsNormalized escape outerModels
                        have checkedToState : state.Refines checked
                            (rigidCount + count) :=
                          InferState.allocate_refines.trans <|
                            rhsSound.1.trans checkedRefines
                        have localStateModels := checkedToState localVal localModels
                        have outerWF : outerVal.WF rigidCount state.next := by
                          simpa [outerState, projected, localStart,
                            projectedSafe.1] using outerModels.valuationWF
                        constructor
                        · simpa [stateSafe.solutions_length] using outerWF
                        · intro id ty entry
                          have idLt : id < state.solutions.length := by
                            by_contra outOfRange
                            have noneEq : state.solutions[id]? = none :=
                              List.getElem?_eq_none_iff.mpr (by omega)
                            rw [noneEq] at entry
                            exact Option.noConfusion entry
                          have idOuter : id < localStart := by
                            simpa [localStart, stateSafe.solutions_length] using idLt
                          have localEq := localStateModels.equation id ty entry
                          have tyMember : some ty ∈ state.solutions :=
                            List.mem_of_getElem? entry
                          have entryBounded : ty.MVarBounded state.next :=
                            stateSafe.solutionsBounded ty tyMember
                          calc
                            outerVal id = localVal id := (agree id idOuter).symm
                            _ = ty.realize localVal := localEq
                            _ = ty.realize outerVal :=
                              Ty.realize_eq_of_agree entryBounded (by
                                simpa [MValuation.AgreeBelow, localStart] using agree)
                      refine ⟨outerRefines.trans bodySound.1, ?_⟩
                      intro outerVal finalModels
                      have outerModels := bodySound.1 outerVal finalModels
                      obtain ⟨localVal, localModels, agree⟩ :=
                        MStore.Models.extend_checkedPrefix localStartLe
                          checkedSafe.1.solutionsScoped
                          (by simpa [checkedSafe.1.solutions_length] using
                            checkedSafe.1.solutionsBounded)
                          checkedSafe.1.solutionsNormalized escape outerModels
                      have rhsModels := checkedRefines localVal localModels
                      have rhsTyping := rhsSound.2 localVal rhsModels
                      have ctxEq : ctx.realize localVal = ctx.realize outerVal :=
                        Ctx.realize_eq_of_agree
                          (fun scheme member => (ctxWF scheme member).2) agree
                      rw [ctxEq] at rhsTyping
                      have checkedEq := checkedSafe.2.2.2
                      have semanticEq := congrArg (Ty.realize localVal) checkedEq
                      rw [localModels.realize_apply rhsResult.ty,
                        localModels.realize_apply seeded.2] at semanticEq
                      rw [semanticEq] at rhsTyping
                      have completedOpenScoped : completedOpen.Scoped
                          (rigidCount + count) 0 := by
                        apply Ty.scopedB_eq_true_iff.mp
                        simpa [completedOpen, count] using completionProof.2
                      have completedOpenFree : completedOpen.MetaFree := by
                        apply Ty.metaFreeB_eq_true_iff.mp
                        simpa [completedOpen] using completionProof.1
                      have seedEqOpen : seeded.2.realize localVal = completedOpen := by
                        calc
                          seeded.2.realize localVal =
                              completedOpen.realize localVal :=
                            (localModels.realize_apply seeded.2).symm
                          _ = completedOpen := Ty.realize_eq_self
                            completedOpenFree localVal
                      have rhsExpected : Typing (rigidCount + count)
                          (ctx.realize outerVal) (rhs.openRigids rigidCount count)
                          (completed.openRigids rigidCount) := by
                        rw [PolyTy.openRigids_closeRigids completedOpenScoped]
                        simpa [seedEqOpen] using rhsTyping
                      have openedMatches : openedTemplate.Matches
                          (seeded.2.realize localVal) :=
                        Template.allocate_matches_realize
                          (valuation := localVal) (frontier := localStart)
                            openedTemplateScoped
                      rw [seedEqOpen] at openedMatches
                      have writtenBodyScoped : written.body.Scoped
                          rigidCount count := by
                        simpa [count] using writtenScoped
                      have closedMatches := Template.matches_closeRigids
                        writtenBodyScoped completedOpenScoped openedMatches
                      have schemeMatches : SchemeTemplateMatches written completed :=
                        ⟨rfl, by simpa [completed, completedOpen, count] using
                          closedMatches⟩
                      have bodyTyping := bodySound.2 outerVal finalModels
                      apply Typing.letPoly schemeMatches completedWF
                      · apply Ctx.realize_wf ctxWF
                        have outerValWF : outerVal.WF rigidCount outerState.next :=
                          modelWF (candidate := outerState) outerSafe outerModels
                        simpa [outerState, localStart] using outerValWF
                      · simpa [completed, count] using rhsScoped
                      · exact rhsExpected
                      · simpa [Ctx.realize, PolyTy.realize,
                          Ty.realize_eq_self completedWF.2 outerVal] using bodyTyping
      | fix ann body =>
          cases inputScoped with
          | fix annScoped bodyScoped =>
            simp only [inferFuel] at run
            let seeded := state.allocate ann
            have seededSafe := InferState.allocate_safe stateSafe annScoped
            have bodyCtxWF : Ctx.InferWF (PolyTy.mono seeded.2 :: ctx)
                rigidCount seeded.1.next := by
              intro scheme member
              simp only [List.mem_cons] at member
              rcases member with rfl | member
              · exact seededSafe.2.1
              · exact ctx_mono ctxWF seededSafe.2.2 scheme member
            cases bodyRun : inferFuel fuel rigidCount
                (PolyTy.mono seeded.2 :: ctx) body seeded.1 with
            | none =>
                dsimp [seeded] at bodyRun
                simp [bodyRun] at run
            | some bodyResult =>
                dsimp [seeded] at bodyRun
                rw [bodyRun] at run
                change (bodyResult.state.constrain bodyResult.ty
                  (state.allocate ann).2).bind (fun checked =>
                    some ⟨checked, checked.solutions.apply (state.allocate ann).2⟩) =
                      some result at run
                have bodySafe := inferFuel_safe seededSafe.1 bodyCtxWF
                  bodyScoped bodyRun
                have bodySound := ih seededSafe.1 bodyCtxWF bodyScoped bodyRun
                have selfWF : seeded.2.InferWF rigidCount 0 bodyResult.state.next :=
                  inferWF_mono seededSafe.2.1 bodySafe.2.2
                cases checkedRun : bodyResult.state.constrain
                    bodyResult.ty (state.allocate ann).2 with
                | none =>
                    rw [checkedRun] at run
                    simp at run
                | some checked =>
                    have checkedSafe := InferState.constrain_safe bodySafe.1
                      bodySafe.2.1 selfWF (by simpa [seeded] using checkedRun)
                    rw [checkedRun] at run
                    simp only [Option.bind_some, Option.some.injEq] at run
                    subst result
                    have checkedRefines : bodyResult.state.Refines checked rigidCount :=
                      InferState.constrain_refines bodySafe.1 (by
                        simpa [seeded] using checkedRun)
                    refine ⟨InferState.allocate_refines.trans <|
                      bodySound.1.trans checkedRefines, ?_⟩
                    intro valuation models
                    have bodyModels := checkedRefines valuation models
                    have bodyTyping := bodySound.2 valuation bodyModels
                    have checkedEq := checkedSafe.2.2.2
                    have semanticEq := congrArg (Ty.realize valuation) checkedEq
                    rw [models.realize_apply bodyResult.ty,
                      models.realize_apply seeded.2] at semanticEq
                    rw [semanticEq] at bodyTyping
                    have selfAtChecked : seeded.2.InferWF rigidCount 0 checked.next := by
                      rw [checkedSafe.2.1]
                      exact selfWF
                    have selfSemanticWF := Ty.realize_inferWF selfAtChecked
                      (modelWF checkedSafe.1 models)
                    have annMatches : ann.Matches
                        (seeded.2.realize valuation) := by
                      exact Template.allocate_matches_realize
                        (valuation := valuation) (frontier := state.next) annScoped
                    have realizedBody : Typing rigidCount
                        (PolyTy.mono (seeded.2.realize valuation) ::
                          ctx.realize valuation) body
                        (seeded.2.realize valuation) := by
                      simpa [Ctx.realize, PolyTy.realize, PolyTy.mono] using
                        bodyTyping
                    have fixTyping := Typing.fix selfSemanticWF annMatches realizedBody
                    change Typing rigidCount (ctx.realize valuation)
                      (.fix ann body)
                      ((checked.solutions.apply seeded.2).realize valuation)
                    rw [models.realize_apply seeded.2]
                    exact fixTyping

/-- Every successful public inference result belongs to the declarative source
typing relation. -/
theorem infer_sound
    {input : Source} {result : InferenceResult}
    (run : infer input = some result) :
    Typing 0 [] input result.ty := by
  unfold infer at run
  by_cases sourceBad : (!input.typeScopedB 0 0) = true
  · rw [if_pos sourceBad] at run
    simp at run
  · rw [if_neg sourceBad] at run
    cases internalRun : inferFuel (input.inferSize + 1) 0 [] input
        ⟨0, [], []⟩ with
    | none => simp [internalRun] at run
    | some internal =>
        rw [internalRun] at run
        by_cases finalGood : (internal.state.solvedB 0 &&
            (internal.state.solutions.apply internal.ty).wfB 0 0) = true
        · simp at run
          rcases run with ⟨guardParts, resultEq⟩
          cases resultEq
          have sourceScopedB : input.typeScopedB 0 0 = true := by
            cases sourceEq : input.typeScopedB 0 0 <;> simp_all
          have inputScoped : input.TypeScoped 0 0 :=
            Expr.typeScopedB_eq_true_iff.mp sourceScopedB
          have initialSafe : (⟨0, [], []⟩ : InferState).Safe 0 :=
            InferState.initial_safe
          have emptyCtxWF : Ctx.InferWF [] 0 0 := by
            simp [Ctx.InferWF]
          have internalSafe := inferFuel_safe initialSafe emptyCtxWF
            inputScoped internalRun
          obtain ⟨valuation, models⟩ :=
            InferState.has_model internalSafe.1
          have typing := (inferFuel_sound_model initialSafe emptyCtxWF
            inputScoped internalRun).2 valuation models
          have publicWF :
              (internal.state.solutions.apply internal.ty).WF 0 0 :=
            Ty.wfB_eq_true_iff.mp guardParts.2
          have resultEq : internal.ty.realize valuation =
              internal.state.solutions.apply internal.ty := by
            calc
              internal.ty.realize valuation =
                  (internal.state.solutions.apply internal.ty).realize valuation :=
                (models.realize_apply internal.ty).symm
              _ = internal.state.solutions.apply internal.ty :=
                Ty.realize_eq_self publicWF.2 valuation
          simpa [Ctx.realize, resultEq] using typing
        · simp at run
          apply False.elim
          apply finalGood
          simpa only [Bool.and_eq_true] using run.1

/-- The public result contains a closed semantic type; in particular it has no
remaining inference metavariables. -/
theorem infer_result_wf
    {input : Source} {result : InferenceResult}
    (run : infer input = some result) :
    result.ty.WF 0 0 := by
  exact Typing.regular (infer_sound run)

end EPL
