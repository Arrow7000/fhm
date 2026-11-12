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

/-- Realize every annotation of an elaborated expression. -/
def Expr.realize (expr : Expr Ty) (valuation : MValuation) : Expr Ty :=
  expr.mapAnn (·.realize valuation)

def InferState.Models (state : InferState) (valuation : MValuation) : Prop :=
  state.solutions.Models valuation

theorem Ty.realize_eq_self
    {ty : Ty} (metaFree : ty.MetaFree) (valuation : MValuation) :
    ty.realize valuation = ty := by
  induction metaFree with
  | prim => rfl
  | arrow _ _ ihDomain ihCodomain =>
      simp only [Ty.realize, ihDomain, ihCodomain]
  | bvar => rfl
  | rigid => rfl

/-- Monotonicity of algorithmic scope in the rigid count. -/
private theorem Ty.Scoped.mono_rigid {ty : Ty} {rigid rigid' binder : Nat}
    (hscoped : ty.Scoped rigid binder) (le : rigid ≤ rigid') :
    ty.Scoped rigid' binder := by
  induction hscoped with
  | prim => exact .prim
  | arrow _ _ ihDomain ihCodomain => exact .arrow ihDomain ihCodomain
  | bvar hlt => exact .bvar hlt
  | rigid hlt => exact .rigid (lt_of_lt_of_le hlt le)
  | mvar id => exact .mvar id

/-- Monotonicity of semantic well-formedness in the rigid count. -/
private theorem Ty.WF.mono_rigid {ty : Ty} {rigid rigid' binder : Nat}
    (wf : ty.WF rigid binder) (le : rigid ≤ rigid') : ty.WF rigid' binder :=
  ⟨Ty.Scoped.mono_rigid wf.1 le, wf.2⟩

private theorem Ty.Scoped.mono_binder {ty : Ty} {rigid binder binder' : Nat}
    (typeScoped : ty.Scoped rigid binder) (le : binder ≤ binder') :
    ty.Scoped rigid binder' := by
  induction typeScoped with
  | prim => exact .prim
  | arrow _ _ ihDomain ihCodomain => exact .arrow ihDomain ihCodomain
  | bvar hlt => exact .bvar (lt_of_lt_of_le hlt le)
  | rigid hlt => exact .rigid hlt
  | mvar id => exact .mvar id

private theorem Ty.LevelBounded.mono_le
    {ty : Ty} {store store' : MStore} {level : Nat}
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

/-- The images of a type's metavariables under a model are scoped at the type's
rigid count, provided those metavariables are allocated below the table's
frontier and their levels are bounded by the rigid count. -/
theorem MStore.Models.images_scoped
    {store : MStore} {valuation : MValuation} {ty : Ty}
    {rigidCount frontier : Nat}
    (models : store.Models valuation)
    (length : store.length = frontier)
    (bounded : ty.MVarBounded frontier)
    (levels : ty.LevelBounded store rigidCount) :
    ∀ id ∈ ty.mvars, (valuation id).Scoped rigidCount 0 := by
  intro id member
  have idBounded : id < frontier := bounded id member
  have idIn : id < store.length := by omega
  cases entryEq : store[id]? with
  | none =>
      have := List.getElem?_eq_none_iff.mp entryEq
      omega
  | some entry =>
      have wf := models.valuationWF id entry entryEq
      have levelEq : store.levelOf id = entry.level := by
        simp [MStore.levelOf, entryEq]
      have levelLe : entry.level ≤ rigidCount := by
        rw [← levelEq]
        exact levels id member
      exact (Ty.WF.mono_rigid wf levelLe).1

/-- A scoped, allocated, level-bounded type realizes under a model to a
well-formed semantic type. -/
theorem Ty.realize_inferWF_model
    {store : MStore} {valuation : MValuation}
    {ty : Ty} {rigidCount binderCount frontier : Nat}
    (models : store.Models valuation)
    (length : store.length = frontier)
    (typeWF : ty.InferWF rigidCount binderCount frontier)
    (levels : ty.LevelBounded store rigidCount) :
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
        have domainLevels : domain.LevelBounded store rigidCount := by
          intro id member
          exact levels id (by simp [Ty.mvars, member])
        have codomainLevels : codomain.LevelBounded store rigidCount := by
          intro id member
          exact levels id (by simp [Ty.mvars, member])
        have domainWF := ihDomain ⟨domainScoped, domainBounded⟩ domainLevels
        have codomainWF := ihCodomain ⟨codomainScoped, codomainBounded⟩
          codomainLevels
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
      have idIn : id < store.length := by omega
      cases entryEq : store[id]? with
      | none =>
          have := List.getElem?_eq_none_iff.mp entryEq
          omega
      | some entry =>
          have wf := models.valuationWF id entry entryEq
          have levelEq : store.levelOf id = entry.level := by
            simp [MStore.levelOf, entryEq]
          have levelLe : entry.level ≤ rigidCount := by
            rw [← levelEq]
            exact levels id (by simp [Ty.mvars])
          have wfMono := Ty.WF.mono_rigid wf levelLe
          exact ⟨Ty.Scoped.mono_binder wfMono.1 (Nat.zero_le _), wfMono.2⟩

theorem PolyTy.realize_wf_model
    {store : MStore} {scheme : PolyTy} {valuation : MValuation}
    {rigidCount frontier : Nat}
    (models : store.Models valuation)
    (length : store.length = frontier)
    (schemeWF : scheme.InferWF rigidCount frontier)
    (levels : scheme.body.LevelBounded store rigidCount) :
    (scheme.realize valuation).WF rigidCount := by
  exact Ty.realize_inferWF_model models length schemeWF levels

theorem Ctx.realize_wf_model
    {store : MStore} {ctx : Ctx} {valuation : MValuation}
    {rigidCount frontier : Nat}
    (models : store.Models valuation)
    (length : store.length = frontier)
    (ctxWF : ctx.InferWF rigidCount frontier)
    (levels : ∀ scheme ∈ ctx, scheme.body.LevelBounded store rigidCount) :
    (ctx.realize valuation).WF rigidCount := by
  intro scheme member
  rcases List.mem_map.mp member with ⟨original, originalMember, rfl⟩
  exact PolyTy.realize_wf_model models length
    (ctxWF original originalMember) (levels original originalMember)

theorem Ty.realize_openWith
    {ty : Ty} {args : List Ty} {valuation : MValuation}
    {rigidCount : Nat}
    (imagesScoped : ∀ id ∈ ty.mvars, (valuation id).Scoped rigidCount 0) :
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
      have domainScoped : ∀ id ∈ domain.mvars,
          (valuation id).Scoped rigidCount 0 := by
        intro id member
        exact imagesScoped id (by simp [Ty.mvars, member])
      have codomainScoped : ∀ id ∈ codomain.mvars,
          (valuation id).Scoped rigidCount 0 := by
        intro id member
        exact imagesScoped id (by simp [Ty.mvars, member])
      simp only [Ty.openWith, Ty.realize, ihDomain domainScoped,
        ihCodomain codomainScoped]
  | bvar index =>
      simp only [Ty.openWith, Ty.realize, List.getElem?_map]
      cases args[index]? <;> rfl
  | rigid level => rfl
  | mvar id =>
      simpa [Ty.openWith, Ty.realize] using
        (openWith_eq_self (imagesScoped id (by simp [Ty.mvars]))).symm

theorem Ty.realize_openRigidsFrom
    {ty : Ty} {valuation : MValuation}
    {rigidCount depth count : Nat}
    (imagesScoped : ∀ id ∈ ty.mvars, (valuation id).Scoped rigidCount 0) :
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
      have domainScoped : ∀ id ∈ domain.mvars,
          (valuation id).Scoped rigidCount 0 := by
        intro id member
        exact imagesScoped id (by simp [Ty.mvars, member])
      have codomainScoped : ∀ id ∈ codomain.mvars,
          (valuation id).Scoped rigidCount 0 := by
        intro id member
        exact imagesScoped id (by simp [Ty.mvars, member])
      simp only [Ty.openRigidsFrom, Ty.realize, ihDomain domainScoped,
        ihCodomain codomainScoped]
  | bvar index =>
      simp only [Ty.openRigidsFrom, Ty.realize]
      split
      · rfl
      · split <;> rfl
  | rigid level => rfl
  | mvar id =>
      simpa [Ty.openRigidsFrom, Ty.realize] using
        (open_eq_self (imagesScoped id (by simp [Ty.mvars]))).symm

theorem Ty.realize_closeRigids
    {ty : Ty} {valuation : MValuation}
    {rigidCount count : Nat}
    (imagesScoped : ∀ id ∈ ty.mvars, (valuation id).Scoped rigidCount 0) :
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
      have domainScoped : ∀ id ∈ domain.mvars,
          (valuation id).Scoped rigidCount 0 := by
        intro id member
        exact imagesScoped id (by simp [Ty.mvars, member])
      have codomainScoped : ∀ id ∈ codomain.mvars,
          (valuation id).Scoped rigidCount 0 := by
        intro id member
        exact imagesScoped id (by simp [Ty.mvars, member])
      simp only [Ty.closeRigids, Ty.realize, ihDomain domainScoped,
        ihCodomain codomainScoped]
  | bvar index => rfl
  | rigid level =>
      simp only [Ty.closeRigids, Ty.realize]
      split
      · rfl
      · split <;> rfl
  | mvar id =>
      simpa [Ty.closeRigids, Ty.realize] using
        (close_eq_self (imagesScoped id (by simp [Ty.mvars]))).symm

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

/-- Every safe normalized table has a concrete semantic model: solved entries
keep their semantic structure and genuinely unconstrained variables default to
`Unit`. -/
theorem MStore.defaultValuation_models
    {store : MStore} {frontier : Nat}
    (_length : store.length = frontier)
    (storeLeveled : store.Leveled)
    (storeBounded : store.Bounded frontier)
    (storeNormalized : store.Normalized) :
    store.Models store.defaultValuation := by
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
  · intro id entry entryEq
    cases solution : entry.solution with
    | none =>
        have lookupNone : store.lookup id = none := by
          simp [MStore.lookup, entryEq, solution]
        simp only [MStore.defaultValuation, MStore.apply, lookupNone,
          Option.getD_none, Ty.defaultMVars]
        exact ⟨.prim, .prim⟩
    | some ty =>
        have lookupSome : store.lookup id = some ty := by
          simp [MStore.lookup, entryEq, solution]
        simpa [MStore.defaultValuation, MStore.apply, lookupSome] using
          Ty.defaultMVars_wf (storeLeveled id entry ty entryEq solution).1
  · intro id ty entry
    have tyBounded : ty.MVarBounded frontier := storeBounded id ty entry
    have tyFixed : store.apply ty = ty :=
      MStore.apply_eq_self_of_lookup_none store ty
        (storeNormalized id ty entry)
    have realizeEq : ty.realize store.defaultValuation = ty.defaultMVars :=
      realize_eq_default tyBounded tyFixed
    have lookupSome : store.lookup id = some ty := entry
    simp only [MStore.defaultValuation, MStore.apply, lookupSome,
      Option.getD_some]
    rw [realizeEq]

theorem InferState.has_model
    {state : InferState} (safe : state.Safe) :
    ∃ valuation, state.Models valuation := by
  refine ⟨state.solutions.defaultValuation, ?_⟩
  exact MStore.defaultValuation_models safe.solutions_length
    safe.solutionsLeveled safe.solutionsBounded safe.solutionsNormalized

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
def MStore.Refines (older newer : MStore) : Prop :=
  ∀ valuation, newer.Models valuation → older.Models valuation

def InferState.Refines (older newer : InferState) : Prop :=
  older.solutions.Refines newer.solutions

theorem MStore.Refines.refl (store : MStore) :
    store.Refines store := by
  intro valuation models
  exact models

theorem MStore.Refines.trans
    {first second third : MStore}
    (firstSecond : first.Refines second)
    (secondThird : second.Refines third) :
    first.Refines third := by
  intro valuation thirdModels
  exact firstSecond valuation (secondThird valuation thirdModels)

/-- A model of a table also models any literal prefix of that table. -/
theorem MStore.Models.prefix
    {older newer : MStore} {valuation : MValuation}
    (models : newer.Models valuation)
    (prefixEq : newer.take older.length = older) :
    older.Models valuation := by
  have lengthLe : older.length ≤ newer.length := by
    have lengths := congrArg List.length prefixEq
    simp only [List.length_take] at lengths
    omega
  constructor
  · intro id entry entryOlder
    have idLt : id < older.length := by
      by_contra outOfRange
      have noneEq : older[id]? = none :=
        List.getElem?_eq_none_iff.mpr (by omega)
      rw [noneEq] at entryOlder
      exact Option.noConfusion entryOlder
    have prefixAt : newer[id]? = older[id]? := by
      have gets : (newer.take older.length)[id]? = older[id]? :=
        congrArg (fun entries => entries[id]?) prefixEq
      rw [List.getElem?_take_of_lt idLt] at gets
      exact gets
    exact models.valuationWF id entry (by rw [prefixAt]; exact entryOlder)
  · intro id ty lookup
    have idLt : id < older.length := by
      by_contra outOfRange
      have noneEq : older[id]? = none :=
        List.getElem?_eq_none_iff.mpr (by omega)
      have lookupNone : older.lookup id = none := by
        simp [MStore.lookup, noneEq]
      rw [lookupNone] at lookup
      exact Option.noConfusion lookup
    have prefixAt : newer[id]? = older[id]? := by
      have gets : (newer.take older.length)[id]? = older[id]? :=
        congrArg (fun entries => entries[id]?) prefixEq
      rw [List.getElem?_take_of_lt idLt] at gets
      exact gets
    have lookupEq : newer.lookup id = older.lookup id := by
      simp [MStore.lookup, prefixAt]
    exact models.equation id ty (by rw [lookupEq]; exact lookup)

theorem InferState.fresh_refines
    {state : InferState} {level : Nat} :
    state.Refines (state.fresh level).1 := by
  intro valuation models
  apply models.prefix
  simp [InferState.fresh]

theorem InferState.freshMany_refines
    {state : InferState} {level count : Nat} :
    state.Refines (state.freshMany level count).1 := by
  induction count generalizing state with
  | zero => exact MStore.Refines.refl state.solutions
  | succ count ih =>
      have first : state.Refines (state.fresh level).1 :=
        InferState.fresh_refines
      have rest : (state.fresh level).1.Refines
          ((state.fresh level).1.freshMany level count).1 := ih
      simpa [InferState.freshMany] using first.trans rest

theorem InferState.allocate_refines
    {state : InferState} {template : Template} {level : Nat} :
    state.Refines (state.allocate level template).1 := by
  intro valuation models
  apply models.prefix
  simp [InferState.allocate]

/-- Solving a constraint only restricts the set of semantic models; it never
changes the meaning of any previously allocated metavariable. -/
theorem InferState.constrain_refines
    {state checked : InferState} {left right : Ty}
    (_safe : state.Safe)
    (run : state.constrain left right = some checked) :
    state.Refines checked := by
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

private theorem Expr.mapAnn_id (expr : Expr Ty) : expr.mapAnn id = expr := by
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
          simp only [Expr.mapAnn, ihRhs, ihBody]
          cases written with
          | mk count ty => rfl
  | fix selfTy body ih =>
      simp only [Expr.mapAnn]
      rw [ih]
      rfl

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
  | fix selfTy body ih =>
      have bodyPoint : ∀ ty ∈ body.annotations, f ty = g ty := by
        intro ty member
        exact pointwise ty (by simp [Expr.annotations, member])
      simp only [Expr.mapAnn, ih bodyPoint]
      have selfEq := pointwise selfTy (by simp [Expr.annotations])
      simp [selfEq]

/-- Realizing a resolved expression under a model is the same as realizing the
original expression. -/
private theorem Expr.realize_applyExpr {store : MStore} {valuation : MValuation}
    (models : store.Models valuation)
    (expr : Expr Ty) :
    (store.applyExpr expr).realize valuation = expr.realize valuation := by
  change (expr.mapAnn store.apply).mapAnn (fun ty => ty.realize valuation) =
    expr.mapAnn (fun ty => ty.realize valuation)
  rw [Expr.mapAnn_mapAnn]
  apply Expr.mapAnn_congr
  intro ty _
  exact MStore.Models.realize_apply models ty

/-- An expression all of whose annotations are semantic realizes to itself. -/
private theorem Expr.realize_eq_self_of_annotations {expr : Expr Ty}
    {valuation : MValuation}
    (free : ∀ ty ∈ expr.annotations, ty.MetaFree) :
    expr.realize valuation = expr := by
  change expr.mapAnn (fun ty => ty.realize valuation) = expr
  conv_rhs => rw [← Expr.mapAnn_id expr]
  apply Expr.mapAnn_congr
  intro ty member
  exact Ty.realize_eq_self (free ty member) valuation

/-- Closing a block of rigid levels into bound variables preserves algorithmic
type scope: a type scoped at `base + count` with no enclosing binders becomes
one scoped at `base` with `count` binders. -/
private theorem Ty.closeRigids_scoped_zero
    {ty : Ty} {base count : Nat}
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

/-- Closing rigid levels leaves the metavariables of a type unchanged. -/
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

/-- Closing rigid levels preserves metavariable bounds. -/
private theorem Ty.closeRigids_mvarBounded
    {ty : Ty} {base count frontier : Nat}
    (bounded : ty.MVarBounded frontier) :
    (ty.closeRigids base count).MVarBounded frontier := by
  intro id member
  rw [Ty.mvars_closeRigids] at member
  exact bounded id member

/-- Closing rigid levels preserves level bounds. -/
private theorem Ty.closeRigids_levelBounded
    {ty : Ty} {base count : Nat} {store : MStore} {level : Nat}
    (bounded : ty.LevelBounded store level) :
    (ty.closeRigids base count).LevelBounded store level := by
  intro id member
  rw [Ty.mvars_closeRigids] at member
  exact bounded id member

/-- Strong semantic soundness of the internal engine. A successful run both
refines its input state and yields a declarative typing derivation under every
semantic model of the result state. -/
theorem inferFuel_sound_model
    {fuel rigidCount : Nat} {ctx : Ctx} {input : Source}
    {state : InferState} {result : InferResult}
    (stateSafe : state.Safe)
    (ctxWF : ctx.InferWF rigidCount state.next)
    (ctxLevels : ∀ scheme ∈ ctx, scheme.body.LevelBounded state.solutions rigidCount)
    (inputScoped : input.TypeScoped rigidCount 0)
    (run : inferFuel fuel rigidCount ctx input state = some result) :
    state.Refines result.state ∧
      ∀ valuation, result.state.Models valuation →
        Elaborates rigidCount (ctx.realize valuation) input
          (result.elaborated.realize valuation) (result.ty.realize valuation) := by
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
          refine ⟨MStore.Refines.refl _, ?_⟩
          intro valuation models
          cases literal <;> exact Elaborates.primLit
      | primOp op =>
          simp only [inferFuel, Option.some.injEq] at run
          subst result
          refine ⟨MStore.Refines.refl _, ?_⟩
          intro valuation models
          cases op
          exact Elaborates.primOp
      | var index =>
          simp only [inferFuel] at run
          cases lookup : ctx[index]? with
          | none => simp [lookup] at run
          | some scheme =>
              simp only [lookup] at run
              let fresh := state.freshMany rigidCount scheme.paramCount
              have resultEq : result =
                  ⟨fresh.1, (state.solutions.applyScheme scheme).openWith fresh.2,
                    .var index⟩ :=
                Option.some.inj run.symm
              subst result
              have freshSafe := InferState.freshMany_safe
                (level := rigidCount) (count := scheme.paramCount) stateSafe
              refine ⟨InferState.freshMany_refines, ?_⟩
              intro valuation models
              have stateModels : state.Models valuation :=
                InferState.freshMany_refines valuation models
              have schemeMember : scheme ∈ ctx := List.mem_of_getElem? lookup
              have schemeWF := ctxWF scheme schemeMember
              have schemeLevels := ctxLevels scheme schemeMember
              have applied := MStore.apply_inferWF stateSafe.solutionsLeveled
                stateSafe.solutionsBounded schemeWF schemeLevels
              have appliedWF : (state.solutions.apply scheme.body).InferWF
                  rigidCount scheme.paramCount state.next := applied.1
              have appliedLevels : (state.solutions.apply scheme.body).LevelBounded
                  state.solutions rigidCount := applied.2
              have argsWF : ∀ arg ∈ fresh.2,
                  (arg.realize valuation).WF rigidCount 0 := by
                intro arg member
                exact Ty.realize_inferWF_model models freshSafe.1.solutions_length
                  (freshSafe.2.1 arg member) (freshSafe.2.2.1 arg member)
              have resultTyEq :
                  ((state.solutions.applyScheme scheme).openWith fresh.2).realize
                      valuation =
                    (scheme.realize valuation).openWith
                      (fresh.2.map (·.realize valuation)) := by
                have opened := Ty.realize_openWith (args := fresh.2)
                  (MStore.Models.images_scoped stateModels
                    stateSafe.solutions_length appliedWF.2 appliedLevels)
                have appliedEq := stateModels.realize_apply scheme.body
                simpa [PolyTy.openWith, PolyTy.realize, MStore.applyScheme,
                  appliedEq] using opened
              rw [resultTyEq]
              apply Elaborates.var (scheme := scheme.realize valuation)
                  (args := fresh.2.map (·.realize valuation))
              · simp [Ctx.realize, lookup]
              · exact PolyTy.realize_wf_model stateModels
                  stateSafe.solutions_length schemeWF schemeLevels
              · simpa using freshSafe.2.2.2.1
              · intro arg member
                rcases List.mem_map.mp member with ⟨original, originalMem, rfl⟩
                exact argsWF original originalMem
      | lambda ann body =>
          cases inputScoped with
          | lambda annScoped bodyScoped =>
            cases ann with
            | none =>
                simp only [inferFuel] at run
                let seeded := state.fresh rigidCount
                cases bodyRun : inferFuel fuel rigidCount
                    (PolyTy.mono seeded.2 :: ctx) body seeded.1 with
                | none => simp [seeded, bodyRun] at run
                | some bodyResult =>
                    have seededSafe := InferState.fresh_safe
                      (level := rigidCount) stateSafe
                    have bodyCtxWF : Ctx.InferWF
                        (PolyTy.mono seeded.2 :: ctx) rigidCount seeded.1.next := by
                      intro scheme member
                      simp only [List.mem_cons] at member
                      rcases member with rfl | member
                      · exact seededSafe.2.1
                      · exact ctx_mono ctxWF seededSafe.2.2.2.1 scheme member
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
                    have bodySound := ih seededSafe.1 bodyCtxWF bodyCtxLevels
                      bodyScoped bodyRun
                    dsimp [seeded] at bodyRun
                    rw [bodyRun] at run
                    have run := Option.some.inj run
                    subst result
                    refine ⟨InferState.fresh_refines.trans bodySound.1, ?_⟩
                    intro valuation models
                    have seededModels : seeded.1.Models valuation :=
                      bodySound.1 valuation models
                    have paramWF := Ty.realize_inferWF_model seededModels
                      seededSafe.1.solutions_length seededSafe.2.1
                      seededSafe.2.2.1
                    have bodyTyping := bodySound.2 valuation models
                    have annMatches : ParamAnn.Matches none
                        (seeded.2.realize valuation) := by
                      intro template impossible
                      cases impossible
                    change Elaborates rigidCount (ctx.realize valuation)
                      (.lambda none body)
                      (.lambda (some (seeded.2.realize valuation))
                        (bodyResult.elaborated.realize valuation))
                      (.arrow
                        ((bodyResult.state.solutions.apply seeded.2).realize valuation)
                        (bodyResult.ty.realize valuation))
                    rw [models.realize_apply seeded.2]
                    apply Elaborates.lambda (ann := none) (body := body)
                    · exact paramWF
                    · exact annMatches
                    · simpa [Ctx.realize, PolyTy.realize, PolyTy.mono] using bodyTyping
            | some template =>
                have templateScoped := annScoped template rfl
                simp only [inferFuel] at run
                let seeded := state.allocate rigidCount template
                cases bodyRun : inferFuel fuel rigidCount
                    (PolyTy.mono seeded.2 :: ctx) body seeded.1 with
                | none => simp [seeded, bodyRun] at run
                | some bodyResult =>
                    have seededSafe := InferState.allocate_safe
                      (level := rigidCount) (rigidCount := rigidCount)
                      stateSafe templateScoped
                    have bodyCtxWF : Ctx.InferWF
                        (PolyTy.mono seeded.2 :: ctx) rigidCount seeded.1.next := by
                      intro scheme member
                      simp only [List.mem_cons] at member
                      rcases member with rfl | member
                      · exact seededSafe.2.1
                      · exact ctx_mono ctxWF seededSafe.2.2.2.1 scheme member
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
                    have bodySound := ih seededSafe.1 bodyCtxWF bodyCtxLevels
                      bodyScoped bodyRun
                    dsimp [seeded] at bodyRun
                    rw [bodyRun] at run
                    have run := Option.some.inj run
                    subst result
                    refine ⟨InferState.allocate_refines.trans bodySound.1, ?_⟩
                    intro valuation models
                    have seededModels : seeded.1.Models valuation :=
                      bodySound.1 valuation models
                    have paramWF := Ty.realize_inferWF_model seededModels
                      seededSafe.1.solutions_length seededSafe.2.1
                      seededSafe.2.2.1
                    have bodyTyping := bodySound.2 valuation models
                    have annMatches : ParamAnn.Matches (some template)
                        (seeded.2.realize valuation) := by
                      intro candidate annEq
                      cases annEq
                      exact Template.allocate_matches_realize templateScoped
                    change Elaborates rigidCount (ctx.realize valuation)
                      (.lambda (some template) body)
                      (.lambda (some (seeded.2.realize valuation))
                        (bodyResult.elaborated.realize valuation))
                      (.arrow
                        ((bodyResult.state.solutions.apply seeded.2).realize valuation)
                        (bodyResult.ty.realize valuation))
                    rw [models.realize_apply seeded.2]
                    apply Elaborates.lambda (ann := some template) (body := body)
                    · exact paramWF
                    · exact annMatches
                    · simpa [Ctx.realize, PolyTy.realize, PolyTy.mono] using bodyTyping
      | app function argument =>
          cases inputScoped with
          | app functionScoped argumentScoped =>
            simp only [inferFuel] at run
            cases functionRun : inferFuel fuel rigidCount ctx function state with
            | none => simp [functionRun] at run
            | some functionResult =>
              have functionSafe := inferFuel_safe stateSafe ctxWF ctxLevels
                functionScoped functionRun
              have functionSound := ih stateSafe ctxWF ctxLevels
                functionScoped functionRun
              have argumentCtxWF := ctx_mono ctxWF functionSafe.2.2.2.1
              have argumentCtxLevels :
                  ∀ scheme ∈ ctx,
                    scheme.body.LevelBounded
                      functionResult.state.solutions rigidCount := by
                intro scheme member id hid
                have idBound : id < state.next :=
                  (ctxWF scheme member).2 id hid
                exact le_trans (functionSafe.2.2.2.2 id idBound)
                  (ctxLevels scheme member id hid)
              cases argumentRun : inferFuel fuel rigidCount ctx argument
                  functionResult.state with
              | none => simp [functionRun, argumentRun] at run
              | some argumentResult =>
                have argumentSafe := inferFuel_safe functionSafe.1 argumentCtxWF
                  argumentCtxLevels argumentScoped argumentRun
                have argumentSound := ih functionSafe.1 argumentCtxWF
                  argumentCtxLevels argumentScoped argumentRun
                let fresh := argumentResult.state.fresh rigidCount
                have freshSafe := InferState.fresh_safe
                  (level := rigidCount) argumentSafe.1
                have functionTyWF : functionResult.ty.InferWF rigidCount 0
                    fresh.1.next := inferWF_mono functionSafe.2.1
                      (le_trans argumentSafe.2.2.2.1 freshSafe.2.2.2.1)
                have argumentTyWF : argumentResult.ty.InferWF rigidCount 0
                    fresh.1.next := inferWF_mono argumentSafe.2.1 freshSafe.2.2.2.1
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
                        ⟨checked, checked.solutions.apply fresh.2,
                          .app functionResult.elaborated
                            argumentResult.elaborated⟩ := by
                      simpa [functionRun, argumentRun, checkedRun] using run.symm
                    subst result
                    have checkedRefines : fresh.1.Refines checked :=
                      InferState.constrain_refines freshSafe.1 checkedRun
                    refine ⟨functionSound.1.trans <| argumentSound.1.trans <|
                      InferState.fresh_refines.trans checkedRefines, ?_⟩
                    intro valuation models
                    have argumentModels : argumentResult.state.Models valuation :=
                      (InferState.fresh_refines.trans checkedRefines) valuation models
                    have functionModels : functionResult.state.Models valuation :=
                      argumentSound.1 valuation argumentModels
                    have functionTyping := functionSound.2 valuation functionModels
                    have argumentTyping := argumentSound.2 valuation argumentModels
                    have checkedEq := checkedSafe.2.2.1
                    have semanticEq := congrArg (Ty.realize valuation) checkedEq
                    rw [models.realize_apply functionResult.ty,
                      models.realize_apply (.arrow argumentResult.ty fresh.2)] at semanticEq
                    simp only [Ty.realize] at semanticEq
                    rw [semanticEq] at functionTyping
                    have applied := Elaborates.app functionTyping argumentTyping
                    simp only [Expr.realize, Expr.mapAnn]
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
                have rhsSafe := inferFuel_safe stateSafe ctxWF ctxLevels
                  rhsScoped rhsRun
                have rhsSound := ih stateSafe ctxWF ctxLevels rhsScoped rhsRun
                let rhsTy := rhsResult.state.solutions.apply rhsResult.ty
                have rhsApplied := MStore.apply_inferWF rhsSafe.1.solutionsLeveled
                  rhsSafe.1.solutionsBounded rhsSafe.2.1 rhsSafe.2.2.1
                have rhsTyWF : rhsTy.InferWF rigidCount 0 rhsResult.state.next :=
                  rhsApplied.1
                have rhsTyLevels : rhsTy.LevelBounded
                    rhsResult.state.solutions rigidCount := rhsApplied.2
                have bodyCtxWF : Ctx.InferWF (PolyTy.mono rhsTy :: ctx)
                    rigidCount rhsResult.state.next := by
                  intro scheme member
                  simp only [List.mem_cons] at member
                  rcases member with rfl | member
                  · exact rhsTyWF
                  · exact ctx_mono ctxWF rhsSafe.2.2.2.1 scheme member
                have bodyCtxLevels :
                    ∀ scheme ∈ PolyTy.mono rhsTy :: ctx,
                      scheme.body.LevelBounded
                        rhsResult.state.solutions rigidCount := by
                  intro scheme member
                  simp only [List.mem_cons] at member
                  rcases member with rfl | member
                  · exact rhsTyLevels
                  · intro id hid
                    have idBound : id < state.next :=
                      (ctxWF scheme member).2 id hid
                    exact le_trans (rhsSafe.2.2.2.2 id idBound)
                      (ctxLevels scheme member id hid)
                cases bodyRun : inferFuel fuel rigidCount
                    (PolyTy.mono rhsTy :: ctx) body rhsResult.state with
                | none => simp [rhsTy, rhsRun, bodyRun] at run
                | some bodyResult =>
                    have bodySound := ih rhsSafe.1 bodyCtxWF bodyCtxLevels
                      bodyScoped bodyRun
                    have resultEq : result =
                        ⟨bodyResult.state, bodyResult.ty,
                          .letIn none rhsResult.elaborated
                            bodyResult.elaborated⟩ := by
                      simpa [rhsTy, rhsRun, bodyRun] using run.symm
                    subst result
                    refine ⟨rhsSound.1.trans bodySound.1, ?_⟩
                    intro valuation models
                    have rhsModels := bodySound.1 valuation models
                    have rhsTyping := rhsSound.2 valuation rhsModels
                    have bodyTyping := bodySound.2 valuation models
                    have rhsSemanticWF := Ty.realize_inferWF_model rhsModels
                      rhsSafe.1.solutions_length rhsSafe.2.1 rhsSafe.2.2.1
                    apply Elaborates.letMono rhsSemanticWF
                    · exact rhsTyping
                    · have rhsEq := rhsModels.realize_apply rhsResult.ty
                      simpa [rhsTy, Ctx.realize, PolyTy.realize, PolyTy.mono,
                        Expr.realize, Expr.mapAnn, rhsEq] using bodyTyping
          | some written =>
            cases inputScoped with
            | letPoly writtenScoped rhsScoped bodyScoped =>
              simp only [inferFuel] at run
              let localStart := state.next
              let count := written.paramCount
              let inner := rigidCount + count
              let openedTemplate :=
                written.body.openRigidsFrom 0 rigidCount count
              have openedTemplateScoped :
                  openedTemplate.Scoped inner 0 := by
                simpa [openedTemplate, inner, Nat.zero_add] using
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
                ctx_mono (ctx_mono_rigid ctxWF (by omega)) seededSafe.2.2.2.1
              have rhsCtxLevels :
                  ∀ scheme ∈ ctx,
                    scheme.body.LevelBounded seeded.1.solutions inner := by
                intro scheme member id hid
                have idBound : id < state.next :=
                  (ctxWF scheme member).2 id hid
                rw [seededSafe.2.2.2.2 id idBound]
                exact le_trans (ctxLevels scheme member id hid) (by omega)
              cases rhsRun : inferFuel fuel inner ctx
                  (rhs.openRigids rigidCount count) seeded.1 with
              | none =>
                  dsimp [seeded, openedTemplate, count, inner] at rhsRun
                  simp [rhsRun] at run
              | some rhsResult =>
                  dsimp [seeded, openedTemplate, count, inner] at rhsRun
                  have rhsSafe := inferFuel_safe seededSafe.1 rhsCtxWF
                    rhsCtxLevels openedRhsScoped rhsRun
                  have rhsSound := ih seededSafe.1 rhsCtxWF rhsCtxLevels
                    openedRhsScoped rhsRun
                  have seededTyAtRhs : seeded.2.InferWF inner 0
                      rhsResult.state.next :=
                    inferWF_mono seededSafe.2.1 rhsSafe.2.2.2.1
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
                            (fun id => checked.solutions.levelOf id ≤ rigidCount) = true := by
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
                        ctx_mono ctxWF localStartLe
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
                            scheme.body.LevelBounded
                              checked.solutions rigidCount := by
                        intro scheme member
                        simp only [List.mem_cons] at member
                        rcases member with rfl | member
                        · exact completedLevels
                        · exact ctxLevelsChecked scheme member
                      cases bodyRun : inferFuel fuel rigidCount
                          (completed :: ctx) body checked with
                      | none =>
                          simp [completed, completedOpen, count, inner,
                            seeded, openedTemplate, bodyRun] at run
                      | some bodyResult =>
                          have bodySound := ih checkedSafe.1 bodyCtxWF
                            bodyCtxLevels bodyScoped bodyRun
                          simp [completed, completedOpen, count, inner,
                            seeded, openedTemplate, bodyRun] at run
                          have resultEq : result =
                              ⟨bodyResult.state, bodyResult.ty,
                                .letIn (some completed)
                                  rhsResult.elaborated
                                  bodyResult.elaborated⟩ := by
                            have h : some result = some
                                ⟨bodyResult.state, bodyResult.ty,
                                  .letIn (some completed)
                                    rhsResult.elaborated
                                    bodyResult.elaborated⟩ := by
                              simpa [completed, completedOpen, count, inner,
                                seeded, openedTemplate, bodyRun] using run.2.symm
                            exact Option.some.inj h
                          subst result
                          refine ⟨(InferState.allocate_refines.trans <|
                            rhsSound.1.trans checkedRefines).trans
                            bodySound.1, ?_⟩
                          intro valuation models
                          have checkedModels : checked.Models valuation :=
                            bodySound.1 valuation models
                          have rhsModels : rhsResult.state.Models valuation :=
                            checkedRefines valuation checkedModels
                          have rhsTyping := rhsSound.2 valuation rhsModels
                          have checkedEq := checkedSafe.2.2.1
                          have semanticEq :=
                            congrArg (Ty.realize valuation) checkedEq
                          rw [checkedModels.realize_apply rhsResult.ty,
                            checkedModels.realize_apply seeded.2] at semanticEq
                          have seedEq : completedOpen.realize valuation =
                              seeded.2.realize valuation :=
                            checkedModels.realize_apply seeded.2
                          have completedOpenRealizedWF :
                              (completedOpen.realize valuation).WF inner 0 :=
                            Ty.realize_inferWF_model checkedModels
                              checkedSafe.1.solutions_length completedOpenWF
                              completedOpenLevelsInner
                          have imagesScoped : ∀ id ∈ completedOpen.mvars,
                              (valuation id).Scoped rigidCount 0 :=
                            MStore.Models.images_scoped checkedModels
                              checkedSafe.1.solutions_length completedOpenWF.2
                              completedOpenLevelsRigid
                          have completedRealize :
                              completed.realize valuation =
                                ⟨count,
                                  (completedOpen.realize valuation).closeRigids
                                    rigidCount count⟩ := by
                            simp only [completed, PolyTy.realize]
                            rw [Ty.realize_closeRigids imagesScoped]
                          have openEq :
                              (completed.realize valuation).openRigids
                                  rigidCount =
                                completedOpen.realize valuation := by
                            rw [completedRealize]
                            exact PolyTy.openRigids_closeRigids
                              completedOpenRealizedWF.1
                          have typeEq :
                              (completed.realize valuation).openRigids
                                  rigidCount = seeded.2.realize valuation := by
                            rw [openEq, seedEq]
                          rw [semanticEq, ← typeEq] at rhsTyping
                          have openedMatches : openedTemplate.Matches
                              (seeded.2.realize valuation) :=
                            Template.allocate_matches_realize
                              (valuation := valuation) (frontier := localStart)
                              openedTemplateScoped
                          rw [← seedEq] at openedMatches
                          have writtenBodyScoped : written.body.Scoped
                              rigidCount count := by
                            simpa [count] using writtenScoped
                          have closedMatches := Template.matches_closeRigids
                            writtenBodyScoped completedOpenRealizedWF.1
                            openedMatches
                          have schemeMatches : SchemeTemplateMatches written
                              (completed.realize valuation) := by
                            constructor
                            · simp [completed, count, PolyTy.realize]
                            · rw [completedRealize]
                              exact closedMatches
                          have bodyTyping := bodySound.2 valuation models
                          change Elaborates rigidCount
                            (ctx.realize valuation)
                            (.letIn (some written) rhs body)
                            (.letIn (some (completed.realize valuation))
                              (rhsResult.elaborated.realize valuation)
                              (bodyResult.elaborated.realize valuation))
                            (bodyResult.ty.realize valuation)
                          apply Elaborates.letPoly
                            (scheme := completed.realize valuation)
                            (rhsElab := rhsResult.elaborated.realize valuation)
                            (bodyElab := bodyResult.elaborated.realize valuation)
                            (bodyTy := bodyResult.ty.realize valuation)
                          · exact schemeMatches
                          · exact PolyTy.realize_wf_model checkedModels
                              checkedSafe.1.solutions_length completedInferWF
                              completedLevels
                          · exact Ctx.realize_wf_model checkedModels
                              checkedSafe.1.solutions_length ctxWFChecked
                              ctxLevelsChecked
                          · simpa [completed, count, PolyTy.realize] using rhsScoped
                          · exact rhsTyping
                          · simpa [Ctx.realize, PolyTy.realize] using bodyTyping
      | fix ann body =>
          cases inputScoped with
          | fix annScoped bodyScoped =>
            simp only [inferFuel] at run
            let seeded := state.allocate rigidCount ann
            have seededSafe := InferState.allocate_safe
              (level := rigidCount) (rigidCount := rigidCount)
              stateSafe annScoped
            have bodyCtxWF : Ctx.InferWF (PolyTy.mono seeded.2 :: ctx)
                rigidCount seeded.1.next := by
              intro scheme member
              simp only [List.mem_cons] at member
              rcases member with rfl | member
              · exact seededSafe.2.1
              · exact ctx_mono ctxWF seededSafe.2.2.2.1 scheme member
            have bodyCtxLevels :
                ∀ scheme ∈ PolyTy.mono seeded.2 :: ctx,
                  scheme.body.LevelBounded seeded.1.solutions rigidCount := by
              intro scheme member
              simp only [List.mem_cons] at member
              rcases member with rfl | member
              · exact seededSafe.2.2.1
              · intro id hid
                have idBound : id < state.next := (ctxWF scheme member).2 id hid
                rw [seededSafe.2.2.2.2 id idBound]
                exact ctxLevels scheme member id hid
            cases bodyRun : inferFuel fuel rigidCount
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
                      .fix seeded.2 bodyResult.elaborated⟩) =
                      some result at run
                have bodySafe := inferFuel_safe seededSafe.1 bodyCtxWF
                  bodyCtxLevels bodyScoped bodyRun
                have bodySound := ih seededSafe.1 bodyCtxWF bodyCtxLevels
                  bodyScoped bodyRun
                have selfWF : seeded.2.InferWF rigidCount 0 bodyResult.state.next :=
                  inferWF_mono seededSafe.2.1 bodySafe.2.2.2.1
                cases checkedRun : bodyResult.state.constrain
                    bodyResult.ty seeded.2 with
                | none =>
                    rw [checkedRun] at run
                    simp at run
                | some checked =>
                    have checkedSafe := InferState.constrain_safe bodySafe.1
                      bodySafe.2.1 selfWF checkedRun
                    rw [checkedRun] at run
                    simp only [Option.bind_some, Option.some.injEq] at run
                    subst result
                    have checkedRefines : bodyResult.state.Refines checked :=
                      InferState.constrain_refines bodySafe.1 checkedRun
                    refine ⟨InferState.allocate_refines.trans <|
                      bodySound.1.trans checkedRefines, ?_⟩
                    intro valuation models
                    have bodyModels := checkedRefines valuation models
                    have bodyTyping := bodySound.2 valuation bodyModels
                    have checkedEq := checkedSafe.2.2.1
                    have semanticEq := congrArg (Ty.realize valuation) checkedEq
                    rw [models.realize_apply bodyResult.ty,
                      models.realize_apply seeded.2] at semanticEq
                    rw [semanticEq] at bodyTyping
                    have selfAtChecked : seeded.2.InferWF rigidCount 0 checked.next := by
                      rw [checkedSafe.2.1]
                      exact selfWF
                    have selfLevelsBody : seeded.2.LevelBounded
                        bodyResult.state.solutions rigidCount :=
                      Ty.LevelBounded.mono_le_on seededSafe.2.2.1 (fun id member =>
                        bodySafe.2.2.2.2 id (seededSafe.2.1.2 id member))
                    have selfLevelsChecked : seeded.2.LevelBounded
                        checked.solutions rigidCount :=
                      Ty.LevelBounded.mono_le selfLevelsBody
                        (fun id => checkedSafe.2.2.2 id)
                    have selfSemanticWF := Ty.realize_inferWF_model models
                      checkedSafe.1.solutions_length selfAtChecked selfLevelsChecked
                    have annMatches : ann.Matches
                        (seeded.2.realize valuation) := by
                      exact Template.allocate_matches_realize
                        (valuation := valuation) (frontier := state.next) annScoped
                    have realizedBody : Elaborates rigidCount
                        (PolyTy.mono (seeded.2.realize valuation) ::
                          ctx.realize valuation) body
                        (bodyResult.elaborated.realize valuation)
                        (seeded.2.realize valuation) := by
                      simpa [Ctx.realize, PolyTy.realize, PolyTy.mono] using
                        bodyTyping
                    change Elaborates rigidCount (ctx.realize valuation)
                      (.fix ann body)
                      ((Expr.fix seeded.2 bodyResult.elaborated).realize valuation)
                      ((checked.solutions.apply seeded.2).realize valuation)
                    rw [models.realize_apply seeded.2]
                    exact Elaborates.fix selfSemanticWF annMatches realizedBody

/-- Every successful public inference result belongs to the declarative source
typing relation. -/
theorem infer_sound
    {input : Source} {result : InferenceResult}
    (run : infer input = some result) :
    Elaborates 0 [] input result.elaborated result.ty := by
  unfold infer at run
  by_cases sourceBad : (!input.typeScopedB 0 0) = true
  · rw [if_pos sourceBad] at run
    simp at run
  · rw [if_neg sourceBad] at run
    cases internalRun : inferFuel (input.inferSize + 1) 0 [] input
        ⟨0, []⟩ with
    | none => simp [internalRun] at run
    | some internal =>
        rw [internalRun] at run
        by_cases finalGood : (Ty.wfB 0 0 (internal.state.solutions.apply internal.ty) &&
            (internal.state.solutions.applyExpr internal.elaborated).annotations.all
              Ty.metaFreeB) = true
        · simp at run
          rcases run with ⟨guardParts, resultEq⟩
          cases resultEq
          have sourceScopedB : input.typeScopedB 0 0 = true := by
            cases sourceEq : input.typeScopedB 0 0 <;> simp_all
          have inputScoped : input.TypeScoped 0 0 :=
            Expr.typeScopedB_eq_true_iff.mp sourceScopedB
          have initialSafe : (⟨0, []⟩ : InferState).Safe :=
            InferState.initial_safe
          have emptyCtxWF : Ctx.InferWF [] 0 0 := by
            simp [Ctx.InferWF]
          have emptyCtxLevels : ∀ scheme ∈ ([] : Ctx),
              scheme.body.LevelBounded (⟨0, []⟩ : InferState).solutions 0 := by
            intro scheme member
            simp at member
          have internalSafe := inferFuel_safe initialSafe emptyCtxWF
            emptyCtxLevels inputScoped internalRun
          obtain ⟨valuation, models⟩ :=
            InferState.has_model internalSafe.1
          have typing := (inferFuel_sound_model initialSafe emptyCtxWF
            emptyCtxLevels inputScoped internalRun).2 valuation models
          have publicTyWF :
              (internal.state.solutions.apply internal.ty).WF 0 0 :=
            Ty.wfB_eq_true_iff.mp guardParts.1
          have publicAnnotations : ∀ ty ∈
              (internal.state.solutions.applyExpr internal.elaborated).annotations,
              ty.MetaFree := by
            intro ty member
            exact Ty.metaFreeB_eq_true_iff.mp (guardParts.2 ty member)
          have internalTyEq : internal.ty.realize valuation =
              internal.state.solutions.apply internal.ty := by
            calc
              internal.ty.realize valuation =
                  (internal.state.solutions.apply internal.ty).realize valuation :=
                (models.realize_apply internal.ty).symm
              _ = internal.state.solutions.apply internal.ty :=
                Ty.realize_eq_self publicTyWF.2 valuation
          have internalElabEq : internal.elaborated.realize valuation =
              internal.state.solutions.applyExpr internal.elaborated := by
            have realized := Expr.realize_applyExpr models internal.elaborated
            have selfEq := Expr.realize_eq_self_of_annotations
              (valuation := valuation)
              (expr := internal.state.solutions.applyExpr internal.elaborated)
              publicAnnotations
            exact realized.symm.trans selfEq
          simpa [Ctx.realize, internalTyEq, internalElabEq] using typing
        · simp at run
          apply False.elim
          apply finalGood
          rw [Bool.and_eq_true, List.all_eq_true]
          exact run.1

/-- Successful inference produces an ordinary typing at the reported type. -/
theorem infer_typing
    {input : Source} {result : InferenceResult}
    (run : infer input = some result) :
    Typing 0 [] input result.ty :=
  (infer_sound run).typing

/-- Convenience form for tests: a reported type is a declarative type. -/
theorem infer_typing_of_ty
    {input : Source} {ty : Ty}
    (run : (infer input).map (·.ty) = some ty) :
    Typing 0 [] input ty := by
  cases h : infer input with
  | none => simp [h] at run
  | some result =>
      simp only [h, Option.map_some, Option.some.injEq] at run
      exact run ▸ infer_typing h

/-- The public result contains a closed semantic type; in particular it has no
remaining inference metavariables. -/
theorem infer_result_wf
    {input : Source} {result : InferenceResult}
    (run : infer input = some result) :
    result.ty.WF 0 0 := by
  exact Typing.regular (infer_sound run).typing

end EPL
