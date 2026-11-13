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
  | con => rfl
  | app _ _ ihFunction ihArgument =>
      simp only [Ty.realize, ihFunction, ihArgument]

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
  | con id => exact .con id
  | app _ _ ihFunction ihArgument => exact .app ihFunction ihArgument

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
  | con id => exact .con id
  | app _ _ ihFunction ihArgument => exact .app ihFunction ihArgument

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
  | con id =>
      cases typeWF.1 with
      | con _ => exact ⟨.con id, .con⟩
  | app function argument ihFunction ihArgument =>
      cases typeWF.1 with
      | app functionScoped argumentScoped =>
        have functionBounded : function.MVarBounded frontier := by
          intro id member
          exact typeWF.2 id (by simp [Ty.mvars, member])
        have argumentBounded : argument.MVarBounded frontier := by
          intro id member
          exact typeWF.2 id (by simp [Ty.mvars, member])
        have functionLevels : function.LevelBounded store rigidCount := by
          intro id member
          exact levels id (by simp [Ty.mvars, member])
        have argumentLevels : argument.LevelBounded store rigidCount := by
          intro id member
          exact levels id (by simp [Ty.mvars, member])
        have functionWF := ihFunction ⟨functionScoped, functionBounded⟩ functionLevels
        have argumentWF := ihArgument ⟨argumentScoped, argumentBounded⟩
          argumentLevels
        exact ⟨.app functionWF.1 argumentWF.1,
          .app functionWF.2 argumentWF.2⟩

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
    | con id => rfl
    | app _ _ ihFunction ihArgument =>
        simp only [Ty.openWith, ihFunction, ihArgument]
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
  | con id => rfl
  | app function argument ihFunction ihArgument =>
      have functionScoped : ∀ id ∈ function.mvars,
          (valuation id).Scoped rigidCount 0 := by
        intro id member
        exact imagesScoped id (by simp [Ty.mvars, member])
      have argumentScoped : ∀ id ∈ argument.mvars,
          (valuation id).Scoped rigidCount 0 := by
        intro id member
        exact imagesScoped id (by simp [Ty.mvars, member])
      simp only [Ty.openWith, Ty.realize, ihFunction functionScoped,
        ihArgument argumentScoped]

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
    | con id => rfl
    | app _ _ ihFunction ihArgument =>
        simp only [Ty.openRigidsFrom, ihFunction, ihArgument]
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
  | con id => rfl
  | app function argument ihFunction ihArgument =>
      have functionScoped : ∀ id ∈ function.mvars,
          (valuation id).Scoped rigidCount 0 := by
        intro id member
        exact imagesScoped id (by simp [Ty.mvars, member])
      have argumentScoped : ∀ id ∈ argument.mvars,
          (valuation id).Scoped rigidCount 0 := by
        intro id member
        exact imagesScoped id (by simp [Ty.mvars, member])
      simp only [Ty.openRigidsFrom, Ty.realize, ihFunction functionScoped,
        ihArgument argumentScoped]

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
    | con id => rfl
    | app _ _ ihFunction ihArgument =>
        simp only [Ty.closeRigids, ihFunction, ihArgument]
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
  | con id => rfl
  | app function argument ihFunction ihArgument =>
      have functionScoped : ∀ id ∈ function.mvars,
          (valuation id).Scoped rigidCount 0 := by
        intro id member
        exact imagesScoped id (by simp [Ty.mvars, member])
      have argumentScoped : ∀ id ∈ argument.mvars,
          (valuation id).Scoped rigidCount 0 := by
        intro id member
        exact imagesScoped id (by simp [Ty.mvars, member])
      simp only [Ty.closeRigids, Ty.realize, ihFunction functionScoped,
        ihArgument argumentScoped]

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
  | .con id => .con id
  | .app function argument => .app function.defaultMVars argument.defaultMVars

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
  | con id => exact ⟨.con id, .con⟩
  | app _ _ ihFunction ihArgument =>
      exact ⟨.app ihFunction.1 ihArgument.1,
        .app ihFunction.2 ihArgument.2⟩

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
  | con id => rfl
  | app function argument ihFunction ihArgument =>
      have functionUnsolved : ∀ id ∈ function.mvars, store.lookup id = none := by
        intro id inside
        exact unsolved id (by
          simp only [Ty.mvars, List.mem_dedup, List.mem_append]
          exact Or.inl inside)
      have argumentUnsolved : ∀ id ∈ argument.mvars, store.lookup id = none := by
        intro id inside
        exact unsolved id (by
          simp only [Ty.mvars, List.mem_dedup, List.mem_append]
          exact Or.inr inside)
      simp only [MStore.apply]
      rw [ihFunction functionUnsolved, ihArgument argumentUnsolved]

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
    | con id => rfl
    | app function argument ihFunction ihArgument =>
        have functionBounded : function.MVarBounded frontier := by
          intro id member
          exact typeBounded id (by simp [Ty.mvars, member])
        have argumentBounded : argument.MVarBounded frontier := by
          intro id member
          exact typeBounded id (by simp [Ty.mvars, member])
        simp only [MStore.apply, Ty.realize, Ty.defaultMVars] at typeFixed ⊢
        injection typeFixed with functionFixed argumentFixed
        rw [ihFunction functionBounded functionFixed,
          ihArgument argumentBounded argumentFixed]
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
  | app functionFit argumentFit functionIH argumentIH =>
      cases templateScoped with
      | app functionScoped argumentScoped =>
          exact .app (functionIH functionScoped) (argumentIH argumentScoped)

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
  | con id => rfl
  | app _ _ ihFunction ihArgument =>
      simp only [Ty.closeRigids, Ty.openWith, ihFunction, ihArgument]

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
    | con id => rfl
    | app _ _ ihFunction ihArgument =>
        simp only [Ty.openRigidsFrom, Ty.closeRigids, ihFunction, ihArgument]
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
  | app _ _ ihFunction ihArgument =>
      cases fits with
      | app functionFits argumentFits =>
          cases openScoped with
          | app functionOpenScoped argumentOpenScoped =>
              exact .app
                (ihFunction functionOpenScoped holes holesUnique functionFits)
                (ihArgument argumentOpenScoped holes holesUnique argumentFits)

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
  | const c => rfl

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
  | const c => rfl

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
  | const c => rfl

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
  | con id => exact .con id
  | app _ _ ihFunction ihArgument => exact .app ihFunction ihArgument

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
  | con id => rfl
  | app function argument ihFunction ihArgument =>
      simp [Ty.closeRigids, Ty.mvars, ihFunction, ihArgument]

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

/-! ## Determinacy and principality

These facts let soundness discharge the uniqueness premise of
`Elaborates.letPoly`, and are the backbone of completeness. -/

/-- Two valuations that agree on a type's metavariables realize the type
identically. -/
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

/-- A type scoped at `level` with no enclosing binders realizes to a
well-formed type whenever all its metavariable images are well-formed. -/
private theorem Ty.realize_wf_of_scoped
    {ty : Ty} {level : Nat} {valuation : MValuation}
    (typeScoped : ty.Scoped level 0)
    (images : ∀ id ∈ ty.mvars, (valuation id).WF level 0) :
    (ty.realize valuation).WF level 0 := by
  induction ty with
  | prim name => exact ⟨.prim, .prim⟩
  | arrow domain codomain ihDomain ihCodomain =>
      cases typeScoped with
      | arrow domainScoped codomainScoped =>
          have domainImages : ∀ id ∈ domain.mvars, (valuation id).WF level 0 := by
            intro id member
            exact images id (by simp [Ty.mvars, member])
          have codomainImages : ∀ id ∈ codomain.mvars, (valuation id).WF level 0 := by
            intro id member
            exact images id (by simp [Ty.mvars, member])
          have domainWF := ihDomain domainScoped domainImages
          have codomainWF := ihCodomain codomainScoped codomainImages
          exact ⟨.arrow domainWF.1 codomainWF.1,
            .arrow domainWF.2 codomainWF.2⟩
  | bvar index =>
      cases typeScoped with
      | bvar hlt => omega
  | rigid level' =>
      cases typeScoped with
      | rigid hlt => exact ⟨.rigid hlt, .rigid⟩
  | mvar id => exact images id (by simp [Ty.mvars])
  | con id =>
      cases typeScoped with
      | con _ => exact ⟨.con id, .con⟩
  | app function argument ihFunction ihArgument =>
      cases typeScoped with
      | app functionScoped argumentScoped =>
          have functionImages : ∀ id ∈ function.mvars, (valuation id).WF level 0 := by
            intro id member
            exact images id (by simp [Ty.mvars, member])
          have argumentImages : ∀ id ∈ argument.mvars, (valuation id).WF level 0 := by
            intro id member
            exact images id (by simp [Ty.mvars, member])
          have functionWF := ihFunction functionScoped functionImages
          have argumentWF := ihArgument argumentScoped argumentImages
          exact ⟨.app functionWF.1 argumentWF.1,
            .app functionWF.2 argumentWF.2⟩

private theorem MStore.getElem?_of_lt {store : MStore} {id : Nat}
    (lt : id < store.length) : ∃ entry, store[id]? = some entry := by
  cases hget : store[id]? with
  | none =>
      rw [List.getElem?_eq_none_iff] at hget
      omega
  | some entry => exact ⟨entry, rfl⟩

private theorem MStore.levelOf_eq_of_getElem? {store : MStore} {id : Nat}
    {entry : MEntry} (hget : store[id]? = some entry) :
    store.levelOf id = entry.level := by
  simp [MStore.levelOf, hget]

/-- An unsolved metavariable can be given any type well-formed at its level:
the solved entries are recomputed and every other unsolved metavariable keeps
its value. -/
private theorem MStore.Models.reassign_aux
    {store : MStore} {valuation : MValuation} {id : Nat} {ty : Ty}
    (leveled : store.Leveled) (normalized : store.Normalized)
    (bounded : store.Bounded store.length)
    (models : store.Models valuation)
    (allocated : id < store.length) (unsolved : store.lookup id = none)
    (wf : ty.WF (store.levelOf id) 0) :
    ∃ updated, store.Models updated ∧ updated id = ty ∧
      ∀ other, store.lookup other = none → other ≠ id →
        updated other = valuation other := by
  let base : MValuation := fun m =>
    if store.lookup m = none then
      if m = id then ty else valuation m
    else valuation m
  let updated : MValuation := fun m =>
    match store.lookup m with
    | none => base m
    | some solution => solution.realize base
  have baseUnsolved : ∀ m, store.lookup m = none →
      base m = if m = id then ty else valuation m := by
    intro m lookup
    simp [base, lookup]
  have updatedUnsolved : ∀ m, store.lookup m = none → updated m = base m := by
    intro m lookup
    simp [updated, lookup]
  have updatedSolved : ∀ {m : Nat} {solution : Ty},
      store.lookup m = some solution →
      updated m = solution.realize base := by
    intro m solution lookup
    simp [updated, lookup]
  refine ⟨updated, ?_, ?_, ?_⟩
  · constructor
    · intro m entry hentry
      have levelEq : store.levelOf m = entry.level :=
        MStore.levelOf_eq_of_getElem? hentry
      cases solution : entry.solution with
      | none =>
          have lookupNone : store.lookup m = none := by
            simp [MStore.lookup, hentry, solution]
          rw [updatedUnsolved m lookupNone, baseUnsolved m lookupNone]
          by_cases same : m = id
          · subst same
            rw [if_pos rfl, ← levelEq]
            exact wf
          · rw [if_neg same]
            exact models.valuationWF m entry hentry
      | some solved =>
          have lookupSome : store.lookup m = some solved := by
            simp [MStore.lookup, hentry, solution]
          rw [updatedSolved lookupSome]
          obtain ⟨scopedTy, levels⟩ := leveled m entry solved hentry solution
          apply Ty.realize_wf_of_scoped scopedTy
          intro u member
          have lookupNone : store.lookup u = none :=
            normalized m solved lookupSome u member
          rw [baseUnsolved u lookupNone]
          by_cases same : u = id
          · subst same
            rw [if_pos rfl]
            exact Ty.WF.mono_rigid wf (levels u member)
          · rw [if_neg same]
            have uBound : u < store.length :=
              bounded m solved lookupSome u member
            obtain ⟨uEntry, uGet⟩ := MStore.getElem?_of_lt uBound
            have uLevel : store.levelOf u = uEntry.level :=
              MStore.levelOf_eq_of_getElem? uGet
            have wfU := models.valuationWF u uEntry uGet
            have uLevelLe : uEntry.level ≤ entry.level := by
              rw [← uLevel]
              exact levels u member
            exact Ty.WF.mono_rigid wfU uLevelLe
    · intro m solution lookup
      rw [updatedSolved lookup]
      have realizeEq : solution.realize updated = solution.realize base := by
        apply Ty.realize_congr
        intro u member
        have lookupNone : store.lookup u = none :=
          normalized m solution lookup u member
        exact updatedUnsolved u lookupNone
      rw [← realizeEq]
  · rw [updatedUnsolved id unsolved, baseUnsolved id unsolved]
    rw [if_pos rfl]
  · intro other lookup different
    rw [updatedUnsolved other lookup, baseUnsolved other lookup]
    rw [if_neg different]

/-- An unsolved metavariable can be given any type well-formed at its level:
the solved entries are recomputed and every other unsolved metavariable keeps
its value. -/
theorem MStore.Models.reassign
    {store : MStore} {valuation : MValuation} {id : Nat} {ty : Ty}
    (leveled : store.Leveled) (normalized : store.Normalized)
    (bounded : store.Bounded store.length)
    (models : store.Models valuation)
    (allocated : id < store.length) (unsolved : store.lookup id = none)
    (wf : ty.WF (store.levelOf id) 0) :
    ∃ updated, store.Models updated ∧ updated id = ty ∧
      ∀ other, store.lookup other = none → other ≠ id →
        updated other = valuation other := by
  exact MStore.Models.reassign_aux leveled normalized bounded models
    allocated unsolved wf

/-- If two realizations of a type coincide, the two valuations agree on every
metavariable of the type. -/
private theorem Ty.realize_mvars_eq {ty : Ty} {first second : MValuation}
    (equal : ty.realize first = ty.realize second) :
    ∀ id ∈ ty.mvars, first id = second id := by
  induction ty with
  | prim name => intro id member; simp [Ty.mvars] at member
  | arrow domain codomain ihDomain ihCodomain =>
      simp only [Ty.realize] at equal
      injection equal with domainEq codomainEq
      intro id member
      simp only [Ty.mvars, List.mem_dedup, List.mem_append] at member
      rcases member with member | member
      · exact ihDomain domainEq id member
      · exact ihCodomain codomainEq id member
  | bvar index => intro id member; simp [Ty.mvars] at member
  | rigid level => intro id member; simp [Ty.mvars] at member
  | mvar id' =>
      intro id member
      simp only [Ty.realize, Ty.mvars, List.mem_singleton] at equal member
      subst member
      exact equal
  | con id => intro m member; simp [Ty.mvars] at member
  | app function argument ihFunction ihArgument =>
      simp only [Ty.realize] at equal
      injection equal with functionEq argumentEq
      intro id member
      simp only [Ty.mvars, List.mem_dedup, List.mem_append] at member
      rcases member with member | member
      · exact ihFunction functionEq id member
      · exact ihArgument argumentEq id member

/-- Every allocated, unsolved metavariable from `start` on whose level is at
most `level` occurs in the solution of a metavariable allocated before
`start`. -/
def MStore.Anchored (store : MStore) (start level : Nat) : Prop :=
  ∀ id, start ≤ id → id < store.length → store.levelOf id ≤ level →
    store.lookup id = none →
    ∃ outer ty, outer < start ∧ store.lookup outer = some ty ∧ id ∈ ty.mvars

/-- Anchored metavariables at or below `level` are determined by the older
ones: two models that agree before `start` agree on all of them. -/
theorem MStore.Anchored.agree
    {store : MStore} {start level : Nat} {first second : MValuation}
    (leveled : store.Leveled) (normalized : store.Normalized)
    (bounded : store.Bounded store.length)
    (anchored : store.Anchored start level)
    (firstModels : store.Models first) (secondModels : store.Models second)
    (agree : ∀ id, id < start → first id = second id) :
    ∀ id, id < store.length → store.levelOf id ≤ level →
      first id = second id := by
  have unsolvedAgree : ∀ id, id < store.length → store.lookup id = none →
      store.levelOf id ≤ level → first id = second id := by
    intro id hid lookupNone hlevel
    by_cases belowStart : id < start
    · exact agree id belowStart
    · obtain ⟨outer, ty, outerLt, outerLookup, idMem⟩ :=
        anchored id (by omega) hid hlevel lookupNone
      have firstOuter := firstModels.equation outer ty outerLookup
      have secondOuter := secondModels.equation outer ty outerLookup
      have outerAgree : first outer = second outer := agree outer outerLt
      have realizeEq : ty.realize first = ty.realize second := by
        rw [← firstOuter, ← secondOuter, outerAgree]
      exact Ty.realize_mvars_eq realizeEq id idMem
  intro id hid hlevel
  cases hget : store[id]? with
  | none =>
      have noneEq : store[id]? = none := hget
      rw [List.getElem?_eq_none_iff] at noneEq
      omega
  | some entry =>
      cases solution : entry.solution with
      | none =>
          have lookupNone : store.lookup id = none := by
            simp [MStore.lookup, hget, solution]
          exact unsolvedAgree id hid lookupNone hlevel
      | some solved =>
          have lookupSome : store.lookup id = some solved := by
            simp [MStore.lookup, hget, solution]
          have firstEq := firstModels.equation id solved lookupSome
          have secondEq := secondModels.equation id solved lookupSome
          have realizeEq : solved.realize first = solved.realize second := by
            apply Ty.realize_congr
            intro m member
            have lookupNone : store.lookup m = none :=
              normalized id solved lookupSome m member
            have mBound : m < store.length :=
              bounded id solved lookupSome m member
            have levelLe : store.levelOf m ≤ level := by
              have entryLevel : store.levelOf id = entry.level :=
                MStore.levelOf_eq_of_getElem? hget
              have mLevel := (leveled id entry solved hget solution).2 m member
              have hlevel' : entry.level ≤ level := by
                rwa [entryLevel] at hlevel
              exact le_trans mLevel hlevel'
            exact unsolvedAgree m mBound lookupNone levelLe
          rw [firstEq, secondEq, realizeEq]

/-- The defining equation of one phase step. -/
private theorem unifyPhase_cons_eq (store : MStore) (fuel : Nat)
    (left right : Ty) (rest : List Constraint) :
    unifyPhase store (fuel + 1) ((left, right) :: rest) =
      if left = right then unifyPhase store fuel rest
      else
        match left, right with
        | .mvar id, ty | ty, .mvar id =>
            if store.canBind id ty then
              (UnifyPhase.bound (store.solve id ty)
                (rest.map (Constraint.substMVar id ty)) : UnifyPhase)
            else .failed
        | .arrow leftDomain leftCodomain,
          .arrow rightDomain rightCodomain =>
            unifyPhase store fuel
              ((leftDomain, rightDomain) :: (leftCodomain, rightCodomain) :: rest)
        | .app leftFunction leftArgument,
          .app rightFunction rightArgument =>
            unifyPhase store fuel
              ((leftFunction, rightFunction) :: (leftArgument, rightArgument) :: rest)
        | _, _ => .failed := by
  rfl

private theorem unifyLoop_succ (fuel : Nat) (store : MStore)
    (constraints : List Constraint) :
    unifyLoop (fuel + 1) store constraints =
      match unifyPhase store (Constraints.size constraints) constraints with
      | .finished result => some result
      | .bound result rest => unifyLoop fuel result rest
      | .failed | .outOfFuel => none := by
  rfl

private theorem MStore.solve_getElem? (store : MStore) (id : Nat) (ty : Ty) (j : Nat) :
    (store.solve id ty)[j]? =
      (store[j]?).map (fun entry =>
        if j = id then { entry with solution := some ty }
        else
          { level := if j ∈ ty.mvars then min entry.level (store.levelOf id) else entry.level,
            solution := entry.solution.map (·.substMVar id ty) }) := by
  simp only [MStore.solve, List.getElem?_mapIdx]

private theorem MStore.solve_length (store : MStore) (id : Nat) (ty : Ty) :
    (store.solve id ty).length = store.length := by
  simp [MStore.solve]

private theorem MStore.lookup_solve_of_ne (store : MStore) (id j : Nat) (ty : Ty)
    (different : j ≠ id) :
    (store.solve id ty).lookup j =
      (store.lookup j).map (·.substMVar id ty) := by
  unfold MStore.lookup
  rw [MStore.solve_getElem?]
  cases h : store[j]? with
  | none => simp
  | some entry => simp [different, h]

private theorem MStore.lookup_solve_self (store : MStore) (id : Nat) (ty : Ty)
    {e : MEntry} (entry : store[id]? = some e) :
    (store.solve id ty).lookup id = some ty := by
  unfold MStore.lookup
  rw [MStore.solve_getElem?]
  simp [entry]

private theorem MStore.levelOf_solve (store : MStore) (id j : Nat) (ty : Ty) :
    (store.solve id ty).levelOf j =
      if j = id then store.levelOf id
      else if j ∈ ty.mvars then min (store.levelOf j) (store.levelOf id)
      else store.levelOf j := by
  by_cases same : j = id
  · subst same
    unfold MStore.levelOf
    rw [MStore.solve_getElem?]
    cases h : store[j]? <;> simp [h]
  · unfold MStore.levelOf
    rw [MStore.solve_getElem?]
    cases h : store[j]? <;> simp [h, same, MStore.levelOf]

/-- Substitution preserves a metavariable that is not the substituted one. -/
private theorem Ty.mem_mvars_substMVar_of_mem_of_ne {ty replacement : Ty}
    {m target : Nat} (member : m ∈ ty.mvars) (different : m ≠ target) :
    m ∈ (ty.substMVar target replacement).mvars := by
  induction ty with
  | prim name => simp [Ty.mvars] at member
  | arrow domain codomain ihDomain ihCodomain =>
      simp only [Ty.substMVar, Ty.mvars, List.mem_dedup, List.mem_append] at member ⊢
      rcases member with member | member
      · exact Or.inl (ihDomain member)
      · exact Or.inr (ihCodomain member)
  | bvar index => simp [Ty.mvars] at member
  | rigid level => simp [Ty.mvars] at member
  | mvar id =>
      have idEq : m = id := by simpa [Ty.mvars] using member
      subst m
      simp [Ty.substMVar, Ty.mvars, different]
  | con id => simp [Ty.mvars] at member
  | app function argument ihFunction ihArgument =>
      simp only [Ty.substMVar, Ty.mvars, List.mem_dedup, List.mem_append] at member ⊢
      rcases member with member | member
      · exact Or.inl (ihFunction member)
      · exact Or.inr (ihArgument member)

/-- Substitution preserves every metavariable of the replacement, when the
substituted metavariable actually occurs in the type. -/
private theorem Ty.mem_mvars_substMVar_of_mem_replacement {ty replacement : Ty}
    {m target : Nat} (occurs : target ∈ ty.mvars)
    (member : m ∈ replacement.mvars) :
    m ∈ (ty.substMVar target replacement).mvars := by
  induction ty with
  | prim name => simp [Ty.mvars] at occurs
  | arrow domain codomain ihDomain ihCodomain =>
      simp only [Ty.mvars, List.mem_dedup, List.mem_append] at occurs
      rcases occurs with occurs | occurs
      · simp only [Ty.substMVar, Ty.mvars, List.mem_dedup, List.mem_append]
        exact Or.inl (ihDomain occurs)
      · simp only [Ty.substMVar, Ty.mvars, List.mem_dedup, List.mem_append]
        exact Or.inr (ihCodomain occurs)
  | bvar index => simp [Ty.mvars] at occurs
  | rigid level => simp [Ty.mvars] at occurs
  | mvar id =>
      have idEq : target = id := by simpa [Ty.mvars] using occurs
      subst target
      simpa [Ty.substMVar] using member
  | con id => simp [Ty.mvars] at occurs
  | app function argument ihFunction ihArgument =>
      simp only [Ty.mvars, List.mem_dedup, List.mem_append] at occurs
      rcases occurs with occurs | occurs
      · simp only [Ty.substMVar, Ty.mvars, List.mem_dedup, List.mem_append]
        exact Or.inl (ihFunction occurs)
      · simp only [Ty.substMVar, Ty.mvars, List.mem_dedup, List.mem_append]
        exact Or.inr (ihArgument occurs)

private theorem InferState.constrain_solutions
    {state checked : InferState} {left right : Ty}
    (run : state.constrain left right = some checked) :
    state.solutions.unify left right = some checked.solutions := by
  unfold InferState.constrain at run
  cases h : state.solutions.unify left right with
  | none => rw [h] at run; simp at run
  | some result =>
      rw [h] at run
      simp only [Option.map_some, Option.some.injEq] at run
      subst run
      rfl

private theorem MStore.canBind_data {store : MStore} {id : Nat} {ty : Ty}
    (guard : store.canBind id ty = true) :
    ∃ entry, store[id]? = some entry ∧ entry.solution = none := by
  unfold MStore.canBind at guard
  cases hget : store[id]? with
  | none => simp [hget] at guard
  | some entry =>
      simp only [hget, Bool.and_eq_true, Bool.not_eq_true',
        Option.isNone_iff_eq_none] at guard
      exact ⟨entry, rfl, guard.1.1⟩

private theorem MStore.solve_anchored_of_canBind
    {store : MStore} {id : Nat} {ty : Ty} {start level : Nat}
    (anchored : store.Anchored start level)
    (guard : store.canBind id ty = true) :
    (store.solve id ty).Anchored start level := by
  obtain ⟨entry, hentry, hnone⟩ := MStore.canBind_data guard
  have allocated : id < store.length := by
    by_contra hge
    have noneEq : store[id]? = none :=
      List.getElem?_eq_none_iff.mpr (by omega)
    rw [noneEq] at hentry
    exact Option.noConfusion hentry
  have unsolved : store.lookup id = none := by
    simp [MStore.lookup, hentry, hnone]
  intro j hstart hjlen hlevel hlookup
  have different : j ≠ id := by
    intro same
    subst j
    have selfLookup := MStore.lookup_solve_self store id ty hentry
    rw [selfLookup] at hlookup
    exact Option.noConfusion hlookup
  have jLen : j < store.length := by
    rw [MStore.solve_length] at hjlen
    exact hjlen
  have jLookupNone : store.lookup j = none := by
    cases h : store.lookup j with
    | none => rfl
    | some value =>
        rw [MStore.lookup_solve_of_ne store id j ty different, h] at hlookup
        exact Option.noConfusion hlookup
  have jLevel : (store.solve id ty).levelOf j ≤ level := hlevel
  rw [MStore.levelOf_solve] at jLevel
  simp only [different, if_false] at jLevel
  by_cases jMem : j ∈ ty.mvars
  · by_cases oldLevel : store.levelOf j ≤ level
    · obtain ⟨outer, solution, outerLt, outerLookup, jMemSolution⟩ :=
        anchored j hstart jLen oldLevel jLookupNone
      have outerNe : outer ≠ id := by
        intro same
        subst same
        rw [outerLookup] at unsolved
        exact Option.noConfusion unsolved
      refine ⟨outer, solution.substMVar id ty, outerLt, ?_, ?_⟩
      · rw [MStore.lookup_solve_of_ne store id outer ty outerNe]
        simp [outerLookup]
      · exact Ty.mem_mvars_substMVar_of_mem_of_ne jMemSolution different
    · have jLevelLe : min (store.levelOf j) (store.levelOf id) ≤ level := by
        simpa [jMem] using jLevel
      have idLevel : store.levelOf id ≤ level := by
        by_contra idNot
        have minEq : min (store.levelOf j) (store.levelOf id) = store.levelOf j :=
          Nat.min_eq_left (by omega)
        rw [minEq] at jLevelLe
        omega
      by_cases idBelow : id < start
      · refine ⟨id, ty, idBelow, ?_, jMem⟩
        exact MStore.lookup_solve_self store id ty hentry
      · obtain ⟨outer, solution, outerLt, outerLookup, idMemSolution⟩ :=
          anchored id (by omega) allocated idLevel unsolved
        have outerNe : outer ≠ id := by
          intro same
          subst same
          rw [outerLookup] at unsolved
          exact Option.noConfusion unsolved
        refine ⟨outer, solution.substMVar id ty, outerLt, ?_, ?_⟩
        · rw [MStore.lookup_solve_of_ne store id outer ty outerNe]
          simp [outerLookup]
        · exact Ty.mem_mvars_substMVar_of_mem_replacement idMemSolution jMem
  · have oldLevel : store.levelOf j ≤ level := by
      simpa [jMem] using jLevel
    obtain ⟨outer, solution, outerLt, outerLookup, jMemSolution⟩ :=
      anchored j hstart jLen oldLevel jLookupNone
    have outerNe : outer ≠ id := by
      intro same
      subst same
      rw [outerLookup] at unsolved
      exact Option.noConfusion unsolved
    refine ⟨outer, solution.substMVar id ty, outerLt, ?_, ?_⟩
    · rw [MStore.lookup_solve_of_ne store id outer ty outerNe]
      simp [outerLookup]
    · exact Ty.mem_mvars_substMVar_of_mem_of_ne jMemSolution different

private theorem match_bound_anchored
    {store : MStore} {id : Nat} {ty : Ty} {rest : List Constraint}
    {start level : Nat}
    (anchored : store.Anchored start level)
    (guard : store.canBind id ty = true) :
    (match (UnifyPhase.bound (store.solve id ty) rest : UnifyPhase) with
     | .finished result => result.Anchored start level
     | .bound result _ => result.Anchored start level
     | .failed | .outOfFuel => True) := by
  simpa using MStore.solve_anchored_of_canBind anchored guard

private theorem ite_bound_anchored
    {store : MStore} {id : Nat} {ty : Ty} {rest : List Constraint}
    {start level : Nat}
    (anchored : store.Anchored start level) :
    (match (if store.canBind id ty = true then
              (UnifyPhase.bound (store.solve id ty) rest : UnifyPhase)
            else .failed) with
     | .finished result => result.Anchored start level
     | .bound result _ => result.Anchored start level
     | .failed | .outOfFuel => True) := by
  by_cases guard : store.canBind id ty = true
  · rw [if_pos guard]
    exact match_bound_anchored (rest := rest) anchored guard
  · rw [if_neg guard]
    trivial

private theorem unifyPhase_anchored
    {store : MStore} {fuel : Nat} {constraints : List Constraint}
    {start level : Nat}
    (anchored : store.Anchored start level) :
    (match unifyPhase store fuel constraints with
     | .finished result => result.Anchored start level
     | .bound result _ => result.Anchored start level
     | .failed | .outOfFuel => True) := by
  induction fuel generalizing constraints with
  | zero =>
      cases constraints with
      | nil => simp [unifyPhase, anchored]
      | cons _ _ => simp [unifyPhase]
  | succ fuel ih =>
      cases constraints with
      | nil => simp [unifyPhase, anchored]
      | cons constraint rest =>
          obtain ⟨left, right⟩ := constraint
          rw [unifyPhase_cons_eq]
          by_cases equal : left = right
          · rw [if_pos equal]
            exact ih
          · rw [if_neg equal]
            cases left <;> cases right <;> simp only []
            all_goals first
              | exact ih
              | exact ite_bound_anchored anchored
              | simp

private theorem unifyPhase_finished_anchored
    {store result : MStore} {fuel : Nat} {constraints : List Constraint}
    {start level : Nat}
    (anchored : store.Anchored start level)
    (run : unifyPhase store fuel constraints = .finished result) :
    result.Anchored start level := by
  have h := unifyPhase_anchored (fuel := fuel) (constraints := constraints)
    (start := start) (level := level) anchored
  rw [run] at h
  exact h

private theorem unifyPhase_bound_anchored
    {store result : MStore} {fuel : Nat} {constraints rest : List Constraint}
    {start level : Nat}
    (anchored : store.Anchored start level)
    (run : unifyPhase store fuel constraints = .bound result rest) :
    result.Anchored start level := by
  have h := unifyPhase_anchored (fuel := fuel) (constraints := constraints)
    (start := start) (level := level) anchored
  rw [run] at h
  exact h

private theorem unifyLoop_anchored
    {fuel : Nat} {store result : MStore} {constraints : List Constraint}
    {start level : Nat}
    (anchored : store.Anchored start level)
    (run : unifyLoop fuel store constraints = some result) :
    result.Anchored start level := by
  induction fuel generalizing store constraints with
  | zero => simp [unifyLoop] at run
  | succ fuel ih =>
      rw [unifyLoop_succ] at run
      split at run
      · rename_i finishedRun
        injection run with resultEq
        subst resultEq
        exact unifyPhase_finished_anchored anchored finishedRun
      · rename_i boundRun
        exact ih (unifyPhase_bound_anchored anchored boundRun) run
      · exact nomatch run
      · exact nomatch run

/-- Unification keeps metavariables anchored: one is lowered to `level` or
below only by becoming part of a solution at that level, which is older or
itself anchored. -/
theorem MStore.unify_anchored
    {store result : MStore} {left right : Ty} {start level : Nat}
    (normalized : store.Normalized)
    (anchored : store.Anchored start level)
    (run : store.unify left right = some result) :
    result.Anchored start level := by
  unfold MStore.unify at run
  exact unifyLoop_anchored anchored run

private theorem MStore.levelOf_append_replicate {store : MStore} {count level id : Nat}
    (hlo : store.length ≤ id) (hhi : id < store.length + count) :
    (store ++ List.replicate count (⟨level, none⟩ : MEntry)).levelOf id = level := by
  unfold MStore.levelOf
  rw [List.getElem?_append_right hlo]
  have hlt : id - store.length < count := by omega
  rw [List.getElem?_replicate]
  simp only [hlt, if_true, Option.map_some, Option.getD_some]

private theorem MStore.Anchored.append_replicate
    {store : MStore} {count level start anchorLevel : Nat}
    (anchored : store.Anchored start anchorLevel)
    (higher : anchorLevel < level) :
    (store ++ List.replicate count (⟨level, none⟩ : MEntry)).Anchored
      start anchorLevel := by
  intro id hstart hid hlevel hlookup
  by_cases idOld : id < store.length
  · have oldLookup : store.lookup id = none := by
      simpa [MStore.lookup, List.getElem?_append_left idOld] using hlookup
    have oldLevel : store.levelOf id ≤ anchorLevel := by
      simpa [MStore.levelOf, List.getElem?_append_left idOld] using hlevel
    obtain ⟨outer, ty, outerLt, outerLookup, idMem⟩ :=
      anchored id hstart idOld oldLevel oldLookup
    have outerLtStore : outer < store.length := by
      by_contra hge
      have noneEq : store[outer]? = none :=
        List.getElem?_eq_none_iff.mpr (by omega)
      have lookupNone : store.lookup outer = none := by
        simp [MStore.lookup, noneEq]
      rw [lookupNone] at outerLookup
      exact Option.noConfusion outerLookup
    refine ⟨outer, ty, outerLt, ?_, idMem⟩
    simpa [MStore.lookup, List.getElem?_append_left outerLtStore] using outerLookup
  · have ge : store.length ≤ id := by omega
    have hidLen : id < store.length + count := by
      simpa [List.length_append, List.length_replicate] using hid
    have levelEq := MStore.levelOf_append_replicate (store := store)
      (count := count) (level := level) (id := id) ge hidLen
    rw [levelEq] at hlevel
    omega

private theorem InferState.freshMany_solutions (level count : Nat) (state : InferState) :
    (state.freshMany level count).1.solutions =
      state.solutions ++ List.replicate count (⟨level, none⟩ : MEntry) := by
  induction count generalizing state with
  | zero => simp [InferState.freshMany]
  | succ count ih =>
      simp only [InferState.freshMany]
      rw [ih]
      simp [InferState.fresh, List.replicate_succ, List.append_assoc]

private theorem Ty.InferWF.mono_frontier
    {ty : Ty} {rigidCount binder frontier frontier' : Nat}
    (wf : ty.InferWF rigidCount binder frontier) (le : frontier ≤ frontier') :
    ty.InferWF rigidCount binder frontier' :=
  ⟨wf.1, fun id member => lt_of_lt_of_le (wf.2 id member) le⟩

private theorem Ty.InferWF.mono_rigid
    {ty : Ty} {rigidCount rigidCount' binder frontier : Nat}
    (wf : ty.InferWF rigidCount binder frontier) (le : rigidCount ≤ rigidCount') :
    ty.InferWF rigidCount' binder frontier := by
  have scopedMono : ∀ {candidate : Ty},
      candidate.Scoped rigidCount binder → candidate.Scoped rigidCount' binder := by
    intro candidate hscoped
    induction hscoped with
    | prim => exact .prim
    | arrow _ _ ihDomain ihCodomain => exact .arrow ihDomain ihCodomain
    | bvar hlt => exact .bvar hlt
    | rigid hlt => exact .rigid (lt_of_lt_of_le hlt le)
    | mvar id => exact .mvar id
    | con id => exact .con id
    | app _ _ ihFunction ihArgument => exact .app ihFunction ihArgument
  exact ⟨scopedMono wf.1, wf.2⟩

private theorem Ctx.InferWF.mono_frontier
    {context : Ctx} {rigidCount smaller larger : Nat}
    (wf : context.InferWF rigidCount smaller) (le : smaller ≤ larger) :
    context.InferWF rigidCount larger :=
  fun scheme member => Ty.InferWF.mono_frontier (wf scheme member) le

private theorem Ctx.InferWF.mono_rigid
    {context : Ctx} {frontier smaller larger : Nat}
    (wf : context.InferWF smaller frontier) (le : smaller ≤ larger) :
    context.InferWF larger frontier :=
  fun scheme member => Ty.InferWF.mono_rigid (wf scheme member) le

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

/-- Inference at a rigid count above `level` (inside an explicit scheme's
region) allocates nothing at or below `level`, so it preserves anchoring. -/
theorem inferFuel_anchored
    {fuel rigidCount start level : Nat} {ctx : Ctx} {input : Source}
    {state : InferState} {result : InferResult}
    (stateSafe : state.Safe)
    (ctxWF : ctx.InferWF rigidCount state.next)
    (ctxLevels : ∀ scheme ∈ ctx, scheme.body.LevelBounded state.solutions rigidCount)
    (inputScoped : input.TypeScoped rigidCount 0)
    (below : level < rigidCount)
    (startLe : start ≤ state.next)
    (anchored : state.solutions.Anchored start level)
    (run : inferFuel sig fuel rigidCount ctx input state = some result) :
    result.state.solutions.Anchored start level := by
  have ctx_mono : ∀ {context : Ctx} {rigid smaller larger : Nat},
      context.InferWF rigid smaller → smaller ≤ larger →
        context.InferWF rigid larger := by
    intro context rigid smaller larger h le scheme member
    exact Ty.InferWF.mono_frontier (h scheme member) le
  have ctx_mono_rigid : ∀ {context : Ctx} {frontier smaller larger : Nat},
      context.InferWF smaller frontier → smaller ≤ larger →
        context.InferWF larger frontier := by
    intro context frontier smaller larger h le scheme member
    exact Ty.InferWF.mono_rigid (h scheme member) le
  induction fuel generalizing rigidCount ctx input state result with
  | zero => simp [inferFuel] at run
  | succ fuel ih =>
      cases input with
      | primLit literal =>
          simp only [inferFuel, Option.some.injEq] at run
          subst result
          exact anchored
      | primOp op =>
          cases hty : op.ty sig with
          | none => simp [inferFuel, hty] at run
          | some primTy =>
              simp [inferFuel, hty] at run
              subst result
              exact anchored
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
              have appended : fresh.1.solutions =
                  state.solutions ++ List.replicate scheme.paramCount
                    (⟨rigidCount, none⟩ : MEntry) := by
                simpa [fresh] using InferState.freshMany_solutions rigidCount
                  scheme.paramCount state
              rw [appended]
              exact MStore.Anchored.append_replicate anchored below
      | lambda ann body =>
          cases inputScoped with
          | lambda annScoped bodyScoped =>
            cases ann with
            | none =>
                simp only [inferFuel] at run
                let seeded := state.fresh rigidCount
                have seededSafe := InferState.fresh_safe
                  (level := rigidCount) stateSafe
                have seededAnchored : seeded.1.solutions.Anchored start level := by
                  have appended : seeded.1.solutions =
                      state.solutions ++ List.replicate 1
                        (⟨rigidCount, none⟩ : MEntry) := by
                    simp [seeded, InferState.fresh, List.replicate_one]
                  rw [appended]
                  exact MStore.Anchored.append_replicate anchored below
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
                    exact ih (result := bodyResult) seededSafe.1 bodyCtxWF
                      bodyCtxLevels bodyScoped
                      below (le_trans startLe seededSafe.2.2.2.1)
                      seededAnchored bodyRun
            | some template =>
                have templateScoped := annScoped template rfl
                simp only [inferFuel] at run
                let seeded := state.allocate rigidCount template
                have seededSafe := InferState.allocate_safe
                  (level := rigidCount) (rigidCount := rigidCount)
                  stateSafe templateScoped
                have seededAnchored : seeded.1.solutions.Anchored start level := by
                  have appended : seeded.1.solutions =
                      state.solutions ++ List.replicate
                        ((template.allocate state.next).next - state.next)
                        (⟨rigidCount, none⟩ : MEntry) := by
                    simp [seeded, InferState.allocate]
                  rw [appended]
                  exact MStore.Anchored.append_replicate anchored below
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
                    exact ih (result := bodyResult) seededSafe.1 bodyCtxWF
                      bodyCtxLevels bodyScoped
                      below (le_trans startLe seededSafe.2.2.2.1)
                      seededAnchored bodyRun
      | app function argument =>
          cases inputScoped with
          | app functionScoped argumentScoped =>
            simp only [inferFuel] at run
            cases functionRun : inferFuel sig fuel rigidCount ctx function state with
            | none => simp [functionRun] at run
            | some functionResult =>
              have functionAnchored := ih (result := functionResult)
                stateSafe ctxWF ctxLevels functionScoped
                below startLe anchored functionRun
              have functionSafe := inferFuel_safe stateSafe ctxWF ctxLevels
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
              cases argumentRun : inferFuel sig fuel rigidCount ctx argument
                  functionResult.state with
              | none => simp [functionRun, argumentRun] at run
              | some argumentResult =>
                have argumentAnchored := ih (result := argumentResult)
                  functionSafe.1 argumentCtxWF
                  argumentCtxLevels argumentScoped below
                  (le_trans startLe functionSafe.2.2.2.1) functionAnchored
                  argumentRun
                have argumentSafe := inferFuel_safe functionSafe.1 argumentCtxWF
                  argumentCtxLevels argumentScoped argumentRun
                let fresh := argumentResult.state.fresh rigidCount
                have freshSafe := InferState.fresh_safe
                  (level := rigidCount) argumentSafe.1
                have freshAnchored : fresh.1.solutions.Anchored start level := by
                  have appended : fresh.1.solutions =
                      argumentResult.state.solutions ++ List.replicate 1
                        (⟨rigidCount, none⟩ : MEntry) := by
                    simp [fresh, InferState.fresh, List.replicate_one]
                  rw [appended]
                  exact MStore.Anchored.append_replicate argumentAnchored below
                have functionTyWF : functionResult.ty.InferWF rigidCount 0
                    fresh.1.next := Ty.InferWF.mono_frontier functionSafe.2.1
                      (le_trans argumentSafe.2.2.2.1 freshSafe.2.2.2.1)
                have argumentTyWF : argumentResult.ty.InferWF rigidCount 0
                    fresh.1.next := Ty.InferWF.mono_frontier argumentSafe.2.1
                      freshSafe.2.2.2.1
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
                    have hunify := InferState.constrain_solutions
                      (state := fresh.1) (checked := checked) checkedRun
                    exact MStore.unify_anchored
                      (store := fresh.1.solutions) (result := checked.solutions)
                      freshSafe.1.solutionsNormalized freshAnchored hunify
      | letIn ann rhs body =>
          cases ann with
          | none =>
            cases inputScoped with
            | letMono rhsScoped bodyScoped =>
              simp only [inferFuel] at run
              cases rhsRun : inferFuel sig fuel rigidCount ctx rhs state with
              | none => simp [rhsRun] at run
              | some rhsResult =>
                have rhsAnchored := ih (result := rhsResult)
                  stateSafe ctxWF ctxLevels rhsScoped below
                  startLe anchored rhsRun
                have rhsSafe := inferFuel_safe stateSafe ctxWF ctxLevels
                  rhsScoped rhsRun
                let rhsTy := rhsResult.state.solutions.apply rhsResult.ty
                have rhsApplied := MStore.apply_inferWF rhsSafe.1.solutionsLeveled
                  rhsSafe.1.solutionsBounded rhsSafe.2.1 rhsSafe.2.2.1
                have bodyCtxWF : Ctx.InferWF (PolyTy.mono rhsTy :: ctx)
                    rigidCount rhsResult.state.next := by
                  intro scheme member
                  simp only [List.mem_cons] at member
                  rcases member with rfl | member
                  · exact rhsApplied.1
                  · exact ctx_mono ctxWF rhsSafe.2.2.2.1 scheme member
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
                    exact ih (result := bodyResult) rhsSafe.1 bodyCtxWF
                      bodyCtxLevels bodyScoped below
                      (le_trans startLe rhsSafe.2.2.2.1) rhsAnchored bodyRun
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
              have seededAnchored : seeded.1.solutions.Anchored start level := by
                have appended : seeded.1.solutions =
                    state.solutions ++ List.replicate
                      ((openedTemplate.allocate state.next).next - state.next)
                      (⟨inner, none⟩ : MEntry) := by
                  simp [seeded, InferState.allocate]
                rw [appended]
                exact MStore.Anchored.append_replicate anchored (by omega)
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
              cases rhsRun : inferFuel sig fuel inner ctx
                  (rhs.openRigids rigidCount count) seeded.1 with
              | none =>
                  dsimp [seeded, openedTemplate, count, inner] at rhsRun
                  simp [rhsRun] at run
              | some rhsResult =>
                  dsimp [seeded, openedTemplate, count, inner] at rhsRun
                  have rhsAnchored := ih (result := rhsResult)
                    seededSafe.1 rhsCtxWF rhsCtxLevels
                    openedRhsScoped (by omega)
                    (le_trans startLe seededSafe.2.2.2.1) seededAnchored rhsRun
                  have rhsSafe := inferFuel_safe seededSafe.1 rhsCtxWF
                    rhsCtxLevels openedRhsScoped rhsRun
                  have seededTyAtRhs : seeded.2.InferWF inner 0
                      rhsResult.state.next :=
                    Ty.InferWF.mono_frontier seededSafe.2.1 rhsSafe.2.2.2.1
                  cases checkedRun : rhsResult.state.constrain
                      rhsResult.ty seeded.2 with
                  | none =>
                      dsimp [seeded, openedTemplate, count, inner] at checkedRun
                      simp [rhsRun, checkedRun] at run
                  | some checked =>
                      dsimp [seeded, openedTemplate, count, inner] at checkedRun
                      have checkedSafe := InferState.constrain_safe rhsSafe.1
                        rhsSafe.2.1 seededTyAtRhs checkedRun
                      simp [rhsRun, checkedRun] at run
                      let completedOpen := checked.solutions.apply seeded.2
                      let completed : PolyTy :=
                        ⟨count, completedOpen.closeRigids rigidCount count⟩
                      have localStartLe : localStart ≤ checked.next := by
                        rw [checkedSafe.2.1]
                        exact le_trans seededSafe.2.2.2.1 rhsSafe.2.2.2.1
                      have ctxWFChecked : ctx.InferWF rigidCount checked.next :=
                        ctx_mono ctxWF localStartLe
                      have ctxLevelsChecked :
                          ∀ scheme ∈ ctx, scheme.body.LevelBounded
                            checked.solutions rigidCount := by
                        intro scheme member id hid
                        have idBound : id < state.next :=
                          (ctxWF scheme member).2 id hid
                        have hidSeeded : id < seeded.1.next :=
                          lt_of_lt_of_le idBound seededSafe.2.2.2.1
                        have hidRhs : id < rhsResult.state.next :=
                          lt_of_lt_of_le hidSeeded rhsSafe.2.2.2.1
                        calc checked.solutions.levelOf id
                            ≤ rhsResult.state.solutions.levelOf id :=
                              checkedSafe.2.2.2 id
                          _ ≤ seeded.1.solutions.levelOf id :=
                              rhsSafe.2.2.2.2 id hidSeeded
                          _ = state.solutions.levelOf id :=
                              seededSafe.2.2.2.2 id idBound
                          _ ≤ rigidCount := ctxLevels scheme member id hid
                      have hunify := InferState.constrain_solutions
                        (state := rhsResult.state) (checked := checked) checkedRun
                      have checkedAnchored : checked.solutions.Anchored
                          start level :=
                        MStore.unify_anchored
                          (store := rhsResult.state.solutions)
                          (result := checked.solutions)
                          rhsSafe.1.solutionsNormalized rhsAnchored hunify
                      have seededAtChecked : seeded.2.InferWF inner 0
                          checked.next := by
                        rw [checkedSafe.2.1]
                        exact seededTyAtRhs
                      have seededLevelsChecked : seeded.2.LevelBounded
                          checked.solutions inner :=
                        Ty.LevelBounded.mono_le
                          (Ty.LevelBounded.mono_le_on seededSafe.2.2.1
                            (fun id member => rhsSafe.2.2.2.2 id
                              (seededSafe.2.1.2 id member)))
                          (fun id => checkedSafe.2.2.2 id)
                      have completedOpenApplied := MStore.apply_inferWF
                        checkedSafe.1.solutionsLeveled
                        checkedSafe.1.solutionsBounded
                        seededAtChecked seededLevelsChecked
                      have completedBodyScoped :
                          completed.body.Scoped rigidCount count := by
                        simpa [completed, inner] using
                          Ty.closeRigids_scoped_zero completedOpenApplied.1.1
                      have completedBodyBounded :
                          completed.body.MVarBounded checked.next := by
                        simpa [completed] using
                          Ty.closeRigids_mvarBounded completedOpenApplied.1.2
                      have completedInferWF : completed.InferWF
                          rigidCount checked.next :=
                        ⟨completedBodyScoped, completedBodyBounded⟩
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
                        · have good :
                              completedOpen.mvars.all
                                (fun id => checked.solutions.levelOf id ≤ rigidCount) = true := by
                            refine List.all_eq_true.mpr ?_
                            intro id mem
                            simpa [completedOpen] using run.1 id mem
                          simpa [completed] using
                            (Ty.closeRigids_levelBounded
                              (base := rigidCount) (count := count)
                              (store := checked.solutions)
                              (ty := completedOpen)
                              (by simpa [Ty.LevelBounded] using
                                (List.all_eq_true.mp good)))
                        · exact ctxLevelsChecked scheme member
                      cases bodyRun : inferFuel sig fuel rigidCount
                          (completed :: ctx) body checked with
                      | none =>
                          simp [completed, completedOpen, count, inner,
                            seeded, openedTemplate, bodyRun] at run
                      | some bodyResult =>
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
                          exact ih (result := bodyResult) checkedSafe.1 bodyCtxWF
                            bodyCtxLevels bodyScoped below
                            (le_trans startLe localStartLe) checkedAnchored bodyRun
      | fix ann body =>
          cases inputScoped with
          | fix annScoped bodyScoped =>
            simp only [inferFuel] at run
            let seeded := state.allocate rigidCount ann
            have seededSafe := InferState.allocate_safe
              (level := rigidCount) (rigidCount := rigidCount)
              stateSafe annScoped
            have seededAnchored : seeded.1.solutions.Anchored start level := by
              have appended : seeded.1.solutions =
                  state.solutions ++ List.replicate
                    ((ann.allocate state.next).next - state.next)
                    (⟨rigidCount, none⟩ : MEntry) := by
                simp [seeded, InferState.allocate]
              rw [appended]
              exact MStore.Anchored.append_replicate anchored below
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
                      .fix seeded.2 bodyResult.elaborated⟩) =
                      some result at run
                have bodyAnchored := ih (result := bodyResult)
                  seededSafe.1 bodyCtxWF bodyCtxLevels
                  bodyScoped below (le_trans startLe seededSafe.2.2.2.1)
                  seededAnchored bodyRun
                have bodySafe := inferFuel_safe seededSafe.1 bodyCtxWF
                  bodyCtxLevels bodyScoped bodyRun
                have selfWF : seeded.2.InferWF rigidCount 0
                    bodyResult.state.next :=
                  Ty.InferWF.mono_frontier seededSafe.2.1 bodySafe.2.2.2.1
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
                    have hunify := InferState.constrain_solutions
                      (state := bodyResult.state) (checked := checked) checkedRun
                    exact MStore.unify_anchored
                      (store := bodyResult.state.solutions)
                      (result := checked.solutions)
                      bodySafe.1.solutionsNormalized bodyAnchored hunify
      | const c =>
          simp only [inferFuel] at run
          cases lookup : sig.schemeOf c with
          | none => simp [lookup] at run
          | some scheme =>
              simp only [lookup] at run
              cases hb : scheme.wfB 0 with
              | false => simp [hb] at run
              | true =>
                  let fresh := state.freshMany rigidCount scheme.paramCount
                  have resultEq : result =
                      ⟨fresh.1, scheme.openWith fresh.2, .const c⟩ := by
                    simpa [fresh, hb] using run.symm
                  subst result
                  have appended : fresh.1.solutions =
                      state.solutions ++ List.replicate scheme.paramCount
                        (⟨rigidCount, none⟩ : MEntry) := by
                    simpa [fresh] using InferState.freshMany_solutions rigidCount
                      scheme.paramCount state
                  rw [appended]
                  exact MStore.Anchored.append_replicate anchored below

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
  | app _ _ ihFunction ihArgument =>
      exact .app ihFunction ihArgument

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

private theorem Ctx.realize_congr {ctx : Ctx} {first second : MValuation}
    (agree : ∀ scheme ∈ ctx, ∀ id ∈ scheme.body.mvars, first id = second id) :
    Ctx.realize ctx first = Ctx.realize ctx second := by
  unfold Ctx.realize
  apply List.map_congr_left
  intro scheme member
  exact PolyTy.realize_congr (agree scheme member)

/-- Closing the opened rigid block of a scoped type returns the original type. -/
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

/-- Principality: when inference succeeds, every declarative typing of the
input, in any model of the starting state, is an instance of the inferred
type under a model of the final state that agrees on every metavariable that
already existed. -/
theorem inferFuel_principal
    {fuel rigidCount : Nat} {ctx : Ctx} {input : Source}
    {state : InferState} {result : InferResult}
    {valuation : MValuation} {ty : Ty}
    (stateSafe : state.Safe)
    (ctxWF : ctx.InferWF rigidCount state.next)
    (ctxLevels : ∀ scheme ∈ ctx, scheme.body.LevelBounded state.solutions rigidCount)
    (inputScoped : input.TypeScoped rigidCount 0)
    (run : inferFuel sig fuel rigidCount ctx input state = some result)
    (models : state.Models valuation)
    (typing : Typing sig rigidCount (ctx.realize valuation) input ty) :
    ∃ extended, result.state.Models extended ∧
      (∀ id, id < state.next → extended id = valuation id) ∧
      result.ty.realize extended = ty := by
  have ctx_mono : ∀ {context : Ctx} {rigid smaller larger : Nat},
      context.InferWF rigid smaller → smaller ≤ larger →
        context.InferWF rigid larger := by
    intro context rigid smaller larger h le scheme member
    exact Ty.InferWF.mono_frontier (h scheme member) le
  have ctx_mono_rigid : ∀ {context : Ctx} {frontier smaller larger : Nat},
      context.InferWF smaller frontier → smaller ≤ larger →
        context.InferWF larger frontier := by
    intro context frontier smaller larger h le scheme member
    exact Ty.InferWF.mono_rigid (h scheme member) le
  induction fuel generalizing rigidCount ctx input state result valuation ty with
  | zero => simp [inferFuel] at run
  | succ fuel ih =>
      cases input with
      | primLit literal =>
          simp only [inferFuel, Option.some.injEq] at run
          subst result
          cases typing
          cases literal <;>
            exact ⟨valuation, models, (fun id hid => rfl), rfl⟩
      | primOp op =>
          cases hty : op.ty sig with
          | none => simp [inferFuel, hty] at run
          | some primTy =>
              simp [inferFuel, hty] at run
              subst result
              cases typing with
              | primOp htyD =>
                  have hEq : primTy = ty := Option.some.inj (hty.symm.trans htyD)
                  subst hEq
                  exact ⟨valuation, models, (fun id hid => rfl),
                    Ty.realize_eq_self (primOpTy_metaFree htyD) valuation⟩
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
              cases typing with
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
                      (count := scheme.paramCount) stateSafe models argsD
                      argsLen hargsD
                  have applied := MStore.apply_inferWF stateSafe.solutionsLeveled
                    stateSafe.solutionsBounded schemeWF schemeLevels
                  have oldModels : state.Models extended :=
                    InferState.freshMany_refines extended extModels
                  have opened := Ty.realize_openWith (args := fresh.2)
                    (MStore.Models.images_scoped oldModels
                      stateSafe.solutions_length applied.1.2 applied.2)
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
                  refine ⟨extended, extModels, extAgree, ?_⟩
                  rw [resultTyEq, ← schemeDEq]
      | const c =>
          simp only [inferFuel] at run
          cases lookup : sig.schemeOf c with
          | none => simp [lookup] at run
          | some scheme =>
              simp only [lookup] at run
              cases hb : scheme.wfB 0 with
              | false =>
                  cases typing with
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
                  let fresh := state.freshMany rigidCount scheme.paramCount
                  have resultEq : result =
                      ⟨fresh.1, scheme.openWith fresh.2, .const c⟩ := by
                    simpa [fresh, hb] using run.symm
                  subst result
                  cases typing with
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
                        rw [Ty.MetaFree.mvars_eq_nil hwfD.2] at member
                        exact absurd member (List.not_mem_nil)
                      have opened := Ty.realize_openWith (ty := scheme.body)
                        (args := fresh.2) (valuation := extended) imagesScoped
                      have bodyRealize : scheme.body.realize extended =
                          scheme.body :=
                        Ty.realize_eq_self hwfD.2 extended
                      have resultTyEq :
                          (scheme.openWith fresh.2).realize extended =
                            scheme.openWith argsD := by
                        simpa [PolyTy.openWith, bodyRealize, extMap, fresh] using opened
                      exact ⟨extended, extModels, extAgree, resultTyEq⟩
      | lambda ann body =>
          cases inputScoped with
          | lambda annScoped bodyScoped =>
            cases ann with
            | none =>
                simp only [inferFuel] at run
                let seeded := state.fresh rigidCount
                have seededSafe := InferState.fresh_safe
                  (level := rigidCount) stateSafe
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
                    cases typing with
                    | lambda paramWF paramMatches bodyTyping =>
                        rename_i paramTy bodyTy
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
                        have bodyTyping' : Typing sig rigidCount
                            (Ctx.realize (PolyTy.mono seeded.2 :: ctx) firstValuation)
                            body bodyTy := by
                          have ctxEq : Ctx.realize (PolyTy.mono seeded.2 :: ctx)
                              firstValuation =
                              PolyTy.mono paramTy :: Ctx.realize ctx valuation := by
                            change PolyTy.mono (seeded.2.realize firstValuation) ::
                                Ctx.realize ctx firstValuation =
                              PolyTy.mono paramTy :: Ctx.realize ctx valuation
                            rw [seedRealize, ctxRealizeEq]
                          rwa [ctxEq]
                        obtain ⟨extended, bodyModels, bodyAgree, bodyTyEq⟩ :=
                          ih (result := bodyResult) seededSafe.1 bodyCtxWF
                            bodyCtxLevels bodyScoped bodyRun seedModels bodyTyping'
                        have seedLt : state.next < seeded.1.next := by
                          simp [seeded, InferState.fresh]
                        have paramEq : seeded.2.realize extended = paramTy := by
                          have h := bodyAgree state.next seedLt
                          simpa [seeded, firstValuation, InferState.fresh, Ty.realize]
                            using h
                        refine ⟨extended, bodyModels, ?_, ?_⟩
                        · intro id hid
                          exact (bodyAgree id (lt_trans hid seedLt)).trans
                            (firstAgree id hid)
                        · change Ty.arrow
                              (Ty.realize extended
                                (bodyResult.state.solutions.apply seeded.2))
                              (bodyResult.ty.realize extended) =
                            Ty.arrow paramTy bodyTy
                          rw [bodyModels.realize_apply seeded.2, paramEq, bodyTyEq]
            | some template =>
                have templateScoped := annScoped template rfl
                simp only [inferFuel] at run
                let seeded := state.allocate rigidCount template
                have seededSafe := InferState.allocate_safe
                  (level := rigidCount) (rigidCount := rigidCount)
                  stateSafe templateScoped
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
                    cases typing with
                    | lambda paramWF paramMatches bodyTyping =>
                        rename_i paramTy bodyTy
                        obtain ⟨holeVal, holeAgree, holeRealize, holeWF⟩ :=
                          Template.allocate_realizes
                            (template := template) (rigid := rigidCount)
                            (binder := 0) (frontier := state.next)
                            (target := paramTy) (base := valuation)
                            (paramMatches template rfl) templateScoped paramWF
                        obtain ⟨firstValuation, seedModels, seedAgree,
                          seedRealizeEq⟩ :=
                          InferState.allocate_models stateSafe models
                            templateScoped (assigned := holeVal) holeWF
                        have seedRealize : seeded.2.realize firstValuation = paramTy := by
                          simpa [seeded] using seedRealizeEq.trans holeRealize
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
                        have bodyTyping' : Typing sig rigidCount
                            (Ctx.realize (PolyTy.mono seeded.2 :: ctx) firstValuation)
                            body bodyTy := by
                          have ctxEq : Ctx.realize (PolyTy.mono seeded.2 :: ctx)
                              firstValuation =
                              PolyTy.mono paramTy :: Ctx.realize ctx valuation := by
                            change PolyTy.mono (seeded.2.realize firstValuation) ::
                                Ctx.realize ctx firstValuation =
                              PolyTy.mono paramTy :: Ctx.realize ctx valuation
                            rw [seedRealize]
                            congr 1
                            exact Ctx.realize_congr (fun scheme member id hid =>
                              seedAgree id ((ctxWF scheme member).2 id hid))
                          rwa [ctxEq]
                        obtain ⟨extended, bodyModels, bodyAgree, bodyTyEq⟩ :=
                          ih (result := bodyResult) seededSafe.1 bodyCtxWF
                            bodyCtxLevels bodyScoped bodyRun seedModels bodyTyping'
                        have paramEq : seeded.2.realize extended = paramTy := by
                          rw [show seeded.2.realize extended =
                              seeded.2.realize firstValuation by
                            apply Ty.realize_congr
                            intro id member
                            exact bodyAgree id
                              (Template.allocate_mvars templateScoped
                                (frontier := state.next) id
                                (by simpa [seeded] using member)).2]
                          exact seedRealize
                        refine ⟨extended, bodyModels, ?_, ?_⟩
                        · intro id hid
                          exact (bodyAgree id (lt_of_lt_of_le hid
                            seededSafe.2.2.2.1)).trans (seedAgree id hid)
                        · change Ty.arrow
                              (Ty.realize extended
                                (bodyResult.state.solutions.apply seeded.2))
                              (bodyResult.ty.realize extended) =
                            Ty.arrow paramTy bodyTy
                          rw [bodyModels.realize_apply seeded.2, paramEq, bodyTyEq]
      | app function argument =>
          cases inputScoped with
          | app functionScoped argumentScoped =>
            simp only [inferFuel] at run
            cases functionRun : inferFuel sig fuel rigidCount ctx function state with
            | none => simp [functionRun] at run
            | some functionResult =>
              cases typing with
              | app functionTyping argumentTyping =>
                  rename_i argumentTyD
                  have wholeTyWF : ty.WF rigidCount 0 :=
                    Typing.regular (Typing.app functionTyping argumentTyping)
                  have functionSafe := inferFuel_safe stateSafe ctxWF ctxLevels
                    functionScoped functionRun
                  obtain ⟨ext1, functionModels, functionAgree, functionTyEq⟩ :=
                    ih (result := functionResult) stateSafe ctxWF ctxLevels
                      functionScoped functionRun models functionTyping
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
                  cases argumentRun : inferFuel sig fuel rigidCount ctx argument
                      functionResult.state with
                  | none => simp [functionRun, argumentRun] at run
                  | some argumentResult =>
                    have argumentTyping' : Typing sig rigidCount
                        (ctx.realize ext1) argument argumentTyD := by
                      have ctxEq := Ctx.realize_congr (ctx := ctx)
                        (first := ext1) (second := valuation)
                        (fun scheme member id idMem =>
                          functionAgree id ((ctxWF scheme member).2 id idMem))
                      simpa [ctxEq] using argumentTyping
                    obtain ⟨ext2, argumentModels, argumentAgree,
                      argumentTyEq⟩ :=
                      ih (result := argumentResult) functionSafe.1 argumentCtxWF
                        argumentCtxLevels argumentScoped argumentRun functionModels
                        argumentTyping'
                    have argumentSafe := inferFuel_safe functionSafe.1 argumentCtxWF
                      argumentCtxLevels argumentScoped argumentRun
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
                    let checked : InferState := { fresh.1 with solutions := unified }
                    have checkedModels : checked.Models extFresh := by
                      simpa [checked] using unifiedModels
                    have resultEq : result =
                        ⟨checked, checked.solutions.apply fresh.2,
                          .app functionResult.elaborated
                            argumentResult.elaborated⟩ := by
                      have h : some result = some
                          ⟨checked, checked.solutions.apply fresh.2,
                            .app functionResult.elaborated
                              argumentResult.elaborated⟩ := by
                        simpa [inferFuel, functionRun, argumentRun,
                          InferState.constrain, unifiedRun, fresh, checked] using run.symm
                      exact Option.some.inj h
                    subst result
                    refine ⟨extFresh, checkedModels, ?_, ?_⟩
                    · intro id hid
                      have idFunction : id < functionResult.state.next :=
                        lt_of_lt_of_le hid functionSafe.2.2.2.1
                      have idArgument : id < argumentResult.state.next :=
                        lt_of_lt_of_le idFunction argumentSafe.2.2.2.1
                      exact (freshAgree id idArgument).trans
                        ((argumentAgree id idFunction).trans (functionAgree id hid))
                    · change (checked.solutions.apply fresh.2).realize extFresh = ty
                      rw [checkedModels.realize_apply fresh.2]
                      exact freshVal
      | letIn ann rhs body =>
          cases ann with
          | none =>
            cases inputScoped with
            | letMono rhsScoped bodyScoped =>
              simp only [inferFuel] at run
              cases rhsRun : inferFuel sig fuel rigidCount ctx rhs state with
              | none => simp [rhsRun] at run
              | some rhsResult =>
                cases typing with
                | letMono rhsWF rhsTyping bodyTyping =>
                    rename_i rhsTyD
                    have rhsSafe := inferFuel_safe stateSafe ctxWF ctxLevels
                      rhsScoped rhsRun
                    obtain ⟨ext1, rhsModels, rhsAgree, rhsTyEq⟩ :=
                      ih (result := rhsResult) stateSafe ctxWF ctxLevels rhsScoped
                        rhsRun models rhsTyping
                    let rhsTy := rhsResult.state.solutions.apply rhsResult.ty
                    have rhsApplied := MStore.apply_inferWF rhsSafe.1.solutionsLeveled
                      rhsSafe.1.solutionsBounded rhsSafe.2.1 rhsSafe.2.2.1
                    have bodyCtxWF : Ctx.InferWF (PolyTy.mono rhsTy :: ctx)
                        rigidCount rhsResult.state.next := by
                      intro scheme member
                      simp only [List.mem_cons] at member
                      rcases member with rfl | member
                      · exact rhsApplied.1
                      · exact ctx_mono ctxWF rhsSafe.2.2.2.1 scheme member
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
                    cases bodyRun : inferFuel sig fuel rigidCount
                        (PolyTy.mono rhsTy :: ctx) body rhsResult.state with
                    | none => simp [rhsTy, rhsRun, bodyRun] at run
                    | some bodyResult =>
                        have bodyTyping' : Typing sig rigidCount
                            (Ctx.realize (PolyTy.mono rhsTy :: ctx) ext1)
                            body ty := by
                          have ctxEq : Ctx.realize (PolyTy.mono rhsTy :: ctx) ext1 =
                              PolyTy.mono rhsTyD :: Ctx.realize ctx valuation := by
                            change PolyTy.mono (rhsTy.realize ext1) ::
                                Ctx.realize ctx ext1 =
                              PolyTy.mono rhsTyD :: Ctx.realize ctx valuation
                            rw [show rhsTy.realize ext1 =
                                rhsResult.ty.realize ext1 by
                              simpa [rhsTy] using rhsModels.realize_apply rhsResult.ty,
                              rhsTyEq]
                            congr 1
                            exact Ctx.realize_congr (fun scheme member id hid =>
                              rhsAgree id ((ctxWF scheme member).2 id hid))
                          rwa [ctxEq]
                        obtain ⟨ext2, bodyModels, bodyAgree, bodyTyEq⟩ :=
                          ih (result := bodyResult) rhsSafe.1 bodyCtxWF
                            bodyCtxLevels bodyScoped bodyRun rhsModels bodyTyping'
                        have resultEq : result =
                            ⟨bodyResult.state, bodyResult.ty,
                              .letIn none rhsResult.elaborated
                                bodyResult.elaborated⟩ := by
                          simpa [rhsTy, rhsRun, bodyRun] using run.symm
                        subst result
                        refine ⟨ext2, bodyModels, ?_, bodyTyEq⟩
                        intro id hid
                        exact (bodyAgree id (lt_of_lt_of_le hid
                          rhsSafe.2.2.2.1)).trans (rhsAgree id hid)
          | some written =>
            cases inputScoped with
            | letPoly writtenScoped rhsScoped bodyScoped =>
              cases typing with
              | letPoly schemeMatches schemeWF ctxWFD rhsScopedD rhsTyping bodyTyping =>
                  rename_i scheme
                  simp only [inferFuel] at run
                  let localStart := state.next
                  let count := written.paramCount
                  let inner := rigidCount + count
                  let openedTemplate :=
                    written.body.openRigidsFrom 0 rigidCount count
                  have openedTemplateScoped : openedTemplate.Scoped inner 0 := by
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
                  have countEq : scheme.paramCount = count :=
                    schemeMatches.paramCount_eq
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
                      have rhsTyping' : Typing sig inner (ctx.realize firstValuation)
                          (rhs.openRigids rigidCount count)
                          (scheme.openRigids rigidCount) := by
                        have ctxEq : Ctx.realize ctx firstValuation =
                            Ctx.realize ctx valuation :=
                          Ctx.realize_congr (fun scheme member id idMem =>
                            seedAgree id ((ctxWF scheme member).2 id idMem))
                        have base := rhsTyping
                        rw [countEq] at base
                        simpa [ctxEq] using base
                      obtain ⟨ext1, rhsModels, rhsAgree, rhsTyEq⟩ :=
                        ih (result := rhsResult) seededSafe.1 rhsCtxWF rhsCtxLevels
                          openedRhsScoped rhsRun seedModels rhsTyping'
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
                            rw [show completedOpen =
                              checked.solutions.apply seeded.2 from rfl,
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
                          have completedEq : completed.realize ext1 = scheme := by
                            rw [completedRealize, completedOpenRealize]
                            cases scheme with
                            | mk schemeCount schemeBody =>
                                have countEq' : count = schemeCount :=
                                  schemeMatches.paramCount_eq.symm
                                have scopedCount : schemeBody.Scoped rigidCount count := by
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
                              have bodyTyping' : Typing sig rigidCount
                                  (Ctx.realize (completed :: ctx) ext1)
                                  body ty := by
                                have ctxEq : Ctx.realize (completed :: ctx) ext1 =
                                    scheme :: Ctx.realize ctx valuation := by
                                  change completed.realize ext1 :: Ctx.realize ctx ext1 =
                                    scheme :: Ctx.realize ctx valuation
                                  rw [completedEq]
                                  congr 1
                                  exact (Ctx.realize_congr (fun s m id hid =>
                                    rhsAgree id (lt_of_lt_of_le
                                      ((ctxWF s m).2 id hid) seededSafe.2.2.2.1))).trans
                                    (Ctx.realize_congr (fun s m id hid =>
                                      seedAgree id ((ctxWF s m).2 id hid)))
                                rwa [ctxEq]
                              obtain ⟨ext2, bodyModels, bodyAgree, bodyTyEq⟩ :=
                                ih (result := bodyResult) checkedSafe.1
                                  bodyCtxWF bodyCtxLevels bodyScoped bodyRun
                                  checkedModels bodyTyping'
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
                              refine ⟨ext2, bodyModels, ?_, bodyTyEq⟩
                              intro id hid
                              have idSeeded : id < seeded.1.next :=
                                lt_of_lt_of_le hid seededSafe.2.2.2.1
                              have idChecked : id < checked.next := by
                                rw [checkedSafe.2.1]
                                exact lt_of_lt_of_le idSeeded rhsSafe.2.2.2.1
                              exact (bodyAgree id idChecked).trans
                                ((rhsAgree id idSeeded).trans (seedAgree id hid))
      | fix ann body =>
          cases inputScoped with
          | fix annScoped bodyScoped =>
            cases typing with
            | fix selfWF annMatches bodyTyping =>
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
                    have idBound : id < state.next :=
                      (ctxWF scheme member).2 id hid
                    rw [seededSafe.2.2.2.2 id idBound]
                    exact ctxLevels scheme member id hid
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
                          .fix seeded.2 bodyResult.elaborated⟩) =
                          some result at run
                    have bodySafe := inferFuel_safe seededSafe.1 bodyCtxWF
                      bodyCtxLevels bodyScoped bodyRun
                    have selfWFAtBody : seeded.2.InferWF rigidCount 0
                        bodyResult.state.next :=
                      Ty.InferWF.mono_frontier seededSafe.2.1 bodySafe.2.2.2.1
                    cases checkedRun : bodyResult.state.constrain
                        bodyResult.ty seeded.2 with
                    | none =>
                        rw [checkedRun] at run
                        simp at run
                    | some checked =>
                        have checkedSafe := InferState.constrain_safe bodySafe.1
                          bodySafe.2.1 selfWFAtBody checkedRun
                        obtain ⟨holeVal, holeAgree, holeRealize, holeWF⟩ :=
                          Template.allocate_realizes
                            (template := ann) (rigid := rigidCount) (binder := 0)
                            (frontier := state.next) (target := ty)
                            (base := valuation) annMatches annScoped selfWF
                        obtain ⟨firstValuation, seedModels, seedAgree,
                          seedRealizeEq⟩ :=
                          InferState.allocate_models stateSafe models annScoped
                            (assigned := holeVal) holeWF
                        have seedRealize : seeded.2.realize firstValuation = ty := by
                          simpa [seeded] using seedRealizeEq.trans holeRealize
                        have bodyTyping' : Typing sig rigidCount
                            (Ctx.realize (PolyTy.mono seeded.2 :: ctx) firstValuation)
                            body ty := by
                          have ctxEq : Ctx.realize (PolyTy.mono seeded.2 :: ctx)
                              firstValuation =
                              PolyTy.mono ty :: Ctx.realize ctx valuation := by
                            change PolyTy.mono (seeded.2.realize firstValuation) ::
                                Ctx.realize ctx firstValuation =
                              PolyTy.mono ty :: Ctx.realize ctx valuation
                            rw [seedRealize]
                            congr 1
                            exact Ctx.realize_congr (fun scheme member id hid =>
                              seedAgree id ((ctxWF scheme member).2 id hid))
                          rwa [ctxEq]
                        obtain ⟨ext1, bodyModels, bodyAgree, bodyTyEq⟩ :=
                          ih (result := bodyResult) seededSafe.1 bodyCtxWF
                            bodyCtxLevels bodyScoped bodyRun seedModels bodyTyping'
                        have seededExt : seeded.2.realize ext1 = ty := by
                          rw [show seeded.2.realize ext1 =
                              seeded.2.realize firstValuation by
                            apply Ty.realize_congr
                            intro id member
                            exact bodyAgree id
                              (Template.allocate_mvars annScoped
                                (frontier := state.next) id
                                (by simpa [seeded] using member)).2]
                          exact seedRealize
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
                        rw [checkedRun] at run
                        simp only [Option.bind_some, Option.some.injEq] at run
                        subst result
                        refine ⟨ext1, checkedModels, ?_, ?_⟩
                        · intro id hid
                          have idSeeded : id < seeded.1.next :=
                            lt_of_lt_of_le hid seededSafe.2.2.2.1
                          exact (bodyAgree id idSeeded).trans (seedAgree id hid)
                        · change (checked.solutions.apply seeded.2).realize ext1 = ty
                          rw [checkedModels.realize_apply seeded.2]
                          exact seededExt


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
    (run : inferFuel sig fuel rigidCount ctx input state = some result) :
    state.Refines result.state ∧
      ∀ valuation, result.state.Models valuation →
        Elaborates sig rigidCount (ctx.realize valuation) input
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
    | con id => exact .con id
    | app _ _ ihFunction ihArgument => exact .app ihFunction ihArgument
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
    | con => simp [Ty.MVarBounded, Ty.mvars]
    | app _ _ ihFunction ihArgument =>
        intro id member
        simp only [Ty.mvars, List.mem_dedup, List.mem_append] at member
        exact member.elim (ihFunction id) (ihArgument id)
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
          cases hty : op.ty sig with
          | none => simp [inferFuel, hty] at run
          | some primTy =>
              simp [inferFuel, hty] at run
              subst result
              refine ⟨MStore.Refines.refl _, ?_⟩
              intro valuation models
              rw [Ty.realize_eq_self (primOpTy_metaFree hty) valuation]
              exact Elaborates.primOp hty
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
      | const c =>
          simp only [inferFuel] at run
          cases lookup : sig.schemeOf c with
          | none => simp [lookup] at run
          | some scheme =>
              simp only [lookup] at run
              cases hb : scheme.wfB 0 with
              | false => simp [hb] at run
              | true =>
                  have schemeWF0 : scheme.WF 0 := Ty.wfB_eq_true_iff.mp hb
                  let fresh := state.freshMany rigidCount scheme.paramCount
                  have resultEq : result =
                      ⟨fresh.1, scheme.openWith fresh.2, .const c⟩ := by
                    simpa [fresh, hb] using run.symm
                  subst result
                  have freshSafe := InferState.freshMany_safe
                    (level := rigidCount) (count := scheme.paramCount) stateSafe
                  refine ⟨InferState.freshMany_refines, ?_⟩
                  intro valuation models
                  have argsWF : ∀ arg ∈ fresh.2,
                      (arg.realize valuation).WF rigidCount 0 := by
                    intro arg member
                    exact Ty.realize_inferWF_model models
                      freshSafe.1.solutions_length
                      (freshSafe.2.1 arg member) (freshSafe.2.2.1 arg member)
                  have imagesScoped : ∀ id ∈ scheme.body.mvars,
                      (valuation id).Scoped rigidCount 0 := by
                    intro id member
                    rw [Ty.MetaFree.mvars_eq_nil schemeWF0.2] at member
                    exact absurd member (List.not_mem_nil)
                  have opened := Ty.realize_openWith (ty := scheme.body)
                    (args := fresh.2) (valuation := valuation) imagesScoped
                  have bodyRealize : scheme.body.realize valuation = scheme.body :=
                    Ty.realize_eq_self schemeWF0.2 valuation
                  have resultTyEq :
                      (scheme.openWith fresh.2).realize valuation =
                        scheme.openWith (fresh.2.map (·.realize valuation)) := by
                    simpa [PolyTy.openWith, bodyRealize] using opened
                  rw [resultTyEq]
                  exact Elaborates.const lookup schemeWF0
                    (by simpa using freshSafe.2.2.2.1)
                    (by
                      intro arg member
                      rcases List.mem_map.mp member with ⟨original, hmem, rfl⟩
                      exact argsWF original hmem)
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
                    change Elaborates sig rigidCount (ctx.realize valuation)
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
                cases bodyRun : inferFuel sig fuel rigidCount
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
                    change Elaborates sig rigidCount (ctx.realize valuation)
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
            cases functionRun : inferFuel sig fuel rigidCount ctx function state with
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
              cases argumentRun : inferFuel sig fuel rigidCount ctx argument
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
              cases rhsRun : inferFuel sig fuel rigidCount ctx rhs state with
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
                cases bodyRun : inferFuel sig fuel rigidCount
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
              cases rhsRun : inferFuel sig fuel inner ctx
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
                      cases bodyRun : inferFuel sig fuel rigidCount
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
                          change Elaborates sig rigidCount
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
                          · by_cases countZero : completed.paramCount = 0
                            · exact Or.inl countZero
                            · right
                              intro other otherMatches otherWF otherTyping
                              have countPositive : 0 < count := by
                                have countEqCompleted : completed.paramCount = count := rfl
                                omega
                              have otherParam : other.paramCount = count :=
                                otherMatches.paramCount_eq
                              have otherTargetEq : other.openRigids rigidCount =
                                  other.body.openRigidsFrom 0 rigidCount count := by
                                simpa [otherParam] using
                                  PolyTy.openRigids_eq_openRigidsFrom otherWF
                              have otherTargetWF : (other.openRigids rigidCount).WF
                                  inner 0 := by
                                rw [otherTargetEq]
                                have bodyWF : other.body.WF rigidCount count := by
                                  simpa [PolyTy.WF, otherParam] using otherWF
                                simpa [inner, Nat.zero_add] using
                                  (Ty.openRigidsFrom_wf (ty := other.body)
                                    (rigidCount := rigidCount) (depth := 0)
                                    (count := count)
                                    (by simpa [Nat.zero_add] using bodyWF))
                              have hmatchesOther : openedTemplate.Matches
                                  (other.openRigids rigidCount) := by
                                rw [otherTargetEq]
                                simpa [openedTemplate] using
                                  (otherMatches.body_matches.openRigidsFrom
                                    0 rigidCount count)
                              obtain ⟨holeVal, holeAgree, holeRealize, holeWF⟩ :=
                                Template.allocate_realizes
                                  (template := openedTemplate) (rigid := inner)
                                  (binder := 0) (frontier := state.next)
                                  (target := other.openRigids rigidCount)
                                  (base := valuation) hmatchesOther
                                  openedTemplateScoped otherTargetWF
                              have seededModels : seeded.1.Models valuation :=
                                rhsSound.1 valuation rhsModels
                              have stateModels : state.Models valuation :=
                                InferState.allocate_refines valuation seededModels
                              obtain ⟨seedValuation, seedModels, seedAgree,
                                seedRealizeEq⟩ :=
                                InferState.allocate_models stateSafe stateModels
                                  openedTemplateScoped (assigned := holeVal) holeWF
                              have seedRealizeOther :
                                  seeded.2.realize seedValuation =
                                    other.openRigids rigidCount := by
                                simpa [seeded] using seedRealizeEq.trans holeRealize
                              have otherTyping' : Typing sig inner
                                  (ctx.realize seedValuation)
                                  (rhs.openRigids rigidCount count)
                                  (other.openRigids rigidCount) := by
                                have ctxEq : Ctx.realize ctx seedValuation =
                                    Ctx.realize ctx valuation :=
                                  Ctx.realize_congr (fun scheme member id hid =>
                                    seedAgree id ((ctxWF scheme member).2 id hid))
                                simpa [ctxEq, inner, otherParam] using otherTyping
                              obtain ⟨ext, rhsModelsExt, extAgree, extTy⟩ :=
                                inferFuel_principal seededSafe.1 rhsCtxWF
                                  rhsCtxLevels openedRhsScoped rhsRun seedModels
                                  otherTyping'
                              have seededExt : seeded.2.realize ext =
                                  other.openRigids rigidCount := by
                                rw [show seeded.2.realize ext =
                                    seeded.2.realize seedValuation by
                                  apply Ty.realize_congr
                                  intro id member
                                  exact extAgree id
                                    (Template.allocate_mvars openedTemplateScoped
                                      (frontier := state.next) id
                                      (by simpa [seeded] using member)).2]
                                exact seedRealizeOther
                              have unifiesExt : rhsResult.ty.realize ext =
                                  seeded.2.realize ext :=
                                extTy.trans seededExt.symm
                              obtain ⟨unified, unifiedRun, unifiedModels⟩ :=
                                MStore.unify_complete
                                  (store := rhsResult.state.solutions)
                                  (left := rhsResult.ty) (right := seeded.2)
                                  (valuation := ext)
                                  rhsSafe.1.solutionsNormalized
                                  (by simpa [rhsSafe.1.solutions_length] using
                                    rhsSafe.1.solutionsBounded)
                                  (by simpa [rhsSafe.1.solutions_length] using
                                    rhsSafe.2.1.2)
                                  (by simpa [rhsSafe.1.solutions_length] using
                                    seededTyAtRhs.2)
                                  rhsModelsExt unifiesExt
                              have checkedUnify : checked.solutions = unified := by
                                have hs := InferState.constrain_solutions checkedRun
                                rw [unifiedRun] at hs
                                exact (Option.some.inj hs).symm
                              have checkedModelsExt : checked.Models ext := by
                                change checked.solutions.Models ext
                                rw [checkedUnify]
                                exact unifiedModels
                              have stateAnchored : state.solutions.Anchored
                                  localStart rigidCount := by
                                intro id hstart hid hlevel hlookup
                                have idBound : id < state.next := by
                                  simpa [localStart, stateSafe.solutions_length]
                                    using hid
                                omega
                              have seededAnchored : seeded.1.solutions.Anchored
                                  localStart rigidCount := by
                                have appended : seeded.1.solutions =
                                    state.solutions ++ List.replicate
                                      ((openedTemplate.allocate state.next).next -
                                        state.next)
                                      (⟨inner, none⟩ : MEntry) := by
                                  simp [seeded, InferState.allocate]
                                rw [appended]
                                exact MStore.Anchored.append_replicate stateAnchored
                                  (by omega)
                              have rhsAnchored : rhsResult.state.solutions.Anchored
                                  localStart rigidCount :=
                                inferFuel_anchored seededSafe.1 rhsCtxWF
                                  rhsCtxLevels openedRhsScoped (by omega)
                                  (by simpa [localStart] using seededSafe.2.2.2.1)
                                  seededAnchored rhsRun
                              have checkedAnchored : checked.solutions.Anchored
                                  localStart rigidCount :=
                                MStore.unify_anchored
                                  (store := rhsResult.state.solutions)
                                  (result := checked.solutions)
                                  rhsSafe.1.solutionsNormalized rhsAnchored
                                  (InferState.constrain_solutions checkedRun)
                              have agreeBelow : ∀ id, id < localStart →
                                  ext id = valuation id := by
                                intro id hid
                                have hidSeeded : id < seeded.1.next :=
                                  lt_of_lt_of_le hid
                                    (by simpa [localStart] using seededSafe.2.2.2.1)
                                exact (extAgree id hidSeeded).trans (seedAgree id hid)
                              have completedOpenRealizeEq :
                                  completedOpen.realize ext =
                                    completedOpen.realize valuation := by
                                apply Ty.realize_congr
                                intro id member
                                have idLevel : checked.solutions.levelOf id ≤
                                    rigidCount := completedOpenLevelsRigid id member
                                have idBound : id < checked.solutions.length := by
                                  have h := completedOpenWF.2 id member
                                  simpa [checkedSafe.1.solutions_length] using h
                                exact MStore.Anchored.agree
                                  checkedSafe.1.solutionsLeveled
                                  checkedSafe.1.solutionsNormalized
                                  (by simpa [checkedSafe.1.solutions_length] using
                                    checkedSafe.1.solutionsBounded)
                                  checkedAnchored checkedModelsExt checkedModels
                                  agreeBelow id idBound idLevel
                              have completedOpenExt : completedOpen.realize ext =
                                  other.openRigids rigidCount := by
                                rw [show completedOpen =
                                  checked.solutions.apply seeded.2 from rfl,
                                  checkedModelsExt.realize_apply seeded.2]
                                exact seededExt
                              have completedOpenVal : completedOpen.realize valuation =
                                  other.openRigids rigidCount := by
                                rw [← completedOpenRealizeEq, completedOpenExt]
                              have openEqOther : (completed.realize valuation).openRigids
                                  rigidCount = other.openRigids rigidCount := by
                                rw [openEq, completedOpenVal]
                              have otherClose : (other.openRigids rigidCount).closeRigids
                                  rigidCount count = other.body := by
                                rw [otherTargetEq]
                                have scopedBody : other.body.Scoped rigidCount count := by
                                  simpa [PolyTy.WF, otherParam] using otherWF.1
                                exact Ty.closeRigids_openRigids scopedBody
                              have completedClose :
                                  ((completed.realize valuation).openRigids
                                    rigidCount).closeRigids rigidCount count =
                                      (completed.realize valuation).body := by
                                rw [openEq]
                                rw [completedRealize]
                              have bodyEq : (completed.realize valuation).body =
                                  other.body := by
                                have h := congrArg
                                  (fun candidate => candidate.closeRigids rigidCount count)
                                  openEqOther
                                simpa [completedClose, otherClose] using h
                              have paramEq : (completed.realize valuation).paramCount =
                                  other.paramCount := by
                                rw [completedRealize]
                                simp [otherParam]
                              cases hcompleted : completed.realize valuation with
                              | mk completedCount completedBody =>
                                cases hother : other with
                                | mk otherCount otherBody =>
                                    simp only [Scheme.mk.injEq]
                                    constructor
                                    · simpa [hcompleted, hother] using paramEq.symm
                                    · simpa [hcompleted, hother] using bodyEq.symm
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
                    have realizedBody : Elaborates sig rigidCount
                        (PolyTy.mono (seeded.2.realize valuation) ::
                          ctx.realize valuation) body
                        (bodyResult.elaborated.realize valuation)
                        (seeded.2.realize valuation) := by
                      simpa [Ctx.realize, PolyTy.realize, PolyTy.mono] using
                        bodyTyping
                    change Elaborates sig rigidCount (ctx.realize valuation)
                      (.fix ann body)
                      ((Expr.fix seeded.2 bodyResult.elaborated).realize valuation)
                      ((checked.solutions.apply seeded.2).realize valuation)
                    rw [models.realize_apply seeded.2]
                    exact Elaborates.fix selfSemanticWF annMatches realizedBody

/-- Every successful public inference result belongs to the declarative source
typing relation. -/
theorem infer_sound
    {input : Source} {result : InferenceResult}
    (run : infer sig input = some result) :
    Elaborates sig 0 [] input result.elaborated result.ty := by
  unfold infer at run
  by_cases sourceBad : (!input.typeScopedB 0 0) = true
  · rw [if_pos sourceBad] at run
    simp at run
  · rw [if_neg sourceBad] at run
    cases internalRun : inferFuel sig (input.inferSize + 1) 0 [] input
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
    (run : infer sig input = some result) :
    Typing sig 0 [] input result.ty :=
  (infer_sound run).typing

/-- Convenience form for tests: a reported type is a declarative type. -/
theorem infer_typing_of_ty
    {input : Source} {ty : Ty}
    (run : (infer sig input).map (·.ty) = some ty) :
    Typing sig 0 [] input ty := by
  cases h : infer sig input with
  | none => simp [h] at run
  | some result =>
      simp only [h, Option.map_some, Option.some.injEq] at run
      exact run ▸ infer_typing h

/-- The public result contains a closed semantic type; in particular it has no
remaining inference metavariables. -/
theorem infer_result_wf
    {input : Source} {result : InferenceResult}
    (run : infer sig input = some result) :
    result.ty.WF 0 0 := by
  exact Typing.regular (infer_sound run).typing

end EPL
