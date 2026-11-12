import EPL.Inference
import EPL.Properties.Unification

namespace EPL

private theorem namedHoleTable_unique (names : List String) (frontier : Nat) :
    (namedHoleTable names frontier).Unique := by
  simp only [HoleAssignment.Unique, namedHoleTable]
  rw [List.map_fst_zip]
  · exact List.nodup_dedup _
  · simp

private theorem lookup_of_mem_key {holes : HoleAssignment} {name : String}
    (hmem : name ∈ holes.map Prod.fst) :
    ∃ ty, holes.lookup name = some ty := by
  induction holes with
  | nil => simp at hmem
  | cons entry rest ih =>
      rcases entry with ⟨key, ty⟩
      simp only [List.map_cons, List.mem_cons] at hmem
      by_cases hkey : name = key
      · subst key
        exact ⟨ty, by simp [List.lookup]⟩
      · obtain ⟨result, hlookup⟩ := ih (hmem.resolve_left hkey)
        have hbeq : (name == key) = false := beq_false_of_ne hkey
        exact ⟨result, by simpa [List.lookup, hbeq] using hlookup⟩

private theorem namedHoleTable_covers {names : List String} {frontier : Nat}
    {name : String} (hmem : name ∈ names) :
    ∃ ty, (namedHoleTable names frontier).lookup name = some ty := by
  apply lookup_of_mem_key
  simp only [namedHoleTable]
  rw [List.map_fst_zip]
  · exact List.mem_dedup.mpr hmem
  · simp

private theorem allocateWith_fits (template : Template) (holes : HoleAssignment)
    (frontier : Nat)
    (hcover : ∀ name ∈ template.names, ∃ ty, holes.lookup name = some ty) :
    template.Fits holes (template.allocateWith holes frontier).2 := by
  induction template generalizing frontier with
  | fixed ty => exact .fixed
  | hole => exact .hole
  | named name =>
      obtain ⟨ty, hlookup⟩ := hcover name (by simp [Template.names])
      simp only [Template.allocateWith, hlookup, Option.getD_some]
      exact .named hlookup
  | arrow domain codomain ihDomain ihCodomain =>
      exact .arrow
        (ihDomain frontier fun name hmem =>
          hcover name (List.mem_append_left _ hmem))
        (ihCodomain (domain.allocateWith holes frontier).1 fun name hmem =>
          hcover name (List.mem_append_right _ hmem))

private theorem lookup_scoped {holes : HoleAssignment} {name : String} {ty : Ty}
    {rigidCount binderCount : Nat}
    (hall : ∀ entry ∈ holes, entry.2.Scoped rigidCount binderCount)
    (hlookup : holes.lookup name = some ty) :
    ty.Scoped rigidCount binderCount := by
  induction holes with
  | nil => simp [List.lookup] at hlookup
  | cons entry rest ih =>
      rcases entry with ⟨key, value⟩
      by_cases hkey : name = key
      · subst key
        simp [List.lookup] at hlookup
        subst ty
        exact hall (name, value) (by simp)
      · apply ih
        · intro entry hmem
          exact hall entry (List.mem_cons_of_mem _ hmem)
        · have hbeq : (name == key) = false := beq_false_of_ne hkey
          simpa [List.lookup, hbeq] using hlookup

private theorem zip_second_scoped {keys : List String} {types : List Ty}
    {entry : String × Ty} {rigidCount binderCount : Nat}
    (hall : ∀ ty ∈ types, ty.Scoped rigidCount binderCount)
    (hmem : entry ∈ keys.zip types) :
    entry.2.Scoped rigidCount binderCount := by
  induction keys generalizing types with
  | nil => simp at hmem
  | cons key keys ih =>
      cases types with
      | nil => simp at hmem
      | cons ty types =>
          simp only [List.zip_cons_cons, List.mem_cons] at hmem
          rcases hmem with rfl | hmem
          · exact hall ty (by simp)
          · exact ih (fun result hresult => hall result (by simp [hresult])) hmem

private theorem namedHoleTable_scoped (names : List String) (frontier : Nat)
    (rigidCount binderCount : Nat) :
    ∀ entry ∈ namedHoleTable names frontier,
      entry.2.Scoped rigidCount binderCount := by
  intro entry hmem
  apply zip_second_scoped (hmem := hmem)
  intro ty hty
  obtain ⟨offset, _, rfl⟩ := List.mem_map.mp hty
  exact .mvar _

private theorem allocateWith_scoped {template : Template} {holes : HoleAssignment}
    {rigidCount binderCount frontier : Nat}
    (hscoped : template.Scoped rigidCount binderCount)
    (hholes : ∀ entry ∈ holes, entry.2.Scoped rigidCount binderCount) :
    (template.allocateWith holes frontier).2.Scoped rigidCount binderCount := by
  induction hscoped generalizing frontier with
  | fixed hwf => exact hwf.1
  | hole => exact .mvar _
  | named =>
      simp only [Template.allocateWith]
      cases hlookup : holes.lookup _ with
      | none =>
          simp only [Option.getD_none]
          exact .mvar _
      | some ty =>
          simp only [Option.getD_some]
          exact lookup_scoped hholes hlookup
  | arrow _ _ ihDomain ihCodomain =>
      exact .arrow ihDomain ihCodomain

/-- The allocator's local named-hole table has no duplicate keys. -/
theorem Template.allocate_unique (template : Template) (frontier : Nat) :
    (template.allocate frontier).holes.Unique := by
  exact namedHoleTable_unique template.names.dedup frontier

/-- The allocated type is a declarative fit of the original template using
exactly the allocator's annotation-local named table. -/
theorem Template.allocate_fits (template : Template) (frontier : Nat) :
    template.Fits (template.allocate frontier).holes
      (template.allocate frontier).ty := by
  apply allocateWith_fits
  intro name hmem
  exact namedHoleTable_covers (List.mem_dedup.mpr hmem)

/-- Allocation preserves authored rigid/bound scope and introduces only
flexible metavariables. -/
theorem Template.allocate_scoped
    {template : Template} {rigidCount binderCount frontier : Nat}
    (hscoped : template.Scoped rigidCount binderCount) :
    (template.allocate frontier).ty.Scoped rigidCount binderCount := by
  apply allocateWith_scoped hscoped
  exact namedHoleTable_scoped template.names.dedup frontier rigidCount binderCount

end EPL

namespace EPL

/-- The executable scope test for algorithmic types recognizes precisely the
inductive scope judgment. Metavariables are deliberately permitted here. -/
theorem Ty.scopedB_eq_true_iff {ty : Ty} {rigidCount binderCount : Nat} :
    ty.scopedB rigidCount binderCount = true ↔
      ty.Scoped rigidCount binderCount := by
  induction ty with
  | prim name =>
      constructor
      · intro _
        exact .prim
      · intro _
        rfl
  | arrow domain codomain ihDomain ihCodomain =>
      simp only [Ty.scopedB, Bool.and_eq_true]
      constructor
      · rintro ⟨hDomain, hCodomain⟩
        exact .arrow (ihDomain.mp hDomain) (ihCodomain.mp hCodomain)
      · intro h
        cases h with
        | arrow hDomain hCodomain =>
            exact ⟨ihDomain.mpr hDomain, ihCodomain.mpr hCodomain⟩
  | bvar index =>
      simp only [Ty.scopedB]
      constructor
      · intro h
        exact .bvar (by simpa using h)
      · intro h
        cases h with
        | bvar hlt => simpa using hlt
  | rigid level =>
      simp only [Ty.scopedB]
      constructor
      · intro h
        exact .rigid (by simpa using h)
      · intro h
        cases h with
        | rigid hlt => simpa using hlt
  | mvar id =>
      constructor
      · intro _
        exact .mvar id
      · intro _
        rfl

/-- The executable metavariable-freedom test recognizes precisely semantic
types. -/
theorem Ty.metaFreeB_eq_true_iff {ty : Ty} :
    ty.metaFreeB = true ↔ ty.MetaFree := by
  induction ty with
  | prim name =>
      constructor
      · intro _
        exact .prim
      · intro _
        rfl
  | arrow domain codomain ihDomain ihCodomain =>
      simp only [Ty.metaFreeB, Bool.and_eq_true]
      constructor
      · rintro ⟨hDomain, hCodomain⟩
        exact .arrow (ihDomain.mp hDomain) (ihCodomain.mp hCodomain)
      · intro h
        cases h with
        | arrow hDomain hCodomain =>
            exact ⟨ihDomain.mpr hDomain, ihCodomain.mpr hCodomain⟩
  | bvar index =>
      constructor
      · intro _
        exact .bvar
      · intro _
        rfl
  | rigid level =>
      constructor
      · intro _
        exact .rigid
      · intro _
        rfl
  | mvar id =>
      constructor
      · intro h
        contradiction
      · intro h
        cases h

/-- Executable type well-formedness agrees with declarative well-formedness. -/
theorem Ty.wfB_eq_true_iff {ty : Ty} {rigidCount binderCount : Nat} :
    ty.wfB rigidCount binderCount = true ↔
      ty.WF rigidCount binderCount := by
  simp only [Ty.wfB, Bool.and_eq_true, Ty.WF]
  exact and_congr Ty.scopedB_eq_true_iff Ty.metaFreeB_eq_true_iff

/-- Executable template validation agrees with the source-language scope
judgment, including the exclusion of authored inference metavariables. -/
theorem Template.scopedB_eq_true_iff {template : Template}
    {rigidCount binderCount : Nat} :
    template.scopedB rigidCount binderCount = true ↔
      template.Scoped rigidCount binderCount := by
  induction template with
  | fixed ty =>
      simp only [Template.scopedB]
      constructor
      · intro h
        exact .fixed (Ty.wfB_eq_true_iff.mp h)
      · intro h
        cases h with
        | fixed hwf => exact Ty.wfB_eq_true_iff.mpr hwf
  | hole =>
      constructor
      · intro _
        exact .hole
      · intro _
        rfl
  | named name =>
      constructor
      · intro _
        exact .named
      · intro _
        rfl
  | arrow domain codomain ihDomain ihCodomain =>
      simp only [Template.scopedB, Bool.and_eq_true]
      constructor
      · rintro ⟨hDomain, hCodomain⟩
        exact .arrow (ihDomain.mp hDomain) (ihCodomain.mp hCodomain)
      · intro h
        cases h with
        | arrow hDomain hCodomain =>
            exact ⟨ihDomain.mpr hDomain, ihCodomain.mpr hCodomain⟩

/-- The public inference guard accepts exactly the declaratively scoped source
language. -/
theorem Expr.typeScopedB_eq_true_iff {input : Source}
    {rigidCount binderCount : Nat} :
    input.typeScopedB rigidCount binderCount = true ↔
      input.TypeScoped rigidCount binderCount := by
  induction input generalizing binderCount with
  | primLit literal =>
      constructor
      · intro _
        exact .primLit
      · intro _
        rfl
  | primOp op =>
      constructor
      · intro _
        exact .primOp
      · intro _
        rfl
  | var index =>
      constructor
      · intro _
        exact .var
      · intro _
        rfl
  | lambda ann body ihBody =>
      cases ann with
      | none =>
          simp only [Expr.typeScopedB, Option.all_none, Bool.true_and]
          constructor
          · intro hBody
            exact .lambda (by simp) (ihBody.mp hBody)
          · intro h
            cases h with
            | lambda _ hBody => exact ihBody.mpr hBody
      | some template =>
          simp only [Expr.typeScopedB, Option.all_some, Bool.and_eq_true]
          constructor
          · rintro ⟨hTemplate, hBody⟩
            exact .lambda
              (by
                intro candidate heq
                cases heq
                exact Template.scopedB_eq_true_iff.mp hTemplate)
              (ihBody.mp hBody)
          · intro h
            cases h with
            | lambda hTemplate hBody =>
                exact ⟨Template.scopedB_eq_true_iff.mpr
                  (hTemplate template rfl), ihBody.mpr hBody⟩
  | app function argument ihFunction ihArgument =>
      simp only [Expr.typeScopedB, Bool.and_eq_true]
      constructor
      · rintro ⟨hFunction, hArgument⟩
        exact .app (ihFunction.mp hFunction) (ihArgument.mp hArgument)
      · intro h
        cases h with
        | app hFunction hArgument =>
            exact ⟨ihFunction.mpr hFunction, ihArgument.mpr hArgument⟩
  | letIn ann rhs body ihRhs ihBody =>
      cases ann with
      | none =>
          simp only [Expr.typeScopedB, Bool.and_eq_true]
          constructor
          · rintro ⟨hRhs, hBody⟩
            exact .letMono (ihRhs.mp hRhs) (ihBody.mp hBody)
          · intro h
            cases h with
            | letMono hRhs hBody =>
                exact ⟨ihRhs.mpr hRhs, ihBody.mpr hBody⟩
      | some written =>
          simp only [Expr.typeScopedB, Bool.and_eq_true]
          constructor
          · rintro ⟨⟨hWritten, hRhs⟩, hBody⟩
            exact .letPoly
              (Template.scopedB_eq_true_iff.mp hWritten)
              (ihRhs.mp hRhs)
              (ihBody.mp hBody)
          · intro h
            cases h with
            | letPoly hWritten hRhs hBody =>
                exact ⟨⟨Template.scopedB_eq_true_iff.mpr hWritten,
                  ihRhs.mpr hRhs⟩, ihBody.mpr hBody⟩
  | fix ann body ihBody =>
      simp only [Expr.typeScopedB, Bool.and_eq_true]
      constructor
      · rintro ⟨hAnn, hBody⟩
        exact .fix (Template.scopedB_eq_true_iff.mp hAnn) (ihBody.mp hBody)
      · intro h
        cases h with
        | fix hAnn hBody =>
            exact ⟨Template.scopedB_eq_true_iff.mpr hAnn, ihBody.mpr hBody⟩

/-- The executable frontier check recognizes precisely the metavariables below
the stated allocation frontier. -/
theorem Ty.mvarsBelow_eq_true_iff {ty : Ty} {cutoff : Nat} :
    ty.mvarsBelow cutoff = true ↔
      ∀ id ∈ ty.mvars, id < cutoff := by
  simp [Ty.mvarsBelow]

/-- The explicit-scheme escape check says exactly that every retained image is
outer-scoped and mentions only outer metavariables. -/
theorem MStore.safeToLeave_eq_true_iff
    {store : MStore} {rigidCount : Nat} :
    store.safeToLeave rigidCount = true ↔
      ∀ ty, some ty ∈ store → ty.Scoped rigidCount 0 := by
  constructor
  · intro h ty hmem
    rw [MStore.safeToLeave, List.all_eq_true] at h
    have hentry := h (some ty) hmem
    rw [Option.all_eq_true] at hentry
    exact Ty.scopedB_eq_true_iff.mp (hentry ty rfl)
  · intro h
    rw [MStore.safeToLeave, List.all_eq_true]
    intro entry hentry
    rw [Option.all_eq_true]
    intro ty hentryEq
    have hmem : some ty ∈ store := by simpa [hentryEq] using hentry
    exact Ty.scopedB_eq_true_iff.mpr (h ty hmem)


end EPL

namespace EPL

theorem Ty.mvarBounded_iff_mvarsBelow
    {ty : Ty} {frontier : Nat} :
    ty.MVarBounded frontier ↔ ty.mvarsBelow frontier = true := by
  exact Ty.mvarsBelow_eq_true_iff.symm

end EPL

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

/-- The dense solution table agrees with its allocation frontier and contains
no out-of-scope, forged, or unnormalized solution. -/
structure InferState.Safe (state : InferState) (rigidCount : Nat) : Prop where
  solutions_length : state.solutions.length = state.next
  solutionsScoped : state.solutions.Scoped rigidCount
  solutionsBounded : state.solutions.Bounded state.next
  solutionsNormalized : state.solutions.Normalized

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
          have hlookup : store.lookup id = none := by
            simp [MStore.lookup, hget]
          simpa [MStore.apply, hlookup] using typeWF
      | some entry =>
          cases entry with
          | none =>
              have hlookup : store.lookup id = none := by
                simp [MStore.lookup, hget]
              simpa [MStore.apply, hlookup] using typeWF
          | some result =>
              have member : some result ∈ store := List.mem_of_getElem? hget
              have hlookup : store.lookup id = some result := by
                simp [MStore.lookup, hget]
              simpa [MStore.apply, hlookup] using
                And.intro (scoped_mono_binder (storeScoped result member))
                  (storeBounded result member)

theorem InferState.initial_safe {rigidCount : Nat} :
    (⟨0, []⟩ : InferState).Safe rigidCount := by
  constructor <;> simp [MStore.Scoped, MStore.Bounded, MStore.Normalized]

theorem InferState.fresh_safe
    {state : InferState} {rigidCount : Nat}
    (safe : state.Safe rigidCount) :
    state.fresh.1.Safe rigidCount ∧
      state.fresh.2.InferWF rigidCount 0 state.fresh.1.next ∧
      state.next ≤ state.fresh.1.next := by
  rcases safe with ⟨length, storeScoped, bounded, normalized⟩
  simp only [InferState.fresh]
  refine ⟨?_, ?_, by omega⟩
  · refine ⟨by simp [length], ?_, ?_, ?_⟩
    · intro ty member
      rcases List.mem_append.mp member with old | new
      · exact storeScoped ty old
      · simp only [List.mem_singleton] at new
        cases new
    · intro ty member
      rcases List.mem_append.mp member with old | new
      · intro id idMember
        exact Nat.lt_succ_of_lt (bounded ty old id idMember)
      · simp only [List.mem_singleton] at new
        cases new
    · intro ty member
      rcases List.mem_append.mp member with old | new
      · intro id idMember
        have idInSolutions : id < state.solutions.length := by
          rw [length]
          exact bounded ty old id idMember
        simp only [MStore.lookup]
        rw [List.getElem?_append_left idInSolutions]
        exact normalized ty old id idMember
      · simp only [List.mem_singleton] at new
        cases new
  · exact ⟨.mvar _, by
      intro id member
      simp only [Ty.mvars, List.mem_singleton] at member
      subst id
      omega⟩

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
  have newSafe :
      ({ next := allocation.next,
          solutions := state.solutions ++ List.replicate count none } :
        InferState).Safe rigidCount := by
    constructor
    · simp [safe.solutions_length, countEq]
    · intro ty hmem
      rcases List.mem_append.mp hmem with hOld | hNew
      · exact safe.solutionsScoped ty hOld
      · simp only [List.mem_replicate] at hNew
        cases hNew.2
    · intro ty hmem id hid
      rcases List.mem_append.mp hmem with hOld | hNew
      · have oldBound := safe.solutionsBounded ty hOld id hid
        exact lt_of_lt_of_le oldBound nextLe
      · simp only [List.mem_replicate] at hNew
        cases hNew.2
    · intro ty hmem
      rcases List.mem_append.mp hmem with hOld | hNew
      · intro id hid
        have idInSolutions : id < state.solutions.length := by
          rw [safe.solutions_length]
          exact safe.solutionsBounded ty hOld id hid
        simp only [MStore.lookup]
        rw [List.getElem?_append_left idInSolutions]
        exact safe.solutionsNormalized ty hOld id hid
      · simp only [List.mem_replicate] at hNew
        cases hNew.2
  refine ⟨?_, ?_, nextLe⟩
  · simpa [allocation, count] using newSafe
  · constructor
    · exact Template.allocate_scoped templateScoped
    · intro id hmem
      exact (Template.allocate_mvars templateScoped id hmem).2

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
      checked.solutions.apply left = checked.solutions.apply right := by
  unfold InferState.constrain at run
  cases hunify : state.solutions.unify left right with
  | none => simp [hunify] at run
  | some solutions =>
      simp only [hunify, Option.map_some, Option.some.injEq] at run
      subst checked
      refine ⟨?_, rfl, ?_⟩
      · refine ⟨?_, ?_, ?_, ?_⟩
        · rw [MStore.unify_length hunify, safe.solutions_length]
        · exact MStore.unify_scoped safe.solutionsScoped
            leftWF.1 rightWF.1 hunify
        · exact MStore.unify_bounded safe.solutionsBounded
            leftWF.2 rightWF.2 hunify
        · exact MStore.unify_normalized safe.solutionsNormalized hunify
      · exact MStore.unify_apply_eq safe.solutionsNormalized hunify

/-- Forgetting preserves the table's length. -/
private theorem MStore.forgetFrom_length (store : MStore) (cutoff : Nat) :
    (store.forgetFrom cutoff).length = store.length := by
  simp only [MStore.forgetFrom, List.length_append, List.length_take,
    List.length_replicate]
  omega

/-- Looking up a forgotten allocated metavariable is the original lookup below
the cutoff and `none` from the cutoff on. -/
private theorem MStore.lookup_forgetFrom (store : MStore) (cutoff id : Nat)
    (hid : id < store.length) :
    (store.forgetFrom cutoff).lookup id =
      if id < cutoff then store.lookup id else none := by
  by_cases h : id < cutoff
  · simp only [h, if_true]
    simp only [MStore.forgetFrom, MStore.lookup]
    rw [List.getElem?_append_left (by rw [List.length_take]; omega)]
    rw [List.getElem?_take_of_lt h]
  · simp only [h, if_false]
    simp only [MStore.forgetFrom, MStore.lookup]
    rw [List.getElem?_append_right (by rw [List.length_take]; omega)]
    rw [List.getElem?_replicate]
    by_cases hin : id - (store.take cutoff).length < store.length - cutoff
    · rw [if_pos hin]
      rfl
    · rw [if_neg hin]
      rfl

/-- Forgetting a region's solutions leaves a safe table at the outer rigid
boundary, provided no remaining solution mentions a region rigid. -/
theorem MStore.forgetFrom_safe
    {store : MStore} {rigidCount cutoff : Nat}
    (normalized : store.Normalized)
    (bounded : store.Bounded store.length)
    (escape : (store.forgetFrom cutoff).safeToLeave rigidCount = true) :
    (store.forgetFrom cutoff).length = store.length ∧
      (store.forgetFrom cutoff).Scoped rigidCount ∧
      (store.forgetFrom cutoff).Bounded store.length ∧
      (store.forgetFrom cutoff).Normalized := by
  have escaped := MStore.safeToLeave_eq_true_iff.mp escape
  have memStore : ∀ {ty : Ty},
      some ty ∈ store.forgetFrom cutoff → some ty ∈ store := by
    intro ty member
    have memTake : some ty ∈ store.take cutoff := by
      simpa [MStore.forgetFrom] using member
    exact List.mem_of_mem_take memTake
  refine ⟨MStore.forgetFrom_length store cutoff, ?_, ?_, ?_⟩
  · intro ty member
    exact escaped ty member
  · intro ty member id hid
    exact bounded ty (memStore member) id hid
  · intro ty member id hid
    have boundedEntry := bounded ty (memStore member) id hid
    have normalizedNone : store.lookup id = none :=
      normalized ty (memStore member) id hid
    rw [MStore.lookup_forgetFrom store cutoff id boundedEntry]
    split
    · exact normalizedNone
    · rfl


end EPL

namespace EPL

/-- Opening one authored binder block into the next rigid-level block preserves
algorithmic type scope. -/
theorem Ty.openRigidsFrom_scoped
    {ty : Ty} {rigidCount depth count : Nat}
    (typeScoped : ty.Scoped rigidCount (depth + count)) :
    (ty.openRigidsFrom depth rigidCount count).Scoped
      (rigidCount + count) depth := by
  induction typeScoped with
  | prim => exact .prim
  | arrow _ _ ihDomain ihCodomain =>
      exact .arrow ihDomain ihCodomain
  | bvar hlt =>
      simp only [Ty.openRigidsFrom]
      split
      next hInner => exact .bvar hInner
      next hOuter =>
        split
        next hBlock => exact .rigid (by omega)
        next hBeyond => omega
  | rigid hlt =>
      exact .rigid (by omega)
  | mvar id => exact .mvar id

theorem Ty.openRigidsFrom_metaFree
    {ty : Ty} {depth base count : Nat}
    (metaFree : ty.MetaFree) :
    (ty.openRigidsFrom depth base count).MetaFree := by
  induction metaFree with
  | prim => exact .prim
  | arrow _ _ ihDomain ihCodomain =>
      exact .arrow ihDomain ihCodomain
  | bvar =>
      simp only [Ty.openRigidsFrom]
      split
      · exact .bvar
      · split
        · exact .rigid
        · exact .bvar
  | rigid => exact .rigid

/-- Opening preserves declarative type well-formedness while replacing the
selected bound block by fresh rigid levels. -/
theorem Ty.openRigidsFrom_wf
    {ty : Ty} {rigidCount depth count : Nat}
    (typeWF : ty.WF rigidCount (depth + count)) :
    (ty.openRigidsFrom depth rigidCount count).WF
      (rigidCount + count) depth := by
  exact ⟨Ty.openRigidsFrom_scoped typeWF.1,
    Ty.openRigidsFrom_metaFree typeWF.2⟩

theorem Template.openRigidsFrom_scoped
    {template : Template} {rigidCount depth count : Nat}
    (templateScoped : template.Scoped rigidCount (depth + count)) :
    (template.openRigidsFrom depth rigidCount count).Scoped
      (rigidCount + count) depth := by
  induction templateScoped with
  | fixed typeWF => exact .fixed (Ty.openRigidsFrom_wf typeWF)
  | hole => exact .hole
  | named => exact .named
  | arrow _ _ ihDomain ihCodomain =>
      exact .arrow ihDomain ihCodomain

/-- Source opening respects nested written schemes: their own binders remain
protected while the selected enclosing block becomes fresh rigid levels. -/
theorem Expr.openRigidsFrom_typeScoped
    {input : Source} {rigidCount depth count : Nat}
    (inputScoped : input.TypeScoped rigidCount (depth + count)) :
    (input.openRigidsFrom depth rigidCount count).TypeScoped
      (rigidCount + count) depth := by
  induction input generalizing depth with
  | primLit literal => exact .primLit
  | primOp op => exact .primOp
  | var index => exact .var
  | lambda ann body ihBody =>
      cases inputScoped with
      | lambda annotationScoped bodyScoped =>
          apply Expr.TypeScoped.lambda
          · intro openedTemplate heq
            cases ann with
            | none => simp at heq
            | some template =>
                simp only [Option.map_some, Option.some.injEq] at heq
                subst openedTemplate
                exact Template.openRigidsFrom_scoped
                  (annotationScoped template rfl)
          · exact ihBody bodyScoped
  | app function argument ihFunction ihArgument =>
      cases inputScoped with
      | app functionScoped argumentScoped =>
          exact .app (ihFunction functionScoped) (ihArgument argumentScoped)
  | letIn ann rhs body ihRhs ihBody =>
      cases ann with
      | none =>
          cases inputScoped with
          | letMono rhsScoped bodyScoped =>
              exact .letMono (ihRhs rhsScoped) (ihBody bodyScoped)
      | some written =>
          cases inputScoped with
          | letPoly writtenScoped rhsScoped bodyScoped =>
              have writtenScoped' :
                  written.body.Scoped rigidCount
                    ((depth + written.paramCount) + count) := by
                simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
                  writtenScoped
              have rhsScoped' :
                  rhs.TypeScoped rigidCount
                    ((depth + written.paramCount) + count) := by
                simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
                  rhsScoped
              exact .letPoly
                (Template.openRigidsFrom_scoped writtenScoped')
                (ihRhs rhsScoped')
                (ihBody bodyScoped)
  | fix ann body ihBody =>
      cases inputScoped with
      | fix annotationScoped bodyScoped =>
          exact .fix
            (Template.openRigidsFrom_scoped annotationScoped)
            (ihBody bodyScoped)

end EPL

namespace EPL

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

/-- Successful internal inference preserves the dense-state invariant, returns
an allocated/scoped algorithmic type, and never moves the caller's outer
frontier backwards. This is the structural precursor to semantic soundness. -/
theorem inferFuel_safe
    {fuel rigidCount : Nat} {ctx : Ctx} {input : Source}
    {state : InferState} {result : InferResult}
    (stateSafe : state.Safe rigidCount)
    (ctxWF : ctx.InferWF rigidCount state.next)
    (inputScoped : input.TypeScoped rigidCount 0)
    (run : inferFuel fuel rigidCount ctx input state = some result) :
    result.state.Safe rigidCount ∧
      result.ty.InferWF rigidCount 0 result.state.next ∧
      state.next ≤ result.state.next := by
  have scoped_mono_rigid :
      ∀ {ty : Ty} {rigid smaller larger : Nat},
        ty.Scoped smaller rigid → smaller ≤ larger → ty.Scoped larger rigid := by
    intro ty rigid smaller larger h le
    induction h with
    | prim => exact .prim
    | arrow _ _ ihDomain ihCodomain => exact .arrow ihDomain ihCodomain
    | bvar hlt => exact .bvar hlt
    | rigid hlt => exact .rigid (lt_of_lt_of_le hlt le)
    | mvar id => exact .mvar id
  have inferWF_mono :
      ∀ {ty : Ty} {rigid binder smaller larger : Nat},
        ty.InferWF rigid binder smaller → smaller ≤ larger →
          ty.InferWF rigid binder larger := by
    intro ty rigid binder smaller larger h le
    exact ⟨h.1, fun id member => lt_of_lt_of_le (h.2 id member) le⟩
  have inferWF_mono_rigid :
      ∀ {ty : Ty} {binder frontier smaller larger : Nat},
        ty.InferWF smaller binder frontier → smaller ≤ larger →
          ty.InferWF larger binder frontier := by
    intro ty binder frontier smaller larger h le
    exact ⟨scoped_mono_rigid h.1 le, h.2⟩
  have ctx_mono :
      ∀ {context : Ctx} {rigid smaller larger : Nat},
        context.InferWF rigid smaller → smaller ≤ larger →
          context.InferWF rigid larger := by
    intro context rigid smaller larger h le scheme member
    exact inferWF_mono (h scheme member) le
  have ctx_mono_rigid :
      ∀ {context : Ctx} {frontier smaller larger : Nat},
        context.InferWF smaller frontier → smaller ≤ larger →
          context.InferWF larger frontier := by
    intro context frontier smaller larger h le scheme member
    exact inferWF_mono_rigid (h scheme member) le
  have state_mono_rigid :
      ∀ {candidate : InferState} {smaller larger : Nat},
        candidate.Safe smaller → smaller ≤ larger → candidate.Safe larger := by
    intro candidate smaller larger h le
    exact ⟨h.solutions_length,
      (fun ty member => scoped_mono_rigid (h.solutionsScoped ty member) le),
      h.solutionsBounded, h.solutionsNormalized⟩
  have metaFree_bounded :
      ∀ {ty : Ty} {frontier : Nat}, ty.MetaFree → ty.MVarBounded frontier := by
    intro ty frontier h
    induction h with
    | prim => simp [Ty.MVarBounded, Ty.mvars]
    | arrow _ _ ihDomain ihCodomain =>
        intro id member
        simp only [Ty.mvars, List.mem_dedup, List.mem_append] at member
        exact member.elim (ihDomain id) (ihCodomain id)
    | bvar => simp [Ty.MVarBounded, Ty.mvars]
    | rigid => simp [Ty.MVarBounded, Ty.mvars]
  have wf_inferWF :
      ∀ {ty : Ty} {rigid binder frontier : Nat},
        ty.WF rigid binder → ty.InferWF rigid binder frontier := by
    intro ty rigid binder frontier h
    exact ⟨h.1, metaFree_bounded h.2⟩
  have openWith_inferWF :
      ∀ {ty : Ty} {args : List Ty} {rigid count frontier : Nat},
        ty.InferWF rigid count frontier →
        args.length = count →
        (∀ arg ∈ args, arg.InferWF rigid 0 frontier) →
        (ty.openWith args).InferWF rigid 0 frontier := by
    intro ty args rigid count frontier typeWF length argsWF
    induction ty with
    | prim name => exact ⟨.prim, by simp [Ty.openWith, Ty.MVarBounded, Ty.mvars]⟩
    | arrow domain codomain ihDomain ihCodomain =>
        cases typeWF.1 with
        | arrow domainScoped codomainScoped =>
          have domainWF : domain.InferWF rigid count frontier :=
            ⟨domainScoped, fun id member => typeWF.2 id (by
              simp [Ty.mvars, member])⟩
          have codomainWF : codomain.InferWF rigid count frontier :=
            ⟨codomainScoped, fun id member => typeWF.2 id (by
              simp [Ty.mvars, member])⟩
          have domainResult := ihDomain domainWF
          have codomainResult := ihCodomain codomainWF
          exact ⟨Ty.Scoped.arrow domainResult.1 codomainResult.1,
            by
              intro id member
              simp only [Ty.openWith, Ty.mvars, List.mem_dedup,
                List.mem_append] at member
              rcases member with member | member
              · exact domainResult.2 id member
              · exact codomainResult.2 id member⟩
    | bvar index =>
        cases typeWF.1 with
        | bvar hlt =>
          have inArgs : index < args.length := by omega
          rw [Ty.openWith, List.getElem?_eq_getElem inArgs, Option.getD_some]
          exact argsWF args[index] (List.getElem_mem ..)
    | rigid level =>
        cases typeWF.1 with
        | rigid hlt =>
          exact ⟨.rigid hlt,
            by simp [Ty.openWith, Ty.MVarBounded, Ty.mvars]⟩
    | mvar id =>
        exact ⟨.mvar id, typeWF.2⟩
  induction fuel generalizing rigidCount ctx input state result with
  | zero => simp [inferFuel] at run
  | succ fuel ih =>
      cases input with
      | primLit literal =>
          simp only [inferFuel, Option.some.injEq] at run
          subst result
          refine ⟨stateSafe, ?_, le_rfl⟩
          cases literal <;> exact wf_inferWF ⟨.prim, .prim⟩
      | primOp op =>
          simp only [inferFuel, Option.some.injEq] at run
          subst result
          refine ⟨stateSafe, ?_, le_rfl⟩
          cases op
          exact wf_inferWF
            ⟨.arrow .prim (.arrow .prim .prim),
              .arrow .prim (.arrow .prim .prim)⟩
      | var index =>
          simp only [inferFuel] at run
          cases lookup : ctx[index]? with
          | none => simp [lookup] at run
          | some scheme =>
              simp only [lookup] at run
              have schemeMember : scheme ∈ ctx := List.mem_of_getElem? lookup
              have schemeWF := ctxWF scheme schemeMember
              have appliedWF :
                  (state.solutions.applyScheme scheme).InferWF
                    rigidCount state.next := by
                exact MStore.apply_inferWF stateSafe.solutionsScoped
                  stateSafe.solutionsBounded schemeWF
              let fresh := state.freshMany scheme.paramCount
              have freshSafe := InferState.freshMany_safe
                (count := scheme.paramCount) stateSafe
              have appliedMono :
                  (state.solutions.applyScheme scheme).InferWF
                    rigidCount fresh.1.next :=
                inferWF_mono appliedWF freshSafe.2.2.2
              have openedWF :
                  ((state.solutions.applyScheme scheme).openWith fresh.2).InferWF
                    rigidCount 0 fresh.1.next :=
                openWith_inferWF appliedMono freshSafe.2.2.1 freshSafe.2.1
              have resultEq : result =
                  ⟨fresh.1, (state.solutions.applyScheme scheme).openWith fresh.2,
                    .var index⟩ := by
                exact Option.some.inj run.symm
              subst result
              exact ⟨freshSafe.1, openedWF, freshSafe.2.2.2⟩
      | lambda ann body =>
          cases inputScoped with
          | lambda annScoped bodyScoped =>
            cases ann with
            | none =>
                simp only [inferFuel] at run
                let seeded := state.fresh
                have seededSafe := InferState.fresh_safe stateSafe
                have bodyCtxWF :
                    Ctx.InferWF (PolyTy.mono seeded.2 :: ctx)
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
                    simp [bodyRun] at run
                    have bodySafe := ih seededSafe.1 bodyCtxWF bodyScoped bodyRun
                    have paramBefore : seeded.2.InferWF rigidCount 0
                        bodyResult.state.next :=
                      inferWF_mono seededSafe.2.1 bodySafe.2.2
                    have paramAfter := MStore.apply_inferWF
                      bodySafe.1.solutionsScoped bodySafe.1.solutionsBounded
                      paramBefore
                    have resultEq : result =
                        ⟨bodyResult.state,
                          .arrow (bodyResult.state.solutions.apply seeded.2)
                            bodyResult.ty,
                          .lambda (some seeded.2) bodyResult.elaborated⟩ := by
                      simpa [seeded] using run.symm
                    subst result
                    exact ⟨bodySafe.1,
                      ⟨.arrow paramAfter.1 bodySafe.2.1.1,
                        by
                          intro id member
                          simp only [Ty.mvars, List.mem_dedup,
                            List.mem_append] at member
                          rcases member with member | member
                          · exact paramAfter.2 id member
                          · exact bodySafe.2.1.2 id member⟩,
                      le_trans seededSafe.2.2 bodySafe.2.2⟩
            | some template =>
                have templateScoped := annScoped template rfl
                simp only [inferFuel] at run
                let seeded := state.allocate template
                have seededSafe := InferState.allocate_safe stateSafe templateScoped
                have bodyCtxWF :
                    Ctx.InferWF (PolyTy.mono seeded.2 :: ctx)
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
                    simp [bodyRun] at run
                    have bodySafe := ih seededSafe.1 bodyCtxWF bodyScoped bodyRun
                    have paramBefore : seeded.2.InferWF rigidCount 0
                        bodyResult.state.next :=
                      inferWF_mono seededSafe.2.1 bodySafe.2.2
                    have paramAfter := MStore.apply_inferWF
                      bodySafe.1.solutionsScoped bodySafe.1.solutionsBounded
                      paramBefore
                    have resultEq : result =
                        ⟨bodyResult.state,
                          .arrow (bodyResult.state.solutions.apply seeded.2)
                            bodyResult.ty,
                          .lambda (some seeded.2) bodyResult.elaborated⟩ := by
                      simpa [seeded] using run.symm
                    subst result
                    exact ⟨bodySafe.1,
                      ⟨.arrow paramAfter.1 bodySafe.2.1.1,
                        by
                          intro id member
                          simp only [Ty.mvars, List.mem_dedup,
                            List.mem_append] at member
                          rcases member with member | member
                          · exact paramAfter.2 id member
                          · exact bodySafe.2.1.2 id member⟩,
                      le_trans seededSafe.2.2 bodySafe.2.2⟩
      | app function argument =>
          cases inputScoped with
          | app functionScoped argumentScoped =>
            simp only [inferFuel] at run
            cases functionRun : inferFuel fuel rigidCount ctx function state with
            | none => simp [functionRun] at run
            | some functionResult =>
                have functionSafe := ih stateSafe ctxWF functionScoped functionRun
                have argumentCtxWF := ctx_mono ctxWF functionSafe.2.2
                cases argumentRun : inferFuel fuel rigidCount ctx argument
                    functionResult.state with
                | none => simp [functionRun, argumentRun] at run
                | some argumentResult =>
                    have argumentSafe := ih functionSafe.1 argumentCtxWF
                      argumentScoped argumentRun
                    let fresh := argumentResult.state.fresh
                    have freshSafe := InferState.fresh_safe argumentSafe.1
                    have functionTyWF : functionResult.ty.InferWF rigidCount 0
                        fresh.1.next :=
                      inferWF_mono functionSafe.2.1
                        (le_trans argumentSafe.2.2 freshSafe.2.2)
                    have argumentTyWF : argumentResult.ty.InferWF rigidCount 0
                        fresh.1.next :=
                      inferWF_mono argumentSafe.2.1 freshSafe.2.2
                    have arrowWF :
                        (Ty.arrow argumentResult.ty fresh.2).InferWF
                          rigidCount 0 fresh.1.next := by
                      exact ⟨.arrow argumentTyWF.1 freshSafe.2.1.1,
                        by
                          intro id member
                          simp only [Ty.mvars, List.mem_dedup,
                            List.mem_append] at member
                          rcases member with member | member
                          · exact argumentTyWF.2 id member
                          · exact freshSafe.2.1.2 id member⟩
                    cases checkedRun : fresh.1.constrain functionResult.ty
                        (.arrow argumentResult.ty fresh.2) with
                    | none =>
                        dsimp [fresh] at checkedRun
                        simp [functionRun, argumentRun, checkedRun] at run
                    | some checked =>
                        dsimp [fresh] at checkedRun
                        simp [functionRun, argumentRun, checkedRun] at run
                        have checkedSafe := InferState.constrain_safe
                          freshSafe.1 functionTyWF arrowWF checkedRun
                        have freshTyAtChecked : fresh.2.InferWF rigidCount 0
                            checked.next := by
                          rw [checkedSafe.2.1]
                          exact freshSafe.2.1
                        have resultTyWF := MStore.apply_inferWF
                          checkedSafe.1.solutionsScoped
                          checkedSafe.1.solutionsBounded freshTyAtChecked
                        have resultEq : result =
                            ⟨checked, checked.solutions.apply fresh.2,
                              .app functionResult.elaborated
                                argumentResult.elaborated⟩ := by
                          simpa [fresh] using run.symm
                        subst result
                        refine ⟨checkedSafe.1, resultTyWF, ?_⟩
                        rw [checkedSafe.2.1]
                        exact le_trans functionSafe.2.2
                          (le_trans argumentSafe.2.2 freshSafe.2.2)
      | letIn ann rhs body =>
          cases ann with
          | none =>
              cases inputScoped with
              | letMono rhsScoped bodyScoped =>
                simp only [inferFuel] at run
                cases rhsRun : inferFuel fuel rigidCount ctx rhs state with
                | none => simp [rhsRun] at run
                | some rhsResult =>
                    have rhsSafe := ih stateSafe ctxWF rhsScoped rhsRun
                    let rhsTy := rhsResult.state.solutions.apply rhsResult.ty
                    have rhsTyWF : rhsTy.InferWF rigidCount 0
                        rhsResult.state.next :=
                      MStore.apply_inferWF rhsSafe.1.solutionsScoped
                        rhsSafe.1.solutionsBounded rhsSafe.2.1
                    have bodyCtxWF :
                        Ctx.InferWF (PolyTy.mono rhsTy :: ctx)
                          rigidCount rhsResult.state.next := by
                      intro scheme member
                      simp only [List.mem_cons] at member
                      rcases member with rfl | member
                      · exact rhsTyWF
                      · exact ctx_mono ctxWF rhsSafe.2.2 scheme member
                    cases bodyRun : inferFuel fuel rigidCount
                        (PolyTy.mono rhsTy :: ctx) body rhsResult.state with
                    | none =>
                        simp [rhsTy, rhsRun, bodyRun] at run
                    | some bodyResult =>
                        have bodySafe := ih rhsSafe.1 bodyCtxWF bodyScoped bodyRun
                        simp [rhsTy, rhsRun, bodyRun] at run
                        have resultEq : result =
                            ⟨bodyResult.state, bodyResult.ty,
                              .letIn none rhsResult.elaborated
                                bodyResult.elaborated⟩ := by
                          exact run.symm
                        subst result
                        exact ⟨bodySafe.1, bodySafe.2.1,
                          le_trans rhsSafe.2.2 bodySafe.2.2⟩
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
                have rhsCtxWF : ctx.InferWF (rigidCount + count)
                    seeded.1.next :=
                  ctx_mono (ctx_mono_rigid ctxWF (by omega)) seededSafe.2.2
                cases rhsRun : inferFuel fuel (rigidCount + count) ctx
                    (rhs.openRigids rigidCount count) seeded.1 with
                | none =>
                    dsimp [seeded, openedTemplate, count] at rhsRun
                    simp [rhsRun] at run
                | some rhsResult =>
                    dsimp [seeded, openedTemplate, count] at rhsRun
                    have rhsSafe := ih seededSafe.1 rhsCtxWF openedRhsScoped rhsRun
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
                        let completedOpen := checked.solutions.apply seeded.2
                        let completed : PolyTy :=
                          ⟨count, completedOpen.closeRigids rigidCount count⟩
                        let projected := checked.solutions.forgetFrom state.next
                        have escape : projected.safeToLeave rigidCount = true := by
                          by_contra h
                          have hfalse : projected.safeToLeave rigidCount = false := by
                            cases hv : projected.safeToLeave rigidCount <;> simp_all
                          simp [rhsRun, checkedRun, projected, hfalse] at run
                        have projectedSafe := MStore.forgetFrom_safe
                          checkedSafe.1.solutionsNormalized
                          (by simpa [checkedSafe.1.solutions_length] using
                            checkedSafe.1.solutionsBounded)
                          escape
                        have localStartLe : localStart ≤ checked.next := by
                          rw [checkedSafe.2.1]
                          exact le_trans seededSafe.2.2 rhsSafe.2.2
                        let outerState : InferState :=
                          { next := checked.next
                            solutions := projected }
                        have outerSafe : outerState.Safe rigidCount := by
                          refine ⟨?_, ?_, ?_, ?_⟩
                          · simpa [outerState, projected,
                              checkedSafe.1.solutions_length] using projectedSafe.1
                          · simpa [outerState, projected] using projectedSafe.2.1
                          · simpa [outerState, projected,
                              checkedSafe.1.solutions_length] using projectedSafe.2.2.1
                          · simpa [outerState, projected] using projectedSafe.2.2.2
                        have seededAtChecked : seeded.2.InferWF
                            (rigidCount + count) 0 checked.next := by
                          rw [checkedSafe.2.1]
                          exact seededTyAtRhs
                        have completedOpenWF := MStore.apply_inferWF
                          checkedSafe.1.solutionsScoped
                          checkedSafe.1.solutionsBounded seededAtChecked
                        have completedBodyScoped :
                            completed.body.Scoped rigidCount count := by
                          simpa [completed] using
                            Ty.closeRigids_scoped_zero completedOpenWF.1
                        have completedBodyBounded :
                            completed.body.MVarBounded checked.next := by
                          simpa [completed] using
                            Ty.closeRigids_mvarBounded completedOpenWF.2
                        have completedWF : completed.InferWF rigidCount checked.next :=
                          ⟨completedBodyScoped, completedBodyBounded⟩
                        have bodyCtxWF : Ctx.InferWF (completed :: ctx)
                            rigidCount outerState.next := by
                          intro scheme member
                          simp only [List.mem_cons] at member
                          rcases member with rfl | member
                          · simpa [outerState] using completedWF
                          · have ctxAtChecked : Ctx.InferWF ctx rigidCount checked.next :=
                              ctx_mono ctxWF (by simpa [localStart] using localStartLe)
                            simpa [outerState] using ctxAtChecked scheme member
                        simp [rhsRun, checkedRun, projected, escape] at run
                        cases bodyRun : inferFuel fuel rigidCount
                            (completed :: ctx) body outerState with
                        | none =>
                            simp [completed, completedOpen, count, outerState,
                              projected, seeded, openedTemplate, bodyRun] at run
                        | some bodyResult =>
                            have bodySafe := ih outerSafe bodyCtxWF bodyScoped bodyRun
                            simp [completed, completedOpen, count, outerState,
                              projected, seeded, openedTemplate, bodyRun] at run
                            have resultEq : result =
                                ⟨bodyResult.state, bodyResult.ty,
                                  .letIn (some completed)
                                    (checked.solutions.applyExpr rhsResult.elaborated)
                                    bodyResult.elaborated⟩ := by
                              exact run.symm
                            subst result
                            exact ⟨bodySafe.1, bodySafe.2.1,
                              le_trans localStartLe bodySafe.2.2⟩
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
                have bodySafe := ih seededSafe.1 bodyCtxWF bodyScoped bodyRun
                have selfAtBody : seeded.2.InferWF rigidCount 0
                    bodyResult.state.next :=
                  inferWF_mono seededSafe.2.1 bodySafe.2.2
                cases checkedRun : bodyResult.state.constrain
                    bodyResult.ty seeded.2 with
                | none =>
                    dsimp [seeded] at checkedRun
                    simp [bodyRun, checkedRun] at run
                | some checked =>
                    dsimp [seeded] at checkedRun
                    simp [bodyRun, checkedRun] at run
                    have checkedSafe := InferState.constrain_safe bodySafe.1
                      bodySafe.2.1 selfAtBody checkedRun
                    have selfAtChecked : seeded.2.InferWF rigidCount 0
                        checked.next := by
                      rw [checkedSafe.2.1]
                      exact selfAtBody
                    have resultTyWF := MStore.apply_inferWF
                      checkedSafe.1.solutionsScoped
                      checkedSafe.1.solutionsBounded selfAtChecked
                    have resultEq : result =
                        ⟨checked, checked.solutions.apply seeded.2,
                          .fix seeded.2 bodyResult.elaborated⟩ := by
                      simpa [seeded] using run.symm
                    subst result
                    refine ⟨checkedSafe.1, resultTyWF, ?_⟩
                    rw [checkedSafe.2.1]
                    exact le_trans seededSafe.2.2 bodySafe.2.2

end EPL
