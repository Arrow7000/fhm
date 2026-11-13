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
  | app function argument ihFunction ihArgument =>
      exact .app
        (ihFunction frontier fun name hmem =>
          hcover name (List.mem_append_left _ hmem))
        (ihArgument (function.allocateWith holes frontier).1 fun name hmem =>
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
  | app _ _ ihFunction ihArgument =>
      exact .app ihFunction ihArgument

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
  | con id =>
      constructor
      · intro _
        exact .con id
      · intro _
        rfl
  | app function argument ihFunction ihArgument =>
      simp only [Ty.scopedB, Bool.and_eq_true]
      constructor
      · rintro ⟨hFunction, hArgument⟩
        exact .app (ihFunction.mp hFunction) (ihArgument.mp hArgument)
      · intro h
        cases h with
        | app hFunction hArgument =>
            exact ⟨ihFunction.mpr hFunction, ihArgument.mpr hArgument⟩
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
  | con id =>
      constructor
      · intro _
        exact .con
      · intro _
        rfl
  | app function argument ihFunction ihArgument =>
      simp only [Ty.metaFreeB, Bool.and_eq_true]
      constructor
      · rintro ⟨hFunction, hArgument⟩
        exact .app (ihFunction.mp hFunction) (ihArgument.mp hArgument)
      · intro h
        cases h with
        | app hFunction hArgument =>
            exact ⟨ihFunction.mpr hFunction, ihArgument.mpr hArgument⟩
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
  | app function argument ihFunction ihArgument =>
      simp only [Template.scopedB, Bool.and_eq_true]
      constructor
      · rintro ⟨hFunction, hArgument⟩
        exact .app (ihFunction.mp hFunction) (ihArgument.mp hArgument)
      · intro h
        cases h with
        | app hFunction hArgument =>
            exact ⟨ihFunction.mpr hFunction, ihArgument.mpr hArgument⟩

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
  | const c =>
      constructor
      · intro _
        exact .const
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

/-- The dense solution table agrees with its allocation frontier, and every
solution is normalized, allocated, and respects its metavariable's level. -/
structure InferState.Safe (state : InferState) : Prop where
  solutions_length : state.solutions.length = state.next
  solutionsLeveled : state.solutions.Leveled
  solutionsBounded : state.solutions.Bounded state.next
  solutionsNormalized : state.solutions.Normalized

private theorem Ty.Scoped.mono_rigid {ty : Ty} {rigid rigid' binder : Nat}
    (typeScoped : ty.Scoped rigid binder) (le : rigid ≤ rigid') :
    ty.Scoped rigid' binder := by
  induction typeScoped with
  | prim => exact .prim
  | arrow _ _ ihDomain ihCodomain => exact .arrow ihDomain ihCodomain
  | bvar hlt => exact .bvar hlt
  | rigid hlt => exact .rigid (lt_of_lt_of_le hlt le)
  | mvar id => exact .mvar id
  | con id => exact .con id
  | app _ _ ihFunction ihArgument => exact .app ihFunction ihArgument

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

private theorem Ty.LevelBounded.mono_le {ty : Ty} {store store' : MStore} {level : Nat}
    (bounded : ty.LevelBounded store level)
    (le : ∀ id, store'.levelOf id ≤ store.levelOf id) :
    ty.LevelBounded store' level := by
  intro id member
  exact le_trans (le id) (bounded id member)

private theorem Ty.LevelBounded.congr {ty : Ty} {store store' : MStore} {level : Nat}
    (bounded : ty.LevelBounded store level)
    (eq : ∀ id ∈ ty.mvars, store'.levelOf id = store.levelOf id) :
    ty.LevelBounded store' level := by
  intro id member
  rw [eq id member]
  exact bounded id member

private theorem Ty.LevelBounded.mono_level {ty : Ty} {store : MStore} {level level' : Nat}
    (bounded : ty.LevelBounded store level) (le : level ≤ level') :
    ty.LevelBounded store level' := by
  intro id member
  exact le_trans (bounded id member) le

private theorem Ty.LevelBounded.mono_le_on {ty : Ty} {store store' : MStore} {level : Nat}
    (bounded : ty.LevelBounded store level)
    (le : ∀ id ∈ ty.mvars, store'.levelOf id ≤ store.levelOf id) :
    ty.LevelBounded store' level := by
  intro id member
  exact le_trans (le id member) (bounded id member)

private theorem MStore.lookup_append_left {store extra : MStore} {id : Nat}
    (h : id < store.length) :
    (store ++ extra).lookup id = store.lookup id := by
  unfold MStore.lookup
  rw [List.getElem?_append_left h]

private theorem MStore.levelOf_append_left {store extra : MStore} {id : Nat}
    (h : id < store.length) :
    (store ++ extra).levelOf id = store.levelOf id := by
  unfold MStore.levelOf
  rw [List.getElem?_append_left h]

private theorem MStore.levelOf_append_replicate {store : MStore} {count level id : Nat}
    (hlo : store.length ≤ id) (hhi : id < store.length + count) :
    (store ++ List.replicate count (⟨level, none⟩ : MEntry)).levelOf id = level := by
  unfold MStore.levelOf
  rw [List.getElem?_append_right hlo]
  have hlt : id - store.length < count := by omega
  rw [List.getElem?_replicate]
  simp only [hlt, if_true, Option.map_some, Option.getD_some]

private theorem MStore.lookup_append_unsolved {store extra : MStore} {id : Nat} {ty : Ty}
    (unsolved : ∀ entry ∈ extra, entry.solution = none)
    (lookup : (store ++ extra).lookup id = some ty) :
    store.lookup id = some ty := by
  unfold MStore.lookup at lookup ⊢
  by_cases hid : id < store.length
  · rwa [List.getElem?_append_left hid] at lookup
  · have hge : store.length ≤ id := by omega
    rw [List.getElem?_append_right hge] at lookup
    cases hget : extra[id - store.length]? with
    | none => simp [hget] at lookup
    | some entry =>
        simp only [hget, Option.bind] at lookup
        have mem : entry ∈ extra := List.mem_of_getElem? hget
        rw [unsolved entry mem] at lookup
        exact absurd lookup (by simp)

private theorem MStore.leveled_append_unsolved
    {store extra : MStore}
    (leveled : store.Leveled)
    (bounded : store.Bounded store.length)
    (unsolved : ∀ entry ∈ extra, entry.solution = none) :
    (store ++ extra).Leveled := by
  intro id entry ty hentry solution
  by_cases hid : id < store.length
  · have oldEntry : store[id]? = some entry := by
      rwa [List.getElem?_append_left hid] at hentry
    obtain ⟨scopedTy, levels⟩ := leveled id entry ty oldEntry solution
    refine ⟨scopedTy, ?_⟩
    intro m mem
    have oldLookup : store.lookup id = some ty := by
      simp [MStore.lookup, oldEntry, solution]
    have mbound : m < store.length := bounded id ty oldLookup m mem
    rw [MStore.levelOf_append_left mbound]
    exact levels m mem
  · have hge : store.length ≤ id := by omega
    rw [List.getElem?_append_right hge] at hentry
    have mem : entry ∈ extra := List.mem_of_getElem? hentry
    rw [unsolved entry mem] at solution
    exact absurd solution (by simp)

private theorem MStore.bounded_append_unsolved
    {store extra : MStore} {frontier : Nat}
    (bounded : store.Bounded frontier)
    (unsolved : ∀ entry ∈ extra, entry.solution = none) :
    (store ++ extra).Bounded frontier := by
  intro id ty lookup
  exact bounded id ty (MStore.lookup_append_unsolved unsolved lookup)

private theorem MStore.normalized_append_unsolved
    {store extra : MStore}
    (normalized : store.Normalized)
    (bounded : store.Bounded store.length)
    (unsolved : ∀ entry ∈ extra, entry.solution = none) :
    (store ++ extra).Normalized := by
  intro id ty lookup m mem
  have oldLookup := MStore.lookup_append_unsolved unsolved lookup
  have mbound : m < store.length := bounded id ty oldLookup m mem
  rw [MStore.lookup_append_left mbound]
  exact normalized id ty oldLookup m mem

/-- Resolving a type through a safe store preserves its scope and boundedness,
and preserves the level bound of its metavariables. -/
theorem MStore.apply_inferWF
    {store : MStore} {ty : Ty} {rigidCount binderCount frontier : Nat}
    (storeLeveled : store.Leveled)
    (storeBounded : store.Bounded frontier)
    (typeWF : ty.InferWF rigidCount binderCount frontier)
    (typeLevels : ty.LevelBounded store rigidCount) :
    (store.apply ty).InferWF rigidCount binderCount frontier ∧
      (store.apply ty).LevelBounded store rigidCount := by
  have main : ∀ (ty : Ty),
      ty.InferWF rigidCount binderCount frontier →
      ty.LevelBounded store rigidCount →
      (store.apply ty).InferWF rigidCount binderCount frontier ∧
        (store.apply ty).LevelBounded store rigidCount := by
    intro ty
    induction ty with
    | prim name =>
        intro typeWF typeLevels
        exact ⟨⟨.prim, by
            intro id member
            simp [MStore.apply, Ty.mvars] at member⟩, by
            intro id member
            simp [MStore.apply, Ty.mvars] at member⟩
    | arrow domain codomain ihDomain ihCodomain =>
        intro typeWF typeLevels
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
        have domainLevels : domain.LevelBounded store rigidCount := by
          intro id member
          exact typeLevels id (by simp [Ty.mvars, member])
        have codomainLevels : codomain.LevelBounded store rigidCount := by
          intro id member
          exact typeLevels id (by simp [Ty.mvars, member])
        obtain ⟨domainResult, domainLevels'⟩ :=
          ihDomain domainWF domainLevels
        obtain ⟨codomainResult, codomainLevels'⟩ :=
          ihCodomain codomainWF codomainLevels
        constructor
        · exact ⟨.arrow domainResult.1 codomainResult.1, by
            intro id member
            simp only [MStore.apply, Ty.mvars, List.mem_dedup,
              List.mem_append] at member
            rcases member with member | member
            · exact domainResult.2 id member
            · exact codomainResult.2 id member⟩
        · intro id member
          simp only [MStore.apply, Ty.mvars, List.mem_dedup,
            List.mem_append] at member
          rcases member with member | member
          · exact domainLevels' id member
          · exact codomainLevels' id member
    | con id =>
        intro typeWF typeLevels
        exact ⟨⟨typeWF.1, by
          intro id member
          simp [MStore.apply, Ty.mvars] at member⟩, by
          intro id member
          simp [MStore.apply, Ty.mvars] at member⟩
    | app function argument ihFunction ihArgument =>
        intro typeWF typeLevels
        have scopedParts :
            function.Scoped rigidCount binderCount ∧
              argument.Scoped rigidCount binderCount := by
          cases typeWF.1 with
          | app hFunction hArgument => exact ⟨hFunction, hArgument⟩
        have functionWF : function.InferWF rigidCount binderCount frontier := by
          exact ⟨scopedParts.1, fun id member =>
            typeWF.2 id (by simp [Ty.mvars, member])⟩
        have argumentWF : argument.InferWF rigidCount binderCount frontier := by
          exact ⟨scopedParts.2, fun id member =>
            typeWF.2 id (by simp [Ty.mvars, member])⟩
        have functionLevels : function.LevelBounded store rigidCount := by
          intro id member
          exact typeLevels id (by simp [Ty.mvars, member])
        have argumentLevels : argument.LevelBounded store rigidCount := by
          intro id member
          exact typeLevels id (by simp [Ty.mvars, member])
        obtain ⟨functionResult, functionLevels'⟩ :=
          ihFunction functionWF functionLevels
        obtain ⟨argumentResult, argumentLevels'⟩ :=
          ihArgument argumentWF argumentLevels
        constructor
        · exact ⟨.app functionResult.1 argumentResult.1, by
            intro id member
            simp only [MStore.apply, Ty.mvars, List.mem_dedup,
              List.mem_append] at member
            rcases member with member | member
            · exact functionResult.2 id member
            · exact argumentResult.2 id member⟩
        · intro id member
          simp only [MStore.apply, Ty.mvars, List.mem_dedup,
            List.mem_append] at member
          rcases member with member | member
          · exact functionLevels' id member
          · exact argumentLevels' id member
    | bvar index =>
        intro typeWF typeLevels
        exact ⟨⟨typeWF.1, by
          intro id member
          simp [MStore.apply, Ty.mvars] at member⟩, by
          intro id member
          simp [MStore.apply, Ty.mvars] at member⟩
    | rigid level =>
        intro typeWF typeLevels
        exact ⟨⟨typeWF.1, by
          intro id member
          simp [MStore.apply, Ty.mvars] at member⟩, by
          intro id member
          simp [MStore.apply, Ty.mvars] at member⟩
    | mvar id =>
        intro typeWF typeLevels
        simp only [MStore.apply]
        cases hget : store[id]? with
        | none =>
            have hlookup : store.lookup id = none := by
              simp [MStore.lookup, hget]
            rw [hlookup]
            simp only [Option.getD_none]
            exact ⟨⟨.mvar id, typeWF.2⟩, typeLevels⟩
        | some entry =>
            cases solution : entry.solution with
            | none =>
                have hlookup : store.lookup id = none := by
                  simp [MStore.lookup, hget, solution]
                rw [hlookup]
                simp only [Option.getD_none]
                exact ⟨⟨.mvar id, typeWF.2⟩, typeLevels⟩
            | some result =>
                have hlookup : store.lookup id = some result := by
                  simp [MStore.lookup, hget, solution]
                rw [hlookup]
                simp only [Option.getD_some]
                have hlevel : store.levelOf id = entry.level := by
                  simp [MStore.levelOf, hget]
                have hlevelLe : entry.level ≤ rigidCount := by
                  rw [← hlevel]
                  exact typeLevels id (by simp [Ty.mvars])
                obtain ⟨scopedTy, levels⟩ :=
                  storeLeveled id entry result hget solution
                have resultScoped : result.Scoped rigidCount binderCount := by
                  exact Ty.Scoped.mono_binder
                    (Ty.Scoped.mono_rigid scopedTy hlevelLe) (Nat.zero_le _)
                constructor
                · exact ⟨resultScoped, storeBounded id result hlookup⟩
                · intro m member
                  exact le_trans (levels m member) hlevelLe
  exact main ty typeWF typeLevels

theorem InferState.initial_safe :
    (⟨0, []⟩ : InferState).Safe := by
  constructor <;>
    simp [MStore.Bounded, MStore.Normalized, MStore.Leveled, MStore.lookup]

theorem InferState.fresh_safe
    {state : InferState} {level : Nat}
    (safe : state.Safe) :
    (state.fresh level).1.Safe ∧
      (state.fresh level).2.InferWF level 0 (state.fresh level).1.next ∧
      (state.fresh level).2.LevelBounded (state.fresh level).1.solutions level ∧
      state.next ≤ (state.fresh level).1.next ∧
      (∀ id, id < state.next →
        (state.fresh level).1.solutions.levelOf id = state.solutions.levelOf id) := by
  rcases safe with ⟨length, leveled, bounded, normalized⟩
  simp only [InferState.fresh]
  have boundedLength : state.solutions.Bounded state.solutions.length := by
    simpa [length] using bounded
  have unsolvedNew :
      ∀ entry ∈ ([(⟨level, none⟩ : MEntry)] : MStore), entry.solution = none := by
    intro entry member
    simp only [List.mem_singleton] at member
    subst member
    rfl
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_, ?_⟩
    · simp [length]
    · exact MStore.leveled_append_unsolved leveled boundedLength unsolvedNew
    · intro id ty lookup m member
      have := MStore.bounded_append_unsolved bounded unsolvedNew id ty lookup
        m member
      show m < state.next + 1
      omega
    · exact MStore.normalized_append_unsolved normalized boundedLength unsolvedNew
  · constructor
    · exact .mvar _
    · intro id member
      simp only [Ty.mvars, List.mem_singleton] at member
      subst id
      omega
  · intro id member
    simp only [Ty.mvars, List.mem_singleton] at member
    subst id
    have := MStore.levelOf_append_replicate
      (store := state.solutions) (count := 1) (level := level)
      (id := state.next) (by simp [length]) (by simp [length])
    simpa [List.replicate_one] using this.le
  · show state.next ≤ state.next + 1
    omega
  · intro id hid
    exact MStore.levelOf_append_left (store := state.solutions)
      (extra := [(⟨level, none⟩ : MEntry)]) (by simpa [length] using hid)

theorem InferState.freshMany_safe
    {state : InferState} {level count : Nat}
    (safe : state.Safe) :
    (state.freshMany level count).1.Safe ∧
      (∀ ty ∈ (state.freshMany level count).2,
        ty.InferWF level 0 (state.freshMany level count).1.next) ∧
      (∀ ty ∈ (state.freshMany level count).2,
        ty.LevelBounded (state.freshMany level count).1.solutions level) ∧
      (state.freshMany level count).2.length = count ∧
      state.next ≤ (state.freshMany level count).1.next ∧
      (∀ id, id < state.next →
        (state.freshMany level count).1.solutions.levelOf id =
          state.solutions.levelOf id) := by
  have inferWF_mono :
      ∀ {ty : Ty} {smaller larger : Nat},
        ty.InferWF level 0 smaller → smaller ≤ larger →
          ty.InferWF level 0 larger := by
    intro ty smaller larger wf le
    exact ⟨wf.1, fun id member => lt_of_lt_of_le (wf.2 id member) le⟩
  have main : ∀ (count : Nat) (state : InferState), state.Safe →
      (state.freshMany level count).1.Safe ∧
        (∀ ty ∈ (state.freshMany level count).2,
          ty.InferWF level 0 (state.freshMany level count).1.next) ∧
        (∀ ty ∈ (state.freshMany level count).2,
          ty.LevelBounded (state.freshMany level count).1.solutions level) ∧
        (state.freshMany level count).2.length = count ∧
        state.next ≤ (state.freshMany level count).1.next ∧
        (∀ id, id < state.next →
          (state.freshMany level count).1.solutions.levelOf id =
            state.solutions.levelOf id) := by
    intro count
    induction count with
    | zero =>
        intro state safe
        simp only [InferState.freshMany]
        exact ⟨safe, by simp, by simp, rfl, le_rfl, by
          intro id hid
          trivial⟩
    | succ count ih =>
        intro state safe
        have first := InferState.fresh_safe (level := level) safe
        have rest := ih (state.fresh level).1 first.1
        have headLevel : (state.fresh level).2.LevelBounded
            (InferState.freshMany level count (state.fresh level).1).1.solutions level :=
          Ty.LevelBounded.congr first.2.2.1 (fun id member =>
            rest.2.2.2.2.2 id (first.2.1.2 id member))
        simp only [InferState.freshMany]
        refine ⟨rest.1, ?_, ?_, ?_,
          le_trans first.2.2.2.1 rest.2.2.2.2.1, ?_⟩
        · intro ty member
          simp only [List.mem_cons] at member
          rcases member with rfl | member
          · exact inferWF_mono first.2.1 rest.2.2.2.2.1
          · exact rest.2.1 ty member
        · intro ty member
          simp only [List.mem_cons] at member
          rcases member with rfl | member
          · exact headLevel
          · exact rest.2.2.1 ty member
        · simp [rest.2.2.2.1]
        · intro id hid
          rw [rest.2.2.2.2.2 id (lt_of_lt_of_le hid first.2.2.2.1)]
          exact first.2.2.2.2 id hid
  exact main count state safe

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
    | app function argument ihFunction ihArgument =>
        intro holes start
        simp only [Template.allocateWith]
        exact le_trans (ihFunction holes start)
          (ihArgument holes (function.allocateWith holes start).1)
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
    | con => rfl
    | app _ _ ihFunction ihArgument => simp [Ty.mvars, ihFunction, ihArgument]
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
    | app function argument ihFunction ihArgument =>
        cases hs with
        | app hFunction hArgument =>
          have functionCover : ∀ name ∈ function.names,
              ∃ ty, holes.lookup name = some ty := by
            intro name hmem
            exact hcover name (List.mem_append_left _ hmem)
          obtain ⟨hFunctionNext, hFunctionBounds⟩ :=
            ihFunction hFunction hholes functionCover hcurrent
          have holesLater :
              ∀ entry ∈ holes, ∀ id ∈ entry.2.mvars,
                frontier ≤ id ∧
                  id < (function.allocateWith holes current).1 := by
            intro entry hentry id hid
            obtain ⟨hbase, hlt⟩ := hholes entry hentry id hid
            exact ⟨hbase, lt_of_lt_of_le hlt hFunctionNext⟩
          have argumentCover : ∀ name ∈ argument.names,
              ∃ ty, holes.lookup name = some ty := by
            intro name hmem
            exact hcover name (List.mem_append_right _ hmem)
          obtain ⟨hArgumentNext, hArgumentBounds⟩ :=
            ihArgument hArgument holesLater argumentCover
              (le_trans hcurrent hFunctionNext)
          constructor
          · exact le_trans hFunctionNext hArgumentNext
          · intro id hmem
            simp only [Template.allocateWith, Ty.mvars,
              List.mem_dedup, List.mem_append] at hmem ⊢
            rcases hmem with hmem | hmem
            · obtain ⟨hbase, hlt⟩ := hFunctionBounds id hmem
              exact ⟨hbase, lt_of_lt_of_le hlt hArgumentNext⟩
            · exact hArgumentBounds id hmem
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
    {state : InferState} {template : Template} {level rigidCount : Nat}
    (safe : state.Safe)
    (templateScoped : template.Scoped rigidCount 0) :
    (state.allocate level template).1.Safe ∧
      (state.allocate level template).2.InferWF rigidCount 0
        (state.allocate level template).1.next ∧
      (state.allocate level template).2.LevelBounded
        (state.allocate level template).1.solutions level ∧
      state.next ≤ (state.allocate level template).1.next ∧
      (∀ id, id < state.next →
        (state.allocate level template).1.solutions.levelOf id =
          state.solutions.levelOf id) := by
  simp only [InferState.allocate]
  let allocation := template.allocate state.next
  let count := allocation.next - state.next
  have nextLe : state.next ≤ allocation.next :=
    Template.allocate_next_le template state.next
  have countEq : state.next + count = allocation.next := by
    simp only [count]
    omega
  have lengthEq : state.solutions.length = state.next := safe.solutions_length
  have boundedLength : state.solutions.Bounded state.solutions.length := by
    simpa [lengthEq] using safe.solutionsBounded
  have unsolvedNew :
      ∀ entry ∈ (List.replicate count (⟨level, none⟩ : MEntry)),
        entry.solution = none := by
    intro entry member
    simp only [List.mem_replicate] at member
    rw [member.2]
  have newSafe :
      ({ next := allocation.next,
          solutions := state.solutions ++
            List.replicate count (⟨level, none⟩ : MEntry) } :
        InferState).Safe := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · simp [safe.solutions_length, countEq]
    · exact MStore.leveled_append_unsolved safe.solutionsLeveled
        boundedLength unsolvedNew
    · intro id ty lookup m member
      have := MStore.bounded_append_unsolved safe.solutionsBounded
        unsolvedNew id ty lookup m member
      show m < allocation.next
      omega
    · exact MStore.normalized_append_unsolved safe.solutionsNormalized
        boundedLength unsolvedNew
  refine ⟨?_, ?_, ?_, nextLe, ?_⟩
  · simpa [allocation, count] using newSafe
  · constructor
    · exact Template.allocate_scoped templateScoped
    · intro id member
      exact (Template.allocate_mvars templateScoped id member).2
  · intro id member
    obtain ⟨hbase, hbound⟩ := Template.allocate_mvars templateScoped id member
    have := MStore.levelOf_append_replicate (store := state.solutions)
      (count := count) (level := level) (id := id)
      (by simpa [lengthEq] using hbase)
      (by rw [lengthEq, countEq]; exact hbound)
    simpa [allocation, count] using this.le
  · intro id hid
    exact MStore.levelOf_append_left (store := state.solutions)
      (extra := List.replicate count (⟨level, none⟩ : MEntry))
      (by simpa [safe.solutions_length] using hid)

/-- Constraining two allocated, scoped types preserves state safety, makes the
equation true in the resulting dense solution table, and only lowers levels. -/
theorem InferState.constrain_safe
    {state checked : InferState} {left right : Ty} {rigidCount : Nat}
    (safe : state.Safe)
    (leftWF : left.InferWF rigidCount 0 state.next)
    (rightWF : right.InferWF rigidCount 0 state.next)
    (run : state.constrain left right = some checked) :
    checked.Safe ∧
      checked.next = state.next ∧
      checked.solutions.apply left = checked.solutions.apply right ∧
      (∀ id, checked.solutions.levelOf id ≤ state.solutions.levelOf id) := by
  unfold InferState.constrain at run
  cases hunify : state.solutions.unify left right with
  | none => simp [hunify] at run
  | some solutions =>
      simp only [hunify, Option.map_some, Option.some.injEq] at run
      subst checked
      refine ⟨?_, rfl, ?_, ?_⟩
      · exact ⟨by rw [MStore.unify_length hunify, safe.solutions_length],
          MStore.unify_leveled safe.solutionsLeveled
            safe.solutionsNormalized hunify,
          MStore.unify_bounded safe.solutionsBounded
            leftWF.2 rightWF.2 hunify,
          MStore.unify_normalized safe.solutionsNormalized hunify⟩
      · exact MStore.unify_apply_eq safe.solutionsNormalized hunify
      · exact MStore.unify_levelOf_le hunify

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
  | con id => exact .con id
  | app _ _ ihFunction ihArgument =>
      exact .app ihFunction ihArgument

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
  | con => exact .con
  | app _ _ ihFunction ihArgument => exact .app ihFunction ihArgument

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
  | app _ _ ihFunction ihArgument =>
      exact .app ihFunction ihArgument

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
  | const c => exact .const

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
  | app _ _ ihFunction ihArgument =>
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

/-- Every metavariable of an opened type comes from the body or one of the
substituted arguments. -/
private theorem Ty.mem_mvars_openWith {ty : Ty} {args : List Ty} {id : Nat}
    (member : id ∈ (ty.openWith args).mvars) :
    id ∈ ty.mvars ∨ ∃ arg ∈ args, id ∈ arg.mvars := by
  induction ty with
  | prim name => simp [Ty.openWith, Ty.mvars] at member
  | arrow domain codomain ihDomain ihCodomain =>
      simp only [Ty.openWith, Ty.mvars, List.mem_dedup, List.mem_append] at member
      rcases member with member | member
      · rcases ihDomain member with old | new
        · exact Or.inl (by simp [Ty.mvars, List.mem_dedup, old])
        · exact Or.inr new
      · rcases ihCodomain member with old | new
        · exact Or.inl (by simp [Ty.mvars, List.mem_dedup, old])
        · exact Or.inr new
  | bvar index =>
      simp only [Ty.openWith] at member
      cases hget : args[index]? with
      | none => simp [hget, Ty.mvars] at member
      | some arg =>
          simp only [hget, Option.getD_some] at member
          exact Or.inr ⟨arg, List.mem_of_getElem? hget, member⟩
  | rigid level => simp [Ty.openWith, Ty.mvars] at member
  | mvar id' =>
      exact Or.inl (by simpa [Ty.openWith, Ty.mvars] using member)
  | con => simp [Ty.openWith, Ty.mvars] at member
  | app function argument ihFunction ihArgument =>
      simp only [Ty.openWith, Ty.mvars, List.mem_dedup, List.mem_append] at member
      rcases member with member | member
      · rcases ihFunction member with old | new
        · exact Or.inl (by simp [Ty.mvars, List.mem_dedup, old])
        · exact Or.inr new
      · rcases ihArgument member with old | new
        · exact Or.inl (by simp [Ty.mvars, List.mem_dedup, old])
        · exact Or.inr new

/-- Opening a scheme body by argument types preserves level bounds when both
the body and every argument satisfy the same bound. -/
private theorem Ty.openWith_levelBounded
    {ty : Ty} {args : List Ty} {store : MStore} {level : Nat}
    (bodyBounded : ty.LevelBounded store level)
    (argsBounded : ∀ arg ∈ args, arg.LevelBounded store level) :
    (ty.openWith args).LevelBounded store level := by
  intro id member
  rcases Ty.mem_mvars_openWith member with old | ⟨arg, argMem, argMember⟩
  · exact bodyBounded id old
  · exact argsBounded arg argMem id argMember

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

/-- Inference preserves state safety, returns an allocated type scoped and
levelled at the current rigid count, never moves the frontier backwards, and
only ever lowers the levels of existing metavariables. -/
theorem inferFuel_safe
    {fuel rigidCount : Nat} {ctx : Ctx} {input : Source}
    {state : InferState} {result : InferResult}
    (stateSafe : state.Safe)
    (ctxWF : ctx.InferWF rigidCount state.next)
    (ctxLevels : ∀ scheme ∈ ctx, scheme.body.LevelBounded state.solutions rigidCount)
    (inputScoped : input.TypeScoped rigidCount 0)
    (run : inferFuel sig fuel rigidCount ctx input state = some result) :
    result.state.Safe ∧
      result.ty.InferWF rigidCount 0 result.state.next ∧
      result.ty.LevelBounded result.state.solutions rigidCount ∧
      state.next ≤ result.state.next ∧
      ∀ id, id < state.next →
        result.state.solutions.levelOf id ≤ state.solutions.levelOf id := by
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
    | con id => exact .con id
    | app _ _ ihFunction ihArgument => exact .app ihFunction ihArgument
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
    | con => simp [Ty.MVarBounded, Ty.mvars]
    | app _ _ ihFunction ihArgument =>
        intro id member
        simp only [Ty.mvars, List.mem_dedup, List.mem_append] at member
        exact member.elim (ihFunction id) (ihArgument id)
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
    | con id =>
        exact ⟨.con id, by simp [Ty.openWith, Ty.MVarBounded, Ty.mvars]⟩
    | app function argument ihFunction ihArgument =>
        cases typeWF.1 with
        | app functionScoped argumentScoped =>
          have functionWF : function.InferWF rigid count frontier :=
            ⟨functionScoped, fun id member => typeWF.2 id (by
              simp [Ty.mvars, member])⟩
          have argumentWF : argument.InferWF rigid count frontier :=
            ⟨argumentScoped, fun id member => typeWF.2 id (by
              simp [Ty.mvars, member])⟩
          have functionResult := ihFunction functionWF
          have argumentResult := ihArgument argumentWF
          exact ⟨Ty.Scoped.app functionResult.1 argumentResult.1,
            by
              intro id member
              simp only [Ty.openWith, Ty.mvars, List.mem_dedup,
                List.mem_append] at member
              rcases member with member | member
              · exact functionResult.2 id member
              · exact argumentResult.2 id member⟩
  induction fuel generalizing rigidCount ctx input state result with
  | zero => simp [inferFuel] at run
  | succ fuel ih =>
      cases input with
      | primLit literal =>
          simp only [inferFuel, Option.some.injEq] at run
          subst result
          refine ⟨stateSafe, ?_, ?_, le_rfl, ?_⟩
          · cases literal <;> exact wf_inferWF ⟨.prim, .prim⟩
          · cases literal <;>
              (intro id member; simp [Ty.mvars, PrimLit.ty] at member)
          · intro id hid
            exact le_rfl
      | primOp op =>
          cases hty : op.ty sig with
          | none => simp [inferFuel, hty] at run
          | some primTy =>
              simp [inferFuel, hty] at run
              subst result
              refine ⟨stateSafe, ?_, ?_, le_rfl, ?_⟩
              · exact wf_inferWF (primOpTy_wf (rigidCount := rigidCount) hty)
              · intro id member
                have hbound := metaFree_bounded
                  (primOpTy_wf (rigidCount := 0) hty).2 (frontier := 0) id member
                omega
              · intro id hid
                exact le_rfl
      | var index =>
          simp only [inferFuel] at run
          cases lookup : ctx[index]? with
          | none => simp [lookup] at run
          | some scheme =>
              simp only [lookup] at run
              have schemeMember : scheme ∈ ctx := List.mem_of_getElem? lookup
              have schemeWF := ctxWF scheme schemeMember
              have schemeLevels := ctxLevels scheme schemeMember
              have applied := MStore.apply_inferWF stateSafe.solutionsLeveled
                stateSafe.solutionsBounded schemeWF schemeLevels
              let fresh := state.freshMany rigidCount scheme.paramCount
              have freshSafe := InferState.freshMany_safe
                (level := rigidCount) (count := scheme.paramCount) stateSafe
              have appliedMono :
                  (state.solutions.applyScheme scheme).InferWF
                    rigidCount fresh.1.next :=
                inferWF_mono applied.1 freshSafe.2.2.2.2.1
              have appliedLevels :
                  (state.solutions.apply scheme.body).LevelBounded
                    fresh.1.solutions rigidCount :=
                Ty.LevelBounded.congr applied.2 (fun id member =>
                  freshSafe.2.2.2.2.2 id (applied.1.2 id member))
              have openedWF :
                  ((state.solutions.applyScheme scheme).openWith fresh.2).InferWF
                    rigidCount 0 fresh.1.next :=
                openWith_inferWF appliedMono freshSafe.2.2.2.1 freshSafe.2.1
              have openedLevels :
                  ((state.solutions.applyScheme scheme).openWith fresh.2).LevelBounded
                    fresh.1.solutions rigidCount :=
                Ty.openWith_levelBounded appliedLevels freshSafe.2.2.1
              have resultEq : result =
                  ⟨fresh.1, (state.solutions.applyScheme scheme).openWith fresh.2,
                    .var index⟩ := by
                exact Option.some.inj run.symm
              subst result
              exact ⟨freshSafe.1, openedWF, openedLevels,
                freshSafe.2.2.2.2.1,
                fun id hid => le_of_eq (freshSafe.2.2.2.2.2 id hid)⟩
      | lambda ann body =>
          cases inputScoped with
          | lambda annScoped bodyScoped =>
            cases ann with
            | none =>
                simp only [inferFuel] at run
                let seeded := state.fresh rigidCount
                have seededSafe := InferState.fresh_safe
                  (level := rigidCount) stateSafe
                have bodyCtxWF :
                    Ctx.InferWF (PolyTy.mono seeded.2 :: ctx)
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
                    simp [bodyRun] at run
                    have bodySafe := ih seededSafe.1 bodyCtxWF bodyCtxLevels
                      bodyScoped bodyRun
                    have paramBefore : seeded.2.InferWF rigidCount 0
                        bodyResult.state.next :=
                      inferWF_mono seededSafe.2.1 bodySafe.2.2.2.1
                    have paramLevels : seeded.2.LevelBounded
                        bodyResult.state.solutions rigidCount :=
                      Ty.LevelBounded.mono_le_on seededSafe.2.2.1 (fun id member =>
                        bodySafe.2.2.2.2 id (seededSafe.2.1.2 id member))
                    have paramAfter := MStore.apply_inferWF
                      bodySafe.1.solutionsLeveled bodySafe.1.solutionsBounded
                      paramBefore paramLevels
                    have resultEq : result =
                        ⟨bodyResult.state,
                          .arrow (bodyResult.state.solutions.apply seeded.2)
                            bodyResult.ty,
                          .lambda (some seeded.2) bodyResult.elaborated⟩ := by
                      simpa [seeded] using run.symm
                    subst result
                    refine ⟨bodySafe.1,
                      ⟨.arrow paramAfter.1.1 bodySafe.2.1.1,
                        by
                          intro id member
                          simp only [Ty.mvars, List.mem_dedup,
                            List.mem_append] at member
                          rcases member with member | member
                          · exact paramAfter.1.2 id member
                          · exact bodySafe.2.1.2 id member⟩,
                      by
                        intro id member
                        simp only [Ty.mvars, List.mem_dedup,
                          List.mem_append] at member
                        rcases member with member | member
                        · exact paramAfter.2 id member
                        · exact bodySafe.2.2.1 id member,
                      le_trans seededSafe.2.2.2.1 bodySafe.2.2.2.1,
                      ?_⟩
                    intro id hid
                    have hidSeeded : id < seeded.1.next :=
                      lt_of_lt_of_le hid seededSafe.2.2.2.1
                    exact le_trans (bodySafe.2.2.2.2 id hidSeeded)
                      (le_of_eq (seededSafe.2.2.2.2 id hid))
            | some template =>
                have templateScoped := annScoped template rfl
                simp only [inferFuel] at run
                let seeded := state.allocate rigidCount template
                have seededSafe := InferState.allocate_safe
                  (level := rigidCount) (rigidCount := rigidCount)
                  stateSafe templateScoped
                have bodyCtxWF :
                    Ctx.InferWF (PolyTy.mono seeded.2 :: ctx)
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
                    simp [bodyRun] at run
                    have bodySafe := ih seededSafe.1 bodyCtxWF bodyCtxLevels
                      bodyScoped bodyRun
                    have paramBefore : seeded.2.InferWF rigidCount 0
                        bodyResult.state.next :=
                      inferWF_mono seededSafe.2.1 bodySafe.2.2.2.1
                    have paramLevels : seeded.2.LevelBounded
                        bodyResult.state.solutions rigidCount :=
                      Ty.LevelBounded.mono_le_on seededSafe.2.2.1 (fun id member =>
                        bodySafe.2.2.2.2 id (seededSafe.2.1.2 id member))
                    have paramAfter := MStore.apply_inferWF
                      bodySafe.1.solutionsLeveled bodySafe.1.solutionsBounded
                      paramBefore paramLevels
                    have resultEq : result =
                        ⟨bodyResult.state,
                          .arrow (bodyResult.state.solutions.apply seeded.2)
                            bodyResult.ty,
                          .lambda (some seeded.2) bodyResult.elaborated⟩ := by
                      simpa [seeded] using run.symm
                    subst result
                    refine ⟨bodySafe.1,
                      ⟨.arrow paramAfter.1.1 bodySafe.2.1.1,
                        by
                          intro id member
                          simp only [Ty.mvars, List.mem_dedup,
                            List.mem_append] at member
                          rcases member with member | member
                          · exact paramAfter.1.2 id member
                          · exact bodySafe.2.1.2 id member⟩,
                      by
                        intro id member
                        simp only [Ty.mvars, List.mem_dedup,
                          List.mem_append] at member
                        rcases member with member | member
                        · exact paramAfter.2 id member
                        · exact bodySafe.2.2.1 id member,
                      le_trans seededSafe.2.2.2.1 bodySafe.2.2.2.1,
                      ?_⟩
                    intro id hid
                    have hidSeeded : id < seeded.1.next :=
                      lt_of_lt_of_le hid seededSafe.2.2.2.1
                    exact le_trans (bodySafe.2.2.2.2 id hidSeeded)
                      (le_of_eq (seededSafe.2.2.2.2 id hid))
      | app function argument =>
          cases inputScoped with
          | app functionScoped argumentScoped =>
            simp only [inferFuel] at run
            cases functionRun : inferFuel sig fuel rigidCount ctx function state with
            | none => simp [functionRun] at run
            | some functionResult =>
                have functionSafe := ih stateSafe ctxWF ctxLevels
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
                    have argumentSafe := ih functionSafe.1 argumentCtxWF
                      argumentCtxLevels argumentScoped argumentRun
                    let fresh := argumentResult.state.fresh rigidCount
                    have freshSafe := InferState.fresh_safe
                      (level := rigidCount) argumentSafe.1
                    have functionTyWF : functionResult.ty.InferWF rigidCount 0
                        fresh.1.next :=
                      inferWF_mono functionSafe.2.1
                        (le_trans argumentSafe.2.2.2.1 freshSafe.2.2.2.1)
                    have argumentTyWF : argumentResult.ty.InferWF rigidCount 0
                        fresh.1.next :=
                      inferWF_mono argumentSafe.2.1 freshSafe.2.2.2.1
                    have functionTyLevels : functionResult.ty.LevelBounded
                        fresh.1.solutions rigidCount := by
                      intro id hid
                      have hidFunction : id < functionResult.state.next :=
                        functionSafe.2.1.2 id hid
                      have hidArgument : id < argumentResult.state.next :=
                        lt_of_lt_of_le hidFunction argumentSafe.2.2.2.1
                      calc fresh.1.solutions.levelOf id
                          = argumentResult.state.solutions.levelOf id :=
                            freshSafe.2.2.2.2 id hidArgument
                        _ ≤ functionResult.state.solutions.levelOf id :=
                            argumentSafe.2.2.2.2 id hidFunction
                        _ ≤ rigidCount := functionSafe.2.2.1 id hid
                    have argumentTyLevels : argumentResult.ty.LevelBounded
                        fresh.1.solutions rigidCount := by
                      intro id hid
                      have hidArgument : id < argumentResult.state.next :=
                        argumentSafe.2.1.2 id hid
                      calc fresh.1.solutions.levelOf id
                          = argumentResult.state.solutions.levelOf id :=
                            freshSafe.2.2.2.2 id hidArgument
                        _ ≤ rigidCount := argumentSafe.2.2.1 id hid
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
                    have arrowLevels :
                        (Ty.arrow argumentResult.ty fresh.2).LevelBounded
                          fresh.1.solutions rigidCount := by
                      intro id member
                      simp only [Ty.mvars, List.mem_dedup,
                        List.mem_append] at member
                      rcases member with member | member
                      · exact argumentTyLevels id member
                      · exact freshSafe.2.2.1 id member
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
                        have freshLevelsAtChecked : fresh.2.LevelBounded
                            checked.solutions rigidCount :=
                          Ty.LevelBounded.mono_le freshSafe.2.2.1
                            (fun id => checkedSafe.2.2.2 id)
                        have resultApplied := MStore.apply_inferWF
                          checkedSafe.1.solutionsLeveled
                          checkedSafe.1.solutionsBounded
                          freshTyAtChecked freshLevelsAtChecked
                        have resultEq : result =
                            ⟨checked, checked.solutions.apply fresh.2,
                              .app functionResult.elaborated
                                argumentResult.elaborated⟩ := by
                          simpa [fresh] using run.symm
                        subst result
                        refine ⟨checkedSafe.1, resultApplied.1,
                          resultApplied.2, ?_, ?_⟩
                        · rw [checkedSafe.2.1]
                          exact le_trans functionSafe.2.2.2.1
                            (le_trans argumentSafe.2.2.2.1 freshSafe.2.2.2.1)
                        · intro id hid
                          have hidFunction : id < functionResult.state.next :=
                            lt_of_lt_of_le hid functionSafe.2.2.2.1
                          have hidArgument : id < argumentResult.state.next :=
                            lt_of_lt_of_le hidFunction argumentSafe.2.2.2.1
                          have hidFresh : id < fresh.1.next :=
                            lt_of_lt_of_le hidArgument freshSafe.2.2.2.1
                          exact le_trans (checkedSafe.2.2.2 id)
                            (le_trans (le_of_eq (freshSafe.2.2.2.2 id hidArgument))
                              (le_trans (argumentSafe.2.2.2.2 id hidFunction)
                                (functionSafe.2.2.2.2 id hid)))
      | letIn ann rhs body =>
          cases ann with
          | none =>
              cases inputScoped with
              | letMono rhsScoped bodyScoped =>
                simp only [inferFuel] at run
                cases rhsRun : inferFuel sig fuel rigidCount ctx rhs state with
                | none => simp [rhsRun] at run
                | some rhsResult =>
                    have rhsSafe := ih stateSafe ctxWF ctxLevels rhsScoped rhsRun
                    let rhsTy := rhsResult.state.solutions.apply rhsResult.ty
                    have rhsApplied := MStore.apply_inferWF
                      rhsSafe.1.solutionsLeveled rhsSafe.1.solutionsBounded
                      rhsSafe.2.1 rhsSafe.2.2.1
                    have rhsTyWF : rhsTy.InferWF rigidCount 0
                        rhsResult.state.next := rhsApplied.1
                    have rhsTyLevels : rhsTy.LevelBounded
                        rhsResult.state.solutions rigidCount := rhsApplied.2
                    have bodyCtxWF :
                        Ctx.InferWF (PolyTy.mono rhsTy :: ctx)
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
                    | none =>
                        simp [rhsTy, rhsRun, bodyRun] at run
                    | some bodyResult =>
                        have bodySafe := ih rhsSafe.1 bodyCtxWF bodyCtxLevels
                          bodyScoped bodyRun
                        simp [rhsTy, rhsRun, bodyRun] at run
                        have resultEq : result =
                            ⟨bodyResult.state, bodyResult.ty,
                              .letIn none rhsResult.elaborated
                                bodyResult.elaborated⟩ := by
                          exact run.symm
                        subst result
                        refine ⟨bodySafe.1, bodySafe.2.1, bodySafe.2.2.1,
                          le_trans rhsSafe.2.2.2.1 bodySafe.2.2.2.1, ?_⟩
                        intro id hid
                        have hidRhs : id < rhsResult.state.next :=
                          lt_of_lt_of_le hid rhsSafe.2.2.2.1
                        exact le_trans (bodySafe.2.2.2.2 id hidRhs)
                          (rhsSafe.2.2.2.2 id hid)
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
                    have rhsSafe := ih seededSafe.1 rhsCtxWF rhsCtxLevels
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
                        have completedBodyScoped :
                            completed.body.Scoped rigidCount count := by
                          simpa [completed, inner] using
                            Ty.closeRigids_scoped_zero completedOpenApplied.1.1
                        have completedBodyBounded :
                            completed.body.MVarBounded checked.next := by
                          simpa [completed] using
                            Ty.closeRigids_mvarBounded completedOpenApplied.1.2
                        have completedWF : completed.InferWF rigidCount checked.next :=
                          ⟨completedBodyScoped, completedBodyBounded⟩
                        have completedOpenLevels : completedOpen.LevelBounded
                            checked.solutions rigidCount := by
                          simpa [Ty.LevelBounded] using (List.all_eq_true.mp good)
                        have completedLevels : completed.body.LevelBounded
                            checked.solutions rigidCount := by
                          simpa [completed] using
                            Ty.closeRigids_levelBounded completedOpenLevels
                        have bodyCtxWF : Ctx.InferWF (completed :: ctx)
                            rigidCount checked.next := by
                          intro scheme member
                          simp only [List.mem_cons] at member
                          rcases member with rfl | member
                          · exact completedWF
                          · exact ctx_mono ctxWF localStartLe scheme member
                        have bodyCtxLevels :
                            ∀ scheme ∈ completed :: ctx,
                              scheme.body.LevelBounded
                                checked.solutions rigidCount := by
                          intro scheme member
                          simp only [List.mem_cons] at member
                          rcases member with rfl | member
                          · exact completedLevels
                          · intro id hid
                            have idBound : id < state.next :=
                              (ctxWF scheme member).2 id hid
                            exact le_trans (checkedLevelLeState id idBound)
                              (ctxLevels scheme member id hid)
                        cases bodyRun : inferFuel sig fuel rigidCount
                            (completed :: ctx) body checked with
                        | none =>
                            simp [completed, completedOpen, count, inner,
                              seeded, openedTemplate, bodyRun] at run
                        | some bodyResult =>
                            have bodySafe := ih checkedSafe.1 bodyCtxWF
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
                            refine ⟨bodySafe.1, bodySafe.2.1,
                              bodySafe.2.2.1,
                              le_trans localStartLe bodySafe.2.2.2.1, ?_⟩
                            intro id hid
                            have hidChecked : id < checked.next :=
                              lt_of_lt_of_le hid localStartLe
                            exact le_trans (bodySafe.2.2.2.2 id hidChecked)
                              (checkedLevelLeState id hid)
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
                have bodySafe := ih seededSafe.1 bodyCtxWF bodyCtxLevels
                  bodyScoped bodyRun
                have selfAtBody : seeded.2.InferWF rigidCount 0
                    bodyResult.state.next :=
                  inferWF_mono seededSafe.2.1 bodySafe.2.2.2.1
                have selfLevelsBody : seeded.2.LevelBounded
                    bodyResult.state.solutions rigidCount :=
                  Ty.LevelBounded.mono_le_on seededSafe.2.2.1 (fun id member =>
                    bodySafe.2.2.2.2 id (seededSafe.2.1.2 id member))
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
                    have selfLevelsChecked : seeded.2.LevelBounded
                        checked.solutions rigidCount :=
                      Ty.LevelBounded.mono_le selfLevelsBody
                        (fun id => checkedSafe.2.2.2 id)
                    have resultApplied := MStore.apply_inferWF
                      checkedSafe.1.solutionsLeveled
                      checkedSafe.1.solutionsBounded
                      selfAtChecked selfLevelsChecked
                    have resultEq : result =
                        ⟨checked, checked.solutions.apply seeded.2,
                          .fix seeded.2 bodyResult.elaborated⟩ := by
                      simpa [seeded] using run.symm
                    subst result
                    refine ⟨checkedSafe.1, resultApplied.1,
                      resultApplied.2, ?_, ?_⟩
                    · rw [checkedSafe.2.1]
                      exact le_trans seededSafe.2.2.2.1 bodySafe.2.2.2.1
                    · intro id hid
                      have hidSeeded : id < seeded.1.next :=
                        lt_of_lt_of_le hid seededSafe.2.2.2.1
                      exact le_trans (checkedSafe.2.2.2 id)
                        (le_trans (bodySafe.2.2.2.2 id hidSeeded)
                          (le_of_eq (seededSafe.2.2.2.2 id hid)))
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
                  have freshSafe := InferState.freshMany_safe
                    (level := rigidCount) (count := scheme.paramCount) stateSafe
                  have bodyWF : scheme.body.InferWF rigidCount
                      scheme.paramCount fresh.1.next :=
                    wf_inferWF
                      ⟨scoped_mono_rigid schemeWF0.1 (Nat.zero_le rigidCount),
                        schemeWF0.2⟩
                  have bodyLevels : scheme.body.LevelBounded
                      fresh.1.solutions rigidCount := by
                    intro id member
                    have hlt := metaFree_bounded (frontier := 0)
                      schemeWF0.2 id member
                    omega
                  have openedWF : (scheme.openWith fresh.2).InferWF
                      rigidCount 0 fresh.1.next :=
                    openWith_inferWF bodyWF freshSafe.2.2.2.1 freshSafe.2.1
                  have openedLevels : (scheme.openWith fresh.2).LevelBounded
                      fresh.1.solutions rigidCount :=
                    Ty.openWith_levelBounded bodyLevels freshSafe.2.2.1
                  have resultEq : result =
                      ⟨fresh.1, scheme.openWith fresh.2, .const c⟩ := by
                    simpa [fresh, hb] using run.symm
                  subst result
                  exact ⟨freshSafe.1, openedWF, openedLevels,
                    freshSafe.2.2.2.2.1,
                    fun id hid => le_of_eq (freshSafe.2.2.2.2.2 id hid)⟩

end EPL
