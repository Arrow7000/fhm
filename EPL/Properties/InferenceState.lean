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
    {store : MStore} {rigidCount cutoff : Nat} :
    store.safeToLeave rigidCount cutoff = true ↔
      ∀ ty ∈ store,
        ty.Scoped rigidCount 0 ∧
          ∀ id ∈ ty.mvars, id < cutoff := by
  simp [MStore.safeToLeave, Ty.scopedB_eq_true_iff,
    Ty.mvarsBelow_eq_true_iff]

/-- Public obligation discharge is executable declarative well-formedness of
every required metavariable's solved image. -/
theorem InferState.solvedB_eq_true_iff
    {state : InferState} {rigidCount : Nat} :
    state.solvedB rigidCount = true ↔
      ∀ id ∈ state.required,
        (state.solutions.apply (.mvar id)).WF rigidCount 0 := by
  simp [InferState.solvedB, Ty.wfB_eq_true_iff]

/-- A lexical scheme boundary discharges precisely the obligations allocated
inside its local metavariable region. -/
theorem InferState.solvedFromB_eq_true_iff
    {state : InferState} {rigidCount cutoff : Nat} :
    state.solvedFromB rigidCount cutoff = true ↔
      ∀ id ∈ state.required, cutoff ≤ id →
        (state.solutions.apply (.mvar id)).WF rigidCount 0 := by
  simp only [InferState.solvedFromB, List.all_eq_true, Bool.or_eq_true,
    decide_eq_true_eq, Ty.wfB_eq_true_iff]
  constructor
  · intro hall id hmem hcutoff
    have := hall id hmem
    rcases this with hlt | hwf
    · omega
    · exact hwf
  · intro hall id hmem
    by_cases hlt : id < cutoff
    · exact Or.inl hlt
    · exact Or.inr (hall id hmem (by omega))

end EPL

namespace EPL

/-- Every metavariable in a type was allocated below `frontier`. -/
def Ty.MVarBounded (frontier : Nat) (ty : Ty) : Prop :=
  ∀ id ∈ ty.mvars, id < frontier

/-- Both the targets and images of a substitution stay inside the allocator's
current namespace. -/
def MSubst.Bounded (frontier : Nat) (subst : MSubst) : Prop :=
  ∀ binding ∈ subst,
    binding.1 < frontier ∧ binding.2.MVarBounded frontier

def Constraints.MVarBounded
    (frontier : Nat) (constraints : List Constraint) : Prop :=
  ∀ constraint ∈ constraints,
    constraint.1.MVarBounded frontier ∧
      constraint.2.MVarBounded frontier

theorem Ty.mvarBounded_iff_mvarsBelow
    {ty : Ty} {frontier : Nat} :
    ty.MVarBounded frontier ↔ ty.mvarsBelow frontier = true := by
  exact Ty.mvarsBelow_eq_true_iff.symm

/-- Fuelled unification never invents a metavariable outside the namespace of
its initial substitution and constraints. -/
theorem unifyFuel_bounded
    (initialBounded : initial.Bounded frontier)
    (constraintsBounded : Constraints.MVarBounded frontier constraints)
    (run : unifyFuel fuel constraints initial = some result) :
    result.Bounded frontier := by
  have substMVar_bounded :
      ∀ {ty replacement : Ty} {target : Nat},
        ty.MVarBounded frontier →
        replacement.MVarBounded frontier →
        (ty.substMVar target replacement).MVarBounded frontier := by
    intro ty replacement target typeBounded replacementBounded
    induction ty with
    | prim name => simp [Ty.MVarBounded, Ty.substMVar, Ty.mvars]
    | arrow domain codomain ihDomain ihCodomain =>
        have domainBounded : domain.MVarBounded frontier := by
          intro id member
          exact typeBounded id (by simp [Ty.mvars, member])
        have codomainBounded : codomain.MVarBounded frontier := by
          intro id member
          exact typeBounded id (by simp [Ty.mvars, member])
        intro id member
        simp only [Ty.substMVar, Ty.mvars, List.mem_dedup,
          List.mem_append] at member
        rcases member with member | member
        · exact ihDomain domainBounded id member
        · exact ihCodomain codomainBounded id member
    | bvar index => simp [Ty.MVarBounded, Ty.substMVar, Ty.mvars]
    | rigid level => simp [Ty.MVarBounded, Ty.substMVar, Ty.mvars]
    | mvar id =>
        simp only [Ty.substMVar]
        split
        · exact replacementBounded
        · intro candidate member
          simp only [Ty.mvars, List.mem_singleton] at member
          subst candidate
          exact typeBounded id (by simp [Ty.mvars])
  have apply_bounded :
      ∀ {subst : MSubst} {ty : Ty},
        subst.Bounded frontier →
        ty.MVarBounded frontier →
        (subst.apply ty).MVarBounded frontier := by
    intro subst ty substBounded typeBounded
    induction subst generalizing ty with
    | nil => simpa [MSubst.apply] using typeBounded
    | cons binding rest ih =>
        have bindingBounded := substBounded binding (by simp)
        have restBounded : MSubst.Bounded frontier rest := by
          intro item member
          exact substBounded item (by simp [member])
        simpa [MSubst.apply, List.foldl] using
          ih restBounded (substMVar_bounded typeBounded bindingBounded.2)
  have append_one_bounded :
      ∀ {subst : MSubst} {id : Nat} {ty : Ty},
        subst.Bounded frontier → id < frontier →
        ty.MVarBounded frontier →
        (subst ++ [(id, ty)]).Bounded frontier := by
    intro subst id ty substBounded idBounded typeBounded binding member
    rcases List.mem_append.mp member with old | new
    · exact substBounded binding old
    · simp only [List.mem_singleton] at new
      subst binding
      exact ⟨idBounded, typeBounded⟩
  have arrow_parts :
      ∀ {domain codomain : Ty},
        (Ty.arrow domain codomain).MVarBounded frontier →
        domain.MVarBounded frontier ∧ codomain.MVarBounded frontier := by
    intro domain codomain bounded
    constructor <;> intro id member
    · exact bounded id (by simp [Ty.mvars, member])
    · exact bounded id (by simp [Ty.mvars, member])
  induction fuel generalizing constraints initial result with
  | zero =>
      cases constraints with
      | nil =>
          simp only [unifyFuel, Option.some.injEq] at run
          subst result
          exact initialBounded
      | cons constraint rest => simp [unifyFuel] at run
  | succ fuel ih =>
      cases constraints with
      | nil =>
          simp only [unifyFuel, Option.some.injEq] at run
          subst result
          exact initialBounded
      | cons constraint rest =>
          rcases constraint with ⟨left, right⟩
          have inputBounded := constraintsBounded (left, right) (by simp)
          have restBounded : Constraints.MVarBounded frontier rest := by
            intro item member
            exact constraintsBounded item (List.mem_cons_of_mem _ member)
          have leftBounded := apply_bounded initialBounded inputBounded.1
          have rightBounded := apply_bounded initialBounded inputBounded.2
          simp only [unifyFuel] at run
          by_cases equal : initial.apply left = initial.apply right
          · rw [if_pos equal] at run
            exact ih initialBounded restBounded run
          · rw [if_neg equal] at run
            generalize leftEq : initial.apply left = left' at leftBounded run
            generalize rightEq : initial.apply right = right' at rightBounded run
            have bindCase (id : Nat) (assigned : Ty)
                (idBounded : id < frontier)
                (assignedBounded : assigned.MVarBounded frontier)
                (bindRun :
                  (if assigned.occursMVar id = true then none
                    else unifyFuel fuel rest (initial ++ [(id, assigned)])) =
                      some result) :
                result.Bounded frontier := by
              by_cases occurs : assigned.occursMVar id = true
              · simp [occurs] at bindRun
              · apply ih
                  (append_one_bounded initialBounded idBounded assignedBounded)
                  restBounded
                simpa [occurs] using bindRun
            cases left' with
            | prim leftPrim =>
                cases right' with
                | prim rightPrim => simp at run
                | arrow _ _ => simp at run
                | bvar _ => simp at run
                | rigid _ => simp at run
                | mvar id =>
                    exact bindCase id (.prim leftPrim)
                      (rightBounded id (by simp [Ty.mvars])) leftBounded run
            | arrow leftDomain leftCodomain =>
                cases right' with
                | prim _ => simp at run
                | arrow rightDomain rightCodomain =>
                    have leftParts := arrow_parts leftBounded
                    have rightParts := arrow_parts rightBounded
                    change unifyFuel fuel
                      ((leftDomain, rightDomain) ::
                        (leftCodomain, rightCodomain) :: rest) initial =
                          some result at run
                    apply ih (constraints :=
                      (leftDomain, rightDomain) ::
                        (leftCodomain, rightCodomain) :: rest) initialBounded
                    · intro item member
                      rcases List.mem_cons.mp member with first | member
                      · simpa [first] using
                          (And.intro leftParts.1 rightParts.1)
                      · rcases List.mem_cons.mp member with second | member
                        · simpa [second] using
                            (And.intro leftParts.2 rightParts.2)
                        · exact restBounded item member
                    · exact run
                | bvar _ => simp at run
                | rigid _ => simp at run
                | mvar id =>
                    exact bindCase id (.arrow leftDomain leftCodomain)
                      (rightBounded id (by simp [Ty.mvars])) leftBounded run
            | bvar leftIndex =>
                cases right' with
                | prim _ => simp at run
                | arrow _ _ => simp at run
                | bvar _ => simp at run
                | rigid _ => simp at run
                | mvar id =>
                    exact bindCase id (.bvar leftIndex)
                      (rightBounded id (by simp [Ty.mvars])) leftBounded run
            | rigid leftLevel =>
                cases right' with
                | prim _ => simp at run
                | arrow _ _ => simp at run
                | bvar _ => simp at run
                | rigid _ => simp at run
                | mvar id =>
                    exact bindCase id (.rigid leftLevel)
                      (rightBounded id (by simp [Ty.mvars])) leftBounded run
            | mvar id =>
                have idBounded : id < frontier :=
                  leftBounded id (by simp [Ty.mvars])
                cases right' with
                | prim rightPrim =>
                    exact bindCase id (.prim rightPrim) idBounded rightBounded run
                | arrow rightDomain rightCodomain =>
                    exact bindCase id (.arrow rightDomain rightCodomain)
                      idBounded rightBounded run
                | bvar rightIndex =>
                    exact bindCase id (.bvar rightIndex) idBounded rightBounded run
                | rigid rightLevel =>
                    exact bindCase id (.rigid rightLevel) idBounded rightBounded run
                | mvar rightId =>
                    exact bindCase id (.mvar rightId) idBounded rightBounded run

/-- Public unification preserves a common metavariable frontier. -/
theorem unify_bounded
    (leftBounded : left.MVarBounded frontier)
    (rightBounded : right.MVarBounded frontier)
    (run : unify left right = some result) :
    result.Bounded frontier := by
  apply unifyFuel_bounded (initial := [])
      (constraints := [(left, right)])
  · simp [MSubst.Bounded]
  · intro constraint member
    simp only [List.mem_singleton] at member
    subst constraint
    exact ⟨leftBounded, rightBounded⟩
  · exact run

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

def MStore.Scoped (store : MStore) (rigidCount : Nat) : Prop :=
  ∀ ty ∈ store, ty.Scoped rigidCount 0

def MStore.Bounded (store : MStore) (frontier : Nat) : Prop :=
  ∀ ty ∈ store, ty.MVarBounded frontier

def MStore.Normalized (store : MStore) : Prop :=
  ∀ ty ∈ store, store.apply ty = ty

/-- The dense solution table agrees with its allocation frontier, contains no
out-of-scope or forged type, and tracks only allocated obligations. -/
structure InferState.Safe (state : InferState) (rigidCount : Nat) : Prop where
  solutions_length : state.solutions.length = state.next
  solutionsScoped : state.solutions.Scoped rigidCount
  solutionsBounded : state.solutions.Bounded state.next
  solutionsNormalized : state.solutions.Normalized
  requiredBounded : ∀ id ∈ state.required, id < state.next

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
          simpa [MStore.apply, hget] using typeWF
      | some result =>
          have member : result ∈ store := List.mem_of_getElem? hget
          simpa [MStore.apply, hget] using
            And.intro (scoped_mono_binder (storeScoped result member))
              (storeBounded result member)

theorem InferState.initial_safe {rigidCount : Nat} :
    (⟨0, [], []⟩ : InferState).Safe rigidCount := by
  constructor <;> simp [MStore.Scoped, MStore.Bounded, MStore.Normalized]

theorem InferState.fresh_safe
    {state : InferState} {rigidCount : Nat}
    (safe : state.Safe rigidCount) :
    state.fresh.1.Safe rigidCount ∧
      state.fresh.2.InferWF rigidCount 0 state.fresh.1.next ∧
      state.next ≤ state.fresh.1.next := by
  rcases safe with ⟨length, storeScoped, bounded, normalized, required⟩
  have apply_append_identity :
      ∀ {ty : Ty}, ty.MVarBounded state.next →
        (state.solutions ++ [Ty.mvar state.next]).apply ty =
          state.solutions.apply ty := by
    intro ty typeBounded
    induction ty with
    | prim name => rfl
    | arrow domain codomain ihDomain ihCodomain =>
        simp only [MStore.apply]
        rw [ihDomain (by
          intro id member
          exact typeBounded id (by simp [Ty.mvars, member]))]
        rw [ihCodomain (by
          intro id member
          exact typeBounded id (by simp [Ty.mvars, member]))]
    | bvar index => rfl
    | rigid level => rfl
    | mvar id =>
        have idBounded : id < state.next :=
          typeBounded id (by simp [Ty.mvars])
        have idInSolutions : id < state.solutions.length := by
          simpa [length] using idBounded
        simp only [MStore.apply]
        rw [List.getElem?_append_left idInSolutions]
  simp only [InferState.fresh]
  refine ⟨?_, ?_, by omega⟩
  · refine ⟨by simp [length], ?_, ?_, ?_, ?_⟩
    · intro ty member
      rcases List.mem_append.mp member with old | new
      · exact storeScoped ty old
      · simp only [List.mem_singleton] at new
        subst ty
        exact .mvar _
    · intro ty member
      rcases List.mem_append.mp member with old | new
      · intro id idMember
        exact Nat.lt_succ_of_lt (bounded ty old id idMember)
      · simp only [List.mem_singleton] at new
        subst ty
        intro id idMember
        simp only [Ty.mvars, List.mem_singleton] at idMember
        subst id
        change state.next < state.next + 1
        omega
    · intro ty member
      rcases List.mem_append.mp member with old | new
      · rw [apply_append_identity (bounded ty old), normalized ty old]
      · simp only [List.mem_singleton] at new
        subst ty
        simp [MStore.apply, length]
    · intro id member
      exact Nat.lt_succ_of_lt (required id member)
  · exact ⟨.mvar _, by
      intro id member
      simp only [Ty.mvars, List.mem_singleton] at member
      subst id
      omega⟩

theorem InferState.freshRequired_safe
    {state : InferState} {rigidCount : Nat}
    (safe : state.Safe rigidCount) :
    state.freshRequired.1.Safe rigidCount ∧
      state.freshRequired.2.InferWF rigidCount 0
        state.freshRequired.1.next ∧
      state.next ≤ state.freshRequired.1.next := by
  have ordinary := InferState.fresh_safe safe
  refine ⟨?_, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [InferState.freshRequired, InferState.fresh] using
        ordinary.1.solutions_length
    · simpa [InferState.freshRequired, InferState.fresh] using
        ordinary.1.solutionsScoped
    · simpa [InferState.freshRequired, InferState.fresh] using
        ordinary.1.solutionsBounded
    · simpa [InferState.freshRequired, InferState.fresh] using
        ordinary.1.solutionsNormalized
    · intro id member
      simp only [InferState.freshRequired, List.mem_cons] at member ⊢
      rcases member with rfl | old
      · omega
      · exact Nat.lt_succ_of_lt (safe.requiredBounded id old)
  · simpa [InferState.freshRequired, InferState.fresh] using ordinary.2.1
  · simp [InferState.freshRequired]

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
  have rangeLength : (mvarRange state.next count).length = count := by
    simp [mvarRange]
  have rangeMember :
      ∀ ty ∈ mvarRange state.next count,
        ∃ offset < count, ty = .mvar (state.next + offset) := by
    intro ty hmem
    obtain ⟨id, hid, rfl⟩ := List.mem_map.mp hmem
    obtain ⟨offset, hlt, hid⟩ := List.mem_range'.mp hid
    subst id
    exact ⟨offset, hlt, by simp⟩
  have apply_append_of_bounded :
      ∀ {ty : Ty}, ty.MVarBounded state.solutions.length →
        (state.solutions ++ mvarRange state.next count).apply ty =
          state.solutions.apply ty := by
    intro ty bounded
    induction ty with
    | prim p => rfl
    | arrow domain codomain ihDomain ihCodomain =>
        simp only [MStore.apply]
        rw [ihDomain, ihCodomain]
        · intro id hmem
          exact bounded id (by simp [Ty.mvars, hmem])
        · intro id hmem
          exact bounded id (by simp [Ty.mvars, hmem])
    | bvar index => rfl
    | rigid level => rfl
    | mvar id =>
        simp only [MStore.apply]
        have hlt : id < state.solutions.length :=
          bounded id (by simp [Ty.mvars])
        rw [List.getElem?_append_left hlt]
  have rangeNormalized :
      ∀ ty ∈ mvarRange state.next count,
        (state.solutions ++ mvarRange state.next count).apply ty = ty := by
    intro ty hmem
    obtain ⟨offset, hlt, rfl⟩ := rangeMember ty hmem
    simp only [MStore.apply]
    rw [List.getElem?_append_right (by
      rw [safe.solutions_length]
      omega)]
    simp [mvarRange, safe.solutions_length, hlt]
  have newSafe :
      ({ next := allocation.next,
          solutions := state.solutions ++ mvarRange state.next count,
          required := List.range' state.next count ++ state.required } :
        InferState).Safe rigidCount := by
    constructor
    · simp [safe.solutions_length, rangeLength, countEq]
    · intro ty hmem
      rcases List.mem_append.mp hmem with hOld | hNew
      · exact safe.solutionsScoped ty hOld
      · obtain ⟨offset, _, rfl⟩ := rangeMember ty hNew
        exact .mvar _
    · intro ty hmem id hid
      rcases List.mem_append.mp hmem with hOld | hNew
      · have oldBound := safe.solutionsBounded ty hOld id hid
        exact lt_of_lt_of_le oldBound nextLe
      · obtain ⟨offset, hlt, rfl⟩ := rangeMember ty hNew
        simp only [Ty.mvars, List.mem_singleton] at hid
        subst id
        change state.next + offset < allocation.next
        omega
    · intro ty hmem
      rcases List.mem_append.mp hmem with hOld | hNew
      · rw [apply_append_of_bounded]
        · exact safe.solutionsNormalized ty hOld
        · intro id hid
          rw [safe.solutions_length]
          exact safe.solutionsBounded ty hOld id hid
      · exact rangeNormalized ty hNew
    · intro id hmem
      rcases List.mem_append.mp hmem with hNew | hOld
      · obtain ⟨offset, hlt, hid⟩ := List.mem_range'.mp hNew
        subst id
        change state.next + 1 * offset < allocation.next
        omega
      · exact lt_of_lt_of_le (safe.requiredBounded id hOld) nextLe
  refine ⟨?_, ?_, nextLe⟩
  · simpa [allocation, count] using newSafe
  · constructor
    · exact Template.allocate_scoped templateScoped
    · intro id hmem
      exact (Template.allocate_mvars templateScoped id hmem).2

/-- A solver run over store-normalized inputs preserves every allocated type
already fixed by that store. This is the sole compatibility contract between
the ordered unifier and inference's dense solution table. -/
theorem MStore.unify_preserves_fixed
    {store : MStore} {left right : Ty} {delta : MSubst} {frontier : Nat}
    (length : store.length = frontier)
    (storeBounded : store.Bounded frontier)
    (storeNormalized : store.Normalized)
    (leftBounded : left.MVarBounded frontier)
    (rightBounded : right.MVarBounded frontier)
    (run : unify (store.apply left) (store.apply right) = some delta) :
    ∀ ty, ty.MVarBounded frontier → store.apply ty = ty →
      store.apply (delta.apply ty) = delta.apply ty := by
  have _storeBounded := storeBounded
  have storeApplyFixed : ∀ {ty : Ty}, ty.MVarBounded frontier →
      store.apply (store.apply ty) = store.apply ty := by
    intro ty bounded
    induction ty with
    | prim name => rfl
    | arrow domain codomain ihDomain ihCodomain =>
        have domainBounded : domain.MVarBounded frontier := by
          intro id member
          exact bounded id (by simp [Ty.mvars, member])
        have codomainBounded : codomain.MVarBounded frontier := by
          intro id member
          exact bounded id (by simp [Ty.mvars, member])
        simp only [MStore.apply, ihDomain domainBounded, ihCodomain codomainBounded]
    | bvar index => rfl
    | rigid level => rfl
    | mvar id =>
        have idBounded : id < frontier := bounded id (by simp [Ty.mvars])
        have idInStore : id < store.length := by simpa [length] using idBounded
        rw [MStore.apply, List.getElem?_eq_getElem idInStore, Option.getD_some]
        exact storeNormalized store[id] (List.getElem_mem ..)
  have substMVarFixed : ∀ {ty replacement : Ty} {target : Nat},
      store.apply ty = ty → store.apply replacement = replacement →
        store.apply (ty.substMVar target replacement) =
          ty.substMVar target replacement := by
    intro ty replacement target typeFixed replacementFixed
    induction ty with
    | prim name => rfl
    | arrow domain codomain ihDomain ihCodomain =>
        simp only [MStore.apply, Ty.substMVar] at typeFixed ⊢
        injection typeFixed with domainFixed codomainFixed
        rw [ihDomain domainFixed, ihCodomain codomainFixed]
    | bvar index => rfl
    | rigid level => rfl
    | mvar id =>
        simp only [Ty.substMVar]
        split
        · exact replacementFixed
        · exact typeFixed
  have substApplyFixed : ∀ {subst : MSubst} {ty : Ty},
      (∀ binding ∈ subst, store.apply binding.2 = binding.2) →
      store.apply ty = ty →
      store.apply (subst.apply ty) = subst.apply ty := by
    intro subst ty substFixed typeFixed
    induction subst generalizing ty with
    | nil => simpa [MSubst.apply] using typeFixed
    | cons binding rest ih =>
        have replacementFixed : store.apply binding.2 = binding.2 :=
          substFixed binding (by simp)
        have restFixed : ∀ item ∈ rest, store.apply item.2 = item.2 := by
          intro item member
          exact substFixed item (by simp [member])
        simpa [MSubst.apply, List.foldl] using
          ih restFixed (substMVarFixed typeFixed replacementFixed)
  have unifyFuelFixed : ∀ {fuel : Nat} {constraints : List Constraint}
      {initial result : MSubst},
      (∀ binding ∈ initial, store.apply binding.2 = binding.2) →
      (∀ constraint ∈ constraints,
        store.apply constraint.1 = constraint.1 ∧
          store.apply constraint.2 = constraint.2) →
      unifyFuel fuel constraints initial = some result →
      ∀ binding ∈ result, store.apply binding.2 = binding.2 := by
    intro fuel
    induction fuel with
    | zero =>
        intro constraints initial result initialFixed constraintsFixed runFuel
        cases constraints with
        | nil =>
            simp only [unifyFuel, Option.some.injEq] at runFuel
            subst result
            exact initialFixed
        | cons constraint rest => simp [unifyFuel] at runFuel
    | succ fuel ih =>
        intro constraints initial result initialFixed constraintsFixed runFuel
        cases constraints with
        | nil =>
            simp only [unifyFuel, Option.some.injEq] at runFuel
            subst result
            exact initialFixed
        | cons constraint rest =>
            rcases constraint with ⟨constraintLeft, constraintRight⟩
            have headFixed := constraintsFixed
              (constraintLeft, constraintRight) (by simp)
            have restFixed : ∀ constraint ∈ rest,
                store.apply constraint.1 = constraint.1 ∧
                  store.apply constraint.2 = constraint.2 := by
              intro constraint member
              exact constraintsFixed constraint (List.mem_cons_of_mem _ member)
            have normalizedLeftFixed :
                store.apply (initial.apply constraintLeft) =
                  initial.apply constraintLeft :=
              substApplyFixed initialFixed headFixed.1
            have normalizedRightFixed :
                store.apply (initial.apply constraintRight) =
                  initial.apply constraintRight :=
              substApplyFixed initialFixed headFixed.2
            simp only [unifyFuel] at runFuel
            by_cases equal :
                initial.apply constraintLeft = initial.apply constraintRight
            · rw [if_pos equal] at runFuel
              exact ih initialFixed restFixed runFuel
            · rw [if_neg equal] at runFuel
              generalize leftEq : initial.apply constraintLeft = normalizedLeft at normalizedLeftFixed runFuel
              generalize rightEq : initial.apply constraintRight = normalizedRight at normalizedRightFixed runFuel
              have bindCase (id : Nat) (assigned : Ty)
                  (assignedFixed : store.apply assigned = assigned)
                  (bindRun :
                    (if assigned.occursMVar id = true then none
                      else unifyFuel fuel rest (initial ++ [(id, assigned)])) =
                        some result) :
                  ∀ binding ∈ result, store.apply binding.2 = binding.2 := by
                by_cases occurs : assigned.occursMVar id = true
                · simp [occurs] at bindRun
                · apply ih
                    (initial := initial ++ [(id, assigned)])
                    (result := result)
                  · intro binding member
                    rcases List.mem_append.mp member with old | new
                    · exact initialFixed binding old
                    · simp only [List.mem_singleton] at new
                      subst binding
                      exact assignedFixed
                  · exact restFixed
                  · simpa [occurs] using bindRun
              cases normalizedLeft with
              | prim leftPrim =>
                  cases normalizedRight with
                  | prim rightPrim => simp at runFuel
                  | arrow _ _ => simp at runFuel
                  | bvar _ => simp at runFuel
                  | rigid _ => simp at runFuel
                  | mvar id =>
                      exact bindCase id (.prim leftPrim) normalizedLeftFixed runFuel
              | arrow leftDomain leftCodomain =>
                  cases normalizedRight with
                  | prim _ => simp at runFuel
                  | arrow rightDomain rightCodomain =>
                      have leftParts := Ty.arrow.inj normalizedLeftFixed
                      have rightParts := Ty.arrow.inj normalizedRightFixed
                      have splitFixed : ∀ constraint ∈
                          ((leftDomain, rightDomain) ::
                            (leftCodomain, rightCodomain) :: rest),
                          store.apply constraint.1 = constraint.1 ∧
                            store.apply constraint.2 = constraint.2 := by
                        rintro ⟨a, b⟩ member
                        simp only [List.mem_cons, Prod.mk.injEq] at member
                        rcases member with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | inRest
                        · exact ⟨leftParts.1, rightParts.1⟩
                        · exact ⟨leftParts.2, rightParts.2⟩
                        · exact restFixed (a, b) inRest
                      exact ih initialFixed splitFixed runFuel
                  | bvar _ => simp at runFuel
                  | rigid _ => simp at runFuel
                  | mvar id =>
                      exact bindCase id (.arrow leftDomain leftCodomain)
                        normalizedLeftFixed runFuel
              | bvar leftIndex =>
                  cases normalizedRight with
                  | prim _ => simp at runFuel
                  | arrow _ _ => simp at runFuel
                  | bvar _ => simp at runFuel
                  | rigid _ => simp at runFuel
                  | mvar id =>
                      exact bindCase id (.bvar leftIndex) normalizedLeftFixed runFuel
              | rigid leftLevel =>
                  cases normalizedRight with
                  | prim _ => simp at runFuel
                  | arrow _ _ => simp at runFuel
                  | bvar _ => simp at runFuel
                  | rigid _ => simp at runFuel
                  | mvar id =>
                      exact bindCase id (.rigid leftLevel)
                        normalizedLeftFixed runFuel
              | mvar id =>
                  cases normalizedRight with
                  | prim rightPrim =>
                      exact bindCase id (.prim rightPrim)
                        normalizedRightFixed runFuel
                  | arrow rightDomain rightCodomain =>
                      exact bindCase id (.arrow rightDomain rightCodomain)
                        normalizedRightFixed runFuel
                  | bvar rightIndex =>
                      exact bindCase id (.bvar rightIndex)
                        normalizedRightFixed runFuel
                  | rigid rightLevel =>
                      exact bindCase id (.rigid rightLevel)
                        normalizedRightFixed runFuel
                  | mvar rightId =>
                      exact bindCase id (.mvar rightId)
                        normalizedRightFixed runFuel
  have deltaFixed : ∀ binding ∈ delta,
      store.apply binding.2 = binding.2 := by
    apply unifyFuelFixed
      (fuel := unifyBudget (store.apply left) (store.apply right))
      (constraints := [(store.apply left, store.apply right)])
      (initial := []) (result := delta)
    · simp
    · intro constraint member
      have constraintEq := List.mem_singleton.mp member
      cases constraintEq
      exact ⟨storeApplyFixed leftBounded, storeApplyFixed rightBounded⟩
    · simpa [unify] using run
  intro ty _ typeFixed
  exact substApplyFixed deltaFixed typeFixed

/-- Unifying types already normalized by a dense solution table and applying
the solver result pointwise produces another normalized table. -/
theorem MStore.map_unify_normalized
    {store : MStore} {left right : Ty} {delta : MSubst} {frontier : Nat}
    (length : store.length = frontier)
    (storeBounded : store.Bounded frontier)
    (storeNormalized : store.Normalized)
    (leftBounded : left.MVarBounded frontier)
    (rightBounded : right.MVarBounded frontier)
    (run : unify (store.apply left) (store.apply right) = some delta) :
    MStore.Normalized (store.map delta.apply) := by
  have storeApplyBounded : ∀ {ty : Ty}, ty.MVarBounded frontier →
      (store.apply ty).MVarBounded frontier := by
    intro ty bounded
    induction ty with
    | prim name => simp [MStore.apply, Ty.MVarBounded, Ty.mvars]
    | arrow domain codomain ihDomain ihCodomain =>
        have domainBounded : domain.MVarBounded frontier := by
          intro id member
          exact bounded id (by simp [Ty.mvars, member])
        have codomainBounded : codomain.MVarBounded frontier := by
          intro id member
          exact bounded id (by simp [Ty.mvars, member])
        intro id member
        simp only [MStore.apply, Ty.mvars, List.mem_dedup,
          List.mem_append] at member
        rcases member with member | member
        · exact ihDomain domainBounded id member
        · exact ihCodomain codomainBounded id member
    | bvar index => simp [MStore.apply, Ty.MVarBounded, Ty.mvars]
    | rigid level => simp [MStore.apply, Ty.MVarBounded, Ty.mvars]
    | mvar id =>
        have idBounded : id < frontier := bounded id (by simp [Ty.mvars])
        have idInStore : id < store.length := by simpa [length] using idBounded
        rw [MStore.apply, List.getElem?_eq_getElem idInStore, Option.getD_some]
        exact storeBounded store[id] (List.getElem_mem ..)
  have substMVarBounded : ∀ {ty replacement : Ty} {target : Nat},
      ty.MVarBounded frontier → replacement.MVarBounded frontier →
        (ty.substMVar target replacement).MVarBounded frontier := by
    intro ty replacement target typeBounded replacementBounded
    induction ty with
    | prim name => simpa [Ty.substMVar] using typeBounded
    | arrow domain codomain ihDomain ihCodomain =>
        have domainBounded : domain.MVarBounded frontier := by
          intro id member
          exact typeBounded id (by simp [Ty.mvars, member])
        have codomainBounded : codomain.MVarBounded frontier := by
          intro id member
          exact typeBounded id (by simp [Ty.mvars, member])
        intro id member
        simp only [Ty.substMVar, Ty.mvars, List.mem_dedup,
          List.mem_append] at member
        rcases member with member | member
        · exact ihDomain domainBounded id member
        · exact ihCodomain codomainBounded id member
    | bvar index => simpa [Ty.substMVar] using typeBounded
    | rigid level => simpa [Ty.substMVar] using typeBounded
    | mvar id =>
        simp only [Ty.substMVar]
        split
        · exact replacementBounded
        · exact typeBounded
  have substApplyBounded : ∀ {subst : MSubst} {ty : Ty},
      subst.Bounded frontier → ty.MVarBounded frontier →
        (subst.apply ty).MVarBounded frontier := by
    intro subst ty substBounded typeBounded
    induction subst generalizing ty with
    | nil => simpa [MSubst.apply] using typeBounded
    | cons binding rest ih =>
        have bindingBounded := substBounded binding (by simp)
        have restBounded : MSubst.Bounded frontier rest := by
          intro item member
          exact substBounded item (by simp [member])
        simpa [MSubst.apply, List.foldl] using
          ih restBounded (substMVarBounded typeBounded bindingBounded.2)
  have leftAppliedBounded := storeApplyBounded leftBounded
  have rightAppliedBounded := storeApplyBounded rightBounded
  have deltaBounded : delta.Bounded frontier :=
    unify_bounded leftAppliedBounded rightAppliedBounded run
  have deltaStable : delta.Stable := unify_stable run
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
  have mapApply : ∀ {ty : Ty}, ty.MVarBounded frontier →
      MStore.apply (store.map delta.apply) ty =
        delta.apply (store.apply ty) := by
    intro ty bounded
    induction ty with
    | prim name => simpa [MStore.apply] using (substApplyPrim delta name).symm
    | arrow domain codomain ihDomain ihCodomain =>
        have domainBounded : domain.MVarBounded frontier := by
          intro id member
          exact bounded id (by simp [Ty.mvars, member])
        have codomainBounded : codomain.MVarBounded frontier := by
          intro id member
          exact bounded id (by simp [Ty.mvars, member])
        simp only [MStore.apply]
        rw [ihDomain domainBounded, ihCodomain codomainBounded,
          substApplyArrow]
    | bvar index => simpa [MStore.apply] using (substApplyBVar delta index).symm
    | rigid level => simpa [MStore.apply] using (substApplyRigid delta level).symm
    | mvar id =>
        have idBounded : id < frontier := bounded id (by simp [Ty.mvars])
        have idInStore : id < store.length := by simpa [length] using idBounded
        simp only [MStore.apply, List.getElem?_map,
          List.getElem?_eq_getElem idInStore, Option.map_some,
          Option.getD_some]
  intro ty member
  obtain ⟨oldTy, oldMember, rfl⟩ := List.mem_map.mp member
  have oldBounded := storeBounded oldTy oldMember
  have updatedBounded : (delta.apply oldTy).MVarBounded frontier :=
    substApplyBounded deltaBounded oldBounded
  rw [mapApply updatedBounded]
  have oldFixed : store.apply oldTy = oldTy := storeNormalized oldTy oldMember
  have deltaOldFixed : store.apply (delta.apply oldTy) = delta.apply oldTy :=
    MStore.unify_preserves_fixed length storeBounded storeNormalized
      leftBounded rightBounded run oldTy oldBounded oldFixed
  rw [deltaOldFixed, deltaStable]

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
      checked.required = state.required ∧
      checked.solutions.apply left = checked.solutions.apply right := by
  unfold InferState.constrain at run
  cases hdelta : unify (state.solutions.apply left)
      (state.solutions.apply right) with
  | none => simp [hdelta] at run
  | some delta =>
      simp only [hdelta, Option.some.injEq] at run
      subst checked
      have leftAppliedWF := MStore.apply_inferWF
        safe.solutionsScoped safe.solutionsBounded leftWF
      have rightAppliedWF := MStore.apply_inferWF
        safe.solutionsScoped safe.solutionsBounded rightWF
      have deltaScoped : delta.Scoped rigidCount :=
        unify_scoped leftAppliedWF.1 rightAppliedWF.1 hdelta
      have deltaBounded : delta.Bounded state.next :=
        unify_bounded leftAppliedWF.2 rightAppliedWF.2 hdelta
      have substMVarScoped : ∀ {ty replacement : Ty} {target : Nat},
          ty.Scoped rigidCount 0 → replacement.Scoped rigidCount 0 →
            (ty.substMVar target replacement).Scoped rigidCount 0 := by
        intro ty replacement target typeScoped replacementScoped
        induction typeScoped with
        | prim => exact .prim
        | arrow _ _ ihDomain ihCodomain => exact .arrow ihDomain ihCodomain
        | bvar hlt => omega
        | rigid hlt => exact .rigid hlt
        | mvar id =>
            simp only [Ty.substMVar]
            split
            · exact replacementScoped
            · exact .mvar _
      have substApplyScoped : ∀ {subst : MSubst} {ty : Ty},
          subst.Scoped rigidCount → ty.Scoped rigidCount 0 →
            (subst.apply ty).Scoped rigidCount 0 := by
        intro subst ty substScoped typeScoped
        induction subst generalizing ty with
        | nil => simpa [MSubst.apply] using typeScoped
        | cons binding rest ih =>
            have bindingScoped : binding.2.Scoped rigidCount 0 :=
              substScoped binding (by simp)
            have restScoped : MSubst.Scoped rigidCount rest := by
              intro item member
              exact substScoped item (by simp [member])
            simpa [MSubst.apply, List.foldl] using
              ih restScoped (substMVarScoped typeScoped bindingScoped)
      have substMVarBounded : ∀ {ty replacement : Ty} {target : Nat},
          ty.MVarBounded state.next → replacement.MVarBounded state.next →
            (ty.substMVar target replacement).MVarBounded state.next := by
        intro ty replacement target typeBounded replacementBounded
        induction ty with
        | prim name => simpa [Ty.substMVar] using typeBounded
        | arrow domain codomain ihDomain ihCodomain =>
            have domainBounded : domain.MVarBounded state.next := by
              intro id member
              exact typeBounded id (by simp [Ty.mvars, member])
            have codomainBounded : codomain.MVarBounded state.next := by
              intro id member
              exact typeBounded id (by simp [Ty.mvars, member])
            intro id member
            simp only [Ty.substMVar, Ty.mvars, List.mem_dedup,
              List.mem_append] at member
            rcases member with member | member
            · exact ihDomain domainBounded id member
            · exact ihCodomain codomainBounded id member
        | bvar index => simpa [Ty.substMVar] using typeBounded
        | rigid level => simpa [Ty.substMVar] using typeBounded
        | mvar id =>
            simp only [Ty.substMVar]
            split
            · exact replacementBounded
            · exact typeBounded
      have substApplyBounded : ∀ {subst : MSubst} {ty : Ty},
          subst.Bounded state.next → ty.MVarBounded state.next →
            (subst.apply ty).MVarBounded state.next := by
        intro subst ty substBounded typeBounded
        induction subst generalizing ty with
        | nil => simpa [MSubst.apply] using typeBounded
        | cons binding rest ih =>
            have bindingBounded := substBounded binding (by simp)
            have restBounded : MSubst.Bounded state.next rest := by
              intro item member
              exact substBounded item (by simp [member])
            simpa [MSubst.apply, List.foldl] using
              ih restBounded (substMVarBounded typeBounded bindingBounded.2)
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
            have idBounded : id < state.next := bounded id (by simp [Ty.mvars])
            have idInStore : id < state.solutions.length := by
              simpa [safe.solutions_length] using idBounded
            simp only [MStore.apply, List.getElem?_map,
              List.getElem?_eq_getElem idInStore, Option.map_some,
              Option.getD_some]
      have mappedScoped : MStore.Scoped
          (state.solutions.map delta.apply) rigidCount := by
        intro ty member
        obtain ⟨oldTy, oldMember, rfl⟩ := List.mem_map.mp member
        exact substApplyScoped deltaScoped
          (safe.solutionsScoped oldTy oldMember)
      have mappedBounded : MStore.Bounded
          (state.solutions.map delta.apply) state.next := by
        intro ty member
        obtain ⟨oldTy, oldMember, rfl⟩ := List.mem_map.mp member
        exact substApplyBounded deltaBounded
          (safe.solutionsBounded oldTy oldMember)
      have mappedNormalized : MStore.Normalized
          (state.solutions.map delta.apply) :=
        MStore.map_unify_normalized safe.solutions_length
          safe.solutionsBounded safe.solutionsNormalized
          leftWF.2 rightWF.2 hdelta
      refine ⟨?_, rfl, rfl, ?_⟩
      · exact ⟨by simpa using safe.solutions_length,
          mappedScoped, mappedBounded, mappedNormalized,
          safe.requiredBounded⟩
      · rw [mapApply leftWF.2, mapApply rightWF.2,
          unify_sound hdelta]

/-- A checked prefix is a safe solution table at the restored outer frontier. -/
theorem MStore.take_safe
    {store : MStore} {rigidCount cutoff : Nat}
    (length : cutoff ≤ store.length)
    (normalized : store.Normalized)
    (escape : MStore.safeToLeave rigidCount cutoff (store.take cutoff) = true) :
    (store.take cutoff).length = cutoff ∧
      MStore.Scoped (store.take cutoff) rigidCount ∧
      MStore.Bounded (store.take cutoff) cutoff ∧
      MStore.Normalized (store.take cutoff) := by
  have prefixApply : ∀ {ty : Ty}, ty.MVarBounded cutoff →
      MStore.apply (store.take cutoff) ty = store.apply ty := by
    intro ty bounded
    induction ty with
    | prim name => rfl
    | arrow domain codomain ihDomain ihCodomain =>
        have domainBounded : domain.MVarBounded cutoff := by
          intro id member
          exact bounded id (by simp [Ty.mvars, member])
        have codomainBounded : codomain.MVarBounded cutoff := by
          intro id member
          exact bounded id (by simp [Ty.mvars, member])
        simp only [MStore.apply, ihDomain domainBounded, ihCodomain codomainBounded]
    | bvar index => rfl
    | rigid level => rfl
    | mvar id =>
        have idBounded : id < cutoff := bounded id (by simp [Ty.mvars])
        simp only [MStore.apply, List.getElem?_take_of_lt idBounded]
  have escaped := MStore.safeToLeave_eq_true_iff.mp escape
  refine ⟨List.length_take_of_le length, ?_, ?_, ?_⟩
  · intro ty member
    exact (escaped ty member).1
  · intro ty member
    exact (Ty.mvarBounded_iff_mvarsBelow.mpr <| by
      exact Ty.mvarsBelow_eq_true_iff.mpr (escaped ty member).2)
  · intro ty member
    have bounded : ty.MVarBounded cutoff :=
      Ty.mvarBounded_iff_mvarsBelow.mpr <|
        Ty.mvarsBelow_eq_true_iff.mpr (escaped ty member).2
    rw [prefixApply bounded]
    exact normalized ty (List.mem_of_mem_take member)

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
      h.solutionsBounded, h.solutionsNormalized, h.requiredBounded⟩
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
                  ⟨fresh.1, (state.solutions.applyScheme scheme).openWith fresh.2⟩ := by
                exact Option.some.inj run.symm
              subst result
              exact ⟨freshSafe.1, openedWF, freshSafe.2.2.2⟩
      | lambda ann body =>
          cases inputScoped with
          | lambda annScoped bodyScoped =>
            cases ann with
            | none =>
                simp only [inferFuel] at run
                let seeded := state.freshRequired
                have seededSafe := InferState.freshRequired_safe stateSafe
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
                            bodyResult.ty⟩ := by
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
                            bodyResult.ty⟩ := by
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
                            ⟨checked, checked.solutions.apply fresh.2⟩ := by
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
                    have bodyRun : inferFuel fuel rigidCount
                        (PolyTy.mono rhsTy :: ctx) body rhsResult.state =
                          some result := by
                      simpa [rhsTy, rhsRun] using run
                    have bodySafe := ih rhsSafe.1 bodyCtxWF bodyScoped bodyRun
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
                        have localStartLe :
                            localStart ≤ checked.solutions.length := by
                          rw [checkedSafe.1.solutions_length,
                            checkedSafe.2.1]
                          exact le_trans seededSafe.2.2 rhsSafe.2.2
                        have projectedSafe := MStore.take_safe
                          localStartLe checkedSafe.1.solutionsNormalized escape
                        let outerState : InferState :=
                          { next := localStart
                            solutions := projected
                            required := checked.required.filter
                              (· < localStart) }
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
                        have bodySafe := ih outerSafe bodyCtxWF bodyScoped bodyRun
                        refine ⟨bodySafe.1, bodySafe.2.1, ?_⟩
                        simpa [outerState, localStart] using bodySafe.2.2
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
                        ⟨checked, checked.solutions.apply seeded.2⟩ := by
                      simpa [seeded] using run.symm
                    subst result
                    refine ⟨checkedSafe.1, resultTyWF, ?_⟩
                    rw [checkedSafe.2.1]
                    exact le_trans seededSafe.2.2 bodySafe.2.2

end EPL
