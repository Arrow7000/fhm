import EPL.Inference

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
