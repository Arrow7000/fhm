import EPL.Properties.InferenceModelCompletion

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
