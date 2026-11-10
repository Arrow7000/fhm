import EPL.Typing

namespace EPL
namespace Typing

private theorem fits_scoped
    (fits : Template.Fits holes template ty)
    (wf : ty.WF rigidCount binderCount) :
    template.Scoped rigidCount binderCount := by
  induction fits with
  | fixed => exact .fixed wf
  | hole => exact .hole
  | named => exact .named
  | arrow domainFit codomainFit domainIH codomainIH =>
      rcases wf with ⟨hScoped, hFree⟩
      cases hScoped with
      | arrow domainScoped codomainScoped =>
          cases hFree with
          | arrow domainFree codomainFree =>
              exact .arrow (domainIH ⟨domainScoped, domainFree⟩)
                (codomainIH ⟨codomainScoped, codomainFree⟩)

private theorem matches_scoped
    {template : Template} {ty : Ty}
    (hMatches : template.Matches ty)
    (wf : ty.WF rigidCount binderCount) :
    template.Scoped rigidCount binderCount := by
  rcases hMatches with ⟨holes, _, fits⟩
  exact fits_scoped fits wf

private theorem param_scoped
    {ann : ParamAnn} {ty : Ty}
    (hMatches : ParamAnn.Matches ann ty)
    (wf : ty.WF rigidCount binderCount) :
    ∀ template, ann = some template → template.Scoped rigidCount binderCount := by
  intro template hann
  exact matches_scoped (hMatches template hann) wf

/-- A derivable source expression cannot contain an out-of-scope authored
rigid, bound type variable, or inference metavariable in its annotations. -/
theorem sourceScoped (typing : Typing rigidCount ctx expr ty) :
    expr.TypeScoped rigidCount 0 := by
  induction typing with
  | primLit => exact .primLit
  | primOp => exact .primOp
  | var => exact .var
  | lambda paramWF hMatches _ bodyScoped =>
      exact .lambda (param_scoped hMatches paramWF) bodyScoped
  | app _ _ functionScoped argumentScoped =>
      exact .app functionScoped argumentScoped
  | letMono _ _ _ rhsScoped bodyScoped =>
      exact .letMono rhsScoped bodyScoped
  | letPoly hMatches schemeWF _ rhsScoped _ _ _ bodyScoped =>
      rcases hMatches with ⟨paramCountEq, bodyMatches⟩
      exact .letPoly
        (by
          rw [← paramCountEq]
          simpa [PolyTy.WF] using matches_scoped bodyMatches schemeWF)
        (by simpa [paramCountEq] using rhsScoped)
        bodyScoped
  | fix selfWF hMatches _ bodyScoped =>
      exact .fix (matches_scoped hMatches selfWF) bodyScoped

end Typing
end EPL
