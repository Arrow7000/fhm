import EPL.RuntimeTyping

namespace EPL

private theorem erase_openRigidsFrom (expr : Source) :
    (expr.openRigidsFrom depth base count).erase = expr.erase := by
  induction expr generalizing depth with
  | primLit => rfl
  | primOp => rfl
  | var => rfl
  | lambda ann body ih =>
      simp only [Expr.openRigidsFrom, Expr.erase, ih]
  | app function argument functionIH argumentIH =>
      simp only [Expr.openRigidsFrom, Expr.erase, functionIH, argumentIH]
  | letIn ann rhs body rhsIH bodyIH =>
      simp only [Expr.openRigidsFrom, Expr.erase, rhsIH, bodyIH]
  | fix ann body ih =>
      simp only [Expr.openRigidsFrom, Expr.erase, ih]

/-- Opening source type annotations has no runtime effect. -/
theorem erase_openRigids (expr : Source) :
    (expr.openRigids base count).erase = expr.erase := by
  exact erase_openRigidsFrom expr

namespace Typing

/-- Erasing Core-native partial annotations preserves the assigned type. -/
theorem erase (typing : Typing rigidCount ctx expr ty) :
    RuntimeTyping rigidCount ctx expr.erase ty := by
  induction typing with
  | primLit => exact .primLit
  | primOp => exact .primOp
  | var hlookup hwf hlen hargs =>
      exact .var hlookup hwf hlen hargs
  | lambda paramWF _ _ bodyErased =>
      exact .lambda paramWF bodyErased
  | app _ _ functionErased argumentErased =>
      exact .app functionErased argumentErased
  | letMono rhsWF _ _ rhsErased bodyErased =>
      exact .letMono rhsWF rhsErased bodyErased
  | letPoly _ schemeWF ctxWF _ _ _ rhsErased bodyErased =>
      apply RuntimeTyping.letPoly schemeWF ctxWF
      · simpa only [erase_openRigids] using rhsErased
      · exact bodyErased
  | fix selfWF _ _ bodyErased =>
      exact .fix selfWF bodyErased

end Typing
end EPL
