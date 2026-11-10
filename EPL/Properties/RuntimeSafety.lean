import EPL.Properties.RuntimeSubstitution

namespace EPL
namespace RuntimeTyping

private theorem int_value
    (value : Eval.Value expr)
    (typing : RuntimeTyping rigidCount [] expr (.prim .int)) :
    ∃ number, expr = .primLit (.int number) := by
  cases value with
  | primLit =>
      cases_type PrimLit <;> cases typing
      exact ⟨_, rfl⟩
  | primOp => cases typing
  | lambda => cases typing
  | intAddPartial =>
      cases typing with
      | app functionTyping _ => cases functionTyping

private theorem progress_empty (typing : RuntimeTyping rigidCount ctx expr ty)
    (empty : ctx = []) :
    Eval.Value expr ∨ ∃ next, Eval.Step expr next := by
  induction typing with
  | primLit => exact .inl .primLit
  | primOp => exact .inl .primOp
  | var hlookup => simp [empty] at hlookup
  | lambda => exact .inl .lambda
  | app functionTyping argumentTyping functionIH argumentIH =>
      rcases functionIH empty with functionValue | ⟨function', functionStep⟩
      · rcases argumentIH empty with argumentValue | ⟨argument', argumentStep⟩
        · cases functionValue with
          | primLit =>
              cases_type PrimLit <;> cases functionTyping
          | primOp =>
              cases_type PrimOp
              cases functionTyping
              obtain ⟨number, rfl⟩ := int_value argumentValue (empty ▸ argumentTyping)
              exact .inl .intAddPartial
          | lambda =>
              exact .inr ⟨_, .beta argumentValue⟩
          | intAddPartial =>
              cases functionTyping with
              | app operatorTyping _ =>
                  cases operatorTyping
                  obtain ⟨number, rfl⟩ := int_value argumentValue (empty ▸ argumentTyping)
                  exact .inr ⟨_, .intAdd⟩
        · exact .inr ⟨_, .appArgument functionValue argumentStep⟩
      · exact .inr ⟨_, .appFunction functionStep⟩
  | letMono _ _ _ rhsIH _ =>
      rcases rhsIH empty with rhsValue | ⟨rhs', rhsStep⟩
      · exact .inr ⟨_, .letValue rhsValue⟩
      · exact .inr ⟨_, .letRhs rhsStep⟩
  | letPoly _ _ _ _ rhsIH _ =>
      rcases rhsIH empty with rhsValue | ⟨rhs', rhsStep⟩
      · exact .inr ⟨_, .letValue rhsValue⟩
      · exact .inr ⟨_, .letRhs rhsStep⟩
  | fix => exact .inr ⟨_, .fixUnfold⟩

/-- Closed, well-typed runtime terms are values or can take a step. -/
theorem progress (typing : RuntimeTyping 0 [] expr ty) :
    Eval.Value expr ∨ ∃ next, Eval.Step expr next := by
  exact progress_empty typing rfl

/-- A runtime step preserves the exact assigned type. -/
theorem preservation
    (typing : RuntimeTyping rigidCount ctx expr ty)
    (step : Eval.Step expr next) :
    RuntimeTyping rigidCount ctx next ty := by
  induction step generalizing rigidCount ctx ty with
  | beta argumentValue =>
      cases typing with
      | app functionTyping argumentTyping =>
          cases functionTyping with
          | lambda paramWF bodyTyping =>
              exact substScheme (RuntimeHasScheme.mono paramWF argumentTyping)
                bodyTyping
  | appFunction functionStep functionIH =>
      cases typing with
      | app functionTyping argumentTyping =>
          exact .app (functionIH functionTyping) argumentTyping
  | appArgument functionValue argumentStep argumentIH =>
      cases typing with
      | app functionTyping argumentTyping =>
          exact .app functionTyping (argumentIH argumentTyping)
  | intAdd =>
      cases typing with
      | app functionTyping argumentTyping =>
          cases functionTyping with
          | app operatorTyping leftTyping =>
              cases operatorTyping
              cases leftTyping
              cases argumentTyping
              exact .primLit
  | letRhs rhsStep rhsIH =>
      cases typing with
      | letMono rhsWF rhsTyping bodyTyping =>
          exact .letMono rhsWF (rhsIH rhsTyping) bodyTyping
      | letPoly schemeWF ctxWF rhsTyping bodyTyping =>
          exact .letPoly schemeWF ctxWF (rhsIH rhsTyping) bodyTyping
  | letValue rhsValue =>
      cases typing with
      | letMono rhsWF rhsTyping bodyTyping =>
          exact substScheme (RuntimeHasScheme.mono rhsWF rhsTyping) bodyTyping
      | letPoly schemeWF ctxWF rhsTyping bodyTyping =>
          exact substScheme (genericHasScheme schemeWF ctxWF rhsTyping) bodyTyping
  | fixUnfold =>
      cases typing with
      | fix selfWF bodyTyping =>
          expose_names
          have fixed := RuntimeTyping.fix selfWF bodyTyping
          exact substScheme (RuntimeHasScheme.mono selfWF fixed) bodyTyping

end RuntimeTyping
end EPL
