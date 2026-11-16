import EPL2.Runtime

/-!
# The evaluator

`Eval.step?` computes exactly the `Eval.Step` relation, which is
deterministic, and values are exactly the expressions `isValue` accepts.
None of this mentions types.
-/

namespace EPL2
namespace Eval

theorem isValue_iff : isValue sig expr = true ↔ Value sig expr := by
  sorry

theorem Value.irreducible (value : Value sig expr) : ¬ Step sig expr next := by
  sorry

theorem step?_sound (found : step? sig expr = some next) : Step sig expr next := by
  sorry

theorem step?_complete (step : Step sig expr next) : step? sig expr = some next := by
  sorry

theorem Step.deterministic (first : Step sig expr a) (second : Step sig expr b) : a = b := by
  sorry

theorem run_steps (fuel : Nat) (expr : RuntimeExpr) : Steps sig expr (run sig fuel expr) := by
  sorry

/-- Every terminating execution is found by `run` with enough fuel. -/
theorem run_complete (steps : Steps sig expr result) (value : Value sig result) :
    ∃ fuel, run sig fuel expr = result := by
  sorry

end Eval
end EPL2
