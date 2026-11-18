import EPL.Runtime

/-!
# The evaluator

`Eval.step?` computes exactly the `Eval.Step` relation, which is
deterministic, and values are exactly the expressions `isValue` accepts.
None of this mentions types.
-/

namespace EPL
namespace Eval

theorem isValue_iff : isValue expr = true ↔ Value expr := by
  sorry

/-- Values do not step. -/
theorem Value.irreducible (value : Value expr) : ¬ Step expr next := by
  sorry

theorem step?_sound (found : step? expr = some next) : Step expr next := by
  sorry

/-- Values do not step. -/
theorem step?_none_of_value {expr : RuntimeExpr} (value : Value expr) : step? expr = none := by
  sorry

theorem step?_complete (step : Step expr next) : step? expr = some next := by
  sorry

theorem Step.deterministic (first : Step expr a) (second : Step expr b) : a = b := by
  have := step?_complete second
  rw [step?_complete first] at this
  exact Option.some.inj this

theorem run_steps (fuel : Nat) (expr : RuntimeExpr) : Steps expr (run fuel expr) := by
  induction fuel generalizing expr with
  | zero => exact Relation.ReflTransGen.refl
  | succ fuel ih =>
      rw [run]
      cases h : step? expr with
      | none => exact Relation.ReflTransGen.refl
      | some next => exact Relation.ReflTransGen.head (step?_sound h) (ih next)

/-- `run` stays at a value. -/
theorem run_value (value : Value expr) (fuel : Nat) : run fuel expr = expr := by
  cases fuel with
  | zero => rfl
  | succ fuel => rw [run, step?_none_of_value value]

/-- Every execution reaching a value is found by `run` with enough fuel, and
with any larger fuel. -/
theorem run_complete (steps : Steps expr result) (value : Value result) :
    ∃ fuel, ∀ extra, run (fuel + extra) expr = result := by
  induction steps using Relation.ReflTransGen.head_induction_on with
  | refl => exact ⟨0, fun extra => by rw [Nat.zero_add, run_value value]⟩
  | head step _ ih =>
      obtain ⟨fuel, found⟩ := ih
      refine ⟨fuel + 1, fun extra => ?_⟩
      rw [Nat.add_right_comm, run, step?_complete step]
      exact found extra

end Eval
end EPL
