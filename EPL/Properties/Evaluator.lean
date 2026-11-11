import EPL.Evaluator

/-!
# The executable evaluator computes `Eval.Step`

`step?` is sound and complete for the step relation, so the relation is
deterministic and `step? = none` characterises normal forms. `run` follows
the relation, and it is complete: any execution that reaches a value is found
by `run` given enough fuel.
-/

namespace EPL
namespace Eval

theorem isValue_iff {expr : RuntimeExpr} :
    isValue expr = true ↔ Value expr := by
  constructor
  · intro h
    cases expr with
    | primLit literal => exact .primLit
    | primOp op => exact .primOp
    | var index => simp [isValue] at h
    | lambda ann body => exact .lambda
    | app function argument =>
        cases function with
        | primOp op =>
            cases op
            cases argument with
            | primLit literal =>
                cases literal with
                | int value => exact .intAddPartial
                | unit => simp [isValue] at h
                | bool value => simp [isValue] at h
            | primOp op => simp [isValue] at h
            | var index => simp [isValue] at h
            | lambda ann body => simp [isValue] at h
            | app f a => simp [isValue] at h
            | letIn ann rhs body => simp [isValue] at h
            | fix ann body => simp [isValue] at h
        | primLit literal => simp [isValue] at h
        | var index => simp [isValue] at h
        | lambda ann body => simp [isValue] at h
        | app f a => simp [isValue] at h
        | letIn ann rhs body => simp [isValue] at h
        | fix ann body => simp [isValue] at h
    | letIn ann rhs body => simp [isValue] at h
    | fix ann body => simp [isValue] at h
  · intro value
    cases value <;> simp [isValue]

/-- `step?` is the identity (returns `none`) on values. -/
private theorem step?_of_value {expr : RuntimeExpr} (value : Value expr) :
    step? expr = none := by
  cases value <;> rfl

private theorem isValue_lambda (ann : Option Unit) (body : RuntimeExpr) :
    isValue (.lambda ann body) = true := rfl

/-- Values are normal forms. -/
theorem Value.irreducible {expr next : RuntimeExpr}
    (value : Value expr) : ¬ Step expr next := by
  intro step
  cases value with
  | primLit => cases step
  | primOp => cases step
  | lambda => cases step
  | intAddPartial =>
      cases step with
      | appFunction h => cases h
      | appArgument _ h => cases h

theorem step?_sound {expr next : RuntimeExpr}
    (h : step? expr = some next) : Step expr next := by
  induction expr generalizing next with
  | primLit literal => simp [step?] at h
  | primOp op => simp [step?] at h
  | var index => simp [step?] at h
  | lambda ann body => simp [step?] at h
  | fix ann body =>
      cases ann
      simp only [step?] at h
      cases h
      exact Step.fixUnfold
  | letIn ann rhs body ihRhs ihBody =>
      simp only [step?] at h
      cases hr : step? rhs with
      | some rhs' =>
          rw [hr] at h
          simp only [Option.some.injEq] at h
          cases h
          exact Step.letRhs (ihRhs hr)
      | none =>
          rw [hr] at h
          by_cases hval : isValue rhs = true
          · simp only [hval, if_true] at h
            cases h
            exact Step.letValue (isValue_iff.mp hval)
          · simp only [hval] at h
            simp at h
  | app function argument ihFunction ihArgument =>
      simp only [step?] at h
      cases hf : step? function with
      | some function' =>
          rw [hf] at h
          simp only [Option.some.injEq] at h
          cases h
          exact Step.appFunction (ihFunction hf)
      | none =>
          rw [hf] at h
          by_cases hval : isValue function = true
          · simp only [hval, if_true] at h
            cases ha : step? argument with
            | some argument' =>
                rw [ha] at h
                simp only [Option.some.injEq] at h
                cases h
                exact Step.appArgument (isValue_iff.mp hval) (ihArgument ha)
            | none =>
                rw [ha] at h
                by_cases harg : isValue argument = true
                · simp only [harg, if_true] at h
                  have vf := isValue_iff.mp hval
                  have va := isValue_iff.mp harg
                  cases vf with
                  | primLit => simp [reduceApp] at h
                  | primOp => simp [reduceApp] at h
                  | lambda =>
                      simp only [reduceApp] at h
                      simp only [Option.some.injEq] at h
                      cases h
                      exact Step.beta va
                  | intAddPartial =>
                      cases va with
                      | primLit =>
                          rename_i literal
                          cases literal with
                          | int right =>
                              simp only [reduceApp] at h
                              simp only [Option.some.injEq] at h
                              cases h
                              exact Step.intAdd
                          | unit => simp [reduceApp] at h
                          | bool b => simp [reduceApp] at h
                      | primOp => simp [reduceApp] at h
                      | lambda => simp [reduceApp] at h
                      | intAddPartial => simp [reduceApp] at h
                · simp only [harg] at h
                  simp at h
          · simp only [hval] at h
            simp at h

theorem step?_complete {expr next : RuntimeExpr}
    (step : Step expr next) : step? expr = some next := by
  induction step with
  | beta value =>
      simp [step?, reduceApp, step?_of_value value, isValue_iff.mpr value, isValue_lambda]
  | appFunction h ih =>
      simp [step?, ih]
  | appArgument value h ih =>
      simp [step?, step?_of_value value, isValue_iff.mpr value, ih]
  | intAdd =>
      simp [step?, reduceApp, isValue]
  | letRhs h ih =>
      simp [step?, ih]
  | letValue value =>
      simp [step?, step?_of_value value, isValue_iff.mpr value]
  | fixUnfold =>
      simp [step?]

theorem Step.deterministic {expr first second : RuntimeExpr}
    (stepFirst : Step expr first) (stepSecond : Step expr second) :
    first = second := by
  have hFirst := step?_complete stepFirst
  have hSecond := step?_complete stepSecond
  rw [hFirst] at hSecond
  exact Option.some.inj hSecond

/-- `step?` returns `none` exactly on normal forms of `Step`. -/
theorem step?_eq_none_iff {expr : RuntimeExpr} :
    step? expr = none ↔ ∀ next, ¬ Step expr next := by
  constructor
  · intro h next step
    have hsome := step?_complete step
    rw [h] at hsome
    exact nomatch hsome
  · intro h
    cases hstep : step? expr with
    | none => rfl
    | some next => exact absurd (step?_sound hstep) (h next)

/-- `run` is stationary when `step?` has no successor. -/
private theorem run_none {expr : RuntimeExpr} (h : step? expr = none) (fuel : Nat) :
    run fuel expr = expr := by
  induction fuel with
  | zero => rfl
  | succ fuel ih => simp [run, h]

private theorem run_add (first second : Nat) (expr : RuntimeExpr) :
    run (first + second) expr = run second (run first expr) := by
  induction first generalizing expr with
  | zero => simp [run]
  | succ first ih =>
      rw [Nat.succ_add]
      cases h : step? expr with
      | none =>
          rw [run_none h (first + second + 1)]
          rw [run_none h (first + 1)]
          rw [run_none h second]
      | some next =>
          have hlhs : run (first + second + 1) expr = run (first + second) next := by
            simp [run, h]
          have hrhs : run (first + 1) expr = run first next := by
            simp [run, h]
          rw [hlhs, hrhs]
          exact ih next

/-- The evaluator only ever follows the step relation. -/
theorem run_steps (fuel : Nat) (expr : RuntimeExpr) :
    Steps expr (run fuel expr) := by
  induction fuel generalizing expr with
  | zero => exact Relation.ReflTransGen.refl
  | succ fuel ih =>
      simp only [run]
      cases h : step? expr with
      | none =>
          exact Relation.ReflTransGen.refl
      | some next =>
          exact Relation.ReflTransGen.head (step?_sound h) (ih next)

/-- The evaluator leaves values unchanged. -/
theorem run_value {fuel : Nat} {expr : RuntimeExpr}
    (value : Value expr) : run fuel expr = expr := by
  exact run_none (step?_of_value value) fuel

/-- Any finite execution is realised by `run` at exactly the corresponding
fuel. -/
private theorem run_reaches {expr result : RuntimeExpr} (steps : Steps expr result) :
    ∃ fuel, run fuel expr = result := by
  induction steps with
  | refl => exact ⟨0, rfl⟩
  | tail hsteps hstep ih =>
      obtain ⟨fuel, hfuel⟩ := ih
      refine ⟨fuel + 1, ?_⟩
      rw [run_add fuel 1 expr, hfuel]
      simp [run, step?_complete hstep]

/-- Evaluator completeness: an execution reaching a value is found by `run`
with enough fuel (and with any larger fuel). -/
theorem run_complete {expr result : RuntimeExpr}
    (steps : Steps expr result) (value : Value result) :
    ∃ fuel, ∀ extra, run (fuel + extra) expr = result := by
  obtain ⟨fuel, hfuel⟩ := run_reaches steps
  refine ⟨fuel, fun extra => ?_⟩
  rw [run_add fuel extra expr, hfuel]
  exact run_value (fuel := extra) value

end Eval
end EPL
