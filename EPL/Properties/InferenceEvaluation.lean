import EPL.Properties.Evaluator
import EPL.Properties.InferenceRuntimeSafety

/-!
# Running inferred programs

Successful inference makes the executable evaluator safe: every intermediate
term keeps the inferred type, and the evaluator never stops at a stuck term.
`evaluate` packages this as a proof-carrying pipeline: infer, erase, run,
and return either a typed value or a typed, still-reducible term.
-/

namespace EPL

/-- Running a successfully inferred program, for any fuel, yields a term of
exactly the inferred type. -/
theorem infer_run_typed
    {input : Source} {result : InferenceResult}
    (inferred : infer input = some result) (fuel : Nat) :
    RuntimeTyping 0 [] (Eval.run fuel input.erase) result.ty := by
  exact infer_steps_preserve inferred (Eval.run_steps fuel input.erase)

/-- The evaluator never gets stuck on an inferred program: if it has no next
step, it has reached a value. -/
theorem infer_run_stops_at_value
    {input : Source} {result : InferenceResult} {fuel : Nat}
    (inferred : infer input = some result)
    (stopped : Eval.step? (Eval.run fuel input.erase) = none) :
    Eval.Value (Eval.run fuel input.erase) := by
  have typed := infer_run_typed inferred fuel
  rcases RuntimeTyping.progress typed with value | ⟨next, step⟩
  · exact value
  · exact absurd step ((Eval.step?_eq_none_iff (expr := Eval.run fuel input.erase)).mp stopped next)

namespace Eval

/-- The result of evaluating a closed program of type `ty` from `start` with
bounded fuel, carrying its own evidence. -/
inductive Outcome (start : RuntimeExpr) (ty : Ty) : Type
  /-- Evaluation finished at a value. -/
  | value (result : RuntimeExpr)
      (steps : Steps start result)
      (isValue : Value result)
      (typed : RuntimeTyping 0 [] result ty)
  /-- Fuel ran out at a typed term that can still step. -/
  | running (current next : RuntimeExpr)
      (steps : Steps start current)
      (typed : RuntimeTyping 0 [] current ty)
      (step : Step current next)

/-- The final value, or `none` if fuel ran out. -/
def Outcome.value? : Outcome start ty → Option RuntimeExpr
  | .value result .. => some result
  | .running .. => none

end Eval

/-- Infer `input`, then evaluate its erasure for at most `fuel` steps.
Rejected programs yield `none`; accepted programs never get stuck, by
construction of `Eval.Outcome`. -/
def evaluate (input : Source) (fuel : Nat) :
    Option ((result : InferenceResult) × Eval.Outcome input.erase result.ty) :=
  match inferred : infer input with
  | none => none
  | some result =>
      some ⟨result,
        match stepped : Eval.step? (Eval.run fuel input.erase) with
        | some next =>
            .running _ next (Eval.run_steps fuel _)
              (infer_run_typed inferred fuel) (Eval.step?_sound stepped)
        | none =>
            .value _ (Eval.run_steps fuel _)
              (infer_run_stops_at_value inferred stepped)
              (infer_run_typed inferred fuel)⟩

end EPL
