import EPL.Properties.InferenceSound
import EPL.Properties.Runtime

namespace EPL

/-- Successful source inference produces a typing derivation for the erased
runtime program at exactly the reported type. -/
theorem infer_erases
    {input : Source} {result : InferenceResult}
    (run : infer input = some result) :
    RuntimeTyping 0 [] input.erase result.ty := by
  exact Typing.erase (infer_sound run)

/-- A successfully inferred closed program is either already a runtime value
after erasure or can take a step. -/
theorem infer_progress
    {input : Source} {result : InferenceResult}
    (run : infer input = some result) :
    Eval.Value input.erase ∨ ∃ next, Eval.Step input.erase next := by
  exact RuntimeTyping.progress (infer_erases run)

/-- Every runtime step from a successfully inferred program preserves the
type reported by inference. -/
theorem infer_step_preserves
    {input : Source} {result : InferenceResult} {next : RuntimeExpr}
    (run : infer input = some result)
    (step : Eval.Step input.erase next) :
    RuntimeTyping 0 [] next result.ty := by
  exact RuntimeTyping.preservation (infer_erases run) step

/-- The reported type survives every finite runtime execution. -/
theorem infer_steps_preserve
    {input : Source} {result : InferenceResult} {next : RuntimeExpr}
    (run : infer input = some result)
    (steps : Eval.Steps input.erase next) :
    RuntimeTyping 0 [] next result.ty := by
  induction steps with
  | refl => exact infer_erases run
  | tail _ step ih => exact RuntimeTyping.preservation ih step

/-- Every finite execution prefix of a successfully inferred program remains
typed and ends at either a value or another reducible term. -/
theorem infer_type_safety
    {input : Source} {result : InferenceResult} {next : RuntimeExpr}
    (run : infer input = some result)
    (steps : Eval.Steps input.erase next) :
    RuntimeTyping 0 [] next result.ty ∧
      (Eval.Value next ∨ ∃ after, Eval.Step next after) := by
  have typed := infer_steps_preserve run steps
  exact ⟨typed, RuntimeTyping.progress typed⟩

end EPL

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
