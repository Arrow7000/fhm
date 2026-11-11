import EPL.Properties.InferenceSound
import EPL.Properties.Erasure
import EPL.Properties.RuntimeSafety

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

end EPL
