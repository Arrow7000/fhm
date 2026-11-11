import EPL.Examples
import EPL.InferenceTests
import EPL.Properties.InferenceSound

namespace EPL.InferenceSoundTests

open EPL EPL.Examples EPL.InferenceTests

/-- End-to-end canaries: these declarative derivations are obtained solely
from successful execution of the public inference function. -/
example : Typing 0 [] inferredIntLambda (.arrow intTy intTy) := by
  apply infer_sound (result := ⟨.arrow intTy intTy⟩)
  decide

example : Typing 0 [] explicitPolyProgram boolTy := by
  apply infer_sound (result := ⟨boolTy⟩)
  decide

example : Typing 0 [] partlyInferredPolyProgram boolTy := by
  apply infer_sound (result := ⟨boolTy⟩)
  decide

example : Typing 0 [] inferredIntegerFix intTy := by
  apply infer_sound (result := ⟨intTy⟩)
  decide

end EPL.InferenceSoundTests
