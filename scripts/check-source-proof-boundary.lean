import FHM.Headlines
import Lean.Util.CollectAxioms

/-! Inspect actual proof dependencies, rather than just source-level imports.
This command adds no declarations to the trusted logical interface. -/

open Lean in
run_cmd do
  let env ← getEnv
  for historical in #[`TypeOfHM, `TypeOfMatchBranch, `Option.Pins,
      `GeneralisesTo, `RecSpecs.StratifiedMonoTyped, `RecSpecs.PolyTypedFinal] do
    if env.contains historical then
      throwError "The default verified import closure still contains {historical}"
  for root in #[`inferWithTypes_infer, `inferWithTypes_input_sound,
      `inferWithTypes_runtime_sound, `inferWithTypes_complete, `inferWithTypes_principal,
      `inferWithTypes_typing_iff, `principalType_sound, `typecheck_sound,
      `InputTyping.erase, `elabDecls_sound, `elabDecls_eq_some_iff,
      `PatComp.compile_correct_surface, `PatComp.lowerMatch_adequate_of_typed,
      `RuntimeTyping.RunWT.varsBelow, `RuntimeTyping.RunWT.type_safety_star,
      `Headlines.lower_and_infer_direct,
      `Headlines.runSafe] do
    let (_, state) := ((CollectAxioms.collect root).run env).run {}
    for entry in env.constants.toList do
      if state.visited.contains entry.1 &&
          (entry.1.toString.startsWith "TypeOfHM" ||
            entry.1.toString.startsWith "TypeOfMatchBranch") then
        throwError "{root} still depends on historical source typing: {entry.1}"
    for axiomName in state.axioms do
      unless #[`propext, `Classical.choice, `Quot.sound].contains axiomName do
        throwError "{root} depends on an unexpected axiom: {axiomName}"
    logInfo m!"{root}: no historical source-typing dependencies; axioms {state.axioms}"
