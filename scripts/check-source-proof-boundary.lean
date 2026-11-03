import FHM.Headlines
import Lean.Util.CollectAxioms

/-! Inspect actual proof dependencies, rather than just source-level imports.
This command adds no declarations to the trusted logical interface. -/

open Lean in
run_cmd do
  let env ← getEnv
  for historical in #[`TypeOfHM, `TypeOfMatchBranch, `Option.Pins,
      `GeneralisesTo, `RecSpecs.StratifiedMonoTyped, `RecSpecs.PolyTypedFinal,
      `Expr.toCore, `Expr.ofCore, `SurfaceBridge.lowerCore,
      `SurfaceBridge.lowerCoreProgram, `SurfaceBridge.SurfaceWTExpr,
      `SurfaceBridge.coreTypecheck] do
    if env.contains historical then
      throwError "The default verified import closure still contains {historical}"
  for root in #[`unifyResult_sound, `unifyResultK_complete,
      `unifyResultK_error_not_unifies,
      `seedResult_complete_source, `checkLetResult_complete_source,
      `checkSignatureResult_complete_source,
      `inferWithTypesResult_infer, `inferWithTypesResult_input_sound,
      `inferWithTypesResult_complete, `inferWithTypesResult_error_not_typing,
      `inferWithTypesResult_principal, `inferWithTypesResult_typing_iff,
      `inferWithTypes_infer, `inferWithTypes_input_sound,
      `inferWithTypes_runtime_sound, `inferWithTypes_complete, `inferWithTypes_principal,
      `inferWithTypes_typing_iff, `principalType_sound, `typecheck_sound,
      `InputTyping.erase, `elabDecls_sound, `elabDecls_eq_some_iff,
      `elabDeclsResult_eq_ok_iff, `elabDeclsResult_error_not_wellFormed,
      `SurfaceBridge.lowerDataDeclsInResult_eq_ok_iff,
      `SurfaceBridge.lowerDataDeclsInResult_error_not_lowers,
      `SurfaceBridge.lowerInputResult_eq_ok_iff,
      `SurfaceBridge.lowerInputResult_error_not_lowers,
      `SurfaceBridge.lowerInputProgramResult_eq_ok_iff,
      `SurfaceBridge.lowerInputProgramResult_error_not_lowers,
      `PatComp.compile_correct_surface, `PatComp.lowerMatch_adequate_of_typed,
      `RuntimeTyping.RunWT.varsBelow, `RuntimeTyping.RunWT.type_safety_star,
      `SurfaceBridge.lowerExpr_exhaustive, `SurfaceBridge.lowerProgram_exhaustive,
      `SurfaceBridge.program_type_safe,
      `Headlines.lower_and_infer_direct,
      `Headlines.runSafe] do
    unless env.contains root do
      throwError "The public proof audit refers to a missing declaration: {root}"
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
