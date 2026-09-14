import FHM.Bounds.Found
import FHM.Bounds.SchemeWalk

/-! Opt-in adapter for the certified scheme-aware fragment. The existing launch
route is unchanged. Coverage and provenance reconciliation are executable guards,
not formal artifact-coherence theorems. Unsupported forms fail explicitly. -/

namespace FHM.Bounds.SchemeFound

open SurfaceBridge.Provenance

def synthNodes (typed : TypedLowered) : Except String
    (SchemeWalk.Result [] [] typed.inference.output [] × List Found.NodeReport) := do
  unless typed.lowering.provenanceTotal && typed.sourceTypesTotal do
    throw "bounds: incomplete typed provenance"
  unless typed.lowering.counts.problems.isEmpty do
    throw "bounds: unresolved or duplicate count binder scope"
  let result ← SchemeWalk.walk [] [] [] typed.inference.output typed.inference.binderSchemes
  unless exactlyOnce (logicalCorePaths typed.inference.output) (result.nodes.map (·.path)) do
    throw "bounds: incomplete or duplicate typed node report"
  let reports ← result.nodes.mapM fun node => do
    let origin ← match typed.lowering.coreOrigins.find? (fun pair => pair.1 == node.path) with
      | some (_, origin) => pure origin
      | none => throw "bounds: missing node origin"
    pure ⟨node, origin⟩
  pure (result, reports)

end FHM.Bounds.SchemeFound
