import FHM.Bounds.Found
import FHM.Bounds.RecursiveGroup

/-! Opt-in provenance adapter for checked found programs and recursive groups. It consumes the
existing HM artifact and exports reports only after whole-group acceptance.
Coverage guards are executable checks, not formal artifact-coherence theorems.
The production CLI/LSP launch remains unchanged.
-/

namespace FHM.Bounds.RecursiveFound

open SurfaceBridge.Provenance

def synthNodes (typed : TypedLowered) : Except String
    (RecursiveGroup.Result [] [] [] [] [] typed.inference.output × List Found.NodeReport) := do
  unless typed.lowering.provenanceTotal && typed.sourceTypesTotal do
    throw "bounds: incomplete typed provenance"
  let result ← RecursiveGroup.check [] [] [] [] [] [] typed.inference.output
    typed.inference.binderSchemes typed.lowering.counts
  unless exactlyOnce (logicalCorePaths typed.inference.output) (result.nodes.map (·.path)) do
    throw "bounds: incomplete or duplicate recursive node report"
  let reports ← result.nodes.mapM fun node => do
    let origin ← match typed.lowering.coreOrigins.find? (fun pair => pair.1 == node.path) with
      | some (_, origin) => pure origin
      | none => throw "bounds: missing recursive node origin"
    pure ⟨node, origin⟩
  pure (result, reports)

end FHM.Bounds.RecursiveFound
