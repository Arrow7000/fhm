import FHM.Unverified.Surface.Provenance
import FHM.Bounds.Synth
import FHM.Bounds.Typed

/-! # `.found` → bounds/provenance adapters

The legacy root adapter takes the HM type from the root `.found` wrapper,
never reruns HM inference, and feeds the stripped Core term plus that type to
the existing bounds synthesizer. The result is keyed to the root source origin.

The legacy `synthRoot` path is intentionally root-only. `synthNodes` uses the
new proof-carrying typed slice, checks inferred unannotated-let binder facts
by exact Core site, and joins its per-node results to provenance.
Neither adapter is the completed D8 checker: the new slice explicitly rejects
unsupported forms and marks constructor scaffolding without synthesized bounds.
-/

namespace FHM.Bounds.Found

open FHM.Bounds
open FHM.Bounds.Synth
open SurfaceBridge.Provenance

structure RootReport where
  source : SourceNode
  hm : Ty
  bounds : BoundsTy

def rootSource? (lowering : Lowered) : Option SourceNode :=
  (lowering.coreOrigins.find? fun pair => pair.1 == []).map fun pair => pair.2.source

/-- Synthesize the root bounds result from an already inferred/provenanced
    artifact. `.found` supplies the HM type; only the established bounds input
    boundary strips the static wrappers. -/
def synthRoot (constraints : List Constraint) (boundEnv : BoundEnv)
    (typed : TypedLowered) : Except String RootReport := do
  unless typed.lowering.provenanceTotal do
    throw "bounds: incomplete lowering provenance"
  unless typed.sourceTypesTotal do
    throw "bounds: incomplete found/source join"
  let source ← match rootSource? typed.lowering with
    | some source => pure source
    | none => throw "bounds: missing root source origin"
  let hm ← match foundTyAtCorePath typed.inference.output [] with
    | some hm => pure hm
    | none => throw "bounds: missing root found type"
  let bounds ← synthBounds constraints boundEnv typed.inference.output.stripFound hm
  pure { source, hm, bounds }

/-- End-to-end non-PatComp expression slice: identify/lower with provenance,
    infer `.found`, join hover facts, then synthesize a root bounds report. -/
def checkRoot (ctors : CtorEnv) (surface : Surface.Expr) (spanned : Surface.Span.SpannedExpr) :
    Except String (TypedLowered × RootReport) := do
  let lowering ← match lowerWithProvenance ctors surface spanned with
    | some lowering => pure lowering
    | none => throw "bounds: provenance-aware lowering failed or reached PatComp"
  let typed ← match inferWithProvenance ctors lowering with
    | some typed => pure typed
    | none => throw "bounds: HM inference failed"
  let report ← synthRoot [] [] typed
  pure (typed, report)

structure NodeReport where
  node : Typed.NodeResult
  origin : Origin

/-- First per-node typed slice. Reports retain each Core occurrence, including
    generated constructor scaffolding, rather than coalescing by source name.
    Coverage guards are executable checks, not a formal provenance theorem. -/
def synthNodes (typed : TypedLowered) :
    Except String
      (Typed.Result [] [] typed.inference.output × List NodeReport) := do
  unless typed.lowering.provenanceTotal && typed.sourceTypesTotal do
    throw "bounds: incomplete typed provenance"
  unless typed.lowering.counts.problems.isEmpty do
    throw "bounds: unresolved or duplicate count binder scope"
  let result ← Typed.walk [] [] [] typed.inference.output (some typed.inference.binderSchemes)
  unless exactlyOnce (logicalCorePaths typed.inference.output) (result.nodes.map (·.path)) do
    throw "bounds: incomplete or duplicate typed node report"
  let reports ← result.nodes.mapM fun node => do
    let origin ← match typed.lowering.coreOrigins.find? (fun pair => pair.1 == node.path) with
      | some (_, origin) => pure origin
      | none => throw "bounds: missing node origin"
    pure ⟨node, origin⟩
  pure (result, reports)

end FHM.Bounds.Found
