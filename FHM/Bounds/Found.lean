import FHM.Unverified.Surface.Provenance
import FHM.Bounds.Synth

/-! # First `.found` → bounds vertical slice

This adapter proves the pipeline shape before the per-node bounds walk lands.
It takes the HM type from the root `.found` wrapper, never reruns HM inference,
and feeds the stripped Core term plus that type to the existing bounds
synthesizer. The result is keyed back to the root source origin.

This is intentionally root-only. It must not be mistaken for D8's final
per-node bounds report; that requires instrumenting the bounds walk itself.
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

end FHM.Bounds.Found
