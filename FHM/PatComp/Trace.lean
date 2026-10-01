import FHM.CorePath
import FHM.PatComp

/-! # Construction trace for pattern compilation

The verified compiler deliberately knows nothing about source spans or editor
protocols. It does, however, uniquely know where it emits administrative Core
and where it copies a source arm. This module exposes that construction trace
without asking later tooling to reverse-engineer the decision tree.
-/

namespace PatComp

/-- Why a logical Core node was introduced by pattern compilation. Source
    ownership is attached by the surface provenance layer. -/
inductive GeneratedNode where
  | scrutineeLet
  | decisionMatch (occ : Occ)
  | decisionScrutinee (occ : Occ)
  | captureLet (act capture : Nat) (occ : Occ)
  | captureRhs (act capture : Nat) (occ : Occ)
  | failureMatch
  | failureSentinel
  deriving Repr, DecidableEq, BEq

/-- A source arm can occur at several leaf roots, and one source capture can
    consequently be represented by several administrative `letIn`s. -/
structure EmissionTrace where
  generated : List (CorePath × GeneratedNode)
  armBodyRoots : List (Nat × CorePath)
  captureLets : List (Nat × Nat × CorePath)
  deriving Repr, DecidableEq, BEq

namespace EmissionTrace

def empty : EmissionTrace := ⟨[], [], []⟩

def append (a b : EmissionTrace) : EmissionTrace :=
  { generated := a.generated ++ b.generated
    armBodyRoots := a.armBodyRoots ++ b.armBodyRoots
    captureLets := a.captureLets ++ b.captureLets }

def belowPath (pre : CorePath) (trace : EmissionTrace) : EmissionTrace :=
  { generated := trace.generated.map fun (path, node) => (pre ++ path, node)
    armBodyRoots := trace.armBodyRoots.map fun (act, path) => (act, pre ++ path)
    captureLets := trace.captureLets.map fun (act, capture, path) =>
      (act, capture, pre ++ path) }

end EmissionTrace

/-- Trace the administrative wrappers introduced by `emitLets`. The outermost
    let re-binds the last capture, while capture zero is innermost. -/
def traceEmitLets (act : Nat) (binds : List Occ) : EmissionTrace :=
  let indexed := binds.reverse.mapIdx fun depth occ =>
    let capture := binds.length - 1 - depth
    let path : CorePath := List.replicate depth .letBody
    (path, capture, occ)
  { generated := indexed.flatMap fun (path, capture, occ) =>
      [(path, .captureLet act capture occ),
       (path ++ [.letRhs], .captureRhs act capture occ)]
    armBodyRoots := [(act, List.replicate binds.length .letBody)]
    captureLets := indexed.map fun (path, capture, _occ) => (act, capture, path) }

mutual

/-- Trace `emit` using paths relative to the emitted tree root. -/
def traceEmit : DTree → EmissionTrace
  | .fail =>
      { generated := [([], .failureMatch), ([.matchScrut], .failureSentinel)]
        armBodyRoots := []
        captureLets := [] }
  | .leaf act binds => traceEmitLets act binds
  | .switch occ cases dflt =>
      let named := traceEmitCases 0 cases
      let default := match dflt with
        | .fail => EmissionTrace.empty
        | d => (traceEmit d).belowPath [.matchBranch cases.length]
      { generated :=
          [([], .decisionMatch occ), ([.matchScrut], .decisionScrutinee occ)] ++
            named.generated ++ default.generated
        armBodyRoots := named.armBodyRoots ++ default.armBodyRoots
        captureLets := named.captureLets ++ default.captureLets }

def traceEmitCases (index : Nat) : List (CtorName × Nat × DTree) → EmissionTrace
  | [] => EmissionTrace.empty
  | (_, _, tree) :: rest =>
      ((traceEmit tree).belowPath [.matchBranch index]).append
        (traceEmitCases (index + 1) rest)

end

/-- Core expression plus its compiler-owned construction trace. -/
structure TracedLowering where
  expr : Expr
  trace : EmissionTrace

/-- The ordinary verified lowering and its administrative construction trace.
    The trace is relative to the whole outer scrutinee `letIn`. -/
def lowerMatchTrace (scrut : Expr) (pats : List Surface.Pattern)
    (bodies : Nat → Expr) : TracedLowering :=
  let tree := compile [[]] (initMatrix pats)
  let emittedTrace := (traceEmit tree).belowPath [.letBody]
  { expr := .letIn none scrut (emit [[]] bodies tree)
    trace := {
      generated := [([], .scrutineeLet)] ++
        emittedTrace.generated
      armBodyRoots := emittedTrace.armBodyRoots
      captureLets := emittedTrace.captureLets } }

/-- Instrumentation is observationally transparent to the verified lowering. -/
theorem lowerMatchTrace_expr (scrut : Expr) (pats : List Surface.Pattern)
    (bodies : Nat → Expr) :
    (lowerMatchTrace scrut pats bodies).expr = lowerMatch scrut pats bodies := rfl

end PatComp
