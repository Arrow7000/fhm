import FHM.Surface.Parse
import FHM.SurfaceBridge
import FHM.InferW
import FHM.Pretty
import FHM.EvaluateUnsafe
import FHM.PipelineShared
import FHM.Bounds.Ann
import FHM.Bounds.Erase
import FHM.Bounds.Report

/-!
# Poly-recursion smoke-test driver (HM path)

Replicates the HM path of `Live.checkPipeline` WITHOUT importing `FHM.Live`:
Live transitively imports `FHM.Bounds.Typing` (via Check → Synth), which
currently fails to build on this commit (missing `Ty.bl` match cases), taking
the `fhm` CLI with it. Everything below runs the real verified pipeline:
parse → erase → lower → infer → report → exhaustiveness → elaborate → eval.

For each binder we dump BOTH the inferred scheme (`hm`) and the user's
ascription (`bounds?`). A walker over the elaborated term additionally
extracts group-INTERNAL `letIn (some σ)` annotations, which
`collectTopSchemes` does not.
-/

open Surface.Parse
open SurfaceBridge
open FHM.Bounds
open FHM.Bounds.Erase
open FHM.Bounds.Report

structure CheckedProgram where
  report : ProgramReport
  elaborated : Expr

/-- Collect ALL `letIn (some σ)` annotations in the elaborated term,
including those nested inside `letRec` groups (internal binders). -/
partial def walkAllSchemes : Expr → List PolyTy
  | .letIn (some σ) _ body => σ :: walkAllSchemes body
  | .letIn none _ body => walkAllSchemes body
  | .letRec _ _ inner => walkAllSchemes inner
  | .lambda _ b => walkAllSchemes b
  | .app f a => walkAllSchemes f ++ walkAllSchemes a
  | .match_ s bs =>
      walkAllSchemes s ++ bs.flatMap fun (_, b) => walkAllSchemes b
  | _ => []

/-- HM path of Live.checkPipeline (minus the BL gate, which only guards
`--bl` mode; all files here are HM-mode programs). -/
def checkPipelineHM (src : String) : Except String CheckedProgram := do
  let p ← match parseProgram src with
    | .error e => throw s!"[parse] {e.msg} (line {e.line}, col {e.col})"
    | .ok p => pure p
  let ep := eraseProgram p
  let p := ep.toProgram
  let (ctors, c) ← match lowerProgram p with
    | none => throw "[lower] lowering failed (unbound name, bad decl, or rejected sugar)"
    | some x => pure x
  let (eOut, τ) ← match infer c.freshFloor ⟨[], ctors⟩ c with
    | none => throw "[typecheck] typechecking failed"
    | some (_, _, eOut, τ) => pure (eOut, τ)
  let bodyσ := genScheme [] [] τ
  let report := assembleProgramReport p.groups (collectTopSchemes eOut) bodyσ ep
  if !(checkExhaustive ctors p.term) then
    throw "[exhaustiveness] match not exhaustive"
  let e ← match elaborateProgram p with
    | none => throw "[elaborate] elaboration failed"
    | some e => pure e
  return { report := report, elaborated := e }

structure FileInfo where
  path : String
  mustPass : Bool := true

def describe (label : String) (s : String) : IO Unit :=
  IO.println s!"  {label}: {s}"

def runFile (info : FileInfo) : IO Bool := do
  IO.println s!"=== {info.path} ==="
  let src ← IO.FS.readFile info.path
  match checkPipelineHM src with
  | .error msg =>
      IO.println s!"  {msg}"
      if info.mustPass then
        IO.println "  ✗ UNEXPECTED failure"
        return false
      else
        IO.println "  ✓ rejected as expected"
        return true
  | .ok checked =>
      match SmallStep.evaluateUnsafe checked.elaborated with
      | none =>
          IO.println "  [eval] stuck (diverged or no step)"
          IO.println "  ✗ UNEXPECTED eval failure"
          return false
      | some v =>
          IO.println s!"  bindings ({checked.report.bindings.length}):"
          for b in checked.report.bindings do
            IO.println s!"    {prettyValName b.name}"
            describe "inferred" b.hm.pretty
            match b.bounds? with
            | some a => describe "ascribed" (BinderAnn.pretty a)
            | none => pure ()
          IO.println s!"  program  : {checked.report.programPretty}"
          IO.println s!"  result   : {v.pretty}"
          IO.println s!"  internal anns (elaborated term):"
          for σ in walkAllSchemes checked.elaborated do
            IO.println s!"    {σ.pretty}"
          IO.println "  ✓ typechecked + evaluated"
          return true

def main : IO UInt32 := do
  let files : List FileInfo :=
    [{ path := "scratch/polyrec-nested.fhm" }
    , { path := "scratch/polyrec-mixed-group.fhm" }
    , { path := "scratch/polyrec-groups-nested.fhm" }
    , { path := "scratch/polyrec-inner-poly-calls.fhm" }
    , { path := "scratch/polyrec-skolem-leak-must-fail.fhm", mustPass := false }
    , { path := "scratch/polyrec-unannotated-must-fail.fhm", mustPass := false }
    , { path := "scratch/polyrec-inner-poly-unannotated-must-fail.fhm", mustPass := false }
    , { path := "scratch/polyrec-mixed-conflict-must-fail.fhm", mustPass := false }
    ]
  let results ← files.mapM runFile
  let nOk := results.count true
  IO.println s!"--- {nOk}/{results.length} files behaved as expected ---"
  return if nOk == results.length then 0 else 1
