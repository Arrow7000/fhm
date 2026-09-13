import FHM.Unverified.Surface.Parse
import FHM.SurfaceBridge
import FHM.InferW
import FHM.Pretty
import FHM.Unverified.EvaluateUnsafe
import FHM.Bounds.Erase

/-!
# Damas--Milner recursion smoke-test driver

This is an executable specification of the recursion boundary on the erased
branch. It deliberately drives the current API directly:

`parse -> erase surface annotations -> lower -> infer -> exhaustiveness ->
erase Core annotations -> evaluate`.

The negative cases assert rejection specifically at inference. In particular,
this suite does not preserve the old type-passing branch's expectation that an
annotation enables polymorphic use inside an SCC.
-/

open Surface.Parse
open SurfaceBridge
open FHM.Bounds.Erase

inductive Stage where
  | parse
  | lower
  | infer
  | exhaustiveness
  | evaluation
  deriving BEq, Repr

def Stage.pretty : Stage -> String
  | .parse => "parse"
  | .lower => "lower"
  | .infer => "infer"
  | .exhaustiveness => "exhaustiveness"
  | .evaluation => "evaluation"

structure PipelineError where
  stage : Stage
  message : String

structure CheckedProgram where
  ty : Ty
  value : Expr

/-- The real erased HM path, kept local so the smoke test pins each stage and
does not depend on the CLI/reporting layer. -/
def checkPipelineDM (src : String) : Except PipelineError CheckedProgram := do
  let parsed <- match parseProgram src with
    | .error e =>
        throw ⟨.parse, s!"{e.msg} (line {e.line}, col {e.col})"⟩
    | .ok p => pure p
  let program := (eraseProgram parsed).toProgram
  let (ctors, core) <- match lowerProgram program with
    | none => throw ⟨.lower,
        "lowering failed (unbound name, bad declaration, or rejected sugar)"⟩
    | some x => pure x
  let ty <- match infer core.freshFloor ⟨[], ctors⟩ core with
    | none => throw ⟨.infer, "typechecking failed"⟩
    | some (_, _, ty) => pure ty
  if !(checkExhaustive ctors program.term) then
    throw ⟨.exhaustiveness, "match not exhaustive"⟩
  let erased := core.erase
  let value <- match SmallStep.evaluateUnsafe erased with
    | none => throw ⟨.evaluation,
        "erased term got stuck (or evaluation diverged)"⟩
    | some value => pure value
  return { ty, value }

inductive Expected where
  | pass (value : String)
  | rejectAt (stage : Stage)

structure Case where
  path : String
  motivation : String
  expected : Expected

def runCase (test : Case) : IO Bool := do
  IO.println s!"=== {test.path} ==="
  IO.println s!"  {test.motivation}"
  let src <- IO.FS.readFile test.path
  match checkPipelineDM src, test.expected with
  | .ok checked, .pass expectedValue =>
      let actualValue := checked.value.pretty
      IO.println s!"  program type: {checked.ty.pretty}"
      IO.println s!"  result:       {actualValue}"
      if actualValue == expectedValue then
        IO.println "  PASS (accepted and evaluated as expected)"
        return true
      else
        IO.println s!"  FAIL (expected result {expectedValue})"
        return false
  | .ok checked, .rejectAt stage =>
      IO.println s!"  FAIL (expected rejection at {stage.pretty}, but accepted)"
      IO.println s!"  program type: {checked.ty.pretty}"
      IO.println s!"  result:       {checked.value.pretty}"
      return false
  | .error err, .pass _ =>
      IO.println s!"  FAIL (unexpected {err.stage.pretty} rejection: {err.message})"
      return false
  | .error err, .rejectAt expectedStage =>
      if err.stage == expectedStage then
        IO.println s!"  PASS (rejected at {err.stage.pretty} as expected)"
        return true
      else
        IO.println s!"  FAIL (rejected at {err.stage.pretty}, expected {expectedStage.pretty})"
        IO.println s!"  {err.message}"
        return false

def main : IO UInt32 := do
  let cases : List Case :=
    [ { path := "scratch/polyrec-ordinary-recursion.fhm"
        motivation := "ordinary monomorphic recursion remains accepted"
        expected := .pass "15" }
    , { path := "scratch/polyrec-generalize-after-scc.fhm"
        motivation := "a recursive binding generalises after its SCC exits"
        expected := .pass "(1, True)" }
    , { path := "scratch/polyrec-inner-poly-calls.fhm"
        motivation := "an annotation does not permit two in-SCC instantiations under D2"
        expected := .rejectAt .infer }
    , { path := "scratch/polyrec-mixed-group.fhm"
        motivation := "mixed SCC members still have one monotype while the SCC is checked"
        expected := .rejectAt .infer }
    , { path := "scratch/polyrec-mixed-conflict-must-fail.fhm"
        motivation := "conflicting in-SCC recursive instantiations are rejected"
        expected := .rejectAt .infer }
    , { path := "scratch/polyrec-unannotated-must-fail.fhm"
        motivation := "unannotated polymorphic recursion remains outside HM inference"
        expected := .rejectAt .infer }
    , { path := "scratch/polyrec-inner-poly-unannotated-must-fail.fhm"
        motivation := "the two-instantiation unannotated variant also fails"
        expected := .rejectAt .infer }
    , { path := "scratch/polyrec-head-binder-scoped-must-fail.fhm"
        motivation := "complete head-binder/scoped-type-variable support is explicitly parked"
        expected := .rejectAt .infer }
    , { path := "scratch/polyrec-nested.fhm"
        motivation := "the canonical annotated polymorphic-recursion example is outside D2"
        expected := .rejectAt .infer }
    , { path := "scratch/polyrec-groups-nested.fhm"
        motivation := "annotations do not restore polymorphic recursion in a larger program"
        expected := .rejectAt .infer }
    , { path := "scratch/polyrec-mixed-fixed-instantiation.fhm"
        motivation := "a mixed SCC is accepted when recursive uses share one instantiation"
        expected := .pass "[5, 5, 5]" }
    ]
  let results <- cases.mapM runCase
  let passed := results.count true
  IO.println s!"--- {passed}/{results.length} cases behaved as specified ---"
  return if passed == results.length then 0 else 1
