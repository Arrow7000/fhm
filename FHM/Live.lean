import FHM.Surface.Parse
import FHM.SurfaceBridge
import FHM.InferW
import FHM.Pretty

/-!
# Live pipeline driver

Read a `.fhm` source file and run:

`parse → lower → typecheck → exhaustiveness → elaborate → evaluate`

Each failure prints the stage name and whatever detail we have.
-/

open Surface.Parse
open SurfaceBridge

/-- Which pipeline stage rejected the program (or ran out of fuel). -/
inductive PipelineStage
  | parse
  | lower
  | typecheck
  | exhaustiveness
  | elaborate
  | eval
  deriving Repr, DecidableEq

def PipelineStage.tag : PipelineStage → String
  | .parse => "parse"
  | .lower => "lower"
  | .typecheck => "typecheck"
  | .exhaustiveness => "exhaustiveness"
  | .elaborate => "elaborate"
  | .eval => "eval"

structure PipelineOk where
  scheme : PolyTy
  value : Expr

/-- Run source text through the full executable pipeline. -/
def runSource (src : String) (fuel : Nat := 10_000) :
    Except (PipelineStage × String) PipelineOk := do
  let p ← match parseProgram src with
    | .error e =>
        throw (.parse, s!"{e.msg} (line {e.line}, col {e.col})")
    | .ok p => pure p
  let (ctors, c) ← match lowerProgram p with
    | none => throw (.lower, "lowering failed (unbound name, bad decl, or rejected sugar)")
    | some x => pure x
  let σ ← match typecheck ctors c with
    | none => throw (.typecheck, "typechecking failed")
    | some σ => pure σ
  if !(checkExhaustive ctors p.term) then
    throw (.exhaustiveness, "match not exhaustive")
  let e ← match elaborateProgram p with
    | none => throw (.elaborate, "elaboration failed")
    | some e => pure e
  match SmallStep.evaluate fuel e with
  | none => throw (.eval, s!"stuck or out of fuel (fuel := {fuel})")
  | some v => pure { scheme := σ, value := v }

/-- Format a successful run for the terminal. -/
def formatOk (r : PipelineOk) : String :=
  s!"ok  :  {r.scheme.pretty}\n⟹  {r.value.pretty}"

/-- Format a staged failure. -/
def formatErr (st : PipelineStage) (msg : String) : String :=
  s!"[{st.tag}] {msg}"

/-- CLI: `fhm_live [path] [fuel]` — default path `scratch/live.fhm`, fuel `10000`. -/
def main (args : List String) : IO UInt32 := do
  let path := args.head?.getD "scratch/live.fhm"
  let fuel :=
    match args.drop 1 |>.head? with
    | some s => s.toNat?.getD 10_000
    | none => 10_000
  let src ← IO.FS.readFile path
  match runSource src fuel with
  | .ok r =>
      IO.println (formatOk r)
      return 0
  | .error (st, msg) =>
      IO.eprintln (formatErr st msg)
      return 1
