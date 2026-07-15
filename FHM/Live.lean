import FHM.Surface.Parse
import FHM.SurfaceBridge
import FHM.InferW
import FHM.Pretty
import FHM.EvaluateUnsafe

/-!
# Live pipeline driver

Read a `.fhm` source file and run:

`parse → lower → infer (print binding + body types) → exhaustiveness → elaborate → evaluateUnsafe`

Types are printed **before** evaluation, since eval is the slow part.
Live uses the unbounded evaluator — naive `fib` blows past any fixed fuel.
-/

open Surface.Parse
open SurfaceBridge

/-- Which pipeline stage rejected the program. -/
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

/-- Collect schemes from the outer `letIn (some σ)` spine produced by
    `letRecElab` (stops at the program body). -/
partial def collectTopSchemes : Expr → List PolyTy
  | .letIn (some σ) _ body => σ :: collectTopSchemes body
  | _ => []

/-- `letRecElab` wraps group members outermost-last, so each group's chunk of
    schemes from `collectTopSchemes` is reversed relative to binding order.
    Undo that per SCC group and zip with surface names. -/
def zipBindingTypes (groups : List (List Surface.Binding)) (schemes : List PolyTy) :
    List (ValName × PolyTy) :=
  let rec go (gs : List (List Surface.Binding)) (ss : List PolyTy)
      (acc : List (ValName × PolyTy)) : List (ValName × PolyTy) :=
    match gs with
    | [] => acc
    | g :: gs' =>
      let n := g.length
      let chunk := (ss.take n).reverse
      let pairs := g.map (·.name) |>.zip chunk
      go gs' (ss.drop n) (acc ++ pairs)
  go groups schemes []

/-- Human-readable duration from a millisecond delta. -/
def formatMs (ms : Nat) : String :=
  if ms < 1000 then s!"{ms}ms"
  else
    let whole := ms / 1000
    let frac := (ms % 1000) / 10  -- hundredths
    let pad := if frac < 10 then "0" else ""
    s!"{whole}.{pad}{frac}s"

/-! ## ANSI colour (TTY + no `NO_COLOR`) -/

structure Ansi where
  on : Bool
  deriving Repr

def Ansi.mkIO : IO Ansi := do
  -- `FORCE_COLOR` wins (handy when piping); otherwise honour `NO_COLOR`, else TTY.
  if (← IO.getEnv "FORCE_COLOR").isSome then
    return ⟨true⟩
  if (← IO.getEnv "NO_COLOR").isSome then
    return ⟨false⟩
  return ⟨← (← IO.getStdout).isTty⟩

/-- Apply an SGR code (e.g. `"36"`, `"1;36"`). Nested paints reset each other,
    so combine attributes into one code instead of wrapping twice. -/
def Ansi.wrap (a : Ansi) (code : String) (s : String) : String :=
  if a.on then s!"\x1b[{code}m{s}\x1b[0m" else s

def Ansi.dim (a : Ansi) (s : String) : String := a.wrap "2" s
def Ansi.red (a : Ansi) (s : String) : String := a.wrap "31" s
def Ansi.yellow (a : Ansi) (s : String) : String := a.wrap "33" s
def Ansi.blue (a : Ansi) (s : String) : String := a.wrap "34" s
def Ansi.brightCyan (a : Ansi) (s : String) : String := a.wrap "96" s
def Ansi.boldCyan (a : Ansi) (s : String) : String := a.wrap "1;36" s
def Ansi.boldMagenta (a : Ansi) (s : String) : String := a.wrap "1;35" s
def Ansi.boldRed (a : Ansi) (s : String) : String := a.wrap "1;31" s
def Ansi.boldBrightGreen (a : Ansi) (s : String) : String := a.wrap "1;92" s

/-- Binding / program type report with light syntax colour. -/
def formatTypes (a : Ansi) (binds : List (ValName × PolyTy)) (body : PolyTy) : String :=
  let bindLines :=
    binds.map fun ⟨n, σ⟩ =>
      s!"  {a.boldCyan (prettyValName n)}  {a.dim ":"}  {a.blue σ.pretty}"
  let bindsBlock :=
    if binds.isEmpty then ""
    else String.intercalate "\n" bindLines ++ "\n"
  bindsBlock ++ s!"  {a.boldMagenta "<program>"}  {a.dim ":"}  {a.blue body.pretty}"

def formatErr (a : Ansi) (st : PipelineStage) (msg : String) : String :=
  s!"{a.boldRed s!"[{st.tag}]"} {a.red msg}"

def formatTiming (a : Ansi) (label : String) (ms : Nat) : String :=
  a.dim s!"  ({label} in {formatMs ms})"

/-- CLI: `fhm_live [path]` — default path `scratch/live.fhm`. -/
def main (args : List String) : IO UInt32 := do
  let path := args.head?.getD "scratch/live.fhm"
  let ansi ← Ansi.mkIO
  let src ← IO.FS.readFile path

  let tCheck0 ← IO.monoMsNow
  -- parse (lex + parse)
  let p ← match parseProgram src with
    | .error e =>
        IO.eprintln (formatErr ansi .parse s!"{e.msg} (line {e.line}, col {e.col})")
        return 1
    | .ok p => pure p

  -- lower
  let (ctors, c) ← match lowerProgram p with
    | none =>
        IO.eprintln (formatErr ansi .lower
          "lowering failed (unbound name, bad decl, or rejected sugar)")
        return 1
    | some x => pure x

  -- infer (types before eval)
  let (eOut, τ) ← match infer c.freshFloor ⟨[], ctors⟩ c with
    | none =>
        IO.eprintln (formatErr ansi .typecheck "typechecking failed")
        return 1
    | some (_, _, eOut, τ) => pure (eOut, τ)
  let tCheck1 ← IO.monoMsNow
  let bodyσ := genScheme [] [] τ
  let binds := zipBindingTypes p.groups (collectTopSchemes eOut)
  IO.println (formatTypes ansi binds bodyσ)
  IO.println (formatTiming ansi "checked" (tCheck1 - tCheck0))
  IO.println ""
  -- Flush so types show up before the (often slow) rest of the pipeline.
  (← IO.getStdout).flush

  -- exhaustiveness
  if !(checkExhaustive ctors p.term) then
    IO.eprintln (formatErr ansi .exhaustiveness "match not exhaustive")
    return 1

  -- elaborate (cheap) then time evaluation alone
  let e ← match elaborateProgram p with
    | none =>
        IO.eprintln (formatErr ansi .elaborate "elaboration failed")
        return 1
    | some e => pure e
  IO.println (ansi.yellow "evaluating…")
  (← IO.getStdout).flush
  let tEval0 ← IO.monoMsNow
  match SmallStep.evaluateUnsafe e with
  | none =>
      IO.eprintln (formatErr ansi .eval "stuck (diverged or no step)")
      return 1
  | some v =>
      let tEval1 ← IO.monoMsNow
      IO.println s!"{ansi.boldBrightGreen "⟹"}  {ansi.brightCyan v.pretty}"
      IO.println (formatTiming ansi "evaluated" (tEval1 - tEval0))
      return 0
