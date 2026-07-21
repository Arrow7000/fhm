import FHM.Surface.Parse
import FHM.SurfaceBridge
import FHM.InferW
import FHM.Pretty
import FHM.EvaluateUnsafe
import FHM.PipelineShared
import Lean.Data.Json

/-!
# Live pipeline driver

Read a `.fhm` source file (or stdin) and run:

`parse → lower → infer (print binding + body types) → exhaustiveness → elaborate → evaluateUnsafe`

Types are printed **before** evaluation in human mode, since eval is the slow part.
Live uses the unbounded evaluator — naive `fib` blows past any fixed fuel.

## CLI

```
fhm [--json] [path]
fhm run [--json] [path]
```

- No path, human mode: default `scratch/live.fhm` (watch-live).
- No path, `--json`: read source from stdin (web playground).
- With path: read that file (human or JSON).
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

/-! ## ANSI colour (TTY + no `NO_COLOR`) -/

/-- Human-readable duration from a nanosecond delta.
    Picks ns / µs / ms / s so sub-millisecond runs don't collapse to `0ms`. -/
def formatDuration (ns : Nat) : String :=
  if ns < 1000 then
    s!"{ns}ns"
  else if ns < 1_000_000 then
    s!"{ns / 1000}µs"
  else if ns < 1_000_000_000 then
    s!"{ns / 1_000_000}ms"
  else
    let whole := ns / 1_000_000_000
    let frac := (ns % 1_000_000_000) / 10_000_000  -- hundredths of a second
    let pad := if frac < 10 then "0" else ""
    s!"{whole}.{pad}{frac}s"

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

def formatTiming (a : Ansi) (label : String) (ns : Nat) : String :=
  a.dim s!"  ({label} in {formatDuration ns})"

/-! ## Structured pipeline (shared by human + JSON) -/

structure PipelineErr where
  stage : PipelineStage
  message : String
  line : Nat := 1
  col : Nat := 1
  deriving Repr

structure CheckedProgram where
  bindings : List (ValName × PolyTy)
  programTy : PolyTy
  checkNs : Nat
  elaborated : Expr

structure PipelineOk where
  bindings : List (ValName × PolyTy)
  programTy : PolyTy
  checkNs : Nat
  evalNs : Nat
  resultPretty : String

/-- Parse → lower → infer → exhaustiveness → elaborate (no eval yet). -/
def checkPipeline (src : String) : IO (Except PipelineErr CheckedProgram) := do
  let tCheck0 ← IO.monoNanosNow
  let p ← match parseProgram src with
    | .error e =>
        return .error {
          stage := .parse
          message := s!"{e.msg} (line {e.line}, col {e.col})"
          line := e.line
          col := e.col
        }
    | .ok p => pure p

  let (ctors, c) ← match lowerProgram p with
    | none =>
        return .error {
          stage := .lower
          message := "lowering failed (unbound name, bad decl, or rejected sugar)"
        }
    | some x => pure x

  let (eOut, τ) ← match infer c.freshFloor ⟨[], ctors⟩ c with
    | none =>
        return .error { stage := .typecheck, message := "typechecking failed" }
    | some (_, _, eOut, τ) => pure (eOut, τ)
  let tCheck1 ← IO.monoNanosNow
  let bodyσ := genScheme [] [] τ
  let binds := zipBindingTypes p.groups (collectTopSchemes eOut)

  if !(checkExhaustive ctors p.term) then
    return .error { stage := .exhaustiveness, message := "match not exhaustive" }

  let e ← match elaborateProgram p with
    | none =>
        return .error { stage := .elaborate, message := "elaboration failed" }
    | some e => pure e

  return .ok {
    bindings := binds
    programTy := bodyσ
    checkNs := tCheck1 - tCheck0
    elaborated := e
  }

/-- Evaluate an already-checked program (timed). -/
def evalCheckedIO (c : CheckedProgram) : IO (Except PipelineErr PipelineOk) := do
  let tEval0 ← IO.monoNanosNow
  match SmallStep.evaluateUnsafe c.elaborated with
  | none =>
      return .error { stage := .eval, message := "stuck (diverged or no step)" }
  | some v =>
      let tEval1 ← IO.monoNanosNow
      return .ok {
        bindings := c.bindings
        programTy := c.programTy
        checkNs := c.checkNs
        evalNs := tEval1 - tEval0
        resultPretty := v.pretty
      }

def PipelineOk.toJson (r : PipelineOk) : Lean.Json :=
  let binds := r.bindings.map fun ⟨n, σ⟩ =>
    Lean.Json.mkObj [
      ("name", Lean.Json.str (prettyValName n)),
      ("type", Lean.Json.str σ.pretty)
    ]
  Lean.Json.mkObj [
    ("version", Lean.Json.num 1),
    ("ok", Lean.Json.bool true),
    ("bindings", Lean.Json.arr binds.toArray),
    ("programTy", Lean.Json.str r.programTy.pretty),
    ("result", Lean.Json.str r.resultPretty),
    ("timings", Lean.Json.mkObj [
      ("checkNs", Lean.Json.num r.checkNs),
      ("evalNs", Lean.Json.num r.evalNs)
    ])
  ]

def PipelineErr.toJson (e : PipelineErr) : Lean.Json :=
  Lean.Json.mkObj [
    ("version", Lean.Json.num 1),
    ("ok", Lean.Json.bool false),
    ("stage", Lean.Json.str e.stage.tag),
    ("message", Lean.Json.str e.message),
    ("line", Lean.Json.num e.line),
    ("col", Lean.Json.num e.col)
  ]

/-- Parse CLI: optional `--json`, optional path. -/
def parseArgs (args : List String) : Except String (Bool × Option String) :=
  let rec go (as : List String) (json : Bool) (path : Option String) :
      Except String (Bool × Option String) :=
    match as with
    | [] => .ok (json, path)
    | "--json" :: rest =>
        if json then .error "duplicate --json"
        else go rest true path
    | "-h" :: _ | "--help" :: _ =>
        .error "usage: fhm [--json] [path]\n\
  no path (human): scratch/live.fhm\n\
  no path (--json): read stdin\n\
  path: read that file"
    | flag :: rest =>
        if flag.startsWith "-" then
          .error s!"unknown flag: {flag}\nusage: fhm [--json] [path]"
        else if path.isSome then
          .error "usage: fhm [--json] [path]"
        else
          go rest json (some flag)
  go args false none

def runLive (args : List String) : IO UInt32 := do
  let (jsonMode, path?) ← match parseArgs args with
    | .error msg =>
        IO.eprintln msg
        return 2
    | .ok x => pure x

  let src ← match path?, jsonMode with
    | some path, _ => IO.FS.readFile path
    | none, true =>
        let stdin ← IO.getStdin
        stdin.readToEnd
    | none, false => IO.FS.readFile "scratch/live.fhm"

  match ← checkPipeline src with
  | .error e =>
      if jsonMode then
        IO.println e.toJson.pretty
      else
        let ansi ← Ansi.mkIO
        IO.eprintln (formatErr ansi e.stage e.message)
      return 1
  | .ok checked =>
      if !jsonMode then
        let ansi ← Ansi.mkIO
        IO.println (formatTypes ansi checked.bindings checked.programTy)
        IO.println (formatTiming ansi "checked" checked.checkNs)
        IO.println ""
        (← IO.getStdout).flush
        IO.println (ansi.yellow "evaluating…")
        (← IO.getStdout).flush
      match ← evalCheckedIO checked with
      | .error e =>
          if jsonMode then
            IO.println e.toJson.pretty
          else
            let ansi ← Ansi.mkIO
            IO.eprintln (formatErr ansi e.stage e.message)
          return 1
      | .ok r =>
          if jsonMode then
            IO.println r.toJson.pretty
          else
            let ansi ← Ansi.mkIO
            IO.println s!"{ansi.boldBrightGreen "⟹"}  {ansi.brightCyan r.resultPretty}"
            IO.println (formatTiming ansi "evaluated" r.evalNs)
          return 0
