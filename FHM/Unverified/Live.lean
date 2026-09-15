import FHM.Unverified.Surface.Parse
import FHM.SurfaceBridge
import FHM.InferW
import FHM.Pretty
import FHM.Unverified.EvaluateUnsafe
import FHM.Unverified.PipelineShared
import FHM.Unverified.HMDisplay
import FHM.Unverified.HMArtifacts
import FHM.Bounds.Erase
import FHM.Bounds.Pipeline
import FHM.Bounds.Ann
import FHM.Bounds.Report
import FHM.Bounds.RecursiveFound
import Lean.Data.Json

/-!
# Live pipeline driver

Read a `.fhm` source file (or stdin) and run:

`parse → lower → inferFound → HM report → exh → erase → evaluateUnsafe`

Default HM admits carried `BL` annotations under Path R: inference ignores
bounds, reports the erased `List` shape, and performs no bounds validation.
`--bl` checks the same provenance-rich inferred artifact with the canonical
proof-producing bounds checker. HM mode keeps surface `checkExhaustive`;
BL match coverage is part of its bounds derivation.

HM display types come from the producer's actual group-exit binder schemes.
BL display retains authored surface annotations and adds the checked body
bounds; display assembly is not an acceptance authority.

## CLI

```
blt [--json] [--bl] [path]
blt run [--json] [--bl] [path]
```

- No path, human mode: default `scratch/live.fhm` (watch-live).
- No path, `--json`: read source from stdin (web playground).
- With path: read that file (human or JSON).
- `--bl`: allow BL syntax; erase + report + bounds check.
-/

open Surface.Parse
open SurfaceBridge
open FHM.Bounds (ProgramBoundsAnns BoundBinding BoundsTy)
open FHM.Bounds.Erase
open FHM.Bounds.Pipeline
open FHM.Bounds.Report

/-- Which pipeline stage rejected the program. -/
inductive PipelineStage
  | parse
  | bounds
  | lower
  | typecheck
  | exhaustiveness
  | elaborate
  | eval
  deriving Repr, DecidableEq

def PipelineStage.tag : PipelineStage → String
  | .parse => "parse"
  | .bounds => "bounds"
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

/-- Binding / program type report with light syntax colour (from `ProgramReport`). -/
def formatReport (a : Ansi) (r : ProgramReport) : String :=
  let bindLines :=
    r.bindings.map fun b =>
      s!"  {a.boldCyan (prettyValName b.name)}  {a.dim ":"}  {a.blue b.pretty}"
  let bindsBlock :=
    if r.bindings.isEmpty then ""
    else String.intercalate "\n" bindLines ++ "\n"
  bindsBlock ++
    s!"  {a.boldMagenta "<program>"}  {a.dim ":"}  {a.blue r.programPretty}"

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
  endLine : Nat := line
  endCol : Nat := col + 1
  deriving Repr

structure CheckedProgram where
  /-- Unified display types (ascription wins when present). -/
  report : ProgramReport
  checkNs : Nat
  elaborated : Expr
  mode : BoundsMode := .default
  /-- Legacy BL erase package; HM neither constructs nor needs its proof. -/
  erased : Option ErasedProgram := none
  /-- De Bruijn projection of erase anns (Check spine only). -/
  boundsAnns : ProgramBoundsAnns := {}
  /-- Names for `ofLower` (0 = innermost). From `binderEnvFromGroups` post-infer. -/
  binderEnv : List ValName := []

structure PipelineOk where
  report : ProgramReport
  checkNs : Nat
  evalNs : Nat
  resultPretty : String
  mode : BoundsMode := .default

structure LiveArgs where
  json : Bool := false
  bl : Bool := false
  path : Option String := none

/-- Read actual group-exit schemes by logical binder identity. Empty surface
groups emit no Core node; every nonempty top-level group emits one `letRec`.
Neither inferred RHS monotypes nor the deleted elaboration wrapper spine are
used to reconstruct generalisation. -/
private def foundTopBindingTypes (groups : List (List Surface.Binding))
    (core : Expr) (schemes : BinderSchemeMap) : Option (List (ValName × PolyTy)) :=
  let rec go (groups : List (List Surface.Binding)) (path : CorePath) :
      Option (List (ValName × PolyTy)) := do
    match groups with
    | [] => pure []
    | group :: rest =>
        if group.isEmpty then go rest path
        else
          let here ← group.zipIdx.mapM fun (binding, member) => do
            -- Declared members are validated by inference but intentionally
            -- absent from the inferred-scheme map. Read their actual lowered
            -- declaration, including any head-parameter desugaring.
            let declared := match core.atCorePath path with
              | some (.letRec anns _ _) => anns[member]?.getD none
              | _ => none
            let inferred := (schemes.find? fun (site, _) =>
              site == .letRec path member).map (·.2)
            let scheme ← declared.orElse (fun _ => inferred)
            pure (binding.name, scheme)
          let later ← go rest (path ++ [.letRecBody])
          pure (here ++ later)
  go groups []

/-- Parse → provenance-aware lower → found inference → optional verified bounds
checking → erased execution. HM and BL consume the same inferred artifact. -/
def checkPipeline (mode : BoundsMode) (src : String) :
    IO (Except PipelineErr CheckedProgram) := do
  let tCheck0 ← IO.monoNanosNow
  let (p, binders, sp) ← match parseProgramWithSpans src with
    | .error e =>
        return .error {
          stage := .parse
          message := s!"{e.msg} (line {e.line}, col {e.col})"
          line := e.line
          col := e.col
          endLine := e.endLine
          endCol := e.endCol
        }
    | .ok parsed => pure parsed

  -- Presentation-only compatibility: acceptance never consumes this erased
  -- package. Core inference itself owns Path R erasure in both modes.
  let ep := if mode == .hm then none else some (eraseProgram p)

  let (ctors, _) ← match lowerProgram p with
    | none =>
        -- Prefer a concrete free-name message when possible (editor path has spans).
        let free := freeNamesD [] p.term
        let message :=
          match free with
          | ⟨n⟩ :: _ => s!"unbound name `{n}`"
          | [] =>
              "lowering failed (unbound name, bad decl, or rejected sugar)"
        return .error { stage := .lower, message }
    | some x => pure x

  let scope :=
    let spans := binders.map (·.span) ++ sp.groups.flatMap (·.map Surface.Span.SpannedExpr.span)
      ++ [sp.body.span]
    (Surface.Span.Span.hull spans).getD sp.body.span
  let tree ← match FHM.Unverified.HMArtifacts.programSpanned p sp scope with
    | none => return .error {
        stage := .lower
        message := "internal parser provenance shape mismatch"
      }
    | some tree => pure tree
  let lowered ← match SurfaceBridge.Provenance.lowerWithProvenance ctors p.term tree with
    | none => return .error { stage := .lower, message := "provenance-aware lowering failed" }
    | some lowered => pure lowered
  let typed ← match SurfaceBridge.Provenance.inferWithProvenance ctors lowered with
    | none => return .error { stage := .typecheck, message := "typechecking failed" }
    | some typed => pure typed
  let τ := typed.inference.ty
  let found := typed.inference
  let checkedBodyBounds ←
    if mode == .bl then
      match FHM.Bounds.RecursiveFound.synthNodes typed with
      | .error msg => return .error { stage := .bounds, message := msg }
      | .ok (result, _) => pure (some result.bounds)
    else
      pure none
  let tCheck1 ← IO.monoNanosNow
  let bodyσ := genScheme [] [] τ
  -- Slice 2: Core body env order (0 = innermost) from the same groups Infer used.
  let binderEnv := binderEnvFromGroups p.groups
  let boundsAnns := (ep.map (ProgramBoundsAnns.ofLower binderEnv)).getD {}
  let bindings ← match foundTopBindingTypes p.groups lowered.expr found.binderSchemes with
    | some bindings => pure bindings
    | none => return .error {
        stage := .typecheck
        message := "internal inference artifact error: missing top-level binder scheme"
      }
  let report0 :=
    if mode == .bl then
      match ep with
      | some erased => assembleFromBindings bindings bodyσ erased
      | none => { programHm := bodyσ }
    else
      { bindings := bindings.map fun (name, hm) =>
          let binding := (p.groups.flatMap id).find? (fun b => b.name == name)
          let ann := binding.bind (fun b => finalizeAnn b.tyParams b.params b.ann)
          let names := FHM.Unverified.HMArtifacts.displayNames ann
          { name, hm := hm.eraseBounds
            synthPretty? := some (FHM.Unverified.HMDisplay.scheme {} names hm) }
        programHm := bodyσ.eraseBounds
        programSynthPretty? := some (FHM.Unverified.HMDisplay.scheme {} [] bodyσ) }
  let report := match checkedBodyBounds with
    | some β => report0.enrichFromSynth binderEnv [] (some β.pretty)
    | none => report0

  if mode != .bl then
    if !(checkExhaustive ctors p.term) then
      return .error { stage := .exhaustiveness, message := "match not exhaustive" }

  let e := found.output.erase

  return .ok {
    report := report
    checkNs := tCheck1 - tCheck0
    elaborated := e
    mode := mode
    erased := ep
    boundsAnns := boundsAnns
    binderEnv := binderEnv
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
        report := c.report
        checkNs := c.checkNs
        evalNs := tEval1 - tEval0
        resultPretty := v.pretty
        mode := c.mode
      }

def PipelineOk.toJson (r : PipelineOk) : Lean.Json :=
  let binds := r.report.bindings.map fun b =>
    Lean.Json.mkObj [
      ("name", Lean.Json.str (prettyValName b.name)),
      ("type", Lean.Json.str b.pretty)
    ]
  Lean.Json.mkObj [
    ("version", Lean.Json.num 1),
    ("ok", Lean.Json.bool true),
    ("mode", Lean.Json.str (if r.mode == .bl then "bl" else "hm")),
    ("bindings", Lean.Json.arr binds.toArray),
    ("programTy", Lean.Json.str r.report.programPretty),
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
    ("col", Lean.Json.num e.col),
    ("endLine", Lean.Json.num e.endLine),
    ("endCol", Lean.Json.num e.endCol)
  ]

/-- Parse CLI: optional `--json`, `--bl`, optional path. -/
def parseArgs (args : List String) : Except String LiveArgs :=
  let rec go (as : List String) (acc : LiveArgs) : Except String LiveArgs :=
    match as with
    | [] => .ok acc
    | "--json" :: rest =>
        if acc.json then .error "duplicate --json"
        else go rest { acc with json := true }
    | "--bl" :: rest =>
        if acc.bl then .error "duplicate --bl"
        else go rest { acc with bl := true }
    | "-h" :: _ | "--help" :: _ =>
        .error "usage: blt [--json] [--bl] [path]\n\
  no path (human): scratch/live.fhm\n\
  no path (--json): read stdin\n\
  path: read that file\n\
  --bl: allow BL syntax (erase + run; bounds check later)"
    | flag :: rest =>
        if flag.startsWith "-" then
          .error s!"unknown flag: {flag}\nusage: blt [--json] [--bl] [path]"
        else if acc.path.isSome then
          .error "usage: blt [--json] [--bl] [path]"
        else
          go rest { acc with path := some flag }
  go args {}

def runLive (args : List String) : IO UInt32 := do
  let liveArgs ← match parseArgs args with
    | .error msg =>
        IO.eprintln msg
        return 2
    | .ok x => pure x

  let mode : BoundsMode := if liveArgs.bl then .bl else .default

  let src ← match liveArgs.path, liveArgs.json with
    | some path, _ => IO.FS.readFile path
    | none, true =>
        let stdin ← IO.getStdin
        stdin.readToEnd
    | none, false => IO.FS.readFile "scratch/live.fhm"

  match ← checkPipeline mode src with
  | .error e =>
      if liveArgs.json then
        IO.println e.toJson.pretty
      else
        let ansi ← Ansi.mkIO
        IO.eprintln (formatErr ansi e.stage e.message)
      return 1
  | .ok checked =>
      if !liveArgs.json then
        let ansi ← Ansi.mkIO
        IO.println (formatReport ansi checked.report)
        IO.println (formatTiming ansi "checked" checked.checkNs)
        IO.println ""
        (← IO.getStdout).flush
        IO.println (ansi.yellow "evaluating…")
        (← IO.getStdout).flush
      match ← evalCheckedIO checked with
      | .error e =>
          if liveArgs.json then
            IO.println e.toJson.pretty
          else
            let ansi ← Ansi.mkIO
            IO.eprintln (formatErr ansi e.stage e.message)
          return 1
      | .ok r =>
          if liveArgs.json then
            IO.println r.toJson.pretty
          else
            let ansi ← Ansi.mkIO
            IO.println s!"{ansi.boldBrightGreen "⟹"}  {ansi.brightCyan r.resultPretty}"
            IO.println (formatTiming ansi "evaluated" r.evalNs)
          return 0
