import Lean.Data.Json
import EPL.Surface.Run

/-!
# The `epl` executable

```
epl [run] [--fuel N] [path]   check and evaluate (at most N steps): print each
                              top-level binding's type and the program's, then
                              its value, as `fhm run` does
epl check [path]              check only; print the program's type
epl diagnose [path]           editor JSON: the first error, if any
```

Each command reads `path`, or standard input if there is none. `run` and
`check` print an error as `[stage] path:line:col: message` on standard error
and exit with status 1. Output is coloured on a terminal (or with
`FORCE_COLOR`, and not with `NO_COLOR`).

`diagnose` prints the shape `fhm diagnose` does (version 3), so the editor
extension can share its code. Positions are 1-based UTF-16, with an exclusive
end. `diagnostics` holds at most one entry. If the program checks, `symbols`
holds the names it defines and uses and its expressions, with their types (see
`Symbol`). `tokens` holds every token and comment, for placing hovers.
-/

namespace EPL.Surface.Main

open Lean (Json)

def usage : String := "\n".intercalate [
  "usage: epl [run] [--fuel N] [path]   check and evaluate a program (at most N steps)",
  "       epl check [path]              check a program and print its type",
  "       epl diagnose [path]           editor diagnostics as JSON",
  "With no path, the program is read from standard input."]

def defaultFuel : Nat := 1000000

/-- The source and the name to report it under. -/
def readSource : Option String → IO (String × String)
  | some path => do pure (← IO.FS.readFile path, path)
  | none => do pure (← (← IO.getStdin).readToEnd, "<stdin>")

/-- The UTF-16 column of codepoint column `col` (both 1-based) on `line`. -/
def utf16Col (lines : Array String) (line col : Nat) : Nat :=
  let text := (lines[line - 1]?).getD ""
  1 + ((text.toList.take (col - 1)).map fun c => if c.val > 0xFFFF then 2 else 1).sum

def _root_.EPL.Surface.Error.code : Error → String
  | .lex _ => "epl.lex"
  | .parse _ => "epl.parse"
  | .lower _ => "epl.lower"
  | .infer .. | .notAFunction .. => "epl.type"
  | .notExhaustive .. | .notExhaustiveUnlocated => "epl.coverage"

/-- A span's fields with UTF-16 columns: `startLine`, ..., `endCol`, or
`scopeStartLine`, ... with the prefix `scope`. -/
def spanFields (lines : Array String) (span : Span) (pre : String := "") :
    List (String × Json) :=
  let key (name : String) := if pre.isEmpty then name.decapitalize else pre ++ name
  [(key "StartLine", span.start.line),
   (key "StartCol", utf16Col lines span.start.line span.start.col),
   (key "EndLine", span.stop.line),
   (key "EndCol", utf16Col lines span.stop.line span.stop.col)]

def _root_.EPL.Surface.Symbol.toJson (lines : Array String) (symbol : Symbol) : Json :=
  Json.mkObj <| [
    ("name", Json.str symbol.name),
    ("kind", Json.str symbol.kind),
    ("type", Json.str symbol.ty),
    ("def", Json.bool symbol.isDef)] ++
    spanFields lines symbol.span ++ spanFields lines symbol.scope "scope"

/-- The editor's class for a token. -/
def tokenClass : Token → String
  | .ident .. | .namedHole _ => "ident"
  | .keyword _ => "keyword"
  | .int _ | .char _ | .string _ => "lit"
  | .op _ => "op"
  | .punct _ => "punct"

/-- The tokens and comments of `source` as `[startLine, startCol, endLine,
endCol, class]` rows in source order; none if it does not lex. -/
def tokenRows (lines : Array String) (source : String) : Array Json :=
  match lexWithComments source with
  | .error _ => #[]
  | .ok (tokens, comments) =>
      let rows := tokens.map (fun tok => (tok.span, tokenClass tok.token)) ++
        comments.map (·, "comment")
      let before (a b : Span × String) : Bool :=
        a.1.start.line < b.1.start.line ||
          (a.1.start.line == b.1.start.line && a.1.start.col < b.1.start.col)
      (rows.qsort before).map fun (span, cls) => Json.arr #[
        span.start.line, utf16Col lines span.start.line span.start.col,
        span.stop.line, utf16Col lines span.stop.line span.stop.col, Json.str cls]

def _root_.EPL.Surface.Error.toJson (lines : Array String) (error : Error) : Json :=
  let span := error.span.getD ⟨⟨1, 1⟩, ⟨1, 1⟩⟩
  Json.mkObj [
    ("severity", "error"),
    ("code", error.code),
    ("message", error.message),
    ("line", span.start.line),
    ("col", utf16Col lines span.start.line span.start.col),
    ("endLine", span.stop.line),
    ("endCol", utf16Col lines span.stop.line span.stop.col)]

def diagnose (source : String) : Json :=
  let lines := (source.splitOn "\n").toArray
  let (diagnostics, symbols, programTy) := match checkWithTypes source with
    | .ok (lowering, result, types) =>
        (#[], (lowering.symbols types).map (Symbol.toJson lines),
          some (showSemTy lowering.globals result.ty))
    | .error error => (#[error.toJson lines], #[], none)
  Json.mkObj <| [
    ("version", Json.num 3),
    ("diagnostics", Json.arr diagnostics),
    ("symbols", Json.arr symbols),
    ("tokens", Json.arr (tokenRows lines source))] ++
    (programTy.map fun ty => [("programTy", Json.str ty)]).getD []

/-! ## Terminal output, in `fhm run`'s style -/

/-- Whether to colour output: `FORCE_COLOR` wins, then `NO_COLOR`, else
whether standard output is a terminal. -/
structure Ansi where
  on : Bool

def Ansi.mkIO : IO Ansi := do
  if (← IO.getEnv "FORCE_COLOR").isSome then return ⟨true⟩
  if (← IO.getEnv "NO_COLOR").isSome then return ⟨false⟩
  return ⟨← (← IO.getStdout).isTty⟩

/-- Paint `text` with SGR `code` (combine attributes in one code). -/
def Ansi.wrap (ansi : Ansi) (code text : String) : String :=
  if ansi.on then s!"\x1b[{code}m{text}\x1b[0m" else text

/-- A duration in the largest unit that keeps it above 1. -/
def formatDuration (ns : Nat) : String :=
  if ns < 1000 then s!"{ns}ns"
  else if ns < 1000000 then s!"{ns / 1000}µs"
  else if ns < 1000000000 then s!"{ns / 1000000}ms"
  else
    let hundredths := (ns % 1000000000) / 10000000
    s!"{ns / 1000000000}.{if hundredths < 10 then "0" else ""}{hundredths}s"

def formatTiming (ansi : Ansi) (label : String) (ns : Nat) : String :=
  ansi.wrap "2" s!"  ({label} in {formatDuration ns})"

/-- `  name  :  type` -/
def formatBinding (ansi : Ansi) (name ty : String) (nameCode : String := "1;36") : String :=
  s!"  {ansi.wrap nameCode name}  {ansi.wrap "2" ":"}  {ansi.wrap "34" ty}"

def report (name : String) (error : Error) : IO UInt32 := do
  let ansi ← Ansi.mkIO
  let stage := error.code.drop "epl.".length
  IO.eprintln s!"{ansi.wrap "1;31" s!"[{stage}]"} {ansi.wrap "31" s!"{name}:{error.render}"}"
  pure 1

/-- Print the top-level bindings' types and the program's, then the value. -/
def runCommand (fuel : Nat) (path : Option String) : IO UInt32 := do
  let (source, name) ← readSource path
  let ansi ← Ansi.mkIO
  let start ← IO.monoNanosNow
  match checkWithTypes source with
  | .error error => report name error
  | .ok (lowering, result, types) =>
    let checked ← IO.monoNanosNow
    for (binding, ty) in lowering.bindingTypes (lowering.symbols types) do
      IO.println (formatBinding ansi binding ty)
    IO.println (formatBinding ansi "<program>" (showSemTy lowering.globals result.ty) "1;35")
    IO.println (formatTiming ansi "checked" (checked - start))
    IO.println ""
    IO.println (ansi.wrap "33" "evaluating…")
    (← IO.getStdout).flush
    let start ← IO.monoNanosNow
    -- `run` checks the program again: `evaluate` is what proves the result.
    match run source fuel with
    | .ok (lowering, value, _) =>
        let evaluated ← IO.monoNanosNow
        let value := match value with
          | some value => ansi.wrap "96" (showValue lowering.globals value)
          | none => ansi.wrap "33" s!"<ran out of fuel after {fuel} steps>"
        IO.println s!"{ansi.wrap "1;92" "⟹"}  {value}"
        IO.println (formatTiming ansi "evaluated" (evaluated - start))
        pure 0
    | .error error => report name error

def checkCommand (path : Option String) : IO UInt32 := do
  let (source, name) ← readSource path
  match check source with
  | .ok (lowering, result) =>
      IO.println (showSemTy lowering.globals result.ty)
      pure 0
  | .error error => report name error

def usageError : IO UInt32 := do
  IO.eprintln usage
  pure 2

/-- `run`'s options: `--fuel N` and at most one path. -/
def runArgs (fuel : Nat) (path : Option String) : List String → IO UInt32
  | [] => runCommand fuel path
  | "--fuel" :: n :: rest => match n.toNat? with
      | some fuel => runArgs fuel path rest
      | none => usageError
  | arg :: rest =>
      if arg.startsWith "-" || path.isSome then usageError else runArgs fuel (some arg) rest

end EPL.Surface.Main

open EPL.Surface.Main in
def main (args : List String) : IO UInt32 := do
  match args with
  | ["--help"] | ["-h"] | ["help"] => IO.println usage; pure 0
  | ["diagnose"] | ["diagnose", _] =>
      let (source, _) ← readSource args[1]?
      IO.println (diagnose source).compress
      pure 0
  | ["check"] | ["check", _] => checkCommand args[1]?
  | "check" :: _ | "diagnose" :: _ => usageError
  | "run" :: rest => runArgs defaultFuel none rest
  | rest => runArgs defaultFuel none rest
