import Lean.Data.Json
import EPL.Surface.Run

/-!
# The `epl` executable

```
epl [run] [--fuel N] [path]   check and evaluate (at most N steps); print `value : type`
epl check [path]              check only; print the program's type
epl diagnose [path]           editor JSON: the first error, if any
```

Each command reads `path`, or standard input if there is none. `run` and
`check` print an error as `path:line:col: message` on standard error and exit
with status 1.

`diagnose` prints the shape `fhm diagnose` does (version 3), so the editor
extension can share its code: `diagnostics` holds at most one entry, with
1-based UTF-16 positions and an exclusive end, and `symbols` is empty.
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

def _root_.EPL.Surface.Error.toJson (source : String) (error : Error) : Json :=
  let lines := (source.splitOn "\n").toArray
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
  let (diagnostics, programTy) := match check source with
    | .ok (lowering, result) => (#[], some (showSemTy lowering.globals result.ty))
    | .error error => (#[error.toJson source], none)
  Json.mkObj <| [
    ("version", Json.num 3),
    ("diagnostics", Json.arr diagnostics),
    ("symbols", Json.arr #[])] ++
    (programTy.map fun ty => [("programTy", Json.str ty)]).getD []

def report (name : String) (error : Error) : IO UInt32 := do
  IO.eprintln s!"{name}:{error.render}"
  pure 1

def runCommand (fuel : Nat) (path : Option String) : IO UInt32 := do
  let (source, name) ← readSource path
  match run source fuel with
  | .ok (lowering, value, ty) =>
      let value := (value.map (showValue lowering.globals)).getD
        s!"<ran out of fuel after {fuel} steps>"
      IO.println s!"{value} : {showSemTy lowering.globals ty}"
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
