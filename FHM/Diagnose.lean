import FHM.Surface.Parse
import Lean.Data.Json

/-!
# Parse-only diagnostics driver

Reads a `.fhm` source file (or stdin) and prints a JSON array of diagnostics:

```
[{"severity":"error","message":"...","line":1,"col":3}]
```

Line/col are 1-based (same as `ParseError` / the lexer). Intended for the
VS Code/Cursor extension's `didChange` diagnostic loop — no typechecking.
-/

open Surface.Parse
open Lean

def diagnose (src : String) : Array Json :=
  match parseProgram src with
  | .ok _ => #[]
  | .error e =>
    #[Json.mkObj [
      ("severity", Json.str "error"),
      ("message", Json.str e.msg),
      ("line", Json.num e.line),
      ("col", Json.num e.col)
    ]]

def usage : String :=
  "usage: fhm_diagnose [path]\n\
   with path: read that file\n\
   without: read source from stdin"

def main (args : List String) : IO UInt32 := do
  let src ← match args with
    | [] =>
      let stdin ← IO.getStdin
      stdin.readToEnd
    | [path] => IO.FS.readFile path
    | _ =>
      IO.eprintln usage
      return 2
  let ds := diagnose src
  IO.println (Json.arr ds).pretty
  return (if ds.isEmpty then 0 else 1)
