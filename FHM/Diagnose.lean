import FHM.EditorSupport
import Lean.Data.Json

/-!
# Editor diagnostics + hover symbols driver

Reads a `.fhm` source file (or stdin) and prints a versioned JSON object:

```
{
  "version": 3,
  "diagnostics": [...],
  "symbols": [
    {"name":"map","kind":"val","type":"...","startLine":…,"startCol":…,"endLine":…,"endCol":…,
     "scopeStartLine":…,"scopeStartCol":…,"scopeEndLine":…,"scopeEndCol":…},
    ...
  ],
  "programTy": "..."
}
```

On parse failure: diagnostics only, empty `symbols` array, no `programTy`.
Line/col are 1-based half-open spans (same as `ParseError` / the lexer).
-/

open Lean

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
  let payload := diagnosePayload src
  IO.println payload.pretty
  let hasDiags :=
    match payload.getObjVal? "diagnostics" with
    | .ok (.arr a) => !a.isEmpty
    | _ => true
  return (if hasDiags then 1 else 0)
