import FHM.Unverified.EditorSupport
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

def diagnoseUsage : String :=
  "usage: fhm diagnose [--hm|--bl|--auto] [path]\n\
   --hm: Path-R HM checking (default; count claims are unchecked)\n\
   --bl: canonical Bounds checking\n\
   --auto: use Bounds checking when the program contains BL\n\
   with path: read that file\n\
   without: read source from stdin"

def runDiagnose (args : List String) : IO UInt32 := do
  let (mode, paths) := match args with
    | "--hm" :: rest => ("hm", rest)
    | "--bl" :: rest => ("bl", rest)
    | "--auto" :: rest => ("auto", rest)
    | rest => ("hm", rest)
  let src ← match paths with
    | [] =>
      let stdin ← IO.getStdin
      stdin.readToEnd
    | [path] => IO.FS.readFile path
    | _ =>
      IO.eprintln diagnoseUsage
      return 2
  let payload := if mode == "bl" then diagnosePayloadMode true src
    else if mode == "auto" then diagnosePayloadAuto src
    else diagnosePayload src
  IO.println payload.pretty
  let hasDiags :=
    match payload.getObjVal? "diagnostics" with
    | .ok (.arr a) => !a.isEmpty
    | _ => true
  return (if hasDiags then 1 else 0)
