import FHM.Unverified.EditorSupport
import FHM.Unverified.HMFrontend
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
  "usage: fhm diagnose [path]\n\
   with path: read that file\n\
   without: read source from stdin"

/-- Reject retired bounds syntax before the still-transitional parser can hand
it to the Path-R HM stack.  Parse errors remain owned by `diagnosePayload`. -/
def diagnosePayloadHM (src : String) : Lean.Json :=
  match Surface.Parse.parseProgramWithSpans src with
  | .ok (program, _, _) =>
      if FHM.Unverified.HMFrontend.programContainsBounds program then
        let diagnostic : HoverDiag := {
          message := FHM.Unverified.HMFrontend.unsupportedMessage
        }
        Lean.Json.mkObj [
          ("version", Lean.Json.num 3),
          ("diagnostics", Lean.Json.arr #[diagnostic.toJson]),
          ("symbols", Lean.Json.arr #[])
        ]
      else
        diagnosePayload src
  | .error _ => diagnosePayload src

def runDiagnose (args : List String) : IO UInt32 := do
  let src ← match args with
    | [] =>
      let stdin ← IO.getStdin
      stdin.readToEnd
    | ["-h"] | ["--help"] =>
      IO.eprintln diagnoseUsage
      return 0
    | [path] =>
      if path.startsWith "-" then
        IO.eprintln diagnoseUsage
        return 2
      else
        IO.FS.readFile path
    | _ =>
      IO.eprintln diagnoseUsage
      return 2
  let payload := diagnosePayloadHM src
  IO.println payload.pretty
  let hasDiags :=
    match payload.getObjVal? "diagnostics" with
    | .ok (.arr a) => !a.isEmpty
    | _ => true
  return (if hasDiags then 1 else 0)
