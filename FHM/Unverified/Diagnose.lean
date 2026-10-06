import FHM.Unverified.EditorSupport

/-!
# Editor diagnostics + hover symbols driver

Reads a `.fhm` source file (or stdin) and prints a versioned JSON object:

```
{
  "version": 3,
  "diagnostics": [...],
  "symbols": [
    {"name":"map","kind":"val","type":"...","startLine":…,"startCol":…,"endLine":…,"endCol":…,
     "scopeStartLine":…,"scopeStartCol":…,"scopeEndLine":…,"scopeEndCol":…,
     "def":true},
    ...
  ],
  "tokens": [[startLine, startCol, endLine, endCol, "ident"], ...],
  "programTy": "..."
}
```

`def` marks definition sites (as opposed to occurrences). `tokens` lists every
lexer token with its class (`comment`, `ident`, `keyword`, `lit`, `op`,
`punct`), so editors can tell what a position is on.

On parse failure: diagnostics and tokens only, empty `symbols` array, no
`programTy`.
Line/col are 1-based half-open spans (same as `ParseError` / the lexer).
-/

open Lean

def diagnoseUsage : String :=
  "usage: fhm diagnose [path]\n\
   with path: read that file\n\
   without: read source from stdin"

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
  let payload := diagnosePayload src
  IO.println payload.pretty
  let hasDiags :=
    match payload.getObjVal? "diagnostics" with
    | .ok (.arr a) => !a.isEmpty
    | _ => true
  return (if hasDiags then 1 else 0)
