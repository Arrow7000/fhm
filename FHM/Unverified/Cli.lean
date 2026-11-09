import FHM.Unverified.Live
import FHM.Unverified.Diagnose

/-!
# Unified FHM CLI

Single executable replacing `fhm_diagnose` and `fhm_live`:

```
fhm diagnose [path]       # editor JSON v3 (stdin if no path)
fhm run [--json] [--fuel N] [path]   # parse → typecheck → eval
fhm [--json] [path]       # default: run (watch-live compat)
```
-/

def usage : String :=
  "usage: fhm <command> [options]\n\
   commands:\n\
     diagnose [path]          editor diagnostics + hover symbols (stdin if no path)\n\
     run [--json] [--fuel N] [path]\n\
                              parse, typecheck, evaluate (at most N steps)\n\
   default (no command): same as run\n\
   \n\
   examples:\n\
     fhm scratch/live.fhm\n\
     fhm --json < program.fhm\n\
     fhm diagnose < program.fhm\n\
     fhm run --json < program.fhm"

-- A line-delimited JSON protocol keeps module initialization out of each edit.
-- Each request runs synchronously; the host kills/replaces this process on
-- cancellation, timeout, or excessive output, just as for one-shot commands.
private def workerPayload (request : Lean.Json) : IO Lean.Json := do
  let src ← IO.ofExcept (request.getObjValAs? String "source")
  let command ← IO.ofExcept (request.getObjValAs? String "command")
  if command == "diagnose" then
    return diagnosePayload src
  if command != "run" && command != "check" then
    throw (IO.userError "unknown worker command")
  let combined := command == "check"
  let fuel := (request.getObjValAs? Nat "fuel").toOption
  match ← checkPipeline src combined with
  | .error e =>
    if combined then
      -- Recovery is editor-only. A rejected strict program is never evaluated.
      return Lean.Json.mkObj [("diagnose", diagnosePayload src), ("run", .null)]
    return e.toJson
  | .ok checked =>
    if combined then
      let some diagnosis := checked.diagnosis?
        | throw (IO.userError "missing checked diagnosis")
      let diagnostics ← IO.ofExcept (diagnosis.getObjValAs? (Array Lean.Json) "diagnostics")
      if diagnostics.any (fun d => (d.getObjValAs? String "severity").toOption != some "warning") then
        return Lean.Json.mkObj [("diagnose", diagnosis), ("run", .null)]
      -- Flush diagnostics before evaluation so the host can enforce its separate
      -- time budget and preserve editor results even when evaluation is killed.
      let stdout ← IO.getStdout
      stdout.putStrLn (Lean.Json.mkObj [("phase", .str "eval"), ("diagnose", diagnosis)]).compress
      stdout.flush
    let result ← match ← evalCheckedIO checked fuel with
      | .error e => pure e.toJson
      | .ok result => pure result.toJson
    return if combined then Lean.Json.mkObj [("run", result)] else result

private def runWorker : IO UInt32 := do
  let stdin ← IO.getStdin
  let stdout ← IO.getStdout
  stdout.putStrLn "{\"ready\":true}"
  stdout.flush
  repeat
    let line ← stdin.getLine
    if line.isEmpty then return 0
    let payload ← try
      workerPayload (← IO.ofExcept (Lean.Json.parse line))
    catch e =>
      pure (Lean.Json.mkObj [("error", Lean.Json.str e.toString)])
    stdout.putStrLn payload.compress
    stdout.flush
  return 0

def main (args : List String) : IO UInt32 := do
  match args with
  | "-h" :: _ | "--help" :: _ =>
      IO.eprintln usage
      return 0
  | ["--worker"] => runWorker
  | "diagnose" :: rest => runDiagnose rest
  | "run" :: rest => runLive rest
  | _ => runLive args
