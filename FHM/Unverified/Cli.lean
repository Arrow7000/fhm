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
  if command != "run" then
    throw (IO.userError "unknown worker command")
  let fuel := (request.getObjValAs? Nat "fuel").toOption
  match ← checkPipeline src with
  | .error e => return e.toJson
  | .ok checked =>
    match ← evalCheckedIO checked fuel with
    | .error e => return e.toJson
    | .ok result => return result.toJson

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
