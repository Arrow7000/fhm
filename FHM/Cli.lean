import FHM.Live
import FHM.Diagnose

/-!
# Unified FHM CLI

Single executable replacing `fhm_diagnose` and `fhm_live`:

```
fhm diagnose [path]       # editor JSON v3 (stdin if no path)
fhm run [--json] [path]   # parse → typecheck → eval
fhm [--json] [path]       # default: run (watch-live compat)
```
-/

def usage : String :=
  "usage: fhm <command> [options]\n\
   commands:\n\
     diagnose [path]          editor diagnostics + hover symbols (stdin if no path)\n\
     run [--json] [--bl] [path]  parse, typecheck, evaluate\n\
   default (no command): same as run\n\
   \n\
   options:\n\
     --bl   allow BL syntax (HM mode rejects it)\n\
   \n\
   examples:\n\
     fhm scratch/live.fhm\n\
     fhm --bl scratch/bl-live.fhm\n\
     fhm --json < program.fhm\n\
     fhm diagnose < program.fhm\n\
     fhm run --json --bl < program.fhm"

def main (args : List String) : IO UInt32 := do
  match args with
  | "-h" :: _ | "--help" :: _ =>
      IO.eprintln usage
      return 0
  | "diagnose" :: rest => runDiagnose rest
  | "run" :: rest => runLive rest
  | _ => runLive args
