import FHM.Z3.Encode
import FHM.Z3.Parse

/-!
# FHM — IO-based Z3 driver (subprocess)

Adapted from Percissus.Fresh.Z3.Process.
-/

namespace FHM.Z3
namespace Process

def runZ3 (script : String) (timeoutMs : UInt32) : IO (Except String String) := do
  try
    let timeoutSecs : UInt32 := max 1 ((timeoutMs + 999) / 1000)
    let child ← IO.Process.spawn
      { cmd := "z3"
        args := #["-in", "-smt2", s!"-T:{timeoutSecs}", s!"-t:{timeoutMs}"]
        stdin := .piped
        stdout := .piped
        stderr := .piped }
    let (stdin, child) ← child.takeStdin
    stdin.putStr script
    stdin.putStr "\n(exit)\n"
    stdin.flush
    let stdout ← child.stdout.readToEnd
    let stderr ← child.stderr.readToEnd
    let _ ← child.wait
    if stderr.trim != "" then
      return .ok (stdout ++ "\n" ++ stderr)
    return .ok stdout
  catch e =>
    return .error s!"z3 process failed: {e}"

def decideIO (q : Query) (cfg : Config := .default) : IO Verdict := do
  let script :=
    if q.unknowns.isEmpty then Encode.Query.toCheckScript q cfg
    else Encode.Query.toWitnessScript q cfg
  match ← runZ3 script cfg.timeoutMs with
  | .ok output =>
      if q.unknowns.isEmpty then
        return Parse.checkOutput output
      else
        return Parse.witnessOutput q.unknowns output
  | .error msg => return .unknown msg

def decideSatIO (assumptions : Assumptions) (cfg : Config := .default) : IO SatVerdict := do
  let script := Encode.toSatScript assumptions cfg
  match ← runZ3 script cfg.timeoutMs with
  | .ok output => return Parse.satOutput output
  | .error msg => return .unknown msg

structure Trace where
  query   : Query
  config  : Config
  script  : String
  verdict : Verdict
  deriving Repr

def traceIO (q : Query) (cfg : Config := .default) : IO Trace := do
  let script :=
    if q.unknowns.isEmpty then Encode.Query.toCheckScript q cfg
    else Encode.Query.toWitnessScript q cfg
  match ← runZ3 script cfg.timeoutMs with
  | .ok output =>
      let verdict :=
        if q.unknowns.isEmpty then Parse.checkOutput output
        else Parse.witnessOutput q.unknowns output
      return { query := q, config := cfg, script, verdict }
  | .error msg =>
      return { query := q, config := cfg, script,
               verdict := .unknown msg }

end Process
end FHM.Z3
