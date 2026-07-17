import FHM.Z3.Encode
import FHM.Z3.Parse
import FHM.Z3.Process

/-!
# FHM — Z3 oracle

Pure `decide` via `@[implemented_by]` subprocess shim. Adapted from Percissus.
-/

namespace FHM.Z3

unsafe def z3RunImpl (script : @& String) (timeoutMs : UInt32) : String :=
  match unsafeBaseIO (Process.runZ3 script timeoutMs).toBaseIO with
  | .ok (.ok output) => output
  | .ok (.error msg) => s!"(error \"shim: {msg}\")"
  | .error e         => s!"(error \"shim io: {e}\")"

@[implemented_by z3RunImpl]
opaque z3Run (script : @& String) (timeoutMs : UInt32) : String

def decide (q : Query) (cfg : Config := .default) : Verdict :=
  if q.unknowns.isEmpty then
    let script := Encode.Query.toCheckScript q cfg
    Parse.checkOutput (z3Run script cfg.timeoutMs)
  else
    let script := Encode.Query.toWitnessScript q cfg
    Parse.witnessOutput q.unknowns (z3Run script cfg.timeoutMs)

def decideSat (assumptions : Assumptions) (cfg : Config := .default) : SatVerdict :=
  let script := Encode.toSatScript assumptions cfg
  Parse.satOutput (z3Run script cfg.timeoutMs)

def decideGoals
    (unknowns : List String) (assumptions : Assumptions) (goals : List Atom)
    (cfg : Config := .default) : Verdict :=
  if goals.isEmpty then .verified
  else if unknowns.isEmpty then
    let results := goals.map fun g =>
      decide { assumptions, goal := g } cfg
    if results.any Verdict.isRefuted then
      match results.find? Verdict.isRefuted with
      | some v => v
      | none => .unknown "refuted"
    else if results.all Verdict.isVerified then .verified
    else .unknown "partial forall result"
  else
    let script := Encode.toWitnessScriptGoals unknowns assumptions goals cfg
    Parse.witnessOutput unknowns (z3Run script cfg.timeoutMs)

/-- ∀-mode soundness: `.verified` means the goal holds under assumptions. -/
axiom decide_verified_sound {q : Query} {cfg : Config}
    (hUnknowns : q.unknowns = []) :
    decide q cfg = .verified →
    ∀ σ : Assignment,
      Assumptions.Holds σ q.assumptions → q.goal.Holds σ

/-- ∃∀-mode soundness: `.witness b` means the binding makes the goal universal. -/
axiom decide_witness_sound {q : Query} {cfg : Config}
    {b : List (String × Nat)} :
    decide q cfg = .witness b →
    ∀ σ : Assignment,
      (∀ pair ∈ b, σ pair.1 = pair.2) →
      Assumptions.Holds σ q.assumptions →
      q.goal.Holds σ

axiom decide_sat_sound {as : Assumptions} {cfg : Config}
    {b : List (String × Nat)} :
    decideSat as cfg = .sat b →
    ∃ σ : Assignment, Assumptions.Holds σ as

end FHM.Z3
