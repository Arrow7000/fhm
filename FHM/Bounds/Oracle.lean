import FHM.Bounds.Kernel
import FHM.Z3.Oracle
import FHM.Z3.Encode

/-!
# Bounds oracles — Z3-backed problem-language interface

**Status:** P1 API for sign-off.

Definitional wrappers over `FHM.Z3` (one IO fiction at `z3Run`). Soundness axioms
at the BL problem-language level until encoding lemmas land.
-/

namespace FHM.Bounds

inductive ValidVerdict where
  | valid | invalid | unknown
  deriving DecidableEq, Repr

inductive SolveVerdict where
  | witness (σ : Assign)
  | unsat
  | unknown

inductive UniqueVerdict where
  | unique | multiple | unknown
  deriving DecidableEq, Repr

instance : Inhabited ValidVerdict := ⟨.unknown⟩
instance : Inhabited SolveVerdict := ⟨.unknown⟩
instance : Inhabited UniqueVerdict := ⟨.unknown⟩

namespace Z3Bridge

open FHM.Z3 (Atom Assumptions Config Verdict decide decideGoals)
open FHM.Z3

def varName (v : Var) : String :=
  match v.kind with
  | .rigid     => s!"r_{v.idx}"
  | .inferable => s!"i_{v.idx}"

def countToExpr : Count → FHM.Z3.Expr
  | .lit n   => .lit n
  | .var v   => .name (varName v)
  | .add a b => .add (countToExpr a) (countToExpr b)
  | .mul a b => .mul (countToExpr a) (countToExpr b)
  | .pred a  => .pred (countToExpr a)
  | .min a b => .min (countToExpr a) (countToExpr b)
  | .max a b => .max (countToExpr a) (countToExpr b)

def constraintToAtom (c : Constraint) : Atom :=
  .le (countToExpr c.lhs) (countToExpr c.rhs)

def constraintsToAssumptions (cs : List Constraint) : Assumptions :=
  cs.map constraintToAtom

def inferableNames (vs : List Var) : List String :=
  vs.filter (·.kind = .inferable) |>.map varName |>.eraseDups

def modelToAssign (model : List (String × Nat)) : Assign :=
  fun v =>
    model.find? (fun p => p.1 = varName v) |>.map (·.2) |>.getD 0

def checkValidZ3 (φ : ForallProblem) : ValidVerdict :=
  let as := constraintsToAssumptions φ.prem
  let goals := φ.goals.map constraintToAtom
  if goals.isEmpty then .valid
  else
    let results := goals.map fun g => decide { assumptions := as, goal := g }
    if results.any Verdict.isRefuted then .invalid
    else if results.all Verdict.isVerified then .valid
    else .unknown

def solveZ3 (ψ : ExistsProblem) : SolveVerdict :=
  let unknowns := inferableNames ψ.inferables
  let as := constraintsToAssumptions ψ.prem
  let goals := constraintsToAssumptions ψ.cons
  if unknowns.isEmpty && goals.isEmpty then
    .witness (fun _ => 0)
  else
    match decideGoals unknowns as goals with
    | .witness b => .witness (modelToAssign b)
    | .unknown "z3 reports no witness exists" => .unsat
    | _ => .unknown

def isWitnessUnsat : FHM.Z3.Verdict → Bool
  | .unknown "z3 reports no witness exists" => true
  | _ => false

/-- Honesty: `.unique` only if every alternative is strong unsat; unknown ≠ unique. -/
def uniqueZ3 (ψ : ExistsProblem) (outs : List Count) : UniqueVerdict :=
  match solveZ3 ψ with
  | .unsat => .unknown
  | .unknown => .unknown
  | .witness σ =>
    let vals := outs.map (·.eval σ)
    let unknowns := inferableNames ψ.inferables
    let baseAs := constraintsToAssumptions (ψ.prem ++ ψ.cons)
    let goals := constraintsToAssumptions ψ.cons
    let differs (c : Count) (v : Nat) : List Assumptions :=
      [[.lt (countToExpr c) (.lit v)], [.lt (.lit v) (countToExpr c)]]
    let statuses : List (Option Bool) :=
      (outs.zip vals).flatMap fun (c, v) =>
        (differs c v).map fun extra =>
          match decideGoals unknowns (baseAs ++ extra) goals with
          | .witness _ => some true
          | v => if isWitnessUnsat v then some false else none
    if statuses.any (· == some true) then .multiple
    else if statuses.any (· == none) then .unknown
    else .unique

end Z3Bridge

def checkValid (φ : ForallProblem) : ValidVerdict :=
  Z3Bridge.checkValidZ3 φ

def solve (ψ : ExistsProblem) : SolveVerdict :=
  Z3Bridge.solveZ3 ψ

def unique (ψ : ExistsProblem) (outs : List Count) : UniqueVerdict :=
  Z3Bridge.uniqueZ3 ψ outs

/-- Positive ∀ answers are sound. (Axiom until encoding lemmas.) -/
axiom checkValid_sound (φ : ForallProblem) :
    checkValid φ = .valid → φ.Valid

/-- Positive ∃ witness answers are sound. (Axiom until multi-goal bridge proved.) -/
axiom solve_sound (ψ : ExistsProblem) (σ : Assign) :
    solve ψ = .witness σ → ψ.SolvedBy σ

/-- Positive uniqueness answers are sound. (Axiom; completeness of solver not assumed elsewhere.) -/
axiom unique_sound (ψ : ExistsProblem) (outs : List Count) :
    unique ψ outs = .unique → ψ.UniqueOutputs outs

theorem checkValid_empty_goals (prem : List Constraint) :
    checkValid ⟨prem, []⟩ = .valid := by
  rfl

end FHM.Bounds
