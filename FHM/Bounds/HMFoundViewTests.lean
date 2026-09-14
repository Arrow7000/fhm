import FHM.Bounds.HMFoundView

namespace FHM.Bounds.HMFoundViewTests

open HMFoundView

private def n : Count := .var ⟨.rigid, 7⟩
private def callerType : BoundsTy := .list n n (.prim .int)
private def interpretation (i : Nat) : BoundsTy := if i = 90 then callerType else .fvar i
private def output : Expr := .found (.arrow (.fvar 90) (.fvar 90))
  (.lambda none (.found (.fvar 90) (.var 0)))
private def succeeds (r : Except String α) : Bool := match r with | .ok _ => true | _ => false
private def fails (r : Except String α) : Bool := !succeeds r

private def checked (path : CorePath) (actual : BoundsTy) (scope : List Nat := [7]) : Except String Unit := do
  let node ← locate output path
  let _ ← checkShape node interpretation scope actual
  pure ()

private def collision (path : CorePath) : Bool :=
  match locate output path with
  | .ok node => match node.view interpretation with
      | .customTy name [.prim .int] => name == FHM.Bounds.listTyName
      | _ => false
  | _ => false

private def simultaneous : Bool :=
  let types (i : Nat) : BoundsTy := if i = 90 then .fvar 91 else if i = 91 then .prim .int else .fvar i
  match ty types (.fvar 90) with
  | .fvar 91 => true
  | _ => false

private def typed (scope : List Nat) : Except String Unit := do
  let node : AtNode output [] :=
    ⟨.arrow (.fvar 90) (.fvar 90), .lambda none (.found (.fvar 90) (.var 0)),
      by simp [Expr.atCorePath, output]⟩
  let actual := BoundsTy.arrow callerType callerType
  have derivation : RecursiveHMJudgement.Derives interpretation [7] [] [] [] node.inner.stripFound actual := by
    simp only [node, actual, Expr.stripFound]
    exact .lambda True.intro (.varMono rfl)
  let _ ← checkTyped node interpretation [7] [] [] [] scope actual derivation
  pure ()

private def cases : List (String × Bool) := [
  ("root HM view specializes a more-general discovered identity", succeeds
    (checked [] (.arrow callerType callerType))),
  ("the same interpretation reaches the exact lambda body", succeeds
    (checked [.lambdaBody] callerType)),
  ("the original Core path locates the unchanged found node", collision [.lambdaBody]),
  ("a node cannot silently retain the old opaque identity", fails
    (checked [.lambdaBody] (.fvar 90))),
  ("an interpreted shape cannot accept the wrong element type", fails
    (checked [.lambdaBody] (.list n n (.prim .char)))),
  ("actual caller counts still require explicit scope", fails
    (checked [.lambdaBody] callerType [])),
  ("shape views do not claim exact intervals from HM alone", succeeds
    (checked [.lambdaBody] (.list (.lit 0) .inf (.prim .int)) [])),
  ("a missing Core path cannot be reconciled externally", fails (locate output [.appArg])),
  ("a non-found node cannot invent a discovered payload", fails (locate (.var 0) [])),
  ("one simultaneous interpretation does not rewrite identities inside an inserted caller type", simultaneous),
  ("typed views retain a genuine derivation for the unchanged source node", succeeds (typed [7])),
  ("a genuine derivation still cannot bypass caller count-scope checks", fails (typed []))]

example (τ : Ty) : ty (fun _ => .list (.lit 2) (.lit 2) (.prim .int)) τ =
    ty (fun _ => .list (.lit 0) .inf (.prim .int)) τ := by
  apply counts_blind
  intro i
  simp only [Synth.BoundsTy.toTy]

def main : IO Unit := do
  for (name, ok) in cases do
    IO.println s!"{if ok then "PASS" else "FAIL"}: {name}"
    unless ok do throw (IO.userError s!"found HM view regression failed: {name}")

#eval main

end FHM.Bounds.HMFoundViewTests
