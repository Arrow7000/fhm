import FHM.Bounds.SchemeVariable

namespace FHM.Bounds.SchemeVariableTests

open SchemeTyping

private def idScheme : Scheme :=
  ⟨⟨1, .arrow (.bvar 0) (.bvar 0)⟩, .arrow (.bvar 0) (.bvar 0),
    by
      change ContainsBvarsUpTo 1 (.arrow (.bvar 0) (.bvar 0))
      exact .arrow (.bvar (by omega)) (.bvar (by omega)),
    by simp [Synth.BoundsTy.toTy, Ty.eraseBounds]⟩

private def n : Count := .var ⟨.rigid, 7⟩
private def caller : BoundsTy := .list n n (.fvar 0)
private def exactList : BoundsTy := .list (.lit 3) (.lit 3) (.prim .char)
private def intFunction : Ty := .arrow (.prim .int) (.prim .int)
private def charFunction : Ty := .arrow (.prim .char) (.prim .char)

private def run (found : Ty) (args : List BoundsTy) (scope : List Nat := []) :=
  SchemeVariable.check [] [.poly idScheme] 0 found args scope

private def succeeds (result : Except String α) : Bool :=
  match result with | .ok _ => true | .error _ => false

private def failsWith (result : Except String α) (needle : String) : Bool :=
  match result with | .ok _ => false | .error message => (message.splitOn needle).length > 1

example {Δ env i found scope} (r : SchemeVariable.Result Δ env i found scope) :
    Derives Δ env (.var i) r.bounds ∧
    Synth.BoundsTy.toTy r.bounds = found.eraseBounds ∧
    ScopedScheme.BoundsScoped scope r.bounds := ⟨r.derivation, r.shape, r.countScope⟩

private def cases : List (String × Bool) := [
  ("Int scheme variable", succeeds (run intFunction [.prim .int])),
  ("independent Char scheme variable", succeeds (run charFunction [.prim .char])),
  ("exact list bounds remain in result", match run
      (.arrow (Synth.BoundsTy.toTy exactList) (Synth.BoundsTy.toTy exactList)) [exactList] with
    | .ok r => match r.bounds with
      | .arrow (.list (.lit 3) (.lit 3) (.prim .char)) (.list (.lit 3) (.lit 3) (.prim .char)) => true
      | _ => false
    | .error _ => false),
  ("caller type and count identities survive", match run
      (.arrow (Synth.BoundsTy.toTy caller) (Synth.BoundsTy.toTy caller)) [caller] [7] with
    | .ok r => match r.bounds with
      | .arrow (.list lo hi (.fvar 0)) (.list lo' hi' (.fvar 0)) => lo == n && hi == n && lo' == n && hi' == n
      | _ => false
    | .error _ => false),
  ("monomorphic variable remains monomorphic", succeeds
      (SchemeVariable.check [] [.mono (.prim .int)] 0 (.prim .int) [] [])),
  ("monomorphic variable rejects scheme arguments", failsWith
      (SchemeVariable.check [] [.mono (.prim .int)] 0 (.prim .int) [.prim .int] []) "monomorphic"),
  ("missing entry rejected", failsWith (SchemeVariable.check [] [] 0 (.prim .int) [] []) "outside"),
  ("missing scheme argument rejected", failsWith (run intFunction []) "disagree"),
  ("wrong argument shape rejected", failsWith (run intFunction [.prim .char]) "disagree"),
  ("repeated final HM slot must agree", failsWith
      (run (.arrow (.prim .int) (.prim .char)) [.prim .int]) "inconsistent"),
  ("unknown caller counts rejected", failsWith (run
      (.arrow (Synth.BoundsTy.toTy caller) (Synth.BoundsTy.toTy caller)) [caller]) "counts"),
  ("intervening mono binding keeps scheme at correct depth", succeeds
      (SchemeVariable.check [] [.mono (.prim .int), .poly idScheme] 1 charFunction [.prim .char] [])),
  ("shadowing mono binding cannot be mistaken for scheme", failsWith
      (SchemeVariable.check [] [.mono (.prim .int), .poly idScheme] 0 charFunction [.prim .char] []) "monomorphic"),
  ("monomorphic final HM mismatch rejected", failsWith
      (SchemeVariable.check [] [.mono (.prim .int)] 0 (.prim .char) [] []) "payload"),
  ("monomorphic captured count scope enforced", failsWith
      (SchemeVariable.check [] [.mono caller] 0 (Synth.BoundsTy.toTy caller) [] []) "counts"),
  ("enclosing HM bound slot rejected", failsWith
      (run (.arrow (.bvar 0) (.bvar 0)) [.bvar 0]) "enclosing bound slot")]

def main : IO Unit := do
  for (name, ok) in cases do
    IO.println s!"{if ok then "PASS" else "FAIL"}: {name}"
    unless ok do throw (IO.userError s!"scheme variable regression: {name}")

#eval main

end FHM.Bounds.SchemeVariableTests
