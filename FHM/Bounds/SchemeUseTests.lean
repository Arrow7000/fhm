import FHM.Bounds.SchemeUse

namespace FHM.Bounds.SchemeUseTests

private def identity : Expr := .lambda none (.var 0)
private def mono : BoundsTy := .arrow (.fvar 7) (.fvar 7)
private def scheme : PolyTy := ⟨1, .arrow (.bvar 0) (.bvar 0)⟩
private theorem typing : Typed.Derives [] [] identity mono := .lambda True.intro (.var rfl)

private def run (found : Ty) (args : List BoundsTy) (scope : List Nat := []) := do
  let a ← BinderBridge.abstract scheme mono ([] ++ identity.tyFreeVars.map Ty.fvar)
  SchemeUse.check a typing found args scope

private def n : Count := .var ⟨.rigid, 7⟩
private def caller : BoundsTy := .list n n (.fvar 7)
private def callerHM : Ty := Synth.BoundsTy.toTy caller
private def exactCaller : BoundsTy := .list (.lit 3) (.lit 3) (.prim .char)
private def countedMono : BoundsTy := .arrow (.list n n (.fvar 7)) (.list n n (.fvar 7))
private def countedScheme : PolyTy := ⟨1, .arrow (listTy (.bvar 0)) (listTy (.bvar 0))⟩
private theorem countedTyping : Typed.Derives [] [] identity countedMono :=
  .lambda True.intro (.var rfl)

private def runCounted (scope : List Nat) := do
  let a ← BinderBridge.abstract countedScheme countedMono ([] ++ identity.tyFreeVars.map Ty.fvar)
  SchemeUse.check a countedTyping (.arrow (listTy (.prim .char)) (listTy (.prim .char)))
    [.prim .char] scope

private def succeeds (result : Except String α) : Bool :=
  match result with | .ok _ => true | .error _ => false

private def failsWith (result : Except String α) (needle : String) : Bool :=
  match result with | .ok _ => false | .error message => (message.splitOn needle).length > 1

-- Accepted executable output exposes the complete declarative proof and HM
-- correspondence, not only a bool verdict or a guessed bounds report.
example {found scope} (result : SchemeUse.Result [] [] identity found scope) :
    Typed.Derives [] [] identity result.bounds ∧
    Synth.BoundsTy.toTy result.bounds = found.eraseBounds ∧
    ScopedScheme.BoundsScoped scope result.bounds :=
  ⟨result.derivation, result.shape, result.countScope⟩

private def cases : List (String × Bool) := [
  ("independent Int identity use", succeeds (run (.arrow (.prim .int) (.prim .int)) [.prim .int])),
  ("independent Char identity use", succeeds (run (.arrow (.prim .char) (.prim .char)) [.prim .char])),
  ("exact caller list bounds retained", match run
      (.arrow (Synth.BoundsTy.toTy exactCaller) (Synth.BoundsTy.toTy exactCaller)) [exactCaller] with
    | .ok r => match r.bounds with
      | .arrow (.list (.lit 3) (.lit 3) (.prim .char)) (.list (.lit 3) (.lit 3) (.prim .char)) => true
      | _ => false
    | .error _ => false),
  ("caller identity collision accepted unchanged", match run (.arrow callerHM callerHM) [caller] [7] with
    | .ok r => match r.bounds with
      | .arrow (.list lo hi (.fvar 7)) (.list lo' hi' (.fvar 7)) => lo == n && hi == n && lo' == n && hi' == n
      | _ => false
    | .error _ => false),
  ("unknown caller count rejected", failsWith (run (.arrow callerHM callerHM) [caller]) "argument counts"),
  ("wrong bounds argument shape rejected", failsWith
      (run (.arrow (.prim .int) (.prim .int)) [.prim .char]) "disagree"),
  ("missing bounds argument rejected", failsWith
      (run (.arrow (.prim .int) (.prim .int)) []) "disagree"),
  ("extra bounds argument rejected", failsWith
      (run (.arrow (.prim .int) (.prim .int)) [.prim .int, .prim .char]) "disagree"),
  ("inconsistent repeated final HM slot rejected", failsWith
      (run (.arrow (.prim .int) (.prim .char)) [.prim .int]) "inconsistent"),
  ("enclosing HM bound slot rejected", failsWith
      (run (.arrow (.bvar 0) (.bvar 0)) [.bvar 0]) "enclosing bound slot"),
  ("captured RHS count available", succeeds (runCounted [7])),
  ("captured RHS count cannot silently escape", failsWith (runCounted []) "RHS counts"),
  ("inferable counts are not lexical captures", failsWith (run
      (.arrow (listTy (.prim .char)) (listTy (.prim .char)))
      [.list (.var ⟨.inferable, 7⟩) .inf (.prim .char)] [7]) "argument counts"),
  ("ground infinity endpoint remains legal", succeeds (run
      (.arrow (listTy (.prim .char)) (listTy (.prim .char)))
      [.list (.lit 0) .inf (.prim .char)]))]

def main : IO Unit := do
  for (name, ok) in cases do
    IO.println s!"{if ok then "PASS" else "FAIL"}: {name}"
    unless ok do throw (IO.userError s!"certified scheme use regression: {name}")

#eval main

end FHM.Bounds.SchemeUseTests
