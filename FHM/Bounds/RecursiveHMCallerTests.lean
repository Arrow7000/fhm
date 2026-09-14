import FHM.Bounds.RecursiveHMCaller
import FHM.Bounds.HMDeclaredCoordinates
import FHM.Bounds.Found

namespace FHM.Bounds.RecursiveHMCallerTests

open HMDeclaredGroup RecursiveHMJudgement

private def count (i : Nat) : Count := .var ⟨.rigid, i⟩
private def signature (precise : Bool := false) : PolyTy :=
  ⟨1, .arrow (.bl (.solid (count 7)) (.solid (count 7)) (.bvar 0))
    (.bl (.solid (if precise then .lit 0 else count 7)) (.solid (count 7)) (.bvar 0))⟩
private def metadata : Scope.Metadata :=
  { telescopes := [⟨.letRec [] 0, [(⟨"n"⟩, 7)]⟩] }

private def exercise {output metadata path index vectors premises typeCaptures env}
    (ps : Interfaces output metadata path [] premises typeCaptures index vectors)
    (ms : CheckedMembers env ps) (n : Nat) (prim : PrimTy) (escape wrongHM precise : Bool) : Except String Bool := do
  match ps, ms with
  | .nil, .nil => throw "test: no original declared member to exercise"
  | .cons p _ _, .cons checked _ =>
      let cert := checked.certificate
      let arg := BoundsTy.list (count 7) (count 7) (.prim prim)
      let resultCount := if precise then 0 else n
      let expected := BoundsTy.arrow (.list (.lit n) (.lit n) arg) (.list (.lit resultCount) (.lit resultCount) arg)
      let found := if wrongHM then Ty.prim .int else Synth.BoundsTy.toTy expected
      let used ← RecursiveHMCaller.check p.declaration.node cert checked.captured [] found
        [.lit n] [arg] (if escape then [] else [7])
      pure (used.result.checked.typed.actual.pretty == expected.pretty &&
        used.used.types.map BoundsTy.pretty == [arg.pretty])

private def actual (n : Nat := 3) (prim : PrimTy := .int)
    (escape : Bool := false) (wrongHM : Bool := false) (precise : Bool := false) : Except String Bool := do
  let ctors : CtorEnv := (elabDecls preludeDecls).getD []
  let source := Expr.letRec [some (signature precise)]
    [.lambda none (if precise then .ctor nilCtorName else .app (.var 1) (.var 0))]
    (.primLit (.int 0))
  let a ← match inferFound ctors source with
    | some a => pure a | none => throw "test: annotated self-loop HM inference failed"
  let premises : List Constraint := [⟨.lit 1, count 7⟩]
  let g ← HMDeclaredCoordinates.check a.output metadata [] (premises := premises) (schemes := a.binderSchemes)
  exercise g.checked.interfaces g.checked.members n prim escape wrongHM precise

private def passes (r : Except String Bool) : Bool := match r with | .ok b => b | _ => false
private def fails {α} (r : Except String α) (part : String) : Bool :=
  match r with | .error message => (message.splitOn part).length > 1 | _ => false

private def tests : List (String × Bool) := [
  ("actual signed RHS specializes at Int with discharged count premises in the caller context", passes actual),
  ("the same original RHS also specializes at Char, without in-group polymorphic calls", passes (actual 4 .char)),
  ("source count substitution preserves caller-owned inner count 7 in full HM arguments", passes (actual 7)),
  ("caller evidence retains exact Nil bounds rather than replacing them with the wider written ceiling",
    passes (actual 3 .int false false true)),
  ("a caller that violates the instantiated contract premise rejects", fails (actual 0) "premises"),
  ("full caller HM argument counts must remain in caller scope", fails (actual 3 .int true) "outside caller scope"),
  ("caller evidence cannot target an unrelated found HM monotype", fails (actual 3 .int false true) "disagrees with found monotype")]

def main : IO Unit := do
  for (name, ok) in tests do
    if ok then IO.println s!"PASS: {name}"
    else throw (IO.userError s!"FAIL: {name}")

#eval main

end FHM.Bounds.RecursiveHMCallerTests
