import FHM.Bounds.HMDeclaredCoordinates
import FHM.Bounds.Found

namespace FHM.Bounds.HMDeclaredCoordinatesTests

open RecursiveHMJudgement

private def count (i : Nat) : Count := .var ⟨.rigid, i⟩
private def signature (i mode : Nat) (swapped : Bool := false) : PolyTy :=
  let first := if swapped && mode == 1 then 1 else 0
  let second := if mode == 1 then (if swapped then 0 else 1) else 0
  ⟨if mode == 0 then 1 else 2,
    .arrow (.bl (.solid (count i)) (.solid (count i)) (.bvar first))
      (.bl (.solid (count i)) (.solid (count i)) (.bvar second))⟩

private def metadata : Scope.Metadata :=
  { telescopes := [⟨.letRec [] 0, [(⟨"n"⟩, 7)]⟩, ⟨.letRec [] 1, [(⟨"m"⟩, 8)]⟩] }

private def artifact (mode : Nat := 0) (badBounds : Bool := false) : Except String FoundResult := do
  let ctors : CtorEnv := (elabDecls preludeDecls).getD []
  let lastAnnotation : PolyTy := if badBounds then
    ⟨0, .bl (.solid (.lit 2)) (.solid (.lit 2)) (.prim .int)⟩ else ⟨0, .prim .int⟩
  let source := Expr.letRec [some (signature 7 mode), some (signature 8 mode true), some lastAnnotation]
    [.lambda none (.app (.var 2) (.var 0)), .lambda none (.app (.var 1) (.var 0)),
      if badBounds then .ctor nilCtorName else .primLit (.int 0)] (.primLit (.int 0))
  match inferFound ctors source with
  | some a => pure a
  | none => throw "test: coordinate regression HM inference failed"

private def automatic (mode : Nat := 0) (freshCaptures : Bool := false) : Except String Bool := do
  let a ← artifact mode
  let outerTypes := if freshCaptures then [Ty.fvar 1000, Ty.fvar 2000] else []
  let outerEnv : List Binding := if freshCaptures then [.mono (.fvar 2000)] else []
  let g ← HMDeclaredCoordinates.check a.output metadata [] (outerTypes := outerTypes)
    (outerEnv := outerEnv) (schemes := a.binderSchemes)
  let again ← HMDeclaredCoordinates.propose a.output metadata [] (outerTypes := outerTypes)
    (outerEnv := outerEnv) (schemes := a.binderSchemes)
  match g.vectors with
  | [first, second, []] =>
      let slots := if mode == 1 then first == second.reverse else
        if mode == 2 then first[0]? == second[0]? && first[1]? != second[1]? else first == second
      pure (slots && g.vectors == again && g.checked.interfaces.contracts.length == 3 &&
        (!freshCaptures || g.vectors.flatten.all (fun i => i > 2000)))
  | _ => throw "test: automatic coordinate proposal changed member/slot arity"

private def bad : Except String Bool := do
  let a ← artifact 0 true
  let _ ← HMDeclaredCoordinates.check a.output metadata [] (schemes := a.binderSchemes)
  pure true

private def malformed : Except String Bool := do
  let output := Expr.found (.prim .int) (.letRec [some ⟨0, .prim .int⟩] []
    (.found (.prim .int) (.primLit (.int 0))))
  let _ ← HMDeclaredCoordinates.check output {} []
  pure true

private def passes (r : Except String Bool) : Bool := match r with | .ok b => b | _ => false
private def fails {α} (r : Except String α) (part : String) : Bool :=
  match r with | .error message => (message.splitOn part).length > 1 | _ => false

private def tests : List (String × Bool) := [
  ("automatic coordinates certify all three actual members without caller-supplied HM vectors", passes automatic),
  ("shared solved shapes align source forall slots in different orders", passes (automatic 1)),
  ("unused forall slots keep their arity and independent opaque coordinates", passes (automatic 2)),
  ("fresh coordinates avoid full source artifacts and outer captured HM identities", passes (automatic 0 true)),
  ("automatic coordinate proposals cannot accept a false final RHS bounds claim", fails bad "inclusion"),
  ("automatic proposals reject malformed original group arities", fails malformed "annotation/RHS arity")]

def main : IO Unit := do
  for (name, ok) in tests do
    if ok then IO.println s!"PASS: {name}"
    else throw (IO.userError s!"FAIL: {name}")

#eval main

end FHM.Bounds.HMDeclaredCoordinatesTests
