import FHM.Bounds.SchemeFound

namespace FHM.Bounds.SchemeWalkTests

private def ctors : CtorEnv := (elabDecls preludeDecls).getD []
private def identity : Expr := .lambda none (.var 0)
private def int : Expr := .primLit (.int 1)
private def char : Expr := .primLit (.char 'a')
private def singleton : Expr := .app (.app (.ctor consCtorName) char) (.ctor nilCtorName)

-- In each body, the intervening let shifts the previously generalized callee.
private def twice (i : Nat) : Expr :=
  .letIn none (.app (.var i) int) (.app (.var (i + 1)) char)
private def simple : Expr := .letIn none identity (twice 0)
private def mixed : Expr := .letIn none identity
  (.letIn none (.lambda none (.app (.var 1) (.var 0))) (twice 0))
private def nested : Expr := .letIn none identity
  (.letIn none
    (.letIn none (.lambda none (.app (.var 1) (.var 0)))
      (.lambda none (.app (.var 1) (.var 0)))) (twice 0))

private def check (e : Expr) : Except String String := do
  let typed ← match inferFound ctors e with
    | some r => pure r
    | none => throw "HM inference failed"
  let result ← SchemeWalk.walk [] [] [] typed.output typed.binderSchemes
  unless SurfaceBridge.Provenance.exactlyOnce
      (SurfaceBridge.Provenance.logicalCorePaths typed.output) (result.nodes.map (·.path)) do
    throw "node coverage failed"
  pure result.bounds.pretty

private def accepts (e : Expr) (expected : String) : Bool :=
  match check e with | .ok actual => actual == expected | .error _ => false

private def exactNil : Bool :=
  match inferFound ctors (.letIn none identity (.app (.var 0) (.ctor nilCtorName))) with
  | none => false
  | some typed => match SchemeWalk.walk [] [] [] typed.output typed.binderSchemes with
    | .ok r => match r.bounds with | .list (.lit 0) (.lit 0) _ => true | _ => false
    | .error _ => false

private def rejects (e : Expr) (needle : String) : Bool :=
  match check e with
  | .error message => (message.splitOn needle).length > 1
  | .ok _ => false

private def damagedFacts (duplicate : Bool) : Bool :=
  match inferFound ctors simple with
  | none => false
  | some typed =>
      let facts := if duplicate then typed.binderSchemes ++ typed.binderSchemes else []
      match SchemeWalk.walk [] [] [] typed.output facts with
      | .error message => (message.splitOn (if duplicate then "duplicate" else "missing")).length > 1
      | .ok _ => false

private def damagedPayload : Bool :=
  match inferFound ctors (.letIn none identity (.app (.var 0) int)) with
  | none => false
  | some typed => match typed.output with
    | .found hm (.letIn ann rhs (.found result (.app (.found _ fn) arg))) =>
        let damaged := .found hm (.letIn ann rhs
          (.found result (.app (.found (.arrow (.prim .char) (.prim .char)) fn) arg)))
        match SchemeWalk.walk [] [] [] damaged typed.binderSchemes with
        | .error message => (message.splitOn "disagree").length > 1
        | .ok _ => false
    | _ => false

private def span : Surface.Span.Span := ⟨1, 1, 1, 80⟩
private def leaf : Surface.Span.SpannedExpr := .leaf span
private def joined : Bool :=
  let e : Surface.Expr := .letIn ⟨"id"⟩ [] [] none
    (.lambda (.name ⟨"x"⟩) none (.var ⟨"x"⟩))
    (.app (.var ⟨"id"⟩) (.list [.primLit (.char 'a')]))
  let sp : Surface.Span.SpannedExpr := .letIn span (.lambda span leaf)
    (.app span leaf (.list span [leaf]))
  match SurfaceBridge.Provenance.lowerWithProvenance ctors e sp with
  | none => false
  | some lowered => match SurfaceBridge.Provenance.inferWithProvenance ctors lowered with
    | none => false
    | some typed => match SchemeFound.synthNodes typed with
      | .error _ => false
      | .ok (r, reports) => r.bounds.pretty == "BL 1 1 Char" &&
          reports.length == r.nodes.length && reports.length == 10 &&
          reports.any (fun r => r.node.path == [.letBody, .appFun] && r.node.bounds.isSome)

private def cases : List (String × Bool) := [
  ("actual HM identity used at Int and Char", accepts simple "Char"),
  ("generalized RHS uses captured polymorphic binding", accepts mixed "Char"),
  ("nested generalized let inside generalized RHS", accepts nested "Char"),
  ("actual HM polymorphic call preserves Cons length", accepts
    (.letIn none identity (.app (.var 0) singleton)) "BL 1 1 Char"),
  ("actual HM polymorphic call preserves Nil length", exactNil),
  ("monomorphic shadowing is not a scheme call", accepts
    (.letIn none identity (.letIn none (.primBinOp .intAdd)
      (.app (.app (.var 0) int) int))) "Int"),
  ("missing machine binder facts rejected", damagedFacts false),
  ("duplicate machine binder facts rejected", damagedFacts true),
  ("incorrect polymorphic callee found payload rejected", damagedPayload),
  ("two-slot curried function with checked unused Unit slot", accepts
    (.letIn none (.lambda none (.lambda none (.var 1)))
      (.app (.app (.var 0) char) (.primLit .unit))) "Char"),
  ("two-slot curried function does not invent unused Int bounds", rejects
    (.letIn none (.lambda none (.lambda none (.var 1)))
      (.app (.app (.var 0) char) int)) "disagree"),
  ("ground List binding annotation checked", accepts
    (.letIn none identity (.letIn
      (some ⟨0, .bl (.solid (.lit 1)) (.solid (.lit 1)) (.prim .char)⟩)
      (.app (.var 0) singleton) (.var 0))) "BL 1 1 Char"),
  ("incorrect ground List binding annotation rejected", rejects
    (.letIn none identity (.letIn
      (some ⟨0, .bl (.solid (.lit 2)) (.solid (.lit 2)) (.prim .char)⟩)
      (.app (.var 0) singleton) (.var 0))) "interval inclusion"),
  ("standalone polymorphic use explicitly deferred", rejects
    (.letIn none identity (.var 0)) "standalone polymorphic"),
  ("recursive expression explicitly deferred", rejects (.letRec [] [] int) "unsupported"),
  ("annotated polymorphic let explicitly deferred", rejects
    (.letIn (some ⟨1, .arrow (.bvar 0) (.bvar 0)⟩) identity
      (.app (.var 0) int)) "polymorphic annotation"),
  ("inference and provenance adapter covers polymorphic List call", joined)]

def main : IO Unit := do
  for (name, ok) in cases do
    IO.println s!"{if ok then "PASS" else "FAIL"}: {name}"
    unless ok do throw (IO.userError s!"scheme-aware traversal regression: {name}")

#eval main

end FHM.Bounds.SchemeWalkTests
