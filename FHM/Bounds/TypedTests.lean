import FHM.Bounds.Found

/-! Executable regressions for the deliberately restricted typed slice. -/

namespace FHM.Bounds.TypedTests

open Typed

private def intTy : Ty := .prim .int
private def intsTy : Ty := listTy intTy

private def ints : List Int → Expr
  | [] => .found intsTy (.ctor nilCtorName)
  | n :: ns =>
      .found intsTy (.app
        (.found (.arrow intsTy intsTy) (.app
          (.found (.arrow intTy (.arrow intsTy intsTy)) (.ctor consCtorName))
          (.found intTy (.primLit (.int n))))) (ints ns))

private def nested (length : Nat) : Expr :=
  .found (.arrow intTy intsTy) (.lambda none
    (.found intsTy (.letIn
      (some ⟨0, .bl (.solid (.lit length)) (.solid (.lit length)) intTy⟩)
      (ints [1, 2]) (.found intsTy (.var 0)))))

private def rejects (e : Expr) (message : String) : Bool :=
  match walk [] [] [] e with
  | .error msg => msg == message
  | .ok _ => false

private def cases : List (String × Bool) := [
  ("nominal subtype recurses through every argument", match subtype []
      (.custom pairTyName [.list (.lit 2) (.lit 2) (.prim .int), .prim .char])
      (.custom pairTyName [.list (.lit 0) .inf (.prim .int), .prim .char]) with
    | .ok _ => true
    | .error _ => false),
  ("nominal subtype rejects arity mismatch", match subtype []
      (.custom pairTyName [.prim .int])
      (.custom pairTyName [.prim .int, .prim .char]) with
    | .error msg => msg == "bounds: data type arity mismatch"
    | .ok _ => false),
  ("nominal shape retains nested List structure", match shapeTop
      (.customTy pairTyName [listTy intTy, .prim .char]) with
    | .ok (.custom name [.list (.lit 0) .inf (.prim .int), .prim .char]) =>
        name == pairTyName
    | _ => false),
  ("nominal annotation retains exact nested bounds", match annotation
      (.customTy pairTyName [
        .bl (.solid (.lit 2)) (.solid (.lit 2)) intTy, .prim .char]) with
    | .ok (.custom name [.list (.lit 2) (.lit 2) (.prim .int), .prim .char]) =>
        name == pairTyName
    | _ => false),
  ("malformed List annotation arity rejected", match annotation
      (.customTy listTyName [intTy, .prim .char]) with
    | .error msg => msg == "bounds: malformed List annotation arity"
    | .ok _ => false),
  ("exact two-element list", match walk [] [] [] (ints [1, 2]) with
    | .ok r => r.bounds.pretty == "BL 2 2 Int" && r.nodes.length == 9
    | _ => false),
  ("nested annotation and unannotated scalar lambda", match walk [] [] [] (nested 2) with
    | .ok r => r.bounds.pretty == "Int → BL 2 2 Int" && r.nodes.length == 12 &&
        r.nodes.any (fun n => n.path == [.lambdaBody, .letRhs, .appArg])
    | _ => false),
  ("nested incorrect annotation rejected", rejects (nested 1)
    "bounds: interval inclusion not established (invalid or unknown)"),
  ("unannotated type-variable identity", match walk [] [] []
      (.found (.arrow (.fvar 5) (.fvar 5)) (.lambda none (.found (.fvar 5) (.var 0)))) with
    | .ok r => r.nodes.length == 2
    | _ => false),
  ("annotated List parameter contract", match walk [] [] []
      (.found (.arrow intsTy intsTy)
        (.lambda (some (.bl (.solid (.lit 2)) (.solid (.lit 2)) intTy))
          (.found intsTy (.var 0)))) with
    | .ok r => r.bounds.pretty == "BL 2 2 Int → BL 2 2 Int"
    | _ => false),
  ("fresh List parameter bounds explicitly deferred", rejects
    (.found (.arrow intsTy intsTy) (.lambda none (.found intsTy (.var 0))))
    "bounds: unannotated non-scalar parameter unsupported in typed slice"),
  ("general scalar application", match walk [] [] []
    (.found intTy (.app
      (.found (.arrow intTy intTy) (.lambda none (.found intTy (.var 0))))
      (.found intTy (.primLit (.int 1))))) with
    | .ok r => r.bounds.pretty == "Int" && r.nodes.length == 4
    | _ => false),
  ("curried primitive application", match walk [] [] []
    (.found intTy (.app
      (.found (.arrow intTy intTy) (.app
        (.found (.arrow intTy (.arrow intTy intTy)) (.primBinOp .intAdd))
        (.found intTy (.primLit (.int 1))))) (.found intTy (.primLit (.int 2))))) with
    | .ok r => r.bounds.pretty == "Int" && r.nodes.length == 5
    | _ => false),
  ("List application preserves checked contract", match walk [] [] []
    (.found intsTy (.app
      (.found (.arrow intsTy intsTy)
        (.lambda (some (.bl (.solid (.lit 2)) (.solid (.lit 2)) intTy))
          (.found intsTy (.var 0)))) (ints [1, 2]))) with
    | .ok r => r.bounds.pretty == "BL 2 2 Int"
    | _ => false),
  ("List application rejects incorrect length", rejects
    (.found intsTy (.app
      (.found (.arrow intsTy intsTy)
        (.lambda (some (.bl (.solid (.lit 2)) (.solid (.lit 2)) intTy))
          (.found intsTy (.var 0)))) (ints [1])))
    "bounds: interval inclusion not established (invalid or unknown)"),
  ("incorrect child payload rejected", rejects
    (.found (.arrow intTy (.prim .char)) (.lambda none
      (.found (.prim .char) (.primLit (.int 1)))))
    "bounds: synthesized shape disagrees with found payload"),
  ("missing wrapper rejected", rejects (.primLit (.int 1))
    "bounds: every logical node must have one found wrapper"),
  ("recursion explicitly unsupported", rejects (.found intTy (.letRec [] []
    (.found intTy (.primLit (.int 1))))) "bounds: expression form unsupported in typed slice"),
  ("polymorphic annotation explicitly unsupported", rejects
    (.found intTy (.letIn (some ⟨1, .bvar 0⟩)
      (.found intTy (.primLit (.int 1))) (.found intTy (.var 0))))
    "bounds: polymorphic annotation unsupported in typed slice"),
  ("count holes explicitly unsupported", rejects
    (.found intsTy (.letIn (some ⟨0, .bl .hole .hole intTy⟩)
      (ints [1, 2]) (.found intsTy (.var 0))))
    "bounds: count holes unsupported in typed slice"),
  ("unscoped symbolic annotation explicitly rejected", rejects
    (.found (.arrow intsTy intsTy)
      (.lambda (some (.bl (.solid (.var ⟨.rigid, 0⟩)) (.solid (.var ⟨.rigid, 0⟩)) intTy))
        (.found intsTy (.var 0))))
    "bounds: symbolic annotation needs preserved count scope")]

private def provenanceSlice : Bool :=
  let ctors := (elabDecls preludeDecls).getD []
  let surface : Surface.Expr := .list [.primLit (.int 1), .primLit (.int 2)]
  let spans : Surface.Span.SpannedExpr :=
    .list ⟨1, 1, 1, 7⟩ [.leaf ⟨1, 2, 1, 3⟩, .leaf ⟨1, 5, 1, 6⟩]
  match SurfaceBridge.Provenance.lowerWithProvenance ctors surface spans with
  | none => false
  | some lowering =>
      match SurfaceBridge.Provenance.inferWithProvenance ctors lowering with
      | none => false
      | some typed =>
          match Found.synthNodes typed with
          | .error _ => false
          | .ok (r, reports) =>
              r.bounds.pretty == "BL 2 2 Int" && reports.length == 9 &&
              reports.any (fun r => r.node.path == [.appFun, .appArg] && r.origin.source.id == 1)

def main : IO Unit := do
  for (name, ok) in cases ++ [("inference/provenance/per-node join", provenanceSlice)] do
    IO.println s!"{if ok then "PASS" else "FAIL"}: {name}"
    unless ok do throw (IO.userError s!"typed bounds regression: {name}")

#eval main

end FHM.Bounds.TypedTests
