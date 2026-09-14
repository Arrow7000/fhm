import FHM.Bounds.RecursiveWalk
import FHM.Bounds.Found

namespace FHM.Bounds.RecursiveMatchTests

open RecursiveTyping SurfaceBridge.Provenance

private def listHM : Ty := listTy (.prim .int)
private def nil : Expr := .found listHM (.ctor nilCtorName)
private def int (n : Int := 1) : Expr := .found (.prim .int) (.primLit (.int n))
private def var (i : Nat) (hm : Ty := listHM) : Expr := .found hm (.var i)
private def cons (h t : Expr) : Expr :=
  .found listHM (.app
    (.found (.arrow listHM listHM) (.app
      (.found (.arrow (.prim .int) (.arrow listHM listHM)) (.ctor consCtorName)) h)) t)
private def matchList (scrut : Expr) (branches : List (MatchPattern × Expr))
    (hm : Ty := listHM) : Expr := .found hm (.match_ scrut branches)
private def both (empty nonempty : Expr) : List (MatchPattern × Expr) :=
  [(.named nilCtorName 0, empty), (.named consCtorName 2, nonempty)]
private def exact (n : Nat) : BoundsTy := .list (.lit n) (.lit n) (.prim .int)
private def k : Count := .var ⟨.rigid, 7⟩

private def run (env : List Binding) (e : Expr) (expected : Option BoundsTy := none)
    (ids : List Nat := []) : Except String String := do
  let r ← RecursiveWalk.walk ids [] ids [] env [] e [] expected
  unless exactlyOnce (logicalCorePaths e) (r.nodes.map (·.path)) do
    throw "test: match lost or duplicated a logical node"
  pure r.bounds.pretty

private def succeeds (r : Except String α) : Bool := match r with | .ok _ => true | _ => false
private def fails (r : Except String α) (needle : String) : Bool :=
  match r with | .error m => (m.splitOn needle).length > 1 | _ => false
private def returns (r : Except String String) (expected : String) : Bool :=
  match r with | .ok s => s == expected | _ => false

private def functionMatch : Expr := matchList (var 0)
  (both (var 1 (.arrow listHM (.prim .int))) (var 4 (.arrow listHM (.prim .int))))
  (.arrow listHM (.prim .int))
private def functionEnv : List Binding :=
  [.mono (.list (.lit 0) .inf (.prim .int)),
   .mono (.arrow (exact 1) (.prim .int)), .mono (.arrow (exact 2) (.prim .int))]

private def retainedArm : Bool :=
  let e := matchList (var 0) (both nil (cons (var 0 (.prim .int)) (var 1)))
  match RecursiveWalk.walk [7] [] [7] [] [.mono (.list k k (.prim .int))] [] e []
      (some (.list k k (.prim .int))) with
  | .error _ => false
  | .ok r => r.nodes.any fun node => node.path == [.matchBranch 0] &&
      match node.bounds with | some (.list (.lit 0) (.lit 0) _) => true | _ => false

private def identity : Expr := .found (.arrow listHM listHM) (.lambda none (var 0))
private def checkedLambda (e : Expr) (β : BoundsTy) (ids : List Nat := []) : Except String Unit := do
  let r ← RecursiveWalk.walk ids [] ids [] [] [] e [] (some β)
  let _ ← Typed.subtype [] r.bounds β
  pure ()

private def consumer (result : Nat := 3) : Expr :=
  .found (.arrow (.arrow listHM listHM) (.prim .int)) (.lambda
    (some (.arrow (.bl (.solid (.lit 3)) (.solid (.lit 3)) (.prim .int))
      (.bl (.solid (.lit result)) (.solid (.lit result)) (.prim .int)))) (int))

private def cases : List (String × Bool) := [
  ("Nil-only match accepts exact empty input", returns
    (run [.mono (exact 0)] (matchList (var 0) [(.named nilCtorName 0, nil)])) "BL 0 0 Int"),
  ("Cons-only match exposes predecessor tail bounds", returns
    (run [.mono (exact 2)] (matchList (var 0) [(.named consCtorName 2, var 1)])) "BL 1 1 Int"),
  ("Cons-only match rejects maybe-empty input", fails
    (run [.mono (.list (.lit 0) .inf (.prim .int))]
      (matchList (var 0) [(.named consCtorName 2, var 1)])) "Cons-only"),
  ("Nil-only match rejects maybe-nonempty input", fails
    (run [.mono (exact 1)] (matchList (var 0) [(.named nilCtorName 0, nil)])) "Nil-only"),
  ("wildcard preserves a monomorphic input bound", returns
    (run [.mono (exact 3)] (matchList (var 0) [(.wildcard, var 0)])) "BL 3 3 Int"),
  ("empty match is not coverage evidence", fails
    (run [.mono (exact 0)] (matchList (var 0) [])) "covering"),
  ("wildcard does not excuse wrong constructor arity", fails
    (run [.mono (exact 0)] (matchList (var 0)
      [(.wildcard, nil), (.named consCtorName 1, nil)])) "unsupported List pattern"),
  ("wildcard does not excuse unrelated constructor", fails
    (run [.mono (exact 0)] (matchList (var 0)
      [(.wildcard, nil), (.named ⟨"Other"⟩ 0, nil)])) "unsupported List pattern"),
  ("match on Int does not manufacture a List", fails
    (run [] (matchList (int) [(.wildcard, nil)])) "non-List"),
  ("forged match root HM type rejects", fails
    (run [.mono (exact 0)] (matchList (var 0) [(.wildcard, nil)] (.prim .char))) "shape disagrees"),
  ("incompatible synthesized branch HM shapes reject", fails
    (run [.mono (exact 1)] (matchList (var 0) (both nil (var 0 (.prim .int))))) "shape"),
  ("path-guided reconstruction proves symbolic exact length", succeeds
    (run [.mono (.list k k (.prim .int))]
      (matchList (var 0) (both nil (cons (var 0 (.prim .int)) (var 1))))
      (some (.list k k (.prim .int))) [7])),
  ("declared match result cannot excuse a bad empty arm", fails
    (run [.mono (.list k k (.prim .int))]
      (matchList (var 0) (both (cons (int) nil) (var 2)))
      (some (.list k k (.prim .int))) [7]) "interval inclusion"),
  ("declared match result cannot excuse an extra Cons", fails
    (run [.mono (.list k k (.prim .int))]
      (matchList (var 0) (both nil (cons (int) (var 2))))
      (some (.list k k (.prim .int))) [7]) "interval inclusion"),
  ("Cons opens head before tail", returns
    (run [.mono (exact 1)] (matchList (var 0)
      [(.named consCtorName 2, var 0 (.prim .int))] (.prim .int))) "Int"),
  ("function-valued match intersects arrow domains", succeeds (run functionEnv functionMatch)),
  ("merged function cannot be called outside common domain", fails
    (run functionEnv (.found (.prim .int) (.app functionMatch (cons (int) nil)))) "interval inclusion"),
  ("declared function domain must work for every arm", fails
    (run functionEnv functionMatch (some (.arrow (exact 1) (.prim .int)))) "interval inclusion"),
  ("guided match keeps actual empty-arm evidence in reports", retainedArm),
  ("nested matches recurse through tail scope", succeeds
    (run [.mono (exact 2)] (matchList (var 0) (both nil
      (matchList (var 1) (both nil (var 1))))))),
  ("declared domain supplies an unannotated List parameter", succeeds
    (checkedLambda identity (.arrow (exact 3) (exact 3)))),
  ("symbolic declared domain retains its scoped count origin", succeeds
    (checkedLambda identity (.arrow (.list k k (.prim .int)) (.list k k (.prim .int))) [7])),
  ("no contract means no guessed open parameter origin", fails (run [] identity) "parameter"),
  ("declared lambda output remains an inclusion obligation", fails
    (checkedLambda identity (.arrow (exact 3) (exact 2))) "interval inclusion"),
  ("declared parameter with different HM spine is not silently specialized", fails
    (checkedLambda identity (.arrow (.list (.lit 3) (.lit 3) (.prim .char)) (exact 3))) "needs specialization"),
  ("declared parameter cannot escape caller count scope", fails
    (checkedLambda identity (.arrow (.list k k (.prim .int)) (.list k k (.prim .int)))) "outside caller scope"),
  ("carried parameter annotation is not overridden by a contract", fails
    (checkedLambda (.found (.arrow listHM listHM) (.lambda
      (some (.bl (.solid (.lit 2)) (.solid (.lit 2)) (.prim .int))) (var 0)))
      (.arrow (exact 3) (exact 3))) "interval inclusion"),
  ("curried contract guidance reaches the inner List parameter", succeeds
    (checkedLambda (.found (.arrow (.prim .int) (.arrow listHM listHM)) (.lambda none identity))
      (.arrow (.prim .int) (.arrow (exact 3) (exact 3))))),
  ("computed function domain guides an unannotated lambda argument", returns
    (run [] (.found (.prim .int) (.app (consumer) identity))) "Int"),
  ("monomorphic variable domain guides an unannotated lambda argument", returns
    (run [.mono (.arrow (.arrow (exact 3) (exact 3)) (.prim .int))]
      (.found (.prim .int) (.app (var 0 (.arrow (.arrow listHM listHM) (.prim .int))) identity))) "Int"),
  ("argument guidance retains output inclusion checks", fails
    (run [] (.found (.prim .int) (.app (consumer 2) identity))) "interval inclusion"),
  ("argument guidance checks correlated match arms independently", returns
    (run [.mono (.arrow (.list k k (.prim .int)) (.prim .int)), .mono (.list k k (.prim .int))]
      (.found (.prim .int) (.app (var 0 (.arrow listHM (.prim .int)))
        (matchList (var 1) (both nil (cons (var 0 (.prim .int)) (var 1)))))) none [7]) "Int")]

def main : IO Unit := do
  for (name, ok) in cases do
    IO.println s!"{if ok then "PASS" else "FAIL"}: {name}"
    unless ok do throw (IO.userError s!"recursive match regression: {name}")

#eval main

end FHM.Bounds.RecursiveMatchTests
