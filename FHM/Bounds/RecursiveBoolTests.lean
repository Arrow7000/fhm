import FHM.Bounds.RecursiveWalk
import FHM.Bounds.Found

namespace FHM.Bounds.RecursiveBoolTests

open RecursiveTyping BoolBranches SurfaceBridge.Provenance

private def boolHM : Ty := .customTy boolTyName []
private def listHM : Ty := listTy (.prim .int)
private def lit (n : Int := 1) : Expr := .found (.prim .int) (.primLit (.int n))
private def truth (b : Bool := true) : Expr :=
  .found boolHM (.ctor (if b then trueCtorName else falseCtorName))
private def nil : Expr := .found listHM (.ctor nilCtorName)
private def singleton : Expr := .found listHM (.app
  (.found (.arrow listHM listHM) (.app
    (.found (.arrow (.prim .int) (.arrow listHM listHM)) (.ctor consCtorName)) (lit))) nil)
private def both (a b : Expr) : List (MatchPattern × Expr) :=
  [(.named trueCtorName 0, a), (.named falseCtorName 0, b)]
private def choose (branches : List (MatchPattern × Expr)) (hm : Ty := .prim .int)
    (scrut : Expr := truth) : Expr := .found hm (.match_ scrut branches)

private def run (e : Expr) (expected : Option BoundsTy := none) : Except String String := do
  let r ← RecursiveWalk.walk [] [] [] [] [] [] e [] expected
  unless exactlyOnce (logicalCorePaths e) (r.nodes.map (·.path)) do
    throw "test: Bool match lost or duplicated a logical node"
  pure r.bounds.pretty

private def fails (r : Except String α) (needle : String) : Bool :=
  match r with | .error m => (m.splitOn needle).length > 1 | _ => false
private def returns (r : Except String String) (expected : String) : Bool :=
  match r with | .ok s => s == expected | _ => false

private def comparison : Expr := .found boolHM (.app
  (.found (.arrow (.prim .int) boolHM) (.app
    (.found (.arrow (.prim .int) (.arrow (.prim .int) boolHM)) (.primBinOp .intLt)) (lit 1))) (lit 2))

example {branches} (h : BoolBranches.Covers branches) (b : Bool) :
    hasWildcardBranch branches ∨
      ∃ body, (.named (if b then trueCtorName else falseCtorName) 0, body) ∈ branches := h.sound b

private def cases : List (String × Bool) := [
  ("True constructor carries Bool bounds", returns (run (truth)) "Bool"),
  ("False constructor carries Bool bounds", returns (run (truth false)) "Bool"),
  ("both Bool constructors cover the match", returns (run (choose (both (lit 1) (lit 2)))) "Int"),
  ("comparison result supports a Bool match", returns
    (run (choose (both (lit 1) (lit 2)) (.prim .int) comparison)) "Int"),
  ("Bool wildcard covers both constructors", returns (run (choose [(.wildcard, lit)])) "Int"),
  ("Bool match cannot omit False", fails (run (choose [(.named trueCtorName 0, lit)])) "missing False"),
  ("Bool match cannot omit True", fails (run (choose [(.named falseCtorName 0, lit)])) "missing True"),
  ("empty Bool match rejects", fails (run (choose [])) "missing True"),
  ("wildcard does not admit nonzero Bool pattern arity", fails
    (run (choose [(.wildcard, lit), (.named trueCtorName 1, lit)])) "unsupported Bool pattern"),
  ("wildcard does not admit a List pattern in a Bool match", fails
    (run (choose [(.wildcard, lit), (.named nilCtorName 0, lit)])) "unsupported Bool pattern"),
  ("Bool arms synthesize a safe List interval union", returns
    (run (choose (both nil singleton) listHM)) "BL 0 1 Int"),
  ("constant True does not excuse a false-arm bound violation", fails
    (run (choose (both nil singleton) listHM) (some (.list (.lit 0) (.lit 0) (.prim .int)))) "interval inclusion"),
  ("forged Bool constructor HM payload rejects", fails
    (run (.found (.prim .int) (.ctor trueCtorName))) "shape disagrees"),
  ("nested Bool matches preserve occurrence reports", returns
    (run (choose (both (choose (both (lit 1) (lit 2))) (lit 3)))) "Int")]

def main : IO Unit := do
  for (name, ok) in cases do
    IO.println s!"{if ok then "PASS" else "FAIL"}: {name}"
    unless ok do throw (IO.userError s!"recursive Bool regression: {name}")

#eval main

end FHM.Bounds.RecursiveBoolTests
