import FHM.Bounds.RecursiveWalk
import FHM.Bounds.Found

namespace FHM.Bounds.RecursiveSpineTests

open RecursiveTyping RecursiveSpine SurfaceBridge.Provenance

private def k : Count := .var ⟨.rigid, 7⟩
private def m : Count := .var ⟨.rigid, 8⟩
private def exact (n : Count) : BoundsTy := .list n n (.prim .int)
private def listHM : Ty := listTy (.prim .int)
private def fnHM : Ty := .arrow (.prim .int) (.prim .int)
private def mapHM : Ty := .arrow fnHM (.arrow listHM listHM)
private def fnBounds : BoundsTy := .arrow (.prim .int) (.prim .int)
private def mapBounds : BoundsTy := .arrow fnBounds (.arrow (exact k) (exact k))
private def listAnn : Ty := .bl (.solid k) (.solid k) (.prim .int)
private def mapAnn : PolyTy := ⟨0, .arrow fnHM (.arrow listAnn listAnn)⟩

private def fn : Expr := .found fnHM (.lambda none (.found (.prim .int) (.var 0)))
private def nil : Expr := .found listHM (.ctor nilCtorName)
private def one : Expr := .found listHM (.app
  (.found (.arrow listHM listHM) (.app
    (.found (.arrow (.prim .int) (.arrow listHM listHM)) (.ctor consCtorName))
    (.found (.prim .int) (.primLit (.int 1))))) nil)
private def call (arg : Expr := nil) (head : Ty := mapHM) (middle : Ty := .arrow listHM listHM) : Expr :=
  .found listHM (.app (.found middle (.app (.found head (.var 0)) fn)) arg)

private def run (e : Expr := call) (caller : List Nat := []) (envTail : List Binding := [])
    (premises : List Constraint := []) : Except String BoundsTy := do
  let c ← RecursiveContract.decode mapAnn mapHM [7] [] premises
  let r ← RecursiveWalk.walk caller [] caller [] (.recursive c :: envTail) [] e []
  unless exactlyOnce (logicalCorePaths e) (r.nodes.map (·.path)) do
    throw "test: full spine lost or duplicated a logical node"
  pure r.bounds

private def fails (r : Except String α) (needle : String) : Bool :=
  match r with | .error m => (m.splitOn needle).length > 1 | _ => false
private def proposes (ids : List Nat) (contract : BoundsTy) (actuals : List BoundsTy)
    (expected : List Count) : Bool :=
  match CountProposal.proposeArguments ids contract actuals with
  | .ok args => args == expected
  | .error _ => false
private def returns (r : Except String BoundsTy) (expected : BoundsTy) : Bool :=
  match r, expected with
  | .ok (.list lo hi (.prim .int)), .list lo' hi' (.prim .int) => lo == lo' && hi == hi'
  | _, _ => false

private def cases : List (String × Bool) := [
  ("full map proposal finds the second input length", proposes [7] mapBounds
    [fnBounds, exact (.lit 3)] [.lit 3]),
  ("partial map does not manufacture zero for an unsupplied input", fails
    (CountProposal.proposeArguments [7] mapBounds [fnBounds]) "later argument origin"),
  ("an earlier direct witness allows a partial call", proposes [7]
    (.arrow (exact k) (.arrow (exact k) (exact k))) [exact (.lit 2)] [.lit 2]),
  ("proposal order follows the telescope, not the argument order", proposes [8, 7]
    (.arrow (exact k) (.arrow (exact m) (exact k)))
    [exact (.lit 2), exact (.lit 3)] [.lit 3, .lit 2]),
  ("repeated coordinates retain the first untrusted proposal", proposes [7]
    (.arrow (exact k) (.arrow (exact k) (exact k)))
    [exact (.lit 2), exact (.lit 3)] [.lit 2]),
  ("later direct witness can supply an earlier compound occurrence", proposes [7]
    (.arrow (exact (.add k (.lit 1))) (.arrow (exact k) (exact k)))
    [exact (.lit 2), exact (.lit 1)] [.lit 1]),
  ("compound-only occurrence still needs unsupported inversion", fails
    (CountProposal.proposeArguments [7] (.arrow (exact (.add k (.lit 1))) (exact k))
      [exact (.lit 2)]) "arithmetic inversion"),
  ("result-only coordinate remains an explicit finite witness", proposes [7]
    (.arrow (.prim .int) (exact k)) [.prim .int] [.lit 0]),
  ("captured coordinates are never included in the proposal telescope", proposes [7]
    (.arrow (exact m) (.arrow (exact k) (exact m)))
    [exact (.lit 5), exact (.lit 2)] [.lit 2]),
  ("excess arguments do not invent an arrow domain", fails
    (CountProposal.proposeArguments [] (.prim .int) [.prim .int]) "excess arguments"),
  ("later incompatible proposal shape rejects", fails
    (CountProposal.proposeArguments [7] mapBounds [fnBounds, .prim .int]) "proposal shape"),
  ("checked full map application returns exact Nil", returns (run) (exact (.lit 0))),
  ("checked full map application returns exact singleton", returns (run (call one))
    (exact (.add (.lit 0) (.lit 1)))),
  ("every intermediate found payload is checked", fails
    (run (call nil mapHM fnHM)) "intermediate found payload"),
  ("spine head keeps the recursive group's fixed HM monotype", fails
    (run (call nil (.arrow fnHM (.arrow (listTy (.prim .char)) (listTy (.prim .char)))))) "fixed HM monotype"),
  ("supplied count must discharge declared premises", fails
    (run (call one) [] [] [⟨k, .lit 0⟩]) "premises"),
  ("infinite direct witness is not a Nat instantiation", fails
    (run (call (.found listHM (.var 1))) [] [.mono (exact .inf)]) "finite"),
  ("caller count identity is retained through full application", returns
    (run (call (.found listHM (.var 1))) [42] [.mono (exact (.var ⟨.rigid, 42⟩))])
    (exact (.var ⟨.rigid, 42⟩))),
  ("caller count outside scope cannot become a proposal witness", fails
    (run (call (.found listHM (.var 1))) [] [.mono (exact (.var ⟨.rigid, 42⟩))]) "caller scope"),
  ("standalone polymorphic variable still requires an origin", fails
    (run (.found mapHM (.var 0))) "needs an argument origin")]

example {ids rows caller Δ env e} {spine : RecursiveSpine.Syntax e}
    (result : RecursiveSpine.Result ids rows caller Δ env spine) :
    Derives ids rows Δ env e.stripFound result.bounds := result.typing

def main : IO Unit := do
  let mut failures := 0
  for (name, ok) in cases do
    IO.println s!"{if ok then "PASS" else "FAIL"}: {name}"
    unless ok do failures := failures + 1
  unless failures = 0 do throw (IO.userError s!"{failures} recursive spine regressions failed")

#eval main

end FHM.Bounds.RecursiveSpineTests
