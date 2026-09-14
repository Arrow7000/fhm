import FHM.Bounds.RecursiveHMWalk
import FHM.Bounds.Found

namespace FHM.Bounds.ScopedHMWalkTests

open RecursiveHMJudgement ScopedHMInterpretation SurfaceBridge.Provenance

private def n : Count := .var ⟨.rigid, 7⟩
private def arg : BoundsTy := .list n n (.prim .int)
private def slots : Nat → BoundsTy := vector [arg]
private def parameter : Ty := .bl (.solid n) (.solid n) (.bvar 0)
private def signature (falseClaim : Bool) : PolyTy :=
  ⟨1, .arrow parameter (.bl (.solid (if falseClaim then .lit 0 else n))
    (.solid (if falseClaim then .lit 0 else n)) (.bvar 0))⟩
private def expected : BoundsTy :=
  .arrow (.list (.lit 3) (.lit 3) arg) (.list (.lit 3) (.lit 3) arg)

private def realArtifact (falseClaim : Bool := false) (recursive : Bool := false)
    (isMutual : Bool := false) (caller : List Nat := [7]) : Except String Bool := do
  let ctors : CtorEnv := (elabDecls preludeDecls).getD []
  let σ := signature falseClaim
  let rhs := Expr.lambda (if recursive then none else some parameter)
    (if recursive then .match_ (.var 0)
      [(.named consCtorName 2, .app (.var (if isMutual then 4 else 3)) (.var 2)),
        (.named nilCtorName 0, .var 0)] else .var 0)
  let source := if recursive then
      Expr.letRec (if isMutual then [some σ, some σ] else [some σ])
        (if isMutual then [rhs, .lambda none (.match_ (.var 0)
          [(.named consCtorName 2, .app (.var 3) (.var 2)), (.named nilCtorName 0, .var 0)])] else [rhs])
        (.primLit (.int 0))
    else Expr.letIn (some σ) rhs (.primLit (.int 0))
  let artifact ← match inferFound ctors source with
    | some artifact => pure artifact | none => throw "test: actual annotated HM inference failed"
  let path : CorePath := if recursive then [.letRecRhs 0] else [.letRhs]
  let node ← HMFoundView.locate artifact.output path
  -- Recursive inference preserves its solved monomorphic free identities,
  -- rather than the lexical bvars of an annotated non-recursive let RHS.
  -- Match the actual declaration directly; do not fabricate an inferred fact.
  let free ← if recursive then do
      let matched ← BinderBridge.instantiate σ node.original
      match matched.args with
      | [.fvar i] => pure (fun j => if j = i then arg else BoundsTy.fvar j)
      | _ => throw "test: recursive declaration did not open at one monomorphic identity"
    else pure BoundsTy.fvar
  unless (if recursive then BinderBridge.candidates artifact.binderSchemes (.letRec [] 0)
    else BinderBridge.candidates artifact.binderSchemes (.letIn [])).isEmpty do
    throw "test: fabricated inferred binder fact"
  let rows : CountSubstitution.Bindings := [(7, .lit 3)]
  let demand ← ScopedHMAnnotation.decode free slots [7] rows caller σ.body
  let env ← if recursive then do
      let s ← HMCountScheme.decode σ [7] []
      let fixed ← RecursiveHMContract.fix s (ty free slots node.original) [arg]
      let c : Contract := ⟨s, _, fixed⟩
      pure (if isMutual then [.recursive c, .recursive c] else [.recursive c])
    else pure []
  let r ← RecursiveHMWalk.checkLocated node free slots [7] rows caller [] env
    artifact.binderSchemes (some demand.bounds)
  let _ ← Typed.subtype [] r.typed.actual demand.bounds
  pure (r.typed.actual.pretty == expected.pretty && exactlyOnce (logicalCorePaths (.found node.original node.inner))
    (r.nodes.map fun node => node.path.drop 1))

private def bothInterfaces (badPayload : Bool := false) : Except String Bool := do
  let free (i : Nat) : BoundsTy := if i = 90 then .prim .char else .fvar i
  let slot : Nat → BoundsTy := vector [.fvar 90]
  let root := Ty.arrow (.bvar 0) (.arrow (.fvar 90) (.bvar 0))
  let e := Expr.found root (.lambda (some (.bvar 0))
    (.found (.arrow (.fvar 90) (.bvar 0)) (.lambda (some (.fvar 90))
      (.found (if badPayload then .prim .char else .bvar 0) (.var 1)))))
  let r ← RecursiveHMWalk.walkScoped free slot [] [] [] [] [] [] e []
  pure (r.bounds.pretty == (BoundsTy.arrow (.fvar 90) (.arrow (.prim .char) (.fvar 90))).pretty &&
    exactlyOnce (logicalCorePaths e) (r.nodes.map (·.path)))

private def realMatch : Except String Bool := do
  let ctors : CtorEnv := (elabDecls preludeDecls).getD []
  let σ : PolyTy := ⟨1, .arrow parameter
    (.bl (.solid (.lit 0)) (.solid n) (.bvar 0))⟩
  let rhs := Expr.lambda (some parameter) (.match_ (.var 0)
    [(.named consCtorName 2, .var 1), (.named nilCtorName 0, .ctor nilCtorName)])
  let artifact ← match inferFound ctors (.letIn (some σ) rhs (.primLit (.int 0))) with
    | some artifact => pure artifact | none => throw "test: annotated List-match inference failed"
  let node ← HMFoundView.locate artifact.output [.letRhs]
  let demand ← ScopedHMAnnotation.decode BoundsTy.fvar slots [7] [(7, .lit 3)] [7] σ.body
  let r ← RecursiveHMWalk.checkLocated node BoundsTy.fvar slots [7] [(7, .lit 3)] [7] [] []
    artifact.binderSchemes (some demand.bounds)
  let _ ← Typed.subtype [] r.typed.actual demand.bounds
  pure (r.typed.actual.pretty == demand.bounds.pretty && exactlyOnce
    (logicalCorePaths (.found node.original node.inner)) (r.nodes.map fun node => node.path.drop 1))

private def trueResult (r : Except String Bool) : Bool := match r with | .ok ok => ok | _ => false
private def fails (r : Except String Bool) (message : String) : Bool := match r with
  | .error error => (error.splitOn message).length > 1
  | _ => false

private def cases : List (String × Bool) := [
  ("real annotated forall RHS checks original nodes without a machine fact", trueResult realArtifact),
  ("real annotated List-match retains lexical element origins and every original branch node", trueResult realMatch),
  ("real annotated self recursion uses a full fixed HM vector", trueResult (realArtifact false true)),
  ("real annotated mutual recursion shares fixed full HM arguments", trueResult (realArtifact false true true)),
  ("false result bounds fail independent inclusion", fails (realArtifact true) "interval inclusion"),
  ("inserted full lexical types cannot escape caller count scope", fails
    (realArtifact false false false []) "outside caller scope"),
  ("both interfaces stay separate without recursively reading inserted types", trueResult bothInterfaces),
  ("forged original body payload fails lexical reconciliation", fails (bothInterfaces true) "found payload")]

def main : IO Unit := do
  for (name, ok) in cases do
    IO.println s!"{if ok then "PASS" else "FAIL"}: {name}"
    unless ok do throw (IO.userError s!"scoped HM walker regression failed: {name}")

#eval main

end FHM.Bounds.ScopedHMWalkTests
