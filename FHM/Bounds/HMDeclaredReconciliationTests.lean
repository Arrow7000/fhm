import FHM.Bounds.HMDeclaredReconciliation
import FHM.Bounds.Found

namespace FHM.Bounds.HMDeclaredReconciliationTests

open HMDeclaredReconciliation

private def n : Count := .var ⟨.rigid, 7⟩
private def list (a : Ty := .bvar 0) : Ty := .bl (.solid n) (.solid n) a
private def signature : PolyTy := ⟨1, .arrow list list⟩

private def actual (recursive : Bool := false) (ids : List Nat := [91])
    (captures : List Ty := []) : Except String Bool := do
  let ctors : CtorEnv := (elabDecls preludeDecls).getD []
  let rhs := Expr.lambda (if recursive then none else some list)
    (if recursive then .app (.var 1) (.var 0) else .var 0)
  let source := if recursive then Expr.letRec [some signature] [rhs] (.primLit (.int 0))
    else Expr.letIn (some signature) rhs (.primLit (.int 0))
  let artifact ← match inferFound ctors source with
    | some artifact => pure artifact | none => throw "test: declared artifact inference failed"
  let site := if recursive then CoreBinderSite.letRec [] 0 else .letIn []
  let d ← locate artifact.output site
  let c ← check d [7] [] ids captures
  unless (BinderBridge.candidates artifact.binderSchemes site).isEmpty do
    throw "test: annotated declaration acquired a fabricated inferred fact"
  if recursive then
    -- The original alpha -> beta loop is more general than List a -> List a.
    -- Matching in the opposite direction must fail; reconciliation must not.
    match BinderBridge.instantiate signature d.node.original with
    | .ok _ => throw "test: expected genuinely more-general solved loop"
    | .error _ => pure (c.flexible.length == 2 && c.arguments.length == 2)
  else pure (c.flexible.isEmpty && c.signatureIds == ids)

private def synthetic (rhs : Expr) (annotation : PolyTy) (ids : List Nat := [91])
    (captures : List Ty := []) : Except String Unit := do
  let output := Expr.found (.prim .int) (.letIn (some annotation) rhs
    (.found (.prim .int) (.primLit (.int 0))))
  let d ← locate output (.letIn [])
  let _ ← check d [7] [] ids captures
  pure ()

private def identity : Expr := .found (.arrow (.fvar 90) (.fvar 90))
  (.lambda none (.found (.fvar 90) (.var 0)))

private def rigid : Expr := .found (.arrow (.fvar 90) (.fvar 90))
  (.lambda (some (.fvar 90)) (.found (.fvar 90) (.var 0)))

private def sourceSelection (site : CoreBinderSite := .letIn []) : Except String Unit := do
  let output := Expr.found (.prim .int) (.letIn none identity
    (.found (.prim .int) (.primLit (.int 0))))
  let _ ← locate output site
  pure ()

private def malformed : Except String Unit := do
  let output := Expr.found (.prim .int) (.letRec [some signature] []
    (.found (.prim .int) (.primLit (.int 0))))
  let _ ← locate output (.letRec [] 0)
  pure ()

private def passes (r : Except String Bool) : Bool := match r with | .ok ok => ok | _ => false
private def succeeds (r : Except String α) : Bool := match r with | .ok _ => true | _ => false
private def fails (r : Except String α) (message : String) : Bool := match r with
  | .error error => (error.splitOn message).length > 1
  | _ => false

private def cases : List (String × Bool) := [
  ("real annotated forall identity reconciles its original lexical slots", passes actual),
  ("real solved alpha-to-beta recursive RHS specializes toward its narrower written ceiling", passes (actual true)),
  ("unused forall retains an explicit fresh opaque coordinate", succeeds
    (synthetic (.found (.prim .int) (.primLit (.int 1))) ⟨1, .prim .int⟩)),
  ("primitive Int cannot justify forall a. a from source metadata", !succeeds
    (synthetic (.found (.prim .int) (.primLit (.int 1))) ⟨1, .bvar 0⟩)),
  ("surrounding captured free IDs cannot be specialized toward the signature", !succeeds
    (synthetic identity signature [91] [.fvar 90])),
  ("rigid IDs carried in original source annotations cannot be specialized", !succeeds
    (synthetic rigid signature)),
  ("a repeated solved identity cannot fit distinct source forall coordinates", !succeeds
    (synthetic identity ⟨2, .arrow (list (.bvar 0)) (list (.bvar 1))⟩ [91, 92])),
  ("source signature IDs remain fresh from original solved identities", !succeeds
    (synthetic identity signature [90])),
  ("source signature IDs cannot escape through a captured type interface", !succeeds
    (synthetic identity signature [91] [.fvar 91])),
  ("source signature coordinates must remain distinct", !passes (actual false [91, 91])),
  ("source signature retains exact forall arity", !passes (actual false [])),
  ("unannotated source sites cannot receive a caller-invented declaration", fails sourceSelection "annotated found let"),
  ("a signature cannot be selected at a different binding site", !succeeds
    (sourceSelection (.letRec [] 0))),
  ("recursive source annotation/RHS arity mismatch rejects before selecting a member", fails malformed "arity mismatch"),
  ("out-of-scope written forall slots reject before proposals", !succeeds
    (synthetic identity ⟨1, .arrow (list (.bvar 1)) (list (.bvar 1))⟩)),
  ("out-of-scope slots in nested RHS annotations reject even when the root shape is closed", fails
    (synthetic (.found (.prim .int)
      (.lambda (some (.bvar 1)) (.found (.prim .int) (.primLit (.int 0)))))
      ⟨1, .prim .int⟩) "source RHS annotation"),
  ("enclosing original lexical slots remain explicitly guarded in the closed interface", fails
    (synthetic (.found (.arrow (.bvar 1) (.bvar 1))
      (.lambda none (.found (.bvar 1) (.var 0)))) signature) "enclosing lexical")]

def main : IO Unit := do
  for (name, ok) in cases do
    IO.println s!"{if ok then "PASS" else "FAIL"}: {name}"
    unless ok do throw (IO.userError s!"declared reconciliation regression failed: {name}")

#eval main

end FHM.Bounds.HMDeclaredReconciliationTests
