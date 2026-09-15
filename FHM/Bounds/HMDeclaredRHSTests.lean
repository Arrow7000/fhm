import FHM.Bounds.HMDeclaredRHS
import FHM.Bounds.Found

namespace FHM.Bounds.HMDeclaredRHSTests

open HMDeclaredReconciliation RecursiveHMJudgement SurfaceBridge.Provenance

private def n : Count := .var ⟨.rigid, 7⟩
private def arg : BoundsTy := .list n n (.prim .int)
private def param : Ty := .bl (.solid n) (.solid n) (.bvar 0)
private def signature (falseClaim : Bool := false) : PolyTy :=
  ⟨1, .arrow param (.bl (.solid (if falseClaim then .lit 0 else n))
    (.solid (if falseClaim then .lit 0 else n)) (.bvar 0))⟩

private def actual (recursive : Bool := false) (falseClaim : Bool := false)
    (localChoice : Nat := 0) : Except String Bool := do
  let ctors : CtorEnv := (elabDecls preludeDecls).getD []
  let σ := signature falseClaim
  let body := if recursive then Expr.app (.var 1) (.var 0) else .var 0
  let localAnn := if localChoice = 3 then
      Ty.bl (.solid (.lit 0)) (.solid (.lit 0)) (.bvar 0) else param
  let rhs := Expr.lambda (if recursive then none else some param)
    (if localChoice = 0 then body else .letIn (if localChoice = 1 then none else some ⟨0, localAnn⟩)
      (.var 0) (.var 0))
  let source := if recursive then Expr.letRec [some σ] [rhs] (.primLit (.int 0))
    else Expr.letIn (some σ) rhs (.primLit (.int 0))
  let artifact ← match inferFound ctors source with
    | some artifact => pure artifact | none => throw "test: declared RHS inference failed"
  let site := if recursive then CoreBinderSite.letRec [] 0 else .letIn []
  let d ← locate artifact.output site
  let typeCaptures := if recursive then [d.annotation.body.eraseBounds] else []
  let c ← HMDeclaredReconciliation.check d [7] [] [91] typeCaptures
  if localChoice > 1 then
    unless (BinderBridge.candidates artifact.binderSchemes (.letIn [.letRhs, .lambdaBody])).isEmpty do
      throw "test: annotated local unexpectedly acquired an inferred binder fact"
  let contract : Contract := ⟨c.interface.scheme, _, RecursiveHMContract.fromOpaque c.opening⟩
  let env : List Binding := if recursive then [.recursive contract] else []
  let checked ← HMDeclaredRHS.check c env artifact.binderSchemes
  let cert := HMDeclaredRHS.certify c checked
    (by
      intro b hb
      cases recursive with
      | false => simp [env] at hb
      | true =>
          have hb : b = contract := by simpa [env] using hb
          subst b
          simp [typeCaptures, contract, HMCountScheme.Annotated.scheme, PolyTy.eraseBounds])
    (by
      intro b hb
      cases recursive <;> simp [env] at hb)
    (by
      intro b hb i hi
      cases recursive with
      | false => simp [env] at hb
      | true =>
          have hb : b = contract := by simpa [env] using hb
          subst b
          simp [contract, HMCountScheme.Annotated.scheme, ScopedAnnotation.Contract.scheme] at hi)
    (by
      intro b hb
      cases recursive <;> simp [env] at hb)
  let sourceCert := cert.implementation.sourceFree (sourceTypes' := BoundsTy.fvar)
    (fun _ named => c.sourceIdentity named)
  let rhsReady ← match checked.located.typed.runtimeReady with
    | some proof => pure proof
    | none => throw "test: actual declared RHS lost its supported runtime witness"
  have _sourceReady : ScopedDerives.RuntimeReady sourceCert.typing :=
    RecursiveHMUniversal.Certified.sourceFree_runtimeReady cert.implementation
      (fun _ named => c.sourceIdentity named) rhsReady.down
  have _sameActual : sourceCert.actual = cert.implementation.actual := rfl
  have _sameOpening : sourceCert.opening.ids = cert.implementation.opening.ids := rfl
  let counts ← c.interface.scheme.counts.instantiate [.lit 3] [7]
  if ha : [arg].length = d.annotation.paramCount then
    let used := RecursiveHMSigned.atScopedNode d.node cert counts [arg]
      ha
      (by
        intro a ha
        have ha : a = arg := by simpa using ha
        subst a
        apply (Ty.bvarsBelow_iff _).mp
        simp [arg, Synth.BoundsTy.toTy, listTy, Ty.bvarsBelow, TyList.bvarsBelow])
      (by decide)
    let expected := BoundsTy.arrow (.list (.lit 3) (.lit 3) arg) (.list (.lit 3) (.lit 3) arg)
    pure (used.typed.actual.pretty == expected.pretty && exactlyOnce
      (logicalCorePaths (.found d.node.original d.node.inner))
      (checked.located.nodes.map fun node => node.path.drop 1) &&
      (BinderBridge.candidates artifact.binderSchemes site).isEmpty)
  
  else throw "test: source annotation did not retain one HM slot"

private def prepareMetadata (duplicate : Bool := false) (unresolved : Bool := false) : Except String Bool := do
  let hm := Ty.arrow (.fvar 90) (.fvar 90)
  let rhs := Expr.found hm (.lambda none (.found (.fvar 90) (.var 0)))
  let output := Expr.found (.prim .int) (.letIn (some (signature false)) rhs
    (.found (.prim .int) (.primLit (.int 0))))
  let telescope : Scope.Telescope := ⟨.letIn [], [(⟨"n"⟩, 7)]⟩
  let metadata : Scope.Metadata :=
    { telescopes := if duplicate then [telescope, telescope] else [telescope]
      problems := if unresolved then [⟨.letIn [], [⟨"missing"⟩], []⟩] else [] }
  let p ← HMDeclaredRHS.prepare output metadata (.letIn []) [91]
  pure (p.quantified == [7] && p.reconciled.signatureIds == [91])

private def passes (r : Except String Bool) : Bool := match r with | .ok ok => ok | _ => false
private def fails (r : Except String Bool) (message : String) : Bool := match r with
  | .error error => (error.splitOn message).length > 1
  | _ => false

private def cases : List (String × Bool) := [
  ("actual source-site forall identity becomes a universal signed original-node certificate", passes actual),
  ("more-general alpha-to-beta recursive implementation is checked against its narrower forall/List ceiling", passes
    (actual true)),
  ("HM-compatible false result bounds fail actual RHS inclusion, not source decoding", fails
    (actual false true) "interval inclusion"),
  ("real inferred mono local captures the enclosing lexical forall slot without re-generalizing it", passes
    (actual false false 1)),
  ("real annotated mono local checks its source obligation without an invented machine fact", passes
    (actual false false 2)),
  ("false bounds in a real annotated mono local fail independent inclusion", fails
    (actual false false 3) "interval inclusion"),
  ("source-site preparation retains the exact lowering count telescope", passes prepareMetadata),
  ("duplicate lowering count telescopes reject instead of choosing one", fails
    (prepareMetadata true) "duplicate count telescope"),
  ("unresolved lowering count scope cannot enter declared RHS checking", fails
    (prepareMetadata false true) "unresolved or duplicate count scope")]

def main : IO Unit := do
  for (name, ok) in cases do
    IO.println s!"{if ok then "PASS" else "FAIL"}: {name}"
    unless ok do throw (IO.userError s!"declared RHS regression failed: {name}")

#eval main

end FHM.Bounds.HMDeclaredRHSTests
