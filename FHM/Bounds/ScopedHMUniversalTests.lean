import FHM.Bounds.RecursiveHMUniversal
import FHM.Bounds.RecursiveHMSigned
import FHM.Bounds.RecursiveHMWalk
import FHM.Bounds.Found

namespace FHM.Bounds.ScopedHMUniversalTests

open RecursiveHMJudgement ScopedHMInterpretation SurfaceBridge.Provenance

private def n : Count := .var ⟨.rigid, 7⟩
private def arg : BoundsTy := .list n n (.prim .int)

private def realUniversal (withMatch : Bool := false) : Except String Bool := do
  let ctors : CtorEnv := (elabDecls preludeDecls).getD []
  let param := Ty.bl (.solid n) (.solid n) (.bvar 0)
  let σ : PolyTy := ⟨1, .arrow param
    (.bl (.solid (if withMatch then .lit 0 else n)) (.solid n) (.bvar 0))⟩
  let rhs := Expr.lambda (some param) (if withMatch then .match_ (.var 0)
    [(.named consCtorName 2, .var 1), (.named nilCtorName 0, .ctor nilCtorName)] else .var 0)
  let artifact ← match inferFound ctors (.letIn (some σ) rhs (.primLit (.int 0))) with
    | some artifact => pure artifact | none => throw "test: scoped universal artifact inference failed"
  let node ← HMFoundView.locate artifact.output [.letRhs]
  let interface ← HMCountScheme.decodeAnnotated σ [7] []
  let opaqueSlots : Nat → BoundsTy := vector [.fvar 91]
  let opening ← HMCountScheme.openFixed interface.scheme (AtNode.view node BoundsTy.fvar opaqueSlots)
    [91] [node.original]
  let located ← RecursiveHMWalk.checkLocated node BoundsTy.fvar opaqueSlots [7] [] [7] [] []
    artifact.binderSchemes (some opening.bounds)
  let inclusion ← Typed.subtype [] located.typed.actual opening.bounds
  let cert := RecursiveHMUniversal.fromScopedChecked node opening located.typed inclusion.down
    (by intro c hc; cases hc) (by intro c hc; cases hc)
  let signed : RecursiveHMSigned.Certified σ [7] [] []
      (AtNode.view node BoundsTy.fvar opaqueSlots) [node.original] [] node.inner.stripFound
      BoundsTy.fvar opaqueSlots := ⟨interface, cert⟩
  let countInstance ← interface.scheme.counts.instantiate [.lit 3] [7]
  let used := RecursiveHMSigned.atScopedNode node signed countInstance [arg]
    (by cases withMatch <;> rfl)
    (by
      intro a ha
      have he : a = arg := by simpa using ha
      subst a
      simp only [arg, Synth.BoundsTy.toTy, listTy]
      exact .customTy (by
        intro t ht
        have ht : t = .prim .int := by simpa using ht
        subst t
        exact .prim))
    (by decide)
  let expected := BoundsTy.arrow (.list (.lit 3) (.lit 3) arg)
    (.list (if withMatch then .lit 0 else .lit 3) (.lit 3) arg)
  pure (used.typed.actual.pretty == expected.pretty &&
    (BinderBridge.candidates artifact.binderSchemes (.letIn [])).isEmpty &&
    exactlyOnce (logicalCorePaths (.found node.original node.inner))
      (located.nodes.map fun node => node.path.drop 1))

private def cases : List (String × Bool) := [
  ("real annotated forall RHS specializes the original node, written signature and full caller intervals", match realUniversal with
    | .ok ok => ok | .error _ => false),
  ("real annotated lexical List-match specializes actual branch proofs and its written source signature", match realUniversal true with
    | .ok ok => ok | .error _ => false)]

def main : IO Unit := do
  for (name, ok) in cases do
    IO.println s!"{if ok then "PASS" else "FAIL"}: {name}"
    unless ok do throw (IO.userError s!"scoped HM universal regression failed: {name}")

#eval main

end FHM.Bounds.ScopedHMUniversalTests
