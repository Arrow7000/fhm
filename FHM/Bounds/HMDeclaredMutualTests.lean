import FHM.Bounds.HMDeclaredRHS
import FHM.Bounds.Found

namespace FHM.Bounds.HMDeclaredMutualTests

open HMDeclaredReconciliation RecursiveHMJudgement SurfaceBridge.Provenance

private def count (i : Nat) : Count := .var ⟨.rigid, i⟩
private def signature (i : Nat) : PolyTy :=
  ⟨1, .arrow (.bl (.solid (count i)) (.solid (count i)) (.bvar 0))
    (.bl (.solid (count i)) (.solid (count i)) (.bvar 0))⟩
private def arg : BoundsTy := .list (count 7) (count 7) (.prim .int)
private theorem argLC : ∀ a ∈ [arg], (Synth.BoundsTy.toTy a).IsLC := by
  intro a ha
  have ha : a = arg := by simpa using ha
  subst a
  apply (Ty.bvarsBelow_iff _).mp
  simp [arg, Synth.BoundsTy.toTy, listTy, Ty.bvarsBelow, TyList.bvarsBelow]

private def vectors (env : List Binding) : List (List String) :=
  env.map fun b => match b with
    | .mono β => [β.pretty]
    | .recursive c => c.fixed.types.map BoundsTy.pretty

/-- Both real members check against one common fixed HM vector, despite
    distinct count telescopes and genuinely more-general solved RHS payloads. -/
private def actual : Except String Bool := do
  let ctors : CtorEnv := (elabDecls preludeDecls).getD []
  let source := Expr.letRec [some (signature 7), some (signature 8)]
    [.lambda none (.app (.var 2) (.var 0)), .lambda none (.app (.var 1) (.var 0))]
    (.primLit (.int 0))
  let artifact ← match inferFound ctors source with
    | some artifact => pure artifact | none => throw "test: mutual declared RHS inference failed"
  let d1 ← locate artifact.output (.letRec [] 0)
  let d2 ← locate artifact.output (.letRec [] 1)
  let captures := [d1.annotation.body.eraseBounds, d2.annotation.body.eraseBounds]
  let c1 ← HMDeclaredReconciliation.check d1 [7] [] [91] captures
  let c2 ← HMDeclaredReconciliation.check d2 [8] [] [91] captures
  if hs : c1.signatureIds = c2.signatureIds then
    let b1 : Contract := ⟨c1.interface.scheme, _, RecursiveHMContract.fromOpaque c1.opening⟩
    let b2 : Contract := ⟨c2.interface.scheme, _, RecursiveHMContract.fromOpaque c2.opening⟩
    have sameFixed : b1.fixed.types = b2.fixed.types := by
      exact c1.fixedTypes.trans ((congrArg (List.map BoundsTy.fvar) hs).trans c2.fixedTypes.symm)
    let env : List Binding := [.recursive b1, .recursive b2]
    let checked1 ← HMDeclaredRHS.check c1 env artifact.binderSchemes
    let checked2 ← HMDeclaredRHS.check c2 env artifact.binderSchemes
    have represented : ∀ b, .recursive b ∈ env → b.template.hm.body ∈ captures := by
      intro b hb
      have hb : b = b1 ∨ b = b2 := by simpa [env] using hb
      rcases hb with rfl | rfl <;>
        simp [captures, b1, b2, HMCountScheme.Annotated.scheme, PolyTy.eraseBounds]
    have fresh1 : ∀ b, .recursive b ∈ env → ∀ i ∈ b.template.counts.captures, i ∉ [7] := by
      intro b hb i hi
      have hb : b = b1 ∨ b = b2 := by simpa [env] using hb
      rcases hb with rfl | rfl <;>
        simp [b1, b2, HMCountScheme.Annotated.scheme, ScopedAnnotation.Contract.scheme] at hi
    have fresh2 : ∀ b, .recursive b ∈ env → ∀ i ∈ b.template.counts.captures, i ∉ [8] := by
      intro b hb i hi
      have hb : b = b1 ∨ b = b2 := by simpa [env] using hb
      rcases hb with rfl | rfl <;>
        simp [b1, b2, HMCountScheme.Annotated.scheme, ScopedAnnotation.Contract.scheme] at hi
    let cert1 := HMDeclaredRHS.certify c1 checked1 represented fresh1
    let cert2 := HMDeclaredRHS.certify c2 checked2 represented fresh2
    let counts1 ← c1.interface.scheme.counts.instantiate [.lit 3] [7]
    let counts2 ← c2.interface.scheme.counts.instantiate [.lit 3] [7]
    if ha1 : [arg].length = d1.annotation.paramCount then
      if ha2 : [arg].length = d2.annotation.paramCount then
        let used1 := RecursiveHMSigned.atScopedNode d1.node cert1 counts1 [arg] ha1 argLC (by decide)
        let used2 := RecursiveHMSigned.atScopedNode d2.node cert2 counts2 [arg] ha2 argLC (by decide)
        let after1 := RecursiveHMUniversal.interpretedEnvironment cert1.implementation [.lit 3] [arg] argLC
        let after2 := RecursiveHMUniversal.interpretedEnvironment cert2.implementation [.lit 3] [arg] argLC
        let expected := BoundsTy.arrow (.list (.lit 3) (.lit 3) arg) (.list (.lit 3) (.lit 3) arg)
        pure (used1.typed.actual.pretty == expected.pretty && used2.typed.actual.pretty == expected.pretty &&
          vectors after1 == [[arg.pretty], [arg.pretty]] && vectors after2 == vectors after1 &&
          exactlyOnce (logicalCorePaths (.found d1.node.original d1.node.inner))
            (checked1.located.nodes.map fun node => node.path.drop 1) &&
          exactlyOnce (logicalCorePaths (.found d2.node.original d2.node.inner))
            (checked2.located.nodes.map fun node => node.path.drop 1))
      else throw "test: second member did not retain one source HM slot"
    else throw "test: first member did not retain one source HM slot"
  else throw "test: mutual members do not share their opaque HM opening"

def main : IO Unit := do
  match actual with
  | .error message => throw (IO.userError message)
  | .ok false => throw (IO.userError "mutual source-site universal specialization lost bounds/vector/path coherence")
  | .ok true => IO.println "PASS: both more-general mutual RHSs share a fixed HM vector across distinct count telescopes and full caller specialization"

#eval main

end FHM.Bounds.HMDeclaredMutualTests
