import FHM.Bounds.RecursiveHMUniform
import FHM.Bounds.HMDeclaredCoordinates
import FHM.Bounds.Found

namespace FHM.Bounds.RecursiveHMUniformTests

open HMDeclaredGroup RecursiveHMJudgement RecursiveHMUniform

private def count (i : Nat) : Count := .var ⟨.rigid, i⟩
private def argument (i : Nat) : BoundsTy :=
  .list (count 7) (count 7) (.prim (if i % 2 == 0 then .int else .char))
private theorem argumentLC : ∀ i, (Synth.BoundsTy.toTy (argument i)).IsLC := by
  intro i
  apply (Ty.bvarsBelow_iff _).mp
  simp [argument, Synth.BoundsTy.toTy, listTy, Ty.bvarsBelow, TyList.bvarsBelow]
private theorem argumentScope : ∀ i, ScopedScheme.BoundsScoped [7] (argument i) := by
  intro i
  exact ScopedScheme.boundsScopedBool_sound (by
    simp [argument, count, ScopedScheme.boundsScopedBool, ScopedScheme.countScopedBool])

private def signature (i : Nat) (swap : Bool := false) : PolyTy :=
  ⟨2, .arrow (.bl (.solid (count i)) (.solid (count i)) (.bvar (if swap then 1 else 0)))
    (.bl (.solid (count i)) (.solid (count i)) (.bvar (if swap then 0 else 1)))⟩

private def exercise {output metadata path captures premises typeCaptures env index vectors}
    {ps : Interfaces output metadata path captures premises typeCaptures index vectors}
    (ms : CheckedMembers env ps) (uniform : RecursiveHMUniform.Members argument argumentLC argumentScope ms) :
    Except String Bool := do
  match ms, uniform with
  | .nil, .nil => pure true
  | .cons (p := p) checked rest, .cons obligations others =>
      let cert := checked.certificate
      let counts := p.quantified.map (fun _ => Count.lit 3)
      let inst ← cert.interface.scheme.counts.instantiate counts [7]
      let r := obligations counts inst
      let own : Contract := ⟨cert.interface.scheme, _, RecursiveHMContract.fromOpaque cert.implementation.opening⟩
      let fixed ← RecursiveHMEnvironment.checkTemplateFixed argument [.recursive own]
      have sourceFixed : ∀ i ∈ cert.interface.scheme.hm.body.freeVars, argument i = .fvar i :=
        fixed.down own (by simp)
      let signed := RecursiveHMUniform.atSignedNode p.declaration.node cert r sourceFixed
      let bounds := signed.typed.actual
      let exactCounts := match bounds with
        | .prim .int => true
        | .arrow (.list lo hi (.list a b _)) (.list lo' hi' (.list a' b' _)) =>
            lo == .lit 3 && hi == .lit 3 && lo' == .lit 3 && hi' == .lit 3 &&
            a == count 7 && b == count 7 && a' == count 7 && b' == count 7
        | _ => false
      let tail ← exercise rest others
      pure (exactCounts && tail)

private def actual : Except String Bool := do
  let ctors : CtorEnv := (elabDecls preludeDecls).getD []
  let source := Expr.letRec [some (signature 7), some (signature 8 true), some ⟨0, .prim .int⟩]
    [.lambda none (.app (.var 2) (.var 0)), .lambda none (.app (.var 1) (.var 0)), .primLit (.int 0)]
    (.primLit (.int 0))
  let a ← match inferFound ctors source with
    | some a => pure a | none => throw "test: permuted mutual group HM inference failed"
  let metadata : Scope.Metadata :=
    { telescopes := [⟨.letRec [] 0, [(⟨"n"⟩, 7)]⟩, ⟨.letRec [] 1, [(⟨"m"⟩, 8)]⟩] }
  let g ← HMDeclaredCoordinates.check a.output metadata [] (schemes := a.binderSchemes)
  let env := g.checked.interfaces.contracts.map Binding.recursive ++ []
  let fixed ← RecursiveHMEnvironment.checkTemplateFixed argument env
  let all := RecursiveHMUniform.allMembers g.checked.members argument argumentLC argumentScope fixed.down
  exercise g.checked.members all

private def changedCapture : Except String Bool := do
  let template ← HMCountScheme.decode ⟨0, .arrow (.fvar 90) (.fvar 90)⟩ [] []
  let found := Ty.arrow (.fvar 90) (.fvar 90)
  let fixed ← RecursiveHMContract.fix template found []
  let c : Contract := ⟨template, found, fixed⟩
  match RecursiveHMEnvironment.checkTemplateFixed argument [.recursive c] with
  | .ok _ => throw "test: uniform group map rewrote a closed template's captured HM identity"
  | .error _ => pure true

def main : IO Unit := do
  match actual with
  | .ok true => IO.println "PASS: every actual member universally specializes through one full group HM map with permuted slots and distinct count telescopes"
  | .error message => throw (IO.userError message)
  | .ok false => throw (IO.userError "uniform group transport captured caller counts inside full HM arguments")
  match changedCapture with
  | .ok true => IO.println "PASS: uniform group specialization cannot rewrite closed recursive template captures"
  | .error message => throw (IO.userError message)
  | .ok false => throw (IO.userError "closed recursive template capture guard failed")

#eval main

end FHM.Bounds.RecursiveHMUniformTests
