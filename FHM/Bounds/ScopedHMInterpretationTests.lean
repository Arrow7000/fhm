import FHM.Bounds.ScopedHMFoundView
import FHM.Bounds.Found

namespace FHM.Bounds.ScopedHMInterpretationTests

open ScopedHMInterpretation

private def n : Count := .var ⟨.rigid, 7⟩
private def arg : BoundsTy := .list n n (.prim .int)
private def bound : Nat → BoundsTy := vector [arg]
private def free (i : Nat) : BoundsTy := if i = 90 then .prim .char else .fvar i

private def simultaneous : Bool :=
  match read (fun i => if i = 90 then .prim .int else .fvar i)
      (vector [.fvar 90]) (.arrow (.fvar 90) (.bvar 0)) with
  | .arrow (.prim .int) (.fvar 90) => true
  | _ => false

private def countBeforeInsertion : Bool :=
  match read BoundsTy.fvar bound (CountSubstitution.bounds [(7, .lit 3)] (.list n n (.bvar 0))) with
  | .list lo hi (.list callerLo callerHi (.prim .int)) =>
      lo == .lit 3 && hi == .lit 3 && callerLo == n && callerHi == n
  | _ => false

private def realAnnotatedArtifact : Except String Bool := do
  let ctors : CtorEnv := (elabDecls preludeDecls).getD []
  let signature : PolyTy := ⟨1, .arrow (.bvar 0) (.bvar 0)⟩
  let source : Expr := .letIn (some signature) (.lambda (some (.bvar 0)) (.var 0)) (.primLit (.int 0))
  let artifact ← match inferFound ctors source with
    | some artifact => pure artifact | none => throw "test: annotated forall inference failed"
  let root ← HMFoundView.locate artifact.output [.letRhs]
  let body ← HMFoundView.locate artifact.output [.letRhs, .lambdaBody]
  let slot : Nat → BoundsTy := vector [.fvar 91]
  let rootView := AtNode.view root BoundsTy.fvar slot
  let bodyView := AtNode.view body BoundsTy.fvar slot
  let carried ← match root.inner with
    | .lambda (some ann) _ => do
        let decoded ← ScopedAnnotation.decode [] ann
        pure decoded.bounds
    | _ => throw "test: original carried scoped parameter annotation missing"
  let annotationView := Synth.BoundsTy.toTy (read BoundsTy.fvar slot carried)
  pure (match root.original, body.original, rootView, bodyView, annotationView with
    | .arrow (.bvar 0) (.bvar 0), .bvar 0, .arrow (.fvar 91) (.fvar 91), .fvar 91, .fvar 91 =>
        BinderBridge.candidates artifact.binderSchemes (.letIn []) |>.isEmpty
    | _, _, _, _, _ => false)

example (β : BoundsTy) (rows : CountSubstitution.Bindings) :
    CountSubstitution.bounds rows (read free bound β) =
      read (fun i => CountSubstitution.bounds rows (free i))
        (fun i => CountSubstitution.bounds rows (bound i)) (CountSubstitution.bounds rows β) :=
  map_counts rows free bound β

example (β : BoundsTy) (outer : Nat → BoundsTy) :
    SchemeSpecialization.mapFree outer (read free bound β) =
      read (fun i => SchemeSpecialization.mapFree outer (free i))
        (fun i => SchemeSpecialization.mapFree outer (bound i)) β := map_types outer free bound β

example (τ : Ty) : ty (fun _ => .list (.lit 2) (.lit 2) (.prim .int))
    (fun _ => .list (.lit 3) (.lit 3) (.prim .char)) τ =
    ty (fun _ => .list (.lit 0) .inf (.prim .int)) (fun _ => .list (.lit 0) .inf (.prim .char)) τ := by
  apply counts_blind <;> intro i <;> simp only [Synth.BoundsTy.toTy]

private def cases : List (String × Bool) := [
  ("free and bound namespaces are interpreted simultaneously", simultaneous),
  ("counts in inserted bound-slot types remain caller-owned", countBeforeInsertion),
  ("a supplied full lexical slot renders its ordinary HM List shape", match ty free bound (.bvar 0) with
    | .customTy name [.prim .int] => name == FHM.Bounds.listTyName | _ => false),
  ("bound slot with no supplied witness remains bound rather than becoming Unit", match bound 1 with
    | .bvar 1 => true | _ => false),
  ("explicit arbitrary vacuous slot is retained by its supplied vector", match vector [.prim .char] 0 with
    | .prim .char => true | _ => false),
  ("original annotated forall root/body/parameter views need no made-up machine fact", match realAnnotatedArtifact with
    | .ok ok => ok | .error _ => false)]

def main : IO Unit := do
  for (name, ok) in cases do
    IO.println s!"{if ok then "PASS" else "FAIL"}: {name}"
    unless ok do throw (IO.userError s!"scoped HM reader regression failed: {name}")

#eval main

end FHM.Bounds.ScopedHMInterpretationTests
