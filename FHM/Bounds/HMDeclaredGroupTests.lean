import FHM.Bounds.HMDeclaredGroup
import FHM.Bounds.Found

namespace FHM.Bounds.HMDeclaredGroupTests

open HMDeclaredGroup RecursiveHMJudgement

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

private def metadata (duplicateCounts : Bool := false) : Scope.Metadata :=
  { telescopes := [⟨.letRec [] 0, [(⟨"n"⟩, 7)]⟩,
      ⟨.letRec [] 1, [(⟨"m"⟩, if duplicateCounts then 7 else 8)]⟩] }

private def artifact (duplicateCounts : Bool := false) (badBounds : Bool := false)
    (unannotated : Bool := false) : Except String FoundResult := do
  let ctors : CtorEnv := (elabDecls preludeDecls).getD []
  let lastAnnotation : PolyTy := if badBounds then
    ⟨0, .bl (.solid (.lit 2)) (.solid (.lit 2)) (.prim .int)⟩ else ⟨0, .prim .int⟩
  let source := Expr.letRec
    [some (signature 7), if unannotated then none else some (signature (if duplicateCounts then 7 else 8)),
      some lastAnnotation]
    [.lambda none (.app (.var 2) (.var 0)), .lambda none (.app (.var 1) (.var 0)),
      if badBounds then .ctor nilCtorName else .primLit (.int 0)]
    (.primLit (.int 0))
  match inferFound ctors source with
  | some a => pure a
  | none => throw "test: three-member group HM inference failed"

private def exercise {output metadata path index vectors premises typeCaptures env}
    (ps : Interfaces output metadata path [] premises typeCaptures index vectors)
    (ms : CheckedMembers env ps) : Except String Bool := do
  match ps, ms with
  | .nil, .nil => pure true
  | .cons p _ tail, .cons checked rest =>
      let cert := checked.certificate
      let counts ← cert.interface.scheme.counts.instantiate (p.quantified.map (fun _ => .lit 3)) [7]
      let types := List.replicate p.declaration.annotation.paramCount arg
      have lc : ∀ a ∈ types, (Synth.BoundsTy.toTy a).IsLC := by
        intro a ha
        have ha : a = arg := (List.mem_replicate.mp ha).2
        subst a
        exact argLC arg (by simp)
      have inScope : types.all (ScopedScheme.boundsScopedBool [7]) = true := by
        simp [types, List.all_replicate, arg, count, ScopedScheme.boundsScopedBool, ScopedScheme.countScopedBool]
      let used := RecursiveHMEnvironment.atScopedSignedNode p.declaration.node cert counts
        checked.captured types (by simp [types]) lc inScope
      let expected : BoundsTy := if p.declaration.annotation.paramCount == 0 then .prim .int else
        .arrow (.list (.lit 3) (.lit 3) arg) (.list (.lit 3) (.lit 3) arg)
      let others ← exercise tail rest
      pure (used.typed.actual.pretty == expected.pretty && others)

private def actual : Except String Bool := do
  let a ← artifact
  let g ← HMDeclaredGroup.check a.output metadata [] [[91], [91], []] (schemes := a.binderSchemes)
  let used ← exercise g.interfaces g.members
  pure (g.interfaces.contracts.length == 3 && g.rhss.length == 3 &&
    g.interfaces.quantified == [7, 8] && used)

private def group (vectors : List (List Nat)) (duplicateCounts : Bool := false)
    (badBounds : Bool := false) (unannotated : Bool := false) : Except String Bool := do
  let a ← artifact duplicateCounts badBounds unannotated
  let g ← HMDeclaredGroup.check a.output (metadata duplicateCounts) [] vectors (schemes := a.binderSchemes)
  pure (g.interfaces.contracts.length == 3)

private def fails {α} (result : Except String α) (part : String) : Bool :=
  match result with | .error message => (message.splitOn part).length > 1 | _ => false

private def tests : List (String × Bool) := [
  ("all three real RHSs assemble and specialize in the same common environment with different HM/count arities",
    match actual with | .ok b => b | .error _ => false),
  ("a skipped member's opaque vector rejects the entire assembly",
    fails (group [[91], [91]]) "opaque vector/RHS arity"),
  ("extra opaque member vectors reject the entire assembly",
    fails (group [[91], [91], [], []]) "opaque vector/RHS arity"),
  ("shared solved HM identities cannot open at unrelated source forall coordinates",
    fails (group [[91], [92], []]) "shared solved HM identity"),
  ("member count telescopes cannot alias across the common group",
    fails (group [[91], [91], []] true) "count telescopes overlap"),
  ("a false contract on the final member prevents returning any accepted group",
    fails (group [[91], [91], []] false true) "inclusion"),
  ("an unannotated recursive member is explicitly guarded rather than assigned invented facts",
    fails (group [[91], [91], []] false false true) "no source annotation"),
  ("distinct solved identities can have different HM interfaces",
    match checkConsistent [(1, .prim .int), (2, .arrow (.fvar 91) (.fvar 91))] with
    | .ok _ => true | _ => false),
  ("repeated solved identities must have exactly the same complete HM shape",
    fails (checkConsistent [(1, .prim .int), (1, .arrow (.prim .int) (.prim .int))]) "shared solved HM identity")]

def main : IO Unit := do
  for (name, ok) in tests do
    if ok then IO.println s!"PASS: {name}"
    else throw (IO.userError s!"FAIL: {name}")

#eval main

end FHM.Bounds.HMDeclaredGroupTests
