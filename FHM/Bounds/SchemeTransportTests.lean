import FHM.Bounds.SchemeTransport

namespace FHM.Bounds.SchemeTransportTests

open SchemeTyping SchemeSpecialization

private def idScheme : Scheme :=
  ⟨⟨1, .arrow (.bvar 0) (.bvar 0)⟩, .arrow (.bvar 0) (.bvar 0),
    by
      change ContainsBvarsUpTo 1 (.arrow (.bvar 0) (.bvar 0))
      exact .arrow (.bvar (by omega)) (.bvar (by omega)),
    by simp [Synth.BoundsTy.toTy]⟩

private def rhs : Expr := .lambda none (.app (.var 1) (.var 0))
private def mono : BoundsTy := .arrow (.fvar 7) (.fvar 7)
private theorem rhsTyping : Derives [] [.poly idScheme] rhs mono := by
  apply Derives.lambda (ann := none) True.intro
  apply Derives.app (domain := .fvar 7) (actual := .fvar 7)
  · exact .varPoly (s := idScheme) (args := [.fvar 7]) rfl ⟨rfl, by
      intro t ht
      simp only [List.map_cons, List.map_nil, Synth.BoundsTy.toTy, List.mem_singleton] at ht
      subst t
      exact .fvar⟩
  · exact .varMono rfl
  · exact .fvar

-- This RHS genuinely uses an existing polymorphic binding, rather than being
-- silently checked in a monomorphic approximation of its environment.
example (a : BinderBridge.Abstraction ⟨1, .arrow (.bvar 0) (.bvar 0)⟩ mono
    ([.poly idScheme].map SchemeTransport.interface ++ rhs.tyFreeVars.map Ty.fvar)) :
    ∀ args, (SchemeTyping.fromBinder a).Arguments args →
      Derives [] [.poly idScheme] rhs ((SchemeTyping.fromBinder a).instantiate args) :=
  SchemeTransport.binder_instances a rhsTyping

private def n : Count := .var ⟨.rigid, 7⟩
private def caller : BoundsTy := .list n n (.prim .char)
private def f : Nat → BoundsTy := fun i => if i = 7 then caller else .fvar i
private theorem fLC : ∀ i, (Synth.BoundsTy.toTy (f i)).IsLC := by
  intro i
  simp only [f]
  split
  · simp only [caller, Synth.BoundsTy.toTy, listTy]
    exact .customTy (by intro t ht; simp only [List.mem_singleton] at ht; subst t; exact .prim)
  · simp only [Synth.BoundsTy.toTy]; exact .fvar

private def capturedScheme : Scheme :=
  ⟨⟨1, .arrow (.bvar 0) (.fvar 7)⟩, .arrow (.bvar 0) (.fvar 7),
    by
      change ContainsBvarsUpTo 1 (.arrow (.bvar 0) (.fvar 7))
      exact .arrow (.bvar (by omega)) .fvar,
    by simp [Synth.BoundsTy.toTy]⟩
private def closure : Expr := .lambda none (.var 1)
private theorem capturedInstances : ∀ args, capturedScheme.Arguments args →
    Derives [] [.mono (.fvar 7)] closure (capturedScheme.instantiate args) := by
  intro args _
  exact .lambda True.intro (.varMono rfl)

-- The transported captured identity becomes a bounded List, but an arbitrary
-- caller argument fvar7 stays fvar7. A naive map over the old caller arguments
-- would turn BOTH into List and would not establish this universal instance.
theorem callerCollision : Derives [] [.mono caller] closure (.arrow (.fvar 7) caller) := by
  have h := SchemeTransport.universal_from
    (fun f hf env β h hs => SchemeTransport.transport f hf h hs)
    f fLC capturedInstances (by simp [closure, Expr.tyFreeVars]) [.fvar 7]
    (by
      refine ⟨rfl, ?_⟩
      intro t ht
      simp only [List.map_cons, List.map_nil, Synth.BoundsTy.toTy, List.mem_singleton] at ht
      subst t
      exact .fvar)
  simpa [SchemeTransport.mapBinding, SchemeTransport.mapScheme, Scheme.instantiate,
    TypeSubstitution.substitute, SchemeUse.vector, capturedScheme, mapFree, f] using h

private def nested : Expr := .letIn none closure (.var 0)
private theorem nestedTyping : Derives [] [.mono (.fvar 7)] nested (.arrow (.fvar 7) (.fvar 7)) :=
  .letPoly capturedInstances (.varPoly (s := capturedScheme) (args := [.fvar 7]) rfl ⟨rfl, by
    intro t ht
    simp only [List.map_cons, List.map_nil, Synth.BoundsTy.toTy, List.mem_singleton] at ht
    subst t
    exact .fvar⟩)

-- Whole-term transport includes an actual polymorphic let introduction.
theorem nestedTransport : Derives [] [.mono caller] nested (.arrow caller caller) := by
  simpa [SchemeTransport.mapBinding, mapFree, f] using
    SchemeTransport.transport f fLC nestedTyping (by simp [nested, closure, Expr.tyFreeVars])

-- Non-LC free replacements really do get captured by bound-slot substitution;
-- the LC hypothesis in the algebra must not be deleted as "just freshness".
example : mapFree (fun _ => .bvar 0) (TypeSubstitution.substitute (fun _ => .prim .int) (.fvar 7)) = .bvar 0 := rfl
example : TypeSubstitution.substitute (fun _ => .prim .int) (mapFree (fun _ => .bvar 0) (.fvar 7)) = .prim .int := rfl

private def cases : List (String × Bool) := [
  ("HM metadata remains bounds-blind", match (SchemeTransport.mapScheme f fLC capturedScheme).hm.body with
    | .arrow (.bvar 0) (.customTy _ [.prim .char]) => true | _ => false),
  ("captured count payloads remain in bounds body", match (SchemeTransport.mapScheme f fLC capturedScheme).body with
    | .arrow (.bvar 0) (.list lo hi (.prim .char)) => lo == n && hi == n | _ => false),
  ("caller identity collision does not alter inserted slot", match
      (SchemeTransport.mapScheme f fLC capturedScheme).instantiate [.fvar 7] with
    | .arrow (.fvar 7) (.list lo hi (.prim .char)) => lo == n && hi == n | _ => false),
  ("placeholder protection is local to fresh block", match SchemeTransport.protect f 100 2 7 with
    | .list _ _ (.prim .char) => true | _ => false),
  ("placeholder identity is protected", match SchemeTransport.protect f 100 2 100 with
    | .fvar 100 => true | _ => false),
  ("caller bounds may mention placeholder identity", match
      SchemeTransport.replaceBlock [.fvar 100] 100 1 100 with
    | .fvar 100 => true | _ => false),
  ("block substitution does not rewrite captured count namespace", match
      mapFree (SchemeTransport.replaceBlock [.prim .int] 100 1) (.list n n (.fvar 100)) with
    | .list lo hi (.prim .int) => lo == n && hi == n | _ => false),
  ("nested scheme arity unchanged", (SchemeTransport.mapScheme f fLC capturedScheme).hm.paramCount == 1)]

def main : IO Unit := do
  for (name, ok) in cases do
    IO.println s!"{if ok then "PASS" else "FAIL"}: {name}"
    unless ok do throw (IO.userError s!"mixed scheme transport regression: {name}")

#eval main
#print axioms callerCollision
#print axioms nestedTransport

end FHM.Bounds.SchemeTransportTests
