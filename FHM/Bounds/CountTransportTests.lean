import FHM.Bounds.CountTransport

namespace FHM.Bounds.CountTransportTests

open SchemeTyping CountSubstitution

private def n : Count := .var ⟨.rigid, 7⟩
private def captured : BoundsTy := .list n n (.prim .char)
private def caller : BoundsTy := .list n n (.prim .int)
private def rows : Bindings := [(7, .lit 2)]
private theorem finite : Finite rows := by
  intro row hr
  simp only [rows, List.mem_singleton] at hr
  subst row
  exact .lit

private def s : Scheme :=
  ⟨⟨1, .arrow (.bvar 0) (listTy (.prim .char))⟩, .arrow (.bvar 0) captured,
    by
      change ContainsBvarsUpTo 1 (.arrow (.bvar 0) (listTy (.prim .char)))
      exact .arrow (.bvar (by omega)) (.customTy (by
        intro t ht
        simp only [List.mem_singleton] at ht
        subst t
        exact .prim)),
    by simp [captured, Synth.BoundsTy.toTy, listTy, FHM.Bounds.listTyName, _root_.listTyName]⟩
private def closure : Expr := .lambda none (.var 1)
private theorem instances : ∀ args, s.Arguments args →
    Derives [] [.mono captured] closure (s.instantiate args) := by
  intro args _
  exact .lambda True.intro (.varMono rfl)
private theorem callerArguments : (CountTransport.mapScheme rows s).Arguments [caller] := by
  refine ⟨rfl, ?_⟩
  intro t ht
  simp only [List.map_cons, List.map_nil, List.mem_singleton] at ht
  subst t
  simp only [caller, Synth.BoundsTy.toTy]
  exact .customTy (by
    intro t ht
    simp only [List.mem_singleton] at ht
    subst t
    exact .prim)

-- A caller count named 7 must remain 7, while the captured scheme count 7
-- becomes 2. Rewriting a previously chosen caller argument cannot prove this.
theorem callerCountCollision : Derives [] [.mono (.list (.lit 2) (.lit 2) (.prim .char))]
    closure (.arrow caller (.list (.lit 2) (.lit 2) (.prim .char))) := by
  have h := CountTransport.universal_from
    (fun rows hf Δ env β h => CountTransport.transport rows hf h)
    rows finite instances [caller] callerArguments
  simpa [CountTransport.mapScheme, CountTransport.mapBinding, Scheme.instantiate,
    TypeSubstitution.substitute, SchemeUse.vector, s, captured, rows, bounds, count, lookup] using h

private def nested : Expr := .letIn none closure (.var 0)
private theorem nestedTyping : Derives [] [.mono captured] nested (.arrow caller captured) :=
  .letPoly instances (.varPoly (s := s) (args := [caller]) rfl (by
    simpa only [CountTransport.mapScheme] using callerArguments))

-- Whole-derivation transport does specialize old use arguments: their lexical
-- environment is changing too. This is distinct from RHS universality above.
theorem nestedTransport : Derives [] [.mono (.list (.lit 2) (.lit 2) (.prim .char))]
    nested (.arrow (.list (.lit 2) (.lit 2) (.prim .int))
      (.list (.lit 2) (.lit 2) (.prim .char))) := by
  simpa [CountTransport.mapBinding, rows, bounds, count, lookup, caller, captured] using
    CountTransport.transport rows finite nestedTyping

private def fixedAnn : Ty := .bl (.solid (.lit 2)) (.solid (.lit 2)) (.prim .char)
private def fixedBounds : BoundsTy := .list (.lit 2) (.lit 2) (.prim .char)
private theorem annotated : Derives [] [] (.lambda (some fixedAnn) (.var 0))
    (.arrow fixedBounds fixedBounds) :=
  .lambda ⟨fixedBounds, by simp [fixedAnn, fixedBounds, Typed.annotation,
    bind, pure, Except.bind, Except.pure], SemanticSub.refl [] _⟩ (.varMono rfl)

example : Derives [] [] (.lambda (some fixedAnn) (.var 0)) (.arrow fixedBounds fixedBounds) := by
  simpa [fixedBounds, CountTransport.mapBinding, bounds, count] using
    CountTransport.transport rows finite annotated

-- Infinite replacement is not a Nat assignment: dropping finiteness really
-- breaks evaluation transport, rather than merely an executable policy.
example : (count [(7, .inf)] n).eval (fun _ => 0) = .inf := rfl
example : n.eval (assignment [(7, .inf)] (fun _ => 0)) = .ofNat 0 := rfl

private def cases : List (String × Bool) := [
  ("captured scheme count specialized", match (CountTransport.mapScheme rows s).body with
    | .arrow (.bvar 0) (.list (.lit 2) (.lit 2) (.prim .char)) => true | _ => false),
  ("stored HM metadata unchanged", match BinderBridge.equalTy (CountTransport.mapScheme rows s).hm.body s.hm.body with
    | some _ => (CountTransport.mapScheme rows s).hm.paramCount == s.hm.paramCount | none => false),
  ("arbitrary inserted caller count not rewritten", match
    (CountTransport.mapScheme rows s).instantiate [caller] with
    | .arrow (.list lo hi (.prim .int)) (.list (.lit 2) (.lit 2) (.prim .char)) => lo == n && hi == n
    | _ => false),
  ("old instantiated arguments transported with lexical environment", match
    bounds rows (s.instantiate [caller]) with
    | .arrow (.list (.lit 2) (.lit 2) (.prim .int)) (.list (.lit 2) (.lit 2) (.prim .char)) => true
    | _ => false),
  ("unselected outer count remains captured", count rows (.var ⟨.rigid, 9⟩) == .var ⟨.rigid, 9⟩),
  ("inferable machine counts are not generalized", count rows (.var ⟨.inferable, 7⟩) == .var ⟨.inferable, 7⟩),
  ("ground annotations stay fixed", match bounds rows fixedBounds with
    | .list (.lit 2) (.lit 2) (.prim .char) => true | _ => false),
  ("path condition counts specialized together", (constraint rows ⟨n, .lit 4⟩).lhs == .lit 2)]

def main : IO Unit := do
  for (name, ok) in cases do
    IO.println s!"{if ok then "PASS" else "FAIL"}: {name}"
    unless ok do throw (IO.userError s!"mixed count transport regression: {name}")

#eval main
#print axioms callerCountCollision
#print axioms nestedTransport

end FHM.Bounds.CountTransportTests
