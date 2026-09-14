import FHM.Bounds.SchemeTyping

namespace FHM.Bounds.SchemeTypingTests

open SchemeTyping

private def idScheme : Scheme :=
  ⟨⟨1, .arrow (.bvar 0) (.bvar 0)⟩, .arrow (.bvar 0) (.bvar 0),
    by
      change ContainsBvarsUpTo 1 (.arrow (.bvar 0) (.bvar 0))
      exact .arrow (.bvar (by omega)) (.bvar (by omega)),
    by simp [Synth.BoundsTy.toTy, Ty.eraseBounds]⟩
private def identity : Expr := .lambda none (.var 0)

private theorem identityInstances : ∀ args, idScheme.Arguments args →
    Derives [] [] identity (idScheme.instantiate args) := by
  intro args _
  exact .lambda True.intro (.varMono rfl)

private theorem argument (β : BoundsTy) (h : (Synth.BoundsTy.toTy β).IsLC) :
    idScheme.Arguments [β] := by
  refine ⟨rfl, ?_⟩
  intro t ht
  simp only [List.map_cons, List.map_nil, List.mem_singleton] at ht
  subst t
  exact h

private def program : Expr := .letIn none identity
  (.letIn none (.app (.var 0) (.primLit (.int 1)))
    (.app (.var 1) (.primLit (.char 'a'))))

-- One binding is independently specialized at Int and Char. The inner mono let
-- changes the de Bruijn depth, but does not shadow away the polymorphic entry.
theorem independentUses : Derives [] [] program (.prim .char) := by
  apply Derives.letPoly (s := idScheme) identityInstances
  apply Derives.letMono (ann := none) (actual := .prim .int) True.intro
  · apply Derives.app (domain := .prim .int) (actual := .prim .int)
    · exact .varPoly (args := [.prim .int]) rfl
        (argument _ (by simp only [Synth.BoundsTy.toTy]; exact .prim))
    · exact .literal
    · exact .prim
  · apply Derives.app (domain := .prim .char) (actual := .prim .char)
    · exact .varPoly (args := [.prim .char]) rfl
        (argument _ (by simp only [Synth.BoundsTy.toTy]; exact .prim))
    · exact .literal
    · exact .prim

-- Lambda parameters stay monomorphic even in a polymorphic environment.
example : Derives [] [.poly idScheme] (.lambda none (.var 0))
    (.arrow (.prim .int) (.prim .int)) := .lambda True.intro (.varMono rfl)

-- Every instance has the formal HM opening, including caller list shapes.
example : idScheme.hm.eraseBounds.InstantiatesTo [listTy (.prim .char)]
    (.arrow (listTy (.prim .char)) (listTy (.prim .char))) := by
  simpa [Synth.BoundsTy.toTy, idScheme, Scheme.instantiate, TypeSubstitution.substitute,
    SchemeUse.vector] using instance_shape idScheme [.list (.lit 3) (.lit 3) (.prim .char)]
    (argument _ (by
      simp only [Synth.BoundsTy.toTy, listTy]
      exact .customTy (by intro t ht; simp only [List.mem_singleton] at ht; subst t; exact .prim)))

example : ¬ idScheme.Arguments [] := by
  intro h
  have := h.1
  simp [idScheme] at this

example : ¬ idScheme.Arguments [.prim .int, .prim .char] := by
  intro h
  have := h.1
  simp [idScheme] at this

-- A captured free HM identity is not a slot, even when it has the same number.
private def capturedScheme : Scheme :=
  ⟨⟨1, .arrow (.fvar 0) (.bvar 0)⟩, .arrow (.fvar 0) (.bvar 0),
    by
      change ContainsBvarsUpTo 1 (.arrow (.fvar 0) (.bvar 0))
      exact .arrow .fvar (.bvar (by omega)),
    by simp [Synth.BoundsTy.toTy, Ty.eraseBounds]⟩
example : capturedScheme.instantiate [.prim .char] = .arrow (.fvar 0) (.prim .char) := rfl

private def cases : List (String × Bool) := [
  ("Int instance", match idScheme.instantiate [.prim .int] with
    | .arrow (.prim .int) (.prim .int) => true | _ => false),
  ("Char instance", match idScheme.instantiate [.prim .char] with
    | .arrow (.prim .char) (.prim .char) => true | _ => false),
  ("full list bounds instance", match idScheme.instantiate [.list (.lit 3) (.lit 3) (.prim .char)] with
    | .arrow (.list (.lit 3) (.lit 3) (.prim .char)) (.list (.lit 3) (.lit 3) (.prim .char)) => true
    | _ => false),
  ("captured free identity is not an indexed slot", match capturedScheme.instantiate [.prim .char] with
    | .arrow (.fvar 0) (.prim .char) => true | _ => false),
  ("caller free identity survives insertion", match idScheme.instantiate [.fvar 0] with
    | .arrow (.fvar 0) (.fvar 0) => true | _ => false),
  ("captured counts remain lexical", match idScheme.instantiate
      [.list (.var ⟨.rigid, 7⟩) .inf (.prim .char)] with
    | .arrow (.list (.var ⟨.rigid, 7⟩) .inf _) (.list (.var ⟨.rigid, 7⟩) .inf _) => true
    | _ => false)]

def main : IO Unit := do
  for (name, ok) in cases do
    IO.println s!"{if ok then "PASS" else "FAIL"}: {name}"
    unless ok do throw (IO.userError s!"scheme bounds typing regression: {name}")

#eval main
#print axioms independentUses

end FHM.Bounds.SchemeTypingTests
