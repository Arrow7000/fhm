import FHM.Bounds.Scheme

namespace FHM.Bounds.SchemeTests

private def n : Count := .var ⟨.rigid, 0⟩
private def sized : BoundsTy := .list n n (.prim .int)
private def identity : BScheme := ⟨1, .arrow sized sized⟩

private def cases : List (String × Bool) := [
  ("finite count instantiation", match identity.instantiateNat [.lit 2] with
    | .ok r => r.bounds.pretty == "BL 2 2 Int → BL 2 2 Int"
    | _ => false),
  ("symbolic finite count instantiation", match identity.instantiateNat
      [.add (.var ⟨.inferable, 7⟩) (.lit 1)] with
    | .ok _ => true
    | _ => false),
  ("infinite Nat argument rejected", match identity.instantiateNat [.inf] with
    | .error msg => msg == "bounds: Nat count argument must be finite"
    | _ => false),
  ("wrong count arity rejected", match identity.instantiateNat [] with
    | .error msg => msg == "bounds: count scheme ill-formed or wrong arity"
    | _ => false),
  ("out-of-scope binder rejected instead of zero-defaulted", match
      (⟨1, .list (.var ⟨.rigid, 1⟩) n (.prim .int)⟩ : BScheme).instantiateNat [.lit 2] with
    | .error _ => true
    | _ => false),
  ("unpacked inferable in scheme body rejected", match
      (⟨1, .list (.var ⟨.inferable, 0⟩) n (.prim .int)⟩ : BScheme).instantiateNat [.lit 2] with
    | .error _ => true
    | _ => false),
  ("literal infinity endpoint remains legal", match
      (⟨1, .list n .inf (.prim .int)⟩ : BScheme).instantiateNat [.lit 2] with
    | .ok r => r.bounds.pretty == "BL 2 ∞ Int"
    | _ => false)]

-- Structural substitution preserves arithmetic meaning, including predecessor.
example (σ : Assign) :
    (Count.pred (.lit 3)).eval σ =
      (Count.pred n).eval (countArgAssign [.lit 3] σ) := by
  apply Count.Subst.eval (Count.Subst.pred (Count.Subst.var (by rfl)))
  intro a ha
  simp only [List.mem_singleton] at ha
  subst a
  exact .lit

def main : IO Unit := do
  for (name, ok) in cases do
    IO.println s!"{if ok then "PASS" else "FAIL"}: {name}"
    unless ok do throw (IO.userError s!"count scheme regression: {name}")

#eval main

end FHM.Bounds.SchemeTests
