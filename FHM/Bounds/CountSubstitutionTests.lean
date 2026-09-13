import FHM.Bounds.CountSubstitution

namespace FHM.Bounds.CountSubstitutionTests

open CountSubstitution

private def n : Count := .var ⟨.rigid, 7⟩
private def captured : Count := .var ⟨.rigid, 99⟩
private def condition : Constraint := ⟨n, captured⟩
private def rows : Bindings := [(7, .lit 3)]

private theorem finite : Finite rows := by
  intro row hr
  simp only [rows, List.mem_singleton] at hr
  subst row
  exact .lit

private theorem original : SemanticSub [condition]
    (.list n n (.prim .int)) (.list (.lit 0) captured (.prim .int)) := by
  apply SemanticSub.list
  · apply Interval.subGoals_valid_iff.mpr
    intro σ hp
    constructor
    · simp [n, Count.eval, ExtNat.le]
    · exact hp condition (by simp)
  · exact .prim

-- The captured variable retains its identity; the quantified variable and its
-- premise are instantiated together.
example : SemanticSub [⟨.lit 3, captured⟩]
    (.list (.lit 3) (.lit 3) (.prim .int))
    (.list (.lit 0) captured (.prim .int)) := by
  simpa [rows, condition, n, captured, bounds, count, constraint, lookup] using
    subtype rows finite original

example : count rows captured = captured := captured_count (by rfl)

-- Substitution is simultaneous, not recursively reapplied to its arguments.
example : count [(7, .pred n)] n = .pred n := by rfl

-- Keeping the old premise while changing its goal is not sound in general.
example : ¬ (⟨[⟨n, .lit 0⟩], [⟨.lit 1, .lit 0⟩]⟩ : ForallProblem).Valid := by
  intro h
  have bad := h (fun _ => 0)
    (by simp [n, Constraint.Holds, Count.eval, ExtNat.le])
    ⟨.lit 1, .lit 0⟩ (by simp)
  simp [Constraint.Holds, Count.eval, ExtNat.le] at bad

private def cases : List (String × Bool) := [
  ("selected count replaced, capture unchanged", (bounds rows
      (.arrow (.list n n (.prim .int)) (.list n captured (.prim .int)))).pretty ==
        "BL 3 3 Int → BL 3 n99 Int"),
  ("captured assignment unchanged", assignment rows (fun i => i.idx) ⟨.rigid, 99⟩ == 99),
  ("replacement assignment uses argument value", assignment rows (fun _ => 20) ⟨.rigid, 7⟩ == 3),
  ("inferable namespace untouched", count rows (.var ⟨.inferable, 7⟩) == .var ⟨.inferable, 7⟩)]

def main : IO Unit := do
  for (name, ok) in cases do
    IO.println s!"{if ok then "PASS" else "FAIL"}: {name}"
    unless ok do throw (IO.userError s!"count substitution regression: {name}")

#eval main

end FHM.Bounds.CountSubstitutionTests
