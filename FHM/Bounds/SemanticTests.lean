import FHM.Bounds.Semantic

/-! Solver-free regression proofs for the new specification. -/

namespace FHM.Bounds

private def exactTwo : BoundsTy := .list (.lit 2) (.lit 2) (.prim .int)
private def zeroToThree : BoundsTy := .list (.lit 0) (.lit 3) (.prim .int)

private theorem widening : SemanticSub [] exactTwo zeroToThree := by
  apply SemanticSub.list
  · simp [ForallProblem.Valid, Interval.subGoals, Constraint.Holds, Count.eval, ExtNat.le]
  · exact .prim

-- Domains are contravariant: accepting the wider interval is more general.
example : SemanticSub [] (.arrow zeroToThree (.prim .int))
    (.arrow exactTwo (.prim .int)) := .arrow widening .prim

-- Results are covariant.
example : SemanticSub [] (.arrow (.prim .int) exactTwo)
    (.arrow (.prim .int) zeroToThree) := .arrow .prim widening

-- Additional path assumptions need no new solver verdict.
example (Δ : List Constraint) : SemanticSub Δ exactTwo zeroToThree :=
  widening.strengthen (by simp)

-- Concrete containment follows from semantic inclusion.
example (σ : Assign) :
    (⟨.lit 0, .lit 3⟩ : Interval).Contains σ (.ofNat 2) := by
  apply Interval.Contains.of_subGoals
    (Δ := []) (a := ⟨.lit 2, .lit 2⟩)
  · exact (by cases widening with | list hv _ => exact hv)
  · simp
  · simp [Interval.Contains, Count.eval, ExtNat.le]

-- The reverse widening is invalid, not an alternative solver outcome.
example : ¬ SemanticSub [] zeroToThree exactTwo := by
  intro h
  cases h with
  | list hv _ =>
      simp [ForallProblem.Valid, Interval.subGoals, Constraint.Holds, Count.eval, ExtNat.le] at hv

end FHM.Bounds
