import EPL.Runtime

/-!
# Exhaustiveness

The check agrees with the relation, and exhaustiveness survives erasure and
evaluation, so progress can be applied after every step.
-/

namespace EPL

/-- The check decides the relation. -/
theorem Expr.exhaustive_iff {sig : Signature} {expr : Expr A} :
    expr.exhaustive sig = true ↔ Exhaustive sig expr := by
  sorry

instance (sig : Signature) (expr : Expr A) : Decidable (Exhaustive sig expr) :=
  decidable_of_iff _ Expr.exhaustive_iff

/-- Erasure keeps every match and its patterns. -/
theorem Exhaustive.erase {sig : Signature} {expr : Expr A} (exhaustive : Exhaustive sig expr) :
    Exhaustive sig expr.erase := by
  sorry

/-- Shifting keeps every match and its patterns. -/
theorem Exhaustive.shift {sig : Signature} {expr : Expr A} (exhaustive : Exhaustive sig expr)
    (cutoff amount : Nat) : Exhaustive sig (expr.shift cutoff amount) := by
  sorry

/-- Substituting an exhaustive value into an exhaustive term. -/
theorem Exhaustive.substAt {sig : Signature} {expr value : Expr A}
    (exhaustive : Exhaustive sig expr) (valueExhaustive : Exhaustive sig value) (depth : Nat) :
    Exhaustive sig (expr.substAt depth value) := by
  sorry

/-- Exhaustiveness survives a step. Proof: induction on the step;
`beta`/`letValue`/`fixUnfold` by `Exhaustive.substAt`; `matchCtor` because
the taken branch and the scrutinee's fields are exhaustive (`Expr.apps`
of exhaustive terms is exhaustive). -/
theorem Exhaustive.step {sig : Signature} {expr next : RuntimeExpr}
    (exhaustive : Exhaustive sig expr) (step : Eval.Step expr next) :
    Exhaustive sig next := by
  sorry

end EPL
