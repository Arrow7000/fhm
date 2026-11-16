import EPL2.Spec.Models

/-!
# Unification computes most general unifiers

The models of `MStore.unify`'s result are exactly the models of its input
that equate the two types (`unify_sound`, `unify_complete`). The remaining
theorems are the invariants inference needs.

**Proof guidance.** Port `EPL/Properties/Unification.lean`, which proves all
of these for the previous representation of the same algorithm (there
`Ty.mvar`, `MVarBounded`, a deduplicated `Ty.mvars`, `occursMVar`, `scopedB`,
separate `Leveled`/`Bounded`/`Normalized`; here `Ty.var`, `Ty.Allocated`,
plain `Ty.vars`, `vars.contains`, `decide (ty.WF _)`, one `MStore.Safe`).
`unify_anchored` ports from `MStore.solve_anchored_of_canBind` and its
neighbours in `EPL/Properties/InferenceSound.lean`. Prove each property for
`MStore.solve` first, then for one `unifyPhase`, then for `unifyLoop` by
induction on the fuel.
-/

namespace EPL2

/-- The phase fuel `Constraints.size` is enough. -/
theorem unifyPhase_ne_outOfFuel {store : MStore} {constraints : List Constraint}
    (enough : Constraints.size constraints ≤ fuel) :
    unifyPhase store fuel constraints ≠ .outOfFuel := by
  sorry

/-- Each binding phase solves one more metavariable, so `unsolved + 1` phases
are enough. -/
theorem unifyPhase_bound_unsolved_lt {store result : MStore}
    {constraints rest : List Constraint}
    (run : unifyPhase store fuel constraints = .bound result rest) :
    result.unsolved < store.unsolved := by
  sorry

theorem MStore.unify_length {store result : MStore} {left right : InfTy}
    (run : store.unify left right = some result) : result.length = store.length := by
  sorry

theorem MStore.unify_safe {store result : MStore} {left right : InfTy} (safe : store.Safe)
    (leftAllocated : left.Allocated store) (rightAllocated : right.Allocated store)
    (run : store.unify left right = some result) : result.Safe := by
  sorry

/-- Levels only decrease. -/
theorem MStore.unify_levelOf_le {store result : MStore} {left right : InfTy}
    (run : store.unify left right = some result) (id : Nat) :
    result.levelOf id ≤ store.levelOf id := by
  sorry

/-- Every model of the result is a model of the input that unifies the two
types. -/
theorem MStore.unify_sound {store result : MStore} {left right : InfTy} {valuation : Valuation}
    (run : store.unify left right = some result) (models : result.Models valuation) :
    store.Models valuation ∧ left.realize valuation = right.realize valuation := by
  sorry

/-- Every model of the input that unifies the two types is a model of the
result (in particular, unification succeeds). -/
theorem MStore.unify_complete {store : MStore} {left right : InfTy} {valuation : Valuation}
    (safe : store.Safe) (leftAllocated : left.Allocated store)
    (rightAllocated : right.Allocated store) (models : store.Models valuation)
    (unifies : left.realize valuation = right.realize valuation) :
    ∃ result, store.unify left right = some result ∧ result.Models valuation := by
  sorry

/-- A metavariable lowered to `level` or below by a binding enters the
solution of whatever it was unified with, which is anchored. -/
theorem MStore.unify_anchored {store result : MStore} {left right : InfTy} (safe : store.Safe)
    (anchored : store.Anchored start level) (run : store.unify left right = some result) :
    result.Anchored start level := by
  sorry

end EPL2
