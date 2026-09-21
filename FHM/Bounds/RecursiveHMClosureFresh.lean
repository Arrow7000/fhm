import FHM.Bounds.RecursiveHMUniform

/-! # Freshness of closure-normal recursive environments

The combined recursive-closing boundary promotes raw recursive contracts to
`recursiveClosure` entries.  Generalized bindings crossing a lexical boundary
must already be represented by `closure`; a raw `exported` entry at that point
would still retain source count and type captures.
-/

namespace FHM.Bounds.RecursiveHMUniform

open RecursiveHMJudgement CountSubstitution

/-- An environment is closure-normal when it contains no legacy raw generalized
    export. Other bindings, including the raw contracts of the SCC currently
    being tied, are permitted. -/
def ClosureNormal (env : List Binding) : Prop :=
  ∀ s, .exported s ∉ env

/-- The internal environment of a generalized group is fresh for the combined
    recursive-closing boundary whenever its captured outer environment is
    closure-normal. The current SCC's raw recursive prefix is vacuous for
    `CloseRecursiveFresh`; closure-normality eliminates the only sensitive
    outer case. -/
theorem GeneralizedGroup.internalCloseRecursiveFresh
    {output metadata path captures premises bodyTypes outerEnv}
    (group : GeneralizedGroup output metadata path captures premises bodyTypes outerEnv)
    (outer : Bindings) (f : Nat → BoundsTy)
    (normal : ClosureNormal outerEnv) :
    CloseRecursiveFresh outer f group.internal := by
  intro binding member
  rcases List.mem_append.mp member with internal | external
  · rcases List.mem_map.mp internal with ⟨contract, _, rfl⟩
    trivial
  · cases binding with
    | mono _ => trivial
    | recursive _ => trivial
    | recursiveClosure _ => trivial
    | exported scheme => exact (normal scheme external).elim
    | closure _ _ _ => trivial

#print axioms GeneralizedGroup.internalCloseRecursiveFresh

end FHM.Bounds.RecursiveHMUniform
