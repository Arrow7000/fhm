import FHM.Bounds.RecursiveHMSpecializableEnvironment

/-! # Closed generalized groups in specializable environments

This module records the specialization algebra needed to extend a Kripke
runtime environment with the lexical closures exported by a generalized
recursive group.  The recursive fixed-point construction itself lives in the
nested internal-realizer module; the facts here only reconcile its worlds with
the environment expected by `SpecializableEnvAt`.
-/

namespace FHM.Bounds.RecursiveHMUniform

open RecursiveHMJudgement SchemeSpecialization CountSubstitution

/-- Closing an already-closed export environment composes its stored lexical
    count/HM interpretations with the new specialization world. -/
theorem GeneralizedGroup.closeRecursiveEnv_closedExports
    {output metadata path captures premises bodyTypes outerEnv}
    (group : GeneralizedGroup output metadata path captures premises bodyTypes outerEnv)
    (rows : Bindings) (types : Nat → BoundsTy)
    (worldRows : Bindings) (worldTypes : Nat → BoundsTy) :
    closeRecursiveEnv worldRows worldTypes (group.closedExports rows types) =
      group.closedExports (CountAlgebra.compose worldRows rows)
        (fun i => mapFree worldTypes (bounds worldRows (types i))) := by
  unfold closeRecursiveEnv GeneralizedGroup.closedExports
  simp only [List.map_map, Function.comp_def, closeRecursiveBinding]
  apply List.map_congr_left
  intro scheme _
  rw [HMCountSchemeClosure.interpretedCountCaptures_compose,
    HMCountSchemeClosure.interpretedTypeCaptures_map]
  simp only [List.map_map, Function.comp_def]

#print axioms GeneralizedGroup.closeRecursiveEnv_closedExports

end FHM.Bounds.RecursiveHMUniform
