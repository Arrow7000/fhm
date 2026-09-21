import FHM.Bounds.RecursiveHMClosedInternalRealizer

/-! # Runtime readiness of top-level closed generalized groups

The use-indexed internal fixed point and the exported-closure tying theorem
compose here into the abstract witness consumed by the body fundamental
theorem.  This module contains packaging only; member semantics remain in the
two preceding closure modules.
-/

namespace FHM.Bounds.RecursiveHMClosedExit

open RecursiveHMJudgement CountSubstitution ScopedScheme
open RecursiveHMUniform

/-- Runtime readiness for a top-level generalized group whose body sees
    lexical closures.  The empty lexical tail is uniquely realized by the
    empty term list; all recursive behavior is supplied by
    `closedInternalRealizerTop`. -/
def GeneralizedGroup.closedRuntimeReadyTop
    {output metadata path captures premises bodyTypes}
    (group : GeneralizedGroup output metadata path captures premises bodyTypes [])
    (outer : Bindings) (outerFinite : Finite outer)
    (target : List Nat)
    (outerScope : ∀ row ∈ outer, Scope.CountScoped target row.2)
    (ambient : Nat → BoundsTy)
    (ambientLC : ∀ i, (Synth.BoundsTy.toTy (ambient i)).IsLC)
    (ambientScope : ∀ i, BoundsScoped target (ambient i))
    (sourceReady : ∀ offset (inside : offset < group.exports.length),
      ScopedDerives.RuntimeReady
        (group.selected offset inside).rhs.certificate.implementation.typing)
    (sourceDemandSupported : ∀ offset (inside : offset < group.exports.length),
      Runtime.Supported
        (group.selected offset inside).rhs.certificate.implementation.opening.bounds)
    (ambientSupported : ∀ i, Runtime.Supported (ambient i)) :
    group.ClosedRuntimeReady outer ambient where
  ordinary bound free sigma hb hf budget enclosing := by
    have enclosingTerms : enclosing.terms = [] := by
      apply List.eq_nil_of_length_eq_zero
      simpa only [ordinaryBodyEnv, List.map_nil] using enclosing.arity
    let internal := closedInternalRealizerTop group outer outerFinite target outerScope
      ambient ambientLC ambientScope sourceReady sourceDemandSupported ambientSupported
      bound free sigma hb hf
    have internal' : ClosedInternalRealizer group outer target ambient bound free sigma
        enclosing.terms := by
      rw [enclosingTerms]
      exact internal
    have realized := GeneralizedGroup.closedExportEnvironmentCaptured group outer outerFinite target outerScope
      ambient ambientLC ambientScope (by intro scheme member; simp at member)
      sourceReady sourceDemandSupported ambientSupported bound free sigma hb hf
      (tail := []) rfl enclosing internal'
    simpa only [ordinaryBodyEnv, List.map_nil, List.append_nil] using realized

#print axioms GeneralizedGroup.closedRuntimeReadyTop

end FHM.Bounds.RecursiveHMClosedExit
