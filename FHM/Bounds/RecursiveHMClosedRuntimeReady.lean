import FHM.Bounds.RecursiveHMPointwiseClosedExport

/-! # Runtime readiness of top-level closed generalized groups

The use-indexed internal fixed point and the exported-closure tying theorem
compose here into the abstract witness consumed by the body fundamental
theorem.  This module contains packaging only; member semantics remain in the
two preceding closure modules.
-/

namespace FHM.Bounds.RecursiveHMClosedExit

open RecursiveHMJudgement SchemeSpecialization CountSubstitution ScopedScheme
open RecursiveHMUniform

/-- Specialize a root group's captured introduction world through one outer
    static world.  The lexical tail is empty, so the pointwise and homogeneous
    internal environments coincide without reconstructing a target group. -/
private def GeneralizedGroup.closedRuntimeReadyTopPointwise
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
    (ambientSupported : ∀ i, Runtime.Supported (ambient i))
    (world : EnvSpecialization [])
    (bound free : Runtime.TypeEnv) (sigma : Assign)
    (hb : Runtime.TypeEnv.Downward bound) (hf : Runtime.TypeEnv.Downward free)
    (budget : Nat) (enclosing : EnvAt bound free sigma budget []) :
    { e : EnvAt bound free sigma budget
        (group.closedExports (CountAlgebra.compose world.outer outer)
          (fun i => mapFree world.types (bounds world.outer (ambient i))) ++ []) //
      e.terms = Runtime.recursiveTerms group.annotations
        (closeOuterRhss group.rhss enclosing.terms) ++ enclosing.terms } := by
  let composedRows := CountAlgebra.compose world.outer outer
  let composedAmbient := fun i => mapFree world.types (bounds world.outer (ambient i))
  let composedTarget := (target ++ world.countTarget) ++ world.typeTarget
  have composedFinite : Finite composedRows :=
    CountAlgebra.finite_compose world.outerFinite outerFinite
  have composedRowsScope : ∀ row ∈ composedRows,
      Scope.CountScoped composedTarget row.2 := by
    intro row member
    exact HMInterpretation.count_mono
      (composedRowsScopedAt outerScope world.outerScope row member)
      (fun _ h => List.mem_append_left _ h)
  have composedLC : ∀ i, (Synth.BoundsTy.toTy (composedAmbient i)).IsLC :=
    composedTypesLCAt ambientLC world.typesLC
  have composedScope : ∀ i, BoundsScoped composedTarget (composedAmbient i) :=
    composedTypesScopedAt ambientScope world.outerScope world.typesScope
  have composedSupported : ∀ i, Runtime.Supported (composedAmbient i) := by
    intro i
    exact Runtime.Supported.types world.types world.typesSupported
      (Runtime.Supported.counts world.outer (ambientSupported i))
  have enclosingTerms : enclosing.terms = [] := by
    apply List.eq_nil_of_length_eq_zero
    simpa using enclosing.arity
  let internal := closedInternalRealizerTop group composedRows composedFinite composedTarget
    composedRowsScope composedAmbient composedLC composedScope sourceReady
    sourceDemandSupported composedSupported bound free sigma hb hf
  have internal' : ClosedInternalRealizer group composedRows composedTarget composedAmbient
      bound free sigma enclosing.terms := by
    rw [enclosingTerms]
    exact internal
  have realized := GeneralizedGroup.closedExportEnvironmentCaptured group composedRows
    composedFinite composedTarget composedRowsScope composedAmbient composedLC composedScope
    (by intro scheme member; simp at member) sourceReady sourceDemandSupported
    composedSupported bound free sigma hb hf (tail := []) rfl enclosing internal'
  simpa only [composedRows, composedAmbient] using realized

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
  ordinaryPointwise world bound free sigma hb hf budget enclosing := by
    let empty : EnvAt bound free sigma budget [] := by
      simpa only [closeRecursiveEnv, List.map_nil, ordinaryBodyEnv] using enclosing
    have realized := GeneralizedGroup.closedRuntimeReadyTopPointwise group outer outerFinite
      target outerScope ambient ambientLC ambientScope sourceReady sourceDemandSupported
      ambientSupported world bound free sigma hb hf budget empty
    simpa only [closeRecursiveEnv, List.map_nil, ordinaryBodyEnv, empty] using
      realized
  fixed bound free sigma hb hf budget enclosing := by
    have enclosingTerms : enclosing.terms = [] := by
      apply List.eq_nil_of_length_eq_zero
      simpa only [fixedBodyEnv] using enclosing.arity
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
    simpa only [fixedBodyEnv, List.append_nil] using realized
  fixedPointwise world bound free sigma hb hf budget enclosing := by
    let empty : EnvAt bound free sigma budget [] := by
      simpa only [closeRecursiveEnv, List.map_nil, fixedBodyEnv] using enclosing
    have realized := GeneralizedGroup.closedRuntimeReadyTopPointwise group outer outerFinite
      target outerScope ambient ambientLC ambientScope sourceReady sourceDemandSupported
      ambientSupported world bound free sigma hb hf budget empty
    simpa only [closeRecursiveEnv, List.map_nil, fixedBodyEnv, empty] using
      realized
  specializable bound free sigma hb hf budget enclosing := by
    let extended := GeneralizedGroup.extendSpecializableEnvAt group outer outerFinite target outerScope
      ambient ambientLC ambientScope (by intro scheme member; simp at member)
      sourceReady sourceDemandSupported ambientSupported
      (by intro beta member; simp at member)
      (by intro beta member; simp at member)
      bound free sigma hb hf budget enclosing
    refine ⟨extended, ?_⟩
    exact GeneralizedGroup.extendSpecializableEnvAt_fixed_terms group outer outerFinite target
      outerScope ambient ambientLC ambientScope (by intro scheme member; simp at member)
      sourceReady sourceDemandSupported ambientSupported
      (by intro beta member; simp at member)
      (by intro beta member; simp at member)
      bound free sigma hb hf budget enclosing

#print axioms GeneralizedGroup.closedRuntimeReadyTop

end FHM.Bounds.RecursiveHMClosedExit
