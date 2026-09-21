import FHM.Bounds.RecursiveHMNestedInternalRealizer
import FHM.Bounds.RecursiveHMClosedSpecializableEnvironment

/-! # Extending specializable environments with a closed recursive group

This is the compositional Kripke step: a group whose lexical tail has one
stable runtime term vector contributes its tied recursive terms in front of
that same vector, in every lawful count/HM specialization world.
-/

namespace FHM.Bounds.RecursiveHMClosedExit

open RecursiveHMJudgement SchemeSpecialization CountSubstitution ScopedScheme
open RecursiveHMUniform

private theorem composedRowsScoped
    {rows worldRows : Bindings} {target worldTarget : List Nat}
    (rowsScope : ∀ row ∈ rows, Scope.CountScoped target row.2)
    (worldScope : ∀ row ∈ worldRows, Scope.CountScoped worldTarget row.2) :
    ∀ row ∈ CountAlgebra.compose worldRows rows,
      Scope.CountScoped (target ++ worldTarget) row.2 := by
  intro row member
  rcases List.mem_append.mp member with mapped | outer
  · obtain ⟨source, sourceMember, rfl⟩ := List.mem_map.mp mapped
    exact ScopedScheme.count_scoped (rowsScope source sourceMember)
      (fun entry entryMember =>
        HMInterpretation.count_mono (worldScope entry entryMember)
          (fun _ h => List.mem_append_right _ h))
      (fun i h _ => List.mem_append_left _ h)
  · exact HMInterpretation.count_mono (worldScope row outer)
      (fun _ h => List.mem_append_right _ h)

private theorem composedTypesLC
    {rows : Bindings} {types worldTypes : Nat → BoundsTy}
    (typesLC : ∀ i, (Synth.BoundsTy.toTy (types i)).IsLC)
    (worldLC : ∀ i, (Synth.BoundsTy.toTy (worldTypes i)).IsLC) :
    ∀ i, (Synth.BoundsTy.toTy
      (mapFree worldTypes (bounds rows (types i)))).IsLC := by
  intro i
  apply FreeAlgebra.bvars worldTypes worldLC
  simpa only [CountSubstitution.bounds_shape] using typesLC i

private theorem composedTypesScoped
    {rows : Bindings} {types worldTypes : Nat → BoundsTy}
    {target rowTarget typeTarget : List Nat}
    (typesScope : ∀ i, BoundsScoped target (types i))
    (rowsScope : ∀ row ∈ rows, Scope.CountScoped rowTarget row.2)
    (worldTypesScope : ∀ i, BoundsScoped typeTarget (worldTypes i)) :
    ∀ i, BoundsScoped ((target ++ rowTarget) ++ typeTarget)
      (mapFree worldTypes (bounds rows (types i))) := by
  intro i
  apply HMInterpretation.map_scope
  · exact ScopedScheme.bounds_scoped (typesScope i)
      (fun row member => HMInterpretation.count_mono (rowsScope row member)
        (fun _ h => List.mem_append_right _ h))
      (fun j h _ => List.mem_append_left _ h)
  · exact worldTypesScope

private theorem ordinaryBodyEnv_closedExports
    {output metadata path captures premises bodyTypes outerEnv}
    (group : GeneralizedGroup output metadata path captures premises bodyTypes outerEnv)
    (rows : Bindings) (types : Nat → BoundsTy) :
    ordinaryBodyEnv (group.closedExports rows types) = group.closedExports rows types := by
  unfold GeneralizedGroup.closedExports ordinaryBodyEnv
  induction group.exports with
  | nil => rfl
  | cons scheme rest ih =>
      simp only [List.map_cons]
      exact congrArg (List.cons _) ih

/-- Prefix a specializable lexical family by one closed generalized group.
    The result remains indexed by the exact same runtime syntax in every
    lawful world; no stability claim is made for worlds that the input family
    itself cannot realize. -/
def GeneralizedGroup.extendSpecializableEnvFamily
    {output metadata path captures premises bodyTypes outerEnv}
    (group : GeneralizedGroup output metadata path captures premises bodyTypes outerEnv)
    (rows : Bindings) (rowsFinite : Finite rows)
    (target : List Nat)
    (rowsScope : ∀ row ∈ rows, Scope.CountScoped target row.2)
    (types : Nat → BoundsTy)
    (typesLC : ∀ i, (Synth.BoundsTy.toTy (types i)).IsLC)
    (typesScope : ∀ i, BoundsScoped target (types i))
    (normal : ClosureNormal outerEnv)
    (sourceReady : ∀ offset (inside : offset < group.exports.length),
      ScopedDerives.RuntimeReady
        (group.selected offset inside).rhs.certificate.implementation.typing)
    (sourceDemandSupported : ∀ offset (inside : offset < group.exports.length),
      Runtime.Supported
        (group.selected offset inside).rhs.certificate.implementation.opening.bounds)
    (typesSupported : ∀ i, Runtime.Supported (types i))
    (rowsCounts : ∀ β, .mono β ∈ outerEnv → bounds rows β = β)
    (typesStable : ∀ β, .mono β ∈ outerEnv →
      ∀ i ∈ (Synth.BoundsTy.toTy β).freeVars, types i = .fvar i)
    (bound free : Runtime.TypeEnv) (sigma : Assign)
    (hb : Runtime.TypeEnv.Downward bound) (hf : Runtime.TypeEnv.Downward free)
    (lexical : SpecializableEnvFamily bound free sigma outerEnv) :
    SpecializableEnvFamily bound free sigma
      (group.closedExports rows types ++ outerEnv) := by
  let terms := Runtime.recursiveTerms group.annotations
    (closeOuterRhss group.rhss lexical.terms) ++ lexical.terms
  refine
    { terms := terms
      world := ?_
      worldTerms := ?_ }
  · intro budget
    let fixedRaw := closedExportEnvironmentNestedFixed group rows rowsFinite target rowsScope
      types typesLC typesScope normal sourceReady sourceDemandSupported typesSupported rowsCounts typesStable
      bound free sigma hb hf lexical budget
    let ordinaryRaw := closedExportEnvironmentNestedOrdinary group rows rowsFinite target rowsScope
      types typesLC typesScope normal sourceReady sourceDemandSupported typesSupported rowsCounts typesStable
      bound free sigma hb hf lexical budget
    let fixed : BodyEnvAt bound free sigma budget
        (fixedBodyEnv (group.closedExports rows types ++ outerEnv)) := by
      simpa only [fixedBodyEnv] using fixedRaw.val
    let ordinary : BodyEnvAt bound free sigma budget
        (ordinaryBodyEnv (group.closedExports rows types ++ outerEnv)) := by
      have envEq : ordinaryBodyEnv (group.closedExports rows types ++ outerEnv) =
          group.closedExports rows types ++ ordinaryBodyEnv outerEnv := by
        rw [ordinaryBodyEnv, List.map_append]
        change ordinaryBodyEnv (group.closedExports rows types) ++ ordinaryBodyEnv outerEnv = _
        rw [ordinaryBodyEnv_closedExports]
      exact EnvAt.castEnv envEq.symm ordinaryRaw.val
    let specialize (world : StableEnvSpecialization
        (group.closedExports rows types ++ outerEnv)) :
        { e : EnvAt bound free sigma budget
            (closeRecursiveEnv world.outer world.types
              (group.closedExports rows types ++ outerEnv)) //
          e.terms = terms } := by
      let lexicalWorld : StableEnvSpecialization outerEnv :=
        { outer := world.outer
          types := world.types
          outerFinite := world.outerFinite
          countTarget := world.countTarget
          outerScope := world.outerScope
          typesLC := world.typesLC
          typeTarget := world.typeTarget
          typesScope := world.typesScope
          fresh := CloseRecursiveFresh.right world.fresh
          typesSupported := world.typesSupported
          monoCounts := fun β h => world.monoCounts β (List.mem_append_right _ h)
          monoTypes := fun β h => world.monoTypes β (List.mem_append_right _ h) }
      let composedRows := CountAlgebra.compose world.outer rows
      let composedTypes := fun i => mapFree world.types (bounds world.outer (types i))
      let composedTarget := (target ++ world.countTarget) ++ world.typeTarget
      have composedFinite : Finite composedRows :=
        CountAlgebra.finite_compose world.outerFinite rowsFinite
      have composedRowsScope : ∀ row ∈ composedRows,
          Scope.CountScoped composedTarget row.2 := by
        intro row member
        exact HMInterpretation.count_mono
          (composedRowsScoped rowsScope world.outerScope row member)
          (fun _ h => List.mem_append_left _ h)
      have composedLC : ∀ i, (Synth.BoundsTy.toTy (composedTypes i)).IsLC :=
        composedTypesLC typesLC world.typesLC
      have composedScope : ∀ i, BoundsScoped composedTarget (composedTypes i) :=
        composedTypesScoped typesScope world.outerScope world.typesScope
      have composedSupported : ∀ i, Runtime.Supported (composedTypes i) := by
        intro i
        exact Runtime.Supported.types world.types world.typesSupported
          (Runtime.Supported.counts world.outer (typesSupported i))
      have composedCounts : ∀ β, .mono β ∈ outerEnv → bounds composedRows β = β := by
        intro β member
        rw [CountAlgebra.bounds_compose, rowsCounts β member]
        exact world.monoCounts β (List.mem_append_right _ member)
      have composedStable : ∀ β, .mono β ∈ outerEnv →
          ∀ i ∈ (Synth.BoundsTy.toTy β).freeVars, composedTypes i = .fvar i := by
        intro β member i free
        simp only [composedTypes, typesStable β member i free, CountSubstitution.bounds, mapFree]
        exact world.monoTypes β (List.mem_append_right _ member) i free
      let internal := closedInternalRealizerNested group composedRows composedFinite
        composedTarget composedRowsScope composedTypes composedLC composedScope normal
        sourceReady sourceDemandSupported composedSupported composedCounts composedStable bound free sigma hb hf lexical
      let tail := (lexical.world budget).specialized lexicalWorld
      have tailTerms : tail.terms = lexical.terms :=
        ((lexical.world budget).specializedTerms lexicalWorld).trans
          (lexical.worldTerms budget)
      have internalTail : ClosedInternalRealizer group composedRows composedTarget
          composedTypes bound free sigma tail.terms := by
        rw [tailTerms]
        exact internal
      let realized := closedExportEnvironmentCaptured group composedRows composedFinite
        composedTarget composedRowsScope composedTypes composedLC composedScope normal
        sourceReady sourceDemandSupported composedSupported bound free sigma hb hf
        (tail := closeRecursiveEnv world.outer world.types outerEnv)
        (by simp only [closeRecursiveEnv, List.length_map]) tail internalTail
      have envEq :
          group.closedExports composedRows composedTypes ++
              closeRecursiveEnv world.outer world.types outerEnv =
            closeRecursiveEnv world.outer world.types
              (group.closedExports rows types ++ outerEnv) := by
        calc
          _ = closeRecursiveEnv world.outer world.types
                (group.closedExports rows types) ++
              closeRecursiveEnv world.outer world.types outerEnv := by
            rw [GeneralizedGroup.closeRecursiveEnv_closedExports]
          _ = _ := by simp only [closeRecursiveEnv, List.map_append]
      refine ⟨EnvAt.castEnv envEq realized.val, ?_⟩
      rw [EnvAt.castEnv_terms]
      simpa only [terms, tailTerms] using realized.property
    refine
      { fixed := fixed
        ordinary := ordinary
        ordinaryTerms := ?_
        specialized := ?_
        specializedTerms := ?_ }
    · rw [EnvAt.castEnv_terms]
      exact ordinaryRaw.property.trans fixedRaw.property.symm
    · exact fun world => (specialize world).val
    · intro world
      exact (specialize world).property.trans fixedRaw.property.symm
  · intro budget
    exact (closedExportEnvironmentNestedFixed group rows rowsFinite target rowsScope
      types typesLC typesScope normal sourceReady sourceDemandSupported typesSupported rowsCounts typesStable
      bound free sigma hb hf lexical budget).property

end FHM.Bounds.RecursiveHMClosedExit
