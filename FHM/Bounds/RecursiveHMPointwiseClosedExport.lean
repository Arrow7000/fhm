import FHM.Bounds.RecursiveHMNestedInternalRealizer
import FHM.Bounds.RecursiveHMClosedSpecializableEnvironment

/-! # Pointwise nested closed-export realization

The all-budget closed-exit realizer is useful for a finished Kripke family,
but too strong inside the pointwise fundamental induction.  This module keeps
the same semantic tie while requiring the recursive environment only at the
single predecessor observation used by `letRec` unfolding.
-/

namespace FHM.Bounds.RecursiveHMClosedExit

open RecursiveHMJudgement SchemeSpecialization CountSubstitution ScopedScheme
open RecursiveHMUniform

theorem composedRowsScopedAt
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

theorem composedTypesLCAt
    {rows : Bindings} {types worldTypes : Nat → BoundsTy}
    (typesLC : ∀ i, (Synth.BoundsTy.toTy (types i)).IsLC)
    (worldLC : ∀ i, (Synth.BoundsTy.toTy (worldTypes i)).IsLC) :
    ∀ i, (Synth.BoundsTy.toTy
      (mapFree worldTypes (bounds rows (types i)))).IsLC := by
  intro i
  apply FreeAlgebra.bvars worldTypes worldLC
  simpa only [CountSubstitution.bounds_shape] using typesLC i

theorem composedTypesScopedAt
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

/-- The use-indexed internal recursive environment at one observation budget. -/
structure GeneralizedGroup.ClosedInternalRealizerAt
    {output metadata path captures premises bodyTypes outerEnv}
    (group : GeneralizedGroup output metadata path captures premises bodyTypes outerEnv)
    (outer : Bindings) (target : List Nat) (ambient : Nat → BoundsTy)
    (bound free : Runtime.TypeEnv) (sigma : Assign) (budget : Nat)
    (outerTerms : List Expr) where
  realize : ∀ offset (inside : offset < group.exports.length)
    {calleeDelta found caller}
    (used : HMCountScheme.Use
      (HMCountSchemeClosure.close
        (group.selected offset inside).rhs.certificate.interface.scheme)
      calleeDelta found caller),
    HMCountSchemeClosure.CapturesAgree
      (group.selected offset inside).rhs.certificate.interface.scheme
      outer ambient used →
    (∀ a ∈ used.types, Runtime.Supported a) →
    { e : EnvAt bound free sigma budget
        (closeRecursiveEnv
          (group.protectedRows offset inside used outer)
          (group.protectedTypes offset inside used ambient)
          group.internal) //
      e.terms = Runtime.recursiveTerms group.annotations
        (closeOuterRhss group.rhss outerTerms) ++ outerTerms }

/-- Restrict one current-budget lexical witness to any smaller observation and
    realize the nested group's protected internal environment there. -/
def GeneralizedGroup.closedInternalRealizerNestedAt
    {output metadata path captures premises bodyTypes outerEnv}
    (group : GeneralizedGroup output metadata path captures premises bodyTypes outerEnv)
    (outer : Bindings) (outerFinite : Finite outer)
    (target : List Nat)
    (outerScope : ∀ row ∈ outer, Scope.CountScoped target row.2)
    (ambient : Nat → BoundsTy)
    (ambientLC : ∀ i, (Synth.BoundsTy.toTy (ambient i)).IsLC)
    (ambientScope : ∀ i, BoundsScoped target (ambient i))
    (normal : ClosureNormal outerEnv)
    (sourceReady : ∀ offset (inside : offset < group.exports.length),
      ScopedDerives.RuntimeReady
        (group.selected offset inside).rhs.certificate.implementation.typing)
    (sourceDemandSupported : ∀ offset (inside : offset < group.exports.length),
      Runtime.Supported
        (group.selected offset inside).rhs.certificate.implementation.opening.bounds)
    (ambientSupported : ∀ i, Runtime.Supported (ambient i))
    (ambientCounts : ∀ beta, .mono beta ∈ outerEnv → bounds outer beta = beta)
    (ambientTypes : ∀ beta, .mono beta ∈ outerEnv →
      ∀ i ∈ (Synth.BoundsTy.toTy beta).freeVars, ambient i = .fvar i)
    (bound free : Runtime.TypeEnv) (sigma : Assign)
    (hb : Runtime.TypeEnv.Downward bound) (hf : Runtime.TypeEnv.Downward free)
    {maximum : Nat}
    (lexical : SpecializableEnvAt bound free sigma maximum outerEnv)
    (budget : Nat) (within : budget ≤ maximum) :
    ClosedInternalRealizerAt group outer target ambient bound free sigma budget
      lexical.fixed.terms := by
  refine ⟨?_⟩
  intro offset inside calleeDelta found caller used capturesAgree arguments
  let rows := group.protectedRows offset inside used outer
  let types := group.protectedTypes offset inside used ambient
  let target' := (group.selected offset inside).rhs.certificate.interface.scheme.counts.captures ++
    caller ++ target
  have rowsFinite : Finite rows :=
    group.protectedRows_finite offset inside used outer outerFinite
  have rowsScoped : ∀ row ∈ rows, Scope.CountScoped target' row.2 :=
    group.protectedRows_scoped offset inside used outer target outerScope
  have typesLC : ∀ i, (Synth.BoundsTy.toTy (types i)).IsLC :=
    group.protectedTypes_lc offset inside used ambient ambientLC
  have typesScoped : ∀ i, BoundsScoped target' (types i) :=
    group.protectedTypes_scoped offset inside used ambient target ambientScope
  have typesSupported : ∀ i, Runtime.Supported (types i) :=
    group.protectedTypes_supported offset inside used ambient arguments ambientSupported
  let lexicalAt := lexical.down hb hf within
  let realized := closedInternalEnvironmentNested group sourceReady sourceDemandSupported
    normal bound free sigma hb hf rows rowsFinite target' rowsScoped types typesLC typesScoped
    typesSupported
    (group.protectedMonoCounts offset inside used outer ambientCounts)
    (group.protectedMonoTypes offset inside used ambient ambientTypes)
    budget lexicalAt
  refine ⟨realized.val, ?_⟩
  exact realized.property

/-- Tie a closed export environment at one budget.  Only the predecessor
    internal realization is needed at positive budgets. -/
def GeneralizedGroup.closedExportEnvironmentCapturedAt
    {output metadata path captures premises bodyTypes outerEnv}
    (group : GeneralizedGroup output metadata path captures premises bodyTypes outerEnv)
    (outer : Bindings) (outerFinite : Finite outer)
    (target : List Nat)
    (outerScope : ∀ row ∈ outer, Scope.CountScoped target row.2)
    (ambient : Nat → BoundsTy)
    (ambientLC : ∀ i, (Synth.BoundsTy.toTy (ambient i)).IsLC)
    (ambientScope : ∀ i, BoundsScoped target (ambient i))
    (normal : ClosureNormal outerEnv)
    (sourceReady : ∀ offset (inside : offset < group.exports.length),
      ScopedDerives.RuntimeReady
        (group.selected offset inside).rhs.certificate.implementation.typing)
    (sourceDemandSupported : ∀ offset (inside : offset < group.exports.length),
      Runtime.Supported
        (group.selected offset inside).rhs.certificate.implementation.opening.bounds)
    (ambientSupported : ∀ i, Runtime.Supported (ambient i))
    (bound free : Runtime.TypeEnv) (sigma : Assign)
    (hb : Runtime.TypeEnv.Downward bound) (hf : Runtime.TypeEnv.Downward free)
    {tail : List Binding} (tailLength : tail.length = outerEnv.length)
    (outerEnvAt : EnvAt bound free sigma budget tail)
    (internal : ClosedInternalRealizerAt group outer target ambient bound free sigma
      (budget - 1) outerEnvAt.terms) :
    { e : EnvAt bound free sigma budget (group.closedExports outer ambient ++ tail) //
      e.terms = Runtime.recursiveTerms group.annotations
        (closeOuterRhss group.rhss outerEnvAt.terms) ++ outerEnvAt.terms } := by
  let closedRhss := closeOuterRhss group.rhss outerEnvAt.terms
  let recursive := Runtime.recursiveTerms group.annotations closedRhss
  have closedScope : ∀ rhs ∈ closedRhss, rhs.varsBelow group.rhss.length = true := by
    apply closeOuterRhss_scoped outerEnvAt
    simpa only [outerEnvAt.arity, tailLength] using group.rhssScoped
  have recursiveClosed : ∀ term ∈ recursive, term.varsBelow 0 = true :=
    Runtime.recursiveTerms_closed (by
      simpa only [closedRhss, closeOuterRhss_length] using closedScope)
  refine ⟨{ terms := recursive ++ outerEnvAt.terms
            arity := ?_
            closed := ?_
            denotes := ?_ }, rfl⟩
  · simp only [List.length_append, recursive, Runtime.recursiveTerms, List.length_map,
      closedRhss, closeOuterRhss_length, group.exportCount, GeneralizedGroup.closedExports,
      List.length_map, outerEnvAt.arity]
  · intro term member
    exact (List.mem_append.mp member).elim (recursiveClosed term) (outerEnvAt.closed term)
  · intro i inside
    by_cases groupInside : i < group.exports.length
    · let selected := group.selected i groupInside
      have exportInside : i < (group.closedExports outer ambient).length := by
        simpa only [GeneralizedGroup.closedExports, List.length_map] using groupInside
      have rhsInside : i < group.rhss.length := by
        rw [← group.exportCount]
        exact groupInside
      have recursiveInside : i < recursive.length := by
        simpa only [recursive, Runtime.recursiveTerms, List.length_map,
          closedRhss, closeOuterRhss_length] using rhsInside
      have exported := List.getElem?_eq_some_iff.mp selected.selection
      have exportEntry : group.exports[i] =
          selected.rhs.certificate.interface.scheme := exported.choose_spec
      rw [List.getElem_append_left exportInside, List.getElem_append_left recursiveInside]
      simp only [GeneralizedGroup.closedExports, List.getElem_map, exportEntry, BindingAt]
      intro calleeDelta found caller used capturesAgree arguments rawPremises
      cases budget with
      | zero =>
          unfold Runtime.TermAt
          intro steps value _ before
          omega
      | succ smaller =>
          have internal' : ClosedInternalRealizerAt group outer target ambient bound free sigma
              smaller outerEnvAt.terms := by
            simpa only [Nat.succ_sub_one] using internal
          let realized := internal'.realize i groupInside used capturesAgree arguments
          have safe := GeneralizedGroup.runtimeExitTermAtRaw group i groupInside used outer
            outerFinite target outerScope ambient ambientLC ambientScope capturesAgree normal
            (sourceReady i groupInside) (sourceDemandSupported i groupInside) arguments
            ambientSupported bound free sigma hb hf smaller rawPremises
            realized.val
          have realizedTerms : realized.val.terms = recursive ++ outerEnvAt.terms := by
            simpa only [recursive, closedRhss] using realized.property
          rw [realizedTerms] at safe
          have sourceRhs := group.checked.memberAtRhs i groupInside
          have rhsLookup : group.rhss[i]? =
              some selected.member.declaration.node.inner.stripFound := by
            simpa only [GeneralizedGroup.rhss, List.getElem?_map, Option.map_some,
              Expr.stripFound] using congrArg (Option.map Expr.stripFound) sourceRhs
          have rhsEq : group.rhss[i] =
              selected.member.declaration.node.inner.stripFound :=
            (List.getElem?_eq_some_iff.mp rhsLookup).choose_spec
          have safe' : Runtime.TermAt bound free sigma smaller used.bounds
              ((group.rhss[i]'rhsInside).substN 0 (recursive ++ outerEnvAt.terms)) := by
            simpa only [rhsEq] using safe
          have composed := Runtime.closing_compose outerEnvAt.terms recursive outerEnvAt.closed
            recursiveClosed (group.rhss[i]'rhsInside) 0
          have recursiveLength : recursive.length = group.rhss.length := by
            simp only [recursive, Runtime.recursiveTerms, List.length_map,
              closedRhss, closeOuterRhss_length]
          rw [Nat.zero_add, recursiveLength] at composed
          rw [← composed] at safe'
          have closedInside : i < closedRhss.length := by
            rw [closeOuterRhss_length]
            exact rhsInside
          have recursiveEntry : recursive[i]'recursiveInside =
              .letRec group.annotations closedRhss (closedRhss[i]'closedInside) := by
            simp only [recursive, Runtime.recursiveTerms, List.getElem_map]
          have rhsEntry : closedRhss[i]'closedInside =
              (group.rhss[i]'rhsInside).substN group.rhss.length outerEnvAt.terms := by
            simp only [closedRhss, closeOuterRhss, List.getElem_map]
          rw [recursiveEntry, rhsEntry]
          exact Runtime.TermAt.prepend SmallStep.Step.letRecUnfold safe'
    · have tailInside : i - group.exports.length < tail.length := by
        simp only [List.length_append, GeneralizedGroup.closedExports, List.length_map] at inside
        omega
      have meaning := outerEnvAt.denotes (i - group.exports.length) tailInside
      have recursiveLength : recursive.length = group.exports.length := by
        simp only [recursive, Runtime.recursiveTerms, List.length_map,
          closedRhss, closeOuterRhss_length, ← group.exportCount]
      have exportPosition : group.exports.length ≤ i := by omega
      have exportBindingPosition : (group.closedExports outer ambient).length ≤ i := by
        simpa only [GeneralizedGroup.closedExports, List.length_map] using exportPosition
      have recursivePosition : recursive.length ≤ i := by
        rw [recursiveLength]
        exact exportPosition
      rw [List.getElem_append_right exportBindingPosition,
        List.getElem_append_right recursivePosition]
      simpa only [GeneralizedGroup.closedExports, List.length_map, recursiveLength] using meaning

/-- Fixed body view of a nested closed group at one observation budget. -/
def GeneralizedGroup.closedExportEnvironmentNestedFixedAt
    {output metadata path captures premises bodyTypes outerEnv}
    (group : GeneralizedGroup output metadata path captures premises bodyTypes outerEnv)
    (outer : Bindings) (outerFinite : Finite outer)
    (target : List Nat) (outerScope : ∀ row ∈ outer, Scope.CountScoped target row.2)
    (ambient : Nat → BoundsTy)
    (ambientLC : ∀ i, (Synth.BoundsTy.toTy (ambient i)).IsLC)
    (ambientScope : ∀ i, BoundsScoped target (ambient i))
    (normal : ClosureNormal outerEnv)
    (sourceReady : ∀ offset (inside : offset < group.exports.length),
      ScopedDerives.RuntimeReady
        (group.selected offset inside).rhs.certificate.implementation.typing)
    (sourceDemandSupported : ∀ offset (inside : offset < group.exports.length),
      Runtime.Supported
        (group.selected offset inside).rhs.certificate.implementation.opening.bounds)
    (ambientSupported : ∀ i, Runtime.Supported (ambient i))
    (ambientCounts : ∀ beta, .mono beta ∈ outerEnv → bounds outer beta = beta)
    (ambientTypes : ∀ beta, .mono beta ∈ outerEnv →
      ∀ i ∈ (Synth.BoundsTy.toTy beta).freeVars, ambient i = .fvar i)
    (bound free : Runtime.TypeEnv) (sigma : Assign)
    (hb : Runtime.TypeEnv.Downward bound) (hf : Runtime.TypeEnv.Downward free)
    (budget : Nat) (lexical : SpecializableEnvAt bound free sigma budget outerEnv) :
    { e : BodyEnvAt bound free sigma budget
        (group.closedExports outer ambient ++ fixedBodyEnv outerEnv) //
      e.terms = Runtime.recursiveTerms group.annotations
        (closeOuterRhss group.rhss lexical.fixed.terms) ++ lexical.fixed.terms } := by
  let internal := closedInternalRealizerNestedAt group outer outerFinite target outerScope
    ambient ambientLC ambientScope normal sourceReady sourceDemandSupported ambientSupported
    ambientCounts ambientTypes bound free sigma hb hf lexical (budget - 1) (Nat.sub_le budget 1)
  exact closedExportEnvironmentCapturedAt group outer outerFinite target outerScope ambient
    ambientLC ambientScope normal sourceReady sourceDemandSupported ambientSupported
    bound free sigma hb hf (tail := fixedBodyEnv outerEnv) (by simp [fixedBodyEnv])
    lexical.fixed internal

/-- Ordinary body view of the same nested group at one observation budget. -/
def GeneralizedGroup.closedExportEnvironmentNestedOrdinaryAt
    {output metadata path captures premises bodyTypes outerEnv}
    (group : GeneralizedGroup output metadata path captures premises bodyTypes outerEnv)
    (outer : Bindings) (outerFinite : Finite outer)
    (target : List Nat) (outerScope : ∀ row ∈ outer, Scope.CountScoped target row.2)
    (ambient : Nat → BoundsTy)
    (ambientLC : ∀ i, (Synth.BoundsTy.toTy (ambient i)).IsLC)
    (ambientScope : ∀ i, BoundsScoped target (ambient i))
    (normal : ClosureNormal outerEnv)
    (sourceReady : ∀ offset (inside : offset < group.exports.length),
      ScopedDerives.RuntimeReady
        (group.selected offset inside).rhs.certificate.implementation.typing)
    (sourceDemandSupported : ∀ offset (inside : offset < group.exports.length),
      Runtime.Supported
        (group.selected offset inside).rhs.certificate.implementation.opening.bounds)
    (ambientSupported : ∀ i, Runtime.Supported (ambient i))
    (ambientCounts : ∀ beta, .mono beta ∈ outerEnv → bounds outer beta = beta)
    (ambientTypes : ∀ beta, .mono beta ∈ outerEnv →
      ∀ i ∈ (Synth.BoundsTy.toTy beta).freeVars, ambient i = .fvar i)
    (bound free : Runtime.TypeEnv) (sigma : Assign)
    (hb : Runtime.TypeEnv.Downward bound) (hf : Runtime.TypeEnv.Downward free)
    (budget : Nat) (lexical : SpecializableEnvAt bound free sigma budget outerEnv) :
    { e : BodyEnvAt bound free sigma budget
        (group.closedExports outer ambient ++ ordinaryBodyEnv outerEnv) //
      e.terms = Runtime.recursiveTerms group.annotations
        (closeOuterRhss group.rhss lexical.fixed.terms) ++ lexical.fixed.terms } := by
  let internalFixed := closedInternalRealizerNestedAt group outer outerFinite target outerScope
    ambient ambientLC ambientScope normal sourceReady sourceDemandSupported ambientSupported
    ambientCounts ambientTypes bound free sigma hb hf lexical
    (budget - 1) (Nat.sub_le budget 1)
  have internal : ClosedInternalRealizerAt group outer target ambient bound free sigma
      (budget - 1) lexical.ordinary.terms := by
    rw [lexical.ordinaryTerms]
    exact internalFixed
  let realized := closedExportEnvironmentCapturedAt group outer outerFinite target outerScope
    ambient ambientLC ambientScope normal sourceReady sourceDemandSupported ambientSupported
    bound free sigma hb hf (tail := ordinaryBodyEnv outerEnv)
    (by simp [ordinaryBodyEnv]) lexical.ordinary internal
  simpa only [lexical.ordinaryTerms] using realized

/-- Extend one current-budget specializable lexical environment by a closed
    generalized group.  Unlike the family constructor, this is usable inside
    a pointwise semantic induction and only asks the lexical witness for the
    current observation budget. -/
def GeneralizedGroup.extendSpecializableEnvAt
    {output metadata path captures premises bodyTypes outerEnv}
    (group : GeneralizedGroup output metadata path captures premises bodyTypes outerEnv)
    (outer : Bindings) (outerFinite : Finite outer)
    (target : List Nat) (outerScope : ∀ row ∈ outer, Scope.CountScoped target row.2)
    (ambient : Nat → BoundsTy)
    (ambientLC : ∀ i, (Synth.BoundsTy.toTy (ambient i)).IsLC)
    (ambientScope : ∀ i, BoundsScoped target (ambient i))
    (normal : ClosureNormal outerEnv)
    (sourceReady : ∀ offset (inside : offset < group.exports.length),
      ScopedDerives.RuntimeReady
        (group.selected offset inside).rhs.certificate.implementation.typing)
    (sourceDemandSupported : ∀ offset (inside : offset < group.exports.length),
      Runtime.Supported
        (group.selected offset inside).rhs.certificate.implementation.opening.bounds)
    (ambientSupported : ∀ i, Runtime.Supported (ambient i))
    (ambientCounts : ∀ beta, .mono beta ∈ outerEnv → bounds outer beta = beta)
    (ambientTypes : ∀ beta, .mono beta ∈ outerEnv →
      ∀ i ∈ (Synth.BoundsTy.toTy beta).freeVars, ambient i = .fvar i)
    (bound free : Runtime.TypeEnv) (sigma : Assign)
    (hb : Runtime.TypeEnv.Downward bound) (hf : Runtime.TypeEnv.Downward free)
    (budget : Nat) (lexical : SpecializableEnvAt bound free sigma budget outerEnv) :
    SpecializableEnvAt bound free sigma budget
      (group.closedExports outer ambient ++ outerEnv) := by
  let fixedRaw := closedExportEnvironmentNestedFixedAt group outer outerFinite target
    outerScope ambient ambientLC ambientScope normal sourceReady sourceDemandSupported
    ambientSupported ambientCounts ambientTypes bound free sigma hb hf budget lexical
  let ordinaryRaw := closedExportEnvironmentNestedOrdinaryAt group outer outerFinite target
    outerScope ambient ambientLC ambientScope normal sourceReady sourceDemandSupported
    ambientSupported ambientCounts ambientTypes bound free sigma hb hf budget lexical
  let fixed : BodyEnvAt bound free sigma budget
      (fixedBodyEnv (group.closedExports outer ambient ++ outerEnv)) := by
    simpa only [fixedBodyEnv] using fixedRaw.val
  let ordinary : BodyEnvAt bound free sigma budget
      (ordinaryBodyEnv (group.closedExports outer ambient ++ outerEnv)) := by
    have closedOrdinary : ordinaryBodyEnv (group.closedExports outer ambient) =
        group.closedExports outer ambient := by
      unfold GeneralizedGroup.closedExports ordinaryBodyEnv
      induction group.exports with
      | nil => rfl
      | cons scheme rest ih =>
          simp only [List.map_cons]
          exact congrArg (List.cons _) ih
    have envEq : ordinaryBodyEnv (group.closedExports outer ambient ++ outerEnv) =
        group.closedExports outer ambient ++ ordinaryBodyEnv outerEnv := by
      rw [ordinaryBodyEnv, List.map_append]
      change ordinaryBodyEnv (group.closedExports outer ambient) ++ ordinaryBodyEnv outerEnv = _
      rw [closedOrdinary]
    exact EnvAt.castEnv envEq.symm ordinaryRaw.val
  refine
    { fixed := fixed
      ordinary := ordinary
      ordinaryTerms := ?_
      specialized := ?_
      specializedTerms := ?_ }
  · rw [EnvAt.castEnv_terms]
    exact ordinaryRaw.property.trans fixedRaw.property.symm
  · intro world
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
        monoCounts := fun beta member =>
          world.monoCounts beta (List.mem_append_right _ member)
        monoTypes := fun beta member =>
          world.monoTypes beta (List.mem_append_right _ member) }
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
    have composedCounts : ∀ beta, .mono beta ∈ outerEnv →
        bounds composedRows beta = beta := by
      intro beta member
      rw [CountAlgebra.bounds_compose, ambientCounts beta member]
      exact world.monoCounts beta (List.mem_append_right _ member)
    have composedTypes : ∀ beta, .mono beta ∈ outerEnv →
        ∀ i ∈ (Synth.BoundsTy.toTy beta).freeVars, composedAmbient i = .fvar i := by
      intro beta member i freeIn
      simp only [composedAmbient, ambientTypes beta member i freeIn, bounds, mapFree]
      exact world.monoTypes beta (List.mem_append_right _ member) i freeIn
    let internalFixed := closedInternalRealizerNestedAt group composedRows composedFinite
      composedTarget composedRowsScope composedAmbient composedLC composedScope normal
      sourceReady sourceDemandSupported composedSupported composedCounts composedTypes
      bound free sigma hb hf lexical (budget - 1) (Nat.sub_le budget 1)
    let tail := lexical.specialized lexicalWorld
    have tailTerms : tail.terms = lexical.fixed.terms := lexical.specializedTerms lexicalWorld
    have internal : ClosedInternalRealizerAt group composedRows composedTarget composedAmbient
        bound free sigma (budget - 1) tail.terms := by
      rw [tailTerms]
      exact internalFixed
    let realized := closedExportEnvironmentCapturedAt group composedRows composedFinite
      composedTarget composedRowsScope composedAmbient composedLC composedScope normal
      sourceReady sourceDemandSupported composedSupported bound free sigma hb hf
      (tail := closeRecursiveEnv world.outer world.types outerEnv)
      (by simp only [closeRecursiveEnv, List.length_map]) tail internal
    have envEq :
        group.closedExports composedRows composedAmbient ++
            closeRecursiveEnv world.outer world.types outerEnv =
          closeRecursiveEnv world.outer world.types
            (group.closedExports outer ambient ++ outerEnv) := by
      calc
        _ = closeRecursiveEnv world.outer world.types
              (group.closedExports outer ambient) ++
            closeRecursiveEnv world.outer world.types outerEnv := by
          rw [GeneralizedGroup.closeRecursiveEnv_closedExports]
        _ = _ := by simp only [closeRecursiveEnv, List.map_append]
    exact EnvAt.castEnv envEq realized.val
  · intro world
    rw [EnvAt.castEnv_terms]
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
        monoCounts := fun beta member =>
          world.monoCounts beta (List.mem_append_right _ member)
        monoTypes := fun beta member =>
          world.monoTypes beta (List.mem_append_right _ member) }
    have tailTerms := lexical.specializedTerms lexicalWorld
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
    have composedCounts : ∀ beta, .mono beta ∈ outerEnv →
        bounds composedRows beta = beta := by
      intro beta member
      rw [CountAlgebra.bounds_compose, ambientCounts beta member]
      exact world.monoCounts beta (List.mem_append_right _ member)
    have composedTypes : ∀ beta, .mono beta ∈ outerEnv →
        ∀ i ∈ (Synth.BoundsTy.toTy beta).freeVars, composedAmbient i = .fvar i := by
      intro beta member i freeIn
      simp only [composedAmbient, ambientTypes beta member i freeIn, bounds, mapFree]
      exact world.monoTypes beta (List.mem_append_right _ member) i freeIn
    let internalFixed := closedInternalRealizerNestedAt group composedRows composedFinite
      composedTarget composedRowsScope composedAmbient composedLC composedScope normal
      sourceReady sourceDemandSupported composedSupported composedCounts composedTypes
      bound free sigma hb hf lexical (budget - 1) (Nat.sub_le budget 1)
    let tail := lexical.specialized lexicalWorld
    have internal : ClosedInternalRealizerAt group composedRows composedTarget composedAmbient
        bound free sigma (budget - 1) tail.terms := by
      rw [tailTerms]
      exact internalFixed
    let realized := closedExportEnvironmentCapturedAt group composedRows composedFinite
      composedTarget composedRowsScope composedAmbient composedLC composedScope normal
      sourceReady sourceDemandSupported composedSupported bound free sigma hb hf
      (tail := closeRecursiveEnv world.outer world.types outerEnv)
      (by simp only [closeRecursiveEnv, List.length_map]) tail internal
    change Runtime.recursiveTerms group.annotations
        (closeOuterRhss group.rhss (lexical.specialized lexicalWorld).terms) ++
          (lexical.specialized lexicalWorld).terms = fixed.terms
    rw [tailTerms]
    exact fixedRaw.property

end FHM.Bounds.RecursiveHMClosedExit
