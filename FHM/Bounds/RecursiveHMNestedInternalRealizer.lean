import FHM.Bounds.RecursiveHMClosedInternalRealizer
import FHM.Bounds.RecursiveHMSpecializableEnvironment

/-! # Nested realization of closed recursive assumptions -/

namespace FHM.Bounds.RecursiveHMClosedExit

open RecursiveHMJudgement SchemeSpecialization CountSubstitution ScopedScheme
open RecursiveHMUniform

private theorem closedUseArgumentsSupported
    {c : RecursiveHMContract.Closed} {Delta : List Constraint} {found : Ty}
    {caller : List Nat} (used : RecursiveHMContract.Closed.Use c Delta found caller)
    (capturesSupported : ∀ a ∈ c.typeCaptures, Runtime.Supported a)
    (fixedSupported : ∀ a ∈ c.fixedTypes, Runtime.Supported a) :
    ∀ a ∈ used.use.types, Runtime.Supported a := by
  intro a member
  rw [← HMCountSchemeClosure.closedUse_typeArguments used.use] at member
  rcases List.mem_append.mp member with captured | fixed
  · apply capturesSupported a
    rw [← used.captures.types]
    exact captured
  · apply fixedSupported a
    rw [← used.fixedTail]
    exact fixed

/-- The generalized-world budget recursion above an arbitrary specializable
    lexical tail.  Weakening the lexical witness preserves its exact terms,
    so all protected worlds close the source RHSs over the same Core values. -/
def GeneralizedGroup.closedInternalEnvironmentNested
    {output metadata path captures premises bodyTypes outerEnv}
    (group : GeneralizedGroup output metadata path captures premises bodyTypes outerEnv)
    (sourceReady : ∀ offset (inside : offset < group.exports.length),
      ScopedDerives.RuntimeReady
        (group.selected offset inside).rhs.certificate.implementation.typing)
    (sourceDemandSupported : ∀ offset (inside : offset < group.exports.length),
      Runtime.Supported
        (group.selected offset inside).rhs.certificate.implementation.opening.bounds)
    (normal : ClosureNormal outerEnv)
    (bound free : Runtime.TypeEnv) (sigma : Assign)
    (hb : Runtime.TypeEnv.Downward bound) (hf : Runtime.TypeEnv.Downward free)
    (outer : Bindings) (outerFinite : Finite outer)
    (target : List Nat)
    (outerScope : ∀ row ∈ outer, Scope.CountScoped target row.2)
    (ambient : Nat → BoundsTy)
    (ambientLC : ∀ i, (Synth.BoundsTy.toTy (ambient i)).IsLC)
    (ambientScope : ∀ i, BoundsScoped target (ambient i))
    (ambientSupported : ∀ i, Runtime.Supported (ambient i))
    (ambientCounts : ∀ β, .mono β ∈ outerEnv → bounds outer β = β)
    (ambientTypes : ∀ β, .mono β ∈ outerEnv →
      ∀ i ∈ (Synth.BoundsTy.toTy β).freeVars, ambient i = .fvar i)
    :
    ∀ budget (lexical : SpecializableEnvAt bound free sigma budget outerEnv),
      { e : EnvAt bound free sigma budget
          (closeRecursiveEnv outer ambient group.internal) //
        e.terms = Runtime.recursiveTerms group.annotations
          (closeOuterRhss group.rhss lexical.fixed.terms) ++ lexical.fixed.terms }
  | 0, lexical => by
      let closedRhss := closeOuterRhss group.rhss lexical.fixed.terms
      let recursive := Runtime.recursiveTerms group.annotations closedRhss
      have closedScope : ∀ rhs ∈ closedRhss, rhs.varsBelow group.rhss.length = true := by
        apply closeOuterRhss_scoped lexical.fixed
        simpa only [fixedBodyEnv] using group.rhssScoped
      have recursiveClosed : ∀ term ∈ recursive, term.varsBelow 0 = true :=
        Runtime.recursiveTerms_closed (by
          simpa only [closedRhss, closeOuterRhss_length] using closedScope)
      refine ⟨{ terms := recursive ++ lexical.fixed.terms
                arity := ?_
                closed := ?_
                denotes := fun _ _ => BindingAt.zero bound free sigma _ _ }, rfl⟩
      · simp only [List.length_append, recursive, Runtime.recursiveTerms, List.length_map,
          closedRhss, closeOuterRhss_length, closeRecursiveEnv, GeneralizedGroup.internal,
          List.map_append, List.length_map, group.checked.memberCount, lexical.fixed.arity,
          fixedBodyEnv]
        simp only [GeneralizedGroup.rhss, List.length_map]
      · intro term member
        exact (List.mem_append.mp member).elim (recursiveClosed term) (lexical.fixed.closed term)
  | budget + 1, lexical => by
      let closedRhss := closeOuterRhss group.rhss lexical.fixed.terms
      let recursive := Runtime.recursiveTerms group.annotations closedRhss
      have closedScope : ∀ rhs ∈ closedRhss, rhs.varsBelow group.rhss.length = true := by
        apply closeOuterRhss_scoped lexical.fixed
        simpa only [fixedBodyEnv] using group.rhssScoped
      have recursiveClosed : ∀ term ∈ recursive, term.varsBelow 0 = true :=
        Runtime.recursiveTerms_closed (by
          simpa only [closedRhss, closeOuterRhss_length] using closedScope)
      have recursiveLength : recursive.length = group.rhss.length := by
        simp only [recursive, Runtime.recursiveTerms, List.length_map,
          closedRhss, closeOuterRhss_length]
      refine ⟨{ terms := recursive ++ lexical.fixed.terms
                arity := ?_
                closed := ?_
                denotes := ?_ }, rfl⟩
      · simp only [List.length_append, recursiveLength, closeRecursiveEnv,
          GeneralizedGroup.internal, List.map_append, List.length_map,
          group.checked.memberCount, lexical.fixed.arity, fixedBodyEnv]
        simp only [GeneralizedGroup.rhss, List.length_map]
      · intro term member
        exact (List.mem_append.mp member).elim (recursiveClosed term) (lexical.fixed.closed term)
      · intro member memberInside
        by_cases groupInside : member < group.exports.length
        · let selected := group.selected member groupInside
          have contractInside : member < group.checked.interfaces.contracts.length := by
            rw [group.checked.memberCount, ← group.checked.exportCount]
            simpa only [GeneralizedGroup.exports] using groupInside
          have leftInside : member <
              (group.checked.interfaces.contracts.map Binding.recursive).length := by
            simpa only [List.length_map] using contractInside
          have closedLeftInside : member <
              (closeRecursiveEnv outer ambient
                (group.checked.interfaces.contracts.map Binding.recursive)).length := by
            simpa only [closeRecursiveEnv, List.length_map] using leftInside
          have mappedLeftInside : member <
              ((group.checked.interfaces.contracts.map Binding.recursive).map
                (closeRecursiveBinding outer ambient)).length := by
            simpa only [closeRecursiveEnv] using closedLeftInside
          have lookup : (closeRecursiveEnv outer ambient group.internal)[member]? = some
              (.recursiveClosure
                (RecursiveHMContract.Closed.ofFixed selected.member.contract.fixed outer ambient)) := by
            rw [GeneralizedGroup.internal, closeRecursiveEnv, List.map_append,
              List.getElem?_append_left mappedLeftInside,
              List.getElem?_map, List.getElem?_map]
            simpa only [Option.map_some, Option.map_map, Function.comp_def,
              closeRecursiveBinding] using congrArg
              (Option.map (fun contract =>
                closeRecursiveBinding outer ambient (.recursive contract)))
              selected.contractSelection
          have entry := (List.getElem?_eq_some_iff.mp lookup).choose_spec
          rw [entry, List.getElem_append_left]
          · change ∀ pathDelta callFound callCaller
                (closedUse : RecursiveHMContract.Closed.Use
                  (RecursiveHMContract.Closed.ofFixed selected.member.contract.fixed outer ambient)
                  pathDelta callFound callCaller),
              (∀ p ∈ closedUse.use.countInstance.premises, p.Holds sigma) → _
            intro pathDelta callFound callCaller closedUse rawPremises
            have captureSupport : ∀ a ∈
                (RecursiveHMContract.Closed.ofFixed
                  selected.member.contract.fixed outer ambient).typeCaptures,
                Runtime.Supported a := by
              intro a memberOf
              obtain ⟨i, _, rfl⟩ := List.mem_map.mp memberOf
              exact ambientSupported i
            have fixedSupport : ∀ a ∈
                (RecursiveHMContract.Closed.ofFixed
                  selected.member.contract.fixed outer ambient).fixedTypes,
                Runtime.Supported a := by
              intro a memberOf
              obtain ⟨counted, countedMember, rfl⟩ := List.mem_map.mp memberOf
              obtain ⟨source, sourceMember, rfl⟩ := List.mem_map.mp countedMember
              apply Runtime.Supported.types ambient ambientSupported
              apply Runtime.Supported.counts outer
              obtain ⟨identity, _, rfl⟩ := List.mem_map.mp sourceMember
              exact Runtime.Supported.fvar
            have usedArguments : ∀ a ∈ closedUse.use.types, Runtime.Supported a :=
              closedUseArgumentsSupported closedUse captureSupport fixedSupport
            let nextOuter := group.protectedRows member groupInside closedUse.use outer
            let nextAmbient := group.protectedTypes member groupInside closedUse.use ambient
            let nextTarget := selected.rhs.certificate.interface.scheme.counts.captures ++
              callCaller ++ target
            have nextFinite : Finite nextOuter :=
              group.protectedRows_finite member groupInside closedUse.use outer outerFinite
            have nextOuterScope : ∀ row ∈ nextOuter,
                Scope.CountScoped nextTarget row.2 :=
              group.protectedRows_scoped member groupInside closedUse.use outer target outerScope
            have nextAmbientLC : ∀ i, (Synth.BoundsTy.toTy (nextAmbient i)).IsLC :=
              group.protectedTypes_lc member groupInside closedUse.use ambient ambientLC
            have nextAmbientScope : ∀ i, BoundsScoped nextTarget (nextAmbient i) :=
              group.protectedTypes_scoped member groupInside closedUse.use ambient target ambientScope
            have nextAmbientSupported : ∀ i, Runtime.Supported (nextAmbient i) :=
              group.protectedTypes_supported member groupInside closedUse.use ambient
                usedArguments ambientSupported
            have nextCounts : ∀ β, .mono β ∈ outerEnv → bounds nextOuter β = β :=
              group.protectedMonoCounts member groupInside closedUse.use outer ambientCounts
            have nextTypes : ∀ β, .mono β ∈ outerEnv →
                ∀ i ∈ (Synth.BoundsTy.toTy β).freeVars, nextAmbient i = .fvar i :=
              group.protectedMonoTypes member groupInside closedUse.use ambient ambientTypes
            let previousLexical := lexical.down hb hf (by omega : budget ≤ budget + 1)
            let previous := closedInternalEnvironmentNested group sourceReady
              sourceDemandSupported normal bound free sigma hb hf nextOuter nextFinite nextTarget
              nextOuterScope nextAmbient nextAmbientLC nextAmbientScope nextAmbientSupported
              nextCounts nextTypes budget previousLexical
            have safe := GeneralizedGroup.runtimeExitTermAtRaw group member groupInside
              closedUse.use outer outerFinite target outerScope ambient ambientLC ambientScope
              closedUse.captures normal (sourceReady member groupInside)
              (sourceDemandSupported member groupInside) usedArguments ambientSupported
              bound free sigma hb hf budget rawPremises previous.val
            rw [previous.property] at safe
            have sourceRhs := group.checked.memberAtRhs member groupInside
            have rhsLookup : group.rhss[member]? =
                some selected.member.declaration.node.inner.stripFound := by
              simpa only [GeneralizedGroup.rhss, List.getElem?_map, Option.map_some,
                Expr.stripFound] using congrArg (Option.map Expr.stripFound) sourceRhs
            have rhsInside : member < group.rhss.length := by
              rw [← group.exportCount]
              exact groupInside
            have rhsEq : group.rhss[member] =
                selected.member.declaration.node.inner.stripFound :=
              (List.getElem?_eq_some_iff.mp rhsLookup).choose_spec
            have previousOuterTerms : previousLexical.fixed.terms = lexical.fixed.terms := rfl
            have safe' : Runtime.TermAt bound free sigma budget closedUse.use.bounds
                ((group.rhss[member]'rhsInside).substN 0
                  (recursive ++ lexical.fixed.terms)) := by
              simpa only [recursive, closedRhss, rhsEq, previousOuterTerms] using safe
            have composed := Runtime.closing_compose lexical.fixed.terms recursive
              lexical.fixed.closed recursiveClosed (group.rhss[member]'rhsInside) 0
            rw [Nat.zero_add, recursiveLength] at composed
            rw [← composed] at safe'
            have closedInside : member < closedRhss.length := by
              rw [closeOuterRhss_length]
              exact rhsInside
            have recursiveInside : member < recursive.length := by
              rw [recursiveLength]
              exact rhsInside
            have rhsEntry : closedRhss[member]'closedInside =
                (group.rhss[member]'rhsInside).substN group.rhss.length
                  lexical.fixed.terms := by
              simp only [closedRhss, closeOuterRhss, List.getElem_map]
            have recursiveEntry : recursive[member]'recursiveInside =
                .letRec group.annotations closedRhss (closedRhss[member]'closedInside) := by
              simp only [recursive, Runtime.recursiveTerms, List.getElem_map]
            rw [recursiveEntry, rhsEntry]
            exact Runtime.TermAt.prepend SmallStep.Step.letRecUnfold safe'
          · rw [recursiveLength]
            rw [← group.exportCount]
            exact groupInside
        · have tailInside : member - group.exports.length < outerEnv.length := by
            have contractCount : group.checked.interfaces.contracts.length =
                group.exports.length := by
              rw [group.checked.memberCount, ← group.checked.exportCount]
              rfl
            simp only [closeRecursiveEnv, GeneralizedGroup.internal, List.map_append,
              List.length_append, List.length_map, contractCount] at memberInside
            omega
          have fresh : CloseRecursiveFresh outer ambient group.internal :=
            group.internalCloseRecursiveFresh outer ambient normal
          let world : StableEnvSpecialization outerEnv :=
            { outer := outer
              types := ambient
              outerFinite := outerFinite
              countTarget := target
              outerScope := outerScope
              typesLC := ambientLC
              typeTarget := target
              typesScope := ambientScope
              fresh := CloseRecursiveFresh.right fresh
              typesSupported := ambientSupported
              monoCounts := ambientCounts
              monoTypes := ambientTypes }
          have meaning := (lexical.specialized world).denotes
            (member - group.exports.length) (by
              simpa only [closeRecursiveEnv, List.length_map] using tailInside)
          have contractCount : group.checked.interfaces.contracts.length =
              group.exports.length := by
            rw [group.checked.memberCount, ← group.checked.exportCount]
            rfl
          have groupPosition : group.exports.length ≤ member := by omega
          have recursivePosition : recursive.length ≤ member := by
            rw [recursiveLength, ← group.exportCount]
            exact groupPosition
          have bindingPosition :
              (closeRecursiveEnv outer ambient
                (group.checked.interfaces.contracts.map Binding.recursive)).length ≤ member := by
            simpa only [closeRecursiveEnv, List.length_map, contractCount] using groupPosition
          have mappedBindingPosition :
              ((group.checked.interfaces.contracts.map Binding.recursive).map
                (closeRecursiveBinding outer ambient)).length ≤ member := by
            simpa only [closeRecursiveEnv] using bindingPosition
          simp only [GeneralizedGroup.internal, closeRecursiveEnv, List.map_append]
          rw [List.getElem_append_right mappedBindingPosition,
            List.getElem_append_right recursivePosition]
          simpa only [closeRecursiveEnv, List.length_map, recursiveLength,
            group.exportCount, contractCount, lexical.specializedTerms] using meaning

/-- A budget-indexed lexical Kripke family whose runtime syntax is independent
    of the observation budget. -/
structure SpecializableEnvFamily (bound free : Runtime.TypeEnv) (sigma : Assign)
    (env : List Binding) where
  terms : List Expr
  world : ∀ budget, SpecializableEnvAt bound free sigma budget env
  worldTerms : ∀ budget, (world budget).fixed.terms = terms

/-- The empty lexical environment has the same empty runtime syntax at every
    observation budget. -/
def SpecializableEnvFamily.empty (bound free : Runtime.TypeEnv) (sigma : Assign) :
    SpecializableEnvFamily bound free sigma [] where
  terms := []
  world := fun budget => SpecializableEnvAt.empty bound free sigma budget
  worldTerms := fun _ => rfl

/-- Concatenate two Kripke families pointwise.  The shared runtime syntax is
    the same left-to-right concatenation in every budget and specialization
    world. -/
def SpecializableEnvFamily.append
    {bound free : Runtime.TypeEnv} {sigma : Assign} {left right : List Binding}
    (head : SpecializableEnvFamily bound free sigma left)
    (tail : SpecializableEnvFamily bound free sigma right) :
    SpecializableEnvFamily bound free sigma (left ++ right) where
  terms := head.terms ++ tail.terms
  world := fun budget => SpecializableEnvAt.append (head.world budget) (tail.world budget)
  worldTerms := by
    intro budget
    simp only [SpecializableEnvAt.append, EnvAt.append, head.worldTerms, tail.worldTerms]

/-- Package the nested environment theorem at every closed exit use in the
    parallel Kripke family.  This is deliberately distinct from the universal
    `ClosedRuntimeReady` interface: it preserves this family's one lexical
    term vector rather than ranging over arbitrary enclosing witnesses. -/
def GeneralizedGroup.closedInternalRealizerNested
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
    (ambientCounts : ∀ β, .mono β ∈ outerEnv → bounds outer β = β)
    (ambientTypes : ∀ β, .mono β ∈ outerEnv →
      ∀ i ∈ (Synth.BoundsTy.toTy β).freeVars, ambient i = .fvar i)
    (bound free : Runtime.TypeEnv) (sigma : Assign)
    (hb : Runtime.TypeEnv.Downward bound) (hf : Runtime.TypeEnv.Downward free)
    (lexical : SpecializableEnvFamily bound free sigma outerEnv) :
    ClosedInternalRealizer group outer target ambient bound free sigma lexical.terms := by
  refine ⟨?_⟩
  intro offset inside calleeDelta found caller used capturesAgree arguments budget
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
  have countsStable : ∀ β, .mono β ∈ outerEnv → bounds rows β = β :=
    group.protectedMonoCounts offset inside used outer ambientCounts
  have typesStable : ∀ β, .mono β ∈ outerEnv →
      ∀ i ∈ (Synth.BoundsTy.toTy β).freeVars, types i = .fvar i :=
    group.protectedMonoTypes offset inside used ambient ambientTypes
  let realized := closedInternalEnvironmentNested group sourceReady sourceDemandSupported
    normal bound free sigma hb hf rows rowsFinite target' rowsScoped types typesLC typesScoped
    typesSupported countsStable typesStable budget (lexical.world budget)
  refine ⟨realized.val, ?_⟩
  simpa only [lexical.worldTerms] using realized.property

/-- Fixed-body view of a nested closed group. -/
def GeneralizedGroup.closedExportEnvironmentNestedFixed
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
    (ambientCounts : ∀ β, .mono β ∈ outerEnv → bounds outer β = β)
    (ambientTypes : ∀ β, .mono β ∈ outerEnv →
      ∀ i ∈ (Synth.BoundsTy.toTy β).freeVars, ambient i = .fvar i)
    (bound free : Runtime.TypeEnv) (sigma : Assign)
    (hb : Runtime.TypeEnv.Downward bound) (hf : Runtime.TypeEnv.Downward free)
    (lexical : SpecializableEnvFamily bound free sigma outerEnv)
    (budget : Nat) :
    { e : BodyEnvAt bound free sigma budget
        (group.closedExports outer ambient ++ fixedBodyEnv outerEnv) //
      e.terms = Runtime.recursiveTerms group.annotations
        (closeOuterRhss group.rhss lexical.terms) ++ lexical.terms } := by
  let internal := closedInternalRealizerNested group outer outerFinite target outerScope
    ambient ambientLC ambientScope normal sourceReady sourceDemandSupported ambientSupported ambientCounts ambientTypes
    bound free sigma hb hf lexical
  let tail := lexical.world budget |>.fixed
  have tailTerms : tail.terms = lexical.terms := lexical.worldTerms budget
  let realized := closedExportEnvironmentCaptured group outer outerFinite target outerScope
    ambient ambientLC ambientScope normal sourceReady sourceDemandSupported ambientSupported
    bound free sigma hb hf (tail := fixedBodyEnv outerEnv) (by simp [fixedBodyEnv]) tail
    (by simpa only [tailTerms] using internal)
  simpa only [tailTerms] using realized

/-- Ordinary exported-body view of the same nested closed group. -/
def GeneralizedGroup.closedExportEnvironmentNestedOrdinary
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
    (ambientCounts : ∀ β, .mono β ∈ outerEnv → bounds outer β = β)
    (ambientTypes : ∀ β, .mono β ∈ outerEnv →
      ∀ i ∈ (Synth.BoundsTy.toTy β).freeVars, ambient i = .fvar i)
    (bound free : Runtime.TypeEnv) (sigma : Assign)
    (hb : Runtime.TypeEnv.Downward bound) (hf : Runtime.TypeEnv.Downward free)
    (lexical : SpecializableEnvFamily bound free sigma outerEnv)
    (budget : Nat) :
    { e : BodyEnvAt bound free sigma budget
        (group.closedExports outer ambient ++ ordinaryBodyEnv outerEnv) //
      e.terms = Runtime.recursiveTerms group.annotations
        (closeOuterRhss group.rhss lexical.terms) ++ lexical.terms } := by
  let internal := closedInternalRealizerNested group outer outerFinite target outerScope
    ambient ambientLC ambientScope normal sourceReady sourceDemandSupported ambientSupported ambientCounts ambientTypes
    bound free sigma hb hf lexical
  let tail := lexical.world budget |>.ordinary
  have tailTerms : tail.terms = lexical.terms :=
    (lexical.world budget).ordinaryTerms.trans (lexical.worldTerms budget)
  let realized := closedExportEnvironmentCaptured group outer outerFinite target outerScope
    ambient ambientLC ambientScope normal sourceReady sourceDemandSupported ambientSupported
    bound free sigma hb hf (tail := ordinaryBodyEnv outerEnv)
    (by simp [ordinaryBodyEnv]) tail (by simpa only [tailTerms] using internal)
  simpa only [tailTerms] using realized

end FHM.Bounds.RecursiveHMClosedExit
