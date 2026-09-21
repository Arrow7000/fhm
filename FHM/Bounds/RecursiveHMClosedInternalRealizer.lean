import FHM.Bounds.RecursiveHMClosedExportEnvironment
import FHM.PatComp

/-! # Top-level realization of closed recursive assumptions

Recursive calls may choose fresh member-local count arguments.  Consequently
the observation-budget induction below generalizes over the current protected
count and HM interpretations instead of fixing one environment throughout.
-/

namespace FHM.Bounds.RecursiveHMClosedExit

open RecursiveHMJudgement SchemeSpecialization CountSubstitution ScopedScheme
open RecursiveHMUniform

private theorem closedUse_argumentsSupported
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

/-- The closed recursive assumptions of a top-level group denote its original
    Core recursive terms under every finite protected interpretation. -/
def GeneralizedGroup.closedInternalEnvironmentTop
    {output metadata path captures premises bodyTypes}
    (group : GeneralizedGroup output metadata path captures premises bodyTypes [])
    (sourceReady : ∀ offset (inside : offset < group.exports.length),
      ScopedDerives.RuntimeReady
        (group.selected offset inside).rhs.certificate.implementation.typing)
    (sourceDemandSupported : ∀ offset (inside : offset < group.exports.length),
      Runtime.Supported
        (group.selected offset inside).rhs.certificate.implementation.opening.bounds)
    (bound free : Runtime.TypeEnv) (sigma : Assign)
    (hb : Runtime.TypeEnv.Downward bound) (hf : Runtime.TypeEnv.Downward free)
    (outer : Bindings) (outerFinite : Finite outer)
    (target : List Nat)
    (outerScope : ∀ row ∈ outer, Scope.CountScoped target row.2)
    (ambient : Nat → BoundsTy)
    (ambientLC : ∀ i, (Synth.BoundsTy.toTy (ambient i)).IsLC)
    (ambientScope : ∀ i, BoundsScoped target (ambient i))
    (ambientSupported : ∀ i, Runtime.Supported (ambient i)) :
    ∀ budget,
      { e : EnvAt bound free sigma budget
          (closeRecursiveEnv outer ambient group.internal) //
        e.terms = Runtime.recursiveTerms group.annotations group.rhss }
  | 0 => by
      let recursive := Runtime.recursiveTerms group.annotations group.rhss
      have arity : recursive.length = (closeRecursiveEnv outer ambient group.internal).length := by
        simp only [recursive, Runtime.recursiveTerms, List.length_map, closeRecursiveEnv,
          GeneralizedGroup.internal, List.length_append, List.length_nil, Nat.add_zero,
          GeneralizedGroup.rhss, group.checked.memberCount]
      have scope : ∀ rhs ∈ group.rhss, rhs.varsBelow group.rhss.length = true := by
        simpa using group.rhssScoped
      exact ⟨{
        terms := recursive
        arity := arity
        closed := Runtime.recursiveTerms_closed scope
        denotes := fun _ _ => BindingAt.zero bound free sigma _ _ }, rfl⟩
  | budget + 1 => by
      let recursive := Runtime.recursiveTerms group.annotations group.rhss
      have arity : recursive.length = (closeRecursiveEnv outer ambient group.internal).length := by
        simp only [recursive, Runtime.recursiveTerms, List.length_map, closeRecursiveEnv,
          GeneralizedGroup.internal, List.length_append, List.length_nil, Nat.add_zero,
          GeneralizedGroup.rhss, group.checked.memberCount]
      have scope : ∀ rhs ∈ group.rhss, rhs.varsBelow group.rhss.length = true := by
        simpa using group.rhssScoped
      refine ⟨{
        terms := recursive
        arity := arity
        closed := Runtime.recursiveTerms_closed scope
        denotes := ?_ }, rfl⟩
      intro member memberInside
      have exitInside : member < group.exports.length := by
        rw [group.exportCount]
        simpa only [recursive, Runtime.recursiveTerms, List.length_map] using
          (show member < recursive.length by rw [arity]; exact memberInside)
      let selected := group.selected member exitInside
      have lookup : (closeRecursiveEnv outer ambient group.internal)[member]? = some
          (.recursiveClosure
            (RecursiveHMContract.Closed.ofFixed selected.member.contract.fixed outer ambient)) := by
        simpa only [GeneralizedGroup.internal, List.append_nil, closeRecursiveEnv,
          List.getElem?_map, Option.map_some, Option.map_map, Function.comp_def,
          closeRecursiveBinding] using
          congrArg
            (Option.map (fun contract =>
              closeRecursiveBinding outer ambient (.recursive contract)))
            selected.contractSelection
      have entry := (List.getElem?_eq_some_iff.mp lookup).choose_spec
      rw [entry]
      change ∀ pathDelta callFound callCaller
          (closedUse : RecursiveHMContract.Closed.Use
            (RecursiveHMContract.Closed.ofFixed selected.member.contract.fixed outer ambient)
            pathDelta callFound callCaller),
        (∀ p ∈ closedUse.use.countInstance.premises, p.Holds sigma) → _
      intro pathDelta callFound callCaller closedUse rawPremises
      have captureSupport : ∀ a ∈
          (RecursiveHMContract.Closed.ofFixed selected.member.contract.fixed outer ambient).typeCaptures,
          Runtime.Supported a := by
        intro a memberOf
        obtain ⟨i, _, rfl⟩ := List.mem_map.mp memberOf
        exact ambientSupported i
      have fixedSupport : ∀ a ∈
          (RecursiveHMContract.Closed.ofFixed selected.member.contract.fixed outer ambient).fixedTypes,
          Runtime.Supported a := by
        intro a memberOf
        obtain ⟨counted, countedMember, rfl⟩ := List.mem_map.mp memberOf
        obtain ⟨source, sourceMember, rfl⟩ := List.mem_map.mp countedMember
        apply Runtime.Supported.types ambient ambientSupported
        apply Runtime.Supported.counts outer
        obtain ⟨identity, _, rfl⟩ := List.mem_map.mp sourceMember
        exact Runtime.Supported.fvar
      have usedArguments : ∀ a ∈ closedUse.use.types, Runtime.Supported a :=
        closedUse_argumentsSupported closedUse captureSupport fixedSupport
      let nextOuter := group.protectedRows member exitInside closedUse.use outer
      let nextAmbient := group.protectedTypes member exitInside closedUse.use ambient
      let nextTarget := selected.rhs.certificate.interface.scheme.counts.captures ++
        callCaller ++ target
      have nextFinite : Finite nextOuter :=
        group.protectedRows_finite member exitInside closedUse.use outer outerFinite
      have nextOuterScope : ∀ row ∈ nextOuter, Scope.CountScoped nextTarget row.2 :=
        group.protectedRows_scoped member exitInside closedUse.use outer target outerScope
      have nextAmbientLC : ∀ i, (Synth.BoundsTy.toTy (nextAmbient i)).IsLC :=
        group.protectedTypes_lc member exitInside closedUse.use ambient ambientLC
      have nextAmbientScope : ∀ i, BoundsScoped nextTarget (nextAmbient i) :=
        group.protectedTypes_scoped member exitInside closedUse.use ambient target ambientScope
      have nextAmbientSupported : ∀ i, Runtime.Supported (nextAmbient i) :=
        group.protectedTypes_supported member exitInside closedUse.use ambient usedArguments
          ambientSupported
      let previous := closedInternalEnvironmentTop group sourceReady sourceDemandSupported
        bound free sigma hb hf nextOuter nextFinite nextTarget nextOuterScope nextAmbient
        nextAmbientLC nextAmbientScope nextAmbientSupported budget
      have safe := GeneralizedGroup.runtimeExitTermAtRaw group member exitInside closedUse.use
        outer outerFinite target outerScope ambient ambientLC ambientScope closedUse.captures
        (by intro scheme member; simp at member) (sourceReady member exitInside)
        (sourceDemandSupported member exitInside) usedArguments ambientSupported bound free sigma
        hb hf budget rawPremises previous.val
      rw [previous.property] at safe
      have sourceRhs := group.checked.memberAtRhs member exitInside
      have rhsLookup : group.rhss[member]? =
          some selected.member.declaration.node.inner.stripFound := by
        simpa only [GeneralizedGroup.rhss, List.getElem?_map, Option.map_some,
          Expr.stripFound] using congrArg (Option.map Expr.stripFound) sourceRhs
      have rhsInside : member < group.rhss.length := by
        rw [← group.exportCount]
        exact exitInside
      have rhsEq : group.rhss[member] =
          selected.member.declaration.node.inner.stripFound :=
        (List.getElem?_eq_some_iff.mp rhsLookup).choose_spec
      have safe' : Runtime.TermAt bound free sigma budget closedUse.use.bounds
          ((group.rhss[member]'rhsInside).substN 0 recursive) := by
        simpa only [recursive, rhsEq] using safe
      simp only [recursive, Runtime.recursiveTerms, List.getElem_map]
      exact Runtime.TermAt.prepend SmallStep.Step.letRecUnfold safe'

/-- Package the generalized environment theorem at each actual closed exit use. -/
def GeneralizedGroup.closedInternalRealizerTop
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
    (bound free : Runtime.TypeEnv) (sigma : Assign)
    (hb : Runtime.TypeEnv.Downward bound) (hf : Runtime.TypeEnv.Downward free) :
    ClosedInternalRealizer group outer target ambient bound free sigma [] := by
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
  let realized := closedInternalEnvironmentTop group sourceReady sourceDemandSupported
    bound free sigma hb hf rows rowsFinite target' rowsScoped types typesLC typesScoped
    typesSupported budget
  refine ⟨realized.val, ?_⟩
  simpa [closeOuterRhss, PatComp.Expr.substN_nil] using realized.property

#print axioms GeneralizedGroup.closedInternalEnvironmentTop
#print axioms GeneralizedGroup.closedInternalRealizerTop

end FHM.Bounds.RecursiveHMClosedExit
