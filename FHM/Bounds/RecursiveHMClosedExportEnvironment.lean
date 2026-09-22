import FHM.Bounds.RecursiveHMClosedExitRuntime

/-! # Runtime environments for closed generalized-group exports

The static closure of an exit is use-dependent: each caller supplies the
source member's count and HM arguments, and those arguments determine the
`closeRecursiveEnv` in which its implementation theorem runs.  This module
isolates that remaining fixed-point obligation from the routine Core tying
argument.

`ClosedInternalRealizer` is deliberately semantic.  It does not assert that
all uses share one static recursive environment; instead it supplies the
appropriately re-specialized environment for each actual closed use.  Given
that family, `closedExportEnvironmentCaptured` proves that the body-visible
lexical closures are represented by exactly Core's original, simultaneously
tied recursive terms.
-/

namespace FHM.Bounds.RecursiveHMClosedExit

open RecursiveHMJudgement SchemeSpecialization CountSubstitution ScopedScheme
open RecursiveHMUniform

/-- The raw-premise form needed while tying an environment.  `BindingAt` for
    an exported closure assumes the closed instance's instantiated premises;
    `runtimeExit` exposes the caller-context form used by variable lookup.
    The promotion theorem identifies the former with the protected source
    premises, allowing the same transported implementation proof to run
    before `assuming` discharges them. -/
theorem GeneralizedGroup.runtimeExitTermAtRawOfFresh
    {output metadata path captures premises bodyTypes outerEnv calleeΔ found caller}
    (group : GeneralizedGroup output metadata path captures premises bodyTypes outerEnv)
    (offset : Nat) (inside : offset < group.exports.length)
    (used : HMCountScheme.Use
      (HMCountSchemeClosure.close
        (group.selected offset inside).rhs.certificate.interface.scheme)
      calleeΔ found caller)
    (outer : Bindings) (outerFinite : Finite outer)
    (target : List Nat)
    (outerScope : ∀ row ∈ outer, Scope.CountScoped target row.2)
    (ambient : Nat → BoundsTy)
    (ambientLC : ∀ i, (Synth.BoundsTy.toTy (ambient i)).IsLC)
    (ambientScope : ∀ i, BoundsScoped target (ambient i))
    (capturesAgree : HMCountSchemeClosure.CapturesAgree
      (group.selected offset inside).rhs.certificate.interface.scheme
      outer ambient used)
    (fresh : CloseRecursiveFresh
      (group.protectedRows offset inside used outer)
      (group.protectedTypes offset inside used ambient)
      group.internal)
    (sourceReady : ScopedDerives.RuntimeReady
      (group.selected offset inside).rhs.certificate.implementation.typing)
    (sourceDemandSupported : Runtime.Supported
      (group.selected offset inside).rhs.certificate.implementation.opening.bounds)
    (arguments : ∀ a ∈ used.types, Runtime.Supported a)
    (ambientSupported : ∀ i, Runtime.Supported (ambient i))
    (bound free : Runtime.TypeEnv) (σ : Assign)
    (hb : Runtime.TypeEnv.Downward bound) (hf : Runtime.TypeEnv.Downward free)
    (budget : Nat)
    (rawPremises : ∀ p ∈ used.countInstance.premises, p.Holds σ)
    (e : EnvAt bound free σ budget
      (closeRecursiveEnv
        (group.protectedRows offset inside used outer)
        (group.protectedTypes offset inside used ambient)
        group.internal)) :
    Runtime.TermAt bound free σ budget used.bounds
      ((group.selected offset inside).member.declaration.node.inner.stripFound.substN
        0 e.terms) := by
  let cert := (group.selected offset inside).rhs.certificate.implementation
  let s := (group.selected offset inside).rhs.certificate.interface.scheme
  let protectedRows := group.protectedRows offset inside used outer
  let protectedTypes := group.protectedTypes offset inside used ambient
  let target' := s.counts.captures ++ caller ++ target
  have rowsFinite : Finite protectedRows :=
    group.protectedRows_finite offset inside used outer outerFinite
  have rowsScoped : ∀ row ∈ protectedRows, Scope.CountScoped target' row.2 :=
    group.protectedRows_scoped offset inside used outer target outerScope
  have typesLC : ∀ i, (Synth.BoundsTy.toTy (protectedTypes i)).IsLC :=
    group.protectedTypes_lc offset inside used ambient ambientLC
  have typesScoped : ∀ i, BoundsScoped target' (protectedTypes i) :=
    group.protectedTypes_scoped offset inside used ambient target ambientScope
  have typeSupport : ∀ i, Runtime.Supported (protectedTypes i) :=
    group.protectedTypes_supported offset inside used ambient arguments ambientSupported
  let closed := cert.typing.closeRecursive protectedRows protectedTypes
    rowsFinite target' rowsScoped typesLC target' typesScoped fresh
  have closedReady : ScopedDerives.RuntimeReady closed :=
    RecursiveHMJudgement.RuntimeReady.closeRecursive protectedRows protectedTypes
      rowsFinite target' rowsScoped typesLC target' typesScoped sourceReady fresh typeSupport
  have sourcePremises : ∀ p ∈
      s.counts.premises.map (constraint protectedRows), p.Holds σ := by
    have premiseEq := HMCountSchemeClosure.closedUse_premises_protected
      used outer ambient capturesAgree
    simpa only [s, protectedRows, GeneralizedGroup.protectedRows] using
      (premiseEq ▸ rawPremises)
  have behavior := closedReady.termAt bound free σ hb hf budget sourcePremises e
  have counted : SemanticSub
      (s.counts.premises.map (constraint protectedRows))
      (bounds protectedRows cert.actual)
      (bounds protectedRows cert.opening.bounds) :=
    CountSubstitution.subtype protectedRows rowsFinite cert.inclusion
  have mapped : SemanticSub
      (s.counts.premises.map (constraint protectedRows))
      (mapFree protectedTypes (bounds protectedRows cert.actual))
      (mapFree protectedTypes (bounds protectedRows cert.opening.bounds)) :=
    SchemeSpecialization.subtype protectedTypes counted
  have targetSupported : Runtime.Supported used.bounds :=
    group.protectedDemand_supported offset inside used outer ambient ambientLC capturesAgree
      sourceDemandSupported arguments ambientSupported
  have demandEq : mapFree protectedTypes (bounds protectedRows cert.opening.bounds) =
      used.bounds := by
    simpa only [cert, protectedRows, protectedTypes] using
      group.protectedDemand offset inside used outer ambient ambientLC capturesAgree
  have transportedTargetSupported : Runtime.Supported
      (mapFree protectedTypes (bounds protectedRows cert.opening.bounds)) := by
    rw [demandEq]
    exact targetSupported
  apply behavior.of_values
  simpa only [demandEq] using
    Runtime.subtype mapped closedReady.supported transportedTargetSupported
      bound free σ sourcePremises

/-- Closure-normal compatibility wrapper for the canonical closed-program
    path.  Base-indexed local semantics use `runtimeExitTermAtRawOfFresh`
    directly, because their lexical tail may already contain closed exports. -/
theorem GeneralizedGroup.runtimeExitTermAtRaw
    {output metadata path captures premises bodyTypes outerEnv calleeΔ found caller}
    (group : GeneralizedGroup output metadata path captures premises bodyTypes outerEnv)
    (offset : Nat) (inside : offset < group.exports.length)
    (used : HMCountScheme.Use
      (HMCountSchemeClosure.close
        (group.selected offset inside).rhs.certificate.interface.scheme)
      calleeΔ found caller)
    (outer : Bindings) (outerFinite : Finite outer)
    (target : List Nat)
    (outerScope : ∀ row ∈ outer, Scope.CountScoped target row.2)
    (ambient : Nat → BoundsTy)
    (ambientLC : ∀ i, (Synth.BoundsTy.toTy (ambient i)).IsLC)
    (ambientScope : ∀ i, BoundsScoped target (ambient i))
    (capturesAgree : HMCountSchemeClosure.CapturesAgree
      (group.selected offset inside).rhs.certificate.interface.scheme
      outer ambient used)
    (normal : ClosureNormal outerEnv)
    (sourceReady : ScopedDerives.RuntimeReady
      (group.selected offset inside).rhs.certificate.implementation.typing)
    (sourceDemandSupported : Runtime.Supported
      (group.selected offset inside).rhs.certificate.implementation.opening.bounds)
    (arguments : ∀ a ∈ used.types, Runtime.Supported a)
    (ambientSupported : ∀ i, Runtime.Supported (ambient i))
    (bound free : Runtime.TypeEnv) (σ : Assign)
    (hb : Runtime.TypeEnv.Downward bound) (hf : Runtime.TypeEnv.Downward free)
    (budget : Nat)
    (rawPremises : ∀ p ∈ used.countInstance.premises, p.Holds σ)
    (e : EnvAt bound free σ budget
      (closeRecursiveEnv
        (group.protectedRows offset inside used outer)
        (group.protectedTypes offset inside used ambient)
        group.internal)) :
    Runtime.TermAt bound free σ budget used.bounds
      ((group.selected offset inside).member.declaration.node.inner.stripFound.substN
        0 e.terms) := by
  apply GeneralizedGroup.runtimeExitTermAtRawOfFresh group offset inside used outer outerFinite target
    outerScope ambient ambientLC ambientScope capturesAgree
  · exact group.internalCloseRecursiveFresh _ _ normal
  · exact sourceReady
  · exact sourceDemandSupported
  · exact arguments
  · exact ambientSupported
  · exact hb
  · exact hf
  · exact rawPremises

/-- The genuinely recursive premise left after closing one generalized exit.
    A closed use determines protected count and HM maps, so the internal
    recursive environment varies with the use.  Every realization must still
    denote the same source-ordered tied terms. -/
structure GeneralizedGroup.ClosedInternalRealizer
    {output metadata path captures premises bodyTypes outerEnv}
    (group : GeneralizedGroup output metadata path captures premises bodyTypes outerEnv)
    (outer : Bindings) (target : List Nat) (ambient : Nat → BoundsTy)
    (bound free : Runtime.TypeEnv) (σ : Assign) (outerTerms : List Expr) where
  realize : ∀ offset (inside : offset < group.exports.length)
    {calleeΔ found caller}
    (used : HMCountScheme.Use
      (HMCountSchemeClosure.close
        (group.selected offset inside).rhs.certificate.interface.scheme)
      calleeΔ found caller),
    HMCountSchemeClosure.CapturesAgree
      (group.selected offset inside).rhs.certificate.interface.scheme
      outer ambient used →
    (∀ a ∈ used.types, Runtime.Supported a) →
    ∀ budget,
      { e : EnvAt bound free σ budget
          (closeRecursiveEnv
            (group.protectedRows offset inside used outer)
            (group.protectedTypes offset inside used ambient)
            group.internal) //
        e.terms = Runtime.recursiveTerms group.annotations
          (closeOuterRhss group.rhss outerTerms) ++ outerTerms }

/-- Once the use-indexed recursive fixed point is available, all closed group
    exits are realized by the original source recursive terms.  The proof is
    the ordinary observation-budget tie: at positive budget, the selected
    transported RHS runs for one fewer observation and Core's `letRec` unfold
    supplies the leading step. -/
def GeneralizedGroup.closedExportEnvironmentCaptured
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
    (bound free : Runtime.TypeEnv) (σ : Assign)
    (hb : Runtime.TypeEnv.Downward bound) (hf : Runtime.TypeEnv.Downward free)
    {tail : List Binding} (tailLength : tail.length = outerEnv.length)
    (outerEnvAt : EnvAt bound free σ budget tail)
    (internal : ClosedInternalRealizer group outer target ambient bound free σ
      outerEnvAt.terms) :
    { e : EnvAt bound free σ budget (group.closedExports outer ambient ++ tail) //
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
      intro calleeΔ found caller used capturesAgree arguments rawPremises
      cases budget with
      | zero =>
          unfold Runtime.TermAt
          intro steps value _ before
          omega
      | succ smaller =>
          let realized := internal.realize i groupInside used capturesAgree arguments smaller
          have safe := GeneralizedGroup.runtimeExitTermAtRaw group i groupInside used outer
            outerFinite target outerScope ambient ambientLC ambientScope capturesAgree normal
            (sourceReady i groupInside) (sourceDemandSupported i groupInside) arguments
            ambientSupported bound free σ hb hf smaller rawPremises realized.val
          rw [realized.property] at safe
          have sourceRhs := group.checked.memberAtRhs i groupInside
          have rhsLookup : group.rhss[i]? =
              some selected.member.declaration.node.inner.stripFound := by
            simpa only [GeneralizedGroup.rhss, List.getElem?_map, Option.map_some,
              Expr.stripFound] using congrArg (Option.map Expr.stripFound) sourceRhs
          have rhsEq : group.rhss[i] =
              selected.member.declaration.node.inner.stripFound :=
            (List.getElem?_eq_some_iff.mp rhsLookup).choose_spec
          have safe' : Runtime.TermAt bound free σ smaller used.bounds
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

#print axioms GeneralizedGroup.closedExportEnvironmentCaptured

end FHM.Bounds.RecursiveHMClosedExit
