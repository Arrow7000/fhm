import FHM.Bounds.RecursiveHMClosureFresh

/-! Static closure of one generalized recursive-group exit.

This module keeps the generic transport result separate from the source group
assembly.  It turns one source RHS derivation into a derivation under the
combined count/HM interpretation and records the transported implementation
inclusion at the caller's demand.
-/

namespace FHM.Bounds.RecursiveHMClosedExit

open RecursiveHMJudgement SchemeSpecialization CountSubstitution ScopedScheme
open RecursiveHMUniform

/-- The static result of closing a source RHS derivation over one enclosing
    interpretation.  The result type is deliberately the transported actual,
    not the demand: retaining the inclusion keeps implementation and interface
    evidence available separately. -/
structure StaticExit
    {types slots : Nat → BoundsTy} {ids : List Nat} {sourceRows : Bindings}
    {sourceΔ : List Constraint} {env : List Binding} {rhs : Expr} {actual : BoundsTy}
    (source : ScopedDerives types slots ids sourceRows sourceΔ env rhs actual)
    (outer : Bindings) (f : Nat → BoundsTy) (calleeΔ : List Constraint)
    (demand : BoundsTy) where
  typing : ScopedDerives
    (fun i => mapFree f (bounds outer (types i)))
    (fun i => mapFree f (bounds outer (slots i)))
    ids (CountAlgebra.compose outer sourceRows) calleeΔ
    (closeRecursiveEnv outer f env) rhs (mapFree f (bounds outer actual))
  inclusion : SemanticSub calleeΔ (mapFree f (bounds outer actual)) demand

/-- Close one actual generalized-group exit use back over its source member.
    The source certificate is transported exactly once.  Protected count/HM
    maps preserve caller arguments, source premises are discharged by the
    closed use, and the transported source demand is identified with the
    caller-visible closed demand. -/
def GeneralizedGroup.staticExit
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
    (normal : ClosureNormal outerEnv) :
    StaticExit
      (group.selected offset inside).rhs.certificate.implementation.typing
      (group.protectedRows offset inside used outer)
      (group.protectedTypes offset inside used ambient) calleeΔ used.bounds := by
  let cert := (group.selected offset inside).rhs.certificate.implementation
  let s := (group.selected offset inside).rhs.certificate.interface.scheme
  let protectedRows := group.protectedRows offset inside used outer
  let protectedTypes := group.protectedTypes offset inside used ambient
  let target' :=
    (((group.selected offset inside).rhs.certificate.interface.scheme.counts.captures ++
      caller) ++ target)
  have rowsFinite : Finite protectedRows :=
    group.protectedRows_finite offset inside used outer outerFinite
  have rowsScoped : ∀ row ∈ protectedRows, Scope.CountScoped target' row.2 :=
    group.protectedRows_scoped offset inside used outer target outerScope
  have typesLC : ∀ i, (Synth.BoundsTy.toTy (protectedTypes i)).IsLC :=
    group.protectedTypes_lc offset inside used ambient ambientLC
  have typesScoped : ∀ i, BoundsScoped target' (protectedTypes i) :=
    group.protectedTypes_scoped offset inside used ambient target ambientScope
  have fresh : CloseRecursiveFresh protectedRows protectedTypes group.internal :=
    group.internalCloseRecursiveFresh protectedRows protectedTypes normal
  let closed := cert.typing.closeRecursive protectedRows protectedTypes
    rowsFinite target' rowsScoped typesLC target' typesScoped fresh
  have usable : (⟨calleeΔ,
      s.counts.premises.map (constraint protectedRows)⟩ :
      ForallProblem).Valid := by
    simpa only [s, cert, protectedRows, GeneralizedGroup.protectedRows] using
      HMCountSchemeClosure.closedUse_usable_protected used outer ambient capturesAgree
  have typing := closed.assuming usable
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
  have included := mapped.assuming usable
  have demandEq : mapFree protectedTypes (bounds protectedRows cert.opening.bounds) =
      used.bounds := by
    simpa only [cert, protectedRows, protectedTypes] using
      group.protectedDemand offset inside used outer ambient ambientLC capturesAgree
  refine ⟨?_, ?_⟩
  · simpa only [cert, protectedRows, protectedTypes, CountAlgebra.compose,
      List.map_nil, List.nil_append] using typing
  · simpa only [cert, protectedRows, protectedTypes, demandEq] using included

end FHM.Bounds.RecursiveHMClosedExit
