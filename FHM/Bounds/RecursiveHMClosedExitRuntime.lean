import FHM.Bounds.RecursiveHMClosedExit

/-! Runtime realization of statically closed generalized-group exits. -/

namespace FHM.Bounds.RecursiveHMClosedExit

open RecursiveHMJudgement SchemeSpecialization CountSubstitution ScopedScheme
open RecursiveHMUniform

/-- Runtime evidence for a statically closed exit keeps both ingredients used
    by the fundamental theorem: readiness of the transported implementation
    and support of the caller-visible demand. -/
structure StaticExit.RuntimeReady
    {types slots : Nat → BoundsTy} {ids : List Nat} {sourceRows : Bindings}
    {sourceΔ : List Constraint} {env : List Binding} {rhs : Expr} {actual : BoundsTy}
    {source : ScopedDerives types slots ids sourceRows sourceΔ env rhs actual}
    {outer : Bindings} {f : Nat → BoundsTy} {calleeΔ : List Constraint}
    {demand : BoundsTy}
    (exit : StaticExit source outer f calleeΔ demand) where
  typing : ScopedDerives.RuntimeReady exit.typing
  demandSupported : Runtime.Supported demand

/-- A runtime-ready closed exit realizes its advertised demand in any semantic
    environment realizing the recursively closed assumptions. -/
theorem StaticExit.RuntimeReady.termAt
    {types slots : Nat → BoundsTy} {ids : List Nat} {sourceRows : Bindings}
    {sourceΔ : List Constraint} {env : List Binding} {rhs : Expr} {actual : BoundsTy}
    {source : ScopedDerives types slots ids sourceRows sourceΔ env rhs actual}
    {outer : Bindings} {f : Nat → BoundsTy} {calleeΔ : List Constraint}
    {demand : BoundsTy} {exit : StaticExit source outer f calleeΔ demand}
    (ready : exit.RuntimeReady)
    (bound free : Runtime.TypeEnv) (σ : Assign)
    (hb : Runtime.TypeEnv.Downward bound) (hf : Runtime.TypeEnv.Downward free)
    (budget : Nat) (premises : ∀ p ∈ calleeΔ, p.Holds σ)
    (e : EnvAt bound free σ budget (closeRecursiveEnv outer f env)) :
    Runtime.TermAt bound free σ budget demand (rhs.substN 0 e.terms) :=
  (ready.typing.termAt bound free σ hb hf budget premises e).of_values
    (Runtime.subtype exit.inclusion ready.typing.supported ready.demandSupported
      bound free σ premises)

/-- Runtime closure follows the exact static exit construction.  The original
    member witness is transported through the protected count/HM maps, while
    support of those maps is supplied by the actual closed-use arguments and
    the enclosing runtime interpretation. -/
def GeneralizedGroup.runtimeExit
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
    (ambientSupported : ∀ i, Runtime.Supported (ambient i)) :
    (GeneralizedGroup.staticExit group offset inside used outer outerFinite target outerScope
      ambient ambientLC ambientScope capturesAgree normal).RuntimeReady := by
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
  have typeSupport : ∀ i, Runtime.Supported (protectedTypes i) :=
    group.protectedTypes_supported offset inside used ambient arguments ambientSupported
  let closed := cert.typing.closeRecursive protectedRows protectedTypes
    rowsFinite target' rowsScoped typesLC target' typesScoped fresh
  have closedReady : ScopedDerives.RuntimeReady closed :=
    RecursiveHMJudgement.RuntimeReady.closeRecursive protectedRows protectedTypes
      rowsFinite target' rowsScoped typesLC target' typesScoped sourceReady fresh typeSupport
  have usable : (⟨calleeΔ,
      s.counts.premises.map (constraint protectedRows)⟩ :
      ForallProblem).Valid := by
    simpa only [s, cert, protectedRows, GeneralizedGroup.protectedRows] using
      HMCountSchemeClosure.closedUse_usable_protected used outer ambient capturesAgree
  have ready := closedReady.assuming usable
  refine ⟨?_, ?_⟩
  · exact ScopedDerives.RuntimeReady.congr ready
  · exact group.protectedDemand_supported offset inside used outer ambient ambientLC
      capturesAgree sourceDemandSupported arguments ambientSupported

end FHM.Bounds.RecursiveHMClosedExit
