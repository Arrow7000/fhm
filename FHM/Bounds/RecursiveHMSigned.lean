import FHM.Bounds.RecursiveHMUniversal

/-! # Written polymorphic signatures backed by universal recursive RHS proofs

Source decoding, HM arity/well-formedness and actual RHS inclusion are explicit.
This is a proof-side polymorphic annotation judgement; the executable group
decoder remains guarded until generalized export and found views are integrated.
-/

namespace FHM.Bounds.RecursiveHMSigned

open CountSubstitution ScopedScheme

def BindingOK (ids : List Nat) (rows : Bindings) (types : List BoundsTy)
    (Δ : List Constraint) (annotation : PolyTy) (actual : BoundsTy) : Prop :=
  annotation.eraseBounds.WF ∧ types.length = annotation.paramCount ∧
    ∃ source : ScopedAnnotation.Decoded ids annotation.body,
      ScopedAnnotation.decode ids annotation.body = .ok source ∧
      SemanticSub Δ actual (TypeSubstitution.combined rows (SchemeUse.vector types) source.bounds)

structure Certified (annotation : PolyTy) (quantified captures : List Nat) (premises : List Constraint)
    (found : Ty) (typeCaptures : List Ty) (env : List RecursiveHMJudgement.Binding) (rhs : Expr)
    (sourceTypes : Nat → BoundsTy := BoundsTy.fvar)
    (sourceSlots : Nat → BoundsTy := BoundsTy.bvar) where
  interface : HMCountScheme.Annotated annotation quantified captures premises
  implementation : RecursiveHMUniversal.Certified interface.scheme found typeCaptures env rhs sourceTypes sourceSlots

/-- The actual RHS meets the written source signature at every count/HM
    instance. In particular, a forall annotation is not accepted from decoding
    an assumption, an HM skeleton comparison, or one chosen primitive instance. -/
theorem signatureInstances {annotation quantified captures premises found typeCaptures env rhs sourceTypes sourceSlots}
    (cert : Certified annotation quantified captures premises found typeCaptures env rhs sourceTypes sourceSlots)
    {counts caller} (inst : Instance cert.interface.scheme.counts counts caller)
    (types : List BoundsTy) (arity : types.length = annotation.paramCount)
    (lc : ∀ a ∈ types, (Synth.BoundsTy.toTy a).IsLC)
    (scope : types.all (boundsScopedBool caller) = true) :
    BindingOK (quantified ++ captures) (quantified.zip counts) types inst.premises annotation
      (RecursiveHMUniversal.actual cert.implementation counts types) := by
  have h := RecursiveHMUniversal.useScopedInterpreted cert.implementation inst types arity lc scope
  exact ⟨cert.interface.hmWF, arity, cert.interface.source.annotation,
    cert.interface.source.decoded, h.2.1⟩

/-- Source agreement and universal implementation evidence stay attached to the
    same template; external specialization cannot silently swap their demands. -/
theorem exactSource {annotation quantified captures premises found typeCaptures env rhs sourceTypes sourceSlots}
    (cert : Certified annotation quantified captures premises found typeCaptures env rhs sourceTypes sourceSlots) :
    cert.interface.scheme.counts.body = cert.interface.source.annotation.bounds := rfl

/-- Exact-node evidence and the source-signature obligation share one actual
    implementation result. A shape view alone cannot inhabit this package. -/
structure NodeChecked {output path} (node : HMFoundView.AtNode output path)
    (interpretation : Nat → BoundsTy) (ids : List Nat) (rows : Bindings)
    (Δ : List Constraint) (env : List RecursiveHMJudgement.Binding) (caller : List Nat)
    (annotation : PolyTy) (types : List BoundsTy) where
  typed : HMFoundView.TypedChecked node interpretation ids rows Δ env caller
  signature : BindingOK ids rows types Δ annotation typed.actual

def atNode {output path} (node : HMFoundView.AtNode output path)
    {annotation quantified captures premises typeCaptures env}
    (cert : Certified annotation quantified captures premises node.original typeCaptures env node.inner.stripFound)
    {counts caller} (inst : Instance cert.interface.scheme.counts counts caller)
    (types : List BoundsTy) (arity : types.length = annotation.paramCount)
    (lc : ∀ a ∈ types, (Synth.BoundsTy.toTy a).IsLC)
    (scope : types.all (boundsScopedBool caller) = true) :
    NodeChecked node
      (SchemeSpecialization.argument cert.implementation.opening.ids (SchemeUse.vector types))
      (quantified ++ captures) (quantified.zip counts) inst.premises
      (RecursiveHMUniversal.interpretedEnvironment cert.implementation counts types lc)
      caller annotation types :=
  ⟨RecursiveHMUniversal.atNode node cert.implementation inst types arity lc scope,
    signatureInstances cert inst types arity lc scope⟩

def atInterpretedNode {output path} (node : HMFoundView.AtNode output path)
    {annotation quantified captures premises typeCaptures env sourceTypes}
    (cert : Certified annotation quantified captures premises (node.view sourceTypes)
      typeCaptures env node.inner.stripFound sourceTypes)
    {counts caller} (inst : Instance cert.interface.scheme.counts counts caller)
    (types : List BoundsTy) (arity : types.length = annotation.paramCount)
    (lc : ∀ a ∈ types, (Synth.BoundsTy.toTy a).IsLC)
    (scope : types.all (boundsScopedBool caller) = true) :
    NodeChecked node
      (fun i => SchemeSpecialization.mapFree
        (SchemeSpecialization.argument cert.implementation.opening.ids (SchemeUse.vector types))
        (CountSubstitution.bounds (quantified.zip counts) (sourceTypes i)))
      (quantified ++ captures) (quantified.zip counts) inst.premises
      (RecursiveHMUniversal.interpretedEnvironment cert.implementation counts types lc)
      caller annotation types :=
  ⟨RecursiveHMUniversal.atInterpretedNode node cert.implementation inst types arity lc scope,
    signatureInstances cert inst types arity lc scope⟩

/-- Scoped node typing and the ORIGINAL written polymorphic signature share
    the same actual implementation result at every full count/HM instance. -/
structure ScopedNodeChecked {output path} (node : HMFoundView.AtNode output path)
    (free slots : Nat → BoundsTy) (ids : List Nat) (rows : Bindings)
    (Δ : List Constraint) (env : List RecursiveHMJudgement.Binding) (caller : List Nat)
    (annotation : PolyTy) (types : List BoundsTy) where
  typed : ScopedHMInterpretation.TypedChecked node free slots ids rows Δ env caller
  signature : BindingOK ids rows types Δ annotation typed.actual

def atScopedNode {output path} (node : HMFoundView.AtNode output path)
    {annotation quantified captures premises typeCaptures env sourceTypes sourceSlots}
    (cert : Certified annotation quantified captures premises
      (ScopedHMInterpretation.AtNode.view node sourceTypes sourceSlots)
      typeCaptures env node.inner.stripFound sourceTypes sourceSlots)
    {counts caller} (inst : Instance cert.interface.scheme.counts counts caller)
    (types : List BoundsTy) (arity : types.length = annotation.paramCount)
    (lc : ∀ a ∈ types, (Synth.BoundsTy.toTy a).IsLC)
    (scope : types.all (boundsScopedBool caller) = true) :
    ScopedNodeChecked node
      (fun i => SchemeSpecialization.mapFree
        (SchemeSpecialization.argument cert.implementation.opening.ids (SchemeUse.vector types))
        (CountSubstitution.bounds (quantified.zip counts) (sourceTypes i)))
      (fun i => SchemeSpecialization.mapFree
        (SchemeSpecialization.argument cert.implementation.opening.ids (SchemeUse.vector types))
        (CountSubstitution.bounds (quantified.zip counts) (sourceSlots i)))
      (quantified ++ captures) (quantified.zip counts) inst.premises
      (RecursiveHMUniversal.interpretedEnvironment cert.implementation counts types lc)
      caller annotation types :=
  ⟨RecursiveHMUniversal.atScopedNode node cert.implementation inst types arity lc scope,
    signatureInstances cert inst types arity lc scope⟩

#print axioms signatureInstances
#print axioms exactSource
#print axioms atNode
#print axioms atInterpretedNode
#print axioms atScopedNode

end FHM.Bounds.RecursiveHMSigned
