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
    (found : Ty) (typeCaptures : List Ty) (env : List RecursiveHMJudgement.Binding) (rhs : Expr) where
  interface : HMCountScheme.Annotated annotation quantified captures premises
  implementation : RecursiveHMUniversal.Certified interface.scheme found typeCaptures env rhs

/-- The actual RHS meets the written source signature at every count/HM
    instance. In particular, a forall annotation is not accepted from decoding
    an assumption, an HM skeleton comparison, or one chosen primitive instance. -/
theorem signatureInstances {annotation quantified captures premises found typeCaptures env rhs}
    (cert : Certified annotation quantified captures premises found typeCaptures env rhs)
    {counts caller} (inst : Instance cert.interface.scheme.counts counts caller)
    (types : List BoundsTy) (arity : types.length = annotation.paramCount)
    (lc : ∀ a ∈ types, (Synth.BoundsTy.toTy a).IsLC)
    (scope : types.all (boundsScopedBool caller) = true) :
    BindingOK (quantified ++ captures) (quantified.zip counts) types inst.premises annotation
      (RecursiveHMUniversal.actual cert.implementation counts types) := by
  have h := RecursiveHMUniversal.use cert.implementation inst types arity lc scope
  exact ⟨cert.interface.hmWF, arity, cert.interface.source.annotation,
    cert.interface.source.decoded, h.2.1⟩

/-- Source agreement and universal implementation evidence stay attached to the
    same template; external specialization cannot silently swap their demands. -/
theorem exactSource {annotation quantified captures premises found typeCaptures env rhs}
    (cert : Certified annotation quantified captures premises found typeCaptures env rhs) :
    cert.interface.scheme.counts.body = cert.interface.source.annotation.bounds := rfl

#print axioms signatureInstances
#print axioms exactSource

end FHM.Bounds.RecursiveHMSigned
