import FHM.Bounds.RecursiveHMEnvironment

/-! Caller-context use of universally signed original RHS nodes. Count/HM
arguments are explicit, scope/arity/HM shape and instantiated premises are
checked by `HMCountScheme.check`. Actual RHS evidence and its original written
signature are then transported into the caller's premises. This does not by
itself introduce a recursive group, validate argument expression origins or
prove generalized closure/runtime soundness. -/

namespace FHM.Bounds.RecursiveHMCaller

open RecursiveHMJudgement CountSubstitution ScopedScheme

def sourceFree {annotation quantified captures premises found typeCaptures env rhs sourceTypes sourceSlots}
    (cert : RecursiveHMSigned.Certified annotation quantified captures premises found typeCaptures env rhs sourceTypes sourceSlots)
    {Δ callerFound caller} (used : HMCountScheme.Use cert.interface.scheme Δ callerFound caller) : Nat → BoundsTy :=
  fun i => SchemeSpecialization.mapFree
    (SchemeSpecialization.argument cert.implementation.opening.ids (SchemeUse.vector used.types))
    (bounds (quantified.zip used.counts) (sourceTypes i))

def callerSlots {annotation quantified captures premises found typeCaptures env rhs sourceTypes sourceSlots}
    (cert : RecursiveHMSigned.Certified annotation quantified captures premises found typeCaptures env rhs sourceTypes sourceSlots)
    {Δ callerFound caller} (used : HMCountScheme.Use cert.interface.scheme Δ callerFound caller) : Nat → BoundsTy :=
  fun i => SchemeSpecialization.mapFree
    (SchemeSpecialization.argument cert.implementation.opening.ids (SchemeUse.vector used.types))
    (bounds (quantified.zip used.counts) (sourceSlots i))

structure Result {output path} (node : HMFoundView.AtNode output path)
    {annotation quantified captures premises typeCaptures env sourceTypes sourceSlots}
    (cert : RecursiveHMSigned.Certified annotation quantified captures premises
      (ScopedHMInterpretation.AtNode.view node sourceTypes sourceSlots) typeCaptures
      env node.inner.stripFound sourceTypes sourceSlots)
    {Δ found caller} (used : HMCountScheme.Use cert.interface.scheme Δ found caller)
    (targetEnv : List Binding) where
  checked : RecursiveHMSigned.ScopedNodeChecked node (sourceFree cert used) (callerSlots cert used)
    (quantified ++ captures) (quantified.zip used.counts) Δ
    targetEnv
    caller annotation used.types
  callerShape : Synth.BoundsTy.toTy checked.typed.actual = found.eraseBounds
  inclusion : SemanticSub Δ checked.typed.actual used.bounds

private theorem signature_assuming {ids rows types Δ Δ' annotation actual}
    (h : RecursiveHMSigned.BindingOK ids rows types Δ annotation actual)
    (hp : (⟨Δ', Δ⟩ : ForallProblem).Valid) :
    RecursiveHMSigned.BindingOK ids rows types Δ' annotation actual := by
  obtain ⟨wf, arity, source, decoded, inclusion⟩ := h
  exact ⟨wf, arity, source, decoded, inclusion.assuming hp⟩

/-- Preserve implementation bounds, not just the declared demand, at the
    original source path and the checked caller HM instance. -/
def fromUse {output path} (node : HMFoundView.AtNode output path)
    {annotation quantified captures premises typeCaptures env sourceTypes sourceSlots}
    (cert : RecursiveHMSigned.Certified annotation quantified captures premises
      (ScopedHMInterpretation.AtNode.view node sourceTypes sourceSlots) typeCaptures
      env node.inner.stripFound sourceTypes sourceSlots)
    {Δ found caller} (used : HMCountScheme.Use cert.interface.scheme Δ found caller)
    (captured : RecursiveHMEnvironment.Captured captures env) :
    Result node cert used (RecursiveHMUniversal.typeEnvironment cert.implementation used.types used.typesLC) := by
  rw [← RecursiveHMEnvironment.interpreted cert.implementation used.countInstance captured used.types used.typesLC]
  let base := RecursiveHMSigned.atScopedNode node cert used.countInstance
    used.types used.arity used.typesLC used.typesScoped
  have all := RecursiveHMUniversal.useScopedInterpreted cert.implementation used.countInstance
    used.types used.arity used.typesLC used.typesScoped
  have actual : base.typed.actual = RecursiveHMUniversal.actual cert.implementation used.counts used.types := rfl
  refine ⟨⟨⟨base.typed.actual, base.typed.checked, base.typed.derivation.assuming used.usable⟩,
    signature_assuming base.signature used.usable⟩, ?_, ?_⟩
  · rw [actual, RecursiveHMUniversal.actual_demand_shape]
    exact used.shape
  · rw [actual]
    exact all.2.1.assuming used.usable

structure Checked {output path} (node : HMFoundView.AtNode output path)
    {annotation quantified captures premises typeCaptures env sourceTypes sourceSlots}
    (cert : RecursiveHMSigned.Certified annotation quantified captures premises
      (ScopedHMInterpretation.AtNode.view node sourceTypes sourceSlots) typeCaptures
      env node.inner.stripFound sourceTypes sourceSlots)
    (Δ : List Constraint) (found : Ty) (caller : List Nat) where
  used : HMCountScheme.Use cert.interface.scheme Δ found caller
  result : Result node cert used (RecursiveHMUniversal.typeEnvironment cert.implementation used.types used.typesLC)

def check {output path} (node : HMFoundView.AtNode output path)
    {annotation quantified captures premises typeCaptures env sourceTypes sourceSlots}
    (cert : RecursiveHMSigned.Certified annotation quantified captures premises
      (ScopedHMInterpretation.AtNode.view node sourceTypes sourceSlots) typeCaptures
      env node.inner.stripFound sourceTypes sourceSlots)
    (captured : RecursiveHMEnvironment.Captured captures env)
    (Δ : List Constraint) (found : Ty) (counts : List Count) (types : List BoundsTy) (caller : List Nat) :
    Except String (Checked node cert Δ found caller) := do
  let used ← HMCountScheme.check cert.interface.scheme Δ found counts types caller
  pure ⟨used, fromUse node cert used captured⟩

#print axioms ScopedDerives.assuming
#print axioms RecursiveHMUniversal.actual_demand_shape
#print axioms fromUse
#print axioms check

end FHM.Bounds.RecursiveHMCaller
