import FHM.Bounds.CountTransport

/-! # Checked use of an RHS-certified HM/count contract

Quantified counts are distinct from captured environment counts. A declaration
certificate requires actual universal RHS typing; scope/shape decoding alone is
not enough. Count specialization precedes insertion of caller HM-slot bounds,
and every instantiated premise must be discharged in the caller's context.

This is a certified-use component, not a declaration synthesizer or a new
recursive rule. The RHS judgement still supports only ground carried annotation
demands. CLI/LSP integration and runtime bounds soundness remain separate work.
-/

namespace FHM.Bounds.CountContract

open SchemeTyping CountSubstitution

structure Certified (env : List Binding) (rhs : Expr) where
  hm : SchemeTyping.Scheme
  counts : ScopedScheme.Scheme
  body : counts.body = hm.body
  wf : counts.WF
  captureScope : ∀ b ∈ env, CountTransport.BindingScoped counts.captures b
  typing : ∀ args, hm.Arguments args → Derives counts.premises env rhs (hm.instantiate args)

private theorem captured_lookup {env rhs} (c : Certified env rhs) {args caller}
    (inst : ScopedScheme.Instance c.counts args caller) :
    ∀ i ∈ c.counts.captures, lookup (c.counts.quantified.zip args) i = none := by
  intro i hi
  apply ScopedScheme.lookup_none
  rw [List.map_fst_zip (Nat.le_of_eq inst.arity)]
  exact c.wf.2.1 i hi

/-- The quantified declaration is specialized without rewriting count names in
    arbitrary caller HM arguments, even when those names coincide. -/
theorem use {env rhs} (c : Certified env rhs) {counts caller Δ}
    (inst : ScopedScheme.Instance c.counts counts caller) (hu : inst.Usable Δ)
    (args : List BoundsTy) (ha : c.hm.Arguments args) :
    Derives Δ env rhs
      (TypeSubstitution.combined (c.counts.quantified.zip counts) (SchemeUse.vector args) c.hm.body) := by
  have hall := CountTransport.universal_from
    (fun rows hf Δ env β h => CountTransport.transport rows hf h)
    (c.counts.quantified.zip counts) inst.finite c.typing args ha
  have envFixed := CountTransport.env_fixed _ c.captureScope (captured_lookup c inst)
  rw [envFixed] at hall
  exact CountTransport.assuming hall hu

structure Result (Δ : List Constraint) (env : List Binding) (rhs : Expr)
    (found : Ty) (caller : List Nat) where
  bounds : BoundsTy
  derivation : Derives Δ env rhs bounds
  shape : Synth.BoundsTy.toTy bounds = found.eraseBounds
  countScope : ScopedScheme.BoundsScoped caller bounds

/-- Caller type arguments carry full bounds, not HM-derived approximations.
    Exact relational HM instance checks precede use; origin typing is the
    consuming application rule's responsibility. -/
def check {env rhs} (c : Certified env rhs) (Δ : List Constraint) (found : Ty)
    (counts : List Count) (args : List BoundsTy) (caller : List Nat) :
    Except String (Result Δ env rhs found caller) := do
  let inst ← c.counts.instantiate counts caller
  let usable ← inst.checkPremises Δ
  let hmUse ← BinderBridge.instantiate c.hm.hm found
  let shapes ← match BinderBridge.equalTys (args.map Synth.BoundsTy.toTy) hmUse.args with
    | none => throw "bounds: count-contract type arguments disagree with HM instance"
    | some shapes => pure shapes
  if hlc : args.all (fun a => (Synth.BoundsTy.toTy a).bvarsBelow 0) = true then
    if hs : args.all (ScopedScheme.boundsScopedBool caller) = true then
      have arguments : c.hm.Arguments args := ⟨by rw [shapes.down]; exact hmUse.arity, by
        intro t ht
        obtain ⟨a, ha, rfl⟩ := List.mem_map.mp ht
        exact (Ty.bvarsBelow_iff (Synth.BoundsTy.toTy a)).mp (List.all_eq_true.mp hlc a ha)⟩
      let specialized := TypeSubstitution.combined (c.counts.quantified.zip counts)
        (SchemeUse.vector args) c.hm.body
      have shape : Synth.BoundsTy.toTy specialized = found.eraseBounds := by
        rw [TypeSubstitution.combined_shape, c.hm.erasedShape]
        exact TypeSubstitution.hm_instance hmUse.witness _ (fun _ _ hi => SchemeUse.vector_shape shapes.down hi)
      have scope : ScopedScheme.BoundsScoped caller specialized := by
        dsimp only [specialized]
        rw [← c.body]
        exact TypeSubstitution.instance_inScope inst _ (SchemeUse.vector_scope hs)
      pure ⟨specialized, use c inst usable.down args arguments, shape, scope⟩
    else throw "bounds: count-contract HM argument counts are outside caller scope"
  else throw "bounds: count-contract HM arguments contain an enclosing bound slot"

#print axioms use
#print axioms check

end FHM.Bounds.CountContract
