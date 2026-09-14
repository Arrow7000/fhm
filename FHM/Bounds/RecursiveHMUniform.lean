import FHM.Bounds.RecursiveHMCaller
import FHM.Bounds.HMDeclaredGroup

/-! Every recursive RHS specializes through ONE uniform full group HM map.
Member counts specialize first. Checked common captures remove that count
transport from the environment; full HM insertion then changes all group vectors
uniformly, including slots unused by this member. Exact implementation and demand
bounds remain separate. Group-body introduction/export remains separate. -/

namespace FHM.Bounds.RecursiveHMUniform

open RecursiveHMJudgement SchemeSpecialization CountSubstitution ScopedScheme

def actual {s found typeCaptures env rhs sourceTypes sourceSlots}
    (cert : RecursiveHMUniversal.Certified s found typeCaptures env rhs sourceTypes sourceSlots)
    (counts : List Count) (f : Nat → BoundsTy) : BoundsTy :=
  mapFree f (bounds (s.counts.quantified.zip counts) cert.actual)

def demand {s found typeCaptures env rhs sourceTypes sourceSlots}
    (cert : RecursiveHMUniversal.Certified s found typeCaptures env rhs sourceTypes sourceSlots)
    (counts : List Count) (f : Nat → BoundsTy) : BoundsTy :=
  mapFree f (bounds (s.counts.quantified.zip counts) cert.opening.bounds)

/-- A member reads precisely its own slots from the uniform group map. Counts
    in those full arguments are inserted after source telescope substitution. -/
theorem demand_instance {s found typeCaptures env rhs sourceTypes sourceSlots}
    (cert : RecursiveHMUniversal.Certified s found typeCaptures env rhs sourceTypes sourceSlots)
    (counts : List Count) (f : Nat → BoundsTy)
    (lc : ∀ i, (Synth.BoundsTy.toTy (f i)).IsLC)
    (fixed : ∀ i ∈ s.hm.body.freeVars, f i = .fvar i) :
    demand cert counts f = TypeSubstitution.combined (s.counts.quantified.zip counts)
      (SchemeUse.vector (cert.opening.ids.map f)) s.counts.body := by
  rw [demand, ← RecursiveHMContract.opaque_count_coherence cert.opening,
    RecursiveHMContract.map_combined s _ _ f lc fixed]
  simp only [RecursiveHMContract.fromOpaque, List.map_map, Function.comp_def, mapFree]

structure Result {s found typeCaptures env rhs sourceTypes sourceSlots}
    (cert : RecursiveHMUniversal.Certified s found typeCaptures env rhs sourceTypes sourceSlots)
    {counts caller} (inst : Instance s.counts counts caller)
    (f : Nat → BoundsTy) (lc : ∀ i, (Synth.BoundsTy.toTy (f i)).IsLC) where
  typing : ScopedDerives
    (fun i => mapFree f (bounds (s.counts.quantified.zip counts) (sourceTypes i)))
    (fun i => mapFree f (bounds (s.counts.quantified.zip counts) (sourceSlots i)))
    (s.counts.quantified ++ s.counts.captures) (s.counts.quantified.zip counts)
    inst.premises (env.map (mapBinding f lc)) rhs (actual cert counts f)
  inclusion : SemanticSub inst.premises (actual cert counts f) (demand cert counts f)
  inScope : BoundsScoped caller (actual cert counts f)

/-- Unlike member-local HM vectors, `f` is the SAME function for every member
    of a group. Its full arguments are inserted only AFTER member count rows. -/
def fromCertified {s found typeCaptures env rhs sourceTypes sourceSlots}
    (cert : RecursiveHMUniversal.Certified s found typeCaptures env rhs sourceTypes sourceSlots)
    {counts caller} (inst : Instance s.counts counts caller)
    (f : Nat → BoundsTy) (lc : ∀ i, (Synth.BoundsTy.toTy (f i)).IsLC)
    (scope : ∀ i, BoundsScoped caller (f i))
    (captured : RecursiveHMEnvironment.Captured s.counts.captures env)
    (fixed : CapturesFixed f env) : Result cert inst f lc := by
  let rows := s.counts.quantified.zip counts
  have countKeep : CountCapturesFixed rows env := by
    intro c hc i hi
    apply lookup_none
    rw [List.map_fst_zip (Nat.le_of_eq inst.arity)]
    exact cert.countFresh c hc i hi
  have typeKeep : CapturesFixed f (env.map (mapCountBinding rows)) := by
    intro c hc i hi
    obtain ⟨original, ho, he⟩ := List.mem_map.mp hc
    cases original with
    | mono β => cases he
    | recursive original =>
        cases he
        exact fixed original ho i hi
  have hc := transportScopedCounts rows inst.finite caller
    (fun row hr => inst.argsScoped row.2 (List.of_mem_zip hr).2) cert.typing countKeep
  have ht := transportScopedTypes f lc caller scope hc typeKeep
  have envFixed := RecursiveHMEnvironment.instantiated inst captured
  have countScope : BoundsScoped caller (bounds rows cert.actual) := by
    apply bounds_scoped cert.actualScope
      (fun row hr => inst.argsScoped row.2 (List.of_mem_zip hr).2)
    intro i hi hn
    rcases List.mem_append.mp hi with hq | hcap
    · have absent := lookup_none_iff.mp hn
      rw [List.map_fst_zip (Nat.le_of_eq inst.arity)] at absent
      exact (absent hq).elim
    · exact inst.capturesScoped i hcap
  refine ⟨?_, SchemeSpecialization.subtype f (inst.subtype cert.inclusion), ?_⟩
  · simpa only [actual, rows, envFixed, CountAlgebra.compose, List.map_nil,
      List.nil_append, ScopedScheme.Instance.premises] using ht
  · exact HMInterpretation.scope_mono (HMInterpretation.map_scope countScope f scope)
      (fun _ hi => (List.mem_append.mp hi).elim id id)

def Result.assuming {s found typeCaptures env rhs sourceTypes sourceSlots}
    {cert : RecursiveHMUniversal.Certified s found typeCaptures env rhs sourceTypes sourceSlots}
    {counts caller} {inst : Instance s.counts counts caller} {f lc}
    (r : Result cert inst f lc) {Δ}
    (premises : inst.Usable Δ) :
    ScopedDerives
      (fun i => mapFree f (bounds (s.counts.quantified.zip counts) (sourceTypes i)))
      (fun i => mapFree f (bounds (s.counts.quantified.zip counts) (sourceSlots i)))
      (s.counts.quantified ++ s.counts.captures) (s.counts.quantified.zip counts)
      Δ (env.map (mapBinding f lc)) rhs (actual cert counts f) ∧
    SemanticSub Δ (actual cert counts f) (demand cert counts f) :=
  ⟨r.typing.assuming premises, r.inclusion.assuming premises⟩

theorem Result.signature {annotation quantified captures premises found typeCaptures env rhs sourceTypes sourceSlots}
    (cert : RecursiveHMSigned.Certified annotation quantified captures premises found typeCaptures env rhs sourceTypes sourceSlots)
    {counts caller} {inst : Instance cert.interface.scheme.counts counts caller} {f lc}
    (r : Result cert.implementation inst f lc)
    (fixed : ∀ i ∈ cert.interface.scheme.hm.body.freeVars, f i = .fvar i) :
    RecursiveHMSigned.BindingOK (quantified ++ captures) (quantified.zip counts)
      (cert.implementation.opening.ids.map f) inst.premises annotation (actual cert.implementation counts f) := by
  refine ⟨cert.interface.hmWF, ?_, cert.interface.source.annotation,
    cert.interface.source.decoded, ?_⟩
  · simpa using cert.implementation.opening.arity
  · change SemanticSub inst.premises (actual cert.implementation counts f)
      (TypeSubstitution.combined (cert.interface.scheme.counts.quantified.zip counts)
        (SchemeUse.vector (cert.implementation.opening.ids.map f)) cert.interface.scheme.counts.body)
    rw [← demand_instance cert.implementation counts f lc fixed]
    exact r.inclusion

def atNode {output path} (node : HMFoundView.AtNode output path)
    {s typeCaptures env sourceTypes sourceSlots}
    (cert : RecursiveHMUniversal.Certified s
      (ScopedHMInterpretation.AtNode.view node sourceTypes sourceSlots) typeCaptures
      env node.inner.stripFound sourceTypes sourceSlots)
    {counts caller} {inst : Instance s.counts counts caller} {f lc}
    (r : Result cert inst f lc) :
    ScopedHMInterpretation.TypedChecked node
      (fun i => mapFree f (bounds (s.counts.quantified.zip counts) (sourceTypes i)))
      (fun i => mapFree f (bounds (s.counts.quantified.zip counts) (sourceSlots i)))
      (s.counts.quantified ++ s.counts.captures) (s.counts.quantified.zip counts)
      inst.premises (env.map (mapBinding f lc)) caller := by
  refine ⟨actual cert counts f, ⟨?_, r.inScope⟩, r.typing⟩
  rw [actual, HMFoundView.bounds_shape, bounds_shape, cert.shape]
  exact ScopedHMInterpretation.specialization f sourceTypes sourceSlots _ node.original

def atSignedNode {output path} (node : HMFoundView.AtNode output path)
    {annotation quantified captures premises typeCaptures env sourceTypes sourceSlots}
    (cert : RecursiveHMSigned.Certified annotation quantified captures premises
      (ScopedHMInterpretation.AtNode.view node sourceTypes sourceSlots) typeCaptures
      env node.inner.stripFound sourceTypes sourceSlots)
    {counts caller} {inst : Instance cert.interface.scheme.counts counts caller} {f lc}
    (r : Result cert.implementation inst f lc)
    (fixed : ∀ i ∈ cert.interface.scheme.hm.body.freeVars, f i = .fvar i) :
    RecursiveHMSigned.ScopedNodeChecked node
      (fun i => mapFree f (bounds (quantified.zip counts) (sourceTypes i)))
      (fun i => mapFree f (bounds (quantified.zip counts) (sourceSlots i)))
      (quantified ++ captures) (quantified.zip counts) inst.premises
      (env.map (mapBinding f lc)) caller annotation (cert.implementation.opening.ids.map f) :=
  ⟨atNode node cert.implementation r, r.signature cert fixed⟩

/-- Ordered ALL-member universal obligations have one common specialized
    recursive environment, not a family of independently mapped assumptions. -/
inductive Members {output metadata path captures premises typeCaptures env}
    (f : Nat → BoundsTy) (lc : ∀ i, (Synth.BoundsTy.toTy (f i)).IsLC)
    (scope : ∀ i, BoundsScoped caller (f i)) :
    {index : Nat} → {vectors : List (List Nat)} →
    {ps : HMDeclaredGroup.Interfaces output metadata path captures premises typeCaptures index vectors} →
    HMDeclaredGroup.CheckedMembers env ps → Type where
  | nil {index} : Members f lc scope (HMDeclaredGroup.CheckedMembers.nil (index := index))
  | cons {index ids rest}
      {p : HMDeclaredGroup.Member output metadata path index captures premises typeCaptures}
      {tail : HMDeclaredGroup.Interfaces output metadata path captures premises typeCaptures (index + 1) rest}
      {he : p.reconciled.signatureIds = ids}
      {head : HMDeclaredGroup.MemberChecked p env} {ms : HMDeclaredGroup.CheckedMembers env tail} :
      (∀ counts (inst : Instance head.certificate.interface.scheme.counts counts caller),
        Result head.certificate.implementation inst f lc) →
      Members f lc scope ms → Members f lc scope (.cons (he := he) head ms)

def allMembers {output metadata path captures premises typeCaptures env index vectors caller}
    {ps : HMDeclaredGroup.Interfaces output metadata path captures premises typeCaptures index vectors}
    (ms : HMDeclaredGroup.CheckedMembers env ps)
    (f : Nat → BoundsTy) (lc : ∀ i, (Synth.BoundsTy.toTy (f i)).IsLC)
    (scope : ∀ i, BoundsScoped caller (f i)) (fixed : CapturesFixed f env) : Members f lc scope ms :=
  match ms with
  | .nil => .nil
  | .cons head rest =>
      .cons (fun _ inst => fromCertified head.certificate.implementation inst f lc scope head.captured fixed)
        (allMembers rest f lc scope fixed)

#print axioms fromCertified
#print axioms demand_instance
#print axioms Result.assuming
#print axioms Result.signature
#print axioms atSignedNode
#print axioms allMembers

end FHM.Bounds.RecursiveHMUniform
