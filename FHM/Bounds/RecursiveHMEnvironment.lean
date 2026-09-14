import FHM.Bounds.RecursiveHMSigned

/-! Count-environment reconciliation for joint recursive HM/count certificates.
The callee's fixed HM vector initially contains opaque HM identities and captured
counts, not the current member's universally instantiated count coordinates.
That property must be proved before erasing an environment transport from `use`.
-/

namespace FHM.Bounds.RecursiveHMEnvironment

open RecursiveHMJudgement CountSubstitution ScopedScheme

private theorem fixed_ext {s found} {a b : RecursiveHMContract.Fixed s found}
    (types : a.types = b.types) : a = b := by
  cases a
  cases b
  cases types
  rfl

def Captured (ids : List Nat) (env : List RecursiveHMJudgement.Binding) : Prop :=
  (∀ β, .mono β ∈ env → BoundsScoped ids β) ∧
    ∀ c, .recursive c ∈ env → ∀ β ∈ c.fixed.types, BoundsScoped ids β

/-- Validate the common environment BEFORE full caller HM insertion. Counts
    in closed callee telescopes are not fixed-argument counts and are ignored. -/
def capturedBool (ids : List Nat) (env : List RecursiveHMJudgement.Binding) : Bool :=
  env.all fun b => match b with
    | .mono β => boundsScopedBool ids β
    | .recursive c => c.fixed.types.all (boundsScopedBool ids)

theorem capturedBool_sound {ids env} (h : capturedBool ids env = true) : Captured ids env := by
  constructor
  · intro β hβ
    exact boundsScopedBool_sound (List.all_eq_true.mp h (.mono β) hβ)
  · intro c hc β hβ
    exact boundsScopedBool_sound (List.all_eq_true.mp (List.all_eq_true.mp h (.recursive c) hc) β hβ)

def checkCaptured (ids : List Nat) (env : List RecursiveHMJudgement.Binding) :
    Except String (PLift (Captured ids env)) :=
  if h : capturedBool ids env = true then .ok ⟨capturedBool_sound h⟩
  else .error "bounds: common recursive fixed HM arguments or mono captures depend on member-local counts"

/-- Callee templates need not be count-substituted to instantiate one member's
    RHS. The fixed HM vector remains unchanged when its counts are captures. -/
theorem fixed (rows : Bindings) {ids env} (captures : Captured ids env)
    (keep : ∀ i ∈ ids, lookup rows i = none) : env.map (mapCountBinding rows) = env := by
  conv_rhs => rw [← List.map_id env]
  apply List.map_congr_left
  intro b hb
  cases b with
  | mono β => exact congrArg Binding.mono (CountTransport.bounds_fixed rows (captures.1 β hb) keep)
  | recursive c =>
      have hv : c.fixed.mapCounts rows = c.fixed := by
        apply fixed_ext
        change c.fixed.types.map (bounds rows) = c.fixed.types
        conv_rhs => rw [← List.map_id c.fixed.types]
        apply List.map_congr_left
        intro β hβ
        exact CountTransport.bounds_fixed rows (captures.2 c hb β hβ) keep
      change Binding.recursive ⟨c.template, c.hm, c.fixed.mapCounts rows⟩ = Binding.recursive c
      rw [hv]

/-- A member's scoped finite instantiation leaves the common recursive count
    environment intact when the group has checked the captured-vector property. -/
theorem instantiated {s : ScopedScheme.Scheme} {counts caller env}
    (inst : Instance s counts caller) (captures : Captured s.captures env) :
    env.map (mapCountBinding (s.quantified.zip counts)) = env := by
  apply fixed _ captures
  intro i hi
  apply lookup_none
  rw [List.map_fst_zip (Nat.le_of_eq inst.arity)]
  exact inst.wf.2.1 i hi

/-- Captured-vector evidence is automatic for opaque HM openings; source
    count interval payloads stay in their closed template, not in the vector. -/
theorem opaqueVector {s found typeCaptures} (o : HMCountScheme.Opening s found typeCaptures)
    (ids : List Nat) : ∀ β ∈ (RecursiveHMContract.fromOpaque o).types, BoundsScoped ids β := by
  intro β hβ
  obtain ⟨i, _, rfl⟩ := List.mem_map.mp hβ
  trivial

/-- Universal RHS transport uses the SAME common recursive environment, with
    only its uniform HM interpretation, once captured-vector scope is checked.
    No closed callee contract or independent per-call HM vector is rewritten. -/
theorem interpreted {s found typeCaptures env rhs sourceTypes sourceSlots}
    (cert : RecursiveHMUniversal.Certified s found typeCaptures env rhs sourceTypes sourceSlots)
    {counts caller} (inst : Instance s.counts counts caller)
    (captures : Captured s.counts.captures env) (types : List BoundsTy)
    (lc : ∀ a ∈ types, (Synth.BoundsTy.toTy a).IsLC) :
    RecursiveHMUniversal.interpretedEnvironment cert counts types lc =
      RecursiveHMUniversal.typeEnvironment cert types lc := by
  unfold RecursiveHMUniversal.interpretedEnvironment RecursiveHMUniversal.typeEnvironment
  rw [instantiated inst captures]

def atNode {output path} (node : HMFoundView.AtNode output path) {s typeCaptures env}
    (cert : RecursiveHMUniversal.Certified s node.original typeCaptures env node.inner.stripFound)
    {counts caller} (inst : Instance s.counts counts caller)
    (captures : Captured s.counts.captures env) (types : List BoundsTy)
    (arity : types.length = s.hm.paramCount)
    (lc : ∀ a ∈ types, (Synth.BoundsTy.toTy a).IsLC)
    (scope : types.all (boundsScopedBool caller) = true) :
    HMFoundView.TypedChecked node (SchemeSpecialization.argument cert.opening.ids (SchemeUse.vector types))
      (s.counts.quantified ++ s.counts.captures) (s.counts.quantified.zip counts) inst.premises
      (RecursiveHMUniversal.typeEnvironment cert types lc) caller := by
  have checked := RecursiveHMUniversal.atNode node cert inst types arity lc scope
  rw [interpreted cert inst captures types lc] at checked
  exact checked

def atInterpretedNode {output path} (node : HMFoundView.AtNode output path)
    {s typeCaptures env sourceTypes}
    (cert : RecursiveHMUniversal.Certified s (node.view sourceTypes) typeCaptures
      env node.inner.stripFound sourceTypes)
    {counts caller} (inst : Instance s.counts counts caller)
    (captures : Captured s.counts.captures env) (types : List BoundsTy)
    (arity : types.length = s.hm.paramCount)
    (lc : ∀ a ∈ types, (Synth.BoundsTy.toTy a).IsLC)
    (scope : types.all (boundsScopedBool caller) = true) :
    HMFoundView.TypedChecked node
      (fun i => SchemeSpecialization.mapFree
        (SchemeSpecialization.argument cert.opening.ids (SchemeUse.vector types))
        (bounds (s.counts.quantified.zip counts) (sourceTypes i)))
      (s.counts.quantified ++ s.counts.captures) (s.counts.quantified.zip counts) inst.premises
      (RecursiveHMUniversal.typeEnvironment cert types lc) caller := by
  have checked := RecursiveHMUniversal.atInterpretedNode node cert inst types arity lc scope
  rw [interpreted cert inst captures types lc] at checked
  exact checked

def atScopedNode {output path} (node : HMFoundView.AtNode output path)
    {s typeCaptures env sourceTypes sourceSlots}
    (cert : RecursiveHMUniversal.Certified s
      (ScopedHMInterpretation.AtNode.view node sourceTypes sourceSlots) typeCaptures
      env node.inner.stripFound sourceTypes sourceSlots)
    {counts caller} (inst : Instance s.counts counts caller)
    (captures : Captured s.counts.captures env) (types : List BoundsTy)
    (arity : types.length = s.hm.paramCount)
    (lc : ∀ a ∈ types, (Synth.BoundsTy.toTy a).IsLC)
    (scope : types.all (boundsScopedBool caller) = true) :
    ScopedHMInterpretation.TypedChecked node
      (fun i => SchemeSpecialization.mapFree
        (SchemeSpecialization.argument cert.opening.ids (SchemeUse.vector types))
        (bounds (s.counts.quantified.zip counts) (sourceTypes i)))
      (fun i => SchemeSpecialization.mapFree
        (SchemeSpecialization.argument cert.opening.ids (SchemeUse.vector types))
        (bounds (s.counts.quantified.zip counts) (sourceSlots i)))
      (s.counts.quantified ++ s.counts.captures) (s.counts.quantified.zip counts) inst.premises
      (RecursiveHMUniversal.typeEnvironment cert types lc) caller := by
  have checked := RecursiveHMUniversal.atScopedNode node cert inst types arity lc scope
  rw [interpreted cert inst captures types lc] at checked
  exact checked

def atScopedSignedNode {output path} (node : HMFoundView.AtNode output path)
    {annotation quantified captured premises typeCaptures env sourceTypes sourceSlots}
    (cert : RecursiveHMSigned.Certified annotation quantified captured premises
      (ScopedHMInterpretation.AtNode.view node sourceTypes sourceSlots) typeCaptures
      env node.inner.stripFound sourceTypes sourceSlots)
    {counts caller} (inst : Instance cert.interface.scheme.counts counts caller)
    (captures : Captured captured env) (types : List BoundsTy)
    (arity : types.length = annotation.paramCount)
    (lc : ∀ a ∈ types, (Synth.BoundsTy.toTy a).IsLC)
    (scope : types.all (boundsScopedBool caller) = true) :
    RecursiveHMSigned.ScopedNodeChecked node
      (fun i => SchemeSpecialization.mapFree
        (SchemeSpecialization.argument cert.implementation.opening.ids (SchemeUse.vector types))
        (bounds (quantified.zip counts) (sourceTypes i)))
      (fun i => SchemeSpecialization.mapFree
        (SchemeSpecialization.argument cert.implementation.opening.ids (SchemeUse.vector types))
        (bounds (quantified.zip counts) (sourceSlots i)))
      (quantified ++ captured) (quantified.zip counts) inst.premises
      (RecursiveHMUniversal.typeEnvironment cert.implementation types lc) caller annotation types := by
  have checked := RecursiveHMSigned.atScopedNode node cert inst types arity lc scope
  rw [interpreted cert.implementation inst captures types lc] at checked
  exact checked

#print axioms capturedBool_sound
#print axioms checkCaptured
#print axioms fixed
#print axioms instantiated
#print axioms opaqueVector
#print axioms interpreted
#print axioms atNode
#print axioms atInterpretedNode
#print axioms atScopedNode
#print axioms atScopedSignedNode

end FHM.Bounds.RecursiveHMEnvironment
