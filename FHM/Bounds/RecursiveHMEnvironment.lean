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

private theorem contract_ext {a b : Contract} (template : a.template = b.template)
    (hm : a.hm = b.hm) (types : a.fixed.types = b.fixed.types) : a = b := by
  cases a
  cases b
  cases template
  cases hm
  have h := fixed_ext types
  cases h
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

/-- Uniform source reconciliation must not give each RHS a different recursive
    assumption environment. Check full argument vectors, not just their shape. -/
def TypesFixed (f : Nat → BoundsTy) (env : List Binding) : Prop :=
  (∀ β, .mono β ∈ env → ∀ i ∈ (Synth.BoundsTy.toTy β).freeVars, f i = .fvar i) ∧
    ∀ c, .recursive c ∈ env → c.hm.eraseBounds = c.hm ∧
      ∀ β ∈ c.fixed.types, ∀ i ∈ (Synth.BoundsTy.toTy β).freeVars, f i = .fvar i

private def identityBool (f : Nat → BoundsTy) (i : Nat) : Bool :=
  match f i with | .fvar j => i == j | _ => false

private theorem identityBool_sound {f i} (h : identityBool f i = true) : f i = .fvar i := by
  unfold identityBool at h
  split at h
  · rename_i j he
    have hi : i = j := by simpa using h
    simpa [hi] using he
  · contradiction

private def fixedBoundsBool (f : Nat → BoundsTy) (β : BoundsTy) : Bool :=
  (Synth.BoundsTy.toTy β).freeVars.all (identityBool f)

private theorem fixedBoundsBool_sound {f β} (h : fixedBoundsBool f β = true) :
    ∀ i ∈ (Synth.BoundsTy.toTy β).freeVars, f i = .fvar i := by
  intro i hi
  exact identityBool_sound (List.all_eq_true.mp h i hi)

private def checkTypesFixedBinding (f : Nat → BoundsTy) (b : Binding) :
    Except String (PLift (TypesFixed f [b])) := do
  match b with
  | .mono β =>
      if h : fixedBoundsBool f β = true then
        pure ⟨⟨by
          intro a ha
          have ha : a = β := by simpa using ha
          subst a
          exact fixedBoundsBool_sound h,
          by intro c hc; simp at hc⟩⟩
      else throw "bounds: RHS reconciliation changes a common mono capture"
  | .recursive c =>
      let normal ← match BinderBridge.equalTy c.hm.eraseBounds c.hm with
        | some h => pure h | none => throw "bounds: common recursive HM payload is not erase-normal"
      if h : c.fixed.types.all (fixedBoundsBool f) = true then
        pure ⟨⟨by intro β hβ; simp at hβ, by
          intro d hd
          have hd : d = c := by simpa using hd
          subst d
          exact ⟨normal.down, fun β hβ => fixedBoundsBool_sound (List.all_eq_true.mp h β hβ)⟩⟩⟩
      else throw "bounds: RHS reconciliation changes the common fixed recursive HM vector"

def checkTypesFixed (f : Nat → BoundsTy) (env : List Binding) :
    Except String (PLift (TypesFixed f env)) := do
  match env with
  | [] => pure ⟨⟨by simp, by simp⟩⟩
  | b :: rest =>
      let head ← checkTypesFixedBinding f b
      let tail ← checkTypesFixed f rest
      pure ⟨⟨by
        intro β hβ
        rcases List.mem_cons.mp hβ with hb | ht
        · exact head.down.1 β (by simp [hb])
        · exact tail.down.1 β ht,
        by
        intro c hc
        rcases List.mem_cons.mp hc with hb | ht
        · exact head.down.2 c (by simp [hb])
        · exact tail.down.2 c ht⟩⟩

theorem typesFixed {f env} (hf : ∀ i, (Synth.BoundsTy.toTy (f i)).IsLC)
    (h : TypesFixed f env) : env.map (mapBinding f hf) = env := by
  conv_rhs => rw [← List.map_id env]
  apply List.map_congr_left
  intro b hb
  cases b with
  | mono β => exact congrArg Binding.mono (SchemeSpecialization.fixed (h.1 β hb))
  | recursive c =>
      have ht : c.fixed.types.map (SchemeSpecialization.mapFree f) = c.fixed.types := by
        conv_rhs => rw [← List.map_id c.fixed.types]
        apply List.map_congr_left
        intro β hβ
        exact SchemeSpecialization.fixed ((h.2 c hb).2 β hβ)
      have hm : Synth.BoundsTy.toTy (HMCountScheme.opened c.template c.fixed.types) = c.hm :=
        c.fixed.shape.trans (h.2 c hb).1
      have hc : c.mapTypes f hf = c := by
        apply contract_ext (a := c.mapTypes f hf) (b := c) rfl
        · change Synth.BoundsTy.toTy (HMCountScheme.opened c.template
            (c.fixed.types.map (SchemeSpecialization.mapFree f))) = c.hm
          rw [ht, hm]
        · exact ht
      exact congrArg Binding.recursive hc

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
#print axioms checkTypesFixed
#print axioms typesFixed
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
