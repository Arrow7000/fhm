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

private theorem closed_ext {a b : RecursiveHMContract.Closed}
    (source : a.source = b.source)
    (fixedTypes : a.fixedTypes = b.fixedTypes)
    (countCaptures : a.countCaptures = b.countCaptures)
    (typeCaptures : a.typeCaptures = b.typeCaptures) : a = b := by
  cases a
  cases b
  cases source
  cases fixedTypes
  cases countCaptures
  cases typeCaptures
  rfl

structure Captured (ids : List Nat) (env : List RecursiveHMJudgement.Binding) : Prop where
  mono : ∀ β, .mono β ∈ env → BoundsScoped ids β
  recursive : ∀ c, .recursive c ∈ env → ∀ β ∈ c.fixed.types, BoundsScoped ids β
  recursiveClosureFixedTypes : ∀ c, .recursiveClosure c ∈ env →
    ∀ β ∈ c.fixedTypes, BoundsScoped ids β
  recursiveClosureCounts : ∀ c, .recursiveClosure c ∈ env →
    ∀ count ∈ c.countCaptures, Scope.CountScoped ids count
  recursiveClosureTypeCaptures : ∀ c, .recursiveClosure c ∈ env →
    ∀ β ∈ c.typeCaptures, BoundsScoped ids β
  closureCounts : ∀ s countCaptures typeCaptures,
    .closure s countCaptures typeCaptures ∈ env →
      ∀ c ∈ countCaptures, Scope.CountScoped ids c
  closureTypes : ∀ s countCaptures typeCaptures,
    .closure s countCaptures typeCaptures ∈ env →
      ∀ β ∈ typeCaptures, BoundsScoped ids β

/-- Validate the common environment BEFORE full caller HM insertion. Counts
    in closed callee telescopes are not fixed-argument counts and are ignored. -/
def capturedBool (ids : List Nat) (env : List RecursiveHMJudgement.Binding) : Bool :=
  env.all fun b => match b with
    | .mono β => boundsScopedBool ids β
    | .recursive c => c.fixed.types.all (boundsScopedBool ids)
    | .recursiveClosure c =>
        (c.fixedTypes.all (boundsScopedBool ids) &&
          c.countCaptures.all (countScopedBool ids)) &&
            c.typeCaptures.all (boundsScopedBool ids)
    | .exported _ => true
    | .closure _ countCaptures typeCaptures =>
        countCaptures.all (countScopedBool ids) &&
          typeCaptures.all (boundsScopedBool ids)

theorem capturedBool_sound {ids env} (h : capturedBool ids env = true) : Captured ids env := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro β hβ
    exact boundsScopedBool_sound (List.all_eq_true.mp h (.mono β) hβ)
  · intro c hc β hβ
    exact boundsScopedBool_sound (List.all_eq_true.mp (List.all_eq_true.mp h (.recursive c) hc) β hβ)
  · intro c hc β hβ
    have both := List.all_eq_true.mp h (.recursiveClosure c) hc
    have all : (c.fixedTypes.all (boundsScopedBool ids) = true ∧
        c.countCaptures.all (countScopedBool ids) = true) ∧
          c.typeCaptures.all (boundsScopedBool ids) = true := by
      simpa only [Bool.and_eq_true] using both
    exact boundsScopedBool_sound (List.all_eq_true.mp all.1.1 β hβ)
  · intro c hc count hcount
    have both := List.all_eq_true.mp h (.recursiveClosure c) hc
    have all : (c.fixedTypes.all (boundsScopedBool ids) = true ∧
        c.countCaptures.all (countScopedBool ids) = true) ∧
          c.typeCaptures.all (boundsScopedBool ids) = true := by
      simpa only [Bool.and_eq_true] using both
    exact countScopedBool_sound (List.all_eq_true.mp all.1.2 count hcount)
  · intro c hc β hβ
    have both := List.all_eq_true.mp h (.recursiveClosure c) hc
    have all : (c.fixedTypes.all (boundsScopedBool ids) = true ∧
        c.countCaptures.all (countScopedBool ids) = true) ∧
          c.typeCaptures.all (boundsScopedBool ids) = true := by
      simpa only [Bool.and_eq_true] using both
    exact boundsScopedBool_sound (List.all_eq_true.mp all.2 β hβ)
  · intro s countCaptures typeCaptures member c hc
    have both := List.all_eq_true.mp h (.closure s countCaptures typeCaptures) member
    have both' : countCaptures.all (countScopedBool ids) = true ∧
        typeCaptures.all (boundsScopedBool ids) = true := by
      simpa only [Bool.and_eq_true] using both
    exact countScopedBool_sound
      (List.all_eq_true.mp both'.1 c hc)
  · intro s countCaptures typeCaptures member β hβ
    have both := List.all_eq_true.mp h (.closure s countCaptures typeCaptures) member
    have both' : countCaptures.all (countScopedBool ids) = true ∧
        typeCaptures.all (boundsScopedBool ids) = true := by
      simpa only [Bool.and_eq_true] using both
    exact boundsScopedBool_sound
      (List.all_eq_true.mp both'.2 β hβ)

def checkCaptured (ids : List Nat) (env : List RecursiveHMJudgement.Binding) :
    Except String (PLift (Captured ids env)) :=
  if h : capturedBool ids env = true then .ok ⟨capturedBool_sound h⟩
  else .error "bounds: common recursive fixed HM arguments or mono captures depend on member-local counts"

/-- Uniform source reconciliation must not give each RHS a different recursive
    assumption environment. Check full argument vectors, not just their shape. -/
structure TypesFixed (f : Nat → BoundsTy) (env : List Binding) : Prop where
  mono : ∀ β, .mono β ∈ env →
    ∀ i ∈ (Synth.BoundsTy.toTy β).freeVars, f i = .fvar i
  recursive : ∀ c, .recursive c ∈ env → c.hm.eraseBounds = c.hm ∧
    ∀ β ∈ c.fixed.types, ∀ i ∈ (Synth.BoundsTy.toTy β).freeVars, f i = .fvar i
  recursiveClosureFixedTypes : ∀ c, .recursiveClosure c ∈ env →
    ∀ β ∈ c.fixedTypes, ∀ i ∈ (Synth.BoundsTy.toTy β).freeVars, f i = .fvar i
  recursiveClosureCaptures : ∀ c, .recursiveClosure c ∈ env →
    ∀ β ∈ c.typeCaptures, ∀ i ∈ (Synth.BoundsTy.toTy β).freeVars, f i = .fvar i
  closure : ∀ s countCaptures typeCaptures,
    .closure s countCaptures typeCaptures ∈ env →
      ∀ β ∈ typeCaptures, ∀ i ∈ (Synth.BoundsTy.toTy β).freeVars, f i = .fvar i

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
        pure ⟨{
          mono := by
            intro a ha
            have ha : a = β := by simpa using ha
            subst a
            exact fixedBoundsBool_sound h
          recursive := by intro c hc; simp at hc
          recursiveClosureFixedTypes := by intro c hc; simp at hc
          recursiveClosureCaptures := by intro c hc; simp at hc
          closure := by intro s countCaptures typeCaptures member; simp at member }⟩
      else throw "bounds: RHS reconciliation changes a common mono capture"
  | .recursive c =>
      let normal ← match BinderBridge.equalTy c.hm.eraseBounds c.hm with
        | some h => pure h | none => throw "bounds: common recursive HM payload is not erase-normal"
      if h : c.fixed.types.all (fixedBoundsBool f) = true then
        pure ⟨{
          mono := by intro β hβ; simp at hβ
          recursive := by
            intro d hd
            have hd : d = c := by simpa using hd
            subst d
            exact ⟨normal.down, fun β hβ => fixedBoundsBool_sound (List.all_eq_true.mp h β hβ)⟩
          recursiveClosureFixedTypes := by intro d hd; simp at hd
          recursiveClosureCaptures := by intro d hd; simp at hd
          closure := by intro s countCaptures typeCaptures member; simp at member }⟩
      else throw "bounds: RHS reconciliation changes the common fixed recursive HM vector"
  | .recursiveClosure c =>
      if h : (c.fixedTypes.all (fixedBoundsBool f) &&
          c.typeCaptures.all (fixedBoundsBool f)) = true then
        pure ⟨{
          mono := by intro β hβ; simp at hβ
          recursive := by intro d hd; simp at hd
          recursiveClosureFixedTypes := by
            intro d hd β hβ
            have same : d = c := by simpa using hd
            subst d
            have both : c.fixedTypes.all (fixedBoundsBool f) = true ∧
                c.typeCaptures.all (fixedBoundsBool f) = true := by
              simpa only [Bool.and_eq_true] using h
            exact fixedBoundsBool_sound (List.all_eq_true.mp both.1 β hβ)
          recursiveClosureCaptures := by
            intro d hd β hβ
            have same : d = c := by simpa using hd
            subst d
            have both : c.fixedTypes.all (fixedBoundsBool f) = true ∧
                c.typeCaptures.all (fixedBoundsBool f) = true := by
              simpa only [Bool.and_eq_true] using h
            exact fixedBoundsBool_sound (List.all_eq_true.mp both.2 β hβ)
          closure := by intro s countCaptures typeCaptures member; simp at member }⟩
      else throw "bounds: RHS reconciliation changes a closed recursive HM capture"
  | .exported s =>
      pure ⟨{
        mono := by intro β hβ; simp at hβ
        recursive := by intro c hc; simp at hc
        recursiveClosureFixedTypes := by intro c hc; simp at hc
        recursiveClosureCaptures := by intro c hc; simp at hc
        closure := by intro source countCaptures typeCaptures member; simp at member }⟩
  | .closure s countCaptures typeCaptures =>
      if h : typeCaptures.all (fixedBoundsBool f) = true then
        pure ⟨{
          mono := by intro β hβ; simp at hβ
          recursive := by intro c hc; simp at hc
          recursiveClosureFixedTypes := by intro c hc; simp at hc
          recursiveClosureCaptures := by intro c hc; simp at hc
          closure := by
            intro source storedCounts storedTypes member
            have equality : source = s ∧ storedCounts = countCaptures ∧
                storedTypes = typeCaptures := by simpa using member
            rcases equality with ⟨rfl, rfl, rfl⟩
            intro β hβ
            exact fixedBoundsBool_sound (List.all_eq_true.mp h β hβ) }⟩
      else throw "bounds: RHS reconciliation changes lexical closure HM captures"

def checkTypesFixed (f : Nat → BoundsTy) (env : List Binding) :
    Except String (PLift (TypesFixed f env)) := do
  match env with
  | [] => pure ⟨{
      mono := by simp
      recursive := by simp
      recursiveClosureFixedTypes := by simp
      recursiveClosureCaptures := by simp
      closure := by simp }⟩
  | b :: rest =>
      let head ← checkTypesFixedBinding f b
      let tail ← checkTypesFixed f rest
      pure ⟨⟨by
        intro β hβ
        rcases List.mem_cons.mp hβ with hb | ht
        · exact head.down.mono β (by simp [hb])
        · exact tail.down.mono β ht,
        by
        intro c hc
        rcases List.mem_cons.mp hc with hb | ht
        · exact head.down.recursive c (by simp [hb])
        · exact tail.down.recursive c ht,
        by
        intro c hc
        rcases List.mem_cons.mp hc with hb | ht
        · exact head.down.recursiveClosureFixedTypes c (by simp [hb])
        · exact tail.down.recursiveClosureFixedTypes c ht,
        by
        intro c hc
        rcases List.mem_cons.mp hc with hb | ht
        · exact head.down.recursiveClosureCaptures c (by simp [hb])
        · exact tail.down.recursiveClosureCaptures c ht,
        by
        intro s countCaptures typeCaptures member
        rcases List.mem_cons.mp member with hb | ht
        · exact head.down.closure s countCaptures typeCaptures (by simp [hb])
        · exact tail.down.closure s countCaptures typeCaptures ht⟩⟩

/-- Universal group specialization MAY change fixed opaque argument vectors,
    but must preserve the closed callee templates' captured free identities. -/
def templateFixedBool (f : Nat → BoundsTy) (env : List Binding) : Bool :=
  env.all fun b => match b with
    | .mono _ => true
    | .recursive c => c.template.hm.body.freeVars.all (identityBool f)
    | .recursiveClosure _ => true
    | .exported s => s.hm.body.freeVars.all (identityBool f)
    | .closure _ _ _ => true

theorem templateFixedBool_sound {f env} (h : templateFixedBool f env = true) :
    CapturesFixed f env := by
  intro b hb
  cases b with
  | mono β => trivial
  | recursive c =>
      intro i hi
      exact identityBool_sound
        (List.all_eq_true.mp (List.all_eq_true.mp h (.recursive c) hb) i hi)
  | recursiveClosure _ => trivial
  | exported s =>
      intro i hi
      exact identityBool_sound
        (List.all_eq_true.mp (List.all_eq_true.mp h (.exported s) hb) i hi)
  | closure _ _ _ => trivial

def checkTemplateFixed (f : Nat → BoundsTy) (env : List Binding) :
    Except String (PLift (CapturesFixed f env)) :=
  if h : templateFixedBool f env = true then .ok ⟨templateFixedBool_sound h⟩
  else .error "bounds: uniform group HM specialization changes a closed recursive template capture"

theorem typesFixed {f env} (hf : ∀ i, (Synth.BoundsTy.toTy (f i)).IsLC)
    (h : TypesFixed f env) : env.map (mapBinding f hf) = env := by
  conv_rhs => rw [← List.map_id env]
  apply List.map_congr_left
  intro b hb
  cases b with
  | mono β => exact congrArg Binding.mono (SchemeSpecialization.fixed (h.mono β hb))
  | recursive c =>
      have ht : c.fixed.types.map (SchemeSpecialization.mapFree f) = c.fixed.types := by
        conv_rhs => rw [← List.map_id c.fixed.types]
        apply List.map_congr_left
        intro β hβ
        exact SchemeSpecialization.fixed ((h.recursive c hb).2 β hβ)
      have hm : Synth.BoundsTy.toTy (HMCountScheme.opened c.template c.fixed.types) = c.hm :=
        c.fixed.shape.trans (h.recursive c hb).1
      have hc : c.mapTypes f hf = c := by
        apply contract_ext (a := c.mapTypes f hf) (b := c) rfl
        · change Synth.BoundsTy.toTy (HMCountScheme.opened c.template
            (c.fixed.types.map (SchemeSpecialization.mapFree f))) = c.hm
          rw [ht, hm]
        · exact ht
      exact congrArg Binding.recursive hc
  | recursiveClosure c =>
      have hfixed : c.fixedTypes.map (SchemeSpecialization.mapFree f) = c.fixedTypes := by
        conv_rhs => rw [← List.map_id c.fixedTypes]
        apply List.map_congr_left
        intro β hβ
        exact SchemeSpecialization.fixed
          (h.recursiveClosureFixedTypes c hb β hβ)
      have hcaptures : c.typeCaptures.map (SchemeSpecialization.mapFree f) = c.typeCaptures := by
        conv_rhs => rw [← List.map_id c.typeCaptures]
        apply List.map_congr_left
        intro β hβ
        exact SchemeSpecialization.fixed
          (h.recursiveClosureCaptures c hb β hβ)
      have hc : closedMapTypes c f = c := by
        apply closed_ext
        · rfl
        · exact hfixed
        · rfl
        · exact hcaptures
      exact congrArg Binding.recursiveClosure hc
  | exported s => rfl
  | closure s countCaptures typeCaptures =>
      have ht : typeCaptures.map (SchemeSpecialization.mapFree f) = typeCaptures := by
        conv_rhs => rw [← List.map_id typeCaptures]
        apply List.map_congr_left
        intro β hβ
        exact SchemeSpecialization.fixed (h.closure s countCaptures typeCaptures hb β hβ)
      simp [mapBinding, ht]

/-- Callee templates need not be count-substituted to instantiate one member's
    RHS. The fixed HM vector remains unchanged when its counts are captures. -/
theorem fixed (rows : Bindings) {ids env} (captures : Captured ids env)
    (keep : ∀ i ∈ ids, lookup rows i = none) : env.map (mapCountBinding rows) = env := by
  conv_rhs => rw [← List.map_id env]
  apply List.map_congr_left
  intro b hb
  cases b with
  | mono β => exact congrArg Binding.mono (CountTransport.bounds_fixed rows (captures.mono β hb) keep)
  | recursive c =>
      have hv : c.fixed.mapCounts rows = c.fixed := by
        apply fixed_ext
        change c.fixed.types.map (bounds rows) = c.fixed.types
        conv_rhs => rw [← List.map_id c.fixed.types]
        apply List.map_congr_left
        intro β hβ
        exact CountTransport.bounds_fixed rows (captures.recursive c hb β hβ) keep
      change Binding.recursive ⟨c.template, c.hm, c.fixed.mapCounts rows⟩ = Binding.recursive c
      rw [hv]
  | recursiveClosure c =>
      have ht : c.fixedTypes.map (bounds rows) = c.fixedTypes := by
        conv_rhs => rw [← List.map_id c.fixedTypes]
        apply List.map_congr_left
        intro β member
        exact CountTransport.bounds_fixed rows
          (captures.recursiveClosureFixedTypes c hb β member) keep
      have hc : c.countCaptures.map (count rows) = c.countCaptures := by
        conv_rhs => rw [← List.map_id c.countCaptures]
        apply List.map_congr_left
        intro count member
        exact CountTransport.count_fixed rows
          (captures.recursiveClosureCounts c hb count member) keep
      have hcaptures : c.typeCaptures.map (bounds rows) = c.typeCaptures := by
        conv_rhs => rw [← List.map_id c.typeCaptures]
        apply List.map_congr_left
        intro β member
        exact CountTransport.bounds_fixed rows
          (captures.recursiveClosureTypeCaptures c hb β member) keep
      have closed : closedMapCounts c rows = c := by
        apply closed_ext
        · rfl
        · exact ht
        · exact hc
        · exact hcaptures
      exact congrArg Binding.recursiveClosure closed
  | exported s => rfl
  | closure s countCaptures typeCaptures =>
      have hc : countCaptures.map (count rows) = countCaptures := by
        conv_rhs => rw [← List.map_id countCaptures]
        apply List.map_congr_left
        intro c member
        exact CountTransport.count_fixed rows
          (captures.closureCounts s countCaptures typeCaptures hb c member) keep
      have ht : typeCaptures.map (bounds rows) = typeCaptures := by
        conv_rhs => rw [← List.map_id typeCaptures]
        apply List.map_congr_left
        intro β member
        exact CountTransport.bounds_fixed rows
          (captures.closureTypes s countCaptures typeCaptures hb β member) keep
      simp [mapCountBinding, hc, ht]

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
#print axioms checkTemplateFixed
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
