import FHM.Bounds.RecursiveHMEmbedding
import FHM.Bounds.ScopedHMFoundView

/-! Joint finite-count/full-HM RHS contract certificates. Universal use retains
the actual implementation's bounds and a separate semantic demand inclusion.
The simultaneously specialized recursive environment is explicit; group
introduction/generalized export must reconcile that environment separately. -/

namespace FHM.Bounds.RecursiveHMUniversal

open RecursiveHMJudgement SchemeSpecialization CountSubstitution ScopedScheme

mutual
theorem close_counts (ids : List Nat) (rows : Bindings) (β : BoundsTy) :
    BinderBridge.close ids (bounds rows β) = bounds rows (BinderBridge.close ids β) := by
  cases β with
  | prim | bvar => rfl
  | fvar i => cases h : ids.idxOf? i <;> simp [BinderBridge.close, bounds, h]
  | arrow a b => simp only [BinderBridge.close, bounds, close_counts ids rows a, close_counts ids rows b]
  | list lo hi a => exact congrArg (BoundsTy.list (count rows lo) (count rows hi)) (close_counts ids rows a)
  | custom n as => exact congrArg (BoundsTy.custom n) (close_list_counts ids rows as)
termination_by sizeOf β

private theorem close_list_counts (ids : List Nat) (rows : Bindings) (as : List BoundsTy) :
    BinderBridge.closeList ids (boundsList rows as) = boundsList rows (BinderBridge.closeList ids as) := by
  cases as with
  | nil => rfl
  | cons a as => simp only [BinderBridge.closeList, boundsList, close_counts ids rows a, close_list_counts ids rows as]
termination_by sizeOf as
end

structure Certified (s : HMCountScheme.Scheme) (found : Ty) (captures : List Ty)
    (env : List RecursiveHMJudgement.Binding) (rhs : Expr)
    (sourceTypes : Nat → BoundsTy := BoundsTy.fvar)
    (sourceSlots : Nat → BoundsTy := BoundsTy.bvar) where
  opening : HMCountScheme.Opening s found captures
  actual : BoundsTy
  shape : Synth.BoundsTy.toTy actual = found.eraseBounds
  actualScope : BoundsScoped (s.counts.quantified ++ s.counts.captures) actual
  typing : ScopedDerives sourceTypes sourceSlots (s.counts.quantified ++ s.counts.captures) [] s.counts.premises env rhs actual
  inclusion : SemanticSub s.counts.premises actual opening.bounds
  typeFresh : ∀ c, .recursive c ∈ env → ∀ i ∈ opening.ids, i ∉ c.template.hm.body.freeVars
  countFresh : ∀ c, .recursive c ∈ env → ∀ i ∈ c.template.counts.captures, i ∉ s.counts.quantified

private theorem argumentsLC (types : List BoundsTy)
    (lc : ∀ a ∈ types, (Synth.BoundsTy.toTy a).IsLC) :
    ∀ i, (Synth.BoundsTy.toTy (SchemeUse.vector types i)).IsLC := by
  intro i
  cases h : types[i]? with
  | none => simp only [SchemeUse.vector, h, Option.getD_none, Synth.BoundsTy.toTy]; exact .prim
  | some a => simpa only [SchemeUse.vector, h, Option.getD_some] using lc a (List.mem_of_getElem? h)

private theorem replacementLC (ids : List Nat) (args : Nat → BoundsTy)
    (lc : ∀ i, (Synth.BoundsTy.toTy (args i)).IsLC) :
    ∀ i, (Synth.BoundsTy.toTy (argument ids args i)).IsLC := by
  intro i
  cases h : ids.idxOf? i with
  | none => simp only [argument, h, Synth.BoundsTy.toTy]; exact .fvar
  | some slot => simpa only [argument, h] using lc slot

private theorem replacementScope (ids : List Nat) (args : Nat → BoundsTy)
    (scope : ∀ i, BoundsScoped caller (args i)) : ∀ i, BoundsScoped caller (argument ids args i) := by
  intro i
  cases h : ids.idxOf? i with
  | none => simp [argument, h, BoundsScoped]
  | some slot => simpa only [argument, h] using scope slot

private theorem countFresh {s found captures env rhs sourceTypes sourceSlots} (cert : Certified s found captures env rhs sourceTypes sourceSlots)
    {counts caller} (inst : Instance s.counts counts caller) :
    CountCapturesFixed (s.counts.quantified.zip counts) env := by
  intro c hc i hi
  apply lookup_none
  rw [List.map_fst_zip (Nat.le_of_eq inst.arity)]
  exact cert.countFresh c hc i hi

private theorem typeFresh {s found captures env rhs sourceTypes sourceSlots} (cert : Certified s found captures env rhs sourceTypes sourceSlots)
    (args : Nat → BoundsTy) (rows : Bindings) :
    CapturesFixed (argument cert.opening.ids args) (env.map (mapCountBinding rows)) := by
  intro c hc i hi
  obtain ⟨b, hb, he⟩ := List.mem_map.mp hc
  cases b with
  | mono β => cases he
  | recursive d =>
      cases he
      have absent : i ∉ cert.opening.ids := fun present => cert.typeFresh d hb i present hi
      have hnone : cert.opening.ids.idxOf? i = none := List.idxOf?_eq_none_iff.mpr absent
      simp [argument, hnone]

def actual {s found captures env rhs sourceTypes sourceSlots} (cert : Certified s found captures env rhs sourceTypes sourceSlots)
    (counts : List Count) (types : List BoundsTy) : BoundsTy :=
  TypeSubstitution.combined (s.counts.quantified.zip counts) (SchemeUse.vector types)
    (BinderBridge.close cert.opening.ids cert.actual)

def demand (s : HMCountScheme.Scheme) (counts : List Count) (types : List BoundsTy) : BoundsTy :=
  TypeSubstitution.combined (s.counts.quantified.zip counts) (SchemeUse.vector types) s.counts.body

/-- The exact implementation bounds, not the contract demand, are the shared
    simultaneous interpretation of count-specialized original RHS bounds. -/
theorem actual_transport {s found captures env rhs sourceTypes sourceSlots} (cert : Certified s found captures env rhs sourceTypes sourceSlots)
    (counts : List Count) (types : List BoundsTy) :
    mapFree (argument cert.opening.ids (SchemeUse.vector types))
      (bounds (s.counts.quantified.zip counts) cert.actual) = actual cert counts types := by
  have actualLC : (Synth.BoundsTy.toTy (bounds (s.counts.quantified.zip counts) cert.actual)).IsLC := by
    rw [bounds_shape, cert.shape]
    exact cert.opening.lc
  rw [← SchemeSpecialization.close_open cert.opening.ids (SchemeUse.vector types) actualLC,
    close_counts]
  rfl

theorem actual_hm_instance {s found captures env rhs sourceTypes sourceSlots} (cert : Certified s found captures env rhs sourceTypes sourceSlots)
    (counts : List Count) (types : List BoundsTy) (arity : types.length = s.hm.paramCount) :
    s.hm.InstantiatesTo (types.map Synth.BoundsTy.toTy) (Synth.BoundsTy.toTy (actual cert counts types)) := by
  have hs : s.hm.body.eraseBounds = s.hm.body := by
    rw [← s.shape]
    exact FreeAlgebra.shape_erased _
  have hc := (cert.opening.abstractActual cert.actual cert.shape).shape
  change Synth.BoundsTy.toTy (BinderBridge.close cert.opening.ids cert.actual) = s.hm.body.eraseBounds at hc
  rw [hs] at hc
  have ha : Synth.BoundsTy.toTy (actual cert counts types) = Synth.BoundsTy.toTy (HMCountScheme.opened s types) := by
    simp only [actual, TypeSubstitution.combined_shape, HMCountScheme.opened, TypeSubstitution.shape, hc, s.shape]
  rw [ha]
  exact HMCountScheme.opened_instance s types arity

theorem actual_inScope {s found captures env rhs sourceTypes sourceSlots} (cert : Certified s found captures env rhs sourceTypes sourceSlots)
    {counts caller} (inst : Instance s.counts counts caller) (types : List BoundsTy)
    (scope : types.all (boundsScopedBool caller) = true) : BoundsScoped caller (actual cert counts types) := by
  apply TypeSubstitution.inScope _ _ (SchemeUse.vector_scope scope)
  apply bounds_scoped (BinderBridge.close_inScope cert.opening.ids cert.actualScope)
    (fun row hr => inst.argsScoped row.2 (List.of_mem_zip hr).2)
  intro i hi hn
  rcases List.mem_append.mp hi with hq | hc
  · have absent := lookup_none_iff.mp hn
    rw [List.map_fst_zip (Nat.le_of_eq inst.arity)] at absent
    exact (absent hq).elim
  · exact inst.capturesScoped i hc

/-- Count substitution precedes full HM insertion. The RHS, every recursive
    assumption, and source annotation interpretation specialize uniformly. -/
theorem useScopedInterpreted {s found captures env rhs sourceTypes sourceSlots} (cert : Certified s found captures env rhs sourceTypes sourceSlots)
    {counts caller} (inst : Instance s.counts counts caller) (types : List BoundsTy)
    (arity : types.length = s.hm.paramCount)
    (lc : ∀ a ∈ types, (Synth.BoundsTy.toTy a).IsLC)
    (scope : types.all (boundsScopedBool caller) = true) :
    let rows := s.counts.quantified.zip counts
    let f := argument cert.opening.ids (SchemeUse.vector types)
    ScopedDerives (fun i => mapFree f (bounds rows (sourceTypes i)))
      (fun i => mapFree f (bounds rows (sourceSlots i)))
      (s.counts.quantified ++ s.counts.captures) rows inst.premises
      ((env.map (mapCountBinding rows)).map (mapBinding f (replacementLC _ _ (argumentsLC types lc))))
      rhs (actual cert counts types) ∧
    SemanticSub inst.premises (actual cert counts types) (demand s counts types) ∧
    s.hm.InstantiatesTo (types.map Synth.BoundsTy.toTy) (Synth.BoundsTy.toTy (actual cert counts types)) ∧
    BoundsScoped caller (actual cert counts types) := by
  let rows := s.counts.quantified.zip counts
  let f := argument cert.opening.ids (SchemeUse.vector types)
  have fLC := replacementLC cert.opening.ids (SchemeUse.vector types) (argumentsLC types lc)
  have fScope := replacementScope cert.opening.ids (SchemeUse.vector types) (SchemeUse.vector_scope scope)
  have hc := transportScopedCounts rows inst.finite caller
    (fun row hr => inst.argsScoped row.2 (List.of_mem_zip hr).2) cert.typing (countFresh cert inst)
  have ht := transportScopedTypes f fLC caller fScope hc (typeFresh cert _ rows)
  have ha : mapFree f (bounds rows cert.actual) = actual cert counts types := by
    exact actual_transport cert counts types
  have hd : mapFree f (bounds rows cert.opening.bounds) = demand s counts types := by
    have openingShape : Synth.BoundsTy.toTy cert.opening.bounds = found.eraseBounds := cert.opening.shape
    rw [← SchemeSpecialization.close_open cert.opening.ids (SchemeUse.vector types)
      (by rw [bounds_shape, openingShape]; exact cert.opening.lc), close_counts, cert.opening.close]
    rfl
  have hs := SchemeSpecialization.subtype f (inst.subtype cert.inclusion)
  rw [ha, hd] at hs
  refine ⟨?_, hs, actual_hm_instance cert counts types arity, actual_inScope cert inst types scope⟩
  simpa only [ha, CountAlgebra.compose, List.map_nil, List.nil_append,
    ScopedScheme.Instance.premises] using ht

/-- Identity-slot compatibility for existing free-only source certificates. -/
theorem useInterpreted {s found captures env rhs sourceTypes} (cert : Certified s found captures env rhs sourceTypes)
    {counts caller} (inst : Instance s.counts counts caller) (types : List BoundsTy)
    (arity : types.length = s.hm.paramCount)
    (lc : ∀ a ∈ types, (Synth.BoundsTy.toTy a).IsLC)
    (scope : types.all (boundsScopedBool caller) = true) :
    let rows := s.counts.quantified.zip counts
    let f := argument cert.opening.ids (SchemeUse.vector types)
    Derives (fun i => mapFree f (bounds rows (sourceTypes i)))
      (s.counts.quantified ++ s.counts.captures) rows inst.premises
      ((env.map (mapCountBinding rows)).map (mapBinding f (replacementLC _ _ (argumentsLC types lc))))
      rhs (actual cert counts types) ∧
    SemanticSub inst.premises (actual cert counts types) (demand s counts types) ∧
    s.hm.InstantiatesTo (types.map Synth.BoundsTy.toTy) (Synth.BoundsTy.toTy (actual cert counts types)) ∧
    BoundsScoped caller (actual cert counts types) := by
  simpa only [bounds, mapFree] using useScopedInterpreted cert inst types arity lc scope

/-- Compatibility view for the original identity-source certificates. -/
theorem use {s found captures env rhs} (cert : Certified s found captures env rhs)
    {counts caller} (inst : Instance s.counts counts caller) (types : List BoundsTy)
    (arity : types.length = s.hm.paramCount)
    (lc : ∀ a ∈ types, (Synth.BoundsTy.toTy a).IsLC)
    (scope : types.all (boundsScopedBool caller) = true) :
    let rows := s.counts.quantified.zip counts
    let f := argument cert.opening.ids (SchemeUse.vector types)
    Derives f (s.counts.quantified ++ s.counts.captures) rows inst.premises
      ((env.map (mapCountBinding rows)).map (mapBinding f (replacementLC _ _ (argumentsLC types lc))))
      rhs (actual cert counts types) ∧
    SemanticSub inst.premises (actual cert counts types) (demand s counts types) ∧
    s.hm.InstantiatesTo (types.map Synth.BoundsTy.toTy) (Synth.BoundsTy.toTy (actual cert counts types)) ∧
    BoundsScoped caller (actual cert counts types) := by
  simpa only [bounds, mapFree] using useInterpreted cert inst types arity lc scope

def interpretedEnvironment {s found captures env rhs sourceTypes sourceSlots} (cert : Certified s found captures env rhs sourceTypes sourceSlots)
    (counts : List Count) (types : List BoundsTy)
    (lc : ∀ a ∈ types, (Synth.BoundsTy.toTy a).IsLC) : List RecursiveHMJudgement.Binding :=
  (env.map (mapCountBinding (s.counts.quantified.zip counts))).map
    (mapBinding (argument cert.opening.ids (SchemeUse.vector types))
      (replacementLC _ _ (argumentsLC types lc)))

def typeEnvironment {s found captures env rhs sourceTypes sourceSlots} (cert : Certified s found captures env rhs sourceTypes sourceSlots)
    (types : List BoundsTy) (lc : ∀ a ∈ types, (Synth.BoundsTy.toTy a).IsLC) :
    List RecursiveHMJudgement.Binding :=
  env.map (mapBinding (argument cert.opening.ids (SchemeUse.vector types))
    (replacementLC _ _ (argumentsLC types lc)))

/-- A universal certificate consumes an exact ORIGINAL found node and produces
    its caller-specialized typed view. Source, Core path, exact implementation
    intervals, count scope and the real recursive RHS derivation stay linked.
    The common group environment is still explicitly specialized; this is not
    a generalized group-introduction rule. -/
def atNode {output path} (node : HMFoundView.AtNode output path) {s captures env}
    (cert : Certified s node.original captures env node.inner.stripFound)
    {counts caller} (inst : Instance s.counts counts caller) (types : List BoundsTy)
    (arity : types.length = s.hm.paramCount)
    (lc : ∀ a ∈ types, (Synth.BoundsTy.toTy a).IsLC)
    (scope : types.all (boundsScopedBool caller) = true) :
    HMFoundView.TypedChecked node (argument cert.opening.ids (SchemeUse.vector types))
      (s.counts.quantified ++ s.counts.captures) (s.counts.quantified.zip counts)
      inst.premises (interpretedEnvironment cert counts types lc) caller := by
  have h := use cert inst types arity lc scope
  refine ⟨actual cert counts types, ⟨?_, h.2.2.2⟩, h.1⟩
  rw [← actual_transport cert counts types]
  apply node.coherent
  rw [bounds_shape, cert.shape]

theorem atNode_actual {output path} (node : HMFoundView.AtNode output path) {s captures env}
    (cert : Certified s node.original captures env node.inner.stripFound)
    {counts caller} (inst : Instance s.counts counts caller) (types : List BoundsTy)
    (arity : types.length = s.hm.paramCount)
    (lc : ∀ a ∈ types, (Synth.BoundsTy.toTy a).IsLC)
    (scope : types.all (boundsScopedBool caller) = true) :
    (atNode node cert inst types arity lc scope).actual = actual cert counts types := rfl

/-- Reconciled RHS certificates start at a nonidentity source interpretation.
    Count substitution acts inside that interpretation before full caller types
    are inserted. The ORIGINAL artifact and path still index the final result. -/
def atInterpretedNode {output path} (node : HMFoundView.AtNode output path)
    {s captures env sourceTypes}
    (cert : Certified s (node.view sourceTypes) captures env node.inner.stripFound sourceTypes)
    {counts caller} (inst : Instance s.counts counts caller) (types : List BoundsTy)
    (arity : types.length = s.hm.paramCount)
    (lc : ∀ a ∈ types, (Synth.BoundsTy.toTy a).IsLC)
    (scope : types.all (boundsScopedBool caller) = true) :
    HMFoundView.TypedChecked node
      (fun i => mapFree (argument cert.opening.ids (SchemeUse.vector types))
        (bounds (s.counts.quantified.zip counts) (sourceTypes i)))
      (s.counts.quantified ++ s.counts.captures) (s.counts.quantified.zip counts)
      inst.premises (interpretedEnvironment cert counts types lc) caller := by
  have h := useInterpreted cert inst types arity lc scope
  refine ⟨actual cert counts types, ⟨?_, h.2.2.2⟩, h.1⟩
  rw [← actual_transport cert counts types, HMFoundView.bounds_shape, bounds_shape, cert.shape]
  exact HMFoundView.specialization _ _ _ node.original

/-- A lexical source certificate specializes both interfaces while retaining
    the exact original artifact, node address, actual bounds and RHS proof. -/
def atScopedNode {output path} (node : HMFoundView.AtNode output path)
    {s captures env sourceTypes sourceSlots}
    (cert : Certified s (ScopedHMInterpretation.AtNode.view node sourceTypes sourceSlots)
      captures env node.inner.stripFound sourceTypes sourceSlots)
    {counts caller} (inst : Instance s.counts counts caller) (types : List BoundsTy)
    (arity : types.length = s.hm.paramCount)
    (lc : ∀ a ∈ types, (Synth.BoundsTy.toTy a).IsLC)
    (scope : types.all (boundsScopedBool caller) = true) :
    ScopedHMInterpretation.TypedChecked node
      (fun i => mapFree (argument cert.opening.ids (SchemeUse.vector types))
        (bounds (s.counts.quantified.zip counts) (sourceTypes i)))
      (fun i => mapFree (argument cert.opening.ids (SchemeUse.vector types))
        (bounds (s.counts.quantified.zip counts) (sourceSlots i)))
      (s.counts.quantified ++ s.counts.captures) (s.counts.quantified.zip counts)
      inst.premises (interpretedEnvironment cert counts types lc) caller := by
  have h := useScopedInterpreted cert inst types arity lc scope
  refine ⟨actual cert counts types, ⟨?_, h.2.2.2⟩, h.1⟩
  rw [← actual_transport cert counts types, HMFoundView.bounds_shape, bounds_shape, cert.shape]
  exact ScopedHMInterpretation.specialization _ _ _ _ node.original

/-- Assemble a universal source certificate only AFTER an exact-node scoped
    derivation and independent demand inclusion have been established. Opaque
    signature opening and closed-template capture protection remain required;
    neither metadata decoding nor the walker alone licenses generalization. -/
def fromScopedChecked {output path} (node : HMFoundView.AtNode output path)
    {s captures env sourceTypes sourceSlots}
    (opening : HMCountScheme.Opening s
      (ScopedHMInterpretation.AtNode.view node sourceTypes sourceSlots) captures)
    (typed : ScopedHMInterpretation.TypedChecked node sourceTypes sourceSlots
      (s.counts.quantified ++ s.counts.captures) [] s.counts.premises env
      (s.counts.quantified ++ s.counts.captures))
    (inclusion : SemanticSub s.counts.premises typed.actual opening.bounds)
    (typeFresh : ∀ c, .recursive c ∈ env → ∀ i ∈ opening.ids, i ∉ c.template.hm.body.freeVars)
    (countFresh : ∀ c, .recursive c ∈ env → ∀ i ∈ c.template.counts.captures, i ∉ s.counts.quantified) :
    Certified s (ScopedHMInterpretation.AtNode.view node sourceTypes sourceSlots)
      captures env node.inner.stripFound sourceTypes sourceSlots := by
  refine ⟨opening, typed.actual, ?_, typed.checked.inScope, typed.derivation, inclusion, typeFresh, countFresh⟩
  rw [← typed.checked.shape]
  exact (FreeAlgebra.shape_erased _).symm

/-- Reuse an existing sound RHS certificate; its actual scope is a real proof
    supplied by the checked artifact, not reconstructed from the HM skeleton. -/
def fromLegacy {c env rhs ann} (cert : RecursiveRHS.Certified c env rhs ann)
    (scope : BoundsScoped (c.counts.quantified ++ c.counts.captures) cert.actual) :
    Certified (RecursiveHMEmbedding.template c) c.hm [] (env.map RecursiveHMEmbedding.binding) rhs := by
  let d := RecursiveHMEmbedding.contract c
  have hmErased : c.hm.eraseBounds = c.hm := by rw [← c.shape]; exact FreeAlgebra.shape_erased _
  refine
    { opening := ⟨[], rfl, by simp, by simp, d.fixed.shape, d.fixed.lc⟩
      actual := cert.actual
      shape := cert.shape.trans hmErased.symm
      actualScope := scope
      typing := RecursiveHMEmbedding.certified cert
      inclusion := ?_
      typeFresh := by simp
      countFresh := ?_ }
  · change SemanticSub c.counts.premises cert.actual (HMCountScheme.opened (RecursiveHMEmbedding.template c) [])
    have lc : (Synth.BoundsTy.toTy c.counts.body).IsLC := by rw [c.shape]; exact c.lc
    simpa only [HMCountScheme.opened, RecursiveHMEmbedding.template, FreeAlgebra.instantiate_fixed _ lc] using cert.inclusion
  · intro d hd i hi
    obtain ⟨b, hb, he⟩ := List.mem_map.mp hd
    cases b with
    | mono β => cases he
    | recursive old =>
        cases he
        exact cert.recursiveFresh old hb i hi

def fromChecked {c env} (checked : RecursiveRHS.Checked c env) :
    Certified (RecursiveHMEmbedding.template c) c.hm [] (env.map RecursiveHMEmbedding.binding)
      checked.rhs.expr.stripFound :=
  fromLegacy checked.certificate (by rw [checked.actualEq]; exact checked.typed.countScope)

def fromLocatedChecked {c env rhs} (checked : RecursiveRHS.LocatedChecked c env rhs) :
    Certified (RecursiveHMEmbedding.template c) c.hm [] (env.map RecursiveHMEmbedding.binding) rhs.expr.stripFound :=
  fromLegacy checked.certificate (by rw [checked.actualEq]; exact checked.typed.countScope)

#print axioms close_counts
#print axioms use
#print axioms useScopedInterpreted
#print axioms useInterpreted
#print axioms actual_hm_instance
#print axioms actual_inScope
#print axioms actual_transport
#print axioms atNode
#print axioms atNode_actual
#print axioms atInterpretedNode
#print axioms atScopedNode
#print axioms fromScopedChecked
#print axioms fromChecked

end FHM.Bounds.RecursiveHMUniversal
