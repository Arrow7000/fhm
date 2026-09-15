import FHM.Bounds.RecursiveHMCaller
import FHM.Bounds.HMDeclaredGroup
import FHM.Bounds.HMDeclaredCoordinates
import FHM.Bounds.RecursiveSpine

/-! Every recursive RHS specializes through ONE uniform full group HM map.
Member counts specialize first. Checked common captures remove that count
transport from the environment; full HM insertion then changes all group vectors
uniformly, including slots unused by this member. Exact implementation and demand
bounds remain separate. The initial closed-group body slice below consumes
ordered generalized exports only after all universal member proofs exist. -/

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
    intro b hb
    cases b with
    | mono β => trivial
    | recursive c =>
        intro i hi
        apply lookup_none
        rw [List.map_fst_zip (Nat.le_of_eq inst.arity)]
        exact cert.countFresh c hb i hi
    | exported s =>
        intro i hi
        apply lookup_none
        rw [List.map_fst_zip (Nat.le_of_eq inst.arity)]
        exact cert.exportCountFresh s hb i hi
  have typeKeep : CapturesFixed f (env.map (mapCountBinding rows)) := by
    intro c hc
    obtain ⟨original, ho, he⟩ := List.mem_map.mp hc
    cases original with
    | mono β => cases he; trivial
    | recursive original =>
        cases he
        simpa [Contract.mapCounts] using fixed.recursive ho
    | exported s =>
        cases he
        exact fixed.exported ho
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

/-- The actual count-first/full-HM-second certificate specialization preserves
    the complete supported proof fragment, including annotated inner scopes.
    This adds no acceptance rule and no new solver call. -/
theorem fromCertified_runtimeReady {s found typeCaptures env rhs sourceTypes sourceSlots}
    (cert : RecursiveHMUniversal.Certified s found typeCaptures env rhs sourceTypes sourceSlots)
    (ready : ScopedDerives.RuntimeReady cert.typing)
    {counts caller} (inst : Instance s.counts counts caller)
    (f : Nat → BoundsTy) (lc : ∀ i, (Synth.BoundsTy.toTy (f i)).IsLC)
    (scope : ∀ i, BoundsScoped caller (f i)) (arguments : ∀ i, Runtime.Supported (f i))
    (captured : RecursiveHMEnvironment.Captured s.counts.captures env)
    (fixed : CapturesFixed f env) :
    ScopedDerives.RuntimeReady (fromCertified cert inst f lc scope captured fixed).typing := by
  let rows := s.counts.quantified.zip counts
  have countKeep : CountCapturesFixed rows env := by
    intro b hb
    cases b with
    | mono β => trivial
    | recursive c =>
        intro i hi
        apply lookup_none
        rw [List.map_fst_zip (Nat.le_of_eq inst.arity)]
        exact cert.countFresh c hb i hi
    | exported s =>
        intro i hi
        apply lookup_none
        rw [List.map_fst_zip (Nat.le_of_eq inst.arity)]
        exact cert.exportCountFresh s hb i hi
  have typeKeep : CapturesFixed f (env.map (mapCountBinding rows)) := by
    intro c hc
    obtain ⟨original, ho, he⟩ := List.mem_map.mp hc
    cases original with
    | mono β => cases he; trivial
    | recursive original =>
        cases he
        simpa [Contract.mapCounts] using fixed.recursive ho
    | exported s =>
        cases he
        exact fixed.exported ho
  have hc := ready.counts rows inst.finite caller
    (fun row hr => inst.argsScoped row.2 (List.of_mem_zip hr).2) countKeep
  have ht := hc.types f lc caller scope arguments typeKeep
  have envFixed := RecursiveHMEnvironment.instantiated inst captured
  simpa only [actual, rows, envFixed, CountAlgebra.compose, List.map_nil,
    List.nil_append, ScopedScheme.Instance.premises] using ht

/-- An actual specialized RHS proof establishes runtime behaviour at its
    demand bounds, provided its recursive assumptions are realized. This is
    the implementation obligation consumed by simultaneous group closure. -/
theorem Result.termAt {s found typeCaptures env rhs sourceTypes sourceSlots}
    {cert : RecursiveHMUniversal.Certified s found typeCaptures env rhs sourceTypes sourceSlots}
    {counts caller} {inst : Instance s.counts counts caller} {f lc}
    (r : Result cert inst f lc) (ready : ScopedDerives.RuntimeReady r.typing)
    (demandSupported : Runtime.Supported (demand cert counts f))
    (bound free : Runtime.TypeEnv) (σ : Assign)
    (hb : Runtime.TypeEnv.Downward bound) (hf : Runtime.TypeEnv.Downward free)
    (budget : Nat) (premises : ∀ p ∈ inst.premises, p.Holds σ)
    (e : EnvAt bound free σ budget (env.map (mapBinding f lc))) :
    Runtime.TermAt bound free σ budget (demand cert counts f) (rhs.substN 0 e.terms) :=
  (ready.termAt bound free σ hb hf budget premises e).of_values
    (Runtime.subtype r.inclusion ready.supported demandSupported bound free σ premises)

#print axioms fromCertified_runtimeReady
#print axioms Result.termAt

/-- The actual specialized member demand is exactly the fixed in-group
    recursive-use bounds. Full caller arguments are inserted after the member
    count telescope; no independent HM vector is selected at a recursive call. -/
theorem _root_.FHM.Bounds.HMDeclaredGroup.MemberChecked.demandAtRecursiveUse
    {output metadata path index captures premises typeCaptures env}
    {p : HMDeclaredGroup.Member output metadata path index captures premises typeCaptures}
    (checked : HMDeclaredGroup.MemberChecked p env)
    (f : Nat → BoundsTy) (lc : ∀ i, (Synth.BoundsTy.toTy (f i)).IsLC)
    (fixed : ∀ i ∈ p.contract.template.hm.body.freeVars, f i = .fvar i)
    {Δ caller} (used : RecursiveHMContract.Use (p.contract.mapTypes f lc).fixed
      Δ (p.contract.mapTypes f lc).hm caller) :
    demand checked.certificate.implementation used.counts f = used.bounds := by
  rw [demand_instance checked.certificate.implementation used.counts f lc fixed]
  rw [checked.certificateOpeningIds, checked.certificateScheme]
  simp only [RecursiveHMContract.Use.bounds, Contract.mapTypes, RecursiveHMContract.Fixed.mapTypes,
    HMDeclaredGroup.Member.contract, RecursiveHMContract.fromOpaque, List.map_map,
    Function.comp_def, mapFree]

#print axioms HMDeclaredGroup.MemberChecked.demandAtRecursiveUse

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
  refine ⟨actual cert counts f, ⟨?_, r.inScope⟩, r.typing, none⟩
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

/-- Select universal implementation evidence at the SAME total source/exit
    position used for the RHS certificate and fixed recursive contract. This
    cannot drop a member or select an independent member-local HM map. -/
def Members.memberAt {output metadata path captures premises typeCaptures env index vectors caller}
    {ps : HMDeclaredGroup.Interfaces output metadata path captures premises typeCaptures index vectors}
    {ms : HMDeclaredGroup.CheckedMembers env ps} {f lc scope}
    (universal : Members f lc (caller := caller) scope ms) (offset : Nat)
    (inside : offset < ms.exports.length) :
    let selected := ms.memberAt offset inside
    ∀ counts (inst : Instance selected.rhs.certificate.interface.scheme.counts counts caller),
      Result selected.rhs.certificate.implementation inst f lc :=
  by
    induction universal generalizing offset with
    | nil => simp [HMDeclaredGroup.CheckedMembers.exports] at inside
    | cons obligations others ih =>
        cases offset with
        | zero => exact obligations
        | succ offset => exact ih offset (by simpa [HMDeclaredGroup.CheckedMembers.exports] using inside)

#print axioms Members.memberAt

/-- ALL source-ordered supported member certificates realize the actual closed
    recursive group at one common full HM map. Recursive calls retain that map;
    only their count instances vary. Caller-scope weakening adds no premises.
    Generalized exit realization is a separate next step. -/
def _root_.FHM.Bounds.HMDeclaredGroup.Checked.runtimeEnvironment
    {output metadata path vectors captures premises bodyTypes}
    (g : HMDeclaredGroup.Checked output metadata path vectors captures premises bodyTypes [])
    (commonCaller : List Nat) (f : Nat → BoundsTy)
    (lc : ∀ i, (Synth.BoundsTy.toTy (f i)).IsLC)
    (scope : ∀ i, BoundsScoped commonCaller (f i)) (arguments : ∀ i, Runtime.Supported (f i))
    (fixed : CapturesFixed f (g.interfaces.contracts.map Binding.recursive ++ []))
    (ready : ∀ offset (inside : offset < g.exports.length),
      ScopedDerives.RuntimeReady (g.members.memberAt offset inside).rhs.certificate.implementation.typing)
    (demandSupport : ∀ offset (inside : offset < g.exports.length),
      Runtime.Supported (g.members.memberAt offset inside).rhs.certificate.implementation.opening.bounds)
    (bound free : Runtime.TypeEnv) (σ : Assign)
    (hb : Runtime.TypeEnv.Downward bound) (hf : Runtime.TypeEnv.Downward free) :
    ∀ budget, { e : EnvAt bound free σ budget
        ((g.interfaces.contracts.map Binding.recursive ++ []).map (mapBinding f lc)) //
      e.terms = Runtime.recursiveTerms g.annotations (g.rhss.map Expr.stripFound) } := by
  let originalEnv := g.interfaces.contracts.map Binding.recursive ++ []
  let env := originalEnv.map (mapBinding f lc)
  have arity : (g.rhss.map Expr.stripFound).length = env.length := by
    simp only [env, originalEnv, List.length_map, List.length_append, List.length_nil,
      Nat.add_zero, g.memberCount]
  apply EnvAt.tieGroup g.annotations (g.rhss.map Expr.stripFound) arity g.rhssScoped
  intro budget e i inside
  have exitInside : i < g.exports.length := by
    simpa only [env, originalEnv, List.length_map, List.length_append, List.length_nil,
      Nat.add_zero, g.memberCount, g.exportCount] using inside
  let selected := g.members.memberAt i exitInside
  have lookup : env[i]? = some (.recursive (selected.member.contract.mapTypes f lc)) := by
    simpa only [env, originalEnv, List.append_nil, List.getElem?_map, Option.map_some,
      Option.map_map, Function.comp_def, mapBinding]
      using congrArg (Option.map (fun c => mapBinding f lc (.recursive c))) selected.contractSelection
  have entry := (List.getElem?_eq_some_iff.mp lookup).choose_spec
  rw [entry]
  change ∀ Δ caller (used : RecursiveHMContract.Use (selected.member.contract.mapTypes f lc).fixed
    Δ (selected.member.contract.mapTypes f lc).hm caller),
    (∀ p ∈ used.inst.premises, p.Holds σ) → _
  intro Δ caller used rawPremises
  let inst := weakenInstance used.inst commonCaller
  have extendedScope : ∀ i, BoundsScoped (caller ++ commonCaller) (f i) :=
    fun i => HMInterpretation.scope_mono (scope i) (fun _ member => List.mem_append_right _ member)
  let result := fromCertified selected.rhs.certificate.implementation inst f lc extendedScope selected.rhs.captured fixed
  have specialized := fromCertified_runtimeReady selected.rhs.certificate.implementation
    (ready i exitInside) inst f lc extendedScope arguments selected.rhs.captured fixed
  have supported : Runtime.Supported (demand selected.rhs.certificate.implementation used.counts f) :=
    ((demandSupport i exitInside).counts _).types f arguments
  have behavior := result.termAt specialized supported bound free σ hb hf budget rawPremises e
  have templateFixed : ∀ j ∈ selected.member.contract.template.hm.body.freeVars, f j = .fvar j := by
    apply fixed.recursive
    exact List.mem_append_left _ (List.mem_map.mpr
      ⟨selected.member.contract, List.mem_of_getElem? selected.contractSelection, rfl⟩)
  rw [selected.rhs.demandAtRecursiveUse f lc templateFixed used] at behavior
  have sourceRhs := g.memberAtRhs i exitInside
  have rhsEq := (List.getElem?_eq_some_iff.mp sourceRhs).choose_spec
  simpa only [List.getElem_map, rhsEq, Expr.stripFound] using behavior

#print axioms HMDeclaredGroup.Checked.runtimeEnvironment

/-- The same simultaneous member argument with a realized outer lexical
    environment.  Outer variables are closed into every recursive replacement
    exactly once by `EnvAt.tieGroupCaptured`; the member proof itself still
    consumes the single mapped `group ++ outer` assumption environment. -/
def _root_.FHM.Bounds.HMDeclaredGroup.Checked.runtimeEnvironmentCaptured
    {output metadata path vectors captures premises bodyTypes outerEnv}
    (g : HMDeclaredGroup.Checked output metadata path vectors captures premises bodyTypes outerEnv)
    (commonCaller : List Nat) (f : Nat → BoundsTy)
    (lc : ∀ i, (Synth.BoundsTy.toTy (f i)).IsLC)
    (scope : ∀ i, BoundsScoped commonCaller (f i)) (arguments : ∀ i, Runtime.Supported (f i))
    (fixed : CapturesFixed f (g.interfaces.contracts.map Binding.recursive ++ outerEnv))
    (ready : ∀ offset (inside : offset < g.exports.length),
      ScopedDerives.RuntimeReady (g.members.memberAt offset inside).rhs.certificate.implementation.typing)
    (demandSupport : ∀ offset (inside : offset < g.exports.length),
      Runtime.Supported (g.members.memberAt offset inside).rhs.certificate.implementation.opening.bounds)
    (bound free : Runtime.TypeEnv) (σ : Assign)
    (hb : Runtime.TypeEnv.Downward bound) (hf : Runtime.TypeEnv.Downward free)
    (budget : Nat)
    (outer : EnvAt bound free σ budget (outerEnv.map (mapBinding f lc))) :
    { e : EnvAt bound free σ budget
        ((g.interfaces.contracts.map Binding.recursive).map (mapBinding f lc) ++
          outerEnv.map (mapBinding f lc)) //
      e.terms = Runtime.recursiveTerms g.annotations
        (closeOuterRhss (g.rhss.map Expr.stripFound) outer.terms) ++ outer.terms } := by
  let innerOriginal := g.interfaces.contracts.map Binding.recursive
  let inner := innerOriginal.map (mapBinding f lc)
  have arity : (g.rhss.map Expr.stripFound).length = inner.length := by
    simp only [inner, innerOriginal, List.length_map, g.memberCount]
  have rhsScope : ∀ rhs ∈ g.rhss.map Expr.stripFound,
      rhs.varsBelow ((g.rhss.map Expr.stripFound).length +
        (outerEnv.map (mapBinding f lc)).length) = true := by
    simpa only [List.length_map] using g.rhssScopedCaptured
  let tied := EnvAt.tieGroupCaptured g.annotations (g.rhss.map Expr.stripFound) arity rhsScope hb hf
    (fun budget e i inside => by
      have exitInside : i < g.exports.length := by
        simpa only [inner, innerOriginal, List.length_map, g.memberCount, g.exportCount] using inside
      let selected := g.members.memberAt i exitInside
      have contractInside : i < g.interfaces.contracts.length := by
        simpa only [g.memberCount, g.exportCount] using exitInside
      have lookup : inner[i]? =
          some (.recursive (selected.member.contract.mapTypes f lc)) := by
        have selectedEntry := congrArg
          (Option.map (fun c => mapBinding f lc (.recursive c))) selected.contractSelection
        simpa only [inner, innerOriginal, List.getElem?_map, Option.map_some,
          Option.map_map, Function.comp_def, mapBinding] using selectedEntry
      have entry := (List.getElem?_eq_some_iff.mp lookup).choose_spec
      rw [entry]
      change ∀ Δ caller (used : RecursiveHMContract.Use
        (selected.member.contract.mapTypes f lc).fixed Δ
        (selected.member.contract.mapTypes f lc).hm caller),
        (∀ p ∈ used.inst.premises, p.Holds σ) → _
      intro Δ caller used rawPremises
      let inst := weakenInstance used.inst commonCaller
      have extendedScope : ∀ i, BoundsScoped (caller ++ commonCaller) (f i) :=
        fun i => HMInterpretation.scope_mono (scope i)
          (fun _ member => List.mem_append_right _ member)
      let result := fromCertified selected.rhs.certificate.implementation inst f lc extendedScope
        selected.rhs.captured fixed
      have specialized := fromCertified_runtimeReady selected.rhs.certificate.implementation
        (ready i exitInside) inst f lc extendedScope arguments selected.rhs.captured fixed
      have supported : Runtime.Supported (demand selected.rhs.certificate.implementation used.counts f) :=
        ((demandSupport i exitInside).counts _).types f arguments
      let mappedE : EnvAt bound free σ budget
          ((g.interfaces.contracts.map Binding.recursive ++ outerEnv).map (mapBinding f lc)) := by
        refine { terms := e.terms, arity := ?_, closed := e.closed, denotes := ?_ }
        · simpa only [List.map_append, inner, innerOriginal] using e.arity
        · simpa only [List.map_append, inner, innerOriginal] using e.denotes
      have behavior := result.termAt specialized supported bound free σ hb hf budget rawPremises mappedE
      have mappedTerms : mappedE.terms = e.terms := by rfl
      rw [mappedTerms] at behavior
      have templateFixed : ∀ j ∈ selected.member.contract.template.hm.body.freeVars,
          f j = .fvar j := by
        apply fixed.recursive
        exact List.mem_append_left _ (List.mem_map.mpr
          ⟨selected.member.contract, List.mem_of_getElem? selected.contractSelection, rfl⟩)
      rw [selected.rhs.demandAtRecursiveUse f lc templateFixed used] at behavior
      have sourceRhs := g.memberAtRhs i exitInside
      have rhsEq := (List.getElem?_eq_some_iff.mp sourceRhs).choose_spec
      simpa only [List.getElem_map, rhsEq, Expr.stripFound] using behavior)
    budget outer
  exact tied

#print axioms HMDeclaredGroup.Checked.runtimeEnvironmentCaptured

theorem _root_.FHM.Bounds.HMDeclaredGroup.MemberChecked.exitMapFixed
    {output metadata path index captures premises typeCaptures env}
    {p : HMDeclaredGroup.Member output metadata path index captures premises typeCaptures}
    (checked : HMDeclaredGroup.MemberChecked p env) (types : List BoundsTy) :
    CapturesFixed (argument checked.certificate.implementation.opening.ids (SchemeUse.vector types)) env := by
  intro b member
  cases b with
  | mono β => trivial
  | recursive c =>
      intro i freeId
      have absent : i ∉ checked.certificate.implementation.opening.ids :=
        fun present => checked.certificate.implementation.typeFresh c member i present freeId
      simp only [argument, List.idxOf?_eq_none_iff.mpr absent]
  | exported s =>
      intro i freeId
      have absent : i ∉ checked.certificate.implementation.opening.ids :=
        fun present => checked.certificate.implementation.exportTypeFresh s member i present freeId
      simp only [argument, List.idxOf?_eq_none_iff.mpr absent]

/-- A generalized exit opening leaves the captured outer environment's mono
    types and fixed recursive vectors unchanged.  The group checker records
    their exact presence in the guarded outer type list; the selected member's
    opening freshness then excludes every local opening identity they use. -/
theorem _root_.FHM.Bounds.HMDeclaredGroup.Checked.exitMapOuterTypesFixed
    {output metadata path vectors captures premises outerTypes outerEnv}
    (g : HMDeclaredGroup.Checked output metadata path vectors captures premises outerTypes outerEnv)
    (offset : Nat) (inside : offset < g.exports.length) (types : List BoundsTy) :
    let selected := g.members.memberAt offset inside
    RecursiveHMEnvironment.TypesFixed
      (argument selected.rhs.certificate.implementation.opening.ids (SchemeUse.vector types)) outerEnv := by
  let selected := g.members.memberAt offset inside
  let f := argument selected.rhs.certificate.implementation.opening.ids (SchemeUse.vector types)
  have fixesOuter {t : Ty} (member : t ∈ outerTypes) {i : Nat} (free : i ∈ t.freeVars) :
      f i = .fvar i := by
    have absent : i ∉ selected.member.reconciled.opening.ids := by
      intro owned
      exact selected.member.reconciled.opening.fresh i owned t
        (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_append_left _
          (List.mem_cons_of_mem _ (List.mem_append_right _ member))))) free
    simp only [f, argument, selected.rhs.certificateOpeningIds,
      List.idxOf?_eq_none_iff.mpr absent]
  constructor
  · intro β member i free
    exact fixesOuter (g.outerMonoRepresented β member) free
  · intro contract member
    have fullMember : Binding.recursive contract ∈
        g.interfaces.contracts.map Binding.recursive ++ outerEnv :=
      List.mem_append_right _ member
    refine ⟨(selected.rhs.stable.2 contract fullMember).1, ?_⟩
    intro β argumentMember i free
    exact fixesOuter (g.outerFixedRepresented contract member β argumentMember) free

theorem _root_.FHM.Bounds.HMDeclaredGroup.MemberChecked.exitMapVector
    {output metadata path index captures premises typeCaptures env}
    {p : HMDeclaredGroup.Member output metadata path index captures premises typeCaptures}
    (checked : HMDeclaredGroup.MemberChecked p env) {Δ found caller}
    (used : HMCountScheme.Use checked.certificate.interface.scheme Δ found caller) :
    let f := argument checked.certificate.implementation.opening.ids (SchemeUse.vector used.types)
    let lc := RecursiveHMUniversal.replacementLC _ _ (RecursiveHMUniversal.argumentsLC _ used.typesLC)
    (p.contract.mapTypes f lc).fixed.types = used.types := by
  simp only [Contract.mapTypes, RecursiveHMContract.Fixed.mapTypes, HMDeclaredGroup.Member.contract,
    RecursiveHMContract.fromOpaque, List.map_map, Function.comp_def, mapFree]
  rw [← checked.certificateOpeningIds]
  exact SchemeUse.vector_of_argument _ _ checked.certificate.implementation.opening.distinct
    (used.arity.trans checked.certificate.implementation.opening.arity.symm)

/-- One arbitrary complete exit instance induces ONE common fixed HM map for
    its recursive implementation proof. This is not polymorphic recursion. -/
def _root_.FHM.Bounds.HMDeclaredGroup.MemberChecked.fixedExitUse
    {output metadata path index captures premises typeCaptures env}
    {p : HMDeclaredGroup.Member output metadata path index captures premises typeCaptures}
    (checked : HMDeclaredGroup.MemberChecked p env) {Δ found caller}
    (used : HMCountScheme.Use checked.certificate.interface.scheme Δ found caller) :
    let f := argument checked.certificate.implementation.opening.ids (SchemeUse.vector used.types)
    let lc := RecursiveHMUniversal.replacementLC _ _ (RecursiveHMUniversal.argumentsLC _ used.typesLC)
    RecursiveHMContract.Use (p.contract.mapTypes f lc).fixed Δ (p.contract.mapTypes f lc).hm caller := by
  refine ⟨used.counts, used.countInstance, used.usable, ?_, rfl⟩
  simpa only [checked.exitMapVector used] using used.typesScoped

theorem _root_.FHM.Bounds.HMDeclaredGroup.MemberChecked.fixedExitUse_bounds
    {output metadata path index captures premises typeCaptures env}
    {p : HMDeclaredGroup.Member output metadata path index captures premises typeCaptures}
    (checked : HMDeclaredGroup.MemberChecked p env) {Δ found caller}
    (used : HMCountScheme.Use checked.certificate.interface.scheme Δ found caller) :
    (checked.fixedExitUse used).bounds = used.bounds := by
  simp only [RecursiveHMContract.Use.bounds, HMDeclaredGroup.MemberChecked.fixedExitUse, HMCountScheme.Use.bounds]
  rw [checked.exitMapVector used]
  simp only [Contract.mapTypes, checked.certificateScheme]

#print axioms HMDeclaredGroup.MemberChecked.exitMapFixed
#print axioms HMDeclaredGroup.Checked.exitMapOuterTypesFixed
#print axioms HMDeclaredGroup.MemberChecked.exitMapVector
#print axioms HMDeclaredGroup.MemberChecked.fixedExitUse_bounds

/-- Arbitrary supported generalized exit instances describe the SAME actual
    recursive implementation. Each proof specializes the whole group at one
    induced common HM map; it never licenses in-group polymorphic recursion. -/
theorem _root_.FHM.Bounds.HMDeclaredGroup.Checked.exportedMemberSafe
    {output metadata path vectors captures premises bodyTypes}
    (g : HMDeclaredGroup.Checked output metadata path vectors captures premises bodyTypes [])
    (ready : ∀ offset (inside : offset < g.exports.length),
      ScopedDerives.RuntimeReady (g.members.memberAt offset inside).rhs.certificate.implementation.typing)
    (demandSupport : ∀ offset (inside : offset < g.exports.length),
      Runtime.Supported (g.members.memberAt offset inside).rhs.certificate.implementation.opening.bounds)
    (offset : Nat) (inside : offset < g.exports.length)
    {Δ found caller}
    (used : HMCountScheme.Use (g.members.memberAt offset inside).rhs.certificate.interface.scheme Δ found caller)
    (arguments : ∀ a ∈ used.types, Runtime.Supported a)
    (bound free : Runtime.TypeEnv) (σ : Assign)
    (hb : Runtime.TypeEnv.Downward bound) (hf : Runtime.TypeEnv.Downward free)
    (rawPremises : ∀ p ∈ used.countInstance.premises, p.Holds σ) :
    Runtime.Safe bound free σ used.bounds
      (.letRec g.annotations (g.rhss.map Expr.stripFound)
        (g.members.memberAt offset inside).member.declaration.node.inner.stripFound) := by
  let selected := g.members.memberAt offset inside
  let f := argument selected.rhs.certificate.implementation.opening.ids (SchemeUse.vector used.types)
  let lc := RecursiveHMUniversal.replacementLC selected.rhs.certificate.implementation.opening.ids
    (SchemeUse.vector used.types) (RecursiveHMUniversal.argumentsLC used.types used.typesLC)
  have scope : ∀ i, BoundsScoped caller (f i) := RecursiveHMUniversal.replacementScope _ _
    (SchemeUse.vector_scope used.typesScoped)
  have slotsSupport : ∀ i, Runtime.Supported (SchemeUse.vector used.types i) := by
    intro i
    cases atIndex : used.types[i]? with
    | none => simp only [SchemeUse.vector, atIndex, Option.getD_none]; exact .prim
    | some a =>
        simpa only [SchemeUse.vector, atIndex, Option.getD_some] using arguments a (List.mem_of_getElem? atIndex)
  have fullSupport : ∀ i, Runtime.Supported (f i) := Runtime.Supported.argument _ _ slotsSupport
  have fixed := selected.rhs.exitMapFixed used.types
  let realized := g.runtimeEnvironment caller f lc scope fullSupport fixed ready demandSupport bound free σ hb hf
  have lookup : ((g.interfaces.contracts.map Binding.recursive ++ []).map (mapBinding f lc))[offset]? =
      some (.recursive (selected.member.contract.mapTypes f lc)) := by
    simpa only [List.append_nil, List.getElem?_map, Option.map_some, Option.map_map,
      Function.comp_def, mapBinding] using
        congrArg (Option.map (fun c => mapBinding f lc (.recursive c))) selected.contractSelection
  have sourceRhs := g.memberAtRhs offset inside
  have rhsLookup : (g.rhss.map Expr.stripFound)[offset]? =
      some selected.member.declaration.node.inner.stripFound := by
    simpa only [List.getElem?_map, Option.map_some, Expr.stripFound] using
      congrArg (Option.map Expr.stripFound) sourceRhs
  have behavior := EnvAt.recursiveMemberSafe realized lookup (selected.rhs.fixedExitUse used) rawPremises rhsLookup
  simpa only [selected.rhs.fixedExitUse_bounds used] using behavior

#print axioms HMDeclaredGroup.Checked.exportedMemberSafe

/-! The program body has generalized exit bindings, unlike the RHS judgement's
fixed recursive assumptions. Keep this boundary explicit: a body variable use
checks a full HM/count instance, while group introduction requires ALL actual
universal RHS obligations. These initial body rules stay in this assembly module
instead of introducing another parallel file family. -/

inductive BodyBinding where
  | mono (bounds : BoundsTy)
  | exported (scheme : HMCountScheme.Scheme)

private def ordinaryBinding : Binding → BodyBinding
  | .mono β => .mono β
  | .recursive c => .exported c.template
  | .exported s => .exported s

def ordinaryBodyEnv (env : List Binding) : List BodyBinding := env.map ordinaryBinding

private theorem ordinaryBodyEnv_exports (schemes : List HMCountScheme.Scheme) :
    ordinaryBodyEnv (schemes.map Binding.exported) = schemes.map BodyBinding.exported := by
  induction schemes with
  | nil => rfl
  | cons _ rest ih =>
      simp only [List.map_cons, ordinaryBodyEnv, ordinaryBinding]
      exact congrArg (List.cons _) (by simpa only [ordinaryBodyEnv] using ih)

/-- Runtime conversion of recursive RHS assumptions additionally records that
    every fixed HM argument exported to the body runtime has an interpretation.
    This is independent of whether a particular RHS happens to use that slot. -/
def RecursiveArgumentsSupported (env : List Binding) : Prop :=
  ∀ c, .recursive c ∈ env → ∀ a ∈ c.fixed.types, Runtime.Supported a

/-- Generalized exits promise each supported complete HM/count instance of the
    same runtime term. Unlike RHS assumptions, their HM arguments are not fixed.
    Supporting all arguments matters even for unused quantifier slots. -/
def BodyBindingAt (bound free : Runtime.TypeEnv) (σ : Assign) (budget : Nat)
    (binding : BodyBinding) (term : Expr) : Prop :=
  match binding with
  | .mono β => Runtime.TermAt bound free σ budget β term
  | .exported s =>
      ∀ Δ found caller (used : HMCountScheme.Use s Δ found caller),
        (∀ a ∈ used.types, Runtime.Supported a) →
        (∀ p ∈ used.countInstance.premises, p.Holds σ) →
        Runtime.TermAt bound free σ budget used.bounds term

structure BodyEnvAt (bound free : Runtime.TypeEnv) (σ : Assign) (budget : Nat)
    (env : List BodyBinding) where
  terms : List Expr
  arity : terms.length = env.length
  closed : ∀ e ∈ terms, e.varsBelow 0 = true
  denotes : ∀ i (inside : i < env.length),
    BodyBindingAt bound free σ budget env[i]
      (terms[i]'(by rw [arity]; exact inside))

def BodyEnvAt.down {bound free σ small large env}
    (e : BodyEnvAt bound free σ large env)
    (hb : Runtime.TypeEnv.Downward bound) (hf : Runtime.TypeEnv.Downward free)
    (le : small ≤ large) : BodyEnvAt bound free σ small env := by
  refine ⟨e.terms, e.arity, e.closed, ?_⟩
  intro i inside
  have actual := e.denotes i inside
  cases kind : env[i] with
  | mono β =>
      simp only [BodyBindingAt, kind] at actual ⊢
      exact actual.down hb hf le
  | exported s =>
      simp only [BodyBindingAt, kind] at actual ⊢
      intro Δ found caller used arguments premises
      exact (actual Δ found caller used arguments premises).down hb hf le

def BodyEnvAt.extend {bound free σ budget env}
    (e : BodyEnvAt bound free σ budget env) (binding : BodyBinding) (term : Expr)
    (closed : term.varsBelow 0 = true) (safe : BodyBindingAt bound free σ budget binding term) :
    BodyEnvAt bound free σ budget (binding :: env) where
  terms := term :: e.terms
  arity := by simp only [List.length_cons, e.arity]
  closed := by
    intro v member
    rcases List.mem_cons.mp member with rfl | rest
    · exact closed
    · exact e.closed v rest
  denotes := by
    intro i inside
    cases i with
    | zero => exact safe
    | succ i =>
        have small : i < env.length := by simp only [List.length_cons] at inside; omega
        simpa only [List.getElem_cons_succ] using e.denotes i small

def BodyEnvAt.extendMono {bound free σ budget env}
    (e : BodyEnvAt bound free σ budget env) (β : BoundsTy) (term : Expr)
    (closed : term.varsBelow 0 = true) (safe : Runtime.TermAt bound free σ budget β term) :
    BodyEnvAt bound free σ budget (.mono β :: env) := e.extend (.mono β) term closed safe

theorem BodyEnvAt.varMono {bound free σ budget env i β}
    (e : BodyEnvAt bound free σ budget env) (lookup : env[i]? = some (.mono β)) :
    Runtime.TermAt bound free σ budget β ((Expr.var i).substN 0 e.terms) := by
  obtain ⟨inside, entry⟩ := List.getElem?_eq_some_iff.mp lookup
  rw [Runtime.closing_var e.terms e.closed i (by rw [e.arity]; exact inside)]
  have meaning := e.denotes i inside
  simpa only [BodyBindingAt, entry] using meaning

theorem BodyEnvAt.varExported {bound free σ budget env i s Δ found caller}
    (e : BodyEnvAt bound free σ budget env) (lookup : env[i]? = some (.exported s))
    (used : HMCountScheme.Use s Δ found caller)
    (arguments : ∀ a ∈ used.types, Runtime.Supported a)
    (premises : ∀ p ∈ Δ, p.Holds σ) :
    Runtime.TermAt bound free σ budget used.bounds ((Expr.var i).substN 0 e.terms) := by
  obtain ⟨inside, entry⟩ := List.getElem?_eq_some_iff.mp lookup
  rw [Runtime.closing_var e.terms e.closed i (by rw [e.arity]; exact inside)]
  have meaning := e.denotes i inside
  simp only [BodyBindingAt, entry] at meaning
  exact meaning Δ found caller used arguments (used.usable σ premises)

/-- Forget the generalized body view of an ordinary RHS environment.  A body
    export for a recursive contract is stronger than the fixed in-group
    assumption: instantiate it at that contract's actual fixed HM vector.
    Support for every fixed argument is explicit, including unused slots. -/
def BodyEnvAt.toEnvAt {bound free σ budget env}
    (e : BodyEnvAt bound free σ budget (ordinaryBodyEnv env))
    (arguments : ∀ c, Binding.recursive c ∈ env →
      ∀ a ∈ c.fixed.types, Runtime.Supported a) :
    EnvAt bound free σ budget env := by
  refine ⟨e.terms, ?_, e.closed, ?_⟩
  · simpa only [ordinaryBodyEnv, List.length_map] using e.arity
  · intro i inside
    have bodyInside : i < (ordinaryBodyEnv env).length := by
      simpa only [ordinaryBodyEnv, List.length_map] using inside
    have meaning := e.denotes i bodyInside
    cases source : env[i] with
    | mono β =>
        simpa only [ordinaryBodyEnv, List.getElem_map, source, ordinaryBinding,
          BodyBindingAt, BindingAt] using meaning
    | recursive c =>
        simp only [ordinaryBodyEnv, List.getElem_map, source, ordinaryBinding,
          BodyBindingAt] at meaning
        simp only [BindingAt, source]
        intro Δ caller used premises
        exact meaning Δ c.hm caller used.external
          (fun a member => arguments c (by simpa only [source] using List.getElem_mem inside) a member)
          premises
    | exported s =>
        simpa only [ordinaryBodyEnv, List.getElem_map, source, ordinaryBinding,
          BodyBindingAt, BindingAt] using meaning

/-- All generalized exports are realized by Core's original source-ordered
    recursive replacements, using the fixed-map member theorem at each use. -/
def _root_.FHM.Bounds.HMDeclaredGroup.Checked.exportEnvironment
    {output metadata path vectors captures premises bodyTypes}
    (g : HMDeclaredGroup.Checked output metadata path vectors captures premises bodyTypes [])
    (ready : ∀ offset (inside : offset < g.exports.length),
      ScopedDerives.RuntimeReady (g.members.memberAt offset inside).rhs.certificate.implementation.typing)
    (demandSupport : ∀ offset (inside : offset < g.exports.length),
      Runtime.Supported (g.members.memberAt offset inside).rhs.certificate.implementation.opening.bounds)
    (bound free : Runtime.TypeEnv) (σ : Assign)
    (hb : Runtime.TypeEnv.Downward bound) (hf : Runtime.TypeEnv.Downward free)
    (budget : Nat) :
    { e : BodyEnvAt bound free σ budget (g.exports.map BodyBinding.exported) //
      e.terms = Runtime.recursiveTerms g.annotations (g.rhss.map Expr.stripFound) } := by
  refine ⟨{ terms := Runtime.recursiveTerms g.annotations (g.rhss.map Expr.stripFound)
            arity := by simp only [Runtime.recursiveTerms, List.length_map, g.exportCount]
            closed := Runtime.recursiveTerms_closed g.rhssScoped
            denotes := ?_ }, rfl⟩
  intro i inside
  have sourceInside : i < g.exports.length := by simpa only [List.length_map] using inside
  let selected := g.members.memberAt i sourceInside
  have exported := List.getElem?_eq_some_iff.mp selected.selection
  have exportEntry : g.exports[i] = selected.rhs.certificate.interface.scheme := exported.choose_spec
  simp only [List.getElem_map, BodyBindingAt, exportEntry]
  intro Δ found caller used arguments rawPremises
  have safe := g.exportedMemberSafe ready demandSupport i sourceInside used arguments bound free σ hb hf rawPremises budget
  have rhs := List.getElem?_eq_some_iff.mp (g.memberAtRhs i sourceInside)
  simpa only [Runtime.recursiveTerms, List.getElem_map, rhs.2, Expr.stripFound] using safe

#print axioms BodyEnvAt.varExported
#print axioms HMDeclaredGroup.Checked.exportEnvironment

/-- Generalized exits of a captured group are realized by the same tied source
    members followed by the already realized outer terms.  Each arbitrary exit
    use induces one common full HM map for ALL members; that map is proved to
    leave the captured outer environment fixed before its realization is used. -/
def _root_.FHM.Bounds.HMDeclaredGroup.Checked.exportEnvironmentCaptured
    {output metadata path vectors captures premises bodyTypes outerEnv}
    (g : HMDeclaredGroup.Checked output metadata path vectors captures premises bodyTypes outerEnv)
    (ready : ∀ offset (inside : offset < g.exports.length),
      ScopedDerives.RuntimeReady (g.members.memberAt offset inside).rhs.certificate.implementation.typing)
    (demandSupport : ∀ offset (inside : offset < g.exports.length),
      Runtime.Supported (g.members.memberAt offset inside).rhs.certificate.implementation.opening.bounds)
    (outerArguments : RecursiveArgumentsSupported outerEnv)
    (bound free : Runtime.TypeEnv) (σ : Assign)
    (hb : Runtime.TypeEnv.Downward bound) (hf : Runtime.TypeEnv.Downward free)
    (budget : Nat) (outer : BodyEnvAt bound free σ budget (ordinaryBodyEnv outerEnv)) :
    { e : BodyEnvAt bound free σ budget
        (g.exports.map BodyBinding.exported ++ ordinaryBodyEnv outerEnv) //
      e.terms = Runtime.recursiveTerms g.annotations
        (closeOuterRhss (g.rhss.map Expr.stripFound) outer.terms) ++ outer.terms } := by
  let outerRhs := outer.toEnvAt outerArguments
  let closedRhss := closeOuterRhss (g.rhss.map Expr.stripFound) outer.terms
  let recursive := Runtime.recursiveTerms g.annotations closedRhss
  have closedScope : ∀ rhs ∈ closedRhss,
      rhs.varsBelow (g.rhss.map Expr.stripFound).length = true := by
    apply closeOuterRhss_scoped outerRhs
    simpa only [ordinaryBodyEnv, List.length_map, Nat.add_comm] using g.rhssScopedCaptured
  have recursiveClosed : ∀ term ∈ recursive, term.varsBelow 0 = true := by
    apply Runtime.recursiveTerms_closed
    simpa only [closedRhss, closeOuterRhss_length] using closedScope
  refine ⟨{ terms := recursive ++ outer.terms
            arity := ?_
            closed := ?_
            denotes := ?_ }, rfl⟩
  · simp only [List.length_append, recursive, Runtime.recursiveTerms, List.length_map,
      closedRhss, closeOuterRhss_length, g.exportCount, ordinaryBodyEnv, outer.arity]
  · intro term member
    exact (List.mem_append.mp member).elim (recursiveClosed term) (outer.closed term)
  · intro i inside
    by_cases groupInside : i < g.exports.length
    · let selected := g.members.memberAt i groupInside
      have exported := List.getElem?_eq_some_iff.mp selected.selection
      have exportEntry : g.exports[i] = selected.rhs.certificate.interface.scheme :=
        exported.choose_spec
      have exportBindingInside : i < (g.exports.map BodyBinding.exported).length := by
        simpa only [List.length_map] using groupInside
      have rhsInside : i < (g.rhss.map Expr.stripFound).length := by
        simpa only [List.length_map, g.exportCount] using groupInside
      have recursiveInside : i < recursive.length := by
        simpa only [recursive, Runtime.recursiveTerms, List.length_map,
          closedRhss, closeOuterRhss_length] using rhsInside
      rw [List.getElem_append_left exportBindingInside, List.getElem_map, exportEntry,
        List.getElem_append_left recursiveInside]
      simp only [BodyBindingAt]
      intro Δ found caller used arguments rawPremises
      let f := argument selected.rhs.certificate.implementation.opening.ids
        (SchemeUse.vector used.types)
      let lc := RecursiveHMUniversal.replacementLC
        selected.rhs.certificate.implementation.opening.ids (SchemeUse.vector used.types)
        (RecursiveHMUniversal.argumentsLC used.types used.typesLC)
      have typeScope : ∀ i, BoundsScoped caller (f i) :=
        RecursiveHMUniversal.replacementScope _ _ (SchemeUse.vector_scope used.typesScoped)
      have slotsSupport : ∀ i, Runtime.Supported (SchemeUse.vector used.types i) := by
        intro slot
        cases atIndex : used.types[slot]? with
        | none => simp only [SchemeUse.vector, atIndex, Option.getD_none]; exact .prim
        | some a =>
            simpa only [SchemeUse.vector, atIndex, Option.getD_some] using
              arguments a (List.mem_of_getElem? atIndex)
      have fullSupport : ∀ i, Runtime.Supported (f i) :=
        Runtime.Supported.argument _ _ slotsSupport
      have fixed := selected.rhs.exitMapFixed used.types
      have outerFixed := g.exitMapOuterTypesFixed i groupInside used.types
      have outerEq : outerEnv.map (mapBinding f lc) = outerEnv :=
        RecursiveHMEnvironment.typesFixed lc outerFixed
      let mappedOuter : EnvAt bound free σ budget (outerEnv.map (mapBinding f lc)) := by
        refine { terms := outerRhs.terms, arity := ?_, closed := outerRhs.closed, denotes := ?_ }
        · simpa only [List.length_map] using outerRhs.arity
        · simpa only [outerEq] using outerRhs.denotes
      let realized := g.runtimeEnvironmentCaptured caller f lc typeScope fullSupport fixed ready
        demandSupport bound free σ hb hf budget mappedOuter
      have contractInside : i < g.interfaces.contracts.length := by
        simpa only [g.memberCount, g.exportCount] using groupInside
      have mappedContractInside : i <
          ((g.interfaces.contracts.map Binding.recursive).map (mapBinding f lc)).length := by
        simpa only [List.length_map] using contractInside
      have fullInside : i <
          ((g.interfaces.contracts.map Binding.recursive).map (mapBinding f lc) ++
            outerEnv.map (mapBinding f lc)).length := by
        simp only [List.length_append, List.length_map]
        omega
      have lookup : ((g.interfaces.contracts.map Binding.recursive).map
          (mapBinding f lc))[i] = .recursive (selected.member.contract.mapTypes f lc) := by
        rw [List.getElem_map, List.getElem_map]
        exact congrArg (fun contract : Contract =>
          Binding.recursive (contract.mapTypes f lc))
          (List.getElem?_eq_some_iff.mp selected.contractSelection).choose_spec
      have meaning := realized.val.denotes i fullInside
      rw [List.getElem_append_left mappedContractInside, lookup] at meaning
      simp only [BindingAt] at meaning
      have safe := meaning Δ caller (selected.rhs.fixedExitUse used) rawPremises
      rw [selected.rhs.fixedExitUse_bounds used] at safe
      simpa only [realized.property, mappedOuter, outerRhs, BodyEnvAt.toEnvAt,
        recursive, closedRhss,
        List.getElem_append_left recursiveInside] using safe
    · have outerInside : i - g.exports.length < (ordinaryBodyEnv outerEnv).length := by
        simp only [List.length_append, List.length_map, ordinaryBodyEnv] at inside ⊢
        omega
      have meaning := outer.denotes (i - g.exports.length) outerInside
      have recursiveLength : recursive.length = g.exports.length := by
        simp only [recursive, Runtime.recursiveTerms, List.length_map,
          closedRhss, closeOuterRhss_length, g.exportCount]
      have exportPosition : g.exports.length ≤ i := by omega
      have recursivePosition : recursive.length ≤ i := by rw [recursiveLength]; exact exportPosition
      have exportBindingPosition : (g.exports.map BodyBinding.exported).length ≤ i := by
        simpa only [List.length_map] using exportPosition
      rw [List.getElem_append_right exportBindingPosition,
        List.getElem_append_right recursivePosition]
      simpa only [List.length_map, recursiveLength] using meaning

#print axioms HMDeclaredGroup.Checked.exportEnvironmentCaptured

/-- One branch path for List refinements and finite nominal coverage. Generalized
    exports remain in the environment behind any newly opened mono fields. -/
inductive BodyBranchContext where
  | list (lo hi : Count) (elem : BoundsTy)
  | bool
  | pair (left right : BoundsTy)

def BodyBranchContext.bounds : BodyBranchContext → BoundsTy
  | .list lo hi elem => .list lo hi elem
  | .bool => .custom boolTyName []
  | .pair left right => .custom pairTyName [left, right]

def BodyBranchContext.refine : BodyBranchContext → MatchPattern → List Constraint
  | .list lo hi _, p => RecursiveTyping.branchRefine p lo hi
  | .bool, _ => []
  | .pair _ _, _ => []

def BodyBranchContext.extend : BodyBranchContext → MatchPattern → List BodyBinding → List BodyBinding
  | .list lo hi elem, p, env =>
      if p = .named consCtorName 2 then
        .mono elem :: .mono (.list (.pred lo) (.pred hi) elem) :: env
      else env
  | .bool, _, env => env
  | .pair left right, p, env =>
      if p = .named pairCtorName 2 then .mono left :: .mono right :: env else env

def BodyBranchContext.Pattern : BodyBranchContext → MatchPattern → Prop
  | .list _ _ _, p => RecursiveTyping.ListPattern p
  | .bool, p => BoolBranches.Pattern p
  | .pair _ _, p => PairBranches.Pattern p

instance (ctx : BodyBranchContext) (p : MatchPattern) : Decidable (ctx.Pattern p) := by
  cases ctx <;> unfold BodyBranchContext.Pattern <;> infer_instance

def BodyBranchContext.Covers (Δ : List Constraint) : BodyBranchContext → List (MatchPattern × Expr) → Prop
  | .list lo hi _, branches => ListBranches.Covers Δ ⟨lo, hi⟩ branches
  | .bool, branches => BoolBranches.Covers branches
  | .pair _ _, branches => PairBranches.Covers branches

def BodyBranchContext.checkCoverage (ctx : BodyBranchContext) (Δ : List Constraint)
    (branches : List (MatchPattern × Expr)) : Except String (PLift (ctx.Covers Δ branches)) :=
  match ctx with
  | .list lo hi _ => ListBranches.check Δ ⟨lo, hi⟩ branches
  | .bool => BoolBranches.check branches
  | .pair _ _ => PairBranches.check branches

private def bodyBranchContext (β : BoundsTy) :
    Except String (Σ ctx : BodyBranchContext, PLift (β = ctx.bounds)) :=
  match β with
  | .list lo hi elem => .ok ⟨.list lo hi elem, ⟨rfl⟩⟩
  | .custom name [] =>
      if hn : name = boolTyName then .ok ⟨.bool, ⟨by subst name; rfl⟩⟩
      else .error "bounds: generalized body match scrutinee is not a supported data type"
  | .custom name [left, right] =>
      if hn : name = pairTyName then .ok ⟨.pair left right, ⟨by subst name; rfl⟩⟩
      else .error "bounds: generalized body match scrutinee is not a supported data type"
  | _ => .error "bounds: generalized body match scrutinee is not a supported data type"

/-- A written generalized local must retain its actual declared HM/count
    interface. Unannotated interfaces instead come from checked machine facts
    at the consuming checker boundary, not from this semantic judgment. -/
def LocalAnnotationOK (s : HMCountScheme.Scheme) : Option PolyTy → Prop
  | none => True
  | some annotation => ∃ declared : HMCountScheme.Annotated annotation
      s.counts.quantified s.counts.captures s.counts.premises, declared.scheme = s

/-- Local generalization may replace only fresh owned HM identities. Captured
    source annotation identities and count scopes remain the parent's. -/
structure LocalFrame (s : HMCountScheme.Scheme) (parentIds : List Nat) (rhs : Expr) where
  owned : List Nat
  arity : owned.length = s.hm.paramCount
  distinct : owned.Nodup
  fresh : ∀ i ∈ owned, i ∉ rhs.tyFreeVars ++ s.hm.body.freeVars
  countFresh : ∀ i ∈ s.counts.quantified, i ∉ parentIds
  capturesScoped : ∀ i ∈ s.counts.captures, i ∈ parentIds

def localTypes (owned : List Nat) (parent : Nat → BoundsTy) (args : List BoundsTy) (i : Nat) : BoundsTy :=
  match owned.idxOf? i with
  | none => parent i
  | some slot => SchemeUse.vector args slot

def localSlots (ann : Option PolyTy) (parent : Nat → BoundsTy) (args : List BoundsTy) (i : Nat) : BoundsTy :=
  let depth := (ann.map (·.paramCount)).getD 0
  if i < depth then SchemeUse.vector args i else parent (i - depth)

theorem localTypes_parent {owned parent args i} (fresh : i ∉ owned) :
    localTypes owned parent args i = parent i := by
  simp only [localTypes, List.idxOf?_eq_none_iff.mpr fresh]

theorem LocalFrame.annotationTypes {s parentIds rhs} (frame : LocalFrame s parentIds rhs)
    (parent : Nat → BoundsTy) (args : List BoundsTy) {i} (captured : i ∈ rhs.tyFreeVars) :
    localTypes frame.owned parent args i = parent i := by
  apply localTypes_parent
  intro owned
  exact frame.fresh i owned (List.mem_append_left _ captured)

theorem localSlots_parent (ann : Option PolyTy) (parent : Nat → BoundsTy) (args : List BoundsTy) (i : Nat) :
    localSlots ann parent args (i + (ann.map (·.paramCount)).getD 0) = parent i := by
  simp only [localSlots]
  rw [if_neg (by omega), Nat.add_sub_cancel]

theorem LocalFrame.slotsFit {s ids rhs ann} (frame : LocalFrame s ids rhs)
    (annotation : LocalAnnotationOK s ann) :
    (ann.map (·.paramCount)).getD 0 ≤ frame.owned.length := by
  cases ann with
  | none => simp
  | some a =>
      obtain ⟨declared, scheme⟩ := annotation
      have arity := congrArg (fun s : HMCountScheme.Scheme => s.hm.paramCount) scheme
      simpa [HMCountScheme.Annotated.scheme, PolyTy.eraseBounds, ← frame.arity] using
        Nat.le_of_eq arity

/-- The source reader used by declared ordinary-let reconciliation and the
    canonical local reader coincide on every slot the declaration can name. -/
theorem declaredLocalSlotsAgree {output path d quantified premises typeCaptures}
    (c : @HMDeclaredReconciliation.Checked output (.letIn path) d
      quantified [] premises typeCaptures) :
    ∀ i < d.annotation.paramCount,
      HMDeclaredReconciliation.slotsFor (.letIn path) c.signatureIds i =
        localSlots (some d.annotation) BoundsTy.bvar
          (c.signatureIds.map BoundsTy.fvar) i := by
  intro i inside
  have small : i < c.signatureIds.length := by
    have arity := c.opening.arity
    rw [c.openingIds] at arity
    rw [arity]
    simpa [HMCountScheme.Annotated.scheme, PolyTy.eraseBounds] using inside
  have mapSmall : i < (c.signatureIds.map BoundsTy.fvar).length := by simpa using small
  have present : (c.signatureIds.map BoundsTy.fvar)[i]? =
      some ((c.signatureIds.map BoundsTy.fvar)[i]'mapSmall) :=
    List.getElem?_eq_getElem mapSmall
  simp only [HMDeclaredReconciliation.slotsFor, localSlots, Option.map_some, Option.getD_some,
    if_pos inside, ScopedHMInterpretation.vector, SchemeUse.vector,
    present, Option.getD_some]

/-- A checked source declaration supplies the canonical closed-parent local
    frame. Freshness comes from its opaque opening, including RHS annotation
    identities that reconciliation explicitly protects. -/
def declaredLocalFrame {output path d quantified premises typeCaptures}
    (c : @HMDeclaredReconciliation.Checked output (.letIn path) d
      quantified [] premises typeCaptures) :
    LocalFrame c.interface.scheme [] d.node.inner.stripFound where
  owned := c.signatureIds
  arity := by rw [← c.openingIds]; exact c.opening.arity
  distinct := by rw [← c.openingIds]; exact c.opening.distinct
  fresh := by
    intro i owned named
    have opened : i ∈ c.opening.ids := by rw [c.openingIds]; exact owned
    rcases List.mem_append.mp named with rhsNamed | schemeNamed
    · have guarded : Ty.fvar i ∈ HMDeclaredReconciliation.guardedTypes d typeCaptures := by
        unfold HMDeclaredReconciliation.guardedTypes
        exact List.mem_cons_of_mem _ (List.mem_append_right _
          (List.mem_map.mpr ⟨i, rhsNamed, rfl⟩))
      exact c.opening.fresh i opened (Ty.fvar i)
        (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ guarded)) (by simp [Ty.freeVars])
    · exact c.opening.fresh i opened c.interface.scheme.hm.body List.mem_cons_self schemeNamed
  countFresh := by simp [HMCountScheme.Annotated.scheme, ScopedAnnotation.Contract.scheme]
  capturesScoped := by simp [HMCountScheme.Annotated.scheme, ScopedAnnotation.Contract.scheme]

/-- The actual checked source RHS, with its exact opening and demand inclusion,
    can be consumed through the canonical local lexical frame. -/
def declaredLocalCertificate {output path d quantified premises typeCaptures}
    (c : @HMDeclaredReconciliation.Checked output (.letIn path) d
      quantified [] premises typeCaptures)
    (rhs : HMDeclaredRHS.Checked c []) :
    RecursiveHMUniversal.Certified c.interface.scheme
      (ScopedHMInterpretation.AtNode.view d.node c.interpretation
        (HMDeclaredReconciliation.slotsFor (.letIn path) c.signatureIds))
      (d.node.original :: HMDeclaredReconciliation.guardedTypes d typeCaptures)
      [] d.node.inner.stripFound BoundsTy.fvar
      (localSlots (some d.annotation) BoundsTy.bvar
        (c.signatureIds.map BoundsTy.fvar)) := by
  let cert := HMDeclaredRHS.certifySource c rhs
    (fun b member => by cases member)
    (fun b member => by cases member)
    (fun b member => by cases member)
    (fun b member => by cases member)
  exact cert.sourceSlots c.rhsSlots (by
    intro i inside
    exact declaredLocalSlotsAgree c i (by
      simpa [HMDeclaredReconciliation.slotLimit] using inside))

/-- The same exact source certificate may retain a surrounding recursive
    environment. Its templates must be represented among the reconciliation
    guards, and their captured count coordinates must stay outside the local
    telescope, exactly as required by the universal RHS certificate. -/
def declaredCapturedLocalCertificate {output path d quantified premises typeCaptures env}
    (c : @HMDeclaredReconciliation.Checked output (.letIn path) d
      quantified [] premises typeCaptures)
    (rhs : HMDeclaredRHS.Checked c env)
    (represented : ∀ b, .recursive b ∈ env → b.template.hm.body ∈ typeCaptures)
    (exportsRepresented : ∀ s, .exported s ∈ env → s.hm.body ∈ typeCaptures)
    (countFresh : ∀ b, .recursive b ∈ env →
      ∀ i ∈ b.template.counts.captures, i ∉ quantified)
    (exportCountFresh : ∀ s, .exported s ∈ env →
      ∀ i ∈ s.counts.captures, i ∉ quantified) :
    RecursiveHMUniversal.Certified c.interface.scheme
      (ScopedHMInterpretation.AtNode.view d.node c.interpretation
        (HMDeclaredReconciliation.slotsFor (.letIn path) c.signatureIds))
      (d.node.original :: HMDeclaredReconciliation.guardedTypes d typeCaptures)
      (env.map (mapBinding c.interpretation c.interpretationLC))
      d.node.inner.stripFound BoundsTy.fvar
      (localSlots (some d.annotation) BoundsTy.bvar
        (c.signatureIds.map BoundsTy.fvar)) := by
  let cert := HMDeclaredRHS.certifySource c rhs represented exportsRepresented
    countFresh exportCountFresh
  exact cert.sourceSlots c.rhsSlots (by
    intro i inside
    exact declaredLocalSlotsAgree c i (by
      simpa [HMDeclaredReconciliation.slotLimit] using inside))

theorem declaredLocalCertificate_runtimeReady {output path d quantified premises typeCaptures}
    (c : @HMDeclaredReconciliation.Checked output (.letIn path) d
      quantified [] premises typeCaptures)
    (rhs : HMDeclaredRHS.Checked c [])
    (ready : ScopedDerives.RuntimeReady rhs.located.typed.derivation) :
    ScopedDerives.RuntimeReady (declaredLocalCertificate c rhs).typing := by
  let base := HMDeclaredRHS.certifySource c rhs
    (fun b member => by cases member)
    (fun b member => by cases member)
    (fun b member => by cases member)
    (fun b member => by cases member)
  have baseReady : ScopedDerives.RuntimeReady base.typing :=
    HMDeclaredRHS.certifySource_runtimeReady c rhs
      (fun b member => by cases member)
      (fun b member => by cases member)
      (fun b member => by cases member)
      (fun b member => by cases member) ready
  have moved := RecursiveHMUniversal.Certified.sourceSlots_runtimeReady base c.rhsSlots
    (by
      intro i inside
      exact declaredLocalSlotsAgree c i (by
        simpa [HMDeclaredReconciliation.slotLimit] using inside)) baseReady
  simpa only [declaredLocalCertificate] using moved

theorem declaredCapturedLocalCertificate_runtimeReady
    {output path d quantified premises typeCaptures env}
    (c : @HMDeclaredReconciliation.Checked output (.letIn path) d
      quantified [] premises typeCaptures)
    (rhs : HMDeclaredRHS.Checked c env)
    (represented : ∀ b, .recursive b ∈ env → b.template.hm.body ∈ typeCaptures)
    (exportsRepresented : ∀ s, .exported s ∈ env → s.hm.body ∈ typeCaptures)
    (countFresh : ∀ b, .recursive b ∈ env →
      ∀ i ∈ b.template.counts.captures, i ∉ quantified)
    (exportCountFresh : ∀ s, .exported s ∈ env →
      ∀ i ∈ s.counts.captures, i ∉ quantified)
    (ready : ScopedDerives.RuntimeReady rhs.located.typed.derivation) :
    ScopedDerives.RuntimeReady
      (declaredCapturedLocalCertificate c rhs represented exportsRepresented
        countFresh exportCountFresh).typing := by
  let base := HMDeclaredRHS.certifySource c rhs represented exportsRepresented
    countFresh exportCountFresh
  have baseReady : ScopedDerives.RuntimeReady base.typing :=
    HMDeclaredRHS.certifySource_runtimeReady c rhs represented exportsRepresented
      countFresh exportCountFresh ready
  have moved := RecursiveHMUniversal.Certified.sourceSlots_runtimeReady base c.rhsSlots
    (by
      intro i inside
      exact declaredLocalSlotsAgree c i (by
        simpa [HMDeclaredReconciliation.slotLimit] using inside)) baseReady
  simpa only [declaredCapturedLocalCertificate] using moved

/-- Specialize opaque lexical annotation slots after source counts. Full type
    arguments are inserted last, so their caller-owned counts are untouched. -/
theorem localSlots_specialize (ann : Option PolyTy) (owned : List Nat)
    (rows : Bindings) (args : List BoundsTy) (distinct : owned.Nodup)
    (fit : (ann.map (·.paramCount)).getD 0 ≤ owned.length) :
    (fun i => mapFree (argument owned (SchemeUse.vector args))
      (bounds rows (localSlots ann BoundsTy.bvar (owned.map BoundsTy.fvar) i))) =
      localSlots ann BoundsTy.bvar args := by
  funext i
  unfold localSlots
  dsimp only
  split
  · rename_i inside
    have small : i < owned.length := Nat.lt_of_lt_of_le inside fit
    have ownedSlot : SchemeUse.vector (owned.map BoundsTy.fvar) i = .fvar owned[i] := by
      simp [SchemeUse.vector, List.getElem?_map, List.getElem?_eq_getElem small]
    simp only [ownedSlot, bounds, mapFree]
    exact argument_slot owned (SchemeUse.vector args) distinct i small
  · rfl

theorem localTypes_specialize (owned : List Nat) (rows : Bindings) (args : List BoundsTy) :
    (fun i => mapFree (argument owned (SchemeUse.vector args)) (bounds rows (.fvar i))) =
      localTypes owned BoundsTy.fvar args := by
  funext i
  rfl

inductive ScopedBodyDerives :
    (Nat → BoundsTy) → (Nat → BoundsTy) → List Nat → Bindings →
    List Constraint → List BodyBinding → Expr → BoundsTy → Prop where
  | literal {env p} : ScopedBodyDerives types slots ids rows Δ env (.primLit p) (boundInfoOfPrimLit p)
  | primBinOp {env op} : ScopedBodyDerives types slots ids rows Δ env (.primBinOp op) (Typed.primOpBounds op)
  | nil {env elem} : ScopedBodyDerives types slots ids rows Δ env (.ctor nilCtorName) (.list (.lit 0) (.lit 0) elem)
  | boolCtor {env name} : BoolBranches.IsCtor name →
      ScopedBodyDerives types slots ids rows Δ env (.ctor name) (.custom boolTyName [])
  | cons {env h t head elem lo hi} :
      ScopedBodyDerives types slots ids rows Δ env h head → ScopedBodyDerives types slots ids rows Δ env t (.list lo hi elem) →
      SemanticSub Δ head elem → ScopedBodyDerives types slots ids rows Δ env (.app (.app (.ctor consCtorName) h) t)
        (.list (.add lo (.lit 1)) (.add hi (.lit 1)) elem)
  | pair {env left right leftTy rightTy} :
      ScopedBodyDerives types slots ids rows Δ env left leftTy →
      ScopedBodyDerives types slots ids rows Δ env right rightTy →
      ScopedBodyDerives types slots ids rows Δ env
        (.app (.app (.ctor pairCtorName) left) right)
        (.custom pairTyName [leftTy, rightTy])
  | varMono {env i β} : env[i]? = some (.mono β) → ScopedBodyDerives types slots ids rows Δ env (.var i) β
  | varExported {env i s found caller} : env[i]? = some (.exported s) →
      (used : HMCountScheme.Use s Δ found caller) → ScopedBodyDerives types slots ids rows Δ env (.var i) used.bounds
  | app {env f arg domain actual result} :
      ScopedBodyDerives types slots ids rows Δ env f (.arrow domain result) → ScopedBodyDerives types slots ids rows Δ env arg actual →
      SemanticSub Δ actual domain → ScopedBodyDerives types slots ids rows Δ env (.app f arg) result
  | subsumption {env e actual demand} :
      ScopedBodyDerives types slots ids rows Δ env e actual → SemanticSub Δ actual demand →
      ScopedBodyDerives types slots ids rows Δ env e demand
  | lambda {env ann body param result} :
      ScopedHMAnnotation.ParamOK types slots ids rows Δ ann param →
      ScopedBodyDerives types slots ids rows Δ (.mono param :: env) body result →
      ScopedBodyDerives types slots ids rows Δ env (.lambda ann body) (.arrow param result)
  | letMono {env ann rhs body actual result} :
      ScopedHMAnnotation.BindingOK types slots ids rows Δ ann actual →
      ScopedBodyDerives types slots ids rows Δ env rhs actual → ScopedBodyDerives types slots ids rows Δ (.mono actual :: env) body result →
      ScopedBodyDerives types slots ids rows Δ env (.letIn ann rhs body) result
  | letExported {env ann rhs body s result} (frame : LocalFrame s ids rhs) :
      LocalAnnotationOK s ann → rhs.varsBelow env.length = true →
      (∀ calleeΔ found caller (used : HMCountScheme.Use s calleeΔ found caller),
        ScopedBodyDerives (localTypes frame.owned types used.types) (localSlots ann slots used.types)
          (s.counts.quantified ++ s.counts.captures ++ ids)
          (CountAlgebra.compose (s.counts.quantified.zip used.counts) rows)
          (Δ ++ used.countInstance.premises) env rhs used.bounds) →
      ScopedBodyDerives types slots ids rows Δ (.exported s :: env) body result →
      ScopedBodyDerives types slots ids rows Δ env (.letIn ann rhs body) result
  | match_ {env scrut branches result} {ctx : BodyBranchContext} {actuals : Nat → BoundsTy} :
      ScopedBodyDerives types slots ids rows Δ env scrut ctx.bounds → ctx.Covers Δ branches →
      (∀ br ∈ branches, ctx.Pattern br.1) →
      (∀ i br, branches[i]? = some br →
        ScopedBodyDerives types slots ids rows (Δ ++ ctx.refine br.1) (ctx.extend br.1 env) br.2 (actuals i)) →
      (∀ i br, branches[i]? = some br → SemanticSub (Δ ++ ctx.refine br.1) (actuals i) result) →
      ScopedBodyDerives types slots ids rows Δ env (.match_ scrut branches) result
  | letRec {output metadata path vectors captures premises bodyTypes outerEnv bodyResult}
      (g : HMDeclaredGroup.Checked output metadata path vectors captures premises bodyTypes outerEnv) :
      (∀ caller (f : Nat → BoundsTy) (lc : ∀ i, (Synth.BoundsTy.toTy (f i)).IsLC)
        (scope : ∀ i, BoundsScoped caller (f i))
        (_fixed : CapturesFixed f (g.interfaces.contracts.map Binding.recursive ++ outerEnv)),
        Members f lc scope g.members) →
      ScopedBodyDerives types slots ids rows Δ
        (g.exports.map BodyBinding.exported ++ ordinaryBodyEnv outerEnv)
        g.body.stripFound bodyResult →
      ScopedBodyDerives types slots ids rows Δ (ordinaryBodyEnv outerEnv)
        (.letRec g.annotations (g.rhss.map Expr.stripFound) g.body.stripFound) bodyResult

/-- Identity-interpreted compatibility view of the same body judgment. -/
abbrev BodyDerives := ScopedBodyDerives BoundsTy.fvar BoundsTy.bvar

/-- Semantic interval weakening cannot change a literal's HM primitive type. -/
theorem ScopedBodyDerives.primLitBounds {types slots ids rows Δ env e β}
    (h : ScopedBodyDerives types slots ids rows Δ env e β) :
    ∀ p, e = .primLit p → β = boundInfoOfPrimLit p := by
  induction h with
  | literal => intro p source; cases source; rfl
  | subsumption _ sub ih =>
      intro p source
      rw [ih p source] at sub
      cases p <;> cases sub <;> rfl
  | primBinOp | nil | boolCtor | cons | pair | varMono | varExported | app | lambda |
      letMono | letExported | match_ | letRec => intro p source; cases source

/-- Ordinary RHS proofs can be reused for local introduction in mono captured
    environments. This does not turn fixed recursive assumptions into universal
    exports: environments containing such assumptions are deliberately excluded. -/
def OrdinaryEnv (env : List Binding) : Prop := ∀ c, Binding.recursive c ∉ env

private theorem OrdinaryEnv.consMono {env β} (ordinary : OrdinaryEnv env) :
    OrdinaryEnv (.mono β :: env) := by
  intro c
  simpa using ordinary c

private theorem OrdinaryEnv.branch {env p lo hi elem} (ordinary : OrdinaryEnv env) :
    OrdinaryEnv (branchEnv p lo hi elem env) := by
  unfold branchEnv
  split
  · exact ordinary.consMono.consMono
  · exact ordinary

private theorem OrdinaryEnv.pairBranch {env p left right} (ordinary : OrdinaryEnv env) :
    OrdinaryEnv (pairBranchEnv p left right env) := by
  unfold pairBranchEnv
  split
  · exact ordinary.consMono.consMono
  · exact ordinary

private theorem ordinaryBodyEnv_branch (env : List Binding) (p : MatchPattern)
    (lo hi : Count) (elem : BoundsTy) :
    ordinaryBodyEnv (branchEnv p lo hi elem env) =
      (BodyBranchContext.list lo hi elem).extend p (ordinaryBodyEnv env) := by
  simp only [branchEnv, BodyBranchContext.extend]
  split <;> rfl

private theorem ordinaryBodyEnv_pairBranch (env : List Binding) (p : MatchPattern)
    (left right : BoundsTy) :
    ordinaryBodyEnv (pairBranchEnv p left right env) =
      (BodyBranchContext.pair left right).extend p (ordinaryBodyEnv env) := by
  simp only [pairBranchEnv, BodyBranchContext.extend]
  split <;> rfl

/-- A recursive RHS assumption becomes the corresponding universally exported
    body binding. Each concrete recursive use already contains an external
    scheme use with the same counts, fixed HM arguments and demanded bounds. -/
theorem rhsToBody {types slots ids rows Δ env e β}
    (h : ScopedDerives types slots ids rows Δ env e β) :
    ScopedBodyDerives types slots ids rows Δ (ordinaryBodyEnv env) e β := by
  induction h with
  | literal => exact .literal
  | primBinOp => exact .primBinOp
  | nil => exact .nil
  | boolCtor ctor => exact .boolCtor ctor
  | cons _ _ sub ihh iht => exact .cons ihh iht sub
  | pair _ _ ihLeft ihRight => exact .pair ihLeft ihRight
  | varMono lookup =>
      exact .varMono (by simpa [ordinaryBodyEnv, List.getElem?_map, lookup, ordinaryBinding])
  | varRecursive lookup used =>
      exact .varExported
        (by simpa [ordinaryBodyEnv, List.getElem?_map, lookup, ordinaryBinding]) used.external
  | varExported lookup used =>
      exact .varExported
        (by simpa [ordinaryBodyEnv, List.getElem?_map, lookup, ordinaryBinding]) used
  | app _ _ sub ihf iha => exact .app ihf iha sub
  | lambda annotation _ ih =>
      simpa only [ordinaryBodyEnv, List.map_cons, ordinaryBinding] using
        ScopedBodyDerives.lambda annotation ih
  | letMono annotation _ _ ihr ihb =>
      simpa only [ordinaryBodyEnv, List.map_cons, ordinaryBinding] using
        ScopedBodyDerives.letMono annotation ihr ihb
  | matchList _ coverage patterns bodies subs ihs ihb =>
      refine .match_ (ctx := .list _ _ _) ihs coverage patterns ?_ subs
      intro i br atIndex
      simpa only [ordinaryBodyEnv_branch] using ihb i br atIndex
  | matchBool _ coverage patterns bodies subs ihs ihb =>
      refine .match_ (ctx := .bool) ihs coverage patterns ?_
        (by simpa [BodyBranchContext.refine] using subs)
      intro i br atIndex
      simpa [BodyBranchContext.extend, BodyBranchContext.refine] using ihb i br atIndex
  | matchPair _ coverage patterns bodies subs ihs ihb =>
      refine .match_ (ctx := .pair _ _) ihs coverage patterns ?_
        (by simpa [BodyBranchContext.refine] using subs)
      intro i br atIndex
      simpa [ordinaryBodyEnv_pairBranch, BodyBranchContext.refine] using ihb i br atIndex

#print axioms rhsToBody

theorem ordinaryRhsToBody {types slots ids rows Δ env e β}
    (h : ScopedDerives types slots ids rows Δ env e β) :
    OrdinaryEnv env → ScopedBodyDerives types slots ids rows Δ (ordinaryBodyEnv env) e β := by
  induction h with
  | literal => intro _; exact .literal
  | primBinOp => intro _; exact .primBinOp
  | nil => intro _; exact .nil
  | boolCtor ctor => intro _; exact .boolCtor ctor
  | cons _ _ sub ihh iht => intro ordinary; exact .cons (ihh ordinary) (iht ordinary) sub
  | pair _ _ ihLeft ihRight => intro ordinary; exact .pair (ihLeft ordinary) (ihRight ordinary)
  | varMono lookup =>
      intro _
      exact .varMono (by simpa [ordinaryBodyEnv, List.getElem?_map, lookup, ordinaryBinding])
  | varRecursive lookup used =>
      intro ordinary
      exact False.elim (ordinary _ (List.mem_of_getElem? lookup))
  | varExported lookup used =>
      intro _
      exact .varExported
        (by simpa [ordinaryBodyEnv, List.getElem?_map, lookup, ordinaryBinding]) used
  | app _ _ sub ihf iha => intro ordinary; exact .app (ihf ordinary) (iha ordinary) sub
  | lambda annotation _ ih => intro ordinary; exact .lambda annotation (ih ordinary.consMono)
  | letMono annotation _ _ ihr ihb =>
      intro ordinary
      exact .letMono annotation (ihr ordinary) (ihb ordinary.consMono)
  | matchList _ coverage patterns bodies subs ihs ihb =>
      intro ordinary
      refine .match_ (ctx := .list _ _ _) (ihs ordinary) coverage patterns ?_ subs
      intro i br atIndex
      simpa only [ordinaryBodyEnv_branch] using ihb i br atIndex ordinary.branch
  | matchBool _ coverage patterns bodies subs ihs ihb =>
      intro ordinary
      refine .match_ (ctx := .bool) (ihs ordinary) coverage patterns ?_
        (by simpa [BodyBranchContext.refine] using subs)
      intro i br atIndex
      simpa [BodyBranchContext.extend, BodyBranchContext.refine] using ihb i br atIndex ordinary
  | matchPair _ coverage patterns bodies subs ihs ihb =>
      intro ordinary
      refine .match_ (ctx := .pair _ _) (ihs ordinary) coverage patterns ?_
        (by simpa [BodyBranchContext.refine] using subs)
      intro i br atIndex
      simpa [ordinaryBodyEnv_pairBranch, BodyBranchContext.refine] using
        ihb i br atIndex ordinary.pairBranch

private theorem body_getElem?_append_left {env tail : List BodyBinding} {i : Nat}
    {binding : BodyBinding}
    (lookup : env[i]? = some binding) : (env ++ tail)[i]? = some binding := by
  obtain ⟨inside, rfl⟩ := List.getElem?_eq_some_iff.mp lookup
  rw [List.getElem?_append_left inside, lookup]

private theorem BodyBranchContext.extend_append (ctx : BodyBranchContext)
    (pattern : MatchPattern) (env tail : List BodyBinding) :
    ctx.extend pattern (env ++ tail) = ctx.extend pattern env ++ tail := by
  cases ctx with
  | bool => rfl
  | pair left right =>
      by_cases pair : pattern = .named pairCtorName 2
      · simp [BodyBranchContext.extend, pair]
      · simp [BodyBranchContext.extend, pair]
  | list lo hi elem =>
      by_cases cons : pattern = .named consCtorName 2
      · simp [BodyBranchContext.extend, cons]
      · simp [BodyBranchContext.extend, cons]

/-- The source recursive environment remains the de Bruijn prefix; unrelated
    surrounding body bindings may be appended without changing any lookup. -/
theorem rhsToBodyAppend {types slots ids rows Δ env e β}
    (h : ScopedDerives types slots ids rows Δ env e β) (tail : List BodyBinding) :
    ScopedBodyDerives types slots ids rows Δ (ordinaryBodyEnv env ++ tail) e β := by
  induction h with
  | literal => exact .literal
  | primBinOp => exact .primBinOp
  | nil => exact .nil
  | boolCtor ctor => exact .boolCtor ctor
  | cons _ _ sub ihh iht => exact .cons ihh iht sub
  | pair _ _ ihLeft ihRight => exact .pair ihLeft ihRight
  | varMono lookup =>
      exact .varMono (body_getElem?_append_left (by
        simpa [ordinaryBodyEnv, List.getElem?_map, lookup, ordinaryBinding]))
  | varRecursive lookup used =>
      exact .varExported (body_getElem?_append_left (by
        simpa [ordinaryBodyEnv, List.getElem?_map, lookup, ordinaryBinding])) used.external
  | varExported lookup used =>
      exact .varExported (body_getElem?_append_left (by
        simpa [ordinaryBodyEnv, List.getElem?_map, lookup, ordinaryBinding])) used
  | app _ _ sub ihf iha => exact .app ihf iha sub
  | lambda annotation _ ih =>
      simpa only [ordinaryBodyEnv, List.map_cons, List.cons_append, ordinaryBinding] using
        ScopedBodyDerives.lambda annotation ih
  | letMono annotation _ _ ihr ihb =>
      simpa only [ordinaryBodyEnv, List.map_cons, List.cons_append, ordinaryBinding] using
        ScopedBodyDerives.letMono annotation ihr ihb
  | matchList _ coverage patterns bodies subs ihs ihb =>
      refine .match_ (ctx := .list _ _ _) ihs coverage patterns ?_ subs
      intro i br atIndex
      simpa only [ordinaryBodyEnv_branch, BodyBranchContext.extend_append] using ihb i br atIndex
  | matchBool _ coverage patterns bodies subs ihs ihb =>
      refine .match_ (ctx := .bool) ihs coverage patterns ?_
        (by simpa [BodyBranchContext.refine] using subs)
      intro i br atIndex
      simpa [BodyBranchContext.extend, BodyBranchContext.refine,
        BodyBranchContext.extend_append] using ihb i br atIndex
  | matchPair _ coverage patterns bodies subs ihs ihb =>
      refine .match_ (ctx := .pair _ _) ihs coverage patterns ?_
        (by simpa [BodyBranchContext.refine] using subs)
      intro i br atIndex
      simpa [ordinaryBodyEnv_pairBranch, BodyBranchContext.refine,
        BodyBranchContext.extend_append] using ihb i br atIndex

#print axioms rhsToBodyAppend

/-- Append an unused outer body environment to an ordinary RHS derivation.
    De Bruijn indices retain their original prefix, so this is the precise
    weakening needed by a closed generalized local nested in a larger body. -/
theorem ordinaryRhsToBodyAppend {types slots ids rows Δ env e β}
    (h : ScopedDerives types slots ids rows Δ env e β)
    (ordinary : OrdinaryEnv env) (tail : List BodyBinding) :
    ScopedBodyDerives types slots ids rows Δ (ordinaryBodyEnv env ++ tail) e β := by
  induction h with
  | literal => exact .literal
  | primBinOp => exact .primBinOp
  | nil => exact .nil
  | boolCtor ctor => exact .boolCtor ctor
  | cons _ _ sub ihh iht => exact .cons (ihh ordinary) (iht ordinary) sub
  | pair _ _ ihLeft ihRight => exact .pair (ihLeft ordinary) (ihRight ordinary)
  | varMono lookup =>
      exact .varMono (body_getElem?_append_left (by
        simpa [ordinaryBodyEnv, List.getElem?_map, lookup, ordinaryBinding]))
  | varRecursive lookup used => exact False.elim (ordinary _ (List.mem_of_getElem? lookup))
  | varExported lookup used =>
      exact .varExported (body_getElem?_append_left (by
        simpa [ordinaryBodyEnv, List.getElem?_map, lookup, ordinaryBinding])) used
  | app _ _ sub ihf iha => exact .app (ihf ordinary) (iha ordinary) sub
  | lambda annotation _ ih =>
      simpa only [ordinaryBodyEnv, List.map_cons, List.cons_append, ordinaryBinding] using
        ScopedBodyDerives.lambda annotation (ih ordinary.consMono)
  | letMono annotation _ _ ihr ihb =>
      simpa only [ordinaryBodyEnv, List.map_cons, List.cons_append, ordinaryBinding] using
        ScopedBodyDerives.letMono annotation (ihr ordinary) (ihb ordinary.consMono)
  | matchList _ coverage patterns bodies subs ihs ihb =>
      refine .match_ (ctx := .list _ _ _) (ihs ordinary) coverage patterns ?_ subs
      intro i br atIndex
      simpa only [ordinaryBodyEnv_branch, BodyBranchContext.extend_append] using
        ihb i br atIndex ordinary.branch
  | matchBool _ coverage patterns bodies subs ihs ihb =>
      refine .match_ (ctx := .bool) (ihs ordinary) coverage patterns ?_
        (by simpa [BodyBranchContext.refine] using subs)
      intro i br atIndex
      simpa [BodyBranchContext.refine, BodyBranchContext.extend,
        BodyBranchContext.extend_append] using ihb i br atIndex ordinary
  | matchPair _ coverage patterns bodies subs ihs ihb =>
      refine .match_ (ctx := .pair _ _) (ihs ordinary) coverage patterns ?_
        (by simpa [BodyBranchContext.refine] using subs)
      intro i br atIndex
      simpa [ordinaryBodyEnv_pairBranch, BodyBranchContext.refine,
        BodyBranchContext.extend_append] using ihb i br atIndex ordinary.pairBranch

namespace BodyDerives
abbrev literal := @ScopedBodyDerives.literal BoundsTy.fvar BoundsTy.bvar
abbrev primBinOp := @ScopedBodyDerives.primBinOp BoundsTy.fvar BoundsTy.bvar
abbrev nil := @ScopedBodyDerives.nil BoundsTy.fvar BoundsTy.bvar
abbrev boolCtor := @ScopedBodyDerives.boolCtor BoundsTy.fvar BoundsTy.bvar
abbrev cons := @ScopedBodyDerives.cons BoundsTy.fvar BoundsTy.bvar
abbrev pair := @ScopedBodyDerives.pair BoundsTy.fvar BoundsTy.bvar
abbrev varMono := @ScopedBodyDerives.varMono BoundsTy.fvar BoundsTy.bvar
abbrev varExported {ids rows Δ env i s found caller}
    (lookup : env[i]? = some (BodyBinding.exported s)) (used : HMCountScheme.Use s Δ found caller) :
    BodyDerives ids rows Δ env (.var i) used.bounds := ScopedBodyDerives.varExported lookup used
abbrev app := @ScopedBodyDerives.app BoundsTy.fvar BoundsTy.bvar
abbrev subsumption := @ScopedBodyDerives.subsumption BoundsTy.fvar BoundsTy.bvar
abbrev lambda := @ScopedBodyDerives.lambda BoundsTy.fvar BoundsTy.bvar
abbrev letMono := @ScopedBodyDerives.letMono BoundsTy.fvar BoundsTy.bvar
abbrev match_ := @ScopedBodyDerives.match_ BoundsTy.fvar BoundsTy.bvar
abbrev letRec := @ScopedBodyDerives.letRec BoundsTy.fvar BoundsTy.bvar
end BodyDerives

theorem BodyBranchContext.Covers.assuming {ctx : BodyBranchContext} {Δ Δ' branches}
    (h : ctx.Covers Δ branches) (hp : (⟨Δ', Δ⟩ : ForallProblem).Valid) :
    ctx.Covers Δ' branches := by
  cases ctx with
  | list => exact ListBranches.Covers.assuming h hp
  | bool => exact h
  | pair => exact h

/-- Established caller/path premises transport the ENTIRE generalized body,
    including original source obligations, all match arms and group introduction.
    Callee premises are still discharged, never merely appended as assumptions. -/
theorem ScopedBodyDerives.assuming {types slots ids rows Δ Δ' env e β}
    (h : ScopedBodyDerives types slots ids rows Δ env e β) (hp : (⟨Δ', Δ⟩ : ForallProblem).Valid) :
    ScopedBodyDerives types slots ids rows Δ' env e β := by
  induction h generalizing Δ' with
  | literal => exact .literal
  | primBinOp => exact .primBinOp
  | nil => exact .nil
  | boolCtor hn => exact .boolCtor hn
  | cons _ _ sub ihh iht => exact .cons (ihh hp) (iht hp) (sub.assuming hp)
  | pair _ _ ihLeft ihRight => exact .pair (ihLeft hp) (ihRight hp)
  | varMono lookup => exact .varMono lookup
  | varExported lookup used =>
      let next : HMCountScheme.Use _ Δ' _ _ :=
        ⟨used.counts, used.countInstance, (fun σ hΔ => used.usable σ (hp σ hΔ)),
          used.types, used.arity, used.typesLC, used.typesScoped, used.shape⟩
      exact .varExported lookup next
  | app _ _ sub ihf iha => exact .app (ihf hp) (iha hp) (sub.assuming hp)
  | subsumption _ sub ih => exact .subsumption (ih hp) (sub.assuming hp)
  | lambda param _ ih => exact .lambda (param_assuming param hp) (ih hp)
  | letMono obligation _ _ ihr ihb =>
      exact .letMono (binding_assuming obligation hp) (ihr hp) (ihb hp)
  | letExported frame annotation scope _ _ ihr ihb =>
      exact .letExported frame annotation scope
        (fun calleeΔ found caller used => ihr calleeΔ found caller used (RecursiveTyping.assuming_append hp))
        (ihb hp)
  | match_ _ coverage patterns _ subs ihs iharms =>
      exact .match_ (ihs hp) (coverage.assuming hp) patterns
        (fun i br hb => iharms i br hb (RecursiveTyping.assuming_append hp))
        (fun i br hb => (subs i br hb).assuming (RecursiveTyping.assuming_append hp))
  | letRec g universal _ ihbody => exact .letRec g universal (ihbody hp)

private theorem bodyBranches_scoped {depth branches}
    (bodies : ∀ br ∈ branches, br.2.varsBelow (depth + br.1.bindCount) = true) :
    BranchListClosed.varsBelow depth branches = true := by
  induction branches with
  | nil => rfl
  | cons br rest ih =>
      simp only [BranchListClosed.varsBelow, Bool.and_eq_true]
      exact ⟨bodies br (by simp), ih (fun br member => bodies br (List.mem_cons_of_mem _ member))⟩

theorem BodyBranchContext.extend_length {ctx : BodyBranchContext} {pat env}
    (pattern : ctx.Pattern pat) : (ctx.extend pat env).length = env.length + pat.bindCount := by
  cases ctx with
  | list lo hi elem =>
      rcases pattern with rfl | rfl | rfl <;>
        simp [BodyBranchContext.extend, MatchPattern.bindCount, nilCtorName, consCtorName]
  | bool => rcases pattern with rfl | rfl | rfl <;> rfl
  | pair left right =>
      rcases pattern with rfl | rfl <;>
        simp [BodyBranchContext.extend, MatchPattern.bindCount]

theorem ScopedBodyDerives.varsBelow {types slots ids rows Δ env e β}
    (h : ScopedBodyDerives types slots ids rows Δ env e β) : e.varsBelow env.length = true := by
  induction h with
  | literal | primBinOp | nil | boolCtor => rfl
  | cons _ _ _ ihh iht => simp [Expr.varsBelow, ihh, iht]
  | pair _ _ ihLeft ihRight => simp [Expr.varsBelow, ihLeft, ihRight]
  | varMono lookup | varExported lookup _ =>
      obtain ⟨small, _⟩ := List.getElem?_eq_some_iff.mp lookup
      simpa only [Expr.varsBelow, decide_eq_true_eq] using small
  | app _ _ _ ihf iha => simp [Expr.varsBelow, ihf, iha]
  | subsumption _ _ ih => exact ih
  | lambda _ _ ih => simpa only [Expr.varsBelow, List.length_cons] using ih
  | letMono _ _ _ ihr ihb =>
      simp only [Expr.varsBelow, Bool.and_eq_true]
      exact ⟨ihr, by simpa only [List.length_cons] using ihb⟩
  | letExported _ _ scope _ _ _ ihb =>
      simp only [Expr.varsBelow, Bool.and_eq_true]
      exact ⟨scope, by simpa only [List.length_cons] using ihb⟩
  | match_ _ _ patterns _ _ ihs ihb =>
      simp only [Expr.varsBelow, Bool.and_eq_true]
      refine ⟨ihs, bodyBranches_scoped ?_⟩
      intro br member
      obtain ⟨i, atIndex⟩ := List.mem_iff_getElem?.mp member
      simpa only [BodyBranchContext.extend_length (patterns br member)] using ihb i br atIndex
  | letRec g _ _ ihbody =>
      apply Runtime.letRec_scoped
      · intro rhs member
        simpa only [ordinaryBodyEnv, List.length_map, Nat.add_comm] using
          g.rhssScopedCaptured rhs member
      · simpa only [List.length_append, List.length_map, g.exportCount,
          ordinaryBodyEnv, Nat.add_comm] using ihbody

theorem BodyEnvAt.closes {bound free σ budget env types slots ids rows Δ expr β}
    (e : BodyEnvAt bound free σ budget env) (h : ScopedBodyDerives types slots ids rows Δ env expr β) :
    (expr.substN 0 e.terms).varsBelow 0 = true := by
  apply Runtime.closing_scoped e.terms e.closed expr 0
  simpa only [Nat.zero_add, e.arity] using h.varsBelow

#print axioms ScopedBodyDerives.varsBelow

namespace BodyDerives
theorem assuming {ids rows Δ Δ' env e β} (h : BodyDerives ids rows Δ env e β)
    (hp : (⟨Δ', Δ⟩ : ForallProblem).Valid) : BodyDerives ids rows Δ' env e β :=
  ScopedBodyDerives.assuming h hp
theorem varsBelow {ids rows Δ env e β} (h : BodyDerives ids rows Δ env e β) :
    e.varsBelow env.length = true := ScopedBodyDerives.varsBelow h
end BodyDerives

theorem BodyEnvAt.listBranch {bound free σ budget env lo hi elem v len name args pat body branches}
    (e : BodyEnvAt bound free σ budget env)
    (hb : Runtime.TypeEnv.Downward bound) (hf : Runtime.TypeEnv.Downward free)
    (list : Runtime.ListValue (Runtime.ValueAt bound free σ (budget + 1) elem) v len)
    (contained : (⟨lo, hi⟩ : Interval).Contains σ (.ofNat len))
    (applied : SmallStep.CtorAppliedTo v name args)
    (selected : SmallStep.FirstMatchingBranch name args.length branches pat body)
    (pattern : RecursiveTyping.ListPattern pat) :
    (∀ p ∈ RecursiveTyping.branchRefine pat lo hi, p.Holds σ) ∧
      ∃ opened : BodyEnvAt bound free σ budget ((BodyBranchContext.list lo hi elem).extend pat env),
        opened.terms = args.take pat.bindCount ++ e.terms := by
  rcases pattern with rfl | rfl | rfl
  · simp only [RecursiveTyping.branchRefine, BodyBranchContext.extend, MatchPattern.bindCount,
      List.take_zero, List.nil_append]
    exact ⟨by simp [nilCtorName, consCtorName], by simpa [nilCtorName, consCtorName] using ⟨e, rfl⟩⟩
  · cases list with
    | nil =>
        obtain ⟨rfl, rfl⟩ := applied.det (.base nilCtorName)
        simp only [RecursiveTyping.branchRefine, BodyBranchContext.extend, MatchPattern.bindCount,
          List.take_zero, List.nil_append]
        exact ⟨by simpa using ListBranches.nil_refine contained,
          by simpa [nilCtorName, consCtorName] using ⟨e, rfl⟩⟩
    | @cons headTerm tailTerm n head tail =>
        have canonical : SmallStep.CtorAppliedTo _ consCtorName [headTerm, tailTerm] :=
          .step (.step (.base consCtorName))
        obtain ⟨rfl, rfl⟩ := applied.det canonical
        have fires := selected.ctor_eq
        simp [MatchPattern.matchesCtor, nilCtorName, consCtorName] at fires
  · cases list with
    | nil =>
        obtain ⟨rfl, rfl⟩ := applied.det (.base nilCtorName)
        have fires := selected.ctor_eq
        simp [MatchPattern.matchesCtor, nilCtorName, consCtorName] at fires
    | @cons headTerm tailTerm n head tail =>
        have canonical : SmallStep.CtorAppliedTo _ consCtorName [headTerm, tailTerm] :=
          .step (.step (.base consCtorName))
        obtain ⟨rfl, rfl⟩ := applied.det canonical
        have headFacts := head
        rw [Runtime.ValueAt.eq_def] at headFacts
        have tailValue := tail.value (fun v hv => by rw [Runtime.ValueAt.eq_def] at hv; exact hv.1)
        have tailClosed := tail.closed (fun v hv => by rw [Runtime.ValueAt.eq_def] at hv; exact hv.2.1)
        have tailBounds : Runtime.ValueAt bound free σ (budget + 1)
            (.list (.pred lo) (.pred hi) elem) tailTerm := by
          rw [Runtime.ValueAt]
          exact ⟨tailValue, tailClosed, n, tail, ListBranches.tail_contains contained⟩
        let opened := (e.extendMono (.list (.pred lo) (.pred hi) elem) tailTerm tailClosed
          (Runtime.TermAt.value tailValue (tailBounds.down hb hf (by omega)))).extendMono
            elem headTerm headFacts.2.1
            (Runtime.TermAt.value headFacts.1 (head.down hb hf (by omega)))
        refine ⟨?_, ?_⟩
        · simpa [RecursiveTyping.branchRefine, nilCtorName, consCtorName] using
            ListBranches.cons_refine contained
        · refine ⟨?_, ?_⟩
          · simpa only [BodyBranchContext.extend, if_pos rfl] using opened
          · rfl

theorem BodyEnvAt.pairBranch {bound free σ budget env leftTy rightTy left right pat}
    (e : BodyEnvAt bound free σ budget env)
    (hb : Runtime.TypeEnv.Downward bound) (hf : Runtime.TypeEnv.Downward free)
    (leftMeaning : Runtime.ValueAt bound free σ (budget + 1) leftTy left)
    (rightMeaning : Runtime.ValueAt bound free σ (budget + 1) rightTy right)
    (pattern : PairBranches.Pattern pat) :
    ∃ opened : BodyEnvAt bound free σ budget
        ((BodyBranchContext.pair leftTy rightTy).extend pat env),
      opened.terms = [left, right].take pat.bindCount ++ e.terms := by
  rcases pattern with rfl | rfl
  · simpa [BodyBranchContext.extend, MatchPattern.bindCount] using ⟨e, rfl⟩
  · have leftFacts := leftMeaning
    have rightFacts := rightMeaning
    rw [Runtime.ValueAt.eq_def] at leftFacts rightFacts
    let opened := (e.extendMono rightTy right rightFacts.2.1
      (Runtime.TermAt.value rightFacts.1 (rightMeaning.down hb hf (by omega)))).extendMono
        leftTy left leftFacts.2.1
        (Runtime.TermAt.value leftFacts.1 (leftMeaning.down hb hf (by omega)))
    refine ⟨?_, ?_⟩
    · simpa only [BodyBranchContext.extend, if_pos rfl] using opened
    · rfl

namespace BodyDerives

/-- Runtime-fragment evidence attached to the existing generalized-body
    derivation. Group evidence covers ALL original source members. -/
inductive RuntimeReady :
    {types slots : Nat → BoundsTy} → {ids : List Nat} → {rows : Bindings} →
    {Δ : List Constraint} → {env : List BodyBinding} → {e : Expr} → {β : BoundsTy} →
    ScopedBodyDerives types slots ids rows Δ env e β → Prop where
  | literal : RuntimeReady (.literal (p := p))
  | primBinOp : RuntimeReady (.primBinOp (op := op))
  | nil : Runtime.Supported elem → RuntimeReady (.nil (elem := elem))
  | boolCtor (nameOK : BoolBranches.IsCtor name) : RuntimeReady (.boolCtor nameOK)
  | cons {hh : ScopedBodyDerives types slots ids rows Δ env h head}
      {ht : ScopedBodyDerives types slots ids rows Δ env t (.list lo hi elem)}
      (sub : SemanticSub Δ head elem) : RuntimeReady hh → RuntimeReady ht →
      RuntimeReady (.cons hh ht sub)
  | pair {hleft : ScopedBodyDerives types slots ids rows Δ env left leftTy}
      {hright : ScopedBodyDerives types slots ids rows Δ env right rightTy} :
      RuntimeReady hleft → RuntimeReady hright → RuntimeReady (.pair hleft hright)
  | varMono (lookup : env[i]? = some (BodyBinding.mono β)) :
      Runtime.Supported β → RuntimeReady (.varMono lookup)
  | varExported (lookup : env[i]? = some (BodyBinding.exported s))
      (used : HMCountScheme.Use s Δ found caller) :
      Runtime.Supported used.bounds → (∀ a ∈ used.types, Runtime.Supported a) →
      RuntimeReady (.varExported lookup used)
  | app {actual : BoundsTy} {hfn : ScopedBodyDerives types slots ids rows Δ env f (.arrow domain result)}
      {ha : ScopedBodyDerives types slots ids rows Δ env arg actual}
      (sub : SemanticSub Δ actual domain) : RuntimeReady hfn → RuntimeReady ha →
      RuntimeReady (.app hfn ha sub)
  | subsumption {actual demand : BoundsTy}
      {h : ScopedBodyDerives types slots ids rows Δ env e actual}
      (sub : SemanticSub Δ actual demand) :
      RuntimeReady h → Runtime.Supported demand → RuntimeReady (.subsumption h sub)
  | lambda {param : BoundsTy}
      (annOK : ScopedHMAnnotation.ParamOK types slots ids rows Δ ann param)
      {hbody : ScopedBodyDerives types slots ids rows Δ (.mono param :: env) body result} :
      Runtime.Supported param → RuntimeReady hbody → RuntimeReady (.lambda annOK hbody)
  | letMono {actual : BoundsTy}
      (annOK : ScopedHMAnnotation.BindingOK types slots ids rows Δ ann actual)
      {hrhs : ScopedBodyDerives types slots ids rows Δ env rhs actual}
      {hbody : ScopedBodyDerives types slots ids rows Δ (.mono actual :: env) body result} :
      RuntimeReady hrhs → RuntimeReady hbody → RuntimeReady (.letMono annOK hrhs hbody)
  | letExported
      (frame : LocalFrame s ids rhs)
      (annotation : LocalAnnotationOK s ann) (scope : rhs.varsBelow env.length = true)
      (instances : ∀ calleeΔ found caller (used : HMCountScheme.Use s calleeΔ found caller),
        ScopedBodyDerives (localTypes frame.owned types used.types) (localSlots ann slots used.types)
          (s.counts.quantified ++ s.counts.captures ++ ids)
          (CountAlgebra.compose (s.counts.quantified.zip used.counts) rows)
          (Δ ++ used.countInstance.premises) env rhs used.bounds)
      {hbody : ScopedBodyDerives types slots ids rows Δ (.exported s :: env) body result} :
      (∀ calleeΔ found caller (used : HMCountScheme.Use s calleeΔ found caller),
        (∀ a ∈ used.types, Runtime.Supported a) → RuntimeReady (instances calleeΔ found caller used)) →
      RuntimeReady hbody → RuntimeReady (.letExported frame annotation scope instances hbody)
  | match_ {actuals : Nat → BoundsTy} {ctx : BodyBranchContext}
      {hs : ScopedBodyDerives types slots ids rows Δ env scrut ctx.bounds}
      (coverage : ctx.Covers Δ branches)
      (patterns : ∀ br ∈ branches, ctx.Pattern br.1)
      (bodies : ∀ i br, branches[i]? = some br →
        ScopedBodyDerives types slots ids rows (Δ ++ ctx.refine br.1) (ctx.extend br.1 env) br.2 (actuals i))
      (subs : ∀ i br, branches[i]? = some br →
        SemanticSub (Δ ++ ctx.refine br.1) (actuals i) result) :
      RuntimeReady hs → (∀ i br atIndex, RuntimeReady (bodies i br atIndex)) →
      Runtime.Supported result → RuntimeReady (.match_ hs coverage patterns bodies subs)
  | letRec
      (g : HMDeclaredGroup.Checked output metadata path vectors captures premises bodyTypes outerEnv)
      (universal : ∀ caller (f : Nat → BoundsTy) (lc : ∀ i, (Synth.BoundsTy.toTy (f i)).IsLC)
        (scope : ∀ i, BoundsScoped caller (f i))
        (_fixed : CapturesFixed f (g.interfaces.contracts.map Binding.recursive ++ outerEnv)),
        Members f lc scope g.members)
      {hbody : ScopedBodyDerives types slots ids rows Δ
        (g.exports.map BodyBinding.exported ++ ordinaryBodyEnv outerEnv)
        g.body.stripFound result} :
      (∀ offset (inside : offset < g.exports.length),
        ScopedDerives.RuntimeReady (g.members.memberAt offset inside).rhs.certificate.implementation.typing) →
      (∀ offset (inside : offset < g.exports.length),
        Runtime.Supported (g.members.memberAt offset inside).rhs.certificate.implementation.opening.bounds) →
      RecursiveArgumentsSupported outerEnv →
      RuntimeReady hbody → RuntimeReady (.letRec g universal hbody)

theorem RuntimeReady.supported {types slots ids rows Δ env e β} {h : ScopedBodyDerives types slots ids rows Δ env e β}
    (ready : RuntimeReady h) : Runtime.Supported β := by
  induction ready with
  | literal => cases ‹PrimLitExpr› <;> exact .prim
  | primBinOp => cases ‹PrimBinOp› <;> first | exact .arrow .prim (.arrow .prim .prim) | exact .arrow .prim (.arrow .prim .bool)
  | nil elem => exact .list elem
  | boolCtor => exact .bool
  | cons _ _ _ _ tail => cases tail with | list elem => exact .list elem
  | pair _ _ left right => exact .pair left right
  | varMono _ supported | varExported _ _ supported _ => exact supported
  | app _ _ _ fn _ => cases fn with | arrow _ result => exact result
  | subsumption _ _ demand => exact demand
  | lambda _ param _ result => exact .arrow param result
  | letMono _ _ _ _ body => exact body
  | letExported _ _ _ _ _ _ _ body => exact body
  | match_ _ _ _ _ _ _ result => exact result
  | letRec _ _ _ _ _ _ body => exact body

/-- Fundamental theorem for the supported generalized-body derivation. Closed
    group introduction discharges recursive assumptions from the actual checked
    members, rather than assuming their annotations describe runtime behavior. -/
theorem RuntimeReady.termAt {types slots ids rows Δ env expr β}
    {h : ScopedBodyDerives types slots ids rows Δ env expr β} (ready : RuntimeReady h)
    (bound free : Runtime.TypeEnv) (σ : Assign)
    (hb : Runtime.TypeEnv.Downward bound) (hf : Runtime.TypeEnv.Downward free) :
    ∀ budget, (∀ p ∈ Δ, p.Holds σ) → (e : BodyEnvAt bound free σ budget env) →
      Runtime.TermAt bound free σ budget β (expr.substN 0 e.terms) := by
  induction ready with
  | subsumption sub inner demand ih =>
      intro budget premises e
      exact (ih budget premises e).of_values
        (Runtime.subtype sub inner.supported demand bound free σ premises)
  | literal =>
      intro budget _ e
      exact Runtime.TermAt.value (.primLit _) (Runtime.ValueAt.literal bound free σ budget _)
  | primBinOp =>
      intro budget _ e
      exact Runtime.TermAt.value (.primBinOp _) (Runtime.ValueAt.primBinOp bound free σ budget _)
  | nil _ =>
      intro budget _ e
      exact Runtime.TermAt.value (.ctor _) (Runtime.ValueAt.nil bound free σ budget _)
  | boolCtor nameOK =>
      intro budget _ e
      exact Runtime.TermAt.value (.ctor _) (Runtime.ValueAt.bool bound free σ budget _ nameOK)
  | cons sub headReady tailReady ihh iht =>
      intro budget premises e
      have tailSupport := tailReady.supported
      cases tailSupport with
      | list elemSupport =>
          exact Runtime.TermAt.cons hb hf
            ((ihh budget premises e).of_values (Runtime.subtype sub headReady.supported elemSupport bound free σ premises))
            (iht budget premises e)
  | pair leftReady rightReady ihLeft ihRight =>
      intro budget premises e
      exact Runtime.TermAt.pair hb hf (ihLeft budget premises e) (ihRight budget premises e)
  | varMono lookup _ =>
      intro budget _ e
      exact e.varMono lookup
  | varExported lookup used _ arguments =>
      intro budget premises e
      exact e.varExported lookup used arguments premises
  | app sub fnReady argReady ihf iha =>
      intro budget premises e
      have fnSupport := fnReady.supported
      cases fnSupport with
      | arrow domainSupport _ =>
          exact Runtime.TermAt.app hb hf (ihf budget premises e)
            ((iha budget premises e).of_values
              (Runtime.subtype sub argReady.supported domainSupport bound free σ premises))
  | lambda annOK _ bodyReady ih =>
      intro budget premises e
      apply Runtime.TermAt.value (.lambda _ _)
      apply Runtime.ValueAt.lambda
      · exact e.closes (.lambda annOK (by assumption))
      · intro j before arg argument
        have facts := argument
        rw [Runtime.ValueAt.eq_def] at facts
        let opened := (e.down hb hf (by omega : j ≤ budget)).extendMono _ arg facts.2.1
          (Runtime.TermAt.value facts.1 (argument.down hb hf (by omega)))
        have bodySafe := ih j premises opened
        change Runtime.TermAt bound free σ j _ (Expr.substN 0 (arg :: e.terms) _) at bodySafe
        rw [Runtime.closing_singleton e.terms e.closed arg facts.2.1]
        exact bodySafe
  | letMono annOK rhsReady bodyReady ihr ihb =>
      intro budget premises e
      cases budget with
      | zero => unfold Runtime.TermAt; intro steps v _ before; omega
      | succ j =>
          have rhsClosed := e.closes (by assumption)
          let opened := (e.down hb hf (by omega : j ≤ j + 1)).extendMono _ _ rhsClosed
            (ihr j premises (e.down hb hf (by omega)))
          have bodySafe := ihb j premises opened
          apply Runtime.TermAt.prepend SmallStep.Step.letReduce
          change Runtime.TermAt bound free σ j _ (Expr.substN 0 (_ :: e.terms) _) at bodySafe
          rw [Runtime.closing_singleton e.terms e.closed _ rhsClosed]
          exact bodySafe
  | letExported frame annotation scope instances _ bodyReady ihr ihb =>
      rename_i s ownIds rhs ann ownEnv ownTypes ownSlots ownRows pathΔ body result hbody rhsReady
      intro budget premises e
      cases budget with
      | zero => unfold Runtime.TermAt; intro steps v _ before; omega
      | succ j =>
          have rhsClosed := Runtime.closing_scoped e.terms e.closed _ 0
            (by simpa only [Nat.zero_add, e.arity] using scope)
          let previous := e.down hb hf (by omega : j ≤ j + 1)
          have rhsSafe : BodyBindingAt bound free σ j (.exported s) (rhs.substN 0 e.terms) := by
            intro calleeΔ found caller used arguments rawPremises
            apply ihr calleeΔ found caller used arguments j ?_ previous
            intro p member
            rcases List.mem_append.mp member with outer | raw
            · exact premises p outer
            · exact rawPremises p raw
          let opened := previous.extend (.exported s) (rhs.substN 0 e.terms) rhsClosed rhsSafe
          have bodySafe := ihb j premises opened
          apply Runtime.TermAt.prepend SmallStep.Step.letReduce
          change Runtime.TermAt bound free σ j _ (Expr.substN 0 (_ :: e.terms) _) at bodySafe
          rw [Runtime.closing_singleton e.terms e.closed _ rhsClosed]
          exact bodySafe
  | match_ coverage patterns bodies subs scrutReady branchReady resultSupport ihs ihb =>
      rename_i pathΔ env' scrut branches result actuals ctx hs
      intro budget premises e
      rw [Runtime.closing_match]
      cases ctx with
      | list lo hi elem =>
          apply Runtime.TermAt.matchList (ihs budget premises e)
            (Runtime.listCoverage_close coverage e.terms) premises
          intro j before v len name args pat closedBody list contained applied selected
          obtain ⟨body, original, rfl⟩ := Runtime.firstMatch_unclose e.terms selected
          obtain ⟨i, atIndex⟩ := List.mem_iff_getElem?.mp original.mem
          obtain ⟨refined, opened, terms⟩ := (e.down hb hf (by omega : j ≤ budget)).listBranch
            hb hf list contained applied original (patterns _ original.mem)
          have path : ∀ p ∈ pathΔ ++ RecursiveTyping.branchRefine pat lo hi, p.Holds σ := by
            intro p member
            rcases List.mem_append.mp member with outer | localPath
            · exact premises p outer
            · exact refined p localPath
          have branchSafe := (ihb i (pat, body) atIndex j path opened).of_values
            (Runtime.subtype (subs i (pat, body) atIndex) (branchReady i _ atIndex).supported
              resultSupport bound free σ path)
          rw [terms] at branchSafe
          have contentsLength : (args.take pat.bindCount).length = pat.bindCount := by
            have arity := opened.arity
            rw [terms, List.length_append] at arity
            rw [BodyBranchContext.extend_length (patterns _ original.mem)] at arity
            change (args.take pat.bindCount).length + e.terms.length = env'.length + pat.bindCount at arity
            rw [e.arity] at arity
            omega
          have contentsClosed : ∀ term ∈ args.take pat.bindCount, term.varsBelow 0 = true := by
            intro term member
            exact opened.closed term (by rw [terms]; exact List.mem_append_left _ member)
          have closing := Runtime.closing_compose e.terms (args.take pat.bindCount) e.closed contentsClosed body 0
          simp only [Nat.zero_add, contentsLength] at closing
          rw [closing]
          exact branchSafe
      | bool =>
          apply Runtime.TermAt.matchBool (ihs budget premises e)
            (Runtime.boolCoverage_close coverage e.terms)
          intro j before name pat closedBody nameOK selected
          obtain ⟨body, original, rfl⟩ := Runtime.firstMatch_unclose e.terms selected
          obtain ⟨i, atIndex⟩ := List.mem_iff_getElem?.mp original.mem
          have zero : pat.bindCount = 0 := by
            rcases patterns _ original.mem with rfl | rfl | rfl <;> rfl
          simp only [zero, List.take_zero]
          rw [Expr.substN_of_closed (e.closes (bodies i (pat, body) atIndex))]
          have path : ∀ p ∈ pathΔ ++ (BodyBranchContext.bool).refine pat, p.Holds σ := by
            simpa only [BodyBranchContext.refine, List.append_nil] using premises
          exact (ihb i (pat, body) atIndex j path (e.down hb hf (by omega))).of_values
            (Runtime.subtype (subs i (pat, body) atIndex) (branchReady i _ atIndex).supported
              resultSupport bound free σ path)
      | pair leftTy rightTy =>
          apply Runtime.TermAt.matchPair (ihs budget premises e)
            (Runtime.pairCoverage_close coverage e.terms)
          intro j before left right pat closedBody leftMeaning rightMeaning selected
          obtain ⟨body, original, rfl⟩ := Runtime.firstMatch_unclose e.terms selected
          obtain ⟨i, atIndex⟩ := List.mem_iff_getElem?.mp original.mem
          obtain ⟨opened, terms⟩ := (e.down hb hf (by omega : j ≤ budget)).pairBranch
            hb hf leftMeaning rightMeaning (patterns _ original.mem)
          have path : ∀ p ∈ pathΔ ++ (BodyBranchContext.pair leftTy rightTy).refine pat,
              p.Holds σ := by
            simpa only [BodyBranchContext.refine, List.append_nil] using premises
          have branchSafe := (ihb i (pat, body) atIndex j path opened).of_values
            (Runtime.subtype (subs i (pat, body) atIndex) (branchReady i _ atIndex).supported
              resultSupport bound free σ path)
          rw [terms] at branchSafe
          have contentsLength : ([left, right].take pat.bindCount).length = pat.bindCount := by
            have arity := opened.arity
            rw [terms, List.length_append] at arity
            rw [BodyBranchContext.extend_length (patterns _ original.mem)] at arity
            change ([left, right].take pat.bindCount).length + e.terms.length =
              env'.length + pat.bindCount at arity
            rw [e.arity] at arity
            omega
          have contentsClosed : ∀ term ∈ [left, right].take pat.bindCount,
              term.varsBelow 0 = true := by
            intro term member
            exact opened.closed term (by rw [terms]; exact List.mem_append_left _ member)
          have closing := Runtime.closing_compose e.terms ([left, right].take pat.bindCount)
            e.closed contentsClosed body 0
          simp only [Nat.zero_add, contentsLength] at closing
          rw [closing]
          exact branchSafe
  | letRec g universal membersReady demandSupport outerArguments bodyReady ihbody =>
      intro budget premises e
      cases budget with
      | zero => unfold Runtime.TermAt; intro steps v _ before; omega
      | succ budget =>
          let previous := e.down hb hf (by omega : budget ≤ budget + 1)
          let realized := g.exportEnvironmentCaptured membersReady demandSupport outerArguments
            bound free σ hb hf budget previous
          have bodySafe := ihbody budget premises realized.val
          rw [realized.property] at bodySafe
          let closedRhss := closeOuterRhss (g.rhss.map Expr.stripFound) previous.terms
          let recursive := Runtime.recursiveTerms g.annotations closedRhss
          have closedScope : ∀ rhs ∈ closedRhss,
              rhs.varsBelow (g.rhss.map Expr.stripFound).length = true := by
            let outerRhs := previous.toEnvAt outerArguments
            apply closeOuterRhss_scoped outerRhs
            simpa only [ordinaryBodyEnv, List.length_map, Nat.add_comm] using
              g.rhssScopedCaptured
          have recursiveClosed : ∀ term ∈ recursive, term.varsBelow 0 = true := by
            apply Runtime.recursiveTerms_closed
            simpa only [closedRhss, closeOuterRhss_length] using closedScope
          have composed := Runtime.closing_compose previous.terms recursive previous.closed
            recursiveClosed g.body.stripFound 0
          have recursiveLength : recursive.length = (g.rhss.map Expr.stripFound).length := by
            simp only [recursive, Runtime.recursiveTerms, List.length_map,
              closedRhss, closeOuterRhss_length]
          rw [Nat.zero_add, recursiveLength] at composed
          rw [← composed] at bodySafe
          have sameTerms : previous.terms = e.terms := rfl
          rw [← sameTerms]
          simp only [Expr.substN, RecGroup.substN_eq_map, Nat.zero_add]
          change Runtime.TermAt bound free σ (budget + 1) _
            (.letRec g.annotations closedRhss
              (g.body.stripFound.substN (g.rhss.map Expr.stripFound).length previous.terms))
          exact Runtime.TermAt.prepend SmallStep.Step.letRecUnfold bodySafe

#print axioms RuntimeReady.supported
#print axioms RuntimeReady.termAt

theorem RuntimeReady.safeClosed {types slots ids rows Δ expr β}
    {h : ScopedBodyDerives types slots ids rows Δ [] expr β} (ready : RuntimeReady h)
    (bound free : Runtime.TypeEnv) (σ : Assign)
    (hb : Runtime.TypeEnv.Downward bound) (hf : Runtime.TypeEnv.Downward free)
    (premises : ∀ p ∈ Δ, p.Holds σ) : Runtime.Safe bound free σ β expr := by
  intro budget
  let empty : BodyEnvAt bound free σ budget [] :=
    ⟨[], rfl, by simp, by intro i inside; simp at inside⟩
  have safe := ready.termAt bound free σ hb hf budget premises empty
  simpa only [Expr.substN_of_closed h.varsBelow] using safe

#print axioms RuntimeReady.safeClosed

/-- Preserve the complete runtime fragment witness when established path
    premises strengthen the body context. The callee's raw premises, full HM
    vector and unused slots remain unchanged. -/
theorem RuntimeReady.assuming {types slots ids rows Δ Δ' env expr β}
    {h : ScopedBodyDerives types slots ids rows Δ env expr β} (ready : RuntimeReady h)
    (hp : (⟨Δ', Δ⟩ : ForallProblem).Valid) : RuntimeReady (h.assuming hp) := by
  induction ready generalizing Δ' with
  | literal => exact .literal
  | primBinOp => exact .primBinOp
  | nil elem => exact .nil elem
  | boolCtor nameOK => exact .boolCtor nameOK
  | cons sub _ _ ihh iht => exact .cons (sub.assuming hp) (ihh hp) (iht hp)
  | pair _ _ ihLeft ihRight => exact .pair (ihLeft hp) (ihRight hp)
  | varMono lookup supported => exact .varMono lookup supported
  | varExported lookup used supported arguments =>
      let next : HMCountScheme.Use _ Δ' _ _ :=
        ⟨used.counts, used.countInstance, (fun σ hΔ => used.usable σ (hp σ hΔ)),
          used.types, used.arity, used.typesLC, used.typesScoped, used.shape⟩
      exact .varExported lookup next supported arguments
  | app sub _ _ ihf iha => exact .app (sub.assuming hp) (ihf hp) (iha hp)
  | subsumption sub _ demand ih => exact .subsumption (sub.assuming hp) (ih hp) demand
  | lambda annOK param _ ih => exact .lambda (param_assuming annOK hp) param (ih hp)
  | letMono annOK _ _ ihr ihb => exact .letMono (binding_assuming annOK hp) (ihr hp) (ihb hp)
  | letExported frame annotation scope instances _ _ ihr ihb =>
      exact .letExported frame annotation scope
        (fun calleeΔ found caller used => (instances calleeΔ found caller used).assuming (RecursiveTyping.assuming_append hp))
        (fun calleeΔ found caller used arguments => ihr calleeΔ found caller used arguments (RecursiveTyping.assuming_append hp))
        (ihb hp)
  | match_ coverage patterns bodies subs _ _ result ihs ihb =>
      exact .match_ (coverage.assuming hp) patterns
        (fun i br atIndex => (bodies i br atIndex).assuming (RecursiveTyping.assuming_append hp))
        (fun i br atIndex => (subs i br atIndex).assuming (RecursiveTyping.assuming_append hp))
        (ihs hp) (fun i br atIndex => ihb i br atIndex (RecursiveTyping.assuming_append hp)) result
  | letRec g universal members demand outerArguments _ ihb =>
      exact .letRec g universal members demand outerArguments (ihb hp)

#print axioms RuntimeReady.assuming

end BodyDerives

private theorem RecursiveArgumentsSupported.consMono {env β}
    (supported : RecursiveArgumentsSupported env) :
    RecursiveArgumentsSupported (.mono β :: env) := by
  intro c member
  exact supported c (by simpa using member)

private theorem RecursiveArgumentsSupported.branch {env p lo hi elem}
    (supported : RecursiveArgumentsSupported env) :
    RecursiveArgumentsSupported (branchEnv p lo hi elem env) := by
  unfold branchEnv
  split
  · exact supported.consMono.consMono
  · exact supported

private theorem RecursiveArgumentsSupported.pairBranch {env p left right}
    (supported : RecursiveArgumentsSupported env) :
    RecursiveArgumentsSupported (pairBranchEnv p left right env) := by
  unfold pairBranchEnv
  split
  · exact supported.consMono.consMono
  · exact supported

theorem rhsReadyToBodyAppend {types slots ids rows Δ env e β}
    {h : ScopedDerives types slots ids rows Δ env e β}
    (ready : ScopedDerives.RuntimeReady h)
    (arguments : RecursiveArgumentsSupported env) (tail : List BodyBinding) :
    BodyDerives.RuntimeReady (rhsToBodyAppend h tail) := by
  induction ready with
  | literal => exact .literal
  | primBinOp => exact .primBinOp
  | nil supported => exact .nil supported
  | boolCtor ctor => exact .boolCtor ctor
  | cons sub _ _ ihh iht => exact .cons sub (ihh arguments) (iht arguments)
  | pair _ _ ihLeft ihRight => exact .pair (ihLeft arguments) (ihRight arguments)
  | varMono lookup supported =>
      exact .varMono (body_getElem?_append_left (by
        simpa [ordinaryBodyEnv, List.getElem?_map, lookup, ordinaryBinding])) supported
  | varRecursive lookup used supported =>
      exact .varExported (body_getElem?_append_left (by
        simpa [ordinaryBodyEnv, List.getElem?_map, lookup, ordinaryBinding])) used.external
        supported (arguments _ (List.mem_of_getElem? lookup))
  | varExported lookup used supported usedArguments =>
      exact .varExported (body_getElem?_append_left (by
        simpa [ordinaryBodyEnv, List.getElem?_map, lookup, ordinaryBinding])) used
        supported usedArguments
  | app sub _ _ ihf iha => exact .app sub (ihf arguments) (iha arguments)
  | lambda annotation supported _ ih =>
      simpa only [ordinaryBodyEnv, List.map_cons, List.cons_append, ordinaryBinding] using
        BodyDerives.RuntimeReady.lambda annotation supported (ih arguments.consMono)
  | letMono annotation _ _ ihr ihb =>
      simpa only [ordinaryBodyEnv, List.map_cons, List.cons_append, ordinaryBinding] using
        BodyDerives.RuntimeReady.letMono annotation (ihr arguments) (ihb arguments.consMono)
  | matchList coverage patterns bodies subs _ _ supported ihs ihb =>
      refine .match_ (ctx := .list _ _ _) coverage patterns
        (fun i br atIndex => by
          simpa only [ordinaryBodyEnv_branch, BodyBranchContext.extend_append] using
            rhsToBodyAppend (bodies i br atIndex) tail)
        subs (ihs arguments) ?_ supported
      intro i br atIndex
      simpa only [ordinaryBodyEnv_branch, BodyBranchContext.extend_append] using
        ihb i br atIndex arguments.branch
  | matchBool coverage patterns bodies subs _ _ supported ihs ihb =>
      refine .match_ (ctx := .bool) coverage patterns
        (fun i br atIndex => by
          simpa [BodyBranchContext.refine, BodyBranchContext.extend,
            BodyBranchContext.extend_append] using rhsToBodyAppend (bodies i br atIndex) tail)
        (by simpa [BodyBranchContext.refine] using subs) (ihs arguments) ?_ supported
      intro i br atIndex
      simpa [BodyBranchContext.refine, BodyBranchContext.extend,
        BodyBranchContext.extend_append] using ihb i br atIndex arguments
  | matchPair coverage patterns bodies subs _ _ supported ihs ihb =>
      refine .match_ (ctx := .pair _ _) coverage patterns
        (fun i br atIndex => by
          simpa [ordinaryBodyEnv_pairBranch, BodyBranchContext.refine,
            BodyBranchContext.extend_append] using rhsToBodyAppend (bodies i br atIndex) tail)
        (by simpa [BodyBranchContext.refine] using subs) (ihs arguments) ?_ supported
      intro i br atIndex
      simpa [ordinaryBodyEnv_pairBranch, BodyBranchContext.refine,
        BodyBranchContext.extend_append] using ihb i br atIndex arguments.pairBranch

#print axioms rhsReadyToBodyAppend

theorem ordinaryRhsReadyToBody {types slots ids rows Δ env e β}
    {h : ScopedDerives types slots ids rows Δ env e β}
    (ready : ScopedDerives.RuntimeReady h) :
    ∀ ordinary : OrdinaryEnv env, BodyDerives.RuntimeReady (ordinaryRhsToBody h ordinary) := by
  induction ready with
  | literal => intro _; exact .literal
  | primBinOp => intro _; exact .primBinOp
  | nil supported => intro _; exact .nil supported
  | boolCtor ctor => intro _; exact .boolCtor ctor
  | cons sub _ _ ihh iht => intro ordinary; exact .cons sub (ihh ordinary) (iht ordinary)
  | pair _ _ ihLeft ihRight =>
      intro ordinary
      exact .pair (ihLeft ordinary) (ihRight ordinary)
  | varMono lookup supported =>
      intro _
      exact .varMono (by simpa [ordinaryBodyEnv, List.getElem?_map, lookup, ordinaryBinding]) supported
  | varRecursive lookup _ _ =>
      intro ordinary
      exact False.elim (ordinary _ (List.mem_of_getElem? lookup))
  | varExported lookup used supported arguments =>
      intro _
      exact .varExported
        (by simpa [ordinaryBodyEnv, List.getElem?_map, lookup, ordinaryBinding])
        used supported arguments
  | app sub _ _ ihf iha => intro ordinary; exact .app sub (ihf ordinary) (iha ordinary)
  | lambda annotation supported _ ih =>
      intro ordinary
      exact .lambda annotation supported (ih ordinary.consMono)
  | letMono annotation _ _ ihr ihb =>
      intro ordinary
      exact .letMono annotation (ihr ordinary) (ihb ordinary.consMono)
  | matchList coverage patterns bodies subs _ _ supported ihs ihb =>
      intro ordinary
      refine .match_ (ctx := .list _ _ _) coverage patterns
        (fun i br atIndex => by
          simpa only [ordinaryBodyEnv_branch] using ordinaryRhsToBody (bodies i br atIndex) ordinary.branch)
        subs (ihs ordinary) ?_ supported
      intro i br atIndex
      simpa only [ordinaryBodyEnv_branch] using ihb i br atIndex ordinary.branch
  | matchBool coverage patterns bodies subs _ _ supported ihs ihb =>
      intro ordinary
      refine .match_ (ctx := .bool) coverage patterns
        (fun i br atIndex => by
          simpa [BodyBranchContext.refine, BodyBranchContext.extend] using
            ordinaryRhsToBody (bodies i br atIndex) ordinary)
        (by simpa [BodyBranchContext.refine] using subs) (ihs ordinary) ?_ supported
      intro i br atIndex
      simpa [BodyBranchContext.refine, BodyBranchContext.extend] using ihb i br atIndex ordinary
  | matchPair coverage patterns bodies subs _ _ supported ihs ihb =>
      intro ordinary
      refine .match_ (ctx := .pair _ _) coverage patterns
        (fun i br atIndex => by
          simpa [ordinaryBodyEnv_pairBranch, BodyBranchContext.refine] using
            ordinaryRhsToBody (bodies i br atIndex) ordinary.pairBranch)
        (by simpa [BodyBranchContext.refine] using subs) (ihs ordinary) ?_ supported
      intro i br atIndex
      simpa [ordinaryBodyEnv_pairBranch, BodyBranchContext.refine] using
        ihb i br atIndex ordinary.pairBranch

theorem ordinaryRhsReadyToBodyAppend {types slots ids rows Δ env e β}
    {h : ScopedDerives types slots ids rows Δ env e β}
    (ready : ScopedDerives.RuntimeReady h) :
    ∀ (ordinary : OrdinaryEnv env) (tail : List BodyBinding),
      BodyDerives.RuntimeReady (ordinaryRhsToBodyAppend h ordinary tail) := by
  induction ready with
  | literal => intro _ _; exact .literal
  | primBinOp => intro _ _; exact .primBinOp
  | nil supported => intro _ _; exact .nil supported
  | boolCtor ctor => intro _ _; exact .boolCtor ctor
  | cons sub _ _ ihh iht =>
      intro ordinary tail
      exact .cons sub (ihh ordinary tail) (iht ordinary tail)
  | pair _ _ ihLeft ihRight =>
      intro ordinary tail
      exact .pair (ihLeft ordinary tail) (ihRight ordinary tail)
  | varMono lookup supported =>
      intro _ tail
      exact .varMono (body_getElem?_append_left (by
        simpa [ordinaryBodyEnv, List.getElem?_map, lookup, ordinaryBinding])) supported
  | varRecursive lookup _ _ =>
      intro ordinary _
      exact False.elim (ordinary _ (List.mem_of_getElem? lookup))
  | varExported lookup used supported arguments =>
      intro _ tail
      exact .varExported (body_getElem?_append_left (by
        simpa [ordinaryBodyEnv, List.getElem?_map, lookup, ordinaryBinding]))
        used supported arguments
  | app sub _ _ ihf iha =>
      intro ordinary tail
      exact .app sub (ihf ordinary tail) (iha ordinary tail)
  | lambda annotation supported _ ih =>
      intro ordinary tail
      simpa only [ordinaryBodyEnv, List.map_cons, List.cons_append, ordinaryBinding] using
        BodyDerives.RuntimeReady.lambda annotation supported (ih ordinary.consMono tail)
  | letMono annotation _ _ ihr ihb =>
      intro ordinary tail
      simpa only [ordinaryBodyEnv, List.map_cons, List.cons_append, ordinaryBinding] using
        BodyDerives.RuntimeReady.letMono annotation (ihr ordinary tail)
          (ihb ordinary.consMono tail)
  | matchList coverage patterns bodies subs _ _ supported ihs ihb =>
      intro ordinary tail
      refine .match_ (ctx := .list _ _ _) coverage patterns
        (fun i br atIndex => by
          simpa only [ordinaryBodyEnv_branch, BodyBranchContext.extend_append] using
            ordinaryRhsToBodyAppend (bodies i br atIndex) ordinary.branch tail)
        subs (ihs ordinary tail) ?_ supported
      intro i br atIndex
      simpa only [ordinaryBodyEnv_branch, BodyBranchContext.extend_append] using
        ihb i br atIndex ordinary.branch tail
  | matchBool coverage patterns bodies subs _ _ supported ihs ihb =>
      intro ordinary tail
      refine .match_ (ctx := .bool) coverage patterns
        (fun i br atIndex => by
          simpa [BodyBranchContext.refine, BodyBranchContext.extend,
            BodyBranchContext.extend_append] using
            ordinaryRhsToBodyAppend (bodies i br atIndex) ordinary tail)
        (by simpa [BodyBranchContext.refine] using subs) (ihs ordinary tail) ?_ supported
      intro i br atIndex
      simpa [BodyBranchContext.refine, BodyBranchContext.extend,
        BodyBranchContext.extend_append] using ihb i br atIndex ordinary tail
  | matchPair coverage patterns bodies subs _ _ supported ihs ihb =>
      intro ordinary tail
      refine .match_ (ctx := .pair _ _) coverage patterns
        (fun i br atIndex => by
          simpa [ordinaryBodyEnv_pairBranch, BodyBranchContext.refine,
            BodyBranchContext.extend_append] using
            ordinaryRhsToBodyAppend (bodies i br atIndex) ordinary.pairBranch tail)
        (by simpa [BodyBranchContext.refine] using subs) (ihs ordinary tail) ?_ supported
      intro i br atIndex
      simpa [ordinaryBodyEnv_pairBranch, BodyBranchContext.refine,
        BodyBranchContext.extend_append] using ihb i br atIndex ordinary.pairBranch tail

#print axioms ordinaryRhsToBody
#print axioms ordinaryRhsToBodyAppend
#print axioms ordinaryRhsReadyToBody
#print axioms ordinaryRhsReadyToBodyAppend

/-- A single real opaque-opening RHS certificate supplies every local use in
    the closed-capture slice. This is certificate elimination, not another
    inference or solver pass, and keeps implementation/demand bounds separate. -/
theorem localRhsDemand {s found typeCaptures env rhs sourceTypes sourceSlots calleeΔ caller useHM}
    (cert : RecursiveHMUniversal.Certified s found typeCaptures env rhs sourceTypes sourceSlots)
    (used : HMCountScheme.Use s calleeΔ useHM caller) :
    demand cert used.counts (argument cert.opening.ids (SchemeUse.vector used.types)) = used.bounds := by
  rw [demand, ← SchemeSpecialization.close_open cert.opening.ids (SchemeUse.vector used.types)
    (by rw [bounds_shape, HMCountScheme.Opening.bounds, cert.opening.shape]; exact cert.opening.lc),
    RecursiveHMUniversal.close_counts, cert.opening.close]
  rfl

def localRhsInstances {s ann rhs found typeCaptures Δ calleeΔ caller useHM}
    (frame : LocalFrame s [] rhs) (annotation : LocalAnnotationOK s ann)
    (cert : RecursiveHMUniversal.Certified s found typeCaptures [] rhs BoundsTy.fvar
      (localSlots ann BoundsTy.bvar (frame.owned.map BoundsTy.fvar)))
    (owners : cert.opening.ids = frame.owned)
    (used : HMCountScheme.Use s calleeΔ useHM caller)
    (outer : List BodyBinding := []) :
    ScopedBodyDerives (localTypes frame.owned BoundsTy.fvar used.types)
      (localSlots ann BoundsTy.bvar used.types)
      (s.counts.quantified ++ s.counts.captures ++ [])
      (CountAlgebra.compose (s.counts.quantified.zip used.counts) [])
      (Δ ++ used.countInstance.premises) outer rhs used.bounds := by
  let rows := s.counts.quantified.zip used.counts
  let f := argument cert.opening.ids (SchemeUse.vector used.types)
  have lc := RecursiveHMUniversal.replacementLC cert.opening.ids (SchemeUse.vector used.types)
    (RecursiveHMUniversal.argumentsLC used.types used.typesLC)
  have scope := RecursiveHMUniversal.replacementScope cert.opening.ids (SchemeUse.vector used.types)
    (SchemeUse.vector_scope used.typesScoped)
  let specialized := fromCertified cert used.countInstance f lc scope
    (by simp [RecursiveHMEnvironment.Captured]) (by simp [CapturesFixed])
  have instanceBody := ordinaryRhsToBodyAppend specialized.typing (by simp [OrdinaryEnv]) outer
  have widened := ScopedBodyDerives.subsumption instanceBody specialized.inclusion
  have withParent := widened.assuming (Δ' := Δ ++ used.countInstance.premises)
    (by intro σ premises p member; exact premises p (List.mem_append_right _ member))
  have typesEq : (fun i => mapFree f (bounds rows (BoundsTy.fvar i))) =
      localTypes frame.owned BoundsTy.fvar used.types := by
    simpa only [f, owners] using localTypes_specialize frame.owned rows used.types
  have slotsEq : (fun i => mapFree f
      (bounds rows (localSlots ann BoundsTy.bvar (frame.owned.map BoundsTy.fvar) i))) =
      localSlots ann BoundsTy.bvar used.types := by
    simpa only [f, owners] using
      localSlots_specialize ann frame.owned rows used.types frame.distinct (frame.slotsFit annotation)
  have demandEq : demand cert used.counts f = used.bounds := by
    exact localRhsDemand cert used
  simpa only [specialized, rows, typesEq, slotsEq, demandEq, ordinaryBodyEnv,
    List.map_nil, List.append_nil, CountAlgebra.compose, List.nil_append] using withParent

def recursiveTypeCaptures (env : List Binding) : List Ty :=
  env.map fun binding => match binding with
    | .mono β => Synth.BoundsTy.toTy β
    | .recursive c => c.template.hm.body
    | .exported s => s.hm.body

def recursiveFixedTypeCaptures (env : List Binding) : List Ty :=
  env.flatMap fun binding => match binding with
    | .mono β => [Synth.BoundsTy.toTy β]
    | .recursive c => c.fixed.types.map Synth.BoundsTy.toTy
    | .exported _ => []

private theorem recursiveTypeCaptures_represented {env c}
    (member : Binding.recursive c ∈ env) :
    c.template.hm.body ∈ recursiveTypeCaptures env :=
  List.mem_map.mpr ⟨.recursive c, member, rfl⟩

private theorem recursiveTypeCaptures_mono {env β}
    (member : Binding.mono β ∈ env) :
    Synth.BoundsTy.toTy β ∈ recursiveTypeCaptures env :=
  List.mem_map.mpr ⟨.mono β, member, rfl⟩

private theorem recursiveTypeCaptures_exported {env s}
    (member : Binding.exported s ∈ env) :
    s.hm.body ∈ recursiveTypeCaptures env :=
  List.mem_map.mpr ⟨.exported s, member, rfl⟩

private theorem recursiveFixedTypeCaptures_represented {env c β}
    (member : Binding.recursive c ∈ env) (argument : β ∈ c.fixed.types) :
    Synth.BoundsTy.toTy β ∈ recursiveFixedTypeCaptures env := by
  apply List.mem_flatMap.mpr
  exact ⟨.recursive c, member, by
    simpa using List.mem_map.mpr ⟨β, argument, rfl⟩⟩

/-- Exact recursive RHS assumptions available at a body point. The root starts
    with the checked group contracts; closed mono binders may subsequently be
    pushed in front while preserving the correspondence with the body env. -/
structure BodyCapture (env : List BodyBinding) where
  rhsEnv : List Binding
  bodyEnv : ordinaryBodyEnv rhsEnv = env
  captured : RecursiveHMEnvironment.Captured [] rhsEnv
  arguments : RecursiveArgumentsSupported rhsEnv
  countClosed : ∀ c, .recursive c ∈ rhsEnv → c.template.counts.captures = []
  exportCountClosed : ∀ s, .exported s ∈ rhsEnv → s.counts.captures = []

private def emptyBodyCapture : BodyCapture [] where
  rhsEnv := []
  bodyEnv := rfl
  captured := by simp [RecursiveHMEnvironment.Captured]
  arguments := by simp [RecursiveArgumentsSupported]
  countClosed := by simp
  exportCountClosed := by simp

/-- Every exit from a group checked with no enclosing count telescope is itself
    count-closed.  This lets later groups capture the generalized exit rather
    than the old fixed recursive opening. -/
private theorem checkedMembersExportCountsClosed
    {output metadata path premises typeCaptures env index vectors}
    {ps : HMDeclaredGroup.Interfaces output metadata path [] premises typeCaptures index vectors}
    (members : HMDeclaredGroup.CheckedMembers env ps) :
    ∀ s ∈ members.exports, s.counts.captures = [] := by
  induction members with
  | nil => simp [HMDeclaredGroup.CheckedMembers.exports]
  | cons head rest ih =>
      intro s member
      rcases List.mem_cons.mp member with first | tail
      · cases first
        rfl
      · exact ih s tail

private def checkedGroupBodyCapture
    {output metadata path vectors premises bodyTypes}
    (g : HMDeclaredGroup.Checked output metadata path vectors [] premises bodyTypes []) :
    BodyCapture (g.exports.map BodyBinding.exported) where
  rhsEnv := g.exports.map Binding.exported
  bodyEnv := ordinaryBodyEnv_exports g.exports
  captured := by simp [RecursiveHMEnvironment.Captured]
  arguments := by simp [RecursiveArgumentsSupported]
  countClosed := by intro c member; simp at member
  exportCountClosed := by
    intro s member
    obtain ⟨t, source, same⟩ := List.mem_map.mp member
    injection same with same
    subst s
    exact checkedMembersExportCountsClosed g.members t source

/-- Enter a checked nested group without losing the exact recursive assumptions
    represented by the surrounding body environment.  The new group's fixed
    contracts precede the captured outer assumptions in the same de Bruijn
    order used by its universally checked RHSs. -/
private def BodyCapture.extendGroup {env output metadata path vectors premises bodyTypes}
    (capture : BodyCapture env)
    (g : HMDeclaredGroup.Checked output metadata path vectors [] premises bodyTypes capture.rhsEnv) :
    BodyCapture (g.exports.map BodyBinding.exported ++ env) where
  rhsEnv := g.exports.map Binding.exported ++ capture.rhsEnv
  bodyEnv := by
    calc
      ordinaryBodyEnv (g.exports.map Binding.exported ++ capture.rhsEnv) =
          ordinaryBodyEnv (g.exports.map Binding.exported) ++ ordinaryBodyEnv capture.rhsEnv := by
            simp only [ordinaryBodyEnv, List.map_append]
      _ = g.exports.map BodyBinding.exported ++ env := by
        rw [ordinaryBodyEnv_exports, capture.bodyEnv]
  captured := by
    constructor
    · intro β member
      rcases List.mem_append.mp member with inner | outer
      · obtain ⟨scheme, _, impossible⟩ := List.mem_map.mp inner
        cases impossible
      · exact capture.captured.1 β outer
    · intro contract member β argument
      rcases List.mem_append.mp member with inner | outer
      · obtain ⟨scheme, _, impossible⟩ := List.mem_map.mp inner
        cases impossible
      · exact capture.captured.2 contract outer β argument
  arguments := by
    intro contract member β argument
    rcases List.mem_append.mp member with inner | outer
    · obtain ⟨scheme, _, impossible⟩ := List.mem_map.mp inner
      cases impossible
    · exact capture.arguments contract outer β argument
  countClosed := by
    intro contract member
    rcases List.mem_append.mp member with inner | outer
    · obtain ⟨scheme, _, impossible⟩ := List.mem_map.mp inner
      cases impossible
    · exact capture.countClosed contract outer
  exportCountClosed := by
    intro s member
    rcases List.mem_append.mp member with inner | outer
    · obtain ⟨t, source, same⟩ := List.mem_map.mp inner
      injection same with same
      subst s
      exact checkedMembersExportCountsClosed g.members t source
    · exact capture.exportCountClosed s outer

private def BodyCapture.extendMono {env} (capture : BodyCapture env) (β : BoundsTy)
    (scope : BoundsScoped [] β) : BodyCapture (.mono β :: env) where
  rhsEnv := .mono β :: capture.rhsEnv
  bodyEnv := by
    change .mono β :: ordinaryBodyEnv capture.rhsEnv = .mono β :: env
    rw [capture.bodyEnv]
  captured := by
    constructor
    · intro a member
      rcases List.mem_cons.mp member with head | tail
      · cases head; exact scope
      · exact capture.captured.1 a tail
    · intro c member a argument
      rcases List.mem_cons.mp member with head | tail
      · cases head
      · exact capture.captured.2 c tail a argument
  arguments := by
    intro c member a argument
    rcases List.mem_cons.mp member with head | tail
    · cases head
    · exact capture.arguments c tail a argument
  countClosed := by
    intro c member
    rcases List.mem_cons.mp member with head | tail
    · cases head
    · exact capture.countClosed c tail
  exportCountClosed := by
    intro s member
    rcases List.mem_cons.mp member with head | tail
    · cases head
    · exact capture.exportCountClosed s tail

private def BodyCapture.extendExported {env} (capture : BodyCapture env)
    (s : HMCountScheme.Scheme) (closed : s.counts.captures = []) :
    BodyCapture (.exported s :: env) where
  rhsEnv := .exported s :: capture.rhsEnv
  bodyEnv := by
    change .exported s :: ordinaryBodyEnv capture.rhsEnv = .exported s :: env
    rw [capture.bodyEnv]
  captured := by
    constructor
    · intro β member
      rcases List.mem_cons.mp member with head | tail
      · cases head
      · exact capture.captured.1 β tail
    · intro c member a argument
      rcases List.mem_cons.mp member with head | tail
      · cases head
      · exact capture.captured.2 c tail a argument
  arguments := by
    intro c member a argument
    rcases List.mem_cons.mp member with head | tail
    · cases head
    · exact capture.arguments c tail a argument
  countClosed := by
    intro c member
    rcases List.mem_cons.mp member with head | tail
    · cases head
    · exact capture.countClosed c tail
  exportCountClosed := by
    intro t member
    rcases List.mem_cons.mp member with head | tail
    · cases head; exact closed
    · exact capture.exportCountClosed t tail

private def extendMonoCapture? {env} (capture : Option (BodyCapture env)) (β : BoundsTy) :
    Option (BodyCapture (.mono β :: env)) :=
  capture.bind fun captured =>
    if inScope : boundsScopedBool [] β = true then
      some (captured.extendMono β (boundsScopedBool_sound inScope))
    else none

private def extendBranchCapture? {env} (capture : Option (BodyCapture env))
    (ctx : BodyBranchContext) (pattern : MatchPattern) :
    Option (BodyCapture (ctx.extend pattern env)) :=
  match ctx with
  | .bool => capture
  | .pair left right =>
      if isPair : pattern = .named pairCtorName 2 then
        have extended : (BodyBranchContext.pair left right).extend pattern env =
            .mono left :: .mono right :: env := by
          simp [BodyBranchContext.extend, isPair]
        extended.symm ▸ extendMonoCapture? (extendMonoCapture? capture right) left
      else
        have unchanged : (BodyBranchContext.pair left right).extend pattern env = env := by
          simp [BodyBranchContext.extend, isPair]
        unchanged.symm ▸ capture
  | .list lo hi elem =>
      if isCons : pattern = .named consCtorName 2 then
        have extended : (BodyBranchContext.list lo hi elem).extend pattern env =
            .mono elem :: .mono (.list (.pred lo) (.pred hi) elem) :: env := by
          simp [BodyBranchContext.extend, isCons]
        extended.symm ▸ extendMonoCapture?
          (extendMonoCapture? capture (.list (.pred lo) (.pred hi) elem)) elem
      else
        have unchanged : (BodyBranchContext.list lo hi elem).extend pattern env = env := by
          simp [BodyBranchContext.extend, isCons]
        unchanged.symm ▸ capture

private theorem RecursiveArgumentsSupported.mapBinding {env}
    (supported : RecursiveArgumentsSupported env) (f : Nat → BoundsTy)
    (lc : ∀ i, (Synth.BoundsTy.toTy (f i)).IsLC)
    (arguments : ∀ i, Runtime.Supported (f i)) :
    RecursiveArgumentsSupported (env.map (mapBinding f lc)) := by
  intro c member a argument
  obtain ⟨binding, source, mapped⟩ := List.mem_map.mp member
  cases binding with
  | mono β => cases mapped
  | recursive original =>
      cases mapped
      obtain ⟨b, sourceArgument, rfl⟩ := List.mem_map.mp (by
        simpa [Contract.mapTypes, RecursiveHMContract.Fixed.mapTypes] using argument)
      exact Runtime.Supported.types f arguments (supported original source b sourceArgument)
  | exported s => cases mapped

/-- Every type named by the captured environment was placed among the local
    opening guards. Consequently arbitrary later instances of the local scheme
    leave mono captures and fixed recursive argument vectors unchanged. -/
private theorem declaredLocalArgumentTypesFixed
    {output path d quantified premises typeCaptures env calleeΔ caller useHM}
    (c : @HMDeclaredReconciliation.Checked output (.letIn path) d
      quantified [] premises typeCaptures)
    (stable : RecursiveHMEnvironment.TypesFixed c.interpretation env)
    (monoRepresented : ∀ β, .mono β ∈ env → Synth.BoundsTy.toTy β ∈ typeCaptures)
    (fixedRepresented : ∀ contract, .recursive contract ∈ env →
      ∀ β ∈ contract.fixed.types, Synth.BoundsTy.toTy β ∈ typeCaptures)
    (used : HMCountScheme.Use c.interface.scheme calleeΔ useHM caller) :
    RecursiveHMEnvironment.TypesFixed
      (argument c.opening.ids (SchemeUse.vector used.types)) env := by
  have fixesCapture {t : Ty} (member : t ∈ typeCaptures) {i : Nat} (free : i ∈ t.freeVars) :
      i ∉ c.opening.ids := by
    intro owned
    exact c.opening.fresh i owned t
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
        (List.mem_cons_of_mem _ (List.mem_append_left _ member)))) free
  constructor
  · intro β member i free
    have absent := fixesCapture (monoRepresented β member) free
    simp only [argument, List.idxOf?_eq_none_iff.mpr absent]
  · intro contract member
    refine ⟨(stable.2 contract member).1, ?_⟩
    intro β argMember i free
    have absent := fixesCapture (fixedRepresented contract member β argMember) free
    simp only [argument, List.idxOf?_eq_none_iff.mpr absent]

/-- A local universal instance may keep a mixed mono/recursive source
    environment. Its guarded opening leaves every captured type fixed;
    converting concrete recursive uses to body exports then preserves the exact
    derivation while mono captures remain mono. -/
def capturedLocalRhsInstances {s ann rhs found typeCaptures env Δ calleeΔ caller useHM}
    (frame : LocalFrame s [] rhs) (annotation : LocalAnnotationOK s ann)
    (cert : RecursiveHMUniversal.Certified s found typeCaptures env rhs BoundsTy.fvar
      (localSlots ann BoundsTy.bvar (frame.owned.map BoundsTy.fvar)))
    (owners : cert.opening.ids = frame.owned)
    (captured : RecursiveHMEnvironment.Captured s.counts.captures env)
    (used : HMCountScheme.Use s calleeΔ useHM caller)
    (typesFixed : RecursiveHMEnvironment.TypesFixed
      (argument cert.opening.ids (SchemeUse.vector used.types)) env)
    (outer : List BodyBinding := []) :
    ScopedBodyDerives (localTypes frame.owned BoundsTy.fvar used.types)
      (localSlots ann BoundsTy.bvar used.types)
      (s.counts.quantified ++ s.counts.captures ++ [])
      (CountAlgebra.compose (s.counts.quantified.zip used.counts) [])
      (Δ ++ used.countInstance.premises) (ordinaryBodyEnv env ++ outer) rhs used.bounds := by
  let rows := s.counts.quantified.zip used.counts
  let f := argument cert.opening.ids (SchemeUse.vector used.types)
  have lc := RecursiveHMUniversal.replacementLC cert.opening.ids (SchemeUse.vector used.types)
    (RecursiveHMUniversal.argumentsLC used.types used.typesLC)
  have scope := RecursiveHMUniversal.replacementScope cert.opening.ids (SchemeUse.vector used.types)
    (SchemeUse.vector_scope used.typesScoped)
  have capturesFixed : CapturesFixed f env := by
    intro b member
    cases b with
    | mono β => trivial
    | recursive c =>
        intro i freeId
        have absent : i ∉ cert.opening.ids :=
          fun present => cert.typeFresh c member i present freeId
        simp only [f, argument, List.idxOf?_eq_none_iff.mpr absent]
    | exported s =>
        intro i freeId
        have absent : i ∉ cert.opening.ids :=
          fun present => cert.exportTypeFresh s member i present freeId
        simp only [f, argument, List.idxOf?_eq_none_iff.mpr absent]
  let specialized := fromCertified cert used.countInstance f lc scope captured capturesFixed
  have instanceBody := rhsToBodyAppend specialized.typing outer
  have widened := ScopedBodyDerives.subsumption instanceBody specialized.inclusion
  have withParent := widened.assuming (Δ' := Δ ++ used.countInstance.premises)
    (by intro σ premises p member; exact premises p (List.mem_append_right _ member))
  have typesEq : (fun i => mapFree f (bounds rows (BoundsTy.fvar i))) =
      localTypes frame.owned BoundsTy.fvar used.types := by
    simpa only [f, owners] using localTypes_specialize frame.owned rows used.types
  have slotsEq : (fun i => mapFree f
      (bounds rows (localSlots ann BoundsTy.bvar (frame.owned.map BoundsTy.fvar) i))) =
      localSlots ann BoundsTy.bvar used.types := by
    simpa only [f, owners] using
      localSlots_specialize ann frame.owned rows used.types frame.distinct (frame.slotsFit annotation)
  have demandEq : demand cert used.counts f = used.bounds := localRhsDemand cert used
  have envFixed := RecursiveHMEnvironment.typesFixed lc typesFixed
  have envEq : ordinaryBodyEnv (env.map (mapBinding f lc)) = ordinaryBodyEnv env := by
    rw [envFixed]
  simpa only [specialized, rows, typesEq, slotsEq, demandEq, envEq,
    CountAlgebra.compose, List.map_nil, List.nil_append, List.append_nil] using withParent

theorem localRhsInstances_runtimeReady {s ann rhs found typeCaptures Δ calleeΔ caller useHM}
    (frame : LocalFrame s [] rhs) (annotation : LocalAnnotationOK s ann)
    (cert : RecursiveHMUniversal.Certified s found typeCaptures [] rhs BoundsTy.fvar
      (localSlots ann BoundsTy.bvar (frame.owned.map BoundsTy.fvar)))
    (owners : cert.opening.ids = frame.owned) (ready : ScopedDerives.RuntimeReady cert.typing)
    (used : HMCountScheme.Use s calleeΔ useHM caller)
    (arguments : ∀ a ∈ used.types, Runtime.Supported a)
    (outer : List BodyBinding := []) :
    BodyDerives.RuntimeReady (localRhsInstances (Δ := Δ) frame annotation cert owners used outer) := by
  let rows := s.counts.quantified.zip used.counts
  let f := argument cert.opening.ids (SchemeUse.vector used.types)
  have lc := RecursiveHMUniversal.replacementLC cert.opening.ids (SchemeUse.vector used.types)
    (RecursiveHMUniversal.argumentsLC used.types used.typesLC)
  have scope := RecursiveHMUniversal.replacementScope cert.opening.ids (SchemeUse.vector used.types)
    (SchemeUse.vector_scope used.typesScoped)
  have vectorSupport : ∀ i, Runtime.Supported (SchemeUse.vector used.types i) := by
    intro i
    cases atIndex : used.types[i]? with
    | none => simp only [SchemeUse.vector, atIndex, Option.getD_none]; exact .prim
    | some a =>
        simpa only [SchemeUse.vector, atIndex, Option.getD_some] using
          arguments a (List.mem_of_getElem? atIndex)
  let specialized := fromCertified cert used.countInstance f lc scope
    (by simp [RecursiveHMEnvironment.Captured]) (by simp [CapturesFixed])
  have specializedReady := fromCertified_runtimeReady cert ready used.countInstance f lc scope
    (Runtime.Supported.argument cert.opening.ids _ vectorSupport)
    (by simp [RecursiveHMEnvironment.Captured]) (by simp [CapturesFixed])
  have bodyReady := ordinaryRhsReadyToBodyAppend specializedReady (by simp [OrdinaryEnv]) outer
  have demandEq : demand cert used.counts f = used.bounds := localRhsDemand cert used
  have demandSupport : Runtime.Supported used.bounds := by
    rw [← demandEq]
    exact Runtime.Supported.subtypeRight specialized.inclusion specializedReady.supported
  have widenedReady := BodyDerives.RuntimeReady.subsumption specialized.inclusion bodyReady
    (by rw [demandEq]; exact demandSupport)
  have withParent := widenedReady.assuming (Δ' := Δ ++ used.countInstance.premises)
    (by intro σ premises p member; exact premises p (List.mem_append_right _ member))
  have typesEq : (fun i => mapFree f (bounds rows (BoundsTy.fvar i))) =
      localTypes frame.owned BoundsTy.fvar used.types := by
    simpa only [f, owners] using localTypes_specialize frame.owned rows used.types
  have slotsEq : (fun i => mapFree f
      (bounds rows (localSlots ann BoundsTy.bvar (frame.owned.map BoundsTy.fvar) i))) =
      localSlots ann BoundsTy.bvar used.types := by
    simpa only [f, owners] using
      localSlots_specialize ann frame.owned rows used.types frame.distinct (frame.slotsFit annotation)
  simpa only [specialized, rows, typesEq, slotsEq, demandEq, ordinaryBodyEnv,
    List.map_nil, List.append_nil, CountAlgebra.compose, List.nil_append] using withParent

theorem capturedLocalRhsInstances_runtimeReady
    {s ann rhs found typeCaptures env Δ calleeΔ caller useHM}
    (frame : LocalFrame s [] rhs) (annotation : LocalAnnotationOK s ann)
    (cert : RecursiveHMUniversal.Certified s found typeCaptures env rhs BoundsTy.fvar
      (localSlots ann BoundsTy.bvar (frame.owned.map BoundsTy.fvar)))
    (owners : cert.opening.ids = frame.owned)
    (ready : ScopedDerives.RuntimeReady cert.typing)
    (captured : RecursiveHMEnvironment.Captured s.counts.captures env)
    (used : HMCountScheme.Use s calleeΔ useHM caller)
    (typesFixed : RecursiveHMEnvironment.TypesFixed
      (argument cert.opening.ids (SchemeUse.vector used.types)) env)
    (sourceArguments : RecursiveArgumentsSupported env)
    (arguments : ∀ a ∈ used.types, Runtime.Supported a)
    (outer : List BodyBinding := []) :
    BodyDerives.RuntimeReady
      (capturedLocalRhsInstances (Δ := Δ) frame annotation cert owners
        captured used typesFixed outer) := by
  let rows := s.counts.quantified.zip used.counts
  let f := argument cert.opening.ids (SchemeUse.vector used.types)
  have lc := RecursiveHMUniversal.replacementLC cert.opening.ids (SchemeUse.vector used.types)
    (RecursiveHMUniversal.argumentsLC used.types used.typesLC)
  have scope := RecursiveHMUniversal.replacementScope cert.opening.ids (SchemeUse.vector used.types)
    (SchemeUse.vector_scope used.typesScoped)
  have vectorSupport : ∀ i, Runtime.Supported (SchemeUse.vector used.types i) := by
    intro i
    cases atIndex : used.types[i]? with
    | none => simp only [SchemeUse.vector, atIndex, Option.getD_none]; exact .prim
    | some a =>
        simpa only [SchemeUse.vector, atIndex, Option.getD_some] using
          arguments a (List.mem_of_getElem? atIndex)
  have fullSupport : ∀ i, Runtime.Supported (f i) :=
    Runtime.Supported.argument cert.opening.ids _ vectorSupport
  have capturesFixed : CapturesFixed f env := by
    intro b member
    cases b with
    | mono β => trivial
    | recursive c =>
        intro i freeId
        have absent : i ∉ cert.opening.ids :=
          fun present => cert.typeFresh c member i present freeId
        simp only [f, argument, List.idxOf?_eq_none_iff.mpr absent]
    | exported s =>
        intro i freeId
        have absent : i ∉ cert.opening.ids :=
          fun present => cert.exportTypeFresh s member i present freeId
        simp only [f, argument, List.idxOf?_eq_none_iff.mpr absent]
  let specialized := fromCertified cert used.countInstance f lc scope captured capturesFixed
  have specializedReady := fromCertified_runtimeReady cert ready used.countInstance f lc scope
    fullSupport captured capturesFixed
  have mappedArguments := sourceArguments.mapBinding f lc fullSupport
  have bodyReady := rhsReadyToBodyAppend specializedReady mappedArguments outer
  have demandEq : demand cert used.counts f = used.bounds := localRhsDemand cert used
  have demandSupport : Runtime.Supported used.bounds := by
    rw [← demandEq]
    exact Runtime.Supported.subtypeRight specialized.inclusion specializedReady.supported
  have widenedReady := BodyDerives.RuntimeReady.subsumption specialized.inclusion bodyReady
    (by rw [demandEq]; exact demandSupport)
  have withParent := widenedReady.assuming (Δ' := Δ ++ used.countInstance.premises)
    (by intro σ premises p member; exact premises p (List.mem_append_right _ member))
  have typesEq : (fun i => mapFree f (bounds rows (BoundsTy.fvar i))) =
      localTypes frame.owned BoundsTy.fvar used.types := by
    simpa only [f, owners] using localTypes_specialize frame.owned rows used.types
  have slotsEq : (fun i => mapFree f
      (bounds rows (localSlots ann BoundsTy.bvar (frame.owned.map BoundsTy.fvar) i))) =
      localSlots ann BoundsTy.bvar used.types := by
    simpa only [f, owners] using
      localSlots_specialize ann frame.owned rows used.types frame.distinct (frame.slotsFit annotation)
  have envFixed := RecursiveHMEnvironment.typesFixed lc typesFixed
  have envEq : ordinaryBodyEnv (env.map (mapBinding f lc)) = ordinaryBodyEnv env := by
    rw [envFixed]
  simpa only [capturedLocalRhsInstances, specialized, rows, typesEq, slotsEq,
    demandEq, envEq, CountAlgebra.compose, List.map_nil, List.nil_append,
    List.append_nil] using withParent

#print axioms localSlots_specialize
#print axioms declaredLocalSlotsAgree
#print axioms declaredLocalFrame
#print axioms declaredLocalCertificate
#print axioms declaredCapturedLocalCertificate
#print axioms declaredLocalCertificate_runtimeReady
#print axioms declaredCapturedLocalCertificate_runtimeReady
#print axioms localRhsInstances
#print axioms localRhsInstances_runtimeReady
#print axioms capturedLocalRhsInstances
#print axioms capturedLocalRhsInstances_runtimeReady

structure BodyResult (ids : List Nat) (rows : Bindings) (caller : List Nat)
    (Δ : List Constraint) (env : List BodyBinding) (e : Expr) where
  hm : Ty
  bounds : BoundsTy
  root : Typed.rootHM? e = some hm.eraseBounds
  shape : Synth.BoundsTy.toTy bounds = hm.eraseBounds
  typing : BodyDerives ids rows Δ env e.stripFound bounds
  inScope : BoundsScoped caller bounds
  nodes : List Typed.NodeResult
  runtimeReady : Option (PLift (BodyDerives.RuntimeReady typing))

/-- Proof-only context transport keeps the original artifact, all node reports,
    inferred bounds and runtime witness. No expressions or schemes are rebuilt. -/
def BodyResult.assuming {ids rows caller Δ Δ' env e}
    (result : BodyResult ids rows caller Δ env e) (hp : (⟨Δ', Δ⟩ : ForallProblem).Valid) :
    BodyResult ids rows caller Δ' env e where
  hm := result.hm
  bounds := result.bounds
  root := result.root
  shape := result.shape
  typing := result.typing.assuming hp
  inScope := result.inScope
  nodes := result.nodes
  runtimeReady := result.runtimeReady.map (fun ready => ⟨ready.down.assuming hp⟩)

#print axioms BodyResult.assuming

private def finishBody {ids rows caller Δ env e} (path : CorePath) (hm : Ty) (β : BoundsTy)
    (root : Typed.rootHM? e = some hm.eraseBounds) (typing : BodyDerives ids rows Δ env e.stripFound β)
    (children : List Typed.NodeResult)
    (ready : Option (PLift (BodyDerives.RuntimeReady typing))) :
    Except String (BodyResult ids rows caller Δ env e) := do
  let shape ← match BinderBridge.equalTy (Synth.BoundsTy.toTy β) hm.eraseBounds with
    | some h => pure h | none => throw "bounds: generalized body result disagrees with original found payload"
  if h : boundsScopedBool caller β = true then
    pure ⟨hm, β, root, shape.down, typing, boundsScopedBool_sound h,
      ⟨path, hm.eraseBounds, some β⟩ :: children, ready⟩
  else throw "bounds: generalized body result counts escape caller scope"

private structure BodyBranches (ids : List Nat) (rows : Bindings) (caller : List Nat)
    (Δ : List Constraint) (env : List BodyBinding) (ctx : BodyBranchContext)
    (branches : List (MatchPattern × Expr)) where
  actuals : Nat → BoundsTy
  typing : ∀ i br, branches[i]? = some br →
    BodyDerives ids rows (Δ ++ ctx.refine br.1) (ctx.extend br.1 env) br.2.stripFound (actuals i)
  patterns : ∀ br ∈ branches, ctx.Pattern br.1
  bounds : Option BoundsTy
  inclusions : ∀ i br, branches[i]? = some br →
    match bounds with | none => False | some β => SemanticSub (Δ ++ ctx.refine br.1) (actuals i) β
  nodes : List Typed.NodeResult
  runtimeReady : Option (PLift (∀ i br atIndex, BodyDerives.RuntimeReady (typing i br atIndex)))

private abbrev BodyBranchSources (output : Expr) (path : CorePath) (index : Nat)
    (branches : List (MatchPattern × Expr)) :=
  ∀ i br, branches[i]? = some br →
    Option (PLift (output.atCorePath (path ++ [.matchBranch (index + i)]) = some br.2))

private def prependBodyBranches {ids rows caller Δ env br branches} {ctx : BodyBranchContext}
    (head : BodyResult ids rows caller (Δ ++ ctx.refine br.1) (ctx.extend br.1 env) br.2)
    (hp : ctx.Pattern br.1) (tail : BodyBranches ids rows caller Δ env ctx branches)
    (β : BoundsTy) (hh : SemanticSub (Δ ++ ctx.refine br.1) head.bounds β)
    (ht : ∀ i arm, branches[i]? = some arm → SemanticSub (Δ ++ ctx.refine arm.1) (tail.actuals i) β) :
    BodyBranches ids rows caller Δ env ctx (br :: branches) where
  actuals := fun i => match i with | 0 => head.bounds | i + 1 => tail.actuals i
  typing := by
    intro i arm h
    cases i with
    | zero => simp only [List.getElem?_cons_zero, Option.some.injEq] at h; subst arm; exact head.typing
    | succ i => exact tail.typing i arm (by simpa only [List.getElem?_cons_succ] using h)
  patterns := by
    intro arm h
    rcases List.mem_cons.mp h with rfl | h
    · exact hp
    · exact tail.patterns arm h
  bounds := some β
  inclusions := by
    intro i arm h
    cases i with
    | zero => simp only [List.getElem?_cons_zero, Option.some.injEq] at h; subst arm; exact hh
    | succ i => exact ht i arm (by simpa only [List.getElem?_cons_succ] using h)
  nodes := head.nodes ++ tail.nodes
  runtimeReady := do
    let hh ← head.runtimeReady
    let ht ← tail.runtimeReady
    pure ⟨by
      intro i arm atIndex
      cases i with
      | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at atIndex
          subst arm
          exact hh.down
      | succ i => exact ht.down i arm (by simpa only [List.getElem?_cons_succ] using atIndex)⟩

private theorem body_match_typing {ids rows caller Δ env branches β} {ctx : BodyBranchContext} {scrut : Expr}
    (hs : BodyDerives ids rows Δ env scrut.stripFound ctx.bounds)
    (arms : BodyBranches ids rows caller Δ env ctx branches) (hb : arms.bounds = some β)
    (hc : ctx.Covers Δ (Expr.stripFoundBranches branches)) :
    BodyDerives ids rows Δ env (Expr.match_ scrut branches).stripFound β := by
  simp only [Expr.stripFound]
  apply BodyDerives.match_ (actuals := arms.actuals) hs hc
  · intro arm ha
    rw [RecursiveHMWalk.stripBranches] at ha
    rcases List.mem_map.mp ha with ⟨br, hm, rfl⟩
    exact arms.patterns br hm
  · intro i arm ha
    rcases RecursiveHMWalk.strip_index ha with ⟨br, hm, rfl⟩
    exact arms.typing i br hm
  · intro i arm ha
    rcases RecursiveHMWalk.strip_index ha with ⟨br, hm, rfl⟩
    simpa only [hb] using arms.inclusions i br hm

private def body_match_ready {ids rows caller Δ env branches β} {ctx : BodyBranchContext} {scrut : Expr}
    (hs : BodyDerives ids rows Δ env scrut.stripFound ctx.bounds)
    (arms : BodyBranches ids rows caller Δ env ctx branches) (hb : arms.bounds = some β)
    (hc : ctx.Covers Δ (Expr.stripFoundBranches branches))
    (ready : Option (PLift (BodyDerives.RuntimeReady hs))) :
    Option (PLift (BodyDerives.RuntimeReady (body_match_typing hs arms hb hc))) := do
  let input ← ready
  let bodies ← arms.runtimeReady
  let result ← Runtime.supported? β
  pure ⟨by
    simp only [Expr.stripFound]
    refine BodyDerives.RuntimeReady.match_ (actuals := arms.actuals) hc ?_ ?_ ?_ input.down ?_ result.down
    · intro arm member
      rw [RecursiveHMWalk.stripBranches] at member
      obtain ⟨br, atSource, rfl⟩ := List.mem_map.mp member
      exact arms.patterns br atSource
    · intro i arm atIndex
      rcases RecursiveHMWalk.strip_index atIndex with ⟨br, atSource, rfl⟩
      exact arms.typing i br atSource
    · intro i arm atIndex
      rcases RecursiveHMWalk.strip_index atIndex with ⟨br, atSource, rfl⟩
      simpa only [hb] using arms.inclusions i br atSource
    · intro i arm atIndex
      rcases RecursiveHMWalk.strip_index atIndex with ⟨br, atSource, rfl⟩
      exact bodies.down i br atSource⟩

private theorem body_path_assuming (Δ Γ : List Constraint) :
    (⟨Δ ++ Γ, Δ⟩ : ForallProblem).Valid := fun _ h c hc => h c (List.mem_append_left Γ hc)

private def appendBody {ids rows caller Δ env fn arg} (path : CorePath) (hm : Ty)
    (prior : BodyResult ids rows caller Δ env fn) (actual : BodyResult ids rows caller Δ env arg) :
    Except String (BodyResult ids rows caller Δ env (.found hm (.app fn arg))) := do
  match hf : prior.bounds with
  | .arrow domain result =>
      let sub ← Typed.subtype Δ actual.bounds domain
      finishBody path hm result rfl
        (by simpa only [Expr.stripFound] using
          (BodyDerives.app (by simpa only [hf] using prior.typing) actual.typing sub.down))
        (prior.nodes ++ actual.nodes)
        (do
          let fn ← prior.runtimeReady
          let arg ← actual.runtimeReady
          pure ⟨by
            simp only [Expr.stripFound]
            apply BodyDerives.RuntimeReady.app sub.down
            · simpa only [hf] using fn.down
            · exact arg.down⟩)
  | _ => throw "bounds: generalized body function is not an arrow"

private def freshLocalTypeIds (output : Expr) (arity : Nat) : List Nat :=
  freshVars (output.tyFreeVars.foldl Nat.max 0 + 1) arity

private def freshGuardedLocalTypeIds (output : Expr) (guards : List Ty) (arity : Nat) : List Nat :=
  freshVars ((output.tyFreeVars ++ guards.flatMap Ty.freeVars).foldl Nat.max 0 + 1) arity

private def descendBodySource {output e child : Expr} {path suffix : CorePath}
    (source : Option (PLift (output.atCorePath path = some e)))
    (localPath : e.atCorePath suffix = some child) :
    Option (PLift (output.atCorePath (path ++ suffix) = some child)) :=
  source.map fun located => ⟨by
    rw [Expr.atCorePath_append, located.down]
    exact localPath⟩

private inductive BodySpine (sourceOutput : Expr) (ids : List Nat) (rows : Bindings) (caller : List Nat)
    (Δ : List Constraint) (env : List BodyBinding) : {e : Expr} → RecursiveSpine.Syntax e → Type where
  | head (path : CorePath) (i : Nat) (hm : Ty) :
      BodySpine sourceOutput ids rows caller Δ env (.head path i hm)
  | app {fn : Expr} {prior : RecursiveSpine.Syntax fn} {arg : Expr} (path : CorePath) (hm : Ty)
      (previous : BodySpine sourceOutput ids rows caller Δ env prior)
      (actual : Option (BodyResult ids rows caller Δ env arg))
      (source : Option (PLift (sourceOutput.atCorePath (path ++ [.appArg]) = some arg))) :
      BodySpine sourceOutput ids rows caller Δ env (.app path hm prior arg)

private def BodySpine.originsRev {sourceOutput ids rows caller Δ env e}
    {spine : RecursiveSpine.Syntax e} :
    BodySpine sourceOutput ids rows caller Δ env spine → List (Option BoundsTy)
  | .head _ _ _ => []
  | .app _ _ previous actual _ => actual.map (·.bounds) :: previous.originsRev

/-- A parsed exported spine together with exact paths back into the single
    original found artifact. Keeping this evidence beside the syntax avoids
    any equality oracle for `Expr` (which intentionally has no `DecidableEq`). -/
private inductive BodySpineSource (output : Expr) :
    {e : Expr} → RecursiveSpine.Syntax e → Type where
  | head {path i hm} :
      output.atCorePath path = some (.found hm (.var i)) →
      BodySpineSource output (.head path i hm)
  | app {fn : Expr} {path : CorePath} {hm : Ty}
      {prior : RecursiveSpine.Syntax fn} {arg : Expr} :
      BodySpineSource output prior →
      output.atCorePath (path ++ [.appArg]) = some arg →
      BodySpineSource output (.app path hm prior arg)

private def parseBodySpineSource (output : Expr) (path : CorePath) (e : Expr)
    (source : PLift (output.atCorePath path = some e)) :
    Option (Σ spine : RecursiveSpine.Syntax e, PLift (BodySpineSource output spine)) :=
  match e with
  | .found hm (.var i) => some ⟨.head path i hm, ⟨.head source.down⟩⟩
  | .found hm (.app fn arg) => do
      have fnSource : output.atCorePath (path ++ [.appFun]) = some fn := by
        rw [Expr.atCorePath_append, source.down]
        simp [Expr.atCorePath]
      have argSource : output.atCorePath (path ++ [.appArg]) = some arg := by
        rw [Expr.atCorePath_append, source.down]
        simp [Expr.atCorePath]
      let ⟨prior, priorSource⟩ ← parseBodySpineSource output (path ++ [.appFun]) fn ⟨fnSource⟩
      pure ⟨.app path hm prior arg, ⟨.app priorSource.down argSource⟩⟩
  | _ => none
termination_by sizeOf e

private def memberNodes {output metadata path captures premises typeCaptures env index vectors}
    {ps : HMDeclaredGroup.Interfaces output metadata path captures premises typeCaptures index vectors}
    (ms : HMDeclaredGroup.CheckedMembers env ps) : List Typed.NodeResult :=
  match ms with
  | .nil => []
  | .cons head rest => head.rhs.located.nodes ++ memberNodes rest

mutual
/-- One exported use at the head, then the ordinary application rule at EVERY
    original frame. Counts/HM arguments are never reproposed at a prefix. -/
private def useBodySpine (sourceOutput : Expr) (metadata : Scope.Metadata)
    {ids rows caller Δ env e} {spine : RecursiveSpine.Syntax e}
    (checked : BodySpine sourceOutput ids rows caller Δ env spine) {s : HMCountScheme.Scheme}
    (lookup : env[spine.index]? = some (.exported s))
    (used : HMCountScheme.Use s Δ spine.headHM caller) (schemes : BinderSchemeMap)
    (capture : Option (BodyCapture env)) :
    Except String (BodyResult ids rows caller Δ env e) := do
  match checked with
  | .head path i hm =>
      finishBody path hm used.bounds rfl
        (by simpa only [Expr.stripFound] using BodyDerives.varExported lookup used) []
        (do
          let supported ← Runtime.supported? used.bounds
          let arguments ← Runtime.supportedArguments? used.types
          pure ⟨by simpa only [Expr.stripFound] using
            (BodyDerives.RuntimeReady.varExported (ids := ids) (rows := rows)
              (i := i) lookup used supported.down arguments.down)⟩)
  | .app (arg := arg) path hm previous actual source =>
      let prior ← useBodySpine sourceOutput metadata previous lookup used schemes capture
      match prior.bounds with
      | .arrow domain _ =>
          let checked ← match actual with
            | some checked => pure checked
            | none =>
                walkBodySource sourceOutput metadata ids rows caller Δ env
                  (path ++ [.appArg]) arg schemes capture source (some domain)
          appendBody path hm prior checked
      | _ => throw "bounds: deferred generalized body spine applies a non-arrow scheme result"
termination_by (sizeOf e, 0)

/-- Source-linked body traversal: literals, List origins, scalar operators,
    lambdas, mono/generalized locals, matches and origin-backed exported
    application spines, including arguments deferred until later origins are
    known. Nested groups remain an explicit frontier. -/
private def walkBodySource (sourceOutput : Expr) (metadata : Scope.Metadata)
    (ids : List Nat) (rows : Bindings) (caller : List Nat) (Δ : List Constraint)
    (env : List BodyBinding) (path : CorePath) (e : Expr) (schemes : BinderSchemeMap)
    (capture : Option (BodyCapture env))
    (sourceAt : Option (PLift (sourceOutput.atCorePath path = some e)))
    (expected : Option BoundsTy) : Except String (BodyResult ids rows caller Δ env e) := do
  match e with
  | .found hm (.primLit p) =>
      finishBody path hm (boundInfoOfPrimLit p) rfl (by simpa only [Expr.stripFound] using BodyDerives.literal) []
        (some ⟨by simpa only [Expr.stripFound] using
          (@BodyDerives.RuntimeReady.literal BoundsTy.fvar BoundsTy.bvar ids rows Δ env p)⟩)
  | .found hm (.primBinOp op) =>
      finishBody path hm (Typed.primOpBounds op) rfl (by simpa only [Expr.stripFound] using BodyDerives.primBinOp) []
        (some ⟨by simpa only [Expr.stripFound] using
          (@BodyDerives.RuntimeReady.primBinOp BoundsTy.fvar BoundsTy.bvar ids rows Δ env op)⟩)
  | .found hm (.ctor name) =>
      if hn : name = nilCtorName then
        match hm.eraseBounds with
        | .customTy n [a] =>
            if n = listTyName then
              let elem ← match expected with
                | some (.list _ _ elem) => pure elem
                | _ => Typed.shapeTop a
              finishBody path hm (.list (.lit 0) (.lit 0) elem) rfl
                (by subst name; simpa only [Expr.stripFound] using BodyDerives.nil) []
                (do
                  let supported ← Runtime.supported? elem
                  pure ⟨by
                    subst name
                    simpa only [Expr.stripFound] using
                      (@BodyDerives.RuntimeReady.nil BoundsTy.fvar BoundsTy.bvar ids rows Δ env elem supported.down)⟩)
            else throw "bounds: generalized body Nil has a non-List found payload"
        | _ => throw "bounds: generalized body Nil has a non-List found payload"
      else if hb : BoolBranches.IsCtor name then
        finishBody path hm (.custom boolTyName []) rfl
          (by simpa only [Expr.stripFound] using BodyDerives.boolCtor hb) []
          (some ⟨by simpa only [Expr.stripFound] using
            (@BodyDerives.RuntimeReady.boolCtor BoundsTy.fvar BoundsTy.bvar ids rows Δ env name hb)⟩)
      else throw "bounds: unsupported standalone constructor in generalized body"
  | .found hm (.var i) =>
      match hv : env[i]? with
      | some (.mono β) =>
          finishBody path hm β rfl
            (by simpa only [Expr.stripFound] using BodyDerives.varMono hv) []
            (do
              let supported ← Runtime.supported? β
              pure ⟨by simpa only [Expr.stripFound] using
                (BodyDerives.RuntimeReady.varMono (ids := ids) (rows := rows) (i := i) hv supported.down)⟩)
      | some (.exported s) =>
          if s.hm.paramCount == 0 && s.counts.quantified.isEmpty then
            let used ← HMCountScheme.check s Δ hm [] [] caller
            finishBody path hm used.bounds rfl
              (by simpa only [Expr.stripFound] using BodyDerives.varExported hv used) []
              (do
                let supported ← Runtime.supported? used.bounds
                let arguments ← Runtime.supportedArguments? used.types
                pure ⟨by simpa only [Expr.stripFound] using
                  (BodyDerives.RuntimeReady.varExported (ids := ids) (rows := rows)
                    (i := i) hv used supported.down arguments.down)⟩)
          else throw "bounds: exported polymorphic use needs origin-backed arguments"
      | none => throw "bounds: generalized body variable outside binding environment"
  | .found hm (.lambda ann body) =>
      match hm.eraseBounds with
      | .arrow paramHM _ =>
          let paramHint := match expected with | some (.arrow a _) => some a | _ => none
          let bodyHint := match expected with | some (.arrow _ b) => some b | _ => none
          let param ← RecursiveHMAnnotation.chooseScopedParam BoundsTy.fvar BoundsTy.bvar ids rows caller Δ ann paramHM paramHint
          let result ← walkBodySource sourceOutput metadata ids rows caller Δ
            (.mono param.bounds :: env) (path ++ [.lambdaBody]) body schemes
            (extendMonoCapture? capture param.bounds)
            (descendBodySource sourceAt (by simp [Expr.atCorePath])) bodyHint
          finishBody path hm (.arrow param.bounds result.bounds) rfl
            (by simpa only [Expr.stripFound] using BodyDerives.lambda param.obligation result.typing) result.nodes
            (do
              let supported ← Runtime.supported? param.bounds
              let body ← result.runtimeReady
              pure ⟨by simpa only [Expr.stripFound] using
                (BodyDerives.RuntimeReady.lambda (ann := ann) param.obligation supported.down body.down)⟩)
      | _ => throw "bounds: generalized body lambda has a non-arrow found payload"
  | .found hm (.app (.found partialHM (.app (.found ctorHM (.ctor name)) head)) tail) =>
      if hn : name = consCtorName then
        let headHint := match expected with | some (.list _ _ elem) => some elem | _ => none
        let h ← walkBodySource sourceOutput metadata ids rows caller Δ env
          (path ++ [.appFun, .appArg]) head schemes
          capture (descendBodySource sourceAt (by simp [Expr.atCorePath])) headHint
        let t ← walkBodySource sourceOutput metadata ids rows caller Δ env
          (path ++ [.appArg]) tail schemes capture
          (descendBodySource sourceAt (by simp [Expr.atCorePath]))
          (some (.list (.lit 0) .inf h.bounds))
        match ht : t.bounds with
        | .list lo hi elem =>
            let _ ← match BinderBridge.equalTy ctorHM.eraseBounds (.arrow h.hm.eraseBounds (.arrow t.hm.eraseBounds t.hm.eraseBounds)) with
              | some h => pure h | none => throw "bounds: generalized body Cons constructor payload mismatch"
            let _ ← match BinderBridge.equalTy partialHM.eraseBounds (.arrow t.hm.eraseBounds t.hm.eraseBounds) with
              | some h => pure h | none => throw "bounds: generalized body partial Cons payload mismatch"
            let sub ← Typed.subtype Δ h.bounds elem
            finishBody path hm (.list (.add lo (.lit 1)) (.add hi (.lit 1)) elem) rfl
              (by subst name; simpa only [Expr.stripFound] using
                BodyDerives.cons h.typing (by simpa only [ht] using t.typing) sub.down)
              (⟨path ++ [.appFun], partialHM.eraseBounds, none⟩ ::
                ⟨path ++ [.appFun, .appFun], ctorHM.eraseBounds, none⟩ :: h.nodes ++ t.nodes)
              (do
                let head ← h.runtimeReady
                let tail ← t.runtimeReady
                pure ⟨by
                  subst name
                  simp only [Expr.stripFound]
                  apply BodyDerives.RuntimeReady.cons sub.down head.down
                  simpa only [ht] using tail.down⟩)
        | _ => throw "bounds: generalized body Cons tail is not a List"
      else if hp : name = pairCtorName then
        let leftHint := match expected with
          | some (.custom pairName [left, _]) => if pairName = pairTyName then some left else none
          | _ => none
        let rightHint := match expected with
          | some (.custom pairName [_, right]) => if pairName = pairTyName then some right else none
          | _ => none
        let left ← walkBodySource sourceOutput metadata ids rows caller Δ env
          (path ++ [.appFun, .appArg]) head schemes capture
          (descendBodySource sourceAt (by simp [Expr.atCorePath])) leftHint
        let right ← walkBodySource sourceOutput metadata ids rows caller Δ env
          (path ++ [.appArg]) tail schemes capture
          (descendBodySource sourceAt (by simp [Expr.atCorePath])) rightHint
        let _ ← match BinderBridge.equalTy ctorHM.eraseBounds
            (.arrow left.hm.eraseBounds (.arrow right.hm.eraseBounds hm.eraseBounds)) with
          | some h => pure h | none => throw "bounds: generalized body Pair constructor payload mismatch"
        let _ ← match BinderBridge.equalTy partialHM.eraseBounds
            (.arrow right.hm.eraseBounds hm.eraseBounds) with
          | some h => pure h | none => throw "bounds: generalized body partial Pair payload mismatch"
        finishBody path hm (.custom pairTyName [left.bounds, right.bounds]) rfl
          (by subst name; simpa only [Expr.stripFound] using
            BodyDerives.pair left.typing right.typing)
          (⟨path ++ [.appFun], partialHM.eraseBounds, none⟩ ::
            ⟨path ++ [.appFun, .appFun], ctorHM.eraseBounds, none⟩ :: left.nodes ++ right.nodes)
          (do
            let leftReady ← left.runtimeReady
            let rightReady ← right.runtimeReady
            pure ⟨by
              subst name
              simpa only [Expr.stripFound] using
                BodyDerives.RuntimeReady.pair leftReady.down rightReady.down⟩)
      else throw "bounds: generalized body constructor application unsupported"
  | .found hm (.app fn arg) =>
      match sourceAt.bind (parseBodySpineSource sourceOutput path (.found hm (.app fn arg))) with
      | some ⟨spine, spineSource⟩ =>
          match hv : env[spine.index]? with
          | some (.exported s) =>
              let checked ← walkBodySpineSourced sourceOutput metadata ids rows caller Δ env
                spine schemes capture spineSource.down
              let origins := checked.originsRev.reverse
              let types ← StructuralApplication.proposeOrigins s.counts.body origins s.hm.paramCount
              let counts ← CountProposal.proposeOrigins s.counts.quantified s.counts.body origins
              let used ← HMCountScheme.check s Δ spine.headHM counts types caller
              return ← useBodySpine sourceOutput metadata checked hv used schemes capture
          | _ => pure ()
      | none =>
          match RecursiveSpine.Syntax.parse path (.found hm (.app fn arg)) with
          | some spine =>
              match hv : env[spine.index]? with
              | some (.exported s) =>
                  let checked ← walkBodySpine sourceOutput metadata ids rows caller Δ env
                    spine schemes capture
                  let origins := checked.originsRev.reverse
                  let types ← StructuralApplication.proposeOrigins s.counts.body origins s.hm.paramCount
                  let counts ← CountProposal.proposeOrigins s.counts.quantified s.counts.body origins
                  let used ← HMCountScheme.check s Δ spine.headHM counts types caller
                  return ← useBodySpine sourceOutput metadata checked hv used schemes capture
              | _ => pure ()
          | none => pure ()
      let function ← walkBodySource sourceOutput metadata ids rows caller Δ env
        (path ++ [.appFun]) fn schemes capture
        (descendBodySource sourceAt (by simp [Expr.atCorePath])) none
      let actual ← walkBodySource sourceOutput metadata ids rows caller Δ env
        (path ++ [.appArg]) arg schemes capture
        (descendBodySource sourceAt (by simp [Expr.atCorePath])) none
      appendBody path hm function actual
  | .found hm (.letIn ann rhs body) =>
      match ann with
      | some annotation =>
          if annotation.paramCount == 0 &&
              (metadata.telescopes.filter (fun telescope => telescope.site == .letIn path)).isEmpty then
            let hint ← RecursiveHMAnnotation.scopedBindingHint BoundsTy.fvar BoundsTy.bvar
              ids rows caller (some annotation)
            let actual ← walkBodySource sourceOutput metadata ids rows caller Δ env
              (path ++ [.letRhs]) rhs schemes capture
              (descendBodySource sourceAt (by simp [Expr.atCorePath])) hint
            let _ ← RecursiveHMWalk.checkLocalInterface (some annotation) schemes
              (.letIn path) actual.hm
            let obligation ← RecursiveHMAnnotation.checkScopedBinding BoundsTy.fvar BoundsTy.bvar
              ids rows caller Δ (some annotation) actual.bounds
            let result ← walkBodySource sourceOutput metadata ids rows caller Δ
              (.mono actual.bounds :: env) (path ++ [.letBody]) body schemes
              (extendMonoCapture? capture actual.bounds)
              (descendBodySource sourceAt (by simp [Expr.atCorePath])) expected
            finishBody path hm result.bounds rfl
              (by simpa only [Expr.stripFound] using
                (BodyDerives.letMono obligation.down actual.typing result.typing))
              (actual.nodes ++ result.nodes)
              (do
                let rhsReady ← actual.runtimeReady
                let bodyReady ← result.runtimeReady
                pure ⟨by simpa only [Expr.stripFound] using
                  (BodyDerives.RuntimeReady.letMono (ann := some annotation)
                    obligation.down rhsReady.down bodyReady.down)⟩)
          else
            let sourceProof ← match sourceAt with
              | some located => pure located
              | none => throw "bounds: generalized local lacks exact source provenance"
            if parentIds : ids = [] then
              if parentRows : rows = [] then
                unless metadata.problems.isEmpty do
                  throw "bounds: unresolved or duplicate count scope in generalized local declaration"
                let quantified ← ScopedDeclaration.telescope metadata (.letIn path)
                match rhs with
                | .found rhsHM rhsInner =>
                    have descent : sourceOutput.atCorePath (path ++ [.letRhs]) =
                        some (.found rhsHM rhsInner) := by
                      rw [Expr.atCorePath_append, sourceProof.down]
                      simp [Expr.atCorePath]
                    let node : HMFoundView.AtNode sourceOutput (path ++ [.letRhs]) :=
                      ⟨rhsHM, rhsInner, descent⟩
                    let declaration : HMDeclaredReconciliation.Declaration sourceOutput (.letIn path) :=
                      ⟨annotation, path ++ [.letRhs], .letIn sourceProof.down, node⟩
                    match capture with
                    | none =>
                        let signatureIds := freshLocalTypeIds sourceOutput annotation.paramCount
                        let reconciled ← HMDeclaredReconciliation.check declaration quantified []
                          signatureIds [] []
                        let checked ← HMDeclaredRHS.check reconciled [] schemes
                        let frame := declaredLocalFrame reconciled
                        let cert := declaredLocalCertificate reconciled checked
                        let annotationOK : LocalAnnotationOK reconciled.interface.scheme (some annotation) :=
                          ⟨reconciled.interface, rfl⟩
                        have owners : cert.opening.ids = frame.owned := by
                          simpa only [cert, frame, declaredLocalCertificate, declaredLocalFrame] using
                            reconciled.openingIds
                        have rhsScope : declaration.node.inner.stripFound.varsBelow env.length = true :=
                          Expr.varsBelow_mono _ (Nat.zero_le env.length) cert.typing.varsBelow
                        let instances := fun calleeΔ found localCaller
                            (used : HMCountScheme.Use reconciled.interface.scheme calleeΔ found localCaller) =>
                          localRhsInstances (Δ := Δ) frame annotationOK cert owners used env
                        let result ← walkBodySource sourceOutput metadata [] [] caller Δ
                          (.exported reconciled.interface.scheme :: env)
                          (path ++ [.letBody]) body schemes none
                          (descendBodySource sourceAt (by simp [Expr.atCorePath])) expected
                        let completed ← finishBody (ids := []) (rows := []) (caller := caller)
                          (Δ := Δ) (env := env)
                          (e := .found hm (.letIn (some annotation) (.found rhsHM rhsInner) body))
                          path hm result.bounds rfl
                          (by
                            let derivation := ScopedBodyDerives.letExported frame annotationOK
                              rhsScope instances result.typing
                            simpa only [Expr.stripFound, declaration, node] using derivation)
                          (checked.located.nodes ++ result.nodes)
                          (do
                            let sourceReady ← checked.located.typed.runtimeReady
                            let bodyReady ← result.runtimeReady
                            let certReady := declaredLocalCertificate_runtimeReady
                              reconciled checked sourceReady.down
                            pure ⟨by
                              let ready := BodyDerives.RuntimeReady.letExported frame annotationOK
                                rhsScope instances
                                (fun calleeΔ found localCaller used arguments =>
                                  localRhsInstances_runtimeReady frame annotationOK cert owners certReady
                                    used arguments env)
                                bodyReady.down
                              simpa only [Expr.stripFound, declaration, node] using ready⟩)
                        pure (by rw [parentIds, parentRows]; exact completed)
                    | some captured =>
                        let typeCaptures := recursiveTypeCaptures captured.rhsEnv ++
                          recursiveFixedTypeCaptures captured.rhsEnv
                        let signatureIds := freshGuardedLocalTypeIds sourceOutput typeCaptures
                          annotation.paramCount
                        let reconciled ← HMDeclaredReconciliation.check declaration quantified []
                          signatureIds typeCaptures []
                        let stable ← RecursiveHMEnvironment.checkTypesFixed
                          reconciled.interpretation captured.rhsEnv
                        let checked ← HMDeclaredRHS.check reconciled captured.rhsEnv schemes
                        let represented := fun c member => List.mem_append_left _
                          (recursiveTypeCaptures_represented member)
                        let exportsRepresented := fun s member => List.mem_append_left _
                          (recursiveTypeCaptures_exported member)
                        let countFresh := fun c member i inside => by
                          rw [captured.countClosed c member] at inside
                          cases inside
                        let exportCountFresh := fun s member i inside => by
                          rw [captured.exportCountClosed s member] at inside
                          cases inside
                        let frame := declaredLocalFrame reconciled
                        let cert := declaredCapturedLocalCertificate reconciled checked
                          represented exportsRepresented countFresh exportCountFresh
                        let annotationOK : LocalAnnotationOK reconciled.interface.scheme (some annotation) :=
                          ⟨reconciled.interface, rfl⟩
                        have owners : cert.opening.ids = frame.owned := by
                          simpa only [cert, frame, declaredCapturedLocalCertificate,
                            declaredLocalFrame] using reconciled.openingIds
                        have stableEnv : captured.rhsEnv.map
                            (mapBinding reconciled.interpretation reconciled.interpretationLC) =
                            captured.rhsEnv :=
                          RecursiveHMEnvironment.typesFixed reconciled.interpretationLC stable.down
                        have certCaptured : RecursiveHMEnvironment.Captured
                            reconciled.interface.scheme.counts.captures
                            (captured.rhsEnv.map
                              (mapBinding reconciled.interpretation reconciled.interpretationLC)) := by
                          simpa only [stableEnv] using captured.captured
                        have certArguments : RecursiveArgumentsSupported (captured.rhsEnv.map
                            (mapBinding reconciled.interpretation reconciled.interpretationLC)) := by
                          simpa only [stableEnv] using captured.arguments
                        have envLength : captured.rhsEnv.length = env.length := by
                          have lengths := congrArg List.length captured.bodyEnv
                          simpa only [ordinaryBodyEnv, List.length_map] using lengths
                        have rhsScope : declaration.node.inner.stripFound.varsBelow env.length = true := by
                          simpa only [List.length_map, envLength] using cert.typing.varsBelow
                        let instances := fun calleeΔ found localCaller
                            (used : HMCountScheme.Use reconciled.interface.scheme calleeΔ found localCaller) =>
                          (by
                            have originalFixed := declaredLocalArgumentTypesFixed reconciled stable.down
                              (fun β member => List.mem_append_left _
                                (recursiveTypeCaptures_mono member))
                              (fun contract member β argument => List.mem_append_right _
                                (recursiveFixedTypeCaptures_represented member argument)) used
                            have certFixed : RecursiveHMEnvironment.TypesFixed
                                (argument cert.opening.ids (SchemeUse.vector used.types))
                                (captured.rhsEnv.map
                                  (mapBinding reconciled.interpretation reconciled.interpretationLC)) := by
                              simpa only [cert, declaredCapturedLocalCertificate, stableEnv] using originalFixed
                            have derived := capturedLocalRhsInstances (Δ := Δ) frame annotationOK
                              cert owners certCaptured used certFixed
                            simpa only [List.append_nil, stableEnv, captured.bodyEnv] using derived :
                            ScopedBodyDerives
                              (localTypes frame.owned BoundsTy.fvar used.types)
                              (localSlots (some annotation) BoundsTy.bvar used.types)
                              (reconciled.interface.scheme.counts.quantified ++
                                reconciled.interface.scheme.counts.captures ++ [])
                              (CountAlgebra.compose
                                (reconciled.interface.scheme.counts.quantified.zip used.counts) [])
                              (Δ ++ used.countInstance.premises) env
                              declaration.node.inner.stripFound used.bounds)
                        let result ← walkBodySource sourceOutput metadata [] [] caller Δ
                          (.exported reconciled.interface.scheme :: env)
                          (path ++ [.letBody]) body schemes
                          (some (captured.extendExported reconciled.interface.scheme (by
                            simp [HMCountScheme.Annotated.scheme, ScopedAnnotation.Contract.scheme])))
                          (descendBodySource sourceAt (by simp [Expr.atCorePath])) expected
                        let completed ← finishBody (ids := []) (rows := []) (caller := caller)
                          (Δ := Δ) (env := env)
                          (e := .found hm (.letIn (some annotation) (.found rhsHM rhsInner) body))
                          path hm result.bounds rfl
                          (by
                            let derivation := ScopedBodyDerives.letExported frame annotationOK
                              rhsScope instances result.typing
                            simpa only [Expr.stripFound, declaration, node] using derivation)
                          (checked.located.nodes ++ result.nodes)
                          (do
                            let sourceReady ← checked.located.typed.runtimeReady
                            let bodyReady ← result.runtimeReady
                            let certReady := declaredCapturedLocalCertificate_runtimeReady
                              reconciled checked represented exportsRepresented countFresh
                                exportCountFresh sourceReady.down
                            pure ⟨by
                              let ready := BodyDerives.RuntimeReady.letExported frame annotationOK
                                rhsScope instances
                                (fun calleeΔ found localCaller used arguments => by
                                  have originalFixed := declaredLocalArgumentTypesFixed reconciled stable.down
                                    (fun β member => List.mem_append_left _
                                      (recursiveTypeCaptures_mono member))
                                    (fun contract member β argument => List.mem_append_right _
                                      (recursiveFixedTypeCaptures_represented member argument)) used
                                  have certFixed : RecursiveHMEnvironment.TypesFixed
                                      (argument cert.opening.ids (SchemeUse.vector used.types))
                                      (captured.rhsEnv.map
                                        (mapBinding reconciled.interpretation reconciled.interpretationLC)) := by
                                    simpa only [cert, declaredCapturedLocalCertificate, stableEnv] using originalFixed
                                  have instanceReady := capturedLocalRhsInstances_runtimeReady
                                    (Δ := Δ) frame annotationOK cert owners certReady certCaptured used
                                    certFixed certArguments arguments
                                  simpa only [List.append_nil, stableEnv, captured.bodyEnv] using
                                    instanceReady)
                                bodyReady.down
                              simpa only [Expr.stripFound, declaration, node] using ready⟩)
                        pure (by rw [parentIds, parentRows]; exact completed)
                | _ => throw "bounds: generalized local RHS lacks its original found root"
              else throw "bounds: generalized local under enclosing count substitutions is not supported yet"
            else throw "bounds: generalized local under enclosing count identities is not supported yet"
      | none =>
          let hint ← RecursiveHMAnnotation.scopedBindingHint BoundsTy.fvar BoundsTy.bvar
            ids rows caller none
          let actual ← walkBodySource sourceOutput metadata ids rows caller Δ env
            (path ++ [.letRhs]) rhs schemes capture
            (descendBodySource sourceAt (by simp [Expr.atCorePath])) hint
          let _ ← RecursiveHMWalk.checkLocalInterface none schemes (.letIn path) actual.hm
          let result ← walkBodySource sourceOutput metadata ids rows caller Δ
            (.mono actual.bounds :: env) (path ++ [.letBody]) body schemes
            (extendMonoCapture? capture actual.bounds)
            (descendBodySource sourceAt (by simp [Expr.atCorePath])) expected
          finishBody path hm result.bounds rfl
            (by simpa only [Expr.stripFound] using
              (BodyDerives.letMono (by trivial) actual.typing result.typing))
            (actual.nodes ++ result.nodes)
            (do
              let rhsReady ← actual.runtimeReady
              let bodyReady ← result.runtimeReady
              pure ⟨by simpa only [Expr.stripFound] using
                (BodyDerives.RuntimeReady.letMono (ann := none) (by trivial)
                  rhsReady.down bodyReady.down)⟩)
  | .found hm (.match_ scrut branches) =>
      let input ← walkBodySource sourceOutput metadata ids rows caller Δ env
        (path ++ [.matchScrut]) scrut schemes capture
        (descendBodySource sourceAt (by simp [Expr.atCorePath])) none
      -- Equality of full bounds, not merely HM shape, connects scrutinee origins
      -- with constructor refinements and freshly opened field bindings.
      let ⟨ctx, hin⟩ ← bodyBranchContext input.bounds
      let coverage ← ctx.checkCoverage Δ (Expr.stripFoundBranches branches)
      let branchSources : BodyBranchSources sourceOutput path 0 branches := fun i br atIndex =>
        sourceAt.map fun located => ⟨by
          simp only [Nat.zero_add]
          rw [Expr.atCorePath_append, located.down]
          simp only [Expr.atCorePath, Option.bind_some]
          rw [atIndex]⟩
      let arms ← walkBodyBranches sourceOutput metadata ids rows caller Δ env ctx path branches 0
        schemes capture branchSources expected
      match hb : arms.bounds with
      | none => throw "bounds: generalized body match has no result-producing branch"
      | some β =>
          finishBody path hm β rfl
            (by simpa only [Expr.stripFound] using
              body_match_typing (by simpa only [hin.down] using input.typing) arms hb coverage.down)
            (input.nodes ++ arms.nodes)
            (by simpa only [Expr.stripFound] using
              (body_match_ready (by simpa only [hin.down] using input.typing) arms hb coverage.down
                (by simpa only [hin.down] using input.runtimeReady)))
  | .found hm (.letRec annotations rhss body) =>
      let sourceProof ← match sourceAt with
        | some located => pure located
        | none => throw "bounds: nested recursive group lacks exact source provenance"
      match capture with
      | none => throw "bounds: nested recursive group lacks a captured lexical environment"
      | some captured =>
          let typeCaptures := recursiveTypeCaptures captured.rhsEnv ++
            recursiveFixedTypeCaptures captured.rhsEnv
          let assembled ← HMDeclaredCoordinates.check sourceOutput metadata path [] Δ
            typeCaptures captured.rhsEnv schemes
          let g := assembled.checked
          have sourceEq : Expr.found hm (Expr.letRec annotations rhss body) =
              Expr.found g.originalHM (Expr.letRec g.annotations g.rhss g.body) := by
            exact Option.some.inj (sourceProof.down.symm.trans g.source)
          have bodyEq : body = g.body := by
            injection sourceEq with _ innerEq
            injection innerEq
          have bodySource : sourceOutput.atCorePath (path ++ [.letRecBody]) = some body := by
            rw [Expr.atCorePath_append, g.source]
            simp [Expr.atCorePath, bodyEq]
          let result ← walkBodySource sourceOutput metadata ids rows caller Δ
            (g.exports.map BodyBinding.exported ++ env) (path ++ [.letRecBody])
            body schemes (some (captured.extendGroup g)) (some ⟨bodySource⟩) expected
          let completed ← finishBody (ids := ids) (rows := rows) (caller := caller)
            (Δ := Δ) (env := env)
            (e := .found g.originalHM (.letRec g.annotations g.rhss g.body))
            path g.originalHM result.bounds rfl
            (by
              have bodyTyping : ScopedBodyDerives BoundsTy.fvar BoundsTy.bvar ids rows Δ
                  (g.exports.map BodyBinding.exported ++ ordinaryBodyEnv captured.rhsEnv)
                  g.body.stripFound result.bounds := by
                simpa only [bodyEq, captured.bodyEnv] using result.typing
              simpa only [Expr.stripFound, captured.bodyEnv] using
                (ScopedBodyDerives.letRec g
                  (fun _ f lc scope fixed => allMembers g.members f lc scope fixed)
                  bodyTyping))
            (memberNodes g.members ++ result.nodes)
            (do
              let members ← g.members.runtimeReady
              let bodyReady ← result.runtimeReady
              have bodyTyping : ScopedBodyDerives BoundsTy.fvar BoundsTy.bvar ids rows Δ
                  (g.exports.map BodyBinding.exported ++ ordinaryBodyEnv captured.rhsEnv)
                  g.body.stripFound result.bounds := by
                simpa only [bodyEq, captured.bodyEnv] using result.typing
              have ready : BodyDerives.RuntimeReady bodyTyping := by
                simpa only [bodyEq, captured.bodyEnv] using bodyReady.down
              pure ⟨by
                simpa only [Expr.stripFound, captured.bodyEnv] using
                  (BodyDerives.RuntimeReady.letRec g
                    (fun _ f lc scope fixed => allMembers g.members f lc scope fixed)
                    (fun offset inside => (members.down offset inside).1)
                    (fun offset inside => (members.down offset inside).2)
                    captured.arguments ready)⟩)
          pure (by simpa only [sourceEq] using completed)
  | _ => throw "bounds: generalized body lacks an original found node"
termination_by (sizeOf e, 1)

private def walkBodySpineSourced (sourceOutput : Expr) (metadata : Scope.Metadata)
    (ids : List Nat) (rows : Bindings) (caller : List Nat)
    (Δ : List Constraint) (env : List BodyBinding) {e : Expr} (spine : RecursiveSpine.Syntax e)
    (schemes : BinderSchemeMap) (capture : Option (BodyCapture env))
    (source : BodySpineSource sourceOutput spine) :
    Except String (BodySpine sourceOutput ids rows caller Δ env spine) := do
  match source with
  | .head (path := path) (i := i) (hm := hm) _ => pure (.head path i hm)
  | .app (path := path) (hm := hm) (prior := prior) (arg := arg) priorSource argSource =>
      let previous ← walkBodySpineSourced sourceOutput metadata ids rows caller Δ env prior schemes capture priorSource
      let actual := match walkBodySource sourceOutput metadata ids rows caller Δ env
          (path ++ [.appArg]) arg schemes capture (some ⟨argSource⟩) none with
        | .ok result => some result
        | .error _ => none
      pure (.app path hm previous actual (some ⟨argSource⟩))
termination_by (sizeOf e, 0)

private def walkBodySpine (sourceOutput : Expr) (metadata : Scope.Metadata)
    (ids : List Nat) (rows : Bindings) (caller : List Nat)
    (Δ : List Constraint) (env : List BodyBinding) {e : Expr} (spine : RecursiveSpine.Syntax e)
    (schemes : BinderSchemeMap) (capture : Option (BodyCapture env)) :
    Except String (BodySpine sourceOutput ids rows caller Δ env spine) := do
  match spine with
  | .head path i hm => pure (.head path i hm)
  | .app path hm prior arg =>
      let previous ← walkBodySpine sourceOutput metadata ids rows caller Δ env prior schemes capture
      let actual := match walkBodySource sourceOutput metadata ids rows caller Δ env
          (path ++ [.appArg]) arg schemes capture none none with
        | .ok result => some result
        | .error _ => none
      pure (.app path hm previous actual none)
termination_by (sizeOf e, 0)

private def walkBodyBranches (sourceOutput : Expr) (metadata : Scope.Metadata)
    (ids : List Nat) (rows : Bindings) (caller : List Nat)
    (Δ : List Constraint) (env : List BodyBinding) (ctx : BodyBranchContext)
    (path : CorePath) (branches : List (MatchPattern × Expr)) (index : Nat)
    (schemes : BinderSchemeMap) (capture : Option (BodyCapture env))
    (sources : BodyBranchSources sourceOutput path index branches)
    (expected : Option BoundsTy) :
    Except String (BodyBranches ids rows caller Δ env ctx branches) := do
  match branches with
  | [] => pure ⟨(fun _ => .prim .int), (by intros; contradiction), (by intros; contradiction),
      none, (by intros; contradiction), [], some ⟨by intros; contradiction⟩⟩
  | br :: rest =>
      if hp : ctx.Pattern br.1 then
        let headSource := sources 0 br (by simp)
        let head ← walkBodySource sourceOutput metadata ids rows caller
          (Δ ++ ctx.refine br.1) (ctx.extend br.1 env)
          (path ++ [.matchBranch index]) br.2 schemes (extendBranchCapture? capture ctx br.1)
          (by simpa only [Nat.add_zero] using headSource) expected
        let tailSources : BodyBranchSources sourceOutput path (index + 1) rest := fun i arm atIndex =>
          have shifted : (br :: rest)[i + 1]? = some arm := by simpa using atIndex
          (sources (i + 1) arm shifted).map fun located => ⟨by
            have position : index + (i + 1) = index + 1 + i := by omega
            simpa only [position] using located.down⟩
        let tail ← walkBodyBranches sourceOutput metadata ids rows caller Δ env ctx path rest
          (index + 1) schemes capture tailSources expected
        match expected with
        | some β =>
            let hs ← Typed.subtype (Δ ++ ctx.refine br.1) head.bounds β
            match ht : tail.bounds with
            | none => pure (prependBodyBranches head hp tail β hs.down (by
                intro i arm ha
                have impossible := tail.inclusions i arm ha
                simp only [ht] at impossible))
            | some τ =>
                let ts ← Typed.subtype Δ τ β
                pure (prependBodyBranches head hp tail β hs.down (by
                  intro i arm ha
                  have sub : SemanticSub (Δ ++ ctx.refine arm.1) (tail.actuals i) τ :=
                    by simpa only [ht] using tail.inclusions i arm ha
                  exact sub.trans (ts.down.assuming (body_path_assuming _ _))))
        | none =>
            match ht : tail.bounds with
            | none => pure (prependBodyBranches head hp tail head.bounds (SemanticSub.refl _ _) (by
                intro i arm ha
                have impossible := tail.inclusions i arm ha
                simp only [ht] at impossible))
            | some τ =>
                let ⟨β, merged⟩ ← BranchMerge.combine .upper head.bounds τ
                let subs := merged.down.sound Δ
                pure (prependBodyBranches head hp tail β (subs.1.assuming (body_path_assuming _ _)) (by
                  intro i arm ha
                  have sub : SemanticSub (Δ ++ ctx.refine arm.1) (tail.actuals i) τ :=
                    by simpa only [ht] using tail.inclusions i arm ha
                  exact sub.trans (subs.2.assuming (body_path_assuming _ _))))
      else throw "bounds: generalized body match has an unsupported pattern or constructor arity"
termination_by (sizeOf branches, 0)
decreasing_by
  all_goals simp_wf
  all_goals first | omega | (cases br; simp_all; omega)
end

/-- Standalone body-fragment entry point. Source-linked program checking uses
    the internal traversal with the complete root artifact and lowering
    metadata; isolated callers have no enclosing source metadata. -/
def walkBody (ids : List Nat) (rows : Bindings) (caller : List Nat) (Δ : List Constraint)
    (env : List BodyBinding) (path : CorePath) (e : Expr) (schemes : BinderSchemeMap)
    (expected : Option BoundsTy := none) : Except String (BodyResult ids rows caller Δ env e) :=
  match path with
  | [] => walkBodySource e {} ids rows caller Δ env [] e schemes
      none (some ⟨by simp [Expr.atCorePath]⟩) expected
  | _ => walkBodySource e {} ids rows caller Δ env path e schemes none none expected

/-- Closed-group vertical slice. Only after all universal RHSs accept do their
    generalized exit bindings become available to actual source body checking. -/
def checkBody {output metadata path vectors premises bodyTypes}
    (g : HMDeclaredGroup.Checked output metadata path vectors [] premises bodyTypes [])
    (ids : List Nat) (rows : Bindings) (caller : List Nat) (Δ : List Constraint)
    (schemes : BinderSchemeMap) (expected : Option BoundsTy := none) :
    Except String (BodyResult ids rows caller Δ []
      (.found g.originalHM (.letRec g.annotations g.rhss g.body))) := do
  have bodySource : output.atCorePath (path ++ [.letRecBody]) = some g.body := by
    rw [Expr.atCorePath_append, g.source]
    simp [Expr.atCorePath]
  let body ← walkBodySource output metadata ids rows caller Δ (g.exports.map BodyBinding.exported)
    (path ++ [.letRecBody]) g.body schemes (some (checkedGroupBodyCapture g))
    (some ⟨bodySource⟩) expected
  finishBody path g.originalHM body.bounds rfl
    (by
      have bodyTyping : BodyDerives ids rows Δ
          (g.exports.map BodyBinding.exported ++ ordinaryBodyEnv [])
          g.body.stripFound body.bounds := by
        simpa only [ordinaryBodyEnv, List.map_nil, List.append_nil] using body.typing
      simpa only [Expr.stripFound] using
        BodyDerives.letRec g
          (fun _ f lc scope fixed => allMembers g.members f lc scope fixed) bodyTyping)
    (memberNodes g.members ++ body.nodes)
    (do
      let members ← g.members.runtimeReady
      let ready ← body.runtimeReady
      pure ⟨by
        have bodyTyping : BodyDerives ids rows Δ
            (g.exports.map BodyBinding.exported ++ ordinaryBodyEnv [])
            g.body.stripFound body.bounds := by
          simpa only [ordinaryBodyEnv, List.map_nil, List.append_nil] using body.typing
        have bodyReady : BodyDerives.RuntimeReady bodyTyping := by
          simpa only [ordinaryBodyEnv, List.map_nil, List.append_nil] using ready.down
        simpa only [Expr.stripFound] using
          (BodyDerives.RuntimeReady.letRec g
            (fun _ f lc scope fixed => allMembers g.members f lc scope fixed)
            (fun offset inside => (members.down offset inside).1)
            (fun offset inside => (members.down offset inside).2)
            (by simp [RecursiveArgumentsSupported]) bodyReady)⟩)

/-- A source-linked closed ROOT recursive program, not a general program-prefix
    or nested-group adapter. The body certificate is indexed by the exact input
    artifact, while retaining the actual all-member coordinate assembly. -/
structure ProgramResult (output : Expr) (metadata : Scope.Metadata) where
  assembled : HMDeclaredCoordinates.Result output metadata [] [] [] [] []
  body : BodyResult [] [] [] [] [] output

/-- No supplied opaque vectors, reconstructed RHSs or legacy fallback. Source
    annotations and real mono-local machine facts keep their distinct roles.
    `expected` is synthesis guidance, not an asserted result inclusion. -/
def checkClosedProgram (output : Expr) (metadata : Scope.Metadata)
    (schemes : BinderSchemeMap := []) (expected : Option BoundsTy := none) :
    Except String (ProgramResult output metadata) := do
  let assembled ← HMDeclaredCoordinates.check output metadata [] (schemes := schemes)
  let body ← checkBody assembled.checked [] [] [] [] schemes expected
  have sourceEq : output = .found assembled.checked.originalHM
      (.letRec assembled.checked.annotations assembled.checked.rhss assembled.checked.body) := by
    simpa only [Expr.atCorePath, Option.some.injEq] using assembled.checked.source
  pure ⟨assembled, by simpa only [sourceEq] using body⟩

/-- Canonical source-linked program entry point.  Unlike the historical
    root-group slice, this begins with the empty represented environment and
    therefore covers ordinary prefixes as well as a recursive group at any
    supported source position.  Successful results carry the same derivation,
    exact-node report and optional runtime theorem as `checkClosedProgram`. -/
def checkProgram (output : Expr) (metadata : Scope.Metadata)
    (schemes : BinderSchemeMap := []) (expected : Option BoundsTy := none) :
    Except String (BodyResult [] [] [] [] [] output) :=
  walkBodySource output metadata [] [] [] [] [] [] output schemes
    (some emptyBodyCapture) (some ⟨by simp [Expr.atCorePath]⟩) expected

/-- Extract the runtime theorem carried by a supported closed report. This is
    indexed by its EXACT input artifact and inferred bounds, not by a rebuilt
    expression. A missing witness makes no runtime soundness claim. Constraint
    validity is still supplied by the existing static certificate machinery. -/
def BodyResult.runtimeSafety? {ids rows caller Δ output}
    (result : BodyResult ids rows caller Δ [] output) :
    Option (PLift (∀ (bound free : Runtime.TypeEnv) (σ : Assign),
      Runtime.TypeEnv.Downward bound → Runtime.TypeEnv.Downward free →
      (∀ p ∈ Δ, p.Holds σ) → Runtime.Safe bound free σ result.bounds output.stripFound)) := do
  let ready ← result.runtimeReady
  pure ⟨by
    intro bound free σ hb hf premises
    exact ready.down.safeClosed bound free σ hb hf premises⟩

#print axioms BodyResult.runtimeSafety?

#print axioms fromCertified
#print axioms demand_instance
#print axioms Result.assuming
#print axioms Result.signature
#print axioms atSignedNode
#print axioms allMembers
#print axioms BodyBranchContext.Covers.assuming
#print axioms BodyDerives.assuming
#print axioms body_match_typing
#print axioms useBodySpine
#print axioms walkBody
#print axioms checkBody
#print axioms checkClosedProgram
#print axioms checkProgram

end FHM.Bounds.RecursiveHMUniform
