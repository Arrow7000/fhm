import FHM.Bounds.HMFoundView
import FHM.Bounds.HMCountScheme
import FHM.Bounds.StructuralApplication

/-! # Checked reconciliation of machine binder identities with source signatures

The original found tree is never rewritten or reinferred. Structural matching
only proposes full bounds replacements for the machine-generalized identities;
acceptance checks the complete interpreted node against a fresh opaque source
signature opening. This is metadata evidence, NOT an RHS typing/origin proof.
In particular, the source demand guides the checker but is not a checked result.
-/

namespace FHM.Bounds.HMReconciliation

open SchemeSpecialization ScopedScheme

/-- Only actual binding RHS sites admit signature reconciliation. -/
def rhsPath : CoreBinderSite → Option CorePath
  | .letIn path => some (path ++ [.letRhs])
  | .letRec path index => some (path ++ [.letRecRhs index])
  | _ => none

structure Checked {output path} (node : HMFoundView.AtNode output path)
    (schemes : BinderSchemeMap) (site : CoreBinderSite) (s : HMCountScheme.Scheme)
    (captures : List Ty) where
  sitePath : rhsPath site = some path
  original : BoundsTy
  originalShape : Synth.BoundsTy.toTy original = node.original.eraseBounds
  machine : BinderBridge.AtSite schemes site original captures
  arguments : List BoundsTy
  argumentArity : arguments.length = machine.scheme.paramCount
  argumentsLC : ∀ a ∈ arguments, (Synth.BoundsTy.toTy a).IsLC
  argumentsScope : arguments.all (boundsScopedBool (s.counts.quantified ++ s.counts.captures)) = true
  signatureIds : List Nat
  /-- Signature slots are newly opaque, including slots unused by the source. -/
  newIdentities : ∀ i ∈ signatureIds, i ∉ machine.abstraction.ids
  opening : HMCountScheme.Opening s
    (node.view (argument machine.abstraction.ids (SchemeUse.vector arguments)))
    (node.original :: captures)
  openingIds : opening.ids = signatureIds

def Checked.interpretation {output path node schemes site s captures}
    (checked : @Checked output path node schemes site s captures) : Nat → BoundsTy :=
  argument checked.machine.abstraction.ids (SchemeUse.vector checked.arguments)

theorem Checked.capturesFixed {output path node schemes site s captures}
    (checked : @Checked output path node schemes site s captures) {t : Ty}
    (captured : t ∈ captures) {i : Nat} (used : i ∈ t.freeVars) :
    checked.interpretation i = .fvar i := by
  have absent : i ∉ checked.machine.abstraction.ids := fun hi =>
    checked.machine.abstraction.fresh i hi t captured used
  simp [Checked.interpretation, argument, List.idxOf?_eq_none_iff.mpr absent]

theorem Checked.signatureIdentityFixed {output path node schemes site s captures}
    (checked : @Checked output path node schemes site s captures) {i : Nat}
    (slot : i ∈ checked.signatureIds) : checked.interpretation i = .fvar i := by
  simp [Checked.interpretation, argument,
    List.idxOf?_eq_none_iff.mpr (checked.newIdentities i slot)]

theorem Checked.interpretationLC {output path node schemes site s captures}
    (checked : @Checked output path node schemes site s captures) :
    ∀ i, (Synth.BoundsTy.toTy (checked.interpretation i)).IsLC := by
  intro i
  cases h : checked.machine.abstraction.ids.idxOf? i with
  | none => simp only [Checked.interpretation, argument, h, Synth.BoundsTy.toTy]; exact .fvar
  | some slot =>
      simp only [Checked.interpretation, argument, h]
      cases ha : checked.arguments[slot]? with
      | none => simp only [SchemeUse.vector, ha, Option.getD_none, Synth.BoundsTy.toTy]; exact .prim
      | some a =>
          simpa only [SchemeUse.vector, ha, Option.getD_some] using
            checked.argumentsLC a (List.mem_of_getElem? ha)

theorem Checked.interpretationScope {output path node schemes site s captures}
    (checked : @Checked output path node schemes site s captures) :
    ∀ i, BoundsScoped (s.counts.quantified ++ s.counts.captures) (checked.interpretation i) := by
  intro i
  cases h : checked.machine.abstraction.ids.idxOf? i with
  | none => simp [Checked.interpretation, argument, h, BoundsScoped]
  | some slot =>
      simpa only [Checked.interpretation, argument, h] using
        SchemeUse.vector_scope checked.argumentsScope slot

/-- The interpreted payload is an exact relational instance of the ORIGINAL
    machine scheme, using the chosen full bounds vector, not a second inference. -/
theorem Checked.machineInstance {output path node schemes site s captures}
    (checked : @Checked output path node schemes site s captures) :
    checked.machine.scheme.eraseBounds.InstantiatesTo
      (checked.arguments.map Synth.BoundsTy.toTy) (node.view checked.interpretation) := by
  have arity := checked.argumentArity
  have hi := InstantiatesBy.openWith checked.machine.abstraction.hmOpening.wf
    (show checked.machine.scheme.paramCount ≤ (checked.arguments.map Synth.BoundsTy.toTy).length by
      simp only [List.length_map]; omega)
  have he := TypeSubstitution.hm_instance hi
    (fun i => Synth.BoundsTy.toTy (SchemeUse.vector checked.arguments i))
    (fun _ _ h => SchemeUse.vector_shape rfl h)
  simp only [PolyTy.eraseBounds] at hi he
  have coherent := node.coherent checked.interpretation checked.originalShape
  change Synth.BoundsTy.toTy (mapFree (argument checked.machine.abstraction.ids
    (SchemeUse.vector checked.arguments)) checked.original) = node.view checked.interpretation at coherent
  rw [← SchemeSpecialization.close_open checked.machine.abstraction.ids
    (SchemeUse.vector checked.arguments) checked.machine.abstraction.originalLC,
    TypeSubstitution.shape, checked.machine.abstraction.shape, he] at coherent
  change InstantiatesBy (checked.arguments.map Synth.BoundsTy.toTy)
    checked.machine.scheme.body.eraseBounds (node.view checked.interpretation)
  rw [← coherent]
  exact hi

/-- Original binder facts must be unique and genuinely generalized. Full bounds
    proposals come from the declared opaque demand, but carry no RHS provenance.
    The consuming walker must separately synthesize and prove the actual RHS. -/
def check {output path} (node : HMFoundView.AtNode output path)
    (schemes : BinderSchemeMap) (site : CoreBinderSite) (s : HMCountScheme.Scheme)
    (original : BoundsTy) (signatureIds : List Nat) (captures : List Ty) :
    Except String (Checked node schemes site s captures) := do
  let sitePath ←
    if h : rhsPath site = some path then pure (⟨h⟩ : PLift (rhsPath site = some path))
    else throw "bounds: machine binder site does not designate this exact RHS Core path"
  let originalShape ← match BinderBridge.equalTy (Synth.BoundsTy.toTy original) node.original.eraseBounds with
    | some h => pure h
    | none => throw "bounds: reconciliation skeleton disagrees with original found node"
  let machine ← BinderBridge.atSite schemes site original captures
  if hn : signatureIds.all (fun i => !machine.abstraction.ids.contains i) = true then
    let target := HMCountScheme.opened s (signatureIds.map BoundsTy.fvar)
    -- This first check validates arity, distinctness, unused-slot freshness,
    -- source captures and source slot closure before structural proposals.
    let _ ← HMCountScheme.openFixed s (Synth.BoundsTy.toTy target) signatureIds (node.original :: captures)
    let arguments ← StructuralApplication.propose
      (BinderBridge.close machine.abstraction.ids original) target machine.scheme.paramCount
    if ha : arguments.length = machine.scheme.paramCount then
      if hlc : arguments.all (fun a => (Synth.BoundsTy.toTy a).bvarsBelow 0) = true then
        if hs : arguments.all (boundsScopedBool (s.counts.quantified ++ s.counts.captures)) = true then
          let viewed := node.view (argument machine.abstraction.ids (SchemeUse.vector arguments))
          let opening ← HMCountScheme.openFixed s viewed signatureIds (node.original :: captures)
          if hi : opening.ids = signatureIds then
            pure ⟨sitePath.down, original, originalShape.down, machine, arguments, ha, by
              intro a h
              exact (Ty.bvarsBelow_iff _).mp (List.all_eq_true.mp hlc a h),
              hs, signatureIds, by
                intro i hi
                simpa [List.contains_iff_mem] using List.all_eq_true.mp hn i hi,
              opening, hi⟩
          else throw "bounds: reconciliation opening changed source HM identities"
        else throw "bounds: reconciliation argument counts escape source signature scope"
      else throw "bounds: reconciliation arguments contain enclosing HM bound slots"
    else throw "bounds: reconciliation machine argument vector has wrong arity"
  else throw "bounds: source signature HM identities must be fresh from machine binder identities"

/-- Acceptance retains real source-node typing and independently checks actual
    bounds against the opaque signature demand. This is the symbolic RHS seam,
    not a universal count certificate or whole-group export. -/
structure RHSChecked {output path node schemes site s captures}
    (checked : @Checked output path node schemes site s captures)
    (env : List RecursiveHMJudgement.Binding) where
  typed : HMFoundView.TypedChecked node checked.interpretation
    (s.counts.quantified ++ s.counts.captures) [] s.counts.premises
    (env.map (RecursiveHMJudgement.mapBinding checked.interpretation checked.interpretationLC))
    (s.counts.quantified ++ s.counts.captures)
  inclusion : SemanticSub s.counts.premises typed.actual checked.opening.bounds

def checkRHS {output path node schemes site s captures}
    (checked : @Checked output path node schemes site s captures)
    {env : List RecursiveHMJudgement.Binding} (actual : BoundsTy)
    (typing : RecursiveHMJudgement.Derives BoundsTy.fvar
      (s.counts.quantified ++ s.counts.captures) [] s.counts.premises env node.inner.stripFound actual)
    (represented : ∀ c, .recursive c ∈ env → c.template.hm.body ∈ captures) :
    Except String (RHSChecked checked env) := do
  have fresh : RecursiveHMJudgement.CapturesFixed checked.interpretation env := by
    intro c hc i hi
    exact checked.capturesFixed (represented c hc) hi
  have transported := RecursiveHMJudgement.transportTypes checked.interpretation
    checked.interpretationLC (s.counts.quantified ++ s.counts.captures)
    checked.interpretationScope typing fresh
  have derivation : RecursiveHMJudgement.Derives checked.interpretation
      (s.counts.quantified ++ s.counts.captures) [] s.counts.premises
      (env.map (RecursiveHMJudgement.mapBinding checked.interpretation checked.interpretationLC))
      node.inner.stripFound (mapFree checked.interpretation actual) := by
    simpa only [mapFree] using transported
  let typed ← HMFoundView.checkTyped node checked.interpretation
    (s.counts.quantified ++ s.counts.captures) [] s.counts.premises
    (env.map (RecursiveHMJudgement.mapBinding checked.interpretation checked.interpretationLC))
    (s.counts.quantified ++ s.counts.captures) (mapFree checked.interpretation actual) derivation
  let inclusion ← Typed.subtype s.counts.premises typed.actual checked.opening.bounds
  pure ⟨typed, inclusion.down⟩

#print axioms Checked.machineInstance
#print axioms Checked.capturesFixed
#print axioms Checked.signatureIdentityFixed
#print axioms Checked.interpretationLC
#print axioms Checked.interpretationScope
#print axioms check
#print axioms checkRHS

end FHM.Bounds.HMReconciliation
