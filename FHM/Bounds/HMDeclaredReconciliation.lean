import FHM.Bounds.HMReconciliation
import FHM.Bounds.RecursiveHMWalk
import FHM.Bounds.RecursiveHMSigned

/-! Source-site reconciliation for annotated bindings. No inferred binder fact
is synthesized or required. Flexible solved identities are only structural
proposals: opaque opening, captured-identity protection, actual RHS checking and
independent inclusion remain separate. This initial closed-HM-scope interface
rejects enclosing lexical slots and does not introduce/export recursive groups. -/

namespace FHM.Bounds.HMDeclaredReconciliation

open SchemeSpecialization ScopedScheme

private theorem mem_eraseDups {a : Nat} {l : List Nat} (h : a ∈ l.eraseDups) : a ∈ l := by
  have go : ∀ n, ∀ (l : List Nat), l.length = n → ∀ a, a ∈ l.eraseDups → a ∈ l := by
    intro n
    refine Nat.strongRecOn n (motive := fun n =>
      ∀ (l : List Nat), l.length = n → ∀ a, a ∈ l.eraseDups → a ∈ l) fun n ih => ?_
    intro l hn a hm
    match l with
    | [] => cases hm
    | b :: rest =>
        simp only [List.length_cons] at hn
        simp only [List.eraseDups_cons, List.mem_cons] at hm
        rcases hm with rfl | ht
        · simp
        · have smaller : (rest.filter (fun x => !x == b)).length < n := by
            rw [← hn]
            exact Nat.lt_add_one_of_le (List.length_filter_le _ rest)
          exact List.mem_cons_of_mem b (List.mem_of_mem_filter (ih _ smaller _ rfl _ ht))
  exact go l.length l rfl a h

/-- The annotation comes from the exact original declaration, not a caller's
    substitute signature or a fabricated inference-produced binder fact. -/
inductive SourceAt (output : Expr) : CoreBinderSite → PolyTy → CorePath → Prop where
  | letIn {path hm annotation rhs body} :
      output.atCorePath path = some (.found hm (.letIn (some annotation) rhs body)) →
      SourceAt output (.letIn path) annotation (path ++ [.letRhs])
  | letRec {path member hm annotations rhss body annotation} :
      output.atCorePath path = some (.found hm (.letRec annotations rhss body)) →
      annotations.length = rhss.length →
      annotations[member]? = some (some annotation) →
      SourceAt output (.letRec path member) annotation (path ++ [.letRecRhs member])

theorem SourceAt.rhsPath {output site annotation path} (h : SourceAt output site annotation path) :
    HMReconciliation.rhsPath site = some path := by
  cases h <;> rfl

structure Declaration (output : Expr) (site : CoreBinderSite) where
  annotation : PolyTy
  path : CorePath
  source : SourceAt output site annotation path
  node : HMFoundView.AtNode output path

def locate (output : Expr) (site : CoreBinderSite) : Except String (Declaration output site) := do
  match site with
  | .letIn path =>
      match hp : output.atCorePath path with
      | some (.found _ (.letIn (some annotation) _ _)) =>
          let node ← HMFoundView.locate output (path ++ [.letRhs])
          pure ⟨annotation, _, .letIn hp, node⟩
      | _ => throw "bounds: requested source site is not an annotated found let declaration"
  | .letRec path member =>
      match hp : output.atCorePath path with
      | some (.found _ (.letRec annotations rhss _)) =>
          if ha : annotations.length = rhss.length then
            match hs : annotations[member]? with
            | some (some annotation) =>
                let node ← HMFoundView.locate output (path ++ [.letRecRhs member])
                pure ⟨annotation, _, .letRec hp ha hs, node⟩
            | _ => throw "bounds: requested recursive member has no source annotation"
          else throw "bounds: source recursive annotation/RHS arity mismatch"
      | _ => throw "bounds: requested source site is not an annotated found recursive declaration"
  | _ => throw "bounds: declared HM reconciliation requires a binding RHS site"

/-- Ordinary annotated let RHSs close at their own forall slots. Recursive
    inference instead preserves the solved monomorphic free identities. -/
def slotsFor (site : CoreBinderSite) (ids : List Nat) : Nat → BoundsTy :=
  match site with
  | .letIn _ => ScopedHMInterpretation.vector (ids.map BoundsTy.fvar)
  | _ => BoundsTy.bvar

def slotLimit (site : CoreBinderSite) (annotation : PolyTy) : Nat :=
  match site with | .letIn _ => annotation.paramCount | _ => 0

/-- Explicit surrounding captures plus rigid free identities carried in source
    annotations are guarded. Found payload identities are NOT source rigids. -/
def guardedTypes {output site} (d : Declaration output site) (captures : List Ty) : List Ty :=
  d.annotation.body :: captures ++ d.node.inner.stripFound.tyFreeVars.map Ty.fvar

structure Checked {output site} (d : Declaration output site)
    (quantified captures : List Nat) (premises : List Constraint) (typeCaptures : List Ty) where
  interface : HMCountScheme.Annotated d.annotation quantified captures premises
  original : BoundsTy
  originalShape : Synth.BoundsTy.toTy original = d.node.original.eraseBounds
  originalSlots : d.node.original.eraseBounds.bvarsBelow (slotLimit site d.annotation) = true
  flexible : List Nat
  distinct : flexible.Nodup
  fromOriginal : ∀ i ∈ flexible, i ∈ d.node.original.freeVars
  guarded : ∀ i ∈ flexible, ∀ t ∈ guardedTypes d typeCaptures, i ∉ t.freeVars
  arguments : List BoundsTy
  argumentArity : arguments.length = flexible.length
  argumentsLC : ∀ a ∈ arguments, (Synth.BoundsTy.toTy a).IsLC
  argumentsScope : arguments.all (boundsScopedBool (quantified ++ captures)) = true
  signatureIds : List Nat
  newIdentities : ∀ i ∈ signatureIds, i ∉ flexible
  opening : HMCountScheme.Opening interface.scheme
    (ScopedHMInterpretation.AtNode.view d.node
      (argument flexible (SchemeUse.vector arguments)) (slotsFor site signatureIds))
    (d.node.original :: guardedTypes d typeCaptures)

def Checked.interpretation {output site d quantified captures premises typeCaptures}
    (c : @Checked output site d quantified captures premises typeCaptures) : Nat → BoundsTy :=
  argument c.flexible (SchemeUse.vector c.arguments)

theorem Checked.capturesFixed {output site d quantified captures premises typeCaptures}
    (c : @Checked output site d quantified captures premises typeCaptures)
    {t : Ty} (captured : t ∈ guardedTypes d typeCaptures) {i : Nat} (used : i ∈ t.freeVars) :
    c.interpretation i = .fvar i := by
  have absent : i ∉ c.flexible := fun hi => c.guarded i hi t captured used
  simp [Checked.interpretation, argument, List.idxOf?_eq_none_iff.mpr absent]

theorem Checked.interpretationLC {output site d quantified captures premises typeCaptures}
    (c : @Checked output site d quantified captures premises typeCaptures) :
    ∀ i, (Synth.BoundsTy.toTy (c.interpretation i)).IsLC := by
  intro i
  cases h : c.flexible.idxOf? i with
  | none => simp only [Checked.interpretation, argument, h, Synth.BoundsTy.toTy]; exact .fvar
  | some slot =>
      simp only [Checked.interpretation, argument, h]
      cases ha : c.arguments[slot]? with
      | none => simp only [SchemeUse.vector, ha, Option.getD_none, Synth.BoundsTy.toTy]; exact .prim
      | some a => simpa only [SchemeUse.vector, ha, Option.getD_some] using
          c.argumentsLC a (List.mem_of_getElem? ha)

/-- Propose specialization in the correct direction: original solved RHS
    identities may stand for complete types in the narrower source ceiling.
    This is METADATA evidence, never a machine-generalization certificate. -/
def check {output site} (d : Declaration output site) (quantified captures : List Nat)
    (signatureIds : List Nat) (typeCaptures : List Ty := []) (premises : List Constraint := []) :
    Except String (Checked d quantified captures premises typeCaptures) := do
  let interface ← HMCountScheme.decodeAnnotated d.annotation quantified captures premises
  let original ← Typed.shapeTop d.node.original.eraseBounds
  let originalShape ← match BinderBridge.equalTy (Synth.BoundsTy.toTy original) d.node.original.eraseBounds with
    | some h => pure h | none => throw "bounds: original declared RHS skeleton disagrees with found payload"
  if hslots : d.node.original.eraseBounds.bvarsBelow (slotLimit site d.annotation) = true then
    let guarded := guardedTypes d typeCaptures
    let flexible := (d.node.original.freeVars.filter fun i =>
      !(guarded.any fun t => t.freeVars.contains i)).eraseDups
    if hd : flexible.Nodup then
      if hf : signatureIds.all (fun i => !flexible.contains i) = true then
        let target := HMCountScheme.opened interface.scheme (signatureIds.map BoundsTy.fvar)
        -- Check unused slot arity/freshness and source captures BEFORE proposals.
        let _ ← HMCountScheme.openFixed interface.scheme (Synth.BoundsTy.toTy target) signatureIds
          (d.node.original :: guarded)
        let pattern := BinderBridge.close flexible
          (ScopedHMInterpretation.read BoundsTy.fvar (slotsFor site signatureIds) original)
        let arguments ← StructuralApplication.propose pattern target flexible.length
        if ha : arguments.length = flexible.length then
          if hlc : arguments.all (fun a => (Synth.BoundsTy.toTy a).bvarsBelow 0) = true then
            if hs : arguments.all (boundsScopedBool (quantified ++ captures)) = true then
              let viewed := ScopedHMInterpretation.AtNode.view d.node
                (argument flexible (SchemeUse.vector arguments)) (slotsFor site signatureIds)
              let opening ← HMCountScheme.openFixed interface.scheme viewed signatureIds
                (d.node.original :: guarded)
              have fromOriginal : ∀ i ∈ flexible, i ∈ d.node.original.freeVars := by
                intro i hi
                have hi : i ∈ d.node.original.freeVars ∧ ∀ t ∈ guarded, i ∉ t.freeVars := by
                  have filtered := List.mem_filter.mp (mem_eraseDups
                    (l := d.node.original.freeVars.filter (fun i => !guarded.any fun t => t.freeVars.contains i)) hi)
                  simpa [List.contains_iff_mem] using filtered
                exact hi.1
              have guardedIds : ∀ i ∈ flexible, ∀ t ∈ guarded, i ∉ t.freeVars := by
                intro i hi t ht used
                have hi : i ∈ d.node.original.freeVars ∧ ∀ t ∈ guarded, i ∉ t.freeVars := by
                  have filtered := List.mem_filter.mp (mem_eraseDups
                    (l := d.node.original.freeVars.filter (fun i => !guarded.any fun t => t.freeVars.contains i)) hi)
                  simpa [List.contains_iff_mem] using filtered
                exact hi.2 t ht used
              have newIds : ∀ i ∈ signatureIds, i ∉ flexible := by
                intro i hi
                simpa [List.contains_iff_mem] using List.all_eq_true.mp hf i hi
              pure ⟨interface, original, originalShape.down, hslots, flexible, hd, fromOriginal, guardedIds,
                arguments, ha, (fun a hm => (Ty.bvarsBelow_iff _).mp (List.all_eq_true.mp hlc a hm)),
                hs, signatureIds, newIds, opening⟩
            else throw "bounds: declared RHS replacement counts escape source signature scope"
          else throw "bounds: declared RHS replacements contain enclosing HM slots"
        else throw "bounds: declared RHS replacement vector has wrong arity"
      else throw "bounds: source signature identities must be fresh from solved RHS identities"
    else throw "bounds: duplicate flexible solved RHS identities"
  else throw "bounds: enclosing lexical HM slots unsupported in closed declared-interface slice"
#print axioms SourceAt.rhsPath
#print axioms locate
#print axioms Checked.capturesFixed
#print axioms Checked.interpretationLC
#print axioms check

end FHM.Bounds.HMDeclaredReconciliation
