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

private def annotationsTyBvarsBelow (n : Nat) (anns : List (Option PolyTy)) : Bool :=
  anns.all fun ann => match ann with
    | none => true
    | some σ => σ.body.bvarsBelow (n + σ.paramCount)

mutual
private def rhsTyBvarsBelow (n : Nat) (e : Expr) : Bool := match e with
  | .primLit _ | .primBinOp _ | .var _ | .ctor _ => true
  | .lambda ann body =>
      (match ann with | none => true | some τ => τ.bvarsBelow n) && rhsTyBvarsBelow n body
  | .app f arg => rhsTyBvarsBelow n f && rhsTyBvarsBelow n arg
  | .letIn ann rhs body =>
      match ann with
      | none => rhsTyBvarsBelow n rhs && rhsTyBvarsBelow n body
      | some σ => σ.body.bvarsBelow (n + σ.paramCount) &&
          rhsTyBvarsBelow (n + σ.paramCount) rhs && rhsTyBvarsBelow n body
  | .match_ scrut branches => rhsTyBvarsBelow n scrut && branchesTyBvarsBelow n branches
  | .found τ inner => τ.bvarsBelow n && rhsTyBvarsBelow n inner
  | .letRec anns rhss body => annotationsTyBvarsBelow n anns &&
      recursiveTyBvarsBelow n anns rhss && rhsTyBvarsBelow n body
termination_by sizeOf e

private def branchesTyBvarsBelow (n : Nat) (branches : List (MatchPattern × Expr)) : Bool := match branches with
  | [] => true
  | (_, body) :: rest => rhsTyBvarsBelow n body && branchesTyBvarsBelow n rest
termination_by sizeOf branches

private def recursiveTyBvarsBelow (n : Nat) (anns : List (Option PolyTy)) (rhss : List Expr) : Bool := match anns, rhss with
  | _, [] => true
  | [], rhs :: rest => rhsTyBvarsBelow n rhs && recursiveTyBvarsBelow n [] rest
  | ann :: anns, rhs :: rest =>
      rhsTyBvarsBelow (n + RecAnn.params ann) rhs && recursiveTyBvarsBelow n anns rest
termination_by sizeOf rhss
end

private theorem annotationsTyBvarsBelow_sound {n anns}
    (h : annotationsTyBvarsBelow n anns = true) :
    ∀ σ, some σ ∈ anns → ContainsBvarsUpTo (n + σ.paramCount) σ.body := by
  intro σ member
  have checked := List.all_eq_true.mp h (some σ) member
  simpa [annotationsTyBvarsBelow, Ty.bvarsBelow_iff] using checked

private theorem branchesTyBvarsBelow_at {branches n pat body}
    (checked : branchesTyBvarsBelow n branches = true) (member : (pat, body) ∈ branches) :
    rhsTyBvarsBelow n body = true := by
  cases branches with
  | nil => cases member
  | cons branch rest =>
      rcases branch with ⟨headPat, headBody⟩
      simp only [branchesTyBvarsBelow, Bool.and_eq_true] at checked
      rcases List.mem_cons.mp member with equality | tail
      · cases equality
        exact checked.1
      · exact branchesTyBvarsBelow_at checked.2 tail

private theorem rhsTyBvarsBelow_sound :
    ∀ {e n}, rhsTyBvarsBelow n e = true → e.TyBvarBounded n := by
  intro e
  induction e using Expr.rec_strong with
  | primLit | primBinOp | var | ctor => intro n _; trivial
  | lambda ann body ih =>
      intro n checked
      cases ann with
      | none =>
          simp only [rhsTyBvarsBelow, Bool.and_eq_true] at checked
          exact ⟨(by intro τ source; cases source), ih checked.2⟩
      | some annotation =>
          simp only [rhsTyBvarsBelow, Bool.and_eq_true] at checked
          exact ⟨(by intro τ source; cases source; exact (Ty.bvarsBelow_iff _).mp checked.1),
            ih checked.2⟩
  | app f arg ihf iha =>
      intro n checked
      simp only [rhsTyBvarsBelow, Bool.and_eq_true] at checked
      exact ⟨ihf checked.1, iha checked.2⟩
  | letIn ann rhs body ihr ihb =>
      intro n checked
      cases ann with
      | none =>
          simp only [rhsTyBvarsBelow, Bool.and_eq_true] at checked
          exact ⟨ihr checked.1, ihb checked.2⟩
      | some σ =>
          simp only [rhsTyBvarsBelow, Bool.and_eq_true] at checked
          exact ⟨(Ty.bvarsBelow_iff _).mp checked.1.1, ihr checked.1.2, ihb checked.2⟩
  | match_ scrut branches ihs ihbs =>
      intro n checked
      simp only [rhsTyBvarsBelow, Bool.and_eq_true] at checked
      refine ⟨ihs checked.1, Expr.TyBvarBounded.BranchList_iff.mpr ?_⟩
      intro pat body member
      exact ihbs pat body member (branchesTyBvarsBelow_at checked.2 member)
  | found τ inner ih =>
      intro n checked
      simp only [rhsTyBvarsBelow, Bool.and_eq_true] at checked
      exact ⟨(Ty.bvarsBelow_iff _).mp checked.1, ih checked.2⟩
  | letRec anns rhss body ihs ihb =>
      intro n checked
      simp only [rhsTyBvarsBelow, Bool.and_eq_true] at checked
      refine ⟨annotationsTyBvarsBelow_sound checked.1.1, ?_, ihb checked.2⟩
      have recursive := checked.1.2
      have go : ∀ (anns : List (Option PolyTy)) (rhss : List Expr),
          (∀ e ∈ rhss, ∀ {n}, rhsTyBvarsBelow n e = true → e.TyBvarBounded n) →
          recursiveTyBvarsBelow n anns rhss = true →
          Expr.TyBvarBounded.RecGroup n anns rhss := by
        intro anns rhss
        induction rhss generalizing anns with
        | nil => intro _ _; trivial
        | cons rhs rest ihr =>
            intro derives checked
            cases anns with
            | nil =>
                simp only [recursiveTyBvarsBelow, Bool.and_eq_true] at checked
                exact ⟨derives rhs (by simp) checked.1,
                  ihr [] (fun e he => derives e (List.mem_cons_of_mem _ he)) checked.2⟩
            | cons ann anns =>
                simp only [recursiveTyBvarsBelow, Bool.and_eq_true] at checked
                exact ⟨derives rhs (by simp) checked.1,
                  ihr anns (fun e he => derives e (List.mem_cons_of_mem _ he)) checked.2⟩
      exact go anns rhss ihs recursive

private def checkRhsTyBvars (n : Nat) (e : Expr) : Except String (PLift (e.TyBvarBounded n)) :=
  if h : rhsTyBvarsBelow n e = true then .ok ⟨rhsTyBvarsBelow_sound h⟩
  else .error "bounds: source RHS annotation contains an out-of-scope HM slot"

theorem mem_eraseDups {a : Nat} {l : List Nat} (h : a ∈ l.eraseDups) : a ∈ l := by
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
  rhsSlots : d.node.inner.stripFound.TyBvarBounded (slotLimit site d.annotation)
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
  openingIds : opening.ids = signatureIds

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

/-- Flexible found identities may be solved, but identities named in carried
    RHS annotations retain the source reader's original meaning. -/
theorem Checked.sourceIdentity {output site d quantified captures premises typeCaptures}
    (c : @Checked output site d quantified captures premises typeCaptures)
    {i} (named : i ∈ d.node.inner.stripFound.tyFreeVars) :
    c.interpretation i = .fvar i := by
  have guarded : Ty.fvar i ∈ guardedTypes d typeCaptures :=
    List.mem_cons_of_mem _ (List.mem_append_right _ (List.mem_map.mpr ⟨i, named, rfl⟩))
  exact c.capturesFixed guarded (by simp [Ty.freeVars])

theorem Checked.signatureIdentityFixed {output site d quantified captures premises typeCaptures}
    (c : @Checked output site d quantified captures premises typeCaptures)
    {i : Nat} (slot : i ∈ c.signatureIds) : c.interpretation i = .fvar i := by
  simp [Checked.interpretation, argument, List.idxOf?_eq_none_iff.mpr (c.newIdentities i slot)]

theorem Checked.interpretationScope {output site d quantified captures premises typeCaptures}
    (c : @Checked output site d quantified captures premises typeCaptures) :
    ∀ i, BoundsScoped (quantified ++ captures) (c.interpretation i) := by
  intro i
  cases h : c.flexible.idxOf? i with
  | none => simp [Checked.interpretation, argument, h, BoundsScoped]
  | some slot => simpa only [Checked.interpretation, argument, h] using
      SchemeUse.vector_scope c.argumentsScope slot

/-- Fixed recursive arguments retain every exact source coordinate, including
    vacuous forall slots. This equality is needed for common-group assembly. -/
theorem Checked.fixedTypes {output site d quantified captures premises typeCaptures}
    (c : @Checked output site d quantified captures premises typeCaptures) :
    (RecursiveHMContract.fromOpaque c.opening).types = c.signatureIds.map BoundsTy.fvar := by
  change c.opening.ids.map BoundsTy.fvar = c.signatureIds.map BoundsTy.fvar
  rw [c.openingIds]

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
    let rhsSlots ← checkRhsTyBvars (slotLimit site d.annotation) d.node.inner.stripFound
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
              if hi : opening.ids = signatureIds then
                pure ⟨interface, original, originalShape.down, hslots, rhsSlots.down,
                  flexible, hd, fromOriginal, guardedIds,
                  arguments, ha, (fun a hm => (Ty.bvarsBelow_iff _).mp (List.all_eq_true.mp hlc a hm)),
                  hs, signatureIds, newIds, opening, hi⟩
              else throw "bounds: declared RHS opening changed source HM identities"
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
#print axioms Checked.signatureIdentityFixed
#print axioms Checked.interpretationScope
#print axioms Checked.fixedTypes
#print axioms Checked.sourceIdentity
#print axioms check

end FHM.Bounds.HMDeclaredReconciliation
