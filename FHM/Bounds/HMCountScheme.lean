import FHM.Bounds.ScopedAnnotation
import FHM.Bounds.SchemeUse
import FHM.Bounds.FreeAlgebra

/-! # Closed HM/count contract interfaces

A closed template separates HM bound slots, quantified count identities and
captured identities. Its opaque opening fixes one HM monotype for a recursive
group. External specialization substitutes counts BEFORE inserting caller bounds
arguments, so counts inside those arguments cannot be captured by the telescope.

These are interface certificates only: neither opening nor specialization proves
an RHS, licenses generalization, or accepts a recursive group.
-/

namespace FHM.Bounds.HMCountScheme

open ScopedScheme CountSubstitution

structure Scheme where
  hm : PolyTy
  counts : ScopedScheme.Scheme
  hmWF : hm.WF
  countWF : counts.WF
  shape : Synth.BoundsTy.toTy counts.body = hm.body

def decode (annotation : PolyTy) (quantified captures : List Nat)
    (premises : List Constraint := []) : Except String Scheme := do
  let source ← ScopedAnnotation.contract quantified captures premises annotation.body
  if hw : annotation.body.eraseBounds.bvarsBelow annotation.paramCount = true then
    pure ⟨annotation.eraseBounds, source.scheme,
      (Ty.bvarsBelow_iff annotation.body.eraseBounds).mp hw, source.wf, source.shape⟩
  else throw "bounds: contract annotation has an out-of-scope HM slot"

def opened (s : Scheme) (args : List BoundsTy) : BoundsTy :=
  TypeSubstitution.substitute (SchemeUse.vector args) s.counts.body

/-- Every supplied vector opens the exact declared HM slots, including unused
    slots. No guessed Unit witness is imposed on a vacuous forall. -/
theorem opened_instance (s : Scheme) (args : List BoundsTy)
    (ha : args.length = s.hm.paramCount) :
    s.hm.InstantiatesTo (args.map Synth.BoundsTy.toTy) (Synth.BoundsTy.toTy (opened s args)) := by
  have hi := InstantiatesBy.openWith s.hmWF (show s.hm.paramCount ≤ (args.map Synth.BoundsTy.toTy).length by
    simp only [List.length_map]; omega)
  have he := TypeSubstitution.hm_instance hi
    (fun i => Synth.BoundsTy.toTy (SchemeUse.vector args i))
    (fun _ _ h => SchemeUse.vector_shape rfl h)
  change InstantiatesBy (args.map Synth.BoundsTy.toTy) s.hm.body _
  rw [opened, TypeSubstitution.shape, s.shape, he]
  exact hi

structure Opening (s : Scheme) (found : Ty) (captures : List Ty) where
  ids : List Nat
  arity : ids.length = s.hm.paramCount
  distinct : ids.Nodup
  /-- Fix declared free captures as well as the surrounding type interface. -/
  fresh : ∀ i ∈ ids, ∀ t ∈ s.hm.body :: captures, i ∉ t.freeVars
  shape : Synth.BoundsTy.toTy (opened s (ids.map BoundsTy.fvar)) = found.eraseBounds
  lc : found.eraseBounds.IsLC

def Opening.bounds {s found captures} (o : Opening s found captures) : BoundsTy :=
  opened s (o.ids.map BoundsTy.fvar)

def Opening.counts {s found captures} (o : Opening s found captures) : ScopedScheme.Scheme :=
  ⟨s.counts.quantified, s.counts.captures, s.counts.premises, o.bounds⟩

theorem Opening.wf {s found captures} (o : Opening s found captures) : o.counts.WF := by
  refine ⟨s.countWF.1, s.countWF.2.1, ?_, s.countWF.2.2.2⟩
  apply TypeSubstitution.inScope (SchemeUse.vector (o.ids.map BoundsTy.fvar)) s.countWF.2.2.1
  apply SchemeUse.vector_scope
  simp [ScopedScheme.boundsScopedBool]

theorem Opening.hm_instance {s found captures} (o : Opening s found captures) :
    s.hm.InstantiatesTo (o.ids.map Ty.fvar) found.eraseBounds := by
  have h := opened_instance s (o.ids.map BoundsTy.fvar) (by simpa using o.arity)
  simpa only [List.map_map, Function.comp_def, Synth.BoundsTy.toTy, o.shape] using h

private theorem close_slot (ids : List Nat) (hd : ids.Nodup) (i : Nat) (hi : i < ids.length) :
    BinderBridge.close ids (SchemeUse.vector (ids.map BoundsTy.fvar) i) = .bvar i := by
  have hm : ids[i] ∈ ids := List.getElem_mem hi
  have hx : ids.idxOf? ids[i] = some i := by
    cases h : ids.idxOf? ids[i] with
    | none => exact False.elim ((List.idxOf?_eq_none_iff.mp h) hm)
    | some j =>
        have hj := hd.idxOf_getElem i hi
        rw [List.idxOf_eq_getD_idxOf?, h] at hj
        simp only [Option.getD_some] at hj
        simpa only [hj] using h
  have hv : SchemeUse.vector (ids.map BoundsTy.fvar) i = .fvar ids[i] := by
    simp [SchemeUse.vector, List.getElem?_map, List.getElem?_eq_getElem hi]
  simp only [hv, BinderBridge.close, hx]

mutual
/-- Opaque opening and reclosing preserve the ENTIRE bounds template, not
    merely its HM skeleton. Declared captures and count payloads are unchanged. -/
theorem close_opened (ids : List Nat) (hd : ids.Nodup) (β : BoundsTy)
    (hw : ContainsBvarsUpTo ids.length (Synth.BoundsTy.toTy β))
    (hf : ∀ i ∈ ids, i ∉ (Synth.BoundsTy.toTy β).freeVars) :
    BinderBridge.close ids (TypeSubstitution.substitute (SchemeUse.vector (ids.map BoundsTy.fvar)) β) = β := by
  cases β with
  | prim => rfl
  | bvar i =>
      simp only [Synth.BoundsTy.toTy] at hw
      cases hw with
      | bvar hi => exact close_slot ids hd i hi
  | fvar i =>
      have hi : i ∉ ids := by
        intro h
        exact hf i h (by simp [Synth.BoundsTy.toTy, Ty.freeVars])
      simp only [TypeSubstitution.substitute, BinderBridge.close, List.idxOf?_eq_none_iff.mpr hi]
  | arrow a b =>
      simp only [Synth.BoundsTy.toTy] at hw
      cases hw with
      | arrow ha hb =>
          simp only [TypeSubstitution.substitute, BinderBridge.close]
          rw [close_opened ids hd a ha (fun i hi h =>
            hf i hi (by simp [Synth.BoundsTy.toTy, Ty.freeVars, h])),
            close_opened ids hd b hb (fun i hi h =>
              hf i hi (by simp [Synth.BoundsTy.toTy, Ty.freeVars, h]))]
  | list lo hi elem =>
      simp only [Synth.BoundsTy.toTy, listTy] at hw
      cases hw with
      | customTy hall =>
          exact congrArg (BoundsTy.list lo hi) (close_opened ids hd elem (hall _ (by simp))
            (fun i hi => by simpa [Synth.BoundsTy.toTy, listTy, Ty.freeVars, TyList.freeVars] using hf i hi))
  | custom name as =>
      simp only [Synth.BoundsTy.toTy] at hw
      cases hw with
      | customTy hall =>
          exact congrArg (BoundsTy.custom name) (close_opened_list ids hd as hall
            (by simpa only [Synth.BoundsTy.toTy, Ty.freeVars] using hf))
termination_by sizeOf β

private theorem close_opened_list (ids : List Nat) (hd : ids.Nodup) (as : List BoundsTy)
    (hw : ∀ t ∈ as.map Synth.BoundsTy.toTy, ContainsBvarsUpTo ids.length t)
    (hf : ∀ i ∈ ids, i ∉ TyList.freeVars (as.map Synth.BoundsTy.toTy)) :
    BinderBridge.closeList ids (TypeSubstitution.substituteList (SchemeUse.vector (ids.map BoundsTy.fvar)) as) = as := by
  cases as with
  | nil => rfl
  | cons a as =>
      simp only [TypeSubstitution.substituteList, BinderBridge.closeList]
      rw [close_opened ids hd a (hw _ (by simp)) (fun i hi h =>
          hf i hi (by simp [TyList.freeVars, h])),
        close_opened_list ids hd as (fun t ht => hw t (List.mem_cons_of_mem _ ht)) (fun i hi h =>
          hf i hi (by simp [TyList.freeVars, h]))]
termination_by sizeOf as
end

theorem Opening.close {s found captures} (o : Opening s found captures) :
    BinderBridge.close o.ids o.bounds = s.counts.body := by
  apply close_opened o.ids o.distinct s.counts.body
  · rw [s.shape, o.arity]; exact s.hmWF
  · intro i hi
    rw [s.shape]
    exact o.fresh i hi s.hm.body (by simp)

/-- Unlike recovering slots from a guessed opening, this bridge includes
    checked unused forall slots. It still needs a real RHS derivation before
    any generalization theorem can be invoked. -/
def Opening.abstraction {s found captures} (o : Opening s found captures) :
    BinderBridge.Abstraction s.hm o.bounds captures := by
  have hb : Synth.BoundsTy.toTy o.bounds = found.eraseBounds := o.shape
  refine ⟨o.ids, o.arity, o.distinct,
    fun i hi t ht => o.fresh i hi t (List.mem_cons_of_mem _ ht),
    (by rw [hb]; exact o.lc),
    ⟨o.ids.map Ty.fvar, (by simpa using o.arity), s.hmWF.eraseBounds, ?_⟩,
    (by rw [o.close, ← s.shape]; exact (FreeAlgebra.shape_erased s.counts.body).symm)⟩
  have h := InstantiatesBy.eraseBounds o.hm_instance
  simpa only [List.map_map, Function.comp_def, Ty.eraseBounds, Ty.eraseBounds_idem, hb] using h

theorem Opening.specialize {s found captures} (o : Opening s found captures) (args : Nat → BoundsTy) :
    SchemeSpecialization.mapFree (SchemeSpecialization.argument o.ids args) o.bounds =
      TypeSubstitution.substitute args s.counts.body := by
  rw [← SchemeSpecialization.close_open o.ids args o.abstraction.originalLC, o.close]

/-- A real derivation at a fresh opaque opening supplies every HM bounds
    instance in the initial (non-recursive) typed fragment. Recursive assumption
    transport and polymorphic source-binding introduction remain separate. -/
theorem Opening.rhs_instances {s found Δ env rhs}
    (o : Opening s found (env.map Synth.BoundsTy.toTy ++ rhs.tyFreeVars.map Ty.fvar))
    (h : Typed.Derives Δ env rhs o.bounds) (args : Nat → BoundsTy) :
    Typed.Derives Δ env rhs (TypeSubstitution.substitute args s.counts.body) := by
  have hg := SchemeSpecialization.fromBinder o.abstraction h args
  change Typed.Derives Δ env rhs (TypeSubstitution.substitute args (BinderBridge.close o.ids o.bounds)) at hg
  simpa only [o.close] using hg

/-- RHS intervals may be more precise than their contract. The exact checked
    HM opening still determines the slot map; no interval information is erased
    or overwritten when the actual RHS bounds are closed. -/
def Opening.abstractActual {s found captures} (o : Opening s found captures)
    (actual : BoundsTy) (shape : Synth.BoundsTy.toTy actual = found.eraseBounds) :
    BinderBridge.Abstraction s.hm actual captures := by
  have hb : Synth.BoundsTy.toTy o.bounds = found.eraseBounds := o.shape
  have ht : Synth.BoundsTy.toTy actual = Synth.BoundsTy.toTy o.bounds := shape.trans hb.symm
  have hc := o.abstraction.shape
  change Synth.BoundsTy.toTy (BinderBridge.close o.ids o.bounds) = s.hm.body.eraseBounds at hc
  refine ⟨o.ids, o.arity, o.distinct,
    fun i hi t ht => o.fresh i hi t (List.mem_cons_of_mem _ ht),
    (by rw [shape]; exact o.lc),
    ⟨o.abstraction.hmOpening.args, o.abstraction.hmOpening.arity,
      o.abstraction.hmOpening.wf, ?_⟩, ?_⟩
  · rw [ht]; exact o.abstraction.hmOpening.witness
  · rw [BinderBridge.close_shape, ht]
    simpa only [BinderBridge.close_shape] using hc

/-- Generalize the actual RHS bounds and its independently checked inclusion
    together. The exact closed contract is a demand, not a fabricated RHS type. -/
theorem Opening.rhs_subinstances {s found Δ env rhs actual}
    (o : Opening s found (env.map Synth.BoundsTy.toTy ++ rhs.tyFreeVars.map Ty.fvar))
    (h : Typed.Derives Δ env rhs actual)
    (shape : Synth.BoundsTy.toTy actual = found.eraseBounds)
    (sub : SemanticSub Δ actual o.bounds) (args : Nat → BoundsTy) :
    Typed.Derives Δ env rhs (TypeSubstitution.substitute args (BinderBridge.close o.ids actual)) ∧
    SemanticSub Δ (TypeSubstitution.substitute args (BinderBridge.close o.ids actual))
      (TypeSubstitution.substitute args s.counts.body) := by
  let a := o.abstractActual actual shape
  have hg := SchemeSpecialization.fromBinder a h args
  change Typed.Derives Δ env rhs (TypeSubstitution.substitute args (BinderBridge.close o.ids actual)) at hg
  have hs := SchemeSpecialization.subtype (SchemeSpecialization.argument o.ids args) sub
  rw [← SchemeSpecialization.close_open o.ids args a.originalLC, o.specialize args] at hs
  exact ⟨hg, hs⟩

/-- Explicit identities must be reconciled with the authoritative fixed found
    monotype. Freshness/shape checks do not themselves establish parametricity. -/
def openFixed (s : Scheme) (found : Ty) (ids : List Nat) (captures : List Ty) :
    Except String (Opening s found captures) := do
  if ha : ids.length = s.hm.paramCount then
    if hd : ids.Nodup then
      if hf : ids.all (fun i => (s.hm.body :: captures).all (fun t => !t.freeVars.contains i)) = true then
        let shape ← match BinderBridge.equalTy (Synth.BoundsTy.toTy (opened s (ids.map BoundsTy.fvar)))
            found.eraseBounds with
          | some h => pure h
          | none => throw "bounds: opaque contract opening needs specialization or disagrees with fixed HM monotype"
        if hlc : found.eraseBounds.bvarsBelow 0 = true then
          pure ⟨ids, ha, hd, by
            intro i hi t ht
            simpa [List.contains_iff_mem] using List.all_eq_true.mp (List.all_eq_true.mp hf i hi) t ht,
            shape.down, (Ty.bvarsBelow_iff found.eraseBounds).mp hlc⟩
        else throw "bounds: opaque contract opening contains an enclosing bound slot"
      else throw "bounds: opaque HM identity escapes into captured type interface"
    else throw "bounds: opaque HM slots alias one free identity"
  else throw "bounds: opaque contract opening has wrong HM arity"

structure Use (s : Scheme) (Δ : List Constraint) (found : Ty) (caller : List Nat) where
  counts : List Count
  countInstance : Instance s.counts counts caller
  usable : countInstance.Usable Δ
  types : List BoundsTy
  arity : types.length = s.hm.paramCount
  typesLC : ∀ a ∈ types, (Synth.BoundsTy.toTy a).IsLC
  typesScoped : types.all (boundsScopedBool caller) = true
  shape : Synth.BoundsTy.toTy
    (TypeSubstitution.combined (s.counts.quantified.zip counts) (SchemeUse.vector types) s.counts.body) =
      found.eraseBounds

def Use.bounds {s Δ found caller} (u : Use s Δ found caller) : BoundsTy :=
  TypeSubstitution.combined (s.counts.quantified.zip u.counts) (SchemeUse.vector u.types) s.counts.body

theorem Use.inScope {s Δ found caller} (u : Use s Δ found caller) : BoundsScoped caller u.bounds :=
  TypeSubstitution.instance_inScope u.countInstance (SchemeUse.vector u.types)
    (SchemeUse.vector_scope u.typesScoped)

theorem Use.hm_instance {s Δ found caller} (u : Use s Δ found caller) :
    s.hm.InstantiatesTo (u.types.map Synth.BoundsTy.toTy) found.eraseBounds := by
  have h := opened_instance s u.types u.arity
  have he : Synth.BoundsTy.toTy (opened s u.types) = found.eraseBounds := by
    simpa only [opened, TypeSubstitution.combined, TypeSubstitution.shape, bounds_shape] using u.shape
  rw [he] at h
  exact h

theorem Use.subtype {s Δ found caller} (u : Use s Δ found caller) {a b}
    (h : SemanticSub s.counts.premises a b) :
    SemanticSub Δ
      (TypeSubstitution.combined (s.counts.quantified.zip u.counts) (SchemeUse.vector u.types) a)
      (TypeSubstitution.combined (s.counts.quantified.zip u.counts) (SchemeUse.vector u.types) b) :=
  TypeSubstitution.instance_useSubtype u.countInstance u.usable (SchemeUse.vector u.types) h

/-- Caller bounds are explicit inputs, not reconstructed from HM shape. Their
    expression-origin evidence remains the consuming typing rule's obligation. -/
def check (s : Scheme) (Δ : List Constraint) (found : Ty) (counts : List Count)
    (types : List BoundsTy) (caller : List Nat) : Except String (Use s Δ found caller) := do
  let inst ← s.counts.instantiate counts caller
  let usable ← inst.checkPremises Δ
  if ha : types.length = s.hm.paramCount then
    if hl : types.all (fun a => (Synth.BoundsTy.toTy a).bvarsBelow 0) = true then
      if hs : types.all (boundsScopedBool caller) = true then
        let β := TypeSubstitution.combined (s.counts.quantified.zip counts) (SchemeUse.vector types) s.counts.body
        let shape ← match BinderBridge.equalTy (Synth.BoundsTy.toTy β) found.eraseBounds with
          | some h => pure h
          | none => throw "bounds: HM/count specialization disagrees with found monotype"
        pure ⟨counts, inst, usable.down, types, ha,
          fun a h => (Ty.bvarsBelow_iff (Synth.BoundsTy.toTy a)).mp (List.all_eq_true.mp hl a h),
          hs, shape.down⟩
      else throw "bounds: supplied HM argument counts are outside caller scope"
    else throw "bounds: supplied HM argument contains an enclosing bound slot"
  else throw "bounds: HM/count specialization has wrong HM arity"

#print axioms decode
#print axioms openFixed
#print axioms opened_instance
#print axioms Opening.wf
#print axioms Opening.hm_instance
#print axioms close_opened
#print axioms Opening.close
#print axioms Opening.abstraction
#print axioms Opening.specialize
#print axioms Opening.rhs_instances
#print axioms Opening.abstractActual
#print axioms Opening.rhs_subinstances
#print axioms Use.inScope
#print axioms Use.hm_instance
#print axioms Use.subtype
#print axioms check

end FHM.Bounds.HMCountScheme
