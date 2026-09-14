import FHM.Bounds.ScopedAnnotation
import FHM.Bounds.SchemeUse

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
#print axioms Use.inScope
#print axioms Use.hm_instance
#print axioms Use.subtype
#print axioms check

end FHM.Bounds.HMCountScheme
