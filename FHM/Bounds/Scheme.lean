import FHM.Bounds.Semantic
import Mathlib.Data.List.GetD

/-! # Count-scheme instantiation certificates

Connect the existing executable well-formedness/instantiation API to its
declarative substitution relation. These are structural contracts, separate
from semantic substitution under assignments and integration into the typed
walk. In particular, count binders range over Nat, not extended naturals.
-/

namespace FHM.Bounds

theorem Count.binderRigidBool_sound {n : Nat} {c : Count} (h : c.binderRigidBool n = true) :
    c.BinderRigid n := by
  induction c with
  | lit | inf => trivial
  | var v => cases v with | mk kind i => cases kind <;> simpa [Count.binderRigidBool, Count.BinderRigid] using h
  | add a b ha hb | mul a b ha hb | min a b ha hb | max a b ha hb =>
      simp only [Count.binderRigidBool, Bool.and_eq_true] at h
      exact ⟨ha h.1, hb h.2⟩
  | pred a ha => exact ha h

theorem BoundsTy.schemeWFBool_sound {n : Nat} {β : BoundsTy} (h : β.schemeWFBool n = true) :
    β.SchemeWF n := by
  cases β with
  | prim | bvar | fvar => simp [BoundsTy.SchemeWF]
  | arrow a b =>
      simp only [BoundsTy.SchemeWF]
      simp only [BoundsTy.schemeWFBool, Bool.and_eq_true] at h
      exact ⟨BoundsTy.schemeWFBool_sound h.1, BoundsTy.schemeWFBool_sound h.2⟩
  | list lo hi elem =>
      simp only [BoundsTy.SchemeWF]
      simp only [BoundsTy.schemeWFBool, Bool.and_eq_true] at h
      exact ⟨Count.binderRigidBool_sound h.1.1, Count.binderRigidBool_sound h.1.2,
        BoundsTy.schemeWFBool_sound h.2⟩
  | custom name args =>
      cases args with
      | nil => simp [BoundsTy.SchemeWF]
      | cons a as =>
          simp only [BoundsTy.schemeWFBool, Bool.and_eq_true] at h
          have hh := BoundsTy.schemeWFBool_sound h.1
          have ht := BoundsTy.schemeWFBool_sound h.2
          simpa only [BoundsTy.SchemeWF, List.mem_cons, forall_eq_or_imp] using And.intro hh ht
termination_by sizeOf β

theorem Count.applyArgs_subst {args : List Count} {c : Count}
    (h : c.BinderRigid args.length) : Count.Subst args c (c.applyArgs args) := by
  induction c with
  | lit => exact .lit
  | inf => exact .inf
  | var v =>
      cases v with | mk kind i =>
        cases kind with
        | inferable => cases h
        | rigid =>
            simp only [Count.BinderRigid] at h
            simp only [Count.applyArgs, List.getD_eq_getElem args (.lit 0) h]
            exact .var (List.getElem?_eq_getElem h)
  | add a b ha hb => exact .add (ha h.1) (hb h.2)
  | mul a b ha hb => exact .mul (ha h.1) (hb h.2)
  | pred a ha => exact .pred (ha h)
  | min a b ha hb => exact .min (ha h.1) (hb h.2)
  | max a b ha hb => exact .max (ha h.1) (hb h.2)

mutual
  theorem BoundsTy.applyArgs_subst {args : List Count} {β : BoundsTy}
      (h : β.SchemeWF args.length) : BoundsTy.Subst args β (β.applyArgs args) := by
    cases β with
    | prim => simpa only [BoundsTy.applyArgs] using (BoundsTy.Subst.prim (args := args))
    | bvar => simpa only [BoundsTy.applyArgs] using (BoundsTy.Subst.bvar (args := args))
    | fvar => simpa only [BoundsTy.applyArgs] using (BoundsTy.Subst.fvar (args := args))
    | arrow a b =>
        simp only [BoundsTy.SchemeWF] at h
        simpa only [BoundsTy.applyArgs] using BoundsTy.Subst.arrow (BoundsTy.applyArgs_subst h.1) (BoundsTy.applyArgs_subst h.2)
    | list lo hi elem =>
        simp only [BoundsTy.SchemeWF] at h
        simpa only [BoundsTy.applyArgs] using BoundsTy.Subst.list
          (Count.applyArgs_subst h.1) (Count.applyArgs_subst h.2.1) (BoundsTy.applyArgs_subst h.2.2)
    | custom name as =>
        simp only [BoundsTy.SchemeWF] at h
        simpa only [BoundsTy.applyArgs] using BoundsTy.Subst.custom (applyArgsAll_subst h)
  termination_by sizeOf β

  private theorem applyArgsAll_subst {args : List Count} {as : List BoundsTy}
      (h : ∀ β ∈ as, β.SchemeWF args.length) :
      List.Forall₂ (BoundsTy.Subst args) as (as.map (BoundsTy.applyArgs args)) := by
    cases as with
    | nil => exact .nil
    | cons a as =>
        exact .cons (BoundsTy.applyArgs_subst (h a (by simp)))
          (applyArgsAll_subst (fun β hb => h β (by simp [hb])))
  termination_by sizeOf as
end

/-- The legacy zero-default lookup is unreachable for well-formed schemes:
    successful instantiation has the specified arity and a full substitution
    derivation. This theorem does not license infinite Nat-binder arguments. -/
theorem BScheme.instantiate?_sound {s : BScheme} {args : List Count} {β : BoundsTy}
    (h : s.instantiate? args = some β) : s.InstantiatesTo args β := by
  unfold instantiate? at h
  split at h
  · rename_i hg
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hg
    have hw : s.WF := BoundsTy.schemeWFBool_sound hg.1
    have hs := BoundsTy.applyArgs_subst (args := args) (β := s.body)
      (by simpa only [hg.2] using hw)
    cases h
    exact .intro hw hg.2 hs
  · cases h

/-- A Nat-only evaluator used to interpret finite count arguments. Its infinity
    case is deliberately not a semantic encoding; the equality theorem below
    requires `NoInf` evidence. -/
def Count.evalNat (c : Count) (σ : Assign) : Nat :=
  match c with
  | .lit n => n
  | .inf => 0
  | .var v => σ v
  | .add a b => a.evalNat σ + b.evalNat σ
  | .mul a b => a.evalNat σ * b.evalNat σ
  | .pred a => a.evalNat σ - 1
  | .min a b => Nat.min (a.evalNat σ) (b.evalNat σ)
  | .max a b => Nat.max (a.evalNat σ) (b.evalNat σ)

private theorem mul_ofNat (a b : Nat) :
    ExtNat.mul (.ofNat a) (.ofNat b) = .ofNat (a * b) := by
  cases a <;> cases b <;> simp [ExtNat.mul]

theorem Count.NoInf.eval_eq_ofNat {c : Count} (h : c.NoInf) (σ : Assign) :
    c.eval σ = .ofNat (c.evalNat σ) := by
  induction h with
  | lit | var => rfl
  | add _ _ ha hb => simp only [Count.eval, Count.evalNat, ha, hb, ExtNat.add]
  | mul _ _ ha hb => simp only [Count.eval, Count.evalNat, ha, hb, mul_ofNat]
  | pred _ ha => simp only [Count.eval, Count.evalNat, ha, ExtNat.pred]
  | min _ _ ha hb => simp only [Count.eval, Count.evalNat, ha, hb, ExtNat.min]
  | max _ _ ha hb => simp only [Count.eval, Count.evalNat, ha, hb, ExtNat.max]

def countArgAssign (args : List Count) (σ : Assign) : Assign :=
  fun v => match v.kind with
    | .rigid => (args.getD v.idx (.lit 0)).evalNat σ
    | .inferable => σ v

/-- Substitution commutes with evaluation when Nat arguments are finite. The
    body may still explicitly contain infinity as an interval endpoint. -/
theorem Count.Subst.eval {args : List Count} {c c' : Count}
    (h : Count.Subst args c c') (hf : ∀ a ∈ args, a.NoInf) (σ : Assign) :
    c'.eval σ = c.eval (countArgAssign args σ) := by
  induction h with
  | lit | inf => rfl
  | @var i c hc =>
      have hfinite := hf c (List.mem_of_getElem? hc)
      simpa only [Count.eval, countArgAssign, List.getD_eq_getElem?_getD, hc,
        Option.getD_some] using hfinite.eval_eq_ofNat σ
  | add _ _ ha hb => simp only [Count.eval, ha, hb]
  | mul _ _ ha hb => simp only [Count.eval, ha, hb]
  | pred _ ha => simp only [Count.eval, ha]
  | min _ _ ha hb => simp only [Count.eval, ha, hb]
  | max _ _ ha hb => simp only [Count.eval, ha, hb]

structure NatInstance (s : BScheme) (args : List Count) where
  bounds : BoundsTy
  substitution : s.InstantiatesTo args bounds
  finiteArgs : ∀ a ∈ args, a.NoInf

/-- Guarded instantiation for Nat telescopes. This conservative check rejects
    expressions containing infinity, even if some evaluate finitely. -/
def BScheme.instantiateNat (s : BScheme) (args : List Count) :
    Except String (NatInstance s args) := do
  if hf : args.all Count.noInf = true then
    match h : s.instantiate? args with
    | none => throw "bounds: count scheme ill-formed or wrong arity"
    | some β =>
        pure ⟨β, BScheme.instantiate?_sound h,
          fun a ha => Count.noInf_of_isNoInf (List.all_eq_true.mp hf a ha)⟩
  else throw "bounds: Nat count argument must be finite"

#print axioms BScheme.instantiate?_sound
#print axioms Count.Subst.eval
#print axioms BScheme.instantiateNat

end FHM.Bounds
