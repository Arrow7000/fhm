import FHM.InferenceSupport

theorem Ty.openVarsFrom_zero (Xs : List Nat) (ty : Ty) :
    Ty.openVarsFrom 0 Xs ty = Ty.openVars Xs ty := by
  simp only [Ty.openVarsFrom, Ty.openVars, Nat.not_lt_zero, if_false, Nat.sub_zero]

/-! Declarative annotation matching for canonical partial source. No expression
inference or generalization worker is defined here. -/

namespace PartialCore

abbrev HoleAssignment := List (String × Ty)

namespace HoleAssignment

def Unique (holes : HoleAssignment) : Prop := (holes.map Prod.fst).Nodup

def Scoped (n : Nat) (holes : HoleAssignment) : Prop :=
  ∀ entry ∈ holes, ContainsBvarsUpTo n entry.2

def map (f : Ty → Ty) (holes : HoleAssignment) : HoleAssignment :=
  List.map (fun entry => (entry.1, f entry.2)) holes

theorem lookup_map (f : Ty → Ty) (holes : HoleAssignment) (name : String) :
    LookupList.get? (map f holes) name = (LookupList.get? holes name).map f := by
  induction holes with
  | nil => rfl
  | cons entry rest ih =>
      by_cases hn : name = entry.1
      · simp [map, LookupList.get?, hn]
      · simpa only [map, List.map_cons, LookupList.get?, if_neg hn] using ih

theorem unique_map (f : Ty → Ty) (h : Unique holes) : Unique (map f holes) := by
  simpa only [Unique, map, List.map_map, Function.comp_def] using h

theorem scoped_map (h : Scoped n holes)
    (hf : ∀ ty, ContainsBvarsUpTo n ty → ContainsBvarsUpTo m (f ty)) :
    Scoped m (map f holes) := by
  intro entry he
  obtain ⟨original, ho, rfl⟩ := List.mem_map.mp he
  exact hf _ (h _ ho)

end HoleAssignment

mutual
def Template.map (f : Ty → Ty) : Template → Template
  | .fixed ty => .fixed (f ty)
  | .hole => .hole
  | .named name => .named name
  | .arrow a b => .arrow (a.map f) (b.map f)
  | .custom name args => .custom name (mapTemplates f args)
def mapTemplates (f : Ty → Ty) : List Template → List Template
  | [] => []
  | t :: ts => t.map f :: mapTemplates f ts
end

mutual
theorem Template.map_map (t : Template) (f g : Ty → Ty) :
    (t.map f).map g = t.map (g ∘ f) := by
  cases t with
  | fixed | hole | named => rfl
  | arrow a b => simp only [Template.map, a.map_map, b.map_map]
  | custom name args => simp only [Template.map, mapTemplates_map args f g]
theorem mapTemplates_map (ts : List Template) (f g : Ty → Ty) :
    mapTemplates g (mapTemplates f ts) = mapTemplates (g ∘ f) ts := by
  cases ts with
  | nil => rfl
  | cons t ts => simp only [mapTemplates, t.map_map, mapTemplates_map ts f g]
end

/-- Pure matching. `_` has no lookup; every named occurrence uses the same
finite assignment. Scope and uniqueness are supplied by `Completion`. -/
inductive Template.Fits (holes : HoleAssignment) : Template → Ty → Prop
  | fixed : Fits holes (.fixed ty) ty
  | hole : Fits holes .hole ty
  | named : LookupList.get? holes name = some ty → Fits holes (.named name) ty
  | arrow : Fits holes a ta → Fits holes b tb → Fits holes (.arrow a b) (.arrow ta tb)
  | custom : List.Forall₂ (Fits holes) args tys →
      Fits holes (.custom name args) (.customTy name tys)

mutual
theorem Template.Fits.map (h : Template.Fits holes t ty) (f : Ty → Ty)
    (ha : ∀ a b, f (.arrow a b) = .arrow (f a) (f b))
    (hc : ∀ name args, f (.customTy name args) = .customTy name (args.map f)) :
    Template.Fits (HoleAssignment.map f holes) (t.map f) (f ty) := by
  cases h with
  | fixed => exact .fixed
  | hole => exact .hole
  | named hl => exact .named (by rw [HoleAssignment.lookup_map, hl]; rfl)
  | arrow a b => rw [ha]; exact .arrow (a.map f ha hc) (b.map f ha hc)
  | custom hs => rw [hc]; exact .custom (fitsList_map hs f ha hc)
theorem fitsList_map (h : List.Forall₂ (Template.Fits holes) ts tys) (f : Ty → Ty)
    (ha : ∀ a b, f (.arrow a b) = .arrow (f a) (f b))
    (hc : ∀ name args, f (.customTy name args) = .customTy name (args.map f)) :
    List.Forall₂ (Template.Fits (HoleAssignment.map f holes)) (mapTemplates f ts) (tys.map f) := by
  cases h with
  | nil => exact .nil
  | cons h ht => exact .cons (h.map f ha hc) (fitsList_map ht f ha hc)
end

/-- A local annotation witness, before opening written binders. Unused entries
need not have unique solutions, and no principality of assignments is claimed. -/
structure Completion (n : Nat) (t : Template) (ty : Ty) where
  holes : HoleAssignment
  unique : holes.Unique
  scope : holes.Scoped n
  fits : t.Fits holes ty
  regular : ContainsBvarsUpTo n ty

def Completion.onSubst (h : Completion n t ty) (S : Subst)
    (hS : ∀ entry ∈ S, entry.2.IsLC) :
    Completion n (t.map S.onTy) (S.onTy ty) :=
  ⟨HoleAssignment.map S.onTy h.holes, HoleAssignment.unique_map S.onTy h.unique,
    HoleAssignment.scoped_map h.scope (fun _ ht => Subst.onTy_containsBvars hS ht),
    h.fits.map _ (fun _ _ => Subst.onTy_arrow) (fun _ _ => Subst.onTy_customTy),
    Subst.onTy_containsBvars hS h.regular⟩

/-- Opening transports the entire assignment, including references to written
bound variables. Repeated names therefore open in lockstep. -/
def Completion.open (h : Completion n t ty) (Xs : List Nat) (hlen : n ≤ Xs.length) :
    Completion 0 (t.map (Ty.openVars Xs)) (ty.openVars Xs) :=
  ⟨HoleAssignment.map (Ty.openVars Xs) h.holes, HoleAssignment.unique_map _ h.unique,
    HoleAssignment.scoped_map h.scope (fun _ ht => Ty.openVars_isLC ht hlen),
    h.fits.map _ (fun _ _ => Ty.openVars_arrow) (fun _ _ => Ty.openVars_customTy),
    Ty.openVars_isLC h.regular hlen⟩

theorem Template.Fits.named_equality
    (ha : Template.Fits holes (.named name) a)
    (hb : Template.Fits holes (.named name) b) : a = b := by
  cases ha with
  | named ha => cases hb with | named hb => exact Option.some.inj (ha.symm.trans hb)

/-- Authored fixed leaves may mention only written binders. Inferred extra
binders can be selected by holes but cannot retroactively scope authored syntax. -/
inductive Template.WellScoped (n : Nat) : Template → Prop
  | fixed : ContainsBvarsUpTo n ty → WellScoped n (.fixed ty)
  | hole : WellScoped n .hole
  | named : WellScoped n (.named name)
  | arrow : WellScoped n a → WellScoped n b → WellScoped n (.arrow a b)
  | custom : (∀ t ∈ args, WellScoped n t) → WellScoped n (.custom name args)

mutual
theorem Template.Fits.wellScoped (h : Template.Fits holes t ty)
    (hty : ContainsBvarsUpTo n ty) : t.WellScoped n := by
  cases h with
  | fixed => exact .fixed hty
  | hole => exact .hole
  | named => exact .named
  | arrow ha hb =>
      cases hty with
      | arrow hta htb => exact .arrow (ha.wellScoped hta) (hb.wellScoped htb)
  | custom hs =>
      cases hty with
      | customTy ht => exact .custom (fitsList_wellScoped hs ht)
theorem fitsList_wellScoped (h : List.Forall₂ (Template.Fits holes) ts tys)
    (htys : ∀ ty ∈ tys, ContainsBvarsUpTo n ty) : ∀ t ∈ ts, t.WellScoped n := by
  cases h with
  | nil => simp
  | cons hh ht =>
      intro t hm
      rcases List.mem_cons.mp hm with rfl | hm
      · exact hh.wellScoped (htys _ (List.mem_cons_self ..))
      · exact fitsList_wellScoped ht (fun ty hty => htys ty (List.mem_cons_of_mem _ hty)) t hm
end

private theorem ty_open_prefix (h : ContainsBvarsUpTo count ty) (Xs : List Nat) :
    ty.openVars (Xs.take count) = ty.openVars Xs := by
  induction ty using Ty.rec_strong with
  | prim | fvar => rfl
  | bvar i =>
      cases h with
      | bvar hi => simp [Ty.openVars, Ty.instantiate, hi]
  | arrow a b iha ihb =>
      cases h with
      | arrow ha hb => simp only [Ty.openVars_arrow, iha ha, ihb hb]
  | customTy name args ih =>
      cases h with
      | customTy hs =>
          rw [Ty.openVars_customTy, Ty.openVars_customTy]
          congr 1
          exact List.map_congr_left (fun t ht => ih t ht (hs t ht))

private theorem mapTemplates_eq_map (ts : List Template) (f : Ty → Ty) :
    mapTemplates f ts = ts.map (Template.map f) := by
  induction ts with
  | nil => rfl
  | cons t ts ih => simp only [mapTemplates, List.map_cons, ih]

theorem Template.WellScoped.map {t : Template} (h : t.WellScoped n)
    (f : Ty → Ty) (hf : ∀ ty, ContainsBvarsUpTo n ty → ContainsBvarsUpTo m (f ty)) :
    (t.map f).WellScoped m := by
  induction h with
  | fixed ht => exact .fixed (hf _ ht)
  | hole => exact .hole
  | named => exact .named
  | arrow _ _ iha ihb => exact .arrow iha ihb
  | custom hs ih =>
      simp only [Template.map, mapTemplates_eq_map]
      apply Template.WellScoped.custom
      intro mapped hm
      obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hm
      exact ih t ht

/-- Ordinary annotations have no written binders. Opening an inferred scheme
changes their hole solutions, while all authored fixed leaves stay unchanged. -/
theorem Template.WellScoped.open_lc {t : Template} (h : t.WellScoped 0) (Xs : List Nat) :
    t.map (Ty.openVars Xs) = t := by
  induction h with
  | fixed ht => exact congrArg Template.fixed (Ty.instantiate_eq_self_of_lc ht)
  | hole | named => rfl
  | arrow _ _ iha ihb => simp only [Template.map, iha, ihb]
  | @custom args name hs ih =>
      simp only [Template.map, mapTemplates_eq_map]
      congr 1
      conv_rhs => rw [← List.map_id args]
      exact List.map_congr_left (fun t ht => ih t ht)

mutual
/-- Scope reflection does not assume that authored fixed leaves were valid:
checking one fully opened, locally closed result establishes that fact. -/
theorem Template.scope_of_open (t : Template) (Xs : List Nat)
    (h : (t.map (Ty.openVars (Xs.take count))).WellScoped 0) : t.WellScoped count := by
  cases t with
  | fixed ty =>
      cases h with
      | fixed ht =>
          have hb := Ty.containsBvars_of_openVarsFrom 0 (Xs.take count) (t := ty) (by
            simpa only [Ty.openVarsFrom, Ty.openVars, Nat.not_lt_zero, if_false, Nat.sub_zero] using ht)
          exact .fixed (hb.mono (by simp only [List.length_take]; omega))
  | hole => exact .hole
  | named => exact .named
  | arrow a b =>
      cases h with
      | arrow ha hb => exact .arrow (a.scope_of_open Xs ha) (b.scope_of_open Xs hb)
  | custom name args =>
      simp only [Template.map, mapTemplates_eq_map] at h
      cases h with
      | custom hs =>
          exact .custom (scopeList_of_open args Xs (by
            simpa only [mapTemplates_eq_map] using hs))
termination_by sizeOf t
theorem scopeList_of_open (ts : List Template) (Xs : List Nat)
    (h : ∀ t ∈ mapTemplates (Ty.openVars (Xs.take count)) ts, t.WellScoped 0) :
    ∀ t ∈ ts, t.WellScoped count := by
  cases ts with
  | nil => simp
  | cons t ts =>
      intro a ha
      rcases List.mem_cons.mp ha with rfl | ha
      · exact Template.scope_of_open _ Xs (h _ (List.mem_cons_self ..))
      · exact scopeList_of_open ts Xs (fun t ht => h t (List.mem_cons_of_mem _ ht)) a ha
termination_by sizeOf ts
decreasing_by
  all_goals (subst_vars; simp_wf)
  all_goals omega
end

/-- Only the written prefix opens authored syntax. Inferred extra binders are
available to the preselected hole assignment, not to authored fixed leaves. -/
theorem Template.WellScoped.open_prefix {t : Template} (h : t.WellScoped count) (Xs : List Nat) :
    t.map (Ty.openVars (Xs.take count)) = t.map (Ty.openVars Xs) := by
  induction h with
  | fixed ht => exact congrArg Template.fixed (ty_open_prefix ht Xs)
  | hole | named => rfl
  | arrow _ _ iha ihb => simp only [Template.map, iha, ihb]
  | custom hs ih =>
      simp only [Template.map, mapTemplates_eq_map]
      congr 1
      exact List.map_congr_left (fun t ht => ih t ht)

mutual
/-- Written type-variable leaves, excluding both kinds of inferred holes. -/
def Template.rigidVars : Template → List Nat
  | .fixed ty => ty.freeVars
  | .hole | .named _ => []
  | .arrow a b => a.rigidVars ++ b.rigidVars
  | .custom _ args => templateRigidVars args
def templateRigidVars : List Template → List Nat
  | [] => []
  | t :: ts => t.rigidVars ++ templateRigidVars ts
end

private theorem mem_templateRigidVars {t : Template} {ts : List Template}
    (ht : t ∈ ts) (hx : x ∈ t.rigidVars) : x ∈ templateRigidVars ts := by
  induction ts with
  | nil => cases ht
  | cons a ts ih =>
      rcases List.mem_cons.mp ht with rfl | ht
      · exact List.mem_append_left _ hx
      · exact List.mem_append_right _ (ih ht)

theorem Template.WellScoped.close_open {t : Template} (h : t.WellScoped count)
    (Xs : List Nat) (hnd : Xs.Nodup) (hlen : count ≤ Xs.length)
    (hfresh : ∀ x ∈ Xs, x ∉ t.rigidVars) :
    t.map (fun ty => (ty.openVars Xs).closeOver Xs) = t := by
  revert hfresh
  induction h with
  | fixed ht =>
      intro hfresh
      exact congrArg Template.fixed (Ty.closeOver_openVars_self hnd (ht.mono hlen) hfresh)
  | hole | named => intro _; rfl
  | arrow ha hb iha ihb =>
      intro hfresh
      simp only [Template.map]
      rw [iha (fun x hx hv => hfresh x hx (List.mem_append_left _ hv)),
        ihb (fun x hx hv => hfresh x hx (List.mem_append_right _ hv))]
  | @custom args name hs ih =>
      intro hfresh
      simp only [Template.map, mapTemplates_eq_map]
      congr 1
      conv_rhs => rw [← List.map_id args]
      exact List.map_congr_left (fun t ht => ih t ht (fun x hx hv =>
        hfresh x hx (mem_templateRigidVars ht hv)))

/-- Close an opened match and its local assignment together. This is shared by
ordinary and explicitly quantified annotation checking, independently of which
names the generalization policy chose. -/
theorem Template.Fits.close_open {t : Template} {ty : Ty}
    (h : Template.Fits holes (t.map (Ty.openVars Xs)) (ty.openVars Xs))
    (hs : t.WellScoped count) (hnd : Xs.Nodup) (hlen : count ≤ Xs.length)
    (hb : ContainsBvarsUpTo Xs.length ty)
    (htFresh : ∀ x ∈ Xs, x ∉ t.rigidVars)
    (hFresh : ∀ x ∈ Xs, x ∉ ty.freeVars) :
    Template.Fits (HoleAssignment.map (Ty.closeOver Xs) holes) t ty := by
  have hc := h.map (Ty.closeOver Xs)
    (fun _ _ => rfl) (fun name args => by
      simp only [Ty.closeOver]
      congr 1
      induction args with
      | nil => rfl
      | cons a args ih => simp only [TyList.closeOver, List.map_cons, ih])
  simpa only [Template.map_map, Function.comp_def, hs.close_open Xs hnd hlen htFresh,
    Ty.closeOver_openVars_self hnd hb hFresh] using hc

mutual
def Template.names : Template → List String
  | .fixed _ | .hole => []
  | .named name => [name]
  | .arrow a b => a.names ++ b.names
  | .custom _ args => templateNames args
def templateNames : List Template → List String
  | [] => []
  | t :: ts => t.names ++ templateNames ts
end

mutual
theorem Template.Fits.covers {t : Template} {holes : HoleAssignment} {ty : Ty}
    (h : t.Fits holes ty) :
    ∀ name ∈ t.names, ∃ target, LookupList.get? holes name = some target := by
  cases h with
  | fixed | hole => simp [Template.names]
  | named hl =>
      intro query hn
      simp only [Template.names, List.mem_singleton] at hn
      subst query
      exact ⟨_, hl⟩
  | arrow ha hb =>
      intro name hn
      exact (List.mem_append.mp hn).elim (ha.covers name) (hb.covers name)
  | custom hs => exact fitsList_covers hs
theorem fitsList_covers (h : List.Forall₂ (Template.Fits holes) ts tys) :
    ∀ name ∈ templateNames ts, ∃ target, LookupList.get? holes name = some target := by
  cases h with
  | nil => simp [templateNames]
  | cons ht hs =>
      intro name hn
      exact (List.mem_append.mp hn).elim (ht.covers name) (fitsList_covers hs name)
end

mutual
theorem Template.Fits.named_regular (h : Template.Fits holes t ty) (hlc : ContainsBvarsUpTo n ty) :
    ∀ name ∈ t.names, ∀ value, LookupList.get? holes name = some value → ContainsBvarsUpTo n value := by
  cases h with
  | fixed | hole => simp [Template.names]
  | named hl =>
    intro name hn value hv
    simp only [Template.names, List.mem_singleton] at hn
    subst name
    cases Option.some.inj (hl.symm.trans hv)
    exact hlc
  | arrow ha hb =>
    cases hlc with
    | arrow hla hlb =>
      intro name hn
      exact (List.mem_append.mp hn).elim (ha.named_regular hla name) (hb.named_regular hlb name)
  | custom hs =>
    cases hlc with
    | customTy hall => exact fitsList_named_regular hs hall
theorem fitsList_named_regular (h : List.Forall₂ (Template.Fits holes) ts tys)
    (hlc : ∀ ty ∈ tys, ContainsBvarsUpTo n ty) :
    ∀ name ∈ templateNames ts, ∀ value, LookupList.get? holes name = some value → ContainsBvarsUpTo n value := by
  cases h with
  | nil => simp [templateNames]
  | cons ht hs =>
    intro name hn
    exact (List.mem_append.mp hn).elim (ht.named_regular (hlc _ List.mem_cons_self) name)
      (fitsList_named_regular hs (fun ty ht => hlc ty (List.mem_cons_of_mem _ ht)) name)
end

def HoleAssignment.restrict (keys : List String) (holes : HoleAssignment) : HoleAssignment :=
  keys.map fun name => (name, (LookupList.get? holes name).getD (.prim .unit))

theorem HoleAssignment.restrict_lookup (hk : name ∈ keys)
    (hl : LookupList.get? holes name = some ty) :
    LookupList.get? (restrict keys holes) name = some ty := by
  induction keys with
  | nil => cases hk
  | cons key rest ih =>
    by_cases heq : name = key
    · subst key; simp [restrict, LookupList.get?, hl]
    · simp only [List.mem_cons] at hk
      simpa only [restrict, List.map_cons, LookupList.get?, if_neg heq] using ih (hk.resolve_left heq)

theorem HoleAssignment.restrict_unique (hk : keys.Nodup) : (restrict keys holes).Unique := by
  unfold Unique restrict
  rw [List.map_map]
  change (keys.map id).Nodup
  simpa only [List.map_id] using hk

mutual
theorem Template.Fits.change_assignment (h : Template.Fits holes t ty)
    (ha : ∀ name ∈ t.names, LookupList.get? other name = LookupList.get? holes name) :
    Template.Fits other t ty := by
  cases h with
  | fixed => exact .fixed
  | hole => exact .hole
  | named hl => exact .named ((ha _ (by simp [Template.names])).trans hl)
  | arrow h₁ h₂ =>
    exact .arrow
      (h₁.change_assignment (fun name hn => ha name (List.mem_append_left _ hn)))
      (h₂.change_assignment (fun name hn => ha name (List.mem_append_right _ hn)))
  | custom hs => exact .custom (fitsList_change_assignment hs ha)
theorem fitsList_change_assignment (h : List.Forall₂ (Template.Fits holes) ts tys)
    (ha : ∀ name ∈ templateNames ts, LookupList.get? other name = LookupList.get? holes name) :
    List.Forall₂ (Template.Fits other) ts tys := by
  cases h with
  | nil => exact .nil
  | cons ht hs =>
    exact .cons
      (ht.change_assignment (fun name hn => ha name (List.mem_append_left _ hn)))
      (fitsList_change_assignment hs (fun name hn => ha name (List.mem_append_right _ hn)))
end

theorem Template.Fits.restrict (h : Template.Fits holes t ty) :
    Template.Fits (HoleAssignment.restrict t.names.dedup holes) t ty := by
  apply h.change_assignment
  intro name hn
  obtain ⟨value, hv⟩ := h.covers name hn
  exact (HoleAssignment.restrict_lookup (List.mem_dedup.mpr hn) hv).trans hv.symm

/-- A regular matched type gives a finite regular completion. Unused entries
are discarded; no uniqueness or principality claim about them is required. -/
def Template.Fits.completion (h : Template.Fits holes t ty) (hlc : ContainsBvarsUpTo n ty) :
    Completion n t ty := by
  let selected := HoleAssignment.restrict t.names.dedup holes
  have hag : ∀ name ∈ t.names, LookupList.get? selected name = LookupList.get? holes name := by
    intro name hn
    obtain ⟨value, hv⟩ := h.covers name hn
    exact (HoleAssignment.restrict_lookup (List.mem_dedup.mpr hn) hv).trans hv.symm
  refine ⟨selected, HoleAssignment.restrict_unique (List.nodup_dedup _), ?_, h.change_assignment hag, hlc⟩
  intro entry he
  obtain ⟨name, hn, rfl⟩ := List.mem_map.mp he
  obtain ⟨value, hv⟩ := h.covers name (List.mem_dedup.mp hn)
  simp only [hv, Option.getD_some]
  exact h.named_regular hlc name (List.mem_dedup.mp hn) value hv

/-- Close a single selected assignment together with its matched type. The
same completion can subsequently be reopened at every fresh scheme opening. -/
def Completion.close {t : Template} {ty : Ty} {Xs : List Nat} {count : Nat}
    (h : Completion 0 (t.map (Ty.openVars Xs)) (ty.openVars Xs))
    (hs : t.WellScoped count) (hnd : Xs.Nodup) (hlen : count ≤ Xs.length)
    (hb : ContainsBvarsUpTo Xs.length ty)
    (htFresh : ∀ x ∈ Xs, x ∉ t.rigidVars)
    (hFresh : ∀ x ∈ Xs, x ∉ ty.freeVars) : Completion Xs.length t ty :=
  ⟨HoleAssignment.map (Ty.closeOver Xs) h.holes,
    HoleAssignment.unique_map _ h.unique,
    HoleAssignment.scoped_map h.scope (fun _ hv => Ty.closeOver_preserves_bvars hv),
    h.fits.close_open hs hnd hlen hb htFresh hFresh, hb⟩

def Ann.paramCount : Ann → Nat
  | .complete scheme => scheme.paramCount
  | .partialForall count _ => count
  | _ => 0

def Ann.map (f : Ty → Ty) : Ann → Ann
  | .absent => .absent
  | .complete scheme => .complete ⟨scheme.paramCount, f scheme.body⟩
  | .template t => .template (t.map f)
  | .partialForall count t => .partialForall count (t.map f)

/-- Additional inferred binders are permitted, as in the current policy. This
helper makes that policy independent of annotation matching. -/
def AllowsExtraBinders (written inferred : Nat) : Prop := written ≤ inferred

/-- All witnesses here are chosen BEFORE the cofinite premise of `TypeOf.letIn`.
In particular a hole may be a `bvar` of the completed scheme. -/
inductive SchemeMatches : Ann → PolyTy → Type
  | absent : scheme.WF → SchemeMatches .absent scheme
  | complete : scheme.WF → SchemeMatches (.complete scheme) scheme
  | template : t.WellScoped 0 → Completion scheme.paramCount t scheme.body →
      SchemeMatches (.template t) scheme
  | partialForall : AllowsExtraBinders count scheme.paramCount →
      t.WellScoped count → Completion scheme.paramCount t scheme.body →
      SchemeMatches (.partialForall count t) scheme

theorem SchemeMatches.regular (h : SchemeMatches ann scheme) : scheme.WF := by
  cases h with
  | absent h | complete h => exact h
  | template _ h | partialForall _ _ h => exact h.regular

/-- Substitution carries the very same local assignment through the signature.
Generalization policy and written binder counts do not participate. -/
def SchemeMatches.onSubst (h : SchemeMatches ann scheme) (S : Subst)
    (hS : ∀ pair ∈ S, pair.2.IsLC) :
    SchemeMatches (ann.map S.onTy) (S.onPolyTy scheme) := by
  cases h with
  | absent hwf => exact .absent (Subst.onPolyTy_wf hS hwf)
  | complete hwf => exact .complete (Subst.onPolyTy_wf hS hwf)
  | template hs hc =>
      exact .template (hs.map S.onTy (fun _ ht => Subst.onTy_containsBvars hS ht)) (hc.onSubst S hS)
  | partialForall hle hs hc =>
      exact .partialForall hle (hs.map S.onTy (fun _ ht => Subst.onTy_containsBvars hS ht)) (hc.onSubst S hS)

def SchemeMatches.open_partial
    (h : SchemeMatches (.partialForall count t) scheme) (Xs : List Nat)
    (hlen : scheme.paramCount ≤ Xs.length) :
    Completion 0 (t.map (Ty.openVars (Xs.take count))) (scheme.openVars Xs) := by
  cases h with
  | partialForall _ hs h =>
      rw [hs.open_prefix]
      exact h.open Xs hlen

end PartialCore
