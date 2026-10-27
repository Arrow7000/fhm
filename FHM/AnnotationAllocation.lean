import FHM.AnnotationMatching

/-! Annotation-local allocation and checking, independent of expression
inference and of generalization or recursive scheduling policy. -/

namespace PartialCore

/-- Tabulation gives a finite, annotation-local assignment. The caller starts
a new table for every annotation, even when the textual names are identical. -/
def holeTable (keys : List String) (frontier : Nat) : HoleAssignment :=
  keys.map fun name => (name, .fvar (frontier + keys.idxOf name))

theorem lookup_holeTable (h : name ∈ keys) :
    LookupList.get? (holeTable keys frontier) name =
      some (.fvar (frontier + keys.idxOf name)) := by
  have tabulate : ∀ (ks : List String) (f : String → Ty), name ∈ ks →
      LookupList.get? (List.map (fun key => (key, f key)) ks) name = some (f name) := by
    intro ks f hm
    induction ks with
    | nil => simp at hm
    | cons k ks ih =>
        by_cases hk : name = k
        · subst k; simp [LookupList.get?]
        · simp only [List.mem_cons] at hm
          simpa only [List.map_cons, LookupList.get?, if_neg hk] using
            ih (hm.resolve_left hk)
  exact tabulate keys _ h

theorem holeTable_unique (h : keys.Nodup) : (holeTable keys frontier).Unique := by
  simpa [HoleAssignment.Unique, holeTable, List.map_map, Function.comp_def] using h

theorem holeTable_scope : (holeTable keys frontier).Scoped 0 := by
  intro entry he
  obtain ⟨name, _, rfl⟩ := List.mem_map.mp he
  exact .fvar

mutual
/-- Anonymous holes allocate on each occurrence; named holes read the table
chosen once for this annotation. This allocation is strictly algorithmic. -/
def resolveTemplate (holes : HoleAssignment) (frontier : Nat) : Template → Nat × Ty
  | .fixed ty => (frontier, ty)
  | .hole => (frontier + 1, .fvar frontier)
  | .named name => (frontier, (LookupList.get? holes name).getD (.fvar frontier))
  | .arrow a b =>
      let (next, ta) := resolveTemplate holes frontier a
      let (last, tb) := resolveTemplate holes next b
      (last, .arrow ta tb)
  | .custom name args =>
      let (next, tys) := resolveTemplates holes frontier args
      (next, .customTy name tys)
def resolveTemplates (holes : HoleAssignment) (frontier : Nat) : List Template → Nat × List Ty
  | [] => (frontier, [])
  | t :: ts =>
      let (next, ty) := resolveTemplate holes frontier t
      let (last, tys) := resolveTemplates holes next ts
      (last, ty :: tys)
end

mutual
theorem resolveTemplate_fits (t : Template) (holes : HoleAssignment) (frontier : Nat)
    (hc : ∀ name ∈ t.names, ∃ ty, LookupList.get? holes name = some ty) :
    t.Fits holes (resolveTemplate holes frontier t).2 := by
  cases t with
  | fixed => exact .fixed
  | hole => exact .hole
  | named name =>
      obtain ⟨ty, ht⟩ := hc name (by simp [Template.names])
      simp only [resolveTemplate, ht, Option.getD_some]
      exact .named ht
  | arrow a b =>
      exact .arrow
        (resolveTemplate_fits a holes frontier (fun name hn => hc name (List.mem_append_left _ hn)))
        (resolveTemplate_fits b holes _ (fun name hn => hc name (List.mem_append_right _ hn)))
  | custom name args => exact .custom (resolveTemplates_fits args holes frontier hc)
theorem resolveTemplates_fits (ts : List Template) (holes : HoleAssignment) (frontier : Nat)
    (hc : ∀ name ∈ templateNames ts, ∃ ty, LookupList.get? holes name = some ty) :
    List.Forall₂ (Template.Fits holes) ts (resolveTemplates holes frontier ts).2 := by
  cases ts with
  | nil => exact .nil
  | cons t ts =>
      exact .cons
        (resolveTemplate_fits t holes frontier (fun name hn => hc name (List.mem_append_left _ hn)))
        (resolveTemplates_fits ts holes _ (fun name hn => hc name (List.mem_append_right _ hn)))
end

def Template.allocationHoles (frontier : Nat) (t : Template) : HoleAssignment :=
  holeTable t.names.dedup frontier

def Template.allocate (frontier : Nat) (t : Template) : Nat × Ty :=
  resolveTemplate (t.allocationHoles frontier) (frontier + t.names.dedup.length) t

/-- One fresh visit, returning semantic/editor data rather than a completed
expression. LC is checked so malformed hand-built bound-variable syntax fails. -/
structure Allocation (t : Template) where
  frontier : Nat
  ty : Ty
  completion : Completion 0 t ty

def allocate (frontier : Nat) (t : Template) : Option (Allocation t) :=
  let keys := t.names.dedup
  let holes := holeTable keys frontier
  let result := resolveTemplate holes (frontier + keys.length) t
  if hlc : result.2.bvarsBelow 0 = true then
    some ⟨result.1, result.2,
      ⟨holes, holeTable_unique (List.nodup_dedup _), holeTable_scope,
        resolveTemplate_fits t holes _ (fun _ hn =>
          ⟨_, lookup_holeTable (List.mem_dedup.mpr hn)⟩),
        (Ty.bvarsBelow_iff _).mp hlc⟩⟩
  else none

structure CheckedAnnotation (t : Template) (target : Ty) where
  subst : Subst
  substLC : ∀ entry ∈ subst, entry.2.IsLC
  completion : Completion 0 (t.map subst.onTy) (subst.onTy target)

/-- The repeated-name constraint participates in unification, rather than a
post-hoc comparison of independent holes. The reported assignment is proved to
match the substituted authored template. -/
def checkAnnotation (frontier : Nat) (t : Template) (target : Ty)
    (htarget : target.IsLC) : Option (CheckedAnnotation t target) := do
  let allocated ← allocate frontier t
  let solved ← unifyCore allocated.ty target
  let hlc := solved.property.lc allocated.completion.regular htarget
  let completion := allocated.completion.onSubst solved.val hlc
  have heq := solved.property.unifies
  pure ⟨solved.val, hlc, heq ▸ completion⟩

private theorem lookup_mem {holes : HoleAssignment} {name : String} {ty : Ty}
    (h : LookupList.get? holes name = some ty) : (name, ty) ∈ holes := by
  induction holes with
  | nil => cases h
  | cons entry rest ih =>
    rcases entry with ⟨key, value⟩
    simp only [LookupList.get?] at h
    split_ifs at h with hk
    · simp_all
    · exact List.mem_cons_of_mem _ (ih h)

private theorem subst_congr_freeVars {ty : Ty} {S U : Subst}
    (h : ∀ v ∈ ty.freeVars, U.onTy (.fvar v) = S.onTy (.fvar v)) : U.onTy ty = S.onTy ty := by
  induction ty using Ty.rec_strong with
  | prim p => simp only [Subst.onTy_prim]
  | bvar i => simp only [Subst.onTy_bvar]
  | fvar v => exact h v (by simp [Ty.freeVars])
  | arrow a b iha ihb =>
    simp only [Subst.onTy_arrow]
    exact congrArg₂ Ty.arrow
      (iha (fun v hv => h v (by simp [Ty.freeVars, hv])))
      (ihb (fun v hv => h v (by simp [Ty.freeVars, hv])))
  | customTy name args ih =>
    simp only [Subst.onTy_customTy]
    congr 1
    exact List.map_congr_left (fun ty ht => ih ty ht (fun v hv => h v (TyList.mem_freeVars_of_mem ht hv)))

mutual
theorem Template.names_map (t : Template) (f : Ty → Ty) : (t.map f).names = t.names := by
  cases t with
  | fixed | hole | named => rfl
  | arrow a b => simp only [Template.map, Template.names, a.names_map, b.names_map]
  | custom name args => exact templateNames_map args f
theorem templateNames_map (ts : List Template) (f : Ty → Ty) :
    templateNames (mapTemplates f ts) = templateNames ts := by
  cases ts with
  | nil => rfl
  | cons t ts => simp only [mapTemplates, templateNames, t.names_map, templateNames_map ts f]
end

mutual
private theorem anonymous_targets (t : Template) {S0 : Subst} {target : Ty} {holes allocated : HoleAssignment}
    (h : (t.map S0.onTy).Fits holes target) (hlc : target.IsLC)
    (hc : ∀ name ∈ t.names, ∃ ty, LookupList.get? allocated name = some ty) (Φ : Nat) :
    ∃ ts : List Ty, (resolveTemplate allocated Φ t).1 = Φ + ts.length ∧
      (∀ ty ∈ ts, ty.IsLC) ∧ ∀ U : Subst,
      (∀ v ∈ t.rigidVars, U.onTy (.fvar v) = S0.onTy (.fvar v)) →
      (∀ name ∈ t.names, (LookupList.get? allocated name).map U.onTy = LookupList.get? holes name) →
      (∀ i (hi : i < ts.length), U.onTy (.fvar (Φ + i)) = ts[i]) →
      U.onTy (resolveTemplate allocated Φ t).2 = target := by
  cases t with
  | fixed ty =>
    cases h
    exact ⟨[], rfl, by simp, fun _ hr _ _ => subst_congr_freeVars hr⟩
  | hole =>
    refine ⟨[target], rfl, by simpa using hlc, ?_⟩
    intro U _ _ hb
    simpa only [Nat.add_zero] using hb 0 (by simp)
  | named name =>
    cases h with
    | named ht =>
      obtain ⟨ty, ha⟩ := hc name (by simp [Template.names])
      refine ⟨[], rfl, by simp, ?_⟩
      intro U _ hn _
      have heq := hn name (by simp [Template.names])
      simp only [ha, ht, Option.map_some, Option.some.injEq] at heq
      simpa only [resolveTemplate, ha, Option.getD_some] using heq
  | arrow a b =>
    cases h with
    | arrow ha hb =>
      cases hlc with
      | arrow hla hlb =>
        obtain ⟨as, halen, halc, haeq⟩ := anonymous_targets a ha hla
          (fun name hn => hc name (List.mem_append_left _ hn)) Φ
        obtain ⟨bs, hblen, hblc, hbeq⟩ := anonymous_targets b hb hlb
          (fun name hn => hc name (List.mem_append_right _ hn)) (resolveTemplate allocated Φ a).1
        refine ⟨as ++ bs, ?_, ?_, ?_⟩
        · change (resolveTemplate allocated (resolveTemplate allocated Φ a).1 b).1 = _
          rw [hblen, halen, List.length_append, Nat.add_assoc]
        · intro ty ht; exact (List.mem_append.mp ht).elim (halc ty) (hblc ty)
        · intro U hr hn hblock
          simp only [resolveTemplate, Subst.onTy_arrow]
          congr 1
          · apply haeq U (fun v hv => hr v (List.mem_append_left _ hv))
              (fun name hm => hn name (List.mem_append_left _ hm))
            intro i hi
            have heq := hblock i (by simp only [List.length_append]; omega)
            rwa [List.getElem_append_left hi] at heq
          · apply hbeq U (fun v hv => hr v (List.mem_append_right _ hv))
              (fun name hm => hn name (List.mem_append_right _ hm))
            intro i hi
            have heq := hblock (as.length + i) (by simp only [List.length_append]; omega)
            rw [List.getElem_append_right (by omega)] at heq
            simpa only [halen, Nat.add_assoc, Nat.add_sub_cancel_left] using heq
  | custom name templates =>
    cases h with
    | custom hs =>
      cases hlc with
      | customTy hlcs =>
        obtain ⟨ts, hlen, hlc, heq⟩ := anonymous_targets_list templates hs hlcs hc Φ
        refine ⟨ts, hlen, hlc, ?_⟩
        intro U hr hn hb
        simp only [resolveTemplate, Subst.onTy_customTy, heq U hr hn hb]
private theorem anonymous_targets_list (templates : List Template) {S0 : Subst} {targets : List Ty}
    {holes allocated : HoleAssignment}
    (h : List.Forall₂ (Template.Fits holes) (mapTemplates S0.onTy templates) targets)
    (hlc : ∀ ty ∈ targets, ty.IsLC)
    (hc : ∀ name ∈ templateNames templates, ∃ ty, LookupList.get? allocated name = some ty) (Φ : Nat) :
    ∃ ts : List Ty, (resolveTemplates allocated Φ templates).1 = Φ + ts.length ∧
      (∀ ty ∈ ts, ty.IsLC) ∧ ∀ U : Subst,
      (∀ v ∈ templateRigidVars templates, U.onTy (.fvar v) = S0.onTy (.fvar v)) →
      (∀ name ∈ templateNames templates,
        (LookupList.get? allocated name).map U.onTy = LookupList.get? holes name) →
      (∀ i (hi : i < ts.length), U.onTy (.fvar (Φ + i)) = ts[i]) →
      (resolveTemplates allocated Φ templates).2.map U.onTy = targets := by
  cases templates with
  | nil => cases h; exact ⟨[], rfl, by simp, by simp [resolveTemplates]⟩
  | cons t templates =>
    cases h with
    | cons hh ht =>
      obtain ⟨as, halen, halc, haeq⟩ := anonymous_targets t hh (hlc _ List.mem_cons_self)
        (fun name hn => hc name (List.mem_append_left _ hn)) Φ
      obtain ⟨bs, hblen, hblc, hbeq⟩ := anonymous_targets_list templates ht
        (fun ty ht => hlc ty (List.mem_cons_of_mem _ ht))
        (fun name hn => hc name (List.mem_append_right _ hn)) (resolveTemplate allocated Φ t).1
      refine ⟨as ++ bs, ?_, ?_, ?_⟩
      · change (resolveTemplates allocated (resolveTemplate allocated Φ t).1 templates).1 = _
        rw [hblen, halen, List.length_append, Nat.add_assoc]
      · intro ty ht; exact (List.mem_append.mp ht).elim (halc ty) (hblc ty)
      · intro U hr hn hblock
        simp only [resolveTemplates, List.map_cons]
        congr 1
        · apply haeq U (fun v hv => hr v (List.mem_append_left _ hv))
            (fun name hm => hn name (List.mem_append_left _ hm))
          intro i hi
          have heq := hblock i (by simp only [List.length_append]; omega)
          rwa [List.getElem_append_left hi] at heq
        · apply hbeq U (fun v hv => hr v (List.mem_append_right _ hv))
            (fun name hm => hn name (List.mem_append_right _ hm))
          intro i hi
          have heq := hblock (as.length + i) (by simp only [List.length_append]; omega)
          rw [List.getElem_append_right (by omega)] at heq
          simpa only [halen, Nat.add_assoc, Nat.add_sub_cancel_left] using heq
end

/-- Factor a declarative annotation match through one local named block plus
independent anonymous allocations. Repeated names share that one block entry.
Earlier ambient behavior is preserved, even if targets mention allocated IDs. -/
theorem Template.Fits.allocate_override_source {t : Template} {target : Ty} {S0 : Subst}
    {holes : HoleAssignment} (h : (t.map S0.onTy).Fits holes target)
    (hlc : target.IsLC) (hh : holes.Scoped 0) (hS0 : ∀ p ∈ S0, p.2.IsLC) (Φ : Nat)
    (hrigid : ∀ v ∈ t.rigidVars, v < Φ) :
    ∃ U : Subst, (∀ p ∈ U, p.2.IsLC) ∧ Subst.AgreesBelow Φ S0 U ∧
      U.onTy (resolveTemplate (holeTable t.names.dedup Φ) (Φ + t.names.dedup.length) t).2 = target ∧
      ∀ name ∈ t.names,
        LookupList.get? (HoleAssignment.map U.onTy (holeTable t.names.dedup Φ)) name =
          LookupList.get? holes name := by
  let keys := t.names.dedup
  let allocated := holeTable keys Φ
  have hcover : ∀ name ∈ t.names, ∃ ty, LookupList.get? holes name = some ty := by
    simpa only [Template.names_map] using h.covers
  have halloc : ∀ name ∈ t.names, ∃ ty, LookupList.get? allocated name = some ty :=
    fun name hn => ⟨_, lookup_holeTable (List.mem_dedup.mpr hn)⟩
  let namedTargets := keys.map (fun name => (LookupList.get? holes name).getD (.prim .unit))
  have htargets : ∀ ty ∈ namedTargets, ty.IsLC := by
    intro ty ht
    obtain ⟨name, hn, rfl⟩ := List.mem_map.mp ht
    obtain ⟨value, hv⟩ := hcover name (List.mem_dedup.mp hn)
    simp only [hv, Option.getD_some]
    apply hh (name, value)
    exact lookup_mem hv
  obtain ⟨ts, hlen, hts, htemplate⟩ := anonymous_targets t h hlc halloc (Φ + keys.length)
  obtain ⟨U, hUlc, hag, hb⟩ := Subst.override_block hS0 Φ (namedTargets ++ ts)
    (fun ty ht => (List.mem_append.mp ht).elim (htargets ty) (hts ty))
  have hn : ∀ name ∈ t.names,
      (LookupList.get? allocated name).map U.onTy = LookupList.get? holes name := by
    intro name hm
    have hk : name ∈ keys := List.mem_dedup.mpr hm
    obtain ⟨value, hv⟩ := hcover name hm
    have hi : keys.idxOf name < namedTargets.length := by
      simpa only [namedTargets, List.length_map] using List.idxOf_lt_length_iff.mpr hk
    have heq := hb (keys.idxOf name) (by rw [List.length_append]; omega)
    rw [List.getElem_append_left hi] at heq
    simp only [namedTargets, List.getElem_map,
      List.getElem_idxOf (List.idxOf_lt_length_iff.mpr hk), hv, Option.getD_some] at heq
    simpa only [allocated, lookup_holeTable hk, Option.map_some, hv] using congrArg some heq
  refine ⟨U, hUlc, hag, htemplate U (fun v hv => (hag v (hrigid v hv)).symm) hn ?_, ?_⟩
  · intro i hi
    have heq := hb (keys.length + i) (by simp only [List.length_append, namedTargets, List.length_map]; omega)
    rw [List.getElem_append_right (by simp only [namedTargets, List.length_map]; omega)] at heq
    simpa only [namedTargets, List.length_map, Nat.add_sub_cancel_left, Nat.add_assoc] using heq
  · intro name hm
    rw [HoleAssignment.lookup_map]
    exact hn name hm

mutual
theorem resolveTemplate_bounds (t : Template) (holes : HoleAssignment) (Φ : Nat) :
    Φ ≤ (resolveTemplate holes Φ t).1 ∧
      ((∀ v ∈ t.rigidVars, v < Φ) →
      (∀ name ∈ t.names, ∃ ty, LookupList.get? holes name = some ty ∧ Ty.BelowFvars Φ ty) →
      Ty.BelowFvars (resolveTemplate holes Φ t).1 (resolveTemplate holes Φ t).2) := by
  cases t with
  | fixed ty => exact ⟨Nat.le_refl _, fun hr _ => Ty.BelowFvars.of_freeVars_lt hr⟩
  | hole => exact ⟨Nat.le_succ _, fun _ _ => .fvar (Nat.lt_succ_self _)⟩
  | named name =>
    refine ⟨Nat.le_refl _, ?_⟩
    intro _ hn
    obtain ⟨ty, hl, hb⟩ := hn name (by simp [Template.names])
    simpa only [resolveTemplate, hl, Option.getD_some] using hb
  | arrow a b =>
    obtain ⟨hale, hab⟩ := resolveTemplate_bounds a holes Φ
    obtain ⟨hble, hbb⟩ := resolveTemplate_bounds b holes (resolveTemplate holes Φ a).1
    refine ⟨Nat.le_trans hale hble, ?_⟩
    intro hr hn
    apply Ty.BelowFvars.arrow
    · exact Ty.BelowFvars.mono hble (hab (fun v hv => hr v (List.mem_append_left _ hv))
        (fun name hm => hn name (List.mem_append_left _ hm)))
    · apply hbb (fun v hv => Nat.lt_of_lt_of_le (hr v (List.mem_append_right _ hv)) hale)
      intro name hm
      obtain ⟨ty, hl, hb⟩ := hn name (List.mem_append_right _ hm)
      exact ⟨ty, hl, Ty.BelowFvars.mono hale hb⟩
  | custom name args =>
    obtain ⟨hle, hb⟩ := resolveTemplates_bounds args holes Φ
    exact ⟨hle, fun hr hn => .customTy (hb hr hn)⟩
theorem resolveTemplates_bounds (ts : List Template) (holes : HoleAssignment) (Φ : Nat) :
    Φ ≤ (resolveTemplates holes Φ ts).1 ∧
      ((∀ v ∈ templateRigidVars ts, v < Φ) →
      (∀ name ∈ templateNames ts, ∃ ty, LookupList.get? holes name = some ty ∧ Ty.BelowFvars Φ ty) →
      ∀ ty ∈ (resolveTemplates holes Φ ts).2, Ty.BelowFvars (resolveTemplates holes Φ ts).1 ty) := by
  cases ts with
  | nil => exact ⟨Nat.le_refl _, by simp [resolveTemplates]⟩
  | cons t ts =>
    obtain ⟨hhle, hhb⟩ := resolveTemplate_bounds t holes Φ
    obtain ⟨htle, htb⟩ := resolveTemplates_bounds ts holes (resolveTemplate holes Φ t).1
    refine ⟨Nat.le_trans hhle htle, ?_⟩
    intro hr hn ty hty
    rcases List.mem_cons.mp hty with rfl | hty
    · exact Ty.BelowFvars.mono htle (hhb (fun v hv => hr v (List.mem_append_left _ hv))
        (fun name hm => hn name (List.mem_append_left _ hm)))
    · apply htb (fun v hv => Nat.lt_of_lt_of_le (hr v (List.mem_append_right _ hv)) hhle) ?_ ty hty
      intro name hm
      obtain ⟨ty, hl, hb⟩ := hn name (List.mem_append_right _ hm)
      exact ⟨ty, hl, Ty.BelowFvars.mono hhle hb⟩
end

theorem Template.allocate_fits (t : Template) (Φ : Nat) :
    t.Fits (t.allocationHoles Φ) (t.allocate Φ).2 :=
  resolveTemplate_fits t _ _ (fun _ hn => ⟨_, lookup_holeTable (List.mem_dedup.mpr hn)⟩)

theorem Template.allocate_bounds (t : Template) (Φ : Nat) :
    Φ ≤ (t.allocate Φ).1 ∧ ((∀ v ∈ t.rigidVars, v < Φ) →
      Ty.BelowFvars (t.allocate Φ).1 (t.allocate Φ).2) := by
  have hb := resolveTemplate_bounds t (t.allocationHoles Φ) (Φ + t.names.dedup.length)
  refine ⟨Nat.le_trans (Nat.le_add_right _ _) hb.1, ?_⟩
  intro hr
  apply hb.2 (fun v hv => by have := hr v hv; omega)
  intro name hn
  refine ⟨_, lookup_holeTable (List.mem_dedup.mpr hn), .fvar ?_⟩
  have := List.idxOf_lt_length_iff.mpr (List.mem_dedup.mpr hn)
  omega

mutual
theorem resolveTemplate_lc (t : Template) (holes : HoleAssignment) (Φ : Nat)
    (hs : t.WellScoped 0)
    (hh : ∀ name ∈ t.names, ∃ ty, LookupList.get? holes name = some ty ∧ ty.IsLC) :
    (resolveTemplate holes Φ t).2.IsLC := by
  cases t with
  | fixed ty => cases hs with | fixed h => exact h
  | hole => exact .fvar
  | named name =>
    obtain ⟨ty, hl, hb⟩ := hh name (by simp [Template.names])
    simpa only [resolveTemplate, hl, Option.getD_some] using hb
  | arrow a b =>
    cases hs with
    | arrow ha hb =>
      exact .arrow (resolveTemplate_lc a holes Φ ha (fun name hn => hh name (List.mem_append_left _ hn)))
        (resolveTemplate_lc b holes _ hb (fun name hn => hh name (List.mem_append_right _ hn)))
  | custom name args =>
    cases hs with
    | custom hs => exact .customTy (resolveTemplates_lc args holes Φ hs hh)
theorem resolveTemplates_lc (ts : List Template) (holes : HoleAssignment) (Φ : Nat)
    (hs : ∀ t ∈ ts, t.WellScoped 0)
    (hh : ∀ name ∈ templateNames ts, ∃ ty, LookupList.get? holes name = some ty ∧ ty.IsLC) :
    ∀ ty ∈ (resolveTemplates holes Φ ts).2, ty.IsLC := by
  cases ts with
  | nil => simp [resolveTemplates]
  | cons t ts =>
    intro ty ht
    rcases List.mem_cons.mp ht with rfl | ht
    · exact resolveTemplate_lc t holes Φ (hs t List.mem_cons_self)
        (fun name hn => hh name (List.mem_append_left _ hn))
    · exact resolveTemplates_lc ts holes _ (fun t ht => hs t (List.mem_cons_of_mem _ ht))
        (fun name hn => hh name (List.mem_append_right _ hn)) ty ht
end

theorem Template.allocate_lc {t : Template} (hs : t.WellScoped 0) (Φ : Nat) : (t.allocate Φ).2.IsLC :=
  resolveTemplate_lc t _ _ hs (fun _ hn =>
    ⟨_, lookup_holeTable (List.mem_dedup.mpr hn), .fvar⟩)

mutual
theorem Template.WellScoped.of_subst {t : Template} {S : Subst} (h : (t.map S.onTy).WellScoped n) :
    t.WellScoped n := by
  cases t with
  | fixed ty => cases h with | fixed hb => exact .fixed (ContainsBvarsUpTo.of_substFvars hb)
  | hole => exact .hole
  | named => exact .named
  | arrow a b => cases h with | arrow ha hb => exact .arrow ha.of_subst hb.of_subst
  | custom name args => cases h with | custom hs => exact .custom (scopeTemplates_of_subst args hs)
theorem scopeTemplates_of_subst (ts : List Template) {S : Subst}
    (h : ∀ t ∈ mapTemplates S.onTy ts, t.WellScoped n) : ∀ t ∈ ts, t.WellScoped n := by
  cases ts with
  | nil => simp
  | cons t ts =>
    intro ty ht
    rcases List.mem_cons.mp ht with rfl | ht
    · exact Template.WellScoped.of_subst (h _ List.mem_cons_self)
    · exact scopeTemplates_of_subst ts (fun ty ht => h ty (List.mem_cons_of_mem _ ht)) ty ht
end

theorem Template.Fits.allocate_lc_source {t : Template} {target : Ty} {S : Subst}
    (h : (t.map S.onTy).Fits holes target) (hlc : target.IsLC) (Φ : Nat) :
    (t.allocate Φ).2.IsLC := Template.allocate_lc (h.wellScoped hlc).of_subst Φ

mutual
theorem resolveTemplate_avoid (t : Template) (holes : HoleAssignment) (Φ : Nat)
    (hw : w < Φ) (hs : w ∉ t.rigidVars)
    (hh : ∀ name ∈ t.names, ∃ ty, LookupList.get? holes name = some ty ∧ w ∉ ty.freeVars) :
    w ∉ (resolveTemplate holes Φ t).2.freeVars := by
  cases t with
  | fixed ty => exact hs
  | hole => simp only [resolveTemplate, Ty.freeVars, List.mem_singleton]; omega
  | named name =>
    obtain ⟨ty, hl, hb⟩ := hh name (by simp [Template.names])
    simpa only [resolveTemplate, hl, Option.getD_some] using hb
  | arrow a b =>
    simp only [Template.rigidVars, List.mem_append, not_or] at hs
    have hle := (resolveTemplate_bounds a holes Φ).1
    have ha := resolveTemplate_avoid a holes Φ hw hs.1
      (fun name hn => hh name (List.mem_append_left _ hn))
    have hb := resolveTemplate_avoid b holes _ (Nat.lt_of_lt_of_le hw hle) hs.2
      (fun name hn => hh name (List.mem_append_right _ hn))
    simpa only [resolveTemplate, Ty.freeVars, List.mem_dedup, List.mem_append, not_or] using And.intro ha hb
  | custom name args =>
    exact TyList.not_mem_freeVars_iff.mpr (resolveTemplates_avoid args holes Φ hw hs hh)
theorem resolveTemplates_avoid (ts : List Template) (holes : HoleAssignment) (Φ : Nat)
    (hw : w < Φ) (hs : w ∉ templateRigidVars ts)
    (hh : ∀ name ∈ templateNames ts, ∃ ty, LookupList.get? holes name = some ty ∧ w ∉ ty.freeVars) :
    ∀ ty ∈ (resolveTemplates holes Φ ts).2, w ∉ ty.freeVars := by
  cases ts with
  | nil => simp [resolveTemplates]
  | cons t ts =>
    simp only [templateRigidVars, List.mem_append, not_or] at hs
    have hle := (resolveTemplate_bounds t holes Φ).1
    intro ty ht
    rcases List.mem_cons.mp ht with rfl | ht
    · exact resolveTemplate_avoid t holes Φ hw hs.1
        (fun name hn => hh name (List.mem_append_left _ hn))
    · exact resolveTemplates_avoid ts holes _ (Nat.lt_of_lt_of_le hw hle) hs.2
        (fun name hn => hh name (List.mem_append_right _ hn)) ty ht
end

theorem Template.allocate_avoid {t : Template} {Φ w : Nat}
    (hw : w < Φ) (hs : w ∉ t.rigidVars) : w ∉ (t.allocate Φ).2.freeVars := by
  apply resolveTemplate_avoid t _ _ (Nat.lt_of_lt_of_le hw (Nat.le_add_right _ _)) hs
  intro name hn
  refine ⟨_, lookup_holeTable (List.mem_dedup.mpr hn), ?_⟩
  simp only [Ty.freeVars, List.mem_singleton]
  omega
end PartialCore
