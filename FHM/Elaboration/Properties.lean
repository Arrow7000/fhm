import FHM.Elaboration.Infer

private theorem override_freshVars_getElem? {Φ n i : Nat} (hi : i < n) :
    (freshVars Φ n)[i]? = some (Φ + i) := by
  simp only [freshVars, List.getElem?_map, List.getElem?_range hi, Option.map_some]

/-- Assign a freshly allocated block arbitrary LC targets while preserving an
existing substitution on every earlier variable. Targets may mention the block. -/
theorem Subst.override_block {S0 : Subst} (hS0 : ∀ p ∈ S0, p.2.IsLC)
    (Φ : Nat) (ts : List Ty) (hts : ∀ t ∈ ts, t.IsLC) :
    ∃ U : Subst, (∀ p ∈ U, p.2.IsLC) ∧ Subst.AgreesBelow Φ S0 U ∧
      ∀ i (hi : i < ts.length), U.onTy (.fvar (Φ + i)) = ts[i] := by
  obtain ⟨W, hWge, hWfresh⟩ := exists_fresh_block
    (S0.map Prod.fst ++ S0.flatMap (fun p => p.2.freeVars) ++ ts.flatMap Ty.freeVars)
    Φ ts.length
  let A : Subst := (freshVars Φ ts.length).zip ((freshVars W ts.length).map Ty.fvar)
  let C : Subst := (freshVars W ts.length).zip ts
  let U : Subst := A ++ S0 ++ C
  have hUonTy : ∀ x, U.onTy x = C.onTy (S0.onTy (A.onTy x)) := by
    intro x; exact (Subst.onTy_append _ _ _).trans (congrArg C.onTy (Subst.onTy_append _ _ _))
  have hkeys : ∀ w ∈ freshVars W ts.length, w ∉ S0.map Prod.fst := by
    intro w hw hc
    have := freshVars_ge w hw
    have := hWfresh w (List.mem_append_left _ (List.mem_append_left _ hc))
    omega
  have hranges : ∀ w ∈ freshVars W ts.length, ∀ p ∈ S0, w ∉ p.2.freeVars := by
    intro w hw p hp hc
    have := freshVars_ge w hw
    have := hWfresh w (List.mem_append_left _ (List.mem_append_right _
      (List.mem_flatMap.mpr ⟨p, hp, hc⟩)))
    omega
  have htargets : ∀ t ∈ ts, Ty.BelowFvars W t := by
    intro t ht
    apply Ty.BelowFvars.of_freeVars_lt
    intro v hv
    exact hWfresh v (List.mem_append_right _ (List.mem_flatMap.mpr ⟨t, ht, hv⟩))
  refine ⟨U, ?_, ?_, ?_⟩
  · intro p hp
    rcases List.mem_append.mp hp with hp | hp
    · rcases List.mem_append.mp hp with hp | hp
      · obtain ⟨x, _, heq⟩ := List.mem_map.mp (List.of_mem_zip hp).2
        rw [← heq]; exact .fvar
      · exact hS0 p hp
    · exact hts p.2 (List.of_mem_zip hp).2
  · intro v hv
    symm
    rw [hUonTy]
    have hA : A.onTy (.fvar v) = .fvar v := by
      apply Ty.substFvars_eq_self_of_no_key
      intro p hp hc
      simp only [Ty.freeVars, List.mem_singleton] at hc
      have := freshVars_ge p.1 (List.of_mem_zip hp).1
      omega
    rw [hA]
    apply Ty.substFvars_eq_self_of_no_key
    intro p hp hc
    have hw := (List.of_mem_zip hp).1
    exact Subst.not_mem_onTy_freeVars (hranges p.1 hw)
      (by simp only [Ty.freeVars, List.mem_singleton]; have := freshVars_ge p.1 hw; omega) hc
  · intro i hi
    rw [hUonTy]
    have hA : A.onTy (.fvar (Φ + i)) = .fvar (W + i) := by
      apply Ty.substFvars_zip_fvar_eq' freshVars_nodup (override_freshVars_getElem? hi)
      · rw [List.getElem?_map, override_freshVars_getElem? hi]; rfl
      · intro x hx hc
        simp only [Ty.freeVars, List.mem_singleton] at hc
        have := freshVars_lt x hx
        omega
    rw [hA]
    have hS : S0.onTy (.fvar (W + i)) = .fvar (W + i) := by
      apply Ty.substFvars_eq_self_of_no_key
      intro p hp hc
      simp only [Ty.freeVars, List.mem_singleton] at hc
      apply hkeys (W + i)
      · simp only [freshVars, List.mem_map, List.mem_range]
        exact ⟨i, hi, rfl⟩
      · rw [← hc]; exact List.mem_map.mpr ⟨p, hp, rfl⟩
    rw [hS]
    apply Ty.substFvars_zip_fvar_eq' freshVars_nodup (override_freshVars_getElem? hi)
      (List.getElem?_eq_getElem hi)
    intro w hw hc
    have := freshVars_ge w hw
    have := (htargets ts[i] (List.getElem_mem hi)).mem_lt w hc
    omega

namespace Elaboration

mutual
private theorem Template.Fits.hole_targets {template : Template} {target : Ty}
    (h : template.Fits target) (hlc : target.IsLC) (Φ : Nat) :
    ∃ ts : List Ty, (template.allocate Φ).1 = Φ + ts.length ∧
      (∀ t ∈ ts, t.IsLC) ∧ ∀ U : Subst,
      (∀ v ∈ template.rigidVars, U.onTy (.fvar v) = .fvar v) →
      (∀ i (hi : i < ts.length), U.onTy (.fvar (Φ + i)) = ts[i]) →
      U.onTy (template.allocate Φ).2 = target := by
  cases h with
  | fixed =>
    exact ⟨[], rfl, by simp, fun _ hr _ => Subst.onTy_eq_self_of_fixes hr⟩
  | hole =>
    refine ⟨[target], rfl, ?_, ?_⟩
    · simpa using hlc
    · intro U _ hb
      simpa only [Nat.add_zero] using hb 0 (by simp)
  | @arrow a ta b tb ha hb =>
    cases hlc with
    | arrow hlca hlcb =>
      obtain ⟨as, halen, halc, haeq⟩ := ha.hole_targets hlca Φ
      obtain ⟨bs, hblen, hblc, hbeq⟩ := hb.hole_targets hlcb (a.allocate Φ).1
      refine ⟨as ++ bs, ?_, ?_, ?_⟩
      · change (b.allocate (a.allocate Φ).1).1 = Φ + (as ++ bs).length
        rw [hblen, halen, List.length_append, Nat.add_assoc]
      · intro t ht; exact (List.mem_append.mp ht).elim (halc t) (hblc t)
      · intro U hr hblock
        simp only [Template.allocate, Subst.onTy_arrow]
        congr 1
        · apply haeq U (fun v hv => hr v (List.mem_append_left _ hv))
          intro i hi
          have heq := hblock i (by simp only [List.length_append]; omega)
          rwa [List.getElem_append_left hi] at heq
        · apply hbeq U (fun v hv => hr v (List.mem_append_right _ hv))
          intro i hi
          have heq := hblock (as.length + i) (by simp only [List.length_append]; omega)
          rw [List.getElem_append_right (by omega)] at heq
          simpa only [halen, Nat.add_assoc, Nat.add_sub_cancel_left] using heq
  | @custom templates targets name h =>
    cases hlc with
    | customTy hlcs =>
      obtain ⟨ts, hlen, hlc, heq⟩ := hole_targets_list h hlcs Φ
      refine ⟨ts, hlen, hlc, ?_⟩
      intro U hr hb
      simp only [Template.allocate, Subst.onTy_customTy, heq U hr hb]
private theorem hole_targets_list {templates : List Template} {targets : List Ty}
    (h : List.Forall₂ Template.Fits templates targets)
    (hlc : ∀ t ∈ targets, t.IsLC) (Φ : Nat) :
    ∃ ts : List Ty, (allocateList Φ templates).1 = Φ + ts.length ∧
      (∀ t ∈ ts, t.IsLC) ∧ ∀ U : Subst,
      (∀ v ∈ rigidVarsList templates, U.onTy (.fvar v) = .fvar v) →
      (∀ i (hi : i < ts.length), U.onTy (.fvar (Φ + i)) = ts[i]) →
      (allocateList Φ templates).2.map U.onTy = targets := by
  cases h with
  | nil => exact ⟨[], rfl, by simp, by simp [allocateList]⟩
  | @cons template target templates targets hh ht =>
    obtain ⟨as, halen, halc, haeq⟩ := hh.hole_targets (hlc target List.mem_cons_self) Φ
    obtain ⟨bs, hblen, hblc, hbeq⟩ := hole_targets_list ht
      (fun t ht => hlc t (List.mem_cons_of_mem _ ht)) (template.allocate Φ).1
    refine ⟨as ++ bs, ?_, ?_, ?_⟩
    · change (allocateList (template.allocate Φ).1 templates).1 = Φ + (as ++ bs).length
      rw [hblen, halen, List.length_append, Nat.add_assoc]
    · intro t ht; exact (List.mem_append.mp ht).elim (halc t) (hblc t)
    · intro U hr hblock
      simp only [allocateList, List.map_cons]
      congr 1
      · apply haeq U (fun v hv => hr v (List.mem_append_left _ hv))
        intro i hi
        have heq := hblock i (by simp only [List.length_append]; omega)
        rwa [List.getElem_append_left hi] at heq
      · apply hbeq U (fun v hv => hr v (List.mem_append_right _ hv))
        intro i hi
        have heq := hblock (as.length + i) (by simp only [List.length_append]; omega)
        rw [List.getElem_append_right (by omega)] at heq
        simpa only [halen, Nat.add_assoc, Nat.add_sub_cancel_left] using heq
end

/-- Every LC template target is obtainable without changing the ambient
substitution below the allocation frontier, even when the target mentions the
new block. Authored fixed variables stay fixed. -/
theorem Template.Fits.allocate_override {template : Template} {target : Ty}
    (h : template.Fits target) (hlc : target.IsLC) {S0 : Subst}
    (hS0 : ∀ p ∈ S0, p.2.IsLC) (Φ : Nat)
    (hrigid : ∀ v ∈ template.rigidVars, v < Φ)
    (hfix : ∀ v ∈ template.rigidVars, S0.onTy (.fvar v) = .fvar v) :
    ∃ U : Subst, (∀ p ∈ U, p.2.IsLC) ∧ Subst.AgreesBelow Φ S0 U ∧
      U.onTy (template.allocate Φ).2 = target := by
  obtain ⟨ts, _, hts, htemplate⟩ := h.hole_targets hlc Φ
  obtain ⟨U, hUlc, hUagree, hUblock⟩ := Subst.override_block hS0 Φ ts hts
  exact ⟨U, hUlc, hUagree, htemplate U
    (fun v hv => (hUagree v (hrigid v hv)).symm.trans (hfix v hv)) hUblock⟩

end Elaboration


namespace Elaboration

mutual
private theorem Template.allocate_bounds (template : Template) (frontier : Nat) :
    frontier ≤ (template.allocate frontier).1 ∧
      ((∀ v ∈ template.rigidVars, v < frontier) →
        Ty.BelowFvars (template.allocate frontier).1 (template.allocate frontier).2) := by
  cases template with
  | fixed ty => exact ⟨Nat.le_refl _, Ty.BelowFvars.of_freeVars_lt⟩
  | hole => exact ⟨Nat.le_succ _, fun _ => .fvar (Nat.lt_succ_self _)⟩
  | arrow a b =>
    obtain ⟨hale, hab⟩ := a.allocate_bounds frontier
    obtain ⟨hble, hbb⟩ := b.allocate_bounds (a.allocate frontier).1
    refine ⟨hale.trans hble, fun hr => .arrow ?_ ?_⟩
    · exact (hab (fun v hv => hr v (List.mem_append_left _ hv))).mono hble
    · exact hbb (fun v hv => Nat.lt_of_lt_of_le (hr v (List.mem_append_right _ hv)) hale)
  | custom name args =>
    obtain ⟨hle, hb⟩ := allocateList_bounds args frontier
    exact ⟨hle, fun hr => .customTy (hb hr)⟩
private theorem allocateList_bounds (templates : List Template) (frontier : Nat) :
    frontier ≤ (allocateList frontier templates).1 ∧
      ((∀ v ∈ rigidVarsList templates, v < frontier) →
        ∀ t ∈ (allocateList frontier templates).2, Ty.BelowFvars (allocateList frontier templates).1 t) := by
  cases templates with
  | nil => exact ⟨Nat.le_refl _, fun _ _ ht => by cases ht⟩
  | cons template rest =>
    obtain ⟨hhle, hhb⟩ := template.allocate_bounds frontier
    obtain ⟨htle, htb⟩ := allocateList_bounds rest (template.allocate frontier).1
    refine ⟨hhle.trans htle, ?_⟩
    intro hr t ht
    rcases List.mem_cons.mp ht with rfl | ht
    · exact (hhb (fun v hv => hr v (List.mem_append_left _ hv))).mono htle
    · exact htb (fun v hv => Nat.lt_of_lt_of_le (hr v (List.mem_append_right _ hv)) hhle) t ht
end

theorem Seed.frontier_le (h : Seed K frontier ann param initial) : frontier ≤ initial := by
  cases h with
  | absent => omega
  | @annotated next ty template heq _ _ =>
    have hle := (template.allocate_bounds frontier).1
    rwa [heq] at hle

theorem Seed.belowFvars (h : Seed K frontier ann param initial)
    (hK : ∀ k ∈ K, k < frontier) : Ty.BelowFvars initial param := by
  cases h with
  | absent => exact .fvar (by omega)
  | @annotated next ty template heq _ hr =>
    have hb := (template.allocate_bounds frontier).2 (fun v hv => hK v (hr v hv))
    rwa [heq] at hb

theorem LetCheck.frontier_le (h : LetCheck K frontier ty ann next subst) : frontier ≤ next := by
  cases h with
  | absent => omega
  | hole => omega
  | @template next expected subst sourceTemplate heq _ _ _ =>
    have hle := (sourceTemplate.allocate_bounds frontier).1
    rwa [heq] at hle

theorem LetCheck.belowFvars (h : LetCheck K frontier ty ann next subst)
    (hty : Ty.BelowFvars frontier ty) (hK : ∀ k ∈ K, k < frontier) :
    ∀ p ∈ subst, Ty.BelowFvars next p.2 := by
  cases h with
  | absent => simp
  | hole => simp
  | @template next expected subst sourceTemplate heq _ hr hu =>
    have hb := (sourceTemplate.allocate_bounds frontier).2 (fun v hv => hK v (hr v hv))
    rw [heq] at hb
    have hle := (sourceTemplate.allocate_bounds frontier).1
    rw [heq] at hle
    exact hu.unifies.belowFvars (hty.mono hle) hb

theorem _root_.Infer.frontier_le (h : Infer K frontier ctx input next subst output ty) : frontier ≤ next := by
  induction h with
  | backend _ h _ _ _ => exact CoreBackend.Infer.frontier_le h
  | lambda hs _ ih => exact hs.frontier_le.trans ih
  | app _ _ _ ihf iha => omega
  | letIn _ hc _ ihr ihb => exact ihr.trans (hc.frontier_le.trans ihb)

theorem _root_.Infer.belowFvars (h : Infer K frontier ctx input next subst output ty) :
    CtxBelow frontier ctx → (∀ k ∈ K, k < frontier) →
      Ty.BelowFvars next ty ∧ ∀ p ∈ subst, Ty.BelowFvars next p.2 := by
  induction h with
  | backend _ h _ _ hr =>
    intro hctx hK
    exact CoreBackend.Infer.belowFvars h hctx (fun v hv => hK v (hr v hv))
  | lambda hs hb ih =>
    intro hctx hK
    have hle := hs.frontier_le
    have hparam := hs.belowFvars hK
    obtain ⟨hbTy, hbSubst⟩ := ih (by
      intro M hM
      rcases List.mem_cons.mp hM with rfl | hM
      · exact hparam
      · exact (hctx M hM).mono hle)
      (fun k hk => Nat.lt_of_lt_of_le (hK k hk) hle)
    exact ⟨.arrow (Subst.onTy_belowFvars hbSubst (hparam.mono hb.frontier_le)) hbTy, hbSubst⟩
  | app hf ha hu ihf iha =>
    intro hctx hK
    have hfLe := hf.frontier_le
    have haLe := ha.frontier_le
    obtain ⟨hfTy, hfSubst⟩ := ihf hctx hK
    obtain ⟨haTy, haSubst⟩ := iha (Subst.onCtx_below hfSubst hfLe hctx)
      (fun k hk => Nat.lt_of_lt_of_le (hK k hk) hfLe)
    have huni := hu.unifies.belowFvars
      (Subst.onTy_belowFvars (fun p hp => (haSubst p hp).mono (Nat.le_succ _))
        (hfTy.mono (haLe.trans (Nat.le_succ _))))
      (.arrow (haTy.mono (Nat.le_succ _)) (.fvar (Nat.lt_succ_self _)))
    refine ⟨Subst.onTy_belowFvars huni (.fvar (Nat.lt_succ_self _)), ?_⟩
    intro p hp
    rcases List.mem_append.mp hp with hp | hp
    · rcases List.mem_append.mp hp with hp | hp
      · exact (hfSubst p hp).mono (haLe.trans (Nat.le_succ _))
      · exact (haSubst p hp).mono (Nat.le_succ _)
    · exact huni p hp
  | letIn hr hc hb ihr ihb =>
    intro hctx hK
    have hrLe := hr.frontier_le
    have hcLe := hc.frontier_le
    have hbLe := hb.frontier_le
    obtain ⟨hrTy, hrSubst⟩ := ihr hctx hK
    have hcSubst := hc.belowFvars hrTy (fun k hk => Nat.lt_of_lt_of_le (hK k hk) hrLe)
    have hcTy := Subst.onTy_belowFvars hcSubst (hrTy.mono hcLe)
    have hcheckedCtx := Subst.onCtx_below hcSubst hcLe
      (Subst.onCtx_below hrSubst hrLe hctx)
    obtain ⟨hbTy, hbSubst⟩ := ihb (by
      intro M hM
      rcases List.mem_cons.mp hM with rfl | hM
      · exact hcTy.closeOver
      · exact hcheckedCtx M hM)
      (fun k hk => Nat.lt_of_lt_of_le (hK k hk) (hrLe.trans hcLe))
    refine ⟨hbTy, ?_⟩
    intro p hp
    rcases List.mem_append.mp hp with hp | hp
    · rcases List.mem_append.mp hp with hp | hp
      · exact (hrSubst p hp).mono (hcLe.trans hbLe)
      · exact (hcSubst p hp).mono hbLe
    · exact hbSubst p hp




end Elaboration


namespace Elaboration

private theorem generalizes_lookup {new old : Env}
    (h : List.Forall₂ PolyTy.Generalizes new old) {index : Nat} {scheme : PolyTy}
    (hlook : old[index]? = some scheme) :
    ∃ scheme', new[index]? = some scheme' ∧ scheme'.Generalizes scheme := by
  induction h generalizing index with
  | nil => simp at hlook
  | @cons headNew headOld tailNew tailOld hhead htail ih =>
    cases index with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hlook
      subst scheme
      exact ⟨headNew, rfl, hhead⟩
    | succ index => exact ih hlook

/-- Replacing each environment entry by a more general scheme preserves
independent anonymous input typing, with its protected variables unchanged. -/
theorem Typing.weaken {K : List Nat} {ctx : Ctx} {input : Input} {ty : Ty}
    (h : Typing K ctx input ty) :
    ∀ {env' : Env}, List.Forall₂ PolyTy.Generalizes env' ctx.env →
      Typing K { ctx with env := env' } input ty := by
  induction h with
  | complete hemb hprotected hcore =>
    intro env' hgen
    refine .complete hemb hprotected ?_
    simpa only [List.append_nil] using
      TypeOfHM.weaken_schemes (env := []) hgen (by simpa only [List.append_nil] using hcore)
  | primLit hcore =>
    intro env' hgen
    apply Typing.primLit
    simpa only [List.append_nil] using
      TypeOfHM.weaken_schemes (env := []) hgen (by simpa only [List.append_nil] using hcore)
  | primBinOp hcore =>
    intro env' hgen
    apply Typing.primBinOp
    simpa only [List.append_nil] using
      TypeOfHM.weaken_schemes (env := []) hgen (by simpa only [List.append_nil] using hcore)
  | lambda hlc hfit hprotected _ ih =>
    intro env' hgen
    refine .lambda hlc hfit hprotected ?_
    exact ih (.cons (PolyTy.Generalizes.refl _) hgen)
  | app _ _ ihf iha =>
    intro env' hgen
    exact .app (ihf hgen) (iha hgen)
  | letIn hwf hprotected hfit _ _ ihr ihb =>
    intro env' hgen
    refine .letIn hwf hprotected hfit (fun Xs hf => ihr Xs hf hgen) ?_
    exact ihb (.cons (PolyTy.Generalizes.refl _) hgen)
  | var hlook hargs hinst =>
    intro env' hgen
    obtain ⟨scheme', hlook', hscheme⟩ := generalizes_lookup hgen hlook
    obtain ⟨args', hargs', hinst'⟩ := hscheme _ _ hargs hinst
    exact .var hlook' hargs' hinst'
  | ctor hlook hargs hinst =>
    intro env' _
    exact .ctor hlook hargs hinst

/-- Segment form matching the existing `TypeOfHM.weaken_schemes` contract. -/
theorem Typing.weaken_schemes {K : List Nat} {ctors : CtorEnv} {env : Env}
    {Ms Ms' : List PolyTy} {input : Input} {ty : Ty}
    (hgen : List.Forall₂ PolyTy.Generalizes Ms' Ms)
    (h : Typing K ⟨Ms ++ env, ctors⟩ input ty) :
    Typing K ⟨Ms' ++ env, ctors⟩ input ty := by
  apply h.weaken
  clear h
  have hrefl : List.Forall₂ PolyTy.Generalizes env env := by
    induction env with
    | nil => exact .nil
    | cons head tail ih => exact .cons (PolyTy.Generalizes.refl head) ih
  induction hgen with
  | nil => exact hrefl
  | cons hh _ ih => exact .cons hh ih

end Elaboration


namespace Elaboration

mutual
/-- Allocating flexible holes preserves local closure of any matching target. -/
theorem Template.Fits.allocate_lc {template : Template} {target : Ty}
    (h : template.Fits target) (hlc : target.IsLC) (frontier : Nat) :
    (template.allocate frontier).2.IsLC := by
  cases h with
  | fixed => exact hlc
  | hole => exact .fvar
  | arrow ha hb =>
    cases hlc with
    | arrow hla hlb =>
      exact .arrow (ha.allocate_lc hla frontier) (hb.allocate_lc hlb _)
  | custom hall =>
    cases hlc with
    | customTy hl => exact .customTy (allocateList_lc hall hl frontier)
theorem allocateList_lc {templates : List Template} {targets : List Ty}
    (h : List.Forall₂ Template.Fits templates targets)
    (hlc : ∀ t ∈ targets, t.IsLC) (frontier : Nat) :
    ∀ t ∈ (allocateList frontier templates).2, t.IsLC := by
  cases h with
  | nil => simp [allocateList]
  | @cons template target templates targets hh ht =>
    intro t hmem
    rcases List.mem_cons.mp hmem with rfl | hmem
    · exact hh.allocate_lc (hlc target List.mem_cons_self) frontier
    · exact allocateList_lc ht (fun t ht => hlc t (List.mem_cons_of_mem _ ht)) _ t hmem
end

/-- The executable lambda seed accepts every locally closed, scoped template. -/
theorem seed_complete {K : List Nat} {Φ : Nat} {ann : Option Template} {target : Ty}
    (hlc : target.IsLC)
    (hfit : ∀ template, ann = some template → template.Fits target)
    (hscope : ∀ template, ann = some template → ∀ v ∈ template.rigidVars, v ∈ K) :
    (seed K Φ ann).isSome := by
  cases ann with
  | none => rfl
  | some template =>
    have halloc : (template.allocate Φ).2.bvarsBelow 0 = true :=
      (Ty.bvarsBelow_iff _).mpr ((hfit template rfl).allocate_lc hlc Φ)
    have hr : template.rigidVars.all (fun v => decide (v ∈ K)) = true :=
      List.all_eq_true.mpr (fun v hv => decide_eq_true (hscope template rfl v hv))
    simp only [seed, halloc, hr, dite_true, Option.isSome_some]

/-- The executable ordinary-let check succeeds for every LC scoped target
reachable by an LC substitution that fixes the protected variables. -/
theorem checkLet_complete {K : List Nat} {Φ : Nat} {ann : LetAnn} {ty target : Ty} {R : Subst}
    (hK : ∀ k ∈ K, k < Φ) (hty : ty.IsLC) (hbelow : Ty.BelowFvars Φ ty)
    (hR : ∀ p ∈ R, p.2.IsLC) (hRfix : ∀ k ∈ K, R.onTy (.fvar k) = .fvar k)
    (htarget : target.IsLC) (hfit : ann.FitsMono target)
    (hscope : ∀ template, ann = .template template → ∀ v ∈ template.rigidVars, v ∈ K)
    (heq : target = R.onTy ty) : (checkLet K Φ ann ty).isSome := by
  cases ann with
  | absent => rfl
  | complete scheme => cases hfit
  | partialForall count template => cases hfit
  | template template =>
    have hlc := hfit.allocate_lc htarget Φ
    have halloc : (template.allocate Φ).2.bvarsBelow 0 = true := (Ty.bvarsBelow_iff _).mpr hlc
    have hr : template.rigidVars.all (fun v => decide (v ∈ K)) = true :=
      List.all_eq_true.mpr (fun v hv => decide_eq_true (hscope template rfl v hv))
    obtain ⟨U, hUlc, hagree, hUexpected⟩ := hfit.allocate_override htarget hR Φ
      (fun v hv => hK v (hscope template rfl v hv))
      (fun v hv => hRfix v (hscope template rfl v hv))
    have hUty : U.onTy ty = target := (Subst.onTy_congr hagree hbelow).symm.trans heq.symm
    have huni : Unifies U ty (template.allocate Φ).2 := by
      change U.onTy ty = U.onTy (template.allocate Φ).2
      rw [hUty, hUexpected]
    have hunifies := unifyCoreK_complete hty hlc hUlc huni
      (fun k hk => (hagree k (hK k hk)).symm.trans (hRfix k hk))
    cases template <;> simp only [checkLet, halloc, hr, dite_true, Option.isSome_some]
    all_goals cases hu : unifyCoreK K ty _ with
      | none => simp only [hu, Option.isSome_none] at hunifies; contradiction
      | some result => rcases result with ⟨subst, hun, hav⟩; rfl

end Elaboration
