import FHM.Elaboration.Judgment

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
private theorem transformed_hole_targets (template : Template) {S0 : Subst} {target : Ty}
    (h : (template.substTyFvars S0).Fits target) (hlc : target.IsLC) (Φ : Nat) :
    ∃ ts : List Ty, (template.allocate Φ).1 = Φ + ts.length ∧
      (∀ t ∈ ts, t.IsLC) ∧ ∀ U : Subst,
      (∀ v ∈ template.rigidVars, U.onTy (.fvar v) = S0.onTy (.fvar v)) →
      (∀ i (hi : i < ts.length), U.onTy (.fvar (Φ + i)) = ts[i]) →
      U.onTy (template.allocate Φ).2 = target := by
  cases template with
  | fixed ty =>
    cases h
    exact ⟨[], rfl, by simp, fun _ hr _ => Template.fixed.inj ((Template.fixed ty).substTyFvars_congr hr)⟩
  | hole =>
    refine ⟨[target], rfl, ?_, ?_⟩
    · simpa using hlc
    · intro U _ hb
      simpa only [Nat.add_zero] using hb 0 (by simp)
  | arrow a b =>
    cases h with
    | arrow ha hb =>
       cases hlc with
        | arrow hlca hlcb =>
          obtain ⟨as, halen, halc, haeq⟩ := transformed_hole_targets a ha hlca Φ
          obtain ⟨bs, hblen, hblc, hbeq⟩ := transformed_hole_targets b hb hlcb (a.allocate Φ).1
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
  | custom name templates =>
    cases h with
    | custom h =>
      cases hlc with
      | customTy hlcs =>
        obtain ⟨ts, hlen, hlc, heq⟩ := transformed_hole_targets_list templates h hlcs Φ
        refine ⟨ts, hlen, hlc, ?_⟩
        intro U hr hb
        simp only [Template.allocate, Subst.onTy_customTy, heq U hr hb]
private theorem transformed_hole_targets_list (templates : List Template) {S0 : Subst} {targets : List Ty}
    (h : List.Forall₂ Template.Fits (substTemplateList S0 templates) targets)
    (hlc : ∀ t ∈ targets, t.IsLC) (Φ : Nat) :
    ∃ ts : List Ty, (allocateList Φ templates).1 = Φ + ts.length ∧
      (∀ t ∈ ts, t.IsLC) ∧ ∀ U : Subst,
      (∀ v ∈ rigidVarsList templates, U.onTy (.fvar v) = S0.onTy (.fvar v)) →
      (∀ i (hi : i < ts.length), U.onTy (.fvar (Φ + i)) = ts[i]) →
      (allocateList Φ templates).2.map U.onTy = targets := by
  cases templates with
  | nil => cases h; exact ⟨[], rfl, by simp, by simp [allocateList]⟩
  | cons template templates =>
    cases h with
    | cons hh ht =>
      obtain ⟨as, halen, halc, haeq⟩ := transformed_hole_targets template hh (hlc _ List.mem_cons_self) Φ
      obtain ⟨bs, hblen, hblc, hbeq⟩ := transformed_hole_targets_list templates ht
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

/-- A target fitting the ambient-substituted source is realizable from the
original allocation while preserving ambient behavior below its frontier.
Neither frozen raw leaves nor fresh target names are required. -/
theorem Template.Fits.allocate_override_source {template : Template} {target : Ty} {S0 : Subst}
    (h : (template.substTyFvars S0).Fits target) (hlc : target.IsLC)
    (hS0 : ∀ p ∈ S0, p.2.IsLC) (Φ : Nat)
    (hrigid : ∀ v ∈ template.rigidVars, v < Φ) :
    ∃ U : Subst, (∀ p ∈ U, p.2.IsLC) ∧ Subst.AgreesBelow Φ S0 U ∧
      U.onTy (template.allocate Φ).2 = target := by
  obtain ⟨ts, _, hts, htemplate⟩ := transformed_hole_targets template h hlc Φ
  obtain ⟨U, hUlc, hUagree, hUblock⟩ := Subst.override_block hS0 Φ ts hts
  exact ⟨U, hUlc, hUagree, htemplate U
    (fun v hv => (hUagree v (hrigid v hv)).symm) hUblock⟩

/-- Fixed-source compatibility follows from the source-transforming allocator. -/
theorem Template.Fits.allocate_override {template : Template} {target : Ty}
    (h : template.Fits target) (hlc : target.IsLC) {S0 : Subst}
    (hS0 : ∀ p ∈ S0, p.2.IsLC) (Φ : Nat)
    (hrigid : ∀ v ∈ template.rigidVars, v < Φ)
    (hfix : ∀ v ∈ template.rigidVars, S0.onTy (.fvar v) = .fvar v) :
    ∃ U : Subst, (∀ p ∈ U, p.2.IsLC) ∧ Subst.AgreesBelow Φ S0 U ∧
      U.onTy (template.allocate Φ).2 = target := by
  have hsource : template.substTyFvars S0 = template := template.substTyFvars_eq_self_of_fixes hfix
  exact (hsource.symm ▸ h).allocate_override_source hlc hS0 Φ hrigid

end Elaboration


namespace Elaboration

theorem softVars_lt {F : List Ty} (hF : ∀ t ∈ F, Ty.BelowFvars frontier t) :
    ∀ v ∈ softVars F, v < frontier := by
  intro v hv
  obtain ⟨t, ht, hv⟩ := TyList.mem_freeVars_iff.mp hv
  exact (hF t ht).mem_lt v hv

theorem substSoft_below {S : Subst} {F : List Ty}
    (hS : ∀ p ∈ S, Ty.BelowFvars next p.2) (hle : frontier ≤ next)
    (hF : ∀ t ∈ F, Ty.BelowFvars frontier t) :
    ∀ t ∈ substSoft S F, Ty.BelowFvars next t := by
  intro t ht
  obtain ⟨u, hu, rfl⟩ := List.mem_map.mp ht
  exact Subst.onTy_belowFvars hS ((hF u hu).mono hle)

private theorem rigid_soft_lt {K F frontier}
    (hK : ∀ k ∈ K, k < frontier) (hF : ∀ t ∈ F, Ty.BelowFvars frontier t) :
    ∀ v ∈ K ++ softVars F, v < frontier :=
  fun v hv => (List.mem_append.mp hv).elim (hK v) (softVars_lt hF v)

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

theorem LetCheck.frontier_le (h : LetCheck K F frontier ty ann next subst) : frontier ≤ next := by
  cases h with
  | absent => omega
  | hole => omega
  | @template next expected subst sourceTemplate heq _ _ _ =>
    have hle := (sourceTemplate.allocate_bounds frontier).1
    rwa [heq] at hle

theorem LetCheck.belowFvars (h : LetCheck K F frontier ty ann next subst)
    (hty : Ty.BelowFvars frontier ty) (hK : ∀ k ∈ K, k < frontier)
    (hF : ∀ t ∈ F, Ty.BelowFvars frontier t) :
    ∀ p ∈ subst, Ty.BelowFvars next p.2 := by
  cases h with
  | absent => simp
  | hole => simp
  | @template next expected subst sourceTemplate heq _ hr hu =>
    have hb := (sourceTemplate.allocate_bounds frontier).2 (fun v hv => rigid_soft_lt hK hF v (hr v hv))
    rw [heq] at hb
    have hle := (sourceTemplate.allocate_bounds frontier).1
    rw [heq] at hle
    exact hu.unifies.belowFvars (hty.mono hle) hb

theorem SignatureCheck.frontier_le (h : SignatureCheck K F written frontier ty ann next subst) :
    frontier ≤ next := by
  cases h with
  | complete => exact Nat.le_refl _
  | @partialSignature next expected subst count template heq _ _ _ =>
      have hle := ((template.openTyVarsFrom 0 written).allocate_bounds frontier).1
      rwa [heq] at hle

theorem SignatureCheck.belowFvars (h : SignatureCheck K F written frontier ty ann next subst)
    (hty : Ty.BelowFvars frontier ty) (hK : ∀ k ∈ K, k < frontier)
    (hwritten : ∀ name ∈ written, name < frontier)
    (hF : ∀ t ∈ F, Ty.BelowFvars frontier t) :
    ∀ p ∈ subst, Ty.BelowFvars next p.2 := by
  cases h with
  | complete _ hr hu =>
      exact hu.unifies.belowFvars hty
        (Ty.openVars_belowFvars (Ty.BelowFvars.of_freeVars_lt (fun v hv => rigid_soft_lt hK hF v (hr v hv))) hwritten)
  | @partialSignature next expected subst count template heq _ hr hu =>
      have hb := ((template.openTyVarsFrom 0 written).allocate_bounds frontier).2
        (fun v hv => (List.mem_append.mp (Template.open_scope hr v hv)).elim (rigid_soft_lt hK hF v) (hwritten v))
      rw [heq] at hb
      have hle := ((template.openTyVarsFrom 0 written).allocate_bounds frontier).1
      rw [heq] at hle
      exact hu.unifies.belowFvars (hty.mono hle) hb

theorem SignatureCheck.scheme_belowFvars (h : SignatureCheck K F written frontier ty ann next subst)
    (hty : Ty.BelowFvars next (subst.onTy ty))
    (hrigid : ∀ v ∈ (ann.substTyFvars subst).rigidVars, v < next) :
    Ty.BelowFvars next (signatureScheme (ann.substTyFvars subst) Q written ctx (subst.onTy ty)).body := by
  cases h with
  | complete _ _ _ => exact Ty.BelowFvars.of_freeVars_lt hrigid
  | partialSignature => exact hty.closeOver

mutual
theorem _root_.Infer.frontier_le (h : Infer K F frontier ctx input next subst output ty) : frontier ≤ next := by
  match h with
  | .backend _ hi _ _ _ _ => exact hi.frontier_le
  | .lambda _ hs hb => exact hs.frontier_le.trans hb.frontier_le
  | .app _ hf ha _ => have := hf.frontier_le; have := ha.frontier_le; omega
  | .letIn _ hr hc hb => exact hr.frontier_le.trans (hc.frontier_le.trans hb.frontier_le)
  | .letSignature _ _ _ _ hr hc _ hb =>
      have := hr.frontier_le
      have := hc.frontier_le
      have := hb.frontier_le
      omega
  | .match_ _ hs _ hb => have := hs.frontier_le; have := hb.frontier_le; omega
  | .letRec _ _ _ hstrata hsigned _ _ hbody =>
      have := hstrata.frontier_le; have := hsigned.frontier_le; have := hbody.frontier_le; omega
termination_by (input.size, 0)
decreasing_by all_goals (simp only [Input.size, Input.size_openTyVars, Input.size_substTyFvars, sizeBranches_substInputBranches, sizeBindings_map_substTyFvars] at *; omega)

theorem _root_.InferBranches.frontier_le
    (h : InferBranches K F frontier ctx scrutTy resultTy branches next subst output) : frontier ≤ next := by
  match h with
  | .nil => omega
  | .cons _ _ _ _ hb _ hr => have := hb.frontier_le; have := hr.frontier_le; omega
  | .consWild _ hb _ hr => have := hb.frontier_le; have := hr.frontier_le; omega
termination_by (sizeBranches branches, 0)
decreasing_by all_goals (simp only [sizeBranches, Input.size_substTyFvars, sizeBranches_substInputBranches]; omega)

theorem _root_.InferRecComponent.frontier_le
    (h : InferRecComponent K F members index frontier ctx bindings specs next S outputs facts) :
    frontier ≤ next := by
  match h with
  | .nil => exact Nat.le_refl _
  | .skipMono _ hr | .skipPoly hr => exact hr.frontier_le
  | .consSelected _ hi _ hr => exact hi.frontier_le.trans hr.frontier_le
termination_by (sizeBindings bindings, 0)
decreasing_by all_goals (simp only [sizeBindings, sizeBindings_map_substTyFvars]; omega)

theorem _root_.InferRecStrata.frontier_le
    (h : InferRecStrata K F frontier ctx anns bindings state groups next S final) : frontier ≤ next := by
  match h with
  | .nil => exact Nat.le_refl _
  | .cons ho _ hc _ hr => exact ho.frontier_le.trans (hc.frontier_le.trans hr.frontier_le)
termination_by (sizeBindings bindings, groups.length + 1)
decreasing_by all_goals (simp only [sizeBindings_map_substTyFvars, sizeBindings_openRecSources, List.length_cons]; omega)

theorem _root_.InferRecSigned.frontier_le
    (h : InferRecSigned K F index frontier ctx anns bindings state next S final) : frontier ≤ next := by
  match h with
  | .nil => exact Nat.le_refl _
  | .skip _ hr => exact hr.frontier_le
  | .cons _ _ hi _ _ hr => have := hi.frontier_le; have := hr.frontier_le; omega
termination_by (sizeBindings bindings, 0)
decreasing_by all_goals (simp only [sizeBindings, Input.size_openTyVars, sizeBindings_map_substTyFvars]; omega)
end


private theorem anns_below_subst {anns : List LetAnn}
    (h : ∀ ann ∈ anns, ∀ v ∈ ann.rigidVars, v < frontier)
    (hS : ∀ p ∈ S, Ty.BelowFvars next p.2) (hle : frontier ≤ next) :
    ∀ ann ∈ anns.map (LetAnn.substTyFvars S), ∀ v ∈ ann.rigidVars, v < next := by
  intro ann hm v hv
  obtain ⟨old, hold, rfl⟩ := List.mem_map.mp hm
  obtain ⟨k, hk, hv⟩ := LetAnn.rigidVars_substTyFvars hv
  exact (Subst.onTy_belowFvars hS (.fvar (Nat.lt_of_lt_of_le (h old hold k hk) hle))).mem_lt v hv

private theorem specs_below_subst {specs : List RecSpec}
    (h : ∀ spec ∈ specs, spec.BelowFvars frontier)
    (hS : ∀ p ∈ S, Ty.BelowFvars next p.2) (hle : frontier ≤ next) :
    ∀ spec ∈ specs.map (RecSpec.onSubstSource S), spec.BelowFvars next := by
  intro spec hm
  obtain ⟨old, hold, rfl⟩ := List.mem_map.mp hm
  cases old with
  | mono ty => exact Subst.onTy_belowFvars hS ((h _ hold).mono hle)
  | poly scheme => exact Subst.onTy_belowFvars hS ((h _ hold).mono hle)

 theorem RecState.shapes_below {state : RecState} {openings : List RecOpening}
    (hstate : state.Below frontier)
    (hopen : ∀ opening ∈ openings, ∀ ty, opening.expected = some ty → Ty.BelowFvars frontier ty) :
    ∀ shape ∈ state.shapes members openings, RecShape.BelowFvars frontier shape := by
  intro shape hm
  obtain ⟨i, _, heq⟩ := List.mem_filterMap.mp hm
  cases hs : state.specs[i]? with
  | none => simp [hs] at heq
  | some spec =>
    cases spec with
    | poly σ => simp [hs, RecSpec.monoTy?] at heq
    | mono ty =>
      cases ho : openings[i]? with
      | none => simp [hs, RecSpec.monoTy?, ho] at heq
      | some opening =>
        simp [hs, RecSpec.monoTy?, ho] at heq
        subst shape
        exact ⟨hstate.1 _ (List.mem_of_getElem? hs), hopen opening (List.mem_of_getElem? ho)⟩

 theorem _root_.InferRecComponent.belowFvars_of_infer
    (h : InferRecComponent K F members index frontier ctx bindings specs next S outputs facts)
    (hInfer : ∀ {κ F' Ψ c e Ψ' T output ty}, e.size ≤ sizeBindings bindings →
      Infer κ F' Ψ c e Ψ' T output ty → CtxBelow Ψ c → (∀ k ∈ κ, k < Ψ) →
      (∀ t ∈ F', Ty.BelowFvars Ψ t) → Ty.BelowFvars Ψ' ty ∧ ∀ p ∈ T, Ty.BelowFvars Ψ' p.2)
    (hctx : CtxBelow frontier ctx) (hK : ∀ k ∈ K, k < frontier)
    (hF : ∀ t ∈ F, Ty.BelowFvars frontier t) (hspec : ∀ spec ∈ specs, spec.BelowFvars frontier) :
    ∀ p ∈ S, Ty.BelowFvars next p.2 := by
  match h with
  | .nil => simp
  | .skipMono _ hr | .skipPoly hr =>
      exact hr.belowFvars_of_infer (fun he h => hInfer (by simp only [sizeBindings]; omega) h)
        hctx hK hF (fun spec hm => hspec spec (List.mem_cons_of_mem _ hm))
  | .consSelected _ hi hu hr =>
      expose_names
      have hle := hi.frontier_le
      have hrle := hr.frontier_le
      obtain ⟨hiTy, hiS⟩ := hInfer (by simp only [sizeBindings]; omega) hi hctx hK hF
      have huS := hu.unifies.belowFvars hiTy (Subst.onTy_belowFvars hiS ((hspec _ List.mem_cons_self).mono hle))
      have hboth : ∀ p ∈ s1 ++ s2, Ty.BelowFvars first p.2 :=
        fun p hp => (List.mem_append.mp hp).elim (hiS p) (huS p)
      have hrS := hr.belowFvars_of_infer
        (fun he h => hInfer (by simp only [sizeBindings_map_substTyFvars] at he; simp only [sizeBindings]; omega) h)
        (by simpa only [Subst.onCtx_append] using Subst.onCtx_below hboth hle hctx)
        (fun k hk => Nat.lt_of_lt_of_le (hK k hk) hle)
        (substSoft_below hboth hle hF)
        (specs_below_subst (fun spec hm => hspec spec (List.mem_cons_of_mem _ hm)) hboth hle)
      intro p hp
      exact (List.mem_append.mp hp).elim (fun hp => (hboth p hp).mono hrle) (hrS p)
 termination_by structural h

 theorem _root_.InferRecStrata.belowFvars_of_infer
    (h : InferRecStrata K F frontier ctx anns bindings state groups next S final)
    (hInfer : ∀ {κ F' Ψ c e Ψ' T output ty}, e.size ≤ sizeBindings bindings →
      Infer κ F' Ψ c e Ψ' T output ty → CtxBelow Ψ c → (∀ k ∈ κ, k < Ψ) →
      (∀ t ∈ F', Ty.BelowFvars Ψ t) → Ty.BelowFvars Ψ' ty ∧ ∀ p ∈ T, Ty.BelowFvars Ψ' p.2)
    (hctx : CtxBelow frontier ctx) (hK : ∀ k ∈ K, k < frontier)
    (hF : ∀ t ∈ F, Ty.BelowFvars frontier t) (hstate : state.Below frontier)
    (hanns : ∀ ann ∈ anns, ∀ v ∈ ann.rigidVars, v < frontier) :
    (∀ p ∈ S, Ty.BelowFvars next p.2) ∧ final.Below next := by
  match h with
  | .nil => exact ⟨by simp, hstate⟩
  | .cons hopen hshape hcomponent hfinish hrest =>
    expose_names
    have hle := hopen.frontier_le
    have hcle := hcomponent.frontier_le
    have hrle := hrest.frontier_le
    have hinit := hstate.installOpenings hopen
    have hpre := hshape.belowFvars (RecState.shapes_below hinit (hopen.expected_below hanns))
    have hFopened : ∀ t ∈ F ++ (openings.flatMap RecOpening.written).map Ty.fvar, Ty.BelowFvars opened t := by
      intro t ht
      rcases List.mem_append.mp ht with ht | ht
      · exact (hF t ht).mono hle
      · obtain ⟨v, hv, rfl⟩ := List.mem_map.mp ht
        exact .fvar (hopen.written_range v hv).2
    have hcurrent := hcomponent.belowFvars_of_infer
      (fun he h => hInfer (by simpa only [sizeBindings_map_substTyFvars, sizeBindings_openRecSources] using he) h)
      ((hinit.onSubst hpre (Nat.le_refl _)).rhsCtx (Subst.onCtx_below hpre hle hctx))
      (fun k hk => Nat.lt_of_lt_of_le (hK k hk) hle)
      (substSoft_below hpre (Nat.le_refl _) hFopened) (hinit.onSubst hpre (Nat.le_refl _)).1
    have hboth : ∀ p ∈ pre ++ current, Ty.BelowFvars first p.2 :=
      fun p hp => (List.mem_append.mp hp).elim (fun hp => (hpre p hp).mono hcle) (hcurrent p)
    have hfullle := hle.trans hcle
    obtain ⟨htail, hfinal⟩ := hrest.belowFvars_of_infer
      (fun he h => hInfer (by simpa only [sizeBindings_map_substTyFvars] using he) h)
      (Subst.onCtx_below hboth hfullle hctx)
      (fun k hk => Nat.lt_of_lt_of_le (hK k hk) hfullle)
      (substSoft_below hboth hfullle hF)
      (hfinish.below (hinit.onSubst hboth hcle))
      (anns_below_subst hanns hboth hfullle)
    exact ⟨fun p hp => (List.mem_append.mp hp).elim (fun hp => (hboth p hp).mono hrle) (htail p), hfinal⟩
 termination_by structural h

 theorem _root_.InferRecSigned.belowFvars_of_infer
    (h : InferRecSigned K F index frontier ctx anns bindings state next S final)
    (hInfer : ∀ {κ F' Ψ c e Ψ' T output ty}, e.size ≤ sizeBindings bindings →
      Infer κ F' Ψ c e Ψ' T output ty → CtxBelow Ψ c → (∀ k ∈ κ, k < Ψ) →
      (∀ t ∈ F', Ty.BelowFvars Ψ t) → Ty.BelowFvars Ψ' ty ∧ ∀ p ∈ T, Ty.BelowFvars Ψ' p.2)
    (hctx : CtxBelow frontier ctx) (hK : ∀ k ∈ K, k < frontier)
    (hF : ∀ t ∈ F, Ty.BelowFvars frontier t) (hstate : state.Below frontier)
    (hanns : ∀ ann ∈ anns, ∀ v ∈ ann.rigidVars, v < frontier) :
    (∀ p ∈ S, Ty.BelowFvars next p.2) ∧ final.Below next := by
  match h with
  | .nil => exact ⟨by simp, hstate⟩
  | .skip _ hr =>
      exact hr.belowFvars_of_infer (fun he h => hInfer (by simp only [sizeBindings]; omega) h)
        hctx hK hF hstate (fun ann ha => hanns ann (List.mem_cons_of_mem _ ha))
  | .cons _ _ hi hu _ hr =>
      expose_names
      have hle := hi.frontier_le
      have hrle := hr.frontier_le
      have hbase : frontier ≤ first := by omega
      obtain ⟨hiTy, hiS⟩ := hInfer (by simp only [Input.size_openTyVars, sizeBindings]; omega) hi
        (fun M hm => ((hstate.rhsCtx hctx) M hm).mono (by omega))
        (by
          intro k hk
          rcases List.mem_append.mp hk with hk | hk
          · have := hK k hk; omega
          · exact freshVars_lt k hk)
        (fun t ht => (hF t ht).mono (by omega))
      have hexpected : Ty.BelowFvars first ((s1.onPolyTy scheme).openVars (freshVars frontier scheme.paramCount)) :=
        Ty.openVars_belowFvars (Subst.onTy_belowFvars hiS
          ((Ty.BelowFvars.of_freeVars_lt (hanns _ List.mem_cons_self)).mono hbase))
          (fun v hv => Nat.lt_of_lt_of_le (freshVars_lt v hv) hle)
      have huS := hu.unifies.belowFvars hiTy hexpected
      have hboth : ∀ p ∈ s1 ++ s2, Ty.BelowFvars first p.2 :=
        fun p hp => (List.mem_append.mp hp).elim (hiS p) (huS p)
      obtain ⟨htail, hfinal⟩ := hr.belowFvars_of_infer
        (fun he h => hInfer (by simp only [sizeBindings_map_substTyFvars] at he; simp only [sizeBindings]; omega) h)
        (Subst.onCtx_below hboth hbase hctx)
        (fun k hk => Nat.lt_of_lt_of_le (hK k hk) hbase)
        (substSoft_below hboth hbase hF) ((hstate.onSubst hboth hbase).setSigned)
        (anns_below_subst (fun ann ha => hanns ann (List.mem_cons_of_mem _ ha)) hboth hbase)
      exact ⟨fun p hp => (List.mem_append.mp hp).elim (fun hp => (hboth p hp).mono hrle) (htail p), hfinal⟩
 termination_by structural h

mutual
theorem _root_.Infer.belowFvars (h : Infer K F frontier ctx input next subst output ty) :
    CtxBelow frontier ctx → (∀ k ∈ K, k < frontier) →
      (∀ t ∈ F, Ty.BelowFvars frontier t) →
      Ty.BelowFvars next ty ∧ ∀ p ∈ subst, Ty.BelowFvars next p.2 := by
  match h with
  | .backend _ h _ _ hr _ =>
    intro hctx hK _
    exact CoreBackend.Infer.belowFvars h hctx (fun v hv => hK v (hr v hv))
  | .lambda _ hs hb =>
    intro hctx hK hF
    have hle := hs.frontier_le
    have hparam := hs.belowFvars (rigid_soft_lt hK hF)
    obtain ⟨hbTy, hbSubst⟩ := hb.belowFvars (by
      intro M hM
      rcases List.mem_cons.mp hM with rfl | hM
      · exact hparam
      · exact (hctx M hM).mono hle)
      (fun k hk => Nat.lt_of_lt_of_le (hK k hk) hle)
      (fun t ht => (hF t ht).mono hle)
    exact ⟨.arrow (Subst.onTy_belowFvars hbSubst (hparam.mono hb.frontier_le)) hbTy, hbSubst⟩
  | .app _ hf ha hu =>
    intro hctx hK hF
    have hfLe := hf.frontier_le
    have haLe := ha.frontier_le
    obtain ⟨hfTy, hfSubst⟩ := hf.belowFvars hctx hK hF
    obtain ⟨haTy, haSubst⟩ := ha.belowFvars (Subst.onCtx_below hfSubst hfLe hctx)
      (fun k hk => Nat.lt_of_lt_of_le (hK k hk) hfLe)
      (substSoft_below hfSubst hfLe hF)
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
  | .letIn _ hr hc hb =>
    intro hctx hK hF
    have hrLe := hr.frontier_le
    have hcLe := hc.frontier_le
    have hbLe := hb.frontier_le
    obtain ⟨hrTy, hrSubst⟩ := hr.belowFvars hctx hK hF
    have hFfirst := substSoft_below hrSubst hrLe hF
    have hcSubst := hc.belowFvars hrTy (fun k hk => Nat.lt_of_lt_of_le (hK k hk) hrLe) hFfirst
    have hcTy := Subst.onTy_belowFvars hcSubst (hrTy.mono hcLe)
    have hcheckedCtx := Subst.onCtx_below hcSubst hcLe
      (Subst.onCtx_below hrSubst hrLe hctx)
    obtain ⟨hbTy, hbSubst⟩ := hb.belowFvars (by
      intro M hM
      rcases List.mem_cons.mp hM with rfl | hM
      · exact hcTy.closeOver
      · exact hcheckedCtx M hM)
      (fun k hk => Nat.lt_of_lt_of_le (hK k hk) (hrLe.trans hcLe))
      (by simpa only [substSoft_append] using substSoft_below hcSubst hcLe hFfirst)
    refine ⟨hbTy, ?_⟩
    intro p hp
    rcases List.mem_append.mp hp with hp | hp
    · rcases List.mem_append.mp hp with hp | hp
      · exact (hrSubst p hp).mono (hcLe.trans hbLe)
      · exact (hcSubst p hp).mono hbLe
    · exact hbSubst p hp

  | @Infer.letSignature K F ann rhs body written frontier ctx first s1 rhsOut rhsTy checked sCheck
      next s2 bodyOut bodyTy _ hprefix _ _ hr hc _ hb =>
    intro hctx hK hF
    have hrLe := hr.frontier_le
    have hcLe := hc.frontier_le
    have hbLe := hb.frontier_le
    obtain ⟨hrTy, hrSubst⟩ := hr.belowFvars
      (fun M hM => (hctx M hM).mono (by omega)) (by
        intro k hk
        rcases List.mem_append.mp hk with hk | hk
        · exact Nat.lt_of_lt_of_le (hK k hk) (by omega)
        · exact freshVars_lt k (by rwa [← hprefix]))
      (fun t ht => (hF t ht).mono (by omega))
    have hKfirst : ∀ k ∈ K, k < first := fun k hk => Nat.lt_of_lt_of_le (hK k hk) (by omega)
    have hWfirst : ∀ name ∈ written, name < first := fun name hn =>
      Nat.lt_of_lt_of_le (freshVars_lt name (by rwa [← hprefix])) hrLe
    have hFfirst := substSoft_below hrSubst (by omega) hF
    have hcSubst := hc.belowFvars hrTy hKfirst hWfirst hFfirst
    have hcTy := Subst.onTy_belowFvars hcSubst (hrTy.mono hcLe)
    have hcheckedCtx := Subst.onCtx_below hcSubst hcLe
      (Subst.onCtx_below hrSubst (by omega) hctx)
    have hpostrigid : ∀ v ∈ ((ann.substTyFvars s1).substTyFvars sCheck).rigidVars, v < checked := by
      intro v hv
      obtain ⟨k, hk, hv⟩ := LetAnn.rigidVars_substTyFvars hv
      exact (Subst.onTy_belowFvars hcSubst (.fvar
        (Nat.lt_of_lt_of_le (rigid_soft_lt hKfirst hFfirst k (hc.rigid k hk)) hcLe))).mem_lt v hv
    obtain ⟨hbTy, hbSubst⟩ := hb.belowFvars (by
      intro M hM
      rcases List.mem_cons.mp hM with rfl | hM
      · rw [LetAnn.substTyFvars_append]
        exact hc.scheme_belowFvars hcTy hpostrigid
      · exact hcheckedCtx M hM)
      (fun k hk => Nat.lt_of_lt_of_le (hK k hk) (by omega))
      (by simpa only [substSoft_append] using substSoft_below hcSubst hcLe hFfirst)
    refine ⟨hbTy, ?_⟩
    intro p hp
    rcases List.mem_append.mp hp with hp | hp
    · rcases List.mem_append.mp hp with hp | hp
      · exact (hrSubst p hp).mono (hcLe.trans hbLe)
      · exact (hcSubst p hp).mono hbLe
    · exact hbSubst p hp

  | .match_ _ hs _ hb =>
    intro hctx hK hF
    obtain ⟨ht, hS1⟩ := hs.belowFvars hctx hK hF
    have hle := hs.frontier_le
    obtain ⟨hresult, hS2⟩ := hb.belowFvars
      (Subst.onCtx_below (fun p hp => (hS1 p hp).mono (Nat.le_succ _)) (hle.trans (Nat.le_succ _)) hctx)
      (ht.mono (Nat.le_succ _)) (.fvar (Nat.lt_succ_self _))
      (fun k hk => Nat.lt_of_lt_of_le (hK k hk) (hle.trans (Nat.le_succ _)))
      (substSoft_below (fun p hp => (hS1 p hp).mono (Nat.le_succ _))
        (hle.trans (Nat.le_succ _)) hF)
    refine ⟨hresult, fun p hp => ?_⟩
    rcases List.mem_append.mp hp with hp | hp
    · exact (hS1 p hp).mono ((Nat.le_succ _).trans hb.frontier_le)
    · exact hS2 p hp
  | .letRec hscope _ hvalid hstrata hsigned _ _ hbody =>
    intro hctx hK hF
    expose_names
    have hanns : ∀ ann ∈ anns, ∀ v ∈ ann.rigidVars, v < frontier := by
      intro ann ha v hv
      exact rigid_soft_lt hK hF v (hscope v (by
        simp only [Input.rigidVars, List.mem_append]
        exact Or.inl (Or.inl (List.mem_flatMap.mpr ⟨ann, ha, hv⟩))))
    have hlen : anns.length = bindings.length := by simpa only [List.length_map] using hvalid.length
    have hseed : frontier ≤ frontier + bindings.length := by omega
    obtain ⟨hs1, hstate1⟩ := hstrata.belowFvars_of_infer
      (fun he hi => hi.belowFvars)
      (fun M hm => (hctx M hm).mono hseed)
      (fun k hk => Nat.lt_of_lt_of_le (hK k hk) hseed)
      (fun t ht => (hF t ht).mono hseed)
      (by simpa only [hlen] using RecState.Below.init hanns)
      (fun ann ha v hv => Nat.lt_of_lt_of_le (hanns ann ha v hv) hseed)
    have hle1 := hstrata.frontier_le
    have hle2 := hsigned.frontier_le
    have hle3 := hbody.frontier_le
    have hbase1 : frontier ≤ first := by omega
    have hbase2 : frontier ≤ second := by omega
    obtain ⟨hs2, hstate2⟩ := hsigned.belowFvars_of_infer
      (fun he hi => hi.belowFvars)
      (Subst.onCtx_below hs1 hbase1 hctx)
      (fun k hk => Nat.lt_of_lt_of_le (hK k hk) hbase1)
      (substSoft_below hs1 hbase1 hF) hstate1 (anns_below_subst hanns hs1 hbase1)
    have hs12 : ∀ p ∈ s1 ++ s2, Ty.BelowFvars second p.2 :=
      fun p hp => (List.mem_append.mp hp).elim (fun hp => (hs1 p hp).mono hle2) (hs2 p)
    obtain ⟨hbodyTy, hs3⟩ := hbody.belowFvars
      (hstate2.rhsCtx (Subst.onCtx_below hs12 hbase2 hctx))
      (fun k hk => Nat.lt_of_lt_of_le (hK k hk) hbase2)
      (substSoft_below hs12 hbase2 hF)
    exact ⟨hbodyTy, fun p hp => (List.mem_append.mp hp).elim (fun hp => (hs12 p hp).mono hle3) (hs3 p)⟩
termination_by (input.size, 0)
decreasing_by all_goals (simp only [Input.size, Input.size_openTyVars, Input.size_substTyFvars, sizeBranches_substInputBranches, sizeBindings_map_substTyFvars] at *; omega)

theorem _root_.InferBranches.belowFvars {Φ ctx scrutTy ρ brs Φ' S}
    (h : InferBranches κ F Φ ctx scrutTy ρ brs Φ' S out)
    (hctx : CtxBelow Φ ctx) (hscrutTy : Ty.BelowFvars Φ scrutTy) (hρ : Ty.BelowFvars Φ ρ)
    (hK : ∀ k ∈ κ, k < Φ) (hF : ∀ t ∈ F, Ty.BelowFvars Φ t) :
    Ty.BelowFvars Φ' (S.onTy ρ) ∧ (∀ p ∈ S, Ty.BelowFvars Φ' p.2) := by
  match h with
  | .nil => exact ⟨by simpa using hρ, by simp⟩
  | @InferBranches.cons name count body rest κ F ctor scrutTy Φ S₀ ctx Φ₁ S₁ bodyOut bodyTy ρ S₂ Φ' S₃ restOut _ hlook hn huni0Rigid hbody huniRigid hrest =>
    have huni0 := huni0Rigid.unifies
    have huni := huniRigid.unifies
    have hS₀ : ∀ p ∈ S₀, Ty.BelowFvars (Φ + ctor.paramCount) p.2 :=
      UnifyRel.belowFvars huni0 (hscrutTy.mono (by omega))
        (.customTy (fun t ht => by
          obtain ⟨x, hx, rfl⟩ := List.mem_map.mp ht
          exact .fvar (by have := freshVars_lt x hx; omega)))
    obtain ⟨hτb, hS₁⟩ := Infer.belowFvars hbody
      (branchBindings_below (ctorr := ctor)
        (ta := ((freshVars Φ ctor.paramCount).map (Ty.fvar ·)).map S₀.onTy)
        (Subst.onCtx_below hS₀ (by omega) hctx)
        (fun t ht => by
          obtain ⟨v, hv, rfl⟩ := List.mem_map.mp ht
          obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hv
          exact Subst.onTy_belowFvars hS₀ (.fvar (by have := freshVars_lt x hx; omega))))
      (fun k hk => Nat.lt_of_lt_of_le (hK k hk) (by omega))
      (substSoft_below hS₀ (by omega) hF)
    have hle0 : Φ + ctor.paramCount ≤ Φ₁ := Infer.frontier_le hbody
    have hS₀ρ : Ty.BelowFvars Φ₁ (S₀.onTy ρ) :=
      (Subst.onTy_belowFvars hS₀ (hρ.mono (by omega))).mono hle0
    have hS₀scrut : Ty.BelowFvars Φ₁ (S₀.onTy scrutTy) :=
      (Subst.onTy_belowFvars hS₀ (hscrutTy.mono (by omega))).mono hle0
    have hS₁ρ := Subst.onTy_belowFvars hS₁ hS₀ρ
    have hS₂ := UnifyRel.belowFvars huni hτb hS₁ρ
    have hctx1 : CtxBelow Φ₁ (S₂.onCtx (S₁.onCtx (S₀.onCtx ctx))) :=
      Subst.onCtx_below hS₂ (le_refl _)
        (Subst.onCtx_below hS₁ (le_refl _)
          (Subst.onCtx_below (fun p hp => (hS₀ p hp).mono hle0) (by omega) hctx))
    obtain ⟨hres, hS₃⟩ := InferBranches.belowFvars hrest hctx1
      (Subst.onTy_belowFvars hS₂ (Subst.onTy_belowFvars hS₁ hS₀scrut))
      (Subst.onTy_belowFvars hS₂ (Subst.onTy_belowFvars hS₁ hS₀ρ))
      (fun k hk => Nat.lt_of_lt_of_le (hK k hk) (by omega))
      (by simpa only [substSoft_append] using
        substSoft_below hS₂ (le_refl _) (substSoft_below hS₁ (le_refl _)
          (substSoft_below (fun p hp => (hS₀ p hp).mono hle0) (by omega) hF)))
    have hbrle := InferBranches.frontier_le hrest
    refine ⟨?_, ?_⟩
    · rw [Subst.onTy_append, Subst.onTy_append, Subst.onTy_append]; exact hres
    · intro p hp; rw [List.mem_append, List.mem_append, List.mem_append] at hp
      rcases hp with ((hp | hp) | hp) | hp
      · exact (hS₀ p hp).mono (by omega)
      · exact (hS₁ p hp).mono (by omega)
      · exact (hS₂ p hp).mono (by omega)
      · exact hS₃ p hp
  | .consWild _ hbody huniRigid hrest =>
    have huni := huniRigid.unifies
    obtain ⟨hτb, hS₁⟩ := Infer.belowFvars hbody hctx
      hK hF
    have hle1 := Infer.frontier_le hbody
    have hS₁ρ := Subst.onTy_belowFvars hS₁ (hρ.mono hle1)
    have hS₂ := UnifyRel.belowFvars huni hτb hS₁ρ
    have hctx1 := Subst.onCtx_below hS₂ (le_refl _) (Subst.onCtx_below hS₁ hle1 hctx)
    obtain ⟨hres, hS₃⟩ := InferBranches.belowFvars hrest hctx1
      (Subst.onTy_belowFvars hS₂ (Subst.onTy_belowFvars hS₁ (hscrutTy.mono hle1)))
      (Subst.onTy_belowFvars hS₂ (Subst.onTy_belowFvars hS₁ (hρ.mono hle1)))
      (fun k hk => Nat.lt_of_lt_of_le (hK k hk) hle1)
      (by simpa only [substSoft_append] using
        substSoft_below hS₂ (le_refl _) (substSoft_below hS₁ hle1 hF))
    have hbrle := InferBranches.frontier_le hrest
    refine ⟨?_, ?_⟩
    · rw [Subst.onTy_append, Subst.onTy_append]; exact hres
    · intro p hp; rw [List.mem_append, List.mem_append] at hp
      rcases hp with (hp | hp) | hp
      · exact (hS₁ p hp).mono (by omega)
      · exact (hS₂ p hp).mono (by omega)
      · exact hS₃ p hp
termination_by (sizeBranches brs, 0)
decreasing_by
  all_goals (try subst_vars; try simp only [sizeBranches, Input.size_substTyFvars, sizeBranches_substInputBranches]; omega)
end


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
  induction h using Typing.rec
      (motive_2 := fun K ctx branch scrutTy resultTy _ =>
        ∀ {env' : Env}, List.Forall₂ PolyTy.Generalizes env' ctx.env →
          BranchTyping Typing K { ctx with env := env' } branch scrutTy resultTy) with
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
  | letSignature hwf hann hrhs hfit _ _ ihr ihb =>
    intro env' hgen
    refine .letSignature hwf hann hrhs hfit (fun Xs hf => ihr Xs hf hgen) ?_
    exact ihb (.cons (PolyTy.Generalizes.refl _) hgen)
  | var hlook hargs hinst =>
    intro env' hgen
    obtain ⟨scheme', hlook', hscheme⟩ := generalizes_lookup hgen hlook
    obtain ⟨args', hargs', hinst'⟩ := hscheme _ _ hargs hinst
    exact .var hlook' hargs' hinst'
  | ctor hlook hargs hinst =>
    intro env' _
    exact .ctor hlook hargs hinst

  | match_ _ hne _ ihscrut ihbranches =>
    intro env' hgen
    exact .match_ (ihscrut hgen) hne (fun branch hb => ihbranches branch hb hgen)
  | @named name count scrutTy ctor args fields K ctx body resultTy hspec _ ih =>
    rename_i env' hgen
    refine .named hspec (ih ?_)
    have hextra : ∀ extra : Env,
        List.Forall₂ PolyTy.Generalizes (extra ++ env') (extra ++ ctx.env) := by
      intro extra
      induction extra with
      | nil => exact hgen
      | cons head tail ih => exact .cons (PolyTy.Generalizes.refl head) ih
    exact hextra (fields.map PolyTy.mkTrivial)
  | wildcard _ ih =>
    rename_i env' hgen
    exact .wildcard (ih hgen)

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


mutual
/-- A locally closed filling of the transformed source reflects local closure
of the original allocation. No rigidity or closure of the substitution needed. -/
theorem Template.Fits.allocate_lc_source {template : Template} {target : Ty} {S : Subst}
    (h : (template.substTyFvars S).Fits target) (hlc : target.IsLC) (frontier : Nat) :
    (template.allocate frontier).2.IsLC := by
  cases template with
  | fixed ty => cases h; exact ContainsBvarsUpTo.of_substFvars hlc
  | hole => exact .fvar
  | arrow a b =>
    cases h with
    | arrow ha hb =>
      cases hlc with
      | arrow hla hlb => exact .arrow (ha.allocate_lc_source hla frontier) (hb.allocate_lc_source hlb _)
  | custom name args =>
    cases h with
    | custom hall =>
      cases hlc with
      | customTy hl => exact .customTy (allocateList_lc_source hall hl frontier)
private theorem allocateList_lc_source {templates : List Template} {targets : List Ty} {S : Subst}
    (h : List.Forall₂ Template.Fits (substTemplateList S templates) targets)
    (hlc : ∀ t ∈ targets, t.IsLC) (frontier : Nat) :
    ∀ t ∈ (allocateList frontier templates).2, t.IsLC := by
  cases templates with
  | nil => intro t ht; cases ht
  | cons template templates =>
    cases h with
    | cons hh ht =>
      intro t hmem
      rcases List.mem_cons.mp hmem with rfl | hmem
      · exact hh.allocate_lc_source (hlc _ List.mem_cons_self) frontier
      · exact allocateList_lc_source ht (fun t ht => hlc t (List.mem_cons_of_mem _ ht)) _ t hmem
end


end Elaboration



namespace Elaboration

private theorem UnifyRel.sourceAvoid_local {t u : Ty} {S : Subst} {w : Nat}
    (h : UnifyRel t u S) (ht : w ∉ t.freeVars) (hu : w ∉ u.freeVars) :
    (∀ p ∈ S, w ∉ p.2.freeVars) ∧ w ∉ S.map Prod.fst := by
  constructor
  · intro p hp hw
    exact (h.range_mem p hp w hw).elim ht hu
  · intro hw
    obtain ⟨p, hp, heq⟩ := List.mem_map.mp hw
    have hm := h.dom_mem p hp
    rw [heq] at hm
    exact hm.elim ht hu

private theorem Subst.sourceAvoid_append_local {S T : Subst} {w : Nat}
    (hS : (∀ p ∈ S, w ∉ p.2.freeVars) ∧ w ∉ S.map Prod.fst)
    (hT : (∀ p ∈ T, w ∉ p.2.freeVars) ∧ w ∉ T.map Prod.fst) :
    (∀ p ∈ S ++ T, w ∉ p.2.freeVars) ∧ w ∉ (S ++ T).map Prod.fst := by
  exact ⟨fun p hp => (List.mem_append.mp hp).elim (hS.1 p) (hT.1 p),
    by simpa only [List.map_append, List.mem_append, not_or] using And.intro hS.2 hT.2⟩

mutual
 theorem Template.allocate_avoid {template : Template} {frontier w : Nat}
    (hw : w < frontier) (h : w ∉ template.rigidVars) :
    w ∉ (template.allocate frontier).2.freeVars := by
  cases template with
  | fixed ty => exact h
  | hole => simp only [Template.allocate, Ty.freeVars, List.mem_singleton]; omega
  | arrow a b =>
    simp only [Template.rigidVars, List.mem_append, not_or] at h
    have ha := a.allocate_avoid hw h.1
    have hb := b.allocate_avoid (Nat.lt_of_lt_of_le hw (a.allocate_bounds frontier).1) h.2
    simpa only [Template.allocate, Ty.freeVars, List.mem_dedup, List.mem_append, not_or] using And.intro ha hb
  | custom name args =>
    exact allocateList_avoid hw h
 theorem allocateList_avoid {templates : List Template} {frontier w : Nat}
    (hw : w < frontier) (h : w ∉ rigidVarsList templates) :
    w ∉ TyList.freeVars (allocateList frontier templates).2 := by
  cases templates with
  | nil => simp [allocateList, TyList.freeVars]
  | cons a rest =>
    simp only [rigidVarsList, List.mem_append, not_or] at h
    have ha := a.allocate_avoid hw h.1
    have hb := allocateList_avoid (Nat.lt_of_lt_of_le hw (a.allocate_bounds frontier).1) h.2
    simpa only [allocateList, TyList.freeVars, List.mem_dedup, List.mem_append, not_or] using And.intro ha hb
end

 theorem Seed.sourceAvoid (h : Seed K frontier ann param initial) (hw : w < frontier)
    (hann : ∀ t, ann = some t → w ∉ t.rigidVars) : w ∉ param.freeVars := by
  cases h with
  | absent => simp only [Ty.freeVars, List.mem_singleton]; omega
  | annotated heq _ _ => simpa only [heq] using Template.allocate_avoid hw (hann _ rfl)

 theorem LetCheck.sourceAvoid (h : LetCheck K F frontier ty ann next subst)
    (hw : w < frontier) (hty : w ∉ ty.freeVars) (hann : w ∉ ann.rigidVars) :
    (∀ p ∈ subst, w ∉ p.2.freeVars) ∧ w ∉ subst.map Prod.fst := by
  cases h with
  | absent => simp
  | hole => simp
  | template heq _ _ hu =>
    exact UnifyRel.sourceAvoid_local hu.unifies hty (by simpa only [heq] using Template.allocate_avoid hw hann)

 theorem SignatureCheck.sourceAvoid (h : SignatureCheck K F written frontier ty ann next subst)
    (hw : w < frontier) (hty : w ∉ ty.freeVars) (hann : w ∉ ann.rigidVars)
    (hwr : w ∉ written) :
    (∀ p ∈ subst, w ∉ p.2.freeVars) ∧ w ∉ subst.map Prod.fst := by
  cases h with
  | complete _ _ hu =>
    refine UnifyRel.sourceAvoid_local hu.unifies hty ?_
    intro hc
    exact (Ty.freeVars_openVars_subset w hc).elim hann hwr
  | partialSignature heq _ _ hu =>
    refine UnifyRel.sourceAvoid_local hu.unifies hty ?_
    simpa only [heq] using Template.allocate_avoid hw
      (fun hc => (List.mem_append.mp (Template.openTyVarsFrom_scope _ (K := _) (fun _ h => h) 0 written w hc)).elim hann hwr)

private theorem Input.avoid_subst {input : Input} {S : Subst} {w : Nat}
    (hS : ∀ p ∈ S, w ∉ p.2.freeVars) (h : w ∉ input.rigidVars) :
    w ∉ (input.substTyFvars S).rigidVars := by
  intro hw
  obtain ⟨v, hv, him⟩ := Input.rigidVars_substTyFvars hw
  exact Subst.notMemOnTy hS (by simpa only [Ty.freeVars, List.mem_singleton] using (show w ≠ v from fun heq => h (heq.symm ▸ hv))) him

private theorem LetAnn.avoid_subst {ann : LetAnn} {S : Subst} {w : Nat}
    (hS : ∀ p ∈ S, w ∉ p.2.freeVars) (h : w ∉ ann.rigidVars) :
    w ∉ (ann.substTyFvars S).rigidVars := by
  intro hw
  obtain ⟨v, hv, him⟩ := LetAnn.rigidVars_substTyFvars hw
  exact Subst.notMemOnTy hS (by simpa only [Ty.freeVars, List.mem_singleton] using (show w ≠ v from fun heq => h (heq.symm ▸ hv))) him

private theorem branches_avoid_subst {brs : List (MatchPattern × Input)} {S : Subst} {w : Nat}
    (hS : ∀ p ∈ S, w ∉ p.2.freeVars) (h : w ∉ rigidBranchVars brs) :
    w ∉ rigidBranchVars (substInputBranches S brs) := by
  induction brs with
  | nil => simp [substInputBranches, rigidBranchVars]
  | cons pair rest ih =>
    simp only [rigidBranchVars, List.mem_append, not_or] at h
    exact fun hm => (List.mem_append.mp hm).elim (Input.avoid_subst hS h.1) (ih h.2)

private theorem mem_eraseBranches {brs : List (MatchPattern × Input)} {p : MatchPattern} {b : Input}
    (h : (p,b) ∈ brs) : (p,b.erase) ∈ eraseBranches brs := by
  induction brs with
  | nil => cases h
  | cons pair rest ih =>
    rcases List.mem_cons.mp h with heq | hm
    · cases heq; exact List.mem_cons_self ..
    · exact List.mem_cons_of_mem _ (ih hm)

private theorem branches_refs_subst {brs : List (MatchPattern × Input)} {ctx : Ctx} {S : Subst} {w : Nat}
    (hrefs : ∀ p b, (p,b) ∈ brs → b.erase.ForallOuter
      (fun i => ∀ M, ctx.env[i]? = some M → w ∉ M.body.freeVars) p.bindCount)
    (hS : ∀ p ∈ S, w ∉ p.2.freeVars) :
    ∀ p b, (p,b) ∈ substInputBranches S brs → b.erase.ForallOuter
      (fun i => ∀ M, (S.onCtx ctx).env[i]? = some M → w ∉ M.body.freeVars) p.bindCount := by
  intro p b hm
  rw [substInputBranches_eq_map] at hm
  obtain ⟨⟨oldpat,oldbody⟩, hold, heq⟩ := List.mem_map.mp hm
  cases heq
  simpa only [Input.erase_substTyFvars] using Expr.ForallOuter.lookupAvoid_onSubst
    (hrefs oldpat oldbody hold) hS

mutual
 theorem _root_.Infer.sourceLocality (h : Infer K F frontier ctx input next subst output ty) :
    ∀ {w}, w < frontier →
    input.erase.ForallOuter (fun i => ∀ M, ctx.env[i]? = some M → w ∉ M.body.freeVars) 0 →
    w ∉ input.rigidVars →
    (∀ p ∈ subst, w ∉ p.2.freeVars) ∧ w ∉ ty.freeVars ∧ w ∉ subst.map Prod.fst := by
  match h with
  | .backend hemb hi _ _ _ _ =>
    intro w hw hrefs hwe
    apply hi.sourceLocality hw
    · apply (Expr.ForallOuter.erase_iff _).mp
      rwa [Input.toCore_erase _ hemb]
    · intro hm
      exact hwe ((Input.toCore_rigidVars _ hemb w).mpr hm)
  | .lambda _ hs hb =>
    intro w hw hrefs hwe
    simp only [Input.erase, Expr.ForallOuter, Expr.rec_strong, Nat.zero_add] at hrefs
    simp only [Input.rigidVars, List.mem_append, not_or] at hwe
    have hp := hs.sourceAvoid hw (by intro t ht; cases ht; exact hwe.1)
    have hbrefs := Expr.ForallOuter.lookupAvoid_prepend (pre := [PolyTy.mkTrivial _]) hrefs
      (by intro M hM; rcases List.mem_singleton.mp hM with rfl; exact hp)
    obtain ⟨hS, hty, hD⟩ := hb.sourceLocality (Nat.lt_of_lt_of_le hw hs.frontier_le) hbrefs hwe.2
    exact ⟨hS, by simpa only [Ty.freeVars, List.mem_dedup, List.mem_append, not_or]
      using And.intro (Subst.notMemOnTy hS hp) hty, hD⟩
  | .app _ hf ha hu =>
    intro w hw hrefs hwe
    expose_names
    simp only [Input.erase, Expr.ForallOuter, Expr.rec_strong] at hrefs
    simp only [Input.rigidVars, List.mem_append, not_or] at hwe
    obtain ⟨hfS, hfTy, hfD⟩ := hf.sourceLocality hw hrefs.1 hwe.1
    obtain ⟨haS, haTy, haD⟩ := ha.sourceLocality (Nat.lt_of_lt_of_le hw hf.frontier_le)
      (by simpa only [Input.erase_substTyFvars] using Expr.ForallOuter.lookupAvoid_onSubst hrefs.2 hfS)
      (Input.avoid_subst hfS hwe.2)
    have hnew : w ∉ (Ty.fvar second).freeVars := by
      simp only [Ty.freeVars, List.mem_singleton]; have := hf.frontier_le; have := ha.frontier_le; omega
    have huA := UnifyRel.sourceAvoid_local hu.unifies (Subst.notMemOnTy haS hfTy)
      (by simpa only [Ty.freeVars, List.mem_dedup, List.mem_append, not_or] using And.intro haTy hnew)
    have hA := Subst.sourceAvoid_append_local (Subst.sourceAvoid_append_local ⟨hfS, hfD⟩ ⟨haS, haD⟩) huA
    exact ⟨hA.1, Subst.notMemOnTy huA.1 hnew, hA.2⟩
  | .letIn _ hr hc hb =>
    intro w hw hrefs hwe
    expose_names
    simp only [Input.erase, Expr.ForallOuter, Expr.rec_strong, Nat.zero_add] at hrefs
    simp only [Input.rigidVars, List.mem_append, not_or] at hwe
    obtain ⟨hrS, hrTy, hrD⟩ := hr.sourceLocality hw hrefs.1 hwe.1.2
    have hcA := hc.sourceAvoid (Nat.lt_of_lt_of_le hw hr.frontier_le) hrTy
      (LetAnn.avoid_subst hrS hwe.1.1)
    have hA := Subst.sourceAvoid_append_local ⟨hrS, hrD⟩ hcA
    have hfinalTy := Subst.notMemOnTy hcA.1 hrTy
    have hp : w ∉ (genScheme (K ++ softVars (substSoft (s1 ++ sCheck) F))
      (sCheck.onCtx (s1.onCtx ctx)).env (sCheck.onTy rhsTy)).body.freeVars :=
      fun hm => hfinalTy (Ty.freeVars_closeOver_subset hm)
    have hbrefs := Expr.ForallOuter.lookupAvoid_prepend (pre := [genScheme _ _ _])
      (Expr.ForallOuter.lookupAvoid_onSubst (Expr.ForallOuter.lookupAvoid_onSubst hrefs.2 hrS) hcA.1)
      (by intro M hM; rcases List.mem_singleton.mp hM with rfl; exact hp)
    obtain ⟨hbS, hbTy, hbD⟩ := hb.sourceLocality
      (Nat.lt_of_lt_of_le hw (hr.frontier_le.trans hc.frontier_le))
      (by simpa only [Input.erase_substTyFvars] using hbrefs) (Input.avoid_subst hA.1 hwe.2)
    have hAll := Subst.sourceAvoid_append_local hA ⟨hbS, hbD⟩
    exact ⟨hAll.1, hbTy, hAll.2⟩
  | .letSignature _ heq _ _ hr hc _ hb =>
    intro w hw hrefs hwe
    expose_names
    subst written
    simp only [Input.erase, Expr.ForallOuter, Expr.rec_strong, Nat.zero_add] at hrefs
    simp only [Input.rigidVars, List.mem_append, not_or] at hwe
    have hwr : w ∉ freshVars frontier ann.paramCount := fun hm => by have := freshVars_ge w hm; omega
    obtain ⟨hrS, hrTy, hrD⟩ := hr.sourceLocality (by omega)
      (by simpa only [Input.erase_openTyVars] using hrefs.1)
      (fun hm => (Input.rigidVars_openTyVarsFrom hm).elim hwe.1.2 hwr)
    have hcA := hc.sourceAvoid (Nat.lt_of_lt_of_le hw (by have := hr.frontier_le; omega)) hrTy
      (LetAnn.avoid_subst hrS hwe.1.1) hwr
    have hA := Subst.sourceAvoid_append_local ⟨hrS, hrD⟩ hcA
    have hp : w ∉ (signatureScheme (ann.substTyFvars (s1 ++ sCheck))
      (K ++ softVars (substSoft (s1 ++ sCheck) F)) (freshVars frontier ann.paramCount)
      (sCheck.onCtx (s1.onCtx ctx)) (sCheck.onTy rhsTy)).body.freeVars := by
      cases ann with
      | complete σ => exact LetAnn.avoid_subst hA.1 hwe.1.1
      | absent | template t | partialForall n t =>
        exact fun hm => Subst.notMemOnTy hcA.1 hrTy (Ty.freeVars_closeOver_subset hm)
    have hbrefs := Expr.ForallOuter.lookupAvoid_prepend (pre := [signatureScheme _ _ _ _ _])
      (Expr.ForallOuter.lookupAvoid_onSubst (Expr.ForallOuter.lookupAvoid_onSubst hrefs.2 hrS) hcA.1)
      (by intro M hM; rcases List.mem_singleton.mp hM with rfl; exact hp)
    obtain ⟨hbS, hbTy, hbD⟩ := hb.sourceLocality
      (Nat.lt_of_lt_of_le hw (by have := hr.frontier_le; have := hc.frontier_le; omega))
      (by simpa only [Input.erase_substTyFvars] using hbrefs) (Input.avoid_subst hA.1 hwe.2)
    have hAll := Subst.sourceAvoid_append_local hA ⟨hbS, hbD⟩
    exact ⟨hAll.1, hbTy, hAll.2⟩
  | .match_ _ hs _ hb =>
    intro w hw hrefs hwe
    expose_names
    simp only [Input.erase, Expr.ForallOuter, Expr.rec_strong, Nat.zero_add] at hrefs
    simp only [Input.rigidVars, List.mem_append, not_or] at hwe
    obtain ⟨hsS, hsTy, hsD⟩ := hs.sourceLocality hw hrefs.1 hwe.1
    have hnew : w ∉ (Ty.fvar first).freeVars := by
      simp only [Ty.freeVars, List.mem_singleton]; have := hs.frontier_le; omega
    obtain ⟨hbS, hbTy, hbD⟩ := hb.sourceLocality (by have := hs.frontier_le; omega)
      (branches_refs_subst (fun p b hm => hrefs.2 p b.erase (mem_eraseBranches hm)) hsS)
      hsTy hnew (branches_avoid_subst hsS hwe.2)
    have hA := Subst.sourceAvoid_append_local ⟨hsS, hsD⟩ ⟨hbS, hbD⟩
    exact ⟨hA.1, hbTy, hA.2⟩
 termination_by (input.size, 1)
 decreasing_by all_goals (simp only [Input.size, Input.size_substTyFvars, Input.size_openTyVars, sizeBranches_substInputBranches]; omega)

 theorem _root_.InferBranches.sourceLocality
    (h : InferBranches K F frontier ctx scrutTy resultTy brs next subst completed) :
    ∀ {w}, w < frontier →
    (∀ p b, (p,b) ∈ brs → b.erase.ForallOuter
      (fun i => ∀ M, ctx.env[i]? = some M → w ∉ M.body.freeVars) p.bindCount) →
    w ∉ scrutTy.freeVars → w ∉ resultTy.freeVars → w ∉ rigidBranchVars brs →
    (∀ p ∈ subst, w ∉ p.2.freeVars) ∧ w ∉ (subst.onTy resultTy).freeVars ∧ w ∉ subst.map Prod.fst := by
  match h with
  | .nil => intro w _ _ _ hρ _; exact ⟨by simp, by simpa using hρ, by simp⟩
  | .cons _ hlook hn hu₀ hb hu hr =>
    intro w hw hrefs hscrut hρ hbrs
    expose_names
    simp only [rigidBranchVars, List.mem_append, not_or] at hbrs
    have hcustom : w ∉ (Ty.customTy ctor.tyName ((freshVars frontier ctor.paramCount).map Ty.fvar)).freeVars := by
      intro hc; simp only [Ty.freeVars] at hc; rw [mem_TyList_freeVars] at hc
      obtain ⟨t, ht, hwt⟩ := hc; obtain ⟨x, hx, rfl⟩ := List.mem_map.mp ht
      simp only [Ty.freeVars, List.mem_singleton] at hwt
      have := freshVars_ge x hx; omega
    have hA₀ := UnifyRel.sourceAvoid_local hu₀.unifies hscrut hcustom
    have hta : ∀ t ∈ ((freshVars frontier ctor.paramCount).map Ty.fvar).map s0.onTy, w ∉ t.freeVars := by
      intro t ht; obtain ⟨t₀, ht₀, rfl⟩ := List.mem_map.mp ht
      obtain ⟨x, hx, rfl⟩ := List.mem_map.mp ht₀
      apply Subst.notMemOnTy hA₀.1
      simp only [Ty.freeVars, List.mem_singleton]; have := freshVars_ge x hx; omega
    have hbrefs : body.erase.ForallOuter
        (fun i => ∀ M,
          ((ctor.contents.map (Ty.openWith (((freshVars frontier ctor.paramCount).map Ty.fvar).map s0.onTy))).map PolyTy.mkTrivial
            ++ (s0.onCtx ctx).env)[i]? = some M → w ∉ M.body.freeVars) 0 := by
      apply Expr.ForallOuter.lookupAvoid_prepend
        (by simpa only [List.length_map, Nat.zero_add, MatchPattern.bindCount, hn] using
          Expr.ForallOuter.lookupAvoid_onSubst (hrefs (.named name count) body List.mem_cons_self) hA₀.1)
      intro M hM; obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hM
      obtain ⟨t₀, ht₀, rfl⟩ := List.mem_map.mp ht
      exact Ty.not_mem_freeVars_openWith hta ((ctor.closed t₀ ht₀).not_mem_freeVars w)
    obtain ⟨hbS, hbTy, hbD⟩ := hb.sourceLocality (by omega)
      (by simpa only [Input.erase_substTyFvars] using hbrefs) (Input.avoid_subst hA₀.1 hbrs.1)
    have hA₂ := UnifyRel.sourceAvoid_local hu.unifies hbTy
      (Subst.notMemOnTy hbS (Subst.notMemOnTy hA₀.1 hρ))
    have hApre := Subst.sourceAvoid_append_local (Subst.sourceAvoid_append_local hA₀ ⟨hbS,hbD⟩) hA₂
    obtain ⟨hrS, hrTy, hrD⟩ := hr.sourceLocality (by have := hb.frontier_le; omega)
      (by
        have hf := branches_refs_subst
          (fun p b hm => hrefs p b (List.mem_cons_of_mem _ hm)) hApre.1
        simpa only [Subst.onCtx_append] using hf)
      (Subst.notMemOnTy hA₂.1 (Subst.notMemOnTy hbS (Subst.notMemOnTy hA₀.1 hscrut)))
      (Subst.notMemOnTy hA₂.1 (Subst.notMemOnTy hbS (Subst.notMemOnTy hA₀.1 hρ)))
      (branches_avoid_subst hApre.1 hbrs.2)
    have hA := Subst.sourceAvoid_append_local hApre ⟨hrS,hrD⟩
    exact ⟨hA.1, by simpa only [Subst.onTy_append] using hrTy, hA.2⟩
  | .consWild _ hb hu hr =>
    intro w hw hrefs hscrut hρ hbrs
    expose_names
    simp only [rigidBranchVars, List.mem_append, not_or] at hbrs
    obtain ⟨hbS, hbTy, hbD⟩ := hb.sourceLocality hw
      (hrefs .wildcard body List.mem_cons_self) hbrs.1
    have hA₂ := UnifyRel.sourceAvoid_local hu.unifies hbTy (Subst.notMemOnTy hbS hρ)
    have hApre := Subst.sourceAvoid_append_local ⟨hbS,hbD⟩ hA₂
    obtain ⟨hrS, hrTy, hrD⟩ := hr.sourceLocality (Nat.lt_of_lt_of_le hw hb.frontier_le)
      (by
        have hf := branches_refs_subst
          (fun p b hm => hrefs p b (List.mem_cons_of_mem _ hm)) hApre.1
        simpa only [Subst.onCtx_append] using hf)
      (Subst.notMemOnTy hA₂.1 (Subst.notMemOnTy hbS hscrut))
      (Subst.notMemOnTy hA₂.1 (Subst.notMemOnTy hbS hρ))
      (branches_avoid_subst hApre.1 hbrs.2)
    have hA := Subst.sourceAvoid_append_local hApre ⟨hrS,hrD⟩
    exact ⟨hA.1, by simpa only [Subst.onTy_append] using hrTy, hA.2⟩
 termination_by (sizeBranches brs, 0)
 decreasing_by all_goals (simp only [sizeBranches, Input.size_substTyFvars, sizeBranches_substInputBranches]; omega)
end

end Elaboration



theorem RecSpec.notMem_freeVars_onSubstSource {S : Subst} {spec : RecSpec} {w : Nat}
    (hS : ∀ p ∈ S, w ∉ p.2.freeVars) (h : w ∉ spec.freeVars) :
    w ∉ (spec.onSubstSource S).freeVars := by
  cases spec with
  | mono ty => exact Subst.notMemOnTy hS h
  | poly scheme => exact Subst.notMemOnTy hS h

theorem RecSpec.mono_getElem?_map_onSubstSource {S : Subst} {specs : List RecSpec}
    {member : Nat} {ty : Ty}
    (h : (specs.map (RecSpec.onSubstSource S))[member]? = some (.mono ty)) :
    ∃ old, specs[member]? = some (.mono old) ∧ ty = S.onTy old := by
  rw [List.getElem?_map] at h
  obtain ⟨s, hs, heq⟩ := Option.map_eq_some_iff.mp h
  cases s with
  | mono old => exact ⟨old, hs, (RecSpec.mono.inj heq).symm⟩
  | poly scheme => cases heq

theorem RecSpecs.PendingSeeds.onSubst_source {base : Nat} {ctx : Ctx} {specs : List RecSpec}
    {done done' : List Nat} {S : Subst} (h : RecSpecs.PendingSeeds base ctx specs done)
    (hdone : ∀ member ∈ done, member ∈ done')
    (havoid : ∀ member ty, specs[member]? = some (.mono ty) → member ∉ done' →
      (∀ p ∈ S, base + member ∉ p.2.freeVars) ∧ base + member ∉ S.map Prod.fst) :
    RecSpecs.PendingSeeds base (S.onCtx ctx) (specs.map (RecSpec.onSubstSource S)) done' := by
  constructor
  · intro member ty hty hm
    obtain ⟨old, hold, rfl⟩ := RecSpec.mono_getElem?_map_onSubstSource hty
    rw [h.mono member old hold (fun hc => hm (hdone member hc))]
    apply Ty.substFvars_eq_self_of_no_key
    intro p hp hc
    apply (havoid member old hold hm).2
    apply List.mem_map.mpr
    refine ⟨p, hp, ?_⟩
    simpa only [Ty.freeVars, List.mem_singleton] using hc
  · intro member ty hty hm j spec hs hj
    obtain ⟨old, hold, _⟩ := RecSpec.mono_getElem?_map_onSubstSource hty
    rw [List.getElem?_map] at hs
    obtain ⟨oldSpec, holdSpec, rfl⟩ := Option.map_eq_some_iff.mp hs
    exact RecSpec.notMem_freeVars_onSubstSource (havoid member old hold hm).1
      (h.other member old hold (fun hc => hm (hdone member hc)) j oldSpec holdSpec hj)
  · intro member ty hty hm
    obtain ⟨old, hold, _⟩ := RecSpec.mono_getElem?_map_onSubstSource hty
    exact Subst.onCtx_avoid (h.env member old hold (fun hc => hm (hdone member hc)))
      (havoid member old hold hm).1
