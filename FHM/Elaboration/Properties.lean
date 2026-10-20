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
  | .primLitUnit | .primLitInt | .primLitNat | .primLitChar | .primBinOpIntAdd | .primBinOpIntSub | .primBinOpIntLt _ _ _ _ | .primBinOpCharLt _ _ _ _ => exact Nat.le_refl _
  | .var _ | .ctor _ => exact Nat.le_add_right _ _
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
  | .primLitUnit => intro _ _ _; exact ⟨.prim, by simp⟩
  | .primLitInt => intro _ _ _; exact ⟨.prim, by simp⟩
  | .primLitNat => intro _ _ _; exact ⟨.prim, by simp⟩
  | .primLitChar => intro _ _ _; exact ⟨.prim, by simp⟩
  | .primBinOpIntAdd => intro _ _ _; exact ⟨.arrow .prim (.arrow .prim .prim), by simp⟩
  | .primBinOpIntSub => intro _ _ _; exact ⟨.arrow .prim (.arrow .prim .prim), by simp⟩
  | .primBinOpIntLt _ _ _ _ => intro _ _ _; exact ⟨.arrow .prim (.arrow .prim (.customTy (by simp))), by simp⟩
  | .primBinOpCharLt _ _ _ _ => intro _ _ _; exact ⟨.arrow .prim (.arrow .prim (.customTy (by simp))), by simp⟩
  | .var hlook =>
      intro hctx _ _
      refine ⟨?_, by simp⟩
      exact Ty.openVars_belowFvars ((hctx _ (List.mem_of_getElem? hlook)).mono (by omega))
        (fun x hx => by have := freshVars_lt x hx; omega)
  | .ctor hlook =>
      intro _ _ _
      refine ⟨?_, by simp⟩
      exact Ty.openVars_belowFvars (Ty.BelowFvars.of_noFreeVars (Ctor.toTy_body_noFreeVars _))
        (fun x hx => by have := freshVars_lt x hx; omega)
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
    have hvalid := hvalid.1
    have hanns : ∀ ann ∈ anns, ∀ v ∈ ann.rigidVars, v < frontier := by
      intro ann ha v hv
      exact rigid_soft_lt hK hF v (hscope.1 v (by
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
  | @letRec anns K bindings ctx body resultTy specs groups prefixes G L hg hw hp hG hAnn hRhs hFits _ _ _ ihMono ihPoly ihBody =>
    intro env' hgen
    have hextra : ∀ extra : Env, List.Forall₂ PolyTy.Generalizes (extra ++ env') (extra ++ ctx.env) := by
      intro extra
      induction extra with
      | nil => exact hgen
      | cons head tail ih => exact .cons (PolyTy.Generalizes.refl head) ih
    let avoid := K ++ env'.freeVars ++ G ++ specs.flatMap RecSpec.freeVars
    obtain ⟨W, hWlen, hWnd, hWavoid⟩ := exists_fresh_names avoid G.length
    have hGW : ∀ g ∈ G, g ∉ W := by
      intro g hg hw
      exact hWavoid g hw (by simp only [avoid, List.mem_append]; tauto)
    have hWmono : ∀ ty, .mono ty ∈ specs → ∀ w ∈ W, w ∉ ty.freeVars := by
      intro ty ht w hw hv
      exact hWavoid w hw (by
        simp only [avoid, List.mem_append]
        right
        exact List.mem_flatMap.mpr ⟨.mono ty, ht, hv⟩)
    let specs' := specs.map (fun spec => RecSpec.onSubstSource [] (RecSpec.onSubst (G.zip (W.map Ty.fvar)) spec))
    let prefixes' := prefixes.map (recRenameNames G W)
    let L' := G ++ W ++ L
    have annNil : anns.map (LetAnn.substTyFvars []) = anns := by
      conv_rhs => rw [← List.map_id anns]
      apply List.map_congr_left
      intro ann _
      exact ann.substTyFvars_eq_self_of_fixes (fun _ _ => rfl)
    have hw' : RecSpecs.WF (anns.map LetAnn.recModeAnn) (bindings.map Input.erase) specs' W := by
      simpa only [annNil] using Elaboration.RecSpecs.WF.subst_fresh_pool (S := []) hw (by simp) hWnd
    have hp' : RecPrefixesWF anns specs' prefixes' W := by
      simpa only [annNil] using hp.subst_fresh_pool (S := []) hWlen hWnd
    have hannsLen : anns.length = specs.length := by
      have hh := congrArg List.length hw.anns_eq
      simpa using hh.symm
    have hpData := fun i hi => hp.get hannsLen (i := i) hi
    have mapNil : ∀ xs : List PolyTy, xs.map (Subst.onPolyTy []) = xs := by
      intro xs
      rw [show Subst.onPolyTy [] = id from funext Subst.onPolyTy_nil, List.map_id]
    have hcompleted : recCompletedSchemes specs' prefixes' W = recCompletedSchemes specs prefixes G := by
      simpa only [mapNil] using recCompletedSchemes_subst_fresh_pool (S := []) (by simp) hWlen hw.nodup hWnd
        hGW hWmono (by simp) (by simp) hw.mono_lc hpData
    have oldFresh : ∀ Xs, FreshNames (W ++ L') W.length Xs → FreshNames (G ++ L) G.length Xs := by
      intro Xs hf
      refine ⟨hf.length.trans hWlen, hf.nodup, ?_⟩
      intro x hx hl
      exact hf.avoid x hx (by simp only [L', List.mem_append] at hl ⊢; tauto)
    have hGXs : ∀ Xs, FreshNames (W ++ L') W.length Xs → ∀ g ∈ G, g ∉ Xs := by
      intro Xs hf g hg hx
      exact hf.avoid g hx (by simp only [L', List.mem_append]; tauto)
    have hWXs : ∀ Xs, FreshNames (W ++ L') W.length Xs → ∀ w ∈ W, w ∉ Xs := by
      intro Xs hf w hw hx
      exact hf.avoid w hx (List.mem_append_left _ hw)
    have hstage : ∀ Xs, FreshNames (W ++ L') W.length Xs → ∀ done,
        specs'.mapIdx (recStageEntry prefixes' done W Xs) = specs.mapIdx (recStageEntry prefixes done G Xs) := by
      intro Xs hf done
      simpa only [mapNil] using recStageSchemes_subst_fresh_pool (S := []) (done := done) (by simp)
        hWlen hw.nodup hWnd hGW hWmono (by simp) (by simp) hw.mono_lc hpData
        (hf.length.trans hWlen) (hGXs Xs hf) (hWXs Xs hf) (by simp)
    have hsquare : ∀ ty, .mono ty ∈ specs → ∀ Xs, FreshNames (W ++ L') W.length Xs →
        Ty.renameG W Xs (Ty.renameG G W ty) = Ty.renameG G Xs ty := by
      intro ty ht Xs hf
      simpa only [Subst.onTy_nil] using Ty.renameG_subst_fresh_pool (S := []) (hw.mono_lc ty ht) (by simp)
        hWlen hw.nodup hWnd hGW (hWmono ty ht) (by simp) (by simp)
        (hf.length.trans hWlen) (hGXs Xs hf) (hWXs Xs hf) (by simp)
    refine Typing.letRec (specs := specs') (groups := groups) (prefixes := prefixes') (G := W) (L := L')
      hg hw' hp' ?_ hAnn hRhs ?_ ?_ ?_ ?_
    · intro w hw hm
      exact hWavoid w hw (by simp only [avoid, List.mem_append] at hm ⊢; tauto)
    · intro stage component hs Xs hf member hm rhs ann names ty hri hai hni hti
      rw [List.getElem?_map] at hni hti
      obtain ⟨names0, hn0, rfl⟩ := Option.map_eq_some_iff.mp hni
      obtain ⟨spec, ht0, heq⟩ := Option.map_eq_some_iff.mp hti
      cases spec with
      | poly scheme => cases heq
      | mono ty0 =>
        cases heq
        obtain ⟨_, _, hsub⟩ := hp.member member ann names0 hai hn0
        change ann.RecFits (recRenameNames W Xs (recRenameNames G W names0))
          (Ty.renameG W Xs (Ty.renameG G W ty0))
        rw [recRenameNames_composition hWlen (hf.length.trans hWlen) hWnd hsub,
          hsquare ty0 (List.mem_of_getElem? ht0) Xs hf]
        exact hFits stage component hs Xs (oldFresh Xs hf) member hm rhs ann names0 ty0 hri hai hn0 ht0
    · intro stage component hs Xs hf member hm rhs ann names ty hri hai hni hti
      rw [List.getElem?_map] at hni hti
      obtain ⟨names0, hn0, rfl⟩ := Option.map_eq_some_iff.mp hni
      obtain ⟨spec, ht0, heq⟩ := Option.map_eq_some_iff.mp hti
      cases spec with
      | poly scheme => cases heq
      | mono ty0 =>
        cases heq
        obtain ⟨_, _, hsub⟩ := hp.member member ann names0 hai hn0
        change Typing (K ++ Xs)
          (recStageCtx { ctx with env := env' } specs' prefixes' (groups.take stage).flatten W Xs)
          (rhs.openTyVars (recRenameNames W Xs (recRenameNames G W names0)))
          (Ty.renameG W Xs (Ty.renameG G W ty0))
        rw [recRenameNames_composition hWlen (hf.length.trans hWlen) hWnd hsub,
          hsquare ty0 (List.mem_of_getElem? ht0) Xs hf]
        have hc := ihMono stage component hs Xs (oldFresh Xs hf) member hm rhs ann names0 ty0 hri hai hn0 ht0
          (hextra (specs.mapIdx (recStageEntry prefixes (groups.take stage).flatten G Xs)))
        simpa only [recStageCtx, hstage Xs hf] using hc
    · intro member rhs scheme hri hsi Ys hy
      rw [List.getElem?_map] at hsi
      obtain ⟨spec, hs0, heq⟩ := Option.map_eq_some_iff.mp hsi
      cases spec with
      | mono ty => cases heq
      | poly scheme0 =>
        cases heq
        have hy0 : FreshNames L scheme0.paramCount Ys :=
          ⟨hy.length, hy.nodup, fun y hy' hl => hy.avoid y hy' (by simp only [L', List.mem_append]; tauto)⟩
        have hc := ihPoly member rhs scheme0 hri hs0 Ys hy0 (hextra (recCompletedSchemes specs prefixes G))
        simpa only [recBodyCtx, hcompleted] using hc
    · have hc := ihBody (hextra (recCompletedSchemes specs prefixes G))
      simpa only [recBodyCtx, hcompleted] using hc
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

theorem Input.avoid_subst {input : Input} {S : Subst} {w : Nat}
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

 theorem _root_.InferRecComponent.sourceLocality_of_infer
    (h : InferRecComponent K F members index frontier ctx bindings specs next S outputs facts)
    (hInfer : ∀ {κ F' Ψ c e Ψ' T output ty}, e.size ≤ sizeBindings bindings →
      Infer κ F' Ψ c e Ψ' T output ty →
      ∀ {w}, w < Ψ →
      e.erase.ForallOuter (fun i => ∀ M, c.env[i]? = some M → w ∉ M.body.freeVars) 0 →
      w ∉ e.rigidVars →
      (∀ p ∈ T, w ∉ p.2.freeVars) ∧ w ∉ ty.freeVars ∧ w ∉ T.map Prod.fst) :
    ∀ {w}, w < frontier →
    (∀ j rhs, index + j ∈ members → bindings[j]? = some rhs →
      rhs.erase.ForallOuter
        (fun i => ∀ M, ctx.env[i]? = some M → w ∉ M.body.freeVars) 0 ∧ w ∉ rhs.rigidVars) →
    (∀ j ty, index + j ∈ members → specs[j]? = some (.mono ty) → w ∉ ty.freeVars) →
    (∀ p ∈ S, w ∉ p.2.freeVars) ∧ w ∉ S.map Prod.fst := by
  match h with
  | .nil => intro w _ _ _; exact ⟨by simp, by simp⟩
  | .consSelected hsel hi hu hrest =>
    intro w hw hrefs htargets
    expose_names
    have hrhs := hrefs 0 rhs (by simpa using hsel) rfl
    obtain ⟨hiS, hiTy, hiD⟩ := hInfer (by simp only [sizeBindings]; omega) hi hw hrhs.1 hrhs.2
    have ht : w ∉ expected.freeVars := htargets 0 expected (by simpa using hsel) rfl
    have huS : ∀ p ∈ s2, w ∉ p.2.freeVars := by
      intro p hp hwp
      exact (hu.unifies.range_mem p hp w hwp).elim hiTy (Subst.notMemOnTy hiS ht)
    have huD : w ∉ s2.map Prod.fst := by
      intro hm
      obtain ⟨p, hp, hpw⟩ := List.mem_map.mp hm
      have hmem := hu.unifies.dom_mem p hp
      rw [hpw] at hmem
      exact hmem.elim hiTy (Subst.notMemOnTy hiS ht)
    have hS12 : ∀ p ∈ s1 ++ s2, w ∉ p.2.freeVars :=
      fun p hp => (List.mem_append.mp hp).elim (hiS p) (huS p)
    have hrestRefs : ∀ j rhs', index + 1 + j ∈ members →
        (rest.map (Input.substTyFvars (s1 ++ s2)))[j]? = some rhs' →
        rhs'.erase.ForallOuter
          (fun i => ∀ M, (s2.onCtx (s1.onCtx ctx)).env[i]? = some M → w ∉ M.body.freeVars) 0 ∧
          w ∉ rhs'.rigidVars := by
      intro j rhs' hj hget
      rw [List.getElem?_map] at hget
      obtain ⟨old, hold, rfl⟩ := Option.map_eq_some_iff.mp hget
      have horig := hrefs (j + 1) old
        (by simpa only [Nat.add_assoc, Nat.add_comm 1 j] using hj)
        (by simpa only [List.getElem?_cons_succ] using hold)
      refine ⟨?_, Input.avoid_subst hS12 horig.2⟩
      simpa only [Input.erase_substTyFvars, Subst.onCtx_append] using
        Expr.ForallOuter.lookupAvoid_onSubst (S := s1 ++ s2) horig.1 hS12
    have hrestTargets : ∀ j ty, index + 1 + j ∈ members →
        (specs_1.map (RecSpec.onSubstSource (s1 ++ s2)))[j]? = some (.mono ty) →
        w ∉ ty.freeVars := by
      intro j ty hj hget
      rw [List.getElem?_map] at hget
      obtain ⟨old, hold, heq⟩ := Option.map_eq_some_iff.mp hget
      cases old with
      | poly σ => cases heq
      | mono τ =>
          cases RecSpec.mono.inj heq
          exact Subst.notMemOnTy hS12 (htargets (j + 1) τ
            (by simpa only [Nat.add_assoc, Nat.add_comm 1 j] using hj)
            (by simpa only [List.getElem?_cons_succ] using hold))
    obtain ⟨hrS, hrD⟩ := hrest.sourceLocality_of_infer
      (fun he h => hInfer (by
        simp only [sizeBindings_map_substTyFvars] at he
        simp only [sizeBindings]; omega) h)
      (Nat.lt_of_lt_of_le hw hi.frontier_le) hrestRefs hrestTargets
    refine ⟨?_, ?_⟩
    · intro p hp
      rw [List.mem_append, List.mem_append] at hp
      rcases hp with (hp | hp) | hp
      · exact hiS p hp
      · exact huS p hp
      · exact hrS p hp
    · simpa only [List.map_append, List.mem_append, not_or] using
        And.intro (And.intro hiD huD) hrD
  | .skipMono _ hrest | .skipPoly hrest =>
    intro w hw hrefs htargets
    apply hrest.sourceLocality_of_infer
      (fun he h => hInfer (by simp only [sizeBindings]; omega) h) hw
    · intro j rhs hj hget
      exact hrefs (j + 1) rhs
        (by simpa only [Nat.add_assoc, Nat.add_comm 1 j] using hj)
        (by simpa only [List.getElem?_cons_succ] using hget)
    · intro j ty hj hget
      exact htargets (j + 1) ty
        (by simpa only [Nat.add_assoc, Nat.add_comm 1 j] using hj)
        (by simpa only [List.getElem?_cons_succ] using hget)
 termination_by structural h

/-- Only live type specs and exports affect the recursive term environment. -/
def RecState.Avoids (w : Nat) (state : RecState) : Prop :=
  (∀ spec ∈ state.specs, w ∉ spec.freeVars) ∧
  ∀ scheme ∈ state.exports.filterMap id, w ∉ scheme.body.freeVars

theorem RecState.Avoids.exported {state : RecState} (h : state.Avoids w)
    (hs : some scheme ∈ state.exports) : w ∉ scheme.body.freeVars :=
  h.2 scheme (List.mem_filterMap.mpr ⟨some scheme, hs, rfl⟩)

theorem RecState.Avoids.init {anns : List LetAnn} (hw : w < base)
    (hanns : ∀ ann ∈ anns, w ∉ ann.rigidVars) : (RecState.init base anns).Avoids w := by
  have hmode : ∀ scheme, some scheme ∈ anns.map LetAnn.recModeAnn → w ∉ scheme.body.freeVars := by
    intro scheme hs
    obtain ⟨ann, ha, heq⟩ := List.mem_map.mp hs
    cases ann with
    | absent | template | partialForall => cases heq
    | complete original =>
      cases heq
      exact hanns _ ha
  constructor
  · intro spec hs
    rcases RecSpec.mem_init hs with ⟨m, hlo, _, rfl⟩ | ⟨scheme, hsigma, rfl⟩
    · simp only [RecSpec.freeVars, Ty.freeVars, List.mem_singleton]
      omega
    · exact hmode scheme hsigma
  · intro scheme hs
    obtain ⟨old, ho, heq⟩ := List.mem_filterMap.mp hs
    exact hmode scheme (heq ▸ ho)

theorem RecState.Avoids.onSubst {state : RecState} (h : state.Avoids w)
    (hS : ∀ p ∈ S, w ∉ p.2.freeVars) : (state.onSubst S).Avoids w := by
  constructor
  · intro spec hs
    obtain ⟨old, ho, rfl⟩ := List.mem_map.mp hs
    cases old with
    | mono ty => exact Subst.notMemOnTy hS (h.1 _ ho)
    | poly scheme => exact Subst.notMemOnTy hS (h.1 _ ho)
  · intro scheme hs
    obtain ⟨old, ho, heq⟩ := List.mem_filterMap.mp hs
    obtain ⟨original, horiginal, rfl⟩ := List.mem_map.mp ho
    obtain ⟨sigma, hsigma, heq'⟩ := Option.map_eq_some_iff.mp heq
    subst scheme
    exact Subst.notMemOnTy hS (h.exported (hsigma ▸ horiginal))

theorem RecState.Avoids.installOpenings {state : RecState} (h : state.Avoids w) :
    (state.installOpenings members openings).Avoids w := h

theorem RecState.Avoids.setSigned {state : RecState} {member : Nat} {names : List Nat}
    {output : Expr} {facts : RecFacts} (h : state.Avoids w) :
    (state.setSigned member names output facts).Avoids w := h

theorem RecState.Avoids.entries {state : RecState} (h : state.Avoids w) :
    ∀ scheme ∈ state.entries, w ∉ scheme.body.freeVars := by
  intro scheme hs
  obtain ⟨⟨spec, exported⟩, hp, heq⟩ := List.mem_map.mp hs
  have hmem := List.of_mem_zip hp
  cases exported with
  | none =>
    subst scheme
    cases spec with
    | mono ty => exact h.1 _ hmem.1
    | poly sigma => exact h.1 _ hmem.1
  | some sigma =>
    cases heq
    exact h.exported hmem.2

theorem RecState.Avoids.rhsCtx {state : RecState} {e : Expr} {groupSize : Nat} {ctx : Ctx} (h : state.Avoids w)
    (hlen : state.entries.length = groupSize)
    (href : e.ForallOuter (fun i => ∀ M, ctx.env[i]? = some M → w ∉ M.body.freeVars) groupSize) :
    e.ForallOuter (fun i => ∀ M, (state.rhsCtx ctx).env[i]? = some M → w ∉ M.body.freeVars) 0 := by
  exact Expr.ForallOuter.lookupAvoid_prepend (pre := state.entries)
    (by simpa only [Nat.zero_add, hlen] using href) h.entries

theorem RecState.Avoids.exportComponent {state : RecState} {members pool : List Nat}
    {written : List (List Nat)} {outputs : List (Option Expr)} {facts : List RecFacts} (h : state.Avoids w) :
    (state.exportComponent members written pool outputs facts).Avoids w := by
  refine ⟨h.1, ?_⟩
  intro scheme hs
  obtain ⟨old, ho, heq⟩ := List.mem_filterMap.mp hs
  obtain ⟨i, hi, heq'⟩ := List.mem_mapIdx.mp ho
  subst old
  split at heq
  · cases hlookup : state.specs[i]? with
    | none => simp [hlookup] at heq
    | some spec =>
      simp only [hlookup, bind, pure, Option.bind_some] at heq
      cases heq
      cases spec with
      | mono ty => exact fun hv => h.1 _ (List.mem_of_getElem? hlookup) (Ty.freeVars_closeOver_subset hv)
      | poly sigma => exact h.1 _ (List.mem_of_getElem? hlookup)
  · exact h.exported (heq ▸ List.getElem_mem hi)

theorem FinishRecComponent.avoids (h : FinishRecComponent K soft members ctx state outputs facts final)
    (ha : state.Avoids w) : final.Avoids w := by
  cases h
  exact ha.exportComponent

private theorem opening_template_avoid {template : Template} {names : List Nat}
    (ht : w ∉ template.rigidVars) (hn : w ∉ names) :
    w ∉ (template.openTyVarsFrom 0 names).rigidVars := by
  intro hv
  have hh := template.openTyVarsFrom_scope (K := template.rigidVars) (fun _ h => h) 0 names w hv
  exact (List.mem_append.mp hh).elim ht hn

theorem OpenRecAnn.expected_avoid (h : OpenRecAnn frontier ann next opening) (hw : w < frontier)
    (ha : w ∉ ann.rigidVars) (he : opening.expected = some ty) : w ∉ ty.freeVars := by
  cases h with
  | absent | complete => cases he
  | template halloc _ =>
    cases he
    simpa only [halloc] using Template.allocate_avoid hw ha
  | @partialForall next ty frontier count template halloc _ =>
    cases he
    have hn : w ∉ freshVars frontier count := fun hm => by have := freshVars_ge w hm; omega
    have hh := Template.allocate_avoid (frontier := frontier + count) (by omega : w < frontier + count)
      (opening_template_avoid ha hn)
    simpa only [halloc] using hh

theorem OpenRecAnns.expected_avoid (h : OpenRecAnns members index frontier anns next openings)
    (hw : w < frontier) (ha : ∀ ann ∈ anns, w ∉ ann.rigidVars) :
    ∀ opening ∈ openings, ∀ ty, opening.expected = some ty → w ∉ ty.freeVars := by
  induction h with
  | nil => intro opening hm; cases hm
  | skip _ _ ih =>
    intro opening hm ty he
    rcases List.mem_cons.mp hm with rfl | hm
    · cases he
    · exact ih hw (fun ann hm => ha ann (List.mem_cons_of_mem _ hm)) opening hm ty he
  | cons _ hh ht ih =>
    intro opening hm ty he
    rcases List.mem_cons.mp hm with rfl | hm
    · exact hh.expected_avoid hw (ha _ List.mem_cons_self) he
    · exact ih (Nat.lt_of_lt_of_le hw hh.frontier_le)
        (fun ann hm => ha ann (List.mem_cons_of_mem _ hm)) opening hm ty he

private theorem openRecSources_locality {openings : List RecOpening} {bindings : List Input}
    (ho : ∀ opening ∈ openings, w ∉ opening.written)
    (hr : ∀ rhs ∈ bindings, rhs.erase.ForallOuter P depth ∧ w ∉ rhs.rigidVars) :
    ∀ rhs ∈ openRecSources openings bindings, rhs.erase.ForallOuter P depth ∧ w ∉ rhs.rigidVars := by
  induction bindings generalizing openings with
  | nil => cases openings <;> intro rhs hm <;> cases hm
  | cons rhs rest ih =>
    cases openings with
    | nil => exact hr
    | cons opening openings =>
      intro source hs
      rcases List.mem_cons.mp hs with rfl | hs
      · refine ⟨by simpa only [Input.erase_openTyVars] using (hr rhs List.mem_cons_self).1, ?_⟩
        intro hv
        exact (Input.rigidVars_openTyVarsFrom hv).elim (hr rhs List.mem_cons_self).2 (ho opening List.mem_cons_self)
      · exact ih (fun opening ho' => ho opening (List.mem_cons_of_mem _ ho'))
          (fun rhs hr' => hr rhs (List.mem_cons_of_mem _ hr')) source hs

private theorem recShapes_avoid {state : RecState} (ha : state.Avoids w)
    (ho : ∀ opening ∈ openings, ∀ ty, opening.expected = some ty → w ∉ ty.freeVars) :
    ∀ shape ∈ state.shapes members openings, w ∉ shape.1.freeVars ∧
      ∀ ty, shape.2 = some ty → w ∉ ty.freeVars := by
  intro shape hs
  obtain ⟨i, _, heq⟩ := List.mem_filterMap.mp hs
  cases hspec : state.specs[i]? with
  | none => simp [hspec] at heq
  | some spec =>
    cases spec with
    | poly scheme => simp [hspec, RecSpec.monoTy?] at heq
    | mono ty =>
      cases hopen : openings[i]? with
      | none => simp [hspec, RecSpec.monoTy?, hopen] at heq
      | some opening =>
        simp [hspec, RecSpec.monoTy?, hopen] at heq
        subst shape
        exact ⟨ha.1 _ (List.mem_of_getElem? hspec), ho opening (List.mem_of_getElem? hopen)⟩

private theorem FinishRecComponent.avoid_lengths
    (h : FinishRecComponent K soft members ctx state outputs facts final) :
    final.specs.length = state.specs.length ∧ final.exports.length = state.exports.length := by
  cases h
  exact ⟨rfl, List.length_mapIdx⟩


 theorem _root_.InferRecStrata.sourceLocality_of_infer
    (h : InferRecStrata K F frontier ctx anns bindings state groups next S final)
    (hInfer : ∀ {κ F' Ψ c e Ψ' T output ty}, e.size ≤ sizeBindings bindings →
      Infer κ F' Ψ c e Ψ' T output ty →
      ∀ {w}, w < Ψ →
      e.erase.ForallOuter (fun i => ∀ M, c.env[i]? = some M → w ∉ M.body.freeVars) 0 →
      w ∉ e.rigidVars →
      (∀ p ∈ T, w ∉ p.2.freeVars) ∧ w ∉ ty.freeVars ∧ w ∉ T.map Prod.fst)
    (hw : w < frontier) (ha : state.Avoids w)
    (hlenS : state.specs.length = bindings.length)
    (hlenE : state.exports.length = bindings.length)
    (hanns : ∀ ann ∈ anns, w ∉ ann.rigidVars)
    (hrhs : ∀ rhs ∈ bindings, rhs.erase.ForallOuter
      (fun i => ∀ M, ctx.env[i]? = some M → w ∉ M.body.freeVars) bindings.length ∧ w ∉ rhs.rigidVars) :
    (∀ p ∈ S, w ∉ p.2.freeVars) ∧ w ∉ S.map Prod.fst ∧ final.Avoids w := by
  match h with
  | .nil => exact ⟨by simp, by simp, ha⟩
  | .cons ho hp hc hf hr =>
    expose_names
    have hpre := hp.sourceAvoid (recShapes_avoid ha.installOpenings (ho.expected_avoid hw hanns))
    have hapre : ((state.installOpenings component openings).onSubst pre).Avoids w :=
      ha.installOpenings.onSubst hpre.1
    have hentry : (((state.installOpenings component openings).onSubst pre).entries).length = bindings.length := by
      rw [RecState.entries_length]
      · simpa [RecState.onSubst, RecState.installOpenings] using hlenS
      · simpa [RecState.onSubst, RecState.installOpenings] using hlenE.trans hlenS.symm
    have hopen : ∀ rhs ∈ openRecSources openings bindings, rhs.erase.ForallOuter
        (fun i => ∀ M, ctx.env[i]? = some M → w ∉ M.body.freeVars) bindings.length ∧ w ∉ rhs.rigidVars :=
      openRecSources_locality (fun opening hm hv => by
        have hh := ho.written_range w (List.mem_flatMap.mpr ⟨opening, hm, hv⟩)
        omega) hrhs
    have hcomponent := hc.sourceLocality_of_infer
      (fun he hi => hInfer (by simpa only [sizeBindings_map_substTyFvars, sizeBindings_openRecSources] using he) hi)
      (Nat.lt_of_lt_of_le hw ho.frontier_le)
      (by
        intro j rhs _ hget
        obtain ⟨old, hold, rfl⟩ := Option.map_eq_some_iff.mp (by simpa only [List.getElem?_map] using hget)
        have hh := hopen old (List.mem_of_getElem? hold)
        refine ⟨?_, Input.avoid_subst hpre.1 hh.2⟩
        exact hapre.rhsCtx hentry (by simpa only [Input.erase_substTyFvars] using
          Expr.ForallOuter.lookupAvoid_onSubst hh.1 hpre.1))
      (by intro j ty _ hget; exact hapre.1 _ (List.mem_of_getElem? hget))
    have hboth : ∀ p ∈ pre ++ current, w ∉ p.2.freeVars :=
      fun p hm => (List.mem_append.mp hm).elim (hpre.1 p) (hcomponent.1 p)
    have hafinal := hf.avoids (ha.installOpenings.onSubst hboth)
    have hlength := hf.avoid_lengths
    have htailS : exported.specs.length = (bindings.map (Input.substTyFvars (pre ++ current))).length := by
      simpa [RecState.onSubst, RecState.installOpenings] using hlength.1.trans (by simpa [RecState.onSubst, RecState.installOpenings] using hlenS)
    have htailE : exported.exports.length = (bindings.map (Input.substTyFvars (pre ++ current))).length := by
      simpa [RecState.onSubst, RecState.installOpenings] using hlength.2.trans (by simpa [RecState.onSubst, RecState.installOpenings] using hlenE)
    obtain ⟨htS, htD, htA⟩ := hr.sourceLocality_of_infer
      (fun he hi => hInfer (by simpa only [sizeBindings_map_substTyFvars] using he) hi)
      (Nat.lt_of_lt_of_le hw (ho.frontier_le.trans hc.frontier_le)) hafinal htailS htailE
      (by intro ann hm; obtain ⟨old, hold, rfl⟩ := List.mem_map.mp hm
          exact LetAnn.avoid_subst hboth (hanns old hold))
      (by intro rhs hm; obtain ⟨old, hold, rfl⟩ := List.mem_map.mp hm
          have hh := hrhs old hold
          exact ⟨by simpa only [Input.erase_substTyFvars, List.length_map] using
            Expr.ForallOuter.lookupAvoid_onSubst hh.1 hboth, Input.avoid_subst hboth hh.2⟩)
    refine ⟨fun p hp => (List.mem_append.mp hp).elim (hboth p) (htS p), ?_, htA⟩
    simpa only [List.map_append, List.mem_append, not_or] using And.intro (And.intro hpre.2 hcomponent.2) htD
 termination_by structural h

 theorem _root_.InferRecSigned.sourceLocality_of_infer
    (h : InferRecSigned K F index frontier ctx anns bindings state next S final)
    (hInfer : ∀ {κ F' Ψ c e Ψ' T output ty}, e.size ≤ sizeBindings bindings →
      Infer κ F' Ψ c e Ψ' T output ty →
      ∀ {w}, w < Ψ →
      e.erase.ForallOuter (fun i => ∀ M, c.env[i]? = some M → w ∉ M.body.freeVars) 0 →
      w ∉ e.rigidVars →
      (∀ p ∈ T, w ∉ p.2.freeVars) ∧ w ∉ ty.freeVars ∧ w ∉ T.map Prod.fst)
    (hw : w < frontier) (ha : state.Avoids w)
    (groupSize : Nat) (hlenS : state.specs.length = groupSize)
    (hlenE : state.exports.length = groupSize)
    (hanns : ∀ ann ∈ anns, w ∉ ann.rigidVars)
    (hrhs : ∀ rhs ∈ bindings, rhs.erase.ForallOuter
      (fun i => ∀ M, ctx.env[i]? = some M → w ∉ M.body.freeVars) groupSize ∧ w ∉ rhs.rigidVars) :
    (∀ p ∈ S, w ∉ p.2.freeVars) ∧ w ∉ S.map Prod.fst ∧ final.Avoids w := by
  match h with
  | .nil => exact ⟨by simp, by simp, ha⟩
  | .skip _ hr =>
    exact hr.sourceLocality_of_infer
      (fun he hi => hInfer (by simp only [sizeBindings]; omega) hi) hw ha groupSize hlenS hlenE
      (fun ann hm => hanns ann (List.mem_cons_of_mem _ hm))
      (fun rhs hm => hrhs rhs (List.mem_cons_of_mem _ hm))
  | .cons _ _ hi hu _ hr =>
    expose_names
    have hy : w ∉ freshVars frontier scheme.paramCount := fun hm => by
      have := freshVars_ge w hm; omega
    have hhead := hrhs rhs List.mem_cons_self
    have hentry : state.entries.length = groupSize := by
      rw [state.entries_length (hlenE.trans hlenS.symm)]; exact hlenS
    obtain ⟨hfirstS, hfirstTy, hfirstD⟩ := hInfer
      (by simp only [Input.size_openTyVars, sizeBindings]; omega) hi (by omega)
      (by simpa only [Input.erase_openTyVars] using ha.rhsCtx hentry hhead.1)
      (fun hv => (Input.rigidVars_openTyVarsFrom hv).elim hhead.2 hy)
    have hexpected : w ∉ ((s1.onPolyTy scheme).openVars (freshVars frontier scheme.paramCount)).freeVars := by
      intro hv
      exact (Ty.freeVars_openVars_subset w hv).elim
        (Subst.notMemOnTy hfirstS (hanns (.complete scheme) List.mem_cons_self)) hy
    have hsecondS : ∀ p ∈ s2, w ∉ p.2.freeVars := by
      intro p hp hv
      exact (hu.unifies.range_mem p hp w hv).elim hfirstTy hexpected
    have hsecondD : w ∉ s2.map Prod.fst := by
      intro hm
      obtain ⟨p, hp, hpw⟩ := List.mem_map.mp hm
      have hh := hu.unifies.dom_mem p hp
      rw [hpw] at hh
      exact hh.elim hfirstTy hexpected
    have hboth : ∀ p ∈ s1 ++ s2, w ∉ p.2.freeVars :=
      fun p hm => (List.mem_append.mp hm).elim (hfirstS p) (hsecondS p)
    have hanext : ((state.onSubst (s1 ++ s2)).setSigned index (freshVars frontier scheme.paramCount)
        (output.substTyFvars s2) (bodyFacts.onSubst s2)).Avoids w :=
      (ha.onSubst hboth).setSigned
    obtain ⟨htS, htD, htA⟩ := hr.sourceLocality_of_infer
      (fun he hh => hInfer (by
        simp only [sizeBindings_map_substTyFvars] at he
        simp only [sizeBindings]
        omega) hh)
      (by have := hi.frontier_le; omega) hanext groupSize
      (by simpa [RecState.setSigned, RecState.onSubst] using hlenS)
      (by simpa [RecState.setSigned, RecState.onSubst] using hlenE)
      (by intro ann hm; obtain ⟨old, hold, rfl⟩ := List.mem_map.mp hm
          exact LetAnn.avoid_subst hboth (hanns old (List.mem_cons_of_mem _ hold)))
      (by intro source hm; obtain ⟨old, hold, rfl⟩ := List.mem_map.mp hm
          have hh := hrhs old (List.mem_cons_of_mem _ hold)
          exact ⟨by simpa only [Input.erase_substTyFvars] using
            Expr.ForallOuter.lookupAvoid_onSubst hh.1 hboth, Input.avoid_subst hboth hh.2⟩)
    refine ⟨fun p hp => (List.mem_append.mp hp).elim (hboth p) (htS p), ?_, htA⟩
    simpa only [List.map_append, List.mem_append, not_or] using And.intro (And.intro hfirstD hsecondD) htD
 termination_by structural h


private theorem mem_eraseBindings {bindings : List Input} {rhs : Input}
    (hr : rhs ∈ bindings) : rhs.erase ∈ eraseBindings bindings := by
  induction bindings with
  | nil => cases hr
  | cons head rest ih =>
    rcases List.mem_cons.mp hr with rfl | hr
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (ih hr)

private theorem rigidBindingVars_mem {bindings : List Input} {rhs : Input} {v : Nat}
    (hr : rhs ∈ bindings) (hv : v ∈ rhs.rigidVars) : v ∈ rigidBindingVars bindings := by
  induction bindings with
  | nil => cases hr
  | cons head rest ih =>
    rcases List.mem_cons.mp hr with rfl | hr
    · exact List.mem_append_left _ hv
    · exact List.mem_append_right _ (ih hr)

 theorem _root_.InferRecStrata.env_lengths
    (h : InferRecStrata K F frontier ctx anns bindings state groups next S final) :
    final.specs.length = state.specs.length ∧ final.exports.length = state.exports.length := by
  match h with
  | .nil => exact ⟨rfl, rfl⟩
  | .cons _ _ _ hf hr =>
    have he := hf.avoid_lengths
    have ht := hr.env_lengths
    exact ⟨ht.1.trans (he.1.trans (by simp [RecState.onSubst, RecState.installOpenings])),
      ht.2.trans (he.2.trans (by simp [RecState.onSubst, RecState.installOpenings]))⟩
 termination_by structural h

 theorem _root_.InferRecSigned.env_lengths
    (h : InferRecSigned K F index frontier ctx anns bindings state next S final) :
    final.specs.length = state.specs.length ∧ final.exports.length = state.exports.length := by
  match h with
  | .nil => exact ⟨rfl, rfl⟩
  | .skip _ hr => exact hr.env_lengths
  | .cons _ _ _ _ _ hr =>
    have ht := hr.env_lengths
    exact ⟨ht.1.trans (by simp [RecState.onSubst, RecState.setSigned]),
      ht.2.trans (by simp [RecState.onSubst, RecState.setSigned])⟩
 termination_by structural h

mutual
 theorem _root_.Infer.sourceLocality (h : Infer K F frontier ctx input next subst output ty) :
    ∀ {w}, w < frontier →
    input.erase.ForallOuter (fun i => ∀ M, ctx.env[i]? = some M → w ∉ M.body.freeVars) 0 →
    w ∉ input.rigidVars →
    (∀ p ∈ subst, w ∉ p.2.freeVars) ∧ w ∉ ty.freeVars ∧ w ∉ subst.map Prod.fst := by
  match h with
  | .primLitUnit | .primLitInt | .primLitNat | .primLitChar
  | .primBinOpIntAdd | .primBinOpIntSub | .primBinOpIntLt _ _ _ _
  | .primBinOpCharLt _ _ _ _ =>
    intro w _ _ _; simp [Ty.freeVars, TyList.freeVars]
  | .var hlook =>
    intro w hw hrefs _
    refine ⟨by simp, ?_, by simp⟩
    intro hc
    rcases Ty.freeVars_openVars_subset w hc with h | h
    · simp only [Input.erase, Expr.ForallOuter, Expr.rec_strong, Nat.zero_le, Nat.sub_zero] at hrefs
      exact hrefs (by trivial) _ hlook h
    · have := freshVars_ge w h; omega
  | .ctor hlook =>
    intro w hw _ _
    refine ⟨by simp, ?_, by simp⟩
    intro hc
    rcases Ty.freeVars_openVars_subset w hc with h | h
    · exact (Ctor.toTy_body_noFreeVars _).not_mem_freeVars w h
    · have := freshVars_ge w h; omega
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
  | .letRec _ _ hv hs hp _ _ hb =>
    intro w hw hrefs hwe
    expose_names
    have hv := hv.1
    simp only [Input.erase, Expr.ForallOuter, Expr.rec_strong, eraseBindings_length, Nat.zero_add] at hrefs
    simp only [Input.rigidVars, List.mem_append, not_or] at hwe
    have hanns : ∀ ann ∈ anns, w ∉ ann.rigidVars :=
      fun ann ha hv => hwe.1.1 (List.mem_flatMap.mpr ⟨ann, ha, hv⟩)
    have hrhs : ∀ rhs ∈ bindings, rhs.erase.ForallOuter
        (fun i => ∀ M, ctx.env[i]? = some M → w ∉ M.body.freeVars) bindings.length ∧ w ∉ rhs.rigidVars := by
      intro rhs hr
      exact ⟨hrefs.1 rhs.erase (mem_eraseBindings hr), fun hv => hwe.1.2 (rigidBindingVars_mem hr hv)⟩
    have hlen : anns.length = bindings.length := by simpa only [List.length_map] using hv.length
    obtain ⟨hsS, hsD, hstate1⟩ := hs.sourceLocality_of_infer (fun _ hi => hi.sourceLocality)
      (by omega) (RecState.Avoids.init hw hanns)
      (by simpa only [RecState.init, RecSpec.init_length, List.length_map] using hlen)
      (by simpa only [RecState.init, List.length_map] using hlen) hanns hrhs
    have hsl := hs.env_lengths
    have hs1len : state1.specs.length = bindings.length := by
      simpa only [RecState.init, RecSpec.init_length, List.length_map] using hsl.1.trans (by simpa [RecState.init, RecSpec.init_length] using hlen)
    have he1len : state1.exports.length = bindings.length := by
      simpa only [RecState.init, List.length_map] using hsl.2.trans (by simpa [RecState.init] using hlen)
    obtain ⟨hpS, hpD, hstate2⟩ := hp.sourceLocality_of_infer (fun _ hi => hi.sourceLocality)
      (by have := hs.frontier_le; omega) hstate1 bindings.length hs1len he1len
      (by intro ann ha; obtain ⟨old, ho, rfl⟩ := List.mem_map.mp ha; exact LetAnn.avoid_subst hsS (hanns old ho))
      (by
        intro rhs hr
        obtain ⟨old, ho, rfl⟩ := List.mem_map.mp hr
        exact ⟨by simpa only [Input.erase_substTyFvars] using Expr.ForallOuter.lookupAvoid_onSubst (hrhs old ho).1 hsS,
          Input.avoid_subst hsS (hrhs old ho).2⟩)
    have hpre := Subst.sourceAvoid_append_local ⟨hsS, hsD⟩ ⟨hpS, hpD⟩
    have hpl := hp.env_lengths
    have hentries : state2.entries.length = bindings.length := by
      rw [state2.entries_length ((hpl.2.trans he1len).trans (hpl.1.trans hs1len).symm)]
      exact hpl.1.trans hs1len
    obtain ⟨hbS, hbTy, hbD⟩ := hb.sourceLocality (show w < second from by have := hs.frontier_le; have := hp.frontier_le; omega)
      (by
        have hh := hstate2.rhsCtx hentries (Expr.ForallOuter.lookupAvoid_onSubst hrefs.2 hpre.1)
        simpa only [Input.erase_substTyFvars] using hh)
      (Input.avoid_subst hpre.1 hwe.2)
    have hAll := Subst.sourceAvoid_append_local hpre ⟨hbS, hbD⟩
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
 decreasing_by
  all_goals simp only [sizeBindings_map_substTyFvars] at *
  all_goals (simp only [Input.size, Input.size_substTyFvars, Input.size_openTyVars, sizeBranches_substInputBranches]; omega)

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

namespace Elaboration

private theorem soft_avoids_subst {F : List Ty} {S : Subst} {v : Nat}
    (hF : v ∉ TyList.freeVars F) (hS : ∀ p ∈ S, v ∉ p.2.freeVars) :
    v ∉ TyList.freeVars (F.map S.onTy) := by
  intro hm
  obtain ⟨ty, ht, hv⟩ := TyList.mem_freeVars_iff.mp hm
  obtain ⟨old, ho, rfl⟩ := List.mem_map.mp ht
  exact Subst.notMemOnTy hS (fun hv => hF (TyList.mem_freeVars_iff.mpr ⟨old, ho, hv⟩)) hv

 theorem RecState.Frame.onSubst {state : RecState} {S : Subst}
    (h : state.Frame base K F ctx anns done)
    (hpool : ∀ g ∈ state.pool, (∀ p ∈ S, g ∉ p.2.freeVars) ∧ g ∉ S.map Prod.fst)
    (hpending : ∀ i ty, state.specs[i]? = some (.mono ty) → i ∉ done →
      (∀ p ∈ S, base + i ∉ p.2.freeVars) ∧ base + i ∉ S.map Prod.fst) :
    (state.onSubst S).Frame base K (F.map S.onTy) (S.onCtx ctx)
      (anns.map (LetAnn.substTyFvars S)) done := by
  have hdom : ∀ p ∈ S, p.1 ∉ state.pool := by
    intro p hp hg
    exact (hpool p.1 hg).2 (List.mem_map.mpr ⟨p, hp, rfl⟩)
  have hran : ∀ p ∈ S, ∀ g ∈ p.2.freeVars, g ∉ state.pool :=
    fun p hp g hg hgp => (hpool g hgp).1 p hp hg
  have hfix : ∀ g ∈ state.pool, S.onTy (.fvar g) = .fvar g := Subst.fixes_of_dom_avoids hdom
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, h.pool_nodup, ?_, h.pool_rigid, ?_, ?_, ?_, h.rigid_below, ?_⟩
  · simpa only [RecState.onSubst, List.length_map] using h.specs_length
  · simpa only [RecState.onSubst, List.length_map] using h.slots_length
  · simpa only [RecState.onSubst, List.length_map] using h.exports_length
  · simpa only [RecState.onSubst, List.length_map] using h.outputs_length
  · simpa only [RecState.onSubst, List.length_map] using h.facts_length
  · have hm : ((state.onSubst S).specs).map RecSpec.ann =
        (state.specs.map RecSpec.ann).map (Option.map S.onPolyTy) := by
      simp only [RecState.onSubst, List.map_map]
      apply List.map_congr_left
      intro spec _
      cases spec <;> rfl
    rw [hm, h.modes]
    simp only [List.map_map, Function.comp_def, LetAnn.recModeAnn_subst_source]
  · intro i scheme hget
    rw [RecState.onSubst, List.getElem?_map] at hget
    obtain ⟨old, hold, heq⟩ := Option.map_eq_some_iff.mp hget
    cases old with
    | mono ty => cases heq
    | poly σ =>
      cases RecSpec.poly.inj heq
      simp only [RecState.onSubst, List.getElem?_map, h.poly i σ hold, Option.map_some]
  · intro i ty hget
    rw [RecState.onSubst, List.getElem?_map] at hget
    obtain ⟨old, hold, heq⟩ := Option.map_eq_some_iff.mp hget
    cases old with
    | poly scheme => cases heq
    | mono original =>
      cases RecSpec.mono.inj heq
      by_cases hi : i ∈ done
      · obtain ⟨written, hslots, hcount, hnd, hsub, hexport⟩ := if_pos hi ▸ h.mono i original hold
        rw [if_pos hi]
        refine ⟨written, ?_, ?_, hnd, hsub, ?_⟩
        · simp only [RecState.onSubst, List.getElem?_map, hslots, Option.map_some, List.map_map]
          congr 1
          apply List.map_congr_left
          intro name hn
          exact hfix name (hsub name hn)
        · cases ha : anns[i]? with
          | none => simpa only [List.getElem?_map, ha, Option.map_none] using hcount
          | some ann => simpa only [List.getElem?_map, ha, Option.map_some, Option.getD_some,
              LetAnn.recPrefixCount_subst_source] using hcount
        · simp only [RecState.onSubst, List.getElem?_map, hexport, Option.map_some]
          rw [recScheme_subst_pool_avoid hdom hran hsub]
      · rw [if_neg hi]
        have he := if_neg hi ▸ h.mono i original hold
        simp only [RecState.onSubst, List.getElem?_map, he, Option.map_some, Option.map_none]
  · exact h.pending.onSubst_source (fun _ hm => hm) hpending
  · intro g hg hm
    obtain ⟨scheme, hs, hv⟩ := Env.mem_freeVars_iff.mp hm
    obtain ⟨old, ho, rfl⟩ := List.mem_map.mp hs
    exact Subst.notMemOnTy (hpool g hg).1
      (fun hv => h.pool_ctx g hg (Env.mem_freeVars_iff.mpr ⟨old, ho, hv⟩)) hv
  · intro g hg
    exact soft_avoids_subst (h.pool_soft g hg) (hpool g hg).1
  · intro scheme ⟨i, hget⟩ g hg
    rw [RecState.onSubst, List.getElem?_map] at hget
    obtain ⟨old, hold, heq⟩ := Option.map_eq_some_iff.mp hget
    cases old with
    | mono ty => cases heq
    | poly σ =>
      cases RecSpec.poly.inj heq
      exact Subst.notMemOnTy (hpool g hg).1 (h.pool_poly σ ⟨i, hold⟩ g hg)
  · intro i ty hget hi
    obtain ⟨old, hold, _⟩ := RecSpec.mono_getElem?_map_onSubstSource hget
    exact h.pool_pending i old hold hi
  · intro i ty hget hi
    obtain ⟨old, hold, _⟩ := RecSpec.mono_getElem?_map_onSubstSource hget
    exact soft_avoids_subst (h.pending_soft i old hold hi) (hpending i old hold hi).1


end Elaboration

namespace Elaboration

private theorem mem_eraseBranches_local {branches : List (MatchPattern × Input)}
    (h : (pat, body) ∈ branches) : (pat, body.erase) ∈ eraseBranches branches := by
  induction branches with
  | nil => cases h
  | cons head rest ih =>
    rcases List.mem_cons.mp h with hh | hh
    · cases hh; exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (ih hh)
private theorem mem_eraseBindings_local {bindings : List Input} (h : rhs ∈ bindings) :
    rhs.erase ∈ eraseBindings bindings := by
  induction bindings with
  | nil => cases h
  | cons head rest ih =>
    rcases List.mem_cons.mp h with hh | hh
    · cases hh; exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (ih hh)

 theorem Typing.env_agreement {Q : List Nat} {ctx : Ctx} {input : Input} {ty : Ty}
    (h : Typing Q ctx input ty) : ∀ env',
    input.erase.ForallOuter (fun i => env'[i]? = ctx.env[i]?) 0 →
    Typing Q ⟨env', ctx.ctors⟩ input ty := by
  induction h using Typing.rec
      (motive_2 := fun Q ctx branch scrutTy resultTy _ => ∀ env',
        branch.2.erase.ForallOuter (fun i => env'[i]? = ctx.env[i]?) branch.1.bindCount →
        BranchTyping Typing Q ⟨env', ctx.ctors⟩ branch scrutTy resultTy) with
  | complete hemb hprotected hcore =>
    intro env' hag
    refine .complete hemb hprotected (hcore.env_agreement env' ?_)
    apply (Expr.ForallOuter.erase_iff _).mp
    rwa [Input.toCore_erase _ hemb]
  | primLit hcore =>
    intro env' hag
    exact .primLit (hcore.env_agreement env' hag)
  | primBinOp hcore =>
    intro env' hag
    exact .primBinOp (hcore.env_agreement env' hag)
  | lambda hlc hfit hprotected _ ih =>
    intro env' hag
    simp only [Input.erase, Expr.ForallOuter, Expr.rec_strong, Nat.zero_add] at hag
    refine .lambda hlc hfit hprotected (ih _ ?_)
    exact Expr.ForallOuter.prepend_env (pre := [PolyTy.mkTrivial _]) hag
  | app _ _ ihf iha =>
    intro env' hag
    simp only [Input.erase, Expr.ForallOuter, Expr.rec_strong] at hag
    exact .app (ihf env' hag.1) (iha env' hag.2)
  | letIn hwf hprotected hfit _ _ ihr ihb =>
    intro env' hag
    simp only [Input.erase, Expr.ForallOuter, Expr.rec_strong, Nat.zero_add] at hag
    refine .letIn hwf hprotected hfit (fun Xs hf => ihr Xs hf env' hag.1) (ihb _ ?_)
    exact Expr.ForallOuter.prepend_env (pre := [_]) hag.2
  | letSignature hwf hann hrhs hfit _ _ ihr ihb =>
    intro env' hag
    simp only [Input.erase, Expr.ForallOuter, Expr.rec_strong, Nat.zero_add] at hag
    refine .letSignature hwf hann hrhs hfit (fun Xs hf => ihr Xs hf env' ?_) (ihb _ ?_)
    · simpa only [Input.erase_openTyVars] using hag.1
    · exact Expr.ForallOuter.prepend_env (pre := [_]) hag.2
  | var hlook hargs hinst =>
    intro env' hag
    simp only [Input.erase, Expr.ForallOuter, Expr.rec_strong, Nat.zero_le, Nat.sub_zero] at hag
    exact .var (by rw [hag trivial]; exact hlook) hargs hinst
  | ctor hlook hargs hinst => intro _ _; exact .ctor hlook hargs hinst
  | match_ _ hne _ ihs ihbr =>
    intro env' hag
    simp only [Input.erase, Expr.ForallOuter, Expr.rec_strong, Nat.zero_add] at hag
    refine .match_ (ihs env' hag.1) hne ?_
    intro ⟨pat, body⟩ hb
    exact ihbr (pat, body) hb env' (hag.2 pat body.erase (mem_eraseBranches_local hb))
  | @letRec anns K bindings ctx body resultTy specs groups prefixes G L hg hw hp hG hAnn hRhs hFits _ _ _ ihMono ihPoly ihBody =>
    intro env' hag
    simp only [Input.erase, Expr.ForallOuter, Expr.rec_strong, eraseBindings_length, Nat.zero_add] at hag
    let avoid := K ++ env'.freeVars ++ G ++ specs.flatMap RecSpec.freeVars
    obtain ⟨W, hWlen, hWnd, hWavoid⟩ := exists_fresh_names avoid G.length
    have hGW : ∀ g ∈ G, g ∉ W := by
      intro g hg hw
      exact hWavoid g hw (by simp only [avoid, List.mem_append]; tauto)
    have hWmono : ∀ ty, .mono ty ∈ specs → ∀ w ∈ W, w ∉ ty.freeVars := by
      intro ty ht w hw hv
      exact hWavoid w hw (by
        simp only [avoid, List.mem_append]
        right
        exact List.mem_flatMap.mpr ⟨.mono ty, ht, hv⟩)
    let specs' := specs.map (fun spec => RecSpec.onSubstSource [] (RecSpec.onSubst (G.zip (W.map Ty.fvar)) spec))
    let prefixes' := prefixes.map (recRenameNames G W)
    let L' := G ++ W ++ L
    have annNil : anns.map (LetAnn.substTyFvars []) = anns := by
      conv_rhs => rw [← List.map_id anns]
      apply List.map_congr_left
      intro ann _
      exact ann.substTyFvars_eq_self_of_fixes (fun _ _ => rfl)
    have hw' : RecSpecs.WF (anns.map LetAnn.recModeAnn) (bindings.map Input.erase) specs' W := by
      simpa only [annNil] using Elaboration.RecSpecs.WF.subst_fresh_pool (S := []) hw (by simp) hWnd
    have hp' : RecPrefixesWF anns specs' prefixes' W := by
      simpa only [annNil] using hp.subst_fresh_pool (S := []) hWlen hWnd
    have hannsLen : anns.length = specs.length := by
      have hh := congrArg List.length hw.anns_eq
      simpa using hh.symm
    have hpData := fun i hi => hp.get hannsLen (i := i) hi
    have mapNil : ∀ xs : List PolyTy, xs.map (Subst.onPolyTy []) = xs := by
      intro xs
      rw [show Subst.onPolyTy [] = id from funext Subst.onPolyTy_nil, List.map_id]
    have hcompleted : recCompletedSchemes specs' prefixes' W = recCompletedSchemes specs prefixes G := by
      simpa only [mapNil] using recCompletedSchemes_subst_fresh_pool (S := []) (by simp) hWlen hw.nodup hWnd
        hGW hWmono (by simp) (by simp) hw.mono_lc hpData
    have oldFresh : ∀ Xs, FreshNames (W ++ L') W.length Xs → FreshNames (G ++ L) G.length Xs := by
      intro Xs hf
      refine ⟨hf.length.trans hWlen, hf.nodup, ?_⟩
      intro x hx hl
      exact hf.avoid x hx (by simp only [L', List.mem_append] at hl ⊢; tauto)
    have hGXs : ∀ Xs, FreshNames (W ++ L') W.length Xs → ∀ g ∈ G, g ∉ Xs := by
      intro Xs hf g hg hx
      exact hf.avoid g hx (by simp only [L', List.mem_append]; tauto)
    have hWXs : ∀ Xs, FreshNames (W ++ L') W.length Xs → ∀ w ∈ W, w ∉ Xs := by
      intro Xs hf w hw hx
      exact hf.avoid w hx (List.mem_append_left _ hw)
    have hstage : ∀ Xs, FreshNames (W ++ L') W.length Xs → ∀ done,
        specs'.mapIdx (recStageEntry prefixes' done W Xs) = specs.mapIdx (recStageEntry prefixes done G Xs) := by
      intro Xs hf done
      simpa only [mapNil] using recStageSchemes_subst_fresh_pool (S := []) (done := done) (by simp)
        hWlen hw.nodup hWnd hGW hWmono (by simp) (by simp) hw.mono_lc hpData
        (hf.length.trans hWlen) (hGXs Xs hf) (hWXs Xs hf) (by simp)
    have hsquare : ∀ ty, .mono ty ∈ specs → ∀ Xs, FreshNames (W ++ L') W.length Xs →
        Ty.renameG W Xs (Ty.renameG G W ty) = Ty.renameG G Xs ty := by
      intro ty ht Xs hf
      simpa only [Subst.onTy_nil] using Ty.renameG_subst_fresh_pool (S := []) (hw.mono_lc ty ht) (by simp)
        hWlen hw.nodup hWnd hGW (hWmono ty ht) (by simp) (by simp)
        (hf.length.trans hWlen) (hGXs Xs hf) (hWXs Xs hf) (by simp)
    refine Typing.letRec (specs := specs') (groups := groups) (prefixes := prefixes') (G := W) (L := L')
      hg hw' hp' ?_ hAnn hRhs ?_ ?_ ?_ ?_
    · intro w hw hm
      exact hWavoid w hw (by simp only [avoid, List.mem_append] at hm ⊢; tauto)
    · intro stage component hs Xs hf member hm rhs ann names ty hri hai hni hti
      rw [List.getElem?_map] at hni hti
      obtain ⟨names0, hn0, rfl⟩ := Option.map_eq_some_iff.mp hni
      obtain ⟨spec, ht0, heq⟩ := Option.map_eq_some_iff.mp hti
      cases spec with
      | poly scheme => cases heq
      | mono ty0 =>
        cases heq
        obtain ⟨_, _, hsub⟩ := hp.member member ann names0 hai hn0
        change ann.RecFits (recRenameNames W Xs (recRenameNames G W names0))
          (Ty.renameG W Xs (Ty.renameG G W ty0))
        rw [recRenameNames_composition hWlen (hf.length.trans hWlen) hWnd hsub,
          hsquare ty0 (List.mem_of_getElem? ht0) Xs hf]
        exact hFits stage component hs Xs (oldFresh Xs hf) member hm rhs ann names0 ty0 hri hai hn0 ht0
    · intro stage component hs Xs hf member hm rhs ann names ty hri hai hni hti
      rw [List.getElem?_map] at hni hti
      obtain ⟨names0, hn0, rfl⟩ := Option.map_eq_some_iff.mp hni
      obtain ⟨spec, ht0, heq⟩ := Option.map_eq_some_iff.mp hti
      cases spec with
      | poly scheme => cases heq
      | mono ty0 =>
        cases heq
        obtain ⟨_, _, hsub⟩ := hp.member member ann names0 hai hn0
        change Typing (K ++ Xs)
          (recStageCtx { ctx with env := env' } specs' prefixes' (groups.take stage).flatten W Xs)
          (rhs.openTyVars (recRenameNames W Xs (recRenameNames G W names0)))
          (Ty.renameG W Xs (Ty.renameG G W ty0))
        rw [recRenameNames_composition hWlen (hf.length.trans hWlen) hWnd hsub,
          hsquare ty0 (List.mem_of_getElem? ht0) Xs hf]
        have hc := ihMono stage component hs Xs (oldFresh Xs hf) member hm rhs ann names0 ty0 hri hai hn0 ht0
          ((specs.mapIdx (recStageEntry prefixes (groups.take stage).flatten G Xs)) ++ env') (by
            apply Expr.ForallOuter.prepend_env
            simpa only [Input.erase_openTyVars, List.length_mapIdx, Nat.zero_add, ← hw.length, List.length_map] using
              hag.1 rhs.erase (mem_eraseBindings_local (List.mem_of_getElem? hri)))
        simpa only [recStageCtx, hstage Xs hf] using hc
    · intro member rhs scheme hri hsi Ys hy
      rw [List.getElem?_map] at hsi
      obtain ⟨spec, hs0, heq⟩ := Option.map_eq_some_iff.mp hsi
      cases spec with
      | mono ty => cases heq
      | poly scheme0 =>
        cases heq
        have hy0 : FreshNames L scheme0.paramCount Ys :=
          ⟨hy.length, hy.nodup, fun y hy' hl => hy.avoid y hy' (by simp only [L', List.mem_append]; tauto)⟩
        have hc := ihPoly member rhs scheme0 hri hs0 Ys hy0 ((recCompletedSchemes specs prefixes G) ++ env') (by
          apply Expr.ForallOuter.prepend_env
          simpa only [Input.erase_openTyVars, recCompletedSchemes, List.length_mapIdx, Nat.zero_add, ← hw.length, List.length_map] using
            hag.1 rhs.erase (mem_eraseBindings_local (List.mem_of_getElem? hri)))
        simpa only [recBodyCtx, hcompleted] using hc
    · have hc := ihBody ((recCompletedSchemes specs prefixes G) ++ env') (by
        apply Expr.ForallOuter.prepend_env
        simpa only [recCompletedSchemes, List.length_mapIdx, Nat.zero_add, ← hw.length, List.length_map] using hag.2)
      simpa only [recBodyCtx, hcompleted] using hc
  | @named name count scrutTy ctor args fields K ctx body resultTy hspec _ ih =>
    rename_i env' hag
    refine .named hspec (ih _ ?_)
    apply Expr.ForallOuter.prepend_env
    have hlen : fields.length = count := hspec.fields.length_eq.symm.trans hspec.bind_count.symm
    simpa only [List.length_map, Nat.zero_add, MatchPattern.bindCount, hlen] using hag
  | wildcard _ ih =>
    rename_i env' hag
    exact .wildcard (ih env' hag)

private def inputSchemeHybrid (input : Input) (old new : List PolyTy) : List PolyTy :=
  old.mapIdx fun member oldScheme =>
    if member ∈ input.erase.recGroupRefs old.length 0 then oldScheme else new[member]?.getD oldScheme

private theorem inputSchemeHybrid_getElem {input : Input} {old new : List PolyTy}
    (member : Nat) (hold : member < old.length) (hnew : member < new.length) :
    (inputSchemeHybrid input old new)[member]'(by simpa [inputSchemeHybrid] using hold) =
      if member ∈ input.erase.recGroupRefs old.length 0 then old[member]'hold else new[member]'hnew := by
  simp only [inputSchemeHybrid, List.getElem_mapIdx]
  split
  · rfl
  · rw [List.getElem?_eq_getElem hnew, Option.getD_some]

 theorem Typing.weaken_recGroupRefs {Q : List Nat} {ctx : Ctx} {input : Input} {ty : Ty}
    {old new : List PolyTy} (hlen : old.length = new.length)
    (hgen : ∀ member (hold : member < old.length) (hnew : member < new.length),
      member ∈ input.erase.recGroupRefs old.length 0 →
      (new[member]'hnew).Generalizes (old[member]'hold))
    (hty : Typing Q ⟨old ++ ctx.env, ctx.ctors⟩ input ty) :
    Typing Q ⟨new ++ ctx.env, ctx.ctors⟩ input ty := by
  let hybrid := inputSchemeHybrid input old new
  have hlenHybrid : hybrid.length = old.length := by simp [hybrid, inputSchemeHybrid]
  have htyHybrid : Typing Q ⟨hybrid ++ ctx.env, ctx.ctors⟩ input ty := by
    apply hty.env_agreement
    apply Expr.ForallOuter.of_recGroupRefs_with_outer (n := old.length)
    · intro member href
      by_cases hmember : member < old.length
      · rw [List.getElem?_append_left (by simpa [hlenHybrid] using hmember),
          List.getElem?_append_left hmember]
        have hnew : member < new.length := by omega
        rw [List.getElem?_eq_getElem (by simpa [hlenHybrid] using hmember),
          inputSchemeHybrid_getElem member hmember hnew, if_pos href,
          List.getElem?_eq_getElem hmember]
      · have hmember' : old.length ≤ member := by omega
        rw [List.getElem?_append_right (by simpa [hlenHybrid] using hmember'),
          List.getElem?_append_right hmember']
        simp only [hlenHybrid]
    · intro member hmember
      rw [List.getElem?_append_right (by simpa [hlenHybrid] using hmember),
        List.getElem?_append_right hmember]
      simp only [hlenHybrid]
  apply Typing.weaken_schemes (Ms := hybrid) (Ms' := new) ?_ htyHybrid
  apply (List.forall₂_iff_get).mpr
  refine ⟨by omega, ?_⟩
  intro member hnew hhybrid
  change new[member].Generalizes (inputSchemeHybrid input old new)[member]
  rw [inputSchemeHybrid_getElem member (by omega) hnew]
  split
  · exact hgen member (by omega) hnew (by assumption)
  · exact PolyTy.Generalizes.refl new[member]

end Elaboration
