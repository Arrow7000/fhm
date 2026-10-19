import FHM.Elaboration.Principal
import FHM.Elaboration.Infer

namespace Elaboration

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


/-- Producer completeness for the concrete worker, under an arbitrary LC
specialization fixing the inference's rigid variables. Successful results
already carry output typing and residual principality. -/
def _root_.InferWithTypesCoreComplete (input : Input) : Prop :=
  ∀ (K : List Nat) (frontier : Nat) (ctx : Ctx) (ambient : Subst) (target : Ty),
    CtxWF ctx → CtxBelow frontier ctx → (∀ k ∈ K, k < frontier) →
    (∀ pair ∈ ambient, pair.2.IsLC) →
    (∀ k ∈ K, ambient.onTy (.fvar k) = .fvar k) →
    Typing K (ambient.onCtx ctx) input target → (inferWithTypesCore K frontier ctx input).isSome

private theorem rigid_all {K : List Nat} (h : ∀ k ∈ K, k < frontier) :
    K.all (fun v => decide (v < frontier)) = true :=
  List.all_eq_true.mpr (fun v hv => decide_eq_true (h v hv))

private theorem ctx_all (h : CtxBelow frontier ctx) :
    ctx.env.freeVars.all (fun v => decide (v < frontier)) = true := by
  apply List.all_eq_true.mpr
  intro v hv
  obtain ⟨scheme, hs, hv⟩ := Env.mem_freeVars_iff.mp hv
  exact decide_eq_true ((h scheme hs).mem_lt v hv)

/-- Concrete branch producer completeness shares one common scrutinee and result. -/
def _root_.InferBranchesWithTypesCoreComplete (branches : List (MatchPattern × Input)) : Prop :=
  ∀ (K : List Nat) (frontier : Nat) (ctx : Ctx) (scrutTy resultTy : Ty)
    (branchIndex : Nat) (ambient : Subst),
    CtxWF ctx → CtxBelow frontier ctx → (∀ k ∈ K, k < frontier) →
    (∀ pair ∈ ambient, pair.2.IsLC) →
    (∀ k ∈ K, ambient.onTy (.fvar k) = .fvar k) →
    scrutTy.IsLC → resultTy.IsLC →
    Ty.BelowFvars frontier scrutTy → Ty.BelowFvars frontier resultTy →
    (∀ b ∈ branches, BranchTyping Typing K (ambient.onCtx ctx) b
      (ambient.onTy scrutTy) (ambient.onTy resultTy)) →
    (inferBranchesWithTypesCore K frontier ctx scrutTy resultTy branchIndex branches).isSome

theorem _root_.inferBranchesWithTypesCore_complete_nil : InferBranchesWithTypesCoreComplete [] := by
  unfold InferBranchesWithTypesCoreComplete
  intros
  simp only [inferBranchesWithTypesCore, Option.isSome_some]

theorem _root_.inferBranchesWithTypesCore_complete_wildcard
    (ihbody : InferWithTypesCoreComplete body)
    (ihrest : InferBranchesWithTypesCoreComplete rest) :
    InferBranchesWithTypesCoreComplete ((.wildcard, body) :: rest) := by
  intro K frontier ctx scrutTy resultTy branchIndex ambient hwf hbelow hK hS hfix
    hscrut hresult hscrutB hresultB htyping
  have hbodyD := htyping (.wildcard, body) List.mem_cons_self
  cases hbodyD with
  | wildcard hbodyD =>
    obtain ⟨⟨⟨first, s1, bodyOut, bodyTy, bodyTypes, bodySchemes⟩, hb⟩, hbResult⟩ :=
      Option.isSome_iff_exists.mp
        (ihbody K frontier ctx ambient (ambient.onTy resultTy) hwf hbelow hK hS hfix hbodyD)
    obtain ⟨R, hR, hbodyTy, hRK, hag⟩ := hb.principal
      hwf hbelow hK ambient (ambient.onTy resultTy) K hS hK hfix hbodyD
    have hle := hb.frontier_le
    obtain ⟨hbB, hs1B⟩ := hb.belowFvars hbelow hK
    obtain ⟨hbLC, hs1LC⟩ := hb.lc hwf
    have hctx1 := Subst.onCtx_below hs1B hle hbelow
    have hK1 : ∀ k ∈ K, k < first := fun k hk => Nat.lt_of_lt_of_le (hK k hk) hle
    have hrightB := Subst.onTy_belowFvars hs1B (hresultB.mono hle)
    have hscrut1B := Subst.onTy_belowFvars hs1B (hscrutB.mono hle)
    have hUni : Unifies R bodyTy (s1.onTy resultTy) := by
      change R.onTy bodyTy = R.onTy (s1.onTy resultTy)
      rw [show R.onTy bodyTy = ambient.onTy resultTy from hbodyTy.symm]
      simpa only [Subst.onTy_append] using Subst.onTy_congr hag hresultB
    obtain ⟨⟨s2, hu⟩, huResult⟩ := Option.isSome_iff_exists.mp
      (unifyCoreK_complete hbLC (Subst.onTy_lc hs1LC hresult) hR hUni hRK)
    rcases hu with ⟨hun, havoid⟩
    obtain ⟨V, hfac, hV, hVK⟩ := hun.greatest_K R hR hUni hRK
    have hs2LC := hun.lc hbLC (Subst.onTy_lc hs1LC hresult)
    have hs2B := hun.belowFvars hbB hrightB
    have hctx2 := Subst.onCtx_below hs2B (Nat.le_refl _) hctx1
    have hctxeq : V.onCtx (s2.onCtx (s1.onCtx ctx)) = ambient.onCtx ctx := by
      have heq : Subst.AgreesBelow frontier ambient (s1 ++ s2 ++ V) := by
        intro v hv
        rw [Subst.onTy_append, Subst.onTy_append]
        exact (show ambient.onTy (.fvar v) = R.onTy (s1.onTy (.fvar v)) from
          by simpa only [Subst.onTy_append] using hag v hv).trans (hfac (s1.onTy (.fvar v)))
      rw [← Subst.onCtx_append, ← Subst.onCtx_append]
      simpa only [List.append_assoc] using (Subst.onCtx_congr heq hbelow).symm
    have hscruteq : V.onTy (s2.onTy (s1.onTy scrutTy)) = ambient.onTy scrutTy := by
      simpa only [Subst.onTy_append] using
        (hfac (s1.onTy scrutTy)).symm.trans (show R.onTy (s1.onTy scrutTy) = ambient.onTy scrutTy from
          by simpa only [Subst.onTy_append] using (Subst.onTy_congr hag hscrutB).symm)
    have hresulteq : V.onTy (s2.onTy (s1.onTy resultTy)) = ambient.onTy resultTy := by
      exact (hfac (s1.onTy resultTy)).symm.trans (show R.onTy (s1.onTy resultTy) = ambient.onTy resultTy from
          by simpa only [Subst.onTy_append] using (Subst.onTy_congr hag hresultB).symm)
    obtain ⟨⟨⟨next, s3, restOut, restTypes, restSchemes⟩, hr⟩, hrResult⟩ :=
      Option.isSome_iff_exists.mp
        (ihrest K first _ _ _ (branchIndex + 1) V
          (Subst.onCtx_wf hs2LC (Subst.onCtx_wf hs1LC hwf)) hctx2 hK1 hV hVK
          (Subst.onTy_lc hs2LC (Subst.onTy_lc hs1LC hscrut))
          (Subst.onTy_lc hs2LC (Subst.onTy_lc hs1LC hresult))
          (Subst.onTy_belowFvars hs2B hscrut1B)
          (Subst.onTy_belowFvars hs2B hrightB)
          (by simpa only [hctxeq, hscruteq, hresulteq] using
            (fun b hb => htyping b (List.mem_cons_of_mem _ hb))))
    simp only [inferBranchesWithTypesCore, hbResult, huResult, hrResult, Option.isSome_some]

theorem _root_.inferBranchesWithTypesCore_complete_named
    (ihbody : InferWithTypesCoreComplete body)
    (ihrest : InferBranchesWithTypesCoreComplete rest) :
    InferBranchesWithTypesCoreComplete ((.named name count, body) :: rest) := by
  intro K frontier ctx scrutTy resultTy branchIndex ambient hwf hbelow hK hS hfix
    hscrut hresult hscrutB hresultB htyping
  have hhead := htyping (.named name count, body) List.mem_cons_self
  cases hhead with
  | named hspec hbodyD =>
    rename_i ctor args fields
    have hlookup : LookupList.get? ctx.ctors name = some ctor := hspec.lookup
    have hargsLC : ∀ t ∈ args, t.IsLC := by
      have hh := Subst.onTy_lc hS hscrut
      rw [hspec.scrut_eq] at hh
      cases hh with | customTy hh => exact hh
    obtain ⟨U, hU, hagU, hblock⟩ := Subst.override_block hS frontier args hargsLC
    have hargs : ((freshVars frontier ctor.paramCount).map Ty.fvar).map U.onTy = args := by
      apply List.ext_getElem
      · simp only [List.length_map, freshVars_length, hspec.arity]
      · intro i hi hi'
        simp only [List.getElem_map, freshVars, List.getElem_range]
        exact hblock i hi'
    have hUK : ∀ k ∈ K, U.onTy (.fvar k) = .fvar k := fun k hk =>
      (hagU k (hK k hk)).symm.trans (hfix k hk)
    have hUni : Unifies U scrutTy
        (.customTy ctor.tyName ((freshVars frontier ctor.paramCount).map Ty.fvar)) := by
      change U.onTy scrutTy = U.onTy _
      rw [← Subst.onTy_congr hagU hscrutB, hspec.scrut_eq, Subst.onTy_customTy, hargs]
    have hcustomLC : (Ty.customTy ctor.tyName ((freshVars frontier ctor.paramCount).map Ty.fvar)).IsLC :=
      .customTy (fun t ht => by obtain ⟨_, _, rfl⟩ := List.mem_map.mp ht; exact .fvar)
    obtain ⟨⟨s0, hu0⟩, hu0Result⟩ := Option.isSome_iff_exists.mp
      (unifyCoreK_complete hscrut hcustomLC hU hUni hUK)
    rcases hu0 with ⟨hun0, hav0⟩
    have hhead : BranchTyping Typing K (ambient.onCtx ctx) (.named name count, body)
        (ambient.onTy scrutTy) (ambient.onTy resultTy) := .named hspec hbodyD
    obtain ⟨V, hV, hVK, hag0, hbD⟩ := hhead.factor_named hlookup hun0 hbelow hscrutB hS
      (Subst.onTy_lc hS hscrut) hK hfix rfl
    have hs0LC := hun0.lc hscrut hcustomLC
    have hcustomB : Ty.BelowFvars (frontier + ctor.paramCount)
        (.customTy ctor.tyName ((freshVars frontier ctor.paramCount).map Ty.fvar)) := by
      exact .customTy (fun t ht => by
        obtain ⟨v, hv, rfl⟩ := List.mem_map.mp ht
        exact .fvar (freshVars_lt v hv))
    have hs0B := hun0.belowFvars (hscrutB.mono (Nat.le_add_right _ _)) hcustomB
    have hargs0LC : ∀ t ∈ ((freshVars frontier ctor.paramCount).map Ty.fvar).map s0.onTy, t.IsLC := by
      intro t ht
      obtain ⟨v, hv, rfl⟩ := List.mem_map.mp ht
      obtain ⟨_, _, rfl⟩ := List.mem_map.mp hv
      exact Subst.onTy_lc hs0LC .fvar
    have hargs0B : ∀ t ∈ ((freshVars frontier ctor.paramCount).map Ty.fvar).map s0.onTy,
        Ty.BelowFvars (frontier + ctor.paramCount) t := by
      intro t ht
      obtain ⟨v, hv, rfl⟩ := List.mem_map.mp ht
      obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hv
      exact Subst.onTy_belowFvars hs0B (.fvar (freshVars_lt x hx))
    have hbodyWF := branchBindings_wf (ctorr := ctor)
      (ta := ((freshVars frontier ctor.paramCount).map Ty.fvar).map s0.onTy)
      (Subst.onCtx_wf hs0LC hwf) hargs0LC (by simp)
    have hbodyB := branchBindings_below (ctorr := ctor)
      (ta := ((freshVars frontier ctor.paramCount).map Ty.fvar).map s0.onTy)
      (Subst.onCtx_below hs0B (Nat.le_add_right _ _) hbelow) hargs0B
    have hK0 : ∀ k ∈ K, k < frontier + ctor.paramCount :=
      fun k hk => Nat.lt_of_lt_of_le (hK k hk) (Nat.le_add_right _ _)
    obtain ⟨⟨⟨first, s1, bodyOut, bodyTy, bodyTypes, bodySchemes⟩, hb⟩, hbResult⟩ :=
      Option.isSome_iff_exists.mp (ihbody K _ _ V (ambient.onTy resultTy)
        hbodyWF hbodyB hK0 hV hVK hbD)
    obtain ⟨R, hR, hbodyTy, hRK, hag1⟩ := hb.principal hbodyWF hbodyB hK0
      V (ambient.onTy resultTy) K hV hK0 hVK hbD
    have hle := hb.frontier_le
    obtain ⟨hbB, hs1B⟩ := hb.belowFvars hbodyB hK0
    obtain ⟨hbLC, hs1LC⟩ := hb.lc hbodyWF
    have hctx0B := Subst.onCtx_below hs0B (Nat.le_add_right _ _) hbelow
    have hctx1B := Subst.onCtx_below hs1B hle hctx0B
    have hK1 : ∀ k ∈ K, k < first := fun k hk => Nat.lt_of_lt_of_le (hK0 k hk) hle
    have hres0B := Subst.onTy_belowFvars hs0B (hresultB.mono (Nat.le_add_right _ _))
    have hscrut0B := Subst.onTy_belowFvars hs0B (hscrutB.mono (Nat.le_add_right _ _))
    have hres1B := Subst.onTy_belowFvars hs1B (hres0B.mono hle)
    have hscrut1B := Subst.onTy_belowFvars hs1B (hscrut0B.mono hle)
    have hUni2 : Unifies R bodyTy (s1.onTy (s0.onTy resultTy)) := by
      change R.onTy bodyTy = R.onTy (s1.onTy (s0.onTy resultTy))
      rw [← hbodyTy]
      have heq := Subst.onTy_congr hag0 hresultB
      have heq1 := Subst.onTy_congr hag1 hres0B
      simp only [Subst.onTy_append] at heq heq1
      exact heq.trans heq1
    obtain ⟨⟨s2, hu2⟩, hu2Result⟩ := Option.isSome_iff_exists.mp
      (unifyCoreK_complete hbLC (Subst.onTy_lc hs1LC (Subst.onTy_lc hs0LC hresult)) hR hUni2 hRK)
    rcases hu2 with ⟨hun2, hav2⟩
    obtain ⟨W, hfac, hW, hWK⟩ := hun2.greatest_K R hR hUni2 hRK
    have hs2LC := hun2.lc hbLC (Subst.onTy_lc hs1LC (Subst.onTy_lc hs0LC hresult))
    have hs2B := hun2.belowFvars hbB hres1B
    have hag : Subst.AgreesBelow frontier ambient (s0 ++ s1 ++ s2 ++ W) := by
      have hag2 : Subst.AgreesBelow (frontier + ctor.paramCount) V (s1 ++ s2 ++ W) := by
        intro v hv
        have heq := hag1 v hv
        simp only [Subst.onTy_append] at heq
        simpa only [Subst.onTy_append] using heq.trans (hfac (s1.onTy (.fvar v)))
      have heq := Subst.AgreesBelow.trans_append (Nat.le_add_right frontier ctor.paramCount) hag0 hs0B hag2
      simpa only [List.append_assoc] using heq
    have hctxeq : W.onCtx (s2.onCtx (s1.onCtx (s0.onCtx ctx))) = ambient.onCtx ctx := by
      simpa only [Subst.onCtx_append] using (Subst.onCtx_congr hag hbelow).symm
    have hscruteq : W.onTy (s2.onTy (s1.onTy (s0.onTy scrutTy))) = ambient.onTy scrutTy := by
      simpa only [Subst.onTy_append] using (Subst.onTy_congr hag hscrutB).symm
    have hresulteq : W.onTy (s2.onTy (s1.onTy (s0.onTy resultTy))) = ambient.onTy resultTy := by
      simpa only [Subst.onTy_append] using (Subst.onTy_congr hag hresultB).symm
    obtain ⟨⟨⟨next, s3, restOut, restTypes, restSchemes⟩, hr⟩, hrResult⟩ :=
      Option.isSome_iff_exists.mp (ihrest K first _ _ _ (branchIndex + 1) W
        (Subst.onCtx_wf hs2LC (Subst.onCtx_wf hs1LC (Subst.onCtx_wf hs0LC hwf)))
        (Subst.onCtx_below hs2B (Nat.le_refl _) hctx1B) hK1 hW hWK
        (Subst.onTy_lc hs2LC (Subst.onTy_lc hs1LC (Subst.onTy_lc hs0LC hscrut)))
        (Subst.onTy_lc hs2LC (Subst.onTy_lc hs1LC (Subst.onTy_lc hs0LC hresult)))
        (Subst.onTy_belowFvars hs2B hscrut1B) (Subst.onTy_belowFvars hs2B hres1B)
        (by simpa only [hctxeq, hscruteq, hresulteq] using
          (fun b hb => htyping b (List.mem_cons_of_mem _ hb))))
    rw [inferBranchesWithTypesCore]
    change LookupList.get? ctx.ctors name = some ctor at hlookup
    split
    · rename_i heq
      simp only [hlookup, reduceCtorEq] at heq
    · rename_i ctor' heq
      have hct := Option.some.inj (heq.symm.trans hlookup)
      subst ctor'
      rw [dif_pos hspec.bind_count]
      simp only [hu0Result, hbResult, hu2Result, hrResult, Option.isSome_some]

theorem checkSignature_complete {K written : List Nat} {frontier : Nat} {ann : LetAnn} {ty target : Ty}
    {R : Subst} (hmode : ann.isSignature = true) (hprefix : written.length = ann.paramCount)
    (hK : ∀ k ∈ K ++ written, k < frontier) (hty : ty.IsLC) (hbelow : Ty.BelowFvars frontier ty)
    (hR : ∀ pair ∈ R, pair.2.IsLC) (hRfix : ∀ k ∈ K ++ written, R.onTy (.fvar k) = .fvar k)
    (htarget : target.IsLC) (hrigid : ∀ v ∈ ann.rigidVars, v ∈ K)
    (heq : target = R.onTy ty)
    (hcomplete : ∀ scheme, ann = .complete scheme → scheme.WF ∧ target = scheme.openVars written)
    (hpartial : ∀ count template, ann = .partialForall count template →
      (template.openTyVarsFrom 0 written).Fits target) :
    (checkSignature K written frontier ann ty).isSome := by
  cases ann with
  | absent => cases hmode
  | template => cases hmode
  | complete scheme =>
      have hSchemeWF := (hcomplete scheme rfl).1
      have hSchemeB : scheme.body.bvarsBelow scheme.paramCount = true := PolyTy.wf_iff_bvarsBelow.mpr hSchemeWF
      have hscope : scheme.body.freeVars.all (fun v => decide (v ∈ K)) = true :=
        List.all_eq_true.mpr (fun v hv => decide_eq_true (hrigid v hv))
      have hexpected := PolyTy.openVars_isLC hSchemeWF hprefix.ge
      have hExpected : R.onTy (scheme.openVars written) = scheme.openVars written := by
        apply Subst.onTy_eq_self_of_fixes
        intro v hv
        rcases Ty.freeVars_openVars_subset v hv with hv | hv
        · exact hRfix v (List.mem_append_left _ (hrigid v hv))
        · exact hRfix v (List.mem_append_right _ hv)
      have hUni : Unifies R ty (scheme.openVars written) := by
        change R.onTy ty = R.onTy (scheme.openVars written)
        rw [hExpected, ← heq, (hcomplete scheme rfl).2]
      have hunifies := unifyCoreK_complete hty hexpected hR hUni hRfix
      simp only [checkSignature, hSchemeB, hscope, dite_true]
      cases hu : unifyCoreK (K ++ written) ty (scheme.openVars written) with
      | none => simp only [hu, Option.isSome_none] at hunifies; contradiction
      | some result => rcases result with ⟨subst, hun, hav⟩; rfl
  | partialForall count template =>
      have hfit := hpartial count template rfl
      have hexpected := hfit.allocate_lc htarget frontier
      have hExpectedB : ((template.openTyVarsFrom 0 written).allocate frontier).2.bvarsBelow 0 = true :=
        (Ty.bvarsBelow_iff _).mpr hexpected
      have hscope : template.rigidVars.all (fun v => decide (v ∈ K)) = true :=
        List.all_eq_true.mpr (fun v hv => decide_eq_true (hrigid v hv))
      obtain ⟨U, hU, hag, hUexpected⟩ := hfit.allocate_override htarget hR frontier
        (fun v hv => hK v (Template.open_scope hrigid v hv))
        (fun v hv => hRfix v (Template.open_scope hrigid v hv))
      have hUty : U.onTy ty = target := (Subst.onTy_congr hag hbelow).symm.trans heq.symm
      have hUni : Unifies U ty ((template.openTyVarsFrom 0 written).allocate frontier).2 :=
        hUty.trans hUexpected.symm
      have hUfix : ∀ k ∈ K ++ written, U.onTy (.fvar k) = .fvar k := fun k hk =>
        (hag k (hK k hk)).symm.trans (hRfix k hk)
      have hunifies := unifyCoreK_complete hty hexpected hU hUni hUfix
      simp only [checkSignature, hExpectedB, hscope, dite_true]
      cases hu : unifyCoreK (K ++ written) ty ((template.openTyVarsFrom 0 written).allocate frontier).2 with
      | none => simp only [hu, Option.isSome_none] at hunifies; contradiction
      | some result => rcases result with ⟨subst, hun, hav⟩; rfl


theorem _root_.inferWithTypesCore_complete_backend {input : Input} {core : Expr}
    (hemb : input.toCore = some core) : InferWithTypesCoreComplete input := by
  intro K frontier ctx ambient target hwf hbelow hK hS hfix ht
  obtain ⟨hcore, hscope⟩ := ht.toCore hemb
  obtain ⟨next, subst, ty, R, hi, _⟩ := CoreBackend.Infer.complete core K hwf hbelow hS hK hscope hfix hcore
  have hsome := CoreBackend.inferCore_complete core K hwf hbelow hK hscope hi
  obtain ⟨⟨⟨n, s, t, nodes, schemes⟩, hresult⟩, hworker⟩ := Option.isSome_iff_exists.mp hsome
  have hscopeAll : core.tyFreeVars.all (fun v => decide (v ∈ K)) = true :=
    List.all_eq_true.mpr (fun v hv => decide_eq_true (hscope v hv))
  rw [inferWithTypesCore, dif_pos (rigid_all hK), dif_pos (ctx_all hbelow)]
  split
  · rename_i core' heq
    have hcoreeq := Option.some.inj (heq.symm.trans hemb)
    subst core'
    simp only [hscopeAll, dite_true, hworker, Option.isSome_some]
  · rename_i heq
    simp [hemb] at heq

theorem _root_.inferWithTypesCore_complete_lambda_partial
    (ih : InferWithTypesCoreComplete body) (hemb : (Input.lambda ann body).toCore = none) :
    InferWithTypesCoreComplete (.lambda ann body) := by
  intro K frontier ctx ambient target hwf hbelow hK hS hfix ht
  obtain ⟨paramD, resultD, rfl, hparamD, hfit, hrigid, hbodyD⟩ := ht.lambda_inv
  obtain ⟨⟨⟨initial, param⟩, hs⟩, hseedResult⟩ :=
    Option.isSome_iff_exists.mp (seed_complete hparamD hfit hrigid)
  obtain ⟨U, hU, hUagree, hUparam⟩ := hs.override hK hparamD hfit hS
    (fun t ht v hv => hfix v (hrigid t ht v hv))
  have hle := hs.frontier_le
  have hbodywf : CtxWF { ctx with env := PolyTy.mkTrivial param :: ctx.env } := by
    intro M hM
    rcases List.mem_cons.mp hM with rfl | hM
    · exact hs.lc
    · exact hwf M hM
  have hbodybelow : CtxBelow initial { ctx with env := PolyTy.mkTrivial param :: ctx.env } := by
    intro M hM
    rcases List.mem_cons.mp hM with rfl | hM
    · exact hs.belowFvars hK
    · exact (hbelow M hM).mono hle
  have hctxeq : U.onCtx { ctx with env := PolyTy.mkTrivial param :: ctx.env } =
      { ambient.onCtx ctx with env := PolyTy.mkTrivial paramD :: (ambient.onCtx ctx).env } := by
    have heq := Subst.onCtx_congr hUagree hbelow
    simpa only [Subst.onCtx, Subst.onEnv, List.map_cons, Subst.onPolyTy, PolyTy.mkTrivial,
      hUparam] using congrArg (fun c : Ctx => { c with env := PolyTy.mkTrivial paramD :: c.env }) heq.symm
  have hUfix : ∀ k ∈ K, U.onTy (.fvar k) = .fvar k :=
    fun k hk => (hUagree k (hK k hk)).symm.trans (hfix k hk)
  have hbody := ih K initial _ U resultD hbodywf hbodybelow
    (fun k hk => Nat.lt_of_lt_of_le (hK k hk) hle) hU hUfix (hctxeq.symm ▸ hbodyD)
  obtain ⟨⟨⟨next, subst, completed, bodyTy, bodyTypes, bodySchemes⟩, hb⟩, hbodyResult⟩ := Option.isSome_iff_exists.mp hbody
  rw [inferWithTypesCore, dif_pos (rigid_all hK), dif_pos (ctx_all hbelow)]
  split
  · rename_i core heq
    simp [hemb] at heq
  · simp only [hseedResult, hbodyResult, Option.isSome_some]

theorem _root_.inferWithTypesCore_complete_app_partial
    (ihf : InferWithTypesCoreComplete f) (iha : InferWithTypesCoreComplete arg)
    (hemb : (Input.app f arg).toCore = none) : InferWithTypesCoreComplete (.app f arg) := by
  intro K frontier ctx ambient target hwf hbelow hK hS hfix ht
  obtain ⟨paramD, hfD, haD⟩ := ht.app_inv
  obtain ⟨⟨⟨first, s1, fOut, fTy, fTypes, fSchemes⟩, hf⟩, hfResult⟩ := Option.isSome_iff_exists.mp
    (ihf K frontier ctx ambient (.arrow paramD target) hwf hbelow hK hS hfix hfD)
  obtain ⟨Rf, hRf, hfTy, hRfK, hagf⟩ := hf.principal hwf hbelow hK ambient
    (.arrow paramD target) K hS hK hfix hfD
  have hfle := hf.frontier_le
  obtain ⟨hfB, hs1B⟩ := hf.belowFvars hbelow hK
  obtain ⟨hfLC, hs1LC⟩ := hf.lc hwf
  have hctx1 := Subst.onCtx_below hs1B hfle hbelow
  have hK1 : ∀ k ∈ K, k < first := fun k hk => Nat.lt_of_lt_of_le (hK k hk) hfle
  have hctxeq : ambient.onCtx ctx = Rf.onCtx (s1.onCtx ctx) := by
    rw [← Subst.onCtx_append]
    exact Subst.onCtx_congr hagf hbelow
  obtain ⟨⟨⟨second, s2, argOut, argTy, argTypes, argSchemes⟩, ha⟩, haResult⟩ := Option.isSome_iff_exists.mp
    (iha K first (s1.onCtx ctx) Rf paramD (Subst.onCtx_wf hs1LC hwf) hctx1 hK1
      hRf hRfK (hctxeq ▸ haD))
  obtain ⟨Ra, hRa, haTy, hRaK, haga⟩ := ha.principal (Subst.onCtx_wf hs1LC hwf) hctx1 hK1
    Rf paramD K hRf hK1 hRfK (hctxeq ▸ haD)
  have hale := ha.frontier_le
  obtain ⟨haB, hs2B⟩ := ha.belowFvars hctx1 hK1
  obtain ⟨haLC, hs2LC⟩ := ha.lc (Subst.onCtx_wf hs1LC hwf)
  have hleftB := Subst.onTy_belowFvars hs2B (hfB.mono hale)
  have hleft : Ra.onTy (s2.onTy fTy) = .arrow paramD target := by
    have heq := Subst.onTy_congr haga hfB
    rw [Subst.onTy_append, ← hfTy] at heq
    exact heq.symm
  obtain ⟨U, hU, hUagree, hUblock⟩ := Subst.override_block hRa second [target]
    (by simpa using ht.regular)
  have hUret : U.onTy (.fvar second) = target := by simpa using hUblock 0 (by simp)
  have hUK : ∀ k ∈ K, U.onTy (.fvar k) = .fvar k := fun k hk =>
    (hUagree k (Nat.lt_of_lt_of_le (hK1 k hk) hale)).symm.trans (hRaK k hk)
  have hUni : Unifies U (s2.onTy fTy) (.arrow argTy (.fvar second)) := by
    change U.onTy (s2.onTy fTy) = U.onTy (.arrow argTy (.fvar second))
    rw [← Subst.onTy_congr hUagree hleftB, hleft, Subst.onTy_arrow,
      ← Subst.onTy_congr hUagree haB, ← haTy, hUret]
  have hsome := unifyCoreK_complete (Subst.onTy_lc hs2LC hfLC) (.arrow haLC .fvar) hU hUni hUK
  obtain ⟨⟨s3, hu⟩, huResult⟩ := Option.isSome_iff_exists.mp hsome
  rcases hu with ⟨hun, havoid⟩
  rw [inferWithTypesCore, dif_pos (rigid_all hK), dif_pos (ctx_all hbelow)]
  split
  · rename_i core heq; simp [hemb] at heq
  · simp only [hfResult, haResult, huResult, Option.isSome_some]

theorem _root_.inferWithTypesCore_complete_signature_partial
    {ann : LetAnn} {rhs body : Input}
    (ihr : ∀ written, InferWithTypesCoreComplete (rhs.openTyVars written))
    (ihb : InferWithTypesCoreComplete body) (hmode : ann.isSignature = true)
    (hemb : (Input.letIn ann rhs body).toCore = none) :
    InferWithTypesCoreComplete (.letIn ann rhs body) := by
  intro K frontier ctx ambient target hwf hbelow hK hS hfix ht
  obtain ⟨W, M, L, hMoved, hMovedFix, _, _, _, _, hM, hann, hrhs, hfits, htypes, hbodyD,
      hYsM, hYsCtx, hYsImages⟩ := ht.signature_dodge (K := K) hmode hbelow hK hK hS hfix
  let written := freshVars frontier ann.paramCount
  let moved := Subst.conj (blockSwap frontier W ann.paramCount) ambient
  have hYlen : written.length = ann.paramCount := freshVars_length _ _
  have hYnd : written.Nodup := freshVars_nodup
  have hYsK : ∀ y ∈ written, y ∉ K := by
    intro y hy hk
    have hge := freshVars_ge y hy
    have hlt := hK y hk
    omega
  obtain ⟨Ns, hNlen, hNnd, hNavoid⟩ := exists_fresh_names L M.paramCount
  have hCount := (hfits Ns ⟨hNlen, hNnd, hNavoid⟩).prefix_le
  obtain ⟨extras, hElen, hXsNd, _, hAll, hAligned, hAlignedFits⟩ :=
    Typing.align_partial_prefix_with_fits rfl hfits hann htypes hCount hrhs
      hYlen hYnd hYsK hYsCtx hYsM []
  have hFullLen : (written ++ extras).length = M.paramCount := by
    simp only [List.length_append, hYlen, hElen]; omega
  have hTake : (written ++ extras).take ann.paramCount = written := by rw [← hYlen]; simp
  have hCtxOpen : CtxBelow (frontier + ann.paramCount) ctx :=
    fun M hM => (hbelow M hM).mono (Nat.le_add_right _ _)
  have hKOpen : ∀ k ∈ K ++ written, k < frontier + ann.paramCount := by
    intro k hk
    rcases List.mem_append.mp hk with hk | hk
    · have := hK k hk; omega
    · exact freshVars_lt k hk
  obtain ⟨⟨⟨first, s1, rhsOut, rhsTy, rhsTypes, rhsSchemes⟩, hr⟩, hrResult⟩ :=
    Option.isSome_iff_exists.mp (ihr written (K ++ written) (frontier + ann.paramCount) ctx
      moved (M.openVars (written ++ extras)) hwf hCtxOpen hKOpen hMoved hMovedFix hAligned)
  obtain ⟨R, hR, hRty, hRfix, _⟩ := hr.principal hwf hCtxOpen hKOpen moved
    (M.openVars (written ++ extras)) (K ++ written) hMoved hKOpen hMovedFix hAligned
  have hrle := hr.frontier_le
  obtain ⟨hrB, _⟩ := hr.belowFvars hCtxOpen hKOpen
  obtain ⟨hrLC, _⟩ := hr.lc hwf
  have hKFirst : ∀ k ∈ K ++ written, k < first :=
    fun k hk => Nat.lt_of_lt_of_le (hKOpen k hk) hrle
  have hComplete : ∀ scheme, ann = .complete scheme →
      scheme.WF ∧ M.openVars (written ++ extras) = scheme.openVars written := by
    intro scheme heq
    subst ann
    cases hAlignedFits
    have hFull : written ++ extras = written := by
      have ht : (written ++ extras).take M.paramCount = written ++ extras := by
        rw [← hFullLen, List.take_length]
      exact ht.symm.trans hTake
    exact ⟨hM, congrArg M.openVars hFull⟩
  have hPartial : ∀ count template, ann = .partialForall count template →
      (template.openTyVarsFrom 0 written).Fits (M.openVars (written ++ extras)) := by
    intro count template heq
    subst ann
    cases hAlignedFits with
    | partialSignature _ hf =>
      have ht : (written ++ extras).take count = written := by simpa only [LetAnn.paramCount] using hTake
      simpa only [ht] using hf
  obtain ⟨⟨⟨checked, sCheck⟩, hc⟩, hcResult⟩ := Option.isSome_iff_exists.mp
    (checkSignature_complete hmode hYlen hKFirst hrLC hrB hR hRfix hAligned.regular hann hRty hComplete hPartial)
  obtain ⟨V, hV, hVK, hagPrefix, hbodyV, hbodyWF, hbodyB, _⟩ :=
    hr.signature_frame hc hr.principal rfl hwf hbelow hK hMoved hK hMovedFix hM hann hrhs
      hfits htypes hbodyD hYsM hYsCtx hYsImages
  have hctxeq : V.onCtx (sCheck.onCtx (s1.onCtx ctx)) = moved.onCtx ctx := by
    rw [← Subst.onCtx_append, ← Subst.onCtx_append]
    simpa only [List.append_assoc] using (Subst.onCtx_congr hagPrefix hCtxOpen).symm
  have hescape : ∀ y ∈ written, y ∉ (sCheck.onCtx (s1.onCtx ctx)).env.freeVars := by
    intro y hy hcenv
    apply hYsCtx y hy
    rw [← hctxeq]
    obtain ⟨scheme, hs, hv⟩ := Env.mem_freeVars_iff.mp hcenv
    apply Env.mem_freeVars_iff.mpr
    refine ⟨V.onPolyTy scheme, List.mem_map.mpr ⟨scheme, hs, rfl⟩, ?_⟩
    apply Ty.mem_freeVars_onTy_iff.mpr
    refine ⟨y, hv, ?_⟩
    rw [hVK y (List.mem_append_right _ hy)]
    exact List.mem_singleton_self y
  have hle : frontier ≤ checked :=
    (Nat.le_add_right frontier ann.paramCount).trans (hrle.trans hc.frontier_le)
  have hKChecked : ∀ k ∈ K, k < checked := fun k hk => Nat.lt_of_lt_of_le (hK k hk) hle
  obtain ⟨⟨⟨next, s2, bodyOut, bodyTy, bodyTypes, bodySchemes⟩, hb⟩, hbResult⟩ :=
    Option.isSome_iff_exists.mp (ihb K checked _ V _ hbodyWF hbodyB hKChecked hV
      (fun k hk => hVK k (List.mem_append_left _ hk)) hbodyV)
  have hraw : rhs.rigidVars.all (fun v => decide (v ∈ K)) = true :=
    List.all_eq_true.mpr (fun v hv => decide_eq_true (hrhs v hv))
  rw [inferWithTypesCore, dif_pos (rigid_all hK), dif_pos (ctx_all hbelow)]
  split
  · rename_i core heq; simp [hemb] at heq
  · simp only [written] at hrResult hcResult hbResult hescape
    simp only [hmode, ↓reduceIte, hraw, dite_true, hrResult, hcResult,
      dif_pos hescape, hbResult, Option.isSome_some]

theorem _root_.inferWithTypesCore_complete_letIn_partial
    (ihr : InferWithTypesCoreComplete rhs) (ihb : InferWithTypesCoreComplete body)
    (hmode : ann.isSignature = false)
    (hemb : (Input.letIn ann rhs body).toCore = none) : InferWithTypesCoreComplete (.letIn ann rhs body) := by
  intro K frontier ctx ambient target hwf hbelow hK hS hfix ht
  have hlet := ht
  cases ht with
  | complete hemb' _ _ => simp [hemb] at hemb'
  | @letSignature ann K ctx rhs body target M L _ _ _ hfit _ _ =>
    obtain ⟨Xs, hlen, hnd, hav⟩ := exists_fresh_names L M.paramCount
    have hm := (hfit Xs ⟨hlen, hnd, hav⟩).isSignature
    simp only [hmode, Bool.false_eq_true] at hm
  | @letIn ann _ _ rhs body target M L hM hannRigid hannFits hrD hbD =>
    obtain ⟨Xs, hXlen, hXnd, hXavoid⟩ := exists_fresh_names L M.paramCount
    have hXs : FreshNames L M.paramCount Xs := ⟨hXlen, hXnd, hXavoid⟩
    obtain ⟨⟨⟨first, s1, rhsOut, rhsTy, rhsTypes, rhsSchemes⟩, hr⟩, hrResult⟩ := Option.isSome_iff_exists.mp
      (ihr K frontier ctx ambient (M.openVars Xs) hwf hbelow hK hS hfix (hrD Xs hXs))
    obtain ⟨R, hR, hrTy, hRK, _⟩ := hr.principal hwf hbelow hK ambient
      (M.openVars Xs) K hS hK hfix (hrD Xs hXs)
    have hrle := hr.frontier_le
    have hK1 : ∀ k ∈ K, k < first := fun k hk => Nat.lt_of_lt_of_le (hK k hk) hrle
    obtain ⟨hrB, _⟩ := hr.belowFvars hbelow hK
    obtain ⟨hrLC, _⟩ := hr.lc hwf
    have hcheck := checkLet_complete hK1 hrLC hrB hR hRK (hrD Xs hXs).regular
      (hannFits Xs hXs) hannRigid hrTy
    obtain ⟨⟨⟨checked, sCheck⟩, hc⟩, hcResult⟩ := Option.isSome_iff_exists.mp hcheck
    obtain ⟨V, hV, hVK, _, hbodyD, hbodyWF, hbodyB, _⟩ :=
      hr.let_frame hc hr.principal hwf hbelow hK ambient target K hS hK hfix hlet
    have hle := hrle.trans hc.frontier_le
    have hKchecked : ∀ k ∈ K, k < checked := fun k hk => Nat.lt_of_lt_of_le (hK k hk) hle
    obtain ⟨⟨⟨next, s2, bodyOut, bodyTy, bodyTypes, bodySchemes⟩, hb⟩, hbResult⟩ := Option.isSome_iff_exists.mp
      (ihb K checked _ V target hbodyWF hbodyB hKchecked hV hVK hbodyD)
    rw [inferWithTypesCore, dif_pos (rigid_all hK), dif_pos (ctx_all hbelow)]
    split
    · rename_i core heq; simp [hemb] at heq
    · simp only [hmode, Bool.false_eq_true, ↓reduceIte, hrResult, hcResult, hbResult, Option.isSome_some]

theorem _root_.inferBranchesWithTypesCore_complete_of_body
    (bodyIH : ∀ branch ∈ branches, InferWithTypesCoreComplete branch.2) :
    InferBranchesWithTypesCoreComplete branches := by
  induction branches with
  | nil => exact inferBranchesWithTypesCore_complete_nil
  | cons head rest ih =>
    have hb := bodyIH head List.mem_cons_self
    have hr := ih (fun b hb => bodyIH b (List.mem_cons_of_mem _ hb))
    rcases head with ⟨pat, body⟩
    cases pat with
    | wildcard =>
        exact inferBranchesWithTypesCore_complete_wildcard hb hr
    | named name count => exact inferBranchesWithTypesCore_complete_named hb hr

theorem _root_.inferWithTypesCore_complete_match_partial
    (ihs : InferWithTypesCoreComplete scrut)
    (ihb : InferBranchesWithTypesCoreComplete branches)
    (hemb : (Input.match_ scrut branches).toCore = none) :
    InferWithTypesCoreComplete (.match_ scrut branches) := by
  intro K frontier ctx ambient target hwf hbelow hK hS hfix ht
  obtain ⟨scrutD, hsD, hne, hbD⟩ := ht.match_inv
  obtain ⟨⟨⟨first, s1, scrutOut, scrutTy, scrutTypes, scrutSchemes⟩, hs⟩, hsResult⟩ :=
    Option.isSome_iff_exists.mp (ihs K frontier ctx ambient scrutD hwf hbelow hK hS hfix hsD)
  obtain ⟨R, hR, hscrut, hRK, hag⟩ := hs.principal hwf hbelow hK ambient
    scrutD K hS hK hfix hsD
  have hle := hs.frontier_le
  obtain ⟨hsB, hs1B⟩ := hs.belowFvars hbelow hK
  obtain ⟨hsLC, hs1LC⟩ := hs.lc hwf
  have hctxB := Subst.onCtx_below hs1B hle hbelow
  obtain ⟨U, hU, hagU, hblock⟩ := Subst.override_block hR first [target]
    (by simpa using ht.regular)
  have hUtarget : U.onTy (.fvar first) = target := by simpa using hblock 0 (by simp)
  have hUK : ∀ k ∈ K, U.onTy (.fvar k) = .fvar k := fun k hk =>
    (hagU k (Nat.lt_of_lt_of_le (hK k hk) hle)).symm.trans (hRK k hk)
  have hctxeq : U.onCtx (s1.onCtx ctx) = ambient.onCtx ctx := by
    trans R.onCtx (s1.onCtx ctx)
    · exact (Subst.onCtx_congr hagU hctxB).symm
    · rw [← Subst.onCtx_append]; exact (Subst.onCtx_congr hag hbelow).symm
  have hUst : U.onTy scrutTy = scrutD :=
    (Subst.onTy_congr hagU hsB).symm.trans hscrut.symm
  obtain ⟨⟨⟨next, s2, branchOut, branchTypes, branchSchemes⟩, hb⟩, hbResult⟩ :=
    Option.isSome_iff_exists.mp (ihb K (first + 1) (s1.onCtx ctx) scrutTy (.fvar first) 0 U
      (Subst.onCtx_wf hs1LC hwf) (fun M hM => (hctxB M hM).mono (by omega))
      (fun k hk => by have := hK k hk; omega) hU hUK hsLC .fvar
      (hsB.mono (by omega)) (.fvar (by omega))
      (by simpa only [hctxeq, hUst, hUtarget] using hbD))
  rw [inferWithTypesCore, dif_pos (rigid_all hK), dif_pos (ctx_all hbelow)]
  split
  · rename_i core heq; simp [hemb] at heq
  · simp only [hsResult]
    split
    · rename_i hh
      exact False.elim (hne (List.head?_eq_none_iff.mp hh))
    · simp only [hbResult, Option.isSome_some]

private theorem branch_size_lt {branch : MatchPattern × Input}
    (h : branch ∈ branches) : branch.2.size < sizeBranches branches := by
  induction branches with
  | nil => cases h
  | cons head rest ih =>
    rcases List.mem_cons.mp h with rfl | h
    · simp only [sizeBranches]; omega
    · have := ih h; simp only [sizeBranches]; omega

/-- Concrete producer completeness for exactly the independently specified
fragment, including structured partial annotations and completed backend leaves. -/
theorem _root_.inferWithTypesCore_complete (input : Input) : InferWithTypesCoreComplete input := by
  cases hemb : input.toCore with
  | some core => exact inferWithTypesCore_complete_backend hemb
  | none =>
    cases input with
    | primLit => cases hemb
    | primBinOp => cases hemb
    | var => cases hemb
    | ctor => cases hemb
    | lambda ann body => exact inferWithTypesCore_complete_lambda_partial (inferWithTypesCore_complete body) hemb
    | app f arg => exact inferWithTypesCore_complete_app_partial (inferWithTypesCore_complete f) (inferWithTypesCore_complete arg) hemb
    | letIn ann rhs body =>
      cases hmode : ann.isSignature with
      | false =>
        exact inferWithTypesCore_complete_letIn_partial (inferWithTypesCore_complete rhs)
          (inferWithTypesCore_complete body) hmode hemb
      | true =>
        exact inferWithTypesCore_complete_signature_partial
          (fun written => inferWithTypesCore_complete (rhs.openTyVars written))
          (inferWithTypesCore_complete body) hmode hemb
    | match_ scrut branches =>
      exact inferWithTypesCore_complete_match_partial (inferWithTypesCore_complete scrut)
        (inferBranchesWithTypesCore_complete_of_body (fun branch hm => inferWithTypesCore_complete branch.2)) hemb
    | letRec anns bindings body =>
      intro K frontier ctx ambient target hwf hbelow hK hS hfix ht
      cases ht with
      | complete hemb' _ _ => simp [hemb] at hemb'
termination_by input.size
decreasing_by
  all_goals (simp only [Input.size, Input.size_openTyVars]; first | omega | have := branch_size_lt hm; omega)

/-- Completeness of the plain result API follows by projection of the same run. -/
def _root_.InferCoreComplete (input : Input) : Prop :=
  ∀ (K : List Nat) (frontier : Nat) (ctx : Ctx) (ambient : Subst) (target : Ty),
    CtxWF ctx → CtxBelow frontier ctx → (∀ k ∈ K, k < frontier) →
    (∀ pair ∈ ambient, pair.2.IsLC) →
    (∀ k ∈ K, ambient.onTy (.fvar k) = .fvar k) →
    Typing K (ambient.onCtx ctx) input target → (inferCore K frontier ctx input).isSome

theorem _root_.inferCore_complete (input : Input) : InferCoreComplete input := by
  intro K frontier ctx ambient target hwf hbelow hK hS hfix ht
  rw [inferCore_isSome]
  exact inferWithTypesCore_complete input K frontier ctx ambient target hwf hbelow hK hS hfix ht

/-- Producer completeness also yields the usual relational residual contract;
it is a corollary of concrete success and principality, not a second worker. -/
theorem _root_.Infer.complete {input : Input} {ctx : Ctx} {K : List Nat}
    {frontier : Nat} {ambient : Subst} {target : Ty}
    (hwf : CtxWF ctx) (hbelow : CtxBelow frontier ctx) (hK : ∀ k ∈ K, k < frontier)
    (hS : ∀ pair ∈ ambient, pair.2.IsLC)
    (hfix : ∀ k ∈ K, ambient.onTy (.fvar k) = .fvar k)
    (ht : Typing K (ambient.onCtx ctx) input target) :
    ∃ next subst output ty residual,
      Infer K frontier ctx input next subst output ty ∧
      (∀ pair ∈ residual, pair.2.IsLC) ∧ target = residual.onTy ty ∧
      (∀ k ∈ K, residual.onTy (.fvar k) = .fvar k) ∧
      Subst.AgreesBelow frontier ambient (subst ++ residual) := by
  obtain ⟨⟨⟨next, subst, output, ty⟩, hi⟩, _⟩ := Option.isSome_iff_exists.mp
    (inferCore_complete input K frontier ctx ambient target hwf hbelow hK hS hfix ht)
  obtain ⟨R, hR, hty, hRK, hag⟩ := hi.principal hwf hbelow hK ambient target K hS hK hfix ht
  exact ⟨next, subst, output, ty, R, hi, hR, hty, hRK, hag⟩

/-- Acceptance is exactly independent input typing under some admissible
specialization of the flexible context. Written rigid variables stay fixed. -/
theorem _root_.inferCore_accepts_iff {K : List Nat} {frontier : Nat} {ctx : Ctx} {input : Input}
    (hwf : CtxWF ctx) (hbelow : CtxBelow frontier ctx) (hK : ∀ k ∈ K, k < frontier) :
    (inferCore K frontier ctx input).isSome ↔
      ∃ (ambient : Subst) (target : Ty), (∀ pair ∈ ambient, pair.2.IsLC) ∧
        (∀ k ∈ K, ambient.onTy (.fvar k) = .fvar k) ∧
        Typing K (ambient.onCtx ctx) input target := by
  constructor
  · intro hsome
    obtain ⟨⟨⟨next, subst, output, ty⟩, hi⟩, _⟩ := Option.isSome_iff_exists.mp hsome
    exact ⟨subst, ty, (hi.lc hwf).2, Subst.fixes_of_dom_avoids hi.dom_avoids, hi.inputSound hwf⟩
  · rintro ⟨ambient, target, hS, hfix, ht⟩
    exact inferCore_complete input K frontier ctx ambient target hwf hbelow hK hS hfix ht

/-- For closed terms no context specialization is needed: accepted inputs are
precisely those admitted by the independent declarative fragment. -/
theorem _root_.inferCore_empty_accepts_iff {K : List Nat} {frontier : Nat} {ctors : CtorEnv} {input : Input}
    (hK : ∀ k ∈ K, k < frontier) :
    (inferCore K frontier ⟨[], ctors⟩ input).isSome ↔ ∃ ty, Typing K ⟨[], ctors⟩ input ty := by
  constructor
  · intro hsome
    obtain ⟨⟨⟨next, subst, output, ty⟩, hi⟩, _⟩ := Option.isSome_iff_exists.mp hsome
    exact ⟨ty, by simpa only [Subst.onCtx, Subst.onEnv, List.map_nil] using hi.inputSound CtxWF.empty⟩
  · rintro ⟨ty, ht⟩
    exact inferCore_complete input K frontier ⟨[], ctors⟩ [] ty CtxWF.empty CtxBelow.empty hK
      (by simp) (by simp) (by simpa only [Subst.onCtx, Subst.onEnv, List.map_nil] using ht)

/-- Public artifact inference is complete for independent input typing. -/
theorem _root_.inferWithTypes_complete {ctors : CtorEnv} {input : Input} {ty : Ty}
    (ht : Typing input.rigidVars ⟨[], ctors⟩ input ty) : (inferWithTypes ctors input).isSome := by
  unfold inferWithTypes
  rw [Option.isSome_map]
  exact inferWithTypesCore_complete input input.rigidVars input.freshFloor ⟨[], ctors⟩ [] ty
    CtxWF.empty CtxBelow.empty (fun v hv => Input.lt_freshFloor hv) (by simp) (by simp)
    (by simpa only [Subst.onCtx_empty] using ht)

theorem _root_.inferWithTypes_accepts_iff {ctors : CtorEnv} {input : Input} :
    (inferWithTypes ctors input).isSome ↔ ∃ ty, Typing input.rigidVars ⟨[], ctors⟩ input ty := by
  constructor
  · intro hsome
    obtain ⟨result, hresult⟩ := Option.isSome_iff_exists.mp hsome
    exact ⟨result.ty, inferWithTypes_input_sound hresult⟩
  · rintro ⟨ty, ht⟩; exact inferWithTypes_complete ht

/-- The public result retains protected-variable residual principality. -/
theorem _root_.inferWithTypes_principal {ctors : CtorEnv} {input : Input} {result : InferenceResult}
    (h : inferWithTypes ctors input = some result) :
    ∀ target, Typing input.rigidVars ⟨[], ctors⟩ input target →
      ∃ R : Subst, (∀ pair ∈ R, pair.2.IsLC) ∧ target = R.onTy result.ty ∧
        (∀ v ∈ input.rigidVars, R.onTy (.fvar v) = .fvar v) := by
  intro target ht
  have hi := inferWithTypes_infer h
  obtain ⟨R, hR, hty, hfix, _⟩ := hi.principal CtxWF.empty CtxBelow.empty
    (fun v hv => Input.lt_freshFloor hv) [] target input.rigidVars (by simp)
    (fun v hv => Input.lt_freshFloor hv) (by simp)
    (by simpa only [Subst.onCtx_empty] using ht)
  exact ⟨R, hR, hty, hfix⟩

#print axioms inferCore_complete
#print axioms Infer.complete
#print axioms inferCore_empty_accepts_iff

end Elaboration
