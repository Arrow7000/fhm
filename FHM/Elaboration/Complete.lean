import FHM.Elaboration.Principal
import FHM.Elaboration.Infer

namespace Elaboration

theorem seed_complete_source {K : List Nat} {F : List Ty} {Φ : Nat}
    {ann : Option Template} {target : Ty} {ambient : Subst}
    (_hS : ∀ p ∈ ambient, p.2.IsLC) (hlc : target.IsLC)
    (hfit : ∀ template, ann = some template → (template.substTyFvars ambient).Fits target)
    (hscope : ∀ template, ann = some template → ∀ v ∈ template.rigidVars, v ∈ K ++ softVars F) :
    (seed (K ++ softVars F) Φ ann).isSome := by
  cases ann with
  | none => rfl
  | some template =>
    have halloc : (template.allocate Φ).2.bvarsBelow 0 = true :=
      (Ty.bvarsBelow_iff _).mpr ((hfit template rfl).allocate_lc_source hlc Φ)
    have hr : template.rigidVars.all (fun v => decide (v ∈ K ++ softVars F)) = true :=
      List.all_eq_true.mpr (fun v hv => decide_eq_true (hscope template rfl v hv))
    simp only [seed, halloc, hr, dite_true, Option.isSome_some]

theorem checkLet_complete_source {K : List Nat} {F : List Ty} {Φ : Nat}
    {ann : LetAnn} {ty target : Ty} {R : Subst}
    (hK : ∀ k ∈ K, k < Φ) (hty : ty.IsLC) (hbelow : Ty.BelowFvars Φ ty)
    (hR : ∀ p ∈ R, p.2.IsLC) (hRfix : ∀ k ∈ K, R.onTy (.fvar k) = .fvar k)
    (htarget : target.IsLC) (hfit : (ann.substTyFvars R).FitsMono target)
    (hscope : ∀ v ∈ ann.rigidVars, v ∈ K ++ softVars F)
    (hraw : ∀ v ∈ ann.rigidVars, v < Φ)
    (heq : target = R.onTy ty) : (checkLet K F Φ ann ty).isSome := by
  cases ann with
  | absent => rfl
  | complete scheme => cases hfit
  | partialForall count template => cases hfit
  | template template =>
    have hlc := hfit.allocate_lc_source htarget Φ
    have halloc : (template.allocate Φ).2.bvarsBelow 0 = true := (Ty.bvarsBelow_iff _).mpr hlc
    have hr : template.rigidVars.all (fun v => decide (v ∈ K ++ softVars F)) = true :=
      List.all_eq_true.mpr (fun v hv => decide_eq_true (hscope v hv))
    obtain ⟨U, hUlc, hagree, hUexpected⟩ := hfit.allocate_override_source htarget hR Φ hraw
    have hUty : U.onTy ty = target := (Subst.onTy_congr hagree hbelow).symm.trans heq.symm
    have huni : Unifies U ty (template.allocate Φ).2 := hUty.trans hUexpected.symm
    have hunifies := unifyCoreK_complete hty hlc hUlc huni
      (fun k hk => (hagree k (hK k hk)).symm.trans (hRfix k hk))
    cases template <;> simp only [checkLet, halloc, hr, dite_true, Option.isSome_some]
    all_goals cases hu : unifyCoreK K ty _ with
      | none => simp only [hu, Option.isSome_none] at hunifies; contradiction
      | some result => rcases result with ⟨subst, hun, hav⟩; rfl



theorem checkSignature_complete_source {K written : List Nat} {F : List Ty}
    {frontier : Nat} {ann : LetAnn} {ty target : Ty} {R : Subst}
    (hmode : ann.isSignature = true) (hprefix : written.length = ann.paramCount)
    (hK : ∀ k ∈ K ++ written, k < frontier) (hty : ty.IsLC) (hbelow : Ty.BelowFvars frontier ty)
    (hR : ∀ pair ∈ R, pair.2.IsLC) (hRfix : ∀ k ∈ K ++ written, R.onTy (.fvar k) = .fvar k)
    (htarget : target.IsLC) (hscope : ∀ v ∈ ann.rigidVars, v ∈ K ++ softVars F)
    (hraw : ∀ v ∈ ann.rigidVars, v < frontier) (heq : target = R.onTy ty)
    (hcomplete : ∀ scheme, ann = .complete scheme → scheme.WF ∧ target = (R.onPolyTy scheme).openVars written)
    (hpartial : ∀ count template, ann = .partialForall count template →
      ((template.substTyFvars R).openTyVarsFrom 0 written).Fits target) :
    (checkSignature K F written frontier ann ty).isSome := by
  have hW : ∀ w ∈ written, R.onTy (.fvar w) = .fvar w :=
    fun w hw => hRfix w (List.mem_append_right _ hw)
  cases ann with
  | absent => cases hmode
  | template => cases hmode
  | complete scheme =>
    have hSchemeWF := (hcomplete scheme rfl).1
    have hSchemeB : scheme.body.bvarsBelow scheme.paramCount = true := PolyTy.wf_iff_bvarsBelow.mpr hSchemeWF
    have hr : scheme.body.freeVars.all (fun v => decide (v ∈ K ++ softVars F)) = true :=
      List.all_eq_true.mpr (fun v hv => decide_eq_true (hscope v hv))
    have hexpected := PolyTy.openVars_isLC hSchemeWF hprefix.ge
    have hExpected : R.onTy (scheme.openVars written) = (R.onPolyTy scheme).openVars written :=
      Subst.onTy_openVars_of_fixes hR hW
    have hUni : Unifies R ty (scheme.openVars written) :=
      heq.symm.trans ((hcomplete scheme rfl).2.trans hExpected.symm)
    have hunifies := unifyCoreK_complete hty hexpected hR hUni hRfix
    simp only [checkSignature, hSchemeB, hr, dite_true]
    cases hu : unifyCoreK (K ++ written) ty (scheme.openVars written) with
    | none => simp only [hu, Option.isSome_none] at hunifies; contradiction
    | some result => rcases result with ⟨subst, hun, hav⟩; rfl
  | partialForall count template =>
    have hfit := hpartial count template rfl
    rw [← Template.substTyFvars_openTyVarsFrom_of_fixes template hR hW 0] at hfit
    have hexpected := hfit.allocate_lc_source htarget frontier
    have hExpectedB : ((template.openTyVarsFrom 0 written).allocate frontier).2.bvarsBelow 0 = true :=
      (Ty.bvarsBelow_iff _).mpr hexpected
    have hr : template.rigidVars.all (fun v => decide (v ∈ K ++ softVars F)) = true :=
      List.all_eq_true.mpr (fun v hv => decide_eq_true (hscope v hv))
    obtain ⟨U, hU, hag, hUexpected⟩ := hfit.allocate_override_source htarget hR frontier (by
      intro v hv
      exact (List.mem_append.mp (Template.open_scope (K := template.rigidVars) (fun _ h => h) v hv)).elim
        (hraw v) (fun hv => hK v (List.mem_append_right _ hv)))
    have hUty : U.onTy ty = target := (Subst.onTy_congr hag hbelow).symm.trans heq.symm
    have hUni : Unifies U ty ((template.openTyVarsFrom 0 written).allocate frontier).2 :=
      hUty.trans hUexpected.symm
    have hUfix : ∀ k ∈ K ++ written, U.onTy (.fvar k) = .fvar k := fun k hk =>
      (hag k (hK k hk)).symm.trans (hRfix k hk)
    have hunifies := unifyCoreK_complete hty hexpected hU hUni hUfix
    simp only [checkSignature, hExpectedB, hr, dite_true]
    cases hu : unifyCoreK (K ++ written) ty ((template.openTyVarsFrom 0 written).allocate frontier).2 with
    | none => simp only [hu, Option.isSome_none] at hunifies; contradiction
    | some result => rcases result with ⟨subst, hun, hav⟩; rfl

/-- Internal producer contract for scoped soft-source visits. The bounded
protected candidate set is independent of K; public completeness uses P=K. -/
def _root_.InferWithTypesCoreSourceComplete (input : Input) : Prop :=
  ∀ (K : List Nat) (F : List Ty) (frontier : Nat) (ctx : Ctx)
    (ambient : Subst) (target : Ty) (P : List Nat),
    SourceScope K F input → CtxWF ctx → CtxBelow frontier ctx →
    (∀ k ∈ K, k < frontier) → (∀ t ∈ F, Ty.BelowFvars frontier t) →
    (∀ pair ∈ ambient, pair.2.IsLC) →
    (∀ k ∈ K, ambient.onTy (.fvar k) = .fvar k) →
    (∀ p ∈ P, p < frontier) → (∀ p ∈ P, ambient.onTy (.fvar p) = .fvar p) →
    Typing P (ambient.onCtx ctx) (input.substTyFvars ambient) target →
    (inferWithTypesCore K frontier ctx input F).isSome

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

private theorem soft_all {F : List Ty} (hF : ∀ t ∈ F, Ty.BelowFvars frontier t) :
    (softVars F).all (fun v => decide (v < frontier)) = true :=
  List.all_eq_true.mpr (fun v hv => decide_eq_true (softVars_lt hF v hv))

private theorem source_all (hs : SourceScope K F input) :
    input.rigidVars.all (fun v => decide (v ∈ K ++ softVars F)) = true :=
  List.all_eq_true.mpr (fun v hv => decide_eq_true (hs v hv))

theorem _root_.inferWithTypesCore_sourceComplete_backend {K : List Nat} {F : List Ty}
    {frontier : Nat} {ctx : Ctx} {input : Input} {core : Expr} {ambient : Subst} {target : Ty} {P : List Nat}
    {hemb : input.toCore = some core} {hr : ∀ v ∈ core.tyFreeVars, v ∈ K}
    {hd : ∀ v ∈ core.tyFreeVars, v ∉ softVars F}
    (hbackend : backendInput K F input = some ⟨core, hemb, hr, hd⟩)
    (hscope : SourceScope K F input) (hwf : CtxWF ctx) (hbelow : CtxBelow frontier ctx)
    (hK : ∀ k ∈ K, k < frontier) (hF : ∀ t ∈ F, Ty.BelowFvars frontier t)
    (hS : ∀ pair ∈ ambient, pair.2.IsLC)
    (hfix : ∀ k ∈ K, ambient.onTy (.fvar k) = .fvar k)
    (_hP : ∀ p ∈ P, p < frontier) (_hfixP : ∀ p ∈ P, ambient.onTy (.fvar p) = .fvar p)
    (ht : Typing P (ambient.onCtx ctx) (input.substTyFvars ambient) target) :
    (inferWithTypesCore K frontier ctx input F).isSome := by
  have hsource : input.substTyFvars ambient = input := input.substTyFvars_eq_self_of_fixes
    (fun v hv => hfix v (hr v ((Input.toCore_rigidVars _ hemb v).mp hv)))
  rw [hsource] at ht
  obtain ⟨hcore, _⟩ := ht.toCore hemb
  obtain ⟨next, subst, ty, R, hi, _⟩ := CoreBackend.Infer.complete core K hwf hbelow hS hK hr hfix hcore
  have hsome := CoreBackend.inferCore_complete core K hwf hbelow hK hr hi
  obtain ⟨⟨⟨n, s, t, nodes, schemes⟩, hresult⟩, hworker⟩ := Option.isSome_iff_exists.mp hsome
  rw [inferWithTypesCore, dif_pos (rigid_all hK), dif_pos (ctx_all hbelow),
    dif_pos (soft_all hF), dif_pos (source_all hscope)]
  split
  · rename_i core' hc hscope' hdisj' heq
    have hcoreeq : core' = core := congrArg Subtype.val (Option.some.inj (heq.symm.trans hbackend))
    subst core'
    simp only [hworker, Option.isSome_some]
  · rename_i heq
    simp only [hbackend] at heq
    cases heq

theorem _root_.inferWithTypesCore_sourceComplete_lambda
    (ih : ∀ e : Input, e.size ≤ body.size → InferWithTypesCoreSourceComplete e)
    {K : List Nat} {F : List Ty} {frontier : Nat} {ctx : Ctx} {ambient : Subst} {target : Ty} {P : List Nat}
    (hbackend : backendInput K F (.lambda ann body) = none)
    (hscope : SourceScope K F (.lambda ann body)) (hwf : CtxWF ctx) (hbelow : CtxBelow frontier ctx)
    (hK : ∀ k ∈ K, k < frontier) (hF : ∀ t ∈ F, Ty.BelowFvars frontier t)
    (hS : ∀ pair ∈ ambient, pair.2.IsLC)
    (hfix : ∀ k ∈ K, ambient.onTy (.fvar k) = .fvar k)
    (hP : ∀ p ∈ P, p < frontier) (hfixP : ∀ p ∈ P, ambient.onTy (.fvar p) = .fvar p)
    (ht : Typing P (ambient.onCtx ctx) ((Input.lambda ann body).substTyFvars ambient) target) :
    (inferWithTypesCore K frontier ctx (.lambda ann body) F).isSome := by
  obtain ⟨paramD, resultD, rfl, hparamD, hfit, _, hbodyD⟩ := ht.lambda_inv
  have hfit' : ∀ t, ann = some t → (t.substTyFvars ambient).Fits paramD := by
    intro t heq
    subst ann
    exact hfit (t.substTyFvars ambient) rfl
  have hannScope : ∀ t, ann = some t → ∀ v ∈ t.rigidVars, v ∈ K ++ softVars F := by
    intro t heq v hv
    subst ann
    exact hscope v (List.mem_append_left _ hv)
  have hbound : ∀ v ∈ K ++ softVars F, v < frontier :=
    fun v hv => (List.mem_append.mp hv).elim (hK v) (softVars_lt hF v)
  have hbodyScope : SourceScope K F body := fun v hv => hscope v (List.mem_append_right _ hv)
  have hbodyBound : ∀ v ∈ body.rigidVars, v < frontier := fun v hv => hbound v (hbodyScope v hv)
  obtain ⟨⟨⟨initial, param⟩, hs⟩, hseedResult⟩ :=
    Option.isSome_iff_exists.mp (seed_complete_source hS hparamD hfit' hannScope)
  obtain ⟨U, hU, hUagree, hUparam⟩ := hs.override hbound hparamD hS hfit'
  have hle := hs.frontier_le
  have hbodywf : CtxWF { ctx with env := PolyTy.mkTrivial param :: ctx.env } := by
    intro M hM
    rcases List.mem_cons.mp hM with rfl | hM
    · exact hs.lc
    · exact hwf M hM
  have hbodybelow : CtxBelow initial { ctx with env := PolyTy.mkTrivial param :: ctx.env } := by
    intro M hM
    rcases List.mem_cons.mp hM with rfl | hM
    · exact hs.belowFvars hbound
    · exact (hbelow M hM).mono hle
  have hctxeq : U.onCtx { ctx with env := PolyTy.mkTrivial param :: ctx.env } =
      { ambient.onCtx ctx with env := PolyTy.mkTrivial paramD :: (ambient.onCtx ctx).env } := by
    have heq := Subst.onCtx_congr hUagree hbelow
    simpa only [Subst.onCtx, Subst.onEnv, List.map_cons, Subst.onPolyTy, PolyTy.mkTrivial,
      hUparam] using congrArg (fun c : Ctx => { c with env := PolyTy.mkTrivial paramD :: c.env }) heq.symm
  have hUfix : ∀ k ∈ K, U.onTy (.fvar k) = .fvar k :=
    fun k hk => (hUagree k (hK k hk)).symm.trans (hfix k hk)
  have hUP : ∀ p ∈ P, U.onTy (.fvar p) = .fvar p :=
    fun p hp => (hUagree p (hP p hp)).symm.trans (hfixP p hp)
  have hsourceeq : body.substTyFvars U = body.substTyFvars ambient :=
    body.substTyFvars_congr (fun v hv => (hUagree v (hbodyBound v hv)).symm)
  have hbody := ih body (Nat.le_refl _) K F initial _ U resultD P hbodyScope hbodywf hbodybelow
    (fun k hk => Nat.lt_of_lt_of_le (hK k hk) hle) (fun t ht => (hF t ht).mono hle)
    hU hUfix (fun p hp => Nat.lt_of_lt_of_le (hP p hp) hle) hUP (by rwa [hctxeq, hsourceeq])
  obtain ⟨⟨⟨next, subst, completed, bodyTy, bodyTypes, bodySchemes⟩, hb⟩, hbodyResult⟩ :=
    Option.isSome_iff_exists.mp hbody
  rw [inferWithTypesCore, dif_pos (rigid_all hK), dif_pos (ctx_all hbelow),
    dif_pos (soft_all hF), dif_pos (source_all hscope)]
  split
  · rename_i backend heq
    simp only [hbackend] at heq
    cases heq
  · simp only [hseedResult, hbodyResult, Option.isSome_some]


theorem _root_.inferWithTypesCore_sourceComplete_app
    (ihf : ∀ e : Input, e.size ≤ f.size → InferWithTypesCoreSourceComplete e)
    (iha : ∀ e : Input, e.size ≤ arg.size → InferWithTypesCoreSourceComplete e)
    (pf : ∀ e : Input, e.size ≤ f.size →
      ∀ {κ F' Φ c n s o t} (h : Infer κ F' Φ c e n s o t), Infer.SourcePrincipal h)
    (pa : ∀ e : Input, e.size ≤ arg.size →
      ∀ {κ F' Φ c n s o t} (h : Infer κ F' Φ c e n s o t), Infer.SourcePrincipal h)
    {K : List Nat} {F : List Ty} {frontier : Nat} {ctx : Ctx} {ambient : Subst} {target : Ty} {P : List Nat}
    (hbackend : backendInput K F (.app f arg) = none)
    (hscope : SourceScope K F (.app f arg)) (hwf : CtxWF ctx) (hbelow : CtxBelow frontier ctx)
    (hK : ∀ k ∈ K, k < frontier) (hF : ∀ t ∈ F, Ty.BelowFvars frontier t)
    (hS : ∀ pair ∈ ambient, pair.2.IsLC)
    (hfix : ∀ k ∈ K, ambient.onTy (.fvar k) = .fvar k)
    (hP : ∀ p ∈ P, p < frontier) (hfixP : ∀ p ∈ P, ambient.onTy (.fvar p) = .fvar p)
    (ht : Typing P (ambient.onCtx ctx) ((Input.app f arg).substTyFvars ambient) target) :
    (inferWithTypesCore K frontier ctx (.app f arg) F).isSome := by
  obtain ⟨paramD, hfD, haD⟩ := ht.app_inv
  have hfScope : SourceScope K F f := fun v hv => hscope v (List.mem_append_left _ hv)
  have haScope : SourceScope K F arg := fun v hv => hscope v (List.mem_append_right _ hv)
  obtain ⟨⟨⟨first, s1, fOut, fTy, fTypes, fSchemes⟩, hf⟩, hfResult⟩ := Option.isSome_iff_exists.mp
    (ihf f (Nat.le_refl _) K F frontier ctx ambient (.arrow paramD target) P hfScope
      hwf hbelow hK hF hS hfix hP hfixP hfD)
  obtain ⟨Rf, hRf, hfTy, hRfP, hagf⟩ := pf f (Nat.le_refl _) hf hwf hbelow hK hF ambient
    (.arrow paramD target) P hS hP hfixP (fun v _ hk _ => hfix v hk) hfD
  have hfle := hf.frontier_le
  obtain ⟨hfB, hs1B⟩ := hf.belowFvars hbelow hK hF
  obtain ⟨hfLC, hs1LC⟩ := hf.lc hwf
  have hctx1 := Subst.onCtx_below hs1B hfle hbelow
  have hK1 : ∀ k ∈ K, k < first := fun k hk => Nat.lt_of_lt_of_le (hK k hk) hfle
  have hP1 : ∀ p ∈ P, p < first := fun p hp => Nat.lt_of_lt_of_le (hP p hp) hfle
  have hF1 := substSoft_below hs1B hfle hF
  have hs1K := Subst.fixes_of_dom_avoids hf.dom_avoids
  have hRfK : ∀ k ∈ K, Rf.onTy (.fvar k) = .fvar k := by
    intro k hk
    have hh := hagf k (hK k hk)
    rw [Subst.onTy_append, hs1K k hk, hfix k hk] at hh
    exact hh.symm
  have hctxeq : ambient.onCtx ctx = Rf.onCtx (s1.onCtx ctx) := by
    rw [← Subst.onCtx_append]
    exact Subst.onCtx_congr hagf hbelow
  have hargBelow : ∀ v ∈ arg.rigidVars, v < frontier := fun v hv =>
    (List.mem_append.mp (haScope v hv)).elim (hK v) (softVars_lt hF v)
  have hsourceeq : arg.substTyFvars ambient = (arg.substTyFvars s1).substTyFvars Rf := by
    rw [← Input.substTyFvars_append]
    exact arg.substTyFvars_congr (fun v hv => hagf v (hargBelow v hv))
  have hargD : Typing P (Rf.onCtx (s1.onCtx ctx)) ((arg.substTyFvars s1).substTyFvars Rf) paramD := by
    rwa [← hctxeq, ← hsourceeq]
  have hargScope := haScope.subst s1 hs1K
  have hargSize : (arg.substTyFvars s1).size ≤ arg.size := by
    simpa only [Input.size_substTyFvars] using Nat.le_refl arg.size
  obtain ⟨⟨⟨second, s2, argOut, argTy, argTypes, argSchemes⟩, ha⟩, haResult⟩ := Option.isSome_iff_exists.mp
    (iha (arg.substTyFvars s1) hargSize K (substSoft s1 F) first (s1.onCtx ctx) Rf paramD P
      hargScope (Subst.onCtx_wf hs1LC hwf) hctx1 hK1 hF1 hRf hRfK hP1 hRfP hargD)
  obtain ⟨Ra, hRa, haTy, hRaP, haga⟩ := pa (arg.substTyFvars s1) hargSize ha
    (Subst.onCtx_wf hs1LC hwf) hctx1 hK1 hF1 Rf paramD P hRf hP1 hRfP
      (fun v _ hk _ => hRfK v hk) hargD
  have hs2K := Subst.fixes_of_dom_avoids ha.dom_avoids
  have hRaK : ∀ k ∈ K, Ra.onTy (.fvar k) = .fvar k := by
    intro k hk
    have hh := haga k (hK1 k hk)
    rw [Subst.onTy_append, hs2K k hk, hRfK k hk] at hh
    exact hh.symm
  have hale := ha.frontier_le
  obtain ⟨haB, hs2B⟩ := ha.belowFvars hctx1 hK1 hF1
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
  rw [inferWithTypesCore, dif_pos (rigid_all hK), dif_pos (ctx_all hbelow),
    dif_pos (soft_all hF), dif_pos (source_all hscope)]
  split
  · rename_i backend heq
    simp only [hbackend] at heq
    cases heq
  · simp only [hfResult, haResult, huResult, Option.isSome_some]

theorem _root_.inferWithTypesCore_sourceComplete_letIn
    (ihr : ∀ e : Input, e.size ≤ rhs.size → InferWithTypesCoreSourceComplete e)
    (ihb : ∀ e : Input, e.size ≤ body.size → InferWithTypesCoreSourceComplete e)
    (prhs : ∀ e : Input, e.size ≤ rhs.size →
      ∀ {κ F' Φ c n s o t} (h : Infer κ F' Φ c e n s o t), Infer.SourcePrincipal h)
    {K : List Nat} {F : List Ty} {frontier : Nat} {ctx : Ctx} {ambient : Subst} {target : Ty} {P : List Nat}
    (hbackend : backendInput K F (.letIn ann rhs body) = none) (hmode : ann.isSignature = false)
    (hscope : SourceScope K F (.letIn ann rhs body)) (hwf : CtxWF ctx) (hbelow : CtxBelow frontier ctx)
    (hK : ∀ k ∈ K, k < frontier) (hF : ∀ t ∈ F, Ty.BelowFvars frontier t)
    (hS : ∀ pair ∈ ambient, pair.2.IsLC)
    (hfix : ∀ k ∈ K, ambient.onTy (.fvar k) = .fvar k)
    (hP : ∀ p ∈ P, p < frontier) (hfixP : ∀ p ∈ P, ambient.onTy (.fvar p) = .fvar p)
    (ht : Typing P (ambient.onCtx ctx) ((Input.letIn ann rhs body).substTyFvars ambient) target) :
    (inferWithTypesCore K frontier ctx (.letIn ann rhs body) F).isSome := by
  obtain ⟨M, L, _, _, hannFits, hrD, _⟩ := ht.letMono_inv
    (by simpa only [LetAnn.isSignature_substTyFvars] using hmode)
  obtain ⟨Xs, hXlen, hXnd, hXavoid⟩ := exists_fresh_names L M.paramCount
  have hXs : FreshNames L M.paramCount Xs := ⟨hXlen, hXnd, hXavoid⟩
  have hrhsScope : SourceScope K F rhs :=
    fun v hv => hscope v (List.mem_append_left _ (List.mem_append_right _ hv))
  have hannScope : ∀ v ∈ ann.rigidVars, v ∈ K ++ softVars F :=
    fun v hv => hscope v (List.mem_append_left _ (List.mem_append_left _ hv))
  have hannBelow : ∀ v ∈ ann.rigidVars, v < frontier := fun v hv =>
    (List.mem_append.mp (hannScope v hv)).elim (hK v) (softVars_lt hF v)
  obtain ⟨⟨⟨first, s1, rhsOut, rhsTy, rhsTypes, rhsSchemes⟩, hr⟩, hrResult⟩ := Option.isSome_iff_exists.mp
    (ihr rhs (Nat.le_refl _) K F frontier ctx ambient (M.openVars Xs) P
      hrhsScope hwf hbelow hK hF hS hfix hP hfixP (hrD Xs hXs))
  have phr := prhs rhs (Nat.le_refl _) hr
  obtain ⟨R, hR, hrTy, hRP, hagR⟩ := phr hwf hbelow hK hF ambient
    (M.openVars Xs) P hS hP hfixP (fun _ _ hk _ => hfix _ hk) (hrD Xs hXs)
  have hrle := hr.frontier_le
  have hK1 : ∀ k ∈ K, k < first := fun k hk => Nat.lt_of_lt_of_le (hK k hk) hrle
  obtain ⟨hrB, hs1B⟩ := hr.belowFvars hbelow hK hF
  obtain ⟨hrLC, hs1LC⟩ := hr.lc hwf
  have hs1K := Subst.fixes_of_dom_avoids hr.dom_avoids
  have hRK : ∀ k ∈ K, R.onTy (.fvar k) = .fvar k := by
    intro k hk
    have heq := hagR k (hK k hk)
    rw [Subst.onTy_append, hs1K k hk, hfix k hk] at heq
    exact heq.symm
  have hannEq : (ann.substTyFvars s1).substTyFvars R = ann.substTyFvars ambient := by
    rw [← LetAnn.substTyFvars_append]
    exact ann.substTyFvars_congr (fun v hv => (hagR v (hannBelow v hv)).symm)
  have hannPostScope : ∀ v ∈ (ann.substTyFvars s1).rigidVars, v ∈ K ++ softVars (substSoft s1 F) := by
    intro v hv
    obtain ⟨k, hk, hv⟩ := ann.rigidVars_substTyFvars hv
    exact scope_image hs1K (hannScope k hk) hv
  have hannPostBelow : ∀ v ∈ (ann.substTyFvars s1).rigidVars, v < first := by
    intro v hv
    obtain ⟨k, hk, hv⟩ := ann.rigidVars_substTyFvars hv
    exact (Subst.onTy_belowFvars hs1B (.fvar (Nat.lt_of_lt_of_le (hannBelow k hk) hrle))).mem_lt v hv
  have hcheck := checkLet_complete_source hK1 hrLC hrB hR hRK (hrD Xs hXs).regular
    (by rw [hannEq]; exact hannFits Xs hXs) hannPostScope hannPostBelow hrTy
  obtain ⟨⟨⟨checked, sCheck⟩, hc⟩, hcResult⟩ := Option.isSome_iff_exists.mp hcheck
  obtain ⟨V, hV, hVP, hagPrefix, hbodyD, hbodyWF, hbodyB, hprefixB⟩ :=
    hr.source_let_frame hscope hc phr hwf hbelow hK hF ambient target P hS hP hfixP
      (fun _ _ hk _ => hfix _ hk) ht
  have hle := hrle.trans hc.frontier_le
  have hKchecked : ∀ k ∈ K, k < checked := fun k hk => Nat.lt_of_lt_of_le (hK k hk) hle
  have hPchecked : ∀ p ∈ P, p < checked := fun p hp => Nat.lt_of_lt_of_le (hP p hp) hle
  have hprefixK : ∀ k ∈ K, (s1 ++ sCheck).onTy (.fvar k) = .fvar k := by
    intro k hk
    simp only [Subst.onTy_append, hs1K k hk, Subst.fixes_of_dom_avoids hc.dom_avoids k hk]
  have hVK : ∀ k ∈ K, V.onTy (.fvar k) = .fvar k := by
    intro k hk
    have heq := hagPrefix k (hK k hk)
    change ambient.onTy (.fvar k) = (s1 ++ sCheck ++ V).onTy (.fvar k) at heq
    rw [Subst.onTy_append, hprefixK k hk, hfix k hk] at heq
    exact heq.symm
  have hFchecked := substSoft_below hprefixB hle hF
  have hpostScope := hscope.subst (s1 ++ sCheck) hprefixK
  have hbodyScope : SourceScope K (substSoft (s1 ++ sCheck) F) (body.substTyFvars (s1 ++ sCheck)) :=
    fun v hv => hpostScope v (List.mem_append_right _ hv)
  obtain ⟨⟨⟨next, s2, bodyOut, bodyTy, bodyTypes, bodySchemes⟩, hb⟩, hbResult⟩ :=
    Option.isSome_iff_exists.mp (ihb (body.substTyFvars (s1 ++ sCheck)) (by
      simpa only [Input.size_substTyFvars] using Nat.le_refl body.size)
      K (substSoft (s1 ++ sCheck) F) checked _ V target P hbodyScope hbodyWF hbodyB
      hKchecked hFchecked hV hVK hPchecked hVP hbodyD)
  rw [inferWithTypesCore, dif_pos (rigid_all hK), dif_pos (ctx_all hbelow),
    dif_pos (soft_all hF), dif_pos (source_all hscope)]
  split
  · rename_i backend heq
    simp only [hbackend] at heq
    cases heq
  · simp only [hmode, Bool.false_eq_true, ↓reduceIte, hrResult, hcResult, hbResult, Option.isSome_some]

theorem _root_.inferWithTypesCore_sourceComplete_signature
    {ann : LetAnn} {rhs body : Input}
    (ihr : ∀ e : Input, e.size ≤ rhs.size → InferWithTypesCoreSourceComplete e)
    (ihb : ∀ e : Input, e.size ≤ body.size → InferWithTypesCoreSourceComplete e)
    {K : List Nat} {F : List Ty} {frontier : Nat} {ctx : Ctx} {ambient : Subst} {target : Ty} {P : List Nat}
    (hbackend : backendInput K F (.letIn ann rhs body) = none) (hmode : ann.isSignature = true)
    (hscope : SourceScope K F (.letIn ann rhs body)) (hwf : CtxWF ctx) (hbelow : CtxBelow frontier ctx)
    (hK : ∀ k ∈ K, k < frontier) (hF : ∀ t ∈ F, Ty.BelowFvars frontier t)
    (hS : ∀ pair ∈ ambient, pair.2.IsLC)
    (hfix : ∀ k ∈ K, ambient.onTy (.fvar k) = .fvar k)
    (hP : ∀ p ∈ P, p < frontier) (hfixP : ∀ p ∈ P, ambient.onTy (.fvar p) = .fvar p)
    (ht : Typing P (ambient.onCtx ctx) ((Input.letIn ann rhs body).substTyFvars ambient) target) :
    (inferWithTypesCore K frontier ctx (.letIn ann rhs body) F).isSome := by
  let Q := P ++ K
  have hQ : ∀ q ∈ Q, q < frontier := fun q hq => (List.mem_append.mp hq).elim (hP q) (hK q)
  have hfixQ : ∀ q ∈ Q, ambient.onTy (.fvar q) = .fvar q :=
    fun q hq => (List.mem_append.mp hq).elim (hfixP q) (hfix q)
  have htQ := ht.scope_mono (K' := Q) (fun _ hp => List.mem_append_left _ hp)
  obtain ⟨W, M, L, hMoved, hMovedFix, _, _, _, _, hMovedFreeze, hM, hann, hrhs, hfits, htypes,
      hbodyD, hYsM, hYsCtx, hYsSoft, hYsImages⟩ :=
    htQ.signature_dodge_source hmode hscope hbelow hQ hK hF hS hfixQ (fun v _ hk _ => hfix v hk)
  let written := freshVars frontier ann.paramCount
  let moved := Subst.conj (blockSwap frontier W ann.paramCount) ambient
  have hYlen : written.length = ann.paramCount := freshVars_length _ _
  have hYnd : written.Nodup := freshVars_nodup
  have hMovedK : ∀ k ∈ K ++ written, moved.onTy (.fvar k) = .fvar k := by
    intro k hk
    rcases List.mem_append.mp hk with hk | hk
    · exact hMovedFix k (List.mem_append_left _ (List.mem_append_right _ hk))
    · exact hMovedFix k (List.mem_append_right _ hk)
  have hYsQ : ∀ y ∈ written, y ∉ Q := by
    intro y hy hq
    have := freshVars_ge y hy
    have := hQ y hq
    omega
  obtain ⟨Ns, hNlen, hNnd, hNavoid⟩ := exists_fresh_names L M.paramCount
  have hCount : ann.paramCount ≤ M.paramCount := by
    simpa only [LetAnn.paramCount_substTyFvars] using (hfits Ns ⟨hNlen, hNnd, hNavoid⟩).prefix_le
  obtain ⟨extras, hElen, hXsNd, _, hAll, hAligned, hAlignedFits⟩ :=
    Typing.align_partial_prefix_with_fits (by simp) hfits hann htypes hCount hrhs
      hYlen hYnd hYsQ hYsCtx hYsM []
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
  have hQOpen : ∀ q ∈ Q ++ written, q < frontier + ann.paramCount := by
    intro q hq
    rcases List.mem_append.mp hq with hq | hq
    · have := hQ q hq; omega
    · exact freshVars_lt q hq
  have hRhsRaw : SourceScope K F rhs :=
    fun v hv => hscope v (List.mem_append_left _ (List.mem_append_right _ hv))
  have hRhsOpen : SourceScope (K ++ written) F (rhs.openTyVars written) := by
    intro v hv
    have hm := rhs.openTyVars_scope hRhsRaw written v hv
    simp only [List.mem_append] at hm ⊢
    tauto
  have hFOpen : ∀ t ∈ F, Ty.BelowFvars (frontier + ann.paramCount) t :=
    fun t ht => (hF t ht).mono (Nat.le_add_right _ _)
  have hAligned' : Typing (Q ++ written) (moved.onCtx ctx)
      ((rhs.openTyVars written).substTyFvars moved) (M.openVars (written ++ extras)) := by
    rwa [Input.substTyFvars_openTyVars_of_fixes rhs hMoved (fun w hw => hMovedFix w (List.mem_append_right _ hw))]
  obtain ⟨⟨⟨first, s1, rhsOut, rhsTy, rhsTypes, rhsSchemes⟩, hr⟩, hrResult⟩ :=
    Option.isSome_iff_exists.mp (ihr (rhs.openTyVars written) (by simp)
      (K ++ written) F (frontier + ann.paramCount) ctx moved (M.openVars (written ++ extras))
      (Q ++ written) hRhsOpen hwf hCtxOpen hKOpen hFOpen hMoved hMovedK hQOpen hMovedFix hAligned')
  obtain ⟨R, hR, hRty, hRfix, hagR⟩ := hr.sourcePrincipal hwf hCtxOpen hKOpen hFOpen moved
    (M.openVars (written ++ extras)) (Q ++ written) hMoved hQOpen hMovedFix
    (fun v _ hk _ => hMovedK v hk) hAligned'
  have hrle := hr.frontier_le
  obtain ⟨hrB, hs1B⟩ := hr.belowFvars hCtxOpen hKOpen hFOpen
  obtain ⟨hrLC, hs1LC⟩ := hr.lc hwf
  have hKFirst : ∀ k ∈ K ++ written, k < first :=
    fun k hk => Nat.lt_of_lt_of_le (hKOpen k hk) hrle
  have hFixRK : ∀ k ∈ K ++ written, R.onTy (.fvar k) = .fvar k := by
    intro k hk
    rcases List.mem_append.mp hk with hk | hk
    · exact hRfix k (List.mem_append_left _ (List.mem_append_right _ hk))
    · exact hRfix k (List.mem_append_right _ hk)
  have hBound : ∀ v ∈ K ++ softVars F, v < frontier :=
    fun v hv => (List.mem_append.mp hv).elim (hK v) (softVars_lt hF v)
  have hAnnSource : (ann.substTyFvars s1).substTyFvars R = ann.substTyFvars moved := by
    rw [← LetAnn.substTyFvars_append]
    exact ann.substTyFvars_congr (fun v hv => (hagR v (by
      have := hBound v (hscope v (List.mem_append_left _ (List.mem_append_left _ hv))); omega)).symm)
  have hAnnScope : ∀ v ∈ (ann.substTyFvars s1).rigidVars, v ∈ K ++ softVars (substSoft s1 F) := by
    intro v hv
    obtain ⟨old, ho, him⟩ := LetAnn.rigidVars_substTyFvars hv
    exact scope_image (Subst.fixes_of_dom_avoids (fun p hp hk => hr.dom_avoids p hp (List.mem_append_left _ hk)))
      (hscope old (List.mem_append_left _ (List.mem_append_left _ ho))) him
  have hF1 := substSoft_below hs1B hrle hFOpen
  have hAnnBound : ∀ v ∈ (ann.substTyFvars s1).rigidVars, v < first :=
    fun v hv => (List.mem_append.mp (hAnnScope v hv)).elim
      (fun hk => hKFirst v (List.mem_append_left _ hk)) (softVars_lt hF1 v)
  have hFitsPost : ((ann.substTyFvars s1).substTyFvars R).SignatureFits M (written ++ extras) :=
    hAnnSource.symm ▸ hAlignedFits
  have hComplete : ∀ scheme, ann.substTyFvars s1 = .complete scheme →
      scheme.WF ∧ M.openVars (written ++ extras) = (R.onPolyTy scheme).openVars written := by
    intro scheme heq
    rw [heq] at hFitsPost
    cases hFitsPost
    have hWF : scheme.WF := ContainsBvarsUpTo.of_substFvars hM
    have hCountEq : scheme.paramCount = ann.paramCount := by
      have he := congrArg LetAnn.paramCount heq
      rw [LetAnn.paramCount_substTyFvars] at he
      exact he.symm
    have hFull : written ++ extras = written := by
      have ht : (written ++ extras).take scheme.paramCount = written ++ extras := by
        change (written ++ extras).length = scheme.paramCount at hFullLen
        rw [← hFullLen, List.take_length]
      exact ht.symm.trans (by rwa [hCountEq])
    exact ⟨hWF, congrArg (R.onPolyTy scheme).openVars hFull⟩
  have hPartial : ∀ count template, ann.substTyFvars s1 = .partialForall count template →
      ((template.substTyFvars R).openTyVarsFrom 0 written).Fits (M.openVars (written ++ extras)) := by
    intro count template heq
    rw [heq] at hFitsPost
    cases hFitsPost with
    | partialSignature _ hf =>
      have ht : (written ++ extras).take count = written := by
        have hc : ann.paramCount = count := by simpa using congrArg LetAnn.paramCount heq
        rw [← hc]
        exact hTake
      simpa only [ht] using hf
  obtain ⟨⟨⟨checked, sCheck⟩, hc⟩, hcResult⟩ := Option.isSome_iff_exists.mp
    (checkSignature_complete_source (by simpa using hmode) (by simpa using hYlen) hKFirst
      hrLC hrB hR hFixRK hAligned.regular hAnnScope hAnnBound hRty hComplete hPartial)
  obtain ⟨V, hV, hVQ, hagPrefix, hbodyV, hbodyWF, hbodyB, hprefixB, hescape⟩ :=
    Infer.source_signature_frame hscope hr hc hr.sourcePrincipal rfl hwf hbelow hK hF
      hMoved hQ hMovedFix hMovedFreeze hM hann hrhs hfits htypes hbodyD hYsM hYsCtx hYsImages hYsSoft
  have hle : frontier ≤ checked :=
    (Nat.le_add_right frontier ann.paramCount).trans (hrle.trans hc.frontier_le)
  have hPrefixFix : ∀ k ∈ K, (s1 ++ sCheck).onTy (.fvar k) = .fvar k := by
    apply Subst.fixes_of_dom_avoids
    intro p hp hk
    exact (List.mem_append.mp hp).elim
      (fun hp => hr.dom_avoids p hp (List.mem_append_left _ hk))
      (fun hp => hc.dom_avoids p hp (List.mem_append_left _ hk))
  have hVK : ∀ k ∈ K, V.onTy (.fvar k) = .fvar k := by
    intro k hk
    have heq := hagPrefix k (by have := hK k hk; omega)
    rw [Subst.onTy_append, hPrefixFix k hk, hMovedK k (List.mem_append_left _ hk)] at heq
    exact heq.symm
  have hbodyScope := (show SourceScope K F body from fun v hv => hscope v (List.mem_append_right _ hv)).subst
    (s1 ++ sCheck) hPrefixFix
  obtain ⟨⟨⟨next, s2, bodyOut, bodyTy, bodyTypes, bodySchemes⟩, hb⟩, hbResult⟩ :=
    Option.isSome_iff_exists.mp (ihb (body.substTyFvars (s1 ++ sCheck)) (by simp) K
      (substSoft (s1 ++ sCheck) F) checked _ V _ Q hbodyScope hbodyWF hbodyB
      (fun k hk => Nat.lt_of_lt_of_le (hK k hk) hle) (substSoft_below hprefixB hle hF)
      hV hVK (fun q hq => Nat.lt_of_lt_of_le (hQ q hq) hle)
      (fun q hq => hVQ q (List.mem_append_left _ hq)) hbodyV)
  have hraw : rhs.rigidVars.all (fun v => decide (v ∈ K ++ softVars F)) = true :=
    List.all_eq_true.mpr (fun v hv => decide_eq_true (hRhsRaw v hv))
  rw [inferWithTypesCore, dif_pos (rigid_all hK), dif_pos (ctx_all hbelow),
    dif_pos (soft_all hF), dif_pos (source_all hscope)]
  split
  · rename_i core heq; simp only [hbackend] at heq; cases heq
  · simp only [written] at hrResult hcResult hbResult hescape
    simp only [hmode, ↓reduceIte, hraw, dite_true, hrResult, hcResult,
      dif_pos hescape, hbResult, Option.isSome_some]

private theorem branch_rigid_mem {bs : List (MatchPattern × Input)} {b : MatchPattern × Input}
    (hb : b ∈ bs) {v : Nat} (hv : v ∈ b.2.rigidVars) : v ∈ rigidBranchVars bs := by
  induction bs with
  | nil => cases hb
  | cons head tail ih =>
    exact (List.mem_cons.mp hb).elim (fun heq => List.mem_append_left _ (heq ▸ hv))
      (fun hb => List.mem_append_right _ (ih hb))

private theorem branch_candidates_frame {bs : List (MatchPattern × Input)}
    {ambient solved residual : Subst} {Φ : Nat} {ctx ctx' : Ctx} {P : List Nat} {st rt : Ty}
    (hbelow : ∀ v ∈ rigidBranchVars bs, v < Φ)
    (hag : Subst.AgreesBelow Φ ambient (solved ++ residual))
    (hctx : residual.onCtx ctx' = ambient.onCtx ctx)
    (hbr : ∀ b ∈ bs, BranchTyping Typing P (ambient.onCtx ctx)
      (b.1, b.2.substTyFvars ambient) st rt) :
    ∀ b ∈ substInputBranches solved bs,
      BranchTyping Typing P (residual.onCtx ctx') (b.1, b.2.substTyFvars residual) st rt := by
  intro b hb
  rw [substInputBranches_eq_map] at hb
  obtain ⟨original, horiginal, rfl⟩ := List.mem_map.mp hb
  have hsource : original.2.substTyFvars ambient =
      (original.2.substTyFvars solved).substTyFvars residual := by
    rw [← Input.substTyFvars_append]
    exact original.2.substTyFvars_congr (fun v hv => hag v (hbelow v (branch_rigid_mem horiginal hv)))
  rw [hctx, ← hsource]
  exact hbr original horiginal


def _root_.InferBranchesWithTypesCoreSourceComplete (branches : List (MatchPattern × Input)) : Prop :=
  ∀ (K : List Nat) (F : List Ty) (frontier : Nat) (ctx : Ctx) (scrutTy resultTy : Ty)
    (branchIndex : Nat) (ambient : Subst) (P : List Nat),
    (∀ v ∈ rigidBranchVars branches, v ∈ K ++ softVars F) →
    CtxWF ctx → CtxBelow frontier ctx → (∀ k ∈ K, k < frontier) →
    (∀ t ∈ F, Ty.BelowFvars frontier t) → (∀ pair ∈ ambient, pair.2.IsLC) →
    (∀ k ∈ K, ambient.onTy (.fvar k) = .fvar k) →
    (∀ p ∈ P, p < frontier) → (∀ p ∈ P, ambient.onTy (.fvar p) = .fvar p) →
    scrutTy.IsLC → resultTy.IsLC → Ty.BelowFvars frontier scrutTy → Ty.BelowFvars frontier resultTy →
    (∀ b ∈ branches, BranchTyping Typing P (ambient.onCtx ctx) (b.1, b.2.substTyFvars ambient)
      (ambient.onTy scrutTy) (ambient.onTy resultTy)) →
    (inferBranchesWithTypesCore K frontier ctx scrutTy resultTy branchIndex branches F).isSome

private theorem branch_source_all (hs : ∀ v ∈ rigidBranchVars branches, v ∈ K ++ softVars F) :
    (rigidBranchVars branches).all (fun v => decide (v ∈ K ++ softVars F)) = true :=
  List.all_eq_true.mpr (fun v hv => decide_eq_true (hs v hv))

private theorem branch_scope_subst {bs : List (MatchPattern × Input)} {S : Subst}
    (hscope : ∀ v ∈ rigidBranchVars bs, v ∈ K ++ softVars F)
    (hfix : ∀ k ∈ K, S.onTy (.fvar k) = .fvar k) :
    ∀ v ∈ rigidBranchVars (substInputBranches S bs), v ∈ K ++ softVars (substSoft S F) := by
  intro v hv
  obtain ⟨k, hk, hv⟩ := rigidBranchVars_substTyFvars hv
  exact scope_image hfix (hscope k hk) hv

private theorem residual_fixes_of_agrees {K : List Nat} {Φ : Nat} {ambient solved residual : Subst}
    (hK : ∀ k ∈ K, k < Φ) (hfix : ∀ k ∈ K, ambient.onTy (.fvar k) = .fvar k)
    (hsolved : ∀ k ∈ K, solved.onTy (.fvar k) = .fvar k)
    (hag : Subst.AgreesBelow Φ ambient (solved ++ residual)) :
    ∀ k ∈ K, residual.onTy (.fvar k) = .fvar k := by
  intro k hk
  have hh := hag k (hK k hk)
  rw [Subst.onTy_append, hsolved k hk, hfix k hk] at hh
  exact hh.symm

theorem _root_.inferBranchesWithTypesCore_sourceComplete_nil : InferBranchesWithTypesCoreSourceComplete [] := by
  unfold InferBranchesWithTypesCoreSourceComplete
  intros
  simp only [inferBranchesWithTypesCore, rigidBranchVars, List.all_nil, dite_true, Option.isSome_some]

theorem _root_.inferBranchesWithTypesCore_sourceComplete_wildcard
    (ihbody : ∀ e : Input, e.size ≤ body.size → InferWithTypesCoreSourceComplete e)
    (pbody : ∀ e : Input, e.size ≤ body.size →
      ∀ {κ F' Φ c n s o t} (h : Infer κ F' Φ c e n s o t), Infer.SourcePrincipal h)
    (ihrest : ∀ bs : List (MatchPattern × Input), sizeBranches bs ≤ sizeBranches rest →
      InferBranchesWithTypesCoreSourceComplete bs) :
    InferBranchesWithTypesCoreSourceComplete ((.wildcard, body) :: rest) := by
  intro K F frontier ctx scrutTy resultTy branchIndex ambient P hscope hwf hbelow hK hF hS hfix hP hfixP
    hscrut hresult hscrutB hresultB htyping
  have hbodyScope : SourceScope K F body := fun v hv => hscope v (List.mem_append_left _ hv)
  have hrestScope : ∀ v ∈ rigidBranchVars rest, v ∈ K ++ softVars F :=
    fun v hv => hscope v (List.mem_append_right _ hv)
  have hrestBelow : ∀ v ∈ rigidBranchVars rest, v < frontier := fun v hv =>
    (List.mem_append.mp (hrestScope v hv)).elim (hK v) (softVars_lt hF v)
  have hbodyD := htyping (.wildcard, body) List.mem_cons_self
  cases hbodyD with
  | wildcard hbodyD =>
    obtain ⟨⟨⟨first, s1, bodyOut, bodyTy, bodyTypes, bodySchemes⟩, hb⟩, hbResult⟩ :=
      Option.isSome_iff_exists.mp
        (ihbody body (Nat.le_refl _) K F frontier ctx ambient (ambient.onTy resultTy) P
          hbodyScope hwf hbelow hK hF hS hfix hP hfixP hbodyD)
    obtain ⟨R, hR, hbodyTy, hRP, hag⟩ := pbody body (Nat.le_refl _) hb
      hwf hbelow hK hF ambient (ambient.onTy resultTy) P hS hP hfixP (fun _ _ hk _ => hfix _ hk) hbodyD
    have hle := hb.frontier_le
    obtain ⟨hbB, hs1B⟩ := hb.belowFvars hbelow hK hF
    obtain ⟨hbLC, hs1LC⟩ := hb.lc hwf
    have hctx1 := Subst.onCtx_below hs1B hle hbelow
    have hK1 : ∀ k ∈ K, k < first := fun k hk => Nat.lt_of_lt_of_le (hK k hk) hle
    have hP1 : ∀ p ∈ P, p < first := fun p hp => Nat.lt_of_lt_of_le (hP p hp) hle
    have hs1K := Subst.fixes_of_dom_avoids hb.dom_avoids
    have hRK := residual_fixes_of_agrees hK hfix hs1K hag
    have hrightB := Subst.onTy_belowFvars hs1B (hresultB.mono hle)
    have hscrut1B := Subst.onTy_belowFvars hs1B (hscrutB.mono hle)
    have hUni : Unifies R bodyTy (s1.onTy resultTy) := by
      change R.onTy bodyTy = R.onTy (s1.onTy resultTy)
      rw [← hbodyTy]
      simpa only [Subst.onTy_append] using Subst.onTy_congr hag hresultB
    obtain ⟨⟨s2, hu⟩, huResult⟩ := Option.isSome_iff_exists.mp
      (unifyCoreK_complete hbLC (Subst.onTy_lc hs1LC hresult) hR hUni hRK)
    rcases hu with ⟨hun, hav⟩
    obtain ⟨V, hfac, hV, hVKP⟩ := hun.greatest_K R hR hUni
      (K := K ++ P) (fun k hk => (List.mem_append.mp hk).elim (hRK k) (hRP k))
    have hVK : ∀ k ∈ K, V.onTy (.fvar k) = .fvar k := fun k hk => hVKP k (List.mem_append_left _ hk)
    have hVP : ∀ p ∈ P, V.onTy (.fvar p) = .fvar p := fun p hp => hVKP p (List.mem_append_right _ hp)
    have hs2LC := hun.lc hbLC (Subst.onTy_lc hs1LC hresult)
    have hs2B := hun.belowFvars hbB hrightB
    have hagV : Subst.AgreesBelow frontier ambient ((s1 ++ s2) ++ V) := by
      intro v hv
      have heq := hag v hv
      simp only [Subst.onTy_append] at heq
      simpa only [Subst.onTy_append] using heq.trans (hfac (s1.onTy (.fvar v)))
    have hctxeq : V.onCtx (s2.onCtx (s1.onCtx ctx)) = ambient.onCtx ctx := by
      simpa only [Subst.onCtx_append] using (Subst.onCtx_congr hagV hbelow).symm
    have hscruteq : V.onTy (s2.onTy (s1.onTy scrutTy)) = ambient.onTy scrutTy := by
      simpa only [Subst.onTy_append] using (Subst.onTy_congr hagV hscrutB).symm
    have hresulteq : V.onTy (s2.onTy (s1.onTy resultTy)) = ambient.onTy resultTy := by
      simpa only [Subst.onTy_append] using (Subst.onTy_congr hagV hresultB).symm
    have hprefixK : ∀ k ∈ K, (s1 ++ s2).onTy (.fvar k) = .fvar k := by
      intro k hk
      simp only [Subst.onTy_append, hs1K k hk, Subst.fixes_of_dom_avoids hav k hk]
    have hFnext : ∀ t ∈ substSoft (s1 ++ s2) F, Ty.BelowFvars first t := by
      simpa only [substSoft_append] using substSoft_below hs2B (Nat.le_refl _) (substSoft_below hs1B hle hF)
    have hbr := branch_candidates_frame hrestBelow hagV hctxeq
      (fun b hb => htyping b (List.mem_cons_of_mem _ hb))
    obtain ⟨⟨⟨next, s3, restOut, restTypes, restSchemes⟩, hr⟩, hrResult⟩ :=
      Option.isSome_iff_exists.mp (ihrest (substInputBranches (s1 ++ s2) rest) (by
        simp only [sizeBranches_substInputBranches]; exact Nat.le_refl _) K (substSoft (s1 ++ s2) F) first
        (s2.onCtx (s1.onCtx ctx)) (s2.onTy (s1.onTy scrutTy)) (s2.onTy (s1.onTy resultTy))
        (branchIndex + 1) V P (branch_scope_subst hrestScope hprefixK)
        (Subst.onCtx_wf hs2LC (Subst.onCtx_wf hs1LC hwf))
        (Subst.onCtx_below hs2B (Nat.le_refl _) hctx1) hK1 hFnext hV hVK hP1 hVP
        (Subst.onTy_lc hs2LC (Subst.onTy_lc hs1LC hscrut))
        (Subst.onTy_lc hs2LC (Subst.onTy_lc hs1LC hresult))
        (Subst.onTy_belowFvars hs2B hscrut1B) (Subst.onTy_belowFvars hs2B hrightB)
        (by simpa only [hscruteq, hresulteq] using hbr))
    simp only [inferBranchesWithTypesCore, dif_pos (branch_source_all hscope),
      hbResult, huResult, hrResult, Option.isSome_some]
theorem _root_.inferBranchesWithTypesCore_sourceComplete_named
    (ihbody : ∀ e : Input, e.size ≤ body.size → InferWithTypesCoreSourceComplete e)
    (pbody : ∀ e : Input, e.size ≤ body.size →
      ∀ {κ F' Φ c n s o t} (h : Infer κ F' Φ c e n s o t), Infer.SourcePrincipal h)
    (ihrest : ∀ bs : List (MatchPattern × Input), sizeBranches bs ≤ sizeBranches rest →
      InferBranchesWithTypesCoreSourceComplete bs) :
    InferBranchesWithTypesCoreSourceComplete ((.named name count, body) :: rest) := by
  intro K F frontier ctx scrutTy resultTy branchIndex ambient P hscope hwf hbelow hK hF hS hfix hP hfixP
    hscrut hresult hscrutB hresultB htyping
  have hbodyScope : SourceScope K F body := fun v hv => hscope v (List.mem_append_left _ hv)
  have hbodyBelow : ∀ v ∈ body.rigidVars, v < frontier := fun v hv =>
    (List.mem_append.mp (hbodyScope v hv)).elim (hK v) (softVars_lt hF v)
  have hrestScope : ∀ v ∈ rigidBranchVars rest, v ∈ K ++ softVars F :=
    fun v hv => hscope v (List.mem_append_right _ hv)
  have hrestBelow : ∀ v ∈ rigidBranchVars rest, v < frontier := fun v hv =>
    (List.mem_append.mp (hrestScope v hv)).elim (hK v) (softVars_lt hF v)
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
    have hhead : BranchTyping Typing P (ambient.onCtx ctx) (.named name count, body.substTyFvars ambient)
        (ambient.onTy scrutTy) (ambient.onTy resultTy) := .named hspec hbodyD
    obtain ⟨V, hV, hVP, hag0, hbD⟩ := hhead.factor_named hlookup hun0 hbelow hscrutB hS
      (Subst.onTy_lc hS hscrut) hP hfixP rfl
    have hs0K := Subst.fixes_of_dom_avoids hav0
    have hVK := residual_fixes_of_agrees hK hfix hs0K hag0
    have hsource0 : body.substTyFvars ambient = (body.substTyFvars s0).substTyFvars V := by
      rw [← Input.substTyFvars_append]
      exact body.substTyFvars_congr (fun v hv => hag0 v (hbodyBelow v hv))
    rw [hsource0] at hbD
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
    have hP0 : ∀ p ∈ P, p < frontier + ctor.paramCount :=
      fun p hp => Nat.lt_of_lt_of_le (hP p hp) (Nat.le_add_right _ _)
    have hF0 := substSoft_below hs0B (Nat.le_add_right _ _) hF
    have hbodyScope0 := hbodyScope.subst s0 hs0K
    have hbodySize : (body.substTyFvars s0).size ≤ body.size := by
      simpa only [Input.size_substTyFvars] using Nat.le_refl body.size
    obtain ⟨⟨⟨first, s1, bodyOut, bodyTy, bodyTypes, bodySchemes⟩, hb⟩, hbResult⟩ :=
      Option.isSome_iff_exists.mp (ihbody (body.substTyFvars s0) hbodySize K (substSoft s0 F) _ _ V
        (ambient.onTy resultTy) P hbodyScope0 hbodyWF hbodyB hK0 hF0 hV hVK hP0 hVP hbD)
    obtain ⟨R, hR, hbodyTy, hRP, hag1⟩ := pbody (body.substTyFvars s0) hbodySize hb
      hbodyWF hbodyB hK0 hF0 V (ambient.onTy resultTy) P hV hP0 hVP (fun _ _ hk _ => hVK _ hk) hbD
    have hs1K := Subst.fixes_of_dom_avoids hb.dom_avoids
    have hRK := residual_fixes_of_agrees hK0 hVK hs1K hag1
    have hle := hb.frontier_le
    obtain ⟨hbB, hs1B⟩ := hb.belowFvars hbodyB hK0 hF0
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
    obtain ⟨W, hfac, hW, hWKP⟩ := hun2.greatest_K R hR hUni2
      (K := K ++ P) (fun k hk => (List.mem_append.mp hk).elim (hRK k) (hRP k))
    have hWK : ∀ k ∈ K, W.onTy (.fvar k) = .fvar k := fun k hk => hWKP k (List.mem_append_left _ hk)
    have hWP : ∀ p ∈ P, W.onTy (.fvar p) = .fvar p := fun p hp => hWKP p (List.mem_append_right _ hp)
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
    have hs2K := Subst.fixes_of_dom_avoids hav2
    have hprefixK : ∀ k ∈ K, (s0 ++ s1 ++ s2).onTy (.fvar k) = .fvar k := by
      intro k hk
      simp only [Subst.onTy_append, hs0K k hk, hs1K k hk, hs2K k hk]
    have hFnext : ∀ t ∈ substSoft (s0 ++ s1 ++ s2) F, Ty.BelowFvars first t := by
      simpa only [substSoft_append] using substSoft_below hs2B (Nat.le_refl _)
        (substSoft_below hs1B hle hF0)
    have hP1 : ∀ p ∈ P, p < first := fun p hp => Nat.lt_of_lt_of_le (hP0 p hp) hle
    have hbr := branch_candidates_frame hrestBelow hag hctxeq
      (fun b hb => htyping b (List.mem_cons_of_mem _ hb))
    obtain ⟨⟨⟨next, s3, restOut, restTypes, restSchemes⟩, hr⟩, hrResult⟩ :=
      Option.isSome_iff_exists.mp (ihrest (substInputBranches (s0 ++ s1 ++ s2) rest) (by
        simp only [sizeBranches_substInputBranches]; exact Nat.le_refl _) K (substSoft (s0 ++ s1 ++ s2) F)
        first (s2.onCtx (s1.onCtx (s0.onCtx ctx))) (s2.onTy (s1.onTy (s0.onTy scrutTy)))
        (s2.onTy (s1.onTy (s0.onTy resultTy))) (branchIndex + 1) W P
        (branch_scope_subst hrestScope hprefixK)
        (Subst.onCtx_wf hs2LC (Subst.onCtx_wf hs1LC (Subst.onCtx_wf hs0LC hwf)))
        (Subst.onCtx_below hs2B (Nat.le_refl _) hctx1B) hK1 hFnext hW hWK hP1 hWP
        (Subst.onTy_lc hs2LC (Subst.onTy_lc hs1LC (Subst.onTy_lc hs0LC hscrut)))
        (Subst.onTy_lc hs2LC (Subst.onTy_lc hs1LC (Subst.onTy_lc hs0LC hresult)))
        (Subst.onTy_belowFvars hs2B hscrut1B) (Subst.onTy_belowFvars hs2B hres1B)
        (by simpa only [hscruteq, hresulteq] using hbr))
    rw [inferBranchesWithTypesCore, dif_pos (branch_source_all hscope)]
    dsimp only
    change LookupList.get? ctx.ctors name = some ctor at hlookup
    split
    · rename_i heq
      simp only [hlookup, reduceCtorEq] at heq
    · rename_i ctor' heq
      have hct := Option.some.inj (heq.symm.trans hlookup)
      subst ctor'
      rw [dif_pos hspec.bind_count]
      simp only [hu0Result, hbResult, hu2Result, hrResult, Option.isSome_some]



set_option maxRecDepth 4096 in
theorem _root_.inferBranchesWithTypesCore_sourceComplete_of_body (branches : List (MatchPattern × Input))
    (bodyIH : ∀ e : Input, e.size < sizeBranches branches → InferWithTypesCoreSourceComplete e)
    (principalIH : ∀ e : Input, e.size < sizeBranches branches →
      ∀ {κ F' Φ c n s o t} (h : Infer κ F' Φ c e n s o t), Infer.SourcePrincipal h) :
    InferBranchesWithTypesCoreSourceComplete branches := by
  cases branches with
  | nil => exact inferBranchesWithTypesCore_sourceComplete_nil
  | cons head rest =>
    rcases head with ⟨pat, body⟩
    have ihbody : ∀ e : Input, e.size ≤ body.size → InferWithTypesCoreSourceComplete e :=
      fun e he => bodyIH e (by simp only [sizeBranches]; omega)
    have pbody : ∀ e : Input, e.size ≤ body.size →
        ∀ {κ F' Φ c n s o t} (h : Infer κ F' Φ c e n s o t), Infer.SourcePrincipal h :=
      fun e he {_ _ _ _ _ _ _ _} h => principalIH e (by simp only [sizeBranches]; omega) h
    have ihrest : ∀ bs : List (MatchPattern × Input), sizeBranches bs ≤ sizeBranches rest →
        InferBranchesWithTypesCoreSourceComplete bs := by
      intro bs hbs
      exact inferBranchesWithTypesCore_sourceComplete_of_body bs
        (fun e he => bodyIH e (by simp only [sizeBranches]; omega))
        (fun e he {_ _ _ _ _ _ _ _} h => principalIH e (by simp only [sizeBranches]; omega) h)
    cases pat with
    | wildcard => exact inferBranchesWithTypesCore_sourceComplete_wildcard ihbody pbody ihrest
    | named name count => exact inferBranchesWithTypesCore_sourceComplete_named ihbody pbody ihrest
termination_by sizeBranches branches
decreasing_by all_goals (subst_vars; simp only [sizeBranches] at *; omega)

theorem _root_.inferWithTypesCore_sourceComplete_match
    (ihs : ∀ e : Input, e.size ≤ scrut.size → InferWithTypesCoreSourceComplete e)
    (ps : ∀ e : Input, e.size ≤ scrut.size →
      ∀ {κ F' Φ c n s o t} (h : Infer κ F' Φ c e n s o t), Infer.SourcePrincipal h)
    (ihb : ∀ bs : List (MatchPattern × Input), sizeBranches bs ≤ sizeBranches branches →
      InferBranchesWithTypesCoreSourceComplete bs)
    {K : List Nat} {F : List Ty} {frontier : Nat} {ctx : Ctx} {ambient : Subst} {target : Ty} {P : List Nat}
    (hbackend : backendInput K F (.match_ scrut branches) = none)
    (hscope : SourceScope K F (.match_ scrut branches)) (hwf : CtxWF ctx) (hbelow : CtxBelow frontier ctx)
    (hK : ∀ k ∈ K, k < frontier) (hF : ∀ t ∈ F, Ty.BelowFvars frontier t)
    (hS : ∀ pair ∈ ambient, pair.2.IsLC)
    (hfix : ∀ k ∈ K, ambient.onTy (.fvar k) = .fvar k)
    (hP : ∀ p ∈ P, p < frontier) (hfixP : ∀ p ∈ P, ambient.onTy (.fvar p) = .fvar p)
    (ht : Typing P (ambient.onCtx ctx) ((Input.match_ scrut branches).substTyFvars ambient) target) :
    (inferWithTypesCore K frontier ctx (.match_ scrut branches) F).isSome := by
  obtain ⟨scrutD, hsD, hne, hbD⟩ := ht.match_inv
  have hscrutScope : SourceScope K F scrut := fun v hv => hscope v (List.mem_append_left _ hv)
  have hbranchScope : ∀ v ∈ rigidBranchVars branches, v ∈ K ++ softVars F :=
    fun v hv => hscope v (List.mem_append_right _ hv)
  have hbranchBelow : ∀ v ∈ rigidBranchVars branches, v < frontier := fun v hv =>
    (List.mem_append.mp (hbranchScope v hv)).elim (hK v) (softVars_lt hF v)
  obtain ⟨⟨⟨first, s1, scrutOut, scrutTy, scrutTypes, scrutSchemes⟩, hs⟩, hsResult⟩ :=
    Option.isSome_iff_exists.mp (ihs scrut (Nat.le_refl _) K F frontier ctx ambient scrutD P
      hscrutScope hwf hbelow hK hF hS hfix hP hfixP hsD)
  obtain ⟨R1, hR1, hscrut, hR1P, hag1⟩ := ps scrut (Nat.le_refl _) hs
    hwf hbelow hK hF ambient scrutD P hS hP hfixP (fun _ _ hk _ => hfix _ hk) hsD
  have hle := hs.frontier_le
  obtain ⟨hsB, hs1B⟩ := hs.belowFvars hbelow hK hF
  obtain ⟨hsLC, hs1LC⟩ := hs.lc hwf
  have hs1K := Subst.fixes_of_dom_avoids hs.dom_avoids
  have hR1K := residual_fixes_of_agrees hK hfix hs1K hag1
  have hctxWF := Subst.onCtx_wf hs1LC hwf
  have hctxB := Subst.onCtx_below hs1B hle hbelow
  obtain ⟨U, hU, hagU, hblock⟩ := Subst.override_block hR1 first [target]
    (by simpa using ht.regular)
  have hUtarget : U.onTy (.fvar first) = target := by simpa using hblock 0 (by simp)
  have hctxeq : U.onCtx (s1.onCtx ctx) = ambient.onCtx ctx := by
    trans R1.onCtx (s1.onCtx ctx)
    · exact (Subst.onCtx_congr hagU hctxB).symm
    · rw [← Subst.onCtx_append]
      exact (Subst.onCtx_congr hag1 hbelow).symm
  have hUK : ∀ k ∈ K, U.onTy (.fvar k) = .fvar k := fun k hk =>
    (hagU k (Nat.lt_of_lt_of_le (hK k hk) hle)).symm.trans (hR1K k hk)
  have hUP : ∀ p ∈ P, U.onTy (.fvar p) = .fvar p := fun p hp =>
    (hagU p (Nat.lt_of_lt_of_le (hP p hp) hle)).symm.trans (hR1P p hp)
  have hUst : scrutD = U.onTy scrutTy :=
    hscrut.trans (Subst.onTy_congr hagU hsB)
  have hagSU : Subst.AgreesBelow frontier ambient (s1 ++ U) := by
    intro v hv
    exact (hag1 v hv).trans (by
      rw [Subst.onTy_append, Subst.onTy_append]
      exact Subst.onTy_congr hagU (Subst.onTy_belowFvars hs1B (.fvar (Nat.lt_of_lt_of_le hv hle))))
  have hbr := branch_candidates_frame hbranchBelow hagSU hctxeq (by
    intro b hb
    exact hbD (b.1, b.2.substTyFvars ambient) (by
      rw [substInputBranches_eq_map]
      exact List.mem_map.mpr ⟨b, hb, rfl⟩))
  obtain ⟨⟨⟨next, s2, branchOut, branchTypes, branchSchemes⟩, hb⟩, hbResult⟩ :=
    Option.isSome_iff_exists.mp (ihb (substInputBranches s1 branches) (by
      simp only [sizeBranches_substInputBranches]; exact Nat.le_refl _) K (substSoft s1 F) (first + 1)
      (s1.onCtx ctx) scrutTy (.fvar first) 0 U P (branch_scope_subst hbranchScope hs1K) hctxWF
      (fun M hM => (hctxB M hM).mono (Nat.le_succ _))
      (fun k hk => Nat.lt_of_lt_of_le (hK k hk) (hle.trans (Nat.le_succ _)))
      (substSoft_below (fun p hp => (hs1B p hp).mono (Nat.le_succ _))
        (hle.trans (Nat.le_succ _)) hF)
      hU hUK (fun p hp => Nat.lt_of_lt_of_le (hP p hp) (hle.trans (Nat.le_succ _))) hUP hsLC .fvar
      (hsB.mono (Nat.le_succ _)) (.fvar (Nat.lt_succ_self _))
      (by simpa only [← hUst, hUtarget] using hbr))
  rw [inferWithTypesCore, dif_pos (rigid_all hK), dif_pos (ctx_all hbelow),
    dif_pos (soft_all hF), dif_pos (source_all hscope)]
  split
  · rename_i backend heq
    simp only [hbackend] at heq
    cases heq
  · cases branches with
    | nil => exact False.elim (hne rfl)
    | cons b bs => simp only [hsResult, List.head?_cons, hbResult, Option.isSome_some]

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
      Infer K [] frontier ctx input next subst output ty ∧
      (∀ pair ∈ residual, pair.2.IsLC) ∧ target = residual.onTy ty ∧
      (∀ k ∈ K, residual.onTy (.fvar k) = .fvar k) ∧
      Subst.AgreesBelow frontier ambient (subst ++ residual) := by
  obtain ⟨⟨⟨next, subst, output, ty⟩, hi⟩, _⟩ := Option.isSome_iff_exists.mp
    (inferCore_complete input K frontier ctx ambient target hwf hbelow hK hS hfix ht)
  obtain ⟨R, hR, hty, hRK, hag⟩ := hi.principal hwf hbelow hK (by simp) ambient target K hS hK hfix ht
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
    (fun v hv => Input.lt_freshFloor hv) (by simp) [] target input.rigidVars (by simp)
    (fun v hv => Input.lt_freshFloor hv) (by simp)
    (by simpa only [Subst.onCtx_empty] using ht)
  exact ⟨R, hR, hty, hfix⟩

#print axioms inferCore_complete
#print axioms Infer.complete
#print axioms inferCore_empty_accepts_iff

end Elaboration
