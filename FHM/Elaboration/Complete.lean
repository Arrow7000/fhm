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

 theorem inferRecComponentWithTypesCore_complete
    (hProducer : ∀ e : Input,e.size ≤ sizeBindings bindings → InferWithTypesCoreSourceComplete e)
    (hPrincipal : ∀ {κ F' Ψ c e Ψ' T output ty},e.size ≤ sizeBindings bindings →
      (hi : Infer κ F' Ψ c e Ψ' T output ty) → Infer.SourcePrincipal hi)
    (hlen : bindings.length = specs.length)
    (hctxWF : CtxWF ctx) (hctx : CtxBelow frontier ctx)
    (hK : ∀ k ∈ K,k < frontier) (hF : ∀ t ∈ F,Ty.BelowFvars frontier t)
    (hspecLC : ∀ spec ∈ specs,spec.LC) (hspecB : ∀ spec ∈ specs,spec.BelowFvars frontier)
    (hscope : ∀ rhs ∈ bindings,SourceScope K F rhs)
    (ambient : Subst) (P : List Nat) (hambient : ∀ p ∈ ambient,p.2.IsLC)
    (hfixK : ∀ k ∈ K,ambient.onTy (.fvar k) = .fvar k)
    (hP : ∀ p ∈ P,p < frontier) (hfixP : ∀ p ∈ P,ambient.onTy (.fvar p) = .fvar p)
    (hcandidate : ∀ (j : Nat) (rhs : Input) (target : Ty),index + j ∈ members →
      bindings[j]? = some rhs → specs[j]? = some (.mono target) →
      Typing P (ambient.onCtx ctx) (rhs.substTyFvars ambient) (ambient.onTy target)) :
    (inferRecComponentWithTypesCore K F members index frontier ctx bindings specs).isSome := by
  match bindings,specs with
  | [],[] => simp only [inferRecComponentWithTypesCore,Option.isSome_some]
  | [],_::_ => simp at hlen
  | _::_,[] => simp at hlen
  | rhs::rest,.poly scheme::specs =>
    have ht := inferRecComponentWithTypesCore_complete
        (bindings := rest) (specs := specs) (K := K) (F := F)
        (index := index+1) (frontier := frontier) (ctx := ctx)
      (fun e he => hProducer e (by simp only [sizeBindings];omega))
      (fun he hi => hPrincipal (by simp only [sizeBindings];omega) hi)
      (Nat.succ.inj hlen) hctxWF hctx hK hF
      (fun spec hm => hspecLC spec (List.mem_cons_of_mem _ hm))
      (fun spec hm => hspecB spec (List.mem_cons_of_mem _ hm))
      (fun rhs hm => hscope rhs (List.mem_cons_of_mem _ hm)) ambient P hambient hfixK hP hfixP
      (fun j rhs target hm hb ht => hcandidate (j+1) rhs target (by simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hm) hb ht)
    cases hr : inferRecComponentWithTypesCore K F members (index+1) frontier ctx rest specs with
    | none => simp only [hr,Option.isSome_none] at ht;contradiction
    | some result => simp only [inferRecComponentWithTypesCore,hr,Option.isSome_some]
  | rhs::rest,.mono expected::specs =>
    by_cases hm : index ∈ members
    · have hTyping := hcandidate 0 rhs expected (by simpa using hm) rfl rfl
      obtain ⟨⟨⟨first,s1,output,ty,types,schemes⟩,hi⟩,hresult⟩ := Option.isSome_iff_exists.mp
        (hProducer rhs (by simp only [sizeBindings];omega) K F frontier ctx ambient (ambient.onTy expected) P
          (hscope rhs List.mem_cons_self) hctxWF hctx hK hF hambient hfixK hP hfixP hTyping)
      obtain ⟨R1,hR1,hty,hR1P,hag1⟩ := hPrincipal (by simp only [sizeBindings];omega) hi
        hctxWF hctx hK hF ambient (ambient.onTy expected) P hambient hP hfixP
        (fun v _ hk _ => hfixK v hk) hTyping
      have hle := hi.frontier_le
      have hheadB : Ty.BelowFvars frontier expected := hspecB _ List.mem_cons_self
      have hExpected : ambient.onTy expected = R1.onTy (s1.onTy expected) := by
        simpa only [Subst.onTy_append] using Subst.onTy_congr hag1 hheadB
      have hUni : Unifies R1 ty (s1.onTy expected) := hty.symm.trans hExpected
      have hs1K := Subst.fixes_of_dom_avoids hi.dom_avoids
      have hR1K : ∀ k ∈ K,R1.onTy (.fvar k) = .fvar k := by
        intro k hk
        have hh := hag1 k (hK k hk)
        rw [Subst.onTy_append,hs1K k hk,hfixK k hk] at hh
        exact hh.symm
      obtain ⟨hiLC,hs1LC⟩ := hi.lc hctxWF
      have hSome := unifyCoreK_complete hiLC (Subst.onTy_lc hs1LC (hspecLC _ List.mem_cons_self)) hR1 hUni hR1K
      cases huni : unifyCoreK K ty (s1.onTy expected) with
      | none => simp only [huni,Option.isSome_none] at hSome;contradiction
      | some result =>
        obtain ⟨s2,hu,havoid⟩ := result
        obtain ⟨R2,hfac,hR2,hR2PK⟩ := hu.greatest_K R1 hR1 hUni
          (fun k hk => (List.mem_append.mp hk).elim (hR1P k) (hR1K k) : ∀ k ∈ P ++ K,R1.onTy (.fvar k) = .fvar k)
        have hR2P : ∀ p ∈ P,R2.onTy (.fvar p) = .fvar p := fun p hp => hR2PK p (List.mem_append_left _ hp)
        have hR2K : ∀ k ∈ K,R2.onTy (.fvar k) = .fvar k := fun k hk => hR2PK k (List.mem_append_right _ hk)
        have hag12 : Subst.AgreesBelow frontier ambient ((s1 ++ s2) ++ R2) := by
          intro v hv
          rw [hag1 v hv,Subst.onTy_append,hfac,Subst.onTy_append,Subst.onTy_append]
        have hs2LC := hu.lc hiLC (Subst.onTy_lc hs1LC (hspecLC _ List.mem_cons_self))
        have hbothLC : ∀ p ∈ s1 ++ s2,p.2.IsLC := fun p hp => (List.mem_append.mp hp).elim (hs1LC p) (hs2LC p)
        obtain ⟨hiB,hs1B⟩ := hi.belowFvars hctx hK hF
        have hs2B := hu.belowFvars hiB (Subst.onTy_belowFvars hs1B (hheadB.mono hle))
        have hbothB : ∀ p ∈ s1 ++ s2,Ty.BelowFvars first p.2 := fun p hp => (List.mem_append.mp hp).elim (hs1B p) (hs2B p)
        have hbothFix : ∀ k ∈ K,(s1 ++ s2).onTy (.fvar k) = .fvar k :=
          Subst.fixes_of_dom_avoids (fun p hp => (List.mem_append.mp hp).elim (hi.dom_avoids p) (havoid p))
        have hctxEq : R2.onCtx (s2.onCtx (s1.onCtx ctx)) = ambient.onCtx ctx := by
          simpa only [Subst.onCtx_append] using (Subst.onCtx_congr hag12 hctx).symm
        have hrawBelow : ∀ rhs ∈ rest,∀ v ∈ rhs.rigidVars,v < frontier := by
          intro rhs hh v hv
          exact (List.mem_append.mp (hscope rhs (List.mem_cons_of_mem _ hh) v hv)).elim (hK v) (softVars_lt hF v)
        have ht := inferRecComponentWithTypesCore_complete
          (bindings := rest.map (Input.substTyFvars (s1 ++ s2)))
          (specs := specs.map (RecSpec.onSubstSource (s1 ++ s2)))
          (K := K) (F := substSoft (s1 ++ s2) F) (index := index+1) (frontier := first)
          (ctx := s2.onCtx (s1.onCtx ctx))
          (fun e he => hProducer e (by simp only [sizeBindings_map_substTyFvars] at he;simp only [sizeBindings];omega))
          (fun he hi => hPrincipal (by simp only [sizeBindings_map_substTyFvars] at he;simp only [sizeBindings];omega) hi)
          (by simpa only [List.length_map] using Nat.succ.inj hlen)
          (Subst.onCtx_wf hs2LC (Subst.onCtx_wf hs1LC hctxWF))
          (by simpa only [Subst.onCtx_append] using Subst.onCtx_below hbothB hle hctx)
          (fun k hk => (hK k hk).trans_le hle) (substSoft_below hbothB hle hF)
          (by intro spec hs;obtain ⟨old,ho,rfl⟩ := List.mem_map.mp hs;exact RecSpec.lc_onSubstSource hbothLC (hspecLC old (List.mem_cons_of_mem _ ho)))
          (by
            intro spec hs
            obtain ⟨old,ho,rfl⟩ := List.mem_map.mp hs
            cases old with
            | mono t => exact Subst.onTy_belowFvars hbothB ((hspecB _ (List.mem_cons_of_mem _ ho)).mono hle)
            | poly M => exact Subst.onTy_belowFvars hbothB ((hspecB _ (List.mem_cons_of_mem _ ho)).mono hle))
          (by intro rhs hs;obtain ⟨old,ho,rfl⟩ := List.mem_map.mp hs;exact (hscope old (List.mem_cons_of_mem _ ho)).subst _ hbothFix)
          R2 P hR2 hR2K (fun p hp => (hP p hp).trans_le hle) hR2P
          (by
            intro j rhs target hj hb ht
            obtain ⟨old,ho,rfl⟩ := Option.map_eq_some_iff.mp (by simpa only [List.getElem?_map] using hb)
            obtain ⟨oldTarget,hot,rfl⟩ := RecSpec.mono_getElem?_map_onSubstSource ht
            have hsourceEq : (old.substTyFvars (s1 ++ s2)).substTyFvars R2 = old.substTyFvars ambient := by
              rw [←Input.substTyFvars_append]
              exact old.substTyFvars_congr (fun v hv => (hag12 v (hrawBelow old (List.mem_of_getElem? ho) v hv)).symm)
            have htargetEq : R2.onTy ((s1 ++ s2).onTy oldTarget) = ambient.onTy oldTarget := by
              simpa only [Subst.onTy_append] using (Subst.onTy_congr hag12 (hspecB _ (List.mem_cons_of_mem _ (List.mem_of_getElem? hot)))).symm
            rw [hctxEq,hsourceEq,htargetEq]
            exact hcandidate (j+1) old oldTarget (by simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hj) ho hot)
        cases htail : inferRecComponentWithTypesCore K (substSoft (s1 ++ s2) F) members (index+1) first
            (s2.onCtx (s1.onCtx ctx)) (rest.map (Input.substTyFvars (s1 ++ s2)))
            (specs.map (RecSpec.onSubstSource (s1 ++ s2))) with
        | none => simp only [htail,Option.isSome_none] at ht;contradiction
        | some tail => simp only [inferRecComponentWithTypesCore,dif_pos hm,hresult,huni,htail,Option.isSome_some]
    · have ht := inferRecComponentWithTypesCore_complete
        (bindings := rest) (specs := specs) (K := K) (F := F)
        (index := index+1) (frontier := frontier) (ctx := ctx)
        (fun e he => hProducer e (by simp only [sizeBindings];omega))
        (fun he hi => hPrincipal (by simp only [sizeBindings];omega) hi)
        (Nat.succ.inj hlen) hctxWF hctx hK hF
        (fun spec hm => hspecLC spec (List.mem_cons_of_mem _ hm))
        (fun spec hm => hspecB spec (List.mem_cons_of_mem _ hm))
        (fun rhs hm => hscope rhs (List.mem_cons_of_mem _ hm)) ambient P hambient hfixK hP hfixP
        (fun j rhs target hm hb ht => hcandidate (j+1) rhs target (by simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hm) hb ht)
      cases hr : inferRecComponentWithTypesCore K F members (index+1) frontier ctx rest specs with
      | none => simp only [hr,Option.isSome_none] at ht;contradiction
      | some result => simp only [inferRecComponentWithTypesCore,dif_neg hm,hr,Option.isSome_some]
 termination_by sizeBindings bindings
 decreasing_by all_goals simp only [sizeBindings,sizeBindings_map_substTyFvars];omega

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

theorem openRecAnn_complete_source {S0 : Subst} {names : List Nat} {target : Ty}
    (hS0 : ∀ p ∈ S0,p.2.IsLC) (hraw : ∀ v ∈ ann.rigidVars,v < frontier)
    (hfit : (ann.substTyFvars S0).RecFits names target)
    (hcount : names.length = ann.recPrefixCount) (htarget : target.IsLC) :
    (openRecAnn frontier ann).isSome := by
  cases ann with
  | absent | complete => simp only [openRecAnn,Option.isSome_some]
  | template template =>
    have hLC := hfit.allocate_lc_source htarget frontier
    have hb := (Ty.bvarsBelow_iff _).mpr hLC
    simp only [openRecAnn,hb,dite_true,Option.isSome_some]
  | partialForall count template =>
    have hlen : names.length = count := hcount
    obtain ⟨U0,hU0,hag0,hblock⟩ := Subst.override_block hS0 frontier (names.map Ty.fvar)
      (by intro t ht;obtain ⟨_,_,rfl⟩ := List.mem_map.mp ht;exact .fvar)
    have himages : (freshVars frontier count).map (fun v => U0.onTy (.fvar v)) = names.map Ty.fvar := by
      apply List.ext_getElem
      · simp only [List.length_map,freshVars_length];exact hlen.symm
      · intro i hi hj
        have hin : i < names.length := by simpa only [List.length_map] using hj
        have hh := hblock i (by simpa only [List.length_map] using hin)
        simpa only [List.getElem_map,freshVars,List.getElem_range] using hh
    have hnewFit : ((template.openTyVarsFrom 0 (freshVars frontier count)).substTyFvars U0).Fits target := by
      rw [Template.substTyFvars_openTyVarsFrom_of_images _ hU0 himages 0]
      have heqSource : template.substTyFvars U0 = template.substTyFvars S0 :=
        template.substTyFvars_congr (fun v hv => (hag0 v (hraw v hv)).symm)
      rw [heqSource]
      exact hfit.2
    have hLC := hnewFit.allocate_lc_source htarget (frontier+count)
    have hb := (Ty.bvarsBelow_iff _).mpr hLC
    simp only [openRecAnn,hb,dite_true,Option.isSome_some]

theorem openRecAnns_complete_source {S0 : Subst}
    (hS0 : ∀ p ∈ S0,p.2.IsLC) (hraw : ∀ ann ∈ anns,∀ v ∈ ann.rigidVars,v < frontier)
    (targetNames : List (List Nat)) (targetTypes : List Ty)
    (hNames : targetNames.length = anns.length) (hTypes : targetTypes.length = anns.length)
    (hfit : ∀ (j : Nat) (ann : LetAnn) (names : List Nat) (target : Ty),index+j ∈ members →
      anns[j]? = some ann → targetNames[j]? = some names → targetTypes[j]? = some target →
      (ann.substTyFvars S0).RecFits names target ∧ names.length = ann.recPrefixCount ∧ target.IsLC) :
    (openRecAnns members index frontier anns).isSome := by
  induction anns generalizing frontier index targetNames targetTypes with
  | nil => simp only [openRecAnns,Option.isSome_some]
  | cons ann rest ih =>
    cases targetNames with
    | nil => simp at hNames
    | cons names targetNames =>
      cases targetTypes with
      | nil => simp at hTypes
      | cons target targetTypes =>
        by_cases hm : index ∈ members
        · obtain ⟨hf,hcount,hLC⟩ := hfit 0 ann names target (by simpa using hm) rfl rfl rfl
          obtain ⟨⟨⟨middle,opening⟩,hOpen⟩,hresult⟩ := Option.isSome_iff_exists.mp
            (openRecAnn_complete_source hS0 (hraw ann List.mem_cons_self) hf hcount hLC)
          have htail := ih
            (frontier := middle) (index := index+1)
            (fun ann ha v hv => (hraw ann (List.mem_cons_of_mem _ ha) v hv).trans_le hOpen.frontier_le)
            targetNames targetTypes (Nat.succ.inj hNames) (Nat.succ.inj hTypes)
            (fun j ann names target hm ha hn ht => hfit (j+1) ann names target
              (by simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hm) ha hn ht)
          cases hr : openRecAnns members (index+1) middle rest with
          | none => simp only [hr,Option.isSome_none] at htail;contradiction
          | some result => simp only [openRecAnns,dif_pos hm,hresult,hr,Option.isSome_some]
        · have htail := ih
            (frontier := frontier) (index := index+1)
            (fun ann ha => hraw ann (List.mem_cons_of_mem _ ha))
            targetNames targetTypes (Nat.succ.inj hNames) (Nat.succ.inj hTypes)
            (fun j ann names target hm ha hn ht => hfit (j+1) ann names target
              (by simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hm) ha hn ht)
          cases hr : openRecAnns members (index+1) frontier rest with
          | none => simp only [hr,Option.isSome_none] at htail;contradiction
          | some result => simp only [openRecAnns,dif_neg hm,hr,Option.isSome_some]

theorem resolveRecSlots_complete_of_factor {R : Subst} {slots : List (List Ty)}
    (candidateNames : List (List Nat)) (hlen : candidateNames.length = slots.length)
    (hfactor : ∀ (j : Nat) (images : List Ty) (names : List Nat),index+j ∈ members →
      slots[j]? = some images → candidateNames[j]? = some names →
      images.map R.onTy = names.map Ty.fvar ∧ names.Nodup ∧
      ∀ name ∈ names,∀ v ∈ forbidden,name ∉ (R.onTy (.fvar v)).freeVars) :
    (resolveRecSlots members forbidden index slots).isSome := by
  induction slots generalizing index candidateNames with
  | nil => dsimp only [resolveRecSlots];simp only [Option.isSome_some]
  | cons images rest ih =>
    -- Use the compiled matchers directly: Lean 4.26 cannot generate the
    -- overlapping dependent-match equation theorem for resolveRecSlots.
    have hstep : resolveRecSlots members forbidden index (images :: rest) =
        (if hm : index ∈ members then
          resolveRecSlots.match_1 members forbidden index images rest
            (fun _ _ => Option {names // ResolveRecSlots members forbidden index (images::rest) names})
            (resolveRecWritten images forbidden) (resolveRecSlots members forbidden (index+1) rest)
            (fun written hbare hnd hav names hn => some ⟨written::names,.cons hm hbare hnd hav hn⟩)
            (fun _ _ => none)
        else
          resolveRecSlots.match_4 members forbidden index rest
            (fun _ => Option {names // ResolveRecSlots members forbidden index (images::rest) names})
            (resolveRecSlots members forbidden (index+1) rest)
            (fun names hn => some ⟨[]::names,.skip hm hn⟩) (fun _ => none)) := rfl
    cases candidateNames with
    | nil => simp at hlen
    | cons names candidateNames =>
      have htail := ih (index := index+1) candidateNames (Nat.succ.inj hlen)
        (fun j images names hm hi hn => hfactor (j+1) images names
          (by simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hm) hi hn)
      cases ht : resolveRecSlots members forbidden (index+1) rest with
      | none => simp only [ht,Option.isSome_none] at htail;contradiction
      | some tail =>
        by_cases hm : index ∈ members
        · obtain ⟨hf,hnd,havoid⟩ := hfactor 0 images names (by simpa using hm) rfl rfl
          have hhead := resolveRecWritten_complete_of_factor hf hnd havoid
          cases hh : resolveRecWritten images forbidden with
          | none => simp only [hh,Option.isSome_none] at hhead;contradiction
          | some head =>
            obtain ⟨written,hbare,hnd,hav⟩ := head
            obtain ⟨tailNames,htailProof⟩ := tail
            rw [hstep,dif_pos hm,hh,ht]
            rfl
        · rw [hstep,dif_neg hm,ht]
          rfl

theorem finishRecComponent_complete_of_factor {state : RecState} {R : Subst}
    (candidateNames : List (List Nat)) (hlen : candidateNames.length = state.slots.length)
    (hfactor : ∀ (i : Nat) (images : List Ty) (names : List Nat),i ∈ members →
      state.slots[i]? = some images → candidateNames[i]? = some names →
      images.map R.onTy = names.map Ty.fvar ∧ names.Nodup ∧
      ∀ name ∈ names,∀ v ∈ (state.fixedCtx ctx).env.freeVars ++ K ++ soft,
        name ∉ (R.onTy (.fvar v)).freeVars) :
    (finishRecComponent K soft members ctx state outputs facts).isSome := by
  have hslots := resolveRecSlots_complete_of_factor (index := 0) candidateNames hlen
    (by simpa only [Nat.zero_add] using hfactor)
  cases hr : resolveRecSlots members ((state.fixedCtx ctx).env.freeVars ++ K ++ soft) 0 state.slots with
  | none => simp only [hr,Option.isSome_none] at hslots;contradiction
  | some result => simp only [finishRecComponent,hr,Option.isSome_some]

theorem inferRecSignedWithTypesCore_complete_one
    {K P : List Nat} {F : List Ty} {frontier index : Nat} {outer : Ctx}
    {state : RecState} {ambient : Subst} {scheme : PolyTy} {rhs : Input}
    (hProducer : ∀ e : Input,e.size ≤ rhs.size → InferWithTypesCoreSourceComplete e)
    (hPrincipal : ∀ {κ F' Ψ c e Ψ' T output ty},e.size ≤ rhs.size →
      (hi : Infer κ F' Ψ c e Ψ' T output ty) → Infer.SourcePrincipal hi)
    (hctxWF : CtxWF (state.rhsCtx outer)) (hbelow : CtxBelow frontier (state.rhsCtx outer))
    (hK : ∀ k ∈ K,k < frontier) (hF : ∀ t ∈ F,Ty.BelowFvars frontier t)
    (hS : ∀ pair ∈ ambient,pair.2.IsLC)
    (hfix : ∀ k ∈ K,ambient.onTy (.fvar k) = .fvar k)
    (hP : ∀ p ∈ P,p < frontier) (hfixP : ∀ p ∈ P,ambient.onTy (.fvar p) = .fvar p)
    (hscope : SourceScope K F (.letIn (.complete scheme) rhs (.primLit .unit)))
    (ht : Typing P (ambient.onCtx (state.rhsCtx outer))
      ((Input.letIn (.complete scheme) rhs (.primLit .unit)).substTyFvars ambient) (.prim .unit)) :
    (inferRecSignedWithTypesCore K F index frontier outer [.complete scheme] [rhs] state).isSome := by
  let ctx := state.rhsCtx outer
  let ann := LetAnn.complete scheme
  let body := Input.primLit .unit
  have hmode : ann.isSignature = true := rfl
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
  change extras.length = M.paramCount - ann.paramCount at hElen
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
    Option.isSome_iff_exists.mp (hProducer (rhs.openTyVars written) (by simp)
      (K ++ written) F (frontier + ann.paramCount) ctx moved (M.openVars (written ++ extras))
      (Q ++ written) hRhsOpen hctxWF hCtxOpen hKOpen hFOpen hMoved hMovedK hQOpen hMovedFix hAligned')
  obtain ⟨R, hR, hRty, hRfix, hagR⟩ := (hPrincipal (by simp) hr) hctxWF hCtxOpen hKOpen hFOpen moved
    (M.openVars (written ++ extras)) (Q ++ written) hMoved hQOpen hMovedFix
    (fun v _ hk _ => hMovedK v hk) hAligned'
  have hrle := hr.frontier_le
  obtain ⟨hrB, hs1B⟩ := hr.belowFvars hCtxOpen hKOpen hFOpen
  obtain ⟨hrLC, hs1LC⟩ := hr.lc hctxWF
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
  obtain ⟨hSchemeWF,hExpectedEq⟩ := hComplete (s1.onPolyTy scheme) rfl
  have hExpectedLC := PolyTy.openVars_isLC (Xs := written) hSchemeWF (by simp only [written,ann,LetAnn.paramCount,freshVars_length,Subst.onPolyTy];omega)
  have hOpenEq : R.onTy ((s1.onPolyTy scheme).openVars written) =
      (R.onPolyTy (s1.onPolyTy scheme)).openVars written :=
    Subst.onTy_openVars_of_fixes hR (fun y hy => hFixRK y (List.mem_append_right _ hy))
  have hUnify := unifyCoreK_complete hrLC hExpectedLC hR
    (hRty.symm.trans (hExpectedEq.trans hOpenEq.symm)) hFixRK
  obtain ⟨⟨s2,hu,hdom⟩,hUnifyResult⟩ := Option.isSome_iff_exists.mp hUnify
  have hAnnScope' : ∀ v ∈ (s1.onPolyTy scheme).body.freeVars,v ∈ K ++ softVars (substSoft s1 F) := hAnnScope
  have hc : SignatureCheck K (substSoft s1 F) written first rhsTy (ann.substTyFvars s1) first s2 :=
    .complete hSchemeWF hAnnScope' ⟨hu,hdom⟩
  obtain ⟨V,hV,hVQ,hagPrefix,hbodyV,hbodyWF,hbodyB,hprefixB,hescape⟩ :=
    Infer.source_signature_frame hscope hr hc (hPrincipal (by simp) hr) rfl hctxWF hbelow hK hF
      hMoved hQ hMovedFix hMovedFreeze hM hann hrhs hfits htypes hbodyD hYsM hYsCtx hYsImages hYsSoft
  have hSchemeWF0 : scheme.WF := ContainsBvarsUpTo.of_substFvars hSchemeWF
  have hraw : rhs.rigidVars.all (fun v => decide (v ∈ K ++ softVars F)) = true :=
    List.all_eq_true.mpr (fun v hv => decide_eq_true (hRhsRaw v hv))
  have hescape' : ∀ y ∈ freshVars frontier scheme.paramCount,
      y ∉ ((state.onSubst (s1 ++ s2)).rhsCtx ((s1 ++ s2).onCtx outer)).env.freeVars ++
        softVars (substSoft (s1 ++ s2) F) := by
    rw [RecState.rhsCtx_onSubst]
    simpa only [ctx,written,ann,LetAnn.paramCount,Subst.onCtx_append] using hescape
  simp only [inferRecSignedWithTypesCore,PolyTy.wf_iff_bvarsBelow.mpr hSchemeWF0,dite_true,hraw]
  simp only [ctx,written,ann,LetAnn.paramCount] at hrResult hUnifyResult
  simp only [hrResult,hUnifyResult,dif_pos hescape',List.map_nil,inferRecSignedWithTypesCore,Option.isSome_some]



theorem inferRecSignedWithTypesCore_complete
    (hProducer : ∀ e : Input, e.size ≤ sizeBindings bindings → InferWithTypesCoreSourceComplete e)
    (hPrincipal : ∀ {κ F' Ψ c e Ψ' T output ty}, e.size ≤ sizeBindings bindings →
      (hi : Infer κ F' Ψ c e Ψ' T output ty) → Infer.SourcePrincipal hi)
    {P declPool Xs done : List Nat} {declCtx : Ctx} {declSpecs : List RecSpec}
    {declPrefixes : List (List Nat)} {R : Subst}
    (hres : RecResidual P declCtx declSpecs declPrefixes declPool Xs ctx state done R)
    (hctxWF : CtxWF ctx) (hctx : CtxBelow frontier ctx)
    (hstateLC : state.LC) (hstateB : state.Below frontier)
    (hK : ∀ k ∈ K, k < frontier) (hF : ∀ t ∈ F, Ty.BelowFvars frontier t)
    (hP : ∀ p ∈ P, p < frontier)
    (hfixK : ∀ k ∈ K, R.onTy (.fvar k) = .fvar k)
    (halign : anns.length = bindings.length)
    (hlen : state.exports.length = state.specs.length)
    (hpoly : ∀ (i : Nat) (scheme : PolyTy), state.specs[i]? = some (.poly scheme) →
      state.exports[i]? = some (some scheme))
    (hdone : ∀ i ty, state.specs[i]? = some (.mono ty) → i ∈ done)
    (hannScope : ∀ ann ∈ anns, ∀ v ∈ ann.rigidVars, v ∈ K ++ softVars F)
    (hrhsScope : ∀ rhs ∈ bindings, SourceScope K F rhs)
    (hcandAnn : ∀ ann ∈ anns, ∀ v ∈ (ann.substTyFvars R).rigidVars, v ∈ P)
    (hcandRhs : ∀ rhs ∈ bindings, ∀ v ∈ (rhs.substTyFvars R).rigidVars, v ∈ P)
    (hcandidate : ∀ (j : Nat) (scheme : PolyTy) (rhs : Input),
      anns[j]? = some (.complete scheme) → bindings[j]? = some rhs →
      ∃ L, ∀ Ys, FreshNames L scheme.paramCount Ys →
        Typing (P ++ Ys) (recBodyCtx declCtx declSpecs declPrefixes declPool)
          ((rhs.substTyFvars R).openTyVars Ys) ((R.onPolyTy scheme).openVars Ys)) :
    (inferRecSignedWithTypesCore K F index frontier ctx anns bindings state).isSome := by
  match anns, bindings with
  | [], [] => simp only [inferRecSignedWithTypesCore,Option.isSome_some]
  | [], _::_ => simp at halign
  | _::_, [] => simp at halign
  | ann :: anns,rhs :: rest =>
    cases ann with
    | complete scheme =>
      have hiCtxWF := hstateLC.rhsCtx hctxWF
      have hiCtxB := hstateB.rhsCtx hctx
      have hheadAnn := hannScope _ List.mem_cons_self
      have hraw : SourceScope K F rhs := hrhsScope _ List.mem_cons_self
      obtain ⟨L,htypes⟩ := hcandidate 0 scheme rhs rfl rfl
      have htypes' : ∀ Ys, FreshNames L scheme.paramCount Ys →
          Typing (P ++ Ys) (R.onCtx (state.rhsCtx ctx)) ((rhs.substTyFvars R).openTyVars Ys)
            ((R.onPolyTy scheme).openVars Ys) :=
        fun Ys hy => hres.weaken_from_body hlen hpoly hdone (htypes Ys hy)
      obtain ⟨Ns,hNlen,hNnd,hNavoid⟩ := exists_fresh_names L scheme.paramCount
      have hOpenLC := (htypes' Ns ⟨hNlen,hNnd,hNavoid⟩).regular
      have hSchemeRWF : (R.onPolyTy scheme).WF := by
        have hb := Ty.containsBvars_of_openVarsFrom 0 Ns hOpenLC
        simpa only [Nat.zero_add,hNlen,Subst.onPolyTy] using hb
      have hSchemeWF : scheme.WF := ContainsBvarsUpTo.of_substFvars hSchemeRWF
      have hUnit : Typing P (R.onCtx (state.rhsCtx ctx))
          ((Input.letIn (.complete scheme) rhs (.primLit .unit)).substTyFvars R) (.prim .unit) := by
        refine Typing.letSignature (M := R.onPolyTy scheme) (L := L) hSchemeRWF
          (hcandAnn _ List.mem_cons_self) (hcandRhs _ List.mem_cons_self)
          (fun _ _ => .complete) ?_ (.primLit .primLitUnit)
        intro Ys hy
        have htake : Ys.take scheme.paramCount = Ys := List.take_of_length_le (by have := hy.length;simpa only [Subst.onPolyTy] using this.le)
        simpa only [LetAnn.substTyFvars,LetAnn.paramCount,Subst.onPolyTy,htake] using htypes' Ys hy
      have hscope : SourceScope K F (.letIn (.complete scheme) rhs (.primLit .unit)) := by
        intro v hv
        simp only [Input.rigidVars,LetAnn.rigidVars,List.mem_append,List.not_mem_nil,or_false] at hv
        exact hv.elim (hheadAnn v) (hraw v)
      have hOne := inferRecSignedWithTypesCore_complete_one (index := index)
        (fun e he => hProducer e (by simp only [sizeBindings];omega))
        (fun he hi => hPrincipal (by simp only [sizeBindings];omega) hi)
        hiCtxWF hiCtxB hK hF hres.lc hfixK hP hres.fixes hscope hUnit
      have hrawBool : rhs.rigidVars.all (fun v => decide (v ∈ K ++ softVars F)) = true :=
        List.all_eq_true.mpr (fun v hv => decide_eq_true (hraw v hv))
      cases hiResult : inferWithTypesCore (K ++ freshVars frontier scheme.paramCount)
          (frontier + scheme.paramCount) (state.rhsCtx ctx) (rhs.openTyVars (freshVars frontier scheme.paramCount)) F with
      | none => simp only [inferRecSignedWithTypesCore,PolyTy.wf_iff_bvarsBelow.mpr hSchemeWF,
          hrawBool,dite_true,hiResult,Option.isSome_none] at hOne;contradiction
      | some result =>
        obtain ⟨⟨first,s1,output,ty,types,schemes⟩,hi⟩ := result
        cases huResult : unifyCoreK (K ++ freshVars frontier scheme.paramCount) ty
            ((s1.onPolyTy scheme).openVars (freshVars frontier scheme.paramCount)) with
        | none => simp only [inferRecSignedWithTypesCore,PolyTy.wf_iff_bvarsBelow.mpr hSchemeWF,
            hrawBool,dite_true,hiResult,huResult,Option.isSome_none] at hOne;contradiction
        | some result =>
          obtain ⟨s2,hu,hdom⟩ := result
          let checked := (state.onSubst (s1 ++ s2)).setSigned index (freshVars frontier scheme.paramCount)
            (output.substTyFvars s2) ((RecFacts.mk types schemes).onSubst s2)
          by_cases hescape : ∀ y ∈ freshVars frontier scheme.paramCount,
              y ∉ ((state.onSubst (s1 ++ s2)).rhsCtx ((s1 ++ s2).onCtx ctx)).env.freeVars ++
                softVars (substSoft (s1 ++ s2) F)
          · have hstep : InferRecSigned K F index frontier ctx [.complete scheme] [rhs] state first
                (s1 ++ s2) checked := by
              simpa only [List.append_nil] using
                (InferRecSigned.cons (anns := []) (bindings := []) (index := index)
                  (bodyFacts := RecFacts.mk types schemes) hSchemeWF hraw hi ⟨hu,hdom⟩ hescape InferRecSigned.nil)
            obtain ⟨U,hU,hUP,hag,hresChecked⟩ := hstep.sourcePrincipal_residual
              (fun he hi => hPrincipal (by simp only [sizeBindings] at he ⊢;omega) hi)
              hres hctxWF hctx hstateLC hstateB hK hF hP hlen hpoly hdone
              (fun ann ha => by rcases List.mem_singleton.mp ha with rfl;exact hheadAnn)
              (fun rhs' ha => by rcases List.mem_singleton.mp ha with rfl;exact hraw)
              (fun _ _ v _ hk _ => hfixK v hk) (fun _ _ v _ hk _ => hfixK v hk)
              (fun ann ha => by rcases List.mem_singleton.mp ha with rfl;exact hcandAnn _ List.mem_cons_self)
              (fun rhs' ha => by rcases List.mem_singleton.mp ha with rfl;exact hcandRhs _ List.mem_cons_self)
              (by
                intro j sigma rhs' ha hb
                cases j with
                | zero => cases ha;cases hb;exact ⟨L,htypes⟩
                | succ j => simp only [List.getElem?_cons_succ,List.getElem?_nil] at ha;cases ha)
            have hle := hstep.frontier_le
            obtain ⟨hbothLC,hcheckedLC⟩ := hstep.lc_of_infer (fun _ hi hc => hi.lc hc) hctxWF hstateLC
            obtain ⟨hbothB,hcheckedB⟩ := hstep.belowFvars_of_infer
              (fun _ hi hc hk hf => hi.belowFvars hc hk hf) hctx hK hF hstateB
              (by intro ann ha v hv;rcases List.mem_singleton.mp ha with rfl
                  exact (List.mem_append.mp (hheadAnn v hv)).elim (hK v) (softVars_lt hF v))
            have hbothFix : ∀ k ∈ K,(s1 ++ s2).onTy (.fvar k) = .fvar k :=
              Subst.fixes_of_dom_avoids hstep.dom_avoids
            have hUfixK : ∀ k ∈ K,U.onTy (.fvar k) = .fvar k := by
              intro k hk
              have he := hag k (hK k hk)
              rw [Subst.onTy_append,hbothFix k hk,hfixK k hk] at he
              exact he.symm
            have hannBelow : ∀ ann ∈ (.complete scheme :: anns),∀ v ∈ ann.rigidVars,v < frontier :=
              fun ann ha v hv => (List.mem_append.mp (hannScope ann ha v hv)).elim (hK v) (softVars_lt hF v)
            have hrhsBelow : ∀ term ∈ (rhs :: rest),∀ v ∈ term.rigidVars,v < frontier :=
              fun term hm v hv => (List.mem_append.mp (hrhsScope term hm v hv)).elim (hK v) (softVars_lt hF v)
            have annEq : ∀ ann ∈ (.complete scheme :: anns),
                (ann.substTyFvars (s1 ++ s2)).substTyFvars U = ann.substTyFvars R := by
              intro ann hm
              rw [← LetAnn.substTyFvars_append]
              exact ann.substTyFvars_congr (fun v hv => (hag v (hannBelow ann hm v hv)).symm)
            have rhsEq : ∀ term ∈ (rhs :: rest),
                (term.substTyFvars (s1 ++ s2)).substTyFvars U = term.substTyFvars R := by
              intro term hm
              rw [← Input.substTyFvars_append]
              exact term.substTyFvars_congr (fun v hv => (hag v (hrhsBelow term hm v hv)).symm)
            have hpolyChecked : ∀ (i : Nat) (sigma : PolyTy),checked.specs[i]? = some (.poly sigma) → checked.exports[i]? = some (some sigma) := by
              intro i sigma hs
              change (state.specs.map (RecSpec.onSubstSource (s1 ++ s2)))[i]? = some (.poly sigma) at hs
              rw [List.getElem?_map] at hs
              obtain ⟨spec,hold,heq⟩ := Option.map_eq_some_iff.mp hs
              cases spec with
              | mono ty => cases heq
              | poly old =>
                change RecSpec.poly ((s1 ++ s2).onPolyTy old) = RecSpec.poly sigma at heq
                cases heq
                simp only [checked,RecState.setSigned,RecState.onSubst,List.getElem?_map,
                  hpoly i old hold,Option.map_some]
            have htail := inferRecSignedWithTypesCore_complete (index := index+1)
              (anns := anns.map (LetAnn.substTyFvars (s1 ++ s2)))
              (bindings := rest.map (Input.substTyFvars (s1 ++ s2)))
              (fun e he => hProducer e (by simp only [sizeBindings_map_substTyFvars] at he;simp only [sizeBindings];omega))
              (fun he hi => hPrincipal (by simp only [sizeBindings_map_substTyFvars] at he;simp only [sizeBindings];omega) hi)
              hresChecked (Subst.onCtx_wf hbothLC hctxWF) (Subst.onCtx_below hbothB hle hctx)
              hcheckedLC hcheckedB (fun k hk => (hK k hk).trans_le hle) (substSoft_below hbothB hle hF)
              (fun p hp => (hP p hp).trans_le hle) hUfixK
              (by simpa only [List.length_map] using Nat.succ.inj halign)
              (by simpa only [checked,RecState.setSigned,RecState.onSubst,List.length_map] using hlen)
              hpolyChecked
              (by intro i tau hs;obtain ⟨old,hold,_⟩ := RecSpec.mono_getElem?_map_onSubstSource hs;exact hdone i old hold)
              (by intro ann hm v hv
                  obtain ⟨old,ho,rfl⟩ := List.mem_map.mp hm
                  obtain ⟨original,horiginal,himage⟩ := LetAnn.rigidVars_substTyFvars hv
                  exact scope_image hbothFix (hannScope old (List.mem_cons_of_mem _ ho) original horiginal) himage)
              (by intro rhs hm
                  obtain ⟨old,ho,rfl⟩ := List.mem_map.mp hm
                  exact (hrhsScope old (List.mem_cons_of_mem _ ho)).subst _ hbothFix)
              (by intro ann hm v hv
                  obtain ⟨old,ho,rfl⟩ := List.mem_map.mp hm
                  rw [annEq old (List.mem_cons_of_mem _ ho)] at hv
                  exact hcandAnn old (List.mem_cons_of_mem _ ho) v hv)
              (by intro rhs hm v hv
                  obtain ⟨old,ho,rfl⟩ := List.mem_map.mp hm
                  rw [rhsEq old (List.mem_cons_of_mem _ ho)] at hv
                  exact hcandRhs old (List.mem_cons_of_mem _ ho) v hv)
              (by
                intro j sigma rhs' ha hb
                rw [List.getElem?_map] at ha hb
                obtain ⟨ann,ho,heq⟩ := Option.map_eq_some_iff.mp ha
                obtain ⟨oldRhs,hro,rfl⟩ := Option.map_eq_some_iff.mp hb
                cases ann with
                | absent | template _ | partialForall _ _ => cases heq
                | complete old =>
                  cases heq
                  obtain ⟨L,htypes⟩ := hcandidate (j+1) old oldRhs
                    (by simpa only [List.getElem?_cons_succ] using ho)
                    (by simpa only [List.getElem?_cons_succ] using hro)
                  refine ⟨L,?_⟩
                  intro Ys hy
                  have hσ : U.onPolyTy ((s1 ++ s2).onPolyTy old) = R.onPolyTy old := by
                    apply congrArg (PolyTy.mk old.paramCount)
                    change U.onTy ((s1 ++ s2).onTy old.body) = R.onTy old.body
                    simpa only [Subst.onTy_append] using (Subst.onTy_congr hag
                      (Ty.BelowFvars.of_freeVars_lt (hannBelow _ (List.mem_cons_of_mem _ (List.mem_of_getElem? ho))))).symm
                  rw [rhsEq oldRhs (List.mem_cons_of_mem _ (List.mem_of_getElem? hro))]
                  change Typing (P ++ Ys) (recBodyCtx declCtx declSpecs declPrefixes declPool)
                    ((oldRhs.substTyFvars R).openTyVars Ys)
                    ((U.onPolyTy ((s1 ++ s2).onPolyTy old)).openVars Ys)
                  rw [hσ]
                  exact htypes Ys hy)
            cases htResult : inferRecSignedWithTypesCore K (substSoft (s1 ++ s2) F) (index+1) first
                ((s1 ++ s2).onCtx ctx) (anns.map (LetAnn.substTyFvars (s1 ++ s2)))
                (rest.map (Input.substTyFvars (s1 ++ s2))) checked with
            | none => simp only [htResult,Option.isSome_none] at htail;contradiction
            | some result =>
              dsimp only [checked] at htResult
              simp only [inferRecSignedWithTypesCore,PolyTy.wf_iff_bvarsBelow.mpr hSchemeWF,hrawBool,
                dite_true,hiResult,huResult,dif_pos hescape,htResult,Option.isSome_some]
          · simp only [inferRecSignedWithTypesCore,PolyTy.wf_iff_bvarsBelow.mpr hSchemeWF,
              hrawBool,dite_true,hiResult,huResult,dif_neg hescape,Option.isSome_none] at hOne;contradiction
    | absent | template _ | partialForall _ _ =>
      have htail := inferRecSignedWithTypesCore_complete (index := index+1)
        (fun e he => hProducer e (by simp only [sizeBindings];omega))
        (fun he hi => hPrincipal (by simp only [sizeBindings];omega) hi)
        hres hctxWF hctx hstateLC hstateB hK hF hP hfixK (Nat.succ.inj halign) hlen hpoly hdone
        (fun ann hm => hannScope ann (List.mem_cons_of_mem _ hm))
        (fun rhs hm => hrhsScope rhs (List.mem_cons_of_mem _ hm))
        (fun ann hm => hcandAnn ann (List.mem_cons_of_mem _ hm))
        (fun rhs hm => hcandRhs rhs (List.mem_cons_of_mem _ hm))
        (fun j sigma rhs ha hb => hcandidate (j+1) sigma rhs ha hb)
      cases htResult : inferRecSignedWithTypesCore K F (index+1) frontier ctx anns rest state with
      | none => simp only [htResult,Option.isSome_none] at htail;contradiction
      | some result =>
        simp only [inferRecSignedWithTypesCore,htResult,Option.isSome_some]
termination_by sizeBindings bindings
decreasing_by all_goals (simp only [sizeBindings,sizeBindings_map_substTyFvars];omega)

theorem inferRecStrataWithTypesCore_cons_of_singleton
    (one : {r : RecRunResult // InferRecStrata K F frontier ctx anns bindings state [component]
      r.frontier r.subst r.state})
    (hOne : inferRecStrataWithTypesCore K F frontier ctx anns bindings state [component] = some one)
    (tail : {r : RecRunResult // InferRecStrata K (substSoft one.val.subst F) one.val.frontier
      (one.val.subst.onCtx ctx) (anns.map (LetAnn.substTyFvars one.val.subst))
      (bindings.map (Input.substTyFvars one.val.subst)) one.val.state rest r.frontier r.subst r.state})
    (hTail : inferRecStrataWithTypesCore K (substSoft one.val.subst F) one.val.frontier
      (one.val.subst.onCtx ctx) (anns.map (LetAnn.substTyFvars one.val.subst))
      (bindings.map (Input.substTyFvars one.val.subst)) one.val.state rest = some tail) :
    ∃ result : {r : RecRunResult // InferRecStrata K F frontier ctx anns bindings state (component::rest)
      r.frontier r.subst r.state},
      inferRecStrataWithTypesCore K F frontier ctx anns bindings state (component::rest) = some result ∧
      result.val.frontier = tail.val.frontier ∧ result.val.subst = one.val.subst ++ tail.val.subst ∧
      result.val.state = tail.val.state := by
  cases ho : openRecAnns component 0 frontier anns with
  | none => simp only [inferRecStrataWithTypesCore,ho] at hOne;cases hOne
  | some opening =>
    obtain ⟨⟨opened,openings⟩,hOpen⟩ := opening
    cases hp : checkRecShapes K ((state.installOpenings component openings).shapes component openings) with
    | none => simp only [inferRecStrataWithTypesCore,ho,hp] at hOne;cases hOne
    | some shapes =>
      obtain ⟨pre,hShapes⟩ := shapes
      cases hc : inferRecComponentWithTypesCore K
          (substSoft pre (F ++ (openings.flatMap RecOpening.written).map Ty.fvar)) component 0 opened
          (((state.installOpenings component openings).onSubst pre).rhsCtx (pre.onCtx ctx))
          ((openRecSources openings bindings).map (Input.substTyFvars pre))
          ((state.installOpenings component openings).onSubst pre).specs with
      | none => simp only [inferRecStrataWithTypesCore,ho,hp,hc] at hOne;cases hOne
      | some current =>
        obtain ⟨current,hCurrent⟩ := current
        cases hf : finishRecComponent K (softVars (substSoft (pre ++ current.subst) F)) component
            ((pre ++ current.subst).onCtx ctx)
            ((state.installOpenings component openings).onSubst (pre ++ current.subst))
            current.outputs current.facts with
        | none => simp only [inferRecStrataWithTypesCore,ho,hp,hc,hf] at hOne;cases hOne
        | some exported =>
          obtain ⟨exported,hExported⟩ := exported
          simp only [inferRecStrataWithTypesCore,ho,hp,hc,hf,List.append_nil,Option.some.injEq] at hOne
          subst one
          simp only [inferRecStrataWithTypesCore,ho,hp,hc,hf,hTail]
          exact ⟨_,rfl,rfl,rfl,rfl⟩



private theorem inferRecStrataWithTypesCore_complete_of_step
    {P G Xs : List Nat} {declCtx : Ctx} {declAnns : List LetAnn}
    {declBindings : List Input} {declSpecs : List RecSpec}
    {declPrefixes : List (List Nat)} {base : Nat}
    {K : List Nat} {F : List Ty} {frontier : Nat} {ctx : Ctx}
    {anns : List LetAnn} {bindings : List Input} {state : RecState}
    {past groups : List (List Nat)} {R : Subst}
    (hStep : ∀ {K : List Nat} {F : List Ty} {frontier : Nat}
      {ctx : Ctx} {anns : List LetAnn} {bindings : List Input}
      {state : RecState} {past rest : List (List Nat)} {component : List Nat} {R : Subst},
      (∀ e : Input,e.size ≤ sizeBindings bindings → InferWithTypesCoreSourceComplete e) →
      (∀ {κ F' Ψ c e Ψ' T output ty},e.size ≤ sizeBindings bindings →
        (hi : Infer κ F' Ψ c e Ψ' T output ty) → Infer.SourcePrincipal hi) →
      RecGroups.ValidResidualGroups (anns.map LetAnn.recModeAnn) (bindings.map Input.erase)
        (past ++ component :: rest) →
      past ++ component :: rest = RecGroup.inferenceSccs
        (anns.map LetAnn.recModeAnn) (bindings.map Input.erase) →
      state.Frame base K F ctx anns past.flatten →
      state.LC → state.Below frontier → CtxWF ctx → CtxBelow frontier ctx →
      base + bindings.length ≤ frontier →
      (∀ k ∈ K,k < frontier) → (∀ t ∈ F,Ty.BelowFvars frontier t) →
      (∀ p ∈ P,p < frontier) →
      RecResidual P declCtx declSpecs declPrefixes G Xs ctx state past.flatten R →
      (∀ k ∈ K,R.onTy (.fvar k) = .fvar k) →
      (∀ x ∈ Xs,∀ k ∈ K,x ∉ (R.onTy (.fvar k)).freeVars) →
      (∀ x ∈ Xs,x ∉ softVars (substSoft R F)) →
      (∀ ann ∈ anns,∀ v ∈ ann.rigidVars,v ∈ K ++ softVars F) →
      (∀ rhs ∈ bindings,SourceScope K F rhs) →
      anns.map (LetAnn.substTyFvars R) = declAnns →
      bindings.map (Input.substTyFvars R) = declBindings →
      ∃ one : {r : RecRunResult // InferRecStrata K F frontier ctx anns bindings state [component]
        r.frontier r.subst r.state},
        inferRecStrataWithTypesCore K F frontier ctx anns bindings state [component] = some one ∧
        ∃ U : Subst,(∀ pair ∈ U,pair.2.IsLC) ∧
          (∀ p ∈ P,U.onTy (.fvar p) = .fvar p) ∧
          Subst.AgreesBelow frontier R (one.val.subst ++ U) ∧
          RecResidual P declCtx declSpecs declPrefixes G Xs (one.val.subst.onCtx ctx)
            one.val.state (past.flatten ++ component) U)
    (hProducer : ∀ e : Input,e.size ≤ sizeBindings bindings → InferWithTypesCoreSourceComplete e)
    (hInfer : ∀ {κ F' Ψ c e Ψ' T output ty},e.size ≤ sizeBindings bindings →
      (hi : Infer κ F' Ψ c e Ψ' T output ty) → Infer.SourcePrincipal hi)
    (hvalid : RecGroups.ValidResidualGroups (anns.map LetAnn.recModeAnn) (bindings.map Input.erase) (past ++ groups))
    (hcanonical : past ++ groups = RecGroup.inferenceSccs (anns.map LetAnn.recModeAnn) (bindings.map Input.erase))
    (hframe : state.Frame base K F ctx anns past.flatten)
    (hstateLC : state.LC) (hstateB : state.Below frontier)
    (hctxWF : CtxWF ctx) (hctx : CtxBelow frontier ctx)
    (hbase : base + bindings.length ≤ frontier)
    (hK : ∀ k ∈ K,k < frontier) (hF : ∀ t ∈ F,Ty.BelowFvars frontier t)
    (hP : ∀ p ∈ P,p < frontier)
    (hres : RecResidual P declCtx declSpecs declPrefixes G Xs ctx state past.flatten R)
    (hfixK : ∀ k ∈ K,R.onTy (.fvar k) = .fvar k)
    (hXsK : ∀ x ∈ Xs,∀ k ∈ K,x ∉ (R.onTy (.fvar k)).freeVars)
    (hXsF : ∀ x ∈ Xs,x ∉ softVars (substSoft R F))
    (hannScope : ∀ ann ∈ anns,∀ v ∈ ann.rigidVars,v ∈ K ++ softVars F)
    (hrhsScope : ∀ rhs ∈ bindings,SourceScope K F rhs)
    (hannEq : anns.map (LetAnn.substTyFvars R) = declAnns)
    (hrhsEq : bindings.map (Input.substTyFvars R) = declBindings) :
    ∃ result : {r : RecRunResult // InferRecStrata K F frontier ctx anns bindings state groups
      r.frontier r.subst r.state},
      inferRecStrataWithTypesCore K F frontier ctx anns bindings state groups = some result ∧
      ∃ V : Subst,(∀ pair ∈ V,pair.2.IsLC) ∧
        (∀ p ∈ P,V.onTy (.fvar p) = .fvar p) ∧
        (∀ k ∈ K,V.onTy (.fvar k) = .fvar k) ∧
        Subst.AgreesBelow frontier R (result.val.subst ++ V) ∧
        RecResidual P declCtx declSpecs declPrefixes G Xs (result.val.subst.onCtx ctx)
          result.val.state (past ++ groups).flatten V ∧
        (anns.map (LetAnn.substTyFvars result.val.subst)).map (LetAnn.substTyFvars V) = declAnns ∧
        (bindings.map (Input.substTyFvars result.val.subst)).map (Input.substTyFvars V) = declBindings ∧
        (∀ x ∈ Xs,∀ k ∈ K,x ∉ (V.onTy (.fvar k)).freeVars) ∧
        (∀ x ∈ Xs,x ∉ softVars (substSoft V (substSoft result.val.subst F))) := by
  match groups with
  | [] =>
    have hannNil : anns.map (LetAnn.substTyFvars []) = anns := by
      calc
        _ = anns.map id := List.map_congr_left (fun ann _ => ann.substTyFvars_eq_self_of_fixes (fun _ _ => rfl))
        _ = anns := List.map_id anns
    have hrhsNil : bindings.map (Input.substTyFvars []) = bindings := by
      calc
        _ = bindings.map id := List.map_congr_left (fun rhs _ => rhs.substTyFvars_eq_self_of_fixes (fun _ _ => rfl))
        _ = bindings := List.map_id bindings
    refine ⟨⟨⟨frontier,[],state⟩,.nil⟩,(by simp only [inferRecStrataWithTypesCore]),R,hres.lc,hres.fixes,hfixK,(fun _ _ => rfl),?_,?_,?_,hXsK,?_⟩
    · simpa only [Subst.onCtx_nil,List.append_nil] using hres
    · simpa only [hannNil] using hannEq
    · simpa only [hrhsNil] using hrhsEq
    · simpa only [substSoft_nil] using hXsF
  | component :: rest =>
    obtain ⟨⟨⟨first,solved,exported⟩,hOne⟩,hOneEq,U,hU,hUP,hag,hresStep⟩ :=
      hStep hProducer hInfer hvalid hcanonical hframe hstateLC hstateB hctxWF hctx hbase
        hK hF hP hres hfixK hXsK hXsF hannScope hrhsScope hannEq hrhsEq
    cases hOne with
    | cons ho hp hc hf hr =>
      cases hr
      expose_names
      have hneutral : List.append (pre ++ current) [] = pre ++ current := List.append_nil _
      simp only [hneutral] at hOneEq hag hresStep
      obtain ⟨hstepFrame,_,_⟩ := recStep_frame ho hp hc hf
        (fun _ hi => hi.sourceLocality) hvalid hframe hstateLC hctxWF hstateB hbase hannScope hrhsScope
      have hstep : InferRecStrata K F frontier ctx anns bindings state [component]
          first (pre ++ current ++ []) exported := .cons ho hp hc hf .nil
      have hstep' : InferRecStrata K F frontier ctx anns bindings state [component]
          first (pre ++ current) exported := by simpa only [List.append_nil] using hstep
      have hle := hstep'.frontier_le
      have hannBelow : ∀ ann ∈ anns,∀ v ∈ ann.rigidVars,v < frontier :=
        fun ann ha v hv => (List.mem_append.mp (hannScope ann ha v hv)).elim (hK v) (softVars_lt hF v)
      have hrhsBelow : ∀ rhs ∈ bindings,∀ v ∈ rhs.rigidVars,v < frontier :=
        fun rhs hm v hv => (List.mem_append.mp (hrhsScope rhs hm v hv)).elim (hK v) (softVars_lt hF v)
      obtain ⟨hbothLC,hstepLC⟩ := hstep'.lc_of_infer (fun _ hi => hi.lc) hctxWF hstateLC
      obtain ⟨hbothB,hstepB⟩ := hstep'.belowFvars_of_infer (fun _ hi => hi.belowFvars)
        hctx hK hF hstateB hannBelow
      have hbothFix : ∀ k ∈ K,(pre ++ current).onTy (.fvar k) = .fvar k :=
        Subst.fixes_of_dom_avoids hstep'.dom_avoids
      have hannEqStep : (anns.map (LetAnn.substTyFvars (pre ++ current))).map
          (LetAnn.substTyFvars U) = declAnns := by
        calc
          _ = anns.map (LetAnn.substTyFvars R) := by
            simp only [List.map_map,Function.comp_def]
            apply List.map_congr_left
            intro ann ha
            rw [← LetAnn.substTyFvars_append]
            exact ann.substTyFvars_congr (fun v hv => (hag v (hannBelow ann ha v hv)).symm)
          _ = declAnns := hannEq
      have hrhsEqStep : (bindings.map (Input.substTyFvars (pre ++ current))).map
          (Input.substTyFvars U) = declBindings := by
        calc
          _ = bindings.map (Input.substTyFvars R) := by
            simp only [List.map_map,Function.comp_def]
            apply List.map_congr_left
            intro rhs hm
            rw [← Input.substTyFvars_append]
            exact rhs.substTyFvars_congr (fun v hv => (hag v (hrhsBelow rhs hm v hv)).symm)
          _ = declBindings := hrhsEq
      have hUonK : ∀ k ∈ K,U.onTy (.fvar k) = R.onTy (.fvar k) := by
        intro k hk
        have he := hag k (hK k hk)
        rw [Subst.onTy_append,hbothFix k hk] at he
        exact he.symm
      have hUfixK : ∀ k ∈ K,U.onTy (.fvar k) = .fvar k := fun k hk => (hUonK k hk).trans (hfixK k hk)
      have hUF : substSoft U (substSoft (pre ++ current) F) = substSoft R F := by
        simp only [substSoft,List.map_map,Function.comp_def]
        apply List.map_congr_left
        intro ty ht
        simpa only [Subst.onTy_append] using (Subst.onTy_congr hag (hF ty ht)).symm
      have htailValid := recValid_subst (S := pre ++ current)
        (by simpa only [List.append_assoc,List.singleton_append] using hvalid :
          RecGroups.ValidResidualGroups (anns.map LetAnn.recModeAnn) (bindings.map Input.erase)
            ((past ++ [component]) ++ rest))
      have htailCanonical : (past ++ [component]) ++ rest = RecGroup.inferenceSccs
          ((anns.map (LetAnn.substTyFvars (pre ++ current))).map LetAnn.recModeAnn)
          ((bindings.map (Input.substTyFvars (pre ++ current))).map Input.erase) := by
        rw [← Input.inferenceSccs_substTyFvars anns bindings (pre ++ current)]
        simpa only [List.append_assoc,List.singleton_append] using hcanonical
      have htailFrame : exported.Frame base K (substSoft (pre ++ current) F) ((pre ++ current).onCtx ctx)
          (anns.map (LetAnn.substTyFvars (pre ++ current))) (past ++ [component]).flatten := by
        simpa only [List.flatten_append,List.flatten_cons,List.flatten_nil,List.append_nil] using hstepFrame
      have htailRes : RecResidual P declCtx declSpecs declPrefixes G Xs ((pre ++ current).onCtx ctx)
          exported (past ++ [component]).flatten U := by
        simpa only [List.flatten_append,List.flatten_cons,List.flatten_nil,List.append_nil] using hresStep
      obtain ⟨tail,hTailEq,V,hV,hVP,hVK,hagTail,hresFinal,hAnnFinal,hRhsFinal,hXKFinal,hXFFinal⟩ :=
        inferRecStrataWithTypesCore_complete_of_step hStep
          (fun e he => hProducer e (by simpa only [sizeBindings_map_substTyFvars] using he))
          (fun he hi => hInfer (by simpa only [sizeBindings_map_substTyFvars] using he) hi)
          htailValid htailCanonical htailFrame hstepLC hstepB
          (Subst.onCtx_wf hbothLC hctxWF) (Subst.onCtx_below hbothB hle hctx)
          (by simp only [List.length_map];omega)
          (fun k hk => (hK k hk).trans_le hle) (substSoft_below hbothB hle hF)
          (fun p hp => (hP p hp).trans_le hle) htailRes hUfixK
          (by intro x hx k hk;rw [hUonK k hk];exact hXsK x hx k hk)
          (by intro x hx;rw [hUF];exact hXsF x hx)
          (by intro ann ha v hv
              obtain ⟨old,ho,rfl⟩ := List.mem_map.mp ha
              obtain ⟨original,horiginal,himage⟩ := LetAnn.rigidVars_substTyFvars hv
              exact scope_image hbothFix (hannScope old ho original horiginal) himage)
          (by intro rhs hm
              obtain ⟨old,ho,rfl⟩ := List.mem_map.mp hm
              exact (hrhsScope old ho).subst _ hbothFix)
          hannEqStep hrhsEqStep
      obtain ⟨result,hResult,hFront,hSubst,hFinal⟩ := inferRecStrataWithTypesCore_cons_of_singleton
        ⟨⟨first,pre ++ current,exported⟩,hstep'⟩ hOneEq tail hTailEq
      refine ⟨result,hResult,V,hV,hVP,hVK,?_,?_,?_,?_,hXKFinal,?_⟩
      · rw [hSubst]
        exact Subst.AgreesBelow.trans_append hle hag hbothB hagTail
      · rw [hSubst,hFinal,Subst.onCtx_append]
        simpa only [List.append_assoc,List.singleton_append] using hresFinal
      · rw [hSubst]
        simpa only [List.map_map,Function.comp_def,← LetAnn.substTyFvars_append,List.append_assoc] using hAnnFinal
      · rw [hSubst]
        simpa only [List.map_map,Function.comp_def,← Input.substTyFvars_append,List.append_assoc] using hRhsFinal
      · rw [hSubst]
        simpa only [substSoft_append,List.append_assoc] using hXFFinal
termination_by groups.length

theorem _root_.InferRecComponent.outputs_selected
    (h : InferRecComponent K F members index frontier ctx bindings specs next S outputs facts) :
    ∀ (j : Nat) (ty : Ty),index+j ∈ members → specs[j]? = some (.mono ty) →
      ∃ output,outputs[j]? = some (some output) := by
  match h with
  | .nil => intro j ty _ hs;cases hs
  | .skipMono hn hr =>
    intro j ty hm hs
    cases j with
    | zero => exact (hn (by simpa only [Nat.add_zero] using hm)).elim
    | succ j =>
      exact hr.outputs_selected j ty (by simpa [Nat.add_assoc,Nat.add_comm 1 j] using hm) hs
  | .skipPoly hr =>
    intro j ty hm hs
    cases j with
    | zero => cases hs
    | succ j => exact hr.outputs_selected j ty (by simpa [Nat.add_assoc,Nat.add_comm 1 j] using hm) hs
  | .consSelected hm hi hu hr =>
    expose_names
    intro j target hj hs
    cases j with
    | zero => exact ⟨_,rfl⟩
    | succ j =>
      simp only [List.getElem?_cons_succ] at hs
      apply hr.outputs_selected j ((s1 ++ s2).onTy target) (by simpa [Nat.add_assoc,Nat.add_comm 1 j] using hj)
      simp only [List.getElem?_map,hs,Option.map_some,RecSpec.onSubstSource]
termination_by structural h

theorem RecState.output_onSubst {state : RecState} {S : Subst} {i : Nat} {output : Expr}
    (h : state.outputs[i]? = some (some output)) :
    ∃ out,(state.onSubst S).outputs[i]? = some (some out) := by
  exact ⟨output.substTyFvars S,by simp only [RecState.onSubst,List.getElem?_map,h,Option.map_some]⟩

theorem FinishRecComponent.outputs_present
    (h : FinishRecComponent K soft members ctx state outputs facts final)
    (hlen : state.outputs.length = state.specs.length)
    (hSelected : ∀ i ∈ members,∃ ty,state.specs[i]? = some (.mono ty) ∧
      ∃ output,outputs[i]? = some (some output)) :
    (∀ (i : Nat) (output : Expr),state.outputs[i]? = some (some output) → ∃ out,final.outputs[i]? = some (some out)) ∧
    (∀ i ∈ members,∃ out,final.outputs[i]? = some (some out)) := by
  cases h with
  | @mk written hresolve =>
    have hFill : ∀ i ∈ members,∃ out,
        (state.exportComponent members written (state.componentPool K soft members ctx written) outputs facts).outputs[i]? = some (some out) := by
      intro i hi
      obtain ⟨ty,ht,out,ho⟩ := hSelected i hi
      have hib : i < state.outputs.length := by rw [hlen];exact (List.getElem?_eq_some_iff.mp ht).1
      refine ⟨out.closeTyVars (recNames (written[i]?.getD []) (state.componentPool K soft members ctx written) ty),?_⟩
      simp only [RecState.exportComponent,List.getElem?_mapIdx,List.getElem?_eq_getElem hib,
        Option.map_some,if_pos hi,ht,bind,pure,Option.bind_some,RecSpec.monoTy?,ho,Option.join_some]
    refine ⟨?_,hFill⟩
    intro i out ho
    by_cases hi : i ∈ members
    · exact hFill i hi
    · exact ⟨out,by simp only [RecState.exportComponent,List.getElem?_mapIdx,ho,Option.map_some,if_neg hi]⟩

theorem _root_.InferRecStrata.outputs_present
    (h : InferRecStrata K F frontier ctx anns bindings state groups next S final)
    (hlen : state.outputs.length = state.specs.length)
    (hSelected : ∀ i ∈ groups.flatten,∃ ty,state.specs[i]? = some (.mono ty)) :
    (∀ (i : Nat) (output : Expr),state.outputs[i]? = some (some output) → ∃ out,final.outputs[i]? = some (some out)) ∧
    (∀ i ∈ groups.flatten,∃ out,final.outputs[i]? = some (some out)) := by
  match h with
  | .nil => exact ⟨fun _ output ho => ⟨output,ho⟩,by simp⟩
  | .cons ho hp hc hf hr =>
    expose_names
    have hCurrent : ∀ i ∈ component,∃ ty,
        ((state.installOpenings component openings).onSubst (pre ++ current)).specs[i]? = some (.mono ty) ∧
        ∃ output,outputs[i]? = some (some output) := by
      intro i hi
      obtain ⟨ty,ht⟩ := hSelected i (by simp only [List.flatten_cons,List.mem_append];exact .inl hi)
      refine ⟨(pre ++ current).onTy ty,?_,?_⟩
      · simp only [RecState.onSubst,RecState.installOpenings,List.getElem?_map,ht,Option.map_some,RecSpec.onSubstSource]
      · apply hc.outputs_selected i (pre.onTy ty) (by simpa only [Nat.zero_add] using hi)
        simp only [RecState.onSubst,RecState.installOpenings,List.getElem?_map,ht,Option.map_some,RecSpec.onSubstSource]
    have hLenCurrent : ((state.installOpenings component openings).onSubst (pre ++ current)).outputs.length =
        ((state.installOpenings component openings).onSubst (pre ++ current)).specs.length := by
      simpa only [RecState.onSubst,RecState.installOpenings,List.length_map] using hlen
    obtain ⟨hKeep,hFill⟩ := hf.outputs_present hLenCurrent hCurrent
    have hLenExported : exported.outputs.length = exported.specs.length := by
      cases hf
      simpa only [RecState.exportComponent,List.length_mapIdx] using hLenCurrent
    have hSelectedRest : ∀ i ∈ rest.flatten,∃ ty,exported.specs[i]? = some (.mono ty) := by
      intro i hi
      obtain ⟨ty,ht⟩ := hSelected i (by simp only [List.flatten_cons,List.mem_append];exact .inr hi)
      refine ⟨(pre ++ current).onTy ty,?_⟩
      cases hf
      simp only [RecState.exportComponent,RecState.onSubst,RecState.installOpenings,List.getElem?_map,
        ht,Option.map_some,RecSpec.onSubstSource]
    obtain ⟨hTailKeep,hTailFill⟩ := hr.outputs_present hLenExported hSelectedRest
    constructor
    · intro i output hout
      obtain ⟨moved,hmoved⟩ := RecState.output_onSubst (S := pre ++ current) hout
      obtain ⟨out,ho⟩ := hKeep i moved (by simpa only [RecState.installOpenings,RecState.onSubst] using hmoved)
      exact hTailKeep i out ho
    · intro i hi
      rcases (by simpa only [List.flatten_cons,List.mem_append] using hi : i ∈ component ∨ i ∈ rest.flatten) with hm | hm
      · obtain ⟨out,ho⟩ := hFill i hm
        exact hTailKeep i out ho
      · exact hTailFill i hm

termination_by structural h



theorem RecState.output_setSigned {state : RecState} {member i : Nat} {written : List Nat}
    {output old : Expr} {facts : RecFacts} (ho : state.outputs[i]? = some (some old)) :
    ∃ out,(state.setSigned member written output facts).outputs[i]? = some (some out) := by
  by_cases hi : i = member
  · subst i
    have hb := (List.getElem?_eq_some_iff.mp ho).1
    exact ⟨output.closeTyVars written,by simp only [RecState.setSigned,List.getElem?_set_self hb]⟩
  · exact ⟨old,by simp only [RecState.setSigned,List.getElem?_set_ne (Ne.symm hi),ho]⟩

theorem _root_.InferRecSigned.outputs_present
    (h : InferRecSigned K F index frontier ctx anns bindings state next S final)
    (hbound : index + anns.length ≤ state.outputs.length) :
    (∀ (i : Nat) (output : Expr),state.outputs[i]? = some (some output) → ∃ out,final.outputs[i]? = some (some out)) ∧
    (∀ (j : Nat) (scheme : PolyTy),anns[j]? = some (.complete scheme) →
      ∃ out,final.outputs[index+j]? = some (some out)) := by
  match h with
  | .nil => exact ⟨fun _ output ho => ⟨output,ho⟩,by intro j scheme ha;cases ha⟩
  | .skip hmode hr =>
    expose_names
    have hb : index + 1 + anns_1.length ≤ state.outputs.length := by simp only [List.length_cons] at hbound;omega
    obtain ⟨hKeep,hFill⟩ := hr.outputs_present hb
    refine ⟨hKeep,?_⟩
    intro j scheme ha
    cases j with
    | zero => cases ha;cases hmode
    | succ j => simpa only [Nat.add_assoc,Nat.add_comm 1 j] using hFill j scheme ha
  | .cons hwf hraw hi hu hescape hr =>
    expose_names
    let checked := (state.onSubst (s1 ++ s2)).setSigned index (freshVars frontier scheme.paramCount)
      (output.substTyFvars s2) (bodyFacts.onSubst s2)
    have hb : index + 1 + (anns_1.map (LetAnn.substTyFvars (s1 ++ s2))).length ≤ checked.outputs.length := by
      simpa only [checked,RecState.setSigned,RecState.onSubst,List.length_set,List.length_map,List.length_cons,
        Nat.add_assoc,Nat.add_comm 1 anns_1.length] using hbound
    obtain ⟨hKeep,hFill⟩ := hr.outputs_present hb
    constructor
    · intro i old ho
      obtain ⟨moved,hmoved⟩ := RecState.output_onSubst (S := s1 ++ s2) ho
      obtain ⟨ready,hready⟩ := RecState.output_setSigned (member := index) (written := freshVars frontier scheme.paramCount)
        (output := output.substTyFvars s2) (facts := bodyFacts.onSubst s2) hmoved
      exact hKeep i ready hready
    · intro j sigma ha
      cases j with
      | zero =>
        cases ha
        have hib : index < (state.onSubst (s1 ++ s2)).outputs.length := by
          simp only [RecState.onSubst,List.length_map,List.length_cons] at hbound ⊢
          omega
        have hout : checked.outputs[index]? = some (some ((output.substTyFvars s2).closeTyVars
            (freshVars frontier scheme.paramCount))) := by
          simp only [checked,RecState.setSigned,List.getElem?_set_self hib]
        simpa only [Nat.add_zero] using hKeep index _ hout
      | succ j =>
        have hnew : (anns_1.map (LetAnn.substTyFvars (s1 ++ s2)))[j]? = some (.complete ((s1 ++ s2).onPolyTy sigma)) := by
          simp only [List.getElem?_map,show anns_1[j]? = some (.complete sigma) from ha,Option.map_some,LetAnn.substTyFvars,Subst.onPolyTy,Subst.onTy]
        simpa only [Nat.add_assoc,Nat.add_comm 1 j] using hFill j ((s1 ++ s2).onPolyTy sigma) hnew
termination_by structural h

theorem collectRecValues_complete {values : List (Option α)}
    (h : ∀ (i : Nat),i < values.length → ∃ value,values[i]? = some (some value)) :
    (collectRecValues values).isSome := by
  induction values with
  | nil => rfl
  | cons value rest ih =>
    obtain ⟨v,hv⟩ := h 0 (by simp)
    simp only [List.getElem?_cons_zero,Option.some.injEq] at hv
    subst value
    have ht := ih (fun i hi => h (i+1) (by simp only [List.length_cons];omega))
    cases hr : collectRecValues rest with
    | none => simp only [hr,Option.isSome_none] at ht;contradiction
    | some result => simp only [collectRecValues,hr,Option.isSome_some]

theorem RecState.Frame.exports_present
    {state : RecState} (h : state.Frame base K F ctx anns done)
    (hDone : ∀ i ty,state.specs[i]? = some (.mono ty) → i ∈ done) :
    ∀ (i : Nat),i < state.exports.length → ∃ scheme,state.exports[i]? = some (some scheme) := by
  intro i hi
  have hs : i < state.specs.length := by rw [h.specs_length,←h.exports_length];exact hi
  have hSpec := List.getElem?_eq_getElem hs
  cases heq : state.specs[i] with
  | mono ty =>
    have hm : state.specs[i]? = some (.mono ty) := by simpa only [heq] using hSpec
    obtain ⟨written,_,_,_,_,he⟩ := if_pos (hDone i ty hm) ▸ h.mono i ty hm
    exact ⟨_,he⟩
  | poly scheme =>
    exact ⟨scheme,h.poly i scheme (by simpa only [heq] using hSpec)⟩



theorem _root_.InferRecSigned.collectors_of_strata
    (hs : InferRecStrata K F frontier ctx anns bindings state groups first S1 state1)
    (hp : InferRecSigned K (substSoft S1 F) 0 first (S1.onCtx ctx)
      (anns.map (LetAnn.substTyFvars S1)) (bindings.map (Input.substTyFvars S1)) state1 second S2 state2)
    (hvalid : RecGroups.ValidResidualGroups (anns.map LetAnn.recModeAnn) (bindings.map Input.erase) groups)
    (hframe : state.Frame base K F ctx anns [])
    (hframe1 : state1.Frame base K (substSoft S1 F) (S1.onCtx ctx)
      (anns.map (LetAnn.substTyFvars S1)) groups.flatten)
    (hframe2 : state2.Frame base K (substSoft S2 (substSoft S1 F)) (S2.onCtx (S1.onCtx ctx))
      ((anns.map (LetAnn.substTyFvars S1)).map (LetAnn.substTyFvars S2)) groups.flatten) :
    (collectRecValues state2.exports).isSome ∧ (collectRecValues state2.outputs).isSome := by
  have hSelected : ∀ i ∈ groups.flatten,∃ ty,state.specs[i]? = some (.mono ty) := by
    intro i hi
    exact hframe.mono_at_unsigned ((hvalid.covers_unsigned i (hvalid.bounded i hi)).mp hi)
  obtain ⟨_,hUnsigned⟩ := hs.outputs_present
    (hframe.outputs_length.trans hframe.specs_length.symm) hSelected
  have hb : 0 + (anns.map (LetAnn.substTyFvars S1)).length ≤ state1.outputs.length := by
    rw [hframe1.outputs_length]
    omega
  obtain ⟨hKeep,hComplete⟩ := hp.outputs_present hb
  have hv2 := recValid_subst (recValid_subst hvalid S1) S2
  have hDone := hframe2.all_mono_done hv2
  refine ⟨collectRecValues_complete (hframe2.exports_present hDone),collectRecValues_complete ?_⟩
  intro i hi
  have hiAnn : i < anns.length := by
    simpa only [hframe2.outputs_length,List.length_map] using hi
  have hAnn := List.getElem?_eq_getElem hiAnn
  cases heq : anns[i] with
  | complete scheme =>
    have ha : (anns.map (LetAnn.substTyFvars S1))[i]? = some (.complete (S1.onPolyTy scheme)) := by
      simp only [List.getElem?_map,hAnn,heq,Option.map_some,LetAnn.substTyFvars,Subst.onPolyTy,Subst.onTy]
    simpa only [Nat.zero_add] using hComplete i (S1.onPolyTy scheme) ha
  | absent | template _ | partialForall _ _ =>
    have hu : RecGroups.UnsignedAt (anns.map LetAnn.recModeAnn) i := by
      simp only [RecGroups.UnsignedAt,List.getElem?_map,hAnn,heq,Option.map_some,LetAnn.recModeAnn]
    have hiBinding : i < (bindings.map Input.erase).length := by
      have hl := hvalid.length
      simp only [List.length_map] at hl ⊢
      omega
    obtain ⟨out,ho⟩ := hUnsigned i ((hvalid.covers_unsigned i hiBinding).mpr hu)
    exact hKeep i out ho


set_option maxHeartbeats 3000000 in
theorem inferRecStrataWithTypesCore_aligned_singleton
    {K P G Xs done members : List Nat} {F : List Ty} {frontier opened : Nat}
    {ctx declCtx : Ctx} {state : RecState} {anns : List LetAnn} {bindings : List Input}
    {openings : List RecOpening} {U : Subst} {declSpecs : List RecSpec} {declPrefixes : List (List Nat)}
    (ho : OpenRecAnns members 0 frontier anns opened openings)
    (hOpenRun : openRecAnns members 0 frontier anns = some ⟨(opened,openings),ho⟩)
    (hProducer : ∀ e : Input, e.size ≤ sizeBindings bindings → InferWithTypesCoreSourceComplete e)
    (hPrincipal : ∀ {κ F' Ψ c e Ψ' T output ty}, e.size ≤ sizeBindings bindings →
      (hi : Infer κ F' Ψ c e Ψ' T output ty) → Infer.SourcePrincipal hi)
    (hres : RecResidual P declCtx declSpecs declPrefixes G Xs ctx state done U)
    (hstateLC : state.LC) (hstateB : state.Below frontier)
    (hctxWF : CtxWF ctx) (hctx : CtxBelow frontier ctx)
    (hK : ∀ k ∈ K, k < frontier) (hF : ∀ t ∈ F, Ty.BelowFvars frontier t)
    (hP : ∀ p ∈ P, p < opened) (hUK : ∀ k ∈ K, U.onTy (.fvar k) = .fvar k)
    (hlen : anns.length = bindings.length) (hspecLen : state.specs.length = bindings.length)
    (hslotLen : state.slots.length = anns.length) (hexports : state.exports.length = state.specs.length)
    (hselected : ∀ i ∈ members, ∃ ty, state.specs[i]? = some (.mono ty))
    (hanns : ∀ ann ∈ anns, ∀ v ∈ ann.rigidVars, v ∈ K ++ softVars F)
    (hrhs : ∀ rhs ∈ bindings, SourceScope K F rhs)
    (hsolve : ∀ (i : Nat) (opening : RecOpening) (ty expected : Ty), i ∈ members →
      openings[i]? = some opening → state.specs[i]? = some (.mono ty) →
      opening.expected = some expected → U.onTy expected = U.onTy ty)
    (himages : ∀ (i : Nat) (opening : RecOpening), i ∈ members → openings[i]? = some opening →
      opening.written.map (fun v => U.onTy (.fvar v)) =
        (recRenameNames G Xs (declPrefixes[i]?.getD [])).map Ty.fvar)
    (hcandidate : ∀ (i : Nat) (rhs : Input) (ty : Ty), i ∈ members →
      (openRecSources openings bindings)[i]? = some rhs → state.specs[i]? = some (.mono ty) →
      Typing P (U.onCtx (state.rhsCtx ctx)) (rhs.substTyFvars U) (U.onTy ty))
    (hdisjoint : ∀ i ∈ members, i ∉ done)
    (hdeclLC : ∀ ty, .mono ty ∈ declSpecs → ty.IsLC) (hG : G.Nodup)
    (hprefix : ∀ (i : Nat) (ty : Ty), declSpecs[i]? = some (.mono ty) →
      (declPrefixes[i]?.getD []).Nodup ∧ ∀ v ∈ declPrefixes[i]?.getD [], v ∈ G)
    (hXsLen : Xs.length = G.length) (hXsND : Xs.Nodup) (hGXs : ∀ g ∈ G, g ∉ Xs)
    (hXsTypes : ∀ x ∈ Xs, ∀ ty, .mono ty ∈ declSpecs → x ∉ ty.freeVars)
    (hXsCtx : ∀ x ∈ Xs, x ∉ (U.onCtx (state.fixedCtx ctx)).env.freeVars)
    (hXsK : ∀ x ∈ Xs, ∀ k ∈ K, x ∉ (U.onTy (.fvar k)).freeVars)
    (hXsF : ∀ x ∈ Xs, x ∉ softVars (substSoft U F)) :
    ∃ one : {r : RecRunResult // InferRecStrata K F frontier ctx anns bindings state [members]
      r.frontier r.subst r.state},
      inferRecStrataWithTypesCore K F frontier ctx anns bindings state [members] = some one ∧
      ∃ V : Subst, (∀ pair ∈ V, pair.2.IsLC) ∧
        (∀ p ∈ P, V.onTy (.fvar p) = .fvar p) ∧
        Subst.AgreesBelow opened U (one.val.subst ++ V) ∧
        RecResidual P declCtx declSpecs declPrefixes G Xs (one.val.subst.onCtx ctx)
          one.val.state (done ++ members) V := by
  let installed := state.installOpenings members openings
  let raws := openRecSources openings bindings
  let active := F ++ (openings.flatMap RecOpening.written).map Ty.fvar
  have hle := ho.frontier_le
  have hiLC : installed.LC := hstateLC.installOpenings
  have hiB : installed.Below opened := hstateB.installOpenings ho
  have hannB : ∀ ann ∈ anns, ∀ v ∈ ann.rigidVars, v < frontier := by
    intro ann ha v hv
    exact (List.mem_append.mp (hanns ann ha v hv)).elim (hK v) (softVars_lt hF v)
  have hactiveB : ∀ t ∈ active, Ty.BelowFvars opened t := by
    intro t ht
    rcases List.mem_append.mp ht with ht | ht
    · exact (hF t ht).mono hle
    · obtain ⟨v, hv, rfl⟩ := List.mem_map.mp ht
      exact .fvar (ho.written_range v hv).2
  have hwritten : ∀ (i v : Nat), v ∈ ((openings[i]?).getD RecOpening.empty).written →
      v ∈ openings.flatMap RecOpening.written := by
    intro i v hv
    cases he : openings[i]? with
    | none => simp only [he,Option.getD_none,RecOpening.empty,List.not_mem_nil] at hv
    | some opening => exact List.mem_flatMap.mpr ⟨opening,List.mem_of_getElem? he,by simpa only [he,Option.getD_some] using hv⟩
  have hsource : ∀ rhs ∈ raws, SourceScope K active rhs := by
    intro rhs hm v hv
    obtain ⟨i,hi⟩ := List.mem_iff_getElem?.mp hm
    obtain ⟨raw,hr,rfl⟩ := openRecSources_getElem? (ho.length.trans hlen) hi
    rcases Input.rigidVars_openTyVarsFrom hv with hv | hv
    · rcases List.mem_append.mp (hrhs raw (List.mem_of_getElem? hr) v hv) with hk | hs
      · exact List.mem_append_left _ hk
      · obtain ⟨t,ht,hv⟩ := TyList.mem_freeVars_iff.mp hs
        exact List.mem_append_right _ (TyList.mem_freeVars_iff.mpr ⟨t,List.mem_append_left _ ht,hv⟩)
    · exact List.mem_append_right _ (TyList.mem_freeVars_iff.mpr ⟨.fvar v,
        List.mem_append_right _ (List.mem_map.mpr ⟨v,hwritten i v hv,rfl⟩),by simp [Ty.freeVars]⟩)
  have hsolveShapes : ∀ ty expected, (ty,some expected) ∈ installed.shapes members openings →
      U.onTy ty = U.onTy expected := by
    intro ty expected hm
    change (ty,some expected) ∈ state.shapes members openings at hm
    obtain ⟨i,hi,he⟩ := List.mem_filterMap.mp hm
    cases hs : state.specs[i]? with
    | none => simp [hs] at he
    | some spec =>
      cases spec with
      | poly scheme => simp [hs,RecSpec.monoTy?] at he
      | mono actual =>
        cases hop : openings[i]? with
        | none => simp [hs,RecSpec.monoTy?,hop] at he
        | some opening =>
          simp [hs,RecSpec.monoTy?,hop] at he
          obtain ⟨rfl,hex⟩ := he
          exact (hsolve i opening actual expected hi hop hs hex).symm
  have hShapeLC := RecState.shapes_lc (members := members) hiLC ho.expected_lc
  have hShapeB := RecState.shapes_below (members := members) hiB (ho.expected_below hannB)
  have hShapeSome := checkRecShapes_complete hShapeLC hres.lc hsolveShapes hUK
  cases hShapeRun : checkRecShapes K (installed.shapes members openings) with
  | none => simp only [hShapeRun,Option.isSome_none] at hShapeSome; contradiction
  | some result =>
    obtain ⟨pre,hp⟩ := result
    have hpreLC := hp.lc hShapeLC
    have hpreB := hp.belowFvars hShapeB
    have hpreK := Subst.fixes_of_dom_avoids hp.dom_avoids
    obtain ⟨Z,hZ,hZP,hfactor⟩ := hp.factor hres.lc hsolveShapes hres.fixes
    have hZK : ∀ k ∈ K, Z.onTy (.fvar k) = .fvar k := by
      intro k hk
      have hh := hfactor (.fvar k)
      rw [hpreK k hk,hUK k hk] at hh
      exact hh.symm
    have hCtxFactor : Z.onCtx (pre.onCtx (installed.rhsCtx ctx)) = U.onCtx (state.rhsCtx ctx) := by
      apply congrArg₂ Ctx.mk
      · simp only [Subst.onCtx,Subst.onEnv,List.map_map]
        apply List.map_congr_left
        intro M hm
        exact congrArg (PolyTy.mk M.paramCount) (hfactor M.body).symm
      · rfl
    have hRawFactor : ∀ rhs : Input, (rhs.substTyFvars pre).substTyFvars Z = rhs.substTyFvars U := by
      intro rhs
      rw [← rhs.substTyFvars_append]
      exact rhs.substTyFvars_congr (fun v _ => by
        change (pre ++ Z).onTy (.fvar v) = U.onTy (.fvar v)
        simpa only [Subst.onTy_append] using (hfactor (.fvar v)).symm)
    have rawLength : ∀ (os : List RecOpening) (bs : List Input), (openRecSources os bs).length = bs.length := by
      intro os bs
      induction bs generalizing os with
      | nil => cases os <;> rfl
      | cons rhs rest ih => cases os <;> simp only [openRecSources,List.length_cons,ih]
    have hCompSome := inferRecComponentWithTypesCore_complete
      (K := K) (F := substSoft pre active) (members := members) (index := 0) (frontier := opened)
      (ctx := (installed.onSubst pre).rhsCtx (pre.onCtx ctx))
      (bindings := raws.map (Input.substTyFvars pre)) (specs := (installed.onSubst pre).specs)
      (fun e he => hProducer e (by simpa only [sizeBindings_map_substTyFvars,raws,sizeBindings_openRecSources] using he))
      (fun he hi => hPrincipal (by simpa only [sizeBindings_map_substTyFvars,raws,sizeBindings_openRecSources] using he) hi)
      (by
        simp only [List.length_map,RecState.onSubst,installed,RecState.installOpenings]
        exact (rawLength openings bindings).trans hspecLen.symm)
      ((hiLC.onSubst hpreLC).rhsCtx (Subst.onCtx_wf hpreLC hctxWF))
      ((hiB.onSubst hpreB (Nat.le_refl _)).rhsCtx (Subst.onCtx_below hpreB hle hctx))
      (fun k hk => (hK k hk).trans_le hle) (substSoft_below hpreB (Nat.le_refl _) hactiveB)
      (hiLC.onSubst hpreLC).1 (hiB.onSubst hpreB (Nat.le_refl _)).1
      (by
        intro rhs hm
        obtain ⟨old,ho,rfl⟩ := List.mem_map.mp hm
        exact (hsource old ho).subst pre hpreK)
      Z P hZ hZK hP hZP
      (by
        intro j rhs target hj hr ht
        obtain ⟨raw,hr0,rfl⟩ := Option.map_eq_some_iff.mp (by simpa only [List.getElem?_map] using hr)
        obtain ⟨old,ht0,rfl⟩ := RecSpec.mono_getElem?_map_onSubstSource ht
        have htyped := hcandidate j raw old (by simpa only [Nat.zero_add] using hj) hr0 ht0
        rw [RecState.rhsCtx_onSubst,hCtxFactor,hRawFactor,← hfactor old]
        exact htyped)
    cases hCompRun : inferRecComponentWithTypesCore K (substSoft pre active) members 0 opened
        ((installed.onSubst pre).rhsCtx (pre.onCtx ctx)) (raws.map (Input.substTyFvars pre))
        (installed.onSubst pre).specs with
    | none => simp only [hCompRun,Option.isSome_none] at hCompSome; contradiction
    | some result =>
      obtain ⟨cres,hc⟩ := result
      obtain ⟨V,hV,hVP,hag⟩ := InferRecComponent.sourcePrincipal_after_shapes hp
        (by simpa only [RecState.rhsCtx_onSubst] using hc)
        (fun he hi => hPrincipal (by simpa only [raws,sizeBindings_openRecSources] using he) hi)
        (hiLC.rhsCtx hctxWF) (hiB.rhsCtx (fun M hm => (hctx M hm).mono hle))
        (fun k hk => (hK k hk).trans_le hle) hactiveB hiLC.1 hiB.1 hsource hpreLC hpreB
        U P hres.lc hP hres.fixes hsolveShapes
        (by intro j rhs hj hr v hv hk hn; exact hUK v hk)
        (by simpa only [Nat.zero_add] using hcandidate)
      let solved := pre ++ cres.subst
      have hag' : Subst.AgreesBelow opened U (solved ++ V) := by
        simpa only [solved,List.append_assoc] using hag
      have hsolvedK : ∀ k ∈ K, solved.onTy (.fvar k) = .fvar k :=
        Subst.fixes_of_dom_avoids (fun pair hp0 hk => (List.mem_append.mp hp0).elim
          (fun hm => hp.dom_avoids pair hm hk) (fun hm => hc.dom_avoids pair hm hk))
      have hCtxEq : V.onCtx ((installed.onSubst solved).fixedCtx (solved.onCtx ctx)) =
          U.onCtx (state.fixedCtx ctx) := by
        rw [RecState.fixedCtx_onSubst,← Subst.onCtx_append]
        exact (Subst.onCtx_congr hag' ((hiB.fixedCtx (fun M hm => (hctx M hm).mono hle)))).symm
      have hBoundary : ∀ x ∈ Xs, ∀ v ∈ ((installed.onSubst solved).fixedCtx (solved.onCtx ctx)).env.freeVars ++
          K ++ softVars (substSoft solved F), x ∉ (V.onTy (.fvar v)).freeVars := by
        intro x hx v hv himage
        rcases List.mem_append.mp hv with hv | hsoft
        · rcases List.mem_append.mp hv with hfixed | hrigid
          · obtain ⟨M,hM,hvM⟩ := Env.mem_freeVars_iff.mp hfixed
            have hh : x ∈ (V.onCtx ((installed.onSubst solved).fixedCtx (solved.onCtx ctx))).env.freeVars := by
              exact Env.mem_freeVars_iff.mpr ⟨V.onPolyTy M,List.mem_map.mpr ⟨M,hM,rfl⟩,
                Ty.mem_freeVars_substFvars_image.mpr ⟨v,hvM,himage⟩⟩
            exact hXsCtx x hx (hCtxEq ▸ hh)
          · have hh := hag' v ((hK v hrigid).trans_le hle)
            rw [Subst.onTy_append,hsolvedK v hrigid] at hh
            exact hXsK x hx v hrigid (hh ▸ himage)
        · obtain ⟨original,ho,hvOriginal⟩ := mem_softVars_substSoft.mp hsoft
          have hh : x ∈ (V.onTy (solved.onTy (.fvar original))).freeVars :=
            Ty.mem_freeVars_substFvars_image.mpr ⟨v,hvOriginal,himage⟩
          have he := hag' original ((softVars_lt hF original ho).trans_le hle)
          rw [Subst.onTy_append] at he
          exact hXsF x hx (mem_softVars_substSoft.mpr ⟨original,ho,he ▸ hh⟩)
      let candidateNames := state.slots.mapIdx (fun i _ => recRenameNames G Xs (declPrefixes[i]?.getD []))
      have hFinishSome := finishRecComponent_complete_of_factor
        (K := K) (soft := softVars (substSoft solved F)) (members := members)
        (ctx := solved.onCtx ctx) (state := installed.onSubst solved)
        (outputs := cres.outputs) (facts := cres.facts) (R := V) candidateNames
        (by simp only [candidateNames,RecState.onSubst,installed,RecState.installOpenings,List.length_mapIdx,List.length_map])
        (by
          intro i images names hi hs hn
          have hib : i < state.slots.length := by
            simpa only [RecState.onSubst,installed,RecState.installOpenings,List.length_map,List.length_mapIdx] using
              (List.getElem?_eq_some_iff.mp hs).1
          have hslot := List.getElem?_eq_getElem hib
          simp only [candidateNames,List.getElem?_mapIdx,hslot,Option.map_some,Option.some.injEq] at hn
          subst names
          have hiopen : i < openings.length := by rw [ho.length,← hslotLen];exact hib
          let opening := openings[i]
          have hop : openings[i]? = some opening := List.getElem?_eq_getElem hiopen
          have he : images = (opening.written.map Ty.fvar).map solved.onTy := by
            simp only [RecState.onSubst,installed,RecState.installOpenings,List.getElem?_map,
              List.getElem?_mapIdx,hslot,Option.map_some,if_pos hi,hop,Option.getD_some] at hs
            exact (Option.some.inj hs).symm
          have hnamesSub : ∀ v ∈ declPrefixes[i]?.getD [], v ∈ G := by
            obtain ⟨ty,ht⟩ := hselected i hi
            obtain ⟨declTy,hd⟩ := hres.mono i ty ht
            exact (hprefix i declTy hd).2
          refine ⟨?_,?_,?_⟩
          · rw [he]
            simp only [List.map_map,Function.comp_def]
            calc
              _ = opening.written.map (fun v => U.onTy (.fvar v)) := by
                apply List.map_congr_left
                intro v hv
                have hh := hag' v (ho.written_range v (List.mem_flatMap.mpr ⟨opening,List.mem_of_getElem? hop,hv⟩)).2
                simpa only [Subst.onTy_append,Function.comp_def] using hh.symm
              _ = _ := himages i opening hi hop
          · obtain ⟨ty,ht⟩ := hselected i hi
            obtain ⟨declTy,hd⟩ := hres.mono i ty ht
            exact recRenameNames_nodup hXsLen hXsND (hprefix i declTy hd).1 hnamesSub
          · intro name hn v hv
            exact hBoundary name (recRenameNames_mem hXsLen hnamesSub name hn) v hv)
      cases hFinishRun : finishRecComponent K (softVars (substSoft solved F)) members (solved.onCtx ctx)
          (installed.onSubst solved) cres.outputs cres.facts with
      | none => simp only [hFinishRun,Option.isSome_none] at hFinishSome; contradiction
      | some result =>
        obtain ⟨exported,hf⟩ := result
        obtain ⟨T,hT,hTP,hagT,hTRes⟩ := hres.close_opened_component ho hp hc hf hPrincipal
          hstateLC hstateB hctxWF hctx hK hF hP hlen hanns hrhs
          (fun i rhs hi hr v hv hk hn => hUK v hk) hsolve hcandidate hexports hdisjoint
          hdeclLC hG hprefix hXsLen hXsND hGXs hXsTypes hXsCtx hXsK hXsF
        let one : {r : RecRunResult // InferRecStrata K F frontier ctx anns bindings state [members]
            r.frontier r.subst r.state} :=
          ⟨⟨cres.frontier,pre ++ cres.subst ++ [],exported⟩,.cons ho hp hc hf .nil⟩
        refine ⟨one,?_,T,hT,hTP,?_,?_⟩
        · simp only [inferRecStrataWithTypesCore,hOpenRun,hShapeRun,hCompRun,hFinishRun,
            List.append_nil,one,installed,raws,active,solved]
        · simpa only [one,List.append_nil] using hagT
        · simpa only [one,List.append_nil] using hTRes


private theorem inferWithTypesCore_sourceComplete_rec_of_unsigned
    {K : List Nat} {F : List Ty} {frontier : Nat} {ctx : Ctx}
    {anns : List LetAnn} {bindings : List Input} {body : Input}
    (hProducer : ∀ e : Input,e.size ≤ sizeBindings bindings → InferWithTypesCoreSourceComplete e)
    (hInfer : ∀ {κ F' Ψ c e Ψ' T output ty},e.size ≤ sizeBindings bindings →
      (hi : Infer κ F' Ψ c e Ψ' T output ty) → Infer.SourcePrincipal hi)
    (hBodyProducer : ∀ e : Input,e.size ≤ body.size → InferWithTypesCoreSourceComplete e)
    (hUnsigned : ∀ (P : List Nat) (declCtx : Ctx) (declAnns : List LetAnn)
      (declBindings : List Input) (declSpecs : List RecSpec)
      (declGroups declPrefixes : List (List Nat)) (G Xs : List Nat) (R : Subst),
      RecGroups.ValidResidualGroups (declAnns.map LetAnn.recModeAnn) (declBindings.map Input.erase) declGroups →
      RecSpecs.WF (declAnns.map LetAnn.recModeAnn) (declBindings.map Input.erase) declSpecs G →
      RecPrefixesWF declAnns declSpecs declPrefixes G →
      (∀ g ∈ G,g ∉ declCtx.env.freeVars ++ P) →
      (∀ ann ∈ declAnns,∀ v ∈ ann.rigidVars,v ∈ P) →
      (∀ rhs ∈ declBindings,∀ v ∈ rhs.rigidVars,v ∈ P) →
      (∀ (stage : Nat) (component : List Nat),declGroups[stage]? = some component →
        ∀ (member : Nat),member ∈ component → ∀ (rhs : Input) (ann : LetAnn) (names : List Nat) (ty : Ty),
        declBindings[member]? = some rhs → declAnns[member]? = some ann →
        declPrefixes[member]? = some names → declSpecs[member]? = some (RecSpec.mono ty) →
        ann.RecFits (recRenameNames G Xs names) (Ty.renameG G Xs ty)) →
      (∀ (stage : Nat) (component : List Nat),declGroups[stage]? = some component →
        ∀ (member : Nat),member ∈ component → ∀ (rhs : Input) (ann : LetAnn) (names : List Nat) (ty : Ty),
        declBindings[member]? = some rhs → declAnns[member]? = some ann →
        declPrefixes[member]? = some names → declSpecs[member]? = some (RecSpec.mono ty) →
        Typing (P ++ Xs) (recStageCtx declCtx declSpecs declPrefixes (declGroups.take stage).flatten G Xs)
          (rhs.openTyVars (recRenameNames G Xs names)) (Ty.renameG G Xs ty)) →
      (∀ g ∈ G,frontier + bindings.length ≤ g) → (∀ x ∈ Xs,frontier + bindings.length ≤ x) →
      Xs.length = G.length → Xs.Nodup → (∀ g ∈ G,g ∉ Xs) →
      (∀ x ∈ Xs,∀ spec ∈ declSpecs,x ∉ spec.freeVars) →
      (∀ x ∈ Xs,x ∉ declCtx.env.freeVars ++ P) →
      CtxWF ctx → CtxBelow (frontier + bindings.length) ctx →
      (RecState.init frontier anns).LC → (RecState.init frontier anns).Below (frontier + bindings.length) →
      (RecState.init frontier anns).Frame frontier K F ctx anns [] →
      (∀ k ∈ K,k < frontier + bindings.length) → (∀ t ∈ F,Ty.BelowFvars (frontier + bindings.length) t) →
      (∀ p ∈ P,p < frontier + bindings.length) →
      RecResidual P declCtx declSpecs declPrefixes G Xs ctx (RecState.init frontier anns) [] R →
      (∀ k ∈ K,R.onTy (.fvar k) = .fvar k) →
      (∀ x ∈ Xs,∀ k ∈ K,x ∉ (R.onTy (.fvar k)).freeVars) →
      (∀ x ∈ Xs,x ∉ softVars (substSoft R F)) →
      (∀ ann ∈ anns,∀ v ∈ ann.rigidVars,v ∈ K ++ softVars F) →
      (∀ rhs ∈ bindings,SourceScope K F rhs) →
      anns.map (LetAnn.substTyFvars R) = declAnns → bindings.map (Input.substTyFvars R) = declBindings →
      ∃ strata : {r : RecRunResult // InferRecStrata K F (frontier + bindings.length) ctx anns bindings
        (RecState.init frontier anns) (RecGroup.inferenceSccs (anns.map LetAnn.recModeAnn) (bindings.map Input.erase))
        r.frontier r.subst r.state},
        inferRecStrataWithTypesCore K F (frontier + bindings.length) ctx anns bindings (RecState.init frontier anns)
          (RecGroup.inferenceSccs (anns.map LetAnn.recModeAnn) (bindings.map Input.erase)) = some strata ∧
        ∃ R1 : Subst,(∀ pair ∈ R1,pair.2.IsLC) ∧ (∀ p ∈ P,R1.onTy (.fvar p) = .fvar p) ∧
          (∀ k ∈ K,R1.onTy (.fvar k) = .fvar k) ∧
          Subst.AgreesBelow (frontier + bindings.length) R (strata.val.subst ++ R1) ∧
          RecResidual P declCtx declSpecs declPrefixes G Xs (strata.val.subst.onCtx ctx) strata.val.state
            (RecGroup.inferenceSccs (anns.map LetAnn.recModeAnn) (bindings.map Input.erase)).flatten R1 ∧
          (anns.map (LetAnn.substTyFvars strata.val.subst)).map (LetAnn.substTyFvars R1) = declAnns ∧
          (bindings.map (Input.substTyFvars strata.val.subst)).map (Input.substTyFvars R1) = declBindings ∧
          (∀ x ∈ Xs,∀ k ∈ K,x ∉ (R1.onTy (.fvar k)).freeVars) ∧
          (∀ x ∈ Xs,x ∉ softVars (substSoft R1 (substSoft strata.val.subst F))))
    {ambient : Subst} {target : Ty} {P : List Nat}
    (hbackend : backendInput K F (.letRec anns bindings body) = none)
    (hscope : SourceScope K F (.letRec anns bindings body))
    (hctxWF : CtxWF ctx) (hctx : CtxBelow frontier ctx)
    (hK : ∀ k ∈ K,k < frontier) (hF : ∀ t ∈ F,Ty.BelowFvars frontier t)
    (hambient : ∀ pair ∈ ambient,pair.2.IsLC)
    (hfixK : ∀ k ∈ K,ambient.onTy (.fvar k) = .fvar k)
    (hP : ∀ p ∈ P,p < frontier) (hfix : ∀ p ∈ P,ambient.onTy (.fvar p) = .fvar p)
    (ht : Typing P (ambient.onCtx ctx) ((Input.letRec anns bindings body).substTyFvars ambient) target) :
    (inferWithTypesCore K frontier ctx (.letRec anns bindings body) F).isSome := by
  have bindingsMap : ∀ (S : Subst) (bs : List Input),substInputBindings S bs = bs.map (Input.substTyFvars S) := by
    intro S bs
    induction bs with
    | nil => rfl
    | cons rhs rest ih => simp only [substInputBindings,List.map_cons,ih]
  change Typing P (ambient.onCtx ctx)
    (.letRec (anns.map (LetAnn.substTyFvars ambient)) (substInputBindings ambient bindings)
      (body.substTyFvars ambient)) target at ht
  rw [bindingsMap] at ht
  obtain ⟨declSpecs,declGroups,declPrefixes,G,L,hGhigh,hdeclValid,hdeclWF,hdeclPrefixes,
    hGfresh,hdeclAnn,hdeclRhs,hdeclFits,hdeclTypes,hdeclPoly,hdeclBody⟩ :=
    ht.rec_inv_high (frontier + bindings.length)
  have hDeclAnnPoly : ∀ (i : Nat) (sigma : PolyTy),
      (anns.map (LetAnn.substTyFvars ambient))[i]? = some (.complete sigma) →
      declSpecs[i]? = some (.poly sigma) := by
    intro i sigma ha
    have hm := congrArg (fun xs : List (Option PolyTy) => xs[i]?) hdeclWF.anns_eq
    dsimp only at hm
    rw [List.getElem?_map,List.getElem?_map,ha,Option.map_some,LetAnn.recModeAnn] at hm
    obtain ⟨spec,hs,he⟩ := Option.map_eq_some_iff.mp hm
    have hEq : spec = .poly sigma := RecSpec.ann_eq_some he
    rwa [hEq] at hs
  have hann : ∀ scheme,.complete scheme ∈ anns → scheme.WF := by
    intro scheme hm
    obtain ⟨i,hi⟩ := List.mem_iff_getElem?.mp hm
    have hd := hDeclAnnPoly i (ambient.onPolyTy scheme) (by
      simp only [List.getElem?_map,hi,Option.map_some,LetAnn.substTyFvars,Subst.onPolyTy,Subst.onTy])
    exact ContainsBvarsUpTo.of_substFvars (hdeclWF.poly_wf _ (List.mem_of_getElem? hd))
  have hlen : anns.length = bindings.length := by simpa only [List.length_map] using hdeclValid.length
  let groups := RecGroup.inferenceSccs (anns.map LetAnn.recModeAnn) (bindings.map Input.erase)
  have hvalid : RecGroups.ValidResidualGroups (anns.map LetAnn.recModeAnn) (bindings.map Input.erase) groups :=
    RecGroup.inferenceSccs_valid (by simp only [List.length_map];exact hlen)
  have hraw := hscope
  have hannscope : ∀ ann ∈ anns, ∀ v ∈ ann.rigidVars, v ∈ K ++ softVars F := by
    intro ann ha v hv
    exact hraw v (List.mem_append_left _ (List.mem_append_left _ (List.mem_flatMap.mpr ⟨ann, ha, hv⟩)))
  have hrhsscope : ∀ rhs ∈ bindings, SourceScope K F rhs := by
    intro rhs hr v hv
    apply hraw v
    apply List.mem_append_left
    apply List.mem_append_right
    have hmap : ∀ bs : List Input, rigidBindingVars bs = bs.flatMap Input.rigidVars := by
      intro bs
      induction bs with
      | nil => rfl
      | cons rhs rest ih => simp only [rigidBindingVars, List.flatMap_cons, ih]
    rw [hmap]
    exact List.mem_flatMap.mpr ⟨rhs, hr, hv⟩
  have hannbelow : ∀ ann ∈ anns, ∀ v ∈ ann.rigidVars, v < frontier := by
    intro ann ha v hv
    exact (List.mem_append.mp (hannscope ann ha v hv)).elim (hK v) (softVars_lt hF v)
  have hrhsbelow : ∀ rhs ∈ bindings, ∀ v ∈ rhs.rigidVars, v < frontier := by
    intro rhs hr v hv
    exact (List.mem_append.mp (hrhsscope rhs hr v hv)).elim (hK v) (softVars_lt hF v)
  have hbodybelow : ∀ v ∈ body.rigidVars, v < frontier := by
    intro v hv
    exact (List.mem_append.mp (hraw v (List.mem_append_right _ hv))).elim (hK v) (softVars_lt hF v)
  have hinitFrame := RecState.Frame.init hctx
    (fun v hv => by obtain ⟨ann, ha, hv⟩ := List.mem_flatMap.mp hv; exact hannbelow ann ha v hv) hK (softVars_lt hF)
  have hinitLC := RecState.LC.init (base := frontier) hann
  have hinitBelow : (RecState.init frontier anns).Below (frontier + bindings.length) := by
    simpa only [hlen] using RecState.Below.init hannbelow
  have hctxSeed : CtxBelow (frontier + bindings.length) ctx :=
    fun M hm => (hctx M hm).mono (by omega)
  have hFSeed : ∀ t ∈ F, Ty.BelowFvars (frontier + bindings.length) t :=
    fun t ht => (hF t ht).mono (by omega)
  have hKSeed : ∀ k ∈ K, k < frontier + bindings.length := fun k hk => by have := hK k hk; omega
  have hPSeed : ∀ p ∈ P, p < frontier + bindings.length := fun p hp => by have := hP p hp; omega
  let avoid := G ++ L ++ (ambient.onCtx ctx).env.freeVars ++ P ++ declSpecs.flatMap RecSpec.freeVars ++
    K.flatMap (fun k => (ambient.onTy (.fvar k)).freeVars) ++ softVars (substSoft ambient F) ++ List.range (frontier + bindings.length)
  obtain ⟨Xs, hXslen, hXsnd, hXsavoid⟩ := exists_fresh_names avoid G.length
  have hXs : FreshNames (G ++ L) G.length Xs := by
    refine ⟨hXslen, hXsnd, ?_⟩
    intro x hx hv
    exact hXsavoid x hx (by simp only [avoid, List.mem_append] at hv ⊢; tauto)
  obtain ⟨R, hR, hag0, hRP, hres0⟩ := RecResidual.init (declPrefixes := declPrefixes) (Xs := Xs)
    hdeclWF hambient hP hfix hannbelow hctx
  have hAnnEq : anns.map (LetAnn.substTyFvars R) = anns.map (LetAnn.substTyFvars ambient) := by
    apply List.map_congr_left
    intro ann ha
    exact ann.substTyFvars_congr (fun v hv => (hag0 v (hannbelow ann ha v hv)).symm)
  have hRhsEq : bindings.map (Input.substTyFvars R) = bindings.map (Input.substTyFvars ambient) := by
    apply List.map_congr_left
    intro rhs hr
    exact rhs.substTyFvars_congr (fun v hv => (hag0 v (hrhsbelow rhs hr v hv)).symm)
  have hXsK : ∀ x ∈ Xs, ∀ k ∈ K, x ∉ (R.onTy (.fvar k)).freeVars := by
    intro x hx k hk hv
    rw [← hag0 k (hK k hk)] at hv
    have hm : x ∈ K.flatMap (fun k => (ambient.onTy (.fvar k)).freeVars) := List.mem_flatMap.mpr ⟨k, hk, hv⟩
    exact hXsavoid x hx (by simp only [avoid, List.mem_append]; tauto)
  have hXsF : ∀ x ∈ Xs, x ∉ softVars (substSoft R F) := by
    intro x hx hv
    have he : substSoft R F = substSoft ambient F := by
      apply List.map_congr_left
      intro t ht
      exact (Subst.onTy_congr hag0 (hF t ht)).symm
    rw [he] at hv
    exact hXsavoid x hx (by simp only [avoid, List.mem_append]; tauto)
  have hRfixK : ∀ k ∈ K,R.onTy (.fvar k) = .fvar k :=
    fun k hk => (hag0 k (hK k hk)).symm.trans (hfixK k hk)
  obtain ⟨⟨⟨first,s1,state1⟩,hstrata⟩,hStrataResult,R1,hR1,hR1P,hR1K,hag1,hres1,hAnnEq1,hRhsEq1,hXsK1,hXsF1⟩ :=
    hUnsigned P (ambient.onCtx ctx) _ _ declSpecs declGroups declPrefixes G Xs R
      hdeclValid hdeclWF hdeclPrefixes hGfresh hdeclAnn hdeclRhs
      (fun st co hs => hdeclFits st co hs Xs hXs)
      (fun st co hs => hdeclTypes st co hs Xs hXs)
      hGhigh (by
        intro x hx
        by_contra hh
        exact hXsavoid x hx (by simp only [avoid,List.mem_append];exact Or.inr (List.mem_range.mpr (by omega))))
      hXslen hXsnd (by intro g hg hx;exact hXs.avoid g hx (List.mem_append_left _ hg))
      (by intro x hx spec hs hv;exact hXsavoid x hx (by
        simp only [avoid,List.mem_append]
        have hm : x ∈ declSpecs.flatMap RecSpec.freeVars := List.mem_flatMap.mpr ⟨spec,hs,hv⟩
        tauto))
      (by intro x hx hv;exact hXsavoid x hx (by simp only [avoid,List.mem_append] at hv ⊢;tauto))
      hctxWF hctxSeed hinitLC hinitBelow hinitFrame hKSeed hFSeed hPSeed hres0 hRfixK hXsK hXsF
      hannscope hrhsscope hAnnEq hRhsEq
  have hvalid0 : RecGroups.ValidResidualGroups (anns.map LetAnn.recModeAnn) (bindings.map Input.erase) ([] ++ groups) := hvalid
  obtain ⟨hframe1, _⟩ := hstrata.frame_of_infer
    (fun _ hi => hi.sourceLocality) hvalid0 hinitFrame hinitLC hctxWF hinitBelow hctxSeed hFSeed
    (by omega) hannscope hrhsscope
  obtain ⟨hS1, hLC1⟩ := hstrata.lc_of_infer (fun _ hi => hi.lc) hctxWF hinitLC
  obtain ⟨hB1, hBelow1⟩ := hstrata.belowFvars_of_infer (fun _ hi => hi.belowFvars)
    hctxSeed hKSeed hFSeed hinitBelow
    (fun ann ha v hv => Nat.lt_of_lt_of_le (hannbelow ann ha v hv) (by omega))
  have hvalid1 := recValid_subst hvalid s1
  have hdone1 := hframe1.all_mono_done hvalid1
  have hle1 := hstrata.frontier_le
  have hbase1 : frontier ≤ first := (Nat.le_add_right frontier bindings.length).trans hle1
  have hctx1 := Subst.onCtx_below hB1 hbase1 hctx
  have hF1 := substSoft_below hB1 hbase1 hF
  have hfix1 := Subst.fixes_of_dom_avoids hstrata.dom_avoids
  have hannscope1 : ∀ ann ∈ anns.map (LetAnn.substTyFvars s1), ∀ v ∈ ann.rigidVars,
      v ∈ K ++ softVars (substSoft s1 F) := by
    intro ann ha v hv
    obtain ⟨old, ho, rfl⟩ := List.mem_map.mp ha
    obtain ⟨k, hk, hv⟩ := LetAnn.rigidVars_substTyFvars hv
    exact scope_image hfix1 (hannscope old ho k hk) hv
  have hrhsscope1 : ∀ rhs ∈ bindings.map (Input.substTyFvars s1), SourceScope K (substSoft s1 F) rhs := by
    intro rhs hr
    obtain ⟨old, ho, rfl⟩ := List.mem_map.mp hr
    exact (hrhsscope old ho).subst s1 hfix1
  have hcandAnn1 : ∀ ann ∈ anns.map (LetAnn.substTyFvars s1),∀ v ∈ (ann.substTyFvars R1).rigidVars,v ∈ P := by
    intro ann ha v hv
    apply hdeclAnn (ann.substTyFvars R1)
    · rw [← hAnnEq1]
      exact List.mem_map.mpr ⟨ann,ha,rfl⟩
    · exact hv
  have hcandRhs1 : ∀ rhs ∈ bindings.map (Input.substTyFvars s1),∀ v ∈ (rhs.substTyFvars R1).rigidVars,v ∈ P := by
    intro rhs hr v hv
    apply hdeclRhs (rhs.substTyFvars R1)
    · rw [← hRhsEq1]
      exact List.mem_map.mpr ⟨rhs,hr,rfl⟩
    · exact hv
  have hSignedCandidate : ∀ (j : Nat) (scheme : PolyTy) (rhs : Input),
      (anns.map (LetAnn.substTyFvars s1))[j]? = some (.complete scheme) →
      (bindings.map (Input.substTyFvars s1))[j]? = some rhs →
      ∃ L,∀ Ys,FreshNames L scheme.paramCount Ys →
        Typing (P ++ Ys) (recBodyCtx (ambient.onCtx ctx) declSpecs declPrefixes G)
          ((rhs.substTyFvars R1).openTyVars Ys) ((R1.onPolyTy scheme).openVars Ys) := by
    intro j scheme rhs ha hr
    have hj : j < state1.specs.length := by
      rw [hframe1.specs_length]
      exact (List.getElem?_eq_some_iff.mp ha).1
    have hs0 := List.getElem?_eq_getElem hj
    have hmode := congrArg (fun xs : List (Option PolyTy) => xs[j]?) hframe1.modes
    dsimp only at hmode
    rw [List.getElem?_map, hs0, List.getElem?_map, ha] at hmode
    have hs : state1.specs[j]? = some (.poly scheme) := by
      cases heq : state1.specs[j]'hj with
      | mono ty => simp only [heq, Option.map_some, RecSpec.ann, LetAnn.recModeAnn] at hmode; cases hmode
      | poly other =>
        simp only [heq, Option.map_some, RecSpec.ann, LetAnn.recModeAnn, Option.some.injEq] at hmode
        exact hmode ▸ (heq ▸ hs0)
    obtain ⟨declScheme, hds, he⟩ := hres1.poly j scheme hs
    refine ⟨L, ?_⟩
    intro Ys hY
    have hr' := congrArg (fun bs : List Input => bs[j]?) hRhsEq1
    simp only [List.getElem?_map, hr, Option.map_some] at hr'
    have hd := hdeclPoly j (rhs.substTyFvars R1) declScheme (by simpa only [List.getElem?_map] using hr'.symm) hds Ys
    rw [← he] at hd
    exact hd hY
  obtain ⟨⟨⟨second,s2,state2⟩,hsigned⟩,hSignedResult⟩ := Option.isSome_iff_exists.mp
    (inferRecSignedWithTypesCore_complete (index := 0)
      (anns := anns.map (LetAnn.substTyFvars s1)) (bindings := bindings.map (Input.substTyFvars s1))
      (fun e he => hProducer e (by simpa only [sizeBindings_map_substTyFvars] using he))
      (fun he hi => hInfer (by simpa only [sizeBindings_map_substTyFvars] using he) hi)
      hres1 (Subst.onCtx_wf hS1 hctxWF) hctx1 hLC1 hBelow1
      (fun k hk => (hK k hk).trans_le hbase1) hF1 (fun p hp => (hP p hp).trans_le hbase1) hR1K
      (by simpa only [List.length_map] using hlen)
      (hframe1.exports_length.trans hframe1.specs_length.symm) hframe1.poly hdone1
      hannscope1 hrhsscope1 hcandAnn1 hcandRhs1 hSignedCandidate)
  obtain ⟨hframe2,_⟩ := hsigned.frame_of_infer
    (fun _ hi => hi.sourceLocality) hframe1 (by simp) hdone1 hBelow1.2.2.2
  obtain ⟨hS2,hLC2⟩ := hsigned.lc_of_infer (fun _ hi => hi.lc) (Subst.onCtx_wf hS1 hctxWF) hLC1
  obtain ⟨R2,hR2,hR2P,hag2,hres2⟩ := hsigned.sourcePrincipal_residual
    (fun he hi => hInfer (by simpa only [sizeBindings_map_substTyFvars] using he) hi)
    hres1 (Subst.onCtx_wf hS1 hctxWF) hctx1 hLC1 hBelow1
    (fun k hk => (hK k hk).trans_le hbase1) hF1 (fun p hp => (hP p hp).trans_le hbase1)
    (hframe1.exports_length.trans hframe1.specs_length.symm) hframe1.poly hdone1 hannscope1 hrhsscope1
    (fun _ _ v _ hk _ => hR1K v hk) (fun _ _ v _ hk _ => hR1K v hk)
    hcandAnn1 hcandRhs1 hSignedCandidate
  have hle2 := hsigned.frontier_le
  have hbase2 : frontier ≤ second := hbase1.trans hle2
  obtain ⟨hB2, hBelow2⟩ := hsigned.belowFvars_of_infer (fun _ hi => hi.belowFvars)
    hctx1 (fun k hk => (hK k hk).trans_le hbase1) hF1 hBelow1
    (by
      intro ann hm v hv
      obtain ⟨old, ho, rfl⟩ := List.mem_map.mp hm
      obtain ⟨k, hk, hv⟩ := LetAnn.rigidVars_substTyFvars hv
      exact (Subst.onTy_belowFvars hB1 ((Ty.BelowFvars.fvar (hannbelow old ho k hk)).mono hbase1)).mem_lt v hv)
  have hag12 : Subst.AgreesBelow (frontier + bindings.length) R ((s1 ++ s2) ++ R2) := by
    simpa only [List.append_assoc] using Subst.AgreesBelow.trans_append hle1 hag1 hB1 hag2
  have hagOriginal : Subst.AgreesBelow frontier ambient ((s1 ++ s2) ++ R2) := by
    intro v hv
    exact (hag0 v hv).trans (hag12 v (by omega))
  have hvalid2 := recValid_subst hvalid1 s2
  have hdone2 := hframe2.all_mono_done hvalid2
  have hcandidateBody := hres2.weaken_from_body
    (hframe2.exports_length.trans hframe2.specs_length.symm) hframe2.poly hdone2 hdeclBody
  have hctxbody : CtxWF (state2.rhsCtx ((s1 ++ s2).onCtx ctx)) := by
    apply hLC2.rhsCtx
    simpa only [Subst.onCtx_append] using Subst.onCtx_wf hS2 (Subst.onCtx_wf hS1 hctxWF)
  have hctxbodyB : CtxBelow second (state2.rhsCtx ((s1 ++ s2).onCtx ctx)) := by
    apply hBelow2.rhsCtx
    simpa only [Subst.onCtx_append] using Subst.onCtx_below hB2 hle2 hctx1
  have hSolvedFixK : ∀ k ∈ K,(s1 ++ s2).onTy (.fvar k) = .fvar k := by
    intro k hk
    rw [Subst.onTy_append,hfix1 k hk,Subst.fixes_of_dom_avoids hsigned.dom_avoids k hk]
  have hR2K : ∀ k ∈ K,R2.onTy (.fvar k) = .fvar k := by
    intro k hk
    have he := hagOriginal k (hK k hk)
    rw [Subst.onTy_append,hfixK k hk,hSolvedFixK k hk] at he
    exact he.symm
  have hBodySource : (body.substTyFvars (s1 ++ s2)).substTyFvars R2 = body.substTyFvars ambient := by
    rw [← Input.substTyFvars_append]
    exact body.substTyFvars_congr (fun v hv => (hagOriginal v (hbodybelow v hv)).symm)
  have hTypedBody : Typing P (R2.onCtx (state2.rhsCtx ((s1 ++ s2).onCtx ctx)))
      ((body.substTyFvars (s1 ++ s2)).substTyFvars R2) target := by
    rw [hBodySource]
    simpa only [Subst.onCtx_append] using hcandidateBody
  have hFbody : ∀ t ∈ substSoft (s1 ++ s2) F,Ty.BelowFvars second t := by
    simpa only [substSoft_append] using substSoft_below hB2 hle2 hF1
  have hBodyScope : SourceScope K (substSoft (s1 ++ s2) F) (body.substTyFvars (s1 ++ s2)) :=
    (show SourceScope K F body from fun v hv => hscope v (List.mem_append_right _ hv)).subst _ hSolvedFixK
  obtain ⟨⟨⟨next,s3,bodyOut,bodyTy,bodyTypes,bodySchemes⟩,hbody⟩,hBodyResult⟩ :=
    Option.isSome_iff_exists.mp (hBodyProducer (body.substTyFvars (s1 ++ s2)) (by simp)
      K (substSoft (s1 ++ s2) F) second (state2.rhsCtx ((s1 ++ s2).onCtx ctx)) R2 target P
      hBodyScope hctxbody hctxbodyB (fun k hk => (hK k hk).trans_le hbase2) hFbody
      hR2 hR2K (fun p hp => (hP p hp).trans_le hbase2) hR2P hTypedBody)
  have hCollectors := InferRecSigned.collectors_of_strata hstrata hsigned hvalid hinitFrame hframe1 hframe2
  obtain ⟨⟨schemes,hSchemes⟩,hCollectSchemes⟩ := Option.isSome_iff_exists.mp hCollectors.1
  obtain ⟨⟨outputs,hOutputs⟩,hCollectOutputs⟩ := Option.isSome_iff_exists.mp hCollectors.2
  have hValidBool := RecGroups.validResidualGroupsB_complete hvalid
  rw [inferWithTypesCore,dif_pos (rigid_all hK),dif_pos (ctx_all hctx),
    dif_pos (soft_all hF),dif_pos (source_all hscope)]
  split
  · rename_i core heq
    simp only [hbackend] at heq
    cases heq
  · simp only [hStrataResult,hSignedResult,hCollectSchemes,hCollectOutputs,hBodyResult]
    split
    · rfl
    · rename_i hBad
      apply False.elim
      apply hBad
      apply List.all_eq_true.mpr
      intro ann ha
      cases ann with
      | absent | template _ | partialForall _ _ => rfl
      | complete sigma => exact PolyTy.wf_iff_bvarsBelow.mpr (hann sigma ha)


/-- Internal assembly only: recursive execution is supplied by its actual phase
producer, while all child visits recurse on source size. -/
private theorem inferWithTypesCore_sourceComplete_of_rec
    (hRec : ∀ (anns : List LetAnn) (bindings : List Input) (body : Input),
      (∀ e : Input,e.size ≤ sizeBindings bindings → InferWithTypesCoreSourceComplete e) →
      (∀ e : Input,e.size ≤ body.size → InferWithTypesCoreSourceComplete e) →
      InferWithTypesCoreSourceComplete (.letRec anns bindings body))
    (input : Input) : InferWithTypesCoreSourceComplete input := by
  induction hs : input.size using Nat.strong_induction_on generalizing input with
  | h size ih =>
    intro K F frontier ctx ambient target P hscope hwf hbelow hK hF hS hfix hP hfixP ht
    cases hemb : backendInput K F input with
    | some core =>
      rcases core with ⟨core,he,hr,hd⟩
      exact inferWithTypesCore_sourceComplete_backend (hemb := he) (hr := hr) (hd := hd) hemb hscope hwf hbelow hK hF hS hfix hP hfixP ht
    | none =>
      have smaller : ∀ e : Input,e.size < input.size → InferWithTypesCoreSourceComplete e := by
        intro e he
        exact ih e.size (by omega) e rfl
      cases input with
      | primLit lit =>
        simp [backendInput,Input.toCore,Expr.tyFreeVars] at hemb
      | primBinOp op =>
        simp [backendInput,Input.toCore,Expr.tyFreeVars] at hemb
      | var i =>
        simp [backendInput,Input.toCore,Expr.tyFreeVars] at hemb
      | ctor name =>
        simp [backendInput,Input.toCore,Expr.tyFreeVars] at hemb
      | lambda ann body =>
        exact inferWithTypesCore_sourceComplete_lambda
          (fun e he => smaller e (by simp only [Input.size];omega))
          hemb hscope hwf hbelow hK hF hS hfix hP hfixP ht
      | app f arg =>
        exact inferWithTypesCore_sourceComplete_app
          (fun e he => smaller e (by simp only [Input.size];omega))
          (fun e he => smaller e (by simp only [Input.size];omega))
          (fun _ _ => Infer.sourcePrincipal) (fun _ _ => Infer.sourcePrincipal)
          hemb hscope hwf hbelow hK hF hS hfix hP hfixP ht
      | letIn ann rhs body =>
        cases hmode : ann.isSignature with
        | false =>
          exact inferWithTypesCore_sourceComplete_letIn
            (fun e he => smaller e (by simp only [Input.size];omega))
            (fun e he => smaller e (by simp only [Input.size];omega))
            (fun _ _ => Infer.sourcePrincipal)
            hemb hmode hscope hwf hbelow hK hF hS hfix hP hfixP ht
        | true =>
          exact inferWithTypesCore_sourceComplete_signature
            (fun e he => smaller e (by simp only [Input.size];omega))
            (fun e he => smaller e (by simp only [Input.size];omega))
            hemb hmode hscope hwf hbelow hK hF hS hfix hP hfixP ht
      | match_ scrut branches =>
        apply inferWithTypesCore_sourceComplete_match
          (fun e he => smaller e (by simp only [Input.size];omega))
          (fun _ _ => Infer.sourcePrincipal) ?_
          hemb hscope hwf hbelow hK hF hS hfix hP hfixP ht
        intro bs hbs
        exact inferBranchesWithTypesCore_sourceComplete_of_body bs
          (fun e he => smaller e (by simp only [Input.size];omega))
          (fun _ _ => Infer.sourcePrincipal)
      | letRec anns bindings body =>
        exact hRec anns bindings body
          (fun e he => smaller e (by simp only [Input.size];omega))
          (fun e he => smaller e (by simp only [Input.size];omega))
          K F frontier ctx ambient target P hscope hwf hbelow hK hF hS hfix hP hfixP ht

/-- Public fixed-source completeness is the F=[] specialization of source
completeness; the source is fixed because its authored variables lie in K. -/
theorem _root_.InferWithTypesCoreSourceComplete.complete
    {input : Input} (hc : InferWithTypesCoreSourceComplete input) : InferWithTypesCoreComplete input := by
  intro K frontier ctx ambient target hwf hbelow hK hS hfix ht
  have hraw : ∀ v ∈ input.rigidVars,v ∈ K := ht.rigidVars
  have hsource : input.substTyFvars ambient = input :=
    input.substTyFvars_eq_self_of_fixes (fun v hv => hfix v (hraw v hv))
  apply hc K [] frontier ctx ambient target K
    (fun v hv => by simpa only [softVars,TyList.freeVars,List.append_nil] using hraw v hv)
    hwf hbelow hK (by simp) hS hfix hK hfix
  rwa [hsource]

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
