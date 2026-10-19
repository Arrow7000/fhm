import FHM.AnonymousPrincipal

namespace Anonymous

/-- Producer completeness for the concrete worker, under an arbitrary LC
specialization fixing the inference's rigid variables. Successful results
already carry output typing and residual principality. -/
def InferCoreComplete (input : Input) : Prop :=
  ∀ (K : List Nat) (frontier : Nat) (ctx : Ctx) (ambient : Subst) (target : Ty),
    CtxWF ctx → CtxBelow frontier ctx → (∀ k ∈ K, k < frontier) →
    (∀ pair ∈ ambient, pair.2.IsLC) →
    (∀ k ∈ K, ambient.onTy (.fvar k) = .fvar k) →
    Typing K (ambient.onCtx ctx) input target → (inferCore K frontier ctx input).isSome

private theorem rigid_all {K : List Nat} (h : ∀ k ∈ K, k < frontier) :
    K.all (fun v => decide (v < frontier)) = true :=
  List.all_eq_true.mpr (fun v hv => decide_eq_true (h v hv))

private theorem ctx_all (h : CtxBelow frontier ctx) :
    ctx.env.freeVars.all (fun v => decide (v < frontier)) = true := by
  apply List.all_eq_true.mpr
  intro v hv
  obtain ⟨scheme, hs, hv⟩ := Env.mem_freeVars_iff.mp hv
  exact decide_eq_true ((h scheme hs).mem_lt v hv)

theorem inferCore_complete_backend {input : Input} {core : Expr}
    (hemb : input.toCore = some core) : InferCoreComplete input := by
  intro K frontier ctx ambient target hwf hbelow hK hS hfix ht
  obtain ⟨hcore, hscope⟩ := ht.toCore hemb
  obtain ⟨next, subst, ty, R, hi, _⟩ := _root_.Infer.complete core K hwf hbelow hS hK hscope hfix hcore
  have hsome := _root_.inferCore_complete core K hwf hbelow hK hscope hi
  obtain ⟨⟨⟨n, s, t, nodes, schemes⟩, hresult⟩, hworker⟩ := Option.isSome_iff_exists.mp hsome
  have hroot : (_root_.inferCore K frontier ctx core).isSome := by
    rw [_root_.inferCore, hworker]
    rfl
  obtain ⟨⟨⟨n, s, t⟩, hi⟩, hroot⟩ := Option.isSome_iff_exists.mp hroot
  have hscopeAll : core.tyFreeVars.all (fun v => decide (v ∈ K)) = true :=
    List.all_eq_true.mpr (fun v hv => decide_eq_true (hscope v hv))
  rw [inferCore, dif_pos (rigid_all hK), dif_pos (ctx_all hbelow)]
  split
  · rename_i core' heq
    have hcoreeq := Option.some.inj (heq.symm.trans hemb)
    subst core'
    simp only [hscopeAll, dite_true, hroot, Option.isSome_some]
  · rename_i heq
    simp [hemb] at heq

theorem inferCore_complete_lambda_partial
    (ih : InferCoreComplete body) (hemb : (Input.lambda ann body).toCore = none) :
    InferCoreComplete (.lambda ann body) := by
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
  obtain ⟨⟨⟨next, subst, completed, bodyTy⟩, hb⟩, hbodyResult⟩ := Option.isSome_iff_exists.mp hbody
  rw [inferCore, dif_pos (rigid_all hK), dif_pos (ctx_all hbelow)]
  split
  · rename_i core heq
    simp [hemb] at heq
  · simp only [hseedResult, hbodyResult, Option.isSome_some]

theorem inferCore_complete_app_partial
    (ihf : InferCoreComplete f) (iha : InferCoreComplete arg)
    (hemb : (Input.app f arg).toCore = none) : InferCoreComplete (.app f arg) := by
  intro K frontier ctx ambient target hwf hbelow hK hS hfix ht
  obtain ⟨paramD, hfD, haD⟩ := ht.app_inv
  obtain ⟨⟨⟨first, s1, fOut, fTy⟩, hf⟩, hfResult⟩ := Option.isSome_iff_exists.mp
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
  obtain ⟨⟨⟨second, s2, argOut, argTy⟩, ha⟩, haResult⟩ := Option.isSome_iff_exists.mp
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
  rw [inferCore, dif_pos (rigid_all hK), dif_pos (ctx_all hbelow)]
  split
  · rename_i core heq; simp [hemb] at heq
  · simp only [hfResult, haResult, huResult, Option.isSome_some]

theorem inferCore_complete_letIn_partial
    (ihr : InferCoreComplete rhs) (ihb : InferCoreComplete body)
    (hemb : (Input.letIn ann rhs body).toCore = none) : InferCoreComplete (.letIn ann rhs body) := by
  intro K frontier ctx ambient target hwf hbelow hK hS hfix ht
  have hlet := ht
  cases ht with
  | complete hemb' _ _ => simp [hemb] at hemb'
  | @letIn ann _ rhs body target M L hM hannRigid hannFits hrD hbD =>
    obtain ⟨Xs, hXlen, hXnd, hXavoid⟩ := exists_fresh_names L M.paramCount
    have hXs : FreshNames L M.paramCount Xs := ⟨hXlen, hXnd, hXavoid⟩
    obtain ⟨⟨⟨first, s1, rhsOut, rhsTy⟩, hr⟩, hrResult⟩ := Option.isSome_iff_exists.mp
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
    obtain ⟨⟨⟨next, s2, bodyOut, bodyTy⟩, hb⟩, hbResult⟩ := Option.isSome_iff_exists.mp
      (ihb K checked _ V target hbodyWF hbodyB hKchecked hV hVK hbodyD)
    rw [inferCore, dif_pos (rigid_all hK), dif_pos (ctx_all hbelow)]
    split
    · rename_i core heq; simp [hemb] at heq
    · simp only [hrResult, hcResult, hbResult, Option.isSome_some]

/-- Concrete producer completeness for exactly the independently specified
fragment, including structured partial annotations and completed backend leaves. -/
theorem inferCore_complete (input : Input) : InferCoreComplete input := by
  cases hemb : input.toCore with
  | some core => exact inferCore_complete_backend hemb
  | none =>
    cases input with
    | primLit => cases hemb
    | primBinOp => cases hemb
    | var => cases hemb
    | ctor => cases hemb
    | lambda ann body => exact inferCore_complete_lambda_partial (inferCore_complete body) hemb
    | app f arg => exact inferCore_complete_app_partial (inferCore_complete f) (inferCore_complete arg) hemb
    | letIn ann rhs body =>
      exact inferCore_complete_letIn_partial (inferCore_complete rhs) (inferCore_complete body) hemb
    | match_ scrut branches =>
      intro K frontier ctx ambient target hwf hbelow hK hS hfix ht
      cases ht with
      | complete hemb' _ _ => simp [hemb] at hemb'
    | letRec anns bindings body =>
      intro K frontier ctx ambient target hwf hbelow hK hS hfix ht
      cases ht with
      | complete hemb' _ _ => simp [hemb] at hemb'
termination_by sizeOf input

/-- Producer completeness also yields the usual relational residual contract;
it is a corollary of concrete success and principality, not a second worker. -/
theorem Infer.complete {input : Input} {ctx : Ctx} {K : List Nat}
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
theorem inferCore_accepts_iff {K : List Nat} {frontier : Nat} {ctx : Ctx} {input : Input}
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
theorem inferCore_empty_accepts_iff {K : List Nat} {frontier : Nat} {ctors : CtorEnv} {input : Input}
    (hK : ∀ k ∈ K, k < frontier) :
    (inferCore K frontier ⟨[], ctors⟩ input).isSome ↔ ∃ ty, Typing K ⟨[], ctors⟩ input ty := by
  constructor
  · intro hsome
    obtain ⟨⟨⟨next, subst, output, ty⟩, hi⟩, _⟩ := Option.isSome_iff_exists.mp hsome
    exact ⟨ty, by simpa only [Subst.onCtx, Subst.onEnv, List.map_nil] using hi.inputSound CtxWF.empty⟩
  · rintro ⟨ty, ht⟩
    exact inferCore_complete input K frontier ⟨[], ctors⟩ [] ty CtxWF.empty CtxBelow.empty hK
      (by simp) (by simp) (by simpa only [Subst.onCtx, Subst.onEnv, List.map_nil] using ht)

#print axioms inferCore_complete
#print axioms Infer.complete
#print axioms inferCore_empty_accepts_iff

end Anonymous
