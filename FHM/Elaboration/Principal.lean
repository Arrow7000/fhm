import FHM.Elaboration.Properties

namespace Elaboration

mutual
theorem Template.toCore_fits {template : Template} {ty : Ty}
    (h : template.toCore = some ty) : template.Fits ty := by
  cases template with
  | fixed => cases h; exact .fixed
  | hole => cases h
  | arrow a b =>
    simp only [Template.toCore, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨ta, ha, tb, hb, rfl⟩ := h
    exact .arrow (Template.toCore_fits ha) (Template.toCore_fits hb)
  | custom name args =>
    simp only [Template.toCore, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨tys, ht, rfl⟩ := h
    exact .custom (completeTypes_fits ht)
theorem completeTypes_fits {templates : List Template} {tys : List Ty}
    (h : completeTypes templates = some tys) : List.Forall₂ Template.Fits templates tys := by
  cases templates with
  | nil => cases h; exact .nil
  | cons t ts =>
    simp only [completeTypes, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨ty, ht, tys, hts, rfl⟩ := h
    exact .cons (Template.toCore_fits ht) (completeTypes_fits hts)
end

mutual
theorem Template.Fits.toCore_eq {template : Template} {ty complete : Ty}
    (h : template.Fits ty) (hc : template.toCore = some complete) : ty = complete := by
  cases h with
  | fixed => cases hc; rfl
  | hole => cases hc
  | arrow ha hb =>
    simp only [Template.toCore, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at hc
    obtain ⟨ta, hta, tb, htb, rfl⟩ := hc
    rw [ha.toCore_eq hta, hb.toCore_eq htb]
  | custom h =>
    simp only [Template.toCore, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at hc
    obtain ⟨tys, htys, rfl⟩ := hc
    rw [fitsList_toCore_eq h htys]
theorem fitsList_toCore_eq {templates : List Template} {tys complete : List Ty}
    (h : List.Forall₂ Template.Fits templates tys)
    (hc : completeTypes templates = some complete) : tys = complete := by
  cases h with
  | nil => cases hc; rfl
  | cons hh ht =>
    simp only [completeTypes, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at hc
    obtain ⟨ty, hty, tys, htys, rfl⟩ := hc
    rw [hh.toCore_eq hty, fitsList_toCore_eq ht htys]
end

private theorem completeBranches_length {inputs : List (MatchPattern × Input)}
    {cores : List (MatchPattern × Expr)} (h : completeBranches inputs = some cores) :
    inputs.length = cores.length := by
  induction inputs generalizing cores with
  | nil => cases h; rfl
  | cons head rest ih =>
    rcases head with ⟨pat, body⟩
    simp only [completeBranches, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨body', _, rest', hr, rfl⟩ := h
    simp only [List.length_cons, ih hr]

private theorem completeBranches_forward {inputs : List (MatchPattern × Input)}
    {cores : List (MatchPattern × Expr)} (h : completeBranches inputs = some cores)
    {branch : MatchPattern × Input} (hb : branch ∈ inputs) :
    ∃ core, (branch.1, core) ∈ cores ∧ branch.2.toCore = some core := by
  induction inputs generalizing cores with
  | nil => cases hb
  | cons head rest ih =>
    rcases head with ⟨pat, body⟩
    simp only [completeBranches, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨body', hh, rest', hr, rfl⟩ := h
    rcases List.mem_cons.mp hb with rfl | hb
    · exact ⟨body', List.mem_cons_self, hh⟩
    · obtain ⟨core, hc, heq⟩ := ih hr hb
      exact ⟨core, List.mem_cons_of_mem _ hc, heq⟩

private theorem completeBranches_backward {inputs : List (MatchPattern × Input)}
    {cores : List (MatchPattern × Expr)} (h : completeBranches inputs = some cores)
    {branch : MatchPattern × Expr} (hb : branch ∈ cores) :
    ∃ body, (branch.1, body) ∈ inputs ∧ body.toCore = some branch.2 := by
  induction inputs generalizing cores with
  | nil => cases h; cases hb
  | cons head rest ih =>
    rcases head with ⟨pat, body⟩
    simp only [completeBranches, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨body', hh, rest', hr, rfl⟩ := h
    rcases List.mem_cons.mp hb with rfl | hb
    · exact ⟨body, List.mem_cons_self, hh⟩
    · obtain ⟨source, hs, heq⟩ := ih hr hb
      exact ⟨source, List.mem_cons_of_mem _ hs, heq⟩

private theorem branchFreeVars_iff {branches : List (MatchPattern × Expr)} {v : Nat} :
    v ∈ Expr.tyFreeVars.BranchList.tyFreeVars branches ↔
      ∃ branch ∈ branches, v ∈ branch.2.tyFreeVars := by
  induction branches with
  | nil => simp [Expr.tyFreeVars.BranchList.tyFreeVars]
  | cons head rest ih =>
    rcases head with ⟨pat, body⟩
    simp only [Expr.tyFreeVars.BranchList.tyFreeVars, List.mem_append, ih, List.mem_cons]
    constructor
    · rintro (hv | ⟨b, hb, hv⟩)
      · exact ⟨_, Or.inl rfl, hv⟩
      · exact ⟨b, Or.inr hb, hv⟩
    · rintro ⟨b, rfl | hb, hv⟩
      · exact Or.inl hv
      · exact Or.inr ⟨b, hb, hv⟩

/-- The independent rules conservatively recover ordinary typing whenever the
input is already complete. This retains complete annotations and recursion. -/
theorem Typing.toCore (h : Typing K ctx input ty) {core : Expr}
    (hc : input.toCore = some core) :
    TypeOfHM ctx core ty ∧ (∀ v ∈ core.tyFreeVars, v ∈ K) := by
  induction h using Typing.rec
      (motive_2 := fun K ctx branch scrutTy resultTy _ =>
        ∀ {body : Expr}, branch.2.toCore = some body →
          TypeOfMatchBranch ctx (branch.1, body) scrutTy resultTy ∧
            (∀ v ∈ body.tyFreeVars, v ∈ K)) generalizing core with
  | complete hemb hscope ht => cases hemb.symm.trans hc; exact ⟨ht, hscope⟩
  | primLit ht => cases hc; exact ⟨ht, by simp [Expr.tyFreeVars]⟩
  | primBinOp ht => cases hc; exact ⟨ht, by simp [Expr.tyFreeVars]⟩
  | @lambda ann _ _ body _ param hlc hfits hrigid _ ih =>
    simp only [Input.toCore, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at hc
    obtain ⟨ann', ha, body', hb, rfl⟩ := hc
    obtain ⟨ht, hs⟩ := ih hb
    have hpin : ann'.Pins param := by
      cases ann with
      | none => cases ha; intro a h; cases h
      | some template =>
        simp only [completeLambdaAnn, bind, pure, Option.bind_eq_some_iff,
          Option.some.injEq] at ha
        obtain ⟨t, ht, rfl⟩ := ha
        intro a ha
        cases ha
        exact (hfits template rfl).toCore_eq ht
    refine ⟨.lambda hlc hpin rfl ht, ?_⟩
    intro v hv
    rcases List.mem_append.mp hv with hv | hv
    · cases ann with
      | none => cases ha; cases hv
      | some template =>
        simp only [completeLambdaAnn, bind, pure, Option.bind_eq_some_iff,
          Option.some.injEq] at ha
        obtain ⟨t, ht, rfl⟩ := ha
        exact hrigid template rfl v ((Template.toCore_rigidVars ht v).mpr hv)
    · exact hs v hv
  | app _ _ ihf ihx =>
    simp only [Input.toCore, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at hc
    obtain ⟨f, hf, x, hx, rfl⟩ := hc
    obtain ⟨htf, hsf⟩ := ihf hf
    obtain ⟨htx, hsx⟩ := ihx hx
    exact ⟨.app htf htx, fun v hv => (List.mem_append.mp hv).elim (hsf v) (hsx v)⟩
  | @letIn ann _ _ rhs body _ M L hwf _ hfits _ _ ihr ihb =>
    simp only [Input.toCore, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at hc
    obtain ⟨ann', ha, rhs', hr, body', hb, rfl⟩ := hc
    obtain ⟨Xs, hlen, hnd, hav⟩ := exists_fresh_names L M.paramCount
    have hXs : FreshNames L M.paramCount Xs := ⟨hlen, hnd, hav⟩
    have hfit := hfits Xs hXs
    cases ann with
    | complete => contradiction
    | partialForall => contradiction
    | template => cases ha
    | absent =>
      cases ha
      obtain ⟨htb, hsb⟩ := ihb hb
      refine ⟨.letIn hwf (by intro a h; cases h) (fun Ys hYs => (ihr Ys hYs hr).1) rfl htb, ?_⟩
      intro v hv
      rcases List.mem_append.mp hv with hv | hv
      · exact (ihr Xs hXs hr).2 v hv
      · exact hsb v hv
  | var hlook hlc hinst => cases hc; exact ⟨.var hlook hlc hinst, by simp [Expr.tyFreeVars]⟩
  | ctor hlook hlc hinst => cases hc; exact ⟨.ctor hlook hlc hinst, by simp [Expr.tyFreeVars]⟩

  | match_ _ hne _ ihs ihbranches =>
    simp only [Input.toCore, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at hc
    obtain ⟨scrut', hs, branches', hbs, rfl⟩ := hc
    obtain ⟨hts, hscopes⟩ := ihs hs
    refine ⟨.match_ hts ?_ ?_, ?_⟩
    · intro hempty
      have hlen := completeBranches_length hbs
      rw [hempty, List.length_nil] at hlen
      exact hne (List.length_eq_zero_iff.mp hlen)
    · intro branch hb
      obtain ⟨body, hbody, heq⟩ := completeBranches_backward hbs hb
      exact (ihbranches (branch.1, body) hbody heq).1
    · intro v hv
      rcases List.mem_append.mp hv with hv | hv
      · exact hscopes v hv
      · obtain ⟨branch, hb, hv⟩ := branchFreeVars_iff.mp hv
        obtain ⟨body, hbody, heq⟩ := completeBranches_backward hbs hb
        exact (ihbranches (branch.1, body) hbody heq).2 v hv
  | named hspec _ ih =>
    rename_i body heq
    obtain ⟨ht, hs⟩ := ih heq
    exact ⟨.mk hspec rfl ht, hs⟩
  | wildcard _ ih =>
    rename_i body heq
    obtain ⟨ht, hs⟩ := ih heq
    exact ⟨.wildcard ht, hs⟩

/-- Lambda inversion covers both partial syntax and the complete-subtree rule. -/
theorem Typing.lambda_inv (h : Typing K ctx (.lambda ann body) ty) :
    ∃ param result, ty = .arrow param result ∧ param.IsLC ∧
      (∀ template, ann = some template → template.Fits param) ∧
      (∀ template, ann = some template → ∀ v ∈ template.rigidVars, v ∈ K) ∧
      Typing K { ctx with env := PolyTy.mkTrivial param :: ctx.env } body result := by
  cases h with
  | lambda hlc hfits hr hb => exact ⟨_, _, rfl, hlc, hfits, hr, hb⟩
  | complete hemb hscope ht =>
    simp only [Input.toCore, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at hemb
    obtain ⟨ann', ha, body', hb, rfl⟩ := hemb
    cases ht with
    | lambda hlc hp hctx ht =>
      subst hctx
      refine ⟨_, _, rfl, hlc, ?_, ?_, .complete hb ?_ ht⟩
      · intro t heq
        subst ann
        simp only [completeLambdaAnn, bind, pure, Option.bind_eq_some_iff,
          Option.some.injEq] at ha
        obtain ⟨a, hta, rfl⟩ := ha
        rw [hp a rfl]
        exact Template.toCore_fits hta
      · intro t heq v hv
        subst ann
        simp only [completeLambdaAnn, bind, pure, Option.bind_eq_some_iff,
          Option.some.injEq] at ha
        obtain ⟨a, hta, rfl⟩ := ha
        exact hscope v (List.mem_append_left _ ((Template.toCore_rigidVars hta v).mp hv))
      · intro v hv; exact hscope v (List.mem_append_right _ hv)

theorem Typing.app_inv (h : Typing K ctx (.app f arg) ty) :
    ∃ param, Typing K ctx f (.arrow param ty) ∧ Typing K ctx arg param := by
  cases h with
  | app hf hx => exact ⟨_, hf, hx⟩
  | complete hemb hscope ht =>
    simp only [Input.toCore, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at hemb
    obtain ⟨f', hf, arg', hx, rfl⟩ := hemb
    cases ht with
    | app htf htx =>
      exact ⟨_, .complete hf (fun v hv => hscope v (List.mem_append_left _ hv)) htf,
        .complete hx (fun v hv => hscope v (List.mem_append_right _ hv)) htx⟩

theorem Typing.letMono_inv (h : Typing K ctx (.letIn ann rhs body) ty)
    (hmono : ann.FitsMono checkedTy) :
    ∃ (M : PolyTy) (L : List Nat), M.WF ∧
      (∀ template, ann = .template template → ∀ v ∈ template.rigidVars, v ∈ K) ∧
      (∀ Xs, FreshNames L M.paramCount Xs → ann.FitsMono (M.openVars Xs)) ∧
      (∀ Xs, FreshNames L M.paramCount Xs → Typing K ctx rhs (M.openVars Xs)) ∧
      Typing K { ctx with env := M :: ctx.env } body ty := by
  cases h with
  | letIn hwf hr hf htr htb => exact ⟨_, _, hwf, hr, hf, htr, htb⟩
  | complete hemb hscope ht =>
    simp only [Input.toCore, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at hemb
    obtain ⟨ann', ha, rhs', hr, body', hb, rfl⟩ := hemb
    cases ann with
    | complete => contradiction
    | partialForall => contradiction
    | template => cases ha
    | absent =>
      cases ha
      cases ht with
      | @letIn _ _ _ _ _ _ M L hwf _ hcofin heq hbody =>
        subst heq
        refine ⟨M, L, hwf, ?_, ?_, ?_, .complete hb ?_ hbody⟩
        · intro template heq; cases heq
        · intro Xs hXs; trivial
        · intro Xs hXs
          exact .complete hr (fun v hv => hscope v (List.mem_append_left _ hv)) (hcofin Xs hXs)
        · intro v hv; exact hscope v (List.mem_append_right _ hv)

/-- Match inversion preserves each constructor's existential arguments and
field context, including when the input used the complete-subtree rule. -/
theorem Typing.match_inv (h : Typing K ctx (.match_ scrut branches) resultTy) :
    ∃ scrutTy, Typing K ctx scrut scrutTy ∧ branches ≠ [] ∧
      ∀ branch ∈ branches, BranchTyping Typing K ctx branch scrutTy resultTy := by
  cases h with
  | match_ hs hne hb => exact ⟨_, hs, hne, hb⟩
  | complete hemb hscope ht =>
    simp only [Input.toCore, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at hemb
    obtain ⟨scrut', hs, branches', hbs, rfl⟩ := hemb
    cases ht with
    | match_ hscrut hne hbranches =>
      refine ⟨_, .complete hs (fun v hv => hscope v (List.mem_append_left _ hv)) hscrut, ?_, ?_⟩
      · intro hempty
        subst branches
        cases hbs
        exact hne rfl
      · intro branch hb
        obtain ⟨core, hc, heq⟩ := completeBranches_forward hbs hb
        have hcoreScope : ∀ v ∈ core.tyFreeVars, v ∈ K := fun v hv =>
          hscope v (List.mem_append_right _ (branchFreeVars_iff.mpr ⟨_, hc, hv⟩))
        have hbranch := hbranches (branch.1, core) hc
        rcases branch with ⟨pat, body⟩
        cases hbranch with
        | mk hspec hctx hbody =>
          subst hctx
          exact .named hspec (.complete heq hcoreScope hbody)
        | wildcard hbody => exact .wildcard (.complete heq hcoreScope hbody)

/-- A whole lambda-parameter hole has exactly omission's independent meaning. -/
theorem Typing.lambda_hole_iff :
    Typing K ctx (.lambda (some .hole) body) ty ↔ Typing K ctx (.lambda none body) ty := by
  constructor
  · intro h
    obtain ⟨param, result, rfl, hlc, _, _, hb⟩ := h.lambda_inv
    exact .lambda hlc (fun _ heq => by cases heq) (fun _ heq => by cases heq) hb
  · intro h
    obtain ⟨param, result, rfl, hlc, _, _, hb⟩ := h.lambda_inv
    refine .lambda hlc ?_ ?_ hb
    · intro template heq; cases heq; exact .hole
    · intro template heq; cases heq; simp only [Template.rigidVars, List.not_mem_nil, false_implies, implies_true]

/-- A whole ordinary-let signature hole has exactly omission's independent
meaning, including cofinite generalization of its RHS. -/
theorem Typing.let_hole_iff :
    Typing K ctx (.letIn (.template .hole) rhs body) ty ↔
      Typing K ctx (.letIn .absent rhs body) ty := by
  constructor
  · intro h
    obtain ⟨M, L, hwf, _, _, hr, hb⟩ := h.letMono_inv (checkedTy := .prim .unit) (.hole)
    exact .letIn hwf (fun _ heq => by cases heq) (fun _ _ => True.intro) hr hb
  · intro h
    obtain ⟨M, L, hwf, _, _, hr, hb⟩ := h.letMono_inv (checkedTy := .prim .unit) True.intro
    refine .letIn hwf ?_ (fun _ _ => .hole) hr hb
    intro template heq; cases heq
    simp only [Template.rigidVars, List.not_mem_nil, false_implies, implies_true]

/-- Residual principality retains an independently quantified protected set.
`Typing P` scopes authored fixed types in precisely that protected set. It does
not claim most-general fillings for every unused annotation hole. -/
def _root_.Infer.Principal (_h : Infer K frontier ctx input next subst output ty) : Prop :=
  CtxWF ctx → CtxBelow frontier ctx → (∀ k ∈ K, k < frontier) →
  ∀ (ambient : Subst) (target : Ty) (P : List Nat),
    (∀ pair ∈ ambient, pair.2.IsLC) → (∀ p ∈ P, p < frontier) →
    (∀ p ∈ P, ambient.onTy (.fvar p) = .fvar p) →
    Typing P (ambient.onCtx ctx) input target →
    ∃ residual : Subst, (∀ pair ∈ residual, pair.2.IsLC) ∧
      target = residual.onTy ty ∧
      (∀ p ∈ P, residual.onTy (.fvar p) = .fvar p) ∧
      Subst.AgreesBelow frontier ambient (subst ++ residual)

theorem Seed.override (h : Seed K frontier ann param initial)
    (hK : ∀ k ∈ K, k < frontier) {target : Ty} (htarget : target.IsLC)
    (hfit : ∀ template, ann = some template → template.Fits target)
    {ambient : Subst} (hlc : ∀ pair ∈ ambient, pair.2.IsLC)
    (hfix : ∀ template, ann = some template →
      ∀ v ∈ template.rigidVars, ambient.onTy (.fvar v) = .fvar v) :
    ∃ U : Subst, (∀ pair ∈ U, pair.2.IsLC) ∧
      Subst.AgreesBelow frontier ambient U ∧ U.onTy param = target := by
  cases h with
  | absent =>
    obtain ⟨U, hU, hag, hb⟩ := Subst.override_block hlc frontier [target] (by simpa using htarget)
    exact ⟨U, hU, hag, by simpa using hb 0 (by simp)⟩
  | @annotated next ty template heq _ hr =>
    obtain ⟨U, hU, hag, ht⟩ := (hfit template rfl).allocate_override htarget hlc frontier
      (fun v hv => hK v (hr v hv)) (hfix template rfl)
    rw [heq] at ht
    exact ⟨U, hU, hag, ht⟩

theorem _root_.Infer.principal_backend {input : Input} {core : Expr} (hemb : input.toCore = some core)
    (h : CoreBackend.Infer K frontier ctx core next subst ty)
    (hctx : CtxBelow frontier ctx) (hK : ∀ k ∈ K, k < frontier)
    (hr : ∀ v ∈ core.tyFreeVars, v ∈ K) :
    Infer.Principal (.backend hemb h hctx hK hr) := by
  intro hwf hb _ ambient target P hlc hP hfix ht
  obtain ⟨ht, hscope⟩ := ht.toCore hemb
  exact h.principal hwf hb ambient target P hlc hP hscope hfix ht

theorem _root_.Infer.principal_lambda {ctx : Ctx}
    (hs : Seed K frontier ann param initial)
    (hb : Infer K initial { ctx with env := PolyTy.mkTrivial param :: ctx.env }
      body next subst completed bodyTy)
    (ih : Infer.Principal hb) : Infer.Principal (.lambda hs hb) := by
  intro hwf hbelow hK ambient target P hS hP hfix htyping
  obtain ⟨paramD, resultD, rfl, hparamD, hfit, hrigid, hbodyD⟩ := htyping.lambda_inv
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
  have hUfix : ∀ p ∈ P, U.onTy (.fvar p) = .fvar p :=
    fun p hp => (hUagree p (hP p hp)).symm.trans (hfix p hp)
  obtain ⟨R, hR, hresult, hRP, hag⟩ := ih hbodywf hbodybelow
    (fun k hk => Nat.lt_of_lt_of_le (hK k hk) hle) U resultD P hU
    (fun p hp => Nat.lt_of_lt_of_le (hP p hp) hle) hUfix (hctxeq.symm ▸ hbodyD)
  refine ⟨R, hR, ?_, hRP, fun v hv => (hUagree v hv).trans (hag v (Nat.lt_of_lt_of_le hv hle))⟩
  rw [Subst.onTy_arrow, ← hresult]
  congr 1
  have hp := Subst.onTy_congr hag (hs.belowFvars hK)
  rw [Subst.onTy_append, hUparam] at hp
  exact hp

theorem _root_.Infer.principal_app
    (hf : Infer K frontier ctx f first s1 fOut fTy)
    (ha : Infer K first (s1.onCtx ctx) arg second s2 argOut argTy)
    (hu : RigidUnify K (s2.onTy fTy) (.arrow argTy (.fvar second)) s3)
    (ihf : Infer.Principal hf) (iha : Infer.Principal ha) :
    Infer.Principal (.app hf ha hu) := by
  intro hwf hbelow hK ambient target P hS hP hfix htyping
  obtain ⟨paramD, hfD, haD⟩ := htyping.app_inv
  obtain ⟨Rf, hRf, hfTy, hRfP, hagf⟩ := ihf hwf hbelow hK ambient
    (.arrow paramD target) P hS hP hfix hfD
  have hfle := hf.frontier_le
  have hale := ha.frontier_le
  obtain ⟨hfB, hs1B⟩ := hf.belowFvars hbelow hK
  obtain ⟨_, hs1lc⟩ := hf.lc hwf
  have hctx1 := Subst.onCtx_below hs1B hfle hbelow
  have hK1 : ∀ k ∈ K, k < first := fun k hk => Nat.lt_of_lt_of_le (hK k hk) hfle
  have hP1 : ∀ p ∈ P, p < first := fun p hp => Nat.lt_of_lt_of_le (hP p hp) hfle
  have hctxeq : ambient.onCtx ctx = Rf.onCtx (s1.onCtx ctx) := by
    rw [← Subst.onCtx_append]
    exact Subst.onCtx_congr hagf hbelow
  obtain ⟨Ra, hRa, haTy, hRaP, haga⟩ := iha (Subst.onCtx_wf hs1lc hwf) hctx1 hK1
    Rf paramD P hRf hP1 hRfP (hctxeq ▸ haD)
  obtain ⟨haB, hs2B⟩ := ha.belowFvars hctx1 hK1
  have hleftB := Subst.onTy_belowFvars hs2B (hfB.mono hale)
  have hleft : Ra.onTy (s2.onTy fTy) = .arrow paramD target := by
    have heq := Subst.onTy_congr haga hfB
    rw [Subst.onTy_append, ← hfTy] at heq
    exact heq.symm
  have htargetlc := htyping.regular
  obtain ⟨U, hU, hUagree, hUblock⟩ := Subst.override_block hRa second [target]
    (by simpa using htargetlc)
  have hUret : U.onTy (.fvar second) = target := by simpa using hUblock 0 (by simp)
  have hUP : ∀ p ∈ P, U.onTy (.fvar p) = .fvar p := fun p hp =>
    (hUagree p (Nat.lt_of_lt_of_le (hP1 p hp) hale)).symm.trans (hRaP p hp)
  have hUni : Unifies U (s2.onTy fTy) (.arrow argTy (.fvar second)) := by
    change U.onTy (s2.onTy fTy) = U.onTy (.arrow argTy (.fvar second))
    rw [← Subst.onTy_congr hUagree hleftB, hleft, Subst.onTy_arrow,
      ← Subst.onTy_congr hUagree haB, ← haTy, hUret]
  obtain ⟨R, hfac, hR, hRP⟩ := hu.unifies.greatest_K U hU hUni hUP
  have hag3 : Subst.AgreesBelow second Ra (s3 ++ R) := by
    intro v hv
    rw [Subst.onTy_append]
    exact (hUagree v hv).trans (hfac (.fvar v))
  have hag2 := Subst.AgreesBelow.trans_append hale haga hs2B hag3
  have hag1 := Subst.AgreesBelow.trans_append hfle hagf hs1B hag2
  refine ⟨R, hR, ?_, hRP, ?_⟩
  · exact hUret.symm.trans (hfac (.fvar second))
  · simpa only [List.append_assoc] using hag1

theorem LetCheck.factor {P : List Nat} (hc : LetCheck K first rhsTy ann checked sCheck)
    (hK : ∀ k ∈ K, k < first) (hP : ∀ p ∈ P, p < first)
    (hty : Ty.BelowFvars first rhsTy)
    {R : Subst} (hR : ∀ pair ∈ R, pair.2.IsLC)
    (hRP : ∀ p ∈ P, R.onTy (.fvar p) = .fvar p)
    {target : Ty} (htarget : target.IsLC) (hfit : ann.FitsMono target)
    (hrigid : ∀ template, ann = .template template → ∀ v ∈ template.rigidVars, v ∈ P)
    (heq : target = R.onTy rhsTy) :
    ∃ V : Subst, (∀ pair ∈ V, pair.2.IsLC) ∧
      target = V.onTy (sCheck.onTy rhsTy) ∧
      (∀ p ∈ P, V.onTy (.fvar p) = .fvar p) ∧
      Subst.AgreesBelow first R (sCheck ++ V) := by
  cases hc with
  | absent => exact ⟨R, hR, heq, hRP, fun _ _ => rfl⟩
  | hole => exact ⟨R, hR, heq, hRP, fun _ _ => rfl⟩
  | @template checked expected sCheck template halloc _ hr hu =>
    change template.Fits target at hfit
    obtain ⟨U, hU, hag, hUexpected⟩ := hfit.allocate_override htarget hR first
      (fun v hv => hK v (hr v hv)) (fun v hv => hRP v (hrigid template rfl v hv))
    rw [halloc] at hUexpected
    have hUty : U.onTy rhsTy = target := (Subst.onTy_congr hag hty).symm.trans heq.symm
    have hUP : ∀ p ∈ P, U.onTy (.fvar p) = .fvar p := by
      intro p hp
      exact (hag p (hP p hp)).symm.trans (hRP p hp)
    obtain ⟨V, hfac, hV, hVP⟩ := hu.unifies.greatest_K U hU
      (hUty.trans hUexpected.symm) hUP
    refine ⟨V, hV, hUty.symm.trans (hfac rhsTy), hVP, ?_⟩
    intro v hv
    simpa only [Subst.onTy_append] using (hag v hv).trans (hfac (.fvar v))

/-- Cofinite RHS comparison after its partial annotation has been checked.
The context and protected-variable image premises are semantic frames, shared
by residual principality and producer completeness. -/
theorem genScheme_generalizes {K : List Nat} {ctx : Ctx} {ty : Ty}
    {V : Subst} {M : PolyTy} {Xs : List Nat}
    (hty : ty.IsLC) (hV : ∀ pair ∈ V, pair.2.IsLC) (hM : M.WF)
    (hXnodup : Xs.Nodup) (hXlen : Xs.length = M.paramCount)
    (hXM : ∀ x ∈ Xs, x ∉ M.body.freeVars)
    (htarget : M.openVars Xs = V.onTy ty)
    (hXctx : ∀ x ∈ Xs, x ∉ (V.onCtx ctx).env.freeVars)
    (hXK : ∀ x ∈ Xs, ∀ k ∈ K, x ∉ (V.onTy (.fvar k)).freeVars) :
    (V.onPolyTy (genScheme K ctx.env ty)).Generalizes M := by
  apply closeOver_generalizes hty hV hM hXnodup hXlen hXM htarget
  intro x hx hcx
  rw [Subst.onPolyTy, Ty.mem_freeVars_onTy_iff] at hcx
  obtain ⟨v, hv, hxv⟩ := hcx
  have hvty := Ty.closeOver_freeVars_subset hv
  have hvnot : v ∉ genVars K ctx.env ty := fun hg => Ty.not_mem_closeOver_freeVars hg hv
  have hor : v ∈ ctx.env.freeVars ∨ v ∈ K := by
    by_cases he : v ∈ ctx.env.freeVars
    · exact .inl he
    · by_cases hk : v ∈ K
      · exact .inr hk
      · exfalso
        apply hvnot
        simp only [genVars, List.mem_filter, Bool.and_eq_true]
        exact ⟨hvty, by simpa using he, by simpa using hk⟩
  rcases hor with henv | hk
  · obtain ⟨scheme, hs, hv⟩ := Env.mem_freeVars_iff.mp henv
    apply hXctx x hx
    apply Env.mem_freeVars_iff.mpr
    refine ⟨V.onPolyTy scheme, List.mem_map.mpr ⟨scheme, hs, rfl⟩, ?_⟩
    exact Ty.mem_freeVars_onTy_iff.mpr ⟨v, hv, hxv⟩
  · exact hXK x hx v hk hxv

/-- Reconcile a checked ordinary RHS with a declarative let scheme, then
transport its continuation. Shared by both completeness directions. -/
theorem _root_.Infer.let_frame
    (hr : Infer K frontier ctx rhs first s1 rhsOut rhsTy)
    (hc : LetCheck K first rhsTy ann checked sCheck)
    (ihr : Infer.Principal hr) :
    CtxWF ctx → CtxBelow frontier ctx → (∀ k ∈ K, k < frontier) →
    ∀ (ambient : Subst) (target : Ty) (P : List Nat),
      (∀ pair ∈ ambient, pair.2.IsLC) → (∀ p ∈ P, p < frontier) →
      (∀ p ∈ P, ambient.onTy (.fvar p) = .fvar p) →
      Typing P (ambient.onCtx ctx) (.letIn ann rhs body) target →
      ∃ V : Subst, (∀ pair ∈ V, pair.2.IsLC) ∧
        (∀ p ∈ P, V.onTy (.fvar p) = .fvar p) ∧
        Subst.AgreesBelow frontier ambient (s1 ++ sCheck ++ V) ∧
        Typing P (V.onCtx { (sCheck.onCtx (s1.onCtx ctx)) with
        env := genScheme K (sCheck.onCtx (s1.onCtx ctx)).env (sCheck.onTy rhsTy) ::
          (sCheck.onCtx (s1.onCtx ctx)).env }) body target ∧
        CtxWF { (sCheck.onCtx (s1.onCtx ctx)) with
        env := genScheme K (sCheck.onCtx (s1.onCtx ctx)).env (sCheck.onTy rhsTy) ::
          (sCheck.onCtx (s1.onCtx ctx)).env } ∧ CtxBelow checked { (sCheck.onCtx (s1.onCtx ctx)) with
        env := genScheme K (sCheck.onCtx (s1.onCtx ctx)).env (sCheck.onTy rhsTy) ::
          (sCheck.onCtx (s1.onCtx ctx)).env } ∧
        (∀ pair ∈ s1 ++ sCheck, Ty.BelowFvars checked pair.2) := by
  intro hwf hbelow hK ambient target P hS hP hfix htyping
  obtain ⟨M, L, hM, hannRigid, hannFits, hrD, hbD⟩ := htyping.letMono_inv hc.fits
  let images := K.flatMap (fun k => (ambient.onTy (.fvar k)).freeVars)
  obtain ⟨Xs, hXlen, hXnd, hXavoid⟩ := exists_fresh_names
    (L ++ M.body.freeVars ++ (ambient.onCtx ctx).env.freeVars ++ images) M.paramCount
  have hXfresh : FreshNames L M.paramCount Xs := ⟨hXlen, hXnd, by
    intro x hx hc; exact hXavoid x hx (by simp only [List.mem_append]; tauto)⟩
  have hXM : ∀ x ∈ Xs, x ∉ M.body.freeVars := by
    intro x hx hc; exact hXavoid x hx (by simp only [List.mem_append]; tauto)
  have hXctx : ∀ x ∈ Xs, x ∉ (ambient.onCtx ctx).env.freeVars := by
    intro x hx hc; exact hXavoid x hx (by simp only [List.mem_append]; tauto)
  have hXimages : ∀ x ∈ Xs, ∀ k ∈ K, x ∉ (ambient.onTy (.fvar k)).freeVars := by
    intro x hx k hk hc
    exact hXavoid x hx (by
      simp only [List.mem_append]; right
      exact List.mem_flatMap.mpr ⟨k, hk, hc⟩)
  obtain ⟨R, hR, hrTy, hRP, hagR⟩ := ihr hwf hbelow hK ambient
    (M.openVars Xs) P hS hP hfix (hrD Xs hXfresh)
  have hrle := hr.frontier_le
  have hcle := hc.frontier_le
  have hK1 : ∀ k ∈ K, k < first := fun k hk => Nat.lt_of_lt_of_le (hK k hk) hrle
  have hP1 : ∀ p ∈ P, p < first := fun p hp => Nat.lt_of_lt_of_le (hP p hp) hrle
  obtain ⟨hrB, hs1B⟩ := hr.belowFvars hbelow hK
  obtain ⟨hrLC, hs1LC⟩ := hr.lc hwf
  obtain ⟨V, hV, hcheckedTy, hVP, hagV⟩ := hc.factor hK1 hP1 hrB hR hRP
    ((hrD Xs hXfresh).regular) (hannFits Xs hXfresh) hannRigid hrTy
  have hsCheckLC := hc.lc hrLC
  have hsCheckB := hc.belowFvars hrB hK1
  have hprefixB : ∀ pair ∈ s1 ++ sCheck, Ty.BelowFvars checked pair.2 := by
    intro pair hp
    exact (List.mem_append.mp hp).elim (fun hp => (hs1B pair hp).mono hcle) (hsCheckB pair)
  have hagPrefix := Subst.AgreesBelow.trans_append hrle hagR hs1B hagV
  have hctxBridge : V.onCtx (sCheck.onCtx (s1.onCtx ctx)) = ambient.onCtx ctx := by
    rw [← Subst.onCtx_append, ← Subst.onCtx_append]
    simpa only [List.append_assoc] using (Subst.onCtx_congr hagPrefix hbelow).symm
  have hprefixFix : ∀ k ∈ K, (s1 ++ sCheck).onTy (.fvar k) = .fvar k := by
    apply Subst.fixes_of_dom_avoids
    intro pair hp
    exact (List.mem_append.mp hp).elim (hr.dom_avoids pair) (hc.dom_avoids pair)
  have hVimages : ∀ x ∈ Xs, ∀ k ∈ K, x ∉ (V.onTy (.fvar k)).freeVars := by
    intro x hx k hk
    have heq := hagPrefix k (hK k hk)
    rw [Subst.onTy_append, hprefixFix k hk] at heq
    rw [← heq]
    exact hXimages x hx k hk
  have hcheckedLC := Subst.onTy_lc hsCheckLC hrLC
  have hgen := genScheme_generalizes (ctx := sCheck.onCtx (s1.onCtx ctx)) hcheckedLC hV hM hXnd hXlen hXM hcheckedTy
    (by simpa only [hctxBridge] using hXctx) hVimages
  have hbodyWeak := Typing.weaken_schemes (env := (ambient.onCtx ctx).env)
    (.cons hgen .nil) hbD
  have hbodyD : Typing P (V.onCtx
      { (sCheck.onCtx (s1.onCtx ctx)) with
        env := genScheme K (sCheck.onCtx (s1.onCtx ctx)).env (sCheck.onTy rhsTy) ::
          (sCheck.onCtx (s1.onCtx ctx)).env }) body target := by
    rw [← hctxBridge] at hbodyWeak
    exact hbodyWeak
  have hcheckedWF := Subst.onCtx_wf hsCheckLC (Subst.onCtx_wf hs1LC hwf)
  have hcheckedB := Subst.onCtx_below hsCheckB hcle
    (Subst.onCtx_below hs1B hrle hbelow)
  have hcheckedTyB := Subst.onTy_belowFvars hsCheckB (hrB.mono hcle)
  have hbodyWF : CtxWF { (sCheck.onCtx (s1.onCtx ctx)) with
      env := genScheme K (sCheck.onCtx (s1.onCtx ctx)).env (sCheck.onTy rhsTy) ::
        (sCheck.onCtx (s1.onCtx ctx)).env } := by
    intro scheme hs
    rcases List.mem_cons.mp hs with rfl | hs
    · exact genScheme_wf hcheckedLC
    · exact hcheckedWF scheme hs
  have hbodyB : CtxBelow checked { (sCheck.onCtx (s1.onCtx ctx)) with
      env := genScheme K (sCheck.onCtx (s1.onCtx ctx)).env (sCheck.onTy rhsTy) ::
        (sCheck.onCtx (s1.onCtx ctx)).env } := by
    intro scheme hs
    rcases List.mem_cons.mp hs with rfl | hs
    · exact hcheckedTyB.closeOver
    · exact hcheckedB scheme hs
  exact ⟨V, hV, hVP, hagPrefix, hbodyD, hbodyWF, hbodyB, hprefixB⟩

theorem _root_.Infer.principal_letIn
    (hr : Infer K frontier ctx rhs first s1 rhsOut rhsTy)
    (hc : LetCheck K first rhsTy ann checked sCheck)
    (hb : Infer K checked
      { (sCheck.onCtx (s1.onCtx ctx)) with
        env := genScheme K (sCheck.onCtx (s1.onCtx ctx)).env (sCheck.onTy rhsTy) ::
          (sCheck.onCtx (s1.onCtx ctx)).env }
      body next s2 bodyOut bodyTy)
    (ihr : Infer.Principal hr) (ihb : Infer.Principal hb) :
    Infer.Principal (.letIn hr hc hb) := by
  intro hwf hbelow hK ambient target P hS hP hfix htyping
  obtain ⟨V, hV, hVP, hagPrefix, hbodyD, hbodyWF, hbodyB, hprefixB⟩ :=
    hr.let_frame hc ihr hwf hbelow hK ambient target P hS hP hfix htyping
  have hle := hr.frontier_le.trans hc.frontier_le
  obtain ⟨R2, hR2, hresult, hR2P, hag2⟩ := ihb hbodyWF hbodyB
    (fun k hk => Nat.lt_of_lt_of_le (hK k hk) hle) V target P hV
    (fun p hp => Nat.lt_of_lt_of_le (hP p hp) hle) hVP hbodyD
  exact ⟨R2, hR2, hresult, hR2P,
    Subst.AgreesBelow.trans_append hle hagPrefix hprefixB hag2⟩

/-- Residual factorization for a nonempty branch thread. The independent
protected set scopes authored annotations; both common type images are explicit. -/
def _root_.InferBranches.Principal
    (_h : InferBranches K frontier ctx scrutTy resultTy branches next subst completed)
    (_hne : branches ≠ []) : Prop :=
  CtxWF ctx → CtxBelow frontier ctx → (∀ k ∈ K, k < frontier) →
  ∀ (ambient : Subst) (scrutD resultD : Ty) (P : List Nat),
    (∀ pair ∈ ambient, pair.2.IsLC) → scrutD.IsLC → scrutTy.IsLC → resultTy.IsLC →
    Ty.BelowFvars frontier scrutTy → Ty.BelowFvars frontier resultTy →
    (∀ p ∈ P, p < frontier) →
    (∀ p ∈ P, ambient.onTy (.fvar p) = .fvar p) →
    resultD = ambient.onTy resultTy → scrutD = ambient.onTy scrutTy →
    (∀ b ∈ branches, BranchTyping Typing P (ambient.onCtx ctx) b scrutD resultD) →
    ∃ residual : Subst, (∀ pair ∈ residual, pair.2.IsLC) ∧
      Subst.AgreesBelow frontier ambient (subst ++ residual) ∧
      (∀ p ∈ P, residual.onTy (.fvar p) = .fvar p) ∧
      resultD = residual.onTy (subst.onTy resultTy)

theorem _root_.Infer.principal_match
    (hs : Infer K frontier ctx scrut first s1 scrutOut scrutTy)
    (hne : branches ≠ [])
    (hb : InferBranches K (first + 1) (s1.onCtx ctx) scrutTy (.fvar first)
      branches next s2 branchesOut)
    (ihs : Infer.Principal hs) (ihb : InferBranches.Principal hb hne) :
    Infer.Principal (.match_ hs hne hb) := by
  intro hwf hbelow hK ambient target P hS hP hfix htyping
  obtain ⟨scrutD, hsD, _, hbD⟩ := htyping.match_inv
  obtain ⟨R1, hR1, hscrut, hR1P, hag1⟩ := ihs hwf hbelow hK ambient
    scrutD P hS hP hfix hsD
  have hle := hs.frontier_le
  obtain ⟨hsB, hs1B⟩ := hs.belowFvars hbelow hK
  obtain ⟨hsLC, hs1LC⟩ := hs.lc hwf
  have hctxWF := Subst.onCtx_wf hs1LC hwf
  have hctxB := Subst.onCtx_below hs1B hle hbelow
  obtain ⟨U, hU, hagU, hblock⟩ := Subst.override_block hR1 first [target]
    (by simpa using htyping.regular)
  have hUtarget : U.onTy (.fvar first) = target := by simpa using hblock 0 (by simp)
  have hctxeq : U.onCtx (s1.onCtx ctx) = ambient.onCtx ctx := by
    trans R1.onCtx (s1.onCtx ctx)
    · exact (Subst.onCtx_congr hagU hctxB).symm
    · rw [← Subst.onCtx_append]
      exact (Subst.onCtx_congr hag1 hbelow).symm
  have hUP : ∀ p ∈ P, U.onTy (.fvar p) = .fvar p := fun p hp =>
    (hagU p (Nat.lt_of_lt_of_le (hP p hp) hle)).symm.trans (hR1P p hp)
  have hUst : scrutD = U.onTy scrutTy :=
    hscrut.trans (Subst.onTy_congr hagU hsB)
  obtain ⟨R2, hR2, hag2, hR2P, htarget⟩ := ihb hctxWF
    (fun M hM => (hctxB M hM).mono (by omega))
    (fun k hk => by have := hK k hk; omega) U scrutD target P hU hsD.regular hsLC .fvar
    (hsB.mono (by omega)) (.fvar (by omega))
    (fun p hp => by have := hP p hp; omega) hUP hUtarget.symm hUst
    (by simpa only [hctxeq] using hbD)
  have hag2' : Subst.AgreesBelow first R1 (s2 ++ R2) := fun v hv =>
    (hagU v hv).trans (hag2 v (by omega))
  exact ⟨R2, hR2, htarget, hR2P, Subst.AgreesBelow.trans_append hle hag1 hs1B hag2'⟩

/-- Factor a named branch's constructor constraint while transporting its
independent body typing into the algorithm's instantiated field context. -/
theorem BranchTyping.factor_named
    {Φ : Nat} {ctx : Ctx} {c : CtorName} {nbr : Nat} {ctor : Ctor}
    {scrutTy scruT₀ ρe : Ty} {S₀ S₀amb : Subst} {K : List Nat} {body : Input}
    (hlook : LookupList.get? ctx.ctors c = some ctor)
    (h₀ : UnifyRel scrutTy
      (.customTy ctor.tyName ((freshVars Φ ctor.paramCount).map Ty.fvar)) S₀)
    (hbelow : CtxBelow Φ ctx) (hbscrut : Ty.BelowFvars Φ scrutTy)
    (hS₀amb : ∀ pair ∈ S₀amb, pair.2.IsLC) (hscruLC : scruT₀.IsLC)
    (hKΦ : ∀ k ∈ K, k < Φ) (hKfix : ∀ k ∈ K, S₀amb.onTy (.fvar k) = .fvar k)
    (hIMGscru : scruT₀ = S₀amb.onTy scrutTy)
    (hdhead : BranchTyping Typing K (S₀amb.onCtx ctx) (.named c nbr, body) scruT₀ ρe) :
    ∃ R₀ : Subst, (∀ pair ∈ R₀, pair.2.IsLC) ∧
      (∀ k ∈ K, R₀.onTy (.fvar k) = .fvar k) ∧
      Subst.AgreesBelow Φ S₀amb (S₀ ++ R₀) ∧
      Typing K (R₀.onCtx { S₀.onCtx ctx with
        env := (ctor.contents.map (Ty.openWith
          (((freshVars Φ ctor.paramCount).map Ty.fvar).map S₀.onTy))).map PolyTy.mkTrivial ++
            (S₀.onCtx ctx).env }) body ρe := by
  cases hdhead with
  | named hspec hbodyty =>
    rename_i ctorE tyArgsE instContentsE
    let bodyCtx : Ctx := { S₀amb.onCtx ctx with
      env := instContentsE.map PolyTy.mkTrivial ++ (S₀amb.onCtx ctx).env }
    have hctxdef : bodyCtx = { S₀amb.onCtx ctx with
      env := instContentsE.map PolyTy.mkTrivial ++ (S₀amb.onCtx ctx).env } := rfl
    have hctorE : ctorE =  ctor := by
      have hl : LookupList.get? (S₀amb.onCtx ctx).ctors c = some ( ctor) := by
        simpa [Subst.onCtx] using hlook
      exact Option.some.inj (hspec.lookup.symm.trans hl)
    have htyArgs_lc : ∀ t ∈ tyArgsE, t.IsLC := by
      have hlc : (Ty.customTy ctor.tyName tyArgsE).IsLC := by
        simpa [hctorE, hspec.scrut_eq] using hscruLC
      cases hlc with | customTy h => exact h
    have hpc' : ctor.paramCount = tyArgsE.length := by
      simpa [hctorE] using hspec.arity
    have hscrutImg' : Eq (.customTy ctor.tyName tyArgsE) (S₀amb.onTy scrutTy) := by
      simpa [hctorE, hspec.scrut_eq] using hIMGscru
    have hinstsE : instContentsE = ctorE.contents.map (Ty.openWith tyArgsE) := by
      refine List.ext_getElem ?_ ?_
      · rw [List.length_map]
        exact hspec.fields.length_eq.symm
      · intro i hi _
        have hlen₂ : i < ctorE.contents.length := hspec.fields.length_eq.symm ▸ hi
        have hinst := hspec.fields.get hlen₂ hi
        rw [List.get_eq_getElem, List.get_eq_getElem] at hinst
        rw [List.getElem_map]
        have hpc'' : tyArgsE.length = ctorE.paramCount := hspec.arity.symm
        exact InstantiatesBy.eq_openWith hinst (ctorE.bound _ (List.getElem_mem hlen₂)) hpc''
    obtain ⟨R₀, hR₀, hR₀K, hAgree₀, hmap₀⟩ :=
      customTy_factor_dodge (R := S₀amb) (S₀ := S₀) (ctor := ctor) (tyArgs := tyArgsE)
        h₀ hbscrut hS₀amb hKΦ hKfix hpc' htyArgs_lc hscrutImg'
    have hAgreeBelow₀ : Subst.AgreesBelow Φ S₀amb (S₀ ++ R₀) :=
      fun v hv => by rw [Subst.onTy_append]; exact hAgree₀ v hv
    let bodyCtxAlg : Ctx := { (S₀.onCtx ctx) with
        env := (ctor.contents.map (Ty.openWith
            (((freshVars Φ ctor.paramCount).map (Ty.fvar ·)).map S₀.onTy))).map PolyTy.mkTrivial
          ++ (S₀.onCtx ctx).env }
    have hctx0 : (R₀.onCtx (S₀.onCtx ctx)) = (S₀amb.onCtx ctx) := by
      rw [← Subst.onCtx_append]
      exact (Subst.onCtx_congr hAgreeBelow₀ hbelow).symm
    have hinstsE_direct :
        instContentsE =
          ctor.contents.map (fun c => Ty.openWith tyArgsE c) := by
      simpa [hctorE] using hinstsE
    have hbodyCtxEq : (R₀.onCtx bodyCtxAlg) = bodyCtx := by
      calc
        (R₀.onCtx bodyCtxAlg)
            = { (R₀.onCtx (S₀.onCtx ctx)) with
                env := (( ctor).contents.map
                  (fun c => Ty.openWith tyArgsE c)).map PolyTy.mkTrivial
                    ++ (R₀.onCtx (S₀.onCtx ctx)).env } := by
          rw [Subst.onCtx_branchBindings hR₀]
          rw [hmap₀]
        _ = { (S₀amb.onCtx ctx) with
                env := (( ctor).contents.map
                  (fun c => Ty.openWith tyArgsE c)).map PolyTy.mkTrivial
                    ++ (S₀amb.onCtx ctx).env } := by
          rw [hctx0]
        _ = bodyCtx := by
          rw [hctxdef]
          simp [hinstsE_direct]
    have hbE : Typing K bodyCtx body ( ρe) := by
      exact hbodyty
    have hbE' : Typing K (R₀.onCtx bodyCtxAlg) body ( ρe) := by
      rwa [← hbodyCtxEq] at hbE
    exact ⟨R₀, hR₀, hR₀K, hAgreeBelow₀, hbE'⟩

theorem _root_.InferBranches.nil_det
    (h : InferBranches κ Φ ctx st rt [] Φ' S out) : Φ' = Φ ∧ S = [] := by
  cases h
  exact ⟨rfl, rfl⟩

theorem _root_.InferBranches.principal_of_body
    (h : InferBranches κ Φ ctx scrutTy ρ brs Φ' S out) (hne : brs ≠ [])
    (bodyIH : ∀ b ∈ brs, ∀ {f c n s o t} (hb : Infer κ f c b.2 n s o t), Infer.Principal hb) :
    InferBranches.Principal h hne := by
  induction brs generalizing Φ ctx scrutTy ρ Φ' S out with
  | nil => exact False.elim (hne rfl)
  | cons head rest ih =>
    cases h with
      | @cons c ctor nbr _ _ _ S₀ _ body Φ₁ S₁ bodyOut τb _ S₂ _ _ S₃ restOut hlook hn h₀Rigid hinfbody h₂Rigid hrest =>
        have h₀ := h₀Rigid.unifies
        have h₂ := h₂Rigid.unifies
        exact fun hwf hbelow hκ S₀amb scruT₀ ρe K hS₀amb hscruLC hscrutLC hρLC hbscrut hbρ hKΦ hKfix hIMGρ hIMGscru hbrs => by
          obtain ⟨R₀, hR₀, hR₀K, hAgreeBelow₀, hbE'⟩ :=
            BranchTyping.factor_named hlook h₀ hbelow hbscrut hS₀amb hscruLC hKΦ hKfix hIMGscru
              (hbrs (.named c nbr, body) (List.mem_cons_self ..))
          have hS₀lc : ∀ p ∈ S₀, p.2.IsLC :=
            UnifyRel.lc h₀ hscrutLC (by
              apply ContainsBvarsUpTo.customTy
              intro t ht
              obtain ⟨x, _, rfl⟩ := List.mem_map.mp ht
              exact ContainsBvarsUpTo.fvar)
          have hS₀_bel : ∀ p ∈ S₀, Ty.BelowFvars (Φ + ctor.paramCount) p.2 :=
            UnifyRel.belowFvars h₀ (hbscrut.mono (by omega)) (by
              apply Ty.BelowFvars.customTy
              intro t ht
              obtain ⟨x, hx, rfl⟩ := List.mem_map.mp ht
              exact Ty.BelowFvars.fvar (by have := freshVars_lt x hx; omega))
          have hfle₀ : Φ ≤ Φ + ctor.paramCount := by omega
          let bodyCtxAlg : Ctx := { (S₀.onCtx ctx) with
              env := (ctor.contents.map (Ty.openWith
                  (((freshVars Φ ctor.paramCount).map (Ty.fvar ·)).map S₀.onTy))).map PolyTy.mkTrivial
                ++ (S₀.onCtx ctx).env }
          have hwf_body : CtxWF bodyCtxAlg := by
            dsimp [bodyCtxAlg]
            refine branchBindings_wf (ctorr := ctor)
              (ta := ((freshVars Φ ctor.paramCount).map (Ty.fvar ·)).map S₀.onTy)
              (Subst.onCtx_wf hS₀lc hwf) ?_ (by simp)
            intro t ht
            obtain ⟨v, hv, rfl⟩ := List.mem_map.mp ht
            obtain ⟨x, _, rfl⟩ := List.mem_map.mp hv
            exact Subst.onTy_lc hS₀lc ContainsBvarsUpTo.fvar
          have hbelow_body : CtxBelow (Φ + ctor.paramCount) bodyCtxAlg := by
            dsimp [bodyCtxAlg]
            refine branchBindings_below (ctorr := ctor)
              (ta := ((freshVars Φ ctor.paramCount).map (Ty.fvar ·)).map S₀.onTy)
              (Subst.onCtx_below hS₀_bel hfle₀ hbelow) ?_
            intro t ht
            obtain ⟨v, hv, rfl⟩ := List.mem_map.mp ht
            obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hv
            exact Subst.onTy_belowFvars hS₀_bel (.fvar (by have := freshVars_lt x hx; omega))
          have hKΦ₀ : ∀ k ∈ K, k < Φ + ctor.paramCount := fun k hk => lt_of_lt_of_le (hKΦ k hk) hfle₀
          obtain ⟨R_b, hR_b, htyb, hR_bK, hagb⟩ :=
            (bodyIH (.named c nbr, body) (List.mem_cons_self ..) hinfbody)
              hwf_body hbelow_body (fun k hk => Nat.lt_of_lt_of_le (hκ k hk) hfle₀)
              R₀ ρe K hR₀ hKΦ₀ hR₀K hbE'
          have hle_b : Φ + ctor.paramCount ≤ Φ₁ := Infer.frontier_le hinfbody
          have hKΦ₁ : ∀ k ∈ K, k < Φ₁ := fun k hk => lt_of_lt_of_le (hKΦ₀ k hk) hle_b
          have hbodyLC := Infer.lc hinfbody hwf_body
          have hτb_lc : τb.IsLC := hbodyLC.1
          have hS₁lc : ∀ p ∈ S₁, p.2.IsLC := hbodyLC.2
          have hbb := Infer.belowFvars hinfbody hbelow_body (fun k hk => Nat.lt_of_lt_of_le (hκ k hk) hfle₀)
          have hτb_bel : Ty.BelowFvars Φ₁ τb := hbb.1
          have hS₁_bel : ∀ p ∈ S₁, Ty.BelowFvars Φ₁ p.2 := hbb.2
          have htyb' : Eq ρe (R_b.onTy τb) :=
            htyb
          have hρbel₁ : Ty.BelowFvars (Φ + ctor.paramCount) (S₀.onTy ρ) :=
            Subst.onTy_belowFvars hS₀_bel (hbρ.mono hfle₀)
          have hρImg₀ : Eq ρe (R₀.onTy (S₀.onTy ρ)) := by
            rw [← Subst.onTy_append]
            exact Eq.trans hIMGρ (Subst.onTy_congr hAgreeBelow₀ hbρ)
          have hρImg_b : Eq ρe (R_b.onTy (S₁.onTy (S₀.onTy ρ))) := by
            rw [← Subst.onTy_append]
            exact Eq.trans hρImg₀ (Subst.onTy_congr hagb hρbel₁)
          have hUni : Unifies R_b τb (S₁.onTy (S₀.onTy ρ)) := by
            show Eq (R_b.onTy τb) (R_b.onTy (S₁.onTy (S₀.onTy ρ)))
            exact Eq.trans (Eq.symm htyb') hρImg_b
          obtain ⟨R_u, hR_u_fac, hR_u, hR_uK⟩ :=
            UnifyRel.greatest_K h₂ R_b hR_b hUni hR_bK
          have hS₂lc : ∀ p ∈ S₂, p.2.IsLC :=
            UnifyRel.lc h₂ hτb_lc (Subst.onTy_lc hS₁lc (Subst.onTy_lc hS₀lc hρLC))
          have hS₂_bel : ∀ p ∈ S₂, Ty.BelowFvars Φ₁ p.2 :=
            UnifyRel.belowFvars h₂ hτb_bel
              (Subst.onTy_belowFvars hS₁_bel
                ((Subst.onTy_belowFvars hS₀_bel (hbρ.mono hfle₀)).mono hle_b))
          have hAgreeUni : Subst.AgreesBelow Φ₁ R_b (S₂ ++ R_u) :=
            fun v hv => by rw [Subst.onTy_append]; exact hR_u_fac (Ty.fvar v)
          have hρImg_u : Eq ρe (R_u.onTy (S₂.onTy (S₁.onTy (S₀.onTy ρ)))) :=
            Eq.trans hρImg_b (hR_u_fac (S₁.onTy (S₀.onTy ρ)))
          have hwf' : CtxWF (S₂.onCtx (S₁.onCtx (S₀.onCtx ctx))) :=
            Subst.onCtx_wf hS₂lc (Subst.onCtx_wf hS₁lc (Subst.onCtx_wf hS₀lc hwf))
          have hbelow' : CtxBelow Φ₁ (S₂.onCtx (S₁.onCtx (S₀.onCtx ctx))) :=
            Subst.onCtx_below hS₂_bel (le_refl _)
              (Subst.onCtx_below hS₁_bel hle_b
                (Subst.onCtx_below hS₀_bel hfle₀ hbelow))
          have hbscrut' : Ty.BelowFvars Φ₁ (S₂.onTy (S₁.onTy (S₀.onTy scrutTy))) :=
            Subst.onTy_belowFvars hS₂_bel
              (Subst.onTy_belowFvars hS₁_bel
                ((Subst.onTy_belowFvars hS₀_bel (hbscrut.mono hfle₀)).mono hle_b))
          have hbρ' : Ty.BelowFvars Φ₁ (S₂.onTy (S₁.onTy (S₀.onTy ρ))) :=
            Subst.onTy_belowFvars hS₂_bel
              (Subst.onTy_belowFvars hS₁_bel
                ((Subst.onTy_belowFvars hS₀_bel (hbρ.mono hfle₀)).mono hle_b))
          have hscrutTy'lc : (S₂.onTy (S₁.onTy (S₀.onTy scrutTy))).IsLC :=
            Subst.onTy_lc hS₂lc (Subst.onTy_lc hS₁lc (Subst.onTy_lc hS₀lc hscrutLC))
          have hρ'lc : (S₂.onTy (S₁.onTy (S₀.onTy ρ))).IsLC :=
            Subst.onTy_lc hS₂lc (Subst.onTy_lc hS₁lc (Subst.onTy_lc hS₀lc hρLC))
          have hScrutStep1 : Eq (S₀amb.onTy scrutTy) (R₀.onTy (S₀.onTy scrutTy)) := by
            rw [← Subst.onTy_append]
            exact Subst.onTy_congr hAgreeBelow₀ hbscrut
          have hScrutStep2 : Eq (R₀.onTy (S₀.onTy scrutTy))
              (R_b.onTy (S₁.onTy (S₀.onTy scrutTy))) := by
            simpa [Subst.onTy_append] using
              (Subst.onTy_congr hagb (Subst.onTy_belowFvars hS₀_bel (hbscrut.mono hfle₀)))
          have hScrutStep3 : Eq (R_b.onTy (S₁.onTy (S₀.onTy scrutTy)))
              (R_u.onTy (S₂.onTy (S₁.onTy (S₀.onTy scrutTy)))) := by
            simpa [Subst.onTy_append] using (hR_u_fac (S₁.onTy (S₀.onTy scrutTy)))
          have hscrutImg' : Eq scruT₀ (R_u.onTy (S₂.onTy (S₁.onTy (S₀.onTy scrutTy)))) :=
            Eq.trans hIMGscru (Eq.trans hScrutStep1 (Eq.trans hScrutStep2 hScrutStep3))
          have hctxeq' : (R_u.onCtx (S₂.onCtx (S₁.onCtx (S₀.onCtx ctx))))
              = (S₀amb.onCtx ctx) := by
            have h1 : (R_u.onCtx (S₂.onCtx (S₁.onCtx (S₀.onCtx ctx))))
                = (R_b.onCtx (S₁.onCtx (S₀.onCtx ctx))) := by
              rw [← Subst.onCtx_append]
              exact (Subst.onCtx_congr hAgreeUni
                (Subst.onCtx_below hS₁_bel hle_b
                  (Subst.onCtx_below hS₀_bel hfle₀ hbelow))).symm
            have hAgree01 : Subst.AgreesBelow Φ S₀amb ((S₀ ++ S₁) ++ R_b) :=
              @Subst.AgreesBelow.trans_append Φ (Φ + ctor.paramCount) S₀amb S₀ R₀ S₁ R_b
                hfle₀ hAgreeBelow₀ hS₀_bel hagb
            have h2 : (R_b.onCtx (S₁.onCtx (S₀.onCtx ctx)))
                = (S₀amb.onCtx ctx) := by
              simpa [Subst.onCtx_append, List.append_assoc] using
                (Subst.onCtx_congr hAgree01 hbelow).symm
            exact h1.trans h2
          have hbr' : ∀ br ∈ rest, BranchTyping Typing K (R_u.onCtx (S₂.onCtx (S₁.onCtx (S₀.onCtx ctx))))
              (br.1, br.2) scruT₀ ρe := by
            intro br hbr
            rw [hctxeq']
            exact hbrs br (List.mem_cons_of_mem _ hbr)
          by_cases hrestNe : rest = []
          · -- rest = []: the rest derivation is `nil`, so S₃ = [] and Φ₂ = Φ₁.
            subst hrestNe
            have hnil := InferBranches.nil_det hrest
            have hAgree1 : Subst.AgreesBelow Φ S₀amb ((S₀ ++ S₁ ++ S₂) ++ R_u) := by
              have hA : Subst.AgreesBelow Φ S₀amb ((S₀ ++ (S₁ ++ S₂)) ++ R_u) :=
                @Subst.AgreesBelow.trans_append Φ (Φ + ctor.paramCount) S₀amb S₀ R₀ (S₁ ++ S₂) R_u
                  hfle₀ hAgreeBelow₀ hS₀_bel
                  (@Subst.AgreesBelow.trans_append (Φ + ctor.paramCount) Φ₁ R₀ S₁ R_b S₂ R_u
                    hle_b hagb hS₁_bel hAgreeUni)
              simpa [List.append_assoc] using hA
            rw [hnil.2]
            refine ⟨R_u, hR_u, by simpa [List.append_assoc, List.append_nil] using hAgree1, hR_uK, ?_⟩
            · simpa [Subst.onTy_append, List.append_assoc, List.append_nil] using hρImg_u
          · -- rest ≠ []: recurse with the tier IH.
            have hrestNe' : rest ≠ [] := hrestNe
            obtain ⟨R_r, hR_r, hAgreeRest, hR_rK, htyRest⟩ :=
              ih hrest hrestNe' (fun b hb => bodyIH b (List.mem_cons_of_mem _ hb))
                hwf' hbelow' (fun k hk => Nat.lt_of_lt_of_le (hκ k hk) (by omega)) R_u scruT₀ ρe K
                hR_u hscruLC hscrutTy'lc hρ'lc hbscrut' hbρ' hKΦ₁ hR_uK hρImg_u hscrutImg' hbr'
            have hAgree1 : Subst.AgreesBelow Φ₁ R_u (S₃ ++ R_r) := hAgreeRest
            have hAgree01 : Subst.AgreesBelow Φ S₀amb ((S₀ ++ S₁ ++ S₂) ++ R_u) := by
              have hA : Subst.AgreesBelow Φ S₀amb ((S₀ ++ (S₁ ++ S₂)) ++ R_u) :=
                @Subst.AgreesBelow.trans_append Φ (Φ + ctor.paramCount) S₀amb S₀ R₀ (S₁ ++ S₂) R_u
                  hfle₀ hAgreeBelow₀ hS₀_bel
                  (@Subst.AgreesBelow.trans_append (Φ + ctor.paramCount) Φ₁ R₀ S₁ R_b S₂ R_u
                    hle_b hagb hS₁_bel hAgreeUni)
              simpa [List.append_assoc] using hA
            have hAgree : Subst.AgreesBelow Φ S₀amb ((S₀ ++ S₁ ++ S₂ ++ S₃) ++ R_r) := by
              have hA : Subst.AgreesBelow Φ S₀amb (((S₀ ++ S₁ ++ S₂) ++ S₃) ++ R_r) :=
                @Subst.AgreesBelow.trans_append Φ Φ₁ S₀amb (S₀ ++ S₁ ++ S₂) R_u S₃ R_r (by omega)
                  hAgree01
                  (fun p hp => by
                    rcases List.mem_append.mp hp with hp | hp
                    · rcases List.mem_append.mp hp with hp | hp
                      · exact (hS₀_bel p hp).mono hle_b
                      · exact hS₁_bel p hp
                    · exact hS₂_bel p hp)
                  hAgreeRest
              simpa [List.append_assoc] using hA
            refine ⟨R_r, hR_r, hAgree, hR_rK, ?_⟩
            · simpa [Subst.onTy_append] using htyRest
      | @consWild _ _ _ body Φ₁ S₁ bodyOut τb _ S₂ _ _ _ S₃ restOut hinfbody h₂Rigid hrest =>
        have h₂ := h₂Rigid.unifies
        exact fun hwf hbelow hκ S₀amb scruT₀ ρe K hS₀amb hscruLC hscrutLC hρLC hbscrut hbρ hKΦ hKfix hIMGρ hIMGscru hbrs => by
          have hdhead := hbrs (.wildcard, body) (List.mem_cons_self ..)
          have hbodyD : Typing K (S₀amb.onCtx ctx) body ρe := by
            cases hdhead with
            | wildcard hbodyty => exact hbodyty
          obtain ⟨R_b, hR_b, htyb, hR_bK, hagb⟩ :=
            (bodyIH (.wildcard, body) (List.mem_cons_self ..) hinfbody)
              hwf hbelow hκ S₀amb ρe K hS₀amb hKΦ hKfix hbodyD
          have hle_b : Φ ≤ Φ₁ := Infer.frontier_le hinfbody
          have hKΦ₁ : ∀ k ∈ K, k < Φ₁ := fun k hk => lt_of_lt_of_le (hKΦ k hk) hle_b
          have hbodyLC := Infer.lc hinfbody hwf
          have hτb_lc : τb.IsLC := hbodyLC.1
          have hS₁lc : ∀ p ∈ S₁, p.2.IsLC := hbodyLC.2
          have hbb := Infer.belowFvars hinfbody hbelow hκ
          have hτb_bel : Ty.BelowFvars Φ₁ τb := hbb.1
          have hS₁_bel : ∀ p ∈ S₁, Ty.BelowFvars Φ₁ p.2 := hbb.2
          have hρImg_b : Eq ρe (R_b.onTy (S₁.onTy ρ)) := by
            rw [← Subst.onTy_append]
            exact Eq.trans hIMGρ (Subst.onTy_congr hagb hbρ)
          have hUni : Unifies R_b τb (S₁.onTy ρ) := by
            show Eq (R_b.onTy τb) (R_b.onTy (S₁.onTy ρ))
            exact Eq.trans (Eq.symm htyb) hρImg_b
          obtain ⟨R_u, hR_u_fac, hR_u, hR_uK⟩ :=
            UnifyRel.greatest_K h₂ R_b hR_b hUni hR_bK
          have hS₂lc : ∀ p ∈ S₂, p.2.IsLC :=
            UnifyRel.lc h₂ hτb_lc (Subst.onTy_lc hS₁lc hρLC)
          have hS₂_bel : ∀ p ∈ S₂, Ty.BelowFvars Φ₁ p.2 :=
            UnifyRel.belowFvars h₂ hτb_bel (Subst.onTy_belowFvars hS₁_bel (hbρ.mono hle_b))
          have hAgreeUni : Subst.AgreesBelow Φ₁ R_b (S₂ ++ R_u) :=
            fun v hv => by rw [Subst.onTy_append]; exact hR_u_fac (Ty.fvar v)
          have hρImg_u : Eq ρe (R_u.onTy (S₂.onTy (S₁.onTy ρ))) :=
            Eq.trans hρImg_b (hR_u_fac (S₁.onTy ρ))
          have hwf' : CtxWF (S₂.onCtx (S₁.onCtx ctx)) :=
            Subst.onCtx_wf hS₂lc (Subst.onCtx_wf hS₁lc hwf)
          have hbelow' : CtxBelow Φ₁ (S₂.onCtx (S₁.onCtx ctx)) :=
            Subst.onCtx_below hS₂_bel (le_refl _) (Subst.onCtx_below hS₁_bel hle_b hbelow)
          have hbscrut' : Ty.BelowFvars Φ₁ (S₂.onTy (S₁.onTy scrutTy)) :=
            Subst.onTy_belowFvars hS₂_bel (Subst.onTy_belowFvars hS₁_bel (hbscrut.mono hle_b))
          have hbρ' : Ty.BelowFvars Φ₁ (S₂.onTy (S₁.onTy ρ)) :=
            Subst.onTy_belowFvars hS₂_bel (Subst.onTy_belowFvars hS₁_bel (hbρ.mono hle_b))
          have hscrutTy'lc : (S₂.onTy (S₁.onTy scrutTy)).IsLC :=
            Subst.onTy_lc hS₂lc (Subst.onTy_lc hS₁lc hscrutLC)
          have hρ'lc : (S₂.onTy (S₁.onTy ρ)).IsLC :=
            Subst.onTy_lc hS₂lc (Subst.onTy_lc hS₁lc hρLC)
          have hScrutStep1 : Eq (S₀amb.onTy scrutTy) (R_b.onTy (S₁.onTy scrutTy)) := by
            simpa [Subst.onTy_append] using (Subst.onTy_congr hagb hbscrut)
          have hScrutStep2 : Eq (R_b.onTy (S₁.onTy scrutTy))
              (R_u.onTy (S₂.onTy (S₁.onTy scrutTy))) := by
            simpa [Subst.onTy_append] using (hR_u_fac (S₁.onTy scrutTy))
          have hscrutImg' : Eq scruT₀ (R_u.onTy (S₂.onTy (S₁.onTy scrutTy))) :=
            Eq.trans hIMGscru (Eq.trans hScrutStep1 hScrutStep2)
          have hctxeq' : (R_u.onCtx (S₂.onCtx (S₁.onCtx ctx)))
              = (S₀amb.onCtx ctx) := by
            have h1 : (R_u.onCtx (S₂.onCtx (S₁.onCtx ctx)))
                = (R_b.onCtx (S₁.onCtx ctx)) := by
              rw [← Subst.onCtx_append]
              exact (Subst.onCtx_congr hAgreeUni (Subst.onCtx_below hS₁_bel hle_b hbelow)).symm
            have h2 : (R_b.onCtx (S₁.onCtx ctx)) = (S₀amb.onCtx ctx) := by
              rw [← Subst.onCtx_append]
              exact (Subst.onCtx_congr hagb hbelow).symm
            exact h1.trans h2
          have hbr' : ∀ br ∈ rest, BranchTyping Typing K (R_u.onCtx (S₂.onCtx (S₁.onCtx ctx)))
              (br.1, br.2) scruT₀ ρe := by
            intro br hbr
            rw [hctxeq']
            exact hbrs br (List.mem_cons_of_mem _ hbr)
          by_cases hrestNe : rest = []
          · subst hrestNe
            have hnil := InferBranches.nil_det hrest
            have hAgree : Subst.AgreesBelow Φ S₀amb ((S₁ ++ S₂) ++ R_u) :=
              @Subst.AgreesBelow.trans_append Φ Φ₁ S₀amb S₁ R_b S₂ R_u hle_b hagb hS₁_bel hAgreeUni
            rw [hnil.2]
            refine ⟨R_u, hR_u, by simpa [List.append_assoc, List.append_nil] using hAgree, hR_uK, ?_⟩
            · simpa [Subst.onTy_append, List.append_assoc, List.append_nil] using hρImg_u
          · have hrestNe' : rest ≠ [] := hrestNe
            obtain ⟨R_r, hR_r, hAgreeRest, hR_rK, htyRest⟩ :=
              ih hrest hrestNe' (fun b hb => bodyIH b (List.mem_cons_of_mem _ hb))
                hwf' hbelow' (fun k hk => Nat.lt_of_lt_of_le (hκ k hk) hle_b) R_u scruT₀ ρe K
                hR_u hscruLC hscrutTy'lc hρ'lc hbscrut' hbρ' hKΦ₁ hR_uK hρImg_u hscrutImg' hbr'
            have hAgree : Subst.AgreesBelow Φ S₀amb ((S₁ ++ S₂ ++ S₃) ++ R_r) := by
              have hA : Subst.AgreesBelow Φ S₀amb (((S₁ ++ S₂) ++ S₃) ++ R_r) :=
                @Subst.AgreesBelow.trans_append Φ Φ₁ S₀amb (S₁ ++ S₂) R_u S₃ R_r hle_b
                  (@Subst.AgreesBelow.trans_append Φ Φ₁ S₀amb S₁ R_b S₂ R_u hle_b hagb hS₁_bel hAgreeUni)
                  (fun p hp => by
                    rcases List.mem_append.mp hp with hp | hp
                    · exact hS₁_bel p hp
                    · exact hS₂_bel p hp)
                  hAgreeRest
              simpa [List.append_assoc] using hA
            refine ⟨R_r, hR_r, hAgree, hR_rK, ?_⟩
            · simpa [Subst.onTy_append] using htyRest

private theorem branch_size_lt {branch : MatchPattern × Input}
    (h : branch ∈ branches) : branch.2.size < sizeBranches branches := by
  induction branches with
  | nil => cases h
  | cons head rest ih =>
    rcases List.mem_cons.mp h with rfl | h
    · simp only [sizeBranches]; omega
    · have := ih h; simp only [sizeBranches]; omega

/-- Every elaboration is principal for independent input typings, retaining
ordinary Core's residual factorization and protected-set guarantees. -/
theorem _root_.Infer.principal (h : Infer K frontier ctx input next subst output ty) :
    Infer.Principal h := by
  match h with
  | .backend hemb hi hctx hK hr => exact Infer.principal_backend hemb hi hctx hK hr
  | .lambda hs hb => exact Infer.principal_lambda hs hb hb.principal
  | .app hf ha hu => exact Infer.principal_app hf ha hu hf.principal ha.principal
  | .letIn hr hc hb => exact Infer.principal_letIn hr hc hb hr.principal hb.principal
  | .match_ hs hne hb =>
      exact Infer.principal_match hs hne hb hs.principal
        (hb.principal_of_body hne (fun b hm {_ _ _ _ _ _} hi => hi.principal))
termination_by input.size
decreasing_by
  all_goals (simp only [Input.size]; first | omega | have := branch_size_lt hm; omega)

end Elaboration
