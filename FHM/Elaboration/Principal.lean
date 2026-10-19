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
  | @letSignature K ctx body bodyTy ann rhs M L hwf hann hrhs hfits _ _ ihr ihb =>
    simp only [Input.toCore, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at hc
    obtain ⟨ann', ha, rhs', hr, body', hb, rfl⟩ := hc
    obtain ⟨Xs, hlen, hnd, hav⟩ := exists_fresh_names L M.paramCount
    have hXs : FreshNames L M.paramCount Xs := ⟨hlen, hnd, hav⟩
    have hfit := hfits Xs hXs
    cases ann with
    | absent => cases hfit
    | template => cases hfit
    | partialForall => cases ha
    | complete scheme =>
      cases ha
      cases hfit
      obtain ⟨htb, hsb⟩ := ihb hb
      refine ⟨.letIn (L := L) hwf (fun _ heq => Option.some.inj heq) ?_ rfl htb, ?_⟩
      · intro fresh hf
        have htake : fresh.take M.paramCount = fresh := by
          exact List.take_of_length_le hf.length.le
        have hemb := rhs.toCore_openTyVars hr (fresh.take M.paramCount)
        have ht := (ihr fresh hf hemb).1
        simpa only [htake, Expr.openBoundTyVars] using ht
      · intro v hv
        rcases List.mem_append.mp hv with hprefix | hv
        · rcases List.mem_append.mp hprefix with hv | hv
          · exact hann v hv
          · exact hrhs v ((Input.toCore_rigidVars rhs hr v).mpr hv)
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
    (hmode : ann.isSignature = false) :
    ∃ (M : PolyTy) (L : List Nat), M.WF ∧
      (∀ template, ann = .template template → ∀ v ∈ template.rigidVars, v ∈ K) ∧
      (∀ Xs, FreshNames L M.paramCount Xs → ann.FitsMono (M.openVars Xs)) ∧
      (∀ Xs, FreshNames L M.paramCount Xs → Typing K ctx rhs (M.openVars Xs)) ∧
      Typing K { ctx with env := M :: ctx.env } body ty := by
  cases h with
  | letIn hwf hr hf htr htb => exact ⟨_, _, hwf, hr, hf, htr, htb⟩
  | @letSignature _ _ _ _ _ _ M L _ _ _ hfit _ _ =>
    obtain ⟨Xs, hlen, hnd, hav⟩ := exists_fresh_names L M.paramCount
    have hs := hfit Xs ⟨hlen, hnd, hav⟩
    have := hs.isSignature
    rw [hmode] at this
    cases this
  | complete hemb hscope ht =>
    simp only [Input.toCore, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at hemb
    obtain ⟨ann', ha, rhs', hr, body', hb, rfl⟩ := hemb
    cases ann with
    | complete => cases hmode
    | partialForall => cases hmode
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
    obtain ⟨M, L, hwf, _, _, hr, hb⟩ := h.letMono_inv rfl
    exact .letIn hwf (fun _ heq => by cases heq) (fun _ _ => True.intro) hr hb
  · intro h
    obtain ⟨M, L, hwf, _, _, hr, hb⟩ := h.letMono_inv rfl
    refine .letIn hwf ?_ (fun _ _ => .hole) hr hb
    intro template heq; cases heq
    simp only [Template.rigidVars, List.not_mem_nil, false_implies, implies_true]


/-- Signed-let inversion retains the full candidate scheme, including any
additional declarative quantifiers after the authored prefix. -/
theorem Typing.signature_inv (h : Typing K ctx (.letIn ann rhs body) ty)
    (hmode : ann.isSignature = true) :
    ∃ (M : PolyTy) (L : List Nat), M.WF ∧
      (∀ v ∈ ann.rigidVars, v ∈ K) ∧ (∀ v ∈ rhs.rigidVars, v ∈ K) ∧
      (∀ Xs, FreshNames L M.paramCount Xs → ann.SignatureFits M Xs) ∧
      (∀ Xs, FreshNames L M.paramCount Xs →
        Typing (K ++ Xs.take ann.paramCount) ctx (rhs.openTyVars (Xs.take ann.paramCount)) (M.openVars Xs)) ∧
      Typing K { ctx with env := M :: ctx.env } body ty := by
  cases h with
  | letSignature hwf hann hrhs hfit htr htb => exact ⟨_, _, hwf, hann, hrhs, hfit, htr, htb⟩
  | @letIn _ _ _ _ _ _ M L _ _ hfit _ _ =>
      obtain ⟨Xs, hlen, hnd, hav⟩ := exists_fresh_names L M.paramCount
      have hmono := hfit Xs ⟨hlen, hnd, hav⟩
      cases ann with
      | absent => cases hmode
      | template => cases hmode
      | complete => cases hmono
      | partialForall => cases hmono
  | complete hemb hscope ht =>
      simp only [Input.toCore, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at hemb
      obtain ⟨ann', ha, rhs', hr, body', hb, rfl⟩ := hemb
      cases ann with
      | absent => cases hmode
      | template => cases hmode
      | partialForall => cases ha
      | complete scheme =>
          cases ha
          cases ht with
          | @letIn _ _ _ _ _ _ M L hwf hpin hgen hctx hbody =>
              subst hctx
              have hM : M = scheme := hpin scheme rfl
              subst M
              have hrhsScope : ∀ v ∈ rhs'.tyFreeVars, v ∈ K := fun v hv =>
                hscope v (List.mem_append_left _ (List.mem_append_right _ hv))
              refine ⟨scheme, L, hwf, ?_, ?_, ?_, ?_, .complete hb ?_ hbody⟩
              · intro v hv
                exact hscope v (List.mem_append_left _ (List.mem_append_left _ hv))
              · intro v hv
                exact hrhsScope v ((Input.toCore_rigidVars rhs hr v).mp hv)
              · intro Xs hXs; exact .complete
              · intro Xs hXs
                have htake : Xs.take scheme.paramCount = Xs := List.take_of_length_le hXs.length.le
                refine .complete (rhs.toCore_openTyVars hr (Xs.take scheme.paramCount)) ?_ ?_
                · intro v hv
                  rcases Expr.tyFreeVars_openTyVars hv with hv | hv
                  · exact List.mem_append_left _ (hrhsScope v hv)
                  · exact List.mem_append_right _ hv
                · simpa only [htake, Expr.openBoundTyVars] using hgen Xs hXs
              · intro v hv; exact hscope v (List.mem_append_right _ hv)


/-- Move candidate occurrences of an algorithmic skolem block out to fresh
scratch space. The conjugated ambient fixes the algorithmic skolems, agrees
with forward-renaming the old ambient below the block, and maps back exactly.
Only scratch freshness is required; candidate types may contain the whole
algorithmic block. `avoid` can include an algorithm's final allocated range. -/
theorem signed_candidate_dodge (S : Subst) (hS : ∀ p ∈ S, p.2.IsLC)
    (N count : Nat) (targets : List Ty) (avoid : List Nat) :
    ∃ W, N + count ≤ W ∧ (∀ v ∈ avoid, v < W) ∧
      (∀ p ∈ Subst.conj (blockSwap N W count) S, p.2.IsLC) ∧
      (∀ y ∈ freshVars N count,
        (Subst.conj (blockSwap N W count) S).onTy (.fvar y) = .fvar y) ∧
      (∀ v, v < N →
        (blockList N W count).onTy (.fvar v) = .fvar v ∧
        (blockListBack N W count).onTy (.fvar v) = .fvar v) ∧
      (∀ τ, Ty.BelowFvars N τ →
        (Subst.conj (blockSwap N W count) S).onTy τ =
          (blockList N W count).onTy (S.onTy τ)) ∧
      (∀ τ, Ty.BelowFvars N τ →
        (blockListBack N W count).onTy
          ((Subst.conj (blockSwap N W count) S).onTy τ) = S.onTy τ) ∧
      (∀ τ ∈ targets,
        (blockListBack N W count).onTy ((blockList N W count).onTy τ) = τ ∧
        ∀ y ∈ freshVars N count, y ∉ ((blockList N W count).onTy τ).freeVars) := by
  obtain ⟨W, hd, hfresh⟩ := exists_fresh_block
    (S.map Prod.fst ++ S.flatMap (fun p => p.2.freeVars) ++ targets.flatMap Ty.freeVars ++ avoid) N count
  have hkeys : ∀ p ∈ S, p.1 < W := fun p hp =>
    hfresh p.1 (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
      (List.mem_map.mpr ⟨p, hp, rfl⟩))))
  have hranges : ∀ p ∈ S, Ty.BelowFvars W p.2 := by
    intro p hp
    apply Ty.BelowFvars.of_freeVars_lt
    intro v hv
    exact hfresh v (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _
      (List.mem_flatMap.mpr ⟨p, hp, hv⟩))))
  have hSscratch : ∀ τ, Ty.BelowFvars N τ →
      ∀ v ∈ (S.onTy τ).freeVars, ¬ (W ≤ v ∧ v < W + count) := by
    intro τ hτ v hv
    have hlt := (Subst.onTy_belowFvars hranges (hτ.mono (by omega))).mem_lt v hv
    omega
  have hforward : ∀ τ, Ty.BelowFvars N τ →
      (Subst.conj (blockSwap N W count) S).onTy τ = (blockList N W count).onTy (S.onTy τ) := by
    intro τ hτ
    have hrename : Ty.rename (blockSwap N W count) τ = τ :=
      Ty.rename_eq_self (fun v hv => blockSwap_lt (by omega) (hτ.mem_lt v hv))
    have hconj := Subst.onTy_conj (blockSwap_injective hd) S τ
    rw [hrename] at hconj
    exact hconj.trans (blockList_onTy hd (hSscratch τ hτ)).symm
  refine ⟨W, hd, fun v hv => hfresh v (List.mem_append_right _ hv), Subst.conj_lc hS, ?_, ?_, hforward, ?_, ?_⟩
  · intro y hy
    apply Ty.substFvars_eq_self_of_no_key
    intro p hp hc
    simp only [Subst.conj, List.mem_map] at hp
    obtain ⟨q, hq, rfl⟩ := hp
    have hqlt := hkeys q hq
    have hyge := freshVars_ge y hy
    have hylt := freshVars_lt y hy
    simp only [Ty.freeVars, List.mem_singleton, blockSwap] at hc
    split_ifs at hc <;> omega
  · intro v hv
    constructor
    · apply Ty.substFvars_eq_self_of_no_key
      intro p hp hc
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hp
      simp only [Ty.freeVars, List.mem_singleton] at hc
      omega
    · apply Ty.substFvars_eq_self_of_no_key
      intro p hp hc
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hp
      simp only [Ty.freeVars, List.mem_singleton] at hc
      omega
  · intro τ hτ
    rw [hforward τ hτ, blockList_onTy hd (hSscratch τ hτ)]
    exact blockListBack_onTy_rename hd (hSscratch τ hτ)
  · intro τ hτ
    have hτscratch : ∀ v ∈ τ.freeVars, ¬ (W ≤ v ∧ v < W + count) := by
      intro v hv
      have hlt := hfresh v (List.mem_append_left _ (List.mem_append_right _
        (List.mem_flatMap.mpr ⟨τ, hτ, hv⟩)))
      omega
    rw [blockList_onTy hd hτscratch]
    exact ⟨blockListBack_onTy_rename hd hτscratch, fun y hy =>
      blockSwap_rename_not_mem hd hτscratch y (freshVars_ge y hy) (freshVars_lt y hy)⟩

/-- Internal source-transforming residual theorem. The local freeze premise
concerns authored frozen leaves only; unrelated K/context variables may vary. -/
def _root_.Infer.SourcePrincipal (_h : Infer K F frontier ctx input next subst output ty) : Prop :=
  CtxWF ctx → CtxBelow frontier ctx → (∀ k ∈ K, k < frontier) →
  (∀ soft ∈ F, Ty.BelowFvars frontier soft) →
  ∀ (ambient : Subst) (target : Ty) (P : List Nat),
    (∀ pair ∈ ambient, pair.2.IsLC) → (∀ p ∈ P, p < frontier) →
    (∀ p ∈ P, ambient.onTy (.fvar p) = .fvar p) →
    (∀ v ∈ input.rigidVars, v ∈ K → v ∉ softVars F → ambient.onTy (.fvar v) = .fvar v) →
    Typing P (ambient.onCtx ctx) (input.substTyFvars ambient) target →
    ∃ residual : Subst, (∀ pair ∈ residual, pair.2.IsLC) ∧
      target = residual.onTy ty ∧
      (∀ p ∈ P, residual.onTy (.fvar p) = .fvar p) ∧
      Subst.AgreesBelow frontier ambient (subst ++ residual)

/-- Residual principality retains an independently quantified protected set.
`Typing P` scopes authored fixed types in precisely that protected set. It does
not claim most-general fillings for every unused annotation hole. -/
def _root_.Infer.Principal (_h : Infer K F frontier ctx input next subst output ty) : Prop :=
  CtxWF ctx → CtxBelow frontier ctx → (∀ k ∈ K, k < frontier) →
  (∀ soft ∈ F, Ty.BelowFvars frontier soft) →
  ∀ (ambient : Subst) (target : Ty) (P : List Nat),
    (∀ pair ∈ ambient, pair.2.IsLC) → (∀ p ∈ P, p < frontier) →
    (∀ p ∈ P, ambient.onTy (.fvar p) = .fvar p) →
    Typing P (ambient.onCtx ctx) input target →
    ∃ residual : Subst, (∀ pair ∈ residual, pair.2.IsLC) ∧
      target = residual.onTy ty ∧
      (∀ p ∈ P, residual.onTy (.fvar p) = .fvar p) ∧
      Subst.AgreesBelow frontier ambient (subst ++ residual)

theorem _root_.Infer.SourcePrincipal.principal {h : Infer K F frontier ctx input next subst output ty}
    (ih : Infer.SourcePrincipal h) : Infer.Principal h := by
  intro hwf hctx hK hF ambient target P hS hP hfix ht
  have heq := input.substTyFvars_eq_self_of_fixes (fun v hv => hfix v (ht.rigidVars v hv))
  exact ih hwf hctx hK hF ambient target P hS hP hfix
    (fun v hv _ _ => hfix v (ht.rigidVars v hv)) (heq.symm ▸ ht)

theorem Seed.override (h : Seed K frontier ann param initial)
    (hK : ∀ k ∈ K, k < frontier) {target : Ty} (htarget : target.IsLC)
    {ambient : Subst} (hlc : ∀ pair ∈ ambient, pair.2.IsLC)
    (hfit : ∀ template, ann = some template → (template.substTyFvars ambient).Fits target) :
    ∃ U : Subst, (∀ pair ∈ U, pair.2.IsLC) ∧
      Subst.AgreesBelow frontier ambient U ∧ U.onTy param = target := by
  cases h with
  | absent =>
    obtain ⟨U, hU, hag, hb⟩ := Subst.override_block hlc frontier [target] (by simpa using htarget)
    exact ⟨U, hU, hag, by simpa using hb 0 (by simp)⟩
  | @annotated next ty template heq _ hr =>
    obtain ⟨U, hU, hag, ht⟩ := (hfit template rfl).allocate_override_source htarget hlc frontier
      (fun v hv => hK v (hr v hv))
    rw [heq] at ht
    exact ⟨U, hU, hag, ht⟩

/-- The local source freeze is stable under solving and factoring. A source
leaf that originated in F remains marked by the full substituted F image. -/
theorem SourceScope.residual_freeze {K : List Nat} {F : List Ty} {input : Input} {frontier : Nat}
    {ambient solved residual : Subst}
    (hscope : SourceScope K F input)
    (hbelow : ∀ v ∈ input.rigidVars, v < frontier)
    (hsolved : ∀ k ∈ K, solved.onTy (.fvar k) = .fvar k)
    (hfreeze : ∀ v ∈ input.rigidVars, v ∈ K → v ∉ softVars F → ambient.onTy (.fvar v) = .fvar v)
    (hagree : Subst.AgreesBelow frontier ambient (solved ++ residual)) :
    ∀ v ∈ (input.substTyFvars solved).rigidVars,
      v ∈ K → v ∉ softVars (substSoft solved F) → residual.onTy (.fvar v) = .fvar v := by
  intro v hv _ hnot
  obtain ⟨original, horiginal, himage⟩ := input.rigidVars_substTyFvars hv
  have horiginalNotF : original ∉ softVars F := by
    intro hin
    exact hnot (mem_softVars_substSoft.mpr ⟨original, hin, himage⟩)
  have horiginalK : original ∈ K := (List.mem_append.mp (hscope original horiginal)).resolve_right horiginalNotF
  have hfixed := hsolved original horiginalK
  rw [hfixed] at himage
  have heq : v = original := List.mem_singleton.mp himage
  subst v
  have hag := hagree original (hbelow original horiginal)
  rw [Subst.onTy_append, hfixed, hfreeze original horiginal horiginalK horiginalNotF] at hag
  exact hag.symm

theorem _root_.Infer.sourcePrincipal_backend {input : Input} {core : Expr}
    (hemb : input.toCore = some core)
    (h : CoreBackend.Infer K frontier ctx core next subst ty)
    (hctx : CtxBelow frontier ctx) (hK : ∀ k ∈ K, k < frontier)
    (hr : ∀ v ∈ core.tyFreeVars, v ∈ K)
    (hdisj : ∀ v ∈ core.tyFreeVars, v ∉ softVars F) :
    Infer.SourcePrincipal (.backend hemb h hctx hK hr hdisj) := by
  intro hwf hb _ _ ambient target P hlc hP hfix hfreeze ht
  have heq : input.substTyFvars ambient = input := input.substTyFvars_eq_self_of_fixes (by
    intro v hv
    have hcore := (input.toCore_rigidVars hemb v).mp hv
    exact hfreeze v hv (hr v hcore) (hdisj v hcore))
  rw [heq] at ht
  obtain ⟨ht, hscope⟩ := ht.toCore hemb
  exact h.principal hwf hb ambient target P hlc hP hscope hfix ht

theorem _root_.Infer.sourcePrincipal_lambda {ctx : Ctx}
    (hscope : SourceScope K F (.lambda ann body))
    (hs : Seed (K ++ softVars F) frontier ann param initial)
    (hb : Infer K F initial { ctx with env := PolyTy.mkTrivial param :: ctx.env }
      body next subst completed bodyTy)
    (ih : Infer.SourcePrincipal hb) : Infer.SourcePrincipal (.lambda hscope hs hb) := by
  intro hwf hbelow hK hF ambient target P hS hP hfix hfreeze htyping
  obtain ⟨paramD, resultD, rfl, hparamD, hfit, _, hbodyD⟩ := htyping.lambda_inv
  have hscopeBound : ∀ v ∈ K ++ softVars F, v < frontier :=
    fun v hv => (List.mem_append.mp hv).elim (hK v) (softVars_lt hF v)
  have hbodyBound : ∀ v ∈ body.rigidVars, v < frontier :=
    fun v hv => hscopeBound v (hscope v (List.mem_append_right _ hv))
  obtain ⟨U, hU, hUagree, hUparam⟩ := hs.override hscopeBound hparamD hS (by
    intro t ht
    subst ann
    exact hfit (t.substTyFvars ambient) rfl)
  have hle := hs.frontier_le
  have hbodywf : CtxWF { ctx with env := PolyTy.mkTrivial param :: ctx.env } := by
    intro M hM
    rcases List.mem_cons.mp hM with rfl | hM
    · exact hs.lc
    · exact hwf M hM
  have hbodybelow : CtxBelow initial { ctx with env := PolyTy.mkTrivial param :: ctx.env } := by
    intro M hM
    rcases List.mem_cons.mp hM with rfl | hM
    · exact hs.belowFvars hscopeBound
    · exact (hbelow M hM).mono hle
  have hctxeq : U.onCtx { ctx with env := PolyTy.mkTrivial param :: ctx.env } =
      { ambient.onCtx ctx with env := PolyTy.mkTrivial paramD :: (ambient.onCtx ctx).env } := by
    have heq := Subst.onCtx_congr hUagree hbelow
    simpa only [Subst.onCtx, Subst.onEnv, List.map_cons, Subst.onPolyTy, PolyTy.mkTrivial,
      hUparam] using congrArg (fun c : Ctx => { c with env := PolyTy.mkTrivial paramD :: c.env }) heq.symm
  have hsourceeq : body.substTyFvars U = body.substTyFvars ambient :=
    body.substTyFvars_congr (fun v hv => (hUagree v (hbodyBound v hv)).symm)
  have hUfix : ∀ p ∈ P, U.onTy (.fvar p) = .fvar p :=
    fun p hp => (hUagree p (hP p hp)).symm.trans (hfix p hp)
  obtain ⟨R, hR, hresult, hRP, hag⟩ := ih hbodywf hbodybelow
    (fun k hk => Nat.lt_of_lt_of_le (hK k hk) hle)
    (fun t ht => (hF t ht).mono hle) U resultD P hU
    (fun p hp => Nat.lt_of_lt_of_le (hP p hp) hle) hUfix
    (fun v hv hk hnot => (hUagree v (hbodyBound v hv)).symm.trans
      (hfreeze v (List.mem_append_right _ hv) hk hnot)) (by rwa [hctxeq, hsourceeq])
  refine ⟨R, hR, ?_, hRP, fun v hv => (hUagree v hv).trans (hag v (Nat.lt_of_lt_of_le hv hle))⟩
  rw [Subst.onTy_arrow, ← hresult]
  congr 1
  have hp := Subst.onTy_congr hag (hs.belowFvars hscopeBound)
  rw [Subst.onTy_append, hUparam] at hp
  exact hp

theorem _root_.Infer.sourcePrincipal_app
    (hscope : SourceScope K F (.app f arg))
    (hf : Infer K F frontier ctx f first s1 fOut fTy)
    (ha : Infer K (substSoft s1 F) first (s1.onCtx ctx) (arg.substTyFvars s1) second s2 argOut argTy)
    (hu : RigidUnify K (s2.onTy fTy) (.arrow argTy (.fvar second)) s3)
    (ihf : Infer.SourcePrincipal hf) (iha : Infer.SourcePrincipal ha) :
    Infer.SourcePrincipal (.app hscope hf ha hu) := by
  intro hwf hbelow hK hF ambient target P hS hP hfix hfreeze htyping
  obtain ⟨paramD, hfD, haD⟩ := htyping.app_inv
  obtain ⟨Rf, hRf, hfTy, hRfP, hagf⟩ := ihf hwf hbelow hK hF ambient
    (.arrow paramD target) P hS hP hfix
    (fun v hv => hfreeze v (List.mem_append_left _ hv)) hfD
  have hfle := hf.frontier_le
  have hale := ha.frontier_le
  obtain ⟨hfB, hs1B⟩ := hf.belowFvars hbelow hK hF
  obtain ⟨_, hs1lc⟩ := hf.lc hwf
  have hctx1 := Subst.onCtx_below hs1B hfle hbelow
  have hK1 : ∀ k ∈ K, k < first := fun k hk => Nat.lt_of_lt_of_le (hK k hk) hfle
  have hP1 : ∀ p ∈ P, p < first := fun p hp => Nat.lt_of_lt_of_le (hP p hp) hfle
  have hctxeq : ambient.onCtx ctx = Rf.onCtx (s1.onCtx ctx) := by
    rw [← Subst.onCtx_append]
    exact Subst.onCtx_congr hagf hbelow
  have hargScope : SourceScope K F arg := fun v hv => hscope v (List.mem_append_right _ hv)
  have hargBelow : ∀ v ∈ arg.rigidVars, v < frontier := fun v hv =>
    (List.mem_append.mp (hargScope v hv)).elim (hK v) (softVars_lt hF v)
  have hF1 := substSoft_below hs1B hfle hF
  have hsourceeq : arg.substTyFvars ambient = (arg.substTyFvars s1).substTyFvars Rf := by
    rw [← Input.substTyFvars_append]
    exact arg.substTyFvars_congr (fun v hv => hagf v (hargBelow v hv))
  have hfreeze1 := hargScope.residual_freeze hargBelow (Subst.fixes_of_dom_avoids hf.dom_avoids)
    (fun v hv => hfreeze v (List.mem_append_right _ hv)) hagf
  obtain ⟨Ra, hRa, haTy, hRaP, haga⟩ := iha (Subst.onCtx_wf hs1lc hwf) hctx1 hK1 hF1
    Rf paramD P hRf hP1 hRfP hfreeze1 (by rwa [← hctxeq, ← hsourceeq])
  obtain ⟨haB, hs2B⟩ := ha.belowFvars hctx1 hK1 hF1
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





mutual
theorem Template.substTyFvars_openTyVarsFrom_of_fixes (template : Template) {S : Subst} {Xs : List Nat}
    (hlc : ∀ p ∈ S, p.2.IsLC)
    (hfix : ∀ x ∈ Xs, S.onTy (.fvar x) = .fvar x) (depth : Nat) :
    (template.openTyVarsFrom depth Xs).substTyFvars S =
      (template.substTyFvars S).openTyVarsFrom depth Xs := by
  cases template with
  | fixed ty => exact congrArg Template.fixed (Subst.onTy_openVarsFrom_of_fixes hlc hfix ty depth)
  | hole => rfl
  | arrow a b =>
    simp only [Template.openTyVarsFrom, Template.substTyFvars,
      a.substTyFvars_openTyVarsFrom_of_fixes hlc hfix depth,
      b.substTyFvars_openTyVarsFrom_of_fixes hlc hfix depth]
  | custom name args =>
    exact congrArg (Template.custom name) (templateList_open_subst_of_fixes args hlc hfix depth)
private theorem templateList_open_subst_of_fixes (templates : List Template) {S : Subst} {Xs : List Nat}
    (hlc : ∀ p ∈ S, p.2.IsLC)
    (hfix : ∀ x ∈ Xs, S.onTy (.fvar x) = .fvar x) (depth : Nat) :
    substTemplateList S (openTemplateList depth Xs templates) =
      openTemplateList depth Xs (substTemplateList S templates) := by
  cases templates with
  | nil => rfl
  | cons t ts =>
    simp only [substTemplateList, openTemplateList,
      t.substTyFvars_openTyVarsFrom_of_fixes hlc hfix depth,
      templateList_open_subst_of_fixes ts hlc hfix depth]
end

/-- Factor an ordinary annotation check against the transformed source. Only
raw-source allocation bounds and independent target protection are required. -/
theorem LetCheck.factor_source {P : List Nat} (hc : LetCheck K F first rhsTy ann checked sCheck)
    (hrigid : ∀ v ∈ ann.rigidVars, v < first) (hP : ∀ p ∈ P, p < first)
    (hty : Ty.BelowFvars first rhsTy)
    {R : Subst} (hR : ∀ pair ∈ R, pair.2.IsLC)
    (hRP : ∀ p ∈ P, R.onTy (.fvar p) = .fvar p)
    {target : Ty} (htarget : target.IsLC) (hfit : (ann.substTyFvars R).FitsMono target)
    (heq : target = R.onTy rhsTy) :
    ∃ V : Subst, (∀ pair ∈ V, pair.2.IsLC) ∧
      target = V.onTy (sCheck.onTy rhsTy) ∧
      (∀ p ∈ P, V.onTy (.fvar p) = .fvar p) ∧
      Subst.AgreesBelow first R (sCheck ++ V) := by
  cases hc with
  | absent => exact ⟨R, hR, heq, hRP, fun _ _ => rfl⟩
  | hole => exact ⟨R, hR, heq, hRP, fun _ _ => rfl⟩
  | @template checked expected sCheck template halloc _ _ hu =>
    change (template.substTyFvars R).Fits target at hfit
    obtain ⟨U, hU, hag, hUexpected⟩ := hfit.allocate_override_source htarget hR first hrigid
    rw [halloc] at hUexpected
    have hUty : U.onTy rhsTy = target := (Subst.onTy_congr hag hty).symm.trans heq.symm
    have hUP : ∀ p ∈ P, U.onTy (.fvar p) = .fvar p :=
      fun p hp => (hag p (hP p hp)).symm.trans (hRP p hp)
    obtain ⟨V, hfac, hV, hVP⟩ := hu.unifies.greatest_K U hU
      (hUty.trans hUexpected.symm) hUP
    refine ⟨V, hV, hUty.symm.trans (hfac rhsTy), hVP, ?_⟩
    intro v hv
    simpa only [Subst.onTy_append] using (hag v hv).trans (hfac (.fvar v))

/-- The signed version protects the candidate set and the written names
pointwise, while allowing authored provisional leaves to specialize. -/
theorem SignatureCheck.factor_source {P : List Nat}
    (hc : SignatureCheck K F written first rhsTy ann checked sCheck)
    (_hprefix : written.length = ann.paramCount)
    (hrigid : ∀ v ∈ ann.rigidVars, v < first)
    (hP : ∀ p ∈ P ++ written, p < first) (hty : Ty.BelowFvars first rhsTy)
    {R : Subst} (hR : ∀ pair ∈ R, pair.2.IsLC)
    (hRP : ∀ p ∈ P ++ written, R.onTy (.fvar p) = .fvar p)
    {target : Ty} (htarget : target.IsLC) (heq : target = R.onTy rhsTy)
    (hcomplete : ∀ scheme, ann = .complete scheme → target = (R.onPolyTy scheme).openVars written)
    (hpartial : ∀ count template, ann = .partialForall count template →
      ((template.substTyFvars R).openTyVarsFrom 0 written).Fits target) :
    ∃ V : Subst, (∀ pair ∈ V, pair.2.IsLC) ∧
      target = V.onTy (sCheck.onTy rhsTy) ∧
      (∀ p ∈ P ++ written, V.onTy (.fvar p) = .fvar p) ∧
      Subst.AgreesBelow first R (sCheck ++ V) := by
  have hW : ∀ w ∈ written, R.onTy (.fvar w) = .fvar w :=
    fun w hw => hRP w (List.mem_append_right _ hw)
  cases hc with
  | @complete sCheck scheme _ _ hu =>
    have hExpected : R.onTy (scheme.openVars written) = (R.onPolyTy scheme).openVars written :=
      Subst.onTy_openVars_of_fixes hR hW
    have hUni : Unifies R rhsTy (scheme.openVars written) :=
      heq.symm.trans ((hcomplete scheme rfl).trans hExpected.symm)
    obtain ⟨V, hfac, hV, hVP⟩ := hu.unifies.greatest_K R hR hUni hRP
    refine ⟨V, hV, heq.trans (hfac rhsTy), hVP, ?_⟩
    intro v hv
    simpa only [Subst.onTy_append] using hfac (.fvar v)
  | @partialSignature checked expected sCheck count template halloc _ _ hu =>
    have hfit := hpartial count template rfl
    rw [← Template.substTyFvars_openTyVarsFrom_of_fixes template hR hW 0] at hfit
    obtain ⟨U, hU, hag, hUexpected⟩ := hfit.allocate_override_source htarget hR first (by
      intro v hv
      exact (List.mem_append.mp (Template.open_scope (K := template.rigidVars) (fun _ h => h) v hv)).elim
        (hrigid v) (fun hv => hP v (List.mem_append_right _ hv)))
    rw [halloc] at hUexpected
    have hUty : U.onTy rhsTy = target := (Subst.onTy_congr hag hty).symm.trans heq.symm
    have hUP : ∀ p ∈ P ++ written, U.onTy (.fvar p) = .fvar p :=
      fun p hp => (hag p (hP p hp)).symm.trans (hRP p hp)
    obtain ⟨V, hfac, hV, hVP⟩ := hu.unifies.greatest_K U hU
      (hUty.trans hUexpected.symm) hUP
    refine ⟨V, hV, hUty.symm.trans (hfac rhsTy), hVP, ?_⟩
    intro v hv
    simpa only [Subst.onTy_append] using (hag v hv).trans (hfac (.fvar v))

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

/-- Factor a signed check against an independently protected target. Target
free variables may coincide with any fresh inference IDs. -/
theorem SignatureCheck.factor {P : List Nat}
    (hc : SignatureCheck K written first rhsTy ann checked sCheck)
    (hK : ∀ k ∈ K ++ written, k < first) (hP : ∀ p ∈ P ++ written, p < first)
    (hty : Ty.BelowFvars first rhsTy)
    {R : Subst} (hR : ∀ pair ∈ R, pair.2.IsLC)
    (hRP : ∀ p ∈ P ++ written, R.onTy (.fvar p) = .fvar p)
    {target : Ty} (htarget : target.IsLC)
    (hrigid : ∀ v ∈ ann.rigidVars, v ∈ P)
    (heq : target = R.onTy rhsTy)
    (hcomplete : ∀ scheme, ann = .complete scheme → target = scheme.openVars written)
    (hpartial : ∀ count template, ann = .partialForall count template →
      (template.openTyVarsFrom 0 written).Fits target) :
    ∃ V : Subst, (∀ pair ∈ V, pair.2.IsLC) ∧
      target = V.onTy (sCheck.onTy rhsTy) ∧
      (∀ p ∈ P ++ written, V.onTy (.fvar p) = .fvar p) ∧
      Subst.AgreesBelow first R (sCheck ++ V) := by
  cases hc with
  | @complete sCheck scheme _ _ hu =>
      have hExpected : R.onTy (scheme.openVars written) = scheme.openVars written := by
        apply Subst.onTy_eq_self_of_fixes
        intro v hv
        rcases Ty.freeVars_openVars_subset v hv with hv | hv
        · exact hRP v (List.mem_append_left _ (hrigid v hv))
        · exact hRP v (List.mem_append_right _ hv)
      have hUni : Unifies R rhsTy (scheme.openVars written) := by
        change R.onTy rhsTy = R.onTy (scheme.openVars written)
        rw [hExpected, ← heq, hcomplete scheme rfl]
      obtain ⟨V, hfac, hV, hVP⟩ := hu.unifies.greatest_K R hR hUni hRP
      refine ⟨V, hV, heq.trans (hfac rhsTy), hVP, ?_⟩
      intro v hv
      simpa only [Subst.onTy_append] using hfac (.fvar v)
  | @partialSignature checked expected sCheck count template halloc _ hr hu =>
      have hfit := hpartial count template rfl
      obtain ⟨U, hU, hag, hUexpected⟩ := hfit.allocate_override htarget hR first
        (fun v hv => hK v (Template.open_scope hr v hv))
        (fun v hv => hRP v (Template.open_scope hrigid v hv))
      rw [halloc] at hUexpected
      have hUty : U.onTy rhsTy = target := (Subst.onTy_congr hag hty).symm.trans heq.symm
      have hUP : ∀ p ∈ P ++ written, U.onTy (.fvar p) = .fvar p := fun p hp =>
        (hag p (hP p hp)).symm.trans (hRP p hp)
      obtain ⟨V, hfac, hV, hVP⟩ := hu.unifies.greatest_K U hU
        (hUty.trans hUexpected.symm) hUP
      refine ⟨V, hV, hUty.symm.trans (hfac rhsTy), hVP, ?_⟩
      intro v hv
      simpa only [Subst.onTy_append] using (hag v hv).trans (hfac (.fvar v))


theorem closeScheme_generalizes {K names : List Nat} {ctx : Ctx} {ty : Ty}
    {V : Subst} {M : PolyTy} {Xs : List Nat}
    (hty : ty.IsLC) (hV : ∀ pair ∈ V, pair.2.IsLC) (hM : M.WF)
    (hXnodup : Xs.Nodup) (hXlen : Xs.length = M.paramCount)
    (hXM : ∀ x ∈ Xs, x ∉ M.body.freeVars)
    (htarget : M.openVars Xs = V.onTy ty)
    (hXctx : ∀ x ∈ Xs, x ∉ (V.onCtx ctx).env.freeVars)
    (hXK : ∀ x ∈ Xs, ∀ k ∈ K, x ∉ (V.onTy (.fvar k)).freeVars)
    (hcover : ∀ v ∈ ty.freeVars, v ∉ names → v ∈ ctx.env.freeVars ∨ v ∈ K) :
    (V.onPolyTy ⟨names.length, Ty.closeOver names ty⟩).Generalizes M := by
  apply closeOver_generalizes hty hV hM hXnodup hXlen hXM htarget
  intro x hx hcx
  rw [Subst.onPolyTy, Ty.mem_freeVars_onTy_iff] at hcx
  obtain ⟨v, hv, hxv⟩ := hcx
  have hvty := Ty.closeOver_freeVars_subset hv
  have hvnot : v ∉ names := fun hg => Ty.not_mem_closeOver_freeVars hg hv
  have hor := hcover v hvty hvnot
  rcases hor with henv | hk
  · obtain ⟨scheme, hs, hv⟩ := Env.mem_freeVars_iff.mp henv
    apply hXctx x hx
    apply Env.mem_freeVars_iff.mpr
    refine ⟨V.onPolyTy scheme, List.mem_map.mpr ⟨scheme, hs, rfl⟩, ?_⟩
    exact Ty.mem_freeVars_onTy_iff.mpr ⟨v, hv, hxv⟩
  · exact hXK x hx v hk hxv


theorem genScheme_generalizes {K : List Nat} {ctx : Ctx} {ty : Ty}
    {V : Subst} {M : PolyTy} {Xs : List Nat}
    (hty : ty.IsLC) (hV : ∀ pair ∈ V, pair.2.IsLC) (hM : M.WF)
    (hXnodup : Xs.Nodup) (hXlen : Xs.length = M.paramCount)
    (hXM : ∀ x ∈ Xs, x ∉ M.body.freeVars)
    (htarget : M.openVars Xs = V.onTy ty)
    (hXctx : ∀ x ∈ Xs, x ∉ (V.onCtx ctx).env.freeVars)
    (hXK : ∀ x ∈ Xs, ∀ k ∈ K, x ∉ (V.onTy (.fvar k)).freeVars) :
    (V.onPolyTy (genScheme K ctx.env ty)).Generalizes M := by
  apply closeScheme_generalizes hty hV hM hXnodup hXlen hXM htarget hXctx hXK
  intro v hv hnot
  by_cases he : v ∈ ctx.env.freeVars
  · exact .inl he
  · by_cases hk : v ∈ K
    · exact .inr hk
    · exfalso
      apply hnot
      simp only [genVars, List.mem_filter, Bool.and_eq_true]
      exact ⟨hv, by simpa using he, by simpa using hk⟩

theorem SignatureCheck.cover (h : SignatureCheck K written frontier ty ann next subst)
    (hlen : written.length = ann.paramCount) :
    ∀ v ∈ (subst.onTy ty).freeVars,
      v ∉ signatureNames ann K written ctx (subst.onTy ty) → v ∈ ctx.env.freeVars ∨ v ∈ K := by
  have hcomp := h.completion (ctx := ctx) hlen
  cases h with
  | complete _ hr _ =>
    cases hcomp with
    | complete _ heq =>
      intro v hv hnot
      rw [heq] at hv
      rcases Ty.freeVars_openVars_subset v hv with hv | hv
      · exact .inr (hr v hv)
      · exact False.elim (hnot hv)
  | partialSignature _ _ _ _ =>
    intro v hv hnot
    change v ∉ written ++ genVars (K ++ written) ctx.env (subst.onTy ty) at hnot
    by_cases he : v ∈ ctx.env.freeVars
    · exact .inl he
    · by_cases hk : v ∈ K
      · exact .inr hk
      · have hw : v ∉ written := fun hc => hnot (List.mem_append_left _ hc)
        exfalso
        apply hnot
        apply List.mem_append_right
        simp only [genVars, List.mem_filter, Bool.and_eq_true]
        have hkw : v ∉ K ++ written := by simpa only [List.mem_append, not_or] using And.intro hk hw
        exact ⟨hv, by simpa using he, by simpa using hkw⟩

theorem SignatureCheck.scheme_generalizes
    (h : SignatureCheck K written frontier ty ann next subst)
    (hlen : written.length = ann.paramCount) (hnd : written.Nodup)
    (havoid : ∀ name ∈ written, name ∉ K)
    {V : Subst} {M : PolyTy} {Xs : List Nat}
    (hty : (subst.onTy ty).IsLC) (hV : ∀ pair ∈ V, pair.2.IsLC) (hM : M.WF)
    (hXnodup : Xs.Nodup) (hXlen : Xs.length = M.paramCount)
    (hXM : ∀ x ∈ Xs, x ∉ M.body.freeVars)
    (htarget : M.openVars Xs = V.onTy (subst.onTy ty))
    (hXctx : ∀ x ∈ Xs, x ∉ (V.onCtx ctx).env.freeVars)
    (hXK : ∀ x ∈ Xs, ∀ k ∈ K, x ∉ (V.onTy (.fvar k)).freeVars) :
    (V.onPolyTy (signatureScheme ann K written ctx (subst.onTy ty))).Generalizes M := by
  rw [h.scheme_eq_close hlen hnd havoid]
  exact closeScheme_generalizes hty hV hM hXnodup hXlen hXM htarget hXctx hXK (h.cover hlen)

theorem _root_.Infer.signature_frame_aligned {rhs body : Input} {ann : LetAnn}
    (hr : Infer (K ++ Ys) (frontier + ann.paramCount) ctx (rhs.openTyVars Ys) first s1 rhsOut rhsTy)
    (hc : SignatureCheck K Ys first rhsTy ann checked sCheck) (ihr : Infer.Principal hr)
    (hprefix : Ys = freshVars frontier ann.paramCount)
    (hwf : CtxWF ctx) (hbelow : CtxBelow frontier ctx) (hK : ∀ k ∈ K, k < frontier)
    {ambient : Subst} {P : List Nat} {M : PolyTy} {Xs : List Nat} {target : Ty}
    (hS : ∀ pair ∈ ambient, pair.2.IsLC) (hP : ∀ p ∈ P, p < frontier)
    (hfix : ∀ p ∈ P ++ Ys, ambient.onTy (.fvar p) = .fvar p)
    (hM : M.WF) (hannRigid : ∀ v ∈ ann.rigidVars, v ∈ P)
    (hXlen : Xs.length = M.paramCount) (hXnd : Xs.Nodup) (hXtake : Xs.take ann.paramCount = Ys)
    (hannFits : ann.SignatureFits M Xs)
    (hrD : Typing (P ++ Ys) (ambient.onCtx ctx) (rhs.openTyVars Ys) (M.openVars Xs))
    (hbD : Typing P { ambient.onCtx ctx with env := M :: (ambient.onCtx ctx).env } body target)
    (hXM : ∀ x ∈ Xs, x ∉ M.body.freeVars)
    (hXctx : ∀ x ∈ Xs, x ∉ (ambient.onCtx ctx).env.freeVars)
    (hXimages : ∀ x ∈ Xs, ∀ k ∈ K, x ∉ (ambient.onTy (.fvar k)).freeVars) :
    let checkedCtx := sCheck.onCtx (s1.onCtx ctx)
    let scheme := signatureScheme ann K Ys checkedCtx (sCheck.onTy rhsTy)
    ∃ V : Subst, (∀ pair ∈ V, pair.2.IsLC) ∧
      (∀ p ∈ P ++ Ys, V.onTy (.fvar p) = .fvar p) ∧
      Subst.AgreesBelow (frontier + ann.paramCount) ambient ((s1 ++ sCheck) ++ V) ∧
      Typing P (V.onCtx { checkedCtx with env := scheme :: checkedCtx.env }) body target ∧
      CtxWF { checkedCtx with env := scheme :: checkedCtx.env } ∧
      CtxBelow checked { checkedCtx with env := scheme :: checkedCtx.env } ∧
      (∀ pair ∈ s1 ++ sCheck, Ty.BelowFvars checked pair.2) := by
  dsimp only
  have hYlen : Ys.length = ann.paramCount := by rw [hprefix, freshVars_length]
  have hYnd : Ys.Nodup := hprefix ▸ freshVars_nodup
  have hYavoid : ∀ y ∈ Ys, y ∉ K := by
    intro y hy hk
    have hge := freshVars_ge y (hprefix ▸ hy)
    have hlt := hK y hk
    omega
  have hKopen : ∀ k ∈ K ++ Ys, k < frontier + ann.paramCount := by
    intro k hk
    rcases List.mem_append.mp hk with hk | hk
    · have := hK k hk; omega
    · exact freshVars_lt k (hprefix ▸ hk)
  have hPopen : ∀ p ∈ P ++ Ys, p < frontier + ann.paramCount := by
    intro p hp
    rcases List.mem_append.mp hp with hp | hp
    · have := hP p hp; omega
    · exact freshVars_lt p (hprefix ▸ hp)
  have hbelowOpen : CtxBelow (frontier + ann.paramCount) ctx :=
    fun scheme hs => (hbelow scheme hs).mono (by omega)
  obtain ⟨R, hR, hrTy, hRP, hagR⟩ := ihr hwf hbelowOpen hKopen ambient
    (M.openVars Xs) (P ++ Ys) hS hPopen hfix hrD
  have hrle := hr.frontier_le
  have hcle := hc.frontier_le
  have hK1 : ∀ k ∈ K ++ Ys, k < first := fun k hk => Nat.lt_of_lt_of_le (hKopen k hk) hrle
  have hP1 : ∀ p ∈ P ++ Ys, p < first := fun p hp => Nat.lt_of_lt_of_le (hPopen p hp) hrle
  obtain ⟨hrB, hs1B⟩ := hr.belowFvars hbelowOpen hKopen
  obtain ⟨hrLC, hs1LC⟩ := hr.lc hwf
  obtain ⟨V, hV, hcheckedTy, hVP, hagV⟩ := hc.factor hK1 hP1 hrB hR hRP
    hrD.regular hannRigid hrTy
    (by
      intro scheme heq
      subst ann
      cases hannFits
      have htake : Xs.take M.paramCount = Xs := List.take_of_length_le hXlen.le
      change Xs.take M.paramCount = Ys at hXtake
      rw [htake] at hXtake
      exact congrArg M.openVars hXtake)
    (by
      intro count template heq
      subst ann
      cases hannFits with
      | partialSignature _ hfits =>
          change Xs.take count = Ys at hXtake
          simpa only [hXtake] using hfits)
  have hsCheckLC := hc.lc hYlen hrLC
  have hsCheckB := hc.belowFvars hrB
    (fun k hk => hK1 k (List.mem_append_left _ hk))
    (fun y hy => hK1 y (List.mem_append_right _ hy))
  have hprefixB : ∀ pair ∈ s1 ++ sCheck, Ty.BelowFvars checked pair.2 := by
    intro pair hp
    exact (List.mem_append.mp hp).elim (fun hp => (hs1B pair hp).mono hcle) (hsCheckB pair)
  have hagPrefix := Subst.AgreesBelow.trans_append hrle hagR hs1B hagV
  have hctxBridge : V.onCtx (sCheck.onCtx (s1.onCtx ctx)) = ambient.onCtx ctx := by
    rw [← Subst.onCtx_append, ← Subst.onCtx_append]
    simpa only [List.append_assoc] using (Subst.onCtx_congr hagPrefix hbelowOpen).symm
  have hprefixFix : ∀ k ∈ K, (s1 ++ sCheck).onTy (.fvar k) = .fvar k := by
    apply Subst.fixes_of_dom_avoids
    intro pair hp
    exact (List.mem_append.mp hp).elim
      (fun hp => fun hk => hr.dom_avoids pair hp (List.mem_append_left _ hk))
      (fun hp => fun hk => hc.dom_avoids pair hp (List.mem_append_left _ hk))
  have hVimages : ∀ x ∈ Xs, ∀ k ∈ K, x ∉ (V.onTy (.fvar k)).freeVars := by
    intro x hx k hk
    have heq := hagPrefix k (hKopen k (List.mem_append_left _ hk))
    rw [Subst.onTy_append, hprefixFix k hk] at heq
    rw [← heq]
    exact hXimages x hx k hk
  have hcheckedLC := Subst.onTy_lc hsCheckLC hrLC
  have hgen := hc.scheme_generalizes (ctx := sCheck.onCtx (s1.onCtx ctx)) hYlen hYnd hYavoid
    hcheckedLC hV hM hXnd hXlen hXM hcheckedTy
    (by simpa only [hctxBridge] using hXctx) hVimages
  have hbodyWeak := Typing.weaken_schemes (env := (ambient.onCtx ctx).env) (.cons hgen .nil) hbD
  have hbodyD : Typing P (V.onCtx
      { (sCheck.onCtx (s1.onCtx ctx)) with
        env := signatureScheme ann K Ys (sCheck.onCtx (s1.onCtx ctx)) (sCheck.onTy rhsTy) ::
          (sCheck.onCtx (s1.onCtx ctx)).env }) body target := by
    rw [← hctxBridge] at hbodyWeak
    exact hbodyWeak
  have hcheckedWF := Subst.onCtx_wf hsCheckLC (Subst.onCtx_wf hs1LC hwf)
  have hcheckedB := Subst.onCtx_below hsCheckB hcle (Subst.onCtx_below hs1B (by omega) hbelow)
  have hcheckedTyB := Subst.onTy_belowFvars hsCheckB (hrB.mono hcle)
  have hbodyWF : CtxWF { (sCheck.onCtx (s1.onCtx ctx)) with
      env := signatureScheme ann K Ys (sCheck.onCtx (s1.onCtx ctx)) (sCheck.onTy rhsTy) ::
        (sCheck.onCtx (s1.onCtx ctx)).env } := by
    intro scheme hs
    rcases List.mem_cons.mp hs with rfl | hs
    · exact hc.scheme_wf hcheckedLC
    · exact hcheckedWF scheme hs
  have hbodyB : CtxBelow checked { (sCheck.onCtx (s1.onCtx ctx)) with
      env := signatureScheme ann K Ys (sCheck.onCtx (s1.onCtx ctx)) (sCheck.onTy rhsTy) ::
        (sCheck.onCtx (s1.onCtx ctx)).env } := by
    intro scheme hs
    rcases List.mem_cons.mp hs with rfl | hs
    · exact hc.scheme_belowFvars hcheckedTyB (fun k hk => Nat.lt_of_lt_of_le (hK k hk) (by omega))
    · exact hcheckedB scheme hs
  exact ⟨V, hV, hVP, hagPrefix, hbodyD, hbodyWF, hbodyB, hprefixB⟩

/-- Align only a candidate signature's written prefix with algorithmic skolems.
The freshness hypotheses concern the already dodged candidate. Additional
quantifiers receive fresh names disjoint from an arbitrary caller avoid set. -/
theorem Typing.align_partial_prefix_with_fits {P : List Nat} {ctx : Ctx} {rhs : Input}
    {scheme : PolyTy} {ann : LetAnn} {count : Nat} {L Ys : List Nat}
    (hcount : count = ann.paramCount)
    (hFits : ∀ Xs, FreshNames L scheme.paramCount Xs → ann.SignatureFits scheme Xs)
    (hAnn : ∀ v ∈ ann.rigidVars, v ∈ P)
    (hcofinite : ∀ Xs, FreshNames L scheme.paramCount Xs →
      Typing (P ++ Xs.take count) ctx (rhs.openTyVars (Xs.take count)) (scheme.openVars Xs))
    (hle : count ≤ scheme.paramCount) (hsource : ∀ v ∈ rhs.rigidVars, v ∈ P)
    (hYsLen : Ys.length = count) (hYsNodup : Ys.Nodup)
    (hYsP : ∀ y ∈ Ys, y ∉ P) (hYsCtx : ∀ y ∈ Ys, y ∉ ctx.env.freeVars)
    (hYsScheme : ∀ y ∈ Ys, y ∉ scheme.body.freeVars) (avoid : List Nat) :
    ∃ extras : List Nat,
      extras.length = scheme.paramCount - count ∧ (Ys ++ extras).Nodup ∧
      (∀ z ∈ extras, z ∉ avoid ++ P ++ Ys ++ ctx.env.freeVars ++ scheme.body.freeVars ++ rhs.rigidVars) ∧
      (∀ z ∈ Ys ++ extras, z ∉ P ∧ z ∉ ctx.env.freeVars ∧ z ∉ scheme.body.freeVars) ∧
      Typing (P ++ Ys) ctx (rhs.openTyVars Ys) (scheme.openVars (Ys ++ extras)) ∧
      ann.SignatureFits scheme (Ys ++ extras) := by
  obtain ⟨extras, hELen, hENodup, hEAvoid⟩ := exists_fresh_names
    (avoid ++ P ++ Ys ++ ctx.env.freeVars ++ scheme.body.freeVars ++ rhs.rigidVars)
    (scheme.paramCount - count)
  have hVsLen : (Ys ++ extras).length = scheme.paramCount := by
    simp only [List.length_append, hYsLen, hELen]; omega
  have hVsNodup : (Ys ++ extras).Nodup := by
    refine List.nodup_append.mpr ⟨hYsNodup, hENodup, ?_⟩
    intro y hy z hz heq
    subst z
    apply hEAvoid y hz
    simp only [List.mem_append]
    tauto
  obtain ⟨Ns, hNLen, hNNodup, hNAvoid⟩ := exists_fresh_names
    (L ++ P ++ (Ys ++ extras) ++ ctx.env.freeVars ++ scheme.body.freeVars ++ rhs.rigidVars)
    scheme.paramCount
  have hNfresh : FreshNames L scheme.paramCount Ns :=
    ⟨hNLen, hNNodup, fun x hx hl => hNAvoid x hx (by simp only [List.mem_append]; tauto)⟩
  have hNP : ∀ x ∈ Ns, x ∉ P := fun x hx hp => hNAvoid x hx (by simp only [List.mem_append]; tauto)
  have hNCtx : ∀ x ∈ Ns, x ∉ ctx.env.freeVars := fun x hx hc => hNAvoid x hx (by simp only [List.mem_append]; tauto)
  have hNScheme : ∀ x ∈ Ns, x ∉ scheme.body.freeVars := fun x hx hm => hNAvoid x hx (by simp only [List.mem_append]; tauto)
  have hNVs : ∀ x ∈ Ns, x ∉ Ys ++ extras := fun x hx hv => hNAvoid x hx (by simp only [List.mem_append] at hv ⊢; tauto)
  have hNtake : (Ns.take count).length = Ys.length := by
    rw [List.length_take, hNLen, hYsLen]; omega
  have hNSplit : (Ns.take count ++ Ns.drop count).Nodup := by simpa only [List.take_append_drop] using hNNodup
  have hNtakeY : ∀ name ∈ Ns.take count, name ∉ Ys := fun name hn hy =>
    hNVs name (List.mem_of_mem_take hn) (List.mem_append_left _ hy)
  let RY : Subst := (Ns.take count).zip (Ys.map Ty.fvar)
  let RG : Subst := (Ns.drop count).zip (extras.map Ty.fvar)
  have hRYlc : ∀ p ∈ RY, p.2.IsLC := by
    intro p hp
    obtain ⟨_, _, heq⟩ := List.mem_map.mp (List.of_mem_zip hp).2
    rw [← heq]; exact .fvar
  have hRGlc : ∀ p ∈ RG, p.2.IsLC := by
    intro p hp
    obtain ⟨_, _, heq⟩ := List.mem_map.mp (List.of_mem_zip hp).2
    rw [← heq]; exact .fvar
  have hRYK : ∀ k ∈ P, RY.onTy (.fvar k) = .fvar k := by
    intro k hk
    apply Ty.substFvars_eq_self_of_no_key
    intro p hp hc
    have heq : p.1 = k := List.mem_singleton.mp hc
    exact hNP p.1 (List.mem_of_mem_take (List.of_mem_zip hp).1) (heq ▸ hk)
  have hRYscope : ∀ k ∈ P ++ Ns.take count, ∀ v ∈ (RY.onTy (.fvar k)).freeVars, v ∈ P ++ Ys := by
    intro k hk v hv
    rcases List.mem_append.mp hk with hk | hk
    · rw [hRYK k hk] at hv
      exact List.mem_append_left _ ((List.mem_singleton.mp hv) ▸ hk)
    · obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hk
      have hilt : i < (Ns.take count).length := (List.getElem?_eq_some_iff.mp hi).choose
      have hit : i < Ys.length := by omega
      have himg : RY.onTy (.fvar k) = .fvar Ys[i] := by
        apply Ty.substFvars_zip_fvar_eq' hNSplit.of_append_left hi
        · simp only [List.getElem?_map, List.getElem?_eq_getElem hit, Option.map_some]
        · intro y hy hc
          simp only [Ty.freeVars, List.mem_singleton] at hc
          apply hNtakeY y hy
          rw [hc]
          exact List.getElem_mem hit
      rw [himg] at hv
      exact List.mem_append_right _ ((List.mem_singleton.mp hv) ▸ List.getElem_mem hit)
  have ctxFixed : ∀ S : Subst, (∀ p ∈ S, p.1 ∈ Ns) → S.onCtx ctx = ctx := by
    intro S hS
    have henv := Subst.onEnv_eq_self_of_fresh (fun p hp => hNCtx p.1 (hS p hp))
    cases ctx
    simp only [Subst.onCtx, henv]
  have hRYctx : RY.onCtx ctx = ctx := ctxFixed RY
    (fun p hp => List.mem_of_mem_take (List.of_mem_zip hp).1)
  have hRGctx : RG.onCtx ctx = ctx := ctxFixed RG
    (fun p hp => List.mem_of_mem_drop (List.of_mem_zip hp).1)
  have hRYsource : (rhs.openTyVars (Ns.take count)).substTyFvars RY = rhs.openTyVars Ys := by
    exact rhs.substTyFvars_zip_openTyVars hNtake hNSplit.of_append_left
      (fun y hy hv => hNP y (List.mem_of_mem_take hy) (hsource y hv)) hNtakeY
  have hfirst := (hcofinite Ns hNfresh).onSubst_source RY hRYlc hRYscope
  rw [hRYctx, hRYsource] at hfirst
  have hRGavoid : ∀ p ∈ RG, p.1 ∉ P ++ Ys := by
    intro p hp hc
    have hpN := List.mem_of_mem_drop (List.of_mem_zip hp).1
    rcases List.mem_append.mp hc with hk | hy
    · exact hNP p.1 hpN hk
    · exact hNVs p.1 hpN (List.mem_append_left _ hy)
  have hsecond := hfirst.onSubst RG hRGlc hRGavoid
  rw [hRGctx] at hsecond
  have hzip : Ns.zip ((Ys ++ extras).map Ty.fvar) = RY ++ RG := by
    conv_lhs => rw [← List.take_append_drop count Ns, List.map_append]
    exact List.zip_append (by simpa only [List.length_map] using hNtake)
  have htype : (RY ++ RG).onTy (scheme.openVars Ns) = scheme.openVars (Ys ++ extras) := by
    rw [← hzip]
    have h := Ty.substFvars_zip_openVarsFrom (d := 0) (t := scheme.body)
      (hNLen.trans hVsLen.symm) hNNodup hNScheme hNVs
    simpa only [Subst.onTy, PolyTy.openVars, Ty.openVarsFrom, Ty.openVars,
      Nat.not_lt_zero, ↓reduceIte, Nat.sub_zero] using h
  have hpaired : ann.SignatureFits scheme (Ys ++ extras) := by
    have hfit := hFits Ns hNfresh
    cases hfit with
    | complete => exact .complete
    | @partialSignature scheme template declaredCount names hdeclLe hfitNs =>
      have hsame : count = declaredCount := hcount
      subst declaredCount
      change ∀ v ∈ template.rigidVars, v ∈ P at hAnn
      have hRYTemplate : (template.openTyVarsFrom 0 (Ns.take count)).substTyFvars RY =
          template.openTyVarsFrom 0 Ys :=
        template.substTyFvars_zip_openTyVarsFrom hNtake hNSplit.of_append_left
          (fun y hy hv => hNP y (List.mem_of_mem_take hy) (hAnn y hv)) hNtakeY 0
      have hfirstFit := hfitNs.substTyFvars RY
      rw [hRYTemplate] at hfirstFit
      have hRGTemplate : (template.openTyVarsFrom 0 Ys).substTyFvars RG =
          template.openTyVarsFrom 0 Ys := by
        rw [template.substTyFvars_openTyVarsFrom hRGlc
          (fun p hp hy => hRGavoid p hp (List.mem_append_right _ hy)) 0]
        rw [template.substTyFvars_eq_self_of_fixes (fun v hv =>
          Subst.fixes_of_dom_avoids hRGavoid v (List.mem_append_left _ (hAnn v hv)))]
      have hsecondFit := hfirstFit.substTyFvars RG
      rw [hRGTemplate] at hsecondFit
      refine .partialSignature hdeclLe ?_
      have htakeVs : (Ys ++ extras).take count = Ys := by
        rw [← hYsLen]
        simp
      rw [htakeVs, ← htype, Subst.onTy_append]
      exact hsecondFit
  refine ⟨extras, hELen, hVsNodup, hEAvoid, ?_, ?_, hpaired⟩
  · intro z hz
    rcases List.mem_append.mp hz with hz | hz
    · exact ⟨hYsP z hz, hYsCtx z hz, hYsScheme z hz⟩
    · refine ⟨?_, ?_, ?_⟩ <;> intro hc <;> apply hEAvoid z hz <;>
        simp only [List.mem_append] <;> tauto
  · rw [← htype, Subst.onTy_append]
    exact hsecond

/-- Shared signed continuation frame for an internally dodged candidate. The
cofinite template and RHS premises use one aligned opening and one extra block. -/
theorem _root_.Infer.signature_frame {rhs body : Input} {ann : LetAnn}
    (hr : Infer (K ++ Ys) (frontier + ann.paramCount) ctx (rhs.openTyVars Ys) first s1 rhsOut rhsTy)
    (hc : SignatureCheck K Ys first rhsTy ann checked sCheck) (ihr : Infer.Principal hr)
    (hprefix : Ys = freshVars frontier ann.paramCount)
    (hwf : CtxWF ctx) (hbelow : CtxBelow frontier ctx) (hK : ∀ k ∈ K, k < frontier)
    {ambient : Subst} {P : List Nat} {M : PolyTy} {L : List Nat} {target : Ty}
    (hS : ∀ pair ∈ ambient, pair.2.IsLC) (hP : ∀ p ∈ P, p < frontier)
    (hfix : ∀ p ∈ P ++ Ys, ambient.onTy (.fvar p) = .fvar p)
    (hM : M.WF) (hannRigid : ∀ v ∈ ann.rigidVars, v ∈ P)
    (hrhsRigid : ∀ v ∈ rhs.rigidVars, v ∈ P)
    (hannFits : ∀ Xs, FreshNames L M.paramCount Xs → ann.SignatureFits M Xs)
    (hrD : ∀ Xs, FreshNames L M.paramCount Xs →
      Typing (P ++ Xs.take ann.paramCount) (ambient.onCtx ctx)
        (rhs.openTyVars (Xs.take ann.paramCount)) (M.openVars Xs))
    (hbD : Typing P { ambient.onCtx ctx with env := M :: (ambient.onCtx ctx).env } body target)
    (hYsM : ∀ y ∈ Ys, y ∉ M.body.freeVars)
    (hYsCtx : ∀ y ∈ Ys, y ∉ (ambient.onCtx ctx).env.freeVars)
    (hYsImages : ∀ y ∈ Ys, ∀ k ∈ K, y ∉ (ambient.onTy (.fvar k)).freeVars) :
    let checkedCtx := sCheck.onCtx (s1.onCtx ctx)
    let scheme := signatureScheme ann K Ys checkedCtx (sCheck.onTy rhsTy)
    ∃ V : Subst, (∀ pair ∈ V, pair.2.IsLC) ∧
      (∀ p ∈ P ++ Ys, V.onTy (.fvar p) = .fvar p) ∧
      Subst.AgreesBelow (frontier + ann.paramCount) ambient ((s1 ++ sCheck) ++ V) ∧
      Typing P (V.onCtx { checkedCtx with env := scheme :: checkedCtx.env }) body target ∧
      CtxWF { checkedCtx with env := scheme :: checkedCtx.env } ∧
      CtxBelow checked { checkedCtx with env := scheme :: checkedCtx.env } ∧
      (∀ pair ∈ s1 ++ sCheck, Ty.BelowFvars checked pair.2) := by
  have hYlen : Ys.length = ann.paramCount := by rw [hprefix, freshVars_length]
  have hYnd : Ys.Nodup := hprefix ▸ freshVars_nodup
  have hYsP : ∀ y ∈ Ys, y ∉ P := by
    intro y hy hp
    have hge := freshVars_ge y (hprefix ▸ hy)
    have hlt := hP y hp
    omega
  obtain ⟨Ns, hNlen, hNnd, hNavoid⟩ := exists_fresh_names L M.paramCount
  have hle := (hannFits Ns ⟨hNlen, hNnd, hNavoid⟩).prefix_le
  let images := K.flatMap (fun k => (ambient.onTy (.fvar k)).freeVars)
  obtain ⟨extras, hElen, hXsNd, hExtra, hAll, hAligned, hAlignedFits⟩ :=
    Typing.align_partial_prefix_with_fits rfl hannFits hannRigid hrD hle hrhsRigid
      hYlen hYnd hYsP hYsCtx hYsM images
  have hXsLen : (Ys ++ extras).length = M.paramCount := by
    simp only [List.length_append, hYlen, hElen]; omega
  have hXsTake : (Ys ++ extras).take ann.paramCount = Ys := by rw [← hYlen]; simp
  have hXImages : ∀ x ∈ Ys ++ extras, ∀ k ∈ K, x ∉ (ambient.onTy (.fvar k)).freeVars := by
    intro x hx k hk hv
    rcases List.mem_append.mp hx with hy | he
    · exact hYsImages x hy k hk hv
    · apply hExtra x he
      have himages : x ∈ images := List.mem_flatMap.mpr ⟨k, hk, hv⟩
      simp only [List.mem_append]
      tauto
  exact hr.signature_frame_aligned hc ihr hprefix hwf hbelow hK hS hP hfix hM hannRigid
    hXsLen hXsNd hXsTake hAlignedFits hAligned hbD
    (fun x hx => (hAll x hx).2.2) (fun x hx => (hAll x hx).2.1) hXImages


/-- Move arbitrary candidate free variables away from newly allocated signature
skolems. Only the scratch block is fresh; candidate types are unrestricted. -/
theorem Typing.signature_dodge
    {K P : List Nat} {ambient : Subst} {ctx : Ctx} {ann : LetAnn} {rhs body : Input} {target : Ty} {frontier : Nat}
    (ht : Typing P (ambient.onCtx ctx) (.letIn ann rhs body) target)
    (hmode : ann.isSignature = true) (hbelow : CtxBelow frontier ctx)
    (hP : ∀ p ∈ P, p < frontier) (hK : ∀ k ∈ K, k < frontier)
    (hS : ∀ pair ∈ ambient, pair.2.IsLC)
    (hfix : ∀ p ∈ P, ambient.onTy (.fvar p) = .fvar p) :
    ∃ (W : Nat) (M : PolyTy) (L : List Nat),
      let written := freshVars frontier ann.paramCount
      let forward := blockList frontier W ann.paramCount
      let backward := blockListBack frontier W ann.paramCount
      let moved := Subst.conj (blockSwap frontier W ann.paramCount) ambient
      (∀ pair ∈ moved, pair.2.IsLC) ∧
      (∀ p ∈ P ++ written, moved.onTy (.fvar p) = .fvar p) ∧
      (∀ v, v < frontier → backward.onTy (moved.onTy (.fvar v)) = ambient.onTy (.fvar v)) ∧
      (∀ pair ∈ backward, pair.2.IsLC) ∧
      (∀ p ∈ P, backward.onTy (.fvar p) = .fvar p) ∧
      backward.onTy (forward.onTy target) = target ∧
      M.WF ∧ (∀ v ∈ ann.rigidVars, v ∈ P) ∧ (∀ v ∈ rhs.rigidVars, v ∈ P) ∧
      (∀ Xs, FreshNames L M.paramCount Xs → ann.SignatureFits M Xs) ∧
      (∀ Xs, FreshNames L M.paramCount Xs →
        Typing (P ++ Xs.take ann.paramCount) (moved.onCtx ctx)
          (rhs.openTyVars (Xs.take ann.paramCount)) (M.openVars Xs)) ∧
      Typing P { moved.onCtx ctx with env := M :: (moved.onCtx ctx).env } body (forward.onTy target) ∧
      (∀ y ∈ written, y ∉ M.body.freeVars) ∧
      (∀ y ∈ written, y ∉ (moved.onCtx ctx).env.freeVars) ∧
      (∀ y ∈ written, ∀ k ∈ K, y ∉ (moved.onTy (.fvar k)).freeVars) := by
  obtain ⟨M, L, hM, hann, hrhs, hfit, htyped, hbody⟩ := ht.signature_inv hmode
  let images := K.map (fun k => ambient.onTy (.fvar k))
  let contextTypes := (ambient.onCtx ctx).env.map PolyTy.body
  let targets := M.body :: target :: (contextTypes ++ images)
  obtain ⟨W, hW, _, hMoved, hWritten, hBelow, hForward, hBackward, hTargets⟩ :=
    signed_candidate_dodge ambient hS frontier ann.paramCount targets []
  let forward := blockList frontier W ann.paramCount
  let backward := blockListBack frontier W ann.paramCount
  let moved := Subst.conj (blockSwap frontier W ann.paramCount) ambient
  have hforwardLC := blockList_lc frontier W ann.paramCount
  have hForwardP : ∀ p ∈ P, forward.onTy (.fvar p) = .fvar p :=
    fun p hp => (hBelow p (hP p hp)).1
  have hMovedP : ∀ p ∈ P, moved.onTy (.fvar p) = .fvar p := by
    intro p hp
    rw [hForward (.fvar _) (.fvar (hP p hp)), hfix p hp]
    exact hForwardP p hp
  have hdomP : ∀ pair ∈ forward, pair.1 ∉ P := by
    intro pair hp hmem
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hp
    have := hP _ hmem
    omega
  have hag : Subst.AgreesBelow frontier (ambient ++ forward) moved := by
    intro v hv
    simpa only [Subst.onTy_append] using (hForward (.fvar v) (.fvar hv)).symm
  have hctxeq : forward.onCtx (ambient.onCtx ctx) = moved.onCtx ctx := by
    rw [← Subst.onCtx_append]
    exact Subst.onCtx_congr hag hbelow
  obtain ⟨L', hfits', htypes'⟩ := Typing.signatureBinding_onSubst hfit htyped hann
    forward hforwardLC hdomP
  have hbody' := hbody.onSubst_fixes forward hforwardLC hForwardP
  have hbodyctx : forward.onCtx { ambient.onCtx ctx with env := M :: (ambient.onCtx ctx).env } =
      { moved.onCtx ctx with env := forward.onPolyTy M :: (moved.onCtx ctx).env } := by
    change { forward.onCtx (ambient.onCtx ctx) with
      env := forward.onPolyTy M :: (forward.onCtx (ambient.onCtx ctx)).env } = _
    rw [hctxeq]
  rw [hbodyctx] at hbody'
  have htargetM := hTargets M.body (by simp only [targets, List.mem_cons]; tauto)
  have htargetResult := hTargets target (by simp only [targets, List.mem_cons]; tauto)
  refine ⟨W, forward.onPolyTy M, L', hMoved, ?_, (fun v hv => hBackward (.fvar v) (.fvar hv)), blockListBack_lc _ _ _, ?_,
    htargetResult.1, Subst.onPolyTy_wf hforwardLC hM, hann, hrhs, hfits', ?_, hbody',
    htargetM.2, ?_, ?_⟩
  · intro p hp
    exact (List.mem_append.mp hp).elim (hMovedP p) (hWritten p)
  · intro p hp
    exact (hBelow p (hP p hp)).2
  · intro Xs hf
    simpa only [hctxeq] using htypes' Xs hf
  · intro y hy hmem
    rw [← hctxeq] at hmem
    obtain ⟨scheme, hs, hv⟩ := Env.mem_freeVars_iff.mp hmem
    obtain ⟨old, ho, rfl⟩ := List.mem_map.mp hs
    exact (hTargets old.body (by
      simp only [targets, List.mem_cons, List.mem_append]
      right; right; left
      exact List.mem_map.mpr ⟨old, ho, rfl⟩)).2 y hy hv
  · intro y hy k hk hv
    rw [hForward (.fvar _) (.fvar (hK k hk))] at hv
    exact (hTargets (ambient.onTy (.fvar k)) (by
      simp only [targets, List.mem_cons, List.mem_append]
      right; right; right
      exact List.mem_map.mpr ⟨k, hk, rfl⟩)).2 y hy hv

/-- Reconcile a checked ordinary RHS with a declarative let scheme, then
transport its continuation. Shared by both completeness directions. -/
theorem _root_.Infer.source_let_frame
    (hscope : SourceScope K F (.letIn ann rhs body))
    (hr : Infer K F frontier ctx rhs first s1 rhsOut rhsTy)
    (hc : LetCheck K (substSoft s1 F) first rhsTy (ann.substTyFvars s1) checked sCheck)
    (ihr : Infer.SourcePrincipal hr) :
    CtxWF ctx → CtxBelow frontier ctx → (∀ k ∈ K, k < frontier) →
    (∀ t ∈ F, Ty.BelowFvars frontier t) →
    ∀ (ambient : Subst) (target : Ty) (P : List Nat),
      (∀ pair ∈ ambient, pair.2.IsLC) → (∀ p ∈ P, p < frontier) →
      (∀ p ∈ P, ambient.onTy (.fvar p) = .fvar p) →
      (∀ v ∈ (Input.letIn ann rhs body).rigidVars, v ∈ K → v ∉ softVars F → ambient.onTy (.fvar v) = .fvar v) →
      Typing P (ambient.onCtx ctx) ((Input.letIn ann rhs body).substTyFvars ambient) target →
      ∃ V : Subst, (∀ pair ∈ V, pair.2.IsLC) ∧
        (∀ p ∈ P, V.onTy (.fvar p) = .fvar p) ∧
        Subst.AgreesBelow frontier ambient (s1 ++ sCheck ++ V) ∧
        Typing P (V.onCtx { (sCheck.onCtx (s1.onCtx ctx)) with
        env := genScheme (K ++ softVars (substSoft (s1 ++ sCheck) F)) (sCheck.onCtx (s1.onCtx ctx)).env (sCheck.onTy rhsTy) ::
          (sCheck.onCtx (s1.onCtx ctx)).env }) ((body.substTyFvars (s1 ++ sCheck)).substTyFvars V) target ∧
        CtxWF { (sCheck.onCtx (s1.onCtx ctx)) with
        env := genScheme (K ++ softVars (substSoft (s1 ++ sCheck) F)) (sCheck.onCtx (s1.onCtx ctx)).env (sCheck.onTy rhsTy) ::
          (sCheck.onCtx (s1.onCtx ctx)).env } ∧ CtxBelow checked { (sCheck.onCtx (s1.onCtx ctx)) with
        env := genScheme (K ++ softVars (substSoft (s1 ++ sCheck) F)) (sCheck.onCtx (s1.onCtx ctx)).env (sCheck.onTy rhsTy) ::
          (sCheck.onCtx (s1.onCtx ctx)).env } ∧
        (∀ pair ∈ s1 ++ sCheck, Ty.BelowFvars checked pair.2) := by
  intro hwf hbelow hK hF ambient target P hS hP hfix hfreeze htyping
  have hscopeBound : ∀ v ∈ K ++ softVars F, v < frontier :=
    fun v hv => (List.mem_append.mp hv).elim (hK v) (softVars_lt hF v)
  have hmode : ann.isSignature = false := by simpa only [LetAnn.isSignature_substTyFvars] using hc.not_signature
  obtain ⟨M, L, hM, hannRigid, hannFits, hrD, hbD⟩ := htyping.letMono_inv (by simpa using hmode)
  let images := K.flatMap (fun k => (ambient.onTy (.fvar k)).freeVars) ++ softVars (substSoft ambient F)
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
      exact List.mem_append_left _ (List.mem_flatMap.mpr ⟨k, hk, hc⟩))
  obtain ⟨R, hR, hrTy, hRP, hagR⟩ := ihr hwf hbelow hK hF ambient
    (M.openVars Xs) P hS hP hfix
    (fun v hv => hfreeze v (List.mem_append_left _ (List.mem_append_right _ hv))) (hrD Xs hXfresh)
  have hrle := hr.frontier_le
  have hcle := hc.frontier_le
  have hK1 : ∀ k ∈ K, k < first := fun k hk => Nat.lt_of_lt_of_le (hK k hk) hrle
  have hP1 : ∀ p ∈ P, p < first := fun p hp => Nat.lt_of_lt_of_le (hP p hp) hrle
  obtain ⟨hrB, hs1B⟩ := hr.belowFvars hbelow hK hF
  obtain ⟨hrLC, hs1LC⟩ := hr.lc hwf
  have hF1 := substSoft_below hs1B hrle hF
  have hannEq : (ann.substTyFvars s1).substTyFvars R = ann.substTyFvars ambient := by
    rw [← LetAnn.substTyFvars_append]
    exact ann.substTyFvars_congr (fun v hv => (hagR v
      (hscopeBound v (hscope v (List.mem_append_left _ (List.mem_append_left _ hv))))).symm)
  obtain ⟨V, hV, hcheckedTy, hVP, hagV⟩ := hc.factor_source
    (fun v hv => by
      have hs := hscope.subst s1 (Subst.fixes_of_dom_avoids hr.dom_avoids)
      have hvscope := hs v (List.mem_append_left _ (List.mem_append_left _ hv))
      exact (List.mem_append.mp hvscope).elim (hK1 v) (softVars_lt hF1 v))
    hP1 hrB hR hRP ((hrD Xs hXfresh).regular) (hannEq.symm ▸ hannFits Xs hXfresh) hrTy
  have hsCheckLC := hc.lc hrLC
  have hsCheckB := hc.belowFvars hrB hK1 hF1
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
  have hVimages : ∀ x ∈ Xs, ∀ k ∈ K ++ softVars (substSoft (s1 ++ sCheck) F),
      x ∉ (V.onTy (.fvar k)).freeVars := by
    intro x hx k hk hv
    rcases List.mem_append.mp hk with hk | hk
    · have heq := hagPrefix k (hK k hk)
      rw [Subst.onTy_append, hprefixFix k hk] at heq
      rw [← heq] at hv
      exact hXimages x hx k hk hv
    · obtain ⟨ty, hty, hk⟩ := TyList.mem_freeVars_iff.mp hk
      obtain ⟨original, ho, rfl⟩ := List.mem_map.mp hty
      have himage : x ∈ (V.onTy ((s1 ++ sCheck).onTy original)).freeVars :=
        Ty.mem_freeVars_substFvars_image.mpr ⟨k, hk, hv⟩
      have heq := Subst.onTy_congr hagPrefix (hF original ho)
      rw [Subst.onTy_append] at heq
      rw [← heq] at himage
      exact hXavoid x hx (by
        simp only [List.mem_append, images]
        right; right
        exact TyList.mem_freeVars_iff.mpr ⟨ambient.onTy original,
          List.mem_map.mpr ⟨original, ho, rfl⟩, himage⟩)
  have hcheckedLC := Subst.onTy_lc hsCheckLC hrLC
  have hgen := genScheme_generalizes (ctx := sCheck.onCtx (s1.onCtx ctx)) hcheckedLC hV hM hXnd hXlen hXM hcheckedTy
    (by simpa only [hctxBridge] using hXctx) hVimages
  have hbodyWeak := Typing.weaken_schemes (env := (ambient.onCtx ctx).env)
    (.cons hgen .nil) hbD
  have hbodySource : body.substTyFvars ambient =
      (body.substTyFvars (s1 ++ sCheck)).substTyFvars V := by
    rw [← Input.substTyFvars_append]
    exact body.substTyFvars_congr (fun v hv => hagPrefix v
      (hscopeBound v (hscope v (List.mem_append_right _ hv))))
  rw [hbodySource] at hbodyWeak
  have hbodyD : Typing P (V.onCtx
      { (sCheck.onCtx (s1.onCtx ctx)) with
        env := genScheme (K ++ softVars (substSoft (s1 ++ sCheck) F)) (sCheck.onCtx (s1.onCtx ctx)).env (sCheck.onTy rhsTy) ::
          (sCheck.onCtx (s1.onCtx ctx)).env }) ((body.substTyFvars (s1 ++ sCheck)).substTyFvars V) target := by
    rw [← hctxBridge] at hbodyWeak
    exact hbodyWeak
  have hcheckedWF := Subst.onCtx_wf hsCheckLC (Subst.onCtx_wf hs1LC hwf)
  have hcheckedB := Subst.onCtx_below hsCheckB hcle
    (Subst.onCtx_below hs1B hrle hbelow)
  have hcheckedTyB := Subst.onTy_belowFvars hsCheckB (hrB.mono hcle)
  have hbodyWF : CtxWF { (sCheck.onCtx (s1.onCtx ctx)) with
      env := genScheme (K ++ softVars (substSoft (s1 ++ sCheck) F)) (sCheck.onCtx (s1.onCtx ctx)).env (sCheck.onTy rhsTy) ::
        (sCheck.onCtx (s1.onCtx ctx)).env } := by
    intro scheme hs
    rcases List.mem_cons.mp hs with rfl | hs
    · exact genScheme_wf hcheckedLC
    · exact hcheckedWF scheme hs
  have hbodyB : CtxBelow checked { (sCheck.onCtx (s1.onCtx ctx)) with
      env := genScheme (K ++ softVars (substSoft (s1 ++ sCheck) F)) (sCheck.onCtx (s1.onCtx ctx)).env (sCheck.onTy rhsTy) ::
        (sCheck.onCtx (s1.onCtx ctx)).env } := by
    intro scheme hs
    rcases List.mem_cons.mp hs with rfl | hs
    · exact hcheckedTyB.closeOver
    · exact hcheckedB scheme hs
  exact ⟨V, hV, hVP, hagPrefix, hbodyD, hbodyWF, hbodyB, hprefixB⟩

theorem _root_.Infer.sourcePrincipal_letIn
    (hscope : SourceScope K F (.letIn ann rhs body))
    (hr : Infer K F frontier ctx rhs first s1 rhsOut rhsTy)
    (hc : LetCheck K (substSoft s1 F) first rhsTy (ann.substTyFvars s1) checked sCheck)
    (hb : Infer K (substSoft (s1 ++ sCheck) F) checked
      { (sCheck.onCtx (s1.onCtx ctx)) with
        env := genScheme (K ++ softVars (substSoft (s1 ++ sCheck) F)) (sCheck.onCtx (s1.onCtx ctx)).env (sCheck.onTy rhsTy) ::
          (sCheck.onCtx (s1.onCtx ctx)).env }
      (body.substTyFvars (s1 ++ sCheck)) next s2 bodyOut bodyTy)
    (ihr : Infer.SourcePrincipal hr) (ihb : Infer.SourcePrincipal hb) :
    Infer.SourcePrincipal (.letIn hscope hr hc hb) := by
  intro hwf hbelow hK hF ambient target P hS hP hfix hfreeze htyping
  obtain ⟨V, hV, hVP, hagPrefix, hbodyD, hbodyWF, hbodyB, hprefixB⟩ :=
    hr.source_let_frame hscope hc ihr hwf hbelow hK hF ambient target P hS hP hfix hfreeze htyping
  have hle := hr.frontier_le.trans hc.frontier_le
  obtain ⟨R2, hR2, hresult, hR2P, hag2⟩ := ihb hbodyWF hbodyB
    (fun k hk => Nat.lt_of_lt_of_le (hK k hk) hle)
    (substSoft_below hprefixB hle hF) V target P hV
    (fun p hp => Nat.lt_of_lt_of_le (hP p hp) hle) hVP
    ((show SourceScope K F body from fun v hv => hscope v (List.mem_append_right _ hv)).residual_freeze
      (fun v hv => (List.mem_append.mp (hscope v (List.mem_append_right _ hv))).elim
        (hK v) (softVars_lt hF v))
      (Subst.fixes_of_dom_avoids (fun p hp => (List.mem_append.mp hp).elim (hr.dom_avoids p) (hc.dom_avoids p)))
      (fun v hv => hfreeze v (List.mem_append_right _ hv)) hagPrefix) hbodyD
  exact ⟨R2, hR2, hresult, hR2P,
    Subst.AgreesBelow.trans_append hle hagPrefix hprefixB hag2⟩

/-- Residual factorization for a nonempty branch thread. The independent
protected set scopes authored annotations; both common type images are explicit. -/
def _root_.InferBranches.SourcePrincipal
    (_h : InferBranches K F frontier ctx scrutTy resultTy branches next subst completed)
    (_hne : branches ≠ []) : Prop :=
  CtxWF ctx → CtxBelow frontier ctx → (∀ k ∈ K, k < frontier) →
  (∀ soft ∈ F, Ty.BelowFvars frontier soft) →
  ∀ (ambient : Subst) (scrutD resultD : Ty) (P : List Nat),
    (∀ pair ∈ ambient, pair.2.IsLC) → scrutD.IsLC → scrutTy.IsLC → resultTy.IsLC →
    Ty.BelowFvars frontier scrutTy → Ty.BelowFvars frontier resultTy →
    (∀ p ∈ P, p < frontier) →
    (∀ p ∈ P, ambient.onTy (.fvar p) = .fvar p) →
    (∀ v ∈ rigidBranchVars branches, v ∈ K → v ∉ softVars F → ambient.onTy (.fvar v) = .fvar v) →
    resultD = ambient.onTy resultTy → scrutD = ambient.onTy scrutTy →
    (∀ b ∈ branches, BranchTyping Typing P (ambient.onCtx ctx) (b.1, b.2.substTyFvars ambient) scrutD resultD) →
    ∃ residual : Subst, (∀ pair ∈ residual, pair.2.IsLC) ∧
      Subst.AgreesBelow frontier ambient (subst ++ residual) ∧
      (∀ p ∈ P, residual.onTy (.fvar p) = .fvar p) ∧
      resultD = residual.onTy (subst.onTy resultTy)

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
    (h : InferBranches κ F Φ ctx st rt [] Φ' S out) : Φ' = Φ ∧ S = [] := by
  cases h
  exact ⟨rfl, rfl⟩

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

private theorem branch_freeze_frame {κ : List Nat} {F : List Ty} {bs : List (MatchPattern × Input)}
    {ambient solved residual : Subst} {Φ : Nat}
    (hscope : ∀ v ∈ rigidBranchVars bs, v ∈ κ ++ softVars F)
    (hbelow : ∀ v ∈ rigidBranchVars bs, v < Φ)
    (hprefix : ∀ k ∈ κ, solved.onTy (.fvar k) = .fvar k)
    (hfreeze : ∀ v ∈ rigidBranchVars bs, v ∈ κ → v ∉ softVars F → ambient.onTy (.fvar v) = .fvar v)
    (hag : Subst.AgreesBelow Φ ambient (solved ++ residual)) :
    ∀ v ∈ rigidBranchVars (substInputBranches solved bs),
      v ∈ κ → v ∉ softVars (substSoft solved F) → residual.onTy (.fvar v) = .fvar v := by
  exact SourceScope.residual_freeze (input := .match_ (.var 0) bs) hscope hbelow hprefix hfreeze hag
set_option maxRecDepth 4096 in
theorem _root_.InferBranches.sourcePrincipal_of_body
    (h : InferBranches κ F Φ ctx scrutTy ρ brs Φ' S out) (hne : brs ≠ [])
    (bodyIH : ∀ body : Input, body.size < sizeBranches brs →
      ∀ {κ F' f c n s o t} (hb : Infer κ F' f c body n s o t), Infer.SourcePrincipal hb) :
    InferBranches.SourcePrincipal h hne := by
  cases h with
      | nil => exact False.elim (hne rfl)
      | @cons c nbr body rest κ F ctor scrutTy Φ S₀ ctx Φ₁ S₁ bodyOut τb ρ S₂ Φ' S₃ restOut hscope hlook hn h₀Rigid hinfbody h₂Rigid hrest =>
        have h₀ := h₀Rigid.unifies
        have h₂ := h₂Rigid.unifies
        exact fun hwf hbelow hκ hF S₀amb scruT₀ ρe K hS₀amb hscruLC hscrutLC hρLC hbscrut hbρ hKΦ hKfix hfreeze hIMGρ hIMGscru hbrs => by
          have hrawBelow : ∀ v ∈ rigidBranchVars ((.named c nbr, body) :: rest), v < Φ := by
            intro v hv
            exact (List.mem_append.mp (hscope v hv)).elim (hκ v) (softVars_lt hF v)
          have hbodyScope : SourceScope κ F body := fun v hv => hscope v (List.mem_append_left _ hv)
          have hbodyBelow : ∀ v ∈ body.rigidVars, v < Φ := fun v hv => hrawBelow v (List.mem_append_left _ hv)
          have hrestScope : ∀ v ∈ rigidBranchVars rest, v ∈ κ ++ softVars F :=
            fun v hv => hscope v (List.mem_append_right _ hv)
          have hrestBelow : ∀ v ∈ rigidBranchVars rest, v < Φ :=
            fun v hv => hrawBelow v (List.mem_append_right _ hv)
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
          have hsource0 : body.substTyFvars S₀amb = (body.substTyFvars S₀).substTyFvars R₀ := by
            rw [← Input.substTyFvars_append]
            exact body.substTyFvars_congr (fun v hv => hAgreeBelow₀ v (hbodyBelow v hv))
          have hF0 := substSoft_below hS₀_bel hfle₀ hF
          have hfreeze0 := hbodyScope.residual_freeze hbodyBelow
            (Subst.fixes_of_dom_avoids h₀Rigid.dom_avoids)
            (fun v hv => hfreeze v (List.mem_append_left _ hv)) hAgreeBelow₀
          obtain ⟨R_b, hR_b, htyb, hR_bK, hagb⟩ :=
            (bodyIH (body.substTyFvars S₀) (by simp only [Input.size_substTyFvars, sizeBranches]; omega) hinfbody)
              hwf_body hbelow_body (fun k hk => Nat.lt_of_lt_of_le (hκ k hk) hfle₀) hF0
              R₀ ρe K hR₀ hKΦ₀ hR₀K hfreeze0 (hsource0 ▸ hbE')
          have hle_b : Φ + ctor.paramCount ≤ Φ₁ := Infer.frontier_le hinfbody
          have hKΦ₁ : ∀ k ∈ K, k < Φ₁ := fun k hk => lt_of_lt_of_le (hKΦ₀ k hk) hle_b
          have hbodyLC := Infer.lc hinfbody hwf_body
          have hτb_lc : τb.IsLC := hbodyLC.1
          have hS₁lc : ∀ p ∈ S₁, p.2.IsLC := hbodyLC.2
          have hbb := Infer.belowFvars hinfbody hbelow_body (fun k hk => Nat.lt_of_lt_of_le (hκ k hk) hfle₀) hF0
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
          have hAgreePrefix : Subst.AgreesBelow Φ S₀amb ((S₀ ++ S₁ ++ S₂) ++ R_u) := by
            have hA : Subst.AgreesBelow Φ S₀amb ((S₀ ++ (S₁ ++ S₂)) ++ R_u) :=
              @Subst.AgreesBelow.trans_append Φ (Φ + ctor.paramCount) S₀amb S₀ R₀ (S₁ ++ S₂) R_u
                hfle₀ hAgreeBelow₀ hS₀_bel
                (@Subst.AgreesBelow.trans_append (Φ + ctor.paramCount) Φ₁ R₀ S₁ R_b S₂ R_u
                  hle_b hagb hS₁_bel hAgreeUni)
            simpa [List.append_assoc] using hA
          have hF' : ∀ t ∈ substSoft (S₀ ++ S₁ ++ S₂) F, Ty.BelowFvars Φ₁ t := by
            simpa only [substSoft_append] using substSoft_below hS₂_bel (le_refl _)
              (substSoft_below hS₁_bel hle_b hF0)
          have hprefixFix : ∀ k ∈ κ, (S₀ ++ S₁ ++ S₂).onTy (.fvar k) = .fvar k := by
            intro k hk
            simp only [Subst.onTy_append, Subst.fixes_of_dom_avoids h₀Rigid.dom_avoids k hk,
              Subst.fixes_of_dom_avoids hinfbody.dom_avoids k hk,
              Subst.fixes_of_dom_avoids h₂Rigid.dom_avoids k hk]
          have hfreeze' := branch_freeze_frame hrestScope hrestBelow hprefixFix
            (fun v hv => hfreeze v (List.mem_append_right _ hv)) hAgreePrefix
          have hbr' := branch_candidates_frame hrestBelow hAgreePrefix hctxeq'
            (fun b hb => hbrs b (List.mem_cons_of_mem _ hb))
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
              InferBranches.sourcePrincipal_of_body hrest (by
                intro heq
                cases rest with
                | nil => exact hrestNe rfl
                | cons b bs => cases heq)
                (fun b hb {_ _ _ _ _ _ _ _} hi => bodyIH b (by
                  rw [sizeBranches_substInputBranches] at hb
                  simp only [sizeBranches]; omega) hi)
                hwf' hbelow' (fun k hk => Nat.lt_of_lt_of_le (hκ k hk) (by omega)) hF' R_u scruT₀ ρe K
                hR_u hscruLC hscrutTy'lc hρ'lc hbscrut' hbρ' hKΦ₁ hR_uK hfreeze' hρImg_u hscrutImg' hbr'
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
      | @consWild body rest κ F Φ ctx Φ₁ S₁ bodyOut τb ρ S₂ scrutTy Φ' S₃ restOut hscope hinfbody h₂Rigid hrest =>
        have h₂ := h₂Rigid.unifies
        exact fun hwf hbelow hκ hF S₀amb scruT₀ ρe K hS₀amb hscruLC hscrutLC hρLC hbscrut hbρ hKΦ hKfix hfreeze hIMGρ hIMGscru hbrs => by
          have hrawBelow : ∀ v ∈ rigidBranchVars ((.wildcard, body) :: rest), v < Φ := by
            intro v hv
            exact (List.mem_append.mp (hscope v hv)).elim (hκ v) (softVars_lt hF v)
          have hbodyScope : SourceScope κ F body := fun v hv => hscope v (List.mem_append_left _ hv)
          have hbodyBelow : ∀ v ∈ body.rigidVars, v < Φ := fun v hv => hrawBelow v (List.mem_append_left _ hv)
          have hrestScope : ∀ v ∈ rigidBranchVars rest, v ∈ κ ++ softVars F :=
            fun v hv => hscope v (List.mem_append_right _ hv)
          have hrestBelow : ∀ v ∈ rigidBranchVars rest, v < Φ :=
            fun v hv => hrawBelow v (List.mem_append_right _ hv)
          have hdhead := hbrs (.wildcard, body) (List.mem_cons_self ..)
          have hbodyD : Typing K (S₀amb.onCtx ctx) (body.substTyFvars S₀amb) ρe := by
            cases hdhead with
            | wildcard hbodyty => exact hbodyty
          obtain ⟨R_b, hR_b, htyb, hR_bK, hagb⟩ :=
            (bodyIH body (by simp only [sizeBranches]; omega) hinfbody)
              hwf hbelow hκ hF S₀amb ρe K hS₀amb hKΦ hKfix
                (fun v hv => hfreeze v (List.mem_append_left _ hv)) hbodyD
          have hle_b : Φ ≤ Φ₁ := Infer.frontier_le hinfbody
          have hKΦ₁ : ∀ k ∈ K, k < Φ₁ := fun k hk => lt_of_lt_of_le (hKΦ k hk) hle_b
          have hbodyLC := Infer.lc hinfbody hwf
          have hτb_lc : τb.IsLC := hbodyLC.1
          have hS₁lc : ∀ p ∈ S₁, p.2.IsLC := hbodyLC.2
          have hbb := Infer.belowFvars hinfbody hbelow hκ hF
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
          have hAgreePrefix : Subst.AgreesBelow Φ S₀amb ((S₁ ++ S₂) ++ R_u) :=
            Subst.AgreesBelow.trans_append hle_b hagb hS₁_bel hAgreeUni
          have hF' : ∀ t ∈ substSoft (S₁ ++ S₂) F, Ty.BelowFvars Φ₁ t := by
            simpa only [substSoft_append] using substSoft_below hS₂_bel (le_refl _)
              (substSoft_below hS₁_bel hle_b hF)
          have hprefixFix : ∀ k ∈ κ, (S₁ ++ S₂).onTy (.fvar k) = .fvar k := by
            intro k hk
            simp only [Subst.onTy_append, Subst.fixes_of_dom_avoids hinfbody.dom_avoids k hk,
              Subst.fixes_of_dom_avoids h₂Rigid.dom_avoids k hk]
          have hfreeze' := branch_freeze_frame hrestScope hrestBelow hprefixFix
            (fun v hv => hfreeze v (List.mem_append_right _ hv)) hAgreePrefix
          have hbr' := branch_candidates_frame hrestBelow hAgreePrefix hctxeq'
            (fun b hb => hbrs b (List.mem_cons_of_mem _ hb))
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
              InferBranches.sourcePrincipal_of_body hrest (by
                intro heq
                cases rest with
                | nil => exact hrestNe rfl
                | cons b bs => cases heq)
                (fun b hb {_ _ _ _ _ _ _ _} hi => bodyIH b (by
                  rw [sizeBranches_substInputBranches] at hb
                  simp only [sizeBranches]; omega) hi)
                hwf' hbelow' (fun k hk => Nat.lt_of_lt_of_le (hκ k hk) hle_b) hF' R_u scruT₀ ρe K
                hR_u hscruLC hscrutTy'lc hρ'lc hbscrut' hbρ' hKΦ₁ hR_uK hfreeze' hρImg_u hscrutImg' hbr'
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

termination_by sizeBranches brs
decreasing_by all_goals (subst_vars; simp only [sizeBranches_substInputBranches, sizeBranches]; omega)


theorem _root_.Infer.sourcePrincipal_match
    (hscope : SourceScope K F (.match_ scrut branches))
    (hs : Infer K F frontier ctx scrut first s1 scrutOut scrutTy)
    (hne : branches ≠ [])
    (hb : InferBranches K (substSoft s1 F) (first + 1) (s1.onCtx ctx) scrutTy (.fvar first)
      (substInputBranches s1 branches) next s2 branchesOut)
    (ihs : Infer.SourcePrincipal hs)
    (bodyIH : ∀ body : Input, body.size < sizeBranches branches →
      ∀ {κ F' f c n s o t} (hi : Infer κ F' f c body n s o t), Infer.SourcePrincipal hi) :
    Infer.SourcePrincipal (.match_ hscope hs hne hb) := by
  intro hwf hbelow hK hF ambient target P hS hP hfix hfreeze htyping
  obtain ⟨scrutD, hsD, _, hbD⟩ := htyping.match_inv
  obtain ⟨R1, hR1, hscrut, hR1P, hag1⟩ := ihs hwf hbelow hK hF ambient
    scrutD P hS hP hfix (fun v hv => hfreeze v (List.mem_append_left _ hv)) hsD
  have hle := hs.frontier_le
  obtain ⟨hsB, hs1B⟩ := hs.belowFvars hbelow hK hF
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
  have hagSU : Subst.AgreesBelow frontier ambient (s1 ++ U) := by
    intro v hv
    exact (hag1 v hv).trans (by
      rw [Subst.onTy_append, Subst.onTy_append]
      exact Subst.onTy_congr hagU (Subst.onTy_belowFvars hs1B (.fvar (Nat.lt_of_lt_of_le hv hle))))
  have hbranchScope : ∀ v ∈ rigidBranchVars branches, v ∈ K ++ softVars F :=
    fun v hv => hscope v (List.mem_append_right _ hv)
  have hbranchBelow : ∀ v ∈ rigidBranchVars branches, v < frontier := fun v hv =>
    (List.mem_append.mp (hbranchScope v hv)).elim (hK v) (softVars_lt hF v)
  have hfreezeB := branch_freeze_frame hbranchScope hbranchBelow
    (Subst.fixes_of_dom_avoids hs.dom_avoids)
    (fun v hv => hfreeze v (List.mem_append_right _ hv)) hagSU
  have hbrU := branch_candidates_frame hbranchBelow hagSU hctxeq (by
    intro b hb
    exact hbD (b.1, b.2.substTyFvars ambient) (by
      rw [substInputBranches_eq_map]
      exact List.mem_map.mpr ⟨b, hb, rfl⟩))
  have hne' : substInputBranches s1 branches ≠ [] := by
    cases branches with
    | nil => exact False.elim (hne rfl)
    | cons b bs => intro heq; cases heq
  have ihb := hb.sourcePrincipal_of_body hne' (fun body hbody {_ _ _ _ _ _ _ _} hi =>
    bodyIH body (by rwa [sizeBranches_substInputBranches] at hbody) hi)
  obtain ⟨R2, hR2, hag2, hR2P, htarget⟩ := ihb hctxWF
    (fun M hM => (hctxB M hM).mono (by omega))
    (fun k hk => by have := hK k hk; omega)
    (substSoft_below (fun p hp => (hs1B p hp).mono (Nat.le_succ _))
      (hle.trans (Nat.le_succ _)) hF)
    U scrutD target P hU hsD.regular hsLC .fvar
    (hsB.mono (by omega)) (.fvar (by omega))
    (fun p hp => by have := hP p hp; omega) hUP hfreezeB hUtarget.symm hUst hbrU
  have hag2' : Subst.AgreesBelow first R1 (s2 ++ R2) := fun v hv =>
    (hagU v hv).trans (hag2 v (by omega))
  exact ⟨R2, hR2, htarget, hR2P, Subst.AgreesBelow.trans_append hle hag1 hs1B hag2'⟩

private theorem branch_size_lt {branch : MatchPattern × Input}
    (h : branch ∈ branches) : branch.2.size < sizeBranches branches := by
  induction branches with
  | nil => cases h
  | cons head rest ih =>
    rcases List.mem_cons.mp h with rfl | h
    · simp only [sizeBranches]; omega
    · have := ih h; simp only [sizeBranches]; omega

theorem _root_.Infer.principal_letSignature {rhs body : Input} {ann : LetAnn}
    (hprefix : written = freshVars frontier ann.paramCount)
    (havoid : ∀ name ∈ written, name ∉ K) (hraw : ∀ v ∈ rhs.rigidVars, v ∈ K)
    (hr : Infer (K ++ written) (frontier + ann.paramCount) ctx (rhs.openTyVars written) first s1 rhsOut rhsTy)
    (hc : SignatureCheck K written first rhsTy ann checked sCheck)
    (hescape : ∀ name ∈ written, name ∉ (sCheck.onCtx (s1.onCtx ctx)).env.freeVars)
    (hb : Infer K checked
      { sCheck.onCtx (s1.onCtx ctx) with
        env := signatureScheme ann K written (sCheck.onCtx (s1.onCtx ctx)) (sCheck.onTy rhsTy) ::
          (sCheck.onCtx (s1.onCtx ctx)).env } body next s2 bodyOut bodyTy)
    (ihr : Infer.Principal hr) (ihb : Infer.Principal hb) :
    Infer.Principal (.letSignature hprefix havoid hraw hr hc hescape hb) := by
  intro hwf hbelow hK ambient target P hS hP hfix ht
  subst written
  have hmode : ann.isSignature = true := by cases hc <;> rfl
  obtain ⟨W, M, L, hMoved, hMovedFix, hBackAmbient, hBackLC, hBackP, hRestore,
      hM, hann, hrhs, hfits, htypes, hbodyD, hYsM, hYsCtx, hYsImages⟩ :=
    ht.signature_dodge (K := K) hmode hbelow hP hK hS hfix
  obtain ⟨V, hV, hVP, hagPrefix, hbodyV, hbodyWF, hbodyB, hprefixB⟩ :=
    hr.signature_frame hc ihr rfl hwf hbelow hK hMoved hP hMovedFix hM hann hrhs
      hfits htypes hbodyD hYsM hYsCtx hYsImages
  have hleOpen := hr.frontier_le.trans hc.frontier_le
  have hle : frontier ≤ checked := (Nat.le_add_right frontier ann.paramCount).trans hleOpen
  obtain ⟨R, hR, hresult, hRP, hagBody⟩ := ihb hbodyWF hbodyB
    (fun k hk => Nat.lt_of_lt_of_le (hK k hk) hle) V _ P hV
    (fun p hp => Nat.lt_of_lt_of_le (hP p hp) hle)
    (fun p hp => hVP p (List.mem_append_left _ hp)) hbodyV
  have hag := Subst.AgreesBelow.trans_append hleOpen hagPrefix hprefixB hagBody
  refine ⟨R ++ blockListBack frontier W ann.paramCount,
    (fun p hp => (List.mem_append.mp hp).elim (hR p) (hBackLC p)), ?_, ?_, ?_⟩
  · simpa only [Subst.onTy_append, ← hresult] using hRestore.symm
  · intro p hp
    rw [Subst.onTy_append, hRP p hp]
    exact hBackP p hp
  · intro v hv
    have heq := congrArg (blockListBack frontier W ann.paramCount).onTy (hag v (by omega))
    rw [hBackAmbient v hv] at heq
    simpa only [Subst.onTy_append, List.append_assoc] using heq

/-- Every elaboration is principal for independent input typings, retaining
ordinary Core's residual factorization and protected-set guarantees. -/
theorem _root_.Infer.principal (h : Infer K frontier ctx input next subst output ty) :
    Infer.Principal h := by
  match h with
  | .backend hemb hi hctx hK hr => exact Infer.principal_backend hemb hi hctx hK hr
  | .lambda hs hb => exact Infer.principal_lambda hs hb hb.principal
  | .app hf ha hu => exact Infer.principal_app hf ha hu hf.principal ha.principal
  | .letIn hr hc hb => exact Infer.principal_letIn hr hc hb hr.principal hb.principal
  | .letSignature hp ha hs hr hc he hb =>
    exact Infer.principal_letSignature hp ha hs hr hc he hb hr.principal hb.principal
  | .match_ hs hne hb =>
      exact Infer.principal_match hs hne hb hs.principal
        (hb.principal_of_body hne (fun b hm {_ _ _ _ _ _} hi => hi.principal))
termination_by input.size
decreasing_by
  all_goals (simp only [Input.size, Input.size_openTyVars]; first | omega | have := branch_size_lt hm; omega)

end Elaboration
