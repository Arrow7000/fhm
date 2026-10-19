import FHM.Elaboration.Typing

/-! Canonical inference elaborates partial annotations while returning completed
Core. Whole completed subtrees reuse the verified backend once; partial lambda,
application, let, and match spines share the same recursive inference judgment.
-/

namespace Elaboration

inductive Seed (K : List Nat) (frontier : Nat) : Option Template → Ty → Nat → Prop
  | absent : Seed K frontier none (.fvar frontier) (frontier + 1)
  | annotated :
      template.allocate frontier = (next, ty) → ty.IsLC →
      (∀ v ∈ template.rigidVars, v ∈ K) →
      Seed K frontier (some template) ty next

inductive LetCheck (K : List Nat) (frontier : Nat) (ty : Ty) : LetAnn → Nat → Subst → Prop
  | absent : LetCheck K frontier ty .absent frontier []
  /-- A whole-signature `_` imposes no constraint on the RHS monotype. This
  eliminates an immediately solved, otherwise unused fresh metavariable. -/
  | hole : LetCheck K frontier ty (.template .hole) frontier []
  | template :
      template.allocate frontier = (next, expected) → expected.IsLC →
      (∀ v ∈ template.rigidVars, v ∈ K) →
      RigidUnify K ty expected subst →
      LetCheck K frontier ty (.template template) next subst

/-- A signed RHS is checked under its written forall prefix. Only those
written skolems and ambient K are protected; anonymous holes stay flexible. -/
inductive SignatureCheck (K written : List Nat) (frontier : Nat) (ty : Ty) :
    LetAnn → Nat → Subst → Prop
  | complete {scheme : PolyTy} : scheme.WF → (∀ v ∈ scheme.body.freeVars, v ∈ K) →
      RigidUnify (K ++ written) ty (scheme.openVars written) subst →
      SignatureCheck K written frontier ty (.complete scheme) frontier subst
  | partialSignature {template : Template} :
      (template.openTyVarsFrom 0 written).allocate frontier = (next, expected) →
      expected.IsLC → (∀ v ∈ template.rigidVars, v ∈ K) →
      RigidUnify (K ++ written) ty expected subst →
      SignatureCheck K written frontier ty (.partialForall count template) next subst

def LetAnn.isSignature : LetAnn → Bool
  | .complete _ | .partialForall _ _ => true
  | .absent | .template _ => false

/-- Written binders keep their authored order; inferred binders follow them. -/
def signatureNames (ann : LetAnn) (K written : List Nat) (ctx : Ctx) (ty : Ty) : List Nat :=
  match ann with
  | .complete _ => written
  | _ => written ++ genVars (K ++ written) ctx.env ty

def signatureScheme (ann : LetAnn) (K written : List Nat) (ctx : Ctx) (ty : Ty) : PolyTy :=
  match ann with
  | .complete scheme => scheme
  | _ => let names := signatureNames ann K written ctx ty
         ⟨names.length, Ty.closeOver names ty⟩

def lambdaOutput (ann : Option Template) (param : Ty) (subst : Subst) (body : Expr) : Expr :=
  .lambda (ann.map fun _ => subst.onTy param) body

def letOutput (scheme : PolyTy) (names : List Nat) (rhs body : Expr) (subst : Subst) : Expr :=
  .letIn (some (subst.onPolyTy scheme)) ((rhs.closeTyVars names).substTyFvars subst) body

mutual
/-- Authoritative input/output judgment for the proved anonymous fragment.
The `backend` rule uses the existing judgment only after a whole subtree embeds
as completed Core. Partial annotation modes never use that rule. -/

inductive _root_.Infer : List Nat → Nat → Ctx → Input → Nat → Subst → Expr → Ty → Prop
  | backend :
      input.toCore = some core →
      CoreBackend.Infer K frontier ctx core next subst ty →
      CtxBelow frontier ctx → (∀ k ∈ K, k < frontier) →
      (∀ v ∈ core.tyFreeVars, v ∈ K) →
      Infer K frontier ctx input next subst core ty
  | lambda :
      Seed K frontier ann param initial →
      Infer K initial { ctx with env := PolyTy.mkTrivial param :: ctx.env }
        body next subst completed bodyTy →
      Infer K frontier ctx (.lambda ann body) next subst
        (lambdaOutput ann param subst completed) (.arrow (subst.onTy param) bodyTy)
  | app :
      Infer K frontier ctx f first s1 fOut fTy →
      Infer K first (s1.onCtx ctx) arg second s2 argOut argTy →
      RigidUnify K (s2.onTy fTy) (.arrow argTy (.fvar second)) s3 →
      Infer K frontier ctx (.app f arg) (second + 1) (s1 ++ s2 ++ s3)
        (.app (fOut.substTyFvars (s2 ++ s3)) (argOut.substTyFvars s3)) (s3.onTy (.fvar second))
  | letIn :
      Infer K frontier ctx rhs first s1 rhsOut rhsTy →
      LetCheck K first rhsTy ann checked sCheck →
      Infer K checked
        { (sCheck.onCtx (s1.onCtx ctx)) with
          env := genScheme K (sCheck.onCtx (s1.onCtx ctx)).env (sCheck.onTy rhsTy) ::
            (sCheck.onCtx (s1.onCtx ctx)).env }
        body next s2 bodyOut bodyTy →
      Infer K frontier ctx (.letIn ann rhs body) next (s1 ++ sCheck ++ s2)
        (letOutput (genScheme K (sCheck.onCtx (s1.onCtx ctx)).env (sCheck.onTy rhsTy))
          (genVars K (sCheck.onCtx (s1.onCtx ctx)).env (sCheck.onTy rhsTy))
          (rhsOut.substTyFvars sCheck) bodyOut s2) bodyTy

  | letSignature :
      written = freshVars frontier ann.paramCount →
      (∀ name ∈ written, name ∉ K) → (∀ v ∈ rhs.rigidVars, v ∈ K) →
      Infer (K ++ written) (frontier + ann.paramCount) ctx (rhs.openTyVars written)
        first s1 rhsOut rhsTy →
      SignatureCheck K written first rhsTy ann checked sCheck →
      (∀ name ∈ written, name ∉ (sCheck.onCtx (s1.onCtx ctx)).env.freeVars) →
      Infer K checked
        { (sCheck.onCtx (s1.onCtx ctx)) with
          env := signatureScheme ann K written (sCheck.onCtx (s1.onCtx ctx)) (sCheck.onTy rhsTy) ::
            (sCheck.onCtx (s1.onCtx ctx)).env }
        body next s2 bodyOut bodyTy →
      Infer K frontier ctx (.letIn ann rhs body) next (s1 ++ sCheck ++ s2)
        (letOutput (signatureScheme ann K written (sCheck.onCtx (s1.onCtx ctx)) (sCheck.onTy rhsTy))
          (signatureNames ann K written (sCheck.onCtx (s1.onCtx ctx)) (sCheck.onTy rhsTy))
          (rhsOut.substTyFvars sCheck) bodyOut s2) bodyTy

  | match_ :
      Infer K frontier ctx scrut first s1 scrutOut scrutTy →
      branches ≠ [] →
      InferBranches K (first + 1) (s1.onCtx ctx) scrutTy (.fvar first)
        branches next s2 branchesOut →
      Infer K frontier ctx (.match_ scrut branches) next (s1 ++ s2)
        (.match_ (scrutOut.substTyFvars s2) branchesOut) (s2.onTy (.fvar first))

/-- Branch inference threads the same ambient rigid set and returns completed
branch bodies alongside the substitution. Constructor allocation and constraint
order match the complete-Core backend. -/
inductive _root_.InferBranches : List Nat → Nat → Ctx → Ty → Ty →
    List (MatchPattern × Input) → Nat → Subst → List (MatchPattern × Expr) → Prop
  | nil : InferBranches K frontier ctx scrutTy resultTy [] frontier [] []
  | consWild :
      Infer K frontier ctx body first s1 bodyOut bodyTy →
      RigidUnify K bodyTy (s1.onTy resultTy) s2 →
      InferBranches K first (s2.onCtx (s1.onCtx ctx))
        (s2.onTy (s1.onTy scrutTy)) (s2.onTy (s1.onTy resultTy)) rest next s3 restOut →
      InferBranches K frontier ctx scrutTy resultTy ((.wildcard, body) :: rest) next (s1 ++ s2 ++ s3)
        ((.wildcard, bodyOut.substTyFvars (s2 ++ s3)) :: restOut)
  | cons :
      LookupList.get? ctx.ctors name = some ctor →
      count = ctor.contents.length →
      RigidUnify K scrutTy (.customTy ctor.tyName ((freshVars frontier ctor.paramCount).map Ty.fvar)) s0 →
      Infer K (frontier + ctor.paramCount)
        { (s0.onCtx ctx) with
          env := (ctor.contents.map (Ty.openWith (((freshVars frontier ctor.paramCount).map Ty.fvar).map s0.onTy))).map PolyTy.mkTrivial ++
              (s0.onCtx ctx).env }
        body first s1 bodyOut bodyTy →
      RigidUnify K bodyTy (s1.onTy (s0.onTy resultTy)) s2 →
      InferBranches K first (s2.onCtx (s1.onCtx (s0.onCtx ctx)))
        (s2.onTy (s1.onTy (s0.onTy scrutTy))) (s2.onTy (s1.onTy (s0.onTy resultTy)))
        rest next s3 restOut →
      InferBranches K frontier ctx scrutTy resultTy ((.named name count, body) :: rest) next
        (s0 ++ s1 ++ s2 ++ s3) ((.named name count, bodyOut.substTyFvars (s2 ++ s3)) :: restOut)
end

theorem Seed.lc (h : Seed K frontier ann param initial) : param.IsLC := by
  cases h with
  | absent => exact .fvar
  | annotated _ hlc _ => exact hlc

theorem Seed.fits (h : Seed K frontier ann param initial) :
    ∀ template, ann = some template → template.Fits param := by
  cases h with
  | absent => intro _ heq; cases heq
  | @annotated next param sourceTemplate heq _ _ =>
      intro t ht
      have hfit := Template.allocate_fits sourceTemplate frontier
      have hequal := Option.some.inj ht
      subst t
      rwa [heq] at hfit

theorem Seed.rigid (h : Seed K frontier ann param initial) :
    ∀ template, ann = some template → ∀ v ∈ template.rigidVars, v ∈ K := by
  cases h with
  | absent => intro _ heq; cases heq
  | annotated _ _ hrigid => intro _ heq; cases heq; exact hrigid

theorem LetCheck.dom_avoids (h : LetCheck K frontier ty ann next subst) :
    ∀ pair ∈ subst, pair.1 ∉ K := by
  cases h with
  | absent => simp
  | hole => simp
  | template _ _ _ huni => exact huni.dom_avoids

theorem LetCheck.lc (h : LetCheck K frontier ty ann next subst) (hlc : ty.IsLC) :
    ∀ pair ∈ subst, pair.2.IsLC := by
  cases h with
  | absent => simp
  | hole => simp
  | template _ he _ huni => exact huni.unifies.lc hlc he

theorem LetCheck.fits (h : LetCheck K frontier ty ann next subst) :
    ann.FitsMono (subst.onTy ty) := by
  cases h with
  | absent => trivial
  | hole => exact .hole
  | @template next expected subst t heq _ hrigid huni =>
      have hfit := Template.allocate_fits t frontier
      rw [heq] at hfit
      change t.Fits (subst.onTy ty)
      rw [huni.unifies.unifies]
      exact hfit.onSubst hrigid huni.dom_avoids

theorem LetCheck.rigid (h : LetCheck K frontier ty ann next subst) :
    ∀ template, ann = .template template → ∀ v ∈ template.rigidVars, v ∈ K := by
  cases h with
  | absent => intro _ heq; cases heq
  | hole => intro _ heq; cases heq; simp [Template.rigidVars]
  | template _ _ hrigid _ => intro _ heq; cases heq; exact hrigid

mutual
theorem Template.open_scope {template : Template} {K written : List Nat}
    (h : ∀ v ∈ template.rigidVars, v ∈ K) :
    ∀ v ∈ (template.openTyVarsFrom 0 written).rigidVars, v ∈ K ++ written := by
  cases template with
  | fixed ty =>
    intro v hv
    exact (Ty.freeVars_openVarsFrom_subset v hv).elim
      (fun hv => List.mem_append_left _ (h v hv)) (List.mem_append_right _)
  | hole => intro _ hv; cases hv
  | arrow a b =>
    intro v hv
    exact (List.mem_append.mp hv).elim
      (Template.open_scope (fun w hw => h w (List.mem_append_left _ hw)) v)
      (Template.open_scope (fun w hw => h w (List.mem_append_right _ hw)) v)
  | custom _ ts => exact templateList_open_scope h
private theorem templateList_open_scope {templates : List Template} {K written : List Nat}
    (h : ∀ v ∈ rigidVarsList templates, v ∈ K) :
    ∀ v ∈ rigidVarsList (openTemplateList 0 written templates), v ∈ K ++ written := by
  cases templates with
  | nil => intro _ hv; cases hv
  | cons t ts =>
    intro v hv
    exact (List.mem_append.mp hv).elim
      (Template.open_scope (fun w hw => h w (List.mem_append_left _ hw)) v)
      (templateList_open_scope (fun w hw => h w (List.mem_append_right _ hw)) v)
end

theorem SignatureCheck.dom_avoids (h : SignatureCheck K written frontier ty ann next subst) :
    ∀ pair ∈ subst, pair.1 ∉ K ++ written := by
  cases h with
  | complete _ _ hu => exact hu.dom_avoids
  | partialSignature _ _ _ hu => exact hu.dom_avoids

theorem SignatureCheck.rigid (h : SignatureCheck K written frontier ty ann next subst) :
    ∀ v ∈ ann.rigidVars, v ∈ K := by
  cases h with
  | complete _ hr _ => exact hr
  | partialSignature _ _ hr _ => exact hr

theorem SignatureCheck.lc (h : SignatureCheck K written frontier ty ann next subst)
    (hprefix : written.length = ann.paramCount) (hlc : ty.IsLC) :
    ∀ pair ∈ subst, pair.2.IsLC := by
  cases h with
  | complete hwf _ hu => exact hu.unifies.lc hlc (PolyTy.openVars_isLC hwf hprefix.ge)
  | partialSignature _ he _ hu => exact hu.unifies.lc hlc he

theorem SignatureCheck.completion (h : SignatureCheck K written frontier ty ann next subst)
    (hprefix : written.length = ann.paramCount) :
    ann.SignatureCompletion written (subst.onTy ty)
      (signatureScheme ann K written ctx (subst.onTy ty))
      (signatureNames ann K written ctx (subst.onTy ty)) := by
  cases h with
  | @complete subst scheme _ hr hu =>
    refine .complete hprefix ?_
    have hfixed : subst.onTy (scheme.openVars written) = scheme.openVars written := by
      apply Subst.onTy_eq_self_of_fixes
      intro v hv
      rcases Ty.freeVars_openVars_subset v hv with hv | hv
      · exact Subst.fixes_of_dom_avoids hu.dom_avoids v (List.mem_append_left _ (hr v hv))
      · exact Subst.fixes_of_dom_avoids hu.dom_avoids v (List.mem_append_right _ hv)
    exact hu.unifies.unifies.trans hfixed
  | @partialSignature next expected subst count template heq _ hr hu =>
    refine .partialSignature hprefix ?_
    have hfit := Template.allocate_fits (template.openTyVarsFrom 0 written) frontier
    rw [heq] at hfit
    rw [hu.unifies.unifies]
    exact hfit.onSubst (Template.open_scope hr) hu.dom_avoids

theorem SignatureCheck.scheme_wf (h : SignatureCheck K written frontier ty ann next subst)
    (hlc : (subst.onTy ty).IsLC) :
    (signatureScheme ann K written ctx (subst.onTy ty)).WF := by
  cases h with
  | complete hwf _ _ => exact hwf
  | partialSignature _ _ _ _ => exact Ty.closeOver_preserves_bvars hlc

theorem SignatureCheck.names_avoid (h : SignatureCheck K written frontier ty ann next subst)
    (havoid : ∀ name ∈ written, name ∉ K) :
    ∀ name ∈ signatureNames ann K written ctx (subst.onTy ty), name ∉ K := by
  cases h with
  | complete _ _ _ => exact havoid
  | partialSignature _ _ _ _ =>
    intro name hn hk
    rcases List.mem_append.mp hn with hn | hn
    · exact havoid name hn hk
    · exact genVars_not_mem_rigid hn (List.mem_append_left _ hk)

theorem SignatureCheck.names_nodup (h : SignatureCheck K written frontier ty ann next subst)
    (hnd : written.Nodup) : (signatureNames ann K written ctx (subst.onTy ty)).Nodup := by
  cases h with
  | complete _ _ _ => exact hnd
  | partialSignature _ _ _ _ =>
    apply List.nodup_append.mpr
    refine ⟨hnd, genVars_nodup, ?_⟩
    intro name hw other hg heq
    subst other
    exact genVars_not_mem_rigid hg (List.mem_append_right _ hw)

theorem SignatureCheck.names_fresh (h : SignatureCheck K written frontier ty ann next subst)
    (havoid : ∀ name ∈ written, name ∉ ctx.env.freeVars) :
    ∀ name ∈ signatureNames ann K written ctx (subst.onTy ty), name ∉ ctx.env.freeVars := by
  cases h with
  | complete _ _ _ => exact havoid
  | partialSignature _ _ _ _ =>
    intro name hn
    rcases List.mem_append.mp hn with hn | hn
    · exact havoid name hn
    · exact genVars_not_mem hn

theorem SignatureCheck.scheme_eq_close (h : SignatureCheck K written frontier ty ann next subst)
    (hlen : written.length = ann.paramCount) (hnd : written.Nodup)
    (havoid : ∀ name ∈ written, name ∉ K) :
    signatureScheme ann K written ctx (subst.onTy ty) =
      ⟨(signatureNames ann K written ctx (subst.onTy ty)).length,
        Ty.closeOver (signatureNames ann K written ctx (subst.onTy ty)) (subst.onTy ty)⟩ := by
  have hcomp := h.completion (ctx := ctx) hlen
  cases h with
  | @complete subst scheme hwf hr _ =>
    cases hcomp with
    | complete hl heq =>
      simp only [signatureScheme, signatureNames]
      rw [heq, PolyTy.openVars, Ty.closeOver_openVars_self hnd (by simpa only [hl] using hwf)
        (fun name hn hv => havoid name hn (hr name hv))]
      cases scheme
      simp only [PolyTy.mk.injEq]
      exact ⟨hl.symm, True.intro⟩
  | partialSignature _ _ _ _ => rfl

private theorem avoids_append {K : List Nat} {S T : Subst}
    (hS : ∀ p ∈ S, p.1 ∉ K) (hT : ∀ p ∈ T, p.1 ∉ K) :
    ∀ p ∈ S ++ T, p.1 ∉ K :=
  fun p hp => (List.mem_append.mp hp).elim (hS p) (hT p)

mutual
theorem _root_.Infer.dom_avoids (h : Infer K frontier ctx input next subst output ty) :
    ∀ pair ∈ subst, pair.1 ∉ K := by
  match h with
  | .backend _ hi _ _ _ => exact hi.dom_avoids
  | .lambda _ hb => exact hb.dom_avoids
  | .app hf ha hu => exact avoids_append (avoids_append hf.dom_avoids ha.dom_avoids) hu.dom_avoids
  | .letIn hr hc hb => exact avoids_append (avoids_append hr.dom_avoids hc.dom_avoids) hb.dom_avoids
  | .letSignature _ _ _ hr hc _ hb =>
    exact avoids_append (avoids_append
      (fun p hp hk => hr.dom_avoids p hp (List.mem_append_left _ hk))
      (fun p hp hk => hc.dom_avoids p hp (List.mem_append_left _ hk))) hb.dom_avoids
  | .match_ hs _ hb => exact avoids_append hs.dom_avoids hb.dom_avoids
termination_by (input.size, 0)
decreasing_by all_goals (simp only [Input.size, Input.size_openTyVars]; omega)

theorem _root_.InferBranches.dom_avoids
    (h : InferBranches K frontier ctx scrutTy resultTy branches next subst completed) :
    ∀ pair ∈ subst, pair.1 ∉ K := by
  match h with
  | .nil => simp
  | .consWild hb hu hr => exact avoids_append (avoids_append hb.dom_avoids hu.dom_avoids) hr.dom_avoids
  | .cons _ _ hu0 hb hu hr =>
    exact avoids_append (avoids_append (avoids_append hu0.dom_avoids hb.dom_avoids) hu.dom_avoids) hr.dom_avoids
termination_by (sizeBranches branches, 0)
decreasing_by all_goals (simp only [sizeBranches]; omega)
end

mutual
theorem _root_.Infer.lc (h : Infer K frontier ctx input next subst output ty) :
    CtxWF ctx → ty.IsLC ∧ ∀ pair ∈ subst, pair.2.IsLC := by
  match h with
  | .backend _ h _ _ _ => exact h.lc
  | @Infer.lambda K frontier ann param initial ctx body next subst completed bodyTy hs hb =>
      intro hctx
      have hbodyCtx : CtxWF { ctx with env := PolyTy.mkTrivial param :: ctx.env } := by
        intro scheme hscheme
        rcases List.mem_cons.mp hscheme with rfl | hscheme
        · exact hs.lc
        · exact hctx scheme hscheme
      obtain ⟨ht, hsubst⟩ := hb.lc hbodyCtx
      exact ⟨.arrow (Subst.onTy_lc hsubst hs.lc) ht, hsubst⟩
  | .app hf hx hu =>
      intro hctx
      obtain ⟨hfTy, hs1⟩ := hf.lc hctx
      obtain ⟨hxTy, hs2⟩ := hx.lc (Subst.onCtx_wf hs1 hctx)
      have hs3 := hu.unifies.lc (Subst.onTy_lc hs2 hfTy) (.arrow hxTy .fvar)
      refine ⟨Subst.onTy_lc hs3 .fvar, ?_⟩
      intro pair hp
      rcases List.mem_append.mp hp with hp | hp
      · exact (List.mem_append.mp hp).elim (hs1 pair) (hs2 pair)
      · exact hs3 pair hp
  | .letIn hr hc hb =>
      intro hctx
      obtain ⟨hrTy, hs1⟩ := hr.lc hctx
      have hcheck := hc.lc hrTy
      obtain ⟨hbTy, hs2⟩ := hb.lc (by
        intro scheme hscheme
        rcases List.mem_cons.mp hscheme with rfl | hscheme
        · exact genScheme_wf (Subst.onTy_lc hcheck hrTy)
        · exact Subst.onCtx_wf hcheck (Subst.onCtx_wf hs1 hctx) scheme hscheme)
      refine ⟨hbTy, ?_⟩
      intro pair hp
      rcases List.mem_append.mp hp with hp | hp
      · exact (List.mem_append.mp hp).elim (hs1 pair) (hcheck pair)
      · exact hs2 pair hp

  | .letSignature hprefix _ _ hr hc _ hb =>
    intro hctx
    have hlen : _ := congrArg List.length hprefix
    simp only [freshVars_length] at hlen
    obtain ⟨hrTy, hs1⟩ := hr.lc hctx
    have hcheck := hc.lc hlen hrTy
    obtain ⟨hbTy, hs2⟩ := hb.lc (by
      intro scheme hscheme
      rcases List.mem_cons.mp hscheme with rfl | hscheme
      · exact hc.scheme_wf (Subst.onTy_lc hcheck hrTy)
      · exact Subst.onCtx_wf hcheck (Subst.onCtx_wf hs1 hctx) scheme hscheme)
    exact ⟨hbTy, fun p hp => (List.mem_append.mp hp).elim
      (fun hp => (List.mem_append.mp hp).elim (hs1 p) (hcheck p)) (hs2 p)⟩
  | .match_ hs _ hb =>
    intro hctx
    obtain ⟨ht, hS1⟩ := hs.lc hctx
    obtain ⟨hresult, hS2⟩ := hb.lc (Subst.onCtx_wf hS1 hctx) ht .fvar
    exact ⟨hresult, fun p hp => (List.mem_append.mp hp).elim (hS1 p) (hS2 p)⟩
termination_by (input.size, 0)
decreasing_by all_goals (simp only [Input.size, Input.size_openTyVars]; omega)

theorem _root_.InferBranches.lc {Φ ctx scrutTy ρ brs Φ' S}
    (h : InferBranches κ Φ ctx scrutTy ρ brs Φ' S out)
    (hctx : CtxWF ctx) (hscrutTy : scrutTy.IsLC) (hρ : ρ.IsLC) :
    (S.onTy ρ).IsLC ∧ (∀ p ∈ S, p.2.IsLC) := by
  match h with
  | .nil => exact ⟨by simpa using hρ, by simp⟩
  | .cons hlook hn huni0Rigid hbody huniRigid hrest =>
    have huni0 := huni0Rigid.unifies
    have huni := huniRigid.unifies
    have hS₀ := huni0.lc hscrutTy
      (.customTy (fun t ht => by obtain ⟨x, _, rfl⟩ := List.mem_map.mp ht; exact ContainsBvarsUpTo.fvar))
    obtain ⟨hτb_lc, hS₁⟩ := Infer.lc hbody
      (branchBindings_wf (Subst.onCtx_wf hS₀ hctx)
        (fun t ht => by
          obtain ⟨v, hv, rfl⟩ := List.mem_map.mp ht
          obtain ⟨x, _, rfl⟩ := List.mem_map.mp hv
          exact Subst.onTy_lc hS₀ ContainsBvarsUpTo.fvar)
        (by simp))
    have hS₂ := huni.lc hτb_lc (Subst.onTy_lc hS₁ (Subst.onTy_lc hS₀ hρ))
    obtain ⟨hres, hS₃⟩ := InferBranches.lc hrest
      (Subst.onCtx_wf hS₂ (Subst.onCtx_wf hS₁ (Subst.onCtx_wf hS₀ hctx)))
      (Subst.onTy_lc hS₂ (Subst.onTy_lc hS₁ (Subst.onTy_lc hS₀ hscrutTy)))
      (Subst.onTy_lc hS₂ (Subst.onTy_lc hS₁ (Subst.onTy_lc hS₀ hρ)))
    refine ⟨?_, ?_⟩
    · rw [Subst.onTy_append, Subst.onTy_append, Subst.onTy_append]; exact hres
    · intro p hp; rw [List.mem_append, List.mem_append, List.mem_append] at hp
      rcases hp with ((hp | hp) | hp) | hp
      · exact hS₀ p hp
      · exact hS₁ p hp
      · exact hS₂ p hp
      · exact hS₃ p hp
  | .consWild hbody huniRigid hrest =>
    have huni := huniRigid.unifies
    obtain ⟨hτb_lc, hS₁⟩ := Infer.lc hbody hctx
    have hS₂ := huni.lc hτb_lc (Subst.onTy_lc hS₁ hρ)
    obtain ⟨hres, hS₃⟩ := InferBranches.lc hrest
      (Subst.onCtx_wf hS₂ (Subst.onCtx_wf hS₁ hctx))
      (Subst.onTy_lc hS₂ (Subst.onTy_lc hS₁ hscrutTy))
      (Subst.onTy_lc hS₂ (Subst.onTy_lc hS₁ hρ))
    refine ⟨?_, ?_⟩
    · rw [Subst.onTy_append, Subst.onTy_append]; exact hres
    · intro p hp; rw [List.mem_append, List.mem_append] at hp
      rcases hp with (hp | hp) | hp
      · exact hS₁ p hp
      · exact hS₂ p hp
      · exact hS₃ p hp
termination_by (sizeBranches brs, 0)
decreasing_by
  all_goals (simp only [sizeBranches]; omega)
end


end Elaboration
