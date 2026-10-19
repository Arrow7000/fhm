import FHM.Elaboration.Typing

/-! Canonical inference elaborates partial annotations while returning completed
Core. Whole completed subtrees reuse the verified backend once; partial lambda,
application, let, and match spines share the same recursive inference judgment.
-/

namespace Elaboration

/-- Images of live provisional written-forall slots. They are scoped and
excluded from nested generalization, but are not frozen by unification. -/
def softVars (soft : List Ty) : List Nat := TyList.freeVars soft

def substSoft (subst : Subst) (soft : List Ty) : List Ty := soft.map subst.onTy

@[simp] theorem substSoft_nil (soft : List Ty) : substSoft [] soft = soft := by
  simp [substSoft, Subst.onTy, Ty.substFvars]

@[simp] theorem substSoft_append (first second : Subst) (soft : List Ty) :
    substSoft (first ++ second) soft = substSoft second (substSoft first soft) := by
  simp [substSoft, List.map_map, Function.comp_def, Subst.onTy_append]

theorem mem_softVars_substSoft {subst : Subst} {soft : List Ty} {v : Nat} :
    v ∈ softVars (substSoft subst soft) ↔
      ∃ original ∈ softVars soft, v ∈ (subst.onTy (.fvar original)).freeVars := by
  constructor
  · intro hv
    obtain ⟨ty, hty, hv⟩ := TyList.mem_freeVars_iff.mp hv
    obtain ⟨originalTy, horiginalTy, rfl⟩ := List.mem_map.mp hty
    obtain ⟨original, horiginal, hv⟩ := Ty.mem_freeVars_substFvars_image.mp hv
    exact ⟨original, TyList.mem_freeVars_iff.mpr ⟨originalTy, horiginalTy, horiginal⟩, hv⟩
  · rintro ⟨original, horiginal, hv⟩
    obtain ⟨ty, hty, horiginal⟩ := TyList.mem_freeVars_iff.mp horiginal
    exact TyList.mem_freeVars_iff.mpr ⟨subst.onTy ty, List.mem_map.mpr ⟨ty, hty, rfl⟩,
      Ty.mem_freeVars_substFvars_image.mpr ⟨original, horiginal, hv⟩⟩

theorem scope_image {K : List Nat} {F : List Ty} {subst : Subst} {original v : Nat}
    (hfix : ∀ k ∈ K, subst.onTy (.fvar k) = .fvar k)
    (hscope : original ∈ K ++ softVars F) (hv : v ∈ (subst.onTy (.fvar original)).freeVars) :
    v ∈ K ++ softVars (substSoft subst F) := by
  rcases List.mem_append.mp hscope with hK | hF
  · rw [hfix original hK] at hv
    exact List.mem_append_left _ ((List.mem_singleton.mp hv) ▸ hK)
  · exact List.mem_append_right _ (mem_softVars_substSoft.mpr ⟨original, hF, hv⟩)

def SourceScope (K : List Nat) (F : List Ty) (input : Input) : Prop :=
  ∀ v ∈ input.rigidVars, v ∈ K ++ softVars F

theorem SourceScope.subst (h : SourceScope K F input) (subst : Subst)
    (hfix : ∀ k ∈ K, subst.onTy (.fvar k) = .fvar k) :
    SourceScope K (substSoft subst F) (input.substTyFvars subst) := by
  intro v hv
  obtain ⟨original, ho, hv⟩ := Input.rigidVars_substTyFvars hv
  exact scope_image hfix (h original ho) hv

inductive Seed (K : List Nat) (frontier : Nat) : Option Template → Ty → Nat → Prop
  | absent : Seed K frontier none (.fvar frontier) (frontier + 1)
  | annotated :
      template.allocate frontier = (next, ty) → ty.IsLC →
      (∀ v ∈ template.rigidVars, v ∈ K) →
      Seed K frontier (some template) ty next

inductive LetCheck (K : List Nat) (F : List Ty) (frontier : Nat) (ty : Ty) : LetAnn → Nat → Subst → Prop
  | absent : LetCheck K F frontier ty .absent frontier []
  /-- A whole-signature `_` imposes no constraint on the RHS monotype. This
  eliminates an immediately solved, otherwise unused fresh metavariable. -/
  | hole : LetCheck K F frontier ty (.template .hole) frontier []
  | template :
      template.allocate frontier = (next, expected) → expected.IsLC →
      (∀ v ∈ template.rigidVars, v ∈ K ++ softVars F) →
      RigidUnify K ty expected subst →
      LetCheck K F frontier ty (.template template) next subst

/-- A signed RHS is checked under its written forall prefix. Only those
written skolems and ambient K are protected; anonymous holes stay flexible. -/
inductive SignatureCheck (K : List Nat) (F : List Ty) (written : List Nat) (frontier : Nat) (ty : Ty) :
    LetAnn → Nat → Subst → Prop
  | complete {scheme : PolyTy} : scheme.WF → (∀ v ∈ scheme.body.freeVars, v ∈ K ++ softVars F) →
      RigidUnify (K ++ written) ty (scheme.openVars written) subst →
      SignatureCheck K F written frontier ty (.complete scheme) frontier subst
  | partialSignature {template : Template} :
      (template.openTyVarsFrom 0 written).allocate frontier = (next, expected) →
      expected.IsLC → (∀ v ∈ template.rigidVars, v ∈ K ++ softVars F) →
      RigidUnify (K ++ written) ty expected subst →
      SignatureCheck K F written frontier ty (.partialForall count template) next subst

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
/-- Canonical inference carries frozen K and the current images F of live
provisional forall slots. Sequential calls transform both F and source syntax. -/
inductive _root_.Infer : List Nat → List Ty → Nat → Ctx → Input → Nat → Subst → Expr → Ty → Prop
  | backend :
      input.toCore = some core →
      CoreBackend.Infer K frontier ctx core next subst ty →
      CtxBelow frontier ctx → (∀ k ∈ K, k < frontier) →
      (∀ v ∈ core.tyFreeVars, v ∈ K) →
      (∀ v ∈ core.tyFreeVars, v ∉ softVars F) →
      Infer K F frontier ctx input next subst core ty
  | lambda :
      SourceScope K F (.lambda ann body) →
      Seed (K ++ softVars F) frontier ann param initial →
      Infer K F initial { ctx with env := PolyTy.mkTrivial param :: ctx.env }
        body next subst completed bodyTy →
      Infer K F frontier ctx (.lambda ann body) next subst
        (lambdaOutput ann param subst completed) (.arrow (subst.onTy param) bodyTy)
  | app :
      SourceScope K F (.app f arg) →
      Infer K F frontier ctx f first s1 fOut fTy →
      Infer K (substSoft s1 F) first (s1.onCtx ctx) (arg.substTyFvars s1) second s2 argOut argTy →
      RigidUnify K (s2.onTy fTy) (.arrow argTy (.fvar second)) s3 →
      Infer K F frontier ctx (.app f arg) (second + 1) (s1 ++ s2 ++ s3)
        (.app (fOut.substTyFvars (s2 ++ s3)) (argOut.substTyFvars s3)) (s3.onTy (.fvar second))
  | letIn :
      SourceScope K F (.letIn ann rhs body) →
      Infer K F frontier ctx rhs first s1 rhsOut rhsTy →
      LetCheck K (substSoft s1 F) first rhsTy (ann.substTyFvars s1) checked sCheck →
      Infer K (substSoft (s1 ++ sCheck) F) checked
        { (sCheck.onCtx (s1.onCtx ctx)) with
          env := genScheme (K ++ softVars (substSoft (s1 ++ sCheck) F))
            (sCheck.onCtx (s1.onCtx ctx)).env (sCheck.onTy rhsTy) ::
            (sCheck.onCtx (s1.onCtx ctx)).env }
        (body.substTyFvars (s1 ++ sCheck)) next s2 bodyOut bodyTy →
      Infer K F frontier ctx (.letIn ann rhs body) next (s1 ++ sCheck ++ s2)
        (letOutput (genScheme (K ++ softVars (substSoft (s1 ++ sCheck) F))
            (sCheck.onCtx (s1.onCtx ctx)).env (sCheck.onTy rhsTy))
          (genVars (K ++ softVars (substSoft (s1 ++ sCheck) F))
            (sCheck.onCtx (s1.onCtx ctx)).env (sCheck.onTy rhsTy))
          (rhsOut.substTyFvars sCheck) bodyOut s2) bodyTy
  | letSignature :
      SourceScope K F (.letIn ann rhs body) →
      written = freshVars frontier ann.paramCount →
      (∀ name ∈ written, name ∉ K ++ softVars F) →
      (∀ v ∈ rhs.rigidVars, v ∈ K ++ softVars F) →
      Infer (K ++ written) F (frontier + ann.paramCount) ctx (rhs.openTyVars written)
        first s1 rhsOut rhsTy →
      SignatureCheck K (substSoft s1 F) written first rhsTy (ann.substTyFvars s1) checked sCheck →
      (∀ name ∈ written, name ∉ (sCheck.onCtx (s1.onCtx ctx)).env.freeVars ++
        softVars (substSoft (s1 ++ sCheck) F)) →
      Infer K (substSoft (s1 ++ sCheck) F) checked
        { (sCheck.onCtx (s1.onCtx ctx)) with
          env := signatureScheme (ann.substTyFvars (s1 ++ sCheck))
            (K ++ softVars (substSoft (s1 ++ sCheck) F)) written
            (sCheck.onCtx (s1.onCtx ctx)) (sCheck.onTy rhsTy) ::
            (sCheck.onCtx (s1.onCtx ctx)).env }
        (body.substTyFvars (s1 ++ sCheck)) next s2 bodyOut bodyTy →
      Infer K F frontier ctx (.letIn ann rhs body) next (s1 ++ sCheck ++ s2)
        (letOutput (signatureScheme (ann.substTyFvars (s1 ++ sCheck))
            (K ++ softVars (substSoft (s1 ++ sCheck) F)) written
            (sCheck.onCtx (s1.onCtx ctx)) (sCheck.onTy rhsTy))
          (signatureNames (ann.substTyFvars (s1 ++ sCheck))
            (K ++ softVars (substSoft (s1 ++ sCheck) F)) written
            (sCheck.onCtx (s1.onCtx ctx)) (sCheck.onTy rhsTy))
          (rhsOut.substTyFvars sCheck) bodyOut s2) bodyTy
  | match_ :
      SourceScope K F (.match_ scrut branches) →
      Infer K F frontier ctx scrut first s1 scrutOut scrutTy →
      branches ≠ [] →
      InferBranches K (substSoft s1 F) (first + 1) (s1.onCtx ctx) scrutTy (.fvar first)
        (substInputBranches s1 branches) next s2 branchesOut →
      Infer K F frontier ctx (.match_ scrut branches) next (s1 ++ s2)
        (.match_ (scrutOut.substTyFvars s2) branchesOut) (s2.onTy (.fvar first))

inductive _root_.InferBranches : List Nat → List Ty → Nat → Ctx → Ty → Ty →
    List (MatchPattern × Input) → Nat → Subst → List (MatchPattern × Expr) → Prop
  | nil : InferBranches K F frontier ctx scrutTy resultTy [] frontier [] []
  | consWild :
      (∀ v ∈ rigidBranchVars ((.wildcard, body) :: rest), v ∈ K ++ softVars F) →
      Infer K F frontier ctx body first s1 bodyOut bodyTy →
      RigidUnify K bodyTy (s1.onTy resultTy) s2 →
      InferBranches K (substSoft (s1 ++ s2) F) first (s2.onCtx (s1.onCtx ctx))
        (s2.onTy (s1.onTy scrutTy)) (s2.onTy (s1.onTy resultTy))
        (substInputBranches (s1 ++ s2) rest) next s3 restOut →
      InferBranches K F frontier ctx scrutTy resultTy ((.wildcard, body) :: rest) next (s1 ++ s2 ++ s3)
        ((.wildcard, bodyOut.substTyFvars (s2 ++ s3)) :: restOut)
  | cons :
      (∀ v ∈ rigidBranchVars ((.named name count, body) :: rest), v ∈ K ++ softVars F) →
      LookupList.get? ctx.ctors name = some ctor →
      count = ctor.contents.length →
      RigidUnify K scrutTy (.customTy ctor.tyName ((freshVars frontier ctor.paramCount).map Ty.fvar)) s0 →
      Infer K (substSoft s0 F) (frontier + ctor.paramCount)
        { (s0.onCtx ctx) with
          env := (ctor.contents.map (Ty.openWith (((freshVars frontier ctor.paramCount).map Ty.fvar).map s0.onTy))).map PolyTy.mkTrivial ++
              (s0.onCtx ctx).env }
        (body.substTyFvars s0) first s1 bodyOut bodyTy →
      RigidUnify K bodyTy (s1.onTy (s0.onTy resultTy)) s2 →
      InferBranches K (substSoft (s0 ++ s1 ++ s2) F) first (s2.onCtx (s1.onCtx (s0.onCtx ctx)))
        (s2.onTy (s1.onTy (s0.onTy scrutTy))) (s2.onTy (s1.onTy (s0.onTy resultTy)))
        (substInputBranches (s0 ++ s1 ++ s2) rest) next s3 restOut →
      InferBranches K F frontier ctx scrutTy resultTy ((.named name count, body) :: rest) next
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

theorem LetCheck.not_signature (h : LetCheck K F frontier ty ann next subst) :
    ann.isSignature = false := by cases h <;> rfl

theorem LetCheck.dom_avoids (h : LetCheck K F frontier ty ann next subst) :
    ∀ pair ∈ subst, pair.1 ∉ K := by
  cases h with
  | absent => simp
  | hole => simp
  | template _ _ _ huni => exact huni.dom_avoids

theorem LetCheck.lc (h : LetCheck K F frontier ty ann next subst) (hlc : ty.IsLC) :
    ∀ pair ∈ subst, pair.2.IsLC := by
  cases h with
  | absent => simp
  | hole => simp
  | template _ he _ huni => exact huni.unifies.lc hlc he

theorem LetCheck.fits (h : LetCheck K F frontier ty ann next subst) :
    (ann.substTyFvars subst).FitsMono (subst.onTy ty) := by
  cases h with
  | absent => trivial
  | hole => exact .hole
  | @template next expected subst t heq _ _ huni =>
      have hfit := Template.allocate_fits t frontier
      rw [heq] at hfit
      change (t.substTyFvars subst).Fits (subst.onTy ty)
      rw [huni.unifies.unifies]
      exact hfit.substTyFvars subst

theorem LetCheck.rigid (h : LetCheck K F frontier ty ann next subst) :
    ∀ template, ann = .template template → ∀ v ∈ template.rigidVars, v ∈ K ++ softVars F := by
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

theorem SignatureCheck.dom_avoids (h : SignatureCheck K F written frontier ty ann next subst) :
    ∀ pair ∈ subst, pair.1 ∉ K ++ written := by
  cases h with
  | complete _ _ hu => exact hu.dom_avoids
  | partialSignature _ _ _ hu => exact hu.dom_avoids

theorem SignatureCheck.rigid (h : SignatureCheck K F written frontier ty ann next subst) :
    ∀ v ∈ ann.rigidVars, v ∈ K ++ softVars F := by
  cases h with
  | complete _ hr _ => exact hr
  | partialSignature _ _ hr _ => exact hr

theorem SignatureCheck.lc (h : SignatureCheck K F written frontier ty ann next subst)
    (hprefix : written.length = ann.paramCount) (hlc : ty.IsLC) :
    ∀ pair ∈ subst, pair.2.IsLC := by
  cases h with
  | complete hwf _ hu => exact hu.unifies.lc hlc (PolyTy.openVars_isLC hwf hprefix.ge)
  | partialSignature _ he _ hu => exact hu.unifies.lc hlc he

theorem SignatureCheck.completion (h : SignatureCheck K F written frontier ty ann next subst)
    (hprefix : written.length = ann.paramCount) (hlc : ty.IsLC) :
    (ann.substTyFvars subst).SignatureCompletion written (subst.onTy ty)
      (signatureScheme (ann.substTyFvars subst) Q written ctx (subst.onTy ty))
      (signatureNames (ann.substTyFvars subst) Q written ctx (subst.onTy ty)) := by
  have hS := h.lc hprefix hlc
  have hdom : ∀ pair ∈ subst, pair.1 ∉ written :=
    fun p hp hw => h.dom_avoids p hp (List.mem_append_right _ hw)
  cases h with
  | @complete subst scheme _ _ hu =>
    refine .complete hprefix ?_
    exact hu.unifies.unifies.trans (Subst.onTy_openVars hS hdom)
  | @partialSignature next expected subst count template heq _ _ hu =>
    refine .partialSignature hprefix ?_
    have hfit := Template.allocate_fits (template.openTyVarsFrom 0 written) frontier
    rw [heq] at hfit
    have ht := hfit.substTyFvars subst
    rw [hu.unifies.unifies]
    simpa only [Template.substTyFvars_openTyVarsFrom _ hS hdom 0] using ht

theorem SignatureCheck.scheme_wf (h : SignatureCheck K F written frontier ty ann next subst)
    (hprefix : written.length = ann.paramCount) (hlc : ty.IsLC) :
    (signatureScheme (ann.substTyFvars subst) Q written ctx (subst.onTy ty)).WF := by
  have hS := h.lc hprefix hlc
  cases h with
  | complete hwf _ _ => exact Subst.onPolyTy_wf hS hwf
  | partialSignature _ _ _ _ => exact Ty.closeOver_preserves_bvars (Subst.onTy_lc hS hlc)

theorem SignatureCheck.names_avoid (h : SignatureCheck K F written frontier ty ann next subst)
    (havoid : ∀ name ∈ written, name ∉ Q) :
    ∀ name ∈ signatureNames (ann.substTyFvars subst) Q written ctx (subst.onTy ty), name ∉ Q := by
  cases h with
  | complete _ _ _ => exact havoid
  | partialSignature _ _ _ _ =>
    intro name hn hk
    rcases List.mem_append.mp hn with hn | hn
    · exact havoid name hn hk
    · exact genVars_not_mem_rigid hn (List.mem_append_left _ hk)

theorem SignatureCheck.names_nodup (h : SignatureCheck K F written frontier ty ann next subst)
    (hnd : written.Nodup) :
    (signatureNames (ann.substTyFvars subst) Q written ctx (subst.onTy ty)).Nodup := by
  cases h with
  | complete _ _ _ => exact hnd
  | partialSignature _ _ _ _ =>
    apply List.nodup_append.mpr
    refine ⟨hnd, genVars_nodup, ?_⟩
    intro name hw other hg heq
    subst other
    exact genVars_not_mem_rigid hg (List.mem_append_right _ hw)

theorem SignatureCheck.names_fresh (h : SignatureCheck K F written frontier ty ann next subst)
    (havoid : ∀ name ∈ written, name ∉ ctx.env.freeVars) :
    ∀ name ∈ signatureNames (ann.substTyFvars subst) Q written ctx (subst.onTy ty), name ∉ ctx.env.freeVars := by
  cases h with
  | complete _ _ _ => exact havoid
  | partialSignature _ _ _ _ =>
    intro name hn
    rcases List.mem_append.mp hn with hn | hn
    · exact havoid name hn
    · exact genVars_not_mem hn

theorem SignatureCheck.scheme_eq_close (h : SignatureCheck K F written frontier ty ann next subst)
    (hlen : written.length = ann.paramCount) (hlc : ty.IsLC) (hnd : written.Nodup)
    (hrigid : ∀ v ∈ (ann.substTyFvars subst).rigidVars, v ∈ Q)
    (havoid : ∀ name ∈ written, name ∉ Q) :
    signatureScheme (ann.substTyFvars subst) Q written ctx (subst.onTy ty) =
      ⟨(signatureNames (ann.substTyFvars subst) Q written ctx (subst.onTy ty)).length,
        Ty.closeOver (signatureNames (ann.substTyFvars subst) Q written ctx (subst.onTy ty))
          (subst.onTy ty)⟩ := by
  have hcomp := h.completion (Q := Q) (ctx := ctx) hlen hlc
  have hwf := h.scheme_wf (Q := Q) (ctx := ctx) hlen hlc
  cases h with
  | @complete subst scheme _ _ _ =>
    cases hcomp with
    | complete hl heq =>
      simp only [LetAnn.substTyFvars, signatureScheme, signatureNames] at *
      rw [heq, PolyTy.openVars, Ty.closeOver_openVars_self hnd
        (by simpa only [hl] using hwf)
        (fun name hn hv => havoid name hn (hrigid name hv))]
      cases scheme
      simp only [PolyTy.mk.injEq]
      exact ⟨hl.symm, True.intro⟩
  | partialSignature _ _ _ _ => rfl

theorem _root_.Infer.sourceScope (h : Infer K F frontier ctx input next subst output ty) :
    SourceScope K F input := by
  cases h with
  | backend hemb _ _ _ hscope _ =>
    intro v hv
    exact List.mem_append_left _ (hscope v ((Input.toCore_rigidVars _ hemb v).mp hv))
  | lambda hs _ _ => exact hs
  | app hs _ _ _ => exact hs
  | letIn hs _ _ _ => exact hs
  | letSignature hs _ _ _ _ _ _ _ => exact hs
  | match_ hs _ _ _ => exact hs

private theorem avoids_append {K : List Nat} {S T : Subst}
    (hS : ∀ p ∈ S, p.1 ∉ K) (hT : ∀ p ∈ T, p.1 ∉ K) :
    ∀ p ∈ S ++ T, p.1 ∉ K :=
  fun p hp => (List.mem_append.mp hp).elim (hS p) (hT p)

mutual
theorem _root_.Infer.dom_avoids (h : Infer K F frontier ctx input next subst output ty) :
    ∀ pair ∈ subst, pair.1 ∉ K := by
  match h with
  | .backend _ hi _ _ _ _ => exact hi.dom_avoids
  | .lambda _ _ hb => exact hb.dom_avoids
  | .app _ hf ha hu => exact avoids_append (avoids_append hf.dom_avoids ha.dom_avoids) hu.dom_avoids
  | .letIn _ hr hc hb => exact avoids_append (avoids_append hr.dom_avoids hc.dom_avoids) hb.dom_avoids
  | .letSignature _ _ _ _ hr hc _ hb =>
    exact avoids_append (avoids_append
      (fun p hp hk => hr.dom_avoids p hp (List.mem_append_left _ hk))
      (fun p hp hk => hc.dom_avoids p hp (List.mem_append_left _ hk))) hb.dom_avoids
  | .match_ _ hs _ hb => exact avoids_append hs.dom_avoids hb.dom_avoids
termination_by (input.size, 0)
decreasing_by all_goals (simp only [Input.size, Input.size_openTyVars, Input.size_substTyFvars, sizeBranches_substInputBranches]; omega)

theorem _root_.InferBranches.dom_avoids
    (h : InferBranches K F frontier ctx scrutTy resultTy branches next subst completed) :
    ∀ pair ∈ subst, pair.1 ∉ K := by
  match h with
  | .nil => simp
  | .consWild _ hb hu hr => exact avoids_append (avoids_append hb.dom_avoids hu.dom_avoids) hr.dom_avoids
  | .cons _ _ _ hu0 hb hu hr =>
    exact avoids_append (avoids_append (avoids_append hu0.dom_avoids hb.dom_avoids) hu.dom_avoids) hr.dom_avoids
termination_by (sizeBranches branches, 0)
decreasing_by all_goals (simp only [sizeBranches, Input.size_substTyFvars, sizeBranches_substInputBranches]; omega)
end

mutual
theorem _root_.Infer.lc (h : Infer K F frontier ctx input next subst output ty) :
    CtxWF ctx → ty.IsLC ∧ ∀ pair ∈ subst, pair.2.IsLC := by
  match h with
  | .backend _ h _ _ _ _ => exact h.lc
  | @Infer.lambda K F ann body frontier param initial ctx next subst completed bodyTy _ hs hb =>
      intro hctx
      have hbodyCtx : CtxWF { ctx with env := PolyTy.mkTrivial param :: ctx.env } := by
        intro scheme hscheme
        rcases List.mem_cons.mp hscheme with rfl | hscheme
        · exact hs.lc
        · exact hctx scheme hscheme
      obtain ⟨ht, hsubst⟩ := hb.lc hbodyCtx
      exact ⟨.arrow (Subst.onTy_lc hsubst hs.lc) ht, hsubst⟩
  | .app _ hf hx hu =>
      intro hctx
      obtain ⟨hfTy, hs1⟩ := hf.lc hctx
      obtain ⟨hxTy, hs2⟩ := hx.lc (Subst.onCtx_wf hs1 hctx)
      have hs3 := hu.unifies.lc (Subst.onTy_lc hs2 hfTy) (.arrow hxTy .fvar)
      refine ⟨Subst.onTy_lc hs3 .fvar, ?_⟩
      intro pair hp
      rcases List.mem_append.mp hp with hp | hp
      · exact (List.mem_append.mp hp).elim (hs1 pair) (hs2 pair)
      · exact hs3 pair hp
  | .letIn _ hr hc hb =>
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

  | .letSignature _ hprefix _ _ hr hc _ hb =>
    intro hctx
    have hlen : _ := congrArg List.length hprefix
    simp only [freshVars_length] at hlen
    obtain ⟨hrTy, hs1⟩ := hr.lc hctx
    have hcheck := hc.lc (by simpa using hlen) hrTy
    obtain ⟨hbTy, hs2⟩ := hb.lc (by
      intro scheme hscheme
      rcases List.mem_cons.mp hscheme with rfl | hscheme
      · simpa only [LetAnn.substTyFvars_append] using hc.scheme_wf (Q := K ++ softVars (substSoft (_ ++ _) F)) (by simpa using hlen) hrTy
      · exact Subst.onCtx_wf hcheck (Subst.onCtx_wf hs1 hctx) scheme hscheme)
    exact ⟨hbTy, fun p hp => (List.mem_append.mp hp).elim
      (fun hp => (List.mem_append.mp hp).elim (hs1 p) (hcheck p)) (hs2 p)⟩
  | .match_ _ hs _ hb =>
    intro hctx
    obtain ⟨ht, hS1⟩ := hs.lc hctx
    obtain ⟨hresult, hS2⟩ := hb.lc (Subst.onCtx_wf hS1 hctx) ht .fvar
    exact ⟨hresult, fun p hp => (List.mem_append.mp hp).elim (hS1 p) (hS2 p)⟩
termination_by (input.size, 0)
decreasing_by all_goals (simp only [Input.size, Input.size_openTyVars, Input.size_substTyFvars, sizeBranches_substInputBranches]; omega)

theorem _root_.InferBranches.lc {Φ ctx scrutTy ρ brs Φ' S}
    (h : InferBranches κ F Φ ctx scrutTy ρ brs Φ' S out)
    (hctx : CtxWF ctx) (hscrutTy : scrutTy.IsLC) (hρ : ρ.IsLC) :
    (S.onTy ρ).IsLC ∧ (∀ p ∈ S, p.2.IsLC) := by
  match h with
  | .nil => exact ⟨by simpa using hρ, by simp⟩
  | .cons _ hlook hn huni0Rigid hbody huniRigid hrest =>
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
  | .consWild _ hbody huniRigid hrest =>
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
  all_goals (simp only [sizeBranches, Input.size_substTyFvars, sizeBranches_substInputBranches]; omega)
end


end Elaboration
