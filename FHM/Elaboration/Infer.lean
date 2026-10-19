import FHM.Elaboration.Worker
import FHM.Elaboration.Close

namespace Elaboration

private theorem forall₂_self_map {α β} {R : α → β → Prop} {f : α → β} :
    ∀ {xs : List α}, (∀ x ∈ xs, R x (f x)) → List.Forall₂ R xs (xs.map f)
  | [], _ => .nil
  | _ :: _, h => .cons (h _ (List.mem_cons_self ..))
      (forall₂_self_map (fun x hx => h x (List.mem_cons_of_mem _ hx)))

/-- Whole substitutions transport a completed branch and its constructor witness. -/
theorem _root_.TypeOfMatchBranch.onSubst
    (h : TypeOfMatchBranch ctx (pat, body) scrutTy resultTy)
    (subst : Subst) (hlc : ∀ pair ∈ subst, pair.2.IsLC) :
    TypeOfMatchBranch (subst.onCtx ctx) (pat, body.substTyFvars subst)
      (subst.onTy scrutTy) (subst.onTy resultTy) := by
  cases h with
  | wildcard hb => exact .wildcard (TypeOfHM.onSubst subst hlc hb)
  | mk hspec heq hb =>
    subst heq
    refine .mk (hspec.onSubst subst hlc) ?_ (TypeOfHM.onSubst subst hlc hb)
    simp only [Subst.onCtx, Subst.onEnv, List.map_append, List.map_map,
      Function.comp_def, Subst.onPolyTy, PolyTy.mkTrivial]

theorem _root_.InferBranches.nil_iff
    (h : InferBranches K F frontier ctx scrutTy resultTy branches next subst completed) :
    completed = [] ↔ branches = [] := by cases h <;> simp

mutual
/-- Successful elaboration produces ordinary annotated Core typing. The proof
constructs the typing from the inference derivation; it does not recheck output
with the Core inferer. -/
theorem _root_.Infer.sourceSound (h : Infer K F frontier ctx input next subst output ty) :
    CtxWF ctx → TypeOfHM (subst.onCtx ctx) output ty := by
  match h with
  | .backend _ h hbelow hK hrigid _ =>
      intro hctx
      exact h.sourceSound hctx hbelow hK hrigid
  | @Infer.lambda K F ann body frontier param initial ctx next subst completed bodyTy _ hs hb =>
      intro hctx
      have hbodyCtx : CtxWF { ctx with env := PolyTy.mkTrivial param :: ctx.env } := by
        intro scheme hscheme
        rcases List.mem_cons.mp hscheme with rfl | hscheme
        · exact hs.lc
        · exact hctx scheme hscheme
      have hsubst := (hb.lc hbodyCtx).2
      refine TypeOfHM.lambda (Subst.onTy_lc hsubst hs.lc) ?_ rfl ?_
      · intro expected heq
        cases ann with
        | none => cases heq
        | some template => exact Option.some.inj heq
      · simpa only [lambdaOutput, Subst.onCtx, Subst.onEnv, List.map_cons,
          Subst.onPolyTy, PolyTy.mkTrivial] using hb.sourceSound hbodyCtx
  | @Infer.app K F f arg frontier ctx first s1 fOut fTy second s2 argOut argTy s3 _ hf ha hu =>
      intro hctx
      have hs1 := (hf.lc hctx).2
      have haCtx := Subst.onCtx_wf hs1 hctx
      have hs2 := (ha.lc haCtx).2
      have hs3 := hu.unifies.lc (Subst.onTy_lc hs2 (hf.lc hctx).1)
        (.arrow (ha.lc haCtx).1 .fvar)
      have hfTyped := TypeOfHM.onSubst (s2 ++ s3)
        (fun pair hp => (List.mem_append.mp hp).elim (hs2 pair) (hs3 pair)) (hf.sourceSound hctx)
      have haTyped := TypeOfHM.onSubst s3 hs3 (ha.sourceSound haCtx)
      have heq : (s2 ++ s3).onTy fTy =
          .arrow (s3.onTy argTy) (s3.onTy (.fvar second)) := by
        simpa only [Unifies, Subst.onTy_append, Subst.onTy_arrow] using hu.unifies.unifies
      rw [heq] at hfTyped
      simp only [Subst.onCtx_append] at hfTyped
      simpa only [Subst.onCtx_append] using TypeOfHM.app hfTyped haTyped
  | @Infer.letIn K F ann rhs body frontier ctx first s1 rhsOut rhsTy checked sCheck next s2 bodyOut bodyTy
      _ hr hc hb =>
      intro hctx
      have hs1 := (hr.lc hctx).2
      have hrTy := (hr.lc hctx).1
      have hsCheck := hc.lc hrTy
      have checkedCtxWF := Subst.onCtx_wf hsCheck (Subst.onCtx_wf hs1 hctx)
      have checkedTyLC := Subst.onTy_lc hsCheck hrTy
      have bodyCtxWF : CtxWF
          { sCheck.onCtx (s1.onCtx ctx) with
            env := genScheme (K ++ softVars (substSoft (s1 ++ sCheck) F)) (sCheck.onCtx (s1.onCtx ctx)).env (sCheck.onTy rhsTy) ::
              (sCheck.onCtx (s1.onCtx ctx)).env } := by
        intro scheme hscheme
        rcases List.mem_cons.mp hscheme with rfl | hscheme
        · exact genScheme_wf checkedTyLC
        · exact checkedCtxWF scheme hscheme
      have hs2 := (hb.lc bodyCtxWF).2
      have rhsTyped := TypeOfHM.onSubst sCheck hsCheck (hr.sourceSound hctx)
      have rhsGeneral := TypeOfHM.generaliseAnnotated
        (names := genVars (K ++ softVars (substSoft (s1 ++ sCheck) F)) (sCheck.onCtx (s1.onCtx ctx)).env (sCheck.onTy rhsTy))
        rhsTyped genVars_nodup
        (fun name hn => genVars_not_mem hn)
      obtain ⟨avoid, rhsFinal⟩ := GeneralisesTo.onSubst_annotated
        (genScheme_wf checkedTyLC) rhsGeneral s2 hs2
      have bodyTyped := hb.sourceSound bodyCtxWF
      have hctxeq :
          s2.onCtx
            { sCheck.onCtx (s1.onCtx ctx) with
              env := genScheme (K ++ softVars (substSoft (s1 ++ sCheck) F)) (sCheck.onCtx (s1.onCtx ctx)).env (sCheck.onTy rhsTy) ::
                (sCheck.onCtx (s1.onCtx ctx)).env } =
          { (s1 ++ sCheck ++ s2).onCtx ctx with
            env := s2.onPolyTy (genScheme (K ++ softVars (substSoft (s1 ++ sCheck) F)) (sCheck.onCtx (s1.onCtx ctx)).env (sCheck.onTy rhsTy)) ::
              ((s1 ++ sCheck ++ s2).onCtx ctx).env } := by
        rw [Subst.onCtx_append, Subst.onCtx_append]
        rfl
      rw [hctxeq] at bodyTyped
      refine TypeOfHM.letIn (L := avoid) (Subst.onPolyTy_wf hs2 (genScheme_wf checkedTyLC))
        (fun _ heq => Option.some.inj heq) ?_ rfl bodyTyped
      simpa only [letOutput, genScheme, ← Subst.onCtx_append] using rhsFinal

  | @Infer.letSignature K F ann rhs body written frontier ctx first s1 rhsOut rhsTy checked sCheck next s2 bodyOut bodyTy
      hraw hprefix havoid _ hr hc hescape hb =>
    intro hctx
    have hlen : written.length = ann.paramCount := by simpa only [freshVars_length] using congrArg List.length hprefix
    have hnd : written.Nodup := hprefix ▸ freshVars_nodup
    obtain ⟨hrTy, hs1⟩ := hr.lc hctx
    have hsCheck := hc.lc (by simpa using hlen) hrTy
    have checkedCtxWF := Subst.onCtx_wf hsCheck (Subst.onCtx_wf hs1 hctx)
    have checkedTyLC := Subst.onTy_lc hsCheck hrTy
    have hscheme : (signatureScheme (ann.substTyFvars (s1 ++ sCheck))
        (K ++ softVars (substSoft (s1 ++ sCheck) F)) written
        (sCheck.onCtx (s1.onCtx ctx)) (sCheck.onTy rhsTy)).WF := by
      simpa only [LetAnn.substTyFvars_append] using
        hc.scheme_wf (Q := K ++ softVars (substSoft (s1 ++ sCheck) F))
          (ctx := sCheck.onCtx (s1.onCtx ctx)) (by simpa using hlen) hrTy
    have hscopePost : ∀ v ∈ (ann.substTyFvars (s1 ++ sCheck)).rigidVars,
        v ∈ K ++ softVars (substSoft (s1 ++ sCheck) F) := by
      intro v hv
      obtain ⟨original, ho, hv⟩ := LetAnn.rigidVars_substTyFvars hv
      exact scope_image (Subst.fixes_of_dom_avoids (fun p hp hk =>
        (List.mem_append.mp hp).elim
          (fun hp => hr.dom_avoids p hp (List.mem_append_left _ hk))
          (fun hp => hc.dom_avoids p hp (List.mem_append_left _ hk))))
        (hraw original (List.mem_append_left _ (List.mem_append_left _ ho))) hv
    have havoidPost : ∀ name ∈ written, name ∉ K ++ softVars (substSoft (s1 ++ sCheck) F) := by
      intro name hn hm
      rcases List.mem_append.mp hm with hK | hF
      · exact havoid name hn (List.mem_append_left _ hK)
      · exact hescape name hn (List.mem_append_right _ hF)
    have hnamesFresh : ∀ name ∈ written, name ∉ (sCheck.onCtx (s1.onCtx ctx)).env.freeVars :=
      fun name hn hm => hescape name hn (List.mem_append_left _ hm)
    have bodyCtxWF : CtxWF
        { sCheck.onCtx (s1.onCtx ctx) with
          env := signatureScheme (ann.substTyFvars (s1 ++ sCheck)) (K ++ softVars (substSoft (s1 ++ sCheck) F)) written (sCheck.onCtx (s1.onCtx ctx)) (sCheck.onTy rhsTy) ::
            (sCheck.onCtx (s1.onCtx ctx)).env } := by
      intro scheme hschemeMem
      rcases List.mem_cons.mp hschemeMem with rfl | hschemeMem
      · exact hscheme
      · exact checkedCtxWF scheme hschemeMem
    have hs2 := (hb.lc bodyCtxWF).2
    have rhsTyped := TypeOfHM.onSubst sCheck hsCheck (hr.sourceSound hctx)
    have rhsGeneral := TypeOfHM.generaliseAnnotated
      (names := signatureNames (ann.substTyFvars (s1 ++ sCheck)) (K ++ softVars (substSoft (s1 ++ sCheck) F)) written (sCheck.onCtx (s1.onCtx ctx)) (sCheck.onTy rhsTy))
      rhsTyped (by simpa only [LetAnn.substTyFvars_append] using hc.names_nodup (Q := K ++ softVars (substSoft (s1 ++ sCheck) F)) hnd)
        (by simpa only [LetAnn.substTyFvars_append] using hc.names_fresh (Q := K ++ softVars (substSoft (s1 ++ sCheck) F)) hnamesFresh)
    have hclose := hc.scheme_eq_close (Q := K ++ softVars (substSoft (s1 ++ sCheck) F))
      (ctx := sCheck.onCtx (s1.onCtx ctx)) (by simpa using hlen) hrTy hnd
      (by simpa only [LetAnn.substTyFvars_append] using hscopePost) havoidPost
    simp only [← LetAnn.substTyFvars_append] at hclose
    rw [← hclose] at rhsGeneral
    obtain ⟨avoid, rhsFinal⟩ := GeneralisesTo.onSubst_annotated hscheme rhsGeneral s2 hs2
    have bodyTyped := hb.sourceSound bodyCtxWF
    have hctxeq :
        s2.onCtx { sCheck.onCtx (s1.onCtx ctx) with
          env := signatureScheme (ann.substTyFvars (s1 ++ sCheck)) (K ++ softVars (substSoft (s1 ++ sCheck) F)) written (sCheck.onCtx (s1.onCtx ctx)) (sCheck.onTy rhsTy) ::
            (sCheck.onCtx (s1.onCtx ctx)).env } =
        { (s1 ++ sCheck ++ s2).onCtx ctx with
          env := s2.onPolyTy (signatureScheme (ann.substTyFvars (s1 ++ sCheck)) (K ++ softVars (substSoft (s1 ++ sCheck) F)) written (sCheck.onCtx (s1.onCtx ctx)) (sCheck.onTy rhsTy)) ::
            ((s1 ++ sCheck ++ s2).onCtx ctx).env } := by
      rw [Subst.onCtx_append, Subst.onCtx_append]
      rfl
    rw [hctxeq] at bodyTyped
    refine TypeOfHM.letIn (L := avoid) (Subst.onPolyTy_wf hs2 hscheme)
      (fun _ heq => Option.some.inj heq) ?_ rfl bodyTyped
    simpa only [letOutput, ← Subst.onCtx_append] using rhsFinal
  | .match_ _ hs hne hb =>
    intro hctx
    have hs1 := (hs.lc hctx).2
    have hbr := hb.lc (Subst.onCtx_wf hs1 hctx) (hs.lc hctx).1 .fvar
    have hscrut := TypeOfHM.onSubst _ hbr.2 (hs.sourceSound hctx)
    have hbranches := hb.sourceSound (Subst.onCtx_wf hs1 hctx) (hs.lc hctx).1 .fvar
    simpa only [Subst.onCtx_append] using
      TypeOfHM.match_ hscrut (fun hnil => hne (substInputBranches_eq_nil _ _ |>.mp (hb.nil_iff.mp hnil))) hbranches
termination_by (input.size, 0)
decreasing_by all_goals (simp only [Input.size, Input.size_openTyVars, Input.size_substTyFvars, sizeBranches_substInputBranches]; omega)

theorem _root_.InferBranches.sourceSound
    (h : InferBranches K F frontier ctx scrutTy resultTy branches next subst completed)
    (hctx : CtxWF ctx) (hscrut : scrutTy.IsLC) (hresult : resultTy.IsLC) :
    ∀ branch ∈ completed, TypeOfMatchBranch (subst.onCtx ctx) branch
      (subst.onTy scrutTy) (subst.onTy resultTy) := by
  match h with
  | .nil => intro branch hb; cases hb
  | @InferBranches.consWild body rest K F frontier ctx first s1 bodyOut bodyTy resultTy s2 scrutTy next s3 restOut
      _ hb hu hr =>
    obtain ⟨hbTy, hs1⟩ := hb.lc hctx
    have hs2 := hu.unifies.lc hbTy (Subst.onTy_lc hs1 hresult)
    have hctxRest := Subst.onCtx_wf hs2 (Subst.onCtx_wf hs1 hctx)
    have hscrutRest := Subst.onTy_lc hs2 (Subst.onTy_lc hs1 hscrut)
    have hresultRest := Subst.onTy_lc hs2 (Subst.onTy_lc hs1 hresult)
    have hs3 := (hr.lc hctxRest hscrutRest hresultRest).2
    have htail := hr.sourceSound hctxRest hscrutRest hresultRest
    intro branch hbranch
    rcases List.mem_cons.mp hbranch with rfl | hbranch
    · have head := TypeOfHM.onSubst (s2 ++ s3)
        (fun p hp => (List.mem_append.mp hp).elim (hs2 p) (hs3 p)) (hb.sourceSound hctx)
      have heq := congrArg s3.onTy hu.unifies.unifies
      rw [Subst.onTy_append] at head
      rw [heq] at head
      simpa only [Subst.onCtx_append, Subst.onTy_append, List.append_assoc] using
        (TypeOfMatchBranch.wildcard (scrutTy := (s1 ++ s2 ++ s3).onTy scrutTy) head)
    · simpa only [Subst.onCtx_append, Subst.onTy_append] using htail branch hbranch
  | @InferBranches.cons name count body rest K F ctor scrutTy frontier s0 ctx first s1 bodyOut bodyTy resultTy s2 next s3 restOut
      _ hlookup hcount hu0 hb hu hr =>
    have hs0 := hu0.unifies.lc hscrut
      (.customTy (fun t ht => by obtain ⟨v, _, rfl⟩ := List.mem_map.mp ht; exact .fvar))
    have hbodyWF := branchBindings_wf (ctorr := ctor)
      (ta := ((freshVars frontier ctor.paramCount).map Ty.fvar).map s0.onTy)
      (Subst.onCtx_wf hs0 hctx)
      (fun t ht => by
        obtain ⟨v, hv, rfl⟩ := List.mem_map.mp ht
        obtain ⟨x, _, rfl⟩ := List.mem_map.mp hv
        exact Subst.onTy_lc hs0 .fvar) (by simp)
    obtain ⟨hbTy, hs1⟩ := hb.lc hbodyWF
    have hs2 := hu.unifies.lc hbTy (Subst.onTy_lc hs1 (Subst.onTy_lc hs0 hresult))
    have hctxRest := Subst.onCtx_wf hs2 (Subst.onCtx_wf hs1 (Subst.onCtx_wf hs0 hctx))
    have hscrutRest := Subst.onTy_lc hs2 (Subst.onTy_lc hs1 (Subst.onTy_lc hs0 hscrut))
    have hresultRest := Subst.onTy_lc hs2 (Subst.onTy_lc hs1 (Subst.onTy_lc hs0 hresult))
    have hs3 := (hr.lc hctxRest hscrutRest hresultRest).2
    have htail := hr.sourceSound hctxRest hscrutRest hresultRest
    intro branch hbranch
    rcases List.mem_cons.mp hbranch with rfl | hbranch
    · let args := (((freshVars frontier ctor.paramCount).map Ty.fvar).map s0.onTy).map s1.onTy
      have hspec : BranchCtorSpec (s1.onCtx (s0.onCtx ctx)).ctors name count
          (s1.onTy (s0.onTy scrutTy)) ctor args (ctor.contents.map (Ty.openWith args)) := by
        refine ⟨hlookup, ?_, ?_, hcount, ?_⟩
        · simpa only [Subst.onTy_customTy, args] using congrArg s1.onTy hu0.unifies.unifies
        · simp only [args, List.length_map, freshVars_length]
        · exact forall₂_self_map (fun t ht => InstantiatesBy.openWith (ctor.bound t ht)
            (by simp only [args, List.length_map, freshVars_length]; omega))
      have head0 := TypeOfMatchBranch.mk hspec (Subst.onCtx_branchBindings hs1) (hb.sourceSound hbodyWF)
      have head := head0.onSubst (s2 ++ s3)
        (fun p hp => (List.mem_append.mp hp).elim (hs2 p) (hs3 p))
      have heq := congrArg s3.onTy hu.unifies.unifies
      simp only [Subst.onTy_append] at head
      rw [heq] at head
      simpa only [Subst.onCtx_append, Subst.onTy_append] using head
    · simpa only [Subst.onCtx_append, Subst.onTy_append] using htail branch hbranch
termination_by (sizeBranches branches, 0)
decreasing_by all_goals (simp only [sizeBranches, Input.size_substTyFvars, sizeBranches_substInputBranches]; omega)
end

mutual
/-- Elaboration changes annotations and binders while preserving runtime syntax. -/
theorem _root_.Infer.erase (h : Infer K F frontier ctx input next subst output ty) :
    output.erase = input.erase := by
  match h with
  | .backend hemb _ _ _ _ _ => exact Input.toCore_erase _ hemb
  | .lambda _ _ hb =>
      simpa only [lambdaOutput, Expr.erase, Input.erase] using
        congrArg (Expr.lambda none) hb.erase
  | .app _ hf ha _ =>
      simp only [Expr.erase, Expr.erase_substTyFvars, Input.erase, hf.erase, ha.erase, Input.erase_substTyFvars]
  | .letIn _ hr _ hb =>
      simp only [letOutput, Expr.erase, Expr.erase_substTyFvars,
        Expr.erase_closeTyVars, Input.erase, hr.erase, hb.erase, Input.erase_substTyFvars]
  | .letSignature _ _ _ _ hr _ _ hb =>
      simp only [letOutput, Expr.erase, Expr.erase_substTyFvars,
        Expr.erase_closeTyVars, Input.erase, hr.erase, hb.erase, Input.erase_openTyVars, Input.erase_substTyFvars]
  | .match_ _ hs _ hb =>
      simp only [Expr.erase, Expr.erase_substTyFvars, Input.erase, hs.erase, hb.erase, eraseBranches_substInputBranches]
termination_by (input.size, 0)
decreasing_by all_goals (simp only [Input.size, Input.size_openTyVars, Input.size_substTyFvars, sizeBranches_substInputBranches]; omega)

theorem _root_.InferBranches.erase
    (h : InferBranches K F frontier ctx scrutTy resultTy branches next subst completed) :
    completed.map (fun pe => (pe.1, pe.2.erase)) = eraseBranches branches := by
  match h with
  | .nil => rfl
  | .consWild _ hb _ hr =>
      simp only [List.map_cons, eraseBranches, Expr.erase_substTyFvars, hb.erase, hr.erase, eraseBranches_substInputBranches]
  | .cons _ _ _ _ hb _ hr =>
      simp only [List.map_cons, eraseBranches, Expr.erase_substTyFvars, hb.erase, hr.erase, Input.erase_substTyFvars, eraseBranches_substInputBranches]
termination_by (sizeBranches branches, 0)
decreasing_by all_goals (simp only [sizeBranches, Input.size_substTyFvars, sizeBranches_substInputBranches]; omega)
end

theorem _root_.Infer.sound (h : Infer K F frontier ctx input next subst output ty) (hctx : CtxWF ctx) :
    RuntimeTyping.RunWT (subst.onCtx ctx) input.erase ty := by
  rw [← h.erase]
  exact (h.sourceSound hctx).erase_preserves_typing

theorem Typing.onSubst_soft {K : List Nat} {F : List Ty}
    (h : Typing (K ++ softVars F) ctx input ty) (subst : Subst)
    (hlc : ∀ p ∈ subst, p.2.IsLC) (havoid : ∀ p ∈ subst, p.1 ∉ K) :
    Typing (K ++ softVars (substSoft subst F)) (subst.onCtx ctx)
      (input.substTyFvars subst) (subst.onTy ty) :=
  h.onSubst_source subst hlc (fun _ hk _ hv => scope_image (Subst.fixes_of_dom_avoids havoid) hk hv)

theorem BranchTyping.onSubst_soft {K : List Nat} {F : List Ty}
    (h : BranchTyping Typing (K ++ softVars F) ctx branch scrutTy resultTy) (subst : Subst)
    (hlc : ∀ p ∈ subst, p.2.IsLC) (havoid : ∀ p ∈ subst, p.1 ∉ K) :
    BranchTyping Typing (K ++ softVars (substSoft subst F)) (subst.onCtx ctx)
      (branch.1, branch.2.substTyFvars subst) (subst.onTy scrutTy) (subst.onTy resultTy) :=
  h.onSubst_source subst hlc (fun _ hk _ hv => scope_image (Subst.fixes_of_dom_avoids havoid) hk hv)

mutual
/-- Successful inference also satisfies the independent partial-input rules.
This connects input admissibility and completed-output typing at the same type. -/
theorem _root_.Infer.inputSound_source (h : Infer K F frontier ctx input next subst output ty) :
    CtxWF ctx → Typing (K ++ softVars (substSoft subst F)) (subst.onCtx ctx) (input.substTyFvars subst) ty := by
  match h with
  | .backend hemb h hbelow hK hrigid _ =>
      intro hctx
      have hinput := input.substTyFvars_eq_self_of_fixes (fun v hv =>
        Subst.fixes_of_dom_avoids h.dom_avoids v (hrigid v ((Input.toCore_rigidVars _ hemb v).mp hv)))
      rw [hinput]
      exact .complete hemb (fun v hv => List.mem_append_left _ (hrigid v hv))
        (h.sourceSound hctx hbelow hK hrigid)
  | @Infer.lambda K F ann body frontier param initial ctx next subst completed bodyTy _ hs hb =>
      intro hctx
      have hbodyCtx : CtxWF { ctx with env := PolyTy.mkTrivial param :: ctx.env } := by
        intro scheme hscheme
        rcases List.mem_cons.mp hscheme with rfl | hscheme
        · exact hs.lc
        · exact hctx scheme hscheme
      have hsubst := (hb.lc hbodyCtx).2
      simp only [Input.substTyFvars]
      refine Typing.lambda (Subst.onTy_lc hsubst hs.lc) ?_ ?_ ?_
      · intro template heq
        cases ann with
        | none => cases heq
        | some original =>
          cases heq
          exact (hs.fits original rfl).substTyFvars subst
      · intro template heq v hv
        cases ann with
        | none => cases heq
        | some original =>
          cases heq
          obtain ⟨old, hold, hv⟩ := Template.rigidVars_substTyFvars hv
          exact scope_image (Subst.fixes_of_dom_avoids hb.dom_avoids) (hs.rigid original rfl old hold) hv
      · simpa only [Subst.onCtx, Subst.onEnv, List.map_cons, Subst.onPolyTy,
          PolyTy.mkTrivial] using hb.inputSound_source hbodyCtx
  | @Infer.app K F f arg frontier ctx first s1 fOut fTy second s2 argOut argTy s3 _ hf ha hu =>
      intro hctx
      have hs1 := (hf.lc hctx).2
      have haCtx := Subst.onCtx_wf hs1 hctx
      have hs2 := (ha.lc haCtx).2
      have hs3 := hu.unifies.lc (Subst.onTy_lc hs2 (hf.lc hctx).1)
        (.arrow (ha.lc haCtx).1 .fvar)
      have hfTyped := (hf.inputSound_source hctx).onSubst_soft (s2 ++ s3)
        (fun pair hp => (List.mem_append.mp hp).elim (hs2 pair) (hs3 pair))
        (fun pair hp => (List.mem_append.mp hp).elim (ha.dom_avoids pair) (hu.dom_avoids pair))
      have haTyped := (ha.inputSound_source haCtx).onSubst_soft s3 hs3 hu.dom_avoids
      have heq : (s2 ++ s3).onTy fTy =
          .arrow (s3.onTy argTy) (s3.onTy (.fvar second)) := by
        simpa only [Unifies, Subst.onTy_append, Subst.onTy_arrow] using hu.unifies.unifies
      rw [heq] at hfTyped
      simp only [Subst.onCtx_append] at hfTyped
      simp only [← substSoft_append, ← Input.substTyFvars_append, List.append_assoc] at hfTyped haTyped
      simpa only [Subst.onCtx_append, Input.substTyFvars, List.append_assoc] using Typing.app hfTyped haTyped
  | @Infer.letIn K F ann rhs body frontier ctx first s1 rhsOut rhsTy checked sCheck next s2 bodyOut bodyTy
      hraw hr hc hb =>
      intro hctx
      have hs1 := (hr.lc hctx).2
      have hrTy := (hr.lc hctx).1
      have hsCheck := hc.lc hrTy
      have hprefixAvoid : ∀ p ∈ s1 ++ sCheck, p.1 ∉ K := fun p hp =>
        (List.mem_append.mp hp).elim (hr.dom_avoids p) (hc.dom_avoids p)
      have hpost := hraw.subst (s1 ++ sCheck) (Subst.fixes_of_dom_avoids hprefixAvoid)
      have hann : ∀ template, (ann.substTyFvars (s1 ++ sCheck)) = .template template →
          ∀ v ∈ template.rigidVars, v ∈ K ++ softVars (substSoft (s1 ++ sCheck) F) := by
        intro template heq v hv
        exact hpost v (List.mem_append_left _ (List.mem_append_left _ (by
          simpa only [LetAnn.rigidVars, heq] using hv)))
      have hfit : (ann.substTyFvars (s1 ++ sCheck)).FitsMono (sCheck.onTy rhsTy) := by
        simpa only [LetAnn.substTyFvars_append] using hc.fits
      have checkedCtxWF := Subst.onCtx_wf hsCheck (Subst.onCtx_wf hs1 hctx)
      have checkedTyLC := Subst.onTy_lc hsCheck hrTy
      have bodyCtxWF : CtxWF
          { sCheck.onCtx (s1.onCtx ctx) with
            env := genScheme (K ++ softVars (substSoft (s1 ++ sCheck) F))
              (sCheck.onCtx (s1.onCtx ctx)).env (sCheck.onTy rhsTy) ::
              (sCheck.onCtx (s1.onCtx ctx)).env } := by
        intro scheme hscheme
        rcases List.mem_cons.mp hscheme with rfl | hscheme
        · exact genScheme_wf checkedTyLC
        · exact checkedCtxWF scheme hscheme
      have hs2 := (hb.lc bodyCtxWF).2
      have rhsTyped := (hr.inputSound_source hctx).onSubst_soft sCheck hsCheck hc.dom_avoids
      simp only [← substSoft_append, ← Input.substTyFvars_append] at rhsTyped
      have rhsGeneral := rhsTyped.generalise
        (names := genVars (K ++ softVars (substSoft (s1 ++ sCheck) F))
          (sCheck.onCtx (s1.onCtx ctx)).env (sCheck.onTy rhsTy))
        hfit hann genVars_nodup (fun _ hn => genVars_not_mem hn)
        (fun _ hn => genVars_not_mem_rigid hn)
      obtain ⟨avoid, hfits, hgeneral⟩ := Typing.binding_onSubst_source
        (scheme := genScheme (K ++ softVars (substSoft (s1 ++ sCheck) F))
          (sCheck.onCtx (s1.onCtx ctx)).env (sCheck.onTy rhsTy))
        (fun fresh hf => (rhsGeneral fresh hf).1)
        (fun fresh hf => (rhsGeneral fresh hf).2) s2 hs2
        (fun _ hk _ hv => scope_image (Subst.fixes_of_dom_avoids hb.dom_avoids) hk hv)
      have hannFinal : ∀ template, (ann.substTyFvars (s1 ++ sCheck ++ s2)) = .template template →
          ∀ v ∈ template.rigidVars, v ∈ K ++ softVars (substSoft (s1 ++ sCheck ++ s2) F) := by
        have hp := hraw.subst (s1 ++ sCheck ++ s2) (Subst.fixes_of_dom_avoids
          (fun p hp => (List.mem_append.mp hp).elim (hprefixAvoid p) (hb.dom_avoids p)))
        intro template heq v hv
        exact hp v (List.mem_append_left _ (List.mem_append_left _ (by
          simpa only [LetAnn.rigidVars, heq] using hv)))
      have bodyTyped := hb.inputSound_source bodyCtxWF
      have hctxeq :
          s2.onCtx
            { sCheck.onCtx (s1.onCtx ctx) with
              env := genScheme (K ++ softVars (substSoft (s1 ++ sCheck) F))
                (sCheck.onCtx (s1.onCtx ctx)).env (sCheck.onTy rhsTy) ::
                (sCheck.onCtx (s1.onCtx ctx)).env } =
          { (s1 ++ sCheck ++ s2).onCtx ctx with
            env := s2.onPolyTy (genScheme (K ++ softVars (substSoft (s1 ++ sCheck) F))
              (sCheck.onCtx (s1.onCtx ctx)).env (sCheck.onTy rhsTy)) ::
              ((s1 ++ sCheck ++ s2).onCtx ctx).env } := by
        rw [Subst.onCtx_append, Subst.onCtx_append]
        rfl
      rw [hctxeq] at bodyTyped
      simp only [← substSoft_append, ← Input.substTyFvars_append, ← LetAnn.substTyFvars_append,
        List.append_assoc] at hfits hgeneral bodyTyped hannFinal ⊢
      refine Typing.letIn (L := avoid) (Subst.onPolyTy_wf hs2 (genScheme_wf checkedTyLC))
        hannFinal hfits ?_ bodyTyped
      intro fresh hfresh
      simpa only [← Subst.onCtx_append, List.append_assoc] using hgeneral fresh hfresh

  | @Infer.letSignature K F ann rhs body written frontier ctx first s1 rhsOut rhsTy checked sCheck next s2 bodyOut bodyTy
      hscope hprefix havoid hraw hr hc hescape hb =>
    intro hctx
    have hlen : written.length = ann.paramCount := by simpa only [freshVars_length] using congrArg List.length hprefix
    have hnd : written.Nodup := hprefix ▸ freshVars_nodup
    obtain ⟨hrTy, hs1⟩ := hr.lc hctx
    have hsCheck := hc.lc (by simpa using hlen) hrTy
    have checkedCtxWF := Subst.onCtx_wf hsCheck (Subst.onCtx_wf hs1 hctx)
    have checkedTyLC := Subst.onTy_lc hsCheck hrTy
    have hscheme : (signatureScheme (ann.substTyFvars (s1 ++ sCheck))
        (K ++ softVars (substSoft (s1 ++ sCheck) F)) written
        (sCheck.onCtx (s1.onCtx ctx)) (sCheck.onTy rhsTy)).WF := by
      simpa only [LetAnn.substTyFvars_append] using
        hc.scheme_wf (Q := K ++ softVars (substSoft (s1 ++ sCheck) F))
          (ctx := sCheck.onCtx (s1.onCtx ctx)) (by simpa using hlen) hrTy
    have hscopePost : ∀ v ∈ (ann.substTyFvars (s1 ++ sCheck)).rigidVars,
        v ∈ K ++ softVars (substSoft (s1 ++ sCheck) F) := by
      intro v hv
      obtain ⟨original, ho, hv⟩ := LetAnn.rigidVars_substTyFvars hv
      exact scope_image (Subst.fixes_of_dom_avoids (fun p hp hk =>
        (List.mem_append.mp hp).elim
          (fun hp => hr.dom_avoids p hp (List.mem_append_left _ hk))
          (fun hp => hc.dom_avoids p hp (List.mem_append_left _ hk))))
        (hscope original (List.mem_append_left _ (List.mem_append_left _ ho))) hv
    have havoidPost : ∀ name ∈ written, name ∉ K ++ softVars (substSoft (s1 ++ sCheck) F) := by
      intro name hn hm
      rcases List.mem_append.mp hm with hK | hF
      · exact havoid name hn (List.mem_append_left _ hK)
      · exact hescape name hn (List.mem_append_right _ hF)
    have hnamesFresh : ∀ name ∈ written, name ∉ (sCheck.onCtx (s1.onCtx ctx)).env.freeVars :=
      fun name hn hm => hescape name hn (List.mem_append_left _ hm)
    have bodyCtxWF : CtxWF
        { sCheck.onCtx (s1.onCtx ctx) with
          env := signatureScheme (ann.substTyFvars (s1 ++ sCheck)) (K ++ softVars (substSoft (s1 ++ sCheck) F)) written (sCheck.onCtx (s1.onCtx ctx)) (sCheck.onTy rhsTy) ::
            (sCheck.onCtx (s1.onCtx ctx)).env } := by
      intro scheme hschemeMem
      rcases List.mem_cons.mp hschemeMem with rfl | hschemeMem
      · exact hscheme
      · exact checkedCtxWF scheme hschemeMem
    have hs2 := (hb.lc bodyCtxWF).2
    have hprefixLC : ∀ p ∈ s1 ++ sCheck, p.2.IsLC := fun p hp =>
      (List.mem_append.mp hp).elim (hs1 p) (hsCheck p)
    have hprefixAvoid : ∀ p ∈ s1 ++ sCheck, p.1 ∉ K ++ written := fun p hp =>
      (List.mem_append.mp hp).elim (hr.dom_avoids p) (hc.dom_avoids p)
    have rhsTyped0 := (hr.inputSound_source hctx).onSubst_soft sCheck hsCheck hc.dom_avoids
    simp only [← substSoft_append, ← Input.substTyFvars_append] at rhsTyped0
    rw [Input.substTyFvars_openTyVars rhs hprefixLC
      (fun p hp hw => hprefixAvoid p hp (List.mem_append_right _ hw))] at rhsTyped0
    have rhsTyped : Typing ((K ++ softVars (substSoft (s1 ++ sCheck) F)) ++ written)
        (sCheck.onCtx (s1.onCtx ctx)) ((rhs.substTyFvars (s1 ++ sCheck)).openTyVars written)
        (sCheck.onTy rhsTy) := rhsTyped0.scope_mono (by
      intro k hk
      simp only [List.mem_append] at hk ⊢
      tauto)
    have hpost := hscope.subst (s1 ++ sCheck) (Subst.fixes_of_dom_avoids
      (fun p hp hk => hprefixAvoid p hp (List.mem_append_left _ hk)))
    have hrawPost : ∀ v ∈ (rhs.substTyFvars (s1 ++ sCheck)).rigidVars,
        v ∈ K ++ softVars (substSoft (s1 ++ sCheck) F) := fun v hv =>
      hpost v (List.mem_append_left _ (List.mem_append_right _ hv))
    have hcomp := hc.completion (Q := K ++ softVars (substSoft (s1 ++ sCheck) F))
      (ctx := sCheck.onCtx (s1.onCtx ctx)) (by simpa using hlen) hrTy
    simp only [← LetAnn.substTyFvars_append] at hcomp
    have hnamesND := hc.names_nodup (Q := K ++ softVars (substSoft (s1 ++ sCheck) F))
      (ctx := sCheck.onCtx (s1.onCtx ctx)) hnd
    have hnamesAvoid := hc.names_avoid (ctx := sCheck.onCtx (s1.onCtx ctx)) havoidPost
    have hnamesFresh := hc.names_fresh (Q := K ++ softVars (substSoft (s1 ++ sCheck) F)) hnamesFresh
    simp only [← LetAnn.substTyFvars_append] at hnamesND hnamesAvoid hnamesFresh
    obtain ⟨fitAvoid, hfits⟩ := hcomp.cofinite_fits hnamesND hnamesAvoid hscopePost checkedTyLC
    obtain ⟨typeAvoid, htypes⟩ := hcomp.cofinite_typing rhsTyped hscheme
      hnamesND hnamesFresh hnamesAvoid hscopePost hrawPost
    have hfitBoth := fun fresh (hf : FreshNames (fitAvoid ++ typeAvoid)
        (signatureScheme (ann.substTyFvars (s1 ++ sCheck))
          (K ++ softVars (substSoft (s1 ++ sCheck) F)) written
          (sCheck.onCtx (s1.onCtx ctx)) (sCheck.onTy rhsTy)).paramCount fresh) =>
      hfits fresh ⟨hf.length, hf.nodup, fun v hv ha => hf.avoid v hv (List.mem_append_left _ ha)⟩
    have htypeBoth := fun fresh (hf : FreshNames (fitAvoid ++ typeAvoid)
        (signatureScheme (ann.substTyFvars (s1 ++ sCheck))
          (K ++ softVars (substSoft (s1 ++ sCheck) F)) written
          (sCheck.onCtx (s1.onCtx ctx)) (sCheck.onTy rhsTy)).paramCount fresh) =>
      htypes fresh ⟨hf.length, hf.nodup, fun v hv ha => hf.avoid v hv (List.mem_append_right _ ha)⟩
    obtain ⟨avoid, hfitsFinal, htypesFinal⟩ := Typing.signatureBinding_onSubst_source
      hfitBoth htypeBoth s2 hs2
      (fun _ hk _ hv => scope_image (Subst.fixes_of_dom_avoids hb.dom_avoids) hk hv)
    have bodyTyped := hb.inputSound_source bodyCtxWF
    have hctxeq :
        s2.onCtx { sCheck.onCtx (s1.onCtx ctx) with
          env := signatureScheme (ann.substTyFvars (s1 ++ sCheck)) (K ++ softVars (substSoft (s1 ++ sCheck) F)) written (sCheck.onCtx (s1.onCtx ctx)) (sCheck.onTy rhsTy) ::
            (sCheck.onCtx (s1.onCtx ctx)).env } =
        { (s1 ++ sCheck ++ s2).onCtx ctx with
          env := s2.onPolyTy (signatureScheme (ann.substTyFvars (s1 ++ sCheck)) (K ++ softVars (substSoft (s1 ++ sCheck) F)) written (sCheck.onCtx (s1.onCtx ctx)) (sCheck.onTy rhsTy)) ::
            ((s1 ++ sCheck ++ s2).onCtx ctx).env } := by
      rw [Subst.onCtx_append, Subst.onCtx_append]
      rfl
    rw [hctxeq] at bodyTyped
    have hpostFinal := hscope.subst (s1 ++ sCheck ++ s2) (Subst.fixes_of_dom_avoids
      (fun p hp hk => (List.mem_append.mp hp).elim
        (fun hp => hprefixAvoid p hp (List.mem_append_left _ hk))
        (fun hp => hb.dom_avoids p hp hk)))
    have hannFinal : ∀ v ∈ (ann.substTyFvars (s1 ++ sCheck ++ s2)).rigidVars,
        v ∈ K ++ softVars (substSoft (s1 ++ sCheck ++ s2) F) := fun v hv =>
      hpostFinal v (List.mem_append_left _ (List.mem_append_left _ hv))
    have hrhsFinal : ∀ v ∈ (rhs.substTyFvars (s1 ++ sCheck ++ s2)).rigidVars,
        v ∈ K ++ softVars (substSoft (s1 ++ sCheck ++ s2) F) := fun v hv =>
      hpostFinal v (List.mem_append_left _ (List.mem_append_right _ hv))
    simp only [← substSoft_append, ← Input.substTyFvars_append, ← LetAnn.substTyFvars_append,
      List.append_assoc] at hfitsFinal htypesFinal bodyTyped hannFinal hrhsFinal ⊢
    refine Typing.letSignature (L := avoid) (Subst.onPolyTy_wf hs2 hscheme)
      hannFinal hrhsFinal hfitsFinal ?_ bodyTyped
    intro fresh hfresh
    simpa only [← Subst.onCtx_append, List.append_assoc] using htypesFinal fresh hfresh

  | .match_ _ hs hne hb =>
    intro hctx
    have hs1 := (hs.lc hctx).2
    have hbr := hb.lc (Subst.onCtx_wf hs1 hctx) (hs.lc hctx).1 .fvar
    have hscrut := (hs.inputSound_source hctx).onSubst_soft _ hbr.2 hb.dom_avoids
    have hbranches := hb.inputSound_source (Subst.onCtx_wf hs1 hctx) (hs.lc hctx).1 .fvar
    simp only [← substSoft_append, ← Input.substTyFvars_append] at hscrut
    simp only [Input.substTyFvars, Subst.onCtx_append]
    refine Typing.match_ hscrut (fun hn => hne (substInputBranches_eq_nil _ _ |>.mp hn)) ?_
    intro branch hbranch
    rw [substInputBranches_eq_map] at hbranch
    obtain ⟨original, ho, rfl⟩ := List.mem_map.mp hbranch
    have ht := hbranches (original.1, original.2.substTyFvars _) (by
      rw [substInputBranches_eq_map]
      exact List.mem_map.mpr ⟨original, ho, rfl⟩)
    simpa only [← substSoft_append, ← Input.substTyFvars_append, Subst.onCtx_append] using ht

termination_by (input.size, 0)
decreasing_by all_goals (simp only [Input.size, Input.size_openTyVars, Input.size_substTyFvars, sizeBranches_substInputBranches]; omega)

theorem _root_.InferBranches.inputSound_source
    (h : InferBranches K F frontier ctx scrutTy resultTy branches next subst completed)
    (hctx : CtxWF ctx) (hscrut : scrutTy.IsLC) (hresult : resultTy.IsLC) :
    ∀ branch ∈ branches, BranchTyping Typing (K ++ softVars (substSoft subst F))
      (subst.onCtx ctx) (branch.1, branch.2.substTyFvars subst)
      (subst.onTy scrutTy) (subst.onTy resultTy) := by
  match h with
  | .nil => intro branch hb; cases hb
  | @InferBranches.consWild body rest K F frontier ctx first s1 bodyOut bodyTy resultTy s2 scrutTy next s3 restOut
      _ hb hu hr =>
    obtain ⟨hbTy, hs1⟩ := hb.lc hctx
    have hs2 := hu.unifies.lc hbTy (Subst.onTy_lc hs1 hresult)
    have hctxRest := Subst.onCtx_wf hs2 (Subst.onCtx_wf hs1 hctx)
    have hscrutRest := Subst.onTy_lc hs2 (Subst.onTy_lc hs1 hscrut)
    have hresultRest := Subst.onTy_lc hs2 (Subst.onTy_lc hs1 hresult)
    have hs3 := (hr.lc hctxRest hscrutRest hresultRest).2
    have htail := hr.inputSound_source hctxRest hscrutRest hresultRest
    intro branch hbranch
    rcases List.mem_cons.mp hbranch with rfl | hbranch
    · have head := (hb.inputSound_source hctx).onSubst_soft (s2 ++ s3)
        (fun p hp => (List.mem_append.mp hp).elim (hs2 p) (hs3 p))
        (fun p hp => (List.mem_append.mp hp).elim (hu.dom_avoids p) (hr.dom_avoids p))
      have heq := congrArg s3.onTy hu.unifies.unifies
      rw [Subst.onTy_append] at head
      rw [heq] at head
      simpa only [Subst.onCtx_append, Subst.onTy_append, List.append_assoc,
        ← substSoft_append, ← Input.substTyFvars_append] using
        (BranchTyping.wildcard (scrutTy := (s1 ++ s2 ++ s3).onTy scrutTy) head)
    · have ht := htail (branch.1, branch.2.substTyFvars (s1 ++ s2)) (by
        rw [substInputBranches_eq_map]
        exact List.mem_map.mpr ⟨branch, hbranch, rfl⟩)
      simpa only [Subst.onCtx_append, Subst.onTy_append, ← substSoft_append,
        ← Input.substTyFvars_append] using ht
  | @InferBranches.cons name count body rest K F ctor scrutTy frontier s0 ctx first s1 bodyOut bodyTy resultTy s2 next s3 restOut
      _ hlookup hcount hu0 hb hu hr =>
    have hs0 := hu0.unifies.lc hscrut
      (.customTy (fun t ht => by obtain ⟨v, _, rfl⟩ := List.mem_map.mp ht; exact .fvar))
    have hbodyWF := branchBindings_wf (ctorr := ctor)
      (ta := ((freshVars frontier ctor.paramCount).map Ty.fvar).map s0.onTy)
      (Subst.onCtx_wf hs0 hctx)
      (fun t ht => by
        obtain ⟨v, hv, rfl⟩ := List.mem_map.mp ht
        obtain ⟨x, _, rfl⟩ := List.mem_map.mp hv
        exact Subst.onTy_lc hs0 .fvar) (by simp)
    obtain ⟨hbTy, hs1⟩ := hb.lc hbodyWF
    have hs2 := hu.unifies.lc hbTy (Subst.onTy_lc hs1 (Subst.onTy_lc hs0 hresult))
    have hctxRest := Subst.onCtx_wf hs2 (Subst.onCtx_wf hs1 (Subst.onCtx_wf hs0 hctx))
    have hscrutRest := Subst.onTy_lc hs2 (Subst.onTy_lc hs1 (Subst.onTy_lc hs0 hscrut))
    have hresultRest := Subst.onTy_lc hs2 (Subst.onTy_lc hs1 (Subst.onTy_lc hs0 hresult))
    have hs3 := (hr.lc hctxRest hscrutRest hresultRest).2
    have htail := hr.inputSound_source hctxRest hscrutRest hresultRest
    intro branch hbranch
    rcases List.mem_cons.mp hbranch with rfl | hbranch
    · let args := (((freshVars frontier ctor.paramCount).map Ty.fvar).map s0.onTy).map s1.onTy
      have hspec : BranchCtorSpec (s1.onCtx (s0.onCtx ctx)).ctors name count
          (s1.onTy (s0.onTy scrutTy)) ctor args (ctor.contents.map (Ty.openWith args)) := by
        refine ⟨hlookup, ?_, ?_, hcount, ?_⟩
        · simpa only [Subst.onTy_customTy, args] using congrArg s1.onTy hu0.unifies.unifies
        · simp only [args, List.length_map, freshVars_length]
        · exact forall₂_self_map (fun t ht => InstantiatesBy.openWith (ctor.bound t ht)
            (by simp only [args, List.length_map, freshVars_length]; omega))
      have head0 : BranchTyping Typing (K ++ softVars (substSoft (s0 ++ s1) F))
          (s1.onCtx (s0.onCtx ctx)) (.named name count, body.substTyFvars (s0 ++ s1)) (s1.onTy (s0.onTy scrutTy)) bodyTy := by
        refine .named hspec ?_
        rw [← Subst.onCtx_branchBindings hs1]
        simpa only [← substSoft_append, ← Input.substTyFvars_append] using hb.inputSound_source hbodyWF
      have head := head0.onSubst_soft (s2 ++ s3)
        (fun p hp => (List.mem_append.mp hp).elim (hs2 p) (hs3 p))
        (fun p hp => (List.mem_append.mp hp).elim (hu.dom_avoids p) (hr.dom_avoids p))
      have heq := congrArg s3.onTy hu.unifies.unifies
      simp only [Subst.onTy_append] at head
      rw [heq] at head
      simpa only [Subst.onCtx_append, Subst.onTy_append, ← substSoft_append,
        ← Input.substTyFvars_append, List.append_assoc] using head
    · have ht := htail (branch.1, branch.2.substTyFvars (s0 ++ s1 ++ s2)) (by
        rw [substInputBranches_eq_map]
        exact List.mem_map.mpr ⟨branch, hbranch, rfl⟩)
      simpa only [Subst.onCtx_append, Subst.onTy_append, ← substSoft_append,
        ← Input.substTyFvars_append] using ht
termination_by (sizeBranches branches, 0)
decreasing_by all_goals (simp only [sizeBranches, Input.size_substTyFvars, sizeBranches_substInputBranches]; omega)
end

/-- With no provisional slots, actual inference preserves authored annotations. -/
theorem _root_.Infer.inputSound (h : Infer K [] frontier ctx input next subst output ty)
    (hctx : CtxWF ctx) : Typing K (subst.onCtx ctx) input ty := by
  have hscope : ∀ v ∈ input.rigidVars, v ∈ K := by
    simpa only [SourceScope, softVars, TyList.freeVars, List.append_nil] using h.sourceScope
  have hinput := input.substTyFvars_eq_self_of_fixes
    (fun v hv => Subst.fixes_of_dom_avoids h.dom_avoids v (hscope v hv))
  simpa only [substSoft, List.map_nil, softVars, TyList.freeVars, List.append_nil, hinput] using
    h.inputSound_source hctx

theorem Completes.onSubst_soft {K : List Nat} {F : List Ty}
    (h : Completes (K ++ softVars F) input output) (S : Subst)
    (hlc : ∀ p ∈ S, p.2.IsLC) (havoid : ∀ p ∈ S, p.1 ∉ K) :
    Completes (K ++ softVars (substSoft S F)) (input.substTyFvars S) (output.substTyFvars S) :=
  h.onSubst_source S hlc (fun _ hk _ hv => scope_image (Subst.fixes_of_dom_avoids havoid) hk hv)

mutual
/-- Exact annotation fidelity follows the same scoped source transformation as
input typing. Completed let binders are compared by cofinite openings. -/
theorem _root_.Infer.completes_source (h : Infer K F frontier ctx input next subst output ty) :
    CtxWF ctx → Completes (K ++ softVars (substSoft subst F)) (input.substTyFvars subst) output := by
  match h with
  | .backend hemb h hbelow hK hrigid _ =>
      intro hctx
      have hinput := input.substTyFvars_eq_self_of_fixes (fun v hv =>
        Subst.fixes_of_dom_avoids h.dom_avoids v (hrigid v ((Input.toCore_rigidVars _ hemb v).mp hv)))
      rw [hinput]
      exact .complete hemb (fun v hv => List.mem_append_left _ (hrigid v hv))
        
  | @Infer.lambda K F ann body frontier param initial ctx next subst completed bodyTy _ hs hb =>
      intro hctx
      have hbodyCtx : CtxWF { ctx with env := PolyTy.mkTrivial param :: ctx.env } := by
        intro scheme hscheme
        rcases List.mem_cons.mp hscheme with rfl | hscheme
        · exact hs.lc
        · exact hctx scheme hscheme
      have hsubst := (hb.lc hbodyCtx).2
      simp only [Input.substTyFvars]
      have hout : ann.map (fun _ => subst.onTy param) =
          (ann.map (Template.substTyFvars subst)).map (fun _ => subst.onTy param) := by
        cases ann <;> rfl
      simp only [lambdaOutput, hout]
      refine Completes.lambda ?_ ?_ ?_
      · intro template heq
        cases ann with
        | none => cases heq
        | some original =>
          cases heq
          exact (hs.fits original rfl).substTyFvars subst
      · intro template heq v hv
        cases ann with
        | none => cases heq
        | some original =>
          cases heq
          obtain ⟨old, hold, hv⟩ := Template.rigidVars_substTyFvars hv
          exact scope_image (Subst.fixes_of_dom_avoids hb.dom_avoids) (hs.rigid original rfl old hold) hv
      · simpa only [Subst.onCtx, Subst.onEnv, List.map_cons, Subst.onPolyTy,
          PolyTy.mkTrivial] using hb.completes_source hbodyCtx
  | @Infer.app K F f arg frontier ctx first s1 fOut fTy second s2 argOut argTy s3 _ hf ha hu =>
      intro hctx
      have hs1 := (hf.lc hctx).2
      have haCtx := Subst.onCtx_wf hs1 hctx
      have hs2 := (ha.lc haCtx).2
      have hs3 := hu.unifies.lc (Subst.onTy_lc hs2 (hf.lc hctx).1)
        (.arrow (ha.lc haCtx).1 .fvar)
      have hfComp := (hf.completes_source hctx).onSubst_soft (s2 ++ s3)
        (fun pair hp => (List.mem_append.mp hp).elim (hs2 pair) (hs3 pair))
        (fun pair hp => (List.mem_append.mp hp).elim (ha.dom_avoids pair) (hu.dom_avoids pair))
      have haComp := (ha.completes_source haCtx).onSubst_soft s3 hs3 hu.dom_avoids
      simp only [← substSoft_append, ← Input.substTyFvars_append, List.append_assoc] at hfComp haComp
      simpa only [List.append_assoc] using Completes.app hfComp haComp
  | @Infer.letIn K F ann rhs body frontier ctx first s1 rhsOut rhsTy checked sCheck next s2 bodyOut bodyTy
      hraw hr hc hb =>
      intro hctx
      have hs1 := (hr.lc hctx).2
      have hrTy := (hr.lc hctx).1
      have hsCheck := hc.lc hrTy
      have hprefixAvoid : ∀ p ∈ s1 ++ sCheck, p.1 ∉ K := fun p hp =>
        (List.mem_append.mp hp).elim (hr.dom_avoids p) (hc.dom_avoids p)
      have hpost := hraw.subst (s1 ++ sCheck) (Subst.fixes_of_dom_avoids hprefixAvoid)
      have hann : ∀ template, (ann.substTyFvars (s1 ++ sCheck)) = .template template →
          ∀ v ∈ template.rigidVars, v ∈ K ++ softVars (substSoft (s1 ++ sCheck) F) := by
        intro template heq v hv
        exact hpost v (List.mem_append_left _ (List.mem_append_left _ (by
          simpa only [LetAnn.rigidVars, heq] using hv)))
      have hfit : (ann.substTyFvars (s1 ++ sCheck)).FitsMono (sCheck.onTy rhsTy) := by
        simpa only [LetAnn.substTyFvars_append] using hc.fits
      have checkedCtxWF := Subst.onCtx_wf hsCheck (Subst.onCtx_wf hs1 hctx)
      have checkedTyLC := Subst.onTy_lc hsCheck hrTy
      have bodyCtxWF : CtxWF
          { sCheck.onCtx (s1.onCtx ctx) with
            env := genScheme (K ++ softVars (substSoft (s1 ++ sCheck) F))
              (sCheck.onCtx (s1.onCtx ctx)).env (sCheck.onTy rhsTy) ::
              (sCheck.onCtx (s1.onCtx ctx)).env } := by
        intro scheme hscheme
        rcases List.mem_cons.mp hscheme with rfl | hscheme
        · exact genScheme_wf checkedTyLC
        · exact checkedCtxWF scheme hscheme
      have hs2 := (hb.lc bodyCtxWF).2
      have rhsTyped := (hr.inputSound_source hctx).onSubst_soft sCheck hsCheck hc.dom_avoids
      simp only [← substSoft_append, ← Input.substTyFvars_append] at rhsTyped
      have rhsGeneral := rhsTyped.generalise
        (names := genVars (K ++ softVars (substSoft (s1 ++ sCheck) F))
          (sCheck.onCtx (s1.onCtx ctx)).env (sCheck.onTy rhsTy))
        hfit hann genVars_nodup (fun _ hn => genVars_not_mem hn)
        (fun _ hn => genVars_not_mem_rigid hn)
      obtain ⟨avoid, hfits, hgeneral⟩ := Typing.binding_onSubst_source
        (scheme := genScheme (K ++ softVars (substSoft (s1 ++ sCheck) F))
          (sCheck.onCtx (s1.onCtx ctx)).env (sCheck.onTy rhsTy))
        (fun fresh hf => (rhsGeneral fresh hf).1)
        (fun fresh hf => (rhsGeneral fresh hf).2) s2 hs2
        (fun _ hk _ hv => scope_image (Subst.fixes_of_dom_avoids hb.dom_avoids) hk hv)
      have hannFinal : ∀ template, (ann.substTyFvars (s1 ++ sCheck ++ s2)) = .template template →
          ∀ v ∈ template.rigidVars, v ∈ K ++ softVars (substSoft (s1 ++ sCheck ++ s2) F) := by
        have hp := hraw.subst (s1 ++ sCheck ++ s2) (Subst.fixes_of_dom_avoids
          (fun p hp => (List.mem_append.mp hp).elim (hprefixAvoid p) (hb.dom_avoids p)))
        intro template heq v hv
        exact hp v (List.mem_append_left _ (List.mem_append_left _ (by
          simpa only [LetAnn.rigidVars, heq] using hv)))
      have rhsComp := (hr.completes_source hctx).onSubst_soft sCheck hsCheck hc.dom_avoids
      simp only [← substSoft_append, ← Input.substTyFvars_append] at rhsComp
      have rhsBound := (TypeOfHM.onSubst sCheck hsCheck (hr.sourceSound hctx)).tyBvarBounded
      obtain ⟨compAvoid, hcomplete⟩ := rhsComp.generalise_closed_after_source
        (names := genVars (K ++ softVars (substSoft (s1 ++ sCheck) F))
          (sCheck.onCtx (s1.onCtx ctx)).env (sCheck.onTy rhsTy))
        genVars_nodup (fun _ hn => genVars_not_mem_rigid hn) rhsBound s2 hs2
        (fun _ hk _ hv => scope_image (Subst.fixes_of_dom_avoids hb.dom_avoids) hk hv)
      have bodyComp := hb.completes_source bodyCtxWF
      simp only [← substSoft_append, ← Input.substTyFvars_append, ← LetAnn.substTyFvars_append,
        List.append_assoc] at hfits hcomplete bodyComp hannFinal ⊢
      simp only [letOutput]
      refine Completes.letIn (L := avoid ++ compAvoid) hannFinal ?_ ?_ bodyComp
      · intro fresh hf
        exact hfits fresh ⟨hf.length, hf.nodup, fun v hv hm => hf.avoid v hv (List.mem_append_left _ hm)⟩
      · intro fresh hf
        exact hcomplete fresh ⟨hf.length, hf.nodup, fun v hv hm => hf.avoid v hv (List.mem_append_right _ hm)⟩

  | @Infer.letSignature K F ann rhs body written frontier ctx first s1 rhsOut rhsTy checked sCheck next s2 bodyOut bodyTy
      hscope hprefix havoid hraw hr hc hescape hb =>
    intro hctx
    have hlen : written.length = ann.paramCount := by simpa only [freshVars_length] using congrArg List.length hprefix
    have hnd : written.Nodup := hprefix ▸ freshVars_nodup
    obtain ⟨hrTy, hs1⟩ := hr.lc hctx
    have hsCheck := hc.lc (by simpa using hlen) hrTy
    have checkedCtxWF := Subst.onCtx_wf hsCheck (Subst.onCtx_wf hs1 hctx)
    have checkedTyLC := Subst.onTy_lc hsCheck hrTy
    have hscheme : (signatureScheme (ann.substTyFvars (s1 ++ sCheck))
        (K ++ softVars (substSoft (s1 ++ sCheck) F)) written
        (sCheck.onCtx (s1.onCtx ctx)) (sCheck.onTy rhsTy)).WF := by
      simpa only [LetAnn.substTyFvars_append] using
        hc.scheme_wf (Q := K ++ softVars (substSoft (s1 ++ sCheck) F))
          (ctx := sCheck.onCtx (s1.onCtx ctx)) (by simpa using hlen) hrTy
    have hscopePost : ∀ v ∈ (ann.substTyFvars (s1 ++ sCheck)).rigidVars,
        v ∈ K ++ softVars (substSoft (s1 ++ sCheck) F) := by
      intro v hv
      obtain ⟨original, ho, hv⟩ := LetAnn.rigidVars_substTyFvars hv
      exact scope_image (Subst.fixes_of_dom_avoids (fun p hp hk =>
        (List.mem_append.mp hp).elim
          (fun hp => hr.dom_avoids p hp (List.mem_append_left _ hk))
          (fun hp => hc.dom_avoids p hp (List.mem_append_left _ hk))))
        (hscope original (List.mem_append_left _ (List.mem_append_left _ ho))) hv
    have havoidPost : ∀ name ∈ written, name ∉ K ++ softVars (substSoft (s1 ++ sCheck) F) := by
      intro name hn hm
      rcases List.mem_append.mp hm with hK | hF
      · exact havoid name hn (List.mem_append_left _ hK)
      · exact hescape name hn (List.mem_append_right _ hF)
    have hnamesFresh : ∀ name ∈ written, name ∉ (sCheck.onCtx (s1.onCtx ctx)).env.freeVars :=
      fun name hn hm => hescape name hn (List.mem_append_left _ hm)
    have bodyCtxWF : CtxWF
        { sCheck.onCtx (s1.onCtx ctx) with
          env := signatureScheme (ann.substTyFvars (s1 ++ sCheck)) (K ++ softVars (substSoft (s1 ++ sCheck) F)) written (sCheck.onCtx (s1.onCtx ctx)) (sCheck.onTy rhsTy) ::
            (sCheck.onCtx (s1.onCtx ctx)).env } := by
      intro scheme hschemeMem
      rcases List.mem_cons.mp hschemeMem with rfl | hschemeMem
      · exact hscheme
      · exact checkedCtxWF scheme hschemeMem
    have hs2 := (hb.lc bodyCtxWF).2
    have hprefixLC : ∀ p ∈ s1 ++ sCheck, p.2.IsLC := fun p hp =>
      (List.mem_append.mp hp).elim (hs1 p) (hsCheck p)
    have hprefixAvoid : ∀ p ∈ s1 ++ sCheck, p.1 ∉ K ++ written := fun p hp =>
      (List.mem_append.mp hp).elim (hr.dom_avoids p) (hc.dom_avoids p)
    have rhsTyped0 := (hr.inputSound_source hctx).onSubst_soft sCheck hsCheck hc.dom_avoids
    simp only [← substSoft_append, ← Input.substTyFvars_append] at rhsTyped0
    rw [Input.substTyFvars_openTyVars rhs hprefixLC
      (fun p hp hw => hprefixAvoid p hp (List.mem_append_right _ hw))] at rhsTyped0
    have rhsTyped : Typing ((K ++ softVars (substSoft (s1 ++ sCheck) F)) ++ written)
        (sCheck.onCtx (s1.onCtx ctx)) ((rhs.substTyFvars (s1 ++ sCheck)).openTyVars written)
        (sCheck.onTy rhsTy) := rhsTyped0.scope_mono (by
      intro k hk
      simp only [List.mem_append] at hk ⊢
      tauto)
    have hpost := hscope.subst (s1 ++ sCheck) (Subst.fixes_of_dom_avoids
      (fun p hp hk => hprefixAvoid p hp (List.mem_append_left _ hk)))
    have hrawPost : ∀ v ∈ (rhs.substTyFvars (s1 ++ sCheck)).rigidVars,
        v ∈ K ++ softVars (substSoft (s1 ++ sCheck) F) := fun v hv =>
      hpost v (List.mem_append_left _ (List.mem_append_right _ hv))
    have hcomp := hc.completion (Q := K ++ softVars (substSoft (s1 ++ sCheck) F))
      (ctx := sCheck.onCtx (s1.onCtx ctx)) (by simpa using hlen) hrTy
    simp only [← LetAnn.substTyFvars_append] at hcomp
    have hnamesND := hc.names_nodup (Q := K ++ softVars (substSoft (s1 ++ sCheck) F))
      (ctx := sCheck.onCtx (s1.onCtx ctx)) hnd
    have hnamesAvoid := hc.names_avoid (ctx := sCheck.onCtx (s1.onCtx ctx)) havoidPost
    have hnamesFresh := hc.names_fresh (Q := K ++ softVars (substSoft (s1 ++ sCheck) F)) hnamesFresh
    simp only [← LetAnn.substTyFvars_append] at hnamesND hnamesAvoid hnamesFresh
    obtain ⟨fitAvoid, hfits⟩ := hcomp.cofinite_fits hnamesND hnamesAvoid hscopePost checkedTyLC
    obtain ⟨typeAvoid, htypes⟩ := hcomp.cofinite_typing rhsTyped hscheme
      hnamesND hnamesFresh hnamesAvoid hscopePost hrawPost
    have hfitBoth := fun fresh (hf : FreshNames (fitAvoid ++ typeAvoid)
        (signatureScheme (ann.substTyFvars (s1 ++ sCheck))
          (K ++ softVars (substSoft (s1 ++ sCheck) F)) written
          (sCheck.onCtx (s1.onCtx ctx)) (sCheck.onTy rhsTy)).paramCount fresh) =>
      hfits fresh ⟨hf.length, hf.nodup, fun v hv ha => hf.avoid v hv (List.mem_append_left _ ha)⟩
    have htypeBoth := fun fresh (hf : FreshNames (fitAvoid ++ typeAvoid)
        (signatureScheme (ann.substTyFvars (s1 ++ sCheck))
          (K ++ softVars (substSoft (s1 ++ sCheck) F)) written
          (sCheck.onCtx (s1.onCtx ctx)) (sCheck.onTy rhsTy)).paramCount fresh) =>
      htypes fresh ⟨hf.length, hf.nodup, fun v hv ha => hf.avoid v hv (List.mem_append_right _ ha)⟩
    obtain ⟨avoid, hfitsFinal, htypesFinal⟩ := Typing.signatureBinding_onSubst_source
      hfitBoth htypeBoth s2 hs2
      (fun _ hk _ hv => scope_image (Subst.fixes_of_dom_avoids hb.dom_avoids) hk hv)
    have rhsComp0 := (hr.completes_source hctx).onSubst_soft sCheck hsCheck hc.dom_avoids
    simp only [← substSoft_append, ← Input.substTyFvars_append] at rhsComp0
    rw [Input.substTyFvars_openTyVars rhs hprefixLC
      (fun p hp hw => hprefixAvoid p hp (List.mem_append_right _ hw))] at rhsComp0
    have rhsComp : Completes ((K ++ softVars (substSoft (s1 ++ sCheck) F)) ++ written)
        ((rhs.substTyFvars (s1 ++ sCheck)).openTyVars written) (rhsOut.substTyFvars sCheck) :=
      rhsComp0.scope_mono (by intro k hk; simp only [List.mem_append] at hk ⊢; tauto)
    have rhsBound := (TypeOfHM.onSubst sCheck hsCheck (hr.sourceSound hctx)).tyBvarBounded
    obtain ⟨completeAvoid, hcomplete⟩ := hcomp.cofinite_completes rhsComp hnamesND hnamesAvoid hrawPost rhsBound
    obtain ⟨finalCompAvoid, hcompleteFinal⟩ := Completes.signatureBinding_onSubst_source hcomplete s2 hs2
      (fun _ hk _ hv => scope_image (Subst.fixes_of_dom_avoids hb.dom_avoids) hk hv)
    have bodyComp := hb.completes_source bodyCtxWF
    have hpostFinal := hscope.subst (s1 ++ sCheck ++ s2) (Subst.fixes_of_dom_avoids
      (fun p hp hk => (List.mem_append.mp hp).elim
        (fun hp => hprefixAvoid p hp (List.mem_append_left _ hk))
        (fun hp => hb.dom_avoids p hp hk)))
    have hannFinal : ∀ v ∈ (ann.substTyFvars (s1 ++ sCheck ++ s2)).rigidVars,
        v ∈ K ++ softVars (substSoft (s1 ++ sCheck ++ s2) F) := fun v hv =>
      hpostFinal v (List.mem_append_left _ (List.mem_append_left _ hv))
    have hrhsFinal : ∀ v ∈ (rhs.substTyFvars (s1 ++ sCheck ++ s2)).rigidVars,
        v ∈ K ++ softVars (substSoft (s1 ++ sCheck ++ s2) F) := fun v hv =>
      hpostFinal v (List.mem_append_left _ (List.mem_append_right _ hv))
    simp only [← substSoft_append, ← Input.substTyFvars_append, ← LetAnn.substTyFvars_append,
      List.append_assoc] at hfitsFinal hcompleteFinal bodyComp hannFinal hrhsFinal ⊢
    simp only [letOutput]
    refine Completes.letSignature (L := avoid ++ finalCompAvoid) hannFinal hrhsFinal ?_ ?_ bodyComp
    · intro fresh hf
      exact hfitsFinal fresh ⟨hf.length, hf.nodup, fun v hv hm => hf.avoid v hv (List.mem_append_left _ hm)⟩
    · intro fresh hf
      simpa only [List.append_assoc, LetAnn.paramCount_substTyFvars] using
        hcompleteFinal fresh ⟨hf.length, hf.nodup, fun v hv hm => hf.avoid v hv (List.mem_append_right _ hm)⟩

  | .match_ _ hs _ hb =>
    intro hctx
    have hs1 := (hs.lc hctx).2
    have hbr := hb.lc (Subst.onCtx_wf hs1 hctx) (hs.lc hctx).1 .fvar
    have hscrut := (hs.completes_source hctx).onSubst_soft _ hbr.2 hb.dom_avoids
    have hbranches := hb.completes_source (Subst.onCtx_wf hs1 hctx) (hs.lc hctx).1 .fvar
    simp only [← substSoft_append, ← Input.substTyFvars_append] at hscrut
    simp only [← substSoft_append, ← substInputBranches_append] at hbranches
    simpa only [Input.substTyFvars, ← substSoft_append, substInputBranches_append] using
      Completes.match_ hscrut hbranches
termination_by (input.size, 0)
decreasing_by all_goals (simp only [Input.size, Input.size_openTyVars, Input.size_substTyFvars, sizeBranches_substInputBranches]; omega)

theorem _root_.InferBranches.completes_source
    (h : InferBranches K F frontier ctx scrutTy resultTy branches next subst completed)
    (hctx : CtxWF ctx) (hscrut : scrutTy.IsLC) (hresult : resultTy.IsLC) :
    CompletedBranches Completes (K ++ softVars (substSoft subst F))
      (substInputBranches subst branches) completed := by
  match h with
  | .nil => exact .nil
  | @InferBranches.consWild body rest K F frontier ctx first s1 bodyOut bodyTy resultTy s2 scrutTy next s3 restOut
      _ hb hu hr =>
    obtain ⟨hbTy, hs1⟩ := hb.lc hctx
    have hs2 := hu.unifies.lc hbTy (Subst.onTy_lc hs1 hresult)
    have hctxRest := Subst.onCtx_wf hs2 (Subst.onCtx_wf hs1 hctx)
    have hscrutRest := Subst.onTy_lc hs2 (Subst.onTy_lc hs1 hscrut)
    have hresultRest := Subst.onTy_lc hs2 (Subst.onTy_lc hs1 hresult)
    have hs3 := (hr.lc hctxRest hscrutRest hresultRest).2
    have htail := hr.completes_source hctxRest hscrutRest hresultRest
    have head := (hb.completes_source hctx).onSubst_soft (s2 ++ s3)
      (fun p hp => (List.mem_append.mp hp).elim (hs2 p) (hs3 p))
      (fun p hp => (List.mem_append.mp hp).elim (hu.dom_avoids p) (hr.dom_avoids p))
    simp only [← substSoft_append, ← Input.substTyFvars_append, ← substInputBranches_append,
      List.append_assoc] at head htail ⊢
    exact CompletedBranches.cons head htail
  | @InferBranches.cons name count body rest K F ctor scrutTy frontier s0 ctx first s1 bodyOut bodyTy resultTy s2 next s3 restOut
      _ hlookup hcount hu0 hb hu hr =>
    have hs0 := hu0.unifies.lc hscrut
      (.customTy (fun t ht => by obtain ⟨v, _, rfl⟩ := List.mem_map.mp ht; exact .fvar))
    have hbodyWF := branchBindings_wf (ctorr := ctor)
      (ta := ((freshVars frontier ctor.paramCount).map Ty.fvar).map s0.onTy)
      (Subst.onCtx_wf hs0 hctx)
      (fun t ht => by
        obtain ⟨v, hv, rfl⟩ := List.mem_map.mp ht
        obtain ⟨x, _, rfl⟩ := List.mem_map.mp hv
        exact Subst.onTy_lc hs0 .fvar) (by simp)
    obtain ⟨hbTy, hs1⟩ := hb.lc hbodyWF
    have hs2 := hu.unifies.lc hbTy (Subst.onTy_lc hs1 (Subst.onTy_lc hs0 hresult))
    have hctxRest := Subst.onCtx_wf hs2 (Subst.onCtx_wf hs1 (Subst.onCtx_wf hs0 hctx))
    have hscrutRest := Subst.onTy_lc hs2 (Subst.onTy_lc hs1 (Subst.onTy_lc hs0 hscrut))
    have hresultRest := Subst.onTy_lc hs2 (Subst.onTy_lc hs1 (Subst.onTy_lc hs0 hresult))
    have hs3 := (hr.lc hctxRest hscrutRest hresultRest).2
    have htail := hr.completes_source hctxRest hscrutRest hresultRest
    have head := (hb.completes_source hbodyWF).onSubst_soft (s2 ++ s3)
      (fun p hp => (List.mem_append.mp hp).elim (hs2 p) (hs3 p))
      (fun p hp => (List.mem_append.mp hp).elim (hu.dom_avoids p) (hr.dom_avoids p))
    simp only [← substSoft_append, ← Input.substTyFvars_append, ← substInputBranches_append,
      List.append_assoc] at head htail ⊢
    exact CompletedBranches.cons head htail
termination_by (sizeBranches branches, 0)
decreasing_by all_goals (simp only [sizeBranches, Input.size_substTyFvars, sizeBranches_substInputBranches]; omega)
end

/-- The public empty-soft-context judgment preserves all authored annotations. -/
theorem _root_.Infer.completes (h : Infer K [] frontier ctx input next subst output ty)
    (hctx : CtxWF ctx) : Completes K input output := by
  have hscope : ∀ v ∈ input.rigidVars, v ∈ K := by
    simpa only [SourceScope, softVars, TyList.freeVars, List.append_nil] using h.sourceScope
  have hinput := input.substTyFvars_eq_self_of_fixes
    (fun v hv => Subst.fixes_of_dom_avoids h.dom_avoids v (hscope v hv))
  simpa only [substSoft, List.map_nil, softVars, TyList.freeVars, List.append_nil, hinput] using
    h.completes_source hctx

/-- The exact completed Core returned to the runtime is source typed. -/
theorem _root_.inferWithTypes_source_sound {ctors : CtorEnv} {input : Input} {result : InferenceResult}
    (h : inferWithTypes ctors input = some result) :
    TypeOfHM ⟨[], ctors⟩ result.completedExpr result.ty := by
  simpa only [Subst.onCtx_empty] using (inferWithTypes_infer h).sourceSound CtxWF.empty

theorem _root_.inferWithTypes_erase {ctors : CtorEnv} {input : Input} {result : InferenceResult}
    (h : inferWithTypes ctors input = some result) : result.completedExpr.erase = input.erase :=
  (inferWithTypes_infer h).erase

theorem _root_.inferWithTypes_input_sound {ctors : CtorEnv} {input : Input} {result : InferenceResult}
    (h : inferWithTypes ctors input = some result) : Typing input.rigidVars ⟨[], ctors⟩ input result.ty := by
  simpa only [Subst.onCtx_empty] using (inferWithTypes_infer h).inputSound CtxWF.empty

end Elaboration
