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

mutual
/-- Fixed annotations are protected through filling and generated scheme binders. -/
theorem _root_.Infer.completes (h : Infer K frontier ctx input next subst output ty) :
    Completes K input output := by
  match h with
  | .backend hemb _ _ _ hrigid => exact .complete hemb hrigid
  | .lambda hs hb =>
      refine .lambda ?_ hs.rigid hb.completes
      intro template heq
      exact (hs.fits template heq).onSubst (hs.rigid template heq) hb.dom_avoids
  | .app hf ha hu =>
      exact .app (.specialise hf.completes (fun pair hp =>
        (List.mem_append.mp hp).elim (ha.dom_avoids pair) (hu.dom_avoids pair)))
        (.specialise ha.completes hu.dom_avoids)
  | .letIn hr hc hb =>
      exact .letIn hc.fits hc.rigid (.specialise hr.completes hc.dom_avoids) hb.completes
        (fun _ hn => genVars_not_mem_rigid hn) hb.dom_avoids
  | .letSignature hprefix havoid hraw hr hc _ hb =>
      have hlen : _ := congrArg List.length hprefix
      simp only [freshVars_length] at hlen
      exact .letSignature (hc.completion hlen) hc.rigid hraw (hc.names_avoid havoid)
        (.specialise hr.completes hc.dom_avoids) hb.completes hb.dom_avoids
  | .match_ hs _ hb =>
      exact .match_ (.specialise hs.completes hb.dom_avoids) hb.completes
termination_by (input.size, 0)
decreasing_by all_goals (simp only [Input.size, Input.size_openTyVars]; omega)

theorem _root_.InferBranches.completes
    (h : InferBranches K frontier ctx scrutTy resultTy branches next subst completed) :
    CompletedBranches Completes K branches completed := by
  match h with
  | .nil => exact .nil
  | .consWild hb hu hr => exact .cons (.specialise hb.completes
      (fun p hp => (List.mem_append.mp hp).elim (hu.dom_avoids p) (hr.dom_avoids p))) hr.completes
  | .cons _ _ _ hb hu hr => exact .cons (.specialise hb.completes
      (fun p hp => (List.mem_append.mp hp).elim (hu.dom_avoids p) (hr.dom_avoids p))) hr.completes
termination_by (sizeBranches branches, 0)
decreasing_by all_goals (simp only [sizeBranches]; omega)
end

mutual
/-- Successful inference also satisfies the independent partial-input rules.
This connects input admissibility and completed-output typing at the same type. -/
theorem _root_.Infer.inputSound (h : Infer K frontier ctx input next subst output ty) :
    CtxWF ctx → Typing K (subst.onCtx ctx) input ty := by
  match h with
  | .backend hemb h hbelow hK hrigid =>
      intro hctx
      exact .complete hemb hrigid (h.sourceSound hctx hbelow hK hrigid)
  | @Infer.lambda K frontier ann param initial ctx body next subst completed bodyTy hs hb =>
      intro hctx
      have hbodyCtx : CtxWF { ctx with env := PolyTy.mkTrivial param :: ctx.env } := by
        intro scheme hscheme
        rcases List.mem_cons.mp hscheme with rfl | hscheme
        · exact hs.lc
        · exact hctx scheme hscheme
      have hsubst := (hb.lc hbodyCtx).2
      refine Typing.lambda (Subst.onTy_lc hsubst hs.lc) ?_ hs.rigid ?_
      · intro template heq
        exact (hs.fits template heq).onSubst (hs.rigid template heq) hb.dom_avoids
      · simpa only [Subst.onCtx, Subst.onEnv, List.map_cons, Subst.onPolyTy,
          PolyTy.mkTrivial] using hb.inputSound hbodyCtx
  | @Infer.app K frontier ctx f first s1 fOut fTy arg second s2 argOut argTy s3 hf ha hu =>
      intro hctx
      have hs1 := (hf.lc hctx).2
      have haCtx := Subst.onCtx_wf hs1 hctx
      have hs2 := (ha.lc haCtx).2
      have hs3 := hu.unifies.lc (Subst.onTy_lc hs2 (hf.lc hctx).1)
        (.arrow (ha.lc haCtx).1 .fvar)
      have hfTyped := (hf.inputSound hctx).onSubst (s2 ++ s3)
        (fun pair hp => (List.mem_append.mp hp).elim (hs2 pair) (hs3 pair))
        (fun pair hp => (List.mem_append.mp hp).elim (ha.dom_avoids pair) (hu.dom_avoids pair))
      have haTyped := (ha.inputSound haCtx).onSubst s3 hs3 hu.dom_avoids
      have heq : (s2 ++ s3).onTy fTy =
          .arrow (s3.onTy argTy) (s3.onTy (.fvar second)) := by
        simpa only [Unifies, Subst.onTy_append, Subst.onTy_arrow] using hu.unifies.unifies
      rw [heq] at hfTyped
      simp only [Subst.onCtx_append] at hfTyped
      simpa only [Subst.onCtx_append] using Typing.app hfTyped haTyped
  | @Infer.letIn K frontier ctx rhs first s1 rhsOut rhsTy ann checked sCheck body next s2 bodyOut bodyTy
      hr hc hb =>
      intro hctx
      have hs1 := (hr.lc hctx).2
      have hrTy := (hr.lc hctx).1
      have hsCheck := hc.lc hrTy
      have checkedCtxWF := Subst.onCtx_wf hsCheck (Subst.onCtx_wf hs1 hctx)
      have checkedTyLC := Subst.onTy_lc hsCheck hrTy
      have bodyCtxWF : CtxWF
          { sCheck.onCtx (s1.onCtx ctx) with
            env := genScheme K (sCheck.onCtx (s1.onCtx ctx)).env (sCheck.onTy rhsTy) ::
              (sCheck.onCtx (s1.onCtx ctx)).env } := by
        intro scheme hscheme
        rcases List.mem_cons.mp hscheme with rfl | hscheme
        · exact genScheme_wf checkedTyLC
        · exact checkedCtxWF scheme hscheme
      have hs2 := (hb.lc bodyCtxWF).2
      have rhsTyped := (hr.inputSound hctx).onSubst sCheck hsCheck hc.dom_avoids
      have rhsGeneral := rhsTyped.generalise
        (names := genVars K (sCheck.onCtx (s1.onCtx ctx)).env (sCheck.onTy rhsTy))
        hc.fits hc.rigid genVars_nodup (fun _ hn => genVars_not_mem hn)
        (fun _ hn => genVars_not_mem_rigid hn)
      obtain ⟨avoid, hfits, hgeneral⟩ := Typing.binding_onSubst
        (scheme := genScheme K (sCheck.onCtx (s1.onCtx ctx)).env (sCheck.onTy rhsTy))
        (fun fresh hf => (rhsGeneral fresh hf).1)
        (fun fresh hf => (rhsGeneral fresh hf).2) hc.rigid s2 hs2 hb.dom_avoids
      have bodyTyped := hb.inputSound bodyCtxWF
      have hctxeq :
          s2.onCtx
            { sCheck.onCtx (s1.onCtx ctx) with
              env := genScheme K (sCheck.onCtx (s1.onCtx ctx)).env (sCheck.onTy rhsTy) ::
                (sCheck.onCtx (s1.onCtx ctx)).env } =
          { (s1 ++ sCheck ++ s2).onCtx ctx with
            env := s2.onPolyTy (genScheme K (sCheck.onCtx (s1.onCtx ctx)).env (sCheck.onTy rhsTy)) ::
              ((s1 ++ sCheck ++ s2).onCtx ctx).env } := by
        rw [Subst.onCtx_append, Subst.onCtx_append]
        rfl
      rw [hctxeq] at bodyTyped
      refine Typing.letIn (L := avoid) (Subst.onPolyTy_wf hs2 (genScheme_wf checkedTyLC))
        hc.rigid hfits ?_ bodyTyped
      simpa only [← Subst.onCtx_append] using hgeneral

  | @Infer.letSignature written frontier K ctx first s1 rhsOut rhsTy ann checked sCheck body next s2 bodyOut bodyTy rhs
      hprefix havoid hraw hr hc hescape hb =>
    intro hctx
    have hlen : written.length = ann.paramCount := by simpa only [freshVars_length] using congrArg List.length hprefix
    have hnd : written.Nodup := hprefix ▸ freshVars_nodup
    obtain ⟨hrTy, hs1⟩ := hr.lc hctx
    have hsCheck := hc.lc hlen hrTy
    have checkedCtxWF := Subst.onCtx_wf hsCheck (Subst.onCtx_wf hs1 hctx)
    have checkedTyLC := Subst.onTy_lc hsCheck hrTy
    have hscheme := hc.scheme_wf (ctx := sCheck.onCtx (s1.onCtx ctx)) checkedTyLC
    have bodyCtxWF : CtxWF
        { sCheck.onCtx (s1.onCtx ctx) with
          env := signatureScheme ann K written (sCheck.onCtx (s1.onCtx ctx)) (sCheck.onTy rhsTy) ::
            (sCheck.onCtx (s1.onCtx ctx)).env } := by
      intro scheme hschemeMem
      rcases List.mem_cons.mp hschemeMem with rfl | hschemeMem
      · exact hscheme
      · exact checkedCtxWF scheme hschemeMem
    have hs2 := (hb.lc bodyCtxWF).2
    have rhsTyped := (hr.inputSound hctx).onSubst sCheck hsCheck hc.dom_avoids
    have hcomp := hc.completion (ctx := sCheck.onCtx (s1.onCtx ctx)) hlen
    obtain ⟨fitAvoid, hfits⟩ := hcomp.cofinite_fits
      (hc.names_nodup hnd) (hc.names_avoid havoid) hc.rigid checkedTyLC
    obtain ⟨typeAvoid, htypes⟩ := hcomp.cofinite_typing rhsTyped hscheme
      (hc.names_nodup hnd) (hc.names_fresh hescape) (hc.names_avoid havoid) hc.rigid hraw
    have hfitBoth := fun fresh (hf : FreshNames (fitAvoid ++ typeAvoid)
        (signatureScheme ann K written (sCheck.onCtx (s1.onCtx ctx)) (sCheck.onTy rhsTy)).paramCount fresh) =>
      hfits fresh ⟨hf.length, hf.nodup, fun v hv ha => hf.avoid v hv (List.mem_append_left _ ha)⟩
    have htypeBoth := fun fresh (hf : FreshNames (fitAvoid ++ typeAvoid)
        (signatureScheme ann K written (sCheck.onCtx (s1.onCtx ctx)) (sCheck.onTy rhsTy)).paramCount fresh) =>
      htypes fresh ⟨hf.length, hf.nodup, fun v hv ha => hf.avoid v hv (List.mem_append_right _ ha)⟩
    obtain ⟨avoid, hfitsFinal, htypesFinal⟩ := Typing.signatureBinding_onSubst
      hfitBoth htypeBoth hc.rigid s2 hs2 hb.dom_avoids
    have bodyTyped := hb.inputSound bodyCtxWF
    have hctxeq :
        s2.onCtx { sCheck.onCtx (s1.onCtx ctx) with
          env := signatureScheme ann K written (sCheck.onCtx (s1.onCtx ctx)) (sCheck.onTy rhsTy) ::
            (sCheck.onCtx (s1.onCtx ctx)).env } =
        { (s1 ++ sCheck ++ s2).onCtx ctx with
          env := s2.onPolyTy (signatureScheme ann K written (sCheck.onCtx (s1.onCtx ctx)) (sCheck.onTy rhsTy)) ::
            ((s1 ++ sCheck ++ s2).onCtx ctx).env } := by
      rw [Subst.onCtx_append, Subst.onCtx_append]
      rfl
    rw [hctxeq] at bodyTyped
    refine Typing.letSignature (L := avoid) (Subst.onPolyTy_wf hs2 hscheme)
      hc.rigid hraw hfitsFinal ?_ bodyTyped
    simpa only [← Subst.onCtx_append] using htypesFinal
  | .match_ hs hne hb =>
    intro hctx
    have hs1 := (hs.lc hctx).2
    have hbr := hb.lc (Subst.onCtx_wf hs1 hctx) (hs.lc hctx).1 .fvar
    have hscrut := (hs.inputSound hctx).onSubst _ hbr.2 hb.dom_avoids
    have hbranches := hb.inputSound (Subst.onCtx_wf hs1 hctx) (hs.lc hctx).1 .fvar
    simpa only [Subst.onCtx_append] using Typing.match_ hscrut hne hbranches
termination_by (input.size, 0)
decreasing_by all_goals (simp only [Input.size, Input.size_openTyVars]; omega)

theorem _root_.InferBranches.inputSound
    (h : InferBranches K frontier ctx scrutTy resultTy branches next subst completed)
    (hctx : CtxWF ctx) (hscrut : scrutTy.IsLC) (hresult : resultTy.IsLC) :
    ∀ branch ∈ branches, BranchTyping Typing K (subst.onCtx ctx) branch
      (subst.onTy scrutTy) (subst.onTy resultTy) := by
  match h with
  | .nil => intro branch hb; cases hb
  | @InferBranches.consWild K frontier ctx body first s1 bodyOut bodyTy resultTy s2 scrutTy rest next s3 restOut
      hb hu hr =>
    obtain ⟨hbTy, hs1⟩ := hb.lc hctx
    have hs2 := hu.unifies.lc hbTy (Subst.onTy_lc hs1 hresult)
    have hctxRest := Subst.onCtx_wf hs2 (Subst.onCtx_wf hs1 hctx)
    have hscrutRest := Subst.onTy_lc hs2 (Subst.onTy_lc hs1 hscrut)
    have hresultRest := Subst.onTy_lc hs2 (Subst.onTy_lc hs1 hresult)
    have hs3 := (hr.lc hctxRest hscrutRest hresultRest).2
    have htail := hr.inputSound hctxRest hscrutRest hresultRest
    intro branch hbranch
    rcases List.mem_cons.mp hbranch with rfl | hbranch
    · have head := (hb.inputSound hctx).onSubst (s2 ++ s3)
        (fun p hp => (List.mem_append.mp hp).elim (hs2 p) (hs3 p))
        (fun p hp => (List.mem_append.mp hp).elim (hu.dom_avoids p) (hr.dom_avoids p))
      have heq := congrArg s3.onTy hu.unifies.unifies
      rw [Subst.onTy_append] at head
      rw [heq] at head
      simpa only [Subst.onCtx_append, Subst.onTy_append, List.append_assoc] using
        (BranchTyping.wildcard (scrutTy := (s1 ++ s2 ++ s3).onTy scrutTy) head)
    · simpa only [Subst.onCtx_append, Subst.onTy_append] using htail branch hbranch
  | @InferBranches.cons name ctor count K scrutTy frontier s0 ctx body first s1 bodyOut bodyTy resultTy s2 rest next s3 restOut
      hlookup hcount hu0 hb hu hr =>
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
    have htail := hr.inputSound hctxRest hscrutRest hresultRest
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
      have head0 : BranchTyping Typing K (s1.onCtx (s0.onCtx ctx))
          (.named name count, body) (s1.onTy (s0.onTy scrutTy)) bodyTy := by
        refine .named hspec ?_
        rw [← Subst.onCtx_branchBindings hs1]
        exact hb.inputSound hbodyWF
      have head := head0.onSubst_fixes (s2 ++ s3)
        (fun p hp => (List.mem_append.mp hp).elim (hs2 p) (hs3 p))
        (Subst.fixes_of_dom_avoids (fun p hp =>
          (List.mem_append.mp hp).elim (hu.dom_avoids p) (hr.dom_avoids p)))
      have heq := congrArg s3.onTy hu.unifies.unifies
      simp only [Subst.onTy_append] at head
      rw [heq] at head
      simpa only [Subst.onCtx_append, Subst.onTy_append] using head
    · simpa only [Subst.onCtx_append, Subst.onTy_append] using htail branch hbranch
termination_by (sizeBranches branches, 0)
decreasing_by all_goals (simp only [sizeBranches]; omega)
end

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
