import FHM.Elaboration.Judgment
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
    (h : InferBranches K frontier ctx scrutTy resultTy branches next subst completed) :
    completed = [] ↔ branches = [] := by cases h <;> simp

mutual
/-- Successful elaboration produces ordinary annotated Core typing. The proof
constructs the typing from the inference derivation; it does not recheck output
with the Core inferer. -/
theorem _root_.Infer.sourceSound (h : Infer K frontier ctx input next subst output ty) :
    CtxWF ctx → TypeOfHM (subst.onCtx ctx) output ty := by
  match h with
  | .backend _ h hbelow hK hrigid =>
      intro hctx
      exact h.sourceSound hctx hbelow hK hrigid
  | @Infer.lambda K frontier ann param initial ctx body next subst completed bodyTy hs hb =>
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
  | @Infer.app K frontier ctx f first s1 fOut fTy arg second s2 argOut argTy s3 hf ha hu =>
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
      have rhsTyped := TypeOfHM.onSubst sCheck hsCheck (hr.sourceSound hctx)
      have rhsGeneral := TypeOfHM.generaliseAnnotated
        (names := genVars K (sCheck.onCtx (s1.onCtx ctx)).env (sCheck.onTy rhsTy))
        rhsTyped genVars_nodup
        (fun name hn => genVars_not_mem hn)
      obtain ⟨avoid, rhsFinal⟩ := GeneralisesTo.onSubst_annotated
        (genScheme_wf checkedTyLC) rhsGeneral s2 hs2
      have bodyTyped := hb.sourceSound bodyCtxWF
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
      refine TypeOfHM.letIn (L := avoid) (Subst.onPolyTy_wf hs2 (genScheme_wf checkedTyLC))
        (fun _ heq => Option.some.inj heq) ?_ rfl bodyTyped
      simpa only [letOutput, genScheme, ← Subst.onCtx_append] using rhsFinal

  | @Infer.letSignature written frontier K ctx first s1 rhsOut rhsTy ann checked sCheck body next s2 bodyOut bodyTy rhs
      hprefix havoid _ hr hc hescape hb =>
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
    have rhsTyped := TypeOfHM.onSubst sCheck hsCheck (hr.sourceSound hctx)
    have rhsGeneral := TypeOfHM.generaliseAnnotated
      (names := signatureNames ann K written (sCheck.onCtx (s1.onCtx ctx)) (sCheck.onTy rhsTy))
      rhsTyped (hc.names_nodup hnd) (hc.names_fresh hescape)
    rw [← hc.scheme_eq_close hlen hnd havoid] at rhsGeneral
    obtain ⟨avoid, rhsFinal⟩ := GeneralisesTo.onSubst_annotated hscheme rhsGeneral s2 hs2
    have bodyTyped := hb.sourceSound bodyCtxWF
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
    refine TypeOfHM.letIn (L := avoid) (Subst.onPolyTy_wf hs2 hscheme)
      (fun _ heq => Option.some.inj heq) ?_ rfl bodyTyped
    simpa only [letOutput, ← Subst.onCtx_append] using rhsFinal
  | .match_ hs hne hb =>
    intro hctx
    have hs1 := (hs.lc hctx).2
    have hbr := hb.lc (Subst.onCtx_wf hs1 hctx) (hs.lc hctx).1 .fvar
    have hscrut := TypeOfHM.onSubst _ hbr.2 (hs.sourceSound hctx)
    have hbranches := hb.sourceSound (Subst.onCtx_wf hs1 hctx) (hs.lc hctx).1 .fvar
    simpa only [Subst.onCtx_append] using
      TypeOfHM.match_ hscrut (fun hnil => hne (hb.nil_iff.mp hnil)) hbranches
termination_by (input.size, 0)
decreasing_by all_goals (simp only [Input.size, Input.size_openTyVars]; omega)

theorem _root_.InferBranches.sourceSound
    (h : InferBranches K frontier ctx scrutTy resultTy branches next subst completed)
    (hctx : CtxWF ctx) (hscrut : scrutTy.IsLC) (hresult : resultTy.IsLC) :
    ∀ branch ∈ completed, TypeOfMatchBranch (subst.onCtx ctx) branch
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
decreasing_by all_goals (simp only [sizeBranches]; omega)
end

mutual
/-- Elaboration changes annotations and binders while preserving runtime syntax. -/
theorem _root_.Infer.erase (h : Infer K frontier ctx input next subst output ty) :
    output.erase = input.erase := by
  match h with
  | .backend hemb _ _ _ _ => exact Input.toCore_erase _ hemb
  | .lambda _ hb =>
      simpa only [lambdaOutput, Expr.erase, Input.erase] using
        congrArg (Expr.lambda none) hb.erase
  | .app hf ha _ =>
      simp only [Expr.erase, Expr.erase_substTyFvars, Input.erase, hf.erase, ha.erase]
  | .letIn hr _ hb =>
      simp only [letOutput, Expr.erase, Expr.erase_substTyFvars,
        Expr.erase_closeTyVars, Input.erase, hr.erase, hb.erase]
  | .letSignature _ _ _ hr _ _ hb =>
      simp only [letOutput, Expr.erase, Expr.erase_substTyFvars,
        Expr.erase_closeTyVars, Input.erase, hr.erase, hb.erase, Input.erase_openTyVars]
  | .match_ hs _ hb =>
      simp only [Expr.erase, Expr.erase_substTyFvars, Input.erase, hs.erase, hb.erase]
termination_by (input.size, 0)
decreasing_by all_goals (simp only [Input.size, Input.size_openTyVars]; omega)

theorem _root_.InferBranches.erase
    (h : InferBranches K frontier ctx scrutTy resultTy branches next subst completed) :
    completed.map (fun pe => (pe.1, pe.2.erase)) = eraseBranches branches := by
  match h with
  | .nil => rfl
  | .consWild hb _ hr =>
      simp only [List.map_cons, eraseBranches, Expr.erase_substTyFvars, hb.erase, hr.erase]
  | .cons _ _ _ hb _ hr =>
      simp only [List.map_cons, eraseBranches, Expr.erase_substTyFvars, hb.erase, hr.erase]
termination_by (sizeBranches branches, 0)
decreasing_by all_goals (simp only [sizeBranches]; omega)
end

theorem _root_.Infer.sound (h : Infer K frontier ctx input next subst output ty) (hctx : CtxWF ctx) :
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

def seed (K : List Nat) (frontier : Nat) (ann : Option Template) :
    Option { result : Nat × Ty // Seed K frontier ann result.2 result.1 } :=
  match ann with
  | none => some ⟨(frontier + 1, .fvar frontier), .absent⟩
  | some template =>
      let result := template.allocate frontier
      if hlc : result.2.bvarsBelow 0 = true then
        if hrigid : template.rigidVars.all (fun v => decide (v ∈ K)) = true then
          some ⟨result, .annotated rfl ((Ty.bvarsBelow_iff _).mp hlc)
            (fun v hv => of_decide_eq_true (List.all_eq_true.mp hrigid v hv))⟩
        else none
      else none

def checkLet (K : List Nat) (frontier : Nat) (ann : LetAnn) (ty : Ty) :
    Option { result : Nat × Subst // LetCheck K frontier ty ann result.1 result.2 } :=
  match ann with
  | .absent => some ⟨(frontier, []), .absent⟩
  | .template .hole => some ⟨(frontier, []), .hole⟩
  | .template template =>
      let result := template.allocate frontier
      if hlc : result.2.bvarsBelow 0 = true then
        if hrigid : template.rigidVars.all (fun v => decide (v ∈ K)) = true then
          match unifyCoreK K ty result.2 with
          | none => none
          | some ⟨subst, hunifies, havoids⟩ =>
              some ⟨(result.1, subst), .template rfl ((Ty.bvarsBelow_iff _).mp hlc)
                (fun v hv => of_decide_eq_true (List.all_eq_true.mp hrigid v hv))
                ⟨hunifies, havoids⟩⟩
        else none
      else none
  | .complete _ | .partialForall _ _ => none

def checkSignature (K written : List Nat) (frontier : Nat) (ann : LetAnn) (ty : Ty) :
    Option { result : Nat × Subst // SignatureCheck K written frontier ty ann result.1 result.2 } :=
  match ann with
  | .complete scheme =>
    if hwf : scheme.body.bvarsBelow scheme.paramCount = true then
      if hr : scheme.body.freeVars.all (fun v => decide (v ∈ K)) = true then
        match unifyCoreK (K ++ written) ty (scheme.openVars written) with
        | none => none
        | some ⟨subst, hu, hd⟩ => some ⟨(frontier, subst), .complete
            (PolyTy.wf_iff_bvarsBelow.mp hwf)
            (fun v hv => of_decide_eq_true (List.all_eq_true.mp hr v hv)) ⟨hu, hd⟩⟩
      else none
    else none
  | .partialForall _ template =>
    let expected := (template.openTyVarsFrom 0 written).allocate frontier
    if hlc : expected.2.bvarsBelow 0 = true then
      if hr : template.rigidVars.all (fun v => decide (v ∈ K)) = true then
        match unifyCoreK (K ++ written) ty expected.2 with
        | none => none
        | some ⟨subst, hu, hd⟩ => some ⟨(expected.1, subst), .partialSignature rfl
            ((Ty.bvarsBelow_iff _).mp hlc)
            (fun v hv => of_decide_eq_true (List.all_eq_true.mp hr v hv)) ⟨hu, hd⟩⟩
      else none
    else none
  | .absent | .template _ => none

private theorem ctxBelow_of_all {ctx : Ctx} {frontier : Nat}
    (h : ctx.env.freeVars.all (fun v => decide (v < frontier)) = true) : CtxBelow frontier ctx := by
  intro scheme hscheme
  apply Ty.BelowFvars.of_freeVars_lt
  intro v hv
  exact of_decide_eq_true (List.all_eq_true.mp h v (Env.mem_freeVars_iff.mpr ⟨scheme, hscheme, hv⟩))

mutual
/-- One dispatch path: completed subtrees use the existing verified worker;
partial spines elaborate while inferring. Unsupported partial constructs fail
before any completed recursive-signature interpretation can be introduced. -/
def _root_.inferWithTypesCore (K : List Nat) (frontier : Nat) (ctx : Ctx) (input : Input) :
    Option { result : Nat × Subst × Expr × Ty × InferredNodeTypes × InferredBinderSchemes //
      Infer K frontier ctx input result.1 result.2.1 result.2.2.1 result.2.2.2.1 } :=
  if hK : K.all (fun v => decide (v < frontier)) = true then
    if hctx : ctx.env.freeVars.all (fun v => decide (v < frontier)) = true then
      match hemb : input.toCore with
      | some core =>
          if hrigid : core.tyFreeVars.all (fun v => decide (v ∈ K)) = true then
            match CoreBackend.inferWithTypesCore K frontier ctx core with
            | none => none
            | some ⟨(next, subst, ty, nodeTypes, schemes), h⟩ =>
                some ⟨(next, subst, core, ty, nodeTypes, schemes), .backend hemb h (ctxBelow_of_all hctx)
                  (fun v hv => of_decide_eq_true (List.all_eq_true.mp hK v hv))
                  (fun v hv => of_decide_eq_true (List.all_eq_true.mp hrigid v hv))⟩
          else none
      | none =>
          match input with
          | .lambda ann body =>
              match seed K frontier ann with
              | none => none
              | some ⟨(initial, param), hs⟩ =>
                  match inferWithTypesCore K initial { ctx with env := PolyTy.mkTrivial param :: ctx.env } body with
                  | none => none
                  | some ⟨(next, subst, completed, bodyTy, bodyTypes, bodySchemes), hb⟩ =>
                      let ty := .arrow (subst.onTy param) bodyTy
                      some ⟨(next, subst, lambdaOutput ann param subst completed, ty,
                        .root ty ++ bodyTypes.below .lambdaBody, bodySchemes.below .lambdaBody), .lambda hs hb⟩
          | .app f arg =>
              match inferWithTypesCore K frontier ctx f with
              | none => none
              | some ⟨(first, s1, fOut, fTy, fTypes, fSchemes), hf⟩ =>
                  match inferWithTypesCore K first (s1.onCtx ctx) arg with
                  | none => none
                  | some ⟨(second, s2, argOut, argTy, argTypes, argSchemes), ha⟩ =>
                      match unifyCoreK K (s2.onTy fTy) (.arrow argTy (.fvar second)) with
                      | none => none
                      | some ⟨s3, hu, hd⟩ =>
                          let ty := s3.onTy (.fvar second)
                          some ⟨(second + 1, s1 ++ s2 ++ s3,
                            .app (fOut.substTyFvars (s2 ++ s3)) (argOut.substTyFvars s3), ty,
                            .root ty ++ (fTypes.onSubst (s2 ++ s3)).below .appFun ++
                              (argTypes.onSubst s3).below .appArg,
                            (fSchemes.onSubst (s2 ++ s3)).below .appFun ++
                              (argSchemes.onSubst s3).below .appArg), .app hf ha ⟨hu, hd⟩⟩
          | .letIn ann rhs body =>
            if ann.isSignature then
              let written := freshVars frontier ann.paramCount
              if hraw : rhs.rigidVars.all (fun v => decide (v ∈ K)) = true then
                match inferWithTypesCore (K ++ written) (frontier + ann.paramCount) ctx (rhs.openTyVars written) with
                | none => none
                | some ⟨(first, s1, rhsOut, rhsTy, rhsTypes, rhsSchemes), hr⟩ =>
                  match checkSignature K written first ann rhsTy with
                  | none => none
                  | some ⟨(checked, sCheck), hc⟩ =>
                    let checkedCtx := sCheck.onCtx (s1.onCtx ctx)
                    let checkedTy := sCheck.onTy rhsTy
                    let checkedOut := rhsOut.substTyFvars sCheck
                    let scheme := signatureScheme ann K written checkedCtx checkedTy
                    let names := signatureNames ann K written checkedCtx checkedTy
                    if hescape : ∀ name ∈ written, name ∉ checkedCtx.env.freeVars then
                      match inferWithTypesCore K checked { checkedCtx with env := scheme :: checkedCtx.env } body with
                      | none => none
                      | some ⟨(next, s2, bodyOut, bodyTy, bodyTypes, bodySchemes), hb⟩ =>
                        let rhsFinalTypes := (((rhsTypes.onSubst sCheck).closeTyVars written).onSubst s2)
                          |>.underTyBinders ann.paramCount |>.below .letRhs
                        let rhsFinalSchemes := (((rhsSchemes.onSubst sCheck).closeTyVars written).onSubst s2)
                          |>.underTyBinders ann.paramCount |>.below .letRhs
                        let inferred : InferredBinderSchemes := match ann with
                          | .partialForall _ _ => [{ site := .letIn [], scheme := s2.onPolyTy scheme, tyDepth := 0 }]
                          | _ => []
                        some ⟨(next, s1 ++ sCheck ++ s2, letOutput scheme names checkedOut bodyOut s2, bodyTy,
                          .root bodyTy ++ rhsFinalTypes ++ bodyTypes.below .letBody,
                          inferred ++ rhsFinalSchemes ++ bodySchemes.below .letBody),
                          .letSignature rfl (fun name hn hk => by
                            have hlt := of_decide_eq_true (List.all_eq_true.mp hK name hk)
                            have hge := freshVars_ge name hn
                            omega)
                            (fun v hv => of_decide_eq_true (List.all_eq_true.mp hraw v hv)) hr hc hescape hb⟩
                    else none
              else none
            else
                  match inferWithTypesCore K frontier ctx rhs with
                  | none => none
                  | some ⟨(first, s1, rhsOut, rhsTy, rhsTypes, rhsSchemes), hr⟩ =>
                      match checkLet K first ann rhsTy with
                      | none => none
                      | some ⟨(checked, sCheck), hc⟩ =>
                          let checkedCtx := sCheck.onCtx (s1.onCtx ctx)
                          let checkedTy := sCheck.onTy rhsTy
                          let checkedOut := rhsOut.substTyFvars sCheck
                          let scheme := genScheme K checkedCtx.env checkedTy
                          let names := genVars K checkedCtx.env checkedTy
                          match inferWithTypesCore K checked { checkedCtx with env := scheme :: checkedCtx.env } body with
                          | none => none
                          | some ⟨(next, s2, bodyOut, bodyTy, bodyTypes, bodySchemes), hb⟩ =>
                              let binder : InferredBinderScheme :=
                                { site := .letIn [], scheme := s2.onPolyTy scheme, tyDepth := 0 }
                              some ⟨(next, s1 ++ sCheck ++ s2,
                                letOutput scheme names checkedOut bodyOut s2, bodyTy,
                                .root bodyTy ++ (rhsTypes.onSubst (sCheck ++ s2)).below .letRhs ++
                                  bodyTypes.below .letBody,
                                binder :: (rhsSchemes.onSubst (sCheck ++ s2)).below .letRhs ++
                                  bodySchemes.below .letBody), .letIn hr hc hb⟩
          | .match_ scrut branches =>
              match inferWithTypesCore K frontier ctx scrut with
              | none => none
              | some ⟨(first, s1, scrutOut, scrutTy, scrutTypes, scrutSchemes), hs⟩ =>
                match hh : branches.head? with
                | none => none
                | some _ =>
                  match inferBranchesWithTypesCore K (first + 1) (s1.onCtx ctx)
                      scrutTy (.fvar first) 0 branches with
                  | none => none
                  | some ⟨(next, s2, branchOut, branchTypes, branchSchemes), hb⟩ =>
                    let ty := s2.onTy (.fvar first)
                    some ⟨(next, s1 ++ s2, .match_ (scrutOut.substTyFvars s2) branchOut, ty,
                      .root ty ++ (scrutTypes.onSubst s2).below .matchScrut ++ branchTypes,
                      (scrutSchemes.onSubst s2).below .matchScrut ++ branchSchemes),
                      .match_ hs (by intro heq; rw [heq] at hh; simp at hh) hb⟩
          | _ => none
    else none
  else none
termination_by (input.size, 0)
decreasing_by all_goals (simp only [Input.size, Input.size_openTyVars]; omega)

def _root_.inferBranchesWithTypesCore (K : List Nat) (Φ : Nat) (ctx : Ctx) (scrutTy : Ty) (ρ : Ty)
    (branchIndex : Nat) (branches : List (MatchPattern × Input)) :
    Option { r : Nat × Subst × List (MatchPattern × Expr) × InferredNodeTypes × InferredBinderSchemes //
      InferBranches K Φ ctx scrutTy ρ branches r.1 r.2.1 r.2.2.1 } :=
  match branches with
  | [] => some ⟨(Φ, [], [], [], []), .nil⟩
  | (.wildcard, body) :: rest =>
      match inferWithTypesCore K Φ ctx body with
      | none => none
      | some ⟨(Φ₁, S₁, bodyOut, τb, bodyTypes, bodySchemes), hbody⟩ =>
        match unifyCoreK K τb (S₁.onTy ρ) with
        | none => none
        | some ⟨S₂, huni, hav₂⟩ =>
          match inferBranchesWithTypesCore K Φ₁ (S₂.onCtx (S₁.onCtx ctx))
              (S₂.onTy (S₁.onTy scrutTy)) (S₂.onTy (S₁.onTy ρ)) (branchIndex + 1) rest with
          | none => none
          | some ⟨(Φ₂, S₃, restOut, restTypes, restSchemes), hrest⟩ =>
            let schemes := (bodySchemes.onSubst (S₂ ++ S₃)).below
              (.matchBranch branchIndex) ++ restSchemes
            let nodeTypes := (bodyTypes.onSubst (S₂ ++ S₃)).below
              (.matchBranch branchIndex) ++ restTypes
            some ⟨(Φ₂, S₁ ++ S₂ ++ S₃,
                (.wildcard, bodyOut.substTyFvars (S₂ ++ S₃)) :: restOut, nodeTypes, schemes),
                .consWild hbody ⟨huni, hav₂⟩ hrest⟩
  | (.named c n, body) :: rest =>
      match hget : LookupList.get? ctx.ctors c with
      | none => none
      | some ctorr =>
        if hcont : n = ctorr.contents.length then
          match unifyCoreK K scrutTy
              (.customTy ctorr.tyName ((freshVars Φ ctorr.paramCount).map (Ty.fvar ·))) with
          | none => none
          | some ⟨S₀, huni0, hav0⟩ =>
            match inferWithTypesCore K (Φ + ctorr.paramCount)
                { (S₀.onCtx ctx) with
                  env := (ctorr.contents.map (Ty.openWith
                      (((freshVars Φ ctorr.paramCount).map (Ty.fvar ·)).map S₀.onTy))).map PolyTy.mkTrivial
                    ++ (S₀.onCtx ctx).env }
                body with
            | none => none
            | some ⟨(Φ₁, S₁, bodyOut, τb, bodyTypes, bodySchemes), hbody⟩ =>
              match unifyCoreK K τb (S₁.onTy (S₀.onTy ρ)) with
              | none => none
              | some ⟨S₂, huni, hav₂⟩ =>
                match inferBranchesWithTypesCore K Φ₁ (S₂.onCtx (S₁.onCtx (S₀.onCtx ctx)))
                    (S₂.onTy (S₁.onTy (S₀.onTy scrutTy))) (S₂.onTy (S₁.onTy (S₀.onTy ρ)))
                    (branchIndex + 1) rest with
                | none => none
                | some ⟨(Φ₂, S₃, restOut, restTypes, restSchemes), hrest⟩ =>
                  let schemes := (bodySchemes.onSubst (S₂ ++ S₃)).below
                    (.matchBranch branchIndex) ++ restSchemes
                  let nodeTypes := (bodyTypes.onSubst (S₂ ++ S₃)).below
                    (.matchBranch branchIndex) ++ restTypes
                  some ⟨(Φ₂, S₀ ++ S₁ ++ S₂ ++ S₃,
                      (.named c n, bodyOut.substTyFvars (S₂ ++ S₃)) :: restOut, nodeTypes, schemes),
                      .cons hget hcont ⟨huni0, hav0⟩ hbody ⟨huni, hav₂⟩ hrest⟩
        else none
termination_by (sizeBranches branches, 0)
decreasing_by
  all_goals (try simp only [sizeBranches]; omega)

end

/-- The plain certificate API projects the one metadata-producing run. -/
def _root_.inferCore (K : List Nat) (frontier : Nat) (ctx : Ctx) (input : Input) :
    Option { result : Nat × Subst × Expr × Ty //
      Infer K frontier ctx input result.1 result.2.1 result.2.2.1 result.2.2.2 } :=
  match inferWithTypesCore K frontier ctx input with
  | none => none
  | some ⟨(next, subst, output, ty, _, _), h⟩ => some ⟨(next, subst, output, ty), h⟩

@[simp] theorem _root_.inferCore_isSome (K : List Nat) (frontier : Nat) (ctx : Ctx) (input : Input) :
    (inferCore K frontier ctx input).isSome = (inferWithTypesCore K frontier ctx input).isSome := by
  unfold inferCore
  cases inferWithTypesCore K frontier ctx input with
  | none => rfl
  | some result => rcases result with ⟨⟨next, subst, output, ty, nodes, schemes⟩, h⟩; rfl

/-- Public artifacts and completed ordinary Core come from the same inference. -/
structure _root_.InferenceResult where
  frontier : Nat
  subst : Subst
  completedExpr : Expr
  ty : Ty
  nodeTypes : NodeTypeMap
  binderSchemes : BinderSchemeMap

def Input.freshFloor (input : Input) : Nat := tyVarCeil input.rigidVars

theorem Input.lt_freshFloor {input : Input} {v : Nat} (h : v ∈ input.rigidVars) :
    v < input.freshFloor := lt_tyVarCeil h

def _root_.inferWithTypes (ctors : CtorEnv) (input : Input) : Option InferenceResult :=
  (inferWithTypesCore input.rigidVars input.freshFloor ⟨[], ctors⟩ input).map fun result =>
    { frontier := result.val.1
      subst := result.val.2.1
      completedExpr := result.val.2.2.1
      ty := result.val.2.2.2.1
      nodeTypes := result.val.2.2.2.2.1.toMap
      binderSchemes := result.val.2.2.2.2.2.toMap }

def _root_.principalType (ctors : CtorEnv) (input : Input) : Option Ty :=
  (inferCore input.rigidVars input.freshFloor ⟨[], ctors⟩ input).map (·.val.2.2.2)

def _root_.typecheck (ctors : CtorEnv) (input : Input) : Option PolyTy :=
  (principalType ctors input).map (genScheme [] [])

/-- A public artifact result carries the canonical elaboration derivation. -/
theorem _root_.inferWithTypes_infer {ctors : CtorEnv} {input : Input} {result : InferenceResult}
    (h : inferWithTypes ctors input = some result) :
    Infer input.rigidVars input.freshFloor ⟨[], ctors⟩ input result.frontier result.subst
      result.completedExpr result.ty := by
  unfold inferWithTypes at h
  cases hcore : inferWithTypesCore input.rigidVars input.freshFloor ⟨[], ctors⟩ input with
  | none => simp only [hcore, Option.map_none, reduceCtorEq] at h
  | some r =>
    rcases r with ⟨⟨next, subst, output, ty, nodes, schemes⟩, hi⟩
    simp only [hcore, Option.map_some, Option.some.injEq] at h
    subst result
    exact hi

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
