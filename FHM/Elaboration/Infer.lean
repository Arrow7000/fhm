import FHM.Elaboration.Judgment
import FHM.Elaboration.Close

namespace Elaboration

/-- Successful elaboration produces ordinary annotated Core typing. The proof
constructs the typing from the inference derivation; it does not recheck output
with the Core inferer. -/
theorem _root_.Infer.sourceSound (h : Infer K frontier ctx input next subst output ty) :
    CtxWF ctx → TypeOfHM (subst.onCtx ctx) output ty := by
  induction h with
  | backend _ h hbelow hK hrigid =>
      intro hctx
      exact h.sourceSound hctx hbelow hK hrigid
  | @lambda K frontier ann param initial ctx body next subst completed bodyTy hs hb ih =>
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
          Subst.onPolyTy, PolyTy.mkTrivial] using ih hbodyCtx
  | @app K frontier ctx f first s1 fOut fTy arg second s2 argOut argTy s3 hf ha hu ihf iha =>
      intro hctx
      have hs1 := (hf.lc hctx).2
      have haCtx := Subst.onCtx_wf hs1 hctx
      have hs2 := (ha.lc haCtx).2
      have hs3 := hu.unifies.lc (Subst.onTy_lc hs2 (hf.lc hctx).1)
        (.arrow (ha.lc haCtx).1 .fvar)
      have hfTyped := TypeOfHM.onSubst (s2 ++ s3)
        (fun pair hp => (List.mem_append.mp hp).elim (hs2 pair) (hs3 pair)) (ihf hctx)
      have haTyped := TypeOfHM.onSubst s3 hs3 (iha haCtx)
      have heq : (s2 ++ s3).onTy fTy =
          .arrow (s3.onTy argTy) (s3.onTy (.fvar second)) := by
        simpa only [Unifies, Subst.onTy_append, Subst.onTy_arrow] using hu.unifies.unifies
      rw [heq] at hfTyped
      simp only [Subst.onCtx_append] at hfTyped
      simpa only [Subst.onCtx_append] using TypeOfHM.app hfTyped haTyped
  | @letIn K frontier ctx rhs first s1 rhsOut rhsTy ann checked sCheck body next s2 bodyOut bodyTy
      hr hc hb ihr ihb =>
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
      have rhsTyped := TypeOfHM.onSubst sCheck hsCheck (ihr hctx)
      have rhsGeneral := TypeOfHM.generaliseAnnotated
        (names := genVars K (sCheck.onCtx (s1.onCtx ctx)).env (sCheck.onTy rhsTy))
        rhsTyped genVars_nodup
        (fun name hn => genVars_not_mem hn)
      obtain ⟨avoid, rhsFinal⟩ := GeneralisesTo.onSubst_annotated
        (genScheme_wf checkedTyLC) rhsGeneral s2 hs2
      have bodyTyped := ihb bodyCtxWF
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

/-- Elaboration changes type annotations and their binders, preserving the
erased expression exactly. -/
theorem _root_.Infer.erase (h : Infer K frontier ctx input next subst output ty) :
    output.erase = input.erase := by
  induction h with
  | backend hemb _ _ _ _ => exact Input.toCore_erase _ hemb
  | lambda _ _ ih => simpa only [lambdaOutput, Expr.erase, Input.erase] using congrArg (Expr.lambda none) ih
  | app _ _ _ ihf ihx =>
      simp only [Expr.erase, Expr.erase_substTyFvars, Input.erase, ihf, ihx]
  | letIn _ _ _ ihr ihb =>
      simp only [letOutput, Expr.erase, Expr.erase_substTyFvars,
        Expr.erase_closeTyVars, Input.erase, ihr, ihb]

theorem _root_.Infer.sound (h : Infer K frontier ctx input next subst output ty) (hctx : CtxWF ctx) :
    RuntimeTyping.RunWT (subst.onCtx ctx) input.erase ty := by
  rw [← h.erase]
  exact (h.sourceSound hctx).erase_preserves_typing

/-- Fixed annotation syntax is protected throughout local filling, substitution,
and the synthesis of enclosing scheme binders. -/
theorem _root_.Infer.completes (h : Infer K frontier ctx input next subst output ty) :
    Completes K input output := by
  induction h with
  | backend hemb _ _ _ hrigid => exact .complete hemb hrigid
  | lambda hs hb ih =>
      refine .lambda ?_ hs.rigid ih
      intro template heq
      exact (hs.fits template heq).onSubst (hs.rigid template heq) hb.dom_avoids
  | app hf ha hu ihf iha =>
      exact .app (.specialise ihf (fun pair hp =>
        (List.mem_append.mp hp).elim (ha.dom_avoids pair) (hu.dom_avoids pair)))
        (.specialise iha hu.dom_avoids)
  | letIn hr hc hb ihr ihb =>
      exact .letIn hc.fits hc.rigid (.specialise ihr hc.dom_avoids) ihb
        (fun _ hn => genVars_not_mem_rigid hn) hb.dom_avoids

/-- Successful inference also satisfies the independent partial-input rules.
This connects input admissibility and completed-output typing at the same type. -/
theorem _root_.Infer.inputSound (h : Infer K frontier ctx input next subst output ty) :
    CtxWF ctx → Typing K (subst.onCtx ctx) input ty := by
  induction h with
  | backend hemb h hbelow hK hrigid =>
      intro hctx
      exact .complete hemb hrigid (h.sourceSound hctx hbelow hK hrigid)
  | @lambda K frontier ann param initial ctx body next subst completed bodyTy hs hb ih =>
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
          PolyTy.mkTrivial] using ih hbodyCtx
  | @app K frontier ctx f first s1 fOut fTy arg second s2 argOut argTy s3 hf ha hu ihf iha =>
      intro hctx
      have hs1 := (hf.lc hctx).2
      have haCtx := Subst.onCtx_wf hs1 hctx
      have hs2 := (ha.lc haCtx).2
      have hs3 := hu.unifies.lc (Subst.onTy_lc hs2 (hf.lc hctx).1)
        (.arrow (ha.lc haCtx).1 .fvar)
      have hfTyped := (ihf hctx).onSubst (s2 ++ s3)
        (fun pair hp => (List.mem_append.mp hp).elim (hs2 pair) (hs3 pair))
        (fun pair hp => (List.mem_append.mp hp).elim (ha.dom_avoids pair) (hu.dom_avoids pair))
      have haTyped := (iha haCtx).onSubst s3 hs3 hu.dom_avoids
      have heq : (s2 ++ s3).onTy fTy =
          .arrow (s3.onTy argTy) (s3.onTy (.fvar second)) := by
        simpa only [Unifies, Subst.onTy_append, Subst.onTy_arrow] using hu.unifies.unifies
      rw [heq] at hfTyped
      simp only [Subst.onCtx_append] at hfTyped
      simpa only [Subst.onCtx_append] using Typing.app hfTyped haTyped
  | @letIn K frontier ctx rhs first s1 rhsOut rhsTy ann checked sCheck body next s2 bodyOut bodyTy
      hr hc hb ihr ihb =>
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
      have rhsTyped := (ihr hctx).onSubst sCheck hsCheck hc.dom_avoids
      have rhsGeneral := rhsTyped.generalise
        (names := genVars K (sCheck.onCtx (s1.onCtx ctx)).env (sCheck.onTy rhsTy))
        hc.fits hc.rigid genVars_nodup (fun _ hn => genVars_not_mem hn)
        (fun _ hn => genVars_not_mem_rigid hn)
      obtain ⟨avoid, hfits, hgeneral⟩ := Typing.binding_onSubst
        (scheme := genScheme K (sCheck.onCtx (s1.onCtx ctx)).env (sCheck.onTy rhsTy))
        (fun fresh hf => (rhsGeneral fresh hf).1)
        (fun fresh hf => (rhsGeneral fresh hf).2) hc.rigid s2 hs2 hb.dom_avoids
      have bodyTyped := ihb bodyCtxWF
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

private theorem ctxBelow_of_all {ctx : Ctx} {frontier : Nat}
    (h : ctx.env.freeVars.all (fun v => decide (v < frontier)) = true) : CtxBelow frontier ctx := by
  intro scheme hscheme
  apply Ty.BelowFvars.of_freeVars_lt
  intro v hv
  exact of_decide_eq_true (List.all_eq_true.mp h v (Env.mem_freeVars_iff.mpr ⟨scheme, hscheme, hv⟩))

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
          | _ => none
    else none
  else none
termination_by sizeOf input

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
