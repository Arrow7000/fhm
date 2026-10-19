import FHM.Anonymous
import FHM.AnonymousClose

/-! The first anonymous-hole elaborator reuses existing inference for a WHOLE
completed subtree. It adds only the lambda/application/ordinary-let spine around
partial annotations; it does not implement another branch or SCC inferer.
-/

namespace Anonymous

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

def lambdaOutput (ann : Option Template) (param : Ty) (subst : Subst) (body : Expr) : Expr :=
  .lambda (ann.map fun _ => subst.onTy param) body

def letOutput (scheme : PolyTy) (names : List Nat) (rhs body : Expr) (subst : Subst) : Expr :=
  .letIn (some (subst.onPolyTy scheme)) ((rhs.closeTyVars names).substTyFvars subst) body

/-- Authoritative input/output judgment for the proved anonymous fragment.
The `backend` rule uses the existing judgment only after a whole subtree embeds
as completed Core. Partial annotation modes never use that rule. -/
inductive Infer : List Nat → Nat → Ctx → Input → Nat → Subst → Expr → Ty → Prop
  | backend :
      input.toCore = some core →
      _root_.Infer K frontier ctx core next subst ty →
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
      (rhsOut.substTyFvars sCheck).TyBvarBounded 0 →
      Infer K checked
        { (sCheck.onCtx (s1.onCtx ctx)) with
          env := genScheme K (sCheck.onCtx (s1.onCtx ctx)).env (sCheck.onTy rhsTy) ::
            (sCheck.onCtx (s1.onCtx ctx)).env }
        body next s2 bodyOut bodyTy →
      Infer K frontier ctx (.letIn ann rhs body) next (s1 ++ sCheck ++ s2)
        (letOutput (genScheme K (sCheck.onCtx (s1.onCtx ctx)).env (sCheck.onTy rhsTy))
          (genVars K (sCheck.onCtx (s1.onCtx ctx)).env (sCheck.onTy rhsTy))
          (rhsOut.substTyFvars sCheck) bodyOut s2) bodyTy

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

theorem Infer.dom_avoids (h : Infer K frontier ctx input next subst output ty) :
    ∀ pair ∈ subst, pair.1 ∉ K := by
  induction h with
  | backend _ h _ _ _ => exact h.dom_avoids
  | lambda _ _ ih => exact ih
  | app _ _ hu ihf ihx =>
      intro pair hp
      rcases List.mem_append.mp hp with hp | hp
      · exact (List.mem_append.mp hp).elim (ihf pair) (ihx pair)
      · exact hu.dom_avoids pair hp
  | letIn _ hc _ _ ihr ihb =>
      intro pair hp
      rcases List.mem_append.mp hp with hp | hp
      · exact (List.mem_append.mp hp).elim (ihr pair) (hc.dom_avoids pair)
      · exact ihb pair hp

theorem Infer.lc (h : Infer K frontier ctx input next subst output ty) :
    CtxWF ctx → ty.IsLC ∧ ∀ pair ∈ subst, pair.2.IsLC := by
  induction h with
  | backend _ h _ _ _ => exact h.lc
  | @lambda K frontier ann param initial ctx body next subst completed bodyTy hs hb ih =>
      intro hctx
      have hbodyCtx : CtxWF { ctx with env := PolyTy.mkTrivial param :: ctx.env } := by
        intro scheme hscheme
        rcases List.mem_cons.mp hscheme with rfl | hscheme
        · exact hs.lc
        · exact hctx scheme hscheme
      obtain ⟨ht, hsubst⟩ := ih hbodyCtx
      exact ⟨.arrow (Subst.onTy_lc hsubst hs.lc) ht, hsubst⟩
  | app hf hx hu ihf ihx =>
      intro hctx
      obtain ⟨hfTy, hs1⟩ := ihf hctx
      obtain ⟨hxTy, hs2⟩ := ihx (Subst.onCtx_wf hs1 hctx)
      have hs3 := hu.unifies.lc (Subst.onTy_lc hs2 hfTy) (.arrow hxTy .fvar)
      refine ⟨Subst.onTy_lc hs3 .fvar, ?_⟩
      intro pair hp
      rcases List.mem_append.mp hp with hp | hp
      · exact (List.mem_append.mp hp).elim (hs1 pair) (hs2 pair)
      · exact hs3 pair hp
  | letIn hr hc _ hb ihr ihb =>
      intro hctx
      obtain ⟨hrTy, hs1⟩ := ihr hctx
      have hcheck := hc.lc hrTy
      obtain ⟨hbTy, hs2⟩ := ihb (by
        intro scheme hscheme
        rcases List.mem_cons.mp hscheme with rfl | hscheme
        · exact genScheme_wf (Subst.onTy_lc hcheck hrTy)
        · exact Subst.onCtx_wf hcheck (Subst.onCtx_wf hs1 hctx) scheme hscheme)
      refine ⟨hbTy, ?_⟩
      intro pair hp
      rcases List.mem_append.mp hp with hp | hp
      · exact (List.mem_append.mp hp).elim (hs1 pair) (hcheck pair)
      · exact hs2 pair hp

/-- Successful elaboration produces ordinary annotated Core typing. The proof
constructs the typing from the inference derivation; it does not recheck output
with the Core inferer. -/
theorem Infer.sourceSound (h : Infer K frontier ctx input next subst output ty) :
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
      hr hc hscope hb ihr ihb =>
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
        rhsTyped hscope genVars_nodup
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
theorem Infer.erase (h : Infer K frontier ctx input next subst output ty) :
    output.erase = input.erase := by
  induction h with
  | backend hemb _ _ _ _ => exact Input.toCore_erase _ hemb
  | lambda _ _ ih => simpa only [lambdaOutput, Expr.erase, Input.erase] using congrArg (Expr.lambda none) ih
  | app _ _ _ ihf ihx =>
      simp only [Expr.erase, Expr.erase_substTyFvars, Input.erase, ihf, ihx]
  | letIn _ _ hscope _ ihr ihb =>
      simp only [letOutput, Expr.erase, Expr.erase_substTyFvars,
        Expr.erase_closeTyVars hscope genVars_nodup, Input.erase, ihr, ihb]

theorem Infer.sound (h : Infer K frontier ctx input next subst output ty) (hctx : CtxWF ctx) :
    RuntimeTyping.RunWT (subst.onCtx ctx) input.erase ty := by
  rw [← h.erase]
  exact (h.sourceSound hctx).erase_preserves_typing

/-- Fixed annotation syntax is protected throughout local filling, substitution,
and the synthesis of enclosing scheme binders. -/
theorem Infer.completes (h : Infer K frontier ctx input next subst output ty) :
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
  | letIn hr hc _ hb ihr ihb =>
      exact .letIn hc.fits hc.rigid (.specialise ihr hc.dom_avoids) ihb
        (fun _ hn => genVars_not_mem_rigid hn) hb.dom_avoids

/-- Successful inference also satisfies the independent partial-input rules.
This connects input admissibility and completed-output typing at the same type. -/
theorem Infer.inputSound (h : Infer K frontier ctx input next subst output ty) :
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
      hr hc _ hb ihr ihb =>
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

/-- The syntactic RHS scope guard always passes on a successfully inferred RHS
in a valid context, including after the annotation-checking substitution. -/
theorem Infer.scoped_afterSubst (h : Infer K frontier ctx input next subst output ty)
    (hctx : CtxWF ctx) (specialise : Subst) (hlc : ∀ pair ∈ specialise, pair.2.IsLC) :
    (output.substTyFvars specialise).scopedAnnotations 0 = true :=
  Expr.scopedAnnotations_complete _ 0
    (TypeOfHM.onSubst specialise hlc (h.sourceSound hctx)).tyBvarBounded

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
def inferCore (K : List Nat) (frontier : Nat) (ctx : Ctx) (input : Input) :
    Option { result : Nat × Subst × Expr × Ty //
      Infer K frontier ctx input result.1 result.2.1 result.2.2.1 result.2.2.2 } :=
  if hK : K.all (fun v => decide (v < frontier)) = true then
    if hctx : ctx.env.freeVars.all (fun v => decide (v < frontier)) = true then
      match hemb : input.toCore with
      | some core =>
          if hrigid : core.tyFreeVars.all (fun v => decide (v ∈ K)) = true then
            match _root_.inferCore K frontier ctx core with
            | none => none
            | some ⟨(next, subst, ty), h⟩ =>
                some ⟨(next, subst, core, ty), .backend hemb h (ctxBelow_of_all hctx)
                  (fun v hv => of_decide_eq_true (List.all_eq_true.mp hK v hv))
                  (fun v hv => of_decide_eq_true (List.all_eq_true.mp hrigid v hv))⟩
          else none
      | none =>
          match input with
          | .lambda ann body =>
              match seed K frontier ann with
              | none => none
              | some ⟨(initial, param), hs⟩ =>
                  match inferCore K initial { ctx with env := PolyTy.mkTrivial param :: ctx.env } body with
                  | none => none
                  | some ⟨(next, subst, completed, bodyTy), hb⟩ =>
                      some ⟨(next, subst, lambdaOutput ann param subst completed,
                        .arrow (subst.onTy param) bodyTy), .lambda hs hb⟩
          | .app f arg =>
              match inferCore K frontier ctx f with
              | none => none
              | some ⟨(first, s1, fOut, fTy), hf⟩ =>
                  match inferCore K first (s1.onCtx ctx) arg with
                  | none => none
                  | some ⟨(second, s2, argOut, argTy), ha⟩ =>
                      match unifyCoreK K (s2.onTy fTy) (.arrow argTy (.fvar second)) with
                      | none => none
                      | some ⟨s3, hu, hd⟩ =>
                          some ⟨(second + 1, s1 ++ s2 ++ s3,
                            .app (fOut.substTyFvars (s2 ++ s3)) (argOut.substTyFvars s3),
                            s3.onTy (.fvar second)), .app hf ha ⟨hu, hd⟩⟩
          | .letIn ann rhs body =>
              match inferCore K frontier ctx rhs with
              | none => none
              | some ⟨(first, s1, rhsOut, rhsTy), hr⟩ =>
                  match checkLet K first ann rhsTy with
                  | none => none
                  | some ⟨(checked, sCheck), hc⟩ =>
                      let checkedCtx := sCheck.onCtx (s1.onCtx ctx)
                      let checkedTy := sCheck.onTy rhsTy
                      let checkedOut := rhsOut.substTyFvars sCheck
                      let scheme := genScheme K checkedCtx.env checkedTy
                      let names := genVars K checkedCtx.env checkedTy
                      if hscope : checkedOut.scopedAnnotations 0 = true then
                        match inferCore K checked { checkedCtx with env := scheme :: checkedCtx.env } body with
                        | none => none
                        | some ⟨(next, s2, bodyOut, bodyTy), hb⟩ =>
                            some ⟨(next, s1 ++ sCheck ++ s2,
                              letOutput scheme names checkedOut bodyOut s2, bodyTy),
                              .letIn hr hc (checkedOut.scopedAnnotations_sound 0 hscope) hb⟩
                      else none
          | _ => none
    else none
  else none
termination_by sizeOf input

end Anonymous
