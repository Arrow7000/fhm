import EPL.Properties.RuntimeSchemes

namespace EPL
namespace RuntimeTyping

private theorem scoped_monoRigids
    {ty : Ty} {rigidCount binderCount larger : Nat}
    (hScoped : ty.Scoped rigidCount binderCount)
    (hscope : rigidCount ≤ larger) :
    ty.Scoped larger binderCount := by
  induction hScoped with
  | prim => exact .prim
  | arrow _ _ domainIH codomainIH => exact .arrow domainIH codomainIH
  | bvar hindex => exact .bvar hindex
  | rigid hlevel => exact .rigid (hlevel.trans_le hscope)
  | mvar id => exact .mvar id

private theorem wf_monoRigids
    {ty : Ty} {rigidCount binderCount larger : Nat}
    (wf : ty.WF rigidCount binderCount)
    (hscope : rigidCount ≤ larger) :
    ty.WF larger binderCount :=
  ⟨scoped_monoRigids wf.1 hscope, wf.2⟩

private theorem schemeWF_monoRigids
    {scheme : PolyTy} {rigidCount larger : Nat}
    (wf : scheme.WF rigidCount)
    (hscope : rigidCount ≤ larger) :
    scheme.WF larger :=
  wf_monoRigids wf hscope

private theorem ctxWF_monoRigids
    {ctx : Ctx} {rigidCount larger : Nat}
    (wf : ctx.WF rigidCount)
    (hscope : rigidCount ≤ larger) :
    ctx.WF larger := by
  intro scheme hmem
  exact schemeWF_monoRigids (wf scheme hmem) hscope

private theorem ctxWF_cons
    {head : PolyTy} {tail : Ctx} {rigidCount : Nat}
    (headWF : head.WF rigidCount)
    (tailWF : Ctx.WF rigidCount tail) :
    Ctx.WF rigidCount (head :: tail) := by
  intro scheme hmem
  rcases List.mem_cons.mp hmem with rfl | htail
  · exact headWF
  · exact tailWF scheme htail

private theorem ctxWF_remove_middle
    {pre post : Ctx} {removed : PolyTy} {rigidCount : Nat}
    (wf : (pre ++ [removed] ++ post : Ctx).WF rigidCount) :
    (pre ++ post : Ctx).WF rigidCount := by
  intro scheme hmem
  apply wf scheme
  simp only [List.mem_append, List.mem_singleton] at hmem ⊢
  tauto

private theorem shiftFrom_zero (expr : Expr T) :
    expr.shiftFrom threshold 0 = expr := by
  induction expr generalizing threshold with
  | primLit => rfl
  | primOp => rfl
  | var index => simp [Expr.shiftFrom]
  | lambda ann body ih => simp [Expr.shiftFrom, ih]
  | app function argument ihFunction ihArgument =>
      simp [Expr.shiftFrom, ihFunction, ihArgument]
  | letIn ann rhs body ihRhs ihBody =>
      simp [Expr.shiftFrom, ihRhs, ihBody]
  | fix ann body ih => simp [Expr.shiftFrom, ih]

private theorem shiftFrom_add_zero (expr : Expr T) :
    (expr.shiftFrom threshold first).shiftFrom threshold second =
      expr.shiftFrom threshold (first + second) := by
  induction expr generalizing threshold with
  | primLit => rfl
  | primOp => rfl
  | var index =>
      by_cases h : threshold ≤ index
      · simp [Expr.shiftFrom, h, h.trans (Nat.le_add_right _ _), Nat.add_assoc]
      · simp [Expr.shiftFrom, h]
  | lambda ann body ih => simp [Expr.shiftFrom, ih]
  | app function argument ihFunction ihArgument =>
      simp [Expr.shiftFrom, ihFunction, ihArgument]
  | letIn ann rhs body ihRhs ihBody =>
      simp [Expr.shiftFrom, ihRhs, ihBody]
  | fix ann body ih => simp [Expr.shiftFrom, ih]

private theorem hasScheme_weakenPrefix
    {rigidCount : Nat} {ctx pre : Ctx} {replacement : RuntimeExpr}
    {scheme : PolyTy}
    (typing : RuntimeHasScheme rigidCount ctx replacement scheme)
    (preWF : pre.WF rigidCount) :
    RuntimeHasScheme rigidCount (pre ++ ctx)
      (replacement.shiftFrom 0 pre.length) scheme := by
  refine ⟨typing.schemeWF, ?_⟩
  intro larger hscope args hlen hargs
  have baseTyping := typing.typed larger hscope args hlen hargs
  induction pre with
  | nil =>
      simpa only [List.nil_append, List.length_nil,
        shiftFrom_zero] using baseTyping
  | cons head tail tailIH =>
      have headWF : head.WF rigidCount := preWF head (by simp)
      have tailWF : Ctx.WF rigidCount tail := by
        intro item hitem
        exact preWF item (by simp [hitem])
      have weakenedTail := tailIH tailWF
      have weakened := RuntimeTyping.weakenHead weakenedTail
        (schemeWF_monoRigids headWF hscope)
      simpa only [List.cons_append, List.length_cons,
        shiftFrom_add_zero, Nat.add_comm] using weakened

private theorem substAt
    (bodyTyping : RuntimeTyping rigidCount env body ty) :
    ∀ (pre ctx : Ctx) (target : PolyTy) (replacement : RuntimeExpr),
      env = pre ++ [target] ++ ctx →
      pre.WF rigidCount →
      RuntimeHasScheme rigidCount ctx replacement target →
      RuntimeTyping rigidCount (pre ++ ctx)
        (body.substN pre.length [replacement]) ty := by
  induction bodyTyping with
  | primLit =>
      intro pre ctx target replacement _ _ _
      exact .primLit
  | primOp =>
      intro pre ctx target replacement _ _ _
      exact .primOp
  | var lookup schemeWF lengthEq argsWF =>
      expose_names
      intro pre ctx target replacement envEq preWF replacementTyping
      rw [envEq, List.append_assoc] at lookup
      simp only [Expr.substN]
      by_cases hlt : index < pre.length
      · rw [if_pos hlt]
        apply RuntimeTyping.var (scheme := scheme) (args := args)
        · rw [List.getElem?_append_left hlt]
          rwa [List.getElem?_append_left hlt] at lookup
        · exact schemeWF
        · exact lengthEq
        · exact argsWF
      · rw [if_neg hlt]
        by_cases hselected : index - pre.length < [replacement].length
        · rw [dif_pos hselected]
          simp only [List.length_cons, List.length_nil, Nat.zero_add] at hselected
          have hzero : index - pre.length = 0 := by omega
          have lookup' := lookup
          rw [List.getElem?_append_right (by omega)] at lookup'
          simp only [hzero] at lookup'
          have schemeEq : scheme = target := (Option.some.inj lookup').symm
          subst scheme
          have replacementAtPrefix := hasScheme_weakenPrefix replacementTyping preWF
          have typed : RuntimeTyping rigidCount_1 (pre ++ ctx)
              (replacement.shiftFrom 0 pre.length) (target.openWith args) :=
            replacementAtPrefix.typed rigidCount_1 (le_refl rigidCount_1)
              args lengthEq argsWF
          simpa using typed
        · rw [dif_neg hselected]
          have hpre : pre.length ≤ index := Nat.le_of_not_gt hlt
          have hone : [target].length ≤ index - pre.length := by
            simpa using (Nat.le_of_not_gt hselected)
          have hindices :
              index - [replacement].length - pre.length =
                index - pre.length - [target].length := by
            simp only [List.length_cons, List.length_nil, Nat.zero_add]
            omega
          apply RuntimeTyping.var (scheme := scheme) (args := args)
          · rw [List.getElem?_append_right
              (by omega : pre.length ≤ index - [replacement].length)]
            rw [List.getElem?_append_right hpre,
              List.getElem?_append_right hone] at lookup
            rw [hindices]
            exact lookup
          · exact schemeWF
          · exact lengthEq
          · exact argsWF
  | lambda paramWF _ bodyIH =>
      expose_names
      intro pre ctx target replacement envEq preWF replacementTyping
      simp only [Expr.substN]
      apply RuntimeTyping.lambda paramWF
      have substituted := bodyIH (PolyTy.mono paramTy :: pre) ctx target replacement
        (by simp [envEq, List.append_assoc])
        (ctxWF_cons ⟨paramWF.1, paramWF.2⟩ preWF) replacementTyping
      simpa only [List.cons_append, List.length_cons] using substituted
  | app _ _ functionIH argumentIH =>
      intro pre ctx target replacement envEq preWF replacementTyping
      exact .app (functionIH pre ctx target replacement envEq preWF replacementTyping)
        (argumentIH pre ctx target replacement envEq preWF replacementTyping)
  | letMono rhsWF _ _ rhsIH bodyIH =>
      expose_names
      intro pre ctx target replacement envEq preWF replacementTyping
      simp only [Expr.substN]
      apply RuntimeTyping.letMono rhsWF
      · exact rhsIH pre ctx target replacement envEq preWF replacementTyping
      · have substituted := bodyIH (PolyTy.mono rhsTy :: pre) ctx target replacement
          (by simp [envEq, List.append_assoc])
          (ctxWF_cons ⟨rhsWF.1, rhsWF.2⟩ preWF) replacementTyping
        simpa only [List.cons_append, List.length_cons] using substituted
  | letPoly schemeWF localCtxWF _ _ rhsIH bodyIH =>
      expose_names
      intro pre ctx target replacement envEq preWF replacementTyping
      simp only [Expr.substN]
      rw [envEq] at localCtxWF
      apply RuntimeTyping.letPoly (scheme := scheme) schemeWF
      · exact ctxWF_remove_middle localCtxWF
      · exact rhsIH pre ctx target replacement envEq
          (ctxWF_monoRigids preWF (Nat.le_add_right _ _))
          ⟨schemeWF_monoRigids replacementTyping.schemeWF (Nat.le_add_right _ _),
            fun larger hscope => replacementTyping.typed larger
              ((Nat.le_add_right _ _).trans hscope)⟩
      · have substituted := bodyIH (scheme :: pre) ctx target replacement
          (by simp [envEq, List.append_assoc])
          (ctxWF_cons schemeWF preWF) replacementTyping
        simpa only [List.cons_append, List.length_cons] using substituted
  | fix selfWF _ bodyIH =>
      expose_names
      intro pre ctx target replacement envEq preWF replacementTyping
      simp only [Expr.substN]
      apply RuntimeTyping.fix selfWF
      have substituted := bodyIH (PolyTy.mono selfTy :: pre) ctx target replacement
        (by simp [envEq, List.append_assoc])
        (ctxWF_cons ⟨selfWF.1, selfWF.2⟩ preWF) replacementTyping
      simpa only [List.cons_append, List.length_cons] using substituted

/-- Replacing the head variable by an expression inhabiting its whole scheme
preserves runtime typing. This is the common substitution principle for beta,
monomorphic lets, explicit-polymorphic lets, and fixed-point unfolding. -/
theorem substScheme
    (replacementTyping : RuntimeHasScheme rigidCount ctx replacement scheme)
    (bodyTyping : RuntimeTyping rigidCount (scheme :: ctx) body ty) :
    RuntimeTyping rigidCount ctx (body.subst1 replacement) ty := by
  simpa [Expr.subst1] using
    substAt bodyTyping [] ctx scheme replacement (by simp) (by simp [Ctx.WF])
      replacementTyping

end RuntimeTyping
end EPL
