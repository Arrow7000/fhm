import EPL.RuntimeTyping

namespace EPL
namespace RuntimeTyping

private theorem scoped_weakenRigids
    {ty : Ty}
    (hScoped : ty.Scoped rigidCount binderCount)
    (hscope : rigidCount ≤ larger) :
    ty.Scoped larger binderCount := by
  induction hScoped with
  | prim => exact .prim
  | arrow _ _ domainIH codomainIH => exact .arrow domainIH codomainIH
  | bvar hindex => exact .bvar hindex
  | rigid hlevel => exact .rigid (hlevel.trans_le hscope)
  | mvar id => exact .mvar id

private theorem schemeWF_weakenRigids
    {scheme : PolyTy}
    (wf : scheme.WF rigidCount)
    (hscope : rigidCount ≤ larger) :
    scheme.WF larger :=
  ⟨scoped_weakenRigids wf.1 hscope, wf.2⟩

private theorem ctxWF_insert
    {pre post : Ctx} {inserted : PolyTy}
    (wf : (pre ++ post : Ctx).WF rigidCount)
    (insertedWF : inserted.WF rigidCount) :
    (pre ++ inserted :: post : Ctx).WF rigidCount := by
  intro scheme hmem
  rcases List.mem_append.mp hmem with hpre | htail
  · exact wf scheme (List.mem_append_left post hpre)
  · rcases List.mem_cons.mp htail with rfl | hsuffix
    · exact insertedWF
    · exact wf scheme (List.mem_append_right pre hsuffix)

private theorem weakenAt
    (typing : RuntimeTyping rigidCount env expr ty) :
    ∀ (pre post : Ctx), env = pre ++ post →
      inserted.WF rigidCount →
      RuntimeTyping rigidCount (pre ++ inserted :: post)
        (expr.shiftFrom pre.length 1) ty := by
  induction typing with
  | primLit =>
      intro pre post _ _
      exact .primLit
  | primOp =>
      intro pre post _ _
      exact .primOp
  | var lookup schemeWF lengthEq argsWF =>
      expose_names
      intro pre post envEq insertedWF
      rw [envEq] at lookup
      by_cases hindex : index < pre.length
      · simp only [Expr.shiftFrom, if_neg (Nat.not_le.mpr hindex)]
        apply RuntimeTyping.var (scheme := scheme) (args := args)
        · rw [List.getElem?_append_left hindex]
          rwa [List.getElem?_append_left hindex] at lookup
        · exact schemeWF
        · exact lengthEq
        · exact argsWF
      · have hle : pre.length ≤ index := Nat.le_of_not_gt hindex
        simp only [Expr.shiftFrom, if_pos hle]
        apply RuntimeTyping.var (scheme := scheme) (args := args)
        · rw [List.getElem?_append_right hle] at lookup
          rw [List.getElem?_append_right (by omega : pre.length ≤ index + 1)]
          have hsub : index + 1 - pre.length = (index - pre.length) + 1 := by omega
          rw [hsub, List.getElem?_cons_succ]
          exact lookup
        · exact schemeWF
        · exact lengthEq
        · exact argsWF
  | lambda paramWF _ bodyIH =>
      expose_names
      intro pre post envEq insertedWF
      simp only [Expr.shiftFrom]
      apply RuntimeTyping.lambda paramWF
      have shifted := bodyIH (PolyTy.mono paramTy :: pre) post
        (by simp [envEq]) insertedWF
      simpa only [List.cons_append, List.length_cons] using shifted
  | app _ _ functionIH argumentIH =>
      intro pre post envEq insertedWF
      exact .app (functionIH pre post envEq insertedWF)
        (argumentIH pre post envEq insertedWF)
  | letMono rhsWF _ _ rhsIH bodyIH =>
      expose_names
      intro pre post envEq insertedWF
      simp only [Expr.shiftFrom]
      apply RuntimeTyping.letMono rhsWF
      · exact rhsIH pre post envEq insertedWF
      · have shifted := bodyIH (PolyTy.mono rhsTy :: pre) post
          (by simp [envEq]) insertedWF
        simpa only [List.cons_append, List.length_cons] using shifted
  | letPoly schemeWF ctxWF _ _ rhsIH bodyIH =>
      expose_names
      intro pre post envEq insertedWF
      simp only [Expr.shiftFrom]
      apply RuntimeTyping.letPoly (scheme := scheme) schemeWF
      · rw [envEq] at ctxWF
        exact ctxWF_insert ctxWF insertedWF
      · exact rhsIH pre post envEq
          (schemeWF_weakenRigids insertedWF (Nat.le_add_right _ _))
      · have shifted := bodyIH (scheme :: pre) post
          (by simp [envEq]) insertedWF
        simpa only [List.cons_append, List.length_cons] using shifted
  | fix selfWF _ bodyIH =>
      expose_names
      intro pre post envEq insertedWF
      simp only [Expr.shiftFrom]
      apply RuntimeTyping.fix selfWF
      have shifted := bodyIH (PolyTy.mono selfTy :: pre) post
        (by simp [envEq]) insertedWF
      simpa only [List.cons_append, List.length_cons] using shifted

/-- Inserting a well-formed scheme at the head of the term context preserves
typing after shifting all free term indices by one. -/
theorem weakenHead
    (typing : RuntimeTyping rigidCount ctx expr ty)
    (insertedWF : inserted.WF rigidCount) :
    RuntimeTyping rigidCount (inserted :: ctx) (expr.shiftFrom 0 1) ty := by
  simpa using weakenAt typing [] ctx rfl insertedWF

end RuntimeTyping
end EPL
