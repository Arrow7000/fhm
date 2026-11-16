import EPL2.Spec.Syntax
import EPL2.Spec.Runtime

/-!
# Declarative metatheory

Everything here is proved once for `TypingWith sig Det`, generically in the
let condition `Det`, so it holds for both `Typing` and `Elaborates`.
-/

namespace EPL2

theorem PrimLit.ty_wf (literal : PrimLit) : (literal.ty : Ty V).WF k := by
  cases literal <;> simp [PrimLit.ty, Ty.WF, Ty.Scoped]

theorem PrimOp.ty_wf {op : PrimOp} {ty : Ty V} (typed : op.ty sig = some ty) : ty.WF k := by
  cases op with
  | intAdd =>
      simp only [PrimOp.ty, Option.some.injEq] at typed
      subst typed
      simp [Ty.WF, Ty.Scoped]
  | intSub =>
      simp only [PrimOp.ty, Option.some.injEq] at typed
      subst typed
      simp [Ty.WF, Ty.Scoped]
  | intLt =>
      by_cases hb : sig.HasBool
      · simp only [PrimOp.ty, if_pos hb, Option.some.injEq] at typed
        subst typed
        simp [Ty.WF, Ty.Scoped, Ty.bool]
      · simp [PrimOp.ty, if_neg hb] at typed
  | charLt =>
      by_cases hb : sig.HasBool
      · simp only [PrimOp.ty, if_pos hb, Option.some.injEq] at typed
        subst typed
        simp [Ty.WF, Ty.Scoped, Ty.bool]
      · simp [PrimOp.ty, if_neg hb] at typed

theorem PrimOp.ty_lift {op : PrimOp} {ty : SemTy} (typed : op.ty sig = some ty) :
    op.ty sig = some (ty.lift : Ty V) := by
  cases op with
  | intAdd =>
      simp only [PrimOp.ty, Option.some.injEq] at typed
      subst typed
      rfl
  | intSub =>
      simp only [PrimOp.ty, Option.some.injEq] at typed
      subst typed
      rfl
  | intLt =>
      by_cases hb : sig.HasBool
      · simp only [PrimOp.ty, if_pos hb, Option.some.injEq] at typed
        subst typed
        simp only [PrimOp.ty, if_pos hb]
        rfl
      · simp [PrimOp.ty, if_neg hb] at typed
  | charLt =>
      by_cases hb : sig.HasBool
      · simp only [PrimOp.ty, if_pos hb, Option.some.injEq] at typed
        subst typed
        simp only [PrimOp.ty, if_pos hb]
        rfl
      · simp [PrimOp.ty, if_neg hb] at typed

/-- Primitive operator types have no variables. -/
theorem PrimOp.ty_bind {op : PrimOp} {ty : Ty V} (typed : op.ty sig = some ty) (f : V → Ty W) :
    op.ty sig = some (ty.bind f) := by
  cases op with
  | intAdd =>
      simp only [PrimOp.ty, Option.some.injEq] at typed
      subst typed
      rfl
  | intSub =>
      simp only [PrimOp.ty, Option.some.injEq] at typed
      subst typed
      rfl
  | intLt =>
      by_cases hb : sig.HasBool
      · simp only [PrimOp.ty, if_pos hb, Option.some.injEq] at typed
        subst typed
        simp only [PrimOp.ty, if_pos hb]
        rfl
      · simp [PrimOp.ty, if_neg hb] at typed
  | charLt =>
      by_cases hb : sig.HasBool
      · simp only [PrimOp.ty, if_pos hb, Option.some.injEq] at typed
        subst typed
        simp only [PrimOp.ty, if_pos hb]
        rfl
      · simp [PrimOp.ty, if_neg hb] at typed

theorem PrimLit.ty_bind (literal : PrimLit) (f : V → Ty W) :
    (literal.ty : Ty V).bind f = literal.ty := by
  cases literal <;> rfl

theorem Signature.schemeOf_wf {sig : Signature} (found : sig.schemeOf c = some scheme) : scheme.WF 0 := by
  cases c with
  | ctor type index =>
      cases hdecl : sig[type]? with
      | none => simp [Signature.schemeOf, hdecl] at found
      | some decl =>
          cases hfields : decl.ctors[index]? with
          | none => simp [Signature.schemeOf, hdecl, hfields] at found
          | some fields =>
              by_cases hwf : (decl.ctorScheme type fields).WF 0
              · have hsome : sig.schemeOf (.ctor type index) = some (decl.ctorScheme type fields) := by
                  simp [Signature.schemeOf, hdecl, hfields, hwf]
                rw [hsome] at found
                have heq : decl.ctorScheme type fields = scheme := Option.some.inj found
                rw [← heq]
                exact hwf
              · simp [Signature.schemeOf, hdecl, hfields, hwf] at found
  | elim type =>
      cases hdecl : sig[type]? with
      | none => simp [Signature.schemeOf, hdecl] at found
      | some decl =>
          by_cases hwf : (decl.elimScheme type).WF 0
          · have hsome : sig.schemeOf (.elim type) = some (decl.elimScheme type) := by
              simp [Signature.schemeOf, hdecl, hwf]
            rw [hsome] at found
            have heq : decl.elimScheme type = scheme := Option.some.inj found
            rw [← heq]
            exact hwf
          · simp [Signature.schemeOf, hdecl, hwf] at found

private theorem map_substRigids_eq_self {ctx : Ctx V} {k : Nat} (wf : ctx.WF k) {f : Nat → Ty V}
    (id : ∀ l < k, f l = .rigid l) : ctx.map (Scheme.substRigids f) = ctx := by
  induction ctx with
  | nil => rfl
  | cons s rest ih =>
      simp only [List.map_cons]
      rw [Scheme.substRigids_eq_self (wf s (by simp)) id,
        ih (fun s hs => wf s (by simp [hs]))]

private theorem blockSubst_wf {args : List (Ty V)} {n k k' : Nat}
    (hlen : args.length = n) (hargs : ∀ arg ∈ args, arg.WF k') (le : k ≤ k')
    {l : Nat} (hl : l < k + n) : (blockSubst k args l).WF k' := by
  unfold blockSubst
  by_cases hlt : l < k
  · rw [if_pos hlt]
    show l < k'
    omega
  · rw [if_neg hlt]
    have hln : l - k < args.length := by omega
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hln, Option.getD_some]
    exact hargs _ (List.getElem_mem hln)

private theorem ctxWF_cons {ctx : Ctx V} {k : Nat} (scheme : Scheme V)
    (hs : scheme.WF k) (hc : ctx.WF k) : Ctx.WF k (scheme :: ctx) := by
  intro s hmem
  rcases List.mem_cons.mp hmem with rfl | h
  · exact hs
  · exact hc s h

private theorem ctxWF_getElem {ctx : Ctx V} {k : Nat} (wf : ctx.WF k) {i : Nat}
    {scheme : Scheme V} (h : ctx[i]? = some scheme) : scheme.WF k :=
  wf scheme (List.mem_of_getElem? h)

namespace TypingWith

/-- A weaker let condition admits more derivations. -/
theorem mono {Det Det' : LetCondition}
    (weaker : ∀ k ctx ann rhs scheme, Det k ctx ann rhs scheme → Det' k ctx ann rhs scheme)
    (typing : TypingWith sig Det k ctx src elaboration ty) :
    TypingWith sig Det' k ctx src elaboration ty := by
  induction typing with
  | lit => exact .lit
  | primOp h => exact .primOp h
  | const hsch hinst => exact .const hsch hinst
  | var hlook hinst => exact .var hlook hinst
  | lambda hwf hmatch hbody ih => exact .lambda hwf hmatch ih
  | app hf ha ihf iha => exact .app ihf iha
  | letMono hrhs hbody ihrhs ihbody => exact .letMono ihrhs ihbody
  | letPoly hcomp hrhs hdet hbody ihrhs ihbody =>
      exact .letPoly hcomp ihrhs (weaker _ _ _ _ _ hdet) ihbody
  | fix hwf hmatch hbody ih => exact .fix hwf hmatch ih

/-- Types are well-formed. Proof: induction on the derivation; the `var`
and `const` cases are `Scheme.inst_wf`. -/
theorem regular (ctxWF : ctx.WF k) (typing : TypingWith sig Det k ctx src elaboration ty) :
    ty.WF k := by
  induction typing with
  | lit => exact PrimLit.ty_wf _
  | primOp h => exact PrimOp.ty_wf h
  | const hsch hinst =>
      obtain ⟨args, hlen, hargs, hEq⟩ := hinst
      rw [← hEq]
      exact Scheme.inst_wf (Signature.schemeOf_wf hsch) (Nat.zero_le _) hlen hargs
  | var hlook hinst =>
      obtain ⟨args, hlen, hargs, hEq⟩ := hinst
      rw [← hEq]
      exact Scheme.inst_wf (ctxWF_getElem ctxWF hlook) (le_refl _) hlen hargs
  | lambda hparam hmatch hbody ih =>
      expose_names
      exact ⟨hparam, ih (ctxWF_cons (Scheme.mono paramTy) hparam ctxWF)⟩
  | app hf ha ihf iha => exact (ihf ctxWF).2
  | letMono hrhs hbody ihrhs ihbody =>
      expose_names
      exact ihbody (ctxWF_cons (Scheme.mono rhsTy) (ihrhs ctxWF) ctxWF)
  | letPoly hcomp hrhs hdet hbody ihrhs ihbody =>
      expose_names
      exact ihbody (ctxWF_cons scheme hcomp.wf ctxWF)
  | fix hwf hmatch hbody ih =>
      expose_names
      exact ih (ctxWF_cons (Scheme.mono selfTy) hwf ctxWF)

/-- A source program and its elaboration erase alike. -/
theorem erase_eq (typing : TypingWith sig Det k ctx src elaboration ty) : elaboration.erase = src.erase := by
  induction typing with
  | lit => rfl
  | primOp _ => rfl
  | const _ _ => rfl
  | var _ _ => rfl
  | lambda _ _ _ ih => simp [Expr.erase, ih]
  | app _ _ ihf iha => simp [Expr.erase, ihf, iha]
  | letMono _ _ ihrhs ihbody => simp [Expr.erase, ihrhs, ihbody]
  | letPoly _ _ _ _ ihrhs ihbody => simp [Expr.erase, ihrhs, ihbody]
  | fix _ _ _ ih => simp [Expr.erase, ih]

/-- Erasure preserves typing. Proof: induction on the derivation. In the
`letPoly` case the induction hypothesis types the right-hand side at the
generic instance at depth `k + arity`; `RuntimeTyping.substRigids` with
`blockSubst k args` and `Scheme.skolemize_substRigids` give every other
instance, and `Scheme.substRigids_eq_self` shows the context is unchanged. -/
theorem erase (ctxWF : ctx.WF k) (typing : TypingWith sig Det k ctx src elaboration ty) :
    RuntimeTyping sig k ctx src.erase ty := by
  induction typing with
  | lit => exact .lit
  | primOp h => exact .primOp h
  | const hsch hinst => exact .const hsch hinst
  | var hlook hinst => exact .var hlook hinst
  | lambda hparam hmatch hbody ih =>
      expose_names
      exact .lambda hparam (ih (ctxWF_cons (Scheme.mono paramTy) hparam ctxWF))
  | app hf ha ihf iha => exact .app (ihf ctxWF) (iha ctxWF)
  | letMono hrhs hbody ihrhs ihbody =>
      expose_names
      refine RuntimeTyping.letIn (scheme := Scheme.mono rhsTy) ?_ ?_ ?_
      · exact regular ctxWF hrhs
      · intro k' hle ty hinst
        rw [Scheme.instance_mono] at hinst
        rw [hinst]
        exact RuntimeTyping.mono_depth (ihrhs ctxWF) hle
      · exact ihbody (ctxWF_cons (Scheme.mono rhsTy) (regular ctxWF hrhs) ctxWF)
  | letPoly hcomp hrhs hdet hbody ihrhs ihbody =>
      expose_names
      refine RuntimeTyping.letIn (scheme := scheme) hcomp.wf ?_
        (ihbody (ctxWF_cons scheme hcomp.wf ctxWF))
      intro k' hle ty hinst
      obtain ⟨args, hlen, hargs, hEq⟩ := hinst
      have hwfK : Ctx.WF (k_1 + scheme.arity) ctx_1 :=
        Ctx.WF.mono ctxWF (Nat.le_add_right k_1 scheme.arity)
      have hsub := RuntimeTyping.substRigids (k' := k') hwfK (ihrhs hwfK)
        (blockSubst k_1 args) (fun l hl => blockSubst_wf hlen hargs hle hl)
      have hctx : ctx_1.map (Scheme.substRigids (blockSubst k_1 args)) = ctx_1 :=
        map_substRigids_eq_self ctxWF (fun l hl => by unfold blockSubst; rw [if_pos hl])
      have htype : (scheme.skolemize k_1).substRigids (blockSubst k_1 args) = ty := by
        rw [Scheme.skolemize_substRigids hcomp.wf hlen, hEq]
      rwa [hctx, htype] at hsub
  | fix hwf hmatch hbody ih =>
      expose_names
      exact .fix hwf (ih (ctxWF_cons (Scheme.mono selfTy) hwf ctxWF))

end TypingWith

theorem Elaborates.typing (elaborates : Elaborates sig k ctx src elaboration ty) :
    Typing sig k ctx src elaboration ty :=
  TypingWith.mono (fun _ _ _ _ _ _ => trivial) elaborates

end EPL2
