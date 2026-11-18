import EPL.Spec.Syntax
import EPL.Spec.Runtime

/-!
# Declarative metatheory

Everything here is proved once for `TypingWith sig Det`, generically in the
let condition `Det`, so it holds for both `Typing` and `Elaborates`.
-/

namespace EPL

theorem PrimLit.ty_wf (literal : PrimLit) : (literal.ty : Ty V).WF k := by
  cases literal <;> trivial

theorem PrimOp.ty_wf {op : PrimOp} {ty : Ty V} (typed : op.ty sig = some ty) : ty.WF k := by
  cases op with
  | intAdd | intSub =>
      simp only [PrimOp.ty, Option.some.injEq] at typed
      subst typed
      simp [Ty.WF, Ty.Scoped]
  | intLt | charLt =>
      by_cases hb : sig.HasBool
      · simp only [PrimOp.ty, if_pos hb, Option.some.injEq] at typed
        subst typed
        simp [Ty.WF, Ty.Scoped, Ty.bool]
      · simp [PrimOp.ty, if_neg hb] at typed

/-- Primitive operator types are unchanged by a monadic bind. -/
private theorem PrimOp.ty_bind_eq {op : PrimOp} {ty : Ty V} (typed : op.ty sig = some ty)
    (f : V → Ty W) : op.ty sig = some (ty.bind f) := by
  cases op with
  | intAdd | intSub =>
      simp only [PrimOp.ty, Option.some.injEq] at typed
      subst typed
      rfl
  | intLt | charLt =>
      by_cases hb : sig.HasBool
      · simp only [PrimOp.ty, if_pos hb, Option.some.injEq] at typed
        subst typed
        simp only [PrimOp.ty, if_pos hb]
        rfl
      · simp [PrimOp.ty, if_neg hb] at typed

theorem PrimOp.ty_lift {op : PrimOp} {ty : SemTy} (typed : op.ty sig = some ty) :
    op.ty sig = some (ty.lift : Ty V) :=
  PrimOp.ty_bind_eq typed Empty.elim

/-- Primitive operator types have no variables. -/
theorem PrimOp.ty_bind {op : PrimOp} {ty : Ty V} (typed : op.ty sig = some ty) (f : V → Ty W) :
    op.ty sig = some (ty.bind f) :=
  PrimOp.ty_bind_eq typed f

theorem PrimLit.ty_bind (literal : PrimLit) (f : V → Ty W) :
    (literal.ty : Ty V).bind f = literal.ty := by
  cases literal <;> rfl

private theorem map_substRigids_eq_self {ctx : Ctx V} {k : Nat} (wf : ctx.WF k) {f : Nat → Ty V}
    (agrees : ∀ l < k, f l = .rigid l) : ctx.map (Scheme.substRigids f) = ctx := by
  induction ctx with
  | nil => rfl
  | cons scheme rest ih =>
      simp [Scheme.substRigids_eq_self (wf scheme (by simp)) agrees,
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

/-- Every instance of a well-formed scheme is well-formed. -/
private theorem Scheme.instance_wf {scheme : Scheme V} {ty : Ty V} {k k' : Nat}
    (wf : scheme.WF k) (le : k ≤ k') (inst : scheme.Instance k' ty) : ty.WF k' := by
  obtain ⟨args, hlen, hargs, hEq⟩ := inst
  rw [← hEq]
  exact Scheme.inst_wf wf le hlen hargs

/-- The codomain of a well-formed arrow type is well formed. -/
private theorem Ty.arrows_wf_codomain {domains : List (Ty V)} {codomain : Ty V} {k : Nat}
    (wf : (Ty.arrows domains codomain).WF k) : codomain.WF k := by
  induction domains with
  | nil => exact wf
  | cons domain domains ih => exact ih wf.2

/-- Branch lists with the same patterns line up by index: the elaboration has a
branch at every index where the source does, with the same pattern. -/
private theorem exists_branch_of_map_fst {A B : Type} {branches : List (CtorRef × Expr A)}
    {branchesElab : List (CtorRef × Expr B)} {i : Nat} {pattern : CtorRef} {body : Expr A}
    (aligned : branchesElab.map (·.1) = branches.map (·.1))
    (found : branches[i]? = some (pattern, body)) :
    ∃ bodyElab, branchesElab[i]? = some (pattern, bodyElab) := by
  have hpattern : (branchesElab.map (·.1))[i]? = some pattern := by
    rw [aligned, List.getElem?_map, found]
    rfl
  rw [List.getElem?_map] at hpattern
  obtain ⟨branch, hbranch, hfst⟩ := Option.map_eq_some_iff.mp hpattern
  obtain ⟨pattern', bodyElab⟩ := branch
  simp only at hfst
  rw [hfst] at hbranch
  exact ⟨bodyElab, hbranch⟩

/-- A match's result type is well formed: it is the codomain of the type of its
first branch, which is an arrow type. -/
private theorem match_result_wf {k : Nat} {ctx : Ctx Empty} {decl : DataDecl} {type : Nat}
    {args : List (Ty Empty)} {branches : List (CtorRef × Source)}
    {branchesElab : List (CtorRef × Elab)} {resultTy : Ty Empty}
    (ctxWF : ctx.WF k)
    (branchesNe : branches ≠ [])
    (patternsOk : ∀ pattern ∈ branches.map (·.1),
      pattern.type = type ∧ pattern.index < decl.ctors.length)
    (aligned : branchesElab.map (·.1) = branches.map (·.1))
    (bodies : ∀ (i : Nat) (pattern : CtorRef) (body : Source) (bodyElab : Elab)
      (fields : List SemTy),
      branches[i]? = some (pattern, body) →
      branchesElab[i]? = some (pattern, bodyElab) →
      decl.ctors[pattern.index]? = some fields →
      Ctx.WF k ctx →
      (Ty.arrows (fields.map (·.instantiate args)) resultTy).WF k) :
    resultTy.WF k := by
  obtain ⟨pattern, body, hb0⟩ : ∃ pattern body, branches[0]? = some (pattern, body) := by
    cases branches with
    | nil => exact absurd rfl branchesNe
    | cons branch rest => exact ⟨branch.1, branch.2, rfl⟩
  obtain ⟨bodyElab, hbE⟩ := exists_branch_of_map_fst aligned hb0
  have hmem : pattern ∈ branches.map (·.1) :=
    List.mem_map.mpr ⟨(pattern, body), List.mem_of_getElem? hb0, rfl⟩
  have hlen : pattern.index < decl.ctors.length := (patternsOk pattern hmem).2
  obtain ⟨fields, hfields⟩ : ∃ fields, decl.ctors[pattern.index]? = some fields :=
    ⟨decl.ctors[pattern.index]'hlen, List.getElem?_eq_getElem hlen⟩
  exact Ty.arrows_wf_codomain (bodies 0 pattern body bodyElab fields hb0 hbE hfields ctxWF)

/-- Erasing the bodies of two pattern-aligned branch lists commutes with the
alignment: branch by branch, the types agree by the indexed premise. -/
private theorem map_erase_eq_of_aligned {A B : Type} {branches : List (CtorRef × Expr A)}
    {branchesElab : List (CtorRef × Expr B)} {decl : DataDecl} {type : Nat}
    (patternsOk : ∀ pattern ∈ branches.map (·.1),
      pattern.type = type ∧ pattern.index < decl.ctors.length)
    (aligned : branchesElab.map (·.1) = branches.map (·.1))
    (bodies : ∀ (i : Nat) (pattern : CtorRef) (body : Expr A) (bodyElab : Expr B)
      (fields : List SemTy),
      branches[i]? = some (pattern, body) →
      branchesElab[i]? = some (pattern, bodyElab) →
      decl.ctors[pattern.index]? = some fields → Expr.erase bodyElab = Expr.erase body) :
    branchesElab.map (fun branch => (branch.1, Expr.erase branch.2)) =
      branches.map (fun branch => (branch.1, Expr.erase branch.2)) := by
  apply List.ext_getElem?
  intro i
  rw [List.getElem?_map, List.getElem?_map]
  cases hb : branches[i]? with
  | none =>
      have hnone : (branchesElab.map (·.1))[i]? = none := by
        rw [aligned, List.getElem?_map, hb]
        rfl
      rw [List.getElem?_map] at hnone
      cases hbE : branchesElab[i]? with
      | none => rfl
      | some branch => simp [hbE] at hnone
  | some branch =>
      obtain ⟨pattern, body⟩ := branch
      obtain ⟨bodyElab, hbE⟩ := exists_branch_of_map_fst aligned hb
      have hmem : pattern ∈ branches.map (·.1) :=
        List.mem_map.mpr ⟨(pattern, body), List.mem_of_getElem? hb, rfl⟩
      have hlen : pattern.index < decl.ctors.length := (patternsOk pattern hmem).2
      obtain ⟨fields, hfields⟩ : ∃ fields, decl.ctors[pattern.index]? = some fields :=
        ⟨decl.ctors[pattern.index]'hlen, List.getElem?_eq_getElem hlen⟩
      rw [hbE]
      show some (pattern, Expr.erase bodyElab) = some (pattern, Expr.erase body)
      rw [bodies i pattern body bodyElab fields hb hbE hfields]

namespace TypingWith

/-- A weaker let condition admits more derivations. -/
theorem mono {Det Det' : LetCondition}
    (weaker : ∀ k ctx ann rhs scheme, Det k ctx ann rhs scheme → Det' k ctx ann rhs scheme)
    (typing : TypingWith sig Det k ctx src elaboration ty) :
    TypingWith sig Det' k ctx src elaboration ty := by
  induction typing with
  | «match» scrutineeTyping declEq argsLen branchesNe patternsOk aligned branchTyping
      scrutineeIh branchIh =>
      exact .«match» scrutineeIh declEq argsLen branchesNe patternsOk aligned branchIh
  | lit => exact .lit
  | primOp h => exact .primOp h
  | ctor hsch hinst => exact .ctor hsch hinst
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
  | «match» scrutineeTyping declEq argsLen branchesNe patternsOk aligned branchTyping
      scrutineeIh branchIh =>
      exact match_result_wf ctxWF branchesNe patternsOk aligned branchIh
  | lit => exact PrimLit.ty_wf _
  | primOp h => exact PrimOp.ty_wf h
  | ctor hsch hinst =>
      exact Scheme.instance_wf (Signature.ctorScheme_wf hsch) (Nat.zero_le _) hinst
  | var hlook hinst =>
      exact Scheme.instance_wf (ctxWF_getElem ctxWF hlook) (le_refl _) hinst
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
  | «match» scrutineeTyping declEq argsLen branchesNe patternsOk aligned branchTyping
      scrutineeIh branchIh =>
      simp only [Expr.erase, scrutineeIh]
      rw [Expr.eraseBranches_eq, Expr.eraseBranches_eq,
        map_erase_eq_of_aligned patternsOk aligned branchIh]
  | lit | primOp | ctor | var => rfl
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
  | «match» scrutineeTyping declEq argsLen branchesNe patternsOk aligned branchTyping
      scrutineeIh branchIh =>
      refine RuntimeTyping.«match» (scrutineeIh ctxWF) declEq argsLen ?_ ?_ ?_
      · rw [Expr.eraseBranches_eq]
        intro hnil
        exact branchesNe (List.map_eq_nil_iff.mp hnil)
      · rw [Expr.eraseBranches_eq]
        simpa using patternsOk
      · intro pattern body fields hmem hfields
        rw [Expr.eraseBranches_eq] at hmem
        obtain ⟨⟨pattern₀, body₀⟩, hmem₀, heq⟩ := List.mem_map.mp hmem
        simp only [Prod.mk.injEq] at heq
        obtain ⟨hpat, hbod⟩ := heq
        obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hmem₀
        obtain ⟨bodyElab, hiElab⟩ := exists_branch_of_map_fst aligned hi
        rw [← hpat] at hfields
        rw [← hbod]
        exact branchIh i pattern₀ body₀ bodyElab fields hi hiElab hfields ctxWF
  | lit => exact .lit
  | primOp h => exact .primOp h
  | ctor hsch hinst => exact .ctor hsch hinst
  | var hlook hinst => exact .var hlook hinst
  | lambda hparam hmatch hbody ih =>
      expose_names
      exact .lambda hparam (ih (ctxWF_cons (Scheme.mono paramTy) hparam ctxWF))
  | app hf ha ihf iha => exact .app (ihf ctxWF) (iha ctxWF)
  | letMono hrhs hbody ihrhs ihbody =>
      expose_names
      have hwf := regular ctxWF hrhs
      refine RuntimeTyping.letIn (scheme := Scheme.mono rhsTy) hwf ?_ ?_
      · intro k' hle ty hinst
        obtain rfl := Scheme.instance_mono.mp hinst
        exact RuntimeTyping.mono_depth (ihrhs ctxWF) hle
      · exact ihbody (ctxWF_cons (Scheme.mono rhsTy) hwf ctxWF)
  | letPoly hcomp hrhs hdet hbody ihrhs ihbody =>
      expose_names
      refine RuntimeTyping.letIn (scheme := scheme) hcomp.wf ?_
        (ihbody (ctxWF_cons scheme hcomp.wf ctxWF))
      intro k' hle ty hinst
      obtain ⟨args, hlen, hargs, rfl⟩ := hinst
      have hwfK : Ctx.WF (k_1 + scheme.arity) ctx_1 :=
        Ctx.WF.mono ctxWF (Nat.le_add_right k_1 scheme.arity)
      have hsub := RuntimeTyping.substRigids (k' := k') hwfK (ihrhs hwfK)
        (blockSubst k_1 args) (fun l hl => blockSubst_wf hlen hargs hle hl)
      rwa [map_substRigids_eq_self ctxWF (fun l hl => by simp [blockSubst, hl]),
        Scheme.skolemize_substRigids hcomp.wf hlen] at hsub
  | fix hwf hmatch hbody ih =>
      expose_names
      exact .fix hwf (ih (ctxWF_cons (Scheme.mono selfTy) hwf ctxWF))

end TypingWith

theorem Elaborates.typing (elaborates : Elaborates sig k ctx src elaboration ty) :
    Typing sig k ctx src elaboration ty :=
  TypingWith.mono (fun _ _ _ _ _ _ => trivial) elaborates

end EPL
