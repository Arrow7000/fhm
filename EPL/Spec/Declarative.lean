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

/-- A type that mentions no rigid variables is unchanged by a rigid
substitution. -/
private theorem Ty.substRigids_closed_eq_self {V : Type} {ty : Ty V} {f : Nat → Ty V}
    {binders : Nat} (wf : ty.Scoped 0 binders) : ty.substRigids f = ty := by
  show ty.subst ⟨.bvar, f, .var⟩ = ty
  have hc : ty.subst ⟨.bvar, f, .var⟩ = ty.subst Ty.Subst.id :=
    Ty.subst_congr wf (fun _ _ => rfl) (fun l hl => absurd hl (Nat.not_lt_zero l))
      (fun _ _ => rfl)
  rw [hc, Ty.subst_id]

/-- A type in scope at depth `k` is unchanged by a rigid substitution that is
the identity below `k`. -/
private theorem Ty.substRigids_eq_self {V : Type} {ty : Ty V} {f : Nat → Ty V} {k : Nat}
    (wf : ty.WF k) (agrees : ∀ l < k, f l = .rigid l) : ty.substRigids f = ty := by
  show ty.subst ⟨.bvar, f, .var⟩ = ty
  have hc : ty.subst ⟨.bvar, f, .var⟩ = ty.subst Ty.Subst.id :=
    Ty.subst_congr wf (fun _ _ => rfl) (fun l hl => agrees l hl) (fun _ _ => rfl)
  rw [hc, Ty.subst_id]

/-- An `instantiate` followed by a rigid substitution is the `instantiate` at
the substituted arguments, provided the type mentions only binders. -/
private theorem Ty.instantiate_substRigids {V : Type} {ty : Ty V} {args : List (Ty V)}
    {f : Nat → Ty V} (wf : ty.Scoped 0 args.length) :
    (ty.instantiate args).substRigids f =
      ty.instantiate (args.map (·.substRigids f)) := by
  have h := Scheme.inst_substRigids (scheme := ⟨args.length, ty⟩) args (k := 0) wf
    (f := f) (rigids := 0) (fun l hl => absurd hl (Nat.not_lt_zero l))
  simp only [Scheme.inst, Scheme.substRigids] at h
  rw [Ty.substRigids_closed_eq_self wf] at h
  exact h

/-- A rigid substitution acts on an arrow type domain by domain. -/
private theorem Ty.arrows_substRigids {V : Type} (domains : List (Ty V)) (codomain : Ty V)
    (f : Nat → Ty V) :
    (Ty.arrows domains codomain).substRigids f =
      Ty.arrows (domains.map (·.substRigids f)) (codomain.substRigids f) := by
  induction domains with
  | nil => rfl
  | cons d ds ih =>
      change Ty.substRigids f (Ty.arrow d (Ty.arrows ds codomain)) =
        Ty.arrow (Ty.substRigids f d)
          (Ty.arrows (ds.map (·.substRigids f)) (Ty.substRigids f codomain))
      rw [show Ty.substRigids f (Ty.arrow d (Ty.arrows ds codomain)) =
          Ty.arrow (Ty.substRigids f d) (Ty.substRigids f (Ty.arrows ds codomain)) from rfl]
      rw [ih]

/-- The head and the arguments of a well-scoped type application are well
scoped. -/
private theorem Ty.apps_scoped_inv {V : Type} {head : Ty V} {args : List (Ty V)} {r b : Nat}
    (h : (Ty.apps head args).Scoped r b) :
    head.Scoped r b ∧ ∀ a ∈ args, a.Scoped r b := by
  induction args generalizing head with
  | nil => exact ⟨h, by simp⟩
  | cons a as ih =>
      change Ty.Scoped r b (Ty.apps (Ty.app head a) as) at h
      obtain ⟨hhead, hrest⟩ := ih h
      refine ⟨hhead.1, ?_⟩
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hmem
      · exact hhead.2
      · exact hrest x hmem

/-- A list of types in scope at depth `k` is unchanged by a rigid substitution
that is the identity below `k`. -/
private theorem List.map_substRigids_eq_self {args : List SemTy} {f : Nat → SemTy} {k : Nat}
    (wf : ∀ a ∈ args, a.WF k) (agrees : ∀ l < k, f l = .rigid l) :
    args.map (·.substRigids f) = args := by
  rw [List.map_congr_left fun a ha => Ty.substRigids_eq_self (wf a ha) agrees]
  exact List.map_id args

/-- Indexing a list by every index below its length gives the list back. -/
private theorem list_getD_range_map {α : Type} {l : List α} {n : Nat} (hlen : l.length = n)
    (d : Nat → α) : (List.range n).map (fun i => l.getD i (d i)) = l := by
  apply List.ext_getElem
  · simp [hlen]
  · intro i hi _
    simp only [List.getElem_map, List.getElem_range]
    have hai : i < l.length := by simpa [hlen] using hi
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hai, Option.getD_some]

/-- A rigid block substituted pointwise is the list of types it stands for. -/
private theorem rigidBlock_map_substRigids {k n : Nat} {hidden : List SemTy} {f : Nat → SemTy}
    (hlen : hidden.length = n) (hf : ∀ i < n, f (k + i) = hidden.getD i (.rigid (k + i))) :
    (rigidBlock k n).map (·.substRigids f) = hidden := by
  have hmap : (rigidBlock k n).map (·.substRigids f) = (List.range n).map fun i => f (k + i) := by
    unfold rigidBlock
    rw [List.map_map]
    rfl
  rw [hmap, show (List.range n).map (fun i => f (k + i)) =
      (List.range n).map (fun i => hidden.getD i (.rigid (k + i))) from by
    apply List.map_congr_left
    intro i hi
    exact hf i (List.mem_range.mp hi)]
  exact list_getD_range_map hlen _

/-- A successful declaration lookup gives a well-formed declaration. -/
private theorem Signature.decl?_wf {sig : Signature} {type : Nat} {decl : DataDecl}
    (found : sig.decl? type = some decl) : decl.WF := by
  cases h : sig[type]? with
  | none => simp [Signature.decl?, h] at found
  | some other =>
      by_cases hwf : other.WF
      · simp only [Signature.decl?, h, Option.bind_eq_bind, Option.bind_some] at found
        simp only [hwf, if_true, Option.some.injEq] at found
        subst found
        exact hwf
      · simp only [Signature.decl?, h, Option.bind_eq_bind, Option.bind_some] at found
        simp only [hwf, if_false] at found
        cases found

/-- Branch lists with the same patterns line up by index: the elaboration has a
branch at every index where the source does, with the same pattern. -/
private theorem exists_branch_of_map_fst {A B : Type} {branches : List (Pattern × Expr A)}
    {branchesElab : List (Pattern × Expr B)} {i : Nat} {pattern : Pattern} {body : Expr A}
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

/-- Erasing the bodies of two pattern-aligned branch lists commutes with the
alignment: branch by branch, the types agree by the indexed premise. -/
private theorem map_erase_eq_of_aligned {A B : Type} {branches : List (Pattern × Expr A)}
    {branchesElab : List (Pattern × Expr B)} {decl : DataDecl} {type : Nat}
    (patternsOk : ∀ pattern ∈ branches.map (·.1),
      pattern.ctor.type = type ∧ pattern.ctor.index < decl.ctors.length)
    (aligned : branchesElab.map (·.1) = branches.map (·.1))
    (bodies : ∀ (i : Nat) (pattern : Pattern) (body : Expr A) (bodyElab : Expr B)
      (ctor : CtorDecl),
      branches[i]? = some (pattern, body) →
      branchesElab[i]? = some (pattern, bodyElab) →
      decl.ctors[pattern.ctor.index]? = some ctor → Expr.erase bodyElab = Expr.erase body) :
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
      have hlen : pattern.ctor.index < decl.ctors.length := (patternsOk pattern hmem).2
      obtain ⟨fields, hfields⟩ : ∃ fields, decl.ctors[pattern.ctor.index]? = some fields :=
        ⟨decl.ctors[pattern.ctor.index]'hlen, List.getElem?_eq_getElem hlen⟩
      rw [hbE]
      show some (pattern, Expr.erase bodyElab) = some (pattern, Expr.erase body)
      rw [bodies i pattern body bodyElab fields hb hbE hfields]

/-- Every type in a rigid block is in scope one block deeper. -/
private theorem rigidBlock_mem_wf {a : SemTy} {k n k' : Nat} (hle : k + n ≤ k')
    (h : a ∈ rigidBlock k n) : a.WF k' := by
  simp only [rigidBlock, List.mem_map, List.mem_range] at h
  obtain ⟨i, hi, rfl⟩ := h
  show k + i < k'
  omega

/-- A constructor's field context is well formed at a depth that sees the type
arguments and the constructor's own variables. -/
private theorem CtorDecl.fieldCtx_wf {decl : DataDecl} {ctor : CtorDecl} {args hidden : List SemTy}
    {k' : Nat} (hdecl : decl.WF) (hctor : ctor ∈ decl.ctors)
    (hargsLen : args.length = decl.params) (hlen : hidden.length = ctor.existentials)
    (hargs : ∀ a ∈ args, a.WF k') (hhidden : ∀ a ∈ hidden, a.WF k') :
    (ctor.fieldCtx args hidden).WF k' := by
  intro scheme hscheme
  unfold CtorDecl.fieldCtx at hscheme
  rw [List.mem_reverse] at hscheme
  obtain ⟨field, hfield, rfl⟩ := List.mem_map.mp hscheme
  show (field.instantiate (args ++ hidden)).WF k'
  have hscope : field.Scoped 0 (decl.params + ctor.existentials) := hdecl ctor hctor field hfield
  have hmono : field.Scoped k' (args ++ hidden).length := by
    rw [List.length_append, hargsLen, hlen]
    exact Ty.Scoped.mono hscope (Nat.zero_le k') (le_refl _)
  exact Scheme.inst_wf (scheme := ⟨(args ++ hidden).length, field⟩) hmono (le_refl k') rfl
    (fun a ha => by
      rcases List.mem_append.mp ha with h | h
      · exact hargs a h
      · exact hhidden a h)

/-- A rigid substitution that fixes the arguments and maps the constructor's
fresh block to `hidden` acts on the field context by replacing the block. -/
private theorem CtorDecl.fieldCtx_substRigids {decl : DataDecl} {ctor : CtorDecl}
    {args hidden : List SemTy} {f : Nat → SemTy} {k : Nat}
    (hdecl : decl.WF) (hctor : ctor ∈ decl.ctors) (hargsLen : args.length = decl.params)
    (hargs : args.map (·.substRigids f) = args)
    (hblock : (rigidBlock k ctor.existentials).map (·.substRigids f) = hidden) :
    (ctor.fieldCtx args (rigidBlock k ctor.existentials)).map (Scheme.substRigids f) =
      ctor.fieldCtx args hidden := by
  unfold CtorDecl.fieldCtx
  rw [List.map_reverse, List.map_map]
  apply congrArg List.reverse
  apply List.map_congr_left
  intro field hfield
  simp only [Function.comp_apply, Scheme.substRigids, Scheme.mono]
  have hscope : field.Scoped 0 (args.length + ctor.existentials) := by
    have h := hdecl ctor hctor field hfield
    rwa [← hargsLen] at h
  have hscoped : field.Scoped 0 (args ++ rigidBlock k ctor.existentials).length := by
    simpa [List.length_append, rigidBlock] using hscope
  rw [Ty.instantiate_substRigids (f := f) hscoped, List.map_append, hargs, hblock]

namespace TypingWith

/-- A weaker let condition admits more derivations. -/
theorem mono {Det Det' : LetCondition}
    (weaker : ∀ k ctx ann rhs scheme, Det k ctx ann rhs scheme → Det' k ctx ann rhs scheme)
    (typing : TypingWith sig Det k ctx src elaboration ty) :
    TypingWith sig Det' k ctx src elaboration ty := by
  induction typing with
  | «match» scrutineeTyping declEq argsLen branchesNe patternsOk arityOk aligned branchTyping
      resultTyWF scrutineeIh branchIh =>
      exact .«match» scrutineeIh declEq argsLen branchesNe patternsOk arityOk aligned branchIh
        resultTyWF
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
  | «match» scrutineeTyping declEq argsLen branchesNe patternsOk arityOk aligned branchTyping
      resultTyWF scrutineeIh branchIh =>
      exact resultTyWF
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
  | «match» scrutineeTyping declEq argsLen branchesNe patternsOk arityOk aligned branchTyping
      resultTyWF scrutineeIh branchIh =>
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
  | «match» scrutineeTyping declEq argsLen branchesNe patternsOk arityOk aligned branchTyping
      resultTyWF scrutineeIh branchIh =>
      refine RuntimeTyping.«match» (scrutineeIh ctxWF) declEq argsLen ?_ ?_ ?_ ?_
      · rw [Expr.eraseBranches_eq]
        intro hnil
        exact branchesNe (List.map_eq_nil_iff.mp hnil)
      · rw [Expr.eraseBranches_eq]
        simpa using patternsOk
      · rw [Expr.eraseBranches_eq]
        simpa using arityOk
      · intro pattern body ctor hmem hfields k' hle hidden hlen hhidden
        rw [Expr.eraseBranches_eq] at hmem
        obtain ⟨⟨pattern₀, body₀⟩, hmem₀, heq⟩ := List.mem_map.mp hmem
        simp only [Prod.mk.injEq] at heq
        obtain ⟨hpat, hbod⟩ := heq
        obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hmem₀
        obtain ⟨bodyElab, hiElab⟩ := exists_branch_of_map_fst aligned hi
        rw [← hpat] at hfields
        rw [← hbod]
        -- The branch body is typed with the constructor's own variables as the
        -- fresh levels `k, ..., k + e - 1` in the field context.
        expose_names
        have hdeclWF : decl.WF := Signature.decl?_wf declEq
        have hctors : ctor ∈ decl.ctors := List.mem_of_getElem? hfields
        have hargsWF : ∀ a ∈ args, a.WF k_1 :=
          (Ty.apps_scoped_inv (regular ctxWF scrutineeTyping)).2
        have hargsWF' : ∀ a ∈ args, a.WF (k_1 + ctor.existentials) :=
          fun a ha => Ty.Scoped.mono (hargsWF a ha) (by omega) (le_refl _)
        have hfieldCtxWF :
            (ctor.fieldCtx args (rigidBlock k_1 ctor.existentials)).WF
              (k_1 + ctor.existentials) :=
          CtorDecl.fieldCtx_wf (hidden := rigidBlock k_1 ctor.existentials)
            hdeclWF hctors argsLen (by simp [rigidBlock]) hargsWF'
            (fun a ha => rigidBlock_mem_wf (k := k_1) (n := ctor.existentials)
              (k' := k_1 + ctor.existentials) (le_refl _) ha)
        have hctx : (ctor.fieldCtx args (rigidBlock k_1 ctor.existentials) ++ ctx_1).WF
            (k_1 + ctor.existentials) := by
          intro scheme hscheme
          rcases List.mem_append.mp hscheme with hscheme | hscheme
          · exact hfieldCtxWF scheme hscheme
          · exact Ctx.WF.mono ctxWF (Nat.le_add_right k_1 ctor.existentials) scheme hscheme
        have ih := branchIh i pattern₀ body₀ bodyElab ctor hi hiElab hfields hctx
        -- Replace those fresh levels by the value's own `hidden` types,
        -- keeping everything below `k` as it is.
        let f : Nat → SemTy :=
          fun l => if l < k_1 then .rigid l else hidden.getD (l - k_1) (.rigid l)
        have hf_agree : ∀ l < k_1, f l = .rigid l := fun l hl => by simp [f, hl]
        have himages : ∀ l < k_1 + ctor.existentials, (f l).WF k' := by
          intro l hl
          by_cases hlt : l < k_1
          · rw [hf_agree l hlt]
            show l < k'
            omega
          · have hfl : f l = hidden.getD (l - k_1) (.rigid l) := by simp [f, hlt]
            rw [hfl]
            have hd : l - k_1 < hidden.length := by omega
            rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hd, Option.getD_some]
            exact hhidden _ (List.getElem_mem hd)
        have hsub := RuntimeTyping.substRigids (k' := k') hctx ih f himages
        have hargsMap : args.map (·.substRigids f) = args :=
          List.map_substRigids_eq_self hargsWF hf_agree
        have hhiddenMap : (rigidBlock k_1 ctor.existentials).map (·.substRigids f) = hidden :=
          rigidBlock_map_substRigids hlen fun i hi => by
            show f (k_1 + i) = hidden.getD i (.rigid (k_1 + i))
            simp [f, show ¬ k_1 + i < k_1 by omega, show k_1 + i - k_1 = i by omega]
        have hctxMap :
            ((ctor.fieldCtx args (rigidBlock k_1 ctor.existentials) ++ ctx_1).map
                (Scheme.substRigids f)) = ctor.fieldCtx args hidden ++ ctx_1 := by
          rw [List.map_append,
            CtorDecl.fieldCtx_substRigids hdeclWF hctors argsLen hargsMap hhiddenMap,
            map_substRigids_eq_self ctxWF hf_agree]
        have hres : resultTy.substRigids f = resultTy :=
          Ty.substRigids_eq_self resultTyWF hf_agree
        rw [hctxMap, hres] at hsub
        exact hsub
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
