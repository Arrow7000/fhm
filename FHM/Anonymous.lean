import FHM.Completeness

/-! Anonymous annotation input is separate from ordinary Core. A hole is syntax,
not a free type variable: each visit allocates a fresh flexible variable. The
completed output of elaboration remains an ordinary `Expr`.

This module starts with ordinary lambda and let generalisation. Partial explicit
quantifiers and partial recursive contracts are deliberately distinguished in
the syntax so an unsupported case cannot accidentally become a complete Core
signature (and hence a polymorphic-recursion dependency cut).
-/


private theorem branch_tyFreeVars_mem {branches : List (MatchPattern × Expr)}
    {p : MatchPattern} {body : Expr} {v : Nat} (hb : (p, body) ∈ branches)
    (hv : v ∈ body.tyFreeVars) :
    v ∈ Expr.tyFreeVars.BranchList.tyFreeVars branches := by
  induction branches with
  | nil => cases hb
  | cons head tail ih =>
    rcases head with ⟨p', body'⟩
    simp only [Expr.tyFreeVars.BranchList.tyFreeVars, List.mem_append]
    rcases List.mem_cons.mp hb with heq | hb
    · cases heq; exact Or.inl hv
    · exact Or.inr (ih hb)

/-- Pointwise identity on annotation free variables fixes an entire Core expression. -/
theorem Expr.substTyFvars_eq_self_of_fixes {S : Subst} {e : Expr}
    (h : ∀ v ∈ e.tyFreeVars, S.onTy (.fvar v) = .fvar v) :
    e.substTyFvars S = e := by
  induction e using Expr.rec_strong with
  | primLit p =>
    exact Expr.substTyFvars_eq_self_of_not_mem_tyFreeVars (by simp [Expr.tyFreeVars])
  | primBinOp op =>
    exact Expr.substTyFvars_eq_self_of_not_mem_tyFreeVars (by simp [Expr.tyFreeVars])
  | var n => exact Expr.substTyFvars_var
  | ctor name =>
    exact Expr.substTyFvars_eq_self_of_not_mem_tyFreeVars (by simp [Expr.tyFreeVars])
  | lambda ann body ih =>
    rw [Expr.substTyFvars_lambda]
    have hb := ih (fun v hv => h v (List.mem_append_right _ hv))
    rw [hb]
    cases ann with
    | none => rfl
    | some t =>
      have ht : Ty.substFvars S t = t := Subst.onTy_eq_self_of_fixes
        (fun v hv => h v (List.mem_append_left _ hv))
      simp only [Option.map_some, ht]
  | app f arg ihf iha =>
    rw [Expr.substTyFvars_app,
      ihf (fun v hv => h v (List.mem_append_left _ hv)),
      iha (fun v hv => h v (List.mem_append_right _ hv))]
  | letIn ann rhs body ihr ihb =>
    rw [Expr.substTyFvars_letIn,
      ihr (fun v hv => h v (List.mem_append_left _ (List.mem_append_right _ hv))),
      ihb (fun v hv => h v (List.mem_append_right _ hv))]
    cases ann with
    | none => rfl
    | some scheme =>
      have hs : Ty.substFvars S scheme.body = scheme.body := Subst.onTy_eq_self_of_fixes
        (fun v hv => h v (List.mem_append_left _ (List.mem_append_left _ hv)))
      simp only [Option.map_some, hs]
  | match_ scrut branches ihs ihbs =>
    rw [Expr.substTyFvars_match, ihs (fun v hv => h v (List.mem_append_left _ hv))]
    congr 1
    apply List.map_eq_self_of_forall_eq_id
    rintro ⟨p, b⟩ hb
    change (p, b.substTyFvars S) = (p, b)
    rw [ihbs p b hb (fun v hv => h v
      (List.mem_append_right _ (branch_tyFreeVars_mem hb hv)))]
  | letRec anns bindings body ihbs ihb =>
    rw [Expr.substTyFvars_letRec,
      ihb (fun v hv => h v (List.mem_append_right _ hv))]
    have hbindings : bindings.map (fun b => b.substTyFvars S) = bindings := by
      apply List.map_eq_self_of_forall_eq_id
      intro b hb
      apply ihbs b hb
      intro v hv
      apply h v
      apply List.mem_append_left
      apply List.mem_append_right
      exact Expr.mem_flatMap_tyFreeVars_iff_recGroup.mp (List.mem_flatMap.mpr ⟨b, hb, hv⟩)
    rw [hbindings]
    congr 1
    apply List.map_eq_self_of_forall_eq_id
    intro ann hann
    cases ann with
    | none => exact RecAnn.substFvars_none S
    | some scheme =>
      have hs : Ty.substFvars S scheme.body = scheme.body := Subst.onTy_eq_self_of_fixes
        (fun v hv => h v (List.mem_append_left _ (List.mem_append_left _
          (Expr.scheme_body_mem_annList_tyFreeVars hann hv))))
      simp only [RecAnn.substFvars_some, PolyTy.substFvars_eq, hs]

/-- Literal domain avoidance implies pointwise rigidity of the composite. -/
theorem Subst.fixes_of_dom_avoids {K : List Nat} {subst : Subst}
    (h : ∀ pair ∈ subst, pair.1 ∉ K) :
    ∀ v ∈ K, subst.onTy (.fvar v) = .fvar v := by
  intro v hv
  apply Ty.substFvars_eq_self_of_no_key
  intro pair hp hc
  have heq : pair.1 = v := by simpa only [Ty.freeVars, List.mem_singleton] using hc
  exact h pair hp (heq ▸ hv)

namespace Anonymous

/-- The fixed leaves retain authored type syntax; every `hole` occurrence is
independent. `fixed` is also the embedding of a complete monotype. -/
inductive Template where
  | fixed (ty : Ty)
  | hole
  | arrow (domain codomain : Template)
  | custom (name : TyName) (args : List Template)

/-- Declarative matching of an annotation template. This relation neither
allocates metavariables nor mentions inference or an executable substitution. -/
inductive Template.Fits : Template → Ty → Prop
  | fixed : Fits (.fixed ty) ty
  | hole : Fits .hole ty
  | arrow : Fits a ta → Fits b tb → Fits (.arrow a b) (.arrow ta tb)
  | custom : List.Forall₂ Fits args tys → Fits (.custom name args) (.customTy name tys)

mutual
def Template.rigidVars : Template → List Nat
  | .fixed ty => ty.freeVars
  | .hole => []
  | .arrow a b => a.rigidVars ++ b.rigidVars
  | .custom _ args => rigidVarsList args
def rigidVarsList : List Template → List Nat
  | [] => []
  | template :: rest => template.rigidVars ++ rigidVarsList rest
end


/-- Complete signatures and partial signatures have different checking modes.
The quantified partial form is recorded separately pending its scoped rule. -/
inductive LetAnn where
  | absent
  | complete (scheme : PolyTy)
  | template (body : Template)
  | partialForall (paramCount : Nat) (body : Template)

/-- A Core-shaped input spine. Type annotations are inputs to elaboration,
whereas the output is always the existing ordinary Core `Expr`. -/
inductive Input where
  | primLit (value : PrimLitExpr)
  | primBinOp (op : PrimBinOp)
  | lambda (ann : Option Template) (body : Input)
  | app (fn arg : Input)
  | letIn (ann : LetAnn) (rhs body : Input)
  | var (index : Nat)
  | ctor (name : CtorName)
  | match_ (scrutinee : Input) (branches : List (MatchPattern × Input))
  | letRec (anns : List LetAnn) (bindings : List Input) (body : Input)

mutual
/-- Runtime shape, independently of any choices made for anonymous holes. -/
def Input.erase : Input → Expr
  | .primLit p => .primLit p
  | .primBinOp op => .primBinOp op
  | .lambda _ body => .lambda none body.erase
  | .app f x => .app f.erase x.erase
  | .letIn _ rhs body => .letIn none rhs.erase body.erase
  | .var i => .var i
  | .ctor c => .ctor c
  | .match_ scrut branches => .match_ scrut.erase (eraseBranches branches)
  | .letRec _ bindings body =>
      .letRec (bindings.map fun _ => none) (eraseBindings bindings) body.erase
def eraseBranches : List (MatchPattern × Input) → List (MatchPattern × Expr)
  | [] => []
  | (pat, body) :: rest => (pat, body.erase) :: eraseBranches rest
def eraseBindings : List Input → List Expr
  | [] => []
  | body :: rest => body.erase :: eraseBindings rest
end

/-- Complete annotation modes only. A partial mode stays partial even if its
template happens not to contain a hole. -/
def LetAnn.toCore : LetAnn → Option (Option PolyTy)
  | .absent => some none
  | .complete scheme => some (some scheme)
  | .template _ | .partialForall _ _ => none

mutual
def Template.toCore : Template → Option Ty
  | .fixed ty => some ty
  | .hole => none
  | .arrow a b => return .arrow (← a.toCore) (← b.toCore)
  | .custom name args => return .customTy name (← completeTypes args)
def completeTypes : List Template → Option (List Ty)
  | [] => some []
  | template :: rest => return (← template.toCore) :: (← completeTypes rest)
end

def completeLambdaAnn : Option Template → Option (Option Ty)
  | none => some none
  | some template => return some (← template.toCore)

mutual
/-- A decidable conservative embedding, preserving complete/partial modes.
Only a whole subtree successfully embedded here may use the old Core backend. -/
def Input.toCore : Input → Option Expr
  | .primLit p => some (.primLit p)
  | .primBinOp op => some (.primBinOp op)
  | .lambda ann body => return .lambda (← completeLambdaAnn ann) (← body.toCore)
  | .app f x => return .app (← f.toCore) (← x.toCore)
  | .letIn ann rhs body => return .letIn (← ann.toCore) (← rhs.toCore) (← body.toCore)
  | .var i => some (.var i)
  | .ctor name => some (.ctor name)
  | .match_ scrut branches => return .match_ (← scrut.toCore) (← completeBranches branches)
  | .letRec anns bindings body =>
      return .letRec (← completeAnns anns) (← completeBindings bindings) (← body.toCore)
def completeBranches : List (MatchPattern × Input) → Option (List (MatchPattern × Expr))
  | [] => some []
  | (pat, body) :: rest => return (pat, ← body.toCore) :: (← completeBranches rest)
def completeBindings : List Input → Option (List Expr)
  | [] => some []
  | body :: rest => return (← body.toCore) :: (← completeBindings rest)
def completeAnns : List LetAnn → Option (List (Option PolyTy))
  | [] => some []
  | ann :: rest => return (← ann.toCore) :: (← completeAnns rest)
end

mutual
theorem Input.toCore_erase (input : Input) {core : Expr}
    (h : input.toCore = some core) : core.erase = input.erase := by
  cases input with
  | primLit p => cases h; simp only [Expr.erase, Input.erase]
  | primBinOp op => cases h; simp only [Expr.erase, Input.erase]
  | var i => cases h; simp only [Expr.erase, Input.erase]
  | ctor c => cases h; simp only [Expr.erase, Input.erase]
  | lambda ann body =>
      simp only [Input.toCore, bind, pure, Option.bind_eq_some_iff,
        Option.some.injEq] at h
      obtain ⟨ann', _, body', hb, rfl⟩ := h
      simp only [Expr.erase, Input.erase, body.toCore_erase hb]
  | app f x =>
      simp only [Input.toCore, bind, pure, Option.bind_eq_some_iff,
        Option.some.injEq] at h
      obtain ⟨f', hf, x', hx, rfl⟩ := h
      simp only [Expr.erase, Input.erase, f.toCore_erase hf, x.toCore_erase hx]
  | letIn ann rhs body =>
      simp only [Input.toCore, bind, pure, Option.bind_eq_some_iff,
        Option.some.injEq] at h
      obtain ⟨ann', _, rhs', hr, body', hb, rfl⟩ := h
      simp only [Expr.erase, Input.erase, rhs.toCore_erase hr, body.toCore_erase hb]
  | match_ scrut branches =>
      simp only [Input.toCore, bind, pure, Option.bind_eq_some_iff,
        Option.some.injEq] at h
      obtain ⟨scrut', hs, branches', hb, rfl⟩ := h
      simp only [Expr.erase, Input.erase, scrut.toCore_erase hs, completeBranches_erase branches hb]
  | letRec anns bindings body =>
      simp only [Input.toCore, bind, pure, Option.bind_eq_some_iff,
        Option.some.injEq] at h
      obtain ⟨anns', _, bindings', hr, body', hb, rfl⟩ := h
      have hbindings := completeBindings_erase bindings hr
      have hlength : bindings'.length = bindings.length := by
        have := congrArg List.length hbindings
        simpa only [List.length_map, eraseBindings_length] using this
      simp only [Expr.erase, Input.erase, body.toCore_erase hb, hbindings]
      congr 1
      simp only [List.map_const', hlength]
theorem completeBranches_erase (inputs : List (MatchPattern × Input))
    {cores : List (MatchPattern × Expr)} (h : completeBranches inputs = some cores) :
    cores.map (fun pe => (pe.1, pe.2.erase)) = eraseBranches inputs := by
  cases inputs with
  | nil => cases h; rfl
  | cons head rest =>
      rcases head with ⟨pat, body⟩
      simp only [completeBranches, bind, pure, Option.bind_eq_some_iff,
        Option.some.injEq] at h
      obtain ⟨body', hb, rest', hr, rfl⟩ := h
      simp only [List.map_cons, eraseBranches, body.toCore_erase hb, completeBranches_erase rest hr]
theorem completeBindings_erase (inputs : List Input) {cores : List Expr}
    (h : completeBindings inputs = some cores) :
    cores.map Expr.erase = eraseBindings inputs := by
  cases inputs with
  | nil => cases h; rfl
  | cons body rest =>
      simp only [completeBindings, bind, pure, Option.bind_eq_some_iff,
        Option.some.injEq] at h
      obtain ⟨body', hb, rest', hr, rfl⟩ := h
      simp only [List.map_cons, eraseBindings, body.toCore_erase hb, completeBindings_erase rest hr]
theorem eraseBindings_length (inputs : List Input) : (eraseBindings inputs).length = inputs.length := by
  cases inputs with
  | nil => rfl
  | cons body rest =>
      simpa only [eraseBindings, List.length_cons] using congrArg Nat.succ (eraseBindings_length rest)
end

/-- A partial ordinary signature constrains the inferred monotype before that
monotype is generalised. It is not an existential complete Core signature. -/
def LetAnn.FitsMono : LetAnn → Ty → Prop
  | .absent, _ => True
  | .template t, ty => t.Fits ty
  | _, _ => False

/-- Structural annotation completion. This is distinct from input admissibility
(`Typing` below): it records fixed syntax, individual hole fillings, and the
type abstraction/specialization performed when an ordinary let is generalized.
Protected fixed variables cannot be substituted or captured by new binders.
Scope correctness of the resulting Core is supplied by output typing. -/
inductive Completes (K : List Nat) : Input → Expr → Prop
  | complete : input.toCore = some core →
      (∀ v ∈ core.tyFreeVars, v ∈ K) → Completes K input core
  | lambda :
      (∀ template, ann = some template → template.Fits param) →
      (∀ template, ann = some template → ∀ v ∈ template.rigidVars, v ∈ K) →
      Completes K body completed →
      Completes K (.lambda ann body) (.lambda (ann.map fun _ => param) completed)
  | app : Completes K f fOut → Completes K x xOut →
      Completes K (.app f x) (.app fOut xOut)
  | specialise :
      Completes K input output → (∀ pair ∈ subst, pair.1 ∉ K) →
      Completes K input (output.substTyFvars subst)
  | letIn {subst : Subst} :
      ann.FitsMono ty →
      (∀ template, ann = .template template → ∀ v ∈ template.rigidVars, v ∈ K) →
      Completes K rhs rhsOut → Completes K body bodyOut →
      (∀ name ∈ names, name ∉ K) → (∀ pair ∈ subst, pair.1 ∉ K) →
      Completes K (.letIn ann rhs body)
        (.letIn (some (subst.onPolyTy ⟨names.length, Ty.closeOver names ty⟩))
          ((rhsOut.closeTyVars names).substTyFvars subst) bodyOut)

/-- Independent input typing for the first fragment. `K` contains ambient rigid
annotation variables; free variables in context monotypes can remain flexible.
 The let rule generalises
the RHS cofinally, and partial annotations constrain that very monotype. There
is no recursive rule: in particular, a partial annotation cannot acquire
polymorphic recursive uses through an arbitrary completed output signature.

Whole completed subtrees use their existing checking rules through the
conservative Core embedding. Complete annotated lets with partial syntax
in their RHS or continuation, and partial match/recursive spines, have no rule
in this first fragment.
-/
inductive Typing (K : List Nat) : Ctx → Input → Ty → Prop
  /-- Existing complete Core programs retain their existing declarative meaning.
  The checked embedding rejects every partial annotation mode. -/
  | complete : input.toCore = some core →
      (∀ v ∈ core.tyFreeVars, v ∈ K) → TypeOfHM ctx core ty → Typing K ctx input ty
  | primLit : TypeOfHM ctx (.primLit p) ty → Typing K ctx (.primLit p) ty
  | primBinOp : TypeOfHM ctx (.primBinOp op) ty → Typing K ctx (.primBinOp op) ty
  | lambda :
      paramTy.IsLC →
      (∀ template, ann = some template → template.Fits paramTy) →
      (∀ template, ann = some template → ∀ v ∈ template.rigidVars, v ∈ K) →
      Typing K { ctx with env := PolyTy.mkTrivial paramTy :: ctx.env } body bodyTy →
      Typing K ctx (.lambda ann body) (.arrow paramTy bodyTy)
  | app : Typing K ctx f (.arrow argTy retTy) → Typing K ctx arg argTy →
      Typing K ctx (.app f arg) retTy
  | letIn {M : PolyTy} {L : List Nat} :
      M.WF →
      (∀ template, ann = .template template → ∀ v ∈ template.rigidVars, v ∈ K) →
      (∀ Xs, FreshNames L M.paramCount Xs → ann.FitsMono (M.openVars Xs)) →
      (∀ Xs, FreshNames L M.paramCount Xs → Typing K ctx rhs (M.openVars Xs)) →
      Typing K { ctx with env := M :: ctx.env } body bodyTy →
      Typing K ctx (.letIn ann rhs body) bodyTy
  | var : ctx.env[index]? = some scheme →
      (∀ arg ∈ args, arg.IsLC) → scheme.InstantiatesTo args ty →
      Typing K ctx (.var index) ty
  | ctor : LookupList.get? ctx.ctors name = some ctor →
      (∀ arg ∈ args, arg.IsLC) → ctor.toTy.InstantiatesTo args ty →
      Typing K ctx (.ctor name) ty

/-- The input specification has the ordinary HM runtime meaning independently
of elaboration. Annotation matching restricts this meaning; it never grants a
new runtime typing rule. -/
theorem Typing.erase (h : Typing K ctx input ty) : RuntimeTyping.RunWT ctx input.erase ty := by
  induction h with
  | complete hemb _ htyping =>
      rw [← Input.toCore_erase _ hemb]
      exact htyping.erase_preserves_typing
  | primLit h => simpa only [Expr.erase] using h.erase_preserves_typing
  | primBinOp h => simpa only [Expr.erase] using h.erase_preserves_typing
  | lambda hlc _ _ _ ih =>
      exact .lambda hlc ih
  | app _ _ ihf ihx => exact .app ihf ihx
  | letIn hwf _ _ _ _ ihrhs ihbody =>
      exact .letIn hwf ihrhs ihbody
  | var hlook hlc hinst => exact .var hlook hlc hinst
  | ctor hlook hlc hinst => exact .ctor hlook hlc hinst

mutual
/-- Instantiate a template at a local inference visit. No authored IDs or
cross-copy allocation table participate in this operation. -/
def Template.allocate (frontier : Nat) : Template → Nat × Ty
  | .fixed ty => (frontier, ty)
  | .hole => (frontier + 1, .fvar frontier)
  | .arrow a b =>
      let (next, ta) := a.allocate frontier
      let (last, tb) := b.allocate next
      (last, .arrow ta tb)
  | .custom name args =>
      let (next, tys) := allocateList frontier args
      (next, .customTy name tys)
def allocateList (frontier : Nat) : List Template → Nat × List Ty
  | [] => (frontier, [])
  | template :: rest =>
      let (next, ty) := template.allocate frontier
      let (last, tys) := allocateList next rest
      (last, ty :: tys)
end

mutual
theorem Template.allocate_fits (template : Template) (frontier : Nat) :
    template.Fits (template.allocate frontier).2 := by
  cases template with
  | fixed => exact .fixed
  | hole => exact .hole
  | arrow a b =>
      exact .arrow (a.allocate_fits frontier) (b.allocate_fits (a.allocate frontier).1)
  | custom name args => exact .custom (allocateList_fits args frontier)
theorem allocateList_fits (templates : List Template) (frontier : Nat) :
    List.Forall₂ Template.Fits templates (allocateList frontier templates).2 := by
  cases templates with
  | nil => exact .nil
  | cons template rest =>
      exact .cons (template.allocate_fits frontier) (allocateList_fits rest (template.allocate frontier).1)
end

mutual
theorem Template.Fits.onSubst_fixes {K : List Nat} {template : Template} {ty : Ty}
    (h : template.Fits ty) (hfixed : ∀ v ∈ template.rigidVars, v ∈ K)
    {subst : Subst} (hsubst : ∀ v ∈ K, subst.onTy (.fvar v) = .fvar v) :
    template.Fits (subst.onTy ty) := by
  cases h with
  | fixed =>
      have heq : subst.onTy ty = ty := Subst.onTy_eq_self_of_fixes
        (fun v hv => hsubst v (hfixed v hv))
      rw [heq]
      exact .fixed
  | hole => exact .hole
  | @arrow a ta b tb ha hb =>
      simpa only [Subst.onTy_arrow] using Template.Fits.arrow (ha.onSubst_fixes (fun v hv => hfixed v (List.mem_append_left _ hv)) hsubst)
        (hb.onSubst_fixes (fun v hv => hfixed v (List.mem_append_right _ hv)) hsubst)
  | custom hall =>
      simpa only [Subst.onTy_customTy] using Template.Fits.custom (fitsList_onSubst_fixes hall hfixed hsubst)
theorem fitsList_onSubst_fixes {K : List Nat} {templates : List Template} {types : List Ty}
    (h : List.Forall₂ Template.Fits templates types)
    (hfixed : ∀ v ∈ rigidVarsList templates, v ∈ K)
    {subst : Subst} (hsubst : ∀ v ∈ K, subst.onTy (.fvar v) = .fvar v) :
    List.Forall₂ Template.Fits templates (types.map subst.onTy) := by
  cases h with
  | nil => exact .nil
  | cons head rest =>
      exact .cons (head.onSubst_fixes (fun v hv => hfixed v (List.mem_append_left _ hv)) hsubst)
        (fitsList_onSubst_fixes rest (fun v hv => hfixed v (List.mem_append_right _ hv)) hsubst)
end

theorem LetAnn.FitsMono.onSubst_fixes {K : List Nat} {ann : LetAnn} {ty : Ty}
    (h : ann.FitsMono ty)
    (hfixed : ∀ template, ann = .template template → ∀ v ∈ template.rigidVars, v ∈ K)
    {subst : Subst} (hsubst : ∀ v ∈ K, subst.onTy (.fvar v) = .fvar v) :
    ann.FitsMono (subst.onTy ty) := by
  cases ann with
  | absent => trivial
  | template template => exact Template.Fits.onSubst_fixes h (hfixed template rfl) hsubst
  | complete => exact False.elim h
  | partialForall => exact False.elim h

theorem Template.Fits.onSubst {K : List Nat} {template : Template} {ty : Ty}
    (h : template.Fits ty) (hfixed : ∀ v ∈ template.rigidVars, v ∈ K)
    {subst : Subst} (hsubst : ∀ pair ∈ subst, pair.1 ∉ K) :
    template.Fits (subst.onTy ty) :=
  h.onSubst_fixes hfixed (Subst.fixes_of_dom_avoids hsubst)

theorem LetAnn.FitsMono.onSubst {K : List Nat} {ann : LetAnn} {ty : Ty}
    (h : ann.FitsMono ty)
    (hfixed : ∀ template, ann = .template template → ∀ v ∈ template.rigidVars, v ∈ K)
    {subst : Subst} (hsubst : ∀ pair ∈ subst, pair.1 ∉ K) :
    ann.FitsMono (subst.onTy ty) :=
  h.onSubst_fixes hfixed (Subst.fixes_of_dom_avoids hsubst)

/-- Whole-substitution transport requires pointwise protection of fixed syntax.
Sequential substitutions may mention K internally while their composite fixes K. -/
theorem Typing.onSubst_fixes (h : Typing K ctx input ty) (subst : Subst)
    (hlc : ∀ pair ∈ subst, pair.2.IsLC)
    (hprotected : ∀ v ∈ K, subst.onTy (.fvar v) = .fvar v) :
    Typing K (subst.onCtx ctx) input (subst.onTy ty) := by
  induction h with
  | complete hemb hrigid htyping =>
      exact .complete hemb hrigid (TypeOfHM.onSubst_fixed subst hlc
        (Expr.substTyFvars_eq_self_of_fixes (fun v hv => hprotected v (hrigid v hv))) htyping)
  | primLit htyping =>
      exact .primLit (TypeOfHM.onSubst_fixed subst hlc
        (Expr.substTyFvars_eq_self_of_tyFreeVars_nil _ rfl) htyping)
  | primBinOp htyping =>
      exact .primBinOp (TypeOfHM.onSubst_fixed subst hlc
        (Expr.substTyFvars_eq_self_of_tyFreeVars_nil _ rfl) htyping)
  | lambda hparam hfit hrigid _ ihbody =>
      simp only [Subst.onTy_arrow]
      refine .lambda (Subst.onTy_lc hlc hparam) ?_ hrigid ?_
      · intro template heq
        exact (hfit template heq).onSubst_fixes (hrigid template heq) hprotected
      · simpa only [Subst.onCtx, Subst.onEnv, List.map_cons, Subst.onPolyTy,
          PolyTy.mkTrivial] using ihbody
  | app _ _ ihf ihx =>
      simp only [Subst.onTy_arrow] at ihf ⊢
      exact .app ihf ihx
  | @letIn ctx ann rhs body bodyTy scheme avoid hwf hrigid hfit hgeneral hbody ihgeneral ihbody =>
      let avoid' := avoid ++ subst.map Prod.fst
      have oldFresh : ∀ fresh, FreshNames avoid' scheme.paramCount fresh → FreshNames avoid scheme.paramCount fresh :=
        fun fresh hf => ⟨hf.length, hf.nodup, fun v hv ha => hf.avoid v hv (List.mem_append_left _ ha)⟩
      have domFresh : ∀ fresh, FreshNames avoid' scheme.paramCount fresh → ∀ pair ∈ subst, pair.1 ∉ fresh := by
        intro fresh hf pair hp hv
        exact hf.avoid pair.1 hv (List.mem_append_right _ (List.mem_map.mpr ⟨pair, hp, rfl⟩))
      refine Typing.letIn (M := subst.onPolyTy scheme) (L := avoid')
        (Subst.onPolyTy_wf hlc hwf) hrigid ?_ ?_ ?_
      · intro fresh hf
        have hs := (hfit fresh (oldFresh fresh hf)).onSubst_fixes hrigid hprotected
        simpa only [PolyTy.openVars, Subst.onPolyTy,
          Subst.onTy_openVars hlc (domFresh fresh hf)] using hs
      · intro fresh hf
        simpa only [PolyTy.openVars, Subst.onPolyTy,
          Subst.onTy_openVars hlc (domFresh fresh hf)] using ihgeneral fresh (oldFresh fresh hf)
      · simpa only [Subst.onCtx, Subst.onEnv, List.map_cons] using ihbody
  | var hlookup hargs hinst =>
      exact .complete rfl (by simp [Expr.tyFreeVars]) (TypeOfHM.onSubst_fixed subst hlc
        (Expr.substTyFvars_eq_self_of_tyFreeVars_nil _ rfl) (.var hlookup hargs hinst))
  | ctor hlookup hargs hinst =>
      exact .complete rfl (by simp [Expr.tyFreeVars]) (TypeOfHM.onSubst_fixed subst hlc
        (Expr.substTyFvars_eq_self_of_tyFreeVars_nil _ rfl) (.ctor hlookup hargs hinst))

theorem Typing.onSubst (h : Typing K ctx input ty) (subst : Subst)
    (hlc : ∀ pair ∈ subst, pair.2.IsLC) (hprotected : ∀ pair ∈ subst, pair.1 ∉ K) :
    Typing K (subst.onCtx ctx) input (subst.onTy ty) :=
  h.onSubst_fixes subst hlc (Subst.fixes_of_dom_avoids hprotected)

theorem Typing.regular (h : Typing K ctx input ty) : ty.IsLC := h.erase.regular

/-- Simultaneous fresh opening of an ordinary partial binding's monotype. The
input syntax stays unchanged because every fixed annotation variable is in K. -/
theorem Typing.generalise {ann : LetAnn} {names : List Nat} (h : Typing K ctx input ty)
    (hfit : ann.FitsMono ty)
    (hrigid : ∀ template, ann = .template template → ∀ v ∈ template.rigidVars, v ∈ K)
    (hnames : names.Nodup) (hctx : ∀ name ∈ names, name ∉ ctx.env.freeVars)
    (hprotected : ∀ name ∈ names, name ∉ K) :
    ∀ fresh, FreshNames names names.length fresh →
      ann.FitsMono (Ty.openVars fresh (Ty.closeOver names ty)) ∧
      Typing K ctx input (Ty.openVars fresh (Ty.closeOver names ty)) := by
  intro fresh hfresh
  let rename : Subst := names.zip (fresh.map Ty.fvar)
  have hdom : ∀ pair ∈ rename, pair.1 ∉ K :=
    fun pair hp => hprotected pair.1 (List.of_mem_zip hp).1
  have hlc : ∀ pair ∈ rename, pair.2.IsLC := by
    intro pair hp
    obtain ⟨name, _, heq⟩ := List.mem_map.mp (List.of_mem_zip hp).2
    rw [← heq]
    exact .fvar
  have hctxfix : rename.onCtx ctx = ctx := by
    cases ctx with
    | mk env ctors =>
        exact congrArg (fun env => Ctx.mk env ctors)
          (Subst.onEnv_eq_self_of_fresh (fun pair hp => hctx pair.1 (List.of_mem_zip hp).1))
  rw [Ty.openVars_closeOver_rename h.regular hnames hfresh.length
    (fun name hn hf => hfresh.avoid name hf hn)]
  refine ⟨hfit.onSubst hrigid hdom, ?_⟩
  have hrenamed := h.onSubst rename hlc hdom
  rwa [hctxfix] at hrenamed

/-- Transport both independent ordinary-let premises through a whole ambient
specialization, freshening opening names away from its domain. -/
theorem Typing.binding_onSubst_fixes {ann : LetAnn} {scheme : PolyTy} {avoid : List Nat}
    (hfit : ∀ fresh, FreshNames avoid scheme.paramCount fresh → ann.FitsMono (scheme.openVars fresh))
    (htyping : ∀ fresh, FreshNames avoid scheme.paramCount fresh → Typing K ctx input (scheme.openVars fresh))
    (hrigid : ∀ template, ann = .template template → ∀ v ∈ template.rigidVars, v ∈ K)
    (subst : Subst) (hlc : ∀ pair ∈ subst, pair.2.IsLC)
    (hprotected : ∀ v ∈ K, subst.onTy (.fvar v) = .fvar v) :
    ∃ avoid',
      (∀ fresh, FreshNames avoid' scheme.paramCount fresh → ann.FitsMono ((subst.onPolyTy scheme).openVars fresh)) ∧
      (∀ fresh, FreshNames avoid' scheme.paramCount fresh →
        Typing K (subst.onCtx ctx) input ((subst.onPolyTy scheme).openVars fresh)) := by
  let avoid' := avoid ++ subst.map Prod.fst
  have hstep : ∀ fresh, FreshNames avoid' scheme.paramCount fresh →
      ann.FitsMono ((subst.onPolyTy scheme).openVars fresh) ∧
      Typing K (subst.onCtx ctx) input ((subst.onPolyTy scheme).openVars fresh) := by
    intro fresh hf
    have hold : FreshNames avoid scheme.paramCount fresh :=
      ⟨hf.length, hf.nodup, fun v hv ha => hf.avoid v hv (List.mem_append_left _ ha)⟩
    have hdom : ∀ pair ∈ subst, pair.1 ∉ fresh := by
      intro pair hp hv
      exact hf.avoid pair.1 hv (List.mem_append_right _ (List.mem_map.mpr ⟨pair, hp, rfl⟩))
    have hfit' := (hfit fresh hold).onSubst_fixes hrigid hprotected
    have htyping' := (htyping fresh hold).onSubst_fixes subst hlc hprotected
    simpa only [PolyTy.openVars, Subst.onPolyTy, Subst.onTy_openVars hlc hdom] using And.intro hfit' htyping'
  exact ⟨avoid', fun fresh hf => (hstep fresh hf).1, fun fresh hf => (hstep fresh hf).2⟩

theorem Typing.binding_onSubst {ann : LetAnn} {scheme : PolyTy} {avoid : List Nat}
    (hfit : ∀ fresh, FreshNames avoid scheme.paramCount fresh → ann.FitsMono (scheme.openVars fresh))
    (htyping : ∀ fresh, FreshNames avoid scheme.paramCount fresh → Typing K ctx input (scheme.openVars fresh))
    (hrigid : ∀ template, ann = .template template → ∀ v ∈ template.rigidVars, v ∈ K)
    (subst : Subst) (hlc : ∀ pair ∈ subst, pair.2.IsLC)
    (hprotected : ∀ pair ∈ subst, pair.1 ∉ K) :
    ∃ avoid',
      (∀ fresh, FreshNames avoid' scheme.paramCount fresh → ann.FitsMono ((subst.onPolyTy scheme).openVars fresh)) ∧
      (∀ fresh, FreshNames avoid' scheme.paramCount fresh →
        Typing K (subst.onCtx ctx) input ((subst.onPolyTy scheme).openVars fresh)) :=
  Typing.binding_onSubst_fixes hfit htyping hrigid subst hlc (Subst.fixes_of_dom_avoids hprotected)

end Anonymous
