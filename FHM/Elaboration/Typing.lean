import FHM.CoreBackend.Complete
import FHM.Elaboration.Input

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

private theorem annList_subst_image {S : Subst} {w : Nat}
    (anns : List (Option PolyTy))
    (h : w ∈ Expr.tyFreeVars.AnnList.tyFreeVars (anns.map (RecAnn.substFvars S))) :
    ∃ k ∈ Expr.tyFreeVars.AnnList.tyFreeVars anns, w ∈ (S.onTy (.fvar k)).freeVars := by
  induction anns with
  | nil => simp [Expr.tyFreeVars.AnnList.tyFreeVars] at h
  | cons ann rest ih =>
    cases ann with
    | none =>
      simp only [List.map_cons, RecAnn.substFvars_none, Expr.tyFreeVars.AnnList.tyFreeVars,
        Option.elim, List.nil_append] at h ⊢
      exact ih h
    | some scheme =>
      simp only [List.map_cons, RecAnn.substFvars_some, Expr.tyFreeVars.AnnList.tyFreeVars,
        Option.elim, List.mem_append, PolyTy.body_substFvars] at h ⊢
      rcases h with h | h
      · obtain ⟨k, hk, hv⟩ := Ty.mem_freeVars_substFvars_image.mp h
        exact ⟨k, Or.inl hk, hv⟩
      · obtain ⟨k, hk, hv⟩ := ih h
        exact ⟨k, Or.inr hk, hv⟩

/-- Every annotation variable after substitution comes from the substituted
image of an annotation variable of the original expression. -/
theorem Expr.mem_tyFreeVars_substTyFvars_image {S : Subst} {w : Nat} {e : Expr}
    (h : w ∈ (e.substTyFvars S).tyFreeVars) :
    ∃ k ∈ e.tyFreeVars, w ∈ (S.onTy (.fvar k)).freeVars := by
  induction e using Expr.rec_strong with
  | primLit p =>
    rw [Expr.substTyFvars_eq_self_of_not_mem_tyFreeVars (by simp [Expr.tyFreeVars])] at h
    simp [Expr.tyFreeVars] at h
  | primBinOp op =>
    rw [Expr.substTyFvars_eq_self_of_not_mem_tyFreeVars (by simp [Expr.tyFreeVars])] at h
    simp [Expr.tyFreeVars] at h
  | ctor c =>
    rw [Expr.substTyFvars_eq_self_of_not_mem_tyFreeVars (by simp [Expr.tyFreeVars])] at h
    simp [Expr.tyFreeVars] at h
  | var i => simp [Expr.substTyFvars_var, Expr.tyFreeVars] at h
  | lambda ann body ih =>
    rw [Expr.substTyFvars_lambda] at h
    cases ann with
    | none =>
      simp only [Expr.tyFreeVars, Option.map_none, Option.elim_none, List.nil_append] at h ⊢
      exact ih h
    | some t =>
      simp only [Expr.tyFreeVars, Option.map_some, Option.elim_some, List.mem_append] at h ⊢
      rcases h with h | h
      · obtain ⟨k, hk, hv⟩ := Ty.mem_freeVars_substFvars_image.mp h
        exact ⟨k, Or.inl hk, hv⟩
      · obtain ⟨k, hk, hv⟩ := ih h
        exact ⟨k, Or.inr hk, hv⟩
  | app f arg ihf iha =>
    rw [Expr.substTyFvars_app] at h
    simp only [Expr.tyFreeVars, List.mem_append] at h ⊢
    rcases h with h | h
    · obtain ⟨k, hk, hv⟩ := ihf h
      exact ⟨k, Or.inl hk, hv⟩
    · obtain ⟨k, hk, hv⟩ := iha h
      exact ⟨k, Or.inr hk, hv⟩
  | letIn ann rhs body ihr ihb =>
    rw [Expr.substTyFvars_letIn] at h
    cases ann with
    | none =>
      simp only [Expr.tyFreeVars, Option.map_none, Option.elim_none, List.nil_append,
        List.mem_append] at h ⊢
      rcases h with h | h
      · obtain ⟨k, hk, hv⟩ := ihr h
        exact ⟨k, Or.inl hk, hv⟩
      · obtain ⟨k, hk, hv⟩ := ihb h
        exact ⟨k, Or.inr hk, hv⟩
    | some scheme =>
      simp only [Expr.tyFreeVars, Option.map_some, Option.elim_some, List.mem_append] at h ⊢
      rcases h with (h | h) | h
      · obtain ⟨k, hk, hv⟩ := Ty.mem_freeVars_substFvars_image.mp h
        exact ⟨k, Or.inl (Or.inl hk), hv⟩
      · obtain ⟨k, hk, hv⟩ := ihr h
        exact ⟨k, Or.inl (Or.inr hk), hv⟩
      · obtain ⟨k, hk, hv⟩ := ihb h
        exact ⟨k, Or.inr hk, hv⟩
  | match_ scrut branches ihs ihbs =>
    rw [Expr.substTyFvars_match] at h
    simp only [Expr.tyFreeVars, List.mem_append] at h ⊢
    rcases h with h | h
    · obtain ⟨k, hk, hv⟩ := ihs h
      exact ⟨k, Or.inl hk, hv⟩
    · obtain ⟨branch, hb, hv⟩ := Expr.mem_branchListTyFreeVars h
      obtain ⟨⟨p, body⟩, hsource, rfl⟩ := List.mem_map.mp hb
      obtain ⟨k, hk, hv⟩ := ihbs p body hsource hv
      exact ⟨k, Or.inr (Expr.mem_branchListTyFreeVars_of hsource hk), hv⟩
  | letRec anns bindings body ihbs ihb =>
    rw [Expr.substTyFvars_letRec] at h
    simp only [Expr.tyFreeVars, List.mem_append] at h ⊢
    rcases h with (h | h) | h
    · obtain ⟨k, hk, hv⟩ := annList_subst_image anns h
      exact ⟨k, Or.inl (Or.inl hk), hv⟩
    · obtain ⟨output, ho, hv⟩ := Expr.mem_recGroupTyFreeVars h
      obtain ⟨source, hs, rfl⟩ := List.mem_map.mp ho
      obtain ⟨k, hk, hv⟩ := ihbs source hs hv
      exact ⟨k, Or.inl (Or.inr (Expr.mem_recGroupTyFreeVars_of hs hk)), hv⟩
    · obtain ⟨k, hk, hv⟩ := ihb h
      exact ⟨k, Or.inr hk, hv⟩

namespace Elaboration



mutual
theorem Template.toCore_rigidVars {template : Template} {ty : Ty}
    (h : template.toCore = some ty) (v : Nat) : v ∈ template.rigidVars ↔ v ∈ ty.freeVars := by
  cases template with
  | fixed => cases h; rfl
  | hole => cases h
  | arrow a b =>
    simp only [Template.toCore, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨ta, ha, tb, hb, rfl⟩ := h
    simp only [Template.rigidVars, Ty.freeVars, List.mem_append, List.mem_dedup,
      Template.toCore_rigidVars ha, Template.toCore_rigidVars hb]
  | custom name args =>
    simp only [Template.toCore, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨tys, ht, rfl⟩ := h
    simpa only [Template.rigidVars, Ty.freeVars, TyList.mem_freeVars_iff, List.mem_flatMap] using completeTypes_rigidVars ht v
theorem completeTypes_rigidVars {templates : List Template} {tys : List Ty}
    (h : completeTypes templates = some tys) (v : Nat) :
    v ∈ rigidVarsList templates ↔ v ∈ tys.flatMap Ty.freeVars := by
  cases templates with
  | nil => cases h; rfl
  | cons t ts =>
    simp only [completeTypes, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨ty, ht, tys, hts, rfl⟩ := h
    simp only [rigidVarsList, List.flatMap_cons, List.mem_append,
      Template.toCore_rigidVars ht, completeTypes_rigidVars hts]
end


private theorem completeLambdaAnn_rigidVars {ann : Option Template} {core : Option Ty}
    (h : completeLambdaAnn ann = some core) (v : Nat) :
    v ∈ ann.elim [] Template.rigidVars ↔ v ∈ core.elim [] Ty.freeVars := by
  cases ann with
  | none => cases h; rfl
  | some template =>
    simp only [completeLambdaAnn, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨ty, ht, rfl⟩ := h
    exact Template.toCore_rigidVars ht v

private theorem LetAnn.toCore_rigidVars {ann : LetAnn} {core : Option PolyTy}
    (h : ann.toCore = some core) (v : Nat) :
    v ∈ ann.rigidVars ↔ v ∈ core.elim [] (fun scheme => scheme.body.freeVars) := by
  cases ann with
  | absent => cases h; rfl
  | complete scheme => cases h; rfl
  | template _ => cases h
  | partialForall _ _ => cases h

private theorem completeAnns_rigidVars (anns : List LetAnn) {cores : List (Option PolyTy)}
    (h : completeAnns anns = some cores) (v : Nat) :
    v ∈ anns.flatMap LetAnn.rigidVars ↔ v ∈ Expr.tyFreeVars.AnnList.tyFreeVars cores := by
  cases anns with
  | nil => cases h; rfl
  | cons ann rest =>
    simp only [completeAnns, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨core, ha, cores, hr, rfl⟩ := h
    simp only [List.flatMap_cons, Expr.tyFreeVars.AnnList.tyFreeVars, List.mem_append,
      LetAnn.toCore_rigidVars ha v, completeAnns_rigidVars rest hr v]

mutual
/-- Conservative embedding preserves exactly the authored free type variables,
including all complete signature binders, branches, and recursive RHSs. -/
theorem Input.toCore_rigidVars (input : Input) {core : Expr}
    (h : input.toCore = some core) (v : Nat) : v ∈ input.rigidVars ↔ v ∈ core.tyFreeVars := by
  cases input with
  | primLit p => cases h; rfl
  | primBinOp op => cases h; rfl
  | var index => cases h; rfl
  | ctor name => cases h; rfl
  | lambda ann body =>
    simp only [Input.toCore, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨ann', ha, body', hb, rfl⟩ := h
    simp only [Input.rigidVars, Expr.tyFreeVars, List.mem_append,
      completeLambdaAnn_rigidVars ha v, body.toCore_rigidVars hb v]
  | app f arg =>
    simp only [Input.toCore, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨f', hf, arg', ha, rfl⟩ := h
    simp only [Input.rigidVars, Expr.tyFreeVars, List.mem_append,
      f.toCore_rigidVars hf v, arg.toCore_rigidVars ha v]
  | letIn ann rhs body =>
    simp only [Input.toCore, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨ann', ha, rhs', hr, body', hb, rfl⟩ := h
    simp only [Input.rigidVars, Expr.tyFreeVars, List.mem_append,
      LetAnn.toCore_rigidVars ha v, rhs.toCore_rigidVars hr v, body.toCore_rigidVars hb v]
  | match_ scrut branches =>
    simp only [Input.toCore, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨scrut', hs, branches', hb, rfl⟩ := h
    simp only [Input.rigidVars, Expr.tyFreeVars, List.mem_append,
      scrut.toCore_rigidVars hs v, completeBranches_rigidVars branches hb v]
  | letRec anns bindings body =>
    simp only [Input.toCore, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨anns', ha, bindings', hr, body', hb, rfl⟩ := h
    simp only [Input.rigidVars, Expr.tyFreeVars, List.mem_append,
      completeAnns_rigidVars anns ha v, completeBindings_rigidVars bindings hr v,
      body.toCore_rigidVars hb v]

theorem completeBranches_rigidVars (branches : List (MatchPattern × Input))
    {cores : List (MatchPattern × Expr)} (h : completeBranches branches = some cores) (v : Nat) :
    v ∈ rigidBranchVars branches ↔ v ∈ Expr.tyFreeVars.BranchList.tyFreeVars cores := by
  cases branches with
  | nil => cases h; rfl
  | cons head rest =>
    rcases head with ⟨pat, body⟩
    simp only [completeBranches, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨body', hb, rest', hr, rfl⟩ := h
    simp only [rigidBranchVars, Expr.tyFreeVars.BranchList.tyFreeVars, List.mem_append,
      body.toCore_rigidVars hb v, completeBranches_rigidVars rest hr v]

theorem completeBindings_rigidVars (bindings : List Input) {cores : List Expr}
    (h : completeBindings bindings = some cores) (v : Nat) :
    v ∈ rigidBindingVars bindings ↔ v ∈ Expr.tyFreeVars.RecGroup.tyFreeVars cores := by
  cases bindings with
  | nil => cases h; rfl
  | cons body rest =>
    simp only [completeBindings, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨body', hb, rest', hr, rfl⟩ := h
    simp only [rigidBindingVars, Expr.tyFreeVars.RecGroup.tyFreeVars, List.mem_append,
      body.toCore_rigidVars hb v, completeBindings_rigidVars rest hr v]
end


/-- A signed completion preserves the written forall prefix. Partial signatures
may additionally quantify independent inferred variables after that prefix. -/
inductive LetAnn.SignatureFits : LetAnn → PolyTy → List Nat → Prop
  | complete : SignatureFits (.complete scheme) scheme names
  | partialSignature {scheme : PolyTy} {template : Template} {count : Nat} {names : List Nat} :
      count ≤ scheme.paramCount →
      (template.openTyVarsFrom 0 (names.take count)).Fits (scheme.openVars names) →
      SignatureFits (.partialForall count template) scheme names

theorem LetAnn.SignatureFits.prefix_le {ann : LetAnn} {scheme : PolyTy} {names : List Nat}
    (h : ann.SignatureFits scheme names) : ann.paramCount ≤ scheme.paramCount := by
  cases h with
  | complete => exact Nat.le_refl _
  | partialSignature h _ => exact h

/-- Structural branch completion preserves patterns and completes each body. -/
inductive CompletedBranches (J : List Nat → Input → Expr → Prop) :
    List Nat → List (MatchPattern × Input) → List (MatchPattern × Expr) → Prop
  | nil : CompletedBranches J K [] []
  | cons {source : Input} {output : Expr} {K : List Nat} :
      J K source output → CompletedBranches J K rest restOut →
      CompletedBranches J K ((pat, source) :: rest) ((pat, output) :: restOut)

/-- Structural annotation completion. This is distinct from input admissibility
(`Typing` below): it records fixed syntax, individual hole fillings, and the
type abstraction/specialization performed when an ordinary let is generalized.
Protected fixed variables cannot be substituted or captured by new binders.
Scope correctness of the resulting Core is supplied by output typing. -/
inductive Completes : List Nat → Input → Expr → Prop
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
  | match_ : Completes K scrut scrutOut →
      CompletedBranches Completes K branches branchesOut →
      Completes K (.match_ scrut branches) (.match_ scrutOut branchesOut)

/-- Independent branch semantics reuse the ordinary constructor specification;
the body relation is a parameter, with no inference state or substitution. -/
inductive BranchTyping (J : List Nat → Ctx → Input → Ty → Prop) :
    List Nat → Ctx → (MatchPattern × Input) → Ty → Ty → Prop
  | named : BranchCtorSpec ctx.ctors name count scrutTy ctor args fields →
      J K { ctx with env := fields.map PolyTy.mkTrivial ++ ctx.env } body resultTy →
      BranchTyping J K ctx (.named name count, body) scrutTy resultTy
  | wildcard : J K ctx body resultTy → BranchTyping J K ctx (.wildcard, body) scrutTy resultTy

/-- Independent input typing for the first fragment. `K` contains ambient rigid
annotation variables; free variables in context monotypes can remain flexible.
 The let rule generalises
the RHS cofinally, and partial annotations constrain that very monotype. There
is no recursive rule: in particular, a partial annotation cannot acquire
polymorphic recursive uses through an arbitrary completed output signature.

Whole completed subtrees use their existing checking rules through the
conservative Core embedding. Complete annotated lets with partial syntax
in their RHS or continuation, and partial recursive spines, have no rule
in this first fragment.
-/
inductive Typing : List Nat → Ctx → Input → Ty → Prop
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
  | match_ : Typing K ctx scrut scrutTy → branches ≠ [] →
      (∀ branch ∈ branches, BranchTyping Typing K ctx branch scrutTy resultTy) →
      Typing K ctx (.match_ scrut branches) resultTy

private theorem erasedBranches_eq_map (branches : List (MatchPattern × Input)) :
    eraseBranches branches = branches.map (fun branch => (branch.1, branch.2.erase)) := by
  induction branches with
  | nil => rfl
  | cons head rest ih => rcases head with ⟨p, b⟩; simp only [eraseBranches, List.map_cons, ih]

/-- The input specification has the ordinary HM runtime meaning independently
of elaboration. Annotation matching restricts this meaning; it never grants a
new runtime typing rule. -/
theorem Typing.erase (h : Typing K ctx input ty) : RuntimeTyping.RunWT ctx input.erase ty := by
  induction h using Typing.rec
      (motive_2 := fun K ctx branch scrutTy resultTy _ =>
        RuntimeTyping.RunWTMatchBranch ctx (branch.1, branch.2.erase) scrutTy resultTy) with
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

  | match_ _ hne _ ihscrut ihbranches =>
    expose_names
    simp only [Input.erase]
    rw [erasedBranches_eq_map]
    refine .match_ ihscrut ?_ ?_
    · intro hempty
      exact hne (List.map_eq_nil_iff.mp hempty)
    · intro branch hb
      obtain ⟨source, hsource, rfl⟩ := List.mem_map.mp hb
      exact ihbranches source hsource
  | named hspec _ ihbody => exact .mk hspec ihbody
  | wildcard _ ihbody => exact .wildcard ihbody

/-- Independently typed branch bodies retain ordinary erased branch semantics. -/
theorem BranchTyping.erase (h : BranchTyping Typing K ctx branch scrutTy resultTy) :
    RuntimeTyping.RunWTMatchBranch ctx (branch.1, branch.2.erase) scrutTy resultTy := by
  cases h with
  | named hspec hbody => exact .mk hspec hbody.erase
  | wildcard hbody => exact .wildcard hbody.erase

mutual
/-- Simultaneously transform the authored template and its instance. -/
theorem Template.Fits.substTyFvars {template : Template} {ty : Ty}
    (h : template.Fits ty) (subst : Subst) :
    (template.substTyFvars subst).Fits (subst.onTy ty) := by
  cases h with
  | fixed => exact .fixed
  | hole => exact .hole
  | arrow ha hb =>
      simpa only [Template.substTyFvars, Subst.onTy_arrow] using
        (Template.Fits.arrow (ha.substTyFvars subst) (hb.substTyFvars subst))
  | custom hargs =>
      simpa only [Template.substTyFvars, Subst.onTy_customTy] using
        (Template.Fits.custom (fitsList_substTyFvars hargs subst))
theorem fitsList_substTyFvars {templates : List Template} {tys : List Ty}
    (h : List.Forall₂ Template.Fits templates tys) (subst : Subst) :
    List.Forall₂ Template.Fits (substTemplateList subst templates) (tys.map subst.onTy) := by
  cases h with
  | nil => exact .nil
  | cons hh ht => exact .cons (hh.substTyFvars subst) (fitsList_substTyFvars ht subst)
end

theorem Template.Fits.onSubst_fixes {K : List Nat} {template : Template} {ty : Ty}
    (h : template.Fits ty) (hfixed : ∀ v ∈ template.rigidVars, v ∈ K)
    {subst : Subst} (hsubst : ∀ v ∈ K, subst.onTy (.fvar v) = .fvar v) :
    template.Fits (subst.onTy ty) := by
  have ht := h.substTyFvars subst
  rwa [template.substTyFvars_eq_self_of_fixes (fun v hv => hsubst v (hfixed v hv))] at ht

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

/-- Constructor branch witnesses transport with LC substitutions; constructor
field declarations themselves are closed and therefore unchanged. -/
theorem _root_.BranchCtorSpec.onSubst {ctors : CtorEnv} {name : CtorName} {count : Nat}
    {scrutTy : Ty} {ctor : Ctor} {args fields : List Ty}
    (h : BranchCtorSpec ctors name count scrutTy ctor args fields)
    (subst : Subst) (hlc : ∀ pair ∈ subst, pair.2.IsLC) :
    BranchCtorSpec ctors name count (subst.onTy scrutTy) ctor
      (args.map subst.onTy) (fields.map subst.onTy) := by
  induction subst generalizing scrutTy args fields with
  | nil =>
    change BranchCtorSpec ctors name count scrutTy ctor (args.map id) (fields.map id)
    simpa only [List.map_id] using h
  | cons pair rest ih =>
    rcases pair with ⟨v, replacement⟩
    have hrepl := hlc (v, replacement) List.mem_cons_self
    have hfields := InstantiatesBy.forall2_substFvar (Z := v) (U := replacement) hrepl h.fields
    have hcontents : ctor.contents.map (Ty.substFvar v replacement) = ctor.contents := by
      apply List.map_eq_self_of_forall_eq_id
      intro field hf
      exact Ty.substFvar_fresh ((ctor.closed field hf).not_mem_freeVars v)
    rw [hcontents] at hfields
    have hstep : BranchCtorSpec ctors name count (Ty.substFvar v replacement scrutTy) ctor
        (args.map (Ty.substFvar v replacement)) (fields.map (Ty.substFvar v replacement)) :=
      ⟨h.lookup, by rw [h.scrut_eq]; simp only [Ty.substFvar, TyList.substFvar_eq_map],
        by simpa only [List.length_map] using h.arity, h.bind_count, hfields⟩
    have ht := ih hstep (fun pair hp => hlc pair (List.mem_cons_of_mem _ hp))
    simpa only [List.map_map, Function.comp_def, Subst.onTy, Ty.substFvars] using ht





mutual
/-- Each authored free variable after substitution comes from one original
fixed leaf variable's image; anonymous holes contribute no variables. -/
theorem Template.rigidVars_substTyFvars {template : Template} {subst : Subst} {v : Nat}
    (h : v ∈ (template.substTyFvars subst).rigidVars) :
    ∃ k ∈ template.rigidVars, v ∈ (subst.onTy (.fvar k)).freeVars := by
  cases template with
  | fixed ty => exact Ty.mem_freeVars_substFvars_image.mp h
  | hole => cases h
  | arrow a b =>
      rcases List.mem_append.mp h with ha | hb
      · obtain ⟨k, hk, hv⟩ := a.rigidVars_substTyFvars ha
        exact ⟨k, List.mem_append_left _ hk, hv⟩
      · obtain ⟨k, hk, hv⟩ := b.rigidVars_substTyFvars hb
        exact ⟨k, List.mem_append_right _ hk, hv⟩
  | custom name args => exact rigidVarsList_substTyFvars h
theorem rigidVarsList_substTyFvars {templates : List Template} {subst : Subst} {v : Nat}
    (h : v ∈ rigidVarsList (substTemplateList subst templates)) :
    ∃ k ∈ rigidVarsList templates, v ∈ (subst.onTy (.fvar k)).freeVars := by
  cases templates with
  | nil => cases h
  | cons t ts =>
      rcases List.mem_append.mp h with ht | hts
      · obtain ⟨k, hk, hv⟩ := t.rigidVars_substTyFvars ht
        exact ⟨k, List.mem_append_left _ hk, hv⟩
      · obtain ⟨k, hk, hv⟩ := rigidVarsList_substTyFvars hts
        exact ⟨k, List.mem_append_right _ hk, hv⟩
end

theorem LetAnn.rigidVars_substTyFvars {ann : LetAnn} {subst : Subst} {v : Nat}
    (h : v ∈ (ann.substTyFvars subst).rigidVars) :
    ∃ k ∈ ann.rigidVars, v ∈ (subst.onTy (.fvar k)).freeVars := by
  cases ann with
  | absent => cases h
  | complete scheme => exact Ty.mem_freeVars_substFvars_image.mp h
  | template t => exact t.rigidVars_substTyFvars h
  | partialForall n t => exact t.rigidVars_substTyFvars h


private theorem fitsMono_sourceSubst {ann : LetAnn} {ty : Ty}
    (h : ann.FitsMono ty) (subst : Subst) :
    (ann.substTyFvars subst).FitsMono (subst.onTy ty) := by
  cases ann with
  | absent => trivial
  | template t => exact h.substTyFvars subst
  | complete _ => cases h
  | partialForall _ _ => cases h

private theorem template_scope_sourceSubst {K K' : List Nat} {template : Template}
    {subst : Subst} (hrigid : ∀ v ∈ template.rigidVars, v ∈ K)
    (hscope : ∀ k ∈ K, ∀ v ∈ (subst.onTy (.fvar k)).freeVars, v ∈ K') :
    ∀ v ∈ (template.substTyFvars subst).rigidVars, v ∈ K' := by
  intro v hv
  obtain ⟨k, hk, hv⟩ := template.rigidVars_substTyFvars hv
  exact hscope k (hrigid k hk) v hv

private theorem substInputBranches_eq_map (subst : Subst) (branches : List (MatchPattern × Input)) :
    substInputBranches subst branches = branches.map (fun b => (b.1, b.2.substTyFvars subst)) := by
  induction branches with
  | nil => rfl
  | cons head rest ih => cases head; simp only [substInputBranches, List.map_cons, ih]

/-- Source-transforming substitution transports the independent judgment when
its authored variable images are scoped by the destination protected set. -/
theorem Typing.onSubst_source {K K' : List Nat} {ctx : Ctx} {input : Input} {ty : Ty}
    (h : Typing K ctx input ty) (subst : Subst)
    (hlc : ∀ pair ∈ subst, pair.2.IsLC)
    (hscope : ∀ k ∈ K, ∀ v ∈ (subst.onTy (.fvar k)).freeVars, v ∈ K') :
    Typing K' (subst.onCtx ctx) (input.substTyFvars subst) (subst.onTy ty) := by
  induction h using Typing.rec
      (motive_2 := fun K ctx branch scrutTy resultTy _ =>
        (∀ k ∈ K, ∀ v ∈ (subst.onTy (.fvar k)).freeVars, v ∈ K') →
          BranchTyping Typing K' (subst.onCtx ctx) (branch.1, branch.2.substTyFvars subst)
            (subst.onTy scrutTy) (subst.onTy resultTy)) with
  | complete hemb hrigid htyping =>
    refine .complete (Input.toCore_substTyFvars _ hemb subst) ?_ (htyping.onSubst subst hlc)
    intro v hv
    obtain ⟨k, hk, hv⟩ := Expr.mem_tyFreeVars_substTyFvars_image hv
    exact hscope k (hrigid k hk) v hv
  | primLit htyping =>
    exact .primLit (TypeOfHM.onSubst_fixed subst hlc
      (Expr.substTyFvars_eq_self_of_tyFreeVars_nil _ rfl) htyping)
  | primBinOp htyping =>
    exact .primBinOp (TypeOfHM.onSubst_fixed subst hlc
      (Expr.substTyFvars_eq_self_of_tyFreeVars_nil _ rfl) htyping)
  | @lambda ann K ctx body bodyTy paramTy hparam hfit hrigid _ ihbody =>
    simp only [Input.substTyFvars, Subst.onTy_arrow]
    refine .lambda (Subst.onTy_lc hlc hparam) ?_ ?_ ?_
    · intro template heq
      cases ann with
      | none => cases heq
      | some original =>
        cases heq
        exact (hfit original rfl).substTyFvars subst
    · intro template heq
      cases ann with
      | none => cases heq
      | some original =>
        cases heq
        exact template_scope_sourceSubst (hrigid original rfl) hscope
    · simpa only [Subst.onCtx, Subst.onEnv, List.map_cons, Subst.onPolyTy,
        PolyTy.mkTrivial] using ihbody hscope
  | app _ _ ihf ihx =>
    simp only [Input.substTyFvars, Subst.onTy_arrow] at ihf ⊢
    exact .app (ihf hscope) (ihx hscope)
  | @letIn ann K ctx rhs body bodyTy scheme avoid hwf hrigid hfit _ _ ihgeneral ihbody =>
    let avoid' := avoid ++ subst.map Prod.fst
    have oldFresh : ∀ fresh, FreshNames avoid' scheme.paramCount fresh → FreshNames avoid scheme.paramCount fresh :=
      fun fresh hf => ⟨hf.length, hf.nodup, fun v hv ha => hf.avoid v hv (List.mem_append_left _ ha)⟩
    have domFresh : ∀ fresh, FreshNames avoid' scheme.paramCount fresh → ∀ pair ∈ subst, pair.1 ∉ fresh := by
      intro fresh hf pair hp hv
      exact hf.avoid pair.1 hv (List.mem_append_right _ (List.mem_map.mpr ⟨pair, hp, rfl⟩))
    refine Typing.letIn (M := subst.onPolyTy scheme) (L := avoid')
      (Subst.onPolyTy_wf hlc hwf) ?_ ?_ ?_ ?_
    · intro template heq
      cases ann with
      | absent => cases heq
      | complete _ => cases heq
      | partialForall _ _ => cases heq
      | template original =>
        cases heq
        exact template_scope_sourceSubst (hrigid original rfl) hscope
    · intro fresh hf
      have hs := fitsMono_sourceSubst (hfit fresh (oldFresh fresh hf)) subst
      simpa only [PolyTy.openVars, Subst.onPolyTy,
        Subst.onTy_openVars hlc (domFresh fresh hf)] using hs
    · intro fresh hf
      simpa only [PolyTy.openVars, Subst.onPolyTy,
        Subst.onTy_openVars hlc (domFresh fresh hf)] using ihgeneral fresh (oldFresh fresh hf) hscope
    · simpa only [Subst.onCtx, Subst.onEnv, List.map_cons] using ihbody hscope
  | var hlookup hargs hinst =>
    exact .complete rfl (by simp [Expr.tyFreeVars]) (TypeOfHM.onSubst_fixed subst hlc
      (Expr.substTyFvars_eq_self_of_tyFreeVars_nil _ rfl) (.var hlookup hargs hinst))
  | ctor hlookup hargs hinst =>
    exact .complete rfl (by simp [Expr.tyFreeVars]) (TypeOfHM.onSubst_fixed subst hlc
      (Expr.substTyFvars_eq_self_of_tyFreeVars_nil _ rfl) (.ctor hlookup hargs hinst))
  | match_ _ hne _ ihscrut ihbranches =>
    simp only [Input.substTyFvars, substInputBranches_eq_map]
    refine .match_ (ihscrut hscope) (fun h => hne (List.map_eq_nil_iff.mp h)) ?_
    intro b hb
    obtain ⟨source, hs, rfl⟩ := List.mem_map.mp hb
    exact ihbranches source hs hscope
  | named hspec _ ihbody hscope =>
    refine .named (hspec.onSubst subst hlc) ?_
    simpa only [Subst.onCtx, Subst.onEnv, List.map_append, List.map_map,
      Subst.onPolyTy, PolyTy.mkTrivial, Function.comp_def] using ihbody hscope
  | wildcard _ ihbody hscope => exact .wildcard (ihbody hscope)


private theorem rigidBranchVars_mem_iff {branches : List (MatchPattern × Input)} :
    v ∈ rigidBranchVars branches ↔ ∃ branch ∈ branches, v ∈ branch.2.rigidVars := by
  induction branches with
  | nil => simp only [rigidBranchVars, List.not_mem_nil, false_iff, not_exists, not_and, false_implies, implies_true]
  | cons head rest ih =>
    simp only [rigidBranchVars, List.mem_append, ih, List.mem_cons]
    constructor
    · rintro (h | ⟨b, hb, hv⟩)
      · exact ⟨head, Or.inl rfl, h⟩
      · exact ⟨b, Or.inr hb, hv⟩
    · rintro ⟨b, rfl | hb, hv⟩
      · exact Or.inl hv
      · exact Or.inr ⟨b, hb, hv⟩

/-- Authored free type variables are scoped intrinsically by independent typing. -/
theorem Typing.rigidVars (h : Typing K ctx input ty) : ∀ v ∈ input.rigidVars, v ∈ K := by
  induction h using Typing.rec
      (motive_2 := fun K _ branch _ _ _ => ∀ v ∈ branch.2.rigidVars, v ∈ K) with
  | complete hemb hr _ => exact fun v hv => hr v ((Input.toCore_rigidVars _ hemb v).mp hv)
  | primLit _ => intro v hv; cases hv
  | primBinOp _ => intro v hv; cases hv
  | lambda _ _ hr _ ih =>
    intro v hv
    rcases List.mem_append.mp hv with hv | hv
    · expose_names
      cases ann with
      | none => cases hv
      | some t => exact hr t rfl v hv
    · exact ih v hv
  | app _ _ ihf ihx =>
    exact fun v hv => (List.mem_append.mp hv).elim (ihf v) (ihx v)
  | @letIn ann K ctx rhs body bodyTy M L _ hr hf _ _ ihr ihb =>
    obtain ⟨Xs, hlen, hnd, hav⟩ := exists_fresh_names L M.paramCount
    have hXs : FreshNames L M.paramCount Xs := ⟨hlen, hnd, hav⟩
    intro v hv
    rcases List.mem_append.mp hv with hv | hv
    · rcases List.mem_append.mp hv with hv | hv
      · cases ann with
        | absent => cases hv
        | complete _ => cases hf Xs hXs
        | partialForall _ _ => cases hf Xs hXs
        | template t => exact hr t rfl v hv
      · exact ihr Xs hXs v hv
    · exact ihb v hv
  | var _ _ _ => intro v hv; cases hv
  | ctor _ _ _ => intro v hv; cases hv
  | match_ _ _ _ ihs ihbranches =>
    intro v hv
    rcases List.mem_append.mp hv with hv | hv
    · exact ihs v hv
    · obtain ⟨branch, hb, hv⟩ := rigidBranchVars_mem_iff.mp hv
      exact ihbranches branch hb v hv
  | named _ _ ih v hv => exact ih v hv
  | wildcard _ ih v hv => exact ih v hv

/-- Fixed-source transport is a corollary of source substitution and intrinsic
annotation scope; it needs only pointwise protection of the composite. -/
theorem Typing.onSubst_fixes (h : Typing K ctx input ty) (subst : Subst)
    (hlc : ∀ pair ∈ subst, pair.2.IsLC)
    (hprotected : ∀ v ∈ K, subst.onTy (.fvar v) = .fvar v) :
    Typing K (subst.onCtx ctx) input (subst.onTy ty) := by
  have ht := h.onSubst_source (K' := K) subst hlc (fun k hk v hv => by
    rw [hprotected k hk] at hv
    exact (List.mem_singleton.mp hv) ▸ hk)
  rwa [input.substTyFvars_eq_self_of_fixes (fun v hv => hprotected v (h.rigidVars v hv))] at ht

/-- Pointwise-fixed transport for an independently typed match branch. -/
theorem BranchTyping.onSubst_fixes (h : BranchTyping Typing K ctx branch scrutTy resultTy)
    (subst : Subst) (hlc : ∀ pair ∈ subst, pair.2.IsLC)
    (hprotected : ∀ v ∈ K, subst.onTy (.fvar v) = .fvar v) :
    BranchTyping Typing K (subst.onCtx ctx) branch (subst.onTy scrutTy) (subst.onTy resultTy) := by
  cases h with
  | named hspec hbody =>
    refine .named (hspec.onSubst subst hlc) ?_
    simpa only [Subst.onCtx, Subst.onEnv, List.map_append, List.map_map,
      Subst.onPolyTy, PolyTy.mkTrivial, Function.comp_def] using hbody.onSubst_fixes subst hlc hprotected
  | wildcard hbody => exact .wildcard (hbody.onSubst_fixes subst hlc hprotected)

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


end Elaboration
