import FHM.CoreBackend.Complete
import FHM.Elaboration.RecScheme
import FHM.Elaboration.Close

/-- Pointwise fixing of the opening names suffices; the substitution's literal
domain may contain those names and its ranges may mention them. -/
theorem Subst.onTy_openVarsFrom_of_fixes {S : Subst} {Xs : List Nat}
    (hlc : ∀ p ∈ S, p.2.IsLC)
    (hfix : ∀ x ∈ Xs, S.onTy (.fvar x) = .fvar x) (ty : Ty) (depth : Nat) :
    S.onTy (Ty.openVarsFrom depth Xs ty) = Ty.openVarsFrom depth Xs (S.onTy ty) := by
  induction ty using Ty.rec_strong with
  | prim p => simp only [Ty.openVarsFrom, Ty.instantiate, Subst.onTy_prim]
  | bvar i =>
    simp only [Subst.onTy_bvar, Ty.openVarsFrom, Ty.instantiate]
    by_cases hi : i < depth
    · simp only [if_pos hi, Subst.onTy_bvar]
    · simp only [if_neg hi]
      cases hx : Xs[i - depth]? with
      | none => exact Subst.onTy_bvar
      | some x => exact hfix x (List.mem_of_getElem? hx)
  | fvar v =>
    change S.onTy (.fvar v) = Ty.openVarsFrom depth Xs (S.onTy (.fvar v))
    exact (Ty.instantiate_eq_self_of_lc (Subst.onTy_lc hlc .fvar)).symm
  | arrow a b iha ihb =>
    simp only [Ty.openVarsFrom, Ty.instantiate, Subst.onTy_arrow] at *
    exact congrArg₂ Ty.arrow iha ihb
  | customTy name args ih =>
    simp only [Ty.openVarsFrom, Ty.instantiate, TyList.instantiate_eq_map,
      Subst.onTy_customTy, List.map_map]
    congr 1
    exact List.map_congr_left (fun t ht => ih t ht)

theorem Subst.onTy_openVars_of_fixes {S : Subst} {Xs : List Nat}
    (hlc : ∀ p ∈ S, p.2.IsLC)
    (hfix : ∀ x ∈ Xs, S.onTy (.fvar x) = .fvar x) {ty : Ty} :
    S.onTy (Ty.openVars Xs ty) = Ty.openVars Xs (S.onTy ty) := by
  simpa only [Ty.openVarsFrom, Nat.not_lt_zero, if_false, Nat.sub_zero, Ty.openVars] using Subst.onTy_openVarsFrom_of_fixes hlc hfix ty 0


/-- Free-variable replacement cannot remove an existing bound variable. -/
theorem ContainsBvarsUpTo.of_substFvar {n Z : Nat} {U ty : Ty}
    (h : ContainsBvarsUpTo n (Ty.substFvar Z U ty)) : ContainsBvarsUpTo n ty := by
  induction ty using Ty.rec_strong with
  | prim p => exact .prim
  | bvar i => exact h
  | fvar v => exact .fvar
  | arrow a b iha ihb => cases h with | arrow ha hb => exact .arrow (iha ha) (ihb hb)
  | customTy name args ih =>
    cases h with
    | customTy hall =>
      exact .customTy (fun t ht => ih t ht (hall _ (by
        rw [TyList.substFvar_eq_map]; exact List.mem_map.mpr ⟨t, ht, rfl⟩)))

theorem ContainsBvarsUpTo.of_substFvars {n : Nat} {S : Subst} {ty : Ty}
    (h : ContainsBvarsUpTo n (Ty.substFvars S ty)) : ContainsBvarsUpTo n ty := by
  induction S generalizing ty with
  | nil => exact h
  | cons pair rest ih => exact ContainsBvarsUpTo.of_substFvar (ih h)

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
theorem Template.allocate_bounds (template : Template) (frontier : Nat) :
    frontier ≤ (template.allocate frontier).1 ∧
      ((∀ v ∈ template.rigidVars, v < frontier) →
        Ty.BelowFvars (template.allocate frontier).1 (template.allocate frontier).2) := by
  cases template with
  | fixed ty => exact ⟨Nat.le_refl _, Ty.BelowFvars.of_freeVars_lt⟩
  | hole => exact ⟨Nat.le_succ _, fun _ => .fvar (Nat.lt_succ_self _)⟩
  | arrow a b =>
    obtain ⟨hale, hab⟩ := a.allocate_bounds frontier
    obtain ⟨hble, hbb⟩ := b.allocate_bounds (a.allocate frontier).1
    refine ⟨hale.trans hble, fun hr => .arrow ?_ ?_⟩
    · exact (hab (fun v hv => hr v (List.mem_append_left _ hv))).mono hble
    · exact hbb (fun v hv => Nat.lt_of_lt_of_le (hr v (List.mem_append_right _ hv)) hale)
  | custom name args =>
    obtain ⟨hle, hb⟩ := allocateList_bounds args frontier
    exact ⟨hle, fun hr => .customTy (hb hr)⟩
theorem allocateList_bounds (templates : List Template) (frontier : Nat) :
    frontier ≤ (allocateList frontier templates).1 ∧
      ((∀ v ∈ rigidVarsList templates, v < frontier) →
        ∀ t ∈ (allocateList frontier templates).2, Ty.BelowFvars (allocateList frontier templates).1 t) := by
  cases templates with
  | nil => exact ⟨Nat.le_refl _, fun _ _ ht => by cases ht⟩
  | cons template rest =>
    obtain ⟨hhle, hhb⟩ := template.allocate_bounds frontier
    obtain ⟨htle, htb⟩ := allocateList_bounds rest (template.allocate frontier).1
    refine ⟨hhle.trans htle, ?_⟩
    intro hr t ht
    rcases List.mem_cons.mp ht with rfl | ht
    · exact (hhb (fun v hv => hr v (List.mem_append_left _ hv))).mono htle
    · exact htb (fun v hv => Nat.lt_of_lt_of_le (hr v (List.mem_append_right _ hv)) hhle) t ht
end



mutual
theorem Template.substTyFvars_openTyVarsFrom_of_fixes (template : Template) {S : Subst} {Xs : List Nat}
    (hlc : ∀ p ∈ S, p.2.IsLC)
    (hfix : ∀ x ∈ Xs, S.onTy (.fvar x) = .fvar x) (depth : Nat) :
    (template.openTyVarsFrom depth Xs).substTyFvars S =
      (template.substTyFvars S).openTyVarsFrom depth Xs := by
  cases template with
  | fixed ty => exact congrArg Template.fixed (Subst.onTy_openVarsFrom_of_fixes hlc hfix ty depth)
  | hole => rfl
  | arrow a b =>
    simp only [Template.openTyVarsFrom, Template.substTyFvars,
      a.substTyFvars_openTyVarsFrom_of_fixes hlc hfix depth,
      b.substTyFvars_openTyVarsFrom_of_fixes hlc hfix depth]
  | custom name args =>
    exact congrArg (Template.custom name) (templateList_open_subst_of_fixes args hlc hfix depth)
private theorem templateList_open_subst_of_fixes (templates : List Template) {S : Subst} {Xs : List Nat}
    (hlc : ∀ p ∈ S, p.2.IsLC)
    (hfix : ∀ x ∈ Xs, S.onTy (.fvar x) = .fvar x) (depth : Nat) :
    substTemplateList S (openTemplateList depth Xs templates) =
      openTemplateList depth Xs (substTemplateList S templates) := by
  cases templates with
  | nil => rfl
  | cons t ts =>
    simp only [substTemplateList, openTemplateList,
      t.substTyFvars_openTyVarsFrom_of_fixes hlc hfix depth,
      templateList_open_subst_of_fixes ts hlc hfix depth]
end

/-- Factor an ordinary annotation check against the transformed source. Only
raw-source allocation bounds and independent target protection are required. -/

theorem LetAnn.substTyFvars_openTyVarsFrom_of_fixes (ann : LetAnn) {subst : Subst} {Xs : List Nat}
    (hlc : ∀ pair ∈ subst, pair.2.IsLC) (hfix : ∀ x ∈ Xs, subst.onTy (.fvar x) = .fvar x) (d : Nat) :
    (ann.openTyVarsFrom d Xs).substTyFvars subst = (ann.substTyFvars subst).openTyVarsFrom d Xs := by
  cases ann with
  | absent => rfl
  | complete scheme =>
      exact congrArg (fun t => LetAnn.complete ⟨scheme.paramCount, t⟩)
        (Subst.onTy_openVarsFrom_of_fixes hlc hfix scheme.body (d + scheme.paramCount))
  | template t => exact congrArg LetAnn.template (t.substTyFvars_openTyVarsFrom_of_fixes hlc hfix d)
  | partialForall n t =>
      exact congrArg (LetAnn.partialForall n) (t.substTyFvars_openTyVarsFrom_of_fixes hlc hfix (d + n))

mutual
/-- Source substitution commutes with opening through nested written signature
binders. LC ranges need not avoid the opened names. -/
theorem Input.substTyFvars_openTyVarsFrom_of_fixes (input : Input) {subst : Subst} {Xs : List Nat}
    (hlc : ∀ pair ∈ subst, pair.2.IsLC) (hfix : ∀ x ∈ Xs, subst.onTy (.fvar x) = .fvar x) (d : Nat) :
    (input.openTyVarsFrom d Xs).substTyFvars subst = (input.substTyFvars subst).openTyVarsFrom d Xs := by
  cases input with
  | primLit | primBinOp | var | ctor => rfl
  | lambda ann body =>
      simp only [Input.openTyVarsFrom, Input.substTyFvars,
        body.substTyFvars_openTyVarsFrom_of_fixes hlc hfix d]
      congr 1
      cases ann with
      | none => rfl
      | some template => exact congrArg some (template.substTyFvars_openTyVarsFrom_of_fixes hlc hfix d)
  | app f a => simp only [Input.openTyVarsFrom, Input.substTyFvars,
      f.substTyFvars_openTyVarsFrom_of_fixes hlc hfix d, a.substTyFvars_openTyVarsFrom_of_fixes hlc hfix d]
  | letIn ann rhs body => simp only [Input.openTyVarsFrom, Input.substTyFvars,
      LetAnn.paramCount_substTyFvars, ann.substTyFvars_openTyVarsFrom_of_fixes hlc hfix d,
      rhs.substTyFvars_openTyVarsFrom_of_fixes hlc hfix (d + ann.paramCount),
      body.substTyFvars_openTyVarsFrom_of_fixes hlc hfix d]
  | match_ scrut branches => simp only [Input.openTyVarsFrom, Input.substTyFvars,
      scrut.substTyFvars_openTyVarsFrom_of_fixes hlc hfix d,
      substInputBranches_openInputBranches_of_fixes branches hlc hfix d]
  | letRec anns bindings body =>
      simp only [Input.openTyVarsFrom, Input.substTyFvars,
        body.substTyFvars_openTyVarsFrom_of_fixes hlc hfix d,
        substInputBindings_openInputBindings_of_fixes bindings anns hlc hfix d, List.map_map]
      congr 1
      apply List.map_congr_left
      intro ann _
      exact ann.substTyFvars_openTyVarsFrom_of_fixes hlc hfix d
termination_by sizeOf input

theorem substInputBranches_openInputBranches_of_fixes (branches : List (MatchPattern × Input)) {subst : Subst} {Xs : List Nat}
    (hlc : ∀ pair ∈ subst, pair.2.IsLC) (hfix : ∀ x ∈ Xs, subst.onTy (.fvar x) = .fvar x) (d : Nat) :
    substInputBranches subst (openInputBranches d Xs branches) = openInputBranches d Xs (substInputBranches subst branches) := by
  cases branches with
  | nil => rfl
  | cons pair rest =>
      rcases pair with ⟨pat, body⟩
      simp only [openInputBranches, substInputBranches, body.substTyFvars_openTyVarsFrom_of_fixes hlc hfix d,
        substInputBranches_openInputBranches_of_fixes rest hlc hfix d]
termination_by sizeOf branches

theorem substInputBindings_openInputBindings_of_fixes (bindings : List Input) (anns : List LetAnn)
    {subst : Subst} {Xs : List Nat}
    (hlc : ∀ pair ∈ subst, pair.2.IsLC) (hfix : ∀ x ∈ Xs, subst.onTy (.fvar x) = .fvar x) (d : Nat) :
    substInputBindings subst (openInputBindings d Xs anns bindings) =
      openInputBindings d Xs (anns.map (LetAnn.substTyFvars subst)) (substInputBindings subst bindings) := by
  cases bindings with
  | nil => rfl
  | cons body rest =>
      cases anns with
      | nil => simp only [openInputBindings, substInputBindings, List.map_nil,
          body.substTyFvars_openTyVarsFrom_of_fixes hlc hfix d,
          substInputBindings_openInputBindings_of_fixes rest [] hlc hfix d]
      | cons ann anns => simp only [openInputBindings, substInputBindings, List.map_cons,
          LetAnn.paramCount_substTyFvars, body.substTyFvars_openTyVarsFrom_of_fixes hlc hfix (d + ann.paramCount),
          substInputBindings_openInputBindings_of_fixes rest anns hlc hfix d]
termination_by sizeOf bindings
end

theorem Input.substTyFvars_openTyVars_of_fixes (input : Input) {subst : Subst} {Xs : List Nat}
    (hlc : ∀ pair ∈ subst, pair.2.IsLC) (hfix : ∀ x ∈ Xs, subst.onTy (.fvar x) = .fvar x) :
    (input.openTyVars Xs).substTyFvars subst = (input.substTyFvars subst).openTyVars Xs :=
  input.substTyFvars_openTyVarsFrom_of_fixes hlc hfix 0





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

theorem LetAnn.SignatureFits.isSignature {ann : LetAnn} {scheme : PolyTy} {names : List Nat}
    (h : ann.SignatureFits scheme names) :
    ann.isSignature = true := by cases h <;> rfl

/-- A checked monotype is closed under the written prefix and any inferred
extra binders. Complete signatures retain their exact authored scheme. -/
inductive LetAnn.SignatureCompletion : LetAnn → List Nat → Ty → PolyTy → List Nat → Prop
  | complete {scheme : PolyTy} :
      names.length = scheme.paramCount → ty = scheme.openVars names →
      SignatureCompletion (.complete scheme) names ty scheme names
  | partialSignature {template : Template} {count : Nat} {written extras : List Nat} :
      written.length = count → (template.openTyVarsFrom 0 written).Fits ty →
      SignatureCompletion (.partialForall count template) written ty
        ⟨(written ++ extras).length, Ty.closeOver (written ++ extras) ty⟩ (written ++ extras)

/-- Structural branch completion preserves patterns and completes each body. -/
def LetAnn.RecFits (ann : LetAnn) (written : List Nat) (ty : Ty) : Prop :=
  match ann with
  | .absent => True
  | .template t => t.Fits ty
  | .partialForall count t => written.length = count ∧
      (t.openTyVarsFrom 0 written).Fits ty
  | .complete _ => False

def LetAnn.BindingFits (ann : LetAnn) (scheme : PolyTy) (fresh : List Nat) : Prop :=
  if ann.isSignature then ann.SignatureFits scheme fresh else ann.FitsMono (scheme.openVars fresh)


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
  | complete : input.toCore = some core → (∀ v ∈ core.tyFreeVars, v ∈ K) → Completes K input core
  | lambda :
      (∀ template, ann = some template → template.Fits param) →
      (∀ template, ann = some template → ∀ v ∈ template.rigidVars, v ∈ K) →
      Completes K body completed →
      Completes K (.lambda ann body) (.lambda (ann.map fun _ => param) completed)
  | app : Completes K f fOut → Completes K arg argOut → Completes K (.app f arg) (.app fOut argOut)
  | letIn {M : PolyTy} {L : List Nat} :
      (∀ template, ann = .template template → ∀ v ∈ template.rigidVars, v ∈ K) →
      (∀ Xs, FreshNames L M.paramCount Xs → ann.FitsMono (M.openVars Xs)) →
      (∀ Xs, FreshNames L M.paramCount Xs → Completes K rhs (rhsOut.openTyVars Xs)) →
      Completes K body bodyOut →
      Completes K (.letIn ann rhs body) (.letIn (some M) rhsOut bodyOut)
  | letSignature {M : PolyTy} {L : List Nat} :
      (∀ v ∈ ann.rigidVars, v ∈ K) → (∀ v ∈ rhs.rigidVars, v ∈ K) →
      (∀ Xs, FreshNames L M.paramCount Xs → ann.SignatureFits M Xs) →
      (∀ Xs, FreshNames L M.paramCount Xs →
        Completes (K ++ Xs.take ann.paramCount) (rhs.openTyVars (Xs.take ann.paramCount))
          (rhsOut.openTyVars Xs)) →
      Completes K body bodyOut →
      Completes K (.letIn ann rhs body) (.letIn (some M) rhsOut bodyOut)
  | match_ : Completes K scrut scrutOut → CompletedBranches Completes K branches branchesOut →
      Completes K (.match_ scrut branches) (.match_ scrutOut branchesOut)

  | letRec {schemes : List PolyTy} {L : List Nat} :
    anns.length = schemes.length → bindings.length = schemes.length →
    completed.length = schemes.length →
    (∀ ann ∈ anns, ∀ v ∈ ann.rigidVars, v ∈ K) →
    (∀ rhs ∈ bindings, ∀ v ∈ rhs.rigidVars, v ∈ K) →
    (∀ (member : Nat) (ann : LetAnn) (rhs : Input) (output : Expr) (scheme : PolyTy),
      anns[member]? = some ann → bindings[member]? = some rhs →
      completed[member]? = some output → schemes[member]? = some scheme →
      (∀ Xs, FreshNames L scheme.paramCount Xs → ann.BindingFits scheme Xs)) →
    (∀ (member : Nat) (ann : LetAnn) (rhs : Input) (output : Expr) (scheme : PolyTy),
      anns[member]? = some ann → bindings[member]? = some rhs →
      completed[member]? = some output → schemes[member]? = some scheme →
      (∀ Xs, FreshNames L scheme.paramCount Xs →
        Completes (K ++ Xs.take ann.paramCount) (rhs.openTyVars (Xs.take ann.paramCount))
          (output.openTyVars Xs))) →
    Completes K body bodyOut →
    Completes K (.letRec anns bindings body) (.letRec (schemes.map some) completed bodyOut)

/-- Independent branch semantics reuse the ordinary constructor specification;
the body relation is a parameter, with no inference state or substitution. -/
inductive BranchTyping (J : List Nat → Ctx → Input → Ty → Prop) :
    List Nat → Ctx → (MatchPattern × Input) → Ty → Ty → Prop
  | named : BranchCtorSpec ctx.ctors name count scrutTy ctor args fields →
      J K { ctx with env := fields.map PolyTy.mkTrivial ++ ctx.env } body resultTy →
      BranchTyping J K ctx (.named name count, body) scrutTy resultTy
  | wildcard : J K ctx body resultTy → BranchTyping J K ctx (.wildcard, body) scrutTy resultTy

/-- Independent input typing. `K` scopes authored rigid annotation variables;
context monotypes can still contain flexible variables. Ordinary lets generalize
cofinally. Signed lets preserve the written forall prefix and check each fresh
opening, with any additional hole variables quantified after that prefix.

Whole completed subtrees retain the existing rules through conservative Core
embedding. Partial recursive spines have no rule here, so a partial annotation
cannot grant polymorphic recursive uses through an arbitrary completed scheme.
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
  | letSignature {M : PolyTy} {L : List Nat} :
      M.WF → (∀ v ∈ ann.rigidVars, v ∈ K) → (∀ v ∈ rhs.rigidVars, v ∈ K) →
      (∀ Xs, FreshNames L M.paramCount Xs → ann.SignatureFits M Xs) →
      (∀ Xs, FreshNames L M.paramCount Xs →
        Typing (K ++ Xs.take ann.paramCount) ctx (rhs.openTyVars (Xs.take ann.paramCount)) (M.openVars Xs)) →
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
  | letRec {specs : List RecSpec} {groups : List (List Nat)} {prefixes : List (List Nat)}
      {G L : List Nat} :
    RecGroups.ValidResidualGroups (anns.map LetAnn.recModeAnn) (bindings.map Input.erase) groups →
    RecSpecs.WF (anns.map LetAnn.recModeAnn) (bindings.map Input.erase) specs G →
    RecPrefixesWF anns specs prefixes G →
    (∀ name ∈ G, name ∉ ctx.env.freeVars ++ K) →
    (∀ ann ∈ anns, ∀ v ∈ ann.rigidVars, v ∈ K) →
    (∀ rhs ∈ bindings, ∀ v ∈ rhs.rigidVars, v ∈ K) →
    (∀ (stage : Nat) (component : List Nat), groups[stage]? = some component →
      ∀ Xs, FreshNames (G ++ L) G.length Xs →
      ∀ (member : Nat), member ∈ component → ∀ (rhs : Input) (ann : LetAnn) (names : List Nat) (ty : Ty),
        bindings[member]? = some rhs → anns[member]? = some ann →
        prefixes[member]? = some names → specs[member]? = some (.mono ty) →
        ann.RecFits (recRenameNames G Xs names) (Ty.renameG G Xs ty)) →
    (∀ (stage : Nat) (component : List Nat), groups[stage]? = some component →
      ∀ Xs, FreshNames (G ++ L) G.length Xs →
      ∀ (member : Nat), member ∈ component → ∀ (rhs : Input) (ann : LetAnn) (names : List Nat) (ty : Ty),
        bindings[member]? = some rhs → anns[member]? = some ann →
        prefixes[member]? = some names → specs[member]? = some (.mono ty) →
        Typing (K ++ Xs) (recStageCtx ctx specs prefixes (groups.take stage).flatten G Xs)
          (rhs.openTyVars (recRenameNames G Xs names)) (Ty.renameG G Xs ty)) →
    (∀ (member : Nat) (rhs : Input) (scheme : PolyTy), bindings[member]? = some rhs →
      specs[member]? = some (.poly scheme) →
      ∀ Ys, FreshNames L scheme.paramCount Ys →
        Typing (K ++ Ys) (recBodyCtx ctx specs prefixes G) (rhs.openTyVars Ys) (scheme.openVars Ys)) →
    Typing K (recBodyCtx ctx specs prefixes G) body resultTy →
    Typing K ctx (.letRec anns bindings body) resultTy



private theorem erasedBranches_eq_map (branches : List (MatchPattern × Input)) :
    eraseBranches branches = branches.map (fun branch => (branch.1, branch.2.erase)) := by
  induction branches with
  | nil => rfl
  | cons head rest ih => rcases head with ⟨p, b⟩; simp only [eraseBranches, List.map_cons, ih]

private theorem eraseBindings_eq_map_source (bindings : List Input) :
    eraseBindings bindings = bindings.map Input.erase := by
  induction bindings with
  | nil => rfl
  | cons rhs rest ih => simp only [eraseBindings, List.map_cons, ih]

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
  | @letSignature K ctx body bodyTy ann rhs scheme avoid hwf _ _ _ _ _ ihrhs ihbody =>
      refine .letIn (avoid := avoid) hwf ?_ ihbody
      intro Xs hf
      simpa only [Input.erase_openTyVars] using ihrhs Xs hf
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
  | letRec hgroups hwf hp _ _ _ _ _ _ _ ihmono ihpoly ihbody =>
    expose_names
    have hannsLen : anns.length = specs.length := by
      have hh := congrArg List.length hwf.anns_eq
      simpa using hh.symm
    have hbodyGen := bodySchemes_generalize_recCompleted hwf hp
    simp only [Input.erase, eraseBindings_eq_map_source]
    rw [show bindings.map (fun _ => none) = (bindings.map Input.erase).map (fun _ => none) by
      simp only [List.map_map, Function.comp_def]]
    refine RuntimeTyping.RunWT.letRec (specs := specs) (G := G) (avoid := G ++ L)
      ⟨hwf.length, hwf.nodup, hwf.mono_lc, hwf.poly_wf⟩ ?_ ?_ ?_
    · intro Xs hf pair hpair ty heq
      obtain ⟨rhs, spec, _, hpair0, rfl⟩ := List.mem_zip_map_left hpair
      obtain ⟨member, hzip⟩ := List.mem_iff_getElem?.mp hpair0
      obtain ⟨hrhs, hspec⟩ := List.getElem?_zip_eq_some.mp hzip
      rw [heq] at hspec
      have hi : member < specs.length := (List.getElem?_eq_some_iff.mp hspec).1
      have hia : member < anns.length := by omega
      have hip : member < prefixes.length := by rw [hp.length]; exact hi
      have hunsigned : RecGroups.UnsignedAt (anns.map LetAnn.recModeAnn) member := by
        simp only [RecGroups.UnsignedAt, ← hwf.anns_eq, List.getElem?_map, hspec,
          Option.map_some, RecSpec.ann]
      have hcovered := (hgroups.covers_unsigned member (by simpa only [List.length_map] using
        (List.getElem?_eq_some_iff.mp hrhs).1)).2 hunsigned
      obtain ⟨component, hc, hm⟩ := List.mem_flatten.mp hcovered
      obtain ⟨stage, hstage⟩ := List.mem_iff_getElem?.mp hc
      have ht := ihmono stage component hstage Xs hf member hm rhs anns[member] prefixes[member] ty
        hrhs (List.getElem?_eq_getElem hia) (List.getElem?_eq_getElem hip) hspec
      simp only [Input.erase_openTyVars] at ht
      have hh := RuntimeTyping.RunWT.weaken_schemes
        (bodySchemes_generalize_recStage (done := (groups.take stage).flatten) (Xs := Xs) hwf hp) ht
      exact hh
    · intro pair hpair scheme heq Ys hy
      obtain ⟨rhs, spec, _, hpair0, rfl⟩ := List.mem_zip_map_left hpair
      obtain ⟨member, hzip⟩ := List.mem_iff_getElem?.mp hpair0
      obtain ⟨hrhs, hspec⟩ := List.getElem?_zip_eq_some.mp hzip
      rw [heq] at hspec
      have hf : FreshNames L scheme.paramCount Ys :=
        ⟨hy.length, hy.nodup, fun y hy' hl => hy.avoid y hy' (List.mem_append_right _ hl)⟩
      have ht := ihpoly member rhs scheme hrhs hspec Ys hf
      simp only [Input.erase_openTyVars] at ht
      exact RuntimeTyping.RunWT.weaken_schemes hbodyGen ht
    · exact RuntimeTyping.RunWT.weaken_schemes hbodyGen ihbody
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


private theorem rigidAnns_substTyFvars {anns : List LetAnn} {subst : Subst} {v : Nat}
    (h : v ∈ (anns.map (LetAnn.substTyFvars subst)).flatMap LetAnn.rigidVars) :
    ∃ k ∈ anns.flatMap LetAnn.rigidVars, v ∈ (subst.onTy (.fvar k)).freeVars := by
  obtain ⟨ann', hann', hv⟩ := List.mem_flatMap.mp h
  obtain ⟨ann, hann, rfl⟩ := List.mem_map.mp hann'
  obtain ⟨k, hk, hv⟩ := ann.rigidVars_substTyFvars hv
  exact ⟨k, List.mem_flatMap.mpr ⟨ann, hann, hk⟩, hv⟩

mutual
/-- Every authored variable after source substitution originates in the image
of one authored variable before substitution. -/
theorem Input.rigidVars_substTyFvars {input : Input} {subst : Subst} {v : Nat}
    (h : v ∈ (input.substTyFvars subst).rigidVars) :
    ∃ k ∈ input.rigidVars, v ∈ (subst.onTy (.fvar k)).freeVars := by
  cases input with
  | primLit | primBinOp | var | ctor => cases h
  | lambda ann body =>
      rcases List.mem_append.mp h with ha | hb
      · cases ann with
        | none => cases ha
        | some template =>
            obtain ⟨k, hk, hv⟩ := template.rigidVars_substTyFvars ha
            exact ⟨k, List.mem_append_left _ hk, hv⟩
      · obtain ⟨k, hk, hv⟩ := body.rigidVars_substTyFvars hb
        exact ⟨k, List.mem_append_right _ hk, hv⟩
  | app f a =>
      rcases List.mem_append.mp h with hf | ha
      · obtain ⟨k, hk, hv⟩ := f.rigidVars_substTyFvars hf
        exact ⟨k, List.mem_append_left _ hk, hv⟩
      · obtain ⟨k, hk, hv⟩ := a.rigidVars_substTyFvars ha
        exact ⟨k, List.mem_append_right _ hk, hv⟩
  | letIn ann rhs body =>
      rcases List.mem_append.mp h with hprefix | hb
      · rcases List.mem_append.mp hprefix with ha | hr
        · obtain ⟨k, hk, hv⟩ := ann.rigidVars_substTyFvars ha
          exact ⟨k, List.mem_append_left _ (List.mem_append_left _ hk), hv⟩
        · obtain ⟨k, hk, hv⟩ := rhs.rigidVars_substTyFvars hr
          exact ⟨k, List.mem_append_left _ (List.mem_append_right _ hk), hv⟩
      · obtain ⟨k, hk, hv⟩ := body.rigidVars_substTyFvars hb
        exact ⟨k, List.mem_append_right _ hk, hv⟩
  | match_ scrut branches =>
      rcases List.mem_append.mp h with hs | hbs
      · obtain ⟨k, hk, hv⟩ := scrut.rigidVars_substTyFvars hs
        exact ⟨k, List.mem_append_left _ hk, hv⟩
      · obtain ⟨k, hk, hv⟩ := rigidBranchVars_substTyFvars hbs
        exact ⟨k, List.mem_append_right _ hk, hv⟩
  | letRec anns bindings body =>
      rcases List.mem_append.mp h with hprefix | hb
      · rcases List.mem_append.mp hprefix with ha | hbs
        · obtain ⟨k, hk, hv⟩ := rigidAnns_substTyFvars ha
          exact ⟨k, List.mem_append_left _ (List.mem_append_left _ hk), hv⟩
        · obtain ⟨k, hk, hv⟩ := rigidBindingVars_substTyFvars hbs
          exact ⟨k, List.mem_append_left _ (List.mem_append_right _ hk), hv⟩
      · obtain ⟨k, hk, hv⟩ := body.rigidVars_substTyFvars hb
        exact ⟨k, List.mem_append_right _ hk, hv⟩
termination_by sizeOf input

theorem rigidBranchVars_substTyFvars {branches : List (MatchPattern × Input)} {subst : Subst} {v : Nat}
    (h : v ∈ rigidBranchVars (substInputBranches subst branches)) :
    ∃ k ∈ rigidBranchVars branches, v ∈ (subst.onTy (.fvar k)).freeVars := by
  cases branches with
  | nil => cases h
  | cons pair rest =>
      rcases List.mem_append.mp h with hb | hr
      · obtain ⟨k, hk, hv⟩ := pair.2.rigidVars_substTyFvars hb
        exact ⟨k, List.mem_append_left _ hk, hv⟩
      · obtain ⟨k, hk, hv⟩ := rigidBranchVars_substTyFvars hr
        exact ⟨k, List.mem_append_right _ hk, hv⟩
termination_by sizeOf branches
decreasing_by all_goals (subst_vars; cases pair; simp_wf <;> omega)

theorem rigidBindingVars_substTyFvars {bindings : List Input} {subst : Subst} {v : Nat}
    (h : v ∈ rigidBindingVars (substInputBindings subst bindings)) :
    ∃ k ∈ rigidBindingVars bindings, v ∈ (subst.onTy (.fvar k)).freeVars := by
  cases bindings with
  | nil => cases h
  | cons body rest =>
      rcases List.mem_append.mp h with hb | hr
      · obtain ⟨k, hk, hv⟩ := body.rigidVars_substTyFvars hb
        exact ⟨k, List.mem_append_left _ hk, hv⟩
      · obtain ⟨k, hk, hv⟩ := rigidBindingVars_substTyFvars hr
        exact ⟨k, List.mem_append_right _ hk, hv⟩
termination_by sizeOf bindings
end


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

theorem LetAnn.SignatureFits.onSubst_source {ann : LetAnn} {scheme : PolyTy} {names : List Nat}
    (h : ann.SignatureFits scheme names) (subst : Subst)
    (hlc : ∀ pair ∈ subst, pair.2.IsLC) (hfresh : ∀ pair ∈ subst, pair.1 ∉ names) :
    (ann.substTyFvars subst).SignatureFits (subst.onPolyTy scheme) names := by
  cases h with
  | complete => exact .complete
  | @partialSignature scheme template count names hle hfit =>
      refine .partialSignature hle ?_
      have hsmall : ∀ pair ∈ subst, pair.1 ∉ names.take count :=
        fun pair hp hv => hfresh pair hp (List.mem_of_mem_take hv)
      have ht := hfit.substTyFvars subst
      simpa only [Template.substTyFvars_openTyVarsFrom _ hlc hsmall 0,
        PolyTy.openVars, Subst.onPolyTy, Subst.onTy_openVars hlc hfresh] using ht

private theorem substInputBindings_eq_map_source (S : Subst) (bindings : List Input) :
    substInputBindings S bindings = bindings.map (Input.substTyFvars S) := by
  induction bindings with
  | nil => rfl
  | cons rhs rest ih => simp only [substInputBindings, List.map_cons, ih]

private theorem recRenameNames_getD_source (G W : List Nat) (prefixes : List (List Nat)) (i : Nat) :
    (prefixes.map (recRenameNames G W))[i]?.getD [] = recRenameNames G W (prefixes[i]?.getD []) := by
  rw [List.getElem?_map]
  cases prefixes[i]? <;> rfl

theorem LetAnn.RecFits.onSubst_source {ann : LetAnn} {names : List Nat} {ty : Ty}
    (h : ann.RecFits names ty) (S : Subst) (hlc : ∀ p ∈ S, p.2.IsLC)
    (hfix : ∀ name ∈ names, S.onTy (.fvar name) = .fvar name) :
    (ann.substTyFvars S).RecFits names (S.onTy ty) := by
  cases ann with
  | absent => trivial
  | complete scheme => exact False.elim h
  | template t => exact h.substTyFvars S
  | partialForall n t =>
    refine ⟨h.1, ?_⟩
    have hh := h.2.substTyFvars S
    rw [Template.substTyFvars_openTyVarsFrom_of_fixes t hlc hfix] at hh
    exact hh

/-- Source-transforming substitution transports the independent judgment when
its authored variable images are scoped by the destination protected set. -/
theorem Typing.onSubst_source {K K' : List Nat} {ctx : Ctx} {input : Input} {ty : Ty}
    (h : Typing K ctx input ty) (subst : Subst)
    (hlc : ∀ pair ∈ subst, pair.2.IsLC)
    (hscope : ∀ k ∈ K, ∀ v ∈ (subst.onTy (.fvar k)).freeVars, v ∈ K') :
    Typing K' (subst.onCtx ctx) (input.substTyFvars subst) (subst.onTy ty) := by
  induction h using Typing.rec
      (motive_2 := fun K ctx branch scrutTy resultTy _ => ∀ {K' : List Nat},
        (∀ k ∈ K, ∀ v ∈ (subst.onTy (.fvar k)).freeVars, v ∈ K') →
          BranchTyping Typing K' (subst.onCtx ctx) (branch.1, branch.2.substTyFvars subst)
            (subst.onTy scrutTy) (subst.onTy resultTy)) generalizing K' with
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
  | @letSignature K ctx body bodyTy ann rhs scheme avoid hwf hann hrhs hfit _ _ ihgeneral ihbody =>
    let avoid' := avoid ++ subst.map Prod.fst
    have oldFresh : ∀ names, FreshNames avoid' scheme.paramCount names → FreshNames avoid scheme.paramCount names :=
      fun names hf => ⟨hf.length, hf.nodup, fun v hv ha => hf.avoid v hv (List.mem_append_left _ ha)⟩
    have domFresh : ∀ names, FreshNames avoid' scheme.paramCount names → ∀ pair ∈ subst, pair.1 ∉ names := by
      intro names hf pair hp hv
      exact hf.avoid pair.1 hv (List.mem_append_right _ (List.mem_map.mpr ⟨pair, hp, rfl⟩))
    refine Typing.letSignature (M := subst.onPolyTy scheme) (L := avoid')
      (Subst.onPolyTy_wf hlc hwf) ?_ ?_ ?_ ?_ ?_
    · intro v hv
      obtain ⟨k, hk, hv⟩ := LetAnn.rigidVars_substTyFvars hv
      exact hscope k (hann k hk) v hv
    · intro v hv
      obtain ⟨k, hk, hv⟩ := Input.rigidVars_substTyFvars hv
      exact hscope k (hrhs k hk) v hv
    · intro names hf
      exact (hfit names (oldFresh names hf)).onSubst_source subst hlc (domFresh names hf)
    · intro names hf
      have hsmall : ∀ pair ∈ subst, pair.1 ∉ names.take ann.paramCount :=
        fun pair hp hv => domFresh names hf pair hp (List.mem_of_mem_take hv)
      have hchild := ihgeneral names (oldFresh names hf) (K' := K' ++ names.take ann.paramCount) (fun k hk v hv => by
        rcases List.mem_append.mp hk with hk | hk
        · exact List.mem_append_left _ (hscope k hk v hv)
        · have hfix : subst.onTy (.fvar k) = .fvar k := by
            apply Ty.substFvars_eq_self_of_no_key
            intro pair hp hc
            have heq : pair.1 = k := List.mem_singleton.mp hc
            exact hsmall pair hp (heq ▸ hk)
          rw [hfix] at hv
          exact List.mem_append_right _ ((List.mem_singleton.mp hv) ▸ hk))
      simpa only [LetAnn.paramCount_substTyFvars,
        Input.substTyFvars_openTyVars _ hlc hsmall, PolyTy.openVars, Subst.onPolyTy,
        Subst.onTy_openVars hlc (domFresh names hf)] using hchild
    · simpa only [Subst.onCtx, Subst.onEnv, List.map_cons] using ihbody hscope
  | letRec hgroups hwf hp hG hAnn hRhs hFits _ _ _ ihMono ihPoly ihBody =>
    expose_names
    let avoid := K' ++ (subst.onCtx ctx_1).env.freeVars ++ G ++ subst.map Prod.fst ++
      subst.flatMap (fun p => p.2.freeVars) ++ specs.flatMap RecSpec.freeVars
    obtain ⟨W, hWlen, hWnd, hWavoid⟩ := exists_fresh_names avoid G.length
    have hGW : ∀ g ∈ G, g ∉ W := by
      intro g hg hw
      exact hWavoid g hw (by simp only [avoid, List.mem_append]; tauto)
    have hWmono : ∀ t, .mono t ∈ specs → ∀ w ∈ W, w ∉ t.freeVars := by
      intro t ht w hw hv
      exact hWavoid w hw (by
        simp only [avoid, List.mem_append]
        right
        exact List.mem_flatMap.mpr ⟨.mono t, ht, hv⟩)
    have hdomW : ∀ p ∈ subst, p.1 ∉ W := by
      intro p hp hw
      exact hWavoid p.1 hw (by
        have hm : p.1 ∈ subst.map Prod.fst := List.mem_map.mpr ⟨p, hp, rfl⟩
        simp only [avoid, List.mem_append]
        tauto)
    have hranW : ∀ p ∈ subst, ∀ v ∈ p.2.freeVars, v ∉ W := by
      intro p hp v hv hw
      exact hWavoid v hw (by
        simp only [avoid, List.mem_append]
        left; right
        exact List.mem_flatMap.mpr ⟨p, hp, hv⟩)
    let specs' := specs.map (fun spec => RecSpec.onSubstSource subst (RecSpec.onSubst (G.zip (W.map Ty.fvar)) spec))
    let prefixes' := prefixes.map (recRenameNames G W)
    let L' := G ++ W ++ L ++ subst.map Prod.fst
    have hannsLen : anns.length = specs.length := by
      have hh := congrArg List.length hwf.anns_eq
      simpa using hh.symm
    have hpData := fun i hi => hp.get hannsLen (i := i) hi
    have hcompleted := recCompletedSchemes_subst_fresh_pool hlc hWlen hwf.nodup hWnd hGW hWmono
      hdomW hranW hwf.mono_lc hpData
    have hbodyCtx : recBodyCtx (subst.onCtx ctx_1) specs' prefixes' W = subst.onCtx (recBodyCtx ctx_1 specs prefixes G) := by
      simp only [recBodyCtx, Subst.onCtx, Subst.onEnv, List.map_append]
      rw [hcompleted]
    have oldFresh : ∀ Xs, FreshNames (W ++ L') W.length Xs → FreshNames (G ++ L) G.length Xs := by
      intro Xs hf
      refine ⟨hf.length.trans hWlen, hf.nodup, ?_⟩
      intro v hv hm
      exact hf.avoid v hv (by simp only [L', List.mem_append] at hm ⊢; tauto)
    have hGXs : ∀ Xs, FreshNames (W ++ L') W.length Xs → ∀ g ∈ G, g ∉ Xs := by
      intro Xs hf g hg hx
      exact hf.avoid g hx (by simp only [L', List.mem_append]; tauto)
    have hWXs : ∀ Xs, FreshNames (W ++ L') W.length Xs → ∀ w ∈ W, w ∉ Xs := by
      intro Xs hf w hw hx
      exact hf.avoid w hx (List.mem_append_left _ hw)
    have hdomXs : ∀ Xs, FreshNames (W ++ L') W.length Xs → ∀ p ∈ subst, p.1 ∉ Xs := by
      intro Xs hf p hp hx
      exact hf.avoid p.1 hx (by
        have hm : p.1 ∈ subst.map Prod.fst := List.mem_map.mpr ⟨p, hp, rfl⟩
        simp only [L', List.mem_append]
        tauto)
    have scopeXs : ∀ Xs, FreshNames (W ++ L') W.length Xs →
        ∀ k ∈ K_1 ++ Xs, ∀ v ∈ (subst.onTy (.fvar k)).freeVars, v ∈ K' ++ Xs := by
      intro Xs hf k hk v hv
      rcases List.mem_append.mp hk with hk | hk
      · exact List.mem_append_left _ (hscope k hk v hv)
      · have hfix : subst.onTy (.fvar k) = .fvar k :=
          Subst.fixes_of_dom_avoids (hdomXs Xs hf) k hk
        rw [hfix] at hv
        exact List.mem_append_right _ ((List.mem_singleton.mp hv) ▸ hk)
    simp only [Input.substTyFvars, substInputBindings_eq_map_source]
    refine Typing.letRec (specs := specs') (groups := groups) (prefixes := prefixes') (G := W) (L := L')
      ?_ ?_ (hp.subst_fresh_pool (S := subst) hWlen hWnd) ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · have hg := hgroups.map_bindings (anns' := (anns.map (LetAnn.substTyFvars subst)).map LetAnn.recModeAnn) id
        (by simp) (fun i => by
          simp only [RecGroups.UnsignedAt, List.getElem?_map, Option.map_map, Function.comp_def]
          cases anns[i]? with
          | none => simp
          | some ann => cases ann <;> simp [LetAnn.recModeAnn, LetAnn.substTyFvars])
        (fun _ _ => rfl)
      simpa only [List.map_id, List.map_map, Function.comp_def, Input.erase_substTyFvars] using hg
    · simpa only [List.map_map, Function.comp_def, Input.erase_substTyFvars] using Elaboration.RecSpecs.WF.subst_fresh_pool hwf hlc hWnd
    · intro w hw hm
      exact hWavoid w hw (by simp only [avoid, List.mem_append] at hm ⊢; tauto)
    · intro ann ha v hv
      obtain ⟨ann0, ha0, rfl⟩ := List.mem_map.mp ha
      obtain ⟨k, hk, himage⟩ := LetAnn.rigidVars_substTyFvars hv
      exact hscope k (hAnn ann0 ha0 k hk) v himage
    · intro rhs hr v hv
      obtain ⟨rhs0, hr0, rfl⟩ := List.mem_map.mp hr
      obtain ⟨k, hk, himage⟩ := Input.rigidVars_substTyFvars hv
      exact hscope k (hRhs rhs0 hr0 k hk) v himage
    · intro stage component hs Xs hf member hm rhs ann names ty hr ha hn ht
      rw [List.getElem?_map] at hr ha hn ht
      obtain ⟨rhs0, hr0, rfl⟩ := Option.map_eq_some_iff.mp hr
      obtain ⟨ann0, ha0, rfl⟩ := Option.map_eq_some_iff.mp ha
      obtain ⟨names0, hn0, rfl⟩ := Option.map_eq_some_iff.mp hn
      obtain ⟨spec0, ht0, heq⟩ := Option.map_eq_some_iff.mp ht
      cases spec0 with
      | poly scheme => cases heq
      | mono ty0 =>
        cases heq
        change (ann0.substTyFvars subst).RecFits
          (recRenameNames W Xs (recRenameNames G W names0))
          (Ty.renameG W Xs (subst.onTy (Ty.renameG G W ty0)))
        obtain ⟨_, _, hsub⟩ := hp.member member ann0 names0 ha0 hn0
        have hfit := (hFits stage component hs Xs (oldFresh Xs hf) member hm rhs0 ann0 names0 ty0 hr0 ha0 hn0 ht0).onSubst_source
          subst hlc (Subst.fixes_of_dom_avoids (fun p hp hn => hdomXs Xs hf p hp
            (recRenameNames_mem (hf.length.trans hWlen) hsub p.1 hn)))
        rw [recRenameNames_composition hWlen (hf.length.trans hWlen) hWnd hsub,
          Ty.renameG_subst_fresh_pool (hwf.mono_lc ty0 (List.mem_of_getElem? ht0)) hlc hWlen hwf.nodup hWnd hGW
            (hWmono ty0 (List.mem_of_getElem? ht0)) hdomW hranW (hf.length.trans hWlen) (hGXs Xs hf)
            (hWXs Xs hf) (hdomXs Xs hf)]
        exact hfit
    · intro stage component hs Xs hf member hm rhs ann names ty hr ha hn ht
      rw [List.getElem?_map] at hr ha hn ht
      obtain ⟨rhs0, hr0, rfl⟩ := Option.map_eq_some_iff.mp hr
      obtain ⟨ann0, ha0, rfl⟩ := Option.map_eq_some_iff.mp ha
      obtain ⟨names0, hn0, rfl⟩ := Option.map_eq_some_iff.mp hn
      obtain ⟨spec0, ht0, heq⟩ := Option.map_eq_some_iff.mp ht
      cases spec0 with
      | poly scheme => cases heq
      | mono ty0 =>
        cases heq
        change Typing (K' ++ Xs)
          (recStageCtx (subst.onCtx ctx_1) specs' prefixes' (groups.take stage).flatten W Xs)
          ((rhs0.substTyFvars subst).openTyVars (recRenameNames W Xs (recRenameNames G W names0)))
          (Ty.renameG W Xs (subst.onTy (Ty.renameG G W ty0)))
        obtain ⟨_, _, hsub⟩ := hp.member member ann0 names0 ha0 hn0
        have hsmall : ∀ p ∈ subst, p.1 ∉ recRenameNames G Xs names0 :=
          fun p hp hn => hdomXs Xs hf p hp (recRenameNames_mem (hf.length.trans hWlen) hsub p.1 hn)
        have hc := ihMono stage component hs Xs (oldFresh Xs hf) member hm rhs0 ann0 names0 ty0 hr0 ha0 hn0 ht0
          (K' := K' ++ Xs) (scopeXs Xs hf)
        have hstageCtx : recStageCtx (subst.onCtx ctx_1) specs' prefixes' (groups.take stage).flatten W Xs =
            subst.onCtx (recStageCtx ctx_1 specs prefixes (groups.take stage).flatten G Xs) := by
          simp only [recStageCtx, Subst.onCtx, Subst.onEnv, List.map_append]
          rw [recStageSchemes_subst_fresh_pool hlc hWlen hwf.nodup hWnd hGW hWmono hdomW hranW
            hwf.mono_lc hpData (hf.length.trans hWlen) (hGXs Xs hf) (hWXs Xs hf) (hdomXs Xs hf)]
        rw [hstageCtx, recRenameNames_composition hWlen (hf.length.trans hWlen) hWnd hsub,
          Ty.renameG_subst_fresh_pool (hwf.mono_lc ty0 (List.mem_of_getElem? ht0)) hlc hWlen hwf.nodup hWnd hGW
            (hWmono ty0 (List.mem_of_getElem? ht0)) hdomW hranW (hf.length.trans hWlen) (hGXs Xs hf)
            (hWXs Xs hf) (hdomXs Xs hf)]
        simpa only [Input.substTyFvars_openTyVars _ hlc hsmall] using hc
    · intro member rhs scheme hr hs Ys hy
      rw [List.getElem?_map] at hr hs
      obtain ⟨rhs0, hr0, rfl⟩ := Option.map_eq_some_iff.mp hr
      obtain ⟨spec0, hs0, heq⟩ := Option.map_eq_some_iff.mp hs
      cases spec0 with
      | mono ty => cases heq
      | poly scheme0 =>
        cases heq
        have hy0 : FreshNames L scheme0.paramCount Ys :=
          ⟨hy.length, hy.nodup, fun y hy' hl => hy.avoid y hy' (by simp only [L', List.mem_append]; tauto)⟩
        have hsmall : ∀ p ∈ subst, p.1 ∉ Ys := by
          intro p hp hy'
          exact hy.avoid p.1 hy' (by
            simp only [L', List.mem_append]
            right
            exact List.mem_map.mpr ⟨p, hp, rfl⟩)
        have hc := ihPoly member rhs0 scheme0 hr0 hs0 Ys hy0 (K' := K' ++ Ys) (fun k hk v hv => by
          rcases List.mem_append.mp hk with hk | hk
          · exact List.mem_append_left _ (hscope k hk v hv)
          · rw [Subst.fixes_of_dom_avoids hsmall k hk] at hv
            exact List.mem_append_right _ ((List.mem_singleton.mp hv) ▸ hk))
        rw [hbodyCtx]
        simpa only [Input.substTyFvars_openTyVars _ hlc hsmall, PolyTy.openVars, Subst.onPolyTy,
          Subst.onTy_openVars hlc hsmall] using hc
    · rw [hbodyCtx]
      exact ihBody hscope
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
private theorem rigidBindingVars_mem_iff {bindings : List Input} :
    v ∈ rigidBindingVars bindings ↔ ∃ rhs ∈ bindings, v ∈ rhs.rigidVars := by
  induction bindings with
  | nil => simp only [rigidBindingVars, List.not_mem_nil, false_iff, not_exists, not_and, false_implies, implies_true]
  | cons head rest ih =>
      simp only [rigidBindingVars, List.mem_append, List.mem_cons, ih]
      constructor
      · rintro (h | ⟨rhs, hr, hv⟩)
        · exact ⟨head, .inl rfl, h⟩
        · exact ⟨rhs, .inr hr, hv⟩
      · rintro ⟨rhs, rfl | hr, hv⟩
        · exact .inl hv
        · exact .inr ⟨rhs, hr, hv⟩

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
  | letSignature _ hann hrhs _ _ _ _ ihb =>
    intro v hv
    rcases List.mem_append.mp hv with hv | hv
    · exact (List.mem_append.mp hv).elim (hann v) (hrhs v)
    · exact ihb v hv
  | var _ _ _ => intro v hv; cases hv
  | ctor _ _ _ => intro v hv; cases hv
  | match_ _ _ _ ihs ihbranches =>
    intro v hv
    rcases List.mem_append.mp hv with hv | hv
    · exact ihs v hv
    · obtain ⟨branch, hb, hv⟩ := rigidBranchVars_mem_iff.mp hv
      exact ihbranches branch hb v hv
  | letRec _ _ _ _ hAnn hRhs _ _ _ _ _ _ ihBody =>
    intro v hv
    rcases List.mem_append.mp hv with hv | hv
    · rcases List.mem_append.mp hv with hv | hv
      · obtain ⟨ann, ha, hv⟩ := List.mem_flatMap.mp hv
        exact hAnn ann ha v hv
      · obtain ⟨rhs, hr, hv⟩ := rigidBindingVars_mem_iff.mp hv
        exact hRhs rhs hr v hv
    · exact ihBody v hv
  | named _ _ ih v hv => exact ih v hv
  | wildcard _ ih v hv => exact ih v hv

/-- Fixed-source transport is a corollary of source substitution and intrinsic
annotation scope; it needs only pointwise protection of the composite. -/
theorem BranchTyping.onSubst_source
    (h : BranchTyping Typing K ctx branch scrutTy resultTy) (subst : Subst)
    (hlc : ∀ p ∈ subst, p.2.IsLC)
    (hscope : ∀ k ∈ K, ∀ v ∈ (subst.onTy (.fvar k)).freeVars, v ∈ K') :
    BranchTyping Typing K' (subst.onCtx ctx) (branch.1, branch.2.substTyFvars subst)
      (subst.onTy scrutTy) (subst.onTy resultTy) := by
  cases h with
  | named hspec hb =>
    refine .named (hspec.onSubst subst hlc) ?_
    simpa only [Subst.onCtx, Subst.onEnv, List.map_append, List.map_map,
      Subst.onPolyTy, PolyTy.mkTrivial, Function.comp_def] using hb.onSubst_source subst hlc hscope
  | wildcard hb => exact .wildcard (hb.onSubst_source subst hlc hscope)

theorem Typing.scope_mono (h : Typing K ctx input ty) (hscope : ∀ k ∈ K, k ∈ K') :
    Typing K' ctx input ty := by
  have hinput : input.substTyFvars [] = input := input.substTyFvars_eq_self_of_fixes (fun _ _ => rfl)
  simpa only [Subst.onCtx_nil, Subst.onTy_nil, hinput] using
    h.onSubst_source [] (by simp) (fun k hk v hv => hscope v ((List.mem_singleton.mp hv) ▸ hk))


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



theorem Typing.generalise_opened {K Ys G : List Nat} {ctx : Ctx} {input : Input} {ty : Ty}
    (h : Typing (K ++ Ys) ctx (input.openTyVars Ys) ty)
    (hnd : (Ys ++ G).Nodup)
    (hctx : ∀ name ∈ Ys ++ G, name ∉ ctx.env.freeVars)
    (hK : ∀ name ∈ Ys ++ G, name ∉ K)
    (hsource : ∀ v ∈ input.rigidVars, v ∈ K) :
    ∃ L, ∀ Xs, FreshNames L (Ys.length + G.length) Xs →
      Typing (K ++ Xs.take Ys.length) ctx (input.openTyVars (Xs.take Ys.length))
        (Ty.openVars Xs (Ty.closeOver (Ys ++ G) ty)) := by
  refine ⟨Ys ++ G, ?_⟩
  intro Xs hXs
  have htake : (Xs.take Ys.length).length = Ys.length := by
    rw [List.length_take, hXs.length]; omega
  have hdisj : ∀ name ∈ Ys ++ G, name ∉ Xs := fun name hn hx => hXs.avoid name hx hn
  have hYtake : ∀ name ∈ Ys, name ∉ Xs.take Ys.length :=
    fun name hn hx => hdisj name (List.mem_append_left _ hn) (List.mem_of_mem_take hx)
  let RY : Subst := Ys.zip ((Xs.take Ys.length).map Ty.fvar)
  let RG : Subst := G.zip ((Xs.drop Ys.length).map Ty.fvar)
  have hRYlc : ∀ p ∈ RY, p.2.IsLC := by
    intro p hp
    obtain ⟨_, _, heq⟩ := List.mem_map.mp (List.of_mem_zip hp).2
    rw [← heq]; exact .fvar
  have hRGlc : ∀ p ∈ RG, p.2.IsLC := by
    intro p hp
    obtain ⟨_, _, heq⟩ := List.mem_map.mp (List.of_mem_zip hp).2
    rw [← heq]; exact .fvar
  have hRYK : ∀ k ∈ K, RY.onTy (.fvar k) = .fvar k := by
    intro k hk
    apply Ty.substFvars_eq_self_of_no_key
    intro p hp hc
    simp only [Ty.freeVars, List.mem_singleton] at hc
    exact hK p.1 (List.mem_append_left _ (List.of_mem_zip hp).1) (hc ▸ hk)
  have hRYscope : ∀ k ∈ K ++ Ys, ∀ v ∈ (RY.onTy (.fvar k)).freeVars, v ∈ K ++ Xs.take Ys.length := by
    intro k hk v hv
    rcases List.mem_append.mp hk with hk | hk
    · rw [hRYK k hk] at hv
      simp only [Ty.freeVars, List.mem_singleton] at hv
      exact List.mem_append_left _ (hv ▸ hk)
    · obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hk
      have hilt : i < Ys.length := (List.getElem?_eq_some_iff.mp hi).choose
      have hit : i < (Xs.take Ys.length).length := by omega
      have himg : RY.onTy (.fvar k) = .fvar ((Xs.take Ys.length)[i]) := by
        apply Ty.substFvars_zip_fvar_eq' hnd.of_append_left hi
        · simp only [List.getElem?_map, List.getElem?_eq_getElem hit, Option.map_some]
        · intro y hy hc
          simp only [Ty.freeVars, List.mem_singleton] at hc
          apply hYtake y hy
          rw [hc]
          exact List.getElem_mem hit
      rw [himg] at hv
      simp only [Ty.freeVars, List.mem_singleton] at hv
      exact List.mem_append_right _ (hv ▸ List.getElem_mem hit)
  have ctxFixed : ∀ S : Subst, (∀ p ∈ S, p.1 ∈ Ys ++ G) → S.onCtx ctx = ctx := by
    intro S hS
    have henv := Subst.onEnv_eq_self_of_fresh (fun p hp => hctx p.1 (hS p hp))
    cases ctx
    simp only [Subst.onCtx, henv]
  have hRYctx : RY.onCtx ctx = ctx := ctxFixed RY
    (fun p hp => List.mem_append_left _ (List.of_mem_zip hp).1)
  have hRGctx : RG.onCtx ctx = ctx := ctxFixed RG
    (fun p hp => List.mem_append_right _ (List.of_mem_zip hp).1)
  have hRYsource : (input.openTyVars Ys).substTyFvars RY = input.openTyVars (Xs.take Ys.length) := by
    exact input.substTyFvars_zip_openTyVars htake.symm hnd.of_append_left
      (fun y hy hv => hK y (List.mem_append_left _ hy) (hsource y hv)) hYtake
  have hfirst := h.onSubst_source RY hRYlc hRYscope
  rw [hRYctx, hRYsource] at hfirst
  have hRGavoid : ∀ p ∈ RG, p.1 ∉ K ++ Xs.take Ys.length := by
    intro p hp hc
    have hpG := (List.of_mem_zip hp).1
    rcases List.mem_append.mp hc with hk | hx
    · exact hK p.1 (List.mem_append_right _ hpG) hk
    · exact hdisj p.1 (List.mem_append_right _ hpG) (List.mem_of_mem_take hx)
  have hsecond := hfirst.onSubst RG hRGlc hRGavoid
  rw [hRGctx] at hsecond
  have hzip : (Ys ++ G).zip (Xs.map Ty.fvar) = RY ++ RG := by
    have hmap : Xs.map Ty.fvar = (Xs.take Ys.length).map Ty.fvar ++ (Xs.drop Ys.length).map Ty.fvar := by
      rw [← List.map_append, List.take_append_drop]
    rw [hmap]
    exact List.zip_append (by simp only [List.length_map, htake])
  rw [Ty.openVars_closeOver_rename h.regular hnd (by simpa only [List.length_append] using hXs.length) hdisj,
    hzip]
  change Typing (K ++ Xs.take Ys.length) ctx (input.openTyVars (Xs.take Ys.length))
    ((RY ++ RG).onTy ty)
  rw [Subst.onTy_append]
  exact hsecond




/-- Closing a checked partial signature preserves its exact written-prefix
matching at every sufficiently fresh opening of the completed scheme. -/
theorem LetAnn.SignatureCompletion.cofinite_fits {ann : LetAnn} {written names : List Nat}
    {ty : Ty} {scheme : PolyTy} {K : List Nat}
    (h : ann.SignatureCompletion written ty scheme names)
    (hnd : names.Nodup) (hK : ∀ name ∈ names, name ∉ K)
    (hsource : ∀ v ∈ ann.rigidVars, v ∈ K) (hlc : ty.IsLC) :
    ∃ L, ∀ Xs, FreshNames L scheme.paramCount Xs → ann.SignatureFits scheme Xs := by
  cases h with
  | complete => exact ⟨[], fun _ _ => .complete⟩
  | @partialSignature ty template count written extras hlen hfit =>
    refine ⟨written ++ extras, ?_⟩
    intro Xs hXs
    have htake : (Xs.take written.length).length = written.length := by
      rw [List.length_take, hXs.length]; simp only [List.length_append]; omega
    have hdisj : ∀ name ∈ written ++ extras, name ∉ Xs := fun name hn hx => hXs.avoid name hx hn
    have hYtake : ∀ name ∈ written, name ∉ Xs.take written.length :=
      fun name hn hx => hdisj name (List.mem_append_left _ hn) (List.mem_of_mem_take hx)
    let RY : Subst := written.zip ((Xs.take written.length).map Ty.fvar)
    let RG : Subst := extras.zip ((Xs.drop written.length).map Ty.fvar)
    have hRGlc : ∀ p ∈ RG, p.2.IsLC := by
      intro p hp
      obtain ⟨_, _, heq⟩ := List.mem_map.mp (List.of_mem_zip hp).2
      rw [← heq]; exact .fvar
    have hRYsource : (template.openTyVarsFrom 0 written).substTyFvars RY =
        template.openTyVarsFrom 0 (Xs.take written.length) := by
      exact template.substTyFvars_zip_openTyVarsFrom htake.symm hnd.of_append_left
        (fun y hy hv => hK y (List.mem_append_left _ hy) (hsource y hv)) hYtake 0
    have hfirst := hfit.substTyFvars RY
    rw [hRYsource] at hfirst
    have hRGfresh : ∀ p ∈ RG, p.1 ∉ Xs.take written.length := by
      intro p hp hc
      exact hdisj p.1 (List.mem_append_right _ (List.of_mem_zip hp).1) (List.mem_of_mem_take hc)
    have hRGsource : (template.openTyVarsFrom 0 (Xs.take written.length)).substTyFvars RG =
        template.openTyVarsFrom 0 (Xs.take written.length) := by
      rw [template.substTyFvars_openTyVarsFrom hRGlc hRGfresh 0]
      rw [template.substTyFvars_eq_self_of_fixes (fun v hv => by
        apply Ty.substFvars_eq_self_of_no_key
        intro p hp hc
        have heq : p.1 = v := List.mem_singleton.mp hc
        exact hK p.1 (List.mem_append_right _ (List.of_mem_zip hp).1) (heq ▸ hsource v hv))]
    have hsecond := hfirst.substTyFvars RG
    rw [hRGsource] at hsecond
    have hzip : (written ++ extras).zip (Xs.map Ty.fvar) = RY ++ RG := by
      have hmap : Xs.map Ty.fvar = (Xs.take written.length).map Ty.fvar ++ (Xs.drop written.length).map Ty.fvar := by
        rw [← List.map_append, List.take_append_drop]
      rw [hmap]
      exact List.zip_append (by simp only [List.length_map, htake])
    refine .partialSignature (by simp only [List.length_append]; omega) ?_
    change (template.openTyVarsFrom 0 (Xs.take count)).Fits
      (Ty.openVars Xs (Ty.closeOver (written ++ extras) ty))
    rw [Ty.openVars_closeOver_rename hlc hnd hXs.length hdisj, hzip]
    change (template.openTyVarsFrom 0 (Xs.take count)).Fits ((RY ++ RG).onTy ty)
    rw [Subst.onTy_append, ← hlen]
    exact hsecond


/-- Opening a completed signed scheme reopens exactly its written source
binders; inferred extra quantifiers specialize only the typing monotype. -/
theorem LetAnn.SignatureCompletion.cofinite_typing
    {ann : LetAnn} {written names K : List Nat} {ty : Ty} {scheme : PolyTy} {ctx : Ctx} {input : Input}
    (hcomp : ann.SignatureCompletion written ty scheme names)
    (ht : Typing (K ++ written) ctx (input.openTyVars written) ty)
    (hwf : scheme.WF) (hnd : names.Nodup)
    (hctx : ∀ name ∈ names, name ∉ ctx.env.freeVars)
    (hK : ∀ name ∈ names, name ∉ K)
    (hann : ∀ v ∈ ann.rigidVars, v ∈ K)
    (hsource : ∀ v ∈ input.rigidVars, v ∈ K) :
    ∃ L, ∀ Xs, FreshNames L scheme.paramCount Xs →
      Typing (K ++ Xs.take ann.paramCount) ctx (input.openTyVars (Xs.take ann.paramCount)) (scheme.openVars Xs) := by
  cases hcomp with
  | @complete ty written scheme hlen heq =>
    obtain ⟨L, hgen⟩ := ht.generalise_opened (G := [])
      (by simpa only [List.append_nil] using hnd)
      (by simpa only [List.append_nil] using hctx)
      (by simpa only [List.append_nil] using hK) hsource
    have hclose : Ty.closeOver written ty = scheme.body := by
      rw [heq, PolyTy.openVars]
      exact Ty.closeOver_openVars_self hnd (by simpa only [hlen] using hwf)
        (fun name hn hv => hK name hn (hann name hv))
    refine ⟨L, ?_⟩
    intro Xs hf
    simpa only [List.append_nil, LetAnn.paramCount, hclose, PolyTy.openVars, hlen] using
      hgen Xs (by simpa only [List.length_nil, Nat.add_zero, hlen] using hf)
  | @partialSignature ty template count written extras hlen _ =>
    obtain ⟨L, hgen⟩ := ht.generalise_opened (G := extras) hnd hctx hK hsource
    refine ⟨L, ?_⟩
    intro Xs hf
    simpa only [LetAnn.paramCount, hlen, PolyTy.openVars] using
      hgen Xs (by simpa only [List.length_append] using hf)

/-- A signed binding's cofinite contract transports under an ambient
specialization; the newly opened written variables are chosen away from its domain. -/
theorem Typing.signatureBinding_onSubst
    {ann : LetAnn} {scheme : PolyTy} {avoid : List Nat} {K : List Nat} {ctx : Ctx} {input : Input}
    (hfit : ∀ fresh, FreshNames avoid scheme.paramCount fresh → ann.SignatureFits scheme fresh)
    (htyping : ∀ fresh, FreshNames avoid scheme.paramCount fresh →
      Typing (K ++ fresh.take ann.paramCount) ctx (input.openTyVars (fresh.take ann.paramCount)) (scheme.openVars fresh))
    (hrigid : ∀ v ∈ ann.rigidVars, v ∈ K)
    (subst : Subst) (hlc : ∀ pair ∈ subst, pair.2.IsLC)
    (hprotected : ∀ pair ∈ subst, pair.1 ∉ K) :
    ∃ avoid',
      (∀ fresh, FreshNames avoid' scheme.paramCount fresh → ann.SignatureFits (subst.onPolyTy scheme) fresh) ∧
      (∀ fresh, FreshNames avoid' scheme.paramCount fresh →
        Typing (K ++ fresh.take ann.paramCount) (subst.onCtx ctx)
          (input.openTyVars (fresh.take ann.paramCount)) ((subst.onPolyTy scheme).openVars fresh)) := by
  let avoid' := avoid ++ subst.map Prod.fst
  have hold : ∀ fresh, FreshNames avoid' scheme.paramCount fresh → FreshNames avoid scheme.paramCount fresh :=
    fun fresh hf => ⟨hf.length, hf.nodup, fun v hv ha => hf.avoid v hv (List.mem_append_left _ ha)⟩
  have hdom : ∀ fresh, FreshNames avoid' scheme.paramCount fresh → ∀ pair ∈ subst, pair.1 ∉ fresh := by
    intro fresh hf pair hp hv
    exact hf.avoid pair.1 hv (List.mem_append_right _ (List.mem_map.mpr ⟨pair, hp, rfl⟩))
  refine ⟨avoid', ?_, ?_⟩
  · intro fresh hf
    have hfit' := (hfit fresh (hold fresh hf)).onSubst_source subst hlc (hdom fresh hf)
    rwa [ann.substTyFvars_eq_self_of_fixes (fun v hv => Subst.fixes_of_dom_avoids hprotected v (hrigid v hv))] at hfit'
  · intro fresh hf
    have hprotected' : ∀ pair ∈ subst, pair.1 ∉ K ++ fresh.take ann.paramCount := by
      intro pair hp hmem
      rcases List.mem_append.mp hmem with hmem | hmem
      · exact hprotected pair hp hmem
      · exact hdom fresh hf pair hp (List.mem_of_mem_take hmem)
    have ht := (htyping fresh (hold fresh hf)).onSubst subst hlc hprotected'
    simpa only [Subst.onPolyTy, PolyTy.openVars, Subst.onTy_openVars hlc (hdom fresh hf)] using ht

/-- Cofinite binding premises transport together with authored source syntax. -/
theorem Typing.binding_onSubst_source {ann : LetAnn} {scheme : PolyTy} {avoid : List Nat}
    (hfit : ∀ fresh, FreshNames avoid scheme.paramCount fresh → ann.FitsMono (scheme.openVars fresh))
    (htyping : ∀ fresh, FreshNames avoid scheme.paramCount fresh → Typing K ctx input (scheme.openVars fresh))
    (subst : Subst) (hlc : ∀ pair ∈ subst, pair.2.IsLC)
    (hscope : ∀ k ∈ K, ∀ v ∈ (subst.onTy (.fvar k)).freeVars, v ∈ K') :
    ∃ avoid',
      (∀ fresh, FreshNames avoid' scheme.paramCount fresh →
        (ann.substTyFvars subst).FitsMono ((subst.onPolyTy scheme).openVars fresh)) ∧
      (∀ fresh, FreshNames avoid' scheme.paramCount fresh →
        Typing K' (subst.onCtx ctx) (input.substTyFvars subst) ((subst.onPolyTy scheme).openVars fresh)) := by
  let avoid' := avoid ++ subst.map Prod.fst
  have hold : ∀ fresh, FreshNames avoid' scheme.paramCount fresh → FreshNames avoid scheme.paramCount fresh :=
    fun fresh hf => ⟨hf.length, hf.nodup, fun v hv ha => hf.avoid v hv (List.mem_append_left _ ha)⟩
  have hdom : ∀ fresh, FreshNames avoid' scheme.paramCount fresh → ∀ pair ∈ subst, pair.1 ∉ fresh := by
    intro fresh hf pair hp hv
    exact hf.avoid pair.1 hv (List.mem_append_right _ (List.mem_map.mpr ⟨pair, hp, rfl⟩))
  refine ⟨avoid', ?_, ?_⟩
  · intro fresh hf
    simpa only [PolyTy.openVars, Subst.onPolyTy, Subst.onTy_openVars hlc (hdom fresh hf)] using
      fitsMono_sourceSubst (hfit fresh (hold fresh hf)) subst
  · intro fresh hf
    simpa only [PolyTy.openVars, Subst.onPolyTy, Subst.onTy_openVars hlc (hdom fresh hf)] using
      (htyping fresh (hold fresh hf)).onSubst_source subst hlc hscope

/-- Scoped written openings also transport; fresh binders are protected only
inside the RHS premise. -/
theorem Typing.signatureBinding_onSubst_source
    {ann : LetAnn} {scheme : PolyTy} {avoid : List Nat} {K K' : List Nat} {ctx : Ctx} {input : Input}
    (hfit : ∀ fresh, FreshNames avoid scheme.paramCount fresh → ann.SignatureFits scheme fresh)
    (htyping : ∀ fresh, FreshNames avoid scheme.paramCount fresh →
      Typing (K ++ fresh.take ann.paramCount) ctx (input.openTyVars (fresh.take ann.paramCount)) (scheme.openVars fresh))
    (subst : Subst) (hlc : ∀ pair ∈ subst, pair.2.IsLC)
    (hscope : ∀ k ∈ K, ∀ v ∈ (subst.onTy (.fvar k)).freeVars, v ∈ K') :
    ∃ avoid',
      (∀ fresh, FreshNames avoid' scheme.paramCount fresh →
        (ann.substTyFvars subst).SignatureFits (subst.onPolyTy scheme) fresh) ∧
      (∀ fresh, FreshNames avoid' scheme.paramCount fresh →
        Typing (K' ++ fresh.take (ann.substTyFvars subst).paramCount) (subst.onCtx ctx)
          ((input.substTyFvars subst).openTyVars (fresh.take (ann.substTyFvars subst).paramCount))
          ((subst.onPolyTy scheme).openVars fresh)) := by
  let avoid' := avoid ++ subst.map Prod.fst
  have hold : ∀ fresh, FreshNames avoid' scheme.paramCount fresh → FreshNames avoid scheme.paramCount fresh :=
    fun fresh hf => ⟨hf.length, hf.nodup, fun v hv ha => hf.avoid v hv (List.mem_append_left _ ha)⟩
  have hdom : ∀ fresh, FreshNames avoid' scheme.paramCount fresh → ∀ pair ∈ subst, pair.1 ∉ fresh := by
    intro fresh hf pair hp hv
    exact hf.avoid pair.1 hv (List.mem_append_right _ (List.mem_map.mpr ⟨pair, hp, rfl⟩))
  refine ⟨avoid', ?_, ?_⟩
  · intro fresh hf
    exact (hfit fresh (hold fresh hf)).onSubst_source subst hlc (hdom fresh hf)
  · intro fresh hf
    have hsmall : ∀ pair ∈ subst, pair.1 ∉ fresh.take ann.paramCount :=
      fun pair hp hv => hdom fresh hf pair hp (List.mem_of_mem_take hv)
    have ht := (htyping fresh (hold fresh hf)).onSubst_source subst hlc
      (K' := K' ++ fresh.take ann.paramCount) (fun k hk v hv => by
        rcases List.mem_append.mp hk with hk | hk
        · exact List.mem_append_left _ (hscope k hk v hv)
        · have hfix : subst.onTy (.fvar k) = .fvar k := by
            apply Ty.substFvars_eq_self_of_no_key
            intro pair hp hc
            exact hsmall pair hp ((List.mem_singleton.mp hc) ▸ hk)
          rw [hfix] at hv
          exact List.mem_append_right _ ((List.mem_singleton.mp hv) ▸ hk))
    simpa only [LetAnn.paramCount_substTyFvars,
      Input.substTyFvars_openTyVars _ hlc hsmall, PolyTy.openVars, Subst.onPolyTy,
      Subst.onTy_openVars hlc (hdom fresh hf)] using ht

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

private theorem Expr.substTyFvars_openTyVars_lc (expr : Expr) {S : Subst} {Xs : List Nat}
    (hlc : ∀ p ∈ S, p.2.IsLC) (hfresh : ∀ p ∈ S, p.1 ∉ Xs) :
    (expr.openTyVars Xs).substTyFvars S = (expr.substTyFvars S).openTyVars Xs := by
  induction S generalizing expr with
  | nil => rfl
  | cons p rest ih =>
    rcases p with ⟨v, ty⟩
    simp only [Expr.substTyFvars]
    rw [Expr.substTyFvar_openTyVars (hlc _ List.mem_cons_self) (hfresh _ List.mem_cons_self)]
    exact ih _ (fun p hp => hlc p (List.mem_cons_of_mem _ hp))
      (fun p hp => hfresh p (List.mem_cons_of_mem _ hp))


namespace Elaboration

/-- Global LC transport is a paired cofinite induction; no closing algebra or
choice of renamed internal witnesses is needed. -/

theorem LetAnn.BindingFits.onSubst_source {ann : LetAnn} {scheme : PolyTy} {Xs : List Nat}
    (h : ann.BindingFits scheme Xs) (S : Subst)
    (hlc : ∀ p ∈ S, p.2.IsLC) (hdom : ∀ p ∈ S, p.1 ∉ Xs) :
    (ann.substTyFvars S).BindingFits (S.onPolyTy scheme) Xs := by
  unfold LetAnn.BindingFits at h ⊢
  rw [LetAnn.isSignature_substTyFvars]
  cases hm : ann.isSignature with
  | false =>
    simp only [hm, Bool.false_eq_true, if_false] at h ⊢
    have hh := fitsMono_sourceSubst h S
    simpa only [PolyTy.openVars, Subst.onPolyTy, Subst.onTy_openVars hlc hdom] using hh
  | true =>
    simp only [hm, if_true] at h ⊢
    exact h.onSubst_source S hlc hdom

theorem Completes.onSubst_source (h : Completes K input output) (S : Subst)
    (hlc : ∀ p ∈ S, p.2.IsLC)
    (hscope : ∀ k ∈ K, ∀ v ∈ (S.onTy (.fvar k)).freeVars, v ∈ K') :
    Completes K' (input.substTyFvars S) (output.substTyFvars S) := by
  induction h using Completes.rec
      (motive_2 := fun K branches branchesOut _ => ∀ {K'},
        (∀ k ∈ K, ∀ v ∈ (S.onTy (.fvar k)).freeVars, v ∈ K') →
        CompletedBranches Completes K' (substInputBranches S branches)
          (branchesOut.map fun (pat, body) => (pat, body.substTyFvars S))) generalizing K' with
  | @complete core K input hemb hr =>
    refine .complete (input.toCore_substTyFvars hemb S) ?_
    intro v hv
    obtain ⟨k, hk, hv⟩ := Expr.mem_tyFreeVars_substTyFvars_image hv
    exact hscope k (hr k hk) v hv
  | @lambda ann K body completed param hfit hr _ ih =>
    rw [Expr.substTyFvars_lambda]
    cases ann with
    | none =>
      simpa only [Input.substTyFvars, Option.map_none] using
        (Completes.lambda (ann := none) (param := S.onTy param)
          (fun _ h => by cases h) (fun _ h => by cases h) (ih hscope))
    | some original =>
      simp only [Input.substTyFvars, Option.map_some]
      refine .lambda ?_ ?_ (ih hscope)
      · intro template heq
        cases heq
        exact (hfit original rfl).substTyFvars S
      · intro template heq
        cases heq
        exact template_scope_sourceSubst (hr original rfl) hscope

  | app _ _ ihf ihx =>
    rw [Expr.substTyFvars_app]
    exact .app (ihf hscope) (ihx hscope)
  | @letIn ann K rhs body bodyOut rhsOut M L hr hfit _ _ ihr ihb =>
    let L' := L ++ S.map Prod.fst
    have oldFresh : ∀ Xs, FreshNames L' M.paramCount Xs → FreshNames L M.paramCount Xs :=
      fun Xs hf => ⟨hf.length, hf.nodup, fun v hv hm => hf.avoid v hv (List.mem_append_left _ hm)⟩
    have domFresh : ∀ Xs, FreshNames L' M.paramCount Xs → ∀ p ∈ S, p.1 ∉ Xs := by
      intro Xs hf p hp hv
      exact hf.avoid p.1 hv (List.mem_append_right _ (List.mem_map.mpr ⟨p, hp, rfl⟩))
    rw [Expr.substTyFvars_letIn]
    refine Completes.letIn (M := S.onPolyTy M) (L := L') ?_ ?_ ?_ (ihb hscope)
    · intro template heq
      cases ann with
      | absent | complete _ | partialForall _ _ => cases heq
      | template original =>
        cases heq
        exact template_scope_sourceSubst (hr original rfl) hscope
    · intro Xs hf
      have hfit' := fitsMono_sourceSubst (hfit Xs (oldFresh Xs hf)) S
      simpa only [PolyTy.openVars, Subst.onPolyTy, Subst.onTy_openVars hlc (domFresh Xs hf)] using hfit'
    · intro Xs hf
      have hc := ihr Xs (oldFresh Xs hf) hscope
      simpa only [Expr.substTyFvars_openTyVars_lc _ hlc (domFresh Xs hf)] using hc
  | @letSignature K body bodyOut ann rhs rhsOut M L hann hrhs hfit _ _ ihr ihb =>
    let L' := L ++ S.map Prod.fst
    have oldFresh : ∀ Xs, FreshNames L' M.paramCount Xs → FreshNames L M.paramCount Xs :=
      fun Xs hf => ⟨hf.length, hf.nodup, fun v hv hm => hf.avoid v hv (List.mem_append_left _ hm)⟩
    have domFresh : ∀ Xs, FreshNames L' M.paramCount Xs → ∀ p ∈ S, p.1 ∉ Xs := by
      intro Xs hf p hp hv
      exact hf.avoid p.1 hv (List.mem_append_right _ (List.mem_map.mpr ⟨p, hp, rfl⟩))
    rw [Expr.substTyFvars_letIn]
    refine Completes.letSignature (M := S.onPolyTy M) (L := L') ?_ ?_ ?_ ?_ (ihb hscope)
    · intro v hv
      obtain ⟨k, hk, hv⟩ := LetAnn.rigidVars_substTyFvars hv
      exact hscope k (hann k hk) v hv
    · intro v hv
      obtain ⟨k, hk, hv⟩ := Input.rigidVars_substTyFvars hv
      exact hscope k (hrhs k hk) v hv
    · intro Xs hf
      exact (hfit Xs (oldFresh Xs hf)).onSubst_source S hlc (domFresh Xs hf)
    · intro Xs hf
      have hsmall : ∀ p ∈ S, p.1 ∉ Xs.take ann.paramCount :=
        fun p hp hv => domFresh Xs hf p hp (List.mem_of_mem_take hv)
      have hc := ihr Xs (oldFresh Xs hf) (K' := K' ++ Xs.take ann.paramCount) (fun k hk v hv => by
        rcases List.mem_append.mp hk with hk | hk
        · exact List.mem_append_left _ (hscope k hk v hv)
        · rw [Subst.fixes_of_dom_avoids hsmall k hk] at hv
          exact List.mem_append_right _ ((List.mem_singleton.mp hv) ▸ hk))
      simpa only [LetAnn.paramCount_substTyFvars, Input.substTyFvars_openTyVars _ hlc hsmall,
        Expr.substTyFvars_openTyVars_lc _ hlc (domFresh Xs hf)] using hc
  | match_ _ _ ihs ihbs =>
    rw [Expr.substTyFvars_match]
    exact .match_ (ihs hscope) (ihbs hscope)
  | letRec hlenA hlenR hlenO hAnn hRhs hFits _ _ ihChildren ihBody =>
    expose_names
    let L' := L ++ S.map Prod.fst
    have oldFresh : ∀ (scheme : PolyTy) (Xs : List Nat), FreshNames L' scheme.paramCount Xs → FreshNames L scheme.paramCount Xs :=
      fun scheme Xs hf => ⟨hf.length, hf.nodup, fun v hv hm => hf.avoid v hv (List.mem_append_left _ hm)⟩
    have domFresh : ∀ (scheme : PolyTy) (Xs : List Nat), FreshNames L' scheme.paramCount Xs → ∀ p ∈ S, p.1 ∉ Xs := by
      intro scheme Xs hf p hp hv
      exact hf.avoid p.1 hv (List.mem_append_right _ (List.mem_map.mpr ⟨p, hp, rfl⟩))
    simp only [Input.substTyFvars, substInputBindings_eq_map_source, Expr.substTyFvars_letRec]
    rw [show (schemes.map some).map (RecAnn.substFvars S) = (schemes.map S.onPolyTy).map some by
      simp only [List.map_map, Function.comp_def, RecAnn.substFvars_some, PolyTy.substFvars_eq]; rfl]
    refine Completes.letRec (schemes := schemes.map S.onPolyTy) (L := L')
      (by simpa only [List.length_map] using hlenA)
      (by simpa only [List.length_map] using hlenR)
      (by simpa only [List.length_map] using hlenO) ?_ ?_ ?_ ?_ (ihBody hscope)
    · intro ann ha v hv
      obtain ⟨original, ho, rfl⟩ := List.mem_map.mp ha
      obtain ⟨k, hk, himage⟩ := LetAnn.rigidVars_substTyFvars hv
      exact hscope k (hAnn original ho k hk) v himage
    · intro rhs hr v hv
      obtain ⟨original, ho, rfl⟩ := List.mem_map.mp hr
      obtain ⟨k, hk, himage⟩ := Input.rigidVars_substTyFvars hv
      exact hscope k (hRhs original ho k hk) v himage
    · intro member ann rhs output scheme ha hr ho hs Xs hf
      rw [List.getElem?_map] at ha hr ho hs
      obtain ⟨ann0, ha0, rfl⟩ := Option.map_eq_some_iff.mp ha
      obtain ⟨rhs0, hr0, rfl⟩ := Option.map_eq_some_iff.mp hr
      obtain ⟨output0, ho0, rfl⟩ := Option.map_eq_some_iff.mp ho
      obtain ⟨scheme0, hs0, rfl⟩ := Option.map_eq_some_iff.mp hs
      exact (hFits member ann0 rhs0 output0 scheme0 ha0 hr0 ho0 hs0 Xs (oldFresh scheme0 Xs hf)).onSubst_source
        S hlc (domFresh scheme0 Xs hf)
    · intro member ann rhs output scheme ha hr ho hs Xs hf
      rw [List.getElem?_map] at ha hr ho hs
      obtain ⟨ann0, ha0, rfl⟩ := Option.map_eq_some_iff.mp ha
      obtain ⟨rhs0, hr0, rfl⟩ := Option.map_eq_some_iff.mp hr
      obtain ⟨output0, ho0, rfl⟩ := Option.map_eq_some_iff.mp ho
      obtain ⟨scheme0, hs0, rfl⟩ := Option.map_eq_some_iff.mp hs
      have hsmall : ∀ p ∈ S, p.1 ∉ Xs.take ann0.paramCount :=
        fun p hp hv => domFresh scheme0 Xs hf p hp (List.mem_of_mem_take hv)
      have hc := ihChildren member ann0 rhs0 output0 scheme0 ha0 hr0 ho0 hs0 Xs (oldFresh scheme0 Xs hf)
        (K' := K' ++ Xs.take ann0.paramCount) (fun k hk v hv => by
          rcases List.mem_append.mp hk with hk | hk
          · exact List.mem_append_left _ (hscope k hk v hv)
          · rw [Subst.fixes_of_dom_avoids hsmall k hk] at hv
            exact List.mem_append_right _ ((List.mem_singleton.mp hv) ▸ hk))
      simpa only [LetAnn.paramCount_substTyFvars, Input.substTyFvars_openTyVars _ hlc hsmall,
        Expr.substTyFvars_openTyVars_lc _ hlc (domFresh scheme0 Xs hf)] using hc
  | nil => exact .nil
  | cons _ _ ih ihs hscope => exact .cons (ih hscope) (ihs hscope)

end Elaboration

namespace Elaboration

theorem Completes.rigidVars (h : Completes K input output) :
    ∀ v ∈ input.rigidVars, v ∈ K := by
  induction h using Completes.rec
      (motive_2 := fun K branches _ _ => ∀ v ∈ rigidBranchVars branches, v ∈ K) with
  | complete hemb hr => exact fun v hv => hr v ((Input.toCore_rigidVars _ hemb v).mp hv)
  | lambda _ hr _ ih =>
    intro v hv
    rcases List.mem_append.mp hv with hv | hv
    · expose_names
      cases ann with
      | none => cases hv
      | some t => exact hr t rfl v hv
    · exact ih v hv
  | app _ _ ihf ihx => exact fun v hv => (List.mem_append.mp hv).elim (ihf v) (ihx v)
  | @letIn ann K rhs body bodyOut rhsOut M L hr hf _ _ ihr ihb =>
    obtain ⟨Xs, hlen, hnd, hav⟩ := exists_fresh_names L M.paramCount
    have hFresh : FreshNames L M.paramCount Xs := ⟨hlen, hnd, hav⟩
    intro v hv
    rcases List.mem_append.mp hv with hv | hv
    · rcases List.mem_append.mp hv with hv | hv
      · cases ann with
        | absent => cases hv
        | template t => exact hr t rfl v hv
        | complete _ => cases hf Xs hFresh
        | partialForall _ _ => cases hf Xs hFresh
      · exact ihr Xs hFresh v hv
    · exact ihb v hv
  | letSignature hann hrhs _ _ _ _ ihb =>
    intro v hv
    rcases List.mem_append.mp hv with hv | hv
    · exact (List.mem_append.mp hv).elim (hann v) (hrhs v)
    · exact ihb v hv
  | match_ _ _ ihs ihbs => exact fun v hv => (List.mem_append.mp hv).elim (ihs v) (ihbs v)
  | letRec _ _ _ hAnn hRhs _ _ _ _ ihBody =>
    intro v hv
    rcases List.mem_append.mp hv with hv | hv
    · rcases List.mem_append.mp hv with hv | hv
      · obtain ⟨ann, ha, hv⟩ := List.mem_flatMap.mp hv
        exact hAnn ann ha v hv
      · obtain ⟨rhs, hr, hv⟩ := rigidBindingVars_mem_iff.mp hv
        exact hRhs rhs hr v hv
    · exact ihBody v hv
  | nil v hv => cases hv
  | cons _ _ ih ihs v hv => exact (List.mem_append.mp hv).elim (ih v) (ihs v)

/-- LC specialization is derived, rather than an unrestricted constructor. -/
theorem Completes.scope_mono (h : Completes K input output) (hscope : ∀ k ∈ K, k ∈ K') :
    Completes K' input output := by
  have hinput : input.substTyFvars [] = input := input.substTyFvars_eq_self_of_fixes (fun _ _ => rfl)
  simpa only [hinput, Expr.substTyFvars] using
    h.onSubst_source [] (by simp) (fun k hk v hv => hscope v ((List.mem_singleton.mp hv) ▸ hk))

theorem Completes.onSubst_fixes (h : Completes K input output) (S : Subst)
    (hlc : ∀ p ∈ S, p.2.IsLC) (hfix : ∀ k ∈ K, S.onTy (.fvar k) = .fvar k) :
    Completes K input (output.substTyFvars S) := by
  have ht := h.onSubst_source S hlc (fun k hk v hv => by
    rw [hfix k hk] at hv
    exact (List.mem_singleton.mp hv) ▸ hk)
  rwa [input.substTyFvars_eq_self_of_fixes (fun v hv => hfix v (h.rigidVars v hv))] at ht

theorem Completes.specialise (h : Completes K input output) (S : Subst)
    (hlc : ∀ p ∈ S, p.2.IsLC) (hdom : ∀ p ∈ S, p.1 ∉ K) :
    Completes K input (output.substTyFvars S) :=
  h.onSubst_fixes S hlc (Subst.fixes_of_dom_avoids hdom)

/-- Generated closing witnesses yield exact cofinite output openings. This uses
only the already established scope of the completed RHS. -/
theorem Completes.generalise_closed (h : Completes K input output) {names : List Nat}
    (hnd : names.Nodup) (hK : ∀ name ∈ names, name ∉ K)
    (hb : output.TyBvarBounded 0) :
    ∀ Xs, FreshNames names names.length Xs →
      Completes K input ((output.closeTyVars names).openTyVars Xs) := by
  intro Xs hf
  rw [Expr.open_closeTyVars_rename hnd hf.length
    (fun name hn hx => hf.avoid name hx hn) hb]
  apply h.specialise
  · intro p hp
    obtain ⟨_, _, heq⟩ := List.mem_map.mp (List.of_mem_zip hp).2
    rw [← heq]
    exact .fvar
  · intro p hp
    exact hK p.1 (List.of_mem_zip hp).1

end Elaboration

namespace Elaboration
/-- A generated signed prefix is renamed together with the full output binder
block. Only the authored prefix enters the child's protected source scope. -/
theorem Completes.generalise_opened {K Ys G : List Nat} {input : Input} {output : Expr}
    (h : Completes (K ++ Ys) (input.openTyVars Ys) output)
    (hnd : (Ys ++ G).Nodup) (hK : ∀ name ∈ Ys ++ G, name ∉ K)
    (hsource : ∀ v ∈ input.rigidVars, v ∈ K) (hbound : output.TyBvarBounded 0) :
    ∃ L, ∀ Xs, FreshNames L (Ys.length + G.length) Xs →
      Completes (K ++ Xs.take Ys.length) (input.openTyVars (Xs.take Ys.length))
        ((output.closeTyVars (Ys ++ G)).openTyVars Xs) := by
  refine ⟨Ys ++ G, ?_⟩
  intro Xs hXs
  have htake : (Xs.take Ys.length).length = Ys.length := by
    rw [List.length_take, hXs.length]; omega
  have hdisj : ∀ name ∈ Ys ++ G, name ∉ Xs := fun name hn hx => hXs.avoid name hx hn
  have hYtake : ∀ name ∈ Ys, name ∉ Xs.take Ys.length :=
    fun name hn hx => hdisj name (List.mem_append_left _ hn) (List.mem_of_mem_take hx)
  let RY : Subst := Ys.zip ((Xs.take Ys.length).map Ty.fvar)
  let RG : Subst := G.zip ((Xs.drop Ys.length).map Ty.fvar)
  have hRYlc : ∀ p ∈ RY, p.2.IsLC := by
    intro p hp
    obtain ⟨_, _, heq⟩ := List.mem_map.mp (List.of_mem_zip hp).2
    rw [← heq]; exact .fvar
  have hRGlc : ∀ p ∈ RG, p.2.IsLC := by
    intro p hp
    obtain ⟨_, _, heq⟩ := List.mem_map.mp (List.of_mem_zip hp).2
    rw [← heq]; exact .fvar
  have hRYK : ∀ k ∈ K, RY.onTy (.fvar k) = .fvar k := by
    intro k hk
    apply Ty.substFvars_eq_self_of_no_key
    intro p hp hc
    simp only [Ty.freeVars, List.mem_singleton] at hc
    exact hK p.1 (List.mem_append_left _ (List.of_mem_zip hp).1) (hc ▸ hk)
  have hRYscope : ∀ k ∈ K ++ Ys, ∀ v ∈ (RY.onTy (.fvar k)).freeVars, v ∈ K ++ Xs.take Ys.length := by
    intro k hk v hv
    rcases List.mem_append.mp hk with hk | hk
    · rw [hRYK k hk] at hv
      simp only [Ty.freeVars, List.mem_singleton] at hv
      exact List.mem_append_left _ (hv ▸ hk)
    · obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hk
      have hilt : i < Ys.length := (List.getElem?_eq_some_iff.mp hi).choose
      have hit : i < (Xs.take Ys.length).length := by omega
      have himg : RY.onTy (.fvar k) = .fvar ((Xs.take Ys.length)[i]) := by
        apply Ty.substFvars_zip_fvar_eq' hnd.of_append_left hi
        · simp only [List.getElem?_map, List.getElem?_eq_getElem hit, Option.map_some]
        · intro y hy hc
          simp only [Ty.freeVars, List.mem_singleton] at hc
          apply hYtake y hy
          rw [hc]
          exact List.getElem_mem hit
      rw [himg] at hv
      simp only [Ty.freeVars, List.mem_singleton] at hv
      exact List.mem_append_right _ (hv ▸ List.getElem_mem hit)
  have hRYsource : (input.openTyVars Ys).substTyFvars RY = input.openTyVars (Xs.take Ys.length) := by
    exact input.substTyFvars_zip_openTyVars htake.symm hnd.of_append_left
      (fun y hy hv => hK y (List.mem_append_left _ hy) (hsource y hv)) hYtake
  have hfirst := h.onSubst_source RY hRYlc hRYscope
  rw [hRYsource] at hfirst
  have hRGavoid : ∀ p ∈ RG, p.1 ∉ K ++ Xs.take Ys.length := by
    intro p hp hc
    have hpG := (List.of_mem_zip hp).1
    rcases List.mem_append.mp hc with hk | hx
    · exact hK p.1 (List.mem_append_right _ hpG) hk
    · exact hdisj p.1 (List.mem_append_right _ hpG) (List.mem_of_mem_take hx)
  have hsecond := hfirst.specialise RG hRGlc hRGavoid
  have hzip : (Ys ++ G).zip (Xs.map Ty.fvar) = RY ++ RG := by
    have hmap : Xs.map Ty.fvar = (Xs.take Ys.length).map Ty.fvar ++ (Xs.drop Ys.length).map Ty.fvar := by
      rw [← List.map_append, List.take_append_drop]
    rw [hmap]
    exact List.zip_append (by simp only [List.length_map, htake])
  rw [Expr.open_closeTyVars_rename hnd
    (by simpa only [List.length_append] using hXs.length) hdisj hbound, hzip,
    Expr.substTyFvars_append]
  exact hsecond

end Elaboration

namespace Elaboration

/-- Closing generated names and then changing the source needs no pointwise
fixing of the old protected set. Only the new opening avoids S's domain. -/
theorem Completes.generalise_closed_after_source (h : Completes Q input output) {names : List Nat}
    (hnd : names.Nodup) (hQ : ∀ name ∈ names, name ∉ Q)
    (hb : output.TyBvarBounded 0) (S : Subst)
    (hlc : ∀ p ∈ S, p.2.IsLC)
    (hscope : ∀ q ∈ Q, ∀ v ∈ (S.onTy (.fvar q)).freeVars, v ∈ Q') :
    ∃ L, ∀ Xs, FreshNames L names.length Xs →
      Completes Q' (input.substTyFvars S)
        (((output.closeTyVars names).substTyFvars S).openTyVars Xs) := by
  refine ⟨names ++ S.map Prod.fst, ?_⟩
  intro Xs hf
  have hXs : FreshNames names names.length Xs :=
    ⟨hf.length, hf.nodup, fun x hx hm => hf.avoid x hx (List.mem_append_left _ hm)⟩
  have hS : ∀ p ∈ S, p.1 ∉ Xs := by
    intro p hp hv
    exact hf.avoid p.1 hv (List.mem_append_right _ (List.mem_map.mpr ⟨p, hp, rfl⟩))
  have ht := (h.generalise_closed hnd hQ hb Xs hXs).onSubst_source S hlc hscope
  simpa only [Expr.substTyFvars_openTyVars_lc _ hlc hS] using ht


/-- A cofinite signed completion transports without fixing the old scope. Only
new opening names, chosen outside S's domain, stay fixed in the child scope. -/
theorem Completes.signatureBinding_onSubst_source
    {Q Q' : List Nat} {input : Input} {rhsOut : Expr} {ann : LetAnn} {M : PolyTy} {avoid : List Nat}
    (h : ∀ Xs, FreshNames avoid M.paramCount Xs →
      Completes (Q ++ Xs.take ann.paramCount) (input.openTyVars (Xs.take ann.paramCount))
        (rhsOut.openTyVars Xs))
    (S : Subst) (hlc : ∀ p ∈ S, p.2.IsLC)
    (hscope : ∀ q ∈ Q, ∀ v ∈ (S.onTy (.fvar q)).freeVars, v ∈ Q') :
    ∃ avoid', ∀ Xs, FreshNames avoid' M.paramCount Xs →
      Completes (Q' ++ Xs.take ann.paramCount)
        ((input.substTyFvars S).openTyVars (Xs.take ann.paramCount))
        ((rhsOut.substTyFvars S).openTyVars Xs) := by
  refine ⟨avoid ++ S.map Prod.fst, ?_⟩
  intro Xs hf
  have hXs : FreshNames avoid M.paramCount Xs :=
    ⟨hf.length, hf.nodup, fun x hx hm => hf.avoid x hx (List.mem_append_left _ hm)⟩
  have hS : ∀ p ∈ S, p.1 ∉ Xs := by
    intro p hp hv
    exact hf.avoid p.1 hv (List.mem_append_right _ (List.mem_map.mpr ⟨p, hp, rfl⟩))
  have hsmall : ∀ p ∈ S, p.1 ∉ Xs.take ann.paramCount :=
    fun p hp hv => hS p hp (List.mem_of_mem_take hv)
  have ht := (h Xs hXs).onSubst_source S hlc
    (K' := Q' ++ Xs.take ann.paramCount) (fun q hq v hv => by
      rcases List.mem_append.mp hq with hq | hq
      · exact List.mem_append_left _ (hscope q hq v hv)
      · rw [Subst.fixes_of_dom_avoids hsmall q hq] at hv
        exact List.mem_append_right _ ((List.mem_singleton.mp hv) ▸ hq))
  simpa only [Input.substTyFvars_openTyVars _ hlc hsmall,
    Expr.substTyFvars_openTyVars_lc _ hlc hS] using ht

/-- The generated signature certificate supplies exactly the prefix/full-block
length correspondence needed by the cofinite completion constructor. -/
theorem LetAnn.SignatureCompletion.cofinite_completes
    {ann : LetAnn} {written names Q : List Nat} {ty : Ty} {M : PolyTy}
    {input : Input} {output : Expr}
    (hcomp : ann.SignatureCompletion written ty M names)
    (h : Completes (Q ++ written) (input.openTyVars written) output)
    (hnd : names.Nodup) (hQ : ∀ name ∈ names, name ∉ Q)
    (hsource : ∀ v ∈ input.rigidVars, v ∈ Q) (hb : output.TyBvarBounded 0) :
    ∃ L, ∀ Xs, FreshNames L M.paramCount Xs →
      Completes (Q ++ Xs.take ann.paramCount) (input.openTyVars (Xs.take ann.paramCount))
        ((output.closeTyVars names).openTyVars Xs) := by
  cases hcomp with
  | complete hlen _ =>
    obtain ⟨L, hgen⟩ := h.generalise_opened (G := []) (by simpa using hnd)
      (by simpa using hQ) hsource hb
    refine ⟨L, ?_⟩
    intro Xs hf
    simpa only [List.append_nil, LetAnn.paramCount, hlen] using
      hgen Xs (by simpa only [List.length_nil, Nat.add_zero, hlen] using hf)
  | partialSignature hlen _ =>
    obtain ⟨L, hgen⟩ := h.generalise_opened hnd hQ hsource hb
    refine ⟨L, ?_⟩
    intro Xs hf
    simpa only [LetAnn.paramCount, hlen] using
      hgen Xs (by simpa only [List.length_append] using hf)

end Elaboration


/-- Opening follows the pointwise images of its provisional roots. No
freshness, injectivity, or literal domain avoidance is required. -/
theorem Subst.onTy_openVarsFrom_of_images {S : Subst} {roots resolved : List Nat}
    (hlc : ∀ p ∈ S, p.2.IsLC)
    (himages : roots.map (fun x => S.onTy (.fvar x)) = resolved.map Ty.fvar)
    (ty : Ty) (depth : Nat) :
    S.onTy (Ty.openVarsFrom depth roots ty) = Ty.openVarsFrom depth resolved (S.onTy ty) := by
  induction ty using Ty.rec_strong with
  | prim p => simp only [Ty.openVarsFrom, Ty.instantiate, Subst.onTy_prim]
  | bvar i =>
    simp only [Subst.onTy_bvar, Ty.openVarsFrom, Ty.instantiate]
    by_cases hi : i < depth
    · simp only [if_pos hi, Subst.onTy_bvar]
    · simp only [if_neg hi]
      have hg := congrArg (fun ts : List Ty => ts[i - depth]?) himages
      cases hr : roots[i - depth]? <;> cases hd : resolved[i - depth]?
      · exact Subst.onTy_bvar
      · simp only [List.getElem?_map, hr, hd, Option.map_none, Option.map_some] at hg
        cases hg
      · simp only [List.getElem?_map, hr, hd, Option.map_none, Option.map_some] at hg
        cases hg
      · simp only [List.getElem?_map, hr, hd, Option.map_some] at hg
        exact Option.some.inj hg
  | fvar v =>
    change S.onTy (.fvar v) = Ty.openVarsFrom depth resolved (S.onTy (.fvar v))
    exact (Ty.instantiate_eq_self_of_lc (Subst.onTy_lc hlc .fvar)).symm
  | arrow a b iha ihb =>
    simp only [Ty.openVarsFrom, Ty.instantiate, Subst.onTy_arrow] at *
    exact congrArg₂ Ty.arrow iha ihb
  | customTy name args ih =>
    simp only [Ty.openVarsFrom, Ty.instantiate, TyList.instantiate_eq_map,
      Subst.onTy_customTy, List.map_map]
    congr 1
    exact List.map_congr_left (fun t ht => ih t ht)

theorem Subst.onTy_openVars_of_images {S : Subst} {roots resolved : List Nat}
    (hlc : ∀ p ∈ S, p.2.IsLC)
    (himages : roots.map (fun x => S.onTy (.fvar x)) = resolved.map Ty.fvar) {ty : Ty} :
    S.onTy (Ty.openVars roots ty) = Ty.openVars resolved (S.onTy ty) := by
  simpa only [Ty.openVarsFrom, Nat.not_lt_zero, if_false, Nat.sub_zero, Ty.openVars] using
    Subst.onTy_openVarsFrom_of_images hlc himages ty 0

namespace Elaboration

mutual
theorem Template.substTyFvars_openTyVarsFrom_of_images (template : Template) {S : Subst} {roots resolved : List Nat}
    (hlc : ∀ p ∈ S, p.2.IsLC)
    (himages : roots.map (fun x => S.onTy (.fvar x)) = resolved.map Ty.fvar) (depth : Nat) :
    (template.openTyVarsFrom depth roots).substTyFvars S =
      (template.substTyFvars S).openTyVarsFrom depth resolved := by
  cases template with
  | fixed ty => exact congrArg Template.fixed (Subst.onTy_openVarsFrom_of_images hlc himages ty depth)
  | hole => rfl
  | arrow a b =>
    simp only [Template.openTyVarsFrom, Template.substTyFvars,
      a.substTyFvars_openTyVarsFrom_of_images hlc himages depth,
      b.substTyFvars_openTyVarsFrom_of_images hlc himages depth]
  | custom name args =>
    exact congrArg (Template.custom name) (templateList_open_subst_of_images args hlc himages depth)
private theorem templateList_open_subst_of_images (templates : List Template) {S : Subst} {roots resolved : List Nat}
    (hlc : ∀ p ∈ S, p.2.IsLC)
    (himages : roots.map (fun x => S.onTy (.fvar x)) = resolved.map Ty.fvar) (depth : Nat) :
    substTemplateList S (openTemplateList depth roots templates) =
      openTemplateList depth resolved (substTemplateList S templates) := by
  cases templates with
  | nil => rfl
  | cons t ts =>
    simp only [substTemplateList, openTemplateList,
      t.substTyFvars_openTyVarsFrom_of_images hlc himages depth,
      templateList_open_subst_of_images ts hlc himages depth]
end

/-- Factor an ordinary annotation check against the transformed source. Only
raw-source allocation bounds and independent target protection are required. -/

theorem LetAnn.substTyFvars_openTyVarsFrom_of_images (ann : LetAnn) {subst : Subst} {roots resolved : List Nat}
    (hlc : ∀ pair ∈ subst, pair.2.IsLC) (himages : roots.map (fun x => subst.onTy (.fvar x)) = resolved.map Ty.fvar) (d : Nat) :
    (ann.openTyVarsFrom d roots).substTyFvars subst = (ann.substTyFvars subst).openTyVarsFrom d resolved := by
  cases ann with
  | absent => rfl
  | complete scheme =>
      exact congrArg (fun t => LetAnn.complete ⟨scheme.paramCount, t⟩)
        (Subst.onTy_openVarsFrom_of_images hlc himages scheme.body (d + scheme.paramCount))
  | template t => exact congrArg LetAnn.template (t.substTyFvars_openTyVarsFrom_of_images hlc himages d)
  | partialForall n t =>
      exact congrArg (LetAnn.partialForall n) (t.substTyFvars_openTyVarsFrom_of_images hlc himages (d + n))

mutual
/-- Source substitution commutes with opening through nested written signature
binders. LC ranges need not avoid the opened names. -/
theorem Input.substTyFvars_openTyVarsFrom_of_images (input : Input) {subst : Subst} {roots resolved : List Nat}
    (hlc : ∀ pair ∈ subst, pair.2.IsLC) (himages : roots.map (fun x => subst.onTy (.fvar x)) = resolved.map Ty.fvar) (d : Nat) :
    (input.openTyVarsFrom d roots).substTyFvars subst = (input.substTyFvars subst).openTyVarsFrom d resolved := by
  cases input with
  | primLit | primBinOp | var | ctor => rfl
  | lambda ann body =>
      simp only [Input.openTyVarsFrom, Input.substTyFvars,
        body.substTyFvars_openTyVarsFrom_of_images hlc himages d]
      congr 1
      cases ann with
      | none => rfl
      | some template => exact congrArg some (template.substTyFvars_openTyVarsFrom_of_images hlc himages d)
  | app f a => simp only [Input.openTyVarsFrom, Input.substTyFvars,
      f.substTyFvars_openTyVarsFrom_of_images hlc himages d, a.substTyFvars_openTyVarsFrom_of_images hlc himages d]
  | letIn ann rhs body => simp only [Input.openTyVarsFrom, Input.substTyFvars,
      LetAnn.paramCount_substTyFvars, ann.substTyFvars_openTyVarsFrom_of_images hlc himages d,
      rhs.substTyFvars_openTyVarsFrom_of_images hlc himages (d + ann.paramCount),
      body.substTyFvars_openTyVarsFrom_of_images hlc himages d]
  | match_ scrut branches => simp only [Input.openTyVarsFrom, Input.substTyFvars,
      scrut.substTyFvars_openTyVarsFrom_of_images hlc himages d,
      substInputBranches_openInputBranches_of_images branches hlc himages d]
  | letRec anns bindings body =>
      simp only [Input.openTyVarsFrom, Input.substTyFvars,
        body.substTyFvars_openTyVarsFrom_of_images hlc himages d,
        substInputBindings_openInputBindings_of_images bindings anns hlc himages d, List.map_map]
      congr 1
      apply List.map_congr_left
      intro ann _
      exact ann.substTyFvars_openTyVarsFrom_of_images hlc himages d
termination_by sizeOf input

theorem substInputBranches_openInputBranches_of_images (branches : List (MatchPattern × Input)) {subst : Subst} {roots resolved : List Nat}
    (hlc : ∀ pair ∈ subst, pair.2.IsLC) (himages : roots.map (fun x => subst.onTy (.fvar x)) = resolved.map Ty.fvar) (d : Nat) :
    substInputBranches subst (openInputBranches d roots branches) = openInputBranches d resolved (substInputBranches subst branches) := by
  cases branches with
  | nil => rfl
  | cons pair rest =>
      rcases pair with ⟨pat, body⟩
      simp only [openInputBranches, substInputBranches, body.substTyFvars_openTyVarsFrom_of_images hlc himages d,
        substInputBranches_openInputBranches_of_images rest hlc himages d]
termination_by sizeOf branches

theorem substInputBindings_openInputBindings_of_images (bindings : List Input) (anns : List LetAnn)
    {subst : Subst} {roots resolved : List Nat}
    (hlc : ∀ pair ∈ subst, pair.2.IsLC) (himages : roots.map (fun x => subst.onTy (.fvar x)) = resolved.map Ty.fvar) (d : Nat) :
    substInputBindings subst (openInputBindings d roots anns bindings) =
      openInputBindings d resolved (anns.map (LetAnn.substTyFvars subst)) (substInputBindings subst bindings) := by
  cases bindings with
  | nil => rfl
  | cons body rest =>
      cases anns with
      | nil => simp only [openInputBindings, substInputBindings, List.map_nil,
          body.substTyFvars_openTyVarsFrom_of_images hlc himages d,
          substInputBindings_openInputBindings_of_images rest [] hlc himages d]
      | cons ann anns => simp only [openInputBindings, substInputBindings, List.map_cons,
          LetAnn.paramCount_substTyFvars, body.substTyFvars_openTyVarsFrom_of_images hlc himages (d + ann.paramCount),
          substInputBindings_openInputBindings_of_images rest anns hlc himages d]
termination_by sizeOf bindings
end

theorem Input.substTyFvars_openTyVars_of_images (input : Input) {subst : Subst} {roots resolved : List Nat}
    (hlc : ∀ pair ∈ subst, pair.2.IsLC) (himages : roots.map (fun x => subst.onTy (.fvar x)) = resolved.map Ty.fvar) :
    (input.openTyVars roots).substTyFvars subst = (input.substTyFvars subst).openTyVars resolved :=
  input.substTyFvars_openTyVarsFrom_of_images hlc himages 0

end Elaboration
