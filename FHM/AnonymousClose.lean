import FHM.InferW

/-! Closing elaborated RHS annotations under a newly synthesized scheme must
reopen the term as well as its type. Existing inner scheme binders are shielded.
The freshness condition below is needed because `substTyFvars` is sequential.
-/

private theorem TyList.closeVarsFrom_map (depth : Nat) (names : List Nat)
    (types : List Ty) :
    TyList.closeVarsFrom depth names types = types.map (Ty.closeVarsFrom depth names) := by
  induction types with
  | nil => rfl
  | cons _ _ ih => simp [TyList.closeVarsFrom, ih]

theorem Ty.open_closeVarsFrom_rename {names fresh : List Nat}
    (hnames : names.Nodup) (hlen : fresh.length = names.length)
    (hdisj : ∀ name ∈ names, name ∉ fresh) (ty : Ty) (depth : Nat)
    (hbound : ContainsBvarsUpTo depth ty) :
    Ty.openVarsFrom depth fresh (Ty.closeVarsFrom depth names ty) =
      Ty.substFvars (names.zip (fresh.map Ty.fvar)) ty := by
  induction ty using Ty.rec_strong with
  | prim p => simp [Ty.closeVarsFrom, Ty.openVarsFrom, Ty.instantiate, Ty.substFvars_prim]
  | bvar i =>
      cases hbound with | bvar hi =>
        simp [Ty.closeVarsFrom, Ty.openVarsFrom, Ty.instantiate, Ty.substFvars_bvar, hi]
  | fvar name =>
      have h := Ty.openVars_closeOver_rename (τ := .fvar name) .fvar hnames hlen hdisj
      convert h using 1
      cases hi : names.idxOf? name with
      | none => simp [Ty.closeVarsFrom, Ty.closeOver, hi, Ty.openVarsFrom,
          Ty.openVars, Ty.instantiate]
      | some i =>
          have hil : i < names.length := by
            rw [List.idxOf?_eq_map_finIdxOf?_val] at hi
            obtain ⟨j, _, heq⟩ := Option.map_eq_some_iff.mp hi
            exact heq ▸ j.isLt
          simp [Ty.closeVarsFrom, Ty.closeOver, hi, Ty.openVarsFrom,
            Ty.openVars, Ty.instantiate, List.getElem?_eq_getElem (by omega : i < fresh.length)]
  | arrow a b iha ihb =>
      cases hbound with | arrow ha hb =>
        simp [Ty.closeVarsFrom, Ty.substFvars_arrow, iha ha, ihb hb]
  | customTy name args ih =>
      cases hbound with | customTy hall =>
        simp only [Ty.closeVarsFrom, TyList.closeVarsFrom_map,
          Ty.openVarsFrom_customTy, Ty.substFvars_customTy, List.map_map]
        congr 1
        exact List.map_congr_left (fun ty hty => ih ty hty (hall ty hty))

/-- Reopening a completed RHS renames its generalized annotation variables,
including beneath already-present scheme binders. -/
theorem Expr.open_closeTyVarsAux_rename {names fresh : List Nat}
    (hnames : names.Nodup) (hlen : fresh.length = names.length)
    (hdisj : ∀ name ∈ names, name ∉ fresh) (expr : Expr) :
    ∀ depth, expr.TyBvarBounded depth →
      (expr.closeTyVarsAux depth names).openTyVarsAux depth fresh =
        expr.substTyFvars (names.zip (fresh.map Ty.fvar)) := by
  induction expr using Expr.rec_strong with
  | primLit p =>
      intro _ _
      exact (Expr.substTyFvars_eq_self_of_tyFreeVars_nil _ rfl).symm
  | primBinOp op =>
      intro _ _
      exact (Expr.substTyFvars_eq_self_of_tyFreeVars_nil _ rfl).symm
  | var i => intro _ _; exact Expr.substTyFvars_var.symm
  | ctor name =>
      intro _ _
      exact (Expr.substTyFvars_eq_self_of_tyFreeVars_nil _ rfl).symm
  | lambda ann body ih =>
      intro depth hbound
      simp only [Expr.TyBvarBounded] at hbound
      simp only [Expr.closeTyVarsAux, Expr.openTyVarsAux, Expr.substTyFvars_lambda]
      rw [ih depth hbound.2]
      congr 1
      cases ann with
      | none => rfl
      | some ty =>
          simp only [Option.map_some, Option.some.injEq]
          exact Ty.open_closeVarsFrom_rename hnames hlen hdisj ty depth (hbound.1 ty rfl)
  | app f x ihf ihx =>
      intro depth hbound
      simp only [Expr.TyBvarBounded] at hbound
      simp only [Expr.closeTyVarsAux, Expr.openTyVarsAux, Expr.substTyFvars_app,
        ihf depth hbound.1, ihx depth hbound.2]
  | letIn ann rhs body ihr ihb =>
      intro depth hbound
      cases ann with
      | none =>
          simp only [Expr.TyBvarBounded] at hbound
          simp only [Expr.closeTyVarsAux, Expr.openTyVarsAux, Expr.substTyFvars_letIn,
            Option.map_none, ihr depth hbound.1, ihb depth hbound.2]
      | some scheme =>
          simp only [Expr.TyBvarBounded] at hbound
          simp only [Expr.closeTyVarsAux, Expr.openTyVarsAux, Expr.substTyFvars_letIn,
            Option.map_some, ihr (depth + scheme.paramCount) hbound.2.1,
            ihb depth hbound.2.2]
          congr 3
          exact Ty.open_closeVarsFrom_rename hnames hlen hdisj scheme.body
            (depth + scheme.paramCount) hbound.1
  | match_ scrut branches ihs ihbs =>
      intro depth hbound
      simp only [Expr.TyBvarBounded] at hbound
      simp only [Expr.closeTyVarsAux, Expr.openTyVarsAux, Expr.substTyFvars_match,
        ihs depth hbound.1]
      congr 1
      have hall := Expr.TyBvarBounded.BranchList_iff.mp hbound.2
      clear hbound ihs
      induction branches with
      | nil => rfl
      | cons head tail ih =>
          rcases head with ⟨pat, body⟩
          simp only [BranchList.closeTyVarsAux, BranchList.openTyVarsAux, List.map_cons,
            List.cons.injEq, Prod.mk.injEq, true_and]
          exact ⟨ihbs pat body List.mem_cons_self depth (hall pat body List.mem_cons_self),
            ih (fun p b h => ihbs p b (List.mem_cons_of_mem _ h))
              (fun p b h => hall p b (List.mem_cons_of_mem _ h))⟩
  | letRec anns bindings body ihbs ihb =>
      intro depth hbound
      simp only [Expr.TyBvarBounded] at hbound
      simp only [Expr.closeTyVarsAux, Expr.openTyVarsAux, Expr.substTyFvars_letRec,
        ihb depth hbound.2.2, Expr.letRec.injEq, and_true]
      constructor
      · simp only [RecGroup.closeAnns, RecGroup.openAnns, List.map_map]
        apply List.map_congr_left
        intro ann hann
        cases ann with
        | none => simp
        | some scheme =>
            simp only [Function.comp_apply, Option.map_some, RecAnn.substFvars_some,
              PolyTy.substFvars_eq, Option.some.injEq, PolyTy.mk.injEq, true_and]
            exact Ty.open_closeVarsFrom_rename hnames hlen hdisj scheme.body
              (depth + scheme.paramCount) (hbound.1 scheme hann)
      · have hbindings := hbound.2.1
        clear hbound ihb
        induction bindings generalizing anns with
        | nil => cases anns <;> rfl
        | cons binding rest ih =>
            cases anns with
            | nil =>
                simp only [RecGroup.closeAnns, List.map_nil, RecGroup.closeTyVarsAux,
                  RecGroup.openTyVarsAux, List.map_cons, Expr.TyBvarBounded.RecGroup,
                  List.cons.injEq] at hbindings ⊢
                exact ⟨ihbs binding List.mem_cons_self depth hbindings.1,
                  ih [] (fun e h => ihbs e (List.mem_cons_of_mem _ h)) hbindings.2⟩
            | cons ann anns =>
                cases ann <;>
                  simp only [RecGroup.closeAnns, List.map_cons, Option.map_none,
                    Option.map_some, RecGroup.closeTyVarsAux, RecGroup.openTyVarsAux,
                    RecAnn.params, Expr.TyBvarBounded.RecGroup, Nat.add_zero,
                    List.cons.injEq] at hbindings ⊢
                all_goals exact ⟨ihbs binding List.mem_cons_self _ hbindings.1,
                  ih anns (fun e h => ihbs e (List.mem_cons_of_mem _ h)) hbindings.2⟩

theorem Expr.open_closeTyVars_rename {names fresh : List Nat}
    (hnames : names.Nodup) (hlen : fresh.length = names.length)
    (hdisj : ∀ name ∈ names, name ∉ fresh) {expr : Expr}
    (hbound : expr.TyBvarBounded 0) :
    (expr.closeTyVars names).openTyVars fresh =
      expr.substTyFvars (names.zip (fresh.map Ty.fvar)) :=
  Expr.open_closeTyVarsAux_rename hnames hlen hdisj expr 0 hbound

/-- Generalising an elaborated RHS closes its annotations under the same ordered
binders as its result type. Unlike the unannotated Core rule, the resulting
cofinite premise opens BOTH the RHS and the scheme. -/
theorem TypeOfHM.generaliseAnnotated {ctx : Ctx} {expr : Expr} {ty : Ty}
    {names : List Nat} (htyping : TypeOfHM ctx expr ty)
    (hbound : expr.TyBvarBounded 0) (hnames : names.Nodup)
    (hctx : ∀ name ∈ names, name ∉ ctx.env.freeVars) :
    GeneralisesTo TypeOfHM ctx (some ⟨names.length, Ty.closeOver names ty⟩)
      (expr.closeTyVars names) ⟨names.length, Ty.closeOver names ty⟩ names := by
  intro fresh hfresh
  have hdisj : ∀ name ∈ names, name ∉ fresh :=
    fun name hn hf => hfresh.avoid name hf hn
  rw [Expr.openBoundTyVars,
    Expr.open_closeTyVars_rename hnames hfresh.length hdisj hbound]
  change TypeOfHM ctx (expr.substTyFvars (names.zip (fresh.map Ty.fvar)))
    (Ty.openVars fresh (Ty.closeOver names ty))
  rw [Ty.openVars_closeOver_rename (TypeOfHM.regular htyping) hnames hfresh.length hdisj]
  apply TypeOfHM.typ_substs_preservation _ _ _ htyping
  · intro pair hp
    exact hctx pair.1 (List.of_mem_zip hp).1
  · intro pair hp
    obtain ⟨name, _, heq⟩ := List.mem_map.mp (List.of_mem_zip hp).2
    rw [← heq]
    exact .fvar

/-- Substitution transports a completed RHS's cofinite scheme premise. This
corollary reuses the existing source substitution theorem, including its binder
freshening, rather than maintaining a second transport proof. -/
theorem GeneralisesTo.onSubst_annotated {ctx : Ctx} {rhs : Expr} {scheme : PolyTy}
    {avoid : List Nat} (hwf : scheme.WF)
    (h : GeneralisesTo TypeOfHM ctx (some scheme) rhs scheme avoid)
    (subst : Subst) (hlc : ∀ pair ∈ subst, pair.2.IsLC) :
    ∃ avoid', GeneralisesTo TypeOfHM (subst.onCtx ctx) (some (subst.onPolyTy scheme))
      (rhs.substTyFvars subst) (subst.onPolyTy scheme) avoid' := by
  have hlet : TypeOfHM ctx (.letIn (some scheme) rhs (.primLit .unit)) (.prim .unit) :=
    .letIn hwf (fun _ heq => Option.some.inj heq) h rfl .primLitUnit
  have transported := TypeOfHM.onSubst subst hlc hlet
  simp only [Expr.substTyFvars_letIn, Option.map_some] at transported
  cases transported with
  | letIn _ hpins hgen _ _ =>
      have heq := hpins _ rfl
      subst heq
      exact ⟨_, hgen⟩

mutual
/-- A syntactic scope check for RHSs that will acquire a synthesized scheme.
It checks only annotation binder scope, not term typing. -/
def Expr.scopedAnnotations (depth : Nat) : Expr → Bool
  | .primLit _ | .primBinOp _ | .var _ | .ctor _ => true
  | .lambda ann body =>
      ann.all (Ty.bvarsBelow depth) && body.scopedAnnotations depth
  | .app f x => f.scopedAnnotations depth && x.scopedAnnotations depth
  | .letIn ann rhs body =>
      ann.all (fun scheme => Ty.bvarsBelow (depth + scheme.paramCount) scheme.body) &&
        rhs.scopedAnnotations (depth + RecAnn.params ann) && body.scopedAnnotations depth
  | .match_ scrut branches => scrut.scopedAnnotations depth && scopedBranches depth branches
  | .letRec anns bindings body =>
      anns.all (fun ann => ann.all fun scheme =>
        Ty.bvarsBelow (depth + scheme.paramCount) scheme.body) &&
        scopedBindings depth anns bindings && body.scopedAnnotations depth
def scopedBranches (depth : Nat) : List (MatchPattern × Expr) → Bool
  | [] => true
  | (_, body) :: rest => body.scopedAnnotations depth && scopedBranches depth rest
def scopedBindings (depth : Nat) : List (Option PolyTy) → List Expr → Bool
  | _, [] => true
  | [], body :: rest => body.scopedAnnotations depth && scopedBindings depth [] rest
  | ann :: anns, body :: rest =>
      body.scopedAnnotations (depth + RecAnn.params ann) && scopedBindings depth anns rest
end

mutual
theorem Expr.scopedAnnotations_sound (expr : Expr) (depth : Nat)
    (h : expr.scopedAnnotations depth = true) : expr.TyBvarBounded depth := by
  cases expr with
  | primLit => trivial
  | primBinOp => trivial
  | var => trivial
  | ctor => trivial
  | lambda ann body =>
      simp only [Expr.scopedAnnotations, Bool.and_eq_true] at h
      refine ⟨?_, body.scopedAnnotations_sound depth h.2⟩
      intro ty hty
      subst ann
      exact (Ty.bvarsBelow_iff ty).mp h.1
  | app f x =>
      simp only [Expr.scopedAnnotations, Bool.and_eq_true] at h
      exact ⟨f.scopedAnnotations_sound depth h.1, x.scopedAnnotations_sound depth h.2⟩
  | letIn ann rhs body =>
      simp only [Expr.scopedAnnotations, Bool.and_eq_true] at h
      cases ann with
      | none => exact ⟨rhs.scopedAnnotations_sound depth h.1.2,
          body.scopedAnnotations_sound depth h.2⟩
      | some scheme => exact ⟨(Ty.bvarsBelow_iff scheme.body).mp h.1.1,
          rhs.scopedAnnotations_sound _ h.1.2, body.scopedAnnotations_sound depth h.2⟩
  | match_ scrut branches =>
      simp only [Expr.scopedAnnotations, Bool.and_eq_true] at h
      exact ⟨scrut.scopedAnnotations_sound depth h.1, scopedBranches_sound branches depth h.2⟩
  | letRec anns bindings body =>
      simp only [Expr.scopedAnnotations, Bool.and_eq_true, List.all_eq_true] at h
      refine ⟨?_, scopedBindings_sound anns bindings depth h.1.2,
        body.scopedAnnotations_sound depth h.2⟩
      intro scheme hscheme
      exact (Ty.bvarsBelow_iff scheme.body).mp (h.1.1 (some scheme) hscheme)
theorem scopedBranches_sound (branches : List (MatchPattern × Expr)) (depth : Nat)
    (h : scopedBranches depth branches = true) : Expr.TyBvarBounded.BranchList depth branches := by
  cases branches with
  | nil => trivial
  | cons head rest =>
      simp only [scopedBranches, Bool.and_eq_true] at h
      exact ⟨head.2.scopedAnnotations_sound depth h.1, scopedBranches_sound rest depth h.2⟩
theorem scopedBindings_sound (anns : List (Option PolyTy)) (bindings : List Expr) (depth : Nat)
    (h : scopedBindings depth anns bindings = true) : Expr.TyBvarBounded.RecGroup depth anns bindings := by
  cases bindings with
  | nil => trivial
  | cons body rest =>
      cases anns with
      | nil =>
          simp only [scopedBindings, Bool.and_eq_true] at h
          exact ⟨body.scopedAnnotations_sound depth h.1, scopedBindings_sound [] rest depth h.2⟩
      | cons ann anns =>
          simp only [scopedBindings, Bool.and_eq_true] at h
          exact ⟨body.scopedAnnotations_sound _ h.1, scopedBindings_sound anns rest depth h.2⟩
end
