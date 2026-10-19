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
