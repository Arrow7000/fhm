import FHM.CoreBackend.Infer


/-- Every declaratively typed Core expression has correctly scoped type annotations. -/
theorem TypeOfHM.tyBvarBounded {ctx : Ctx} {expr : Expr} {ty : Ty}
    (h : TypeOfHM ctx expr ty) : expr.TyBvarBounded 0 := by
  induction h using TypeOfHM.rec
      (motive_2 := fun _ branch _ _ _ => branch.2.TyBvarBounded 0) with
  | primLitUnit => trivial
  | primLitInt => trivial
  | primLitNat => trivial
  | primLitChar => trivial
  | primBinOpIntAdd => trivial
  | primBinOpIntSub => trivial
  | primBinOpIntLt _ _ _ _ => trivial
  | primBinOpCharLt _ _ _ _ => trivial
  | var _ _ _ => trivial
  | ctor _ _ _ => trivial
  | lambda hpc hann _ _ ihbody =>
    exact ⟨fun t ht => (hann t ht) ▸ hpc, ihbody⟩
  | app _ _ ihf iharg => exact ⟨ihf, iharg⟩
  | letIn hwf hann _ _ _ ihcofin ihbody =>
    expose_names
    obtain ⟨Xs, hlen, hnodup, havoid⟩ := exists_fresh_names L M.paramCount
    have hrhs := ihcofin Xs ⟨hlen, hnodup, havoid⟩
    cases ann with
    | none => exact ⟨hrhs, ihbody⟩
    | some σ =>
      have hM : M = σ := hann σ rfl
      subst M
      refine ⟨by simpa only [Nat.zero_add] using hwf, ?_, ihbody⟩
      have hb := Expr.tyBvarBounded_of_openTyVarsAux Xs boundExpr 0 hrhs
      simpa only [Nat.zero_add, hlen] using hb
  | match_ _ _ _ ihscrut ihbranches =>
    refine ⟨ihscrut, Expr.TyBvarBounded.BranchList_iff.mpr ?_⟩
    intro p b hb
    exact ihbranches (p, b) hb
  | mk _ _ _ ihbody => exact ihbody
  | wildcard _ ihbody => exact ihbody
  | letRec hvalid hwf _ _ _ _ ihmono ihpoly ihbody =>
    expose_names
    have hbound : ∀ pair ∈ bindings.zip specs,
        pair.1.TyBvarBounded (RecAnn.params pair.2.ann) := by
      rintro ⟨rhs, spec⟩ hpair
      cases spec with
      | mono τ =>
        obtain ⟨member, hlookup⟩ := List.mem_iff_getElem?.mp hpair
        rw [List.getElem?_zip_eq_some] at hlookup
        obtain ⟨hrhs, hspec⟩ := hlookup
        have hmember : member < bindings.length :=
          (List.getElem?_eq_some_iff.mp hrhs).choose
        have hunsigned : RecGroups.UnsignedAt anns member := by
          rw [RecGroups.UnsignedAt, ← hwf.anns_eq, List.getElem?_map, hspec]
          rfl
        obtain ⟨component, hc, hm⟩ := List.mem_flatten.mp
          ((hvalid.covers_unsigned member hmember).mpr hunsigned)
        obtain ⟨stage, hstage⟩ := List.mem_iff_getElem?.mp hc
        obtain ⟨Xs, hlen, hnodup, havoid⟩ := exists_fresh_names L G.length
        exact ihmono stage component hstage Xs ⟨hlen, hnodup, havoid⟩
          member hm rhs τ hrhs hspec
      | poly σ =>
        obtain ⟨Ys, hlen, hnodup, havoid⟩ := exists_fresh_names L σ.paramCount
        have hopen := ihpoly (rhs, .poly σ) hpair σ rfl Ys ⟨hlen, hnodup, havoid⟩
        have hb := Expr.tyBvarBounded_of_openTyVarsAux Ys rhs 0 hopen
        simpa only [Nat.zero_add, hlen, RecSpec.ann, RecAnn.params] using hb
    refine ⟨?_, ?_, ihbody⟩
    · intro σ hσ
      rw [← hwf.anns_eq] at hσ
      obtain ⟨spec, hspec, heq⟩ := List.mem_map.mp hσ
      have hpolySpec : spec = .poly σ := RecSpec.ann_eq_some heq
      subst spec
      simpa only [Nat.zero_add] using hwf.poly_wf σ hspec
    · apply Expr.TyBvarBounded.RecGroup_of_zip
        (hwf.length.trans (by rw [← hwf.anns_eq, List.length_map]))
      intro pair hpair
      rw [← hwf.anns_eq, List.zip_map_right] at hpair
      obtain ⟨source, hsource, rfl⟩ := List.mem_map.mp hpair
      simpa only [Prod.map, id_eq, Nat.zero_add] using hbound source hsource

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
    (hnames : names.Nodup)
    (hctx : ∀ name ∈ names, name ∉ ctx.env.freeVars) :
    GeneralisesTo TypeOfHM ctx (some ⟨names.length, Ty.closeOver names ty⟩)
      (expr.closeTyVars names) ⟨names.length, Ty.closeOver names ty⟩ names := by
  intro fresh hfresh
  have hdisj : ∀ name ∈ names, name ∉ fresh :=
    fun name hn hf => hfresh.avoid name hf hn
  rw [Expr.openBoundTyVars,
    Expr.open_closeTyVars_rename hnames hfresh.length hdisj htyping.tyBvarBounded]
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

/-- Substitution changes annotations only, so it preserves runtime shape. -/
theorem Expr.erase_substTyFvars (expr : Expr) (subst : Subst) :
    (expr.substTyFvars subst).erase = expr.erase := by
  induction expr using Expr.rec_strong with
  | primLit => rw [Expr.substTyFvars_eq_self_of_tyFreeVars_nil subst rfl]
  | primBinOp => rw [Expr.substTyFvars_eq_self_of_tyFreeVars_nil subst rfl]
  | var => rw [Expr.substTyFvars_var]
  | ctor => rw [Expr.substTyFvars_eq_self_of_tyFreeVars_nil subst rfl]
  | lambda ann body ih => simp only [Expr.substTyFvars_lambda, Expr.erase, ih]
  | app f x ihf ihx => simp only [Expr.substTyFvars_app, Expr.erase, ihf, ihx]
  | letIn ann rhs body ihr ihb => simp only [Expr.substTyFvars_letIn, Expr.erase, ihr, ihb]
  | match_ scrut branches ihs ihbs =>
      simp only [Expr.substTyFvars_match, Expr.erase, ihs, List.map_map]
      congr 1
      exact List.map_congr_left (fun pair hp => congrArg (Prod.mk pair.1) (ihbs pair.1 pair.2 hp))
  | letRec anns bindings body ihbs ihb =>
      simp only [Expr.substTyFvars_letRec, Expr.erase, ihb, List.map_map]
      congr 1
      exact List.map_congr_left (fun binding hb => ihbs binding hb)


/-- Closing scoped type variables changes only annotations, which erasure discards. -/
theorem Expr.erase_closeTyVarsAux (expr : Expr) (depth : Nat) (names : List Nat) :
    (expr.closeTyVarsAux depth names).erase = expr.erase := by
  induction expr using Expr.rec_strong generalizing depth with
  | primLit p => rfl
  | primBinOp op => rfl
  | var i => rfl
  | ctor name => rfl
  | lambda ann body ih => simp only [Expr.closeTyVarsAux, Expr.erase, ih]
  | app f arg ihf iha => simp only [Expr.closeTyVarsAux, Expr.erase, ihf, iha]
  | letIn ann rhs body ihr ihb =>
    cases ann <;> simp only [Expr.closeTyVarsAux, Expr.erase, ihr, ihb]
  | match_ scrut branches ihs ihbs =>
    simp only [Expr.closeTyVarsAux, Expr.erase, ihs]
    congr 1
    induction branches with
    | nil => rfl
    | cons head tail ih =>
      rcases head with ⟨pat, body⟩
      simp only [BranchList.closeTyVarsAux, List.map_cons]
      rw [ihbs pat body List.mem_cons_self depth]
      congr 1
      exact ih (fun p b hb => ihbs p b (List.mem_cons_of_mem _ hb))
  | letRec anns bindings body ihbs ihb =>
    have hgroup : ∀ anns depth,
        (RecGroup.closeTyVarsAux depth names anns bindings).map Expr.erase = bindings.map Expr.erase := by
      induction bindings with
      | nil => intro _ _; rfl
      | cons head tail ih =>
        intro anns depth
        cases anns <;> simp only [RecGroup.closeTyVarsAux, List.map_cons]
        all_goals
          rw [ihbs head List.mem_cons_self]
          congr 1
          exact ih (fun b hb => ihbs b (List.mem_cons_of_mem _ hb)) _ _
    have hlen := congrArg List.length (hgroup anns depth)
    simp only [List.length_map] at hlen
    simp only [Expr.closeTyVarsAux, Expr.erase, ihb, hgroup]
    congr 1
    simp only [List.map_const', hlen]

/-- Erasure is invariant under closing any list of names, including duplicates. -/
theorem Expr.erase_closeTyVars (expr : Expr) (names : List Nat) :
    (expr.closeTyVars names).erase = expr.erase :=
  expr.erase_closeTyVarsAux 0 names
