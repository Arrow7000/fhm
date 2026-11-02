import FHM.InferenceSupport
import FHM.Compatibility.Erasure

/-! Metatheory of historical complete-Core typing. Shared type, substitution,
unification and scheduling foundations remain in `InferenceSupport`. -/

theorem Ctor.IsBoolCtor.typeOfHM {ctx : Ctx} {name : CtorName} {c : Ctor}
    (hlook : LookupList.get? ctx.ctors name = some c) (hb : c.IsBoolCtor) :
    TypeOfHM ctx (.ctor name) (.customTy ⟨"Bool"⟩ []) :=
  .ctor hlook (by simp) hb.instantiatesTo

/-- From a `TypeOfHM` typing of a bare ctor at `Bool`, recover the ctor lookup
    together with its `IsBoolCtor` shape. -/
theorem Ctor.isBoolCtor_of_typeOfHM {ctx : Ctx} {name : CtorName}
    (h : TypeOfHM ctx (.ctor name) (.customTy ⟨"Bool"⟩ [])) :
    ∃ c, LookupList.get? ctx.ctors name = some c ∧ c.IsBoolCtor := by
  cases h with
  | ctor hlook _ hinst => exact ⟨_, hlook, Ctor.IsBoolCtor.of_instantiatesTo hinst⟩

/-! ### `TypeOfHM` metatheory

The standard HM metatheory is proved directly over `TypeOfHM`; variable uses
carry an existential instantiation witness. -/

/-- Branch disjunction motive for `TypeOfHM.rec_strong`. -/
abbrev TypeOfHM.BranchMotive
    (motive : (ctx : Ctx) → (e : Expr) → (τ : Ty) → TypeOfHM ctx e τ → Prop)
    (ctx : Ctx) (branch : MatchPattern × Expr) (scrutTy : Ty)
    (resultTy : Ty) : Prop :=
  (∃ (ctor : Ctor) (c : CtorName) (n : Nat) (tyArgs : List Ty) (instContents : List Ty),
    branch.1 = .named c n ∧
    LookupList.get? ctx.ctors c = some ctor ∧
    scrutTy = .customTy ctor.tyName tyArgs ∧
    ctor.paramCount = tyArgs.length ∧
    n = ctor.contents.length ∧
    List.Forall₂ (InstantiatesBy tyArgs) ctor.contents instContents ∧
    ∃ hbody : TypeOfHM ⟨instContents.map PolyTy.mkTrivial ++ ctx.env, ctx.ctors⟩ branch.2 resultTy,
      motive ⟨instContents.map PolyTy.mkTrivial ++ ctx.env, ctx.ctors⟩ branch.2 resultTy hbody)
  ∨
  (branch.1 = .wildcard ∧
    ∃ hbody : TypeOfHM ctx branch.2 resultTy,
      motive ctx branch.2 resultTy hbody)

/-- Strong induction principle for historical complete-Core typing. -/
@[elab_as_elim]
theorem TypeOfHM.rec_strong
    {motive : (ctx : Ctx) → (e : Expr) → (τ : Ty) → TypeOfHM ctx e τ → Prop}
    (primLitUnit : ∀ {ctx : Ctx}, motive ctx (.primLit .unit) (.prim .unit) .primLitUnit)
    (primLitInt : ∀ {ctx : Ctx} {n : ℤ}, motive ctx (.primLit (.int n)) (.prim .int) .primLitInt)
    (primLitNat : ∀ {ctx : Ctx} {n : ℕ}, motive ctx (.primLit (.nat n)) (.prim .nat) .primLitNat)
    (primLitChar : ∀ {ctx : Ctx} {c : Char}, motive ctx (.primLit (.char c)) (.prim .char) .primLitChar)
    (primBinOpIntAdd : ∀ {ctx : Ctx},
      motive ctx (.primBinOp .intAdd)
        (.arrow (.prim .int) (.arrow (.prim .int) (.prim .int))) .primBinOpIntAdd)
    (primBinOpIntSub : ∀ {ctx : Ctx},
      motive ctx (.primBinOp .intSub)
        (.arrow (.prim .int) (.arrow (.prim .int) (.prim .int))) .primBinOpIntSub)
    (primBinOpIntLt : ∀ {ctx : Ctx}
      (htrue : TypeOfHM ctx (.ctor ⟨"True"⟩) (.customTy ⟨"Bool"⟩ []))
      (hfalse : TypeOfHM ctx (.ctor ⟨"False"⟩) (.customTy ⟨"Bool"⟩ [])),
      motive ctx (.ctor ⟨"True"⟩) (.customTy ⟨"Bool"⟩ []) htrue →
      motive ctx (.ctor ⟨"False"⟩) (.customTy ⟨"Bool"⟩ []) hfalse →
      motive ctx (.primBinOp .intLt)
        (.arrow (.prim .int) (.arrow (.prim .int) (.customTy ⟨"Bool"⟩ [])))
        (.primBinOpIntLt htrue hfalse))
    (primBinOpCharLt : ∀ {ctx : Ctx}
      (htrue : TypeOfHM ctx (.ctor ⟨"True"⟩) (.customTy ⟨"Bool"⟩ []))
      (hfalse : TypeOfHM ctx (.ctor ⟨"False"⟩) (.customTy ⟨"Bool"⟩ [])),
      motive ctx (.ctor ⟨"True"⟩) (.customTy ⟨"Bool"⟩ []) htrue →
      motive ctx (.ctor ⟨"False"⟩) (.customTy ⟨"Bool"⟩ []) hfalse →
      motive ctx (.primBinOp .charLt)
        (.arrow (.prim .char) (.arrow (.prim .char) (.customTy ⟨"Bool"⟩ [])))
        (.primBinOpCharLt htrue hfalse))
    (lambda : ∀ {paramTy : Ty} {ann : Option Ty} {bodyCtx ctx : Ctx} {body : Expr} {bodyTy : Ty}
      (hpc : ContainsBvarsUpTo 0 paramTy) (hann : Option.Pins ann paramTy)
      (heq : bodyCtx = { env := PolyTy.mkTrivial paramTy :: ctx.env, ctors := ctx.ctors })
      (hbody : TypeOfHM bodyCtx body bodyTy),
      motive bodyCtx body bodyTy hbody →
      motive ctx (.lambda ann body) (.arrow paramTy bodyTy) (.lambda hpc hann heq hbody))
    (app : ∀ {ctx : Ctx} {f : Expr} {argTy retTy : Ty} {input : Expr}
      (hf : TypeOfHM ctx f (.arrow argTy retTy)) (hinput : TypeOfHM ctx input argTy),
      motive ctx f (.arrow argTy retTy) hf → motive ctx input argTy hinput →
      motive ctx (.app f input) retTy (.app hf hinput))
    (letIn : ∀ {ann : Option PolyTy} {ctx : Ctx} {boundExpr : Expr} {bodyCtx : Ctx} {body : Expr}
      {bodyTy : Ty} {M : PolyTy} {L : List Nat}
      (hwf : M.WF) (hann : ann.Pins M)
      (hcofin : ∀ Xs, FreshNames L M.paramCount Xs →
        TypeOfHM ctx (Expr.openBoundTyVars ann Xs boundExpr) (M.openVars Xs))
      (heq : bodyCtx = { env := M :: ctx.env, ctors := ctx.ctors })
      (hbody : TypeOfHM bodyCtx body bodyTy),
      (∀ Xs (hf : FreshNames L M.paramCount Xs),
        motive ctx (Expr.openBoundTyVars ann Xs boundExpr) (M.openVars Xs) (hcofin Xs hf)) →
      motive bodyCtx body bodyTy hbody →
      motive ctx (.letIn ann boundExpr body) bodyTy (.letIn hwf hann hcofin heq hbody))
    (var : ∀ {dbl : Nat} {polyTy : PolyTy} {instArgs : List Ty} {ty : Ty} {ctx : Ctx}
      (hlook : ctx.env[dbl]? = some polyTy)
      (htyargs : ∀ tyArg ∈ instArgs, ContainsBvarsUpTo 0 tyArg)
      (hinst : InstantiatesBy instArgs polyTy.body ty),
      motive ctx (.var dbl) ty (.var hlook htyargs hinst))
    (ctor : ∀ {name : CtorName} {ctorr : Ctor} {tyArgs : List Ty} {ty : Ty} {ctx : Ctx}
      (hlook : LookupList.get? ctx.ctors name = some ctorr)
      (htyargs : ∀ tyArg ∈ tyArgs, ContainsBvarsUpTo 0 tyArg)
      (hinst : InstantiatesBy tyArgs ctorr.toTy.body ty),
      motive ctx (.ctor name) ty (.ctor hlook htyargs hinst))
    (match_ : ∀ {ctx : Ctx} {scrutinee : Expr} {scrutTy : Ty}
      {branches : List (MatchPattern × Expr)} {resultTy : Ty}
      (hscrut : TypeOfHM ctx scrutinee scrutTy) (hne : branches ≠ [])
      (hbrs : ∀ branch ∈ branches, TypeOfMatchBranch ctx branch scrutTy resultTy),
      motive ctx scrutinee scrutTy hscrut →
      (∀ branch ∈ branches, TypeOfHM.BranchMotive motive ctx branch scrutTy resultTy) →
      motive ctx (.match_ scrutinee branches) resultTy (.match_ hscrut hne hbrs))
    (letRec : ∀ {ctx bodyCtx : Ctx} {bindings : List CoreRecBinding}
      {specs : List RecSpec} {groups : List (List Nat)} {G L : List Nat} {body : Expr} {ρ : Ty}
      (hvalid : RecGroups.ValidResidualGroups bindings groups)
      (hwf : RecSpecs.WF bindings specs G)
      (hmono : RecSpecs.StratifiedMonoTyped TypeOfHM ctx bindings specs groups G L)
      (hpoly : RecSpecs.PolyTypedFinal TypeOfHM ctx bindings specs G L)
      (heq : bodyCtx = RecSpecs.bodyCtx ctx specs G)
      (hbody : TypeOfHM bodyCtx body ρ),
      (∀ stage component (hc : groups[stage]? = some component)
          Xs (hf : FreshNames L G.length Xs) member (hm : member ∈ component) binding τ
          (hbinding : bindings[member]? = some binding) (hτ : specs[member]? = some (.mono τ)),
        motive (RecSpecs.stageCtx ctx specs (groups.take stage).flatten G Xs)
          binding.rhs (Ty.renameG G Xs τ)
            (hmono stage component hc Xs hf member hm binding τ hbinding hτ)) →
      (∀ p (hp : p ∈ bindings.zip specs) σ (hσ : p.2 = .poly σ)
          Ys (hfY : FreshNames L σ.paramCount Ys),
        motive (RecSpecs.bodyCtx ctx specs G)
          (p.1.rhs.openTyVars Ys) (σ.openVars Ys) (hpoly p hp σ hσ Ys hfY)) →
      motive bodyCtx body ρ hbody →
      motive ctx (.letRec bindings body) ρ (.letRec hvalid hwf hmono hpoly heq hbody))
    {ctx : Ctx} {e : Expr} {τ : Ty} (h : TypeOfHM ctx e τ) : motive ctx e τ h := by
  induction h using TypeOfHM.rec
    (motive_2 := fun ctx br scrutTy resultTy _ =>
      TypeOfHM.BranchMotive motive ctx br scrutTy resultTy) with
  | primLitUnit => exact primLitUnit
  | primLitInt => exact primLitInt
  | primLitNat => exact primLitNat
  | primLitChar => exact primLitChar
  | primBinOpIntAdd => exact primBinOpIntAdd
  | primBinOpIntSub => exact primBinOpIntSub
  | primBinOpIntLt htrue hfalse ihtrue ihfalse => exact primBinOpIntLt htrue hfalse ihtrue ihfalse
  | primBinOpCharLt htrue hfalse ihtrue ihfalse => exact primBinOpCharLt htrue hfalse ihtrue ihfalse
  | lambda hpc hann heq hbody ihbody => exact lambda hpc hann heq hbody ihbody
  | app hf hinput ihf ihinput => exact app hf hinput ihf ihinput
  | letIn hwf hann hcofin heq hbody ihcofin ihbody =>
      exact letIn hwf hann hcofin heq hbody ihcofin ihbody
  | var hlook hlc hinst => exact var hlook hlc hinst
  | ctor hlook htyargs hinst => exact ctor hlook htyargs hinst
  | match_ hscrut hne hbrs ihscrut ihbrs => exact match_ hscrut hne hbrs ihscrut ihbrs
  | letRec hvalid hwf hmono hpoly heq hbody ihmono ihpoly ihbody =>
      exact letRec hvalid hwf hmono hpoly heq hbody ihmono ihpoly ihbody
  | mk hspec heq hbodyT ih =>
      subst heq
      exact Or.inl ⟨_, _, _, _, _, rfl, hspec.lookup, hspec.scrut_eq, hspec.arity,
        hspec.bind_count, hspec.fields, hbodyT, ih⟩
  | wildcard hbodyT ih =>
      exact Or.inr ⟨rfl, hbodyT, ih⟩

/-- Typing only depends on the environment entries actually referenced by the
    expression. In particular, later residual-group slots may change freely. -/
theorem TypeOfHM.env_agreement {ctx : Ctx} {e : Expr} {τ : Ty}
    (h : TypeOfHM ctx e τ) : ∀ env',
    e.ForallOuter (fun i => env'[i]? = ctx.env[i]?) 0 →
    TypeOfHM ⟨env', ctx.ctors⟩ e τ := by
  induction h using TypeOfHM.rec_strong with
  | primLitUnit => intro _ _; exact .primLitUnit
  | primLitInt => intro _ _; exact .primLitInt
  | primLitNat => intro _ _; exact .primLitNat
  | primLitChar => intro _ _; exact .primLitChar
  | primBinOpIntAdd => intro _ _; exact .primBinOpIntAdd
  | primBinOpIntSub => intro _ _; exact .primBinOpIntSub
  | primBinOpIntLt _ _ ihtrue ihfalse =>
    intro env' _
    exact .primBinOpIntLt (ihtrue env' (by simp [Expr.ForallOuter, Expr.rec_strong]))
      (ihfalse env' (by simp [Expr.ForallOuter, Expr.rec_strong]))
  | primBinOpCharLt _ _ ihtrue ihfalse =>
    intro env' _
    exact .primBinOpCharLt (ihtrue env' (by simp [Expr.ForallOuter, Expr.rec_strong]))
      (ihfalse env' (by simp [Expr.ForallOuter, Expr.rec_strong]))
  | var hlook hlc hinst =>
    intro env' hag
    simp only [Expr.ForallOuter, Expr.rec_strong, Nat.zero_le, Nat.sub_zero] at hag
    exact .var (by rw [hag trivial]; exact hlook) hlc hinst
  | ctor hlook hlc hinst => intro _ _; exact .ctor hlook hlc hinst
  | app hf ha ihf iha =>
    intro env' hag
    simp only [Expr.ForallOuter, Expr.rec_strong] at hag
    exact .app (ihf env' hag.1) (iha env' hag.2)
  | lambda hpc hann heq hbody ihbody =>
    intro env' hag
    subst heq
    expose_names
    simp only [Expr.ForallOuter, Expr.rec_strong, Nat.zero_add] at hag
    exact .lambda hpc hann rfl (ihbody (PolyTy.mkTrivial paramTy :: env')
      (Expr.ForallOuter.prepend_env (pre := [PolyTy.mkTrivial paramTy]) hag))
  | letIn hwf hann hcofin heq hbody ihcofin ihbody =>
    intro env' hag
    subst heq
    expose_names
    simp only [Expr.ForallOuter, Expr.rec_strong, Nat.zero_add] at hag
    exact .letIn hwf hann
      (fun Xs hf => ihcofin Xs hf env' (Expr.ForallOuter.openBoundTyVars
        (P := fun i => env'[i]? = ctx_1.env[i]?)
        (e := boundExpr) (depth := 0) hag.1 ann Xs)) rfl
      (ihbody (M :: env') (Expr.ForallOuter.prepend_env (pre := [M]) hag.2))
  | match_ hs hne hbrs ihs ihbrs =>
    intro env' hag
    simp only [Expr.ForallOuter, Expr.rec_strong, Nat.zero_add] at hag
    refine .match_ (ihs env' hag.1) hne ?_
    intro ⟨pat, body⟩ hb
    rcases ihbrs (pat, body) hb with
      ⟨ctorr,c,n,tyArgs,instContents,hpat,hlook,hscrut,hpc,hn,hfields,_,ih⟩ |
      ⟨hpat,_,ih⟩
    · subst hpat
      have hlen : instContents.length = n := by
        have := List.Forall₂.length_eq hfields
        omega
      refine .mk ⟨hlook,hscrut,hpc,hn,hfields⟩ rfl ?_
      apply ih
      apply Expr.ForallOuter.prepend_env
      simpa only [List.length_map, Nat.zero_add, hlen, MatchPattern.bindCount] using hag.2 _ _ hb
    · subst hpat
      exact .wildcard (ih env' (by simpa only [MatchPattern.bindCount] using hag.2 _ _ hb))
  | letRec hvalid hwf hmono hpoly heq hbody ihmono ihpoly ihbody =>
    intro env' hag
    subst heq
    expose_names
    simp only [Expr.ForallOuter, Expr.rec_strong, Nat.zero_add] at hag
    refine .letRec (specs := specs) (groups := groups) (G := G) (L := L)
      hvalid hwf ?_ ?_ rfl ?_
    · intro stage component hc Xs hf member hm binding τ hbinding hτ
      apply ihmono stage component hc Xs hf member hm binding τ hbinding hτ
      apply Expr.ForallOuter.prepend_env
      simpa only [List.length_mapIdx, Nat.zero_add, hwf.length] using
        hag.1 binding (List.mem_of_getElem? hbinding)
    · intro p hp σ hσ Ys hYs
      apply ihpoly p hp σ hσ Ys hYs
      apply Expr.ForallOuter.prepend_env
      have h := Expr.ForallOuter.openTyVars (e := p.1.rhs) (depth := bindings.length)
        (P := fun i => env'[i]? = ctx_1.env[i]?)
        (hag.1 p.1 (List.of_mem_zip hp).1) Ys
      simpa only [List.length_map, Nat.zero_add, hwf.length] using h
    · apply ihbody
      apply Expr.ForallOuter.prepend_env
      simpa only [List.length_map, Nat.zero_add, hwf.length] using hag.2

/-- Single-fvar `substTyFvar` is the one-element iterated `substTyFvars` (defeq).
    Lets the `match_` and `letRec` cases use the public
    `Expr.substTyFvars_*` structural lemmas instead of the Core-private single-fvar
    list helpers. -/
private theorem Expr.substTyFvar_eq_substTyFvars_single {Z : Nat} {U : Ty} {e : Expr} :
    Expr.substTyFvar Z U e = Expr.substTyFvars [(Z, U)] e := rfl

/-- **Single-fvar substitution preservation for `TypeOfHM`**, uniform over the
    whole environment. The match and recursive-group cases use
    `Expr.substTyFvar Z U e ≡ Expr.substTyFvars [(Z, U)] e` together with the
    public structural distribution lemmas. -/
theorem TypeOfHM.typ_subst_preservation_uniform {Z : Nat} {U : Ty} (h_U_lc : U.IsLC)
    {ctx : Ctx} {e : Expr} {τ : Ty} (h : TypeOfHM ctx e τ) :
    TypeOfHM ⟨ctx.env.substFvar Z U, ctx.ctors⟩ (e.substTyFvar Z U) (Ty.substFvar Z U τ) := by
  induction h using TypeOfHM.rec_strong with
  | primLitUnit => exact .primLitUnit
  | primLitInt => exact .primLitInt
  | primLitNat => exact .primLitNat
  | primLitChar => exact .primLitChar
  | primBinOpIntAdd => exact .primBinOpIntAdd
  | primBinOpIntSub => exact .primBinOpIntSub
  | primBinOpIntLt _ _ ihtrue ihfalse => exact .primBinOpIntLt ihtrue ihfalse
  | primBinOpCharLt _ _ ihtrue ihfalse => exact .primBinOpCharLt ihtrue ihfalse
  | app _ _ ihf ihinput =>
    simp only [Expr.substTyFvar]
    simp only [Ty.substFvar] at ihf
    exact .app ihf ihinput
  | lambda hpc hann heq hbody ihbody =>
    subst heq
    expose_names
    simp only [Ty.substFvar, Expr.substTyFvar]
    refine TypeOfHM.lambda (Ty.IsLC.substFvar h_U_lc hpc) ?_ rfl ?_
    · intro T hT
      rcases ann with _ | T₀
      · simp at hT
      · simp only [Option.map_some, Option.some.injEq] at hT
        subst hT
        have hpin := hann T₀ rfl
        simp only [hpin]
    · simpa only [Env.substFvar, List.map_cons, PolyTy.substFvar, PolyTy.mkTrivial] using ihbody
  | var hlook htyargs hinst =>
    simp only [Expr.substTyFvar]
    have hlook' := congrArg (Option.map (PolyTy.substFvar Z U)) hlook
    simp only [Option.map_some] at hlook'
    rw [← List.getElem?_map] at hlook'
    refine TypeOfHM.var hlook' ?_ (InstantiatesBy.substFvar h_U_lc hinst)
    intro tyArg hmem
    obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hmem
    exact Ty.IsLC.substFvar h_U_lc (htyargs t ht)
  | ctor hlook htyargs hinst =>
    simp only [Expr.substTyFvar]
    have hbody := InstantiatesBy.substFvar (Z := Z) (U := U) h_U_lc hinst
    rw [Ty.substFvar_fresh (NoFreeVars.not_mem_freeVars (Ctor.toTy_body_noFreeVars _) Z)] at hbody
    refine TypeOfHM.ctor hlook ?_ hbody
    intro tyArg hmem
    obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hmem
    exact Ty.IsLC.substFvar h_U_lc (htyargs t ht)
  | letIn hwf hann hcofin heq hbody ihcofin ihbody =>
    subst heq
    expose_names
    simp only [Expr.substTyFvar]
    refine TypeOfHM.letIn (M := PolyTy.substFvar Z U M) (L := Z :: L)
      (PolyTy.WF.substFvar h_U_lc hwf) ?_ ?_ rfl ?_
    · intro σ hσ
      rcases ann with _ | σ₀
      · simp at hσ
      · simp only [Option.map_some, Option.some.injEq] at hσ
        subst hσ
        have hpin := hann σ₀ rfl
        simp only [hpin]
    · intro Xs hfresh
      have hZ_notin : Z ∉ Xs := fun hc => hfresh.avoid Z hc List.mem_cons_self
      have hXs_freshL : FreshNames L M.paramCount Xs :=
        ⟨by simpa using hfresh.length, hfresh.nodup,
         fun x hx hc => hfresh.avoid x hx (List.mem_cons_of_mem _ hc)⟩
      have hbe := ihcofin Xs hXs_freshL
      rw [Expr.substTyFvar_openBoundTyVars h_U_lc hZ_notin] at hbe
      have hopen : (M.substFvar Z U).openVars Xs = Ty.substFvar Z U (M.openVars Xs) := by
        unfold PolyTy.openVars PolyTy.substFvar
        exact (Ty.substFvar_openVars h_U_lc hZ_notin).symm
      rw [hopen]
      exact hbe
    · simpa only [Env.substFvar, List.map_cons] using ihbody
  | match_ hscrut hne hbrs ihscrut ihbrs =>
    rw [Expr.substTyFvar_eq_substTyFvars_single, Expr.substTyFvars_match]
    refine TypeOfHM.match_ ihscrut ?_ ?_
    · simpa using hne
    · intro branch' hmem'
      obtain ⟨⟨pat, body⟩, hmem, rfl⟩ := List.mem_map.mp hmem'
      rcases ihbrs (pat, body) hmem with
        ⟨ct, c, n, tyArgs, instContents, hpat, hlook, hScrutEq, hpc, hcontents, hinstC, _, hbodyIH⟩ |
        ⟨hpat, _, hbodyIH⟩
      · subst hpat
        have hcc : ct.contents.map (Ty.substFvar Z U) = ct.contents := by
          have hpt : ∀ c ∈ ct.contents, Ty.substFvar Z U c = id c := fun c hc =>
            Ty.substFvar_fresh ((ct.closed c hc).not_mem_freeVars Z)
          rw [List.map_congr_left hpt, List.map_id]
        have hinstC' := InstantiatesBy.forall2_substFvar (Z := Z) (U := U) h_U_lc hinstC
        rw [hcc] at hinstC'
        rw [Env.substFvar_append, Env.substFvar_map_mkTrivial] at hbodyIH
        refine TypeOfMatchBranch.mk
          ⟨hlook, ?_, by simpa using hpc, hcontents, hinstC'⟩ rfl hbodyIH
        rw [hScrutEq]; simp [Ty.substFvar, TyList.substFvar_eq_map]
      · subst hpat
        exact TypeOfMatchBranch.wildcard hbodyIH
  | letRec hvalid hwf hmono hpoly heq hbody ihmono ihpoly ihbody =>
    -- Fused-node port of Core's `TypeOfElabHM.typ_subst_preservation_uniform`
    -- `letRec` case: pool freshening `G ↦ W`, monotypes transported by
    -- `renameG_substFvar_comm`/`renameG_renameG`/`genGroup_renameG`, schemes
    -- substituted pointwise, the env transport split pointwise by `RecSpec`.
    subst heq
    expose_names
    rw [Expr.substTyFvar_eq_substTyFvars_single, Expr.substTyFvars_letRec]
    obtain ⟨W, hWlen0, hWnodup, hWavoid⟩ :=
      exists_fresh_names (G ++ [Z] ++ U.freeVars ++ specs.flatMap RecSpec.monoFreeVars) G.length
    have hWG : ∀ w ∈ W, w ∉ G := fun w hw hc =>
      hWavoid w hw (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ hc)))
    have hGW : ∀ g ∈ G, g ∉ W := fun g hg hc => hWG g hc hg
    have hZW : Z ∉ W := fun hc =>
      hWavoid Z hc (List.mem_append_left _ (List.mem_append_left _
        (List.mem_append_right _ (List.mem_singleton.2 rfl))))
    have hUW : ∀ u ∈ U.freeVars, u ∉ W := fun u hu hc =>
      hWavoid u hc (List.mem_append_left _ (List.mem_append_right _ hu))
    have hWfree : ∀ τ, RecSpec.mono τ ∈ specs → ∀ w ∈ W, w ∉ τ.freeVars :=
      fun τ hτ w hw hc =>
        hWavoid w hw (List.mem_append_right _
          (List.mem_flatMap.mpr ⟨.mono τ, hτ, hc⟩))
    refine TypeOfHM.letRec
      (specs := specs.map (RecSpec.substFreshened Z U G W))
      (groups := groups) (G := W) (L := Z :: (G ++ W ++ L))
      (hvalid.substTyFvars [(Z, U)])
      ⟨?_, hWnodup, ?_, ?_⟩ ?_ ?_ rfl ?_
    · calc
        (specs.map (RecSpec.substFreshened Z U G W)).map RecSpec.ann =
            (specs.map RecSpec.ann).map (RecAnn.substFvars [(Z, U)]) := by
              simp only [List.map_map]
              apply List.map_congr_left
              intro s _
              cases s <;> rfl
        _ = (bindings.map RecBinding.ann).map (RecAnn.substFvars [(Z, U)]) := by
              rw [hwf.anns_eq]
        _ = (bindings.map fun binding =>
            { ann := RecAnn.substFvars [(Z, U)] binding.ann
              rhs := binding.rhs.substTyFvars [(Z, U)] }).map RecBinding.ann := by
              simp only [List.map_map]
              apply List.map_congr_left
              intro binding _
              rfl
    · intro τ' hτ'
      obtain ⟨s, hs, hsubst⟩ := List.mem_map.mp hτ'
      cases s with
      | mono τ =>
        injection hsubst with hττ
        rw [← hττ]
        exact Ty.IsLC.substFvar h_U_lc (Ty.renameG_isLC (hwf.mono_lc τ hs))
      | poly σ => exact RecSpec.noConfusion hsubst
    · intro σ' hσ'
      obtain ⟨s, hs, hsubst⟩ := List.mem_map.mp hσ'
      cases s with
      | mono τ => exact RecSpec.noConfusion hsubst
      | poly σ =>
        injection hsubst with hσσ
        rw [← hσσ]
        exact PolyTy.WF.substFvar h_U_lc (hwf.poly_wf σ hs)
    · -- UNANNOTATED members: the historical `letRec` transport
      intro stage component hc Xs hfresh member hm binding τ' hbinding hτ'
      have hXlen : Xs.length = G.length := hfresh.length.trans hWlen0
      have hZXs : Z ∉ Xs := fun hc => hfresh.avoid Z hc List.mem_cons_self
      have hGXs : ∀ g ∈ G, g ∉ Xs := fun g hg hc =>
        hfresh.avoid g hc (List.mem_cons_of_mem _
          (List.mem_append_left _ (List.mem_append_left _ hg)))
      have hWXs : ∀ w ∈ W, w ∉ Xs := fun w hw hc =>
        hfresh.avoid w hc (List.mem_cons_of_mem _
          (List.mem_append_left _ (List.mem_append_right _ hw)))
      have hXsL : FreshNames L G.length Xs :=
        ⟨hXlen, hfresh.nodup, fun x hx hc =>
          hfresh.avoid x hx (List.mem_cons_of_mem _ (List.mem_append_right _ hc))⟩
      have key : ∀ τ, RecSpec.mono τ ∈ specs →
          Ty.renameG W Xs (Ty.substFvar Z U (Ty.renameG G W τ))
            = Ty.substFvar Z U (Ty.renameG G Xs τ) := by
        intro τ hτ
        rw [Ty.renameG_substFvar_comm h_U_lc hZW hUW hZXs
              (Ty.renameG_isLC (hwf.mono_lc τ hτ)) hWnodup hfresh.length hWXs,
            Ty.renameG_renameG (hwf.mono_lc τ hτ) hwf.nodup hWnodup hWlen0 hXlen hGW
              (hWfree τ hτ) hWXs hGXs]
      have henv_rhs : (specs.map (RecSpec.substFreshened Z U G W)).mapIdx
          (RecSpec.stageEntry (groups.take stage).flatten W Xs)
          = Env.substFvar Z U (specs.mapIdx
            (RecSpec.stageEntry (groups.take stage).flatten G Xs)) := by
        apply List.ext_getElem?
        intro i
        simp only [Env.substFvar, List.getElem?_map, List.getElem?_mapIdx, Option.map_map]
        cases hs : specs[i]? with
        | none => rfl
        | some s =>
          simp only [Option.map_some, Option.some.injEq, Function.comp_apply]
          have hsmem := List.mem_of_getElem? hs
          cases s with
          | mono τ =>
            simp only [RecSpec.substFreshened, RecSpec.stageEntry]
            split
            · rw [PolyTy.genGroup_renameG (hwf.mono_lc τ hsmem) hWlen0 hwf.nodup hWnodup
                hGW (hWfree τ hsmem), PolyTy.genGroup_substFvar hZW hUW]
            · rw [key τ hsmem]; rfl
          | poly σ => rfl
      rw [List.getElem?_map] at hbinding hτ'
      obtain ⟨a, ha, rfl⟩ := Option.map_eq_some_iff.mp hbinding
      obtain ⟨b, hb, hbs⟩ := Option.map_eq_some_iff.mp hτ'
      cases b with
      | poly σ => exact RecSpec.noConfusion hbs
      | mono τ =>
        injection hbs with hττ
        rw [← hττ, key τ (List.mem_of_getElem? hb)]
        have hIH := ihmono stage component hc Xs hXsL member hm a τ ha hb
        simp only [RecSpecs.stageCtx] at hIH
        rw [Env.substFvar_append, ← henv_rhs] at hIH
        exact hIH
    · -- Signed members are checked under the final body context.
      intro p hp σ' hσ' Ys hYs
      obtain ⟨a, b, hab, rfl⟩ := List.exists_mem_zip_of_mem_zip_map hp
      cases b with
      | mono τ => exact RecSpec.noConfusion hσ'
      | poly σ =>
        injection hσ' with hσσ
        rw [← hσσ]
        have hpc : σ'.paramCount = σ.paramCount := by rw [← hσσ]; rfl
        have hZYs : Z ∉ Ys := fun hc =>
          hYs.avoid Z hc List.mem_cons_self
        have hYsOld : FreshNames L σ.paramCount Ys := by
          refine ⟨hYs.length.trans hpc, hYs.nodup, ?_⟩
          intro y hy hc
          exact hYs.avoid y hy (List.mem_cons_of_mem _
            (List.mem_append_right _ hc))
        have hIH := ihpoly (a, .poly σ) hab σ rfl Ys hYsOld
        have henv_body : (specs.map (RecSpec.substFreshened Z U G W)).map
            (RecSpec.bodyScheme W) =
            Env.substFvar Z U (specs.map (RecSpec.bodyScheme G)) := by
          show _ = (specs.map (RecSpec.bodyScheme G)).map (PolyTy.substFvar Z U)
          rw [List.map_map, List.map_map]
          apply List.map_congr_left
          intro s hs
          cases s with
          | mono τ =>
            show PolyTy.genGroup W (Ty.substFvar Z U (Ty.renameG G W τ))
              = PolyTy.substFvar Z U (PolyTy.genGroup G τ)
            rw [PolyTy.genGroup_renameG (hwf.mono_lc τ hs) hWlen0 hwf.nodup hWnodup hGW
                  (hWfree τ hs), PolyTy.genGroup_substFvar hZW hUW]
          | poly σ => rfl
        simp only [RecSpecs.bodyCtx] at hIH
        rw [Expr.substTyFvar_openTyVars h_U_lc hZYs,
            ← PolyTy.substFvar_openVars h_U_lc hZYs,
            Env.substFvar_append, ← henv_body] at hIH
        exact hIH
    · -- the body: env transport pointwise by constructor
      have henv_body : (specs.map (RecSpec.substFreshened Z U G W)).map (RecSpec.bodyScheme W)
          = Env.substFvar Z U (specs.map (RecSpec.bodyScheme G)) := by
        show _ = (specs.map (RecSpec.bodyScheme G)).map (PolyTy.substFvar Z U)
        rw [List.map_map, List.map_map]
        apply List.map_congr_left
        intro s hs
        cases s with
        | mono τ =>
          show PolyTy.genGroup W (Ty.substFvar Z U (Ty.renameG G W τ))
            = PolyTy.substFvar Z U (PolyTy.genGroup G τ)
          rw [PolyTy.genGroup_renameG (hwf.mono_lc τ hs) hWlen0 hwf.nodup hWnodup hGW
                (hWfree τ hs),
              PolyTy.genGroup_substFvar hZW hUW]
        | poly σ => rfl
      simp only [RecSpecs.bodyCtx] at ihbody
      rw [Env.substFvar_append, ← henv_body] at ihbody
      exact ihbody

/-- Single-variable substitution preserves `TypeOfHM` across the whole context. -/
theorem TypeOfHM.onSubstFvar {ctx : Ctx} {e : Expr} {τ : Ty} (Z : Nat) (U : Ty)
    (hU : U.IsLC) (h : TypeOfHM ctx e τ) :
    TypeOfHM (Subst.onCtx [(Z, U)] ctx) (e.substTyFvar Z U) (Subst.onTy [(Z, U)] τ) :=
  TypeOfHM.typ_subst_preservation_uniform hU h

/-- **Substitution preservation for `TypeOfHM`** over a whole substitution,
    obtained by iterating `onSubstFvar`. No `CtxWF` premise is needed. -/
theorem TypeOfHM.onSubst {ctx : Ctx} {e : Expr} {τ : Ty} (S : Subst)
    (h_lc : ∀ p ∈ S, p.2.IsLC) (h : TypeOfHM ctx e τ) :
    TypeOfHM (S.onCtx ctx) (e.substTyFvars S) (S.onTy τ) := by
  induction S generalizing ctx e τ with
  | nil => simpa [Expr.substTyFvars] using h
  | cons hd S' ih =>
    obtain ⟨Z, U⟩ := hd
    have hU : U.IsLC := h_lc (Z, U) (List.mem_cons_self ..)
    have hS' : ∀ p ∈ S', p.2.IsLC := fun p hp => h_lc p (List.mem_cons_of_mem _ hp)
    have step := TypeOfHM.onSubstFvar Z U hU h
    have rest := ih hS' step
    rw [show ((Z, U) :: S') = [(Z, U)] ++ S' from rfl, Subst.onCtx_append, Subst.onTy_append]
    exact rest

/-- **Fixed-term corollary of `TypeOfHM.onSubst`.** When `S` fixes `e`'s annotation
    free vars (`e.substTyFvars S = e`), preservation keeps the term fixed. -/
theorem TypeOfHM.onSubst_fixed {ctx : Ctx} {e : Expr} {τ : Ty} (S : Subst)
    (h_lc : ∀ p ∈ S, p.2.IsLC) (h_fix : e.substTyFvars S = e) (h : TypeOfHM ctx e τ) :
    TypeOfHM (S.onCtx ctx) e (S.onTy τ) := by
  have key := TypeOfHM.onSubst S h_lc h
  rwa [h_fix] at key

/-- **Iterated fixed-environment substitution preservation for `TypeOfHM`.**
    When substitution keys avoid the environment's free variables, only the
    term and result type change. -/
theorem TypeOfHM.typ_substs_preservation {ctx : Ctx} {e : Expr}
    (pairs : List (Nat × Ty))
    (h_fresh : ∀ p ∈ pairs, p.1 ∉ ctx.env.freeVars)
    (h_lc : ∀ p ∈ pairs, Ty.IsLC p.2)
    {τ : Ty} (h : TypeOfHM ctx e τ) :
    TypeOfHM ctx (e.substTyFvars pairs) (Ty.substFvars pairs τ) := by
  induction pairs generalizing e τ with
  | nil => exact h
  | cons hd tl ih =>
    obtain ⟨Z, U⟩ := hd
    simp only [Expr.substTyFvars, Ty.substFvars]
    have hZ : Z ∉ ctx.env.freeVars := h_fresh (Z, U) List.mem_cons_self
    have hU : Ty.IsLC U := h_lc (Z, U) List.mem_cons_self
    have hstep := TypeOfHM.typ_subst_preservation_uniform (Z := Z) (U := U) hU h
    rw [Env.substFvar_fresh hZ] at hstep
    exact ih (fun p hp => h_fresh p (List.mem_cons_of_mem _ hp))
             (fun p hp => h_lc p (List.mem_cons_of_mem _ hp)) hstep

/-! Regularity for `TypeOfHM`: a declaratively typed term has a locally closed
    type. The variable and constructor cases use the existential locally closed
    instantiation witness. -/
mutual
theorem TypeOfHM.regular : {ctx : Ctx} → {e : Expr} → {τ : Ty} →
    TypeOfHM ctx e τ → τ.IsLC
  | _, _, _, .primLitUnit => .prim
  | _, _, _, .primLitInt => .prim
  | _, _, _, .primLitNat => .prim
  | _, _, _, .primLitChar => .prim
  | _, _, _, .primBinOpIntAdd => .arrow .prim (.arrow .prim .prim)
  | _, _, _, .primBinOpIntSub => .arrow .prim (.arrow .prim .prim)
  | _, _, _, .primBinOpIntLt _ _ => .arrow .prim (.arrow .prim (.customTy (by simp)))
  | _, _, _, .primBinOpCharLt _ _ => .arrow .prim (.arrow .prim (.customTy (by simp)))
  | _, _, _, .lambda hpc _ _ hbody => .arrow hpc (TypeOfHM.regular hbody)
  | _, _, _, .app hf _ => by
    have := TypeOfHM.regular hf; cases this with | arrow _ hret => exact hret
  | _, _, _, .letIn _ _ _ _ hbody => TypeOfHM.regular hbody
  | _, _, _, .var _ htyargs hinst => InstantiatesBy.preserves_bvars htyargs hinst
  | _, _, _, .ctor _ htyargs hinst => InstantiatesBy.preserves_bvars htyargs hinst
  | _, _, _, @TypeOfHM.match_ _ _ _ branches _ hscrut hne hbrs => by
    obtain ⟨hd, tl, rfl⟩ := List.exists_cons_of_ne_nil hne
    exact TypeOfMatchBranch.regular (hbrs hd (List.mem_cons_self ..))
  | _, _, _, .letRec _ _ _ _ _ hbody => TypeOfHM.regular hbody

theorem TypeOfMatchBranch.regular : {ctx : Ctx} → {br : MatchPattern × Expr} →
    {scrutTy : Ty} → {rt : Ty} →
    TypeOfMatchBranch ctx br scrutTy rt → rt.IsLC
  | _, _, _, _, .mk _ _ hbody => TypeOfHM.regular hbody
  | _, _, _, _, .wildcard hbody => TypeOfHM.regular hbody
end

/-! ## Well-typed terms have every free var below the context length

`TypeOfHM` maintains the invariant that a well-typed expression is
`varsBelow ctx.env.length`: the `var` rule forces an in-range context lookup, and
every binder rule extends the environment by exactly the amount required by
`varsBelow`'s bookkeeping. -/

/-- Every left element of a length-matched pair of lists occurs in their zip. -/
private theorem mem_zip_of_mem_left {α β : Type _} :
    ∀ {l : List α} {r : List β}, l.length = r.length → ∀ {a : α}, a ∈ l →
      ∃ b, (a, b) ∈ l.zip r := by
  intro l
  induction l with
  | nil => intro r _ a ha; exact absurd ha (List.not_mem_nil)
  | cons x xs ih =>
    intro r hlen a ha
    cases r with
    | nil => simp only [List.length_cons, List.length_nil] at hlen; exact absurd hlen (by omega)
    | cons y ys =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at hlen
      rcases List.mem_cons.mp ha with rfl | ha'
      · exact ⟨y, by rw [List.zip_cons_cons]; exact List.mem_cons_self⟩
      · obtain ⟨b, hb⟩ := ih hlen ha'
        exact ⟨b, by rw [List.zip_cons_cons]; exact List.mem_cons_of_mem _ hb⟩

/-- The `match_` per-branch motive of `TypeOfHM.varsBelow`: each branch body is
    closed under the context extended by the pattern's `bindCount`. -/
private theorem branchMotive_varsBelow {ctx : Ctx} {pat : MatchPattern} {body : Expr}
    {scrutTy resultTy : Ty}
    (h : TypeOfHM.BranchMotive (fun c e _ _ => Expr.varsBelow c.env.length e = true)
          ctx (pat, body) scrutTy resultTy) :
    Expr.varsBelow (ctx.env.length + pat.bindCount) body = true := by
  rcases h with
    ⟨ctor, c, m, tyArgs, instContents, hpat, _, _, _, hbindCount, hfields, _, ihb⟩
    | ⟨hpat, _, ihb⟩
  · simp only at hpat
    subst hpat
    have hlen : instContents.length = m := by
      have hfe := List.Forall₂.length_eq hfields
      rw [hbindCount]
      omega
    simp only [MatchPattern.bindCount]
    simp only [List.length_append, List.length_map] at ihb
    rw [hlen] at ihb
    rwa [Nat.add_comm] at ihb
  · simp only at hpat
    subst hpat
    simpa only [MatchPattern.bindCount, Nat.add_zero] using ihb

/-- Assemble a closed branch list from the per-branch motives. -/
private theorem branchList_varsBelow_of_motive {ctx : Ctx} {scrutTy resultTy : Ty} :
    ∀ (brs : List (MatchPattern × Expr)),
      (∀ branch ∈ brs, TypeOfHM.BranchMotive
        (fun c e _ _ => Expr.varsBelow c.env.length e = true) ctx branch scrutTy resultTy) →
      BranchListClosed.varsBelow ctx.env.length brs = true := by
  intro brs
  induction brs with
  | nil => intro _; rfl
  | cons hd tl ih =>
    obtain ⟨pat, body⟩ := hd
    intro hbrs
    simp only [BranchListClosed.varsBelow, Bool.and_eq_true]
    exact ⟨branchMotive_varsBelow (hbrs (pat, body) List.mem_cons_self),
      ih (fun br hbr => hbrs br (List.mem_cons_of_mem _ hbr))⟩

/-- **Well-typed ⇒ all free term variables are below the context length.** -/
theorem TypeOfHM.varsBelow {ctx : Ctx} {e : Expr} {τ : Ty}
    (h : TypeOfHM ctx e τ) : Expr.varsBelow ctx.env.length e = true := by
  induction h using TypeOfHM.rec_strong with
  | primLitUnit => rfl
  | primLitInt => rfl
  | primLitNat => rfl
  | primLitChar => rfl
  | primBinOpIntAdd => rfl
  | primBinOpIntSub => rfl
  | primBinOpIntLt _ _ _ _ => rfl
  | primBinOpCharLt _ _ _ _ => rfl
  | ctor _ _ _ => rfl
  | var hlook _ _ =>
    simp only [Expr.varsBelow, decide_eq_true_eq]
    by_contra hle
    push_neg at hle
    rw [List.getElem?_eq_none hle] at hlook
    exact Option.noConfusion hlook
  | lambda hpc hann heq hbody ihbody =>
    subst heq
    simpa only [Expr.varsBelow, List.length_cons] using ihbody
  | app hf hinput ihf ihinput =>
    simp only [Expr.varsBelow, Bool.and_eq_true]
    exact ⟨ihf, ihinput⟩
  | letIn hwf hann hcofin heq hbody ihcofin ihbody =>
    expose_names
    subst heq
    simp only [Expr.varsBelow, Bool.and_eq_true]
    refine ⟨?_, by simpa only [List.length_cons] using ihbody⟩
    obtain ⟨Xs, hXlen, hXnodup, hXavoid⟩ := exists_fresh_names L M.paramCount
    have hc := ihcofin Xs ⟨hXlen, hXnodup, hXavoid⟩
    rwa [Expr.varsBelow_openBoundTyVars] at hc
  | match_ hscrut hne hbrs ihscrut ihbrs =>
    simp only [Expr.varsBelow, Bool.and_eq_true]
    exact ⟨ihscrut, branchList_varsBelow_of_motive _ ihbrs⟩
  | letRec hvalid hwf hmono hpoly heq hbody ihmono ihpoly ihbody =>
    expose_names
    subst heq
    simp only [Expr.varsBelow, Bool.and_eq_true]
    have hspecslen : bindings.length = specs.length := hwf.length
    refine ⟨?_, ?_⟩
    · -- every binding is closed under the group-extended context
      apply RecGroupClosed.varsBelow_of_forall
      intro bnd hmem
      obtain ⟨s, hs⟩ := mem_zip_of_mem_left hspecslen hmem
      obtain ⟨Xs, hXlen, hXnodup, hXavoid⟩ := exists_fresh_names L G.length
      rcases s with τ | σ
      · obtain ⟨member, hpair⟩ := List.mem_iff_getElem?.mp hs
        rw [List.getElem?_zip_eq_some] at hpair
        obtain ⟨hrhs, hspec⟩ := hpair
        have hmember : member < bindings.length :=
          (List.getElem?_eq_some_iff.mp hrhs).choose
        have hu : RecGroups.UnsignedAt bindings member := by
          rw [RecGroups.UnsignedAt, hrhs]
          have ha := congrArg (fun xs => xs[member]?) hwf.anns_eq
          simp only [List.getElem?_map, hspec, hrhs, Option.map_some, RecSpec.ann] at ha
          exact ha.symm
        obtain ⟨component, hc, hm⟩ := List.mem_flatten.mp
          ((hvalid.covers_unsigned member hmember).mpr hu)
        obtain ⟨stage, hstage⟩ := List.mem_iff_getElem?.mp hc
        have hc := ihmono stage component hstage Xs ⟨hXlen, hXnodup, hXavoid⟩
          member hm bnd τ hrhs hspec
        simp only [RecSpecs.stageCtx, List.length_append, List.length_mapIdx] at hc
        rwa [Nat.add_comm, ← hspecslen] at hc
      · obtain ⟨Ys, hYlen, hYnodup, hYavoid⟩ := exists_fresh_names L σ.paramCount
        have hc := ihpoly (bnd, .poly σ) hs σ rfl Ys ⟨hYlen, hYnodup, hYavoid⟩
        simp only [RecSpecs.bodyCtx, List.length_append, List.length_map] at hc
        rw [Expr.varsBelow_openTyVars] at hc
        rwa [Nat.add_comm, ← hspecslen] at hc
    · -- the body is closed under the group-extended context
      simp only [RecSpecs.bodyCtx, List.length_append, List.length_map] at ihbody
      rwa [Nat.add_comm, ← hspecslen] at ihbody

/-- **Well-typed in the empty context ⇒ closed.** -/
theorem TypeOfHM.closed {ctors : CtorEnv} {e : Expr} {τ : Ty}
    (h : TypeOfHM ⟨[], ctors⟩ e τ) : Expr.varsBelow 0 e = true :=
  TypeOfHM.varsBelow h

/-! ### Cofinite `GeneralisesTo` instantiation

The `TypeOfHM`/`Step` dynamics instantiates a cofinite `let`/`letRec` scheme
premise ("the bound value types at every opening of `M`") at a single type `τ`.
`Ty.substFvars_zip_openVars_eq` is the type-side round-trip (substituting the
zipped fresh names back recovers the `InstantiatesBy` instance), and the two
`GeneralisesTo_inst*` lemmas package it against `TypeOfHM` for terms in the
image of `Expr.erase`. -/

/-- Scheme `σ` instantiates to monotype `τ` (the declarative `TypeOfHM.var`
    instantiation: some locally-closed args, no length constraint). -/
def Instantiates (σ : PolyTy) (τ : Ty) : Prop :=
  ∃ instArgs, (∀ a ∈ instArgs, a.IsLC) ∧ σ.InstantiatesTo instArgs τ

/-- If a term types at every opening of scheme `M`, and `M` instantiates to `τ`,
    then the term types at `τ` (the `GeneralisesTo`-instantiation lemma, the
    unannotated case — the annotated case collapses via `ann.Pins M`). -/
theorem GeneralisesTo_inst {ctx : Ctx} {e : Expr} {M : PolyTy} {L : List Nat} {τ : Ty}
    (hgen : GeneralisesTo TypeOfHM ctx none e M L) (hinst : Instantiates M τ) :
    TypeOfHM ctx e τ := by
  rcases hinst with ⟨instArgs, hinstLC, hinstTo⟩
  -- Pick fresh names `Xs` (length `M.paramCount`) avoiding `L`, the context env's
  -- free vars, `e`'s annotation free vars, and the free vars of `instArgs` / `M.body`.
  obtain ⟨Xs, hXlen, hXnodup, hXavoid⟩ :=
    exists_fresh_names
      (L ++ ctx.env.freeVars ++ e.tyFreeVars ++ Ty.freeVarsList instArgs ++ M.body.freeVars)
      M.paramCount
  have hXL : ∀ x ∈ Xs, x ∉ L := fun x hx hc => hXavoid x hx (by simp only [List.mem_append]; tauto)
  have hXenv : ∀ x ∈ Xs, x ∉ ctx.env.freeVars := fun x hx hc =>
    hXavoid x hx (by simp only [List.mem_append]; tauto)
  have hXe : ∀ x ∈ Xs, x ∉ e.tyFreeVars := fun x hx hc =>
    hXavoid x hx (by simp only [List.mem_append]; tauto)
  have hXVs : ∀ x ∈ Xs, x ∉ Ty.freeVarsList instArgs := fun x hx hc =>
    hXavoid x hx (by simp only [List.mem_append]; tauto)
  have hXM : ∀ x ∈ Xs, x ∉ M.body.freeVars := fun x hx hc =>
    hXavoid x hx (by simp only [List.mem_append]; tauto)
  have hfresh : FreshNames L M.paramCount Xs := ⟨hXlen, hXnodup, hXL⟩
  have he : TypeOfHM ctx e (M.openVars Xs) := by
    simpa [Expr.openBoundTyVars] using hgen Xs hfresh
  -- Push the type-fvar substitution `Xs[i] ↦ instArgs[i]` through the derivation;
  -- the fresh names fix both the context and the term.
  have h_lc : ∀ p ∈ Xs.zip instArgs, Ty.IsLC p.2 := fun p hp =>
    hinstLC p.2 (List.of_mem_zip hp).2
  have hsub : TypeOfHM ctx (e.substTyFvars (Xs.zip instArgs))
      (Ty.substFvars (Xs.zip instArgs) (M.openVars Xs)) :=
    TypeOfHM.typ_substs_preservation (Xs.zip instArgs)
      (fun p hp => hXenv p.1 (List.of_mem_zip hp).1) h_lc he
  have hfix : e.substTyFvars (Xs.zip instArgs) = e :=
    Expr.substTyFvars_eq_self_of_not_mem_tyFreeVars (by
      intro p hp
      exact hXe p.1 (List.of_mem_zip hp).1)
  have hreg : (M.openVars Xs).IsLC := TypeOfHM.regular he
  have hty : Ty.substFvars (Xs.zip instArgs) (M.openVars Xs) = τ := by
    change Ty.substFvars (Xs.zip instArgs) (Ty.openVars Xs M.body) = τ
    exact Ty.substFvars_zip_openVars_eq (Xs := Xs) (Vs := instArgs)
      hXnodup hXVs M.body τ hinstTo hXM hreg
  rw [hfix, hty] at hsub
  exact hsub

/-- The annotated analogue of `GeneralisesTo_inst`: if a term in the image of
    `Expr.erase` types at every opening of scheme `M` (whether the `let` was
    annotated or not), and `M` instantiates to `τ`, then the term types at `τ`.
    Erased-ness rewrites the opening `openBoundTyVars ann Xs e` to `e` itself, so
    both the `none` and `some σ` cases collapse to the same substitution argument. -/
theorem GeneralisesTo_inst_ann {ctx : Ctx} {ann : Option PolyTy} {e : Expr}
    {M : PolyTy} {L : List Nat} {τ : Ty}
    (herased : e.erase = e)
    (hgen : GeneralisesTo TypeOfHM ctx ann e M L) (hinst : Instantiates M τ) :
    TypeOfHM ctx e τ := by
  rcases hinst with ⟨instArgs, hinstLC, hinstTo⟩
  -- Pick fresh names `Xs` (length `M.paramCount`) avoiding `L`, the context env's
  -- free vars, `e`'s annotation free vars, and the free vars of `instArgs` / `M.body`.
  obtain ⟨Xs, hXlen, hXnodup, hXavoid⟩ :=
    exists_fresh_names
      (L ++ ctx.env.freeVars ++ e.tyFreeVars ++ Ty.freeVarsList instArgs ++ M.body.freeVars)
      M.paramCount
  have hXL : ∀ x ∈ Xs, x ∉ L := fun x hx hc => hXavoid x hx (by simp only [List.mem_append]; tauto)
  have hXenv : ∀ x ∈ Xs, x ∉ ctx.env.freeVars := fun x hx hc =>
    hXavoid x hx (by simp only [List.mem_append]; tauto)
  have hXe : ∀ x ∈ Xs, x ∉ e.tyFreeVars := fun x hx hc =>
    hXavoid x hx (by simp only [List.mem_append]; tauto)
  have hXVs : ∀ x ∈ Xs, x ∉ Ty.freeVarsList instArgs := fun x hx hc =>
    hXavoid x hx (by simp only [List.mem_append]; tauto)
  have hXM : ∀ x ∈ Xs, x ∉ M.body.freeVars := fun x hx hc =>
    hXavoid x hx (by simp only [List.mem_append]; tauto)
  have hfresh : FreshNames L M.paramCount Xs := ⟨hXlen, hXnodup, hXL⟩
  -- Erased-ness collapses the opening: `openBoundTyVars none` is the identity,
  -- and `openBoundTyVars (some σ)` is `e.openTyVars Xs = e` (no scoped tyVars).
  have he : TypeOfHM ctx e (M.openVars Xs) := by
    cases ann with
    | none => simpa [Expr.openBoundTyVars] using hgen Xs hfresh
    | some σ =>
        have hopen : e.openTyVars Xs = e := by
          rw [← herased, Expr.openTyVars_eq_self_of_erase_image e Xs, herased]
        simpa [Expr.openBoundTyVars, hopen] using hgen Xs hfresh
  -- Push the type-fvar substitution `Xs[i] ↦ instArgs[i]` through the derivation;
  -- the fresh names fix both the context and the term.
  have h_lc : ∀ p ∈ Xs.zip instArgs, Ty.IsLC p.2 := fun p hp =>
    hinstLC p.2 (List.of_mem_zip hp).2
  have hsub : TypeOfHM ctx (e.substTyFvars (Xs.zip instArgs))
      (Ty.substFvars (Xs.zip instArgs) (M.openVars Xs)) :=
    TypeOfHM.typ_substs_preservation (Xs.zip instArgs)
      (fun p hp => hXenv p.1 (List.of_mem_zip hp).1) h_lc he
  have hfix : e.substTyFvars (Xs.zip instArgs) = e :=
    Expr.substTyFvars_eq_self_of_not_mem_tyFreeVars (by
      intro p hp
      exact hXe p.1 (List.of_mem_zip hp).1)
  have hreg : (M.openVars Xs).IsLC := TypeOfHM.regular he
  have hty : Ty.substFvars (Xs.zip instArgs) (M.openVars Xs) = τ := by
    change Ty.substFvars (Xs.zip instArgs) (Ty.openVars Xs M.body) = τ
    exact Ty.substFvars_zip_openVars_eq (Xs := Xs) (Vs := instArgs)
      hXnodup hXVs M.body τ hinstTo hXM hreg
  rw [hfix, hty] at hsub
  exact hsub

/-! ### Direct source-soundness support -/

/-- Append form of fixed-term substitution transport for source subjects. -/
theorem TypeOfHM.onSubst_fixed_append {ctx : Ctx} {e : Expr} {τ : Ty}
    (S₁ S₂ : Subst)
    (_h₁ : ∀ p ∈ S₁, p.2.IsLC) (h₂ : ∀ p ∈ S₂, p.2.IsLC)
    (_h_fix₁ : e.substTyFvars S₁ = e) (h_fix₂ : e.substTyFvars S₂ = e)
    (h : TypeOfHM (S₁.onCtx ctx) e τ) :
    TypeOfHM ((S₁ ++ S₂).onCtx ctx) e (S₂.onTy τ) := by
  have key := TypeOfHM.onSubst_fixed (ctx := S₁.onCtx ctx) (e := e) (τ := τ)
    S₂ h₂ h_fix₂ h
  simpa only [Subst.onCtx_append] using key


/-- Rebuild the mixed source rule at pool `G` from empty-pool checks.
    `hG_env`, `hG_specs`, and `hG_bs` ensure the renaming moves only the shared
    monotypes: the ambient environment, annotated schemes, and scoped source
    annotations keep their meaning. -/
theorem TypeOfHM.letRec_of_emptyPool {ctx : Ctx} {Lp G : List Nat}
    {bindings : List CoreRecBinding} {specs : List RecSpec}
    {groups : List (List Nat)}
    {body : Expr} {ρ : Ty}
    (hvalid : RecGroups.ValidResidualGroups bindings groups)
    (hwf : RecSpecs.WF bindings specs G)
    (hG_env : ∀ g ∈ G, g ∉ ctx.env.freeVars)
    (hG_specs : ∀ g ∈ G, ∀ σ, RecSpec.poly σ ∈ specs → g ∉ σ.body.freeVars)
    (hG_bs : ∀ g ∈ G, ∀ binding ∈ bindings, g ∉ binding.rhs.tyFreeVars)
    (hmono : ∀ stage component, groups[stage]? = some component →
      ∀ member ∈ component, ∀ binding τ,
      bindings[member]? = some binding → specs[member]? = some (.mono τ) →
      TypeOfHM (RecSpecs.algorithmStageCtx ctx specs (groups.take stage).flatten G)
        binding.rhs τ)
    (hpoly : ∀ p ∈ bindings.zip specs, ∀ σ, p.2 = RecSpec.poly σ →
      ∀ Ys, FreshNames Lp σ.paramCount Ys →
        TypeOfHM (RecSpecs.bodyCtx ctx specs G)
          (p.1.rhs.openTyVars Ys) (σ.openVars Ys))
    (hbody : TypeOfHM (RecSpecs.bodyCtx ctx specs G) body ρ) :
    TypeOfHM ctx (Expr.letRec bindings body) ρ := by
  have hctx_eq : ∀ (done Xs : List Nat),
      Subst.onCtx (G.zip (Xs.map (Ty.fvar ·)))
          (RecSpecs.algorithmStageCtx ctx specs done G)
        = RecSpecs.stageCtx ctx specs done G Xs := by
    intro done Xs
    simp only [Subst.onCtx, Subst.onEnv, RecSpecs.algorithmStageCtx, RecSpecs.stageCtx,
      List.map_append]
    congr 1
    congr 1
    · apply List.ext_getElem?
      intro i
      simp only [List.getElem?_map, List.getElem?_mapIdx, Option.map_map]
      cases hs : specs[i]? with
      | none => rfl
      | some s =>
        simp only [Option.map_some, Option.some.injEq, Function.comp_apply]
        cases s with
        | mono τ =>
          simp only [RecSpec.algorithmStageEntry, RecSpec.stageEntry]
          split
          · apply Subst.onPolyTy_eq_self_of_dom_avoids
            intro p hp hfree
            have hg := (List.of_mem_zip hp).1
            have hτ := Ty.freeVars_closeOver_subset hfree
            exact Ty.not_mem_closeOver_freeVars (by
              simp only [Ty.genFilter, List.mem_filter]
              exact ⟨hg, by simpa using hτ⟩) hfree
          · rfl
        | poly σ =>
          apply Subst.onPolyTy_eq_self_of_dom_avoids
          intro p hp hc
          exact hG_specs p.1 (List.of_mem_zip hp).1 σ (List.mem_of_getElem? hs) hc
    · simpa only [Subst.onEnv] using
        Subst.onEnv_eq_self_of_fresh (fun p hp => hG_env p.1 (List.of_mem_zip hp).1)
  refine TypeOfHM.letRec (specs := specs) (groups := groups) (G := G) (L := Lp ++ G)
    hvalid hwf ?mono ?poly rfl hbody
  · intro stage component hc Xs hXs member hm binding τ hbinding hτ
    have hctx := hctx_eq (groups.take stage).flatten Xs
    have hsrc := hmono stage component hc member hm binding τ hbinding hτ
    have hLC : ∀ q ∈ G.zip (Xs.map (Ty.fvar ·)), q.2.IsLC := by
      intro q hq
      obtain ⟨x, hx, hxeq⟩ := List.mem_map.mp (List.of_mem_zip hq).2
      rw [← hxeq]; exact ContainsBvarsUpTo.fvar
    have hfix : binding.rhs.substTyFvars (G.zip (Xs.map (Ty.fvar ·))) = binding.rhs :=
      Expr.substTyFvars_eq_self_of_not_mem_tyFreeVars (fun q hq hc =>
        hG_bs q.1 (List.of_mem_zip hq).1 binding (List.mem_of_getElem? hbinding) hc)
    have hren := TypeOfHM.onSubst_fixed (G.zip (Xs.map (Ty.fvar ·))) hLC hfix hsrc
    rw [hctx] at hren
    simpa [Subst.onTy, Ty.renameG] using hren
  · intro p hp σ hσ Ys hYs
    have hYs' : FreshNames Lp σ.paramCount Ys := by
      refine ⟨hYs.length, hYs.nodup, ?_⟩
      intro y hy hc
      exact hYs.avoid y hy (List.mem_append_left G hc)
    exact hpoly p hp σ hσ Ys hYs'

/-- Replacing a context scheme `M` by a more general `M'` preserves `TypeOfHM`.
    In the weakened-position variable case, `TypeOfHM.var`'s existential
    instantiation witness is supplied by `hgen`. -/
theorem TypeOfHM.weaken_scheme {ctors : CtorEnv} {env_post env : Env} {M M' : PolyTy}
    {e : Expr} {τ : Ty}
    (hgen : M'.Generalizes M)
    (h : TypeOfHM ⟨env_post ++ [M] ++ env, ctors⟩ e τ) :
    TypeOfHM ⟨env_post ++ [M'] ++ env, ctors⟩ e τ := by
  have H : ∀ {ctx : Ctx} {e₀ : Expr} {τ₀ : Ty}, TypeOfHM ctx e₀ τ₀ →
      ∀ ep : Env, ctx.env = ep ++ [M] ++ env →
      TypeOfHM ⟨ep ++ [M'] ++ env, ctx.ctors⟩ e₀ τ₀ := by
    intro ctx e₀ τ₀ hd
    induction hd using TypeOfHM.rec_strong with
    | primLitUnit => intro ep _; exact .primLitUnit
    | primLitInt => intro ep _; exact .primLitInt
    | primLitNat => intro ep _; exact .primLitNat
    | primLitChar => intro ep _; exact .primLitChar
    | primBinOpIntAdd => intro ep _; exact .primBinOpIntAdd
    | primBinOpIntSub => intro ep _; exact .primBinOpIntSub
    | primBinOpIntLt _ _ ihtrue ihfalse => intro ep heq; exact .primBinOpIntLt (ihtrue ep heq) (ihfalse ep heq)
    | primBinOpCharLt _ _ ihtrue ihfalse => intro ep heq; exact .primBinOpCharLt (ihtrue ep heq) (ihfalse ep heq)
    | app hf hinput ihf ihinput => intro ep heq; exact .app (ihf ep heq) (ihinput ep heq)
    | @lambda paramTy ann bodyCtx ctx body bodyTy hpc hann heqctx hbody ihbody =>
      intro ep heq
      refine TypeOfHM.lambda hpc hann rfl ?_
      have hbc := ihbody (PolyTy.mkTrivial paramTy :: ep) (by simp only [heqctx, heq, List.cons_append])
      simpa only [heqctx, List.cons_append] using hbc
    | @letIn ann ctx boundExpr bodyCtx body bodyTy Msch L hwf hann hcofin heqctx hbody ihcofin ihbody =>
      intro ep heq
      refine TypeOfHM.letIn hwf hann (fun Xs hfresh => ihcofin Xs hfresh ep heq) rfl ?_
      have hbc := ihbody (Msch :: ep) (by simp only [heqctx, heq, List.cons_append])
      simpa only [heqctx, List.cons_append] using hbc
    | @var dbl polyTy instArgs ty ctx hlook hbvars hinst =>
      intro ep heq
      rw [heq] at hlook
      rcases lt_trichotomy dbl ep.length with hlt | heqd | hgt
      · refine TypeOfHM.var ?_ hbvars hinst
        show (ep ++ [M'] ++ env)[dbl]? = _
        rw [List.append_assoc, List.getElem?_append_left hlt]
        rw [List.append_assoc, List.getElem?_append_left hlt] at hlook
        exact hlook
      · subst heqd
        have hpoly : polyTy = M := by
          rw [List.append_assoc, List.getElem?_append_right (le_refl ep.length)] at hlook
          simpa only [Nat.sub_self, List.singleton_append, List.getElem?_cons_zero,
            Option.some.injEq] using hlook.symm
        subst hpoly
        obtain ⟨instArgs', hbvars', hinst'⟩ := hgen instArgs ty hbvars hinst
        refine TypeOfHM.var ?_ hbvars' hinst'
        show (ep ++ [M'] ++ env)[ep.length]? = some M'
        rw [List.append_assoc, List.getElem?_append_right (le_refl ep.length)]
        simp only [Nat.sub_self, List.singleton_append, List.getElem?_cons_zero]
      · refine TypeOfHM.var ?_ hbvars hinst
        show (ep ++ [M'] ++ env)[dbl]? = _
        have hle : ep.length ≤ dbl := by omega
        rw [List.append_assoc, List.getElem?_append_right hle] at hlook
        rw [List.append_assoc, List.getElem?_append_right hle]
        rw [show ([M] ++ env) = M :: env from rfl] at hlook
        rw [show ([M'] ++ env) = M' :: env from rfl]
        rw [show (dbl - ep.length) = (dbl - ep.length - 1) + 1 from by omega] at hlook ⊢
        simp only [List.getElem?_cons_succ] at hlook ⊢
        exact hlook
    | ctor hlook htyargs hinst => intro ep _; exact .ctor hlook htyargs hinst
    | @match_ ctx scrut scrutTy branches resultTy hscrut hne hbrs ihscrut ihbrs =>
      intro ep heq
      refine TypeOfHM.match_ (ihscrut ep heq) hne ?_
      intro branch hmem
      obtain ⟨pat, body⟩ := branch
      rcases ihbrs (pat, body) hmem with
        ⟨ctorr, c, n, tyArgs, instContents, hpat, hlook, hscrutEq, hpc, hn, hinstC, _, ihbody⟩ |
        ⟨hpat, _, ihbody⟩
      · subst hpat
        refine TypeOfMatchBranch.mk ⟨hlook, hscrutEq, hpc, hn, hinstC⟩ rfl ?_
        have hbc := ihbody (instContents.map PolyTy.mkTrivial ++ ep)
          (by simp only [heq, List.append_assoc])
        simpa only [List.append_assoc] using hbc
      · subst hpat
        exact TypeOfMatchBranch.wildcard (ihbody ep heq)
    | letRec hvalid hwf hmono hpoly heq hbody ihmono ihpoly ihbody =>
      intro ep hep
      subst heq
      expose_names
      refine TypeOfHM.letRec (specs := specs) (groups := groups) (G := G) (L := L)
        hvalid hwf ?_ ?_ rfl ?_
      · intro stage component hcomponent Xs hfresh member hm rhs τ' hrhs hτ'
        have hc := ihmono stage component hcomponent Xs hfresh member hm rhs τ' hrhs hτ'
          (specs.mapIdx (RecSpec.stageEntry (groups.take stage).flatten G Xs) ++ ep)
          (by simp only [RecSpecs.stageCtx, hep, List.append_assoc])
        simp only [RecSpecs.stageCtx, List.append_assoc] at hc ⊢
        exact hc
      · intro p hp σ' hσ' Ys hYs
        have hc := ihpoly p hp σ' hσ' Ys hYs
          (specs.map (RecSpec.bodyScheme G) ++ ep)
          (by simp only [RecSpecs.bodyCtx, hep, List.append_assoc])
        simp only [RecSpecs.bodyCtx, List.append_assoc] at hc ⊢
        exact hc
      · have hb := ihbody (specs.map (RecSpec.bodyScheme G) ++ ep)
          (by simp only [RecSpecs.bodyCtx, hep, List.append_assoc])
        simp only [RecSpecs.bodyCtx, List.append_assoc] at hb ⊢
        exact hb
  exact H h env_post rfl

/-- Replacing a *list* of context schemes by pointwise more-general schemes preserves
    `TypeOfHM`. Direct port of `TypeOfHM.weaken_schemes` (iterates `weaken_scheme`). -/
theorem TypeOfHM.weaken_schemes {ctors : CtorEnv} {env : Env} {e : Expr} {τ : Ty}
    {Ms Ms' : List PolyTy}
    (hgen : List.Forall₂ PolyTy.Generalizes Ms' Ms)
    (h : TypeOfHM ⟨Ms ++ env, ctors⟩ e τ) :
    TypeOfHM ⟨Ms' ++ env, ctors⟩ e τ := by
  have H : ∀ {Ms Ms' : List PolyTy}, List.Forall₂ PolyTy.Generalizes Ms' Ms →
      ∀ (ep : Env), TypeOfHM ⟨ep ++ Ms ++ env, ctors⟩ e τ →
        TypeOfHM ⟨ep ++ Ms' ++ env, ctors⟩ e τ := by
    intro Ms Ms' hgen
    induction hgen with
    | nil => intro ep h; simpa using h
    | @cons M' M Mt' Mt hM htail ih =>
      intro ep h
      have h1 : TypeOfHM ⟨(ep ++ [M]) ++ Mt ++ env, ctors⟩ e τ := by
        simpa only [List.append_assoc, List.cons_append, List.nil_append,
          List.singleton_append] using h
      have h2 := ih (ep ++ [M]) h1
      have h3 := TypeOfHM.weaken_scheme (env_post := ep) (env := Mt' ++ env) hM
        (by simpa only [List.append_assoc, List.singleton_append] using h2)
      simpa only [List.append_assoc, List.cons_append, List.nil_append,
        List.singleton_append] using h3
  have hfin := H hgen [] (by simpa using h)
  simpa using hfin

/-- Inserting an environment segment and shifting term de Bruijn indices
    preserves `TypeOfHM`. Cofinite `letIn`/`letRec` premises are re-instantiated
    under the grown environment; variable lookup is remapped. -/
theorem TypeOfHM.weaken_env
    {ctors : CtorEnv} {env_pre env_extra env : Env} {e : Expr} {τ : Ty}
    (h : TypeOfHM ⟨env_pre ++ env, ctors⟩ e τ) :
    TypeOfHM ⟨env_pre ++ env_extra ++ env, ctors⟩
      (e.shiftFrom env_pre.length env_extra.length) τ := by
  suffices H : ∀ {ctx' : Ctx} {e' : Expr} {τ' : Ty}, TypeOfHM ctx' e' τ' →
      ∀ (env_pre' : Env), ctx'.env = env_pre' ++ env →
        TypeOfHM ⟨env_pre' ++ env_extra ++ env, ctx'.ctors⟩
          (e'.shiftFrom env_pre'.length env_extra.length) τ' by
    exact H h env_pre rfl
  intro ctx' e' τ' hd
  induction hd using TypeOfHM.rec_strong with
  | primLitUnit => intro env_pre' _; exact .primLitUnit
  | primLitInt => intro env_pre' _; exact .primLitInt
  | primLitNat => intro env_pre' _; exact .primLitNat
  | primLitChar => intro env_pre' _; exact .primLitChar
  | primBinOpIntAdd => intro env_pre' _; exact .primBinOpIntAdd
  | primBinOpIntSub => intro env_pre' _; exact .primBinOpIntSub
  | primBinOpIntLt _ _ ihtrue ihfalse =>
    intro env_pre' hctx
    exact .primBinOpIntLt (ihtrue env_pre' hctx) (ihfalse env_pre' hctx)
  | primBinOpCharLt _ _ ihtrue ihfalse =>
    intro env_pre' hctx
    exact .primBinOpCharLt (ihtrue env_pre' hctx) (ihfalse env_pre' hctx)
  | app hf hinput ihf ihinput =>
    intro env_pre' hctx
    simp only [Expr.shiftFrom]
    exact .app (ihf env_pre' hctx) (ihinput env_pre' hctx)
  | ctor hlook htyargs hinst =>
    intro env_pre' _
    exact .ctor hlook htyargs hinst
  | var hlook hlc hinst =>
    intro env_pre' hctx
    expose_names
    rw [hctx] at hlook
    simp only [Expr.shiftFrom]
    by_cases h_lt : dbl < env_pre'.length
    · rw [if_pos h_lt]
      refine .var ?_ hlc hinst

      show (env_pre' ++ env_extra ++ env)[dbl]? = _
      rw [List.getElem?_append_left
            (by simp only [List.length_append]; omega : dbl < (env_pre' ++ env_extra).length),
          List.getElem?_append_left h_lt]
      rwa [List.getElem?_append_left h_lt] at hlook
    · push_neg at h_lt
      rw [if_neg (Nat.not_lt.mpr h_lt)]
      refine .var ?_ hlc hinst
      show (env_pre' ++ env_extra ++ env)[dbl + env_extra.length]? = _
      rw [List.getElem?_append_right
            (by simp only [List.length_append]; omega :
              (env_pre' ++ env_extra).length ≤ dbl + env_extra.length)]
      rw [show dbl + env_extra.length - (env_pre' ++ env_extra).length = dbl - env_pre'.length
            from by simp only [List.length_append]; omega]
      rwa [List.getElem?_append_right h_lt] at hlook
  | lambda hpc hann heq hbody ihbody =>
    intro env_pre' hctx
    subst heq
    simp only [Expr.shiftFrom]
    refine TypeOfHM.lambda hpc hann rfl ?_
    expose_names
    have hb := ihbody (PolyTy.mkTrivial paramTy :: env_pre') (by rw [hctx, List.cons_append])
    simpa only [List.cons_append, List.length_cons] using hb
  | letIn hwf hann hcofin heq hbody ihcofin ihbody =>
    intro env_pre' hctx
    subst heq
    expose_names
    simp only [Expr.shiftFrom]
    refine TypeOfHM.letIn (M := M) (L := L) hwf hann ?_ rfl ?_
    · intro Xs hfresh
      have hc := ihcofin Xs hfresh env_pre' hctx
      rwa [Expr.shiftFrom_openBoundTyVars] at hc
    · have hb := ihbody (M :: env_pre') (by rw [hctx, List.cons_append])
      simpa only [List.cons_append, List.length_cons] using hb
  | match_ hscrut hne hbrs ihscrut ihbrs =>
    intro env_pre' hctx
    simp only [Expr.shiftFrom]
    refine TypeOfHM.match_ (ihscrut env_pre' hctx) ?_ ?_
    · intro hcontra
      obtain ⟨⟨p, b⟩, rest, hb⟩ := List.exists_cons_of_ne_nil hne
      have hmem' := BranchList.mem_shiftFrom_of_mem
        (threshold := env_pre'.length) (n := env_extra.length)
        (hb ▸ List.mem_cons_self (a := (p, b)))
      rw [hcontra] at hmem'
      exact List.not_mem_nil hmem'
    · intro branch' hmem'
      obtain ⟨pat, body, hmem, rfl⟩ := BranchList.mem_shiftFrom hmem'
      rcases ihbrs (pat, body) hmem with
        ⟨ctorr, c, n, tyArgs, instContents, hpat, hlook, hscrutEq, hpc, hn, hinstC, _, hbodyIH⟩ |
        ⟨hpat, _, hbodyIH⟩
      · subst hpat
        simp only [MatchPattern.bindCount]
        have hib := hbodyIH (instContents.map PolyTy.mkTrivial ++ env_pre')
          (by rw [hctx, List.append_assoc])
        simp only [List.length_append, List.length_map] at hib
        have hlen : instContents.length = n := by
          have := List.Forall₂.length_eq hinstC
          omega
        rw [hlen, show n + env_pre'.length = env_pre'.length + n from Nat.add_comm _ _] at hib
        refine TypeOfMatchBranch.mk ⟨hlook, hscrutEq, hpc, hn, hinstC⟩ rfl ?_
        rw [show env_pre' ++ env_extra ++ env = env_pre' ++ (env_extra ++ env)
              from List.append_assoc _ _ _]
        rw [List.append_assoc, List.append_assoc] at hib
        exact hib
      · subst hpat
        simp only [MatchPattern.bindCount, Nat.add_zero]
        exact TypeOfMatchBranch.wildcard (hbodyIH env_pre' hctx)
  | letRec hvalid hwf hmono hpoly heq hbody ihmono ihpoly ihbody =>
    intro env_pre' hctx
    subst heq
    expose_names
    simp only [Expr.shiftFrom, RecGroup.shiftFrom_eq_map]
    refine TypeOfHM.letRec (specs := specs) (G := G) (L := L)
      (groups := groups) (hvalid.shiftFrom _ _ (by omega))
      ⟨by simpa only [List.map_map, Function.comp_apply, RecBinding.mapRhs]
          using hwf.anns_eq,
        hwf.nodup, hwf.mono_lc, hwf.poly_wf⟩ ?_ ?_ rfl ?_
    · intro stage component hcomponent Xs hfresh member hm binding τ hbinding hτ
      rw [List.getElem?_map] at hbinding
      obtain ⟨a, ha, rfl⟩ := Option.map_eq_some_iff.mp hbinding
      have hc := ihmono stage component hcomponent Xs hfresh member hm a τ ha hτ
        (specs.mapIdx (RecSpec.stageEntry (groups.take stage).flatten G Xs) ++ env_pre')
        (by simp only [RecSpecs.stageCtx]; rw [hctx, List.append_assoc])
      simp only [RecSpecs.stageCtx, List.length_append, List.length_mapIdx] at hc
      rw [← hwf.length, Nat.add_comm bindings.length env_pre'.length] at hc
      simp only [RecSpecs.stageCtx, List.append_assoc] at hc ⊢
      exact hc
    · intro p hp σ hσ Ys hYs
      obtain ⟨a, b, _, hq, rfl⟩ := List.mem_zip_map_left hp
      have hc := ihpoly (a, b) hq σ hσ Ys hYs
        (specs.map (RecSpec.bodyScheme G) ++ env_pre')
        (by simp only [RecSpecs.bodyCtx]; rw [hctx, List.append_assoc])
      rw [Expr.shiftFrom_openTyVars] at hc
      simp only [RecSpecs.bodyCtx, List.length_append, List.length_map] at hc
      rw [← hwf.length, Nat.add_comm bindings.length env_pre'.length] at hc
      simp only [RecSpecs.bodyCtx, List.append_assoc] at hc ⊢
      exact hc
    · have hb := ihbody (specs.map (RecSpec.bodyScheme G) ++ env_pre')
        (by simp only [RecSpecs.bodyCtx]; rw [hctx, List.append_assoc])
      simp only [RecSpecs.bodyCtx, List.length_append, List.length_map] at hb
      rw [← hwf.length, Nat.add_comm bindings.length env_pre'.length] at hb
      simp only [RecSpecs.bodyCtx, List.append_assoc] at hb ⊢
      exact hb


private lemma TypeOfHM.ctor_chain_has_customTy_form
    {ctx e τ}
    (h_chain : SmallStep.IsCtorChain e) (h_ty : TypeOfHM ctx e τ) :
    ∃ name args tys, τ = Ty.wrapArrows (.customTy name args) tys := by
  induction e using Expr.rec_strong generalizing ctx τ with
  | ctor _ =>
    cases h_ty with
    | ctor _ _ hinst =>
      have hform : ∀ {name : TyName} {tyArgs : List Ty} {args tys : List Ty} {τ' : Ty},
          InstantiatesBy tyArgs (Ty.wrapArrows (.customTy name args) tys) τ' →
          ∃ instArgs instTys, τ' = Ty.wrapArrows (.customTy name instArgs) instTys := by
        intro name tyArgs args tys τ'
        induction tys generalizing τ' with
        | nil => intro h; cases h with | customTy _ => exact ⟨_, [], rfl⟩
        | cons _ rest ih =>
          intro h
          cases h with
          | arrow _ h_rest =>
            expose_names
            obtain ⟨instArgs, instRest, h_eq⟩ := ih h_rest
            refine ⟨instArgs, instFst :: instRest, ?_⟩
            simp [Ty.wrapArrows, h_eq]
      obtain ⟨instArgs, instTys, h_eq⟩ := hform hinst
      exact ⟨_, instArgs, instTys, h_eq⟩
  | app _ _ ihf _ =>
    cases h_chain with
    | app h_chain' _ =>
      cases h_ty with
      | app h_f_ty _ =>
        obtain ⟨name, args, tys, h_eq⟩ := ihf h_chain' h_f_ty
        cases tys with
        | nil => simp [Ty.wrapArrows] at h_eq
        | cons _ rest =>
          simp only [Ty.wrapArrows] at h_eq
          injection h_eq with _ h_ret
          exact ⟨name, args, rest, h_ret⟩
  | primLit _      => cases h_chain
  | primBinOp _    => cases h_chain
  | lambda _ _ _   => cases h_chain
  | letIn _ _ _ _ => cases h_chain
  | var _          => cases h_chain
  | match_ _ _ _ _ => cases h_chain
  | letRec _ _ _ _ => cases h_chain

/-- A value of arrow type is a λ, a ctor chain, a bare primop, or a one-argument-
    short primop application. -/
theorem TypeOfHM.canonical_arrow {ctx e argTy retTy}
    (h_ty : TypeOfHM ctx e (.arrow argTy retTy))
    (h_val : SmallStep.IsValue e) :
    (∃ ann body, e = .lambda ann body) ∨ SmallStep.IsCtorChain e
    ∨ (∃ op, e = .primBinOp op) ∨ (∃ op v, e = .app (.primBinOp op) v) := by
  cases h_val with
  | primLit _ => cases h_ty
  | lambda ann body => exact .inl ⟨ann, body, rfl⟩
  | ctor name => exact .inr (.inl (.ctor name))
  | ctorApp h_chain h_v => exact .inr (.inl (.app h_chain h_v))
  -- a bare primop and a one-argument-short application are both arrow-typed values
  | primBinOp op => exact .inr (.inr (.inl ⟨op, rfl⟩))
  | primBinOpPartial hv => exact .inr (.inr (.inr ⟨_, _, rfl⟩))

/-- A value of a data type is a constructor chain. -/
theorem TypeOfHM.canonical_customTy {ctx e tyName tyArgs}
    (h_ty : TypeOfHM ctx e (.customTy tyName tyArgs))
    (h_val : SmallStep.IsValue e) :
    SmallStep.IsCtorChain e := by
  cases h_val with
  | primLit _ => cases h_ty
  | lambda _ _ => cases h_ty
  | ctor name => exact .ctor name
  | ctorApp h_chain h_v => exact .app h_chain h_v
  -- `primBinOp`/`primBinOpPartial` are arrow-typed, never `customTy` — the typing
  -- rule for `.primBinOp _` forces an arrow, contradicting `customTy`.
  | primBinOp op => cases h_ty
  | primBinOpPartial hv => cases h_ty with | app h_pbo _ => cases h_pbo

/-- A value of type `int` is an integer literal. -/
theorem TypeOfHM.canonical_int {ctx e}
    (h_ty : TypeOfHM ctx e (.prim .int))
    (h_val : SmallStep.IsValue e) :
    ∃ m : Int, e = .primLit (.int m) := by
  cases h_val with
  | primLit p => cases h_ty; exact ⟨_, rfl⟩
  | lambda _ _ => cases h_ty
  | ctor name =>
    obtain ⟨_, _, tys, h_eq⟩ :=
      TypeOfHM.ctor_chain_has_customTy_form (.ctor name) h_ty
    cases tys <;> simp [Ty.wrapArrows] at h_eq
  | ctorApp h_chain h_v =>
    obtain ⟨_, _, tys, h_eq⟩ :=
      TypeOfHM.ctor_chain_has_customTy_form (.app h_chain h_v) h_ty
    cases tys <;> simp [Ty.wrapArrows] at h_eq
  | primBinOp op => cases h_ty
  | primBinOpPartial hv => cases h_ty with | app h_pbo _ => cases h_pbo

/-- A value of type `char` is a character literal. -/
theorem TypeOfHM.canonical_char {ctx e}
    (h_ty : TypeOfHM ctx e (.prim .char))
    (h_val : SmallStep.IsValue e) :
    ∃ c : Char, e = .primLit (.char c) := by
  cases h_val with
  | primLit p => cases h_ty; exact ⟨_, rfl⟩
  | lambda _ _ => cases h_ty
  | ctor name =>
    obtain ⟨_, _, tys, h_eq⟩ :=
      TypeOfHM.ctor_chain_has_customTy_form (.ctor name) h_ty
    cases tys <;> simp [Ty.wrapArrows] at h_eq
  | ctorApp h_chain h_v =>
    obtain ⟨_, _, tys, h_eq⟩ :=
      TypeOfHM.ctor_chain_has_customTy_form (.app h_chain h_v) h_ty
    cases tys <;> simp [Ty.wrapArrows] at h_eq
  | primBinOp op => cases h_ty
  | primBinOpPartial hv => cases h_ty with | app h_pbo _ => cases h_pbo

/-- (helper) `Forall₂` distributes over appending one element to both sides. -/
private theorem List.Forall₂.snoc {α β : Type _} {R : α → β → Prop}
    {l1 : List α} {l2 : List β} {a : α} {b : β}
    (h : List.Forall₂ R l1 l2) (hab : R a b) :
    List.Forall₂ R (l1 ++ [a]) (l2 ++ [b]) := by
  induction h with
  | nil => exact .cons hab .nil
  | cons hhd _ ih => exact .cons hhd ih

/-- A well-typed constructor chain decomposes into a head constructor applied to
    args, where the consumed fields are well-typed at their instantiations and
    the result type is the remaining fields wrapped over the (instantiated)
    `customTy`. -/
theorem TypeOfHM.ctor_chain_inversion {ctx : Ctx} {e : Expr} {τ : Ty}
    (h_chain : SmallStep.IsCtorChain e) (h_ty : TypeOfHM ctx e τ) :
    ∃ (name : CtorName) (args : List Expr) (ctor : Ctor)
      (tyArgs consumed remaining : List Ty),
      SmallStep.CtorAppliedTo e name args ∧
      LookupList.get? ctx.ctors name = some ctor ∧
      (∀ t ∈ tyArgs, ContainsBvarsUpTo 0 t) ∧
      ctor.contents = consumed ++ remaining ∧
      List.Forall₂ (fun a c => ∃ ct, InstantiatesBy tyArgs c ct ∧ TypeOfHM ctx a ct)
        args consumed ∧
      InstantiatesBy tyArgs
        (Ty.wrapArrows (.customTy ctor.tyName (Ty.bvarRange ctor.paramCount)) remaining) τ := by
  induction e using Expr.rec_strong generalizing τ with
  | ctor name =>
    cases h_ty with
    | ctor hlook htyargs hinst =>
      exact ⟨name, [], _, _, [], _, .base name, hlook, htyargs, rfl, .nil,
        by simpa [Ctor.toTy] using hinst⟩
  | app f arg ihf _ =>
    cases h_chain with
    | app hchainf hvarg =>
      cases h_ty with
      | app hf harg =>
        obtain ⟨name, args, ctor, tyArgs, consumed, remaining, hcat, hlook, htyargs,
          hcontents, hforall, hinst_f⟩ := ihf hchainf hf
        cases remaining with
        | nil =>
          simp only [Ty.wrapArrows] at hinst_f
          cases hinst_f
        | cons c rest =>
          simp only [Ty.wrapArrows] at hinst_f
          cases hinst_f with
          | arrow hc hrest =>
            refine ⟨name, args ++ [arg], ctor, tyArgs, consumed ++ [c], rest,
              .step hcat, hlook, htyargs, ?_, hforall.snoc ⟨_, hc, harg⟩, hrest⟩
            rw [hcontents]
            exact (List.append_assoc consumed [c] rest).symm
  | primLit _ => cases h_chain
  | primBinOp _ => cases h_chain
  | lambda _ _ _ => cases h_chain
  | letIn _ _ _ _ => cases h_chain
  | var _ => cases h_chain
  | match_ _ _ _ _ => cases h_chain
  | letRec _ _ _ _ => cases h_chain

/-- Progress: a closed, well-typed term is a value or takes a step. -/
theorem TypeOfHM.progress {ctx : Ctx} {e : Expr} {τ : Ty}
    (h_ty : TypeOfHM ctx e τ) (h_closed : ctx.env = [])
    (h_exh : SmallStep.AllMatchesExhaustive ctx.ctors e) (h_erased : e.erase = e) :
    SmallStep.IsValue e ∨ ∃ e', SmallStep.Step e e' := by
  have hrun := TypeOfHM.erase_preserves_typing h_ty
  rw [h_erased] at hrun
  exact RuntimeTyping.RunWT.progress hrun h_closed h_exh h_erased

/-! ### Preservation and type safety

Source checking erases into `RuntimeTyping.RunWT`; runtime subject reduction
then carries the source type through evaluation. Both the erased-input
compatibility statements and the annotated-source safety statements appear below. -/

/-- A checked source term that has already erased retains its type after one
runtime step. The resulting typing judgment keeps recursive scheme witnesses
in the proof, even though the syntax contains no annotations. -/
theorem TypeOfHM.preservation {ctx : Ctx} {e e' : Expr} {τ : Ty}
    (hstep : SmallStep.Step e e') (hty : TypeOfHM ctx e τ)
    (herased : e.erase = e) : RuntimeTyping.RunWT ctx e' τ := by
  have hrun := TypeOfHM.erase_preserves_typing hty
  rw [herased] at hrun
  exact RuntimeTyping.RunWT.preservation hstep hrun

/-- Runtime typing, erasedness, and exhaustiveness are preserved along every
finite execution of a checked, erased source term. -/
theorem TypeOfHM.preservation_star {ctors : CtorEnv} {e e' : Expr} {τ : Ty}
    (hrtc : Relation.ReflTransGen SmallStep.Step e e')
    (hty : TypeOfHM ⟨[], ctors⟩ e τ) (herased : e.erase = e)
    (hexh : SmallStep.AllMatchesExhaustive ctors e) :
    RuntimeTyping.RunWT ⟨[], ctors⟩ e' τ ∧ e'.erase = e' ∧
      SmallStep.AllMatchesExhaustive ctors e' := by
  have hrun := TypeOfHM.erase_preserves_typing hty
  rw [herased] at hrun
  induction hrtc with
  | refl => exact ⟨hrun, herased, hexh⟩
  | tail _ hstep ih =>
      obtain ⟨htyped, herased', hexh'⟩ := ih
      exact ⟨RuntimeTyping.RunWT.preservation hstep htyped,
        SmallStep.Step.preserves_erased herased' hstep,
        SmallStep.Step.preserves_exhaustive hexh' hstep⟩

/-- A checked, erased, exhaustive source program progresses, and every runtime
step preserves the source type under the runtime typing judgment. -/
theorem TypeOfHM.type_safety {ctors : CtorEnv} {e : Expr} {τ : Ty}
    (hty : TypeOfHM ⟨[], ctors⟩ e τ) (herased : e.erase = e)
    (hexh : SmallStep.AllMatchesExhaustive ctors e) :
    (SmallStep.IsValue e ∨ ∃ e', SmallStep.Step e e') ∧
    (∀ e', SmallStep.Step e e' → RuntimeTyping.RunWT ⟨[], ctors⟩ e' τ) :=
  ⟨TypeOfHM.progress hty rfl hexh herased,
    fun _ hstep => TypeOfHM.preservation hstep hty herased⟩

/-- Every term reached from a checked, erased source program retains its type
and is either a value or takes another step. -/
theorem TypeOfHM.type_safety_star {ctors : CtorEnv} {e : Expr} {τ : Ty}
    (hty : TypeOfHM ⟨[], ctors⟩ e τ) (herased : e.erase = e)
    (hexh : SmallStep.AllMatchesExhaustive ctors e) :
    ∀ e', Relation.ReflTransGen SmallStep.Step e e' →
      RuntimeTyping.RunWT ⟨[], ctors⟩ e' τ ∧
        (SmallStep.IsValue e' ∨ ∃ e'', SmallStep.Step e' e'') := by
  intro e' hrtc
  obtain ⟨hty', herased', hexh'⟩ := TypeOfHM.preservation_star hrtc hty herased hexh
  exact ⟨hty', RuntimeTyping.RunWT.progress hty' rfl hexh' herased'⟩

/-- Check first, erase second: annotations justify a runtime derivation before
execution begins, and every erased execution step preserves that type. -/
theorem TypeOfHM.erased_type_safety {ctors : CtorEnv} {e : Expr} {τ : Ty}
    (hty : TypeOfHM ⟨[], ctors⟩ e τ)
    (hexh : SmallStep.AllMatchesExhaustive ctors e) :
    (SmallStep.IsValue e.erase ∨ ∃ e', SmallStep.Step e.erase e') ∧
    (∀ e', SmallStep.Step e.erase e' → RuntimeTyping.RunWT ⟨[], ctors⟩ e' τ) := by
  have hrun := TypeOfHM.erase_preserves_typing hty
  exact ⟨RuntimeTyping.RunWT.progress hrun rfl hexh.erase e.erase_idem,
    fun _ hstep => RuntimeTyping.RunWT.preservation hstep hrun⟩

/-- Every term reached by executing an annotated source program's erasure keeps
the source type and continues to make progress. -/
theorem TypeOfHM.erased_type_safety_star {ctors : CtorEnv} {e : Expr} {τ : Ty}
    (hty : TypeOfHM ⟨[], ctors⟩ e τ)
    (hexh : SmallStep.AllMatchesExhaustive ctors e) :
    ∀ e', Relation.ReflTransGen SmallStep.Step e.erase e' →
      RuntimeTyping.RunWT ⟨[], ctors⟩ e' τ ∧
        (SmallStep.IsValue e' ∨ ∃ e'', SmallStep.Step e' e'') := by
  intro e' hrtc
  have H : RuntimeTyping.RunWT ⟨[], ctors⟩ e' τ ∧ e'.erase = e' ∧
      SmallStep.AllMatchesExhaustive ctors e' := by
    induction hrtc with
    | refl => exact ⟨hty.erase_preserves_typing, e.erase_idem, hexh.erase⟩
    | tail _ hstep ih =>
        obtain ⟨htyped, herased', hexh'⟩ := ih
        exact ⟨RuntimeTyping.RunWT.preservation hstep htyped,
          SmallStep.Step.preserves_erased herased' hstep,
          SmallStep.Step.preserves_exhaustive hexh' hstep⟩
  exact ⟨H.1, RuntimeTyping.RunWT.progress H.1 rfl H.2.2 H.2.1⟩
