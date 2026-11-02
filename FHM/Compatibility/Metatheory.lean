import FHM.InferenceFoundations
import FHM.Compatibility.Erasure

/-! Only the historical complete-Core metatheory still used by the opt-in
compatibility clients lives here: induction, regularity and term weakening.
Canonical source typing and runtime safety do not depend on this module. -/

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

/-- Historical regularity follows from the annotation-free runtime derivation. -/
theorem TypeOfHM.regular {ctx : Ctx} {e : Expr} {τ : Ty}
    (h : TypeOfHM ctx e τ) : τ.IsLC :=
  h.erase_preserves_typing.regular

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
