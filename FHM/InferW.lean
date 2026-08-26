import FHM.Core

-- These pure `Ty`-level lemmas now live in `Core` (they were originally developed
-- here). Core declares them without `@[simp]`, but the InferW proofs below rely on
-- them firing as simp lemmas, so re-grant the attribute here.
attribute [simp] Ty.openVars_arrow Ty.openVars_customTy

/-! ## Scaffolding for the algorithmic phase

Not used yet. Once we move from the declarative relation to algorithmic
inference, `.fvar`s stop being abstract/rigid type variables and become
*unification variables*, each pointing at an entry in a unification context. -/

/-- Either a constrained (`conc`) or unconstrained (`unspec`) unification var. -/
inductive TyMaybe where
  | unspec
  | conc (ty : Ty)

/-- The unification-var context. Each `.fvar` references an item in this list. -/
abbrev FvarCtx := List TyMaybe


/-! ## Algorithmic phase, step 1: substitution algebra

The declarative `TypeOfElabHM` treats `.fvar`s as rigid/abstract type variables.
The algorithm reinterprets them as *unification variables* and solves equality
constraints between monotypes by computing a most-general unifier (MGU).

A unification substitution maps `.fvar` names to types. We reuse the proven
`Ty.substFvars` machinery: a substitution is a `List (Nat × Ty)` applied
left-to-right, so **composition is list append** (`Subst.onTy_append`). This
algebra is shared scaffolding needed by *any* algorithmic presentation
(Algorithm W / M / J or constraint-based) — all of them rest on unification. -/

/-- A unification substitution: maps `.fvar` names to types, applied
    left-to-right via `Ty.substFvars`. Composition of `S` then `T` is `S ++ T`. -/
abbrev Subst := List (Nat × Ty)

/-- Apply a substitution to a monotype. -/
def Subst.onTy (S : Subst) : Ty → Ty := Ty.substFvars S

/-- Apply a substitution to a scheme. `substFvars` only rewrites free vars, so
    the scheme's bound vars (`.bvar`s `< paramCount`) are left untouched. -/
def Subst.onPolyTy (S : Subst) (M : PolyTy) : PolyTy :=
  { paramCount := M.paramCount, body := S.onTy M.body }

/-- Apply a substitution to a value environment. -/
def Subst.onEnv (S : Subst) (env : Env) : Env := env.map S.onPolyTy

/-- Apply a substitution to a typing context. Constructors are closed
    (`Ctor.closed`), so only the value env is affected. -/
def Subst.onCtx (S : Subst) (ctx : Ctx) : Ctx :=
  { env := S.onEnv ctx.env, ctors := ctx.ctors }

/-- `substFvars` of an append applies the prefix first, then the suffix — the
    elementary fact making list-append the composition of substitutions. -/
theorem Ty.substFvars_append (S T : Subst) (τ : Ty) :
    Ty.substFvars (S ++ T) τ = Ty.substFvars T (Ty.substFvars S τ) := by
  induction S generalizing τ with
  | nil => rfl
  | cons hd tl ih =>
    obtain ⟨Z, U⟩ := hd
    simp only [List.cons_append, Ty.substFvars]
    exact ih (Ty.substFvar Z U τ)

/-- Composition of substitutions is concatenation: `(S ++ T)` applies `S` first,
    then `T`. -/
theorem Subst.onTy_append (S T : Subst) (τ : Ty) :
    (S ++ T).onTy τ = T.onTy (S.onTy τ) := by
  simp only [Subst.onTy, Ty.substFvars_append]

@[simp] theorem Subst.onPolyTy_nil (M : PolyTy) : Subst.onPolyTy [] M = M := rfl

@[simp] theorem Subst.onEnv_nil (env : Env) : Subst.onEnv [] env = env := by
  show env.map (Subst.onPolyTy []) = env
  rw [show (Subst.onPolyTy [] : PolyTy → PolyTy) = id from funext Subst.onPolyTy_nil]
  exact List.map_id env

@[simp] theorem Subst.onCtx_nil (ctx : Ctx) : Subst.onCtx [] ctx = ctx := by
  simp only [Subst.onCtx, Subst.onEnv_nil]

theorem Subst.onPolyTy_append (S T : Subst) (M : PolyTy) :
    (S ++ T).onPolyTy M = T.onPolyTy (S.onPolyTy M) := by
  simp only [Subst.onPolyTy, Subst.onTy_append]

theorem Subst.onEnv_append (S T : Subst) (env : Env) :
    (S ++ T).onEnv env = T.onEnv (S.onEnv env) := by
  simp only [Subst.onEnv, List.map_map]
  apply List.map_congr_left
  intro M _
  exact Subst.onPolyTy_append S T M

theorem Subst.onCtx_append (S T : Subst) (ctx : Ctx) :
    (S ++ T).onCtx ctx = T.onCtx (S.onCtx ctx) := by
  simp only [Subst.onCtx, Subst.onEnv_append]


/-- A type-fvar substitution whose keys avoid a term's annotation free vars
    leaves the term fixed (collapse of `Expr.substTyFvars` to a no-op). -/
theorem Expr.substTyFvars_eq_self_of_tyFreeVars_nil {e : Expr} (S : Subst)
    (h : e.tyFreeVars = []) : e.substTyFvars S = e := by
  apply Expr.substTyFvars_eq_self_of_not_mem_tyFreeVars
  intro p _
  simp [h]

/-! ### Path R residual helpers (erase-normal TypeOf bridge)

**Path R (locked):** pure `TypeOf*` is structural HM (structural `Option.Pins`).
Infer is bounds-blind. Soundness bridges via projection:

```
TypeOf* (S.onCtx ctx).eraseBounds  (e.eraseBounds)  (Ty.eraseBounds τ)
```

`Env.eraseBounds` / `Ctx.eraseBounds` / `Expr.eraseBounds` live in Core.
Pipeline Infer never mutates anns through erase — residual theorems only.
-/

theorem InstantiatesBy.eraseBounds {tyArgs : List Ty} {τ τ' : Ty}
    (h : InstantiatesBy tyArgs τ τ') :
    InstantiatesBy (tyArgs.map Ty.eraseBounds) (Ty.eraseBounds τ) (Ty.eraseBounds τ') := by
  induction τ using Ty.rec_strong generalizing τ' with
  | prim _ =>
    cases h
    exact .prim
  | arrow a b iha ihb =>
    cases h with
    | arrow ha hb =>
      simp only [Ty.eraseBounds_arrow]
      exact .arrow (iha ha) (ihb hb)
  | bvar i =>
    cases h with
    | bvar hsome =>
      simp only [Ty.eraseBounds_bvar]
      apply InstantiatesBy.bvar
      rw [List.getElem?_map, hsome]
      rfl
  | fvar n =>
    cases h with
    | fvar =>
      simp only [Ty.eraseBounds_fvar]
      exact .fvar
  | customTy nm tys ih =>
    cases h with
    | customTy hforall =>
      simp only [Ty.eraseBounds_customTy, TyList.eraseBounds_eq_map]
      apply InstantiatesBy.customTy
      induction hforall with
      | nil => exact .nil
      | cons hhd htl ihtl =>
        rename_i hd_ty hd_it tl_tys tl_it
        refine .cons (ih hd_ty List.mem_cons_self hhd) ?_
        exact ihtl (fun t ht => ih t (List.mem_cons_of_mem _ ht))
  | bl lo hi e ih =>
    cases h with
    | bl he =>
      simp only [Ty.eraseBounds_bl, bareListTy]
      exact .customTy (.cons (ih he) .nil)

theorem InstantiatesBy.forall2_eraseBounds {tyArgs ts us : List Ty}
    (h : List.Forall₂ (InstantiatesBy tyArgs) ts us) :
    List.Forall₂ (InstantiatesBy (tyArgs.map Ty.eraseBounds))
      (ts.map Ty.eraseBounds) (us.map Ty.eraseBounds) := by
  induction h with
  | nil => exact .nil
  | cons hhd _ ih => exact .cons (InstantiatesBy.eraseBounds hhd) ih

/-- Erase is the identity on every fvar (and thus on any list of pure fvars). -/
theorem Ty.eraseBounds_eq_self_of_fvar : ∀ {t : Ty}, (∃ n, t = .fvar n) → Ty.eraseBounds t = t
  | .fvar _, ⟨_, rfl⟩ => rfl

theorem List.map_eraseBounds_eq_self_of_fvars (tyArgs : List Ty)
    (h : ∀ t ∈ tyArgs, ∃ n, t = .fvar n) :
    tyArgs.map Ty.eraseBounds = tyArgs := by
  induction tyArgs with
  | nil => rfl
  | cons hd tl ih =>
    simp only [List.map_cons, List.cons.injEq]
    exact ⟨Ty.eraseBounds_eq_self_of_fvar (h hd List.mem_cons_self),
      ih fun t ht => h t (List.mem_cons_of_mem _ ht)⟩

/-- `map f xs = xs` when `f` is id on every element (induction; no mathlib lemma). -/
theorem List.map_eq_self_of_forall_eq_id {α : Type _} (f : α → α) :
    ∀ (xs : List α), (∀ x ∈ xs, f x = x) → xs.map f = xs
  | [], _ => rfl
  | x :: xs, h => by
    simp only [List.map_cons, List.cons.injEq]
    exact ⟨h x List.mem_cons_self, List.map_eq_self_of_forall_eq_id f xs
      (fun y hy => h y (List.mem_cons_of_mem _ hy))⟩

/-- When tyArgs are erase-fixed (e.g. fresh fvars from `Infer.var`), residual
    InstantiatesBy keeps the **same** tyArgs. -/
theorem InstantiatesBy.eraseBounds_eraseFixedTyArgs {tyArgs : List Ty} {τ τ' : Ty}
    (h : InstantiatesBy tyArgs τ τ')
    (hfix : ∀ t ∈ tyArgs, Ty.eraseBounds t = t) :
    InstantiatesBy tyArgs (Ty.eraseBounds τ) (Ty.eraseBounds τ') := by
  have hmap : tyArgs.map Ty.eraseBounds = tyArgs :=
    List.map_eq_self_of_forall_eq_id Ty.eraseBounds tyArgs hfix
  have h' := InstantiatesBy.eraseBounds h
  rwa [hmap] at h'

/-- Structural pin lifts through mapping the annotation and the pinned type by erase. -/
theorem Option.Pins.map_eraseBounds {ann : Option Ty} {τ : Ty}
    (h : ann.Pins τ) : (ann.map Ty.eraseBounds).Pins (Ty.eraseBounds τ) := by
  intro a ha
  cases ann with
  | none => simp at ha
  | some a₀ =>
    simp only [Option.map_some, Option.some.injEq] at ha
    subst ha
    rw [h a₀ rfl]

/-- Scheme form of `Option.Pins.map_eraseBounds`. -/
theorem Option.Pins.map_eraseBounds_poly {ann : Option PolyTy} {σ : PolyTy}
    (h : ann.Pins σ) :
    (ann.map PolyTy.eraseBounds).Pins (PolyTy.eraseBounds σ) := by
  intro a ha
  cases ann with
  | none => simp at ha
  | some a₀ =>
    simp only [Option.map_some, Option.some.injEq] at ha
    subst ha
    rw [h a₀ rfl]

/-- `eraseBounds` commutes with `openVars`: opening only injects fvars/bvars,
    both fixed by erase. Used by `TypeOfElabHM.eraseBounds_of` (`letIn`/`letRec`). -/
theorem Ty.eraseBounds_openVars (Xs : List Nat) (τ : Ty) :
    Ty.eraseBounds (Ty.openVars Xs τ) = Ty.openVars Xs (Ty.eraseBounds τ) := by
  unfold Ty.openVars
  induction τ using Ty.rec_strong with
  | prim _ => rfl
  | arrow a b iha ihb =>
    simp only [Ty.instantiate, Ty.eraseBounds_arrow, iha, ihb]
  | bvar i =>
    simp only [Ty.instantiate, Ty.eraseBounds_bvar]
    cases Xs[i]? with
    | none => rfl
    | some _ => rfl
  | fvar n => rfl
  | customTy nm tys ih =>
    simp only [Ty.instantiate, Ty.eraseBounds_customTy, TyList.eraseBounds_eq_map,
      TyList.instantiate_eq_map, List.map_map]
    congr 1
    refine List.map_congr_left fun t ht => ih t ht
  | bl lo hi e ih =>
    -- both sides: bareListTy (instantiate … (erase e)) via erase∘instantiate = instantiate∘erase
    simp only [Ty.instantiate, Ty.eraseBounds_bl, bareListTy, TyList.instantiate, ih]

@[simp] theorem PolyTy.eraseBounds_openVars (Xs : List Nat) (M : PolyTy) :
    Ty.eraseBounds (M.openVars Xs) = (PolyTy.eraseBounds M).openVars Xs := by
  simp only [PolyTy.openVars, PolyTy.eraseBounds, Ty.eraseBounds_openVars]

/-- `eraseBounds` commutes with `openWith`: instantiate against erased args of an erased template. -/
theorem Ty.eraseBounds_openWith (Vs : List Ty) (τ : Ty) :
    Ty.eraseBounds (Ty.openWith Vs τ) =
      Ty.openWith (Vs.map Ty.eraseBounds) (Ty.eraseBounds τ) := by
  unfold Ty.openWith
  induction τ using Ty.rec_strong with
  | prim _ => rfl
  | arrow a b iha ihb =>
    simp only [Ty.instantiate, Ty.eraseBounds_arrow, iha, ihb]
  | bvar i =>
    simp only [Ty.instantiate, Ty.eraseBounds_bvar]
    cases h : Vs[i]? with
    | none =>
      have : (Vs.map Ty.eraseBounds)[i]? = none := by
        simpa [List.getElem?_map] using congrArg (Option.map Ty.eraseBounds) h
      simp only [this, Option.getD_none, Ty.eraseBounds_bvar]
    | some v =>
      have : (Vs.map Ty.eraseBounds)[i]? = some (Ty.eraseBounds v) := by
        simpa [List.getElem?_map] using congrArg (Option.map Ty.eraseBounds) h
      simp only [this, Option.getD_some]
  | fvar n => rfl
  | customTy nm tys ih =>
    simp only [Ty.instantiate, Ty.eraseBounds_customTy, TyList.eraseBounds_eq_map,
      TyList.instantiate_eq_map, List.map_map]
    congr 1
    refine List.map_congr_left fun t ht => ih t ht
  | bl lo hi e ih =>
    simp only [Ty.instantiate, Ty.eraseBounds_bl, bareListTy, TyList.instantiate, ih]

/-- List form of `eraseBounds_substFvar` (Core has the single-step form). -/
theorem Ty.eraseBounds_substFvars (pairs : List (Nat × Ty)) (τ : Ty) :
    Ty.eraseBounds (Ty.substFvars pairs τ) =
      Ty.substFvars (pairs.map fun p => (p.1, Ty.eraseBounds p.2)) (Ty.eraseBounds τ) := by
  induction pairs generalizing τ with
  | nil => rfl
  | cons hd tl ih =>
    obtain ⟨Z, U⟩ := hd
    simp only [Ty.substFvars, List.map_cons, Ty.eraseBounds_substFvar, ih]

private theorem List.map_eraseBounds_zip_fvar (G Xs : List Nat) :
    (G.zip (Xs.map Ty.fvar)).map (fun p => (p.1, Ty.eraseBounds p.2)) =
      G.zip (Xs.map Ty.fvar) := by
  induction G generalizing Xs with
  | nil => rfl
  | cons g gs ih =>
    cases Xs with
    | nil => rfl
    | cons x xs =>
      simp only [List.map_cons, List.zip_cons_cons, Ty.eraseBounds_fvar, ih]

/-- `eraseBounds` of `renameG` is `renameG` of `eraseBounds` (pool renames substitute
    fvars, which are fixed by erase). -/
theorem Ty.eraseBounds_renameG (G Xs : List Nat) (τ : Ty) :
    Ty.eraseBounds (Ty.renameG G Xs τ) = Ty.renameG G Xs (Ty.eraseBounds τ) := by
  unfold Ty.renameG
  rw [Ty.eraseBounds_substFvars, List.map_eraseBounds_zip_fvar]

/-- Membership in `freeVars` is invariant under `eraseBounds` (list intervals
    contribute no fvars; `dedup` on the bare-List form does not change ∈). -/
theorem Ty.mem_freeVars_eraseBounds (τ : Ty) (x : Nat) :
    x ∈ (Ty.eraseBounds τ).freeVars ↔ x ∈ τ.freeVars := by
  induction τ using Ty.rec_strong with
  | prim _ => simp [Ty.freeVars]
  | arrow a b iha ihb =>
    simp only [Ty.eraseBounds_arrow, Ty.freeVars, List.mem_dedup, List.mem_append, iha, ihb]
  | bvar i => simp [Ty.freeVars]
  | fvar n => simp [Ty.freeVars]
  | customTy nm tys ih =>
    simp only [Ty.eraseBounds_customTy, TyList.eraseBounds_eq_map, Ty.freeVars]
    -- ∈ TyList.freeVars (map erase tys) ↔ ∈ TyList.freeVars tys
    induction tys with
    | nil => simp [TyList.freeVars]
    | cons hd tl ihtl =>
      simp only [List.map_cons, TyList.freeVars, List.mem_dedup, List.mem_append]
      rw [ih hd List.mem_cons_self, ihtl (fun t ht => ih t (List.mem_cons_of_mem _ ht))]
  | bl lo hi e ih =>
    simp only [Ty.eraseBounds_bl, bareListTy, Ty.freeVars, TyList.freeVars, List.append_nil,
      List.mem_dedup, ih]

/-- Membership in env freeVars is invariant under pointwise `eraseBounds` on schemes. -/
theorem Env.mem_freeVars_eraseBounds (env : Env) (x : Nat) :
    x ∈ (Env.eraseBounds env).freeVars ↔ x ∈ env.freeVars := by
  induction env with
  | nil => simp [Env.freeVars, Env.eraseBounds]
  | cons hd tl ih =>
    simp only [Env.eraseBounds_cons, Env.freeVars, List.mem_dedup, List.mem_append,
      PolyTy.eraseBounds, Ty.mem_freeVars_eraseBounds, ih]

private theorem Expr.mem_tyFreeVars_BranchList_eraseBounds
    (branches : List (MatchPattern × Expr)) (x : Nat)
    (ih : ∀ p b, (p, b) ∈ branches → (x ∈ b.eraseBounds.tyFreeVars ↔ x ∈ b.tyFreeVars)) :
    x ∈ Expr.tyFreeVars.BranchList.tyFreeVars (branches.map fun pe => (pe.1, pe.2.eraseBounds)) ↔
      x ∈ Expr.tyFreeVars.BranchList.tyFreeVars branches := by
  induction branches with
  | nil => simp [Expr.tyFreeVars.BranchList.tyFreeVars]
  | cons hd tl ihtl =>
    obtain ⟨p, b⟩ := hd
    have hb := ih p b List.mem_cons_self
    have htl := ihtl (fun p' b' hm => ih p' b' (List.mem_cons_of_mem _ hm))
    simp only [List.map_cons, Expr.tyFreeVars.BranchList.tyFreeVars, List.mem_append, hb, htl]

private theorem Expr.mem_tyFreeVars_RecGroup_eraseBounds
    (bindings : List Expr) (x : Nat)
    (ih : ∀ e, e ∈ bindings → (x ∈ e.eraseBounds.tyFreeVars ↔ x ∈ e.tyFreeVars)) :
    x ∈ Expr.tyFreeVars.RecGroup.tyFreeVars (bindings.map Expr.eraseBounds) ↔
      x ∈ Expr.tyFreeVars.RecGroup.tyFreeVars bindings := by
  induction bindings with
  | nil => simp [Expr.tyFreeVars.RecGroup.tyFreeVars]
  | cons hd tl ihtl =>
    have hhd := ih hd List.mem_cons_self
    have htl := ihtl (fun e' he' => ih e' (List.mem_cons_of_mem _ he'))
    simp only [List.map_cons, Expr.tyFreeVars.RecGroup.tyFreeVars, List.mem_append, hhd, htl]

private theorem Expr.mem_tyFreeVars_AnnList_eraseBounds
    (anns : List (Option PolyTy)) (x : Nat) :
    x ∈ Expr.tyFreeVars.AnnList.tyFreeVars (anns.map (Option.map PolyTy.eraseBounds)) ↔
      x ∈ Expr.tyFreeVars.AnnList.tyFreeVars anns := by
  induction anns with
  | nil => simp [Expr.tyFreeVars.AnnList.tyFreeVars]
  | cons a as iha =>
    cases a with
    | none =>
      simp only [List.map_cons, Option.map_none, Expr.tyFreeVars.AnnList.tyFreeVars,
        Option.elim_none, List.nil_append, iha]
    | some _σ =>
      simp only [List.map_cons, Option.map_some, Expr.tyFreeVars.AnnList.tyFreeVars,
        Option.elim_some, List.mem_append, PolyTy.eraseBounds, Ty.mem_freeVars_eraseBounds, iha]

/-- Annotation free type vars are invariant under `Expr.eraseBounds`. -/
theorem Expr.mem_tyFreeVars_eraseBounds (e : Expr) (x : Nat) :
    x ∈ e.eraseBounds.tyFreeVars ↔ x ∈ e.tyFreeVars := by
  induction e using Expr.rec_strong with
  | primLit _ | primBinOp _ | ctor _ => simp [Expr.eraseBounds, Expr.tyFreeVars]
  | var _i => simp [Expr.eraseBounds, Expr.tyFreeVars]
  | lambda ann body ih =>
    cases ann with
    | none =>
      simp only [Expr.eraseBounds, Expr.tyFreeVars, Option.map_none, Option.elim_none,
        List.nil_append, ih]
    | some _T =>
      simp only [Expr.eraseBounds, Expr.tyFreeVars, Option.map_some, Option.elim_some,
        List.mem_append, Ty.mem_freeVars_eraseBounds, ih]
  | app _f _arg ihf iha =>
    simp only [Expr.eraseBounds, Expr.tyFreeVars, List.mem_append, ihf, iha]
  | letIn ann _rhs _body ihr ihb =>
    cases ann with
    | none =>
      simp only [Expr.eraseBounds, Expr.tyFreeVars, Option.map_none, Option.elim_none,
        List.nil_append, List.mem_append, ihr, ihb]
    | some _σ =>
      simp only [Expr.eraseBounds, Expr.tyFreeVars, Option.map_some, Option.elim_some,
        List.mem_append, PolyTy.eraseBounds, Ty.mem_freeVars_eraseBounds, ihr, ihb]
  | match_ _scrut branches ihs ihbs =>
    simp only [Expr.eraseBounds, Expr.tyFreeVars, List.mem_append, ihs]
    exact or_congr_right (Expr.mem_tyFreeVars_BranchList_eraseBounds branches x ihbs)
  | letRec anns bindings _body ihbs ihb =>
    simp only [Expr.eraseBounds, Expr.tyFreeVars, List.mem_append, ihb]
    rw [Expr.mem_tyFreeVars_AnnList_eraseBounds,
      Expr.mem_tyFreeVars_RecGroup_eraseBounds bindings x ihbs]

theorem Ty.genFilter_eraseBounds (G : List Nat) (τ : Ty) :
    Ty.genFilter G (Ty.eraseBounds τ) = Ty.genFilter G τ := by
  simp only [Ty.genFilter]
  refine List.filter_congr fun x _ => by
    simp only [Ty.mem_freeVars_eraseBounds]

private theorem TyList.closeOver_eq_map' (gs : List Nat) (tys : List Ty) :
    TyList.closeOver gs tys = tys.map (Ty.closeOver gs) := by
  induction tys with
  | nil => rfl
  | cons hd tl ih => simp [TyList.closeOver, ih]

/-- `closeOver` only rewrites fvars→bvars; commutes with erase. -/
theorem Ty.eraseBounds_closeOver (gs : List Nat) (τ : Ty) :
    Ty.eraseBounds (Ty.closeOver gs τ) = Ty.closeOver gs (Ty.eraseBounds τ) := by
  induction τ using Ty.rec_strong with
  | prim _ => rfl
  | arrow a b iha ihb =>
    simp only [Ty.closeOver, Ty.eraseBounds_arrow, iha, ihb]
  | bvar i => rfl
  | fvar n =>
    simp only [Ty.closeOver, Ty.eraseBounds_fvar]
    cases gs.idxOf? n with
    | none => rfl
    | some _ => rfl
  | customTy nm tys ih =>
    simp only [Ty.closeOver, Ty.eraseBounds_customTy, TyList.eraseBounds_eq_map,
      TyList.closeOver_eq_map', List.map_map]
    congr 1
    exact List.map_congr_left fun t ht => ih t ht
  | bl lo hi e ih =>
    simp only [Ty.closeOver, Ty.eraseBounds_bl, bareListTy, TyList.closeOver, ih]

theorem PolyTy.eraseBounds_genGroup (G : List Nat) (τ : Ty) :
    PolyTy.eraseBounds (PolyTy.genGroup G τ) = PolyTy.genGroup G (Ty.eraseBounds τ) := by
  simp only [PolyTy.genGroup, PolyTy.eraseBounds, Ty.genFilter_eraseBounds,
    Ty.eraseBounds_closeOver]

/-- Pointwise erase of a recursion-group spec (mono body / poly scheme). -/
def RecSpec.eraseBounds : RecSpec → RecSpec
  | .mono τ => .mono (Ty.eraseBounds τ)
  | .poly σ => .poly (PolyTy.eraseBounds σ)

theorem RecSpec.eraseBounds_rhsEntry (G Xs : List Nat) (s : RecSpec) :
    PolyTy.eraseBounds (RecSpec.rhsEntry G Xs s) =
      RecSpec.rhsEntry G Xs (RecSpec.eraseBounds s) := by
  cases s with
  | mono τ =>
    simp only [RecSpec.rhsEntry, RecSpec.eraseBounds, PolyTy.eraseBounds_mkTrivial,
      Ty.eraseBounds_renameG]
  | poly σ =>
    rfl

theorem RecSpec.eraseBounds_bodyScheme (G : List Nat) (s : RecSpec) :
    PolyTy.eraseBounds (RecSpec.bodyScheme G s) =
      RecSpec.bodyScheme G (RecSpec.eraseBounds s) := by
  cases s with
  | mono τ =>
    simp only [RecSpec.bodyScheme, RecSpec.eraseBounds, PolyTy.eraseBounds_genGroup]
  | poly σ =>
    rfl

/-- Annotation projection of a recursion-group spec under `eraseBounds`. -/
theorem RecSpec.ann_eraseBounds (s : RecSpec) :
    RecSpec.ann (RecSpec.eraseBounds s) =
      (RecSpec.ann s).map PolyTy.eraseBounds := by
  cases s <;> rfl

theorem Ty.AreLC.eraseBounds {n : Nat} {Vs : List Ty} (h : Ty.AreLC n Vs) :
    Ty.AreLC n (Vs.map Ty.eraseBounds) :=
  ⟨by simpa using h.1, fun V hmem => by
    obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hmem
    exact Ty.IsLC.eraseBounds (h.2 t ht)⟩

theorem Ty.eraseBounds_wrapArrows (result : Ty) (args : List Ty) :
    Ty.eraseBounds (Ty.wrapArrows result args) =
      Ty.wrapArrows (Ty.eraseBounds result) (args.map Ty.eraseBounds) := by
  induction args generalizing result with
  | nil => rfl
  | cons a as ih =>
    simp only [Ty.wrapArrows, Ty.eraseBounds_arrow, List.map_cons, ih]

private theorem Ty.map_eraseBounds_bvarRangeFrom' :
    ∀ (s k : Nat), (Ty.bvarRangeFrom s k).map Ty.eraseBounds = Ty.bvarRangeFrom s k
  | _, 0 => rfl
  | s, k + 1 => by
    simp only [Ty.bvarRangeFrom, List.map_cons, Ty.eraseBounds_bvar,
      Ty.map_eraseBounds_bvarRangeFrom' (s + 1) k]

private theorem Ty.map_eraseBounds_bvarRange' (k : Nat) :
    (Ty.bvarRange k).map Ty.eraseBounds = Ty.bvarRange k :=
  Ty.map_eraseBounds_bvarRangeFrom' 0 k

/-- Erasing ctor fields projects through `Ctor.toTy` (wrapArrows + bvarRange). -/
theorem Ctor.eraseBounds_toTy (c : Ctor) :
    (Ctor.eraseBounds c).toTy = PolyTy.eraseBounds c.toTy := by
  cases c with | mk pc tn contents _ _ =>
  change
    ({ paramCount := pc,
       body := Ty.wrapArrows (.customTy tn (Ty.bvarRange pc))
         (contents.map Ty.eraseBounds) } : PolyTy) =
    { paramCount := pc,
      body := Ty.eraseBounds
        (Ty.wrapArrows (.customTy tn (Ty.bvarRange pc)) contents) }
  simp only [Ty.eraseBounds_wrapArrows, Ty.eraseBounds_customTy, TyList.eraseBounds_eq_map,
    Ty.map_eraseBounds_bvarRange']

theorem Env.eraseBounds_append (env₁ env₂ : Env) :
    Env.eraseBounds (env₁ ++ env₂) =
      Env.eraseBounds env₁ ++ Env.eraseBounds env₂ := by
  simp only [Env.eraseBounds, List.map_append]

theorem Env.eraseBounds_map_mkTrivial (ts : List Ty) :
    Env.eraseBounds (ts.map PolyTy.mkTrivial) =
      (ts.map Ty.eraseBounds).map PolyTy.mkTrivial := by
  simp only [Env.eraseBounds, List.map_map, Function.comp_def, PolyTy.eraseBounds_mkTrivial]

theorem RecSpecs.rhsCtx_eraseBounds (ctx : Ctx) (specs : List RecSpec) (G Xs : List Nat) :
    (RecSpecs.rhsCtx ctx specs G Xs).eraseBounds =
      RecSpecs.rhsCtx ctx.eraseBounds (specs.map RecSpec.eraseBounds) G Xs := by
  simp only [RecSpecs.rhsCtx, Ctx.eraseBounds, Env.eraseBounds, List.map_append, List.map_map]
  refine congrArg₂ Ctx.mk ?_ rfl
  refine congrArg₂ List.append ?_ rfl
  exact List.map_congr_left fun s _ => RecSpec.eraseBounds_rhsEntry G Xs s

theorem RecSpecs.bodyCtx_eraseBounds (ctx : Ctx) (specs : List RecSpec) (G : List Nat) :
    (RecSpecs.bodyCtx ctx specs G).eraseBounds =
      RecSpecs.bodyCtx ctx.eraseBounds (specs.map RecSpec.eraseBounds) G := by
  simp only [RecSpecs.bodyCtx, Ctx.eraseBounds, Env.eraseBounds, List.map_append, List.map_map]
  refine congrArg₂ Ctx.mk ?_ rfl
  refine congrArg₂ List.append ?_ rfl
  exact List.map_congr_left fun s _ => RecSpec.eraseBounds_bodyScheme G s

theorem RecSpecs.WF.eraseBounds {anns : List (Option PolyTy)} {bindings : List Expr}
    {specs : List RecSpec} {G : List Nat} (hwf : RecSpecs.WF anns bindings specs G) :
    RecSpecs.WF (anns.map (Option.map PolyTy.eraseBounds))
      (bindings.map Expr.eraseBounds) (specs.map RecSpec.eraseBounds) G where
  anns_eq := by
    rw [List.map_map, ← hwf.anns_eq, List.map_map]
    exact List.map_congr_left fun s _ => RecSpec.ann_eraseBounds s
  length := by simpa [List.length_map] using hwf.length
  nodup := hwf.nodup
  mono_lc := by
    intro τ hτ
    obtain ⟨s, hs, heq⟩ := List.mem_map.mp hτ
    cases s with
    | mono τ₀ =>
      injection heq with hττ
      rw [← hττ]
      exact Ty.IsLC.eraseBounds (hwf.mono_lc τ₀ hs)
    | poly _ => exact RecSpec.noConfusion heq
  poly_wf := by
    intro σ hσ
    obtain ⟨s, hs, heq⟩ := List.mem_map.mp hσ
    cases s with
    | mono _ => exact RecSpec.noConfusion heq
    | poly σ₀ =>
      injection heq with hσσ
      rw [← hσσ]
      exact PolyTy.WF.eraseBounds (hwf.poly_wf σ₀ hs)
/-- Membership of an erased pair in a pointwise-erased zip. -/
private theorem List.mem_zip_map_eraseBounds
    {bindings : List Expr} {specs : List RecSpec} {p : Expr × RecSpec}
    (hp : p ∈ (bindings.map Expr.eraseBounds).zip (specs.map RecSpec.eraseBounds)) :
    ∃ e s, (e, s) ∈ bindings.zip specs ∧
      p = (e.eraseBounds, RecSpec.eraseBounds s) := by
  induction bindings generalizing specs with
  | nil =>
    cases specs <;> simp at hp
  | cons e es ih =>
    cases specs with
    | nil => simp at hp
    | cons s ss =>
      simp only [List.map_cons, List.zip_cons_cons, List.mem_cons] at hp
      cases hp with
      | inl heq => exact ⟨e, s, List.mem_cons_self, heq⟩
      | inr h' =>
        obtain ⟨e', s', hmem, heq⟩ := ih h'
        exact ⟨e', s', List.mem_cons_of_mem _ hmem, heq⟩

theorem Ty.instantiate_eq_self_of_bvars_lt {σ : Nat → Ty} {d : Nat} {t : Ty}
    (hσ : ∀ i, i < d → σ i = .bvar i) (h : ContainsBvarsUpTo d t) :
    Ty.instantiate σ t = t := by
  induction t using Ty.rec_strong with
  | prim _ => rfl
  | arrow a b iha ihb =>
    cases h with
    | arrow ha hb => simp only [Ty.instantiate, Ty.arrow.injEq]; exact ⟨iha ha, ihb hb⟩
  | bvar i => cases h with | bvar hlt => exact hσ i hlt
  | fvar n => rfl
  | customTy nm tys ih =>
    cases h with
    | customTy hall =>
      simp only [Ty.instantiate, Ty.customTy.injEq, true_and]
      induction tys with
      | nil => rfl
      | cons hd tl ihtl =>
        simp only [TyList.instantiate, List.cons.injEq]
        exact ⟨ih hd List.mem_cons_self (hall hd List.mem_cons_self),
               ihtl (fun t ht => ih t (List.mem_cons_of_mem _ ht))
                    (fun t ht => hall t (List.mem_cons_of_mem _ ht))⟩
  | bl lo hi e ih =>
    cases h with
    | bl he => simp only [Ty.instantiate, Ty.bl.injEq, true_and]; exact ih he

/-- Offset opening (`Ty.openVarsFrom d`) fixes any type whose bvars are all `< d`
    — the opener only touches bvars `≥ d`. Used by the `openTyVars`-identity
    invariant (annotation bvars stay within their own scheme's arity). -/
theorem Ty.openVarsFrom_eq_self_of_containsBvars {d : Nat} {Xs : List Nat} {t : Ty}
    (h : ContainsBvarsUpTo d t) : Ty.openVarsFrom d Xs t = t := by
  unfold Ty.openVarsFrom
  exact Ty.instantiate_eq_self_of_bvars_lt (fun _ hi => if_pos hi) h


/-! ### Most-general unifier specification

`Unifies S τ₁ τ₂` says `S` equates the two monotypes; `IsMGU S τ₁ τ₂` adds that
*every* unifier factors through `S` (`S` is the least committal one). Because
composition is `++` and `(S ++ R).onTy τ = R.onTy (S.onTy τ)`, "`S'` factors
through `S`" means `∃ R, S' acts as (S then R)`.

The occurs check needs no new notion: `.fvar Z` occurs in `τ` exactly when
`Z ∈ τ.freeVars`. -/

/-! ### Option A (locked): bounds-blind HM equality

Chunk 0: definitions + compile scaffold. Residual/TypeOf sites still need
structural images in places — those use `optionA_residual_eq` (grep
`OptionA residual`) until later chunks rewrite them to `FactorsHM`/`AgreesHM`.
-/

/-- HM monotypes agree when they match after dropping list intervals.
`BL lo hi α` and bare `List α` (any lo/hi) are the same HM shape. -/
def AgreesHM (τ₁ τ₂ : Ty) : Prop :=
  Ty.eraseBounds τ₁ = Ty.eraseBounds τ₂

namespace AgreesHM

theorem refl (τ : Ty) : AgreesHM τ τ := rfl

theorem symm {τ₁ τ₂ : Ty} (h : AgreesHM τ₁ τ₂) : AgreesHM τ₂ τ₁ :=
  Eq.symm h

theorem trans {τ₁ τ₂ τ₃ : Ty} (h₁₂ : AgreesHM τ₁ τ₂) (h₂₃ : AgreesHM τ₂ τ₃) :
    AgreesHM τ₁ τ₃ :=
  Eq.trans h₁₂ h₂₃

end AgreesHM

/-- `S` makes `τ₁` and `τ₂` equal **up to list intervals** (official unifier judgment).

Lengths are never solved by the unifier; they stay on ascriptions for the bounds
pass. There is **no** valid implication `Unifies → structural tree equality`
(counterexample: `BL …` vs bare `List`). -/
def Unifies (S : Subst) (τ₁ τ₂ : Ty) : Prop :=
  AgreesHM (S.onTy τ₁) (S.onTy τ₂)

/-- Residual factoring up to HM shape (Option A target for MGU.greatest).
`S'·τ` and `R·(S·τ)` agree after `eraseBounds`, for every τ. -/
def FactorsHM (S' S : Subst) (R : Subst) : Prop :=
  ∀ τ, AgreesHM (S'.onTy τ) (R.onTy (S.onTy τ))

namespace FactorsHM

theorem of_structural {S' S R : Subst}
    (h : ∀ τ, S'.onTy τ = R.onTy (S.onTy τ)) : FactorsHM S' S R :=
  fun τ => congrArg Ty.eraseBounds (h τ)

-- Path R: `FactorsHM.to_structural` is FALSE (only erase-equality). Deleted; do not reintroduce.

end FactorsHM

/-- `S` is a most-general unifier of `τ₁` and `τ₂` (bounds-blind).
Residual factoring is `FactorsHM` (eraseBounds), not structural tree equality. -/
structure IsMGU (S : Subst) (τ₁ τ₂ : Ty) : Prop where
  unifies : Unifies S τ₁ τ₂
  greatest : ∀ S', Unifies S' τ₁ τ₂ → ∃ R : Subst, FactorsHM S' S R

/-- Structural equality of images implies bounds-blind unifiability. -/
theorem Unifies.of_eq {S : Subst} {τ₁ τ₂ : Ty}
    (h : S.onTy τ₁ = S.onTy τ₂) : Unifies S τ₁ τ₂ :=
  congrArg Ty.eraseBounds h

/-- Unfold. -/
theorem Unifies.iff_agreesHM {S : Subst} {τ₁ τ₂ : Ty} :
    Unifies S τ₁ τ₂ ↔ AgreesHM (S.onTy τ₁) (S.onTy τ₂) :=
  Iff.rfl

/-! ### The unification relation
(Option A: no structural recovery from bounds-blind `Unifies` — soundness is erase-normal.)


`UnifyRel τ₁ τ₂ S` is the *graph of unification on success*: it holds when the
two monotypes unify and `S` is a resulting most-general unifier. Failure is the
*absence* of a derivation (constructor clash, arity clash, or occurs-check), so
no negative side-conditions are needed and there is no termination obligation —
this is the relation-first stage; a `unify` function comes later (stage 3).

Compound types thread the prefix substitution into the remaining sub-problems
(`UnifyRel (S₁.onTy b) (S₁.onTy d) S₂`), exactly as Algorithm W's unifier does.
The occurs check is the freshness premise `n ∉ τ.freeVars` on the var rules;
together with `substFvar_fresh` it is what makes `[(n, τ)]` an actual unifier. -/
mutual

inductive UnifyRel : Ty → Ty → Subst → Prop
  | prim {p} :
    UnifyRel (.prim p) (.prim p) []

  | fvarRefl {n} :
    UnifyRel (.fvar n) (.fvar n) []

  | fvarL {n τ} :
    τ ≠ .fvar n → -- are not the same or else `fvarRefl` applies
    n ∉ τ.freeVars → -- the occurs check: `n` doesn't occur in `τ`
    UnifyRel (.fvar n) τ [(n, τ)]

  | fvarR {n τ} :
    τ ≠ .fvar n → -- are not the same or else `fvarRefl` applies
    n ∉ τ.freeVars → -- the occurs check: `n` doesn't occur in `τ`
    UnifyRel τ (.fvar n) [(n, τ)]

  | arrow {a b c d S₁ S₂} :
    UnifyRel a c S₁ →
    UnifyRel (S₁.onTy b) (S₁.onTy d) S₂ →
    UnifyRel (.arrow a b) (.arrow c d) (S₁ ++ S₂)

  | customTy {nm tys₁ tys₂ S} :
    UnifyRelList tys₁ tys₂ S →
    UnifyRel (.customTy nm tys₁) (.customTy nm tys₂) S

  /-- Two BLs: unify elements only; `lo`/`hi` may differ (not HM structure). -/
  | bl {lo₁ hi₁ lo₂ hi₂ e₁ e₂ S} :
    UnifyRel e₁ e₂ S →
    UnifyRel (.bl lo₁ hi₁ e₁) (.bl lo₂ hi₂ e₂) S

  /-- `BL _ _ α` ~ bare `List α` (same shape for HM / match / ctor types). -/
  | blList {lo hi e α S} :
    UnifyRel e α S →
    UnifyRel (.bl lo hi e) (.customTy listTyName [α]) S

  | listBl {lo hi e α S} :
    UnifyRel α e S →
    UnifyRel (.customTy listTyName [α]) (.bl lo hi e) S

/-- Pairwise unification of equal-length type lists, threading the substitution
    left-to-right. Used for the arguments of a custom type constructor. -/
inductive UnifyRelList : List Ty → List Ty → Subst → Prop
  | nil :
    UnifyRelList [] [] []
  | cons {t₁ t₂ ts₁ ts₂ S₁ S₂} :
    UnifyRel t₁ t₂ S₁ →
    UnifyRelList (ts₁.map S₁.onTy) (ts₂.map S₁.onTy) S₂ →
    UnifyRelList (t₁ :: ts₁) (t₂ :: ts₂) (S₁ ++ S₂)

end


/-! ### `onTy` distributes over the type formers -/

@[simp] theorem Subst.onTy_nil {τ : Ty} : Subst.onTy [] τ = τ := rfl

@[simp] theorem Subst.onTy_prim {S : Subst} {p : PrimTy} :
    S.onTy (.prim p) = .prim p := Ty.substFvars_prim

@[simp] theorem Subst.onTy_bvar {S : Subst} {i : Nat} :
    S.onTy (.bvar i) = .bvar i := Ty.substFvars_bvar

@[simp] theorem Subst.onTy_arrow {S : Subst} {a b : Ty} :
    S.onTy (.arrow a b) = .arrow (S.onTy a) (S.onTy b) := Ty.substFvars_arrow

@[simp] theorem Subst.onTy_customTy {S : Subst} {nm : TyName} {tys : List Ty} :
    S.onTy (.customTy nm tys) = .customTy nm (tys.map S.onTy) := Ty.substFvars_customTy

@[simp] theorem Subst.onTy_bl {S : Subst} {lo hi : FHM.Bounds.CountSlot} {e : Ty} :
    S.onTy (.bl lo hi e) = .bl lo hi (S.onTy e) := Ty.substFvars_bl

/-- Mapping a composed substitution over a list = mapping each factor in turn. -/
theorem Subst.map_onTy_append (S T : Subst) (ts : List Ty) :
    ts.map (S ++ T).onTy = (ts.map S.onTy).map T.onTy := by
  rw [List.map_map]
  apply List.map_congr_left
  intro x _
  exact Subst.onTy_append S T x

/-- `erase` after `onTy` ignores BL already present in the type: substituting
    into `τ` then erasing equals substituting into `erase τ` then erasing.
    (Images of `S` may still contain BL; the outer erase cleans those too.) -/
theorem Ty.eraseBounds_onTy_erase (S : Subst) (t : Ty) :
    Ty.eraseBounds (S.onTy (Ty.eraseBounds t)) = Ty.eraseBounds (S.onTy t) := by
  induction t using Ty.rec_strong with
  | prim p => rfl
  | bvar i => rfl
  | fvar n => rfl
  | arrow a b iha ihb =>
    simp only [Subst.onTy_arrow, Ty.eraseBounds_arrow, iha, ihb]
  | customTy nm tys ih =>
    simp only [Subst.onTy_customTy, Ty.eraseBounds_customTy, TyList.eraseBounds_eq_map,
      List.map_map]
    refine congrArg (Ty.customTy nm) ?_
    induction tys with
    | nil => rfl
    | cons hd tl ih_tl =>
      simp only [List.map_cons, List.cons.injEq, Function.comp]
      exact ⟨ih hd List.mem_cons_self, ih_tl fun t ht => ih t (List.mem_cons_of_mem _ ht)⟩
  | bl lo hi e ih =>
    simp only [Subst.onTy_bl, Ty.eraseBounds_bl, bareListTy, Subst.onTy_customTy,
      Ty.eraseBounds_customTy]
    simpa [bareListTy, Ty.customTy.injEq, List.cons.injEq] using ih

/-- `eraseBounds` is a congruence for substitution: equal erased shapes stay
    equal after applying `S` then erasing again. -/
theorem Ty.eraseBounds_onTy_congr (S : Subst) {t₁ t₂ : Ty}
    (h : Ty.eraseBounds t₁ = Ty.eraseBounds t₂) :
    Ty.eraseBounds (S.onTy t₁) = Ty.eraseBounds (S.onTy t₂) := by
  calc Ty.eraseBounds (S.onTy t₁)
      = Ty.eraseBounds (S.onTy (Ty.eraseBounds t₁)) := (Ty.eraseBounds_onTy_erase S t₁).symm
    _ = Ty.eraseBounds (S.onTy (Ty.eraseBounds t₂)) := by rw [h]
    _ = Ty.eraseBounds (S.onTy t₂) := Ty.eraseBounds_onTy_erase S t₂

/-- `erase` after `onPolyTy` ignores BL already present in the scheme body. -/
theorem PolyTy.eraseBounds_onPolyTy_erase (S : Subst) (σ : PolyTy) :
    PolyTy.eraseBounds (S.onPolyTy (PolyTy.eraseBounds σ)) =
      PolyTy.eraseBounds (S.onPolyTy σ) := by
  simp only [PolyTy.eraseBounds, Subst.onPolyTy, Ty.eraseBounds_onTy_erase]

/-- Env form of `eraseBounds_onTy_erase`. -/
theorem Env.eraseBounds_onEnv_erase (S : Subst) (env : Env) :
    Env.eraseBounds (S.onEnv (Env.eraseBounds env)) =
      Env.eraseBounds (S.onEnv env) := by
  simp only [Env.eraseBounds, Subst.onEnv, List.map_map]
  refine List.map_congr_left fun σ _ => ?_
  simpa [Function.comp] using PolyTy.eraseBounds_onPolyTy_erase S σ

/-- Double-erase of a constructor is a no-op (field types are already bare). -/
theorem Ctor.eraseBounds_idem (c : Ctor) :
    Ctor.eraseBounds (Ctor.eraseBounds c) = Ctor.eraseBounds c := by
  cases h : Ctor.eraseBounds c with | mk pc tn contents bound closed =>
  have hc : contents.map Ty.eraseBounds = contents := by
    have := congrArg Ctor.contents h
    simp only [Ctor.eraseBounds_contents] at this
    rw [← this, List.map_map]
    exact List.map_congr_left fun _ _ => Ty.eraseBounds_idem _
  simp only [Ctor.eraseBounds, hc]

theorem CtorEnv.eraseBounds_idem (ctors : CtorEnv) :
    CtorEnv.eraseBounds (CtorEnv.eraseBounds ctors) = CtorEnv.eraseBounds ctors := by
  induction ctors with
  | nil => rfl
  | cons hd tl ih =>
    cases hd
    simp only [CtorEnv.eraseBounds_cons, Ctor.eraseBounds_idem, ih]

@[simp] theorem Env.eraseBounds_idem (env : Env) :
    Env.eraseBounds (Env.eraseBounds env) = Env.eraseBounds env := by
  simp only [Env.eraseBounds, List.map_map]
  apply List.map_congr_left
  intro σ hσ
  simp

/-- Ctx form: double-erase after `onCtx` collapses to single erase on the image. -/
theorem Ctx.eraseBounds_onCtx_erase (S : Subst) (ctx : Ctx) :
    (S.onCtx ctx.eraseBounds).eraseBounds = (S.onCtx ctx).eraseBounds := by
  simp only [Ctx.eraseBounds, Subst.onCtx, Env.eraseBounds_onEnv_erase, CtorEnv.eraseBounds_idem]

theorem Unifies.congr_onTy {S R : Subst} {τ₁ τ₂ : Ty}
    (h : Unifies S τ₁ τ₂) : Unifies R (S.onTy τ₁) (S.onTy τ₂) := by
  simp only [Unifies] at h ⊢
  exact Ty.eraseBounds_onTy_congr R h

/-! ### Soundness, part 1: a derived substitution is a unifier -/

mutual

/-- Any substitution produced by `UnifyRel` actually unifies the two types. -/
theorem UnifyRel.unifies : {τ₁ τ₂ : Ty} → {S : Subst} → UnifyRel τ₁ τ₂ S →
    Unifies S τ₁ τ₂
  | _, _, _, .prim => rfl
  | _, _, _, .fvarRefl => rfl
  | _, _, _, @UnifyRel.fvarL n τ _ hocc => by
    -- [(n, τ)] maps both sides to τ (occurs-check ⇒ right side fixed).
    simp only [Unifies, AgreesHM, Subst.onTy]
    -- left: substFvars [(n,τ)] (.fvar n) = substFvar n τ (.fvar n) = τ
    -- right: substFvars [(n,τ)] τ = substFvar n τ τ = τ  (n fresh in τ)
    change Ty.eraseBounds (Ty.substFvar n τ (.fvar n)) =
      Ty.eraseBounds (Ty.substFvar n τ τ)
    simp only [Ty.substFvar, if_true]
    rw [Ty.substFvar_fresh hocc]
  | _, _, _, @UnifyRel.fvarR n τ _ hocc => by
    simp only [Unifies, AgreesHM, Subst.onTy]
    change Ty.eraseBounds (Ty.substFvar n τ τ) =
      Ty.eraseBounds (Ty.substFvar n τ (.fvar n))
    simp only [Ty.substFvar, if_true]
    rw [Ty.substFvar_fresh hocc]
  | _, _, _, .arrow h₁ h₂ => by
    have e1 := UnifyRel.unifies h₁
    have e2 := UnifyRel.unifies h₂
    simp only [Unifies, AgreesHM, Subst.onTy_append, Subst.onTy_arrow, Ty.eraseBounds_arrow] at e1 e2 ⊢
    refine congrArg₂ Ty.arrow ?_ e2
    exact Ty.eraseBounds_onTy_congr _ e1
  | _, _, _, .customTy hl => by
    have el := UnifyRelList.unifies hl
    simp only [Unifies, AgreesHM, Subst.onTy_customTy, Ty.eraseBounds_customTy,
      TyList.eraseBounds_eq_map, List.map_map]
    exact congrArg (Ty.customTy _) el
  | _, _, _, .bl h => by
    have e := UnifyRel.unifies h
    simp only [Unifies, AgreesHM, Subst.onTy_bl, Ty.eraseBounds_bl] at e ⊢
    exact congrArg bareListTy e
  | _, _, _, .blList h => by
    have e := UnifyRel.unifies h
    simp only [Unifies, AgreesHM, Subst.onTy_bl, Subst.onTy_customTy, Ty.eraseBounds_bl,
      Ty.eraseBounds_customTy, TyList.eraseBounds_eq_map, List.map_cons, List.map_nil,
      bareListTy] at e ⊢
    exact congrArg bareListTy e
  | _, _, _, .listBl h => by
    have e := UnifyRel.unifies h
    simp only [Unifies, AgreesHM, Subst.onTy_bl, Subst.onTy_customTy, Ty.eraseBounds_bl,
      Ty.eraseBounds_customTy, TyList.eraseBounds_eq_map, List.map_cons, List.map_nil,
      bareListTy] at e ⊢
    exact congrArg bareListTy e

/-- The list version: a list-unifier equalises the two lists **up to eraseBounds**. -/
theorem UnifyRelList.unifies : {ts₁ ts₂ : List Ty} → {S : Subst} →
    UnifyRelList ts₁ ts₂ S →
      ts₁.map (fun t => Ty.eraseBounds (S.onTy t)) =
        ts₂.map (fun t => Ty.eraseBounds (S.onTy t))
  | _, _, _, .nil => rfl
  | _, _, _, .cons h₁ ht => by
    have e1 := UnifyRel.unifies h₁
    have et := UnifyRelList.unifies ht
    simp only [Unifies] at e1
    -- e1 : erase (S₁ t₁) = erase (S₁ t₂)
    -- et : map (erase ∘ S₂.onTy) (map S₁ ts₁) = same for ts₂
    -- goal head: erase ((S₁++S₂) t₁) = erase (S₂ (S₁ t₁))
    refine congrArg₂ List.cons ?_ ?_
    · simp only [Subst.onTy_append]
      exact Ty.eraseBounds_onTy_congr _ e1
    · -- et : map (fun t => erase (S₂ (S₁ t))) ... after map_map
      simpa [List.map_map, Function.comp, Subst.onTy_append, Subst.map_onTy_append] using et

end


/-! ### Soundness, part 2: a derived substitution is *most general*

The backbone of the var cases: if `S'` already equates `.fvar n` with `U`, then
applying `S'` is unchanged by first substituting `[n ↦ U]`. -/

theorem Subst.onTy_substFvar {S' : Subst} {n : Nat} {U : Ty}
    (h : S'.onTy (.fvar n) = S'.onTy U) :
    ∀ τ, S'.onTy (Ty.substFvar n U τ) = S'.onTy τ := by
  intro τ
  induction τ using Ty.rec_strong with
  | prim p => rfl
  | bvar i => rfl
  | fvar m =>
    by_cases hm : m = n
    · subst hm
      simp only [Ty.substFvar, if_true]
      exact h.symm
    · simp only [Ty.substFvar, if_neg hm]
  | arrow a b iha ihb => simp only [Ty.substFvar, Subst.onTy_arrow, iha, ihb]
  | customTy nm tys ih =>
    simp only [Ty.substFvar, TyList.substFvar_eq_map, Subst.onTy_customTy, List.map_map]
    apply congrArg (Ty.customTy nm)
    apply List.map_congr_left
    intro t ht
    exact ih t ht
  | bl lo hi e ih =>
    simp only [Ty.substFvar, Subst.onTy_bl, ih]

/-- Bounds-blind form of `onTy_substFvar`: if `S'` equates `.fvar n` with `U`
    after `eraseBounds`, then substituting `[n ↦ U]` is invisible to `S'` up to
    `eraseBounds`. -/
theorem Subst.onTy_substFvar_erase {S' : Subst} {n : Nat} {U : Ty}
    (h : Ty.eraseBounds (S'.onTy (.fvar n)) = Ty.eraseBounds (S'.onTy U)) :
    ∀ τ, Ty.eraseBounds (S'.onTy (Ty.substFvar n U τ)) =
      Ty.eraseBounds (S'.onTy τ) := by
  intro τ
  induction τ using Ty.rec_strong with
  | prim p => rfl
  | bvar i => rfl
  | fvar m =>
    by_cases hm : m = n
    · subst hm
      simp only [Ty.substFvar, if_true]
      exact h.symm
    · simp only [Ty.substFvar, if_neg hm]
  | arrow a b iha ihb =>
    simp only [Ty.substFvar, Subst.onTy_arrow, Ty.eraseBounds_arrow, iha, ihb]
  | customTy nm tys ih =>
    simp only [Ty.substFvar, TyList.substFvar_eq_map, Subst.onTy_customTy,
      Ty.eraseBounds_customTy, TyList.eraseBounds_eq_map, List.map_map]
    refine congrArg (Ty.customTy nm) ?_
    apply List.map_congr_left
    intro t ht
    exact ih t ht
  | bl lo hi e ih =>
    simp only [Ty.substFvar, Subst.onTy_bl, Ty.eraseBounds_bl, ih]

/-- `AgreesHM` form of `onTy_substFvar_erase` (Chunk 1). -/
theorem Subst.onTy_substFvar_agreesHM {S' : Subst} {n : Nat} {U : Ty}
    (h : AgreesHM (S'.onTy (.fvar n)) (S'.onTy U)) (τ : Ty) :
    AgreesHM (S'.onTy (Ty.substFvar n U τ)) (S'.onTy τ) :=
  Subst.onTy_substFvar_erase h τ

/-! ### Most-general unifier factoring (`FactorsHM`)

Every substitution produced by `UnifyRel` is a *most general* unifier: any other
bounds-blind unifier `S'` factors through it **up to `eraseBounds`**
(`FactorsHM`). Var cases use `onTy_substFvar_agreesHM`; compound cases thread
sub-problem residuals. The structural wrappers `UnifyRel.greatest` /
`UnifyRelList.greatest` recover tree equality via the false scaffold
`AgreesHM.optionA_to_eq` so existing `TypeOf*` scripts still typecheck.

`IsMGU.greatest` remains structural for now; the real residual is
`UnifyRel.greatest_factors`. -/
mutual

/-- Real MGU residual: factors through `S` up to HM shape (`FactorsHM`). -/
theorem UnifyRel.greatest_factors : {τ₁ τ₂ : Ty} → {S : Subst} → UnifyRel τ₁ τ₂ S →
    ∀ S' : Subst, Unifies S' τ₁ τ₂ → ∃ R : Subst, FactorsHM S' S R
  | _, _, _, .prim, S', _ =>
    ⟨S', fun τ => by simp only [AgreesHM, Subst.onTy_nil]⟩
  | _, _, _, .fvarRefl, S', _ =>
    ⟨S', fun τ => by simp only [AgreesHM, Subst.onTy_nil]⟩
  | _, _, _, @UnifyRel.fvarL n U _ _, S', hS' => by
    refine ⟨S', fun τ => ?_⟩
    -- S = [(n, U)]; R = S'. Need erase(S' τ) = erase(S' (subst n U τ)).
    simp only [AgreesHM, Subst.onTy] at hS' ⊢
    -- hS' : erase (S' (.fvar n)) = erase (S' U)
    have h := Subst.onTy_substFvar_erase hS' τ
    -- h : erase (S' (subst n U τ)) = erase (S' τ)
    simpa [Subst.onTy] using h.symm
  | _, _, _, @UnifyRel.fvarR n U _ _, S', hS' => by
    refine ⟨S', fun τ => ?_⟩
    simp only [AgreesHM, Subst.onTy] at hS' ⊢
    -- hS' : erase (S' U) = erase (S' (.fvar n)); flip for onTy_substFvar_erase
    have h := Subst.onTy_substFvar_erase hS'.symm τ
    simpa [Subst.onTy] using h.symm
  | _, _, _, @UnifyRel.arrow a b c d S₁ S₂ h₁ h₂, S', hS' => by
    -- Split arrow unifier into domain/codomain up to eraseBounds.
    have hac : Unifies S' a c := by
      simp only [Unifies, AgreesHM, Subst.onTy_arrow, Ty.eraseBounds_arrow] at hS'
      exact (Ty.arrow.inj hS').1
    have hbd : Unifies S' b d := by
      simp only [Unifies, AgreesHM, Subst.onTy_arrow, Ty.eraseBounds_arrow] at hS'
      exact (Ty.arrow.inj hS').2
    obtain ⟨R₁, hR₁⟩ := UnifyRel.greatest_factors h₁ S' hac
    have hR₁bd : Unifies R₁ (S₁.onTy b) (S₁.onTy d) := by
      -- erase (R₁ (S₁ b)) ~ erase (S' b) ~ erase (S' d) ~ erase (R₁ (S₁ d))
      simp only [Unifies, AgreesHM] at hbd ⊢
      exact (hR₁ b).symm.trans (hbd.trans (hR₁ d))
    obtain ⟨R₂, hR₂⟩ := UnifyRel.greatest_factors h₂ R₁ hR₁bd
    refine ⟨R₂, fun τ => ?_⟩
    -- erase (S' τ) ~ erase (R₁ (S₁ τ)) ~ erase (R₂ (S₂ (S₁ τ)))
    simp only [FactorsHM, AgreesHM, Subst.onTy_append] at hR₁ hR₂ ⊢
    exact (hR₁ τ).trans (hR₂ (S₁.onTy τ))
  | _, _, _, @UnifyRel.customTy nm tys₁ tys₂ S hl, S', hS' => by
    have hlist :
        tys₁.map (fun t => Ty.eraseBounds (S'.onTy t)) =
          tys₂.map (fun t => Ty.eraseBounds (S'.onTy t)) := by
      simp only [Unifies, AgreesHM, Subst.onTy_customTy, Ty.eraseBounds_customTy,
        TyList.eraseBounds_eq_map, List.map_map] at hS'
      -- hS' : customTy nm (map erase (map S' tys₁)) = same for tys₂
      exact (Ty.customTy.inj hS').2
    exact UnifyRelList.greatest_factors hl S' hlist
  | _, _, _, @UnifyRel.bl lo₁ hi₁ lo₂ hi₂ e₁ e₂ S h, S', hS' => by
    have hElem : Unifies S' e₁ e₂ := by
      simp only [Unifies, AgreesHM, Subst.onTy_bl, Ty.eraseBounds_bl, bareListTy] at hS' ⊢
      -- bareList (erase (S' e₁)) = bareList (erase (S' e₂))
      simpa [bareListTy, Ty.customTy.injEq, List.cons.injEq] using hS'
    exact UnifyRel.greatest_factors h S' hElem
  | _, _, _, @UnifyRel.blList lo hi e α S h, S', hS' => by
    have hElem : Unifies S' e α := by
      simp only [Unifies, AgreesHM, Subst.onTy_bl, Subst.onTy_customTy, Ty.eraseBounds_bl,
        Ty.eraseBounds_customTy, TyList.eraseBounds_eq_map, List.map_cons, List.map_nil,
        bareListTy] at hS' ⊢
      simpa [bareListTy, Ty.customTy.injEq, List.cons.injEq] using hS'
    exact UnifyRel.greatest_factors h S' hElem
  | _, _, _, @UnifyRel.listBl lo hi e α S h, S', hS' => by
    have hElem : Unifies S' α e := by
      simp only [Unifies, AgreesHM, Subst.onTy_bl, Subst.onTy_customTy, Ty.eraseBounds_bl,
        Ty.eraseBounds_customTy, TyList.eraseBounds_eq_map, List.map_cons, List.map_nil,
        bareListTy] at hS' ⊢
      simpa [bareListTy, Ty.customTy.injEq, List.cons.injEq] using hS'
    exact UnifyRel.greatest_factors h S' hElem

theorem UnifyRelList.greatest_factors : {ts₁ ts₂ : List Ty} → {S : Subst} →
    UnifyRelList ts₁ ts₂ S → ∀ S' : Subst,
      ts₁.map (fun t => Ty.eraseBounds (S'.onTy t)) =
        ts₂.map (fun t => Ty.eraseBounds (S'.onTy t)) →
      ∃ R : Subst, FactorsHM S' S R
  | _, _, _, .nil, S', _ =>
    ⟨S', fun τ => by simp only [AgreesHM, Subst.onTy_nil]⟩
  | _, _, _, @UnifyRelList.cons t₁ t₂ ts₁ ts₂ S₁ S₂ h₁ ht, S', hS' => by
    simp only [List.map_cons, List.cons.injEq] at hS'
    obtain ⟨ht1t2, htail⟩ := hS'
    -- ht1t2 : erase (S' t₁) = erase (S' t₂)
    obtain ⟨R₁, hR₁⟩ := UnifyRel.greatest_factors h₁ S' ht1t2
    have hlist :
        (ts₁.map S₁.onTy).map (fun t => Ty.eraseBounds (R₁.onTy t)) =
          (ts₂.map S₁.onTy).map (fun t => Ty.eraseBounds (R₁.onTy t)) := by
      -- erase (R₁ (S₁ t)) = erase (S' t) via FactorsHM; rewrite both sides to S'-erasure
      have key (l : List Ty) :
          (l.map S₁.onTy).map (fun t => Ty.eraseBounds (R₁.onTy t)) =
            l.map (fun t => Ty.eraseBounds (S'.onTy t)) := by
        rw [List.map_map]
        apply List.map_congr_left
        intro t _
        exact (hR₁ t).symm
      rw [key, key, htail]
    obtain ⟨R₂, hR₂⟩ := UnifyRelList.greatest_factors ht R₁ hlist
    refine ⟨R₂, fun τ => ?_⟩
    simp only [FactorsHM, AgreesHM, Subst.onTy_append] at hR₁ hR₂ ⊢
    exact (hR₁ τ).trans (hR₂ (S₁.onTy τ))

end

/-- Path R: do **not** reintroduce structural residual factoring
    (`S'·τ = R·(S·τ)` for all τ). That is false under bounds-blind unify
    (BL vs List). Use `UnifyRel.greatest_factors` / `FactorsHM` only. -/

theorem UnifyRel.isMGU {τ₁ τ₂ : Ty} {S : Subst} (h : UnifyRel τ₁ τ₂ S) :
    IsMGU S τ₁ τ₂ :=
  ⟨h.unifies, fun S' hS' => UnifyRel.greatest_factors h S' hS'⟩


/-! ### Local-closedness of substitutions

Applying an LC substitution preserves local-closedness, and unification of two
LC monotypes yields an LC substitution (each replacement is a sub-part of an LC
input). These feed the `Infer.lc` invariant. -/

/-- Applying a substitution whose replacements are all LC preserves LC. -/
theorem Subst.onTy_lc {S : Subst} (h_lc : ∀ p ∈ S, p.2.IsLC) :
    ∀ {τ : Ty}, τ.IsLC → (S.onTy τ).IsLC := by
  induction S with
  | nil => intro τ hτ; simpa using hτ
  | cons hd S' ih =>
    obtain ⟨Z, U⟩ := hd
    have hU : U.IsLC := h_lc (Z, U) (List.mem_cons_self ..)
    have hS' : ∀ p ∈ S', p.2.IsLC := fun p hp => h_lc p (List.mem_cons_of_mem _ hp)
    intro τ hτ
    rw [show ((Z, U) :: S') = [(Z, U)] ++ S' from rfl, Subst.onTy_append]
    exact ih hS' (Ty.IsLC.substFvar hU hτ)

mutual

/-- Unifying two locally-closed monotypes yields an LC substitution. -/
theorem UnifyRel.lc : {a b : Ty} → {S : Subst} → UnifyRel a b S →
    a.IsLC → b.IsLC → ∀ p ∈ S, p.2.IsLC
  | _, _, _, .prim, _, _ => by simp
  | _, _, _, .fvarRefl, _, _ => by simp
  | _, _, _, .fvarL _ _, _, hb => by
    intro p hp; rw [List.mem_singleton] at hp; subst hp; exact hb
  | _, _, _, .fvarR _ _, ha, _ => by
    intro p hp; rw [List.mem_singleton] at hp; subst hp; exact ha
  | _, _, _, .arrow h₁ h₂, ha, hb => by
    cases ha with | arrow ha_a ha_b => cases hb with | arrow hb_c hb_d =>
    have h1lc := UnifyRel.lc h₁ ha_a hb_c
    have h2lc := UnifyRel.lc h₂ (Subst.onTy_lc h1lc ha_b) (Subst.onTy_lc h1lc hb_d)
    intro p hp; rw [List.mem_append] at hp
    rcases hp with hp | hp
    · exact h1lc p hp
    · exact h2lc p hp
  | _, _, _, .customTy hl, ha, hb => by
    cases ha with | customTy ha_all => cases hb with | customTy hb_all =>
    exact UnifyRelList.lc hl ha_all hb_all
  | _, _, _, .bl h, ha, hb => by
    cases ha with | bl hae => cases hb with | bl hbe =>
    exact UnifyRel.lc h hae hbe
  | _, _, _, .blList h, ha, hb => by
    cases ha with | bl hae => cases hb with | customTy hball =>
    exact UnifyRel.lc h hae (hball _ List.mem_cons_self)
  | _, _, _, .listBl h, ha, hb => by
    cases ha with | customTy hball => cases hb with | bl hbe =>
    exact UnifyRel.lc h (hball _ List.mem_cons_self) hbe

/-- List version: unifying two LC type lists yields an LC substitution. -/
theorem UnifyRelList.lc : {ts₁ ts₂ : List Ty} → {S : Subst} → UnifyRelList ts₁ ts₂ S →
    (∀ t ∈ ts₁, t.IsLC) → (∀ t ∈ ts₂, t.IsLC) → ∀ p ∈ S, p.2.IsLC
  | _, _, _, .nil, _, _ => by simp
  | _, _, _, @UnifyRelList.cons t₁ t₂ ts₁ ts₂ S₁ S₂ h₁ ht, hts₁, hts₂ => by
    have ht1 : t₁.IsLC := hts₁ t₁ (List.mem_cons_self ..)
    have ht2 : t₂.IsLC := hts₂ t₂ (List.mem_cons_self ..)
    have h1lc := UnifyRel.lc h₁ ht1 ht2
    have hmap₁ : ∀ t ∈ ts₁.map S₁.onTy, t.IsLC := by
      intro t htm; obtain ⟨t0, ht0, rfl⟩ := List.mem_map.mp htm
      exact Subst.onTy_lc h1lc (hts₁ t0 (List.mem_cons_of_mem _ ht0))
    have hmap₂ : ∀ t ∈ ts₂.map S₁.onTy, t.IsLC := by
      intro t htm; obtain ⟨t0, ht0, rfl⟩ := List.mem_map.mp htm
      exact Subst.onTy_lc h1lc (hts₂ t0 (List.mem_cons_of_mem _ ht0))
    have h2lc := UnifyRelList.lc ht hmap₁ hmap₂
    intro p hp; rw [List.mem_append] at hp
    rcases hp with hp | hp
    · exact h1lc p hp
    · exact h2lc p hp

end


/-! ## Algorithmic phase, step 2: the inference relation (Algorithm W, relational)

`Infer Φ ctx e Φ' S τ` is Algorithm W phrased as a *relation* (no function /
termination obligation yet — that is stage 3). It reads: starting with the
fresh-variable frontier `Φ` (every unification var in play is `< Φ`), expression
`e` infers type `τ` under the most-general substitution `S`, allocating fresh
vars up to the new frontier `Φ'`. `.fvar`s are the unification variables;
composition of the threaded substitutions is `++`.

This covers the full language (`primLit`, `pair`, `lambda`, `app`, `var`,
`letIn`, `fst`, `snd`, `ctor`, `match_`), bridging to `TypeOfElabHM` via soundness.

The plan: prove `Infer.sound` (algo type ⟹ declarative type, iterating
`typ_subst_preservation` and using `UnifyRel.isMGU`), then completeness. -/

/-- The `k` fresh unification-var names starting at frontier `Φ`. -/
def freshVars (Φ k : Nat) : List Nat := (List.range k).map (Φ + ·)

/-- Generalization candidates: the free unification vars of `τ` that are *not*
    fixed by `env` and *not* rigid. The `rigid` set carries the in-scope scoped
    type variables (the free type fvars of the bound expression's annotations):
    those are skolems bound by an enclosing signature and must stay rigid —
    generalizing over them is unsound (it would let an inner `let` treat a fixed
    scoped variable as if it were polymorphic). For an ordinary HM program (no
    free-variable annotations) `rigid = []`, recovering the classic
    `ftv(τ) \ ftv(env)`. -/
def genVars (rigid : List Nat) (env : Env) (τ : Ty) : List Nat :=
  τ.freeVars.filter (fun x => !env.freeVars.contains x && !rigid.contains x)

/-- The principal generalization of `τ` relative to `env`, excluding the `rigid`
    scoped type variables. Reuses the existing `Ty.closeOver` (`fvar` ↦ `bvar` by
    position), whose `closeOver_preserves_bvars` immediately gives
    `genScheme … |>.WF`. -/
def genScheme (rigid : List Nat) (env : Env) (τ : Ty) : PolyTy :=
  { paramCount := (genVars rigid env τ).length, body := Ty.closeOver (genVars rigid env τ) τ }

/-- A generalized scheme is well-formed when its body type is locally-closed —
    closing introduces only the `paramCount`-many fresh bound vars. -/
theorem genScheme_wf {rigid : List Nat} {env : Env} {τ : Ty} (hτ : τ.IsLC) :
    (genScheme rigid env τ).WF :=
  Ty.closeOver_preserves_bvars hτ

/-- `freeVars` is always duplicate-free (it dedups). -/
theorem Ty.freeVars_nodup {τ : Ty} : τ.freeVars.Nodup := by
  cases τ with
  | prim => simp [Ty.freeVars]
  | bvar => simp [Ty.freeVars]
  | fvar => simp [Ty.freeVars]
  | arrow a b => simp [Ty.freeVars, List.nodup_dedup]
  | customTy nm tys =>
    cases tys with
    | nil => simp [Ty.freeVars, TyList.freeVars]
    | cons hd tl => simp [Ty.freeVars, TyList.freeVars, List.nodup_dedup]
  | bl _ _ e => exact Ty.freeVars_nodup (τ := e)

/-- The generalization candidates are duplicate-free. -/
theorem genVars_nodup {rigid : List Nat} {env : Env} {τ : Ty} : (genVars rigid env τ).Nodup :=
  Ty.freeVars_nodup.filter _

/-- Group generalization candidates: the free unification vars appearing in *any*
    of the group's solved monotypes `τs`, excluding env-fixed and rigid vars. This
    is the SHARED pool `G` for the whole recursive group, so every binding
    generalizes over the same names — keeping mutual recursion's type-sharing
    linked (the `letRec` analogue of `genVars`). -/
def genGroupVars (rigid : List Nat) (env : Env) (τs : List Ty) : List Nat :=
  (Ty.freeVarsList τs).filter (fun x => !env.freeVars.contains x && !rigid.contains x)

/-- Per-binding generalization of a recursive group: each `τⱼ` is generalized over
    the shared pool `genGroupVars rigid env τs` via `PolyTy.genGroup` (the body
    scheme `∀ (G ∩ ftv τⱼ). τⱼ`). Mirrors the declarative `Ms = τs.map (genGroup G)`. -/
def genGroupSchemes (rigid : List Nat) (env : Env) (τs : List Ty) : List PolyTy :=
  τs.map (PolyTy.genGroup (genGroupVars rigid env τs))

/-- The rigid (non-generalisable) variables of a fused recursion node: the free
    type variables of the stored per-binding scheme annotations TOGETHER with those
    of the binding terms' annotations. The declared schemes sit in the group's
    checking env (`RecSpecs.rhsCtx` binds annotated members at their FULL schemes),
    so their scoped variables must be treated exactly like outer-env variables and
    never enter the gen-pool — otherwise an unannotated sibling whose solved
    monotype mentions an annotated member's scoped variable would wrongly
    generalise it (underivable declaratively: the shared-pool cofinite opening
    renames the pool through the monotypes but leaves the schemes fixed). -/
def RecGroup.rigidVars (anns : List (Option PolyTy)) (bindings : List Expr) : List Nat :=
  Expr.tyFreeVars.AnnList.tyFreeVars anns ++ bindings.flatMap Expr.tyFreeVars

/-- `Ty.freeVarsList` is always duplicate-free (it dedups). -/
theorem Ty.freeVarsList_nodup {τs : List Ty} : (Ty.freeVarsList τs).Nodup := by
  cases τs with
  | nil => simp [Ty.freeVarsList]
  | cons hd tl => simp [Ty.freeVarsList, List.nodup_dedup]

/-- The group generalization candidates are duplicate-free. -/
theorem genGroupVars_nodup {rigid : List Nat} {env : Env} {τs : List Ty} :
    (genGroupVars rigid env τs).Nodup :=
  Ty.freeVarsList_nodup.filter _

/-! ### Algorithmic `RecSpec` helpers (the fused `letRec` rule's internals).

The fused inference rule threads a `List RecSpec` (Core's per-binding datum:
`mono τ` for an unannotated member's solved monotype, `poly σ` for an annotated
member's declared scheme). These small helpers are the algorithmic counterparts
of Core's `RecSpec.rhsEntry`/`bodyScheme`: build the initial specs positionally
from the stored `anns`, thread a substitution through the mono members (schemes
stay RIGID), and project out the mono monotypes for the shared gen-var pool. -/

/-- Thread a substitution through a spec: an unannotated member's solved monotype
    moves under `S`; an annotated member's declared scheme threads RIGID (exactly
    like the old `InferRecGroupAnn` treated its `schemes`). -/
def RecSpec.onSubst (S : Subst) : RecSpec → RecSpec
  | .mono τ => .mono (S.onTy τ)
  | .poly σ => .poly σ

/-- The monotype an unannotated member contributes to the shared gen-var pool
    (`none` for annotated members — schemes are pool-independent). -/
def RecSpec.monoTy? : RecSpec → Option Ty
  | .mono τ => some τ
  | .poly _ => none

/-- The solved monotypes of a group's specs, in order — the pool `genGroupVars`
    ranges over (annotated members contribute nothing). -/
def RecSpecs.monoTys (specs : List RecSpec) : List Ty := specs.filterMap RecSpec.monoTy?

/-- Well-formedness of a single algorithmic `RecSpec`: an unannotated member's
    solved monotype is locally closed; an annotated member's declared scheme is
    `WF`. The spec-level lift of `RecSpecs.WF`'s `mono_lc`/`poly_wf` fields. -/
def RecSpec.LC : RecSpec → Prop
  | .mono τ => τ.IsLC
  | .poly σ => σ.WF

/-- Free type variables a `RecSpec` contributes to the elaborated nest: an
    unannotated member's monotype free vars, an annotated member's scheme-body free
    vars (its scoped variables). -/
def RecSpec.freeVars : RecSpec → List Nat
  | .mono τ => τ.freeVars
  | .poly σ => σ.body.freeVars

/-- Build the initial specs positionally from the stored annotations, starting at
    frontier `Φ`: **every** member — annotated or not — gets a fresh monotype var
    `mono (fvar (Φ+j))` (Damas–Milner monomorphic recursion). The annotations do
    NOT sit in the RHS env as schemes; they act as a *ceiling*, checked separately
    after group unification (see `Infer.letRec`). -/
def RecSpec.init (Φ : Nat) : List (Option PolyTy) → List RecSpec
  | []            => []
  | _ :: as       => RecSpec.mono (.fvar Φ) :: RecSpec.init (Φ + 1) as

/-- `init` produces only monotype specs: the stored annotations are all mapped to
    `none` (the DM cut — annotations are ceilings, not RHS schemes). -/
theorem RecSpec.map_ann_init (Φ : Nat) (anns : List (Option PolyTy)) :
    (RecSpec.init Φ anns).map RecSpec.ann = anns.map (fun _ => none) := by
  induction anns generalizing Φ with
  | nil => rfl
  | cons a as ih => simp only [RecSpec.init, List.map_cons, RecSpec.ann, ih (Φ + 1)]

/-- `init` produces one spec per stored annotation. -/
theorem RecSpec.init_length (Φ : Nat) (anns : List (Option PolyTy)) :
    (RecSpec.init Φ anns).length = anns.length := by
  induction anns generalizing Φ with
  | nil => rfl
  | cons a as ih => simp only [RecSpec.init, List.length_cons, ih (Φ + 1)]

/-- The `j`-th initial spec is `mono (fvar (Φ+j))` (regardless of annotation). -/
theorem RecSpec.init_getElem? (Φ : Nat) (anns : List (Option PolyTy)) (j : Nat) :
    (RecSpec.init Φ anns)[j]? = (anns[j]?).map (fun _ => .mono (.fvar (Φ + j))) := by
  induction anns generalizing Φ j with
  | nil => simp [RecSpec.init]
  | cons a as ih =>
    cases j with
    | zero => simp [RecSpec.init]
    | succ j =>
      simp only [RecSpec.init, List.getElem?_cons_succ, ih (Φ + 1) j, Nat.add_assoc,
        Nat.add_comm 1 j]

/-- Membership characterisation of the initial specs: every member is a fresh
    monotype var in the block `[Φ, Φ + anns.length)`. (The `.poly` disjunct is kept
    only for statement stability with existing call sites — `init` never produces
    `.poly` after the DM cut; it is always the left disjunct.) -/
theorem RecSpec.mem_init {s : RecSpec} :
    ∀ {Φ : Nat} {anns : List (Option PolyTy)}, s ∈ RecSpec.init Φ anns →
      (∃ m, Φ ≤ m ∧ m < Φ + anns.length ∧ s = .mono (.fvar m)) ∨
      (∃ σ, some σ ∈ anns ∧ s = .poly σ) := by
  intro Φ anns
  induction anns generalizing Φ with
  | nil => intro h; simp [RecSpec.init] at h
  | cons a as ih =>
    intro h
    rcases List.mem_cons.mp h with rfl | h
    · exact .inl ⟨Φ, le_refl _, by simp only [List.length_cons]; omega, rfl⟩
    · rcases ih h with ⟨m, h1, h2, h3⟩ | ⟨σ, h1, h2⟩
      · exact .inl ⟨m, by omega, by simp only [List.length_cons]; omega, h3⟩
      · exact .inr ⟨σ, List.mem_cons_of_mem _ h1, h2⟩

/-- A scheme spec among the initial specs is a stored annotation. -/
theorem RecSpec.poly_mem_init {Φ : Nat} {anns : List (Option PolyTy)} {σ : PolyTy}
    (h : RecSpec.poly σ ∈ RecSpec.init Φ anns) : some σ ∈ anns := by
  rcases RecSpec.mem_init h with ⟨m, _, _, heq⟩ | ⟨σ', hσ', heq⟩
  · exact absurd heq (by simp)
  · injection heq with h'
    exact h' ▸ hσ'

/-- `onSubst` preserves the stored annotation view (schemes thread rigid). -/
theorem RecSpec.map_ann_onSubst (S : Subst) (specs : List RecSpec) :
    (specs.map (RecSpec.onSubst S)).map RecSpec.ann = specs.map RecSpec.ann := by
  rw [List.map_map]
  exact List.map_congr_left (fun s _ => by cases s <;> rfl)

/-- A scheme sits among the `onSubst`-transported specs iff it sat among the
    originals (schemes thread rigid, monos stay mono). -/
theorem RecSpec.poly_mem_map_onSubst {S : Subst} {specs : List RecSpec} {σ : PolyTy} :
    RecSpec.poly σ ∈ specs.map (RecSpec.onSubst S) ↔ RecSpec.poly σ ∈ specs := by
  constructor
  · intro h
    obtain ⟨s, hs, heq⟩ := List.mem_map.mp h
    cases s with
    | mono τ => exact absurd heq (by simp [RecSpec.onSubst])
    | poly σ' => exact (RecSpec.poly.injEq .. ▸ heq : σ' = σ) ▸ hs
  · intro h
    exact List.mem_map.mpr ⟨.poly σ, h, rfl⟩

/-- `onSubst` transport of spec local closedness (needs LC images). -/
theorem RecSpec.LC.onSubst {S : Subst} (hS : ∀ p ∈ S, p.2.IsLC) {s : RecSpec}
    (h : s.LC) : (RecSpec.onSubst S s).LC := by
  cases s with
  | mono τ => exact Subst.onTy_lc hS h
  | poly σ => exact h

/-- `onSubst` composes along substitution append (pointwise `Subst.onTy_append`;
    schemes are fixed throughout). -/
theorem RecSpec.onSubst_append (S T : Subst) (s : RecSpec) :
    RecSpec.onSubst (S ++ T) s = RecSpec.onSubst T (RecSpec.onSubst S s) := by
  cases s with
  | mono τ => simp only [RecSpec.onSubst, Subst.onTy_append]
  | poly σ => rfl

/-- The empty-pool RHS entry of a spec is well-formed when the spec is
    (`rhsEntry [] [] = mono ↦ mkTrivial, poly ↦ id` definitionally). -/
theorem RecSpec.rhsEntry_nil_wf {s : RecSpec} (h : s.LC) :
    (RecSpec.rhsEntry [] [] s).WF := by
  cases s with
  | mono τ => exact h
  | poly σ => exact h

/-- The empty-pool RHS entry's body free vars are the spec's free vars. -/
theorem RecSpec.rhsEntry_nil_body_freeVars (s : RecSpec) :
    (RecSpec.rhsEntry [] [] s).body.freeVars = s.freeVars := by
  cases s <;> rfl

/-- A body scheme is well-formed when its spec is (mono: `genGroup_wf`). -/
theorem RecSpec.bodyScheme_wf {G : List Nat} {s : RecSpec} (h : s.LC) :
    (RecSpec.bodyScheme G s).WF := by
  cases s with
  | mono τ => exact PolyTy.genGroup_wf h
  | poly σ => exact h

/-- A body scheme's body free vars come from the spec's free vars (mono: closing
    only removes). -/
theorem RecSpec.mem_bodyScheme_freeVars {G : List Nat} {s : RecSpec} {w : Nat}
    (h : w ∈ (RecSpec.bodyScheme G s).body.freeVars) : w ∈ s.freeVars := by
  cases s with
  | mono τ => exact Ty.freeVars_closeOver_subset h
  | poly σ => exact h

/-- At the empty pool the body scheme IS the RHS entry (`genGroup [] = mkTrivial`)
    — the mono-group trick's identity. -/
theorem RecSpec.bodyScheme_nil (s : RecSpec) :
    RecSpec.bodyScheme [] s = RecSpec.rhsEntry [] [] s := by
  cases s with
  | mono τ =>
    show PolyTy.genGroup [] τ = PolyTy.mkTrivial τ
    have hcl : Ty.closeOver [] τ = τ := Ty.closeOver_eq_self_of_fresh (by simp)
    simp only [PolyTy.genGroup, Ty.genFilter, List.filter_nil, List.length_nil, hcl,
      PolyTy.mkTrivial]
  | poly σ => rfl

/-- Renaming the empty pool at any names is the identity (`[].zip _ = []`). -/
theorem Ty.renameG_nil_pool {Zs : List Nat} {τ : Ty} : Ty.renameG [] Zs τ = τ := rfl

/-- The empty-pool RHS entry is insensitive to the opening names. -/
theorem RecSpec.rhsEntry_nil_any (Zs : List Nat) (s : RecSpec) :
    RecSpec.rhsEntry [] Zs s = RecSpec.rhsEntry [] [] s := by
  cases s <;> rfl

/-! ### Decidable scheme-well-formedness and closedness checks

`Ty.bvarsBelow n` decides `ContainsBvarsUpTo n` (hence `PolyTy.WF` via the
body), and `t.freeVars = []` decides `NoFreeVars` — both needed by the
annotated-`let` arm of `inferCore` to validate a scheme annotation `σ` against
the declarative side conditions. -/

mutual
/-- Boolean: all `.bvar`s in `t` are `< n`. Decides `ContainsBvarsUpTo n t`. -/
def Ty.bvarsBelow (n : Nat) : Ty → Bool
  | .prim _          => true
  | .arrow a b       => Ty.bvarsBelow n a && Ty.bvarsBelow n b
  | .fvar _          => true
  | .bvar i          => decide (i < n)
  | .customTy _ tys  => TyList.bvarsBelow n tys
  | .bl _ _ e        => Ty.bvarsBelow n e
def TyList.bvarsBelow (n : Nat) : List Ty → Bool
  | []      => true
  | t :: ts => Ty.bvarsBelow n t && TyList.bvarsBelow n ts
end

theorem TyList.bvarsBelow_iff_forall {n : Nat} (tys : List Ty) :
    TyList.bvarsBelow n tys = true ↔ ∀ t ∈ tys, Ty.bvarsBelow n t = true := by
  induction tys with
  | nil => simp [TyList.bvarsBelow]
  | cons hd tl ih =>
    simp only [TyList.bvarsBelow, Bool.and_eq_true, List.mem_cons]
    rw [ih]
    constructor
    · rintro ⟨hhd, htl⟩ t (rfl | ht)
      · exact hhd
      · exact htl t ht
    · intro h; exact ⟨h hd (Or.inl rfl), fun t ht => h t (Or.inr ht)⟩

theorem Ty.bvarsBelow_iff {n : Nat} (t : Ty) :
    Ty.bvarsBelow n t = true ↔ ContainsBvarsUpTo n t := by
  induction t using Ty.rec_strong with
  | prim p => exact iff_of_true rfl .prim
  | fvar m => exact iff_of_true rfl .fvar
  | bvar i =>
    simp only [Ty.bvarsBelow, decide_eq_true_eq]
    exact ⟨fun h => .bvar h, fun h => by cases h with | bvar hlt => exact hlt⟩
  | arrow a b iha ihb =>
    simp only [Ty.bvarsBelow, Bool.and_eq_true, iha, ihb]
    exact ⟨fun ⟨ha, hb⟩ => .arrow ha hb, fun h => by cases h with | arrow ha hb => exact ⟨ha, hb⟩⟩
  | customTy nm tys ih =>
    simp only [Ty.bvarsBelow]
    rw [TyList.bvarsBelow_iff_forall]
    constructor
    · intro h; exact .customTy (fun t' ht' => (ih t' ht').mp (h t' ht'))
    · intro h
      cases h with
      | customTy hall => exact fun t' ht' => (ih t' ht').mpr (hall t' ht')
  | bl lo hi e ih =>
    simp only [Ty.bvarsBelow, ih]
    exact ⟨fun he => .bl he, fun h => by cases h with | bl he => exact he⟩

/-- Decidability of scheme well-formedness, via `Ty.bvarsBelow`. -/
theorem PolyTy.wf_iff_bvarsBelow {M : PolyTy} :
    Ty.bvarsBelow M.paramCount M.body = true ↔ M.WF := Ty.bvarsBelow_iff M.body

/-- A type has no free vars iff every var fails to be free in it. -/
theorem Ty.noFreeVars_of_forall_not_mem {t : Ty} (h : ∀ z, z ∉ t.freeVars) :
    NoFreeVars t := by
  induction t using Ty.rec_strong with
  | prim p => exact .prim
  | bvar i => exact .bvar
  | fvar n => exact absurd (List.mem_singleton.mpr rfl) (h n)
  | arrow a b iha ihb =>
    refine .arrow (iha fun z hz => ?_) (ihb fun z hz => ?_)
    · exact h z (by simp only [Ty.freeVars, List.mem_dedup, List.mem_append]; exact .inl hz)
    · exact h z (by simp only [Ty.freeVars, List.mem_dedup, List.mem_append]; exact .inr hz)
  | customTy nm tys ih =>
    refine .customTy (fun t' ht' => ih t' ht' fun z hz => ?_)
    exact h z (by rw [Ty.freeVars]; exact TyList.mem_freeVars_of_mem ht' hz)
  | bl lo hi e ih =>
    refine .bl (ih fun z hz => ?_)
    exact h z (by simpa only [Ty.freeVars] using hz)

/-- A type has no free vars iff its `freeVars` list is empty (decidable bridge). -/
theorem Ty.noFreeVars_iff_freeVars_nil {t : Ty} :
    NoFreeVars t ↔ t.freeVars = [] := by
  refine ⟨fun h => List.eq_nil_iff_forall_not_mem.mpr (fun z => h.not_mem_freeVars z), fun h => ?_⟩
  exact Ty.noFreeVars_of_forall_not_mem (fun z hz => by rw [h] at hz; simp at hz)

/-- How an algorithmic lambda chooses its parameter type and post-binder fresh
    counter from the (optional) annotation: unannotated → a fresh unification
    variable (consuming `Φ`); annotated → the annotation `T`, which must be a
    closed monotype (consuming no fresh var). -/
inductive LamSeed (Φ : Nat) : Option Ty → Ty → Nat → Prop
  | none : LamSeed Φ none (.fvar Φ) (Φ + 1)
  | some (T : Ty) : T.IsLC → LamSeed Φ (some T) T Φ

theorem LamSeed.le {Φ : Nat} {ann pt Φ₀} (h : LamSeed Φ ann pt Φ₀) : Φ ≤ Φ₀ := by
  cases h <;> omega

/-- The chosen parameter type is locally closed (no dangling type `bvar`s). It
    MAY carry free type variables now — those are scoped type variables bound by
    an enclosing signature (the relaxation enabling `ScopedTypeVariables`). -/
theorem LamSeed.pt_isLC {Φ : Nat} {ann pt Φ₀} (h : LamSeed Φ ann pt Φ₀) : pt.IsLC := by
  cases h with
  | none => exact ContainsBvarsUpTo.fvar
  | some _ hlc => exact hlc

/-- A `LamSeed`'s annotation is fixed by `openVarsFrom` (the annotated case is
    locally closed, hence bvar-free). -/
theorem LamSeed.ann_openVarsFrom {Φ : Nat} {ann pt Φ₀} (h : LamSeed Φ ann pt Φ₀)
    (d : Nat) (Xs : List Nat) : ann.map (Ty.openVarsFrom d Xs) = ann := by
  cases h with
  | none => rfl
  | some _ hlc =>
    simp only [Option.map_some, Option.some.injEq]
    exact Ty.openVarsFrom_eq_self_of_containsBvars (hlc.mono (Nat.zero_le d))

def Ctor.IsBoolCtor (c : Ctor) : Prop :=
  c.tyName = ⟨"Bool"⟩ ∧ c.paramCount = 0 ∧ c.contents = []

/-- Decidable `Bool` check (avoids needing `DecidableEq Ty`). -/
def Ctor.isBoolCtor (c : Ctor) : Bool :=
  c.tyName == ⟨"Bool"⟩ && c.paramCount == 0 && c.contents.isEmpty

theorem Ctor.isBoolCtor_iff {c : Ctor} : c.isBoolCtor = true ↔ c.IsBoolCtor := by
  simp [Ctor.isBoolCtor, Ctor.IsBoolCtor, and_assoc]

/-- A `Bool` ctor's scheme instantiates (at no args) to `customTy "Bool" []`. -/
theorem Ctor.IsBoolCtor.instantiatesTo {c : Ctor} (h : c.IsBoolCtor) :
    c.toTy.InstantiatesTo [] (.customTy ⟨"Bool"⟩ []) := by
  obtain ⟨htn, hpc, hct⟩ := h
  unfold Ctor.toTy PolyTy.InstantiatesTo
  simp only [htn, hpc, hct]
  exact .customTy .nil

theorem Ctor.IsBoolCtor.typeOfHM {ctx : Ctx} {name : CtorName} {c : Ctor}
    (hlook : LookupList.get? ctx.ctors name = some c) (hb : c.IsBoolCtor) :
    TypeOfHM ctx (.ctor name) (.customTy ⟨"Bool"⟩ []) :=
  .ctor hlook (by simp) hb.instantiatesTo

/-- Inversion of a `customTy`-to-`customTy` instantiation: the head name is
    preserved and the argument lists instantiate pointwise. -/
theorem InstantiatesBy.customTy_inv {tyArgs : List Ty} {n₁ n₂ : TyName} {ts₁ ts₂ : List Ty}
    (h : InstantiatesBy tyArgs (.customTy n₁ ts₁) (.customTy n₂ ts₂)) :
    n₁ = n₂ ∧ List.Forall₂ (InstantiatesBy tyArgs) ts₁ ts₂ := by
  cases h with
  | customTy hff => exact ⟨rfl, hff⟩

/-- The converse of `Ctor.IsBoolCtor.instantiatesTo`: a ctor whose scheme
    instantiates to `customTy "Bool" []` must itself be a nullary `Bool` ctor. -/
theorem Ctor.IsBoolCtor.of_instantiatesTo {c : Ctor} {tyArgs : List Ty}
    (h : c.toTy.InstantiatesTo tyArgs (.customTy ⟨"Bool"⟩ [])) : c.IsBoolCtor := by
  unfold Ctor.toTy PolyTy.InstantiatesTo at h
  simp only at h
  rcases hcont : c.contents with _ | ⟨d, ds⟩
  · rw [hcont] at h
    simp only [Ty.wrapArrows] at h
    obtain ⟨hname, hff⟩ := InstantiatesBy.customTy_inv h
    refine ⟨hname, ?_, hcont⟩
    rcases hpc : c.paramCount with _ | n
    · rfl
    · exfalso; rw [hpc] at hff; simp only [Ty.bvarRange, Ty.bvarRangeFrom] at hff; cases hff
  · rw [hcont] at h
    simp only [Ty.wrapArrows] at h
    exact absurd h (by rintro ⟨⟩)

/-- From a `TypeOfHM` typing of a bare ctor at `Bool`, recover the ctor lookup
    together with its `IsBoolCtor` shape. -/
theorem Ctor.isBoolCtor_of_typeOfHM {ctx : Ctx} {name : CtorName}
    (h : TypeOfHM ctx (.ctor name) (.customTy ⟨"Bool"⟩ [])) :
    ∃ c, LookupList.get? ctx.ctors name = some c ∧ c.IsBoolCtor := by
  cases h with
  | ctor hlook _ hinst => exact ⟨_, hlook, Ctor.IsBoolCtor.of_instantiatesTo hinst⟩

/-- A raw ctor is a Bool ctor iff its erased image is (tyName/paramCount survive
    erase and `contents = []` iff `contents.map erase = []`). -/
private theorem Ctor.IsBoolCtor.of_eraseBounds {c : Ctor}
    (h : (Ctor.eraseBounds c).IsBoolCtor) : c.IsBoolCtor := by
  obtain ⟨hname, hpc, hcont⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · simpa [Ctor.eraseBounds_tyName] using hname
  · simpa [Ctor.eraseBounds_paramCount] using hpc
  · simpa [Ctor.eraseBounds_contents] using hcont

/-- Lookup transport for the primBinOp `Bool` ctors: a `TypeOfHM` Bool typing of
    `name` under an *erased* context yields the **raw** ctor lookup together with
    its `IsBoolCtor` shape (contrapositive of `Ctor.IsBoolCtor.typeOfHM_erase`). -/
private theorem Ctor.isBoolCtor_of_typeOfHM_erase {ctx : Ctx} {name : CtorName}
    (h : TypeOfHM ctx.eraseBounds (.ctor name) (.customTy ⟨"Bool"⟩ [])) :
    ∃ c, LookupList.get? ctx.ctors name = some c ∧ c.IsBoolCtor := by
  obtain ⟨cE, hlookE, hbE⟩ := Ctor.isBoolCtor_of_typeOfHM h
  have hlookE' : LookupList.get? (CtorEnv.eraseBounds ctx.ctors) name = some cE := by
    simpa [Ctx.eraseBounds] using hlookE
  rw [CtorEnv.eraseBounds_get?] at hlookE'
  obtain ⟨c, hlk, hceq⟩ :
      ∃ c, LookupList.get? ctx.ctors name = some c ∧ Ctor.eraseBounds c = cE := by
    cases hlk : LookupList.get? ctx.ctors name with
    | none => simp [hlk] at hlookE'
    | some c =>
      rw [hlk] at hlookE'
      simp only [Option.map_some, Option.some.injEq] at hlookE'
      exact ⟨c, rfl, hlookE'⟩
  refine ⟨c, hlk, ?_⟩
  exact Ctor.IsBoolCtor.of_eraseBounds (by simpa [hceq] using hbE)

/-- `M'` is at least as general as `M`: every instantiation of `M` is also an
    instantiation of `M'`. (Defined before `Infer` because `Infer.letRec`'s ceiling
    premise uses it.) -/
def PolyTy.Generalizes (M' M : PolyTy) : Prop :=
  ∀ tyArgs ty, (∀ t ∈ tyArgs, t.IsLC) → InstantiatesBy tyArgs M.body ty →
    ∃ tyArgs', (∀ t ∈ tyArgs', t.IsLC) ∧ InstantiatesBy tyArgs' M'.body ty

/-- The `letRec` ceiling premise: for every ANNOTATED member, the solved-and-
    generalised scheme `genGroup G τⱼ` is at least as general as the annotation
    `σⱼ` — an over-claiming annotation is rejected, an under-claiming one passes
    (with the body seeing the less-general annotation as a ceiling). Positional,
    via `List.Forall₂` over `anns` and the solved specs. -/
def RecSpecs.ceilingOK (G : List Nat) (anns : List (Option PolyTy)) (specs : List RecSpec) : Prop :=
  List.Forall₂ (fun a s => match a with
    | some σ => PolyTy.Generalizes (PolyTy.eraseBounds (RecSpec.bodyScheme G s)) (PolyTy.eraseBounds σ)
    | none => True) anns specs

/-- The `letRec` BODY environment under the ceiling: annotated members at their
    (opened) annotation, unannotated members at their generalised scheme
    `genGroup G τⱼ`. -/
def RecSpecs.ceilingSchemes (G : List Nat) (anns : List (Option PolyTy)) (specs : List RecSpec) : List PolyTy :=
  (anns.zip specs).map (fun p => match p.1 with
    | some σ => σ
    | none => RecSpec.bodyScheme G p.2)

/-! Algorithm W as a type-directed **elaboration** relation: the subject `eIn` is
    the unelaborated skeleton and the new output index `eOut` carries the elaborated
    (type-passing) term. The runnable term is `eOut.substTyFvars S`. Mutually defined
    with `InferBranches`/`InferRecGroup` (the `match_`/`letRec` threaders), which
    each thread out their elaborated sub-terms. -/
mutual
inductive Infer : Nat → Ctx → Expr → Nat → Subst → Ty → Prop
  | primLitUnit {Φ ctx} :
    Infer Φ ctx (.primLit .unit) Φ [] (.prim .unit)
  | primLitInt {Φ ctx n} :
    Infer Φ ctx (.primLit (.int n)) Φ [] (.prim .int)
  | primLitNat {Φ ctx n} :
    Infer Φ ctx (.primLit (.nat n)) Φ [] (.prim .nat)
  | primLitChar {Φ ctx c} :
    Infer Φ ctx (.primLit (.char c)) Φ [] (.prim .char)
  | primBinOpIntAdd {Φ ctx} :
    Infer Φ ctx (.primBinOp .intAdd) Φ []
      (.arrow (.prim .int) (.arrow (.prim .int) (.prim .int)))
  | primBinOpIntSub {Φ ctx} :
    Infer Φ ctx (.primBinOp .intSub) Φ []
      (.arrow (.prim .int) (.arrow (.prim .int) (.prim .int)))
  | primBinOpIntLt {Φ ctx trueC falseC} :
    LookupList.get? ctx.ctors ⟨"True"⟩  = some trueC → trueC.IsBoolCtor →
    LookupList.get? ctx.ctors ⟨"False"⟩ = some falseC → falseC.IsBoolCtor →
    Infer Φ ctx (.primBinOp .intLt) Φ []
      (.arrow (.prim .int) (.arrow (.prim .int) (.customTy ⟨"Bool"⟩ [])))
  | primBinOpCharLt {Φ ctx trueC falseC} :
    LookupList.get? ctx.ctors ⟨"True"⟩  = some trueC → trueC.IsBoolCtor →
    LookupList.get? ctx.ctors ⟨"False"⟩ = some falseC → falseC.IsBoolCtor →
    Infer Φ ctx (.primBinOp .charLt) Φ []
      (.arrow (.prim .char) (.arrow (.prim .char) (.customTy ⟨"Bool"⟩ [])))
  | lambda {Φ ctx ann paramTy body Φ₀ Φ' S τb} :
    LamSeed Φ ann paramTy Φ₀ →
    Infer Φ₀ { ctx with env := PolyTy.mkTrivial paramTy :: ctx.env } body Φ' S τb →
    Infer Φ ctx (.lambda ann body) Φ' S (.arrow (S.onTy paramTy) τb)
  | app {Φ ctx f arg Φ₁ Φ₂ S₁ S₂ S₃ τf τa} :
    Infer Φ ctx f Φ₁ S₁ τf →
    Infer Φ₁ (S₁.onCtx ctx) arg Φ₂ S₂ τa →
    UnifyRel (S₂.onTy τf) (.arrow τa (.fvar Φ₂)) S₃ →
    Infer Φ ctx (.app f arg) (Φ₂ + 1) (S₁ ++ S₂ ++ S₃) (S₃.onTy (.fvar Φ₂))
  | var {Φ ctx i polyTy} :
    ctx.env[i]? = some polyTy →
    Infer Φ ctx (.var i) (Φ + polyTy.paramCount) []
      (polyTy.openVars (freshVars Φ polyTy.paramCount))
  | ctor {Φ ctx name ctor} :
    LookupList.get? ctx.ctors name = some ctor →
    Infer Φ ctx (.ctor name) (Φ + ctor.paramCount) []
      (ctor.toTy.openVars (freshVars Φ ctor.paramCount))
  | letIn {Φ ctx rhs body Φ₁ Φ₂ S₁ S₂ τ₁ τ₂} :
    Infer Φ ctx rhs Φ₁ S₁ τ₁ →
    Infer Φ₁
      { (S₁.onCtx ctx) with
        env := genScheme rhs.tyFreeVars (S₁.onCtx ctx).env τ₁ :: (S₁.onCtx ctx).env }
      body Φ₂ S₂ τ₂ →
    Infer Φ ctx (.letIn none rhs body) Φ₂ (S₁ ++ S₂) τ₂
  /-- Annotated `let` (scoped type variables, D2 ordering). The bound scheme is
      the annotation `σ` (`σ.WF`; it MAY carry free type vars — outer scoped
      vars). Allocate `σ`'s skolems `Ys = freshVars Φ σ.paramCount` **first**, then
      infer the bound expression already opened at `Ys` (`rhs.openTyVars Ys`,
      matching the spec's `openBoundTyVars`), so its scoped vars resolve to the
      rigid `Ys`. Unify the rhs type `τ₁` against `σ.openVars Ys` (both may mention
      `Ys`), producing `Schk`. Escape conditions keep `Ys` rigid: none is bound by
      the **whole** rhs+unify substitution `S₁ ++ Schk` (so the signature is no
      more general than `rhs` actually is), and none leaks into the threaded body
      context. -/
  | letInAnn {Φ N ctx σ rhs body Φ₁ Φ₂ S₁ Schk S₂ τ₁ τ₂} :
    σ.WF →
    Φ ≤ N →
    Infer (N + σ.paramCount) ctx (rhs.openTyVars (freshVars N σ.paramCount)) Φ₁ S₁ τ₁ →
    UnifyRel τ₁ (σ.openVars (freshVars N σ.paramCount)) Schk →
    (∀ y ∈ freshVars N σ.paramCount, y ∉ (S₁ ++ Schk).map Prod.fst) →
    (∀ y ∈ freshVars N σ.paramCount, y ∉ (Schk.onCtx (S₁.onCtx ctx)).env.freeVars) →
    Infer Φ₁
      { (Schk.onCtx (S₁.onCtx ctx)) with env := σ :: (Schk.onCtx (S₁.onCtx ctx)).env }
      body Φ₂ S₂ τ₂ →
    Infer Φ ctx (.letIn (some σ) rhs body) Φ₂ (S₁ ++ Schk ++ S₂) τ₂
  | match_ {Φ ctx scrut branches Φ₁ Φ₂ S₁ S₂ τs} :
    Infer Φ ctx scrut Φ₁ S₁ τs →
    branches ≠ [] →
    InferBranches (Φ₁ + 1) (S₁.onCtx ctx) τs (.fvar Φ₁) branches Φ₂ S₂ →
    Infer Φ ctx (.match_ scrut branches) Φ₂ (S₁ ++ S₂) (S₂.onTy (.fvar Φ₁))
  /-- (Mutually) recursive binding group with **per-binding optional annotations**,
      Damas–Milner monomorphic recursion: EVERY member — annotated or not — is
      unified at a fresh monotype (`RecSpec.init` emits all-`.mono`), the solved
      monotypes are generalised over the shared pool `G` for the BODY, and each
      annotation acts as a **ceiling**: it must be generalised *by* the solved
      scheme (`RecSpecs.ceilingOK` — an over-claiming annotation is rejected), and
      the body sees the annotation (`genGroup G τᵢ` when unannotated) via
      `RecSpecs.ceilingSchemes`. -/
  | letRec {Φ ctx anns bindings body Φ₁ Φ₂ S₁ S₂ τ₂} :
    (∀ σ, some σ ∈ anns → σ.WF) →
    InferRecGroup (Φ + bindings.length)
        { ctx with env := (RecSpec.init Φ anns).map (RecSpec.rhsEntry [] []) ++ ctx.env }
        bindings
        (RecSpec.init Φ anns)
        Φ₁ S₁ →
    RecSpecs.ceilingOK
        (genGroupVars (RecGroup.rigidVars anns bindings) (S₁.onCtx ctx).env
          (RecSpecs.monoTys ((RecSpec.init Φ anns).map (RecSpec.onSubst S₁))))
        anns
        ((RecSpec.init Φ anns).map (RecSpec.onSubst S₁)) →
    Infer Φ₁
      { (S₁.onCtx ctx) with
        env := RecSpecs.ceilingSchemes
                 (genGroupVars (RecGroup.rigidVars anns bindings) (S₁.onCtx ctx).env
                   (RecSpecs.monoTys ((RecSpec.init Φ anns).map (RecSpec.onSubst S₁))))
                 anns
                 ((RecSpec.init Φ anns).map (RecSpec.onSubst S₁))
               ++ (S₁.onCtx ctx).env }
      body Φ₂ S₂ τ₂ →
    Infer Φ ctx (.letRec anns bindings body) Φ₂ (S₁ ++ S₂) τ₂

/-- Threads inference through a `match_`'s branch list. Carries the scrutinee type
    `scrutTy` (which each *named* pattern constrains to its ADT by unifying it with a
    fresh `customTy` instance) and a running result type `ρ` that each branch body's
    type is unified against, with substitutions propagated to the next branch. An
    all-wildcard list leaves `scrutTy` free. The output index threads the elaborated
    branch list. -/
inductive InferBranches :
    Nat → Ctx → Ty → Ty → List (MatchPattern × Expr) → Nat → Subst → Prop
  | nil {Φ ctx scrutTy ρ} :
    InferBranches Φ ctx scrutTy ρ [] Φ []
  | cons {Φ ctx scrutTy ρ c n body rest ctor Φ₁ Φ₂ S₀ S₁ S₂ S₃ τb} :
    LookupList.get? ctx.ctors c = some ctor →
    n = ctor.contents.length →
    UnifyRel scrutTy
      (.customTy ctor.tyName ((freshVars Φ ctor.paramCount).map (Ty.fvar ·))) S₀ →
    Infer (Φ + ctor.paramCount)
      { (S₀.onCtx ctx) with
        env := (ctor.contents.map (Ty.openWith
            (((freshVars Φ ctor.paramCount).map (Ty.fvar ·)).map S₀.onTy))).map PolyTy.mkTrivial
          ++ (S₀.onCtx ctx).env }
      body Φ₁ S₁ τb →
    UnifyRel τb (S₁.onTy (S₀.onTy ρ)) S₂ →
    InferBranches Φ₁ (S₂.onCtx (S₁.onCtx (S₀.onCtx ctx)))
      (S₂.onTy (S₁.onTy (S₀.onTy scrutTy))) (S₂.onTy (S₁.onTy (S₀.onTy ρ))) rest Φ₂ S₃ →
    InferBranches Φ ctx scrutTy ρ ((.named c n, body) :: rest) Φ₂ (S₀ ++ S₁ ++ S₂ ++ S₃)
  /-- A wildcard branch: infer `body` in the *unextended* context (it binds
      nothing) and imposes no constraint on `scrutTy`; unify its type against the
      running result type `ρ`, continue. -/
  | consWild {Φ ctx scrutTy ρ body rest Φ₁ Φ₂ S₁ S₂ S₃ τb} :
    Infer Φ ctx body Φ₁ S₁ τb →
    UnifyRel τb (S₁.onTy ρ) S₂ →
    InferBranches Φ₁ (S₂.onCtx (S₁.onCtx ctx))
      (S₂.onTy (S₁.onTy scrutTy)) (S₂.onTy (S₁.onTy ρ)) rest Φ₂ S₃ →
    InferBranches Φ ctx scrutTy ρ ((.wildcard, body) :: rest) Φ₂ (S₁ ++ S₂ ++ S₃)

/-- Threads inference through a `letRec`'s recursive group, carrying the per-binding
    solved-so-far `specs : List RecSpec` (the fusion of the old monomorphic
    `InferRecGroup` and annotated `InferRecGroupAnn`). Two cons shapes:

    - `consMono` (old `InferRecGroup.cons`): the head member's target monotype is
      `τ` (a `mono` spec's stored monotype); infer the binding as stored, unify its
      type against `S₁.onTy τ`, then push the accumulated substitution `S₁ ++ S₂`
      through the REMAINING specs via `RecSpec.onSubst` (monos move, schemes stay
      rigid); output the raw `eOut`.
    - `consPoly` (old `InferRecGroupAnn.cons`): the head member is a `poly σ`
      spec; skolemise `σ` (`Ys = freshVars N σ.paramCount`), infer
      `e.openTyVars Ys` against `σ.openVars Ys` (→ `Schk`), escape-check `Ys`
      rigid (none bound by `S₁ ++ Schk`; none leaking into the threaded env — which
      now also contains the mono βs, so this ALSO rejects skolem-into-pool leaks),
      thread `S₁ ++ Schk` through the remaining specs, and emit the binding closed
      back over `Ys` (after applying `S₁ ++ Schk`). -/
inductive InferRecGroup : Nat → Ctx → List Expr → List RecSpec → Nat → Subst → Prop
  | nil {Φ ctx} : InferRecGroup Φ ctx [] [] Φ []
  | consMono {Φ ctx e rest τ specs Φ₁ Φ₂ S₁ S₂ S₃ τ'} :
    Infer Φ ctx e Φ₁ S₁ τ' →
    UnifyRel τ' (S₁.onTy τ) S₂ →
    InferRecGroup Φ₁ (S₂.onCtx (S₁.onCtx ctx)) rest
      (specs.map (RecSpec.onSubst (S₁ ++ S₂))) Φ₂ S₃ →
    InferRecGroup Φ ctx (e :: rest) (.mono τ :: specs) Φ₂ (S₁ ++ S₂ ++ S₃)
  | consPoly {Φ N ctx σ specs e rest Φ₁ Φ₂ S₁ Schk S₂ τ} :
    Φ ≤ N →
    Infer (N + σ.paramCount) ctx (e.openTyVars (freshVars N σ.paramCount)) Φ₁ S₁ τ →
    UnifyRel τ (σ.openVars (freshVars N σ.paramCount)) Schk →
    (∀ y ∈ freshVars N σ.paramCount, y ∉ (S₁ ++ Schk).map Prod.fst) →
    (∀ y ∈ freshVars N σ.paramCount, y ∉ (Schk.onCtx (S₁.onCtx ctx)).env.freeVars) →
    InferRecGroup Φ₁ (Schk.onCtx (S₁.onCtx ctx)) rest
      (specs.map (RecSpec.onSubst (S₁ ++ Schk))) Φ₂ S₂ →
    InferRecGroup Φ ctx (e :: rest) (.poly σ :: specs) Φ₂ (S₁ ++ Schk ++ S₂)
end


/-! ### `NoRecAnn` RETIRED (Phase A).

The whole `NoRecAnn` preservation family (`closeTyVarsAux`/`closeTyVars`/
`letRecElab(Nest)_noRecAnn`/`substTyFvar(s)_noRecAnn`/`substTyFvar_tyBvarBounded`)
is gone: the fused `letRec` node subsumes `letRecAnn` and `open`/`close` descend
into scheme-annotation bodies symmetrically, so no elaboration path needs a
`letRecAnn`-free witness. The `substTyFvars`-preserves-`TyBvarBounded` fact
survives (fused, below); its old `substTyFvar` single-step sibling was only
scaffolding for it and is deleted. -/

/-- A scheme's body is preserved by `PolyTy.substFvars` (only the body is rewritten). -/
theorem PolyTy.body_substFvars {S : List (Nat × Ty)} {σ : PolyTy} :
    (PolyTy.substFvars S σ).body = Ty.substFvars S σ.body := by
  induction S generalizing σ with
  | nil => rfl
  | cons hd tl ih => obtain ⟨Z, U⟩ := hd; rw [PolyTy.substFvars, ih, PolyTy.substFvar, Ty.substFvars]

/-- `PolyTy.substFvars` keeps the scheme's parameter count. -/
theorem PolyTy.paramCount_substFvars {S : List (Nat × Ty)} {σ : PolyTy} :
    (PolyTy.substFvars S σ).paramCount = σ.paramCount := by
  induction S generalizing σ with
  | nil => rfl
  | cons hd tl ih => obtain ⟨Z, U⟩ := hd; rw [PolyTy.substFvars, ih, PolyTy.substFvar]

/-- A whole substitution with LC images preserves the type-bvar bound. -/
theorem ContainsBvarsUpTo.substFvars {S : List (Nat × Ty)} (hS : ∀ p ∈ S, p.2.IsLC)
    {n : Nat} {t : Ty} (ht : ContainsBvarsUpTo n t) :
    ContainsBvarsUpTo n (Ty.substFvars S t) := by
  induction S generalizing t with
  | nil => exact ht
  | cons hd S' ih =>
    obtain ⟨Z, U⟩ := hd
    exact ih (fun p hp => hS p (List.mem_cons_of_mem _ hp))
      (ContainsBvarsUpTo.substFvar (hS (Z, U) List.mem_cons_self) ht)

/-- `RecAnn.substFvars` preserves the shield depth (`paramCount` is untouched). -/
theorem RecAnn.params_substFvars {S : List (Nat × Ty)} {a : Option PolyTy} :
    RecAnn.params (RecAnn.substFvars S a) = RecAnn.params a := by
  cases a with
  | none => rw [RecAnn.substFvars_none]
  | some σ =>
    rw [RecAnn.substFvars_some]
    exact PolyTy.paramCount_substFvars

/-- The fused-group `substTyFvars` preserves the shielded per-binding bound
    (the anns' shield depths are `paramCount`-preserved). -/
private theorem RecGroup.substTyFvars_tyBvarBounded_aux {S : List (Nat × Ty)} :
    ∀ (anns : List (Option PolyTy)) (bs : List Expr) (d : Nat),
      (∀ e ∈ bs, ∀ d', e.TyBvarBounded d' → (e.substTyFvars S).TyBvarBounded d') →
      Expr.TyBvarBounded.RecGroup d anns bs →
      Expr.TyBvarBounded.RecGroup d (anns.map (RecAnn.substFvars S))
        (bs.map (·.substTyFvars S)) := by
  intro anns bs
  induction bs generalizing anns with
  | nil => intro d _ _; cases anns <;> exact trivial
  | cons hd tl ih =>
    intro d ihB hbb
    cases anns with
    | nil =>
      exact ⟨ihB hd List.mem_cons_self d hbb.1,
        ih [] d (fun e he => ihB e (List.mem_cons_of_mem _ he)) hbb.2⟩
    | cons a as =>
      refine ⟨?_, ih as d (fun e he => ihB e (List.mem_cons_of_mem _ he)) hbb.2⟩
      rw [RecAnn.params_substFvars]
      exact ihB hd List.mem_cons_self (d + RecAnn.params a) hbb.1

/-- A type-substitution with LC images preserves `TyBvarBounded`: it only rewrites
    type annotations by LC types (no dangling bvars), through the fused `letRec`'s
    anns by `RecAnn.substFvars` (shield depths preserved). -/
theorem Expr.substTyFvars_tyBvarBounded {S : List (Nat × Ty)} (hS : ∀ p ∈ S, p.2.IsLC) :
    ∀ {e : Expr} {d : Nat}, e.TyBvarBounded d → (e.substTyFvars S).TyBvarBounded d := by
  intro e
  induction e using Expr.rec_strong with
  | primLit p =>
    intro d _
    rw [Expr.substTyFvars_eq_self_of_not_mem_tyFreeVars (by simp [Expr.tyFreeVars])]; trivial
  | primBinOp op =>
    intro d _
    rw [Expr.substTyFvars_eq_self_of_not_mem_tyFreeVars (by simp [Expr.tyFreeVars])]; trivial
  | ctor c =>
    intro d _
    rw [Expr.substTyFvars_eq_self_of_not_mem_tyFreeVars (by simp [Expr.tyFreeVars])]; trivial
  | var i => intro d hb; rw [Expr.substTyFvars_var]; exact hb
  | lambda ann body ih =>
    intro d hb
    rw [Expr.substTyFvars_lambda]
    refine ⟨?_, ih hb.2⟩
    intro t ht
    obtain ⟨t', ht', rfl⟩ := Option.map_eq_some_iff.mp ht
    exact ContainsBvarsUpTo.substFvars hS (hb.1 t' ht')
  | app f arg ihf iharg =>
    intro d hb
    rw [Expr.substTyFvars_app]
    exact ⟨ihf hb.1, iharg hb.2⟩
  | letIn ann rhs body ihr ihb =>
    intro d hb
    rw [Expr.substTyFvars_letIn]
    cases ann with
    | none => exact ⟨ihr hb.1, ihb hb.2⟩
    | some σ =>
      exact ⟨ContainsBvarsUpTo.substFvars hS hb.1, ihr hb.2.1, ihb hb.2.2⟩
  | match_ scrut branches ihs ihbr =>
    intro d hb
    rw [Expr.substTyFvars_match]
    refine ⟨ihs hb.1, ?_⟩
    rw [Expr.TyBvarBounded.BranchList_iff]
    intro p b hpb
    obtain ⟨⟨p', b'⟩, hmem, heq⟩ := List.mem_map.mp hpb
    simp only [Prod.mk.injEq] at heq
    obtain ⟨_, rfl⟩ := heq
    exact ihbr p' b' hmem (Expr.TyBvarBounded.BranchList_iff.mp hb.2 p' b' hmem)
  | letRec anns bindings body ihbs ihb =>
    intro d hb
    obtain ⟨hsch, hrg, hbody⟩ := hb
    rw [Expr.substTyFvars_letRec]
    refine ⟨?_,
      RecGroup.substTyFvars_tyBvarBounded_aux anns bindings d (fun e he d' => ihbs e he) hrg,
      ihb hbody⟩
    intro σ' hσ'
    obtain ⟨a, ha, haeq⟩ := List.mem_map.mp hσ'
    cases a with
    | none => rw [RecAnn.substFvars_none] at haeq; exact absurd haeq (by simp)
    | some σ0 =>
      rw [RecAnn.substFvars_some] at haeq
      injection haeq with h'
      subst h'
      rw [PolyTy.body_substFvars, PolyTy.paramCount_substFvars]
      exact ContainsBvarsUpTo.substFvars hS (hsch σ0 ha)

/-! ### Invariant layer for `Infer` soundness -/

/-! The fresh-variable frontier only ever grows (`Infer.frontier_le`). -/
mutual
theorem Infer.frontier_le {Φ ctx e Φ' S τ} (h : Infer Φ ctx e Φ' S τ) : Φ ≤ Φ' := by
  cases h with
  | primLitUnit => omega
  | primLitInt => omega
  | primLitNat => omega
  | primLitChar => omega
  | primBinOpIntAdd => omega
  | primBinOpIntSub => omega
  | primBinOpIntLt _ _ _ _ => omega
  | primBinOpCharLt _ _ _ _ => omega
  | lambda hseed hbody => have := Infer.frontier_le hbody; have := hseed.le; omega
  | app hf harg _ => have := Infer.frontier_le hf; have := Infer.frontier_le harg; omega
  | var => omega
  | ctor => omega
  | letIn hrhs hbody => have := Infer.frontier_le hrhs; have := Infer.frontier_le hbody; omega
  | letInAnn _ _hΦN hrhs _ _ _ hbody =>
    have := Infer.frontier_le hrhs; have := Infer.frontier_le hbody; omega
  | match_ hscrut _ hbr =>
    have := Infer.frontier_le hscrut; have := InferBranches.frontier_le hbr; omega
  | letRec _ hgroup _ hbody =>
    have := InferRecGroup.frontier_le hgroup; have := Infer.frontier_le hbody; omega
termination_by e.size
decreasing_by
  all_goals (try subst_vars; try simp only [Expr.size, Expr.size_openTyVars]; omega)
theorem InferBranches.frontier_le {Φ ctx scrutTy ρ brs Φ' S}
    (h : InferBranches Φ ctx scrutTy ρ brs Φ' S) :
    Φ ≤ Φ' := by
  cases h with
  | nil => omega
  | cons _ _ _ hbody _ hrest =>
    have := Infer.frontier_le hbody; have := InferBranches.frontier_le hrest; omega
  | consWild hbody _ hrest =>
    have := Infer.frontier_le hbody; have := InferBranches.frontier_le hrest; omega
termination_by Expr.sizeBranches brs
decreasing_by
  all_goals (try subst_vars; try simp only [Expr.sizeBranches]; omega)
theorem InferRecGroup.frontier_le {Φ ctx bindings specs Φ' S}
    (h : InferRecGroup Φ ctx bindings specs Φ' S) : Φ ≤ Φ' := by
  cases h with
  | nil => omega
  | consMono he _ hrest =>
    have := Infer.frontier_le he; have := InferRecGroup.frontier_le hrest; omega
  | consPoly hΦN hinfer _ _ _ hrest =>
    have := Infer.frontier_le hinfer; have := InferRecGroup.frontier_le hrest; omega
termination_by Expr.sizeRecGroup bindings
decreasing_by
  all_goals (try subst_vars; try simp only [Expr.sizeRecGroup, Expr.size_openTyVars]; omega)
end

/-! DELETED: `InferRecGroup.bindingsOut_length` (referenced the removed elaborated-output
    index `bindingsOut`; its only consumer `InferRecGroup.eOut_tyBvarBounded` was deleted
    in the `eOut`-drop pass). -/

/-- An `InferRecGroup` derivation has matching binding/target lengths. -/
theorem InferRecGroup.length_eq {Φ ctx bindings specs Φ' S}
    (h : InferRecGroup Φ ctx bindings specs Φ' S) : bindings.length = specs.length := by
  induction bindings generalizing Φ ctx specs Φ' S with
  | nil => cases h with | nil => rfl
  | cons e rest ih =>
    cases h with
    | consMono _ _ hrest =>
      have := ih hrest; simp only [List.length_cons, List.length_map] at this ⊢; omega
    | consPoly _ _ _ _ _ hrest =>
      have := ih hrest; simp only [List.length_cons, List.length_map] at this ⊢; omega

/-! ### Scoped-variable regime (replaces the old closed-annotation invariants)

The closed-regime invariants `Infer.tyFreeVars_eq_nil` and the provisional
`Infer.openTyVarsAux_eq_self` are gone. With D2 the bound expression is inferred
*already opened* at the rigid skolems, so an accepted term's annotation free vars
are no longer empty — they are the in-scope skolems. Soundness now threads an
ambient rigid-skolem set `K` (the substitution provably avoids `K`, via the escape
discipline), and the cofinite premise is recovered by renaming `K` to fresh names
through `Expr.substTyFvars_zip_openTyVars` (the Core bridge). -/

/-- A context is well-formed when every scheme in its env is well-formed. -/
def CtxWF (ctx : Ctx) : Prop := ∀ M ∈ ctx.env, M.WF

theorem freshVars_nodup {Φ k : Nat} : (freshVars Φ k).Nodup :=
  (List.nodup_range).map (fun _ _ h => by omega)

@[simp] theorem freshVars_length (Φ k : Nat) : (freshVars Φ k).length = k := by
  simp [freshVars]

/-- Every freshly-allocated name is at least the frontier `Φ`. Lets us conclude a
    skolem block `freshVars Φ k` is disjoint from any set of names below `Φ`
    (e.g. the ambient skolems `K`, all introduced at earlier frontiers). -/
theorem freshVars_ge {Φ k : Nat} : ∀ y ∈ freshVars Φ k, Φ ≤ y := by
  intro y hy
  simp only [freshVars, List.mem_map, List.mem_range] at hy
  obtain ⟨i, _, rfl⟩ := hy
  omega

/-- Every freshly-allocated name is below the post-allocation frontier `Φ + k`. -/
theorem freshVars_lt {Φ k : Nat} : ∀ y ∈ freshVars Φ k, y < Φ + k := by
  intro y hy
  simp only [freshVars, List.mem_map, List.mem_range] at hy
  obtain ⟨i, hi, rfl⟩ := hy
  omega

/-- A whole substitution (LC replacements) preserves any bvar bound. -/
theorem Subst.onTy_containsBvars {S : Subst} (h_lc : ∀ p ∈ S, p.2.IsLC) :
    ∀ {n : Nat} {τ : Ty}, ContainsBvarsUpTo n τ → ContainsBvarsUpTo n (S.onTy τ) := by
  induction S with
  | nil => intro n τ hτ; simpa using hτ
  | cons hd S' ih =>
    obtain ⟨Z, U⟩ := hd
    have hU : U.IsLC := h_lc (Z, U) (List.mem_cons_self ..)
    have hS' : ∀ p ∈ S', p.2.IsLC := fun p hp => h_lc p (List.mem_cons_of_mem _ hp)
    intro n τ hτ
    rw [show ((Z, U) :: S') = [(Z, U)] ++ S' from rfl, Subst.onTy_append]
    exact ih hS' (ContainsBvarsUpTo.substFvar hU hτ)

/-- A whole substitution preserves scheme well-formedness. -/
theorem Subst.onPolyTy_wf {S : Subst} (h_lc : ∀ p ∈ S, p.2.IsLC) {M : PolyTy}
    (hM : M.WF) : (S.onPolyTy M).WF :=
  Subst.onTy_containsBvars h_lc hM

/-- A whole substitution preserves context well-formedness. -/
theorem Subst.onCtx_wf {S : Subst} (h_lc : ∀ p ∈ S, p.2.IsLC) {ctx : Ctx}
    (h : CtxWF ctx) : CtxWF (S.onCtx ctx) := by
  intro M hM
  simp only [Subst.onCtx, Subst.onEnv] at hM
  obtain ⟨M0, hM0, rfl⟩ := List.mem_map.mp hM
  exact Subst.onPolyTy_wf h_lc (h M0 hM0)

/-- Instantiating all bvars below `n` with LC types yields an LC type. -/
theorem Ty.instantiate_isLC {σ : Nat → Ty} {n : Nat}
    (hσ : ∀ i, i < n → (σ i).IsLC) {ty : Ty} (hty : ContainsBvarsUpTo n ty) :
    (ty.instantiate σ).IsLC := by
  induction ty using Ty.rec_strong with
  | prim p => exact .prim
  | bvar i => cases hty with | bvar hlt => exact hσ i hlt
  | fvar m => exact .fvar
  | arrow a b iha ihb => cases hty with | arrow ha hb => exact .arrow (iha ha) (ihb hb)
  | customTy nm tys ih =>
    cases hty with
    | customTy hall =>
      simp only [Ty.instantiate, TyList.instantiate_eq_map]
      apply ContainsBvarsUpTo.customTy
      intro t ht
      obtain ⟨t0, ht0, rfl⟩ := List.mem_map.mp ht
      exact ih t0 ht0 (hall t0 ht0)
  | bl lo hi e ih =>
    cases hty with
    | bl he =>
      simp only [Ty.instantiate]
      exact .bl (ih he)

/-- Opening a type whose bvars are `< Xs.length` with fresh names is LC. -/
theorem Ty.openVars_isLC {Xs : List Nat} {n : Nat} {ty : Ty}
    (hty : ContainsBvarsUpTo n ty) (hn : n ≤ Xs.length) :
    (Ty.openVars Xs ty).IsLC := by
  simp only [Ty.openVars]
  refine Ty.instantiate_isLC (fun i hi => ?_) hty
  rw [List.getElem?_eq_getElem (show i < Xs.length by omega)]
  exact .fvar

/-- Opening a well-formed scheme with enough fresh names is LC. -/
theorem PolyTy.openVars_isLC {Xs : List Nat} {M : PolyTy}
    (hM : M.WF) (hn : M.paramCount ≤ Xs.length) : (M.openVars Xs).IsLC :=
  Ty.openVars_isLC hM hn

/-- Opening a type whose bvars are `< n ≤ |Vs|` with LC args is LC. -/
theorem Ty.openWith_isLC {Vs : List Ty} {n : Nat} {X : Ty}
    (hVs : ∀ v ∈ Vs, v.IsLC) (hX : ContainsBvarsUpTo n X) (hn : n ≤ Vs.length) :
    (Ty.openWith Vs X).IsLC := by
  simp only [Ty.openWith]
  refine Ty.instantiate_isLC (fun i hi => ?_) hX
  simp only [List.getElem?_eq_getElem (show i < Vs.length by omega), Option.getD_some]
  exact hVs _ (List.getElem_mem _)

/-- A `match_` branch's pattern bindings (ctor contents opened with the type
    args) extend a WF context to a WF context, given LC type args of the right
    arity. -/
theorem branchBindings_wf {ctorr : Ctor} {ta : List Ty} {ctx : Ctx}
    (hctx : CtxWF ctx) (hta : ∀ t ∈ ta, t.IsLC) (hpc : ctorr.paramCount = ta.length) :
    CtxWF { ctx with
      env := (ctorr.contents.map (Ty.openWith ta)).map PolyTy.mkTrivial ++ ctx.env } := by
  intro M hM
  rw [List.mem_append] at hM
  rcases hM with hM | hM
  · obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hM
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp ht
    show (Ty.openWith ta c).IsLC
    exact Ty.openWith_isLC hta (hpc ▸ ctorr.bound c hc) (le_of_eq hpc)
  · exact hctx M hM

/-! Local-closedness invariant (`Infer.lc`): from a well-formed context, `Infer`
    yields an LC type and a substitution whose replacements are all LC. (Context
    well-formedness of `S.onCtx ctx` follows separately via `Subst.onCtx_wf`.) -/
mutual
theorem Infer.lc {Φ ctx e Φ' S τ} (h : Infer Φ ctx e Φ' S τ) :
    CtxWF ctx → τ.IsLC ∧ (∀ p ∈ S, p.2.IsLC) := by
  cases h with
  | primLitUnit => intro _; exact ⟨.prim, by simp⟩
  | primLitInt => intro _; exact ⟨.prim, by simp⟩
  | primLitNat => intro _; exact ⟨.prim, by simp⟩
  | primLitChar => intro _; exact ⟨.prim, by simp⟩
  | primBinOpIntAdd => intro _; exact ⟨.arrow .prim (.arrow .prim .prim), by simp⟩
  | primBinOpIntSub => intro _; exact ⟨.arrow .prim (.arrow .prim .prim), by simp⟩
  | primBinOpIntLt _ _ _ _ => intro _; exact ⟨.arrow .prim (.arrow .prim (.customTy (by simp))), by simp⟩
  | primBinOpCharLt _ _ _ _ => intro _; exact ⟨.arrow .prim (.arrow .prim (.customTy (by simp))), by simp⟩
  | lambda hseed hbody =>
    intro hctx
    cases hseed with
    | none =>
      obtain ⟨hb_lc, hb_s⟩ := Infer.lc hbody (by
        intro M hM; rcases List.mem_cons.mp hM with rfl | hM
        · exact ContainsBvarsUpTo.fvar
        · exact hctx M hM)
      exact ⟨.arrow (Subst.onTy_lc hb_s ContainsBvarsUpTo.fvar) hb_lc, hb_s⟩
    | some _ hpc =>
      obtain ⟨hb_lc, hb_s⟩ := Infer.lc hbody (by
        intro M hM; rcases List.mem_cons.mp hM with rfl | hM
        · exact hpc
        · exact hctx M hM)
      exact ⟨.arrow (Subst.onTy_lc hb_s hpc) hb_lc, hb_s⟩
  | app hf harg huni =>
    intro hctx
    obtain ⟨hf_lc, hf_s⟩ := Infer.lc hf hctx
    obtain ⟨harg_lc, harg_s⟩ := Infer.lc harg (Subst.onCtx_wf hf_s hctx)
    have hs3 := huni.lc (Subst.onTy_lc harg_s hf_lc) (.arrow harg_lc ContainsBvarsUpTo.fvar)
    refine ⟨Subst.onTy_lc hs3 ContainsBvarsUpTo.fvar, ?_⟩
    intro p hp; rw [List.mem_append, List.mem_append] at hp
    rcases hp with (hp | hp) | hp
    · exact hf_s p hp
    · exact harg_s p hp
    · exact hs3 p hp
  | var hlook =>
    intro hctx
    exact ⟨PolyTy.openVars_isLC (hctx _ (List.mem_of_getElem? hlook)) (by simp), by simp⟩
  | ctor hlook =>
    intro _
    exact ⟨PolyTy.openVars_isLC (Ctor.toTy_wf _) (by simp [Ctor.toTy]), by simp⟩
  | letIn hrhs hbody =>
    intro hctx
    obtain ⟨hrhs_lc, hrhs_s⟩ := Infer.lc hrhs hctx
    obtain ⟨hbody_lc, hbody_s⟩ := Infer.lc hbody (by
      intro M hM
      rcases List.mem_cons.mp hM with rfl | hM
      · exact genScheme_wf hrhs_lc
      · exact (Subst.onCtx_wf hrhs_s hctx) M hM)
    refine ⟨hbody_lc, ?_⟩
    intro p hp; rw [List.mem_append] at hp
    rcases hp with hp | hp
    · exact hrhs_s p hp
    · exact hbody_s p hp
  | letInAnn hσwf _hΦN hrhs huni _hesc1 _hesc2 hbody =>
    intro hctx
    expose_names
    obtain ⟨hrhs_lc, hrhs_s⟩ := Infer.lc hrhs hctx
    have hSchk_lc : ∀ p ∈ Schk, p.2.IsLC :=
      UnifyRel.lc huni hrhs_lc (PolyTy.openVars_isLC hσwf (by simp))
    obtain ⟨hbody_lc, hbody_s⟩ := Infer.lc hbody (by
      intro M hM
      rcases List.mem_cons.mp hM with rfl | hM
      · exact hσwf
      · exact (Subst.onCtx_wf hSchk_lc (Subst.onCtx_wf hrhs_s hctx)) M hM)
    refine ⟨hbody_lc, ?_⟩
    intro p hp; rw [List.mem_append, List.mem_append] at hp
    rcases hp with (hp | hp) | hp
    · exact hrhs_s p hp
    · exact hSchk_lc p hp
    · exact hbody_s p hp
  | match_ hscrut hne hbr =>
    intro hctx
    obtain ⟨hτs_lc, hS₁⟩ := Infer.lc hscrut hctx
    obtain ⟨hρ_lc, hS₂⟩ := InferBranches.lc hbr
      (Subst.onCtx_wf hS₁ hctx)
      hτs_lc
      ContainsBvarsUpTo.fvar
    refine ⟨hρ_lc, ?_⟩
    intro p hp; rw [List.mem_append] at hp
    rcases hp with hp | hp
    · exact hS₁ p hp
    · exact hS₂ p hp
  | letRec hwf hgroup hceiling hbody =>
    intro hctx
    expose_names
    have hspecs_lc : ∀ s ∈ RecSpec.init Φ anns, s.LC := by
      intro s hs
      rcases List.mem_iff_getElem.mp hs with ⟨j, hj, rfl⟩
      have hlenj : j < anns.length := by
        have h₁ := RecSpec.init_length Φ anns
        omega
      have hget : (RecSpec.init Φ anns)[j] = RecSpec.mono (.fvar (Φ + j)) := by
        have h₁ := List.getElem?_eq_getElem hj
        rw [RecSpec.init_getElem? Φ anns j, List.getElem?_eq_getElem hlenj] at h₁
        injection h₁ with hEq
        exact hEq.symm
      rw [hget]
      exact ContainsBvarsUpTo.fvar
    have hctxGroup : CtxWF
        { ctx with env := (RecSpec.init Φ anns).map (RecSpec.rhsEntry [] []) ++ ctx.env } := by
      intro M hM
      rcases List.mem_append.mp hM with hM1 | hM2
      · obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hM1
        exact RecSpec.rhsEntry_nil_wf (hspecs_lc s hs)
      · exact hctx M hM2
    have hS₁ : ∀ p ∈ S₁, p.2.IsLC := InferRecGroup.lc hgroup hctxGroup hspecs_lc
    have hbodyCtx : CtxWF
        { (S₁.onCtx ctx) with
          env := RecSpecs.ceilingSchemes
                   (genGroupVars (RecGroup.rigidVars anns bindings) (S₁.onCtx ctx).env
                     (RecSpecs.monoTys ((RecSpec.init Φ anns).map (RecSpec.onSubst S₁))))
                   anns
                   ((RecSpec.init Φ anns).map (RecSpec.onSubst S₁))
                 ++ (S₁.onCtx ctx).env } := by
      intro M hM
      rcases List.mem_append.mp hM with hM1 | hM2
      · obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hM1
        have hpa : p.1 ∈ anns := (List.of_mem_zip hp).1
        have hps : p.2 ∈ (RecSpec.init Φ anns).map (RecSpec.onSubst S₁) := (List.of_mem_zip hp).2
        cases p with
        | mk a s =>
          cases a with
          | some σ =>
            exact hwf σ hpa
          | none =>
            obtain ⟨s₀, hs₀, rfl⟩ := List.mem_map.mp hps
            cases s₀ with
            | mono τ =>
              exact PolyTy.genGroup_wf (Subst.onTy_lc hS₁ (hspecs_lc (.mono τ) hs₀))
            | poly σ' =>
              exact hspecs_lc (.poly σ') hs₀
      · exact Subst.onCtx_wf hS₁ hctx M hM2
    obtain ⟨hb_lc, hb_s⟩ := Infer.lc hbody hbodyCtx
    refine ⟨hb_lc, ?_⟩
    intro p hp; rw [List.mem_append] at hp
    rcases hp with hp | hp
    · exact hS₁ p hp
    · exact hb_s p hp
termination_by e.size
decreasing_by
  all_goals (try subst_vars; try simp only [Expr.size, Expr.size_openTyVars]; omega)
theorem InferBranches.lc {Φ ctx scrutTy ρ brs Φ' S}
    (h : InferBranches Φ ctx scrutTy ρ brs Φ' S)
    (hctx : CtxWF ctx) (hscrutTy : scrutTy.IsLC) (hρ : ρ.IsLC) :
    (S.onTy ρ).IsLC ∧ (∀ p ∈ S, p.2.IsLC) := by
  cases h with
  | nil => exact ⟨by simpa using hρ, by simp⟩
  | cons hlook hn huni0 hbody huni hrest =>
    have hS₀ := huni0.lc hscrutTy
      (.customTy (fun t ht => by obtain ⟨x, _, rfl⟩ := List.mem_map.mp ht; exact ContainsBvarsUpTo.fvar))
    obtain ⟨hτb_lc, hS₁⟩ := Infer.lc hbody
      (branchBindings_wf (Subst.onCtx_wf hS₀ hctx)
        (fun t ht => by
          obtain ⟨v, hv, rfl⟩ := List.mem_map.mp ht
          obtain ⟨x, _, rfl⟩ := List.mem_map.mp hv
          exact Subst.onTy_lc hS₀ ContainsBvarsUpTo.fvar)
        (by simp))
    have hS₂ := huni.lc hτb_lc (Subst.onTy_lc hS₁ (Subst.onTy_lc hS₀ hρ))
    obtain ⟨hres, hS₃⟩ := InferBranches.lc hrest
      (Subst.onCtx_wf hS₂ (Subst.onCtx_wf hS₁ (Subst.onCtx_wf hS₀ hctx)))
      (Subst.onTy_lc hS₂ (Subst.onTy_lc hS₁ (Subst.onTy_lc hS₀ hscrutTy)))
      (Subst.onTy_lc hS₂ (Subst.onTy_lc hS₁ (Subst.onTy_lc hS₀ hρ)))
    refine ⟨?_, ?_⟩
    · rw [Subst.onTy_append, Subst.onTy_append, Subst.onTy_append]; exact hres
    · intro p hp; rw [List.mem_append, List.mem_append, List.mem_append] at hp
      rcases hp with ((hp | hp) | hp) | hp
      · exact hS₀ p hp
      · exact hS₁ p hp
      · exact hS₂ p hp
      · exact hS₃ p hp
  | consWild hbody huni hrest =>
    obtain ⟨hτb_lc, hS₁⟩ := Infer.lc hbody hctx
    have hS₂ := huni.lc hτb_lc (Subst.onTy_lc hS₁ hρ)
    obtain ⟨hres, hS₃⟩ := InferBranches.lc hrest
      (Subst.onCtx_wf hS₂ (Subst.onCtx_wf hS₁ hctx))
      (Subst.onTy_lc hS₂ (Subst.onTy_lc hS₁ hscrutTy))
      (Subst.onTy_lc hS₂ (Subst.onTy_lc hS₁ hρ))
    refine ⟨?_, ?_⟩
    · rw [Subst.onTy_append, Subst.onTy_append]; exact hres
    · intro p hp; rw [List.mem_append, List.mem_append] at hp
      rcases hp with (hp | hp) | hp
      · exact hS₁ p hp
      · exact hS₂ p hp
      · exact hS₃ p hp
termination_by Expr.sizeBranches brs
decreasing_by
  all_goals (try subst_vars; try simp only [Expr.sizeBranches]; omega)
/-- Fused `InferRecGroup` local-closedness (consMono + consPoly): from a
    well-formed context and LC/WF specs, every replacement in the group's
    substitution is locally closed. -/
theorem InferRecGroup.lc {Φ ctx bindings specs Φ' S}
    (h : InferRecGroup Φ ctx bindings specs Φ' S)
    (hctx : CtxWF ctx) (hspecs : ∀ s ∈ specs, s.LC) :
    (∀ p ∈ S, p.2.IsLC) := by
  cases h with
  | nil => simp
  | consMono he huni hrest =>
    expose_names
    obtain ⟨hτ', hS₁⟩ := Infer.lc he hctx
    have hτ : τ.IsLC := hspecs (.mono τ) List.mem_cons_self
    have hS₂ := UnifyRel.lc huni hτ' (Subst.onTy_lc hS₁ hτ)
    have hS₃ := InferRecGroup.lc hrest
      (Subst.onCtx_wf hS₂ (Subst.onCtx_wf hS₁ hctx))
      (fun s' hs' => by
        obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hs'
        exact RecSpec.LC.onSubst (fun p hp => (List.mem_append.mp hp).elim (hS₁ p) (hS₂ p))
          (hspecs s (List.mem_cons_of_mem _ hs)))
    intro p hp; rw [List.mem_append, List.mem_append] at hp
    rcases hp with (hp | hp) | hp
    · exact hS₁ p hp
    · exact hS₂ p hp
    · exact hS₃ p hp
  | consPoly hΦN hinfer huni hesc1 hesc2 hrest =>
    expose_names
    obtain ⟨hτ, hS₁⟩ := Infer.lc hinfer hctx
    have hσwf : σ.WF := hspecs (.poly σ) List.mem_cons_self
    have hSchk := UnifyRel.lc huni hτ (PolyTy.openVars_isLC hσwf (by simp))
    have hS₂ := InferRecGroup.lc hrest
      (Subst.onCtx_wf hSchk (Subst.onCtx_wf hS₁ hctx))
      (fun s' hs' => by
        obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hs'
        exact RecSpec.LC.onSubst (fun p hp => (List.mem_append.mp hp).elim (hS₁ p) (hSchk p))
          (hspecs s (List.mem_cons_of_mem _ hs)))
    intro p hp; rw [List.mem_append, List.mem_append] at hp
    rcases hp with (hp | hp) | hp
    · exact hS₁ p hp
    · exact hSchk p hp
    · exact hS₂ p hp
termination_by Expr.sizeRecGroup bindings
decreasing_by
  all_goals (try subst_vars; try simp only [Expr.sizeRecGroup, Expr.size_openTyVars]; omega)
end

private theorem List.forall₂_self_map {α β} {R : α → β → Prop} {f : α → β} :
    ∀ {l : List α}, (∀ x ∈ l, R x (f x)) → List.Forall₂ R l (l.map f)
  | [], _ => .nil
  | _ :: _, h =>
    .cons (h _ (List.mem_cons_self ..))
      (List.forall₂_self_map (fun x hx => h x (List.mem_cons_of_mem _ hx)))

/-- Opening a scheme body (bvars `< Xs.length`) with fresh *names* is an
    instantiation by those names-as-`fvar`s. Bridges the `var` rule: the
    algorithm's `openVars` result is what the declarative `var` rule's
    `InstantiatesBy` premise demands. -/
theorem InstantiatesBy.openVars {Xs : List Nat} {n : Nat} {ty : Ty}
    (hty : ContainsBvarsUpTo n ty) (hn : n ≤ Xs.length) :
    InstantiatesBy (Xs.map (Ty.fvar ·)) ty (ty.openVars Xs) := by
  induction ty using Ty.rec_strong with
  | prim p => exact .prim
  | fvar m => exact .fvar
  | bvar i =>
    cases hty with
    | bvar hlt =>
      have hi : i < Xs.length := by omega
      simp only [Ty.openVars, Ty.instantiate, List.getElem?_eq_getElem hi, Option.elim_some]
      exact .bvar (by simp [List.getElem?_map, List.getElem?_eq_getElem hi])
  | arrow a b iha ihb => cases hty with | arrow ha hb => exact .arrow (iha ha) (ihb hb)
  | customTy nm tys ih =>
    cases hty with
    | customTy hball =>
      simp only [Ty.openVars, Ty.instantiate, TyList.instantiate_eq_map]
      exact .customTy (List.forall₂_self_map (fun t ht => ih t ht (hball t ht)))
  | bl lo hi e ih =>
    cases hty with
    | bl he =>
      simp only [Ty.openVars, Ty.instantiate]
      exact .bl (ih he)


/-! ### Cofinite-generalization machinery for the `letIn` soundness case -/

/-- A generalization candidate is, by construction, not fixed by the env. -/
theorem genVars_not_mem {rigid : List Nat} {env : Env} {τ : Ty} {g : Nat}
    (h : g ∈ genVars rigid env τ) : g ∉ env.freeVars := by
  simp only [genVars, List.mem_filter, Bool.and_eq_true] at h
  simpa using h.2.1

/-- A generalization candidate is, by construction, not one of the rigid scoped
    type variables (the bound expression's annotation fvars). This is what keeps
    the `let` from generalizing over an in-scope skolem. -/
theorem genVars_not_mem_rigid {rigid : List Nat} {env : Env} {τ : Ty} {g : Nat}
    (h : g ∈ genVars rigid env τ) : g ∉ rigid := by
  simp only [genVars, List.mem_filter, Bool.and_eq_true] at h
  simpa using h.2.2

/-- A substitution whose domain avoids `Xs` commutes with opening by `Xs`. -/
theorem Subst.onTy_openVars {S : Subst} {Xs : List Nat}
    (h_lc : ∀ p ∈ S, p.2.IsLC) (h_fresh : ∀ p ∈ S, p.1 ∉ Xs) :
    ∀ {ty : Ty}, S.onTy (Ty.openVars Xs ty) = Ty.openVars Xs (S.onTy ty) := by
  induction S with
  | nil => intro ty; simp only [Subst.onTy_nil]
  | cons hd S' ih =>
    obtain ⟨Z, U⟩ := hd
    have hU : U.IsLC := h_lc (Z, U) (List.mem_cons_self ..)
    have hZ : Z ∉ Xs := h_fresh (Z, U) (List.mem_cons_self ..)
    intro ty
    simp only [Subst.onTy, Ty.substFvars]
    rw [Ty.substFvar_openVars hU hZ]
    exact ih (fun p hp => h_lc p (List.mem_cons_of_mem _ hp))
             (fun p hp => h_fresh p (List.mem_cons_of_mem _ hp))

@[simp] theorem Ty.openVars_prim {Xs : List Nat} {p : PrimTy} :
    Ty.openVars Xs (.prim p) = .prim p := rfl

private theorem TyList.closeOver_eq_map (gs : List Nat) (tys : List Ty) :
    TyList.closeOver gs tys = tys.map (Ty.closeOver gs) := by
  induction tys with
  | nil => rfl
  | cons hd tl ih => simp [TyList.closeOver, ih]

/-- The free vars of an opening are among the original free vars or the opening
    names. -/
theorem Ty.freeVars_openVars_subset {Xs : List Nat} {t : Ty} :
    ∀ z ∈ (Ty.openVars Xs t).freeVars, z ∈ t.freeVars ∨ z ∈ Xs := by
  induction t using Ty.rec_strong with
  | prim p => intro z hz; simp [Ty.openVars, Ty.instantiate, Ty.freeVars] at hz
  | fvar n => intro z hz; left; simpa only [Ty.openVars, Ty.instantiate, Ty.freeVars] using hz
  | bvar i =>
    intro z hz
    simp only [Ty.openVars, Ty.instantiate] at hz
    cases hh : Xs[i]? with
    | none => rw [hh] at hz; simp [Ty.freeVars] at hz
    | some x =>
      rw [hh] at hz
      simp only [Option.elim_some, Ty.freeVars, List.mem_singleton] at hz
      subst hz; exact .inr (List.mem_of_getElem? hh)
  | arrow a b iha ihb =>
    intro z hz
    rw [Ty.openVars_arrow] at hz
    simp only [Ty.freeVars, List.mem_dedup, List.mem_append] at hz ⊢
    rcases hz with hz | hz
    · rcases iha z hz with h | h
      · exact .inl (.inl h)
      · exact .inr h
    · rcases ihb z hz with h | h
      · exact .inl (.inr h)
      · exact .inr h
  | customTy nm tys ih =>
    intro z hz
    rw [Ty.openVars_customTy, Ty.freeVars] at hz
    obtain ⟨t', ht', hzt'⟩ := TyList.mem_freeVars_iff.mp hz
    obtain ⟨t0, ht0, rfl⟩ := List.mem_map.mp ht'
    rcases ih t0 ht0 z hzt' with h | h
    · exact .inl (by rw [Ty.freeVars]; exact TyList.mem_freeVars_of_mem ht0 h)
    · exact .inr h
  | bl lo hi e ih =>
    intro z hz
    simp only [Ty.openVars, Ty.instantiate, Ty.freeVars] at hz ⊢
    exact ih z hz

/-- A closed type's opening has free vars only among the opening names. -/
theorem Ty.freeVars_openVars_closed {Xs : List Nat} {t : Ty} (hcl : NoFreeVars t)
    {z : Nat} (hz : z ∈ (Ty.openVars Xs t).freeVars) : z ∈ Xs := by
  rcases Ty.freeVars_openVars_subset z hz with h | h
  · exact absurd h (hcl.not_mem_freeVars z)
  · exact h

/-! ### Variable-tracking lemmas for substitutions and `UnifyRel`
    (relocated here so the honest soundness can use them)

`Subst.mem_freeVars_onTy` bounds the free vars of a substituted type by the
input's vars plus the substitution's range; `UnifyRel.range_mem` / `.dom_mem`
locate a derived substitution's range/domain inside the inputs' vars; and
`UnifyRel.eliminates` is the occurs-check at the variable-set level (a domain
variable never survives in any image). -/

/-- `TyList.freeVars` membership characterisation (the `customTy` payload). -/
theorem mem_TyList_freeVars {tys : List Ty} {v : Nat} :
    v ∈ TyList.freeVars tys ↔ ∃ t ∈ tys, v ∈ t.freeVars := by
  constructor
  · intro h
    by_contra hc
    push_neg at hc
    exact (TyList.not_mem_freeVars_iff.mpr hc) h
  · rintro ⟨t, ht, hv⟩
    exact TyList.mem_freeVars_of_mem ht hv

/-- An upper bound on the `.bvar` indices occurring in a type (support for
    `PolyTy.Generalizes.freeVars_subset`: opening at `Ty.bvarMax`-many fresh names
    instantiates *every* bound variable). -/
private def Ty.bvarMax : Ty → Nat
  | .prim _ => 0
  | .fvar _ => 0
  | .bvar i => i + 1
  | .arrow a b => max (Ty.bvarMax a) (Ty.bvarMax b)
  | .customTy _ tys => (tys.map Ty.bvarMax).foldr max 0
  | .bl _ _ e => Ty.bvarMax e

/-- A generalising scheme introduces no free type variables beyond those of the
    scheme it generalises (standard "generalisation does not add free vars"). -/
theorem PolyTy.Generalizes.freeVars_subset {M' M : PolyTy} (h : PolyTy.Generalizes M' M) :
    M'.body.freeVars ⊆ M.body.freeVars := by
  intro w hwM'
  by_contra hwM
  -- free fvars of the source survive any `InstantiatesBy` (bvars have no fvars)
  have hsurv : ∀ {tyArgs : List Ty} {ty ty' : Ty},
      InstantiatesBy tyArgs ty ty' → w ∈ ty.freeVars → w ∈ ty'.freeVars := by
    intro tyArgs ty ty' hi
    induction ty using Ty.rec_strong generalizing ty' with
    | prim p => cases hi; intro hw; simp [Ty.freeVars] at hw
    | fvar n => cases hi; intro hw; simpa [Ty.freeVars] using hw
    | bvar i => cases hi; intro hw; simp [Ty.freeVars] at hw
    | arrow a b iha ihb =>
      cases hi with
      | arrow ha hb =>
        intro hw
        simp only [Ty.freeVars, List.mem_dedup, List.mem_append] at hw
        rcases hw with hw | hw
        · exact List.mem_dedup.mpr (List.mem_append.mpr (Or.inl (iha ha hw)))
        · exact List.mem_dedup.mpr (List.mem_append.mpr (Or.inr (ihb hb hw)))
    | customTy nm tys ih =>
      cases hi with
      | customTy hforall =>
        intro hw
        simp only [Ty.freeVars] at hw
        induction hforall with
        | nil => simp [TyList.freeVars] at hw
        | cons hhd htl ihtl =>
          rename_i hd_ty hd_it tl_tys tl_it
          rcases mem_TyList_freeVars.mp hw with ⟨t, ht, hwt⟩
          rcases List.mem_cons.mp ht with rfl | ht
          · exact mem_TyList_freeVars.mpr
              ⟨hd_it, List.mem_cons_self .., ih t List.mem_cons_self hhd hwt⟩
          · exact List.mem_dedup.mpr (List.mem_append.mpr (Or.inr
              (ihtl (fun t ht => ih t (List.mem_cons_of_mem _ ht))
                (mem_TyList_freeVars.mpr ⟨t, ht, hwt⟩))))
    | bl lo hi e ih =>
      cases hi with
      | bl he =>
        intro hw
        simp only [Ty.freeVars] at hw
        simpa [Ty.freeVars] using ih he hw
  have hmono : ∀ {n m : Nat} {ty : Ty}, n ≤ m → ContainsBvarsUpTo n ty → ContainsBvarsUpTo m ty := by
    intro n m ty hnm
    induction ty using Ty.rec_strong with
    | prim p => intro h; exact .prim
    | fvar n' => intro h; exact .fvar
    | bvar i => intro h; cases h with | bvar hlt => exact .bvar (by omega)
    | arrow a b iha ihb => intro h; cases h with
        | arrow ha hb => exact .arrow (iha ha) (ihb hb)
    | customTy nm tys ih => intro h; cases h with
        | customTy hb => exact .customTy (by
            intro t ht
            exact ih t ht (hb t ht))
    | bl lo hi e ih => intro h; cases h with
        | bl he => exact .bl (ih he)
  have hfold : ∀ {a : Nat} {as : List Nat}, a ∈ as → a ≤ as.foldr max 0 := by
    intro a as ha
    induction as with
    | nil => simp at ha
    | cons b bs ih =>
      rcases List.mem_cons.mp ha with rfl | ha
      · exact le_max_left a (bs.foldr max 0)
      · exact le_trans (ih ha) (le_max_right b (bs.foldr max 0))
  have hbvarMax : ∀ {ty : Ty}, ContainsBvarsUpTo (Ty.bvarMax ty) ty := by
    intro ty
    induction ty using Ty.rec_strong with
    | prim p => exact .prim
    | fvar n => exact .fvar
    | bvar i => rw [Ty.bvarMax]; exact .bvar (by omega)
    | arrow a b iha ihb =>
      rw [Ty.bvarMax]
      exact .arrow (hmono (le_max_left (Ty.bvarMax a) (Ty.bvarMax b)) iha)
        (hmono (le_max_right (Ty.bvarMax a) (Ty.bvarMax b)) ihb)
    | customTy nm tys ih =>
      rw [Ty.bvarMax]
      exact .customTy (by
        intro t ht
        exact hmono (hfold (List.mem_map.mpr ⟨t, ht, rfl⟩)) (ih t ht))
    | bl lo hi e ih => rw [Ty.bvarMax]; exact .bl ih
  -- instantiate `M` at fresh fvars `Vs` strictly above `w`
  let n : Nat := Ty.bvarMax M.body
  let Vs : List Nat := (List.range n).map (fun i => w + 1 + i)
  have hwVs : w ∉ Vs := by
    intro hwv
    rcases List.mem_map.mp hwv with ⟨i, _, hieq⟩
    omega
  have hInst : InstantiatesBy (Vs.map Ty.fvar) M.body (M.body.openVars Vs) := by
    exact InstantiatesBy.openVars (Xs := Vs) (n := n) hbvarMax
      (by simp [Vs, n, List.length_map, List.length_range])
  have hLC : ∀ t ∈ Vs.map Ty.fvar, t.IsLC := by
    intro t ht
    rcases List.mem_map.mp ht with ⟨x, _, rfl⟩
    exact ContainsBvarsUpTo.fvar
  have hw_ty : w ∉ (M.body.openVars Vs).freeVars := by
    intro hwty
    have hsub := Ty.freeVars_openVars_subset (Xs := Vs) (t := M.body) w hwty
    rcases hsub with hwbody | hwvs
    · exact hwM hwbody
    · exact hwVs hwvs
  obtain ⟨tyArgs', hLC', hsurv'⟩ := h (Vs.map Ty.fvar) (M.body.openVars Vs) hLC hInst
  exact hw_ty (hsurv hsurv' hwM')

/-- Free vars introduced by a single-variable substitution come from the input
    or from the replacement. -/
theorem Ty.mem_freeVars_substFvar {Z : Nat} {U x : Ty} {v : Nat}
    (hv : v ∈ (Ty.substFvar Z U x).freeVars) : v ∈ x.freeVars ∨ v ∈ U.freeVars := by
  induction x using Ty.rec_strong with
  | prim p => simp [Ty.substFvar, Ty.freeVars] at hv
  | bvar i => simp [Ty.substFvar, Ty.freeVars] at hv
  | fvar m =>
    simp only [Ty.substFvar] at hv
    by_cases hm : m = Z
    · simp only [if_pos hm] at hv; exact Or.inr hv
    · simp only [if_neg hm, Ty.freeVars, List.mem_singleton] at hv
      subst hv; exact Or.inl (by simp [Ty.freeVars])
  | arrow a b iha ihb =>
    simp only [Ty.substFvar, Ty.freeVars, List.mem_dedup, List.mem_append] at hv
    rcases hv with h | h
    · rcases iha h with h' | h'
      · exact Or.inl (by simp only [Ty.freeVars, List.mem_dedup, List.mem_append]; exact Or.inl h')
      · exact Or.inr h'
    · rcases ihb h with h' | h'
      · exact Or.inl (by simp only [Ty.freeVars, List.mem_dedup, List.mem_append]; exact Or.inr h')
      · exact Or.inr h'
  | customTy nm tys ih =>
    simp only [Ty.substFvar, Ty.freeVars, TyList.substFvar_eq_map] at hv
    rw [mem_TyList_freeVars] at hv
    obtain ⟨t', ht', hvt'⟩ := hv
    obtain ⟨t0, ht0, rfl⟩ := List.mem_map.mp ht'
    rcases ih t0 ht0 hvt' with h | h
    · exact Or.inl (by simp only [Ty.freeVars]; exact TyList.mem_freeVars_of_mem ht0 h)
    · exact Or.inr h
  | bl lo hi e ih =>
    simp only [Ty.substFvar, Ty.freeVars] at hv
    rcases ih hv with h | h
    · exact Or.inl (by simpa only [Ty.freeVars] using h)
    · exact Or.inr h

/-- Free vars introduced by a whole substitution come from the input or from
    one of the substitution's replacements. -/
theorem Subst.mem_freeVars_onTy {S : Subst} {x : Ty} {v : Nat}
    (hv : v ∈ (S.onTy x).freeVars) : v ∈ x.freeVars ∨ ∃ p ∈ S, v ∈ p.2.freeVars := by
  induction S generalizing x with
  | nil => exact Or.inl (by simpa [Subst.onTy] using hv)
  | cons hd tl ih =>
    obtain ⟨Z, U⟩ := hd
    rw [show ((Z, U) :: tl) = [(Z, U)] ++ tl from rfl, Subst.onTy_append] at hv
    rcases ih hv with h | h
    · have he : Subst.onTy [(Z, U)] x = Ty.substFvar Z U x := rfl
      rw [he] at h
      rcases Ty.mem_freeVars_substFvar h with h' | h'
      · exact Or.inl h'
      · exact Or.inr ⟨(Z, U), List.mem_cons_self, h'⟩
    · obtain ⟨p, hp, hvp⟩ := h
      exact Or.inr ⟨p, List.mem_cons_of_mem _ hp, hvp⟩

/-- Injecting a sub-type's free var into a compound type's free vars. -/
theorem Ty.mem_freeVars_arrowL {a b : Ty} {v : Nat} (h : v ∈ a.freeVars) :
    v ∈ (Ty.arrow a b).freeVars := by
  simp only [Ty.freeVars, List.mem_dedup, List.mem_append]; exact Or.inl h
theorem Ty.mem_freeVars_arrowR {a b : Ty} {v : Nat} (h : v ∈ b.freeVars) :
    v ∈ (Ty.arrow a b).freeVars := by
  simp only [Ty.freeVars, List.mem_dedup, List.mem_append]; exact Or.inr h
theorem Ty.mem_freeVars_customTy {nm : TyName} {tys : List Ty} {t : Ty} {v : Nat}
    (ht : t ∈ tys) (h : v ∈ t.freeVars) : v ∈ (Ty.customTy nm tys).freeVars := by
  simp only [Ty.freeVars]; exact TyList.mem_freeVars_of_mem ht h
theorem Ty.mem_freeVars_bl {lo hi : FHM.Bounds.CountSlot} {e : Ty} {v : Nat}
    (h : v ∈ e.freeVars) : v ∈ (Ty.bl lo hi e).freeVars := by
  simpa only [Ty.freeVars] using h

/-- A variable not occurring in the replacement does not survive substituting it. -/
theorem Ty.not_mem_freeVars_substFvar_self {n : Nat} {U x : Ty}
    (hU : n ∉ U.freeVars) : n ∉ (Ty.substFvar n U x).freeVars := by
  induction x using Ty.rec_strong with
  | prim p => simp [Ty.substFvar, Ty.freeVars]
  | bvar i => simp [Ty.substFvar, Ty.freeVars]
  | fvar m =>
    simp only [Ty.substFvar]
    by_cases hm : m = n
    · simp only [if_pos hm]; exact hU
    · simp only [if_neg hm, Ty.freeVars, List.mem_singleton]; exact fun hc => hm hc.symm
  | arrow a b iha ihb =>
    simp only [Ty.substFvar, Ty.freeVars, List.mem_dedup, List.mem_append, not_or]
    exact ⟨iha, ihb⟩
  | customTy nm tys ih =>
    simp only [Ty.substFvar, Ty.freeVars, TyList.substFvar_eq_map]
    intro hc
    rw [mem_TyList_freeVars] at hc
    obtain ⟨t', ht', hvt'⟩ := hc
    obtain ⟨t0, ht0, rfl⟩ := List.mem_map.mp ht'
    exact ih t0 ht0 hvt'
  | bl lo hi e ih =>
    simp only [Ty.substFvar, Ty.freeVars]
    exact ih

/-! The range of a `UnifyRel`-substitution lies within the inputs' free vars. -/
mutual
theorem UnifyRel.range_mem : {a b : Ty} → {S : Subst} → UnifyRel a b S →
    ∀ p ∈ S, ∀ v ∈ p.2.freeVars, v ∈ a.freeVars ∨ v ∈ b.freeVars
  | _, _, _, .prim => by simp
  | _, _, _, .fvarRefl => by simp
  | _, _, _, .fvarL _ _ => by
    intro p hp v hv; rw [List.mem_singleton] at hp; subst hp; exact Or.inr hv
  | _, _, _, .fvarR _ _ => by
    intro p hp v hv; rw [List.mem_singleton] at hp; subst hp; exact Or.inl hv
  | _, _, _, @UnifyRel.arrow a b c d S₁ S₂ h₁ h₂ => by
    intro p hp v hv
    rw [List.mem_append] at hp
    rcases hp with hp | hp
    · rcases UnifyRel.range_mem h₁ p hp v hv with h | h
      · exact Or.inl (Ty.mem_freeVars_arrowL h)
      · exact Or.inr (Ty.mem_freeVars_arrowL h)
    · rcases UnifyRel.range_mem h₂ p hp v hv with h | h
      · rcases Subst.mem_freeVars_onTy h with hb | ⟨q, hq, hvq⟩
        · exact Or.inl (Ty.mem_freeVars_arrowR hb)
        · rcases UnifyRel.range_mem h₁ q hq v hvq with h' | h'
          · exact Or.inl (Ty.mem_freeVars_arrowL h')
          · exact Or.inr (Ty.mem_freeVars_arrowL h')
      · rcases Subst.mem_freeVars_onTy h with hd | ⟨q, hq, hvq⟩
        · exact Or.inr (Ty.mem_freeVars_arrowR hd)
        · rcases UnifyRel.range_mem h₁ q hq v hvq with h' | h'
          · exact Or.inl (Ty.mem_freeVars_arrowL h')
          · exact Or.inr (Ty.mem_freeVars_arrowL h')
  | _, _, _, .customTy hl => by
    intro p hp v hv
    rcases UnifyRelList.range_mem hl p hp v hv with ⟨t, ht, h⟩ | ⟨t, ht, h⟩
    · exact Or.inl (Ty.mem_freeVars_customTy ht h)
    · exact Or.inr (Ty.mem_freeVars_customTy ht h)
  | _, _, _, .bl h => by
    intro p hp v hv
    rcases UnifyRel.range_mem h p hp v hv with h' | h'
    · exact Or.inl (Ty.mem_freeVars_bl h')
    · exact Or.inr (Ty.mem_freeVars_bl h')
  | _, _, _, .blList h => by
    intro p hp v hv
    rcases UnifyRel.range_mem h p hp v hv with h' | h'
    · exact Or.inl (Ty.mem_freeVars_bl h')
    · exact Or.inr (Ty.mem_freeVars_customTy List.mem_cons_self h')
  | _, _, _, .listBl h => by
    intro p hp v hv
    rcases UnifyRel.range_mem h p hp v hv with h' | h'
    · exact Or.inl (Ty.mem_freeVars_customTy List.mem_cons_self h')
    · exact Or.inr (Ty.mem_freeVars_bl h')
theorem UnifyRelList.range_mem : {as bs : List Ty} → {S : Subst} → UnifyRelList as bs S →
    ∀ p ∈ S, ∀ v ∈ p.2.freeVars,
      (∃ t ∈ as, v ∈ t.freeVars) ∨ (∃ t ∈ bs, v ∈ t.freeVars)
  | _, _, _, .nil => by simp
  | _, _, _, @UnifyRelList.cons t₁ t₂ ts₁ ts₂ S₁ S₂ h₁ ht => by
    intro p hp v hv
    rw [List.mem_append] at hp
    rcases hp with hp | hp
    · rcases UnifyRel.range_mem h₁ p hp v hv with h | h
      · exact Or.inl ⟨t₁, List.mem_cons_self, h⟩
      · exact Or.inr ⟨t₂, List.mem_cons_self, h⟩
    · rcases UnifyRelList.range_mem ht p hp v hv with ⟨t, ht', hvt⟩ | ⟨t, ht', hvt⟩
      · obtain ⟨t0, ht0, rfl⟩ := List.mem_map.mp ht'
        rcases Subst.mem_freeVars_onTy hvt with hb | ⟨q, hq, hvq⟩
        · exact Or.inl ⟨t0, List.mem_cons_of_mem _ ht0, hb⟩
        · rcases UnifyRel.range_mem h₁ q hq v hvq with h' | h'
          · exact Or.inl ⟨t₁, List.mem_cons_self, h'⟩
          · exact Or.inr ⟨t₂, List.mem_cons_self, h'⟩
      · obtain ⟨t0, ht0, rfl⟩ := List.mem_map.mp ht'
        rcases Subst.mem_freeVars_onTy hvt with hb | ⟨q, hq, hvq⟩
        · exact Or.inr ⟨t0, List.mem_cons_of_mem _ ht0, hb⟩
        · rcases UnifyRel.range_mem h₁ q hq v hvq with h' | h'
          · exact Or.inl ⟨t₁, List.mem_cons_self, h'⟩
          · exact Or.inr ⟨t₂, List.mem_cons_self, h'⟩
end

/-! The domain of a `UnifyRel`-substitution lies within the inputs' free vars. -/
mutual
theorem UnifyRel.dom_mem : {a b : Ty} → {S : Subst} → UnifyRel a b S →
    ∀ p ∈ S, p.1 ∈ a.freeVars ∨ p.1 ∈ b.freeVars
  | _, _, _, .prim => by simp
  | _, _, _, .fvarRefl => by simp
  | _, _, _, .fvarL _ _ => by
    intro p hp; rw [List.mem_singleton] at hp; subst hp; exact Or.inl (by simp [Ty.freeVars])
  | _, _, _, .fvarR _ _ => by
    intro p hp; rw [List.mem_singleton] at hp; subst hp; exact Or.inr (by simp [Ty.freeVars])
  | _, _, _, @UnifyRel.arrow a b c d S₁ S₂ h₁ h₂ => by
    intro p hp
    rw [List.mem_append] at hp
    rcases hp with hp | hp
    · rcases UnifyRel.dom_mem h₁ p hp with h | h
      · exact Or.inl (Ty.mem_freeVars_arrowL h)
      · exact Or.inr (Ty.mem_freeVars_arrowL h)
    · rcases UnifyRel.dom_mem h₂ p hp with h | h
      · rcases Subst.mem_freeVars_onTy h with hb | ⟨q, hq, hvq⟩
        · exact Or.inl (Ty.mem_freeVars_arrowR hb)
        · rcases UnifyRel.range_mem h₁ q hq p.1 hvq with h' | h'
          · exact Or.inl (Ty.mem_freeVars_arrowL h')
          · exact Or.inr (Ty.mem_freeVars_arrowL h')
      · rcases Subst.mem_freeVars_onTy h with hd | ⟨q, hq, hvq⟩
        · exact Or.inr (Ty.mem_freeVars_arrowR hd)
        · rcases UnifyRel.range_mem h₁ q hq p.1 hvq with h' | h'
          · exact Or.inl (Ty.mem_freeVars_arrowL h')
          · exact Or.inr (Ty.mem_freeVars_arrowL h')
  | _, _, _, .customTy hl => by
    intro p hp
    rcases UnifyRelList.dom_mem hl p hp with ⟨t, ht, h⟩ | ⟨t, ht, h⟩
    · exact Or.inl (Ty.mem_freeVars_customTy ht h)
    · exact Or.inr (Ty.mem_freeVars_customTy ht h)
  | _, _, _, .bl h => by
    intro p hp
    rcases UnifyRel.dom_mem h p hp with h' | h'
    · exact Or.inl (Ty.mem_freeVars_bl h')
    · exact Or.inr (Ty.mem_freeVars_bl h')
  | _, _, _, .blList h => by
    intro p hp
    rcases UnifyRel.dom_mem h p hp with h' | h'
    · exact Or.inl (Ty.mem_freeVars_bl h')
    · exact Or.inr (Ty.mem_freeVars_customTy List.mem_cons_self h')
  | _, _, _, .listBl h => by
    intro p hp
    rcases UnifyRel.dom_mem h p hp with h' | h'
    · exact Or.inl (Ty.mem_freeVars_customTy List.mem_cons_self h')
    · exact Or.inr (Ty.mem_freeVars_bl h')
theorem UnifyRelList.dom_mem : {as bs : List Ty} → {S : Subst} → UnifyRelList as bs S →
    ∀ p ∈ S, (∃ t ∈ as, p.1 ∈ t.freeVars) ∨ (∃ t ∈ bs, p.1 ∈ t.freeVars)
  | _, _, _, .nil => by simp
  | _, _, _, @UnifyRelList.cons t₁ t₂ ts₁ ts₂ S₁ S₂ h₁ ht => by
    intro p hp
    rw [List.mem_append] at hp
    rcases hp with hp | hp
    · rcases UnifyRel.dom_mem h₁ p hp with h | h
      · exact Or.inl ⟨t₁, List.mem_cons_self, h⟩
      · exact Or.inr ⟨t₂, List.mem_cons_self, h⟩
    · rcases UnifyRelList.dom_mem ht p hp with ⟨t, ht', hvt⟩ | ⟨t, ht', hvt⟩
      · obtain ⟨t0, ht0, rfl⟩ := List.mem_map.mp ht'
        rcases Subst.mem_freeVars_onTy hvt with hb | ⟨q, hq, hvq⟩
        · exact Or.inl ⟨t0, List.mem_cons_of_mem _ ht0, hb⟩
        · rcases UnifyRel.range_mem h₁ q hq p.1 hvq with h' | h'
          · exact Or.inl ⟨t₁, List.mem_cons_self, h'⟩
          · exact Or.inr ⟨t₂, List.mem_cons_self, h'⟩
      · obtain ⟨t0, ht0, rfl⟩ := List.mem_map.mp ht'
        rcases Subst.mem_freeVars_onTy hvt with hb | ⟨q, hq, hvq⟩
        · exact Or.inr ⟨t0, List.mem_cons_of_mem _ ht0, hb⟩
        · rcases UnifyRel.range_mem h₁ q hq p.1 hvq with h' | h'
          · exact Or.inl ⟨t₁, List.mem_cons_self, h'⟩
          · exact Or.inr ⟨t₂, List.mem_cons_self, h'⟩
end

/-! The occurs check at the variable-set level: a domain variable of a
    `UnifyRel`-substitution never survives in any of its images. -/
mutual
theorem UnifyRel.eliminates : {a b : Ty} → {S : Subst} → UnifyRel a b S →
    ∀ p ∈ S, ∀ (x : Ty), p.1 ∉ (S.onTy x).freeVars
  | _, _, _, .prim => by simp
  | _, _, _, .fvarRefl => by simp
  | _, _, _, .fvarL _ hocc => by
    intro p hp x; rw [List.mem_singleton] at hp; subst hp
    exact Ty.not_mem_freeVars_substFvar_self hocc
  | _, _, _, .fvarR _ hocc => by
    intro p hp x; rw [List.mem_singleton] at hp; subst hp
    exact Ty.not_mem_freeVars_substFvar_self hocc
  | _, _, _, @UnifyRel.arrow a b c d S₁ S₂ h₁ h₂ => by
    intro p hp x hc
    rw [Subst.onTy_append] at hc
    rw [List.mem_append] at hp
    rcases hp with hp | hp
    · rcases Subst.mem_freeVars_onTy hc with h | ⟨q, hq, hvq⟩
      · exact UnifyRel.eliminates h₁ p hp x h
      · rcases UnifyRel.range_mem h₂ q hq p.1 hvq with h' | h'
        · exact UnifyRel.eliminates h₁ p hp b h'
        · exact UnifyRel.eliminates h₁ p hp d h'
    · exact UnifyRel.eliminates h₂ p hp (S₁.onTy x) hc
  | _, _, _, .customTy hl => by
    intro p hp x hc
    exact UnifyRelList.eliminates hl p hp x hc
  | _, _, _, .bl h => by
    intro p hp x hc
    exact UnifyRel.eliminates h p hp x hc
  | _, _, _, .blList h => by
    intro p hp x hc
    exact UnifyRel.eliminates h p hp x hc
  | _, _, _, .listBl h => by
    intro p hp x hc
    exact UnifyRel.eliminates h p hp x hc
theorem UnifyRelList.eliminates : {as bs : List Ty} → {S : Subst} → UnifyRelList as bs S →
    ∀ p ∈ S, ∀ (x : Ty), p.1 ∉ (S.onTy x).freeVars
  | _, _, _, .nil => by simp
  | _, _, _, @UnifyRelList.cons t₁ t₂ ts₁ ts₂ S₁ S₂ h₁ ht => by
    intro p hp x hc
    rw [Subst.onTy_append] at hc
    rw [List.mem_append] at hp
    rcases hp with hp | hp
    · rcases Subst.mem_freeVars_onTy hc with h | ⟨q, hq, hvq⟩
      · exact UnifyRel.eliminates h₁ p hp x h
      · rcases UnifyRelList.range_mem ht q hq p.1 hvq with ⟨t, ht', hvt⟩ | ⟨t, ht', hvt⟩
        · obtain ⟨t0, ht0, rfl⟩ := List.mem_map.mp ht'
          exact UnifyRel.eliminates h₁ p hp t0 hvt
        · obtain ⟨t0, ht0, rfl⟩ := List.mem_map.mp ht'
          exact UnifyRel.eliminates h₁ p hp t0 hvt
    · exact UnifyRelList.eliminates ht p hp (S₁.onTy x) hc
end

/-- Applying a substitution to a *closed* scheme (no free type vars in its body)
    is a no-op. -/
theorem Subst.onPolyTy_eq_self_of_closed {S : Subst} {σ : PolyTy}
    (h : NoFreeVars σ.body) : S.onPolyTy σ = σ := by
  obtain ⟨pc, b⟩ := σ
  simp only [Subst.onPolyTy, Subst.onTy, PolyTy.mk.injEq, true_and]
  exact Ty.substFvars_eq_self_of_no_key (fun p _ => h.not_mem_freeVars p.1)

/-- All free type vars of `τ` are below `Φ`. The `fvar` analogue of
    `ContainsBvarsUpTo`; clean to push through substitution. -/
inductive Ty.BelowFvars (Φ : Nat) : Ty → Prop
  | prim : Ty.BelowFvars Φ (.prim p)
  | arrow : Ty.BelowFvars Φ a → Ty.BelowFvars Φ b → Ty.BelowFvars Φ (.arrow a b)
  | bvar : Ty.BelowFvars Φ (.bvar i)
  | fvar : i < Φ → Ty.BelowFvars Φ (.fvar i)
  | customTy : (∀ t ∈ tys, Ty.BelowFvars Φ t) → Ty.BelowFvars Φ (.customTy nm tys)
  | bl : Ty.BelowFvars Φ e → Ty.BelowFvars Φ (.bl lo hi e)

theorem Ty.BelowFvars.mono {Φ Φ' : Nat} {τ : Ty} (hle : Φ ≤ Φ')
    (h : Ty.BelowFvars Φ τ) : Ty.BelowFvars Φ' τ := by
  induction h with
  | prim => exact .prim
  | arrow _ _ iha ihb => exact .arrow iha ihb
  | bvar => exact .bvar
  | fvar hlt => exact .fvar (by omega)
  | customTy _ ih => exact .customTy (fun t ht => ih t ht)
  | bl _ ih => exact .bl ih

/-- `substFvar` by a below-`Φ` type preserves below-`Φ`. -/
theorem Ty.BelowFvars.substFvar {Φ Z : Nat} {U τ : Ty}
    (hU : Ty.BelowFvars Φ U) (h : Ty.BelowFvars Φ τ) :
    Ty.BelowFvars Φ (Ty.substFvar Z U τ) := by
  induction τ using Ty.rec_strong with
  | prim _ => exact .prim
  | arrow a b iha ihb => cases h with | arrow ha hb => exact .arrow (iha ha) (ihb hb)
  | bvar i => simp only [Ty.substFvar]; exact .bvar
  | fvar m =>
    simp only [Ty.substFvar]
    by_cases hm : m = Z
    · simp only [if_pos hm]; exact hU
    · simp only [if_neg hm]; cases h with | fvar hlt => exact .fvar hlt
  | customTy nm tys ih =>
    cases h with
    | customTy hall =>
      simp only [Ty.substFvar]
      apply Ty.BelowFvars.customTy
      rw [TyList.substFvar_eq_map]
      intro t ht
      obtain ⟨t0, ht0, rfl⟩ := List.mem_map.mp ht
      exact ih t0 ht0 (hall t0 ht0)
  | bl lo hi e ih =>
    cases h with
    | bl he =>
      simp only [Ty.substFvar]
      exact .bl (ih he)

/-- A whole substitution with below-`Φ` replacements preserves below-`Φ`. -/
theorem Subst.onTy_belowFvars {Φ : Nat} {S : Subst} (hS : ∀ p ∈ S, Ty.BelowFvars Φ p.2) :
    ∀ {τ : Ty}, Ty.BelowFvars Φ τ → Ty.BelowFvars Φ (S.onTy τ) := by
  induction S with
  | nil => intro τ hτ; simpa using hτ
  | cons hd S' ih =>
    obtain ⟨Z, U⟩ := hd
    have hU : Ty.BelowFvars Φ U := hS (Z, U) (List.mem_cons_self ..)
    have hS' : ∀ p ∈ S', Ty.BelowFvars Φ p.2 := fun p hp => hS p (List.mem_cons_of_mem _ hp)
    intro τ hτ
    rw [show ((Z, U) :: S') = [(Z, U)] ++ S' from rfl, Subst.onTy_append]
    exact ih hS' (Ty.BelowFvars.substFvar hU hτ)

/-- Bridge to the `freeVars` characterisation: a below-`Φ` type's free vars are
    all `< Φ` (so any `w ≥ Φ` is fresh for it). -/
theorem Ty.BelowFvars.mem_lt {Φ : Nat} {τ : Ty} (h : Ty.BelowFvars Φ τ) :
    ∀ v ∈ τ.freeVars, v < Φ := by
  induction h with
  | prim => intro v hv; simp [Ty.freeVars] at hv
  | bvar => intro v hv; simp [Ty.freeVars] at hv
  | fvar hlt => intro v hv; simp only [Ty.freeVars, List.mem_singleton] at hv; exact hv ▸ hlt
  | arrow _ _ iha ihb =>
    intro v hv; simp only [Ty.freeVars, List.mem_dedup, List.mem_append] at hv
    rcases hv with h | h
    · exact iha v h
    · exact ihb v h
  | customTy hall ih =>
    intro v hv
    simp only [Ty.freeVars] at hv
    by_contra hge
    refine (TyList.not_mem_freeVars_iff.mpr ?_) hv
    intro t ht hc
    exact hge (ih t ht v hc)
  | bl _ ih =>
    intro v hv
    simp only [Ty.freeVars] at hv
    exact ih v hv


/-- Every scheme body of `ctx` has its free type vars below the frontier `Φ`
    (the "new_tv" discipline: vars `Infer` allocates `≥ Φ` are genuinely fresh). -/
def CtxBelow (Φ : Nat) (ctx : Ctx) : Prop := ∀ M ∈ ctx.env, Ty.BelowFvars Φ M.body

/-- Frontier bound for an algorithmic `RecSpec`: an unannotated member's solved
    monotype (resp. an annotated member's scheme body) has its free type vars below
    `Φ`. The spec-level lift used by the fused `InferRecGroup` invariants. -/
def RecSpec.BelowFvars (Φ : Nat) : RecSpec → Prop
  | .mono τ => Ty.BelowFvars Φ τ
  | .poly σ => Ty.BelowFvars Φ σ.body

/-- Frontier-bound monotonicity for specs. -/
theorem RecSpec.BelowFvars.mono {Φ Φ' : Nat} (hle : Φ ≤ Φ') {s : RecSpec}
    (h : s.BelowFvars Φ) : s.BelowFvars Φ' := by
  cases s with
  | mono τ => exact Ty.BelowFvars.mono hle h
  | poly σ => exact Ty.BelowFvars.mono hle h

/-- `onSubst` transport of the spec frontier bound (below-`Φ` images). -/
theorem RecSpec.BelowFvars.onSubst {Φ : Nat} {S : Subst}
    (hS : ∀ p ∈ S, Ty.BelowFvars Φ p.2) {s : RecSpec}
    (h : s.BelowFvars Φ) : (RecSpec.onSubst S s).BelowFvars Φ := by
  cases s with
  | mono τ => exact Subst.onTy_belowFvars hS h
  | poly σ => exact h

/-- The empty-pool RHS entry's body is frontier-bounded when the spec is. -/
theorem RecSpec.rhsEntry_nil_belowFvars {Φ : Nat} {s : RecSpec} (h : s.BelowFvars Φ) :
    Ty.BelowFvars Φ (RecSpec.rhsEntry [] [] s).body := by
  cases s with
  | mono τ => exact h
  | poly σ => exact h

/-- A whole substitution preserves context-below (with frontier growth). -/
theorem Subst.onCtx_below {Φ Φ' : Nat} {S : Subst} {ctx : Ctx}
    (hS : ∀ p ∈ S, Ty.BelowFvars Φ' p.2) (hle : Φ ≤ Φ') (hb : CtxBelow Φ ctx) :
    CtxBelow Φ' (S.onCtx ctx) := by
  intro M hM
  simp only [Subst.onCtx, Subst.onEnv] at hM
  obtain ⟨M0, hM0, rfl⟩ := List.mem_map.mp hM
  exact Subst.onTy_belowFvars hS ((hb M0 hM0).mono hle)

/-- Opening a below-`Φ` type with fresh names all `< Φ` stays below-`Φ`. -/
theorem Ty.openVars_belowFvars {Φ : Nat} {Xs : List Nat} {τ : Ty}
    (hτ : Ty.BelowFvars Φ τ) (hXs : ∀ x ∈ Xs, x < Φ) :
    Ty.BelowFvars Φ (Ty.openVars Xs τ) := by
  induction τ using Ty.rec_strong with
  | prim p => exact .prim
  | arrow a b iha ihb => cases hτ with | arrow ha hb => exact .arrow (iha ha) (ihb hb)
  | bvar i =>
    simp only [Ty.openVars, Ty.instantiate]
    cases h : Xs[i]? with
    | none => exact .bvar
    | some x => exact .fvar (hXs x (List.mem_of_getElem? h))
  | fvar n => cases hτ with | fvar hlt => exact .fvar hlt
  | customTy nm tys ih =>
    cases hτ with
    | customTy hall =>
      simp only [Ty.openVars_customTy]
      apply Ty.BelowFvars.customTy
      intro t' ht'
      obtain ⟨t, ht, rfl⟩ := List.mem_map.mp ht'
      exact ih t ht (hall t ht)
  | bl lo hi e ih =>
    cases hτ with
    | bl he =>
      simp only [Ty.openVars, Ty.instantiate]
      exact .bl (ih he)

/-- A type with no free variables is below any frontier. -/
theorem Ty.BelowFvars.of_noFreeVars {Φ : Nat} {τ : Ty} (h : NoFreeVars τ) :
    Ty.BelowFvars Φ τ := by
  induction h with
  | prim => exact .prim
  | arrow _ _ iha ihb => exact .arrow iha ihb
  | bvar => exact .bvar
  | customTy _ ih => exact .customTy (fun t ht => ih t ht)
  | bl _ ih => exact .bl ih

/-- Converse of `Ty.BelowFvars.mem_lt`: all free vars `< Φ` gives `BelowFvars Φ`. -/
theorem Ty.BelowFvars.of_freeVars_lt {Φ : Nat} {τ : Ty}
    (h : ∀ v ∈ τ.freeVars, v < Φ) : Ty.BelowFvars Φ τ := by
  induction τ using Ty.rec_strong with
  | prim p => exact .prim
  | bvar i => exact .bvar
  | fvar n => exact .fvar (h n (by simp [Ty.freeVars]))
  | arrow a b iha ihb =>
    refine .arrow (iha fun v hv => h v ?_) (ihb fun v hv => h v ?_)
    · simp only [Ty.freeVars, List.mem_dedup, List.mem_append]; exact .inl hv
    · simp only [Ty.freeVars, List.mem_dedup, List.mem_append]; exact .inr hv
  | customTy nm tys ih =>
    refine .customTy fun t ht => ih t ht (fun v hv => h v ?_)
    simp only [Ty.freeVars]
    exact TyList.mem_freeVars_of_mem ht hv
  | bl lo hi e ih =>
    refine .bl (ih fun v hv => h v ?_)
    simpa only [Ty.freeVars] using hv

/-- Opening with below-`Φ` args preserves below-`Φ`-ness. -/
theorem Ty.openWith_belowFvars {Φ : Nat} {Vs : List Ty} {X : Ty}
    (hVs : ∀ v ∈ Vs, Ty.BelowFvars Φ v) (hX : Ty.BelowFvars Φ X) :
    Ty.BelowFvars Φ (Ty.openWith Vs X) := by
  induction X using Ty.rec_strong with
  | prim p => exact .prim
  | fvar n => cases hX with | fvar hlt => exact .fvar hlt
  | bvar i =>
    simp only [Ty.openWith, Ty.instantiate]
    cases h : Vs[i]? with
    | none => simp only [Option.getD_none]; exact .bvar
    | some v => simp only [Option.getD_some]; exact hVs v (List.mem_of_getElem? h)
  | arrow a b iha ihb => cases hX with | arrow ha hb => exact .arrow (iha ha) (ihb hb)
  | customTy nm tys ih =>
    cases hX with
    | customTy hall =>
      simp only [Ty.openWith, Ty.instantiate, TyList.instantiate_eq_map]
      exact .customTy (fun t' ht' => by
        obtain ⟨t, ht, rfl⟩ := List.mem_map.mp ht'; exact ih t ht (hall t ht))
  | bl lo hi e ih =>
    cases hX with
    | bl he =>
      simp only [Ty.openWith, Ty.instantiate]
      exact .bl (ih he)

/-- A `match_` branch's pattern bindings stay below `Φ` (ctor contents are closed,
    so opening with below-`Φ` type args yields below-`Φ` bindings). -/
theorem branchBindings_below {Φ : Nat} {ctorr : Ctor} {ta : List Ty} {ctx : Ctx}
    (hctx : CtxBelow Φ ctx) (hta : ∀ t ∈ ta, Ty.BelowFvars Φ t) :
    CtxBelow Φ { ctx with
      env := (ctorr.contents.map (Ty.openWith ta)).map PolyTy.mkTrivial ++ ctx.env } := by
  intro M hM
  rw [List.mem_append] at hM
  rcases hM with hM | hM
  · obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hM
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp ht
    show Ty.BelowFvars Φ (Ty.openWith ta c)
    exact Ty.openWith_belowFvars hta (Ty.BelowFvars.of_noFreeVars (ctorr.closed c hc))
  · exact hctx M hM

mutual

/-- Unifying two below-`Φ` monotypes yields a below-`Φ` substitution. -/
theorem UnifyRel.belowFvars {Φ : Nat} : {a b : Ty} → {S : Subst} → UnifyRel a b S →
    Ty.BelowFvars Φ a → Ty.BelowFvars Φ b → ∀ p ∈ S, Ty.BelowFvars Φ p.2
  | _, _, _, .prim, _, _ => by simp
  | _, _, _, .fvarRefl, _, _ => by simp
  | _, _, _, .fvarL _ _, _, hb => by
    intro p hp; rw [List.mem_singleton] at hp; subst hp; exact hb
  | _, _, _, .fvarR _ _, ha, _ => by
    intro p hp; rw [List.mem_singleton] at hp; subst hp; exact ha
  | _, _, _, .arrow h₁ h₂, ha, hb => by
    cases ha with | arrow ha_a ha_b => cases hb with | arrow hb_c hb_d =>
    have h1lc := UnifyRel.belowFvars h₁ ha_a hb_c
    have h2lc := UnifyRel.belowFvars h₂ (Subst.onTy_belowFvars h1lc ha_b) (Subst.onTy_belowFvars h1lc hb_d)
    intro p hp; rw [List.mem_append] at hp
    rcases hp with hp | hp
    · exact h1lc p hp
    · exact h2lc p hp
  | _, _, _, .customTy hl, ha, hb => by
    cases ha with | customTy ha_all => cases hb with | customTy hb_all =>
    exact UnifyRelList.belowFvars hl ha_all hb_all
  | _, _, _, .bl h, ha, hb => by
    cases ha with | bl hae => cases hb with | bl hbe =>
    exact UnifyRel.belowFvars h hae hbe
  | _, _, _, .blList h, ha, hb => by
    cases ha with | bl hae => cases hb with | customTy hball =>
    exact UnifyRel.belowFvars h hae (hball _ List.mem_cons_self)
  | _, _, _, .listBl h, ha, hb => by
    cases ha with | customTy hball => cases hb with | bl hbe =>
    exact UnifyRel.belowFvars h (hball _ List.mem_cons_self) hbe

/-- List version: unifying two below-`Φ` type lists yields a below-`Φ` substitution. -/
theorem UnifyRelList.belowFvars {Φ : Nat} : {ts₁ ts₂ : List Ty} → {S : Subst} → UnifyRelList ts₁ ts₂ S →
    (∀ t ∈ ts₁, Ty.BelowFvars Φ t) → (∀ t ∈ ts₂, Ty.BelowFvars Φ t) → ∀ p ∈ S, Ty.BelowFvars Φ p.2
  | _, _, _, .nil, _, _ => by simp
  | _, _, _, @UnifyRelList.cons t₁ t₂ ts₁ ts₂ S₁ S₂ h₁ ht, hts₁, hts₂ => by
    have ht1 : Ty.BelowFvars Φ t₁ := hts₁ t₁ (List.mem_cons_self ..)
    have ht2 : Ty.BelowFvars Φ t₂ := hts₂ t₂ (List.mem_cons_self ..)
    have h1lc := UnifyRel.belowFvars h₁ ht1 ht2
    have hmap₁ : ∀ t ∈ ts₁.map S₁.onTy, Ty.BelowFvars Φ t := by
      intro t htm; obtain ⟨t0, ht0, rfl⟩ := List.mem_map.mp htm
      exact Subst.onTy_belowFvars h1lc (hts₁ t0 (List.mem_cons_of_mem _ ht0))
    have hmap₂ : ∀ t ∈ ts₂.map S₁.onTy, Ty.BelowFvars Φ t := by
      intro t htm; obtain ⟨t0, ht0, rfl⟩ := List.mem_map.mp htm
      exact Subst.onTy_belowFvars h1lc (hts₂ t0 (List.mem_cons_of_mem _ ht0))
    have h2lc := UnifyRelList.belowFvars ht hmap₁ hmap₂
    intro p hp; rw [List.mem_append] at hp
    rcases hp with hp | hp
    · exact h1lc p hp
    · exact h2lc p hp

end

/-- Closing over `gs` only removes free vars, so it preserves below-`Φ`. -/
theorem Ty.BelowFvars.closeOver {Φ : Nat} {gs : List Nat} :
    ∀ {τ : Ty}, Ty.BelowFvars Φ τ → Ty.BelowFvars Φ (Ty.closeOver gs τ) := by
  intro τ h
  induction τ using Ty.rec_strong with
  | prim p => exact .prim
  | bvar i => exact .bvar
  | fvar n =>
    rw [Ty.closeOver.eq_6]
    cases h_idx : gs.idxOf? n with
    | none => cases h with | fvar hlt => exact .fvar hlt
    | some i => exact .bvar
  | arrow a b iha ihb => cases h with | arrow ha hb => exact .arrow (iha ha) (ihb hb)
  | customTy nm tys ih =>
    cases h with
    | customTy hall =>
      simp only [Ty.closeOver, TyList.closeOver_eq_map]
      apply Ty.BelowFvars.customTy
      intro t' ht'; obtain ⟨t, ht, rfl⟩ := List.mem_map.mp ht'
      exact ih t ht (hall t ht)
  | bl lo hi e ih =>
    cases h with
    | bl he =>
      simp only [Ty.closeOver]
      exact .bl (ih he)

/-- A body scheme's body is frontier-bounded when its spec is (mono: closing only
    removes free vars). -/
theorem RecSpec.bodyScheme_belowFvars {Φ : Nat} {G : List Nat} {s : RecSpec}
    (h : s.BelowFvars Φ) : Ty.BelowFvars Φ (RecSpec.bodyScheme G s).body := by
  cases s with
  | mono τ => exact Ty.BelowFvars.closeOver h
  | poly σ => exact h

/-- A fused-group annotation's scheme body free vars are among the ann list's
    (InferW-local copy of Core's `Expr.mem_annList_tyFreeVars`; lets the `letRec`
    arms turn the ann-list free-var bound into per-scheme bounds). -/
theorem Expr.scheme_body_mem_annList_tyFreeVars {σ : PolyTy} {y : Nat}
    {anns : List (Option PolyTy)} (hmem : some σ ∈ anns) (hy : y ∈ σ.body.freeVars) :
    y ∈ Expr.tyFreeVars.AnnList.tyFreeVars anns := by
  induction anns with
  | nil => exact absurd hmem List.not_mem_nil
  | cons hd tl ih =>
    simp only [Expr.tyFreeVars.AnnList.tyFreeVars, List.mem_append]
    rcases List.mem_cons.mp hmem with h | h
    · subst h; exact .inl (by simpa [Option.elim] using hy)
    · exact .inr (ih h)

/-! Frontier invariant (`Infer.belowFvars`): from a context whose schemes are below
    the input frontier `Φ`, `Infer` yields a type and a substitution whose
    replacements are all below the *output* frontier `Φ'` (so `mono` everything up
    to `Φ'`). (Named `belowFvars` rather than `below`, since `Infer.below` is
    reserved by Lean's auto-generated recursor for the `Infer` inductive.) -/
mutual
theorem Infer.belowFvars {Φ ctx e Φ' S τ} (h : Infer Φ ctx e Φ' S τ) :
    CtxBelow Φ ctx → (∀ y ∈ e.tyFreeVars, y < Φ) →
    Ty.BelowFvars Φ' τ ∧ (∀ p ∈ S, Ty.BelowFvars Φ' p.2) := by
  cases h with
  | primLitUnit => intro _ _; exact ⟨.prim, by simp⟩
  | primLitInt => intro _ _; exact ⟨.prim, by simp⟩
  | primLitNat => intro _ _; exact ⟨.prim, by simp⟩
  | primLitChar => intro _ _; exact ⟨.prim, by simp⟩
  | primBinOpIntAdd => intro _ _; exact ⟨.arrow .prim (.arrow .prim .prim), by simp⟩
  | primBinOpIntSub => intro _ _; exact ⟨.arrow .prim (.arrow .prim .prim), by simp⟩
  | primBinOpIntLt _ _ _ _ => intro _ _; exact ⟨.arrow .prim (.arrow .prim (.customTy (by simp))), by simp⟩
  | primBinOpCharLt _ _ _ _ => intro _ _; exact ⟨.arrow .prim (.arrow .prim (.customTy (by simp))), by simp⟩
  | lambda hseed hbody =>
    intro hctx htfv
    cases hseed with
    | none =>
      simp only [Expr.tyFreeVars, Option.elim_none, List.nil_append] at htfv
      obtain ⟨hb_τ, hb_s⟩ := Infer.belowFvars hbody (by
        intro M hM; rcases List.mem_cons.mp hM with rfl | hM
        · exact .fvar (by omega)
        · exact (hctx M hM).mono (by omega))
        (fun y hy => by have := htfv y hy; omega)
      have hfl := Infer.frontier_le hbody
      exact ⟨.arrow (Subst.onTy_belowFvars hb_s (.fvar (by omega))) hb_τ, hb_s⟩
    | some _ hcl =>
      expose_names
      simp only [Expr.tyFreeVars, Option.elim_some, List.mem_append] at htfv
      have hparamTy : Ty.BelowFvars Φ paramTy :=
        Ty.BelowFvars.of_freeVars_lt (fun v hv => htfv v (.inl hv))
      obtain ⟨hb_τ, hb_s⟩ := Infer.belowFvars hbody (by
        intro M hM; rcases List.mem_cons.mp hM with rfl | hM
        · exact hparamTy
        · exact hctx M hM)
        (fun y hy => htfv y (.inr hy))
      exact ⟨.arrow (Subst.onTy_belowFvars hb_s (hparamTy.mono (Infer.frontier_le hbody))) hb_τ, hb_s⟩
  | app hf harg huni =>
    intro hctx htfv
    simp only [Expr.tyFreeVars, List.mem_append] at htfv
    obtain ⟨hf_τ, hf_s⟩ := Infer.belowFvars hf hctx (fun y hy => htfv y (.inl hy))
    have hctx1 := Subst.onCtx_below hf_s (Infer.frontier_le hf) hctx
    obtain ⟨harg_τ, harg_s⟩ := Infer.belowFvars harg hctx1
      (fun y hy => lt_of_lt_of_le (htfv y (.inr hy)) (Infer.frontier_le hf))
    have h1 := Infer.frontier_le hf
    have h2 := Infer.frontier_le harg
    refine ⟨Subst.onTy_belowFvars
        (UnifyRel.belowFvars huni
          (Subst.onTy_belowFvars (fun p hp => (harg_s p hp).mono (by omega)) (hf_τ.mono (by omega)))
          (.arrow (harg_τ.mono (by omega)) (.fvar (by omega))))
        (.fvar (by omega)), ?_⟩
    intro p hp; rw [List.mem_append, List.mem_append] at hp
    rcases hp with (hp | hp) | hp
    · exact (hf_s p hp).mono (by omega)
    · exact (harg_s p hp).mono (by omega)
    · exact UnifyRel.belowFvars huni
        (Subst.onTy_belowFvars (fun p hp => (harg_s p hp).mono (by omega)) (hf_τ.mono (by omega)))
        (.arrow (harg_τ.mono (by omega)) (.fvar (by omega))) p hp
  | var hlook =>
    intro hctx _
    refine ⟨?_, by simp⟩
    exact Ty.openVars_belowFvars ((hctx _ (List.mem_of_getElem? hlook)).mono (by omega))
      (fun x hx => by have := freshVars_lt x hx; omega)
  | ctor hlook =>
    intro _ _
    refine ⟨?_, by simp⟩
    refine Ty.openVars_belowFvars
      (Ty.BelowFvars.of_noFreeVars (Ctor.toTy_body_noFreeVars _))
      (fun x hx => by have := freshVars_lt x hx; omega)
  | letIn hrhs hbody =>
    intro hctx htfv
    simp only [Expr.tyFreeVars, Option.elim_none, List.nil_append, List.mem_append] at htfv
    obtain ⟨hr_τ, hr_s⟩ := Infer.belowFvars hrhs hctx (fun y hy => htfv y (.inl hy))
    have hctx1 := Subst.onCtx_below hr_s (Infer.frontier_le hrhs) hctx
    obtain ⟨hb_τ, hb_s⟩ := Infer.belowFvars hbody (by
      intro M hM
      rcases List.mem_cons.mp hM with rfl | hM
      · exact hr_τ.closeOver
      · exact hctx1 M hM)
      (fun y hy => lt_of_lt_of_le (htfv y (.inr hy)) (Infer.frontier_le hrhs))
    refine ⟨hb_τ, ?_⟩
    intro p hp; rw [List.mem_append] at hp
    rcases hp with hp | hp
    · exact (hr_s p hp).mono (Infer.frontier_le hbody)
    · exact hb_s p hp
  | letInAnn hσwf hΦN hrhs huni _hesc1 _hesc2 hbody =>
    intro hctx htfv
    expose_names
    simp only [Expr.tyFreeVars, Option.elim_some, List.mem_append] at htfv
    have hrle := Infer.frontier_le hrhs
    have hctx_pc : CtxBelow (N + σ.paramCount) ctx := fun M hM => (hctx M hM).mono (by omega)
    have hσbody : Ty.BelowFvars Φ σ.body :=
      Ty.BelowFvars.of_freeVars_lt (fun v hv => htfv v (.inl (.inl hv)))
    obtain ⟨hr_τ, hr_s⟩ := Infer.belowFvars hrhs hctx_pc (fun y hy => by
      rcases Expr.tyFreeVars_openTyVars hy with h | h
      · have := htfv y (.inl (.inr h)); omega
      · have := freshVars_lt y h; omega)
    have hσopen : Ty.BelowFvars Φ₁
        (σ.openVars (freshVars N σ.paramCount)) :=
      Ty.openVars_belowFvars (hσbody.mono (by omega))
        (fun x hx => by have := freshVars_lt x hx; omega)
    have hSchk : ∀ p ∈ Schk, Ty.BelowFvars Φ₁ p.2 :=
      UnifyRel.belowFvars huni hr_τ hσopen
    have hctx1 : CtxBelow Φ₁ (Schk.onCtx (S₁.onCtx ctx)) :=
      Subst.onCtx_below hSchk (le_refl _) (Subst.onCtx_below hr_s hrle hctx_pc)
    obtain ⟨hb_τ, hb_s⟩ := Infer.belowFvars hbody (by
      intro M hM; rcases List.mem_cons.mp hM with rfl | hM
      · exact hσbody.mono (by omega)
      · exact hctx1 M hM)
      (fun y hy => lt_of_lt_of_le (htfv y (.inr hy)) (by omega))
    have hble := Infer.frontier_le hbody
    refine ⟨hb_τ, ?_⟩
    intro p hp; rw [List.mem_append, List.mem_append] at hp
    rcases hp with (hp | hp) | hp
    · exact (hr_s p hp).mono (by omega)
    · exact (hSchk p hp).mono (by omega)
    · exact hb_s p hp
  | match_ hscrut hne hbr =>
    intro hctx htfv
    expose_names
    simp only [Expr.tyFreeVars, List.mem_append] at htfv
    obtain ⟨hτs, hS₁⟩ := Infer.belowFvars hscrut hctx (fun y hy => htfv y (.inl hy))
    have hle1 := Infer.frontier_le hscrut
    have hbrctx : CtxBelow (Φ₁ + 1) (S₁.onCtx ctx) :=
      Subst.onCtx_below (fun p hp => (hS₁ p hp).mono (by omega)) (by omega) hctx
    obtain ⟨hρ_below, hS₂⟩ := InferBranches.belowFvars hbr
      hbrctx
      (hτs.mono (by omega))
      (.fvar (by omega))
      (fun y hy => by have := htfv y (.inr hy); omega)
    refine ⟨hρ_below, ?_⟩
    have hbrle := InferBranches.frontier_le hbr
    intro p hp; rw [List.mem_append] at hp
    rcases hp with hp | hp
    · exact (hS₁ p hp).mono (by omega)
    · exact hS₂ p hp
  | letRec hwf hgroup hceiling hbody =>
    intro hctx htfv
    expose_names
    simp only [Expr.tyFreeVars, List.mem_append] at htfv
    have hlen : bindings.length = anns.length := by
      have h₁ := InferRecGroup.length_eq hgroup
      rw [RecSpec.init_length] at h₁
      exact h₁
    have hspecs_init : ∀ s ∈ RecSpec.init Φ anns, s.BelowFvars (Φ + bindings.length) := by
      intro s hs
      rcases List.mem_iff_getElem.mp hs with ⟨j, hj, rfl⟩
      have hlenj : j < anns.length := by
        have h₂ := RecSpec.init_length Φ anns
        omega
      have hget : (RecSpec.init Φ anns)[j] = RecSpec.mono (.fvar (Φ + j)) := by
        have h₁ := List.getElem?_eq_getElem hj
        rw [RecSpec.init_getElem? Φ anns j, List.getElem?_eq_getElem hlenj] at h₁
        injection h₁ with hEq
        exact hEq.symm
      rw [hget]
      refine Ty.BelowFvars.fvar ?_
      omega
    have hgrpLe : Φ + bindings.length ≤ Φ₁ := InferRecGroup.frontier_le hgroup
    have hctxGroup : CtxBelow (Φ + bindings.length)
        { ctx with env := (RecSpec.init Φ anns).map (RecSpec.rhsEntry [] []) ++ ctx.env } := by
      intro M hM
      rcases List.mem_append.mp hM with hM1 | hM2
      · obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hM1
        exact RecSpec.rhsEntry_nil_belowFvars (hspecs_init s hs)
      · exact (hctx M hM2).mono (by omega)
    have htfv_group : ∀ y ∈ Expr.tyFreeVars.RecGroup.tyFreeVars bindings,
        y < Φ + bindings.length := by
      intro y hy
      have := htfv y (.inl (.inr hy))
      omega
    have hS₁ : ∀ p ∈ S₁, Ty.BelowFvars Φ₁ p.2 :=
      InferRecGroup.belowFvars hgroup hctxGroup hspecs_init htfv_group
    have hspecs_post : ∀ s' ∈ (RecSpec.init Φ anns).map (RecSpec.onSubst S₁),
        s'.BelowFvars Φ₁ := by
      intro s' hs'
      obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hs'
      exact RecSpec.BelowFvars.onSubst hS₁ ((hspecs_init s hs).mono hgrpLe)
    have hbodyCtx : CtxBelow Φ₁
        { (S₁.onCtx ctx) with
          env := RecSpecs.ceilingSchemes
                   (genGroupVars (RecGroup.rigidVars anns bindings) (S₁.onCtx ctx).env
                     (RecSpecs.monoTys ((RecSpec.init Φ anns).map (RecSpec.onSubst S₁))))
                   anns
                   ((RecSpec.init Φ anns).map (RecSpec.onSubst S₁))
                 ++ (S₁.onCtx ctx).env } := by
      intro M hM
      rcases List.mem_append.mp hM with hM1 | hM2
      · obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hM1
        have hpa : p.1 ∈ anns := (List.of_mem_zip hp).1
        have hps : p.2 ∈ (RecSpec.init Φ anns).map (RecSpec.onSubst S₁) := (List.of_mem_zip hp).2
        cases p with
        | mk a s =>
          cases a with
          | some σ =>
            refine Ty.BelowFvars.of_freeVars_lt (fun v hv => ?_)
            have hann := Expr.scheme_body_mem_annList_tyFreeVars hpa hv
            have := htfv v (.inl (.inl hann))
            omega
          | none =>
            exact RecSpec.bodyScheme_belowFvars (hspecs_post s hps)
      · exact Subst.onCtx_below hS₁ (by omega) hctx M hM2
    obtain ⟨hb_τ, hb_s⟩ := Infer.belowFvars hbody hbodyCtx (fun y hy => by
      have := htfv y (.inr hy)
      omega)
    refine ⟨hb_τ, ?_⟩
    intro p hp; rw [List.mem_append] at hp
    rcases hp with hp | hp
    · exact (hS₁ p hp).mono (Infer.frontier_le hbody)
    · exact hb_s p hp
termination_by e.size
decreasing_by
  all_goals (try subst_vars; try simp only [Expr.size, Expr.size_openTyVars]; omega)
theorem InferBranches.belowFvars {Φ ctx scrutTy ρ brs Φ' S}
    (h : InferBranches Φ ctx scrutTy ρ brs Φ' S)
    (hctx : CtxBelow Φ ctx) (hscrutTy : Ty.BelowFvars Φ scrutTy) (hρ : Ty.BelowFvars Φ ρ)
    (htfv : ∀ y ∈ Expr.tyFreeVars.BranchList.tyFreeVars brs, y < Φ) :
    Ty.BelowFvars Φ' (S.onTy ρ) ∧ (∀ p ∈ S, Ty.BelowFvars Φ' p.2) := by
  cases h with
  | nil => exact ⟨by simpa using hρ, by simp⟩
  | cons hlook hn huni0 hbody huni hrest =>
    expose_names
    simp only [Expr.tyFreeVars.BranchList.tyFreeVars, List.mem_append] at htfv
    have hS₀ : ∀ p ∈ S₀, Ty.BelowFvars (Φ + ctor.paramCount) p.2 :=
      UnifyRel.belowFvars huni0 (hscrutTy.mono (by omega))
        (.customTy (fun t ht => by
          obtain ⟨x, hx, rfl⟩ := List.mem_map.mp ht
          exact .fvar (by have := freshVars_lt x hx; omega)))
    obtain ⟨hτb, hS₁⟩ := Infer.belowFvars hbody
      (branchBindings_below (ctorr := ctor)
        (ta := ((freshVars Φ ctor.paramCount).map (Ty.fvar ·)).map S₀.onTy)
        (Subst.onCtx_below hS₀ (by omega) hctx)
        (fun t ht => by
          obtain ⟨v, hv, rfl⟩ := List.mem_map.mp ht
          obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hv
          exact Subst.onTy_belowFvars hS₀ (.fvar (by have := freshVars_lt x hx; omega))))
      (fun y hy => by have := htfv y (.inl hy); omega)
    have hle0 : Φ + ctor.paramCount ≤ Φ₁ := Infer.frontier_le hbody
    have hS₀ρ : Ty.BelowFvars Φ₁ (S₀.onTy ρ) :=
      (Subst.onTy_belowFvars hS₀ (hρ.mono (by omega))).mono hle0
    have hS₀scrut : Ty.BelowFvars Φ₁ (S₀.onTy scrutTy) :=
      (Subst.onTy_belowFvars hS₀ (hscrutTy.mono (by omega))).mono hle0
    have hS₁ρ := Subst.onTy_belowFvars hS₁ hS₀ρ
    have hS₂ := UnifyRel.belowFvars huni hτb hS₁ρ
    have hctx1 : CtxBelow Φ₁ (S₂.onCtx (S₁.onCtx (S₀.onCtx ctx))) :=
      Subst.onCtx_below hS₂ (le_refl _)
        (Subst.onCtx_below hS₁ (le_refl _)
          (Subst.onCtx_below (fun p hp => (hS₀ p hp).mono hle0) (by omega) hctx))
    obtain ⟨hres, hS₃⟩ := InferBranches.belowFvars hrest hctx1
      (Subst.onTy_belowFvars hS₂ (Subst.onTy_belowFvars hS₁ hS₀scrut))
      (Subst.onTy_belowFvars hS₂ (Subst.onTy_belowFvars hS₁ hS₀ρ))
      (fun y hy => lt_of_lt_of_le (htfv y (.inr hy)) (by omega))
    have hbrle := InferBranches.frontier_le hrest
    refine ⟨?_, ?_⟩
    · rw [Subst.onTy_append, Subst.onTy_append, Subst.onTy_append]; exact hres
    · intro p hp; rw [List.mem_append, List.mem_append, List.mem_append] at hp
      rcases hp with ((hp | hp) | hp) | hp
      · exact (hS₀ p hp).mono (by omega)
      · exact (hS₁ p hp).mono (by omega)
      · exact (hS₂ p hp).mono (by omega)
      · exact hS₃ p hp
  | consWild hbody huni hrest =>
    simp only [Expr.tyFreeVars.BranchList.tyFreeVars, List.mem_append] at htfv
    obtain ⟨hτb, hS₁⟩ := Infer.belowFvars hbody hctx
      (fun y hy => htfv y (.inl hy))
    have hle1 := Infer.frontier_le hbody
    have hS₁ρ := Subst.onTy_belowFvars hS₁ (hρ.mono hle1)
    have hS₂ := UnifyRel.belowFvars huni hτb hS₁ρ
    have hctx1 := Subst.onCtx_below hS₂ (le_refl _) (Subst.onCtx_below hS₁ hle1 hctx)
    obtain ⟨hres, hS₃⟩ := InferBranches.belowFvars hrest hctx1
      (Subst.onTy_belowFvars hS₂ (Subst.onTy_belowFvars hS₁ (hscrutTy.mono hle1)))
      (Subst.onTy_belowFvars hS₂ (Subst.onTy_belowFvars hS₁ (hρ.mono hle1)))
      (fun y hy => lt_of_lt_of_le (htfv y (.inr hy)) hle1)
    have hbrle := InferBranches.frontier_le hrest
    refine ⟨?_, ?_⟩
    · rw [Subst.onTy_append, Subst.onTy_append]; exact hres
    · intro p hp; rw [List.mem_append, List.mem_append] at hp
      rcases hp with (hp | hp) | hp
      · exact (hS₁ p hp).mono (by omega)
      · exact (hS₂ p hp).mono (by omega)
      · exact hS₃ p hp
termination_by Expr.sizeBranches brs
decreasing_by
  all_goals (try subst_vars; try simp only [Expr.sizeBranches]; omega)
/-- Fused `InferRecGroup` frontier bound (consMono + consPoly): every replacement
    in the group substitution has its free vars below the output frontier. -/
theorem InferRecGroup.belowFvars {Φ ctx bindings specs Φ' S}
    (h : InferRecGroup Φ ctx bindings specs Φ' S)
    (hctx : CtxBelow Φ ctx) (hspecs : ∀ s ∈ specs, s.BelowFvars Φ)
    (htfv : ∀ y ∈ Expr.tyFreeVars.RecGroup.tyFreeVars bindings, y < Φ) :
    (∀ p ∈ S, Ty.BelowFvars Φ' p.2) := by
  cases h with
  | nil => simp
  | consMono he huni hrest =>
    expose_names
    simp only [Expr.tyFreeVars.RecGroup.tyFreeVars, List.mem_append] at htfv
    obtain ⟨hτ', hS₁⟩ := Infer.belowFvars he hctx (fun y hy => htfv y (.inl hy))
    have hle1 := Infer.frontier_le he
    have hτB : Ty.BelowFvars Φ τ := hspecs (.mono τ) List.mem_cons_self
    have hS₁τ := Subst.onTy_belowFvars hS₁ (hτB.mono hle1)
    have hS₂ := UnifyRel.belowFvars huni hτ' hS₁τ
    have hbrle := InferRecGroup.frontier_le hrest
    have hS₃ := InferRecGroup.belowFvars hrest
      (Subst.onCtx_below hS₂ (le_refl _) (Subst.onCtx_below hS₁ hle1 hctx))
      (fun s' hs' => by
        obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hs'
        exact RecSpec.BelowFvars.onSubst
          (fun p hp => (List.mem_append.mp hp).elim (hS₁ p) (hS₂ p))
          ((hspecs s (List.mem_cons_of_mem _ hs)).mono hle1))
      (fun y hy => lt_of_lt_of_le (htfv y (.inr hy)) hle1)
    intro p hp; rw [List.mem_append, List.mem_append] at hp
    rcases hp with (hp | hp) | hp
    · exact (hS₁ p hp).mono hbrle
    · exact (hS₂ p hp).mono hbrle
    · exact hS₃ p hp
  | consPoly hΦN hinfer huni hesc1 hesc2 hrest =>
    expose_names
    simp only [Expr.tyFreeVars.RecGroup.tyFreeVars, List.mem_append] at htfv
    have hσB : Ty.BelowFvars Φ σ.body := hspecs (.poly σ) List.mem_cons_self
    have hrle := Infer.frontier_le hinfer
    have hΦΦ₁ : Φ ≤ Φ₁ := by omega
    have hctx_pc : CtxBelow (N + σ.paramCount) ctx := fun M hM => (hctx M hM).mono (by omega)
    obtain ⟨hr_τ, hr_s⟩ := Infer.belowFvars hinfer hctx_pc (fun y hy => by
      rcases Expr.tyFreeVars_openTyVars hy with hh | hh
      · have := htfv y (.inl hh); omega
      · have := freshVars_lt y hh; omega)
    have hσopen : Ty.BelowFvars Φ₁ (σ.openVars (freshVars N σ.paramCount)) :=
      Ty.openVars_belowFvars (hσB.mono (by omega))
        (fun x hx => by have := freshVars_lt x hx; omega)
    have hSchk : ∀ p ∈ Schk, Ty.BelowFvars Φ₁ p.2 := UnifyRel.belowFvars huni hr_τ hσopen
    have hbrle := InferRecGroup.frontier_le hrest
    have hS₂ := InferRecGroup.belowFvars hrest
      (Subst.onCtx_below hSchk (le_refl _) (Subst.onCtx_below hr_s hrle hctx_pc))
      (fun s' hs' => by
        obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hs'
        exact RecSpec.BelowFvars.onSubst
          (fun p hp => (List.mem_append.mp hp).elim (hr_s p) (hSchk p))
          ((hspecs s (List.mem_cons_of_mem _ hs)).mono hΦΦ₁))
      (fun y hy => lt_of_lt_of_le (htfv y (.inr hy)) hΦΦ₁)
    intro p hp; rw [List.mem_append, List.mem_append] at hp
    rcases hp with (hp | hp) | hp
    · exact (hr_s p hp).mono hbrle
    · exact (hSchk p hp).mono hbrle
    · exact hS₂ p hp
termination_by Expr.sizeRecGroup bindings
decreasing_by
  all_goals (try subst_vars; try simp only [Expr.sizeRecGroup, Expr.size_openTyVars]; omega)
end


/-! ### M2: substitution domain bound + elaborated-output free-var locality

`Infer.dom_below` extends the frontier discipline to the substitution **domain**
(`∀ p ∈ S, p.1 < Φ'`, via `UnifyRel.dom_mem` + `Infer.belowFvars`).
`Infer.eOut_avoid` is the *locality* of the elaborated output (avoid form): a
variable that is below the input frontier and avoids both the context env and the
skeleton's annotation free vars cannot appear in `eOut`/`τ`/the substitution
range. Together with idempotency (`Infer.eliminates`, M3) these give the prefix-fix
corollary (M4) that the honest soundness needs. -/

mutual
theorem Infer.dom_below {Φ ctx e Φ' S τ} (h : Infer Φ ctx e Φ' S τ) :
    CtxBelow Φ ctx → (∀ y ∈ e.tyFreeVars, y < Φ) → (∀ p ∈ S, p.1 < Φ') := by
  cases h with
  | primLitUnit => intro _ _; simp
  | primLitInt => intro _ _; simp
  | primLitNat => intro _ _; simp
  | primLitChar => intro _ _; simp
  | primBinOpIntAdd => intro _ _; simp
  | primBinOpIntSub => intro _ _; simp
  | primBinOpIntLt _ _ _ _ => intro _ _; simp
  | primBinOpCharLt _ _ _ _ => intro _ _; simp
  | lambda hseed hbody =>
    intro hctx htfv
    cases hseed with
    | none =>
      simp only [Expr.tyFreeVars, Option.elim_none, List.nil_append] at htfv
      exact Infer.dom_below hbody (by
        intro M hM; rcases List.mem_cons.mp hM with rfl | hM
        · exact .fvar (by omega)
        · exact (hctx M hM).mono (by omega))
        (fun y hy => by have := htfv y hy; omega)
    | some _ hcl =>
      expose_names
      simp only [Expr.tyFreeVars, Option.elim_some, List.mem_append] at htfv
      have hparamTy : Ty.BelowFvars Φ paramTy :=
        Ty.BelowFvars.of_freeVars_lt (fun v hv => htfv v (.inl hv))
      exact Infer.dom_below hbody (by
        intro M hM; rcases List.mem_cons.mp hM with rfl | hM
        · exact hparamTy
        · exact hctx M hM)
        (fun y hy => htfv y (.inr hy))
  | app hf harg huni =>
    intro hctx htfv
    simp only [Expr.tyFreeVars, List.mem_append] at htfv
    have hfle := Infer.frontier_le hf
    have hargle := Infer.frontier_le harg
    obtain ⟨hf_τ, hf_s⟩ := Infer.belowFvars hf hctx (fun y hy => htfv y (.inl hy))
    have hf_dom := Infer.dom_below hf hctx (fun y hy => htfv y (.inl hy))
    have hctx1 := Subst.onCtx_below hf_s hfle hctx
    obtain ⟨harg_τ, harg_s⟩ := Infer.belowFvars harg hctx1
      (fun y hy => lt_of_lt_of_le (htfv y (.inr hy)) hfle)
    have harg_dom := Infer.dom_below harg hctx1
      (fun y hy => lt_of_lt_of_le (htfv y (.inr hy)) hfle)
    intro p hp
    rw [List.mem_append, List.mem_append] at hp
    rcases hp with (hp | hp) | hp
    · have := hf_dom p hp; omega
    · have := harg_dom p hp; omega
    · rcases UnifyRel.dom_mem huni p hp with h | h
      · have hb := Subst.onTy_belowFvars harg_s (hf_τ.mono hargle)
        have := hb.mem_lt p.1 h; omega
      · simp only [Ty.freeVars, List.mem_dedup, List.mem_append, List.mem_singleton] at h
        rcases h with h | h
        · have := harg_τ.mem_lt p.1 h; omega
        · omega
  | var => intro _ _; simp
  | ctor => intro _ _; simp
  | letIn hrhs hbody =>
    intro hctx htfv
    simp only [Expr.tyFreeVars, Option.elim_none, List.nil_append, List.mem_append] at htfv
    have hrle := Infer.frontier_le hrhs
    obtain ⟨hr_τ, hr_s⟩ := Infer.belowFvars hrhs hctx (fun y hy => htfv y (.inl hy))
    have hr_dom := Infer.dom_below hrhs hctx (fun y hy => htfv y (.inl hy))
    have hctx1 := Subst.onCtx_below hr_s hrle hctx
    have hb_dom := Infer.dom_below hbody (by
      intro M hM; rcases List.mem_cons.mp hM with rfl | hM
      · exact hr_τ.closeOver
      · exact hctx1 M hM)
      (fun y hy => lt_of_lt_of_le (htfv y (.inr hy)) hrle)
    intro p hp; rw [List.mem_append] at hp
    rcases hp with hp | hp
    · have := hr_dom p hp; have := Infer.frontier_le hbody; omega
    · exact hb_dom p hp
  | letInAnn hσwf hΦN hrhs huni _hesc1 _hesc2 hbody =>
    intro hctx htfv
    expose_names
    simp only [Expr.tyFreeVars, Option.elim_some, List.mem_append] at htfv
    have hrle := Infer.frontier_le hrhs
    have hctx_pc : CtxBelow (N + σ.paramCount) ctx := fun M hM => (hctx M hM).mono (by omega)
    have hσbody : Ty.BelowFvars Φ σ.body :=
      Ty.BelowFvars.of_freeVars_lt (fun v hv => htfv v (.inl (.inl hv)))
    obtain ⟨hr_τ, hr_s⟩ := Infer.belowFvars hrhs hctx_pc (fun y hy => by
      rcases Expr.tyFreeVars_openTyVars hy with h | h
      · have := htfv y (.inl (.inr h)); omega
      · have := freshVars_lt y h; omega)
    have hr_dom := Infer.dom_below hrhs hctx_pc (fun y hy => by
      rcases Expr.tyFreeVars_openTyVars hy with h | h
      · have := htfv y (.inl (.inr h)); omega
      · have := freshVars_lt y h; omega)
    have hσopen : Ty.BelowFvars Φ₁ (σ.openVars (freshVars N σ.paramCount)) :=
      Ty.openVars_belowFvars (hσbody.mono (by omega))
        (fun x hx => by have := freshVars_lt x hx; omega)
    have hSchk : ∀ p ∈ Schk, Ty.BelowFvars Φ₁ p.2 := UnifyRel.belowFvars huni hr_τ hσopen
    have hctx1 : CtxBelow Φ₁ (Schk.onCtx (S₁.onCtx ctx)) :=
      Subst.onCtx_below hSchk (le_refl _) (Subst.onCtx_below hr_s hrle hctx_pc)
    have hb_dom := Infer.dom_below hbody (by
      intro M hM; rcases List.mem_cons.mp hM with rfl | hM
      · exact hσbody.mono (by omega)
      · exact hctx1 M hM)
      (fun y hy => lt_of_lt_of_le (htfv y (.inr hy)) (by omega))
    have hble := Infer.frontier_le hbody
    intro p hp; rw [List.mem_append, List.mem_append] at hp
    rcases hp with (hp | hp) | hp
    · have := hr_dom p hp; omega
    · rcases UnifyRel.dom_mem huni p hp with h | h
      · have := hr_τ.mem_lt p.1 h; omega
      · have := hσopen.mem_lt p.1 h; omega
    · exact hb_dom p hp
  | match_ hscrut hne hbr =>
    intro hctx htfv
    expose_names
    simp only [Expr.tyFreeVars, List.mem_append] at htfv
    have hle1 := Infer.frontier_le hscrut
    obtain ⟨hτs, hS₁⟩ := Infer.belowFvars hscrut hctx (fun y hy => htfv y (.inl hy))
    have hsc_dom := Infer.dom_below hscrut hctx (fun y hy => htfv y (.inl hy))
    have hbrctx : CtxBelow (Φ₁ + 1) (S₁.onCtx ctx) :=
      Subst.onCtx_below (fun p hp => (hS₁ p hp).mono (by omega)) (by omega) hctx
    have hbr_dom := InferBranches.dom_below hbr hbrctx (hτs.mono (by omega)) (.fvar (by omega))
      (fun y hy => by have := htfv y (.inr hy); omega)
    intro p hp; rw [List.mem_append] at hp
    rcases hp with hp | hp
    · have := hsc_dom p hp; have := InferBranches.frontier_le hbr; omega
    · exact hbr_dom p hp
  | letRec hwf hgroup hceiling hbody =>
    intro hctx htfv
    expose_names
    simp only [Expr.tyFreeVars, List.mem_append] at htfv
    have hlen : bindings.length = anns.length := by
      have h₁ := InferRecGroup.length_eq hgroup
      rw [RecSpec.init_length] at h₁
      exact h₁
    have hspecs_init : ∀ s ∈ RecSpec.init Φ anns, s.BelowFvars (Φ + bindings.length) := by
      intro s hs
      rcases List.mem_iff_getElem.mp hs with ⟨j, hj, rfl⟩
      have hlenj : j < anns.length := by
        have h₂ := RecSpec.init_length Φ anns
        omega
      have hget : (RecSpec.init Φ anns)[j] = RecSpec.mono (.fvar (Φ + j)) := by
        have h₁ := List.getElem?_eq_getElem hj
        rw [RecSpec.init_getElem? Φ anns j, List.getElem?_eq_getElem hlenj] at h₁
        injection h₁ with hEq
        exact hEq.symm
      rw [hget]
      refine Ty.BelowFvars.fvar ?_
      omega
    have hgrpLe : Φ + bindings.length ≤ Φ₁ := InferRecGroup.frontier_le hgroup
    have hctxGroup : CtxBelow (Φ + bindings.length)
        { ctx with env := (RecSpec.init Φ anns).map (RecSpec.rhsEntry [] []) ++ ctx.env } := by
      intro M hM
      rcases List.mem_append.mp hM with hM1 | hM2
      · obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hM1
        exact RecSpec.rhsEntry_nil_belowFvars (hspecs_init s hs)
      · exact (hctx M hM2).mono (by omega)
    have htfv_group : ∀ y ∈ Expr.tyFreeVars.RecGroup.tyFreeVars bindings,
        y < Φ + bindings.length := by
      intro y hy
      have := htfv y (.inl (.inr hy))
      omega
    have hS₁ : ∀ p ∈ S₁, Ty.BelowFvars Φ₁ p.2 :=
      InferRecGroup.belowFvars hgroup hctxGroup hspecs_init htfv_group
    have hspecs_post : ∀ s' ∈ (RecSpec.init Φ anns).map (RecSpec.onSubst S₁),
        s'.BelowFvars Φ₁ := by
      intro s' hs'
      obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hs'
      exact RecSpec.BelowFvars.onSubst hS₁ ((hspecs_init s hs).mono hgrpLe)
    have hbodyCtx : CtxBelow Φ₁
        { (S₁.onCtx ctx) with
          env := RecSpecs.ceilingSchemes
                   (genGroupVars (RecGroup.rigidVars anns bindings) (S₁.onCtx ctx).env
                     (RecSpecs.monoTys ((RecSpec.init Φ anns).map (RecSpec.onSubst S₁))))
                   anns
                   ((RecSpec.init Φ anns).map (RecSpec.onSubst S₁))
                 ++ (S₁.onCtx ctx).env } := by
      intro M hM
      rcases List.mem_append.mp hM with hM1 | hM2
      · obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hM1
        have hpa : p.1 ∈ anns := (List.of_mem_zip hp).1
        have hps : p.2 ∈ (RecSpec.init Φ anns).map (RecSpec.onSubst S₁) := (List.of_mem_zip hp).2
        cases p with
        | mk a s =>
          cases a with
          | some σ =>
            refine Ty.BelowFvars.of_freeVars_lt (fun v hv => ?_)
            have hann := Expr.scheme_body_mem_annList_tyFreeVars hpa hv
            have := htfv v (.inl (.inl hann))
            omega
          | none =>
            exact RecSpec.bodyScheme_belowFvars (hspecs_post s hps)
      · exact Subst.onCtx_below hS₁ (by omega) hctx M hM2
    have hb_dom : ∀ p ∈ S₂, p.1 < Φ' :=
      Infer.dom_below hbody hbodyCtx (fun y hy => by
        have := htfv y (.inr hy)
        omega)
    have hS₁_dom : ∀ p ∈ S₁, p.1 < Φ₁ :=
      InferRecGroup.dom_below hgroup hctxGroup hspecs_init htfv_group
    intro p hp; rw [List.mem_append] at hp
    rcases hp with hp | hp
    · have := hS₁_dom p hp; have := Infer.frontier_le hbody; omega
    · exact hb_dom p hp
termination_by e.size
decreasing_by
  all_goals (try subst_vars; try simp only [Expr.size, Expr.size_openTyVars]; omega)
theorem InferBranches.dom_below {Φ ctx scrutTy ρ brs Φ' S}
    (h : InferBranches Φ ctx scrutTy ρ brs Φ' S)
    (hctx : CtxBelow Φ ctx) (hscrutTy : Ty.BelowFvars Φ scrutTy) (hρ : Ty.BelowFvars Φ ρ)
    (htfv : ∀ y ∈ Expr.tyFreeVars.BranchList.tyFreeVars brs, y < Φ) :
    (∀ p ∈ S, p.1 < Φ') := by
  cases h with
  | nil => simp
  | cons hlook hn huni0 hbody huni hrest =>
    expose_names
    simp only [Expr.tyFreeVars.BranchList.tyFreeVars, List.mem_append] at htfv
    have hS₀ : ∀ p ∈ S₀, Ty.BelowFvars (Φ + ctor.paramCount) p.2 :=
      UnifyRel.belowFvars huni0 (hscrutTy.mono (by omega))
        (.customTy (fun t ht => by
          obtain ⟨x, hx, rfl⟩ := List.mem_map.mp ht
          exact .fvar (by have := freshVars_lt x hx; omega)))
    have hS₀dom : ∀ p ∈ S₀, p.1 < Φ + ctor.paramCount := by
      intro p hp
      rcases UnifyRel.dom_mem huni0 p hp with h | h
      · have := (hscrutTy.mono (show Φ ≤ Φ + ctor.paramCount by omega)).mem_lt p.1 h; omega
      · simp only [Ty.freeVars] at h
        rw [mem_TyList_freeVars] at h
        obtain ⟨t, ht, hgt⟩ := h
        obtain ⟨x, hx, rfl⟩ := List.mem_map.mp ht
        simp only [Ty.freeVars, List.mem_singleton] at hgt
        have := freshVars_lt x hx; omega
    have hbctx := branchBindings_below (ctorr := ctor)
        (ta := ((freshVars Φ ctor.paramCount).map (Ty.fvar ·)).map S₀.onTy)
        (Subst.onCtx_below hS₀ (by omega) hctx)
        (fun t ht => by
          obtain ⟨v, hv, rfl⟩ := List.mem_map.mp ht
          obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hv
          exact Subst.onTy_belowFvars hS₀ (.fvar (by have := freshVars_lt x hx; omega)))
    obtain ⟨hτb, hS₁⟩ := Infer.belowFvars hbody hbctx (fun y hy => by have := htfv y (.inl hy); omega)
    have hS₁dom := Infer.dom_below hbody hbctx (fun y hy => by have := htfv y (.inl hy); omega)
    have hle0 : Φ + ctor.paramCount ≤ Φ₁ := Infer.frontier_le hbody
    have hS₀ρ : Ty.BelowFvars Φ₁ (S₀.onTy ρ) :=
      (Subst.onTy_belowFvars hS₀ (hρ.mono (by omega))).mono hle0
    have hS₀scrut : Ty.BelowFvars Φ₁ (S₀.onTy scrutTy) :=
      (Subst.onTy_belowFvars hS₀ (hscrutTy.mono (by omega))).mono hle0
    have hS₁ρ := Subst.onTy_belowFvars hS₁ hS₀ρ
    have hS₂ := UnifyRel.belowFvars huni hτb hS₁ρ
    have hS₂dom : ∀ p ∈ S₂, p.1 < Φ₁ := by
      intro p hp
      rcases UnifyRel.dom_mem huni p hp with h | h
      · have := hτb.mem_lt p.1 h; omega
      · have := hS₁ρ.mem_lt p.1 h; omega
    have hctx1 : CtxBelow Φ₁ (S₂.onCtx (S₁.onCtx (S₀.onCtx ctx))) :=
      Subst.onCtx_below hS₂ (le_refl _)
        (Subst.onCtx_below hS₁ (le_refl _)
          (Subst.onCtx_below (fun p hp => (hS₀ p hp).mono hle0) (by omega) hctx))
    have hrest_dom := InferBranches.dom_below hrest hctx1
      (Subst.onTy_belowFvars hS₂ (Subst.onTy_belowFvars hS₁ hS₀scrut))
      (Subst.onTy_belowFvars hS₂ (Subst.onTy_belowFvars hS₁ hS₀ρ))
      (fun y hy => lt_of_lt_of_le (htfv y (.inr hy)) (by omega))
    have hbrle := InferBranches.frontier_le hrest
    intro p hp; rw [List.mem_append, List.mem_append, List.mem_append] at hp
    rcases hp with ((hp | hp) | hp) | hp
    · have := hS₀dom p hp; omega
    · have := hS₁dom p hp; omega
    · have := hS₂dom p hp; omega
    · exact hrest_dom p hp
  | consWild hbody huni hrest =>
    expose_names
    simp only [Expr.tyFreeVars.BranchList.tyFreeVars, List.mem_append] at htfv
    have hle1 := Infer.frontier_le hbody
    obtain ⟨hτb, hS₁⟩ := Infer.belowFvars hbody hctx (fun y hy => htfv y (.inl hy))
    have hS₁dom := Infer.dom_below hbody hctx (fun y hy => htfv y (.inl hy))
    have hS₁ρ := Subst.onTy_belowFvars hS₁ (hρ.mono hle1)
    have hS₂ := UnifyRel.belowFvars huni hτb hS₁ρ
    have hS₂dom : ∀ p ∈ S₂, p.1 < Φ₁ := by
      intro p hp
      rcases UnifyRel.dom_mem huni p hp with h | h
      · have := hτb.mem_lt p.1 h; omega
      · have := hS₁ρ.mem_lt p.1 h; omega
    have hctx1 := Subst.onCtx_below hS₂ (le_refl _) (Subst.onCtx_below hS₁ hle1 hctx)
    have hrest_dom := InferBranches.dom_below hrest hctx1
      (Subst.onTy_belowFvars hS₂ (Subst.onTy_belowFvars hS₁ (hscrutTy.mono hle1)))
      (Subst.onTy_belowFvars hS₂ (Subst.onTy_belowFvars hS₁ (hρ.mono hle1)))
      (fun y hy => lt_of_lt_of_le (htfv y (.inr hy)) hle1)
    have hbrle := InferBranches.frontier_le hrest
    intro p hp; rw [List.mem_append, List.mem_append] at hp
    rcases hp with (hp | hp) | hp
    · have := hS₁dom p hp; omega
    · have := hS₂dom p hp; omega
    · exact hrest_dom p hp
termination_by Expr.sizeBranches brs
decreasing_by
  all_goals (try subst_vars; try simp only [Expr.sizeBranches]; omega)
/-- Fused `InferRecGroup` substitution-domain bound (consMono + consPoly). -/
theorem InferRecGroup.dom_below {Φ ctx bindings specs Φ' S}
    (h : InferRecGroup Φ ctx bindings specs Φ' S)
    (hctx : CtxBelow Φ ctx) (hspecs : ∀ s ∈ specs, s.BelowFvars Φ)
    (htfv : ∀ y ∈ Expr.tyFreeVars.RecGroup.tyFreeVars bindings, y < Φ) :
    (∀ p ∈ S, p.1 < Φ') := by
  cases h with
  | nil => simp
  | consMono he huni hrest =>
    expose_names
    simp only [Expr.tyFreeVars.RecGroup.tyFreeVars, List.mem_append] at htfv
    have hle1 := Infer.frontier_le he
    obtain ⟨hτ', hS₁⟩ := Infer.belowFvars he hctx (fun y hy => htfv y (.inl hy))
    have hS₁dom := Infer.dom_below he hctx (fun y hy => htfv y (.inl hy))
    have hτB : Ty.BelowFvars Φ τ := hspecs (.mono τ) List.mem_cons_self
    have hS₁τ := Subst.onTy_belowFvars hS₁ (hτB.mono hle1)
    have hS₂ := UnifyRel.belowFvars huni hτ' hS₁τ
    have hS₂dom : ∀ p ∈ S₂, p.1 < Φ₁ := by
      intro p hp
      rcases UnifyRel.dom_mem huni p hp with h | h
      · exact hτ'.mem_lt p.1 h
      · exact hS₁τ.mem_lt p.1 h
    have hrest_dom := InferRecGroup.dom_below hrest
      (Subst.onCtx_below hS₂ (le_refl _) (Subst.onCtx_below hS₁ hle1 hctx))
      (fun s' hs' => by
        obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hs'
        exact RecSpec.BelowFvars.onSubst
          (fun p hp => (List.mem_append.mp hp).elim (hS₁ p) (hS₂ p))
          ((hspecs s (List.mem_cons_of_mem _ hs)).mono hle1))
      (fun y hy => lt_of_lt_of_le (htfv y (.inr hy)) hle1)
    have hbrle := InferRecGroup.frontier_le hrest
    intro p hp; rw [List.mem_append, List.mem_append] at hp
    rcases hp with (hp | hp) | hp
    · have := hS₁dom p hp; omega
    · have := hS₂dom p hp; omega
    · exact hrest_dom p hp
  | consPoly hΦN hinfer huni hesc1 hesc2 hrest =>
    expose_names
    simp only [Expr.tyFreeVars.RecGroup.tyFreeVars, List.mem_append] at htfv
    have hσB : Ty.BelowFvars Φ σ.body := hspecs (.poly σ) List.mem_cons_self
    have hrle := Infer.frontier_le hinfer
    have hΦΦ₁ : Φ ≤ Φ₁ := by omega
    have hctx_pc : CtxBelow (N + σ.paramCount) ctx := fun M hM => (hctx M hM).mono (by omega)
    have hΦropen : ∀ y ∈ (e.openTyVars (freshVars N σ.paramCount)).tyFreeVars,
        y < N + σ.paramCount := fun y hy => by
      rcases Expr.tyFreeVars_openTyVars hy with hh | hh
      · have := htfv y (.inl hh); omega
      · have := freshVars_lt y hh; omega
    obtain ⟨hr_τ, hr_s⟩ := Infer.belowFvars hinfer hctx_pc hΦropen
    have hr_dom := Infer.dom_below hinfer hctx_pc hΦropen
    have hσopen : Ty.BelowFvars Φ₁ (σ.openVars (freshVars N σ.paramCount)) :=
      Ty.openVars_belowFvars (hσB.mono (by omega))
        (fun x hx => by have := freshVars_lt x hx; omega)
    have hSchk : ∀ p ∈ Schk, Ty.BelowFvars Φ₁ p.2 := UnifyRel.belowFvars huni hr_τ hσopen
    have hSchkdom : ∀ p ∈ Schk, p.1 < Φ₁ := by
      intro p hp
      rcases UnifyRel.dom_mem huni p hp with hh | hh
      · exact hr_τ.mem_lt p.1 hh
      · exact hσopen.mem_lt p.1 hh
    have hrest_dom := InferRecGroup.dom_below hrest
      (Subst.onCtx_below hSchk (le_refl _) (Subst.onCtx_below hr_s hrle hctx_pc))
      (fun s' hs' => by
        obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hs'
        exact RecSpec.BelowFvars.onSubst
          (fun p hp => (List.mem_append.mp hp).elim (hr_s p) (hSchk p))
          ((hspecs s (List.mem_cons_of_mem _ hs)).mono hΦΦ₁))
      (fun y hy => lt_of_lt_of_le (htfv y (.inr hy)) hΦΦ₁)
    have hbrle := InferRecGroup.frontier_le hrest
    intro p hp; rw [List.mem_append, List.mem_append] at hp
    rcases hp with (hp | hp) | hp
    · have := hr_dom p hp; omega
    · have := hSchkdom p hp; omega
    · exact hrest_dom p hp
termination_by Expr.sizeRecGroup bindings
decreasing_by
  all_goals (try subst_vars; try simp only [Expr.sizeRecGroup, Expr.size_openTyVars]; omega)
end

/-- A var avoiding both the context env and a substitution's range avoids the
    substituted context env. -/
theorem Subst.onCtx_avoid {S : Subst} {ctx : Ctx} {w : Nat}
    (hctx : ∀ M ∈ ctx.env, w ∉ M.body.freeVars) (hS : ∀ p ∈ S, w ∉ p.2.freeVars) :
    ∀ M ∈ (S.onCtx ctx).env, w ∉ M.body.freeVars := by
  intro M hM
  simp only [Subst.onCtx, Subst.onEnv] at hM
  obtain ⟨M0, hM0, rfl⟩ := List.mem_map.mp hM
  intro hc
  simp only [Subst.onPolyTy] at hc
  rcases Subst.mem_freeVars_onTy hc with h | ⟨p, hp, hvp⟩
  · exact hctx M0 hM0 h
  · exact hS p hp hvp

/-- `RecGroup.tyFreeVars` membership decomposes to a member binding. -/
theorem Expr.mem_recGroupTyFreeVars {L : List Expr} {w : Nat}
    (h : w ∈ Expr.tyFreeVars.RecGroup.tyFreeVars L) : ∃ e ∈ L, w ∈ e.tyFreeVars := by
  induction L with
  | nil => simp [Expr.tyFreeVars.RecGroup.tyFreeVars] at h
  | cons hd tl ih =>
    simp only [Expr.tyFreeVars.RecGroup.tyFreeVars, List.mem_append] at h
    rcases h with h | h
    · exact ⟨hd, List.mem_cons_self, h⟩
    · obtain ⟨e, he, hwe⟩ := ih h; exact ⟨e, List.mem_cons_of_mem _ he, hwe⟩

/-- Every member of a `bvarRange` block is a (free-var-free) bound variable. -/
private theorem Ty.bvarRangeFrom_freeVars_nil :
    ∀ (k s : Nat), ∀ t ∈ Ty.bvarRangeFrom s k, t.freeVars = ([] : List Nat)
  | 0, s => by intro t ht; simp [Ty.bvarRangeFrom] at ht
  | k + 1, s => by
      intro t ht
      rcases List.mem_cons.mp ht with rfl | ht
      · rfl
      · exact Ty.bvarRangeFrom_freeVars_nil k (s + 1) t ht

/-- A `bvarRange` projection block contributes no free type variables. -/
theorem Ty.not_mem_bvarRange_flatMap_freeVars {y k : Nat} :
    y ∉ (Ty.bvarRange k).flatMap Ty.freeVars := by
  intro hc
  rw [List.mem_flatMap] at hc
  obtain ⟨t, ht, hyt⟩ := hc
  rw [Ty.bvarRangeFrom_freeVars_nil k 0 t ht] at hyt
  exact absurd hyt List.not_mem_nil

/-- `AnnList.tyFreeVars` membership decomposes to a stored scheme's body. -/
theorem Expr.mem_annList_tyFreeVars_ex {anns : List (Option PolyTy)} {y : Nat}
    (h : y ∈ Expr.tyFreeVars.AnnList.tyFreeVars anns) :
    ∃ σ, some σ ∈ anns ∧ y ∈ σ.body.freeVars := by
  induction anns with
  | nil => simp [Expr.tyFreeVars.AnnList.tyFreeVars] at h
  | cons a as ih =>
    cases a with
    | none =>
      simp only [Expr.tyFreeVars.AnnList.tyFreeVars, Option.elim_none, List.nil_append] at h
      obtain ⟨σ, h1, h2⟩ := ih h
      exact ⟨σ, List.mem_cons_of_mem _ h1, h2⟩
    | some σ0 =>
      simp only [Expr.tyFreeVars.AnnList.tyFreeVars, Option.elim_some, List.mem_append] at h
      rcases h with h | h
      · exact ⟨σ0, List.mem_cons_self, h⟩
      · obtain ⟨σ, h1, h2⟩ := ih h
        exact ⟨σ, List.mem_cons_of_mem _ h1, h2⟩

/-- Every free type var of the mixed Λ-outside nest comes from the stored anns, a
    member spec (its monotype / scheme body), a raw binding, or the body —
    shifting and closing introduce no new type vars, and the poly projections'
    `bvarRange` tyArgs are fvar-free. The fused nest's inner `.letRec anns …` node
    carries the full `anns` at every level, hence the anns disjunct. -/
theorem Subst.notMemOnTy {S : Subst} {w : Nat} {τ : Ty}
    (hS : ∀ p ∈ S, w ∉ p.2.freeVars) (hτ : w ∉ τ.freeVars) : w ∉ (S.onTy τ).freeVars := by
  intro hc
  rcases Subst.mem_freeVars_onTy hc with h | ⟨p, hp, hvp⟩
  · exact hτ h
  · exact hS p hp hvp

/-- `onSubst` transport of spec free-var avoidance (needs range avoidance). -/
theorem RecSpec.notMem_freeVars_onSubst {S : Subst} {w : Nat}
    (hSran : ∀ p ∈ S, w ∉ p.2.freeVars) {s : RecSpec}
    (h : w ∉ s.freeVars) : w ∉ (RecSpec.onSubst S s).freeVars := by
  cases s with
  | mono τ => exact Subst.notMemOnTy hSran h
  | poly σ => exact h

/-- A var avoiding all opening args (and the body) avoids the opened type. -/
theorem Ty.not_mem_freeVars_openWith {Vs : List Ty} {w : Nat} (hVs : ∀ v ∈ Vs, w ∉ v.freeVars) :
    ∀ {X : Ty}, w ∉ X.freeVars → w ∉ (Ty.openWith Vs X).freeVars := by
  intro X
  induction X using Ty.rec_strong with
  | prim p => intro _; simp [Ty.openWith, Ty.instantiate, Ty.freeVars]
  | fvar n => intro hX; simpa [Ty.openWith, Ty.instantiate, Ty.freeVars] using hX
  | bvar i =>
    intro _
    simp only [Ty.openWith, Ty.instantiate]
    cases h : Vs[i]? with
    | none => simp [Ty.freeVars]
    | some v => simp only [Option.getD_some]; exact hVs v (List.mem_of_getElem? h)
  | arrow a b iha ihb =>
    intro hX
    simp only [Ty.freeVars, List.mem_dedup, List.mem_append, not_or] at hX
    simp only [Ty.openWith, Ty.instantiate, Ty.freeVars, List.mem_dedup, List.mem_append, not_or]
    exact ⟨iha hX.1, ihb hX.2⟩
  | customTy nm tys ih =>
    intro hX
    have hX' : ∀ t ∈ tys, w ∉ t.freeVars := fun t ht hc =>
      hX (by rw [Ty.freeVars]; exact TyList.mem_freeVars_of_mem ht hc)
    simp only [Ty.openWith, Ty.instantiate, TyList.instantiate_eq_map, Ty.freeVars]
    intro hc
    rw [mem_TyList_freeVars] at hc
    obtain ⟨t', ht', hwt'⟩ := hc
    obtain ⟨t0, ht0, rfl⟩ := List.mem_map.mp ht'
    exact ih t0 ht0 (hX' t0 ht0) hwt'
  | bl lo hi e ih =>
    intro hX
    simp only [Ty.openWith, Ty.instantiate, Ty.freeVars]
    exact ih (fun hc => hX (by simpa only [Ty.freeVars] using hc))

/-- `RecGroup.tyFreeVars` membership reconstruction (`_of` direction). -/
theorem Expr.mem_recGroupTyFreeVars_of {L : List Expr} {e : Expr} {w : Nat}
    (he : e ∈ L) (hw : w ∈ e.tyFreeVars) : w ∈ Expr.tyFreeVars.RecGroup.tyFreeVars L := by
  induction L with
  | nil => exact absurd he List.not_mem_nil
  | cons hd tl ih =>
    simp only [Expr.tyFreeVars.RecGroup.tyFreeVars, List.mem_append]
    rcases List.mem_cons.mp he with h | h
    · subst h; exact Or.inl hw
    · exact Or.inr (ih h)

/-- `BranchList.tyFreeVars` membership decomposition. -/
theorem Expr.mem_branchListTyFreeVars {brs : List (MatchPattern × Expr)} {w : Nat}
    (h : w ∈ Expr.tyFreeVars.BranchList.tyFreeVars brs) : ∃ pb ∈ brs, w ∈ pb.2.tyFreeVars := by
  induction brs with
  | nil => simp [Expr.tyFreeVars.BranchList.tyFreeVars] at h
  | cons hd tl ih =>
    obtain ⟨p, b⟩ := hd
    simp only [Expr.tyFreeVars.BranchList.tyFreeVars, List.mem_append] at h
    rcases h with h | h
    · exact ⟨(p, b), List.mem_cons_self, h⟩
    · obtain ⟨pb, hpb, hwpb⟩ := ih h; exact ⟨pb, List.mem_cons_of_mem _ hpb, hwpb⟩

/-- `BranchList.tyFreeVars` membership reconstruction (`_of` direction). -/
theorem Expr.mem_branchListTyFreeVars_of {brs : List (MatchPattern × Expr)} {p : MatchPattern}
    {b : Expr} {w : Nat} (hmem : (p, b) ∈ brs) (hw : w ∈ b.tyFreeVars) :
    w ∈ Expr.tyFreeVars.BranchList.tyFreeVars brs := by
  induction brs with
  | nil => exact absurd hmem List.not_mem_nil
  | cons hd tl ih =>
    obtain ⟨p', b'⟩ := hd
    simp only [Expr.tyFreeVars.BranchList.tyFreeVars, List.mem_append]
    rcases List.mem_cons.mp hmem with h | h
    · rw [Prod.mk.injEq] at h; obtain ⟨_, hb⟩ := h; subst hb; exact Or.inl hw
    · exact Or.inr (ih h)

/-- A free var of an iterated `substFvars`-image comes from the original type or
    one of the substituted-in image types. -/
theorem Ty.mem_freeVars_substFvars {S : List (Nat × Ty)} {t : Ty} {w : Nat}
    (h : w ∈ (Ty.substFvars S t).freeVars) : w ∈ t.freeVars ∨ ∃ p ∈ S, w ∈ p.2.freeVars := by
  induction S generalizing t with
  | nil => exact Or.inl h
  | cons hd S' ih =>
    obtain ⟨Z, U⟩ := hd
    rcases ih h with hh | ⟨p, hp, hwp⟩
    · rcases Ty.mem_freeVars_substFvar hh with h1 | h1
      · exact Or.inl h1
      · exact Or.inr ⟨(Z, U), List.mem_cons_self, h1⟩
    · exact Or.inr ⟨p, List.mem_cons_of_mem _ hp, hwp⟩

/-- A free type var of a fused group's `RecAnn.substFvars`-mapped ann list comes from
    the original anns or the substitution range. -/
private theorem AnnList.mem_tyFreeVars_substFvars {S : List (Nat × Ty)} {w : Nat} :
    ∀ (anns : List (Option PolyTy)),
      w ∈ Expr.tyFreeVars.AnnList.tyFreeVars (anns.map (RecAnn.substFvars S)) →
      w ∈ Expr.tyFreeVars.AnnList.tyFreeVars anns ∨ ∃ p ∈ S, w ∈ p.2.freeVars := by
  intro anns
  induction anns with
  | nil => intro h; simp [Expr.tyFreeVars.AnnList.tyFreeVars] at h
  | cons a as ih =>
    intro h
    cases a with
    | none =>
      simp only [List.map_cons, RecAnn.substFvars_none, Expr.tyFreeVars.AnnList.tyFreeVars,
        Option.elim, List.nil_append] at h ⊢
      exact ih h
    | some σ =>
      simp only [List.map_cons, RecAnn.substFvars_some, Expr.tyFreeVars.AnnList.tyFreeVars,
        Option.elim, List.mem_append, PolyTy.body_substFvars] at h ⊢
      rcases h with h | h
      · rcases Ty.mem_freeVars_substFvars h with hh | hh
        · exact .inl (.inl hh)
        · exact .inr hh
      · rcases ih h with hh | hh
        · exact .inl (.inr hh)
        · exact .inr hh

/-- A free type var of `e.substTyFvars S` comes from `e` or one of the image types.
    (Re-based off `NoRecAnn`: `substTyFvars` rewrites `letRecAnn` schemes by
    `PolyTy.substFvars` and recurses into bindings/body, so the membership split holds
    unconditionally.) Uses the public `substTyFvars_*` distribution lemmas. -/
theorem Expr.mem_tyFreeVars_substTyFvars {S : List (Nat × Ty)} {w : Nat} :
    ∀ {e : Expr}, w ∈ (e.substTyFvars S).tyFreeVars →
      w ∈ e.tyFreeVars ∨ ∃ p ∈ S, w ∈ p.2.freeVars := by
  intro e
  induction e using Expr.rec_strong with
  | primLit p =>
    intro h
    rw [Expr.substTyFvars_eq_self_of_not_mem_tyFreeVars (by simp [Expr.tyFreeVars])] at h
    simp [Expr.tyFreeVars] at h
  | primBinOp op =>
    intro h
    rw [Expr.substTyFvars_eq_self_of_not_mem_tyFreeVars (by simp [Expr.tyFreeVars])] at h
    simp [Expr.tyFreeVars] at h
  | ctor c =>
    intro h
    rw [Expr.substTyFvars_eq_self_of_not_mem_tyFreeVars (by simp [Expr.tyFreeVars])] at h
    simp [Expr.tyFreeVars] at h
  | var i =>
    intro h
    simp [Expr.substTyFvars_var, Expr.tyFreeVars] at h
  | lambda ann body ih =>
    intro h
    rw [Expr.substTyFvars_lambda] at h
    cases ann with
    | none =>
      simp only [Expr.tyFreeVars, Option.map_none, Option.elim_none, List.nil_append] at h ⊢
      exact ih h
    | some t =>
      simp only [Expr.tyFreeVars, Option.map_some, Option.elim_some, List.mem_append] at h ⊢
      rcases h with h | h
      · rcases Ty.mem_freeVars_substFvars h with hh | hh
        · exact Or.inl (Or.inl hh)
        · exact Or.inr hh
      · rcases ih h with hh | hh
        · exact Or.inl (Or.inr hh)
        · exact Or.inr hh
  | app f arg ihf iharg =>
    intro h
    rw [Expr.substTyFvars_app] at h
    simp only [Expr.tyFreeVars, List.mem_append] at h ⊢
    rcases h with h | h
    · rcases ihf h with hh | hh
      · exact Or.inl (Or.inl hh)
      · exact Or.inr hh
    · rcases iharg h with hh | hh
      · exact Or.inl (Or.inr hh)
      · exact Or.inr hh
  | letIn ann rhs body ihr ihb =>
    intro h
    rw [Expr.substTyFvars_letIn] at h
    cases ann with
    | none =>
      simp only [Expr.tyFreeVars, Option.map_none, Option.elim_none, List.nil_append,
        List.mem_append] at h ⊢
      rcases h with h | h
      · rcases ihr h with hh | hh
        · exact Or.inl (Or.inl hh)
        · exact Or.inr hh
      · rcases ihb h with hh | hh
        · exact Or.inl (Or.inr hh)
        · exact Or.inr hh
    | some σ =>
      simp only [Expr.tyFreeVars, Option.map_some, Option.elim_some, List.mem_append] at h ⊢
      rcases h with (h | h) | h
      · rcases Ty.mem_freeVars_substFvars h with hh | hh
        · exact Or.inl (Or.inl (Or.inl hh))
        · exact Or.inr hh
      · rcases ihr h with hh | hh
        · exact Or.inl (Or.inl (Or.inr hh))
        · exact Or.inr hh
      · rcases ihb h with hh | hh
        · exact Or.inl (Or.inr hh)
        · exact Or.inr hh
  | match_ scrut branches ihs ihbr =>
    intro h
    rw [Expr.substTyFvars_match] at h
    simp only [Expr.tyFreeVars, List.mem_append] at h ⊢
    rcases h with h | h
    · rcases ihs h with hh | hh
      · exact Or.inl (Or.inl hh)
      · exact Or.inr hh
    · obtain ⟨pb, hpb, hwpb⟩ := Expr.mem_branchListTyFreeVars h
      obtain ⟨pb0, hpb0, rfl⟩ := List.mem_map.mp hpb
      obtain ⟨p0, b0⟩ := pb0
      rcases ihbr p0 b0 hpb0 hwpb with hh | hh
      · exact Or.inl (Or.inr (Expr.mem_branchListTyFreeVars_of hpb0 hh))
      · exact Or.inr hh
  | letRec anns bindings body ihbs ihb =>
    intro h
    rw [Expr.substTyFvars_letRec] at h
    simp only [Expr.tyFreeVars, List.mem_append] at h ⊢
    rcases h with (h | h) | h
    · rcases AnnList.mem_tyFreeVars_substFvars anns h with hh | hh
      · exact Or.inl (Or.inl (Or.inl hh))
      · exact Or.inr hh
    · obtain ⟨e', he', hwe'⟩ := Expr.mem_recGroupTyFreeVars h
      obtain ⟨e, he, rfl⟩ := List.mem_map.mp he'
      rcases ihbs e he hwe' with hh | hh
      · exact Or.inl (Or.inl (Or.inr (Expr.mem_recGroupTyFreeVars_of he hh)))
      · exact Or.inr hh
    · rcases ihb h with hh | hh
      · exact Or.inl (Or.inr hh)
      · exact Or.inr hh

/-- A var avoiding `e`'s free type vars and the substitution range avoids
    `e.substTyFvars S`'s free type vars. -/
theorem Expr.notMem_tyFreeVars_substTyFvars {S : List (Nat × Ty)} {e : Expr} {w : Nat}
    (hwe : w ∉ e.tyFreeVars) (hwS : ∀ p ∈ S, w ∉ p.2.freeVars) :
    w ∉ (e.substTyFvars S).tyFreeVars := by
  intro hc
  rcases Expr.mem_tyFreeVars_substTyFvars hc with h | ⟨p, hp, hwp⟩
  · exact hwe h
  · exact hwS p hp hwp

mutual
/-- **Locality (avoid form).** A var below the input frontier that avoids the
    context env and the skeleton's annotation free vars also avoids the inferred
    substitution range, result type, and elaborated output. This is the
    characterisation the prefix-fix corollary (M4) needs. -/
theorem Infer.eOut_avoid {Φ ctx e Φ' S τ} (h : Infer Φ ctx e Φ' S τ) :
    ∀ {w : Nat}, w < Φ → (∀ M ∈ ctx.env, w ∉ M.body.freeVars) → w ∉ e.tyFreeVars →
    (∀ p ∈ S, w ∉ p.2.freeVars) ∧ w ∉ τ.freeVars := by
  cases h with
  | primLitUnit => intro w _ _ _; exact ⟨by simp, by simp [Ty.freeVars]⟩
  | primLitInt => intro w _ _ _; exact ⟨by simp, by simp [Ty.freeVars]⟩
  | primLitNat => intro w _ _ _; exact ⟨by simp, by simp [Ty.freeVars]⟩
  | primLitChar => intro w _ _ _; exact ⟨by simp, by simp [Ty.freeVars]⟩
  | primBinOpIntAdd => intro w _ _ _; exact ⟨by simp, by simp [Ty.freeVars]⟩
  | primBinOpIntSub => intro w _ _ _; exact ⟨by simp, by simp [Ty.freeVars]⟩
  | primBinOpIntLt _ _ _ _ => intro w _ _ _; exact ⟨by simp, by simp [Ty.freeVars, TyList.freeVars]⟩
  | primBinOpCharLt _ _ _ _ => intro w _ _ _; exact ⟨by simp, by simp [Ty.freeVars, TyList.freeVars]⟩
  | var hlook =>
    intro w hwΦ hctx _
    refine ⟨by simp, ?_⟩
    intro hc
    rcases Ty.freeVars_openVars_subset w hc with h | h
    · exact hctx _ (List.mem_of_getElem? hlook) h
    · have := freshVars_ge w h; omega
  | ctor hlook =>
    intro w hwΦ _ _
    refine ⟨by simp, ?_⟩
    intro hc
    rcases Ty.freeVars_openVars_subset w hc with h | h
    · exact (Ctor.toTy_body_noFreeVars _).not_mem_freeVars w h
    · have := freshVars_ge w h; omega
  | lambda hseed hbody =>
    intro w hwΦ hctx hwe
    cases hseed with
    | none =>
      simp only [Expr.tyFreeVars, Option.elim_none, List.nil_append] at hwe
      obtain ⟨hbS, hbτ⟩ := Infer.eOut_avoid hbody (w := w) (by omega)
        (by intro M hM; rcases List.mem_cons.mp hM with rfl | hM
            · intro hc; simp only [PolyTy.mkTrivial, Ty.freeVars, List.mem_singleton] at hc; omega
            · exact hctx M hM)
        hwe
      refine ⟨hbS, ?_⟩
      simp only [Ty.freeVars, List.mem_dedup, List.mem_append, not_or]
      refine ⟨?_, hbτ⟩
      intro hc
      rcases Subst.mem_freeVars_onTy hc with h | ⟨p, hp, hvp⟩
      · simp only [Ty.freeVars, List.mem_singleton] at h; omega
      · exact hbS p hp hvp
    | some T hT =>
      simp only [Expr.tyFreeVars, Option.elim_some, List.mem_append, not_or] at hwe
      obtain ⟨hbS, hbτ⟩ := Infer.eOut_avoid hbody (w := w) hwΦ
        (by intro M hM; rcases List.mem_cons.mp hM with rfl | hM
            · simpa only [PolyTy.mkTrivial] using hwe.1
            · exact hctx M hM)
        hwe.2
      refine ⟨hbS, ?_⟩
      simp only [Ty.freeVars, List.mem_dedup, List.mem_append, not_or]
      exact ⟨Subst.notMemOnTy hbS hwe.1, hbτ⟩
  | app hf harg huni =>
    intro w hwΦ hctx hwe
    expose_names
    simp only [Expr.tyFreeVars, List.mem_append, not_or] at hwe
    obtain ⟨hfS, hfτ⟩ := Infer.eOut_avoid hf (w := w) hwΦ hctx hwe.1
    have hfle := Infer.frontier_le hf
    have hargle := Infer.frontier_le harg
    obtain ⟨haS, haτ⟩ := Infer.eOut_avoid harg (w := w) (by omega)
      (Subst.onCtx_avoid hctx hfS) hwe.2
    have hS₃ : ∀ p ∈ S₃, w ∉ p.2.freeVars := by
      intro p hp hwp
      rcases UnifyRel.range_mem huni p hp w hwp with h | h
      · exact Subst.notMemOnTy haS hfτ h
      · simp only [Ty.freeVars, List.mem_dedup, List.mem_append, List.mem_singleton] at h
        rcases h with h | h
        · exact haτ h
        · omega
    refine ⟨?_, ?_⟩
    · intro p hp; rw [List.mem_append, List.mem_append] at hp
      rcases hp with (hp | hp) | hp
      · exact hfS p hp
      · exact haS p hp
      · exact hS₃ p hp
    · intro hc
      rcases Subst.mem_freeVars_onTy hc with h | ⟨q, hq, hvq⟩
      · simp only [Ty.freeVars, List.mem_singleton] at h; omega
      · exact hS₃ q hq hvq
  | letIn hrhs hbody =>
    intro w hwΦ hctx hwe
    expose_names
    simp only [Expr.tyFreeVars, Option.elim_none, List.nil_append, List.mem_append, not_or] at hwe
    obtain ⟨hrS, hrτ⟩ := Infer.eOut_avoid hrhs (w := w) hwΦ hctx hwe.1
    have hrle := Infer.frontier_le hrhs
    have hMbody : w ∉ (genScheme rhs.tyFreeVars (S₁.onCtx ctx).env τ₁).body.freeVars :=
      fun hc => hrτ (Ty.freeVars_closeOver_subset hc)
    obtain ⟨hbS, hbτ⟩ := Infer.eOut_avoid hbody (w := w) (by omega)
      (by intro M hM; rcases List.mem_cons.mp hM with rfl | hM
          · exact hMbody
          · exact Subst.onCtx_avoid hctx hrS M hM)
      hwe.2
    refine ⟨?_, hbτ⟩
    intro p hp; rw [List.mem_append] at hp
    rcases hp with hp | hp
    · exact hrS p hp
    · exact hbS p hp
  | letInAnn hσwf hΦN hrhs huni _hesc1 _hesc2 hbody =>
    intro w hwΦ hctx hwe
    expose_names
    simp only [Expr.tyFreeVars, Option.elim_some, List.mem_append, not_or] at hwe
    have hrle := Infer.frontier_le hrhs
    obtain ⟨hrS, hrτ⟩ := Infer.eOut_avoid hrhs (w := w) (by omega) hctx (by
      intro hc
      rcases Expr.tyFreeVars_openTyVars hc with h | h
      · exact hwe.1.2 h
      · have := freshVars_ge w h; omega)
    have hσopen : w ∉ (σ.openVars (freshVars N σ.paramCount)).freeVars := by
      intro hc
      rcases Ty.freeVars_openVars_subset w hc with h | h
      · exact hwe.1.1 h
      · have := freshVars_ge w h; omega
    have hSchk : ∀ p ∈ Schk, w ∉ p.2.freeVars := by
      intro p hp hwp
      rcases UnifyRel.range_mem huni p hp w hwp with h | h
      · exact hrτ h
      · exact hσopen h
    obtain ⟨hbS, hbτ⟩ := Infer.eOut_avoid hbody (w := w) (by omega)
      (by intro M hM; rcases List.mem_cons.mp hM with rfl | hM
          · exact hwe.1.1
          · exact Subst.onCtx_avoid (Subst.onCtx_avoid hctx hrS) hSchk M hM)
      hwe.2
    refine ⟨?_, hbτ⟩
    intro p hp; rw [List.mem_append, List.mem_append] at hp
    rcases hp with (hp | hp) | hp
    · exact hrS p hp
    · exact hSchk p hp
    · exact hbS p hp
  | match_ hscrut hne hbr =>
    intro w hwΦ hctx hwe
    simp only [Expr.tyFreeVars, List.mem_append, not_or] at hwe
    obtain ⟨hsS, hsτ⟩ := Infer.eOut_avoid hscrut (w := w) hwΦ hctx hwe.1
    have hle1 := Infer.frontier_le hscrut
    obtain ⟨hbrS, hbrρ⟩ := InferBranches.eOut_avoid hbr (w := w) (by omega)
      (Subst.onCtx_avoid hctx hsS) hsτ
      (by intro hc; simp only [Ty.freeVars, List.mem_singleton] at hc; omega) hwe.2
    refine ⟨?_, hbrρ⟩
    intro p hp; rw [List.mem_append] at hp
    rcases hp with hp | hp
    · exact hsS p hp
    · exact hbrS p hp
  | letRec hwf hgroup hceiling hbody =>
    intro w hwΦ hctx hwe
    expose_names
    simp only [Expr.tyFreeVars, List.mem_append] at hwe
    have hwann : w ∉ Expr.tyFreeVars.AnnList.tyFreeVars anns := fun hc => hwe (Or.inl (Or.inl hc))
    have hwbind : w ∉ Expr.tyFreeVars.RecGroup.tyFreeVars bindings := fun hc => hwe (Or.inl (Or.inr hc))
    have hwbody : w ∉ body.tyFreeVars := fun hc => hwe (Or.inr hc)
    have hspecs_init : ∀ s ∈ RecSpec.init Φ anns, w ∉ s.freeVars := by
      intro s hs
      rcases List.mem_iff_getElem.mp hs with ⟨j, hj, rfl⟩
      have hlenj : j < anns.length := by
        have h₂ := RecSpec.init_length Φ anns
        omega
      have hget : (RecSpec.init Φ anns)[j] = RecSpec.mono (.fvar (Φ + j)) := by
        have h₁ := List.getElem?_eq_getElem hj
        rw [RecSpec.init_getElem? Φ anns j, List.getElem?_eq_getElem hlenj] at h₁
        injection h₁ with hEq
        exact hEq.symm
      rw [hget]
      intro hc
      simp only [RecSpec.freeVars, Ty.freeVars, List.mem_singleton] at hc
      omega
    have hctxGroup : ∀ M ∈ ({ ctx with
        env := (RecSpec.init Φ anns).map (RecSpec.rhsEntry [] []) ++ ctx.env } : Ctx).env,
        w ∉ M.body.freeVars := by
      intro M hM
      rcases List.mem_append.mp hM with hM1 | hM2
      · obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hM1
        rw [RecSpec.rhsEntry_nil_body_freeVars]
        exact hspecs_init s hs
      · exact hctx M hM2
    have hS₁ : ∀ p ∈ S₁, w ∉ p.2.freeVars :=
      InferRecGroup.eOut_avoid hgroup (w := w) (by omega)
        hctxGroup (fun s hs => hspecs_init s hs) hwbind
    have hgrpLe : Φ + bindings.length ≤ Φ₁ := InferRecGroup.frontier_le hgroup
    have hbodyCtx : ∀ M ∈ ({ (S₁.onCtx ctx) with
        env := RecSpecs.ceilingSchemes
                 (genGroupVars (RecGroup.rigidVars anns bindings) (S₁.onCtx ctx).env
                   (RecSpecs.monoTys ((RecSpec.init Φ anns).map (RecSpec.onSubst S₁))))
                 anns
                 ((RecSpec.init Φ anns).map (RecSpec.onSubst S₁))
               ++ (S₁.onCtx ctx).env } : Ctx).env, w ∉ M.body.freeVars := by
      intro M hM
      rcases List.mem_append.mp hM with hM1 | hM2
      · obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hM1
        have hpa : p.1 ∈ anns := (List.of_mem_zip hp).1
        have hps : p.2 ∈ (RecSpec.init Φ anns).map (RecSpec.onSubst S₁) := (List.of_mem_zip hp).2
        cases p with
        | mk a s =>
          cases a with
          | some σ =>
            intro hc
            exact hwann (Expr.scheme_body_mem_annList_tyFreeVars hpa hc)
          | none =>
            intro hc
            have hws : w ∈ s.freeVars := RecSpec.mem_bodyScheme_freeVars hc
            obtain ⟨s0, hs0, rfl⟩ := List.mem_map.mp hps
            rcases List.mem_iff_getElem.mp hs0 with ⟨j, hj, rfl⟩
            have hlenj : j < anns.length := by
              have h₂ := RecSpec.init_length Φ anns
              omega
            have hget : (RecSpec.init Φ anns)[j] = RecSpec.mono (.fvar (Φ + j)) := by
              have h₁ := List.getElem?_eq_getElem hj
              rw [RecSpec.init_getElem? Φ anns j, List.getElem?_eq_getElem hlenj] at h₁
              injection h₁ with hEq
              exact hEq.symm
            rw [hget] at hws
            exact absurd hws (Subst.notMemOnTy hS₁ (by
              intro hc2
              simp only [Ty.freeVars, List.mem_singleton] at hc2
              omega))
      · exact Subst.onCtx_avoid hctx hS₁ M hM2
    obtain ⟨hbS, hbτ⟩ := Infer.eOut_avoid hbody (w := w) (by omega) hbodyCtx hwbody
    refine ⟨?_, hbτ⟩
    intro p hp
    rw [List.mem_append] at hp
    rcases hp with hp₁ | hp₂
    · exact hS₁ p hp₁
    · exact hbS p hp₂
termination_by e.size
decreasing_by
  all_goals (try subst_vars; try simp only [Expr.size, Expr.size_openTyVars]; omega)
theorem InferBranches.eOut_avoid {Φ ctx scrutTy ρ brs Φ' S}
    (h : InferBranches Φ ctx scrutTy ρ brs Φ' S) :
    ∀ {w : Nat}, w < Φ → (∀ M ∈ ctx.env, w ∉ M.body.freeVars) → w ∉ scrutTy.freeVars →
    w ∉ ρ.freeVars → w ∉ Expr.tyFreeVars.BranchList.tyFreeVars brs →
    (∀ p ∈ S, w ∉ p.2.freeVars) ∧ w ∉ (S.onTy ρ).freeVars := by
  cases h with
  | nil =>
    intro w _ _ _ hρ _
    exact ⟨by simp, by simpa using hρ⟩
  | cons hlook hn huni0 hbody huni hrest =>
    intro w hwΦ hctx hscrut hρ hbrs
    expose_names
    simp only [Expr.tyFreeVars.BranchList.tyFreeVars, List.mem_append, not_or] at hbrs
    have hS₀ : ∀ p ∈ S₀, w ∉ p.2.freeVars := by
      intro p hp hwp
      rcases UnifyRel.range_mem huni0 p hp w hwp with h | h
      · exact hscrut h
      · simp only [Ty.freeVars] at h
        rw [mem_TyList_freeVars] at h
        obtain ⟨t, ht, hgt⟩ := h
        obtain ⟨x, hx, rfl⟩ := List.mem_map.mp ht
        simp only [Ty.freeVars, List.mem_singleton] at hgt
        have := freshVars_ge x hx; omega
    have hta : ∀ v ∈ (((freshVars Φ ctor.paramCount).map (Ty.fvar ·)).map S₀.onTy), w ∉ v.freeVars := by
      intro v hv hwv
      obtain ⟨v0, hv0, rfl⟩ := List.mem_map.mp hv
      obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hv0
      rcases Subst.mem_freeVars_onTy hwv with h | ⟨p, hp, hvp⟩
      · simp only [Ty.freeVars, List.mem_singleton] at h; have := freshVars_ge x hx; omega
      · exact hS₀ p hp hvp
    have hle0 := Infer.frontier_le hbody
    obtain ⟨hbS, hbτ⟩ := Infer.eOut_avoid hbody (w := w) (by omega)
      (by intro M hM; rcases List.mem_append.mp hM with hM | hM
          · obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hM
            obtain ⟨c, hc, rfl⟩ := List.mem_map.mp ht
            simpa only [PolyTy.mkTrivial] using
              Ty.not_mem_freeVars_openWith hta ((ctor.closed c hc).not_mem_freeVars w)
          · exact Subst.onCtx_avoid hctx hS₀ M hM)
      hbrs.1
    have hS₂ : ∀ p ∈ S₂, w ∉ p.2.freeVars := by
      intro p hp hwp
      rcases UnifyRel.range_mem huni p hp w hwp with h | h
      · exact hbτ h
      · exact Subst.notMemOnTy hbS (Subst.notMemOnTy hS₀ hρ) h
    obtain ⟨hrS, hrρ⟩ := InferBranches.eOut_avoid hrest (w := w) (by omega)
      (Subst.onCtx_avoid (Subst.onCtx_avoid (Subst.onCtx_avoid hctx hS₀) hbS) hS₂)
      (Subst.notMemOnTy hS₂ (Subst.notMemOnTy hbS (Subst.notMemOnTy hS₀ hscrut)))
      (Subst.notMemOnTy hS₂ (Subst.notMemOnTy hbS (Subst.notMemOnTy hS₀ hρ)))
      hbrs.2
    refine ⟨?_, ?_⟩
    · intro p hp; rw [List.mem_append, List.mem_append, List.mem_append] at hp
      rcases hp with ((hp | hp) | hp) | hp
      · exact hS₀ p hp
      · exact hbS p hp
      · exact hS₂ p hp
      · exact hrS p hp
    · rw [Subst.onTy_append, Subst.onTy_append, Subst.onTy_append]; exact hrρ
  | consWild hbody huni hrest =>
    intro w hwΦ hctx hscrut hρ hbrs
    expose_names
    simp only [Expr.tyFreeVars.BranchList.tyFreeVars, List.mem_append, not_or] at hbrs
    have hle1 := Infer.frontier_le hbody
    obtain ⟨hbS, hbτ⟩ := Infer.eOut_avoid hbody (w := w) hwΦ hctx hbrs.1
    have hS₂ : ∀ p ∈ S₂, w ∉ p.2.freeVars := by
      intro p hp hwp
      rcases UnifyRel.range_mem huni p hp w hwp with h | h
      · exact hbτ h
      · exact Subst.notMemOnTy hbS hρ h
    obtain ⟨hrS, hrρ⟩ := InferBranches.eOut_avoid hrest (w := w) (by omega)
      (Subst.onCtx_avoid (Subst.onCtx_avoid hctx hbS) hS₂)
      (Subst.notMemOnTy hS₂ (Subst.notMemOnTy hbS hscrut))
      (Subst.notMemOnTy hS₂ (Subst.notMemOnTy hbS hρ))
      hbrs.2
    refine ⟨?_, ?_⟩
    · intro p hp; rw [List.mem_append, List.mem_append] at hp
      rcases hp with (hp | hp) | hp
      · exact hbS p hp
      · exact hS₂ p hp
      · exact hrS p hp
    · rw [Subst.onTy_append, Subst.onTy_append]; exact hrρ
termination_by Expr.sizeBranches brs
decreasing_by
  all_goals (try subst_vars; try simp only [Expr.sizeBranches]; omega)
/-- Fused `InferRecGroup` output locality (avoid form): a var below the input
    frontier that avoids the context, the specs and the bindings' annotation vars
    is absent from the substitution range and the elaborated outputs. -/
theorem InferRecGroup.eOut_avoid {Φ ctx bindings specs Φ' S}
    (h : InferRecGroup Φ ctx bindings specs Φ' S) :
    ∀ {w : Nat}, w < Φ → (∀ M ∈ ctx.env, w ∉ M.body.freeVars) →
    (∀ s ∈ specs, w ∉ s.freeVars) → w ∉ Expr.tyFreeVars.RecGroup.tyFreeVars bindings →
    (∀ p ∈ S, w ∉ p.2.freeVars) := by
  cases h with
  | nil => intro w _ _ _ _; simp
  | consMono he huni hrest =>
    intro w hwΦ hctx hspecs hbinds
    expose_names
    simp only [Expr.tyFreeVars.RecGroup.tyFreeVars, List.mem_append, not_or] at hbinds
    have hle1 := Infer.frontier_le he
    obtain ⟨heS, heτ⟩ := Infer.eOut_avoid he (w := w) hwΦ hctx hbinds.1
    have hτA : w ∉ τ.freeVars := hspecs (.mono τ) List.mem_cons_self
    have hS₂ : ∀ p ∈ S₂, w ∉ p.2.freeVars := by
      intro p hp hwp
      rcases UnifyRel.range_mem huni p hp w hwp with h | h
      · exact heτ h
      · exact Subst.notMemOnTy heS hτA h
    have hrS : ∀ p ∈ S₃, w ∉ p.2.freeVars :=
      InferRecGroup.eOut_avoid hrest (w := w) (by omega)
        (Subst.onCtx_avoid (Subst.onCtx_avoid hctx heS) hS₂)
        (by intro s' hs'
            obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hs'
            exact RecSpec.notMem_freeVars_onSubst
              (fun p hp => (List.mem_append.mp hp).elim (heS p) (hS₂ p))
              (hspecs s (List.mem_cons_of_mem _ hs)))
        hbinds.2
    intro p hp; rw [List.mem_append, List.mem_append] at hp
    rcases hp with (hp | hp) | hp
    · exact heS p hp
    · exact hS₂ p hp
    · exact hrS p hp
  | consPoly hΦN hinfer huni hesc1 hesc2 hrest =>
    intro w hwΦ hctx hspecs hbinds
    expose_names
    simp only [Expr.tyFreeVars.RecGroup.tyFreeVars, List.mem_append, not_or] at hbinds
    have hσbody : w ∉ σ.body.freeVars := hspecs (.poly σ) List.mem_cons_self
    have hle1 := Infer.frontier_le hinfer
    have hwopen : w ∉ (e.openTyVars (freshVars N σ.paramCount)).tyFreeVars := by
      intro hc
      rcases Expr.tyFreeVars_openTyVars hc with h | h
      · exact hbinds.1 h
      · have := freshVars_ge w h; omega
    obtain ⟨heS, heτ⟩ := Infer.eOut_avoid hinfer (w := w) (by omega) hctx hwopen
    have hσopen : w ∉ (σ.openVars (freshVars N σ.paramCount)).freeVars := by
      intro hc
      rcases Ty.freeVars_openVars_subset w hc with h | h
      · exact hσbody h
      · have := freshVars_ge w h; omega
    have hSchk : ∀ p ∈ Schk, w ∉ p.2.freeVars := by
      intro p hp hwp
      rcases UnifyRel.range_mem huni p hp w hwp with h | h
      · exact heτ h
      · exact hσopen h
    have hrS : ∀ p ∈ S₂, w ∉ p.2.freeVars :=
      InferRecGroup.eOut_avoid hrest (w := w) (by omega)
        (Subst.onCtx_avoid (Subst.onCtx_avoid hctx heS) hSchk)
        (by intro s' hs'
            obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hs'
            exact RecSpec.notMem_freeVars_onSubst
              (fun p hp => (List.mem_append.mp hp).elim (heS p) (hSchk p))
              (hspecs s (List.mem_cons_of_mem _ hs)))
        hbinds.2
    intro p hp; rw [List.mem_append, List.mem_append] at hp
    rcases hp with (hp | hp) | hp
    · exact heS p hp
    · exact hSchk p hp
    · exact hrS p hp
termination_by Expr.sizeRecGroup bindings
decreasing_by
  all_goals (try subst_vars; try simp only [Expr.sizeRecGroup, Expr.size_openTyVars]; omega)
end

/-! ### M3: composed idempotency (`Infer.eliminates`)

`S` is idempotent: a domain var never survives in any `S`-image, and `S` reduces
its own result type. Composed from the single-MGU `UnifyRel.eliminates` by the
cross-disjointness argument: for `S = A ++ B`, `dom(A) ∩ range(B) = ∅` (the later
`B` is inferred in a world avoiding `dom(A)`), discharged via `Infer.eOut_avoid`. -/

/-- Compose idempotency across a substitution append, given the earlier domain
    avoids the later range. -/
theorem Subst.eliminates_append {A B : Subst}
    (hA : ∀ p ∈ A, ∀ x : Ty, p.1 ∉ (A.onTy x).freeVars)
    (hB : ∀ p ∈ B, ∀ x : Ty, p.1 ∉ (B.onTy x).freeVars)
    (hcross : ∀ p ∈ A, ∀ q ∈ B, p.1 ∉ q.2.freeVars) :
    ∀ p ∈ A ++ B, ∀ x : Ty, p.1 ∉ ((A ++ B).onTy x).freeVars := by
  intro p hp x hc
  rw [Subst.onTy_append] at hc
  rcases List.mem_append.mp hp with hpA | hpB
  · rcases Subst.mem_freeVars_onTy hc with h | ⟨q, hq, hvq⟩
    · exact hA p hpA x h
    · exact hcross p hpA q hq hvq
  · exact hB p hpB (A.onTy x) hc

/-- An idempotent substitution's domain var avoids its own substituted context. -/
theorem Subst.eliminates_onCtx {S : Subst} {w : Nat} {ctx : Ctx}
    (hS : ∀ x : Ty, w ∉ (S.onTy x).freeVars) : ∀ M ∈ (S.onCtx ctx).env, w ∉ M.body.freeVars := by
  intro M hM
  simp only [Subst.onCtx, Subst.onEnv] at hM
  obtain ⟨M0, hM0, rfl⟩ := List.mem_map.mp hM
  simp only [Subst.onPolyTy]
  exact hS M0.body

mutual
theorem Infer.eliminates {Φ ctx e Φ' S τ} (h : Infer Φ ctx e Φ' S τ)
    (hctx : CtxBelow Φ ctx) (hΦ : ∀ y ∈ e.tyFreeVars, y < Φ)
    (hSe : ∀ p ∈ S, p.1 ∉ e.tyFreeVars) :
    (∀ p ∈ S, ∀ x : Ty, p.1 ∉ (S.onTy x).freeVars) ∧ (∀ p ∈ S, p.1 ∉ τ.freeVars) := by
  cases h with
  | primLitUnit => exact ⟨by simp, by simp [Ty.freeVars]⟩
  | primLitInt => exact ⟨by simp, by simp [Ty.freeVars]⟩
  | primLitNat => exact ⟨by simp, by simp [Ty.freeVars]⟩
  | primLitChar => exact ⟨by simp, by simp [Ty.freeVars]⟩
  | primBinOpIntAdd => exact ⟨by simp, by simp [Ty.freeVars]⟩
  | primBinOpIntSub => exact ⟨by simp, by simp [Ty.freeVars]⟩
  | primBinOpIntLt _ _ _ _ => exact ⟨by simp, by simp [Ty.freeVars]⟩
  | primBinOpCharLt _ _ _ _ => exact ⟨by simp, by simp [Ty.freeVars]⟩
  | var hlook => exact ⟨by simp, by simp⟩
  | ctor hlook => exact ⟨by simp, by simp⟩
  | lambda hseed hbody =>
    cases hseed with
    | none =>
      expose_names
      have hΦb : ∀ y ∈ body.tyFreeVars, y < Φ := fun y hy => hΦ y (by
        show y ∈ (Expr.lambda none body).tyFreeVars
        simpa only [Expr.tyFreeVars, Option.elim_none, List.nil_append] using hy)
      have hSb : ∀ p ∈ S, p.1 ∉ body.tyFreeVars := fun p hp hc => hSe p hp (by
        show p.1 ∈ (Expr.lambda none body).tyFreeVars
        simpa only [Expr.tyFreeVars, Option.elim_none, List.nil_append] using hc)
      obtain ⟨hbE, hbR⟩ := Infer.eliminates hbody
        (by intro M hM; rcases List.mem_cons.mp hM with rfl | hM
            · exact .fvar (by omega)
            · exact (hctx M hM).mono (by omega))
        (fun y hy => by have := hΦb y hy; omega) hSb
      refine ⟨hbE, ?_⟩
      intro p hp
      simp only [Ty.freeVars, List.mem_dedup, List.mem_append, not_or]
      exact ⟨hbE p hp (Ty.fvar Φ), hbR p hp⟩
    | some _ hT =>
      expose_names
      have hΦb : ∀ y ∈ body.tyFreeVars, y < Φ := fun y hy => hΦ y (by
        show y ∈ (Expr.lambda (some paramTy) body).tyFreeVars
        simp only [Expr.tyFreeVars, Option.elim_some, List.mem_append]; exact Or.inr hy)
      have hSb : ∀ p ∈ S, p.1 ∉ body.tyFreeVars := fun p hp hc => hSe p hp (by
        show p.1 ∈ (Expr.lambda (some paramTy) body).tyFreeVars
        simp only [Expr.tyFreeVars, Option.elim_some, List.mem_append]; exact Or.inr hc)
      obtain ⟨hbE, hbR⟩ := Infer.eliminates hbody
        (by intro M hM; rcases List.mem_cons.mp hM with rfl | hM
            · exact Ty.BelowFvars.of_freeVars_lt (fun v hv => hΦ v (by
                show v ∈ (Expr.lambda (some paramTy) body).tyFreeVars
                simp only [Expr.tyFreeVars, Option.elim_some, List.mem_append]; exact Or.inl hv))
            · exact hctx M hM)
        hΦb hSb
      refine ⟨hbE, ?_⟩
      intro p hp
      simp only [Ty.freeVars, List.mem_dedup, List.mem_append, not_or]
      exact ⟨hbE p hp paramTy, hbR p hp⟩
  | app hf harg huni =>
    expose_names
    have hfle := Infer.frontier_le hf
    have hargle := Infer.frontier_le harg
    have hΦf : ∀ y ∈ f.tyFreeVars, y < Φ := fun y hy => hΦ y (by
      show y ∈ (Expr.app f arg).tyFreeVars; simp only [Expr.tyFreeVars, List.mem_append]; exact Or.inl hy)
    have hΦa : ∀ y ∈ arg.tyFreeVars, y < Φ := fun y hy => hΦ y (by
      show y ∈ (Expr.app f arg).tyFreeVars; simp only [Expr.tyFreeVars, List.mem_append]; exact Or.inr hy)
    have hSf : ∀ p ∈ S₁, p.1 ∉ f.tyFreeVars := fun p hp hc =>
      hSe p (List.mem_append_left _ (List.mem_append_left _ hp)) (by
        show p.1 ∈ (Expr.app f arg).tyFreeVars; simp only [Expr.tyFreeVars, List.mem_append]; exact Or.inl hc)
    have hSa1 : ∀ p ∈ S₁, p.1 ∉ arg.tyFreeVars := fun p hp hc =>
      hSe p (List.mem_append_left _ (List.mem_append_left _ hp)) (by
        show p.1 ∈ (Expr.app f arg).tyFreeVars; simp only [Expr.tyFreeVars, List.mem_append]; exact Or.inr hc)
    have hSa : ∀ p ∈ S₂, p.1 ∉ arg.tyFreeVars := fun p hp hc =>
      hSe p (List.mem_append_left _ (List.mem_append_right _ hp)) (by
        show p.1 ∈ (Expr.app f arg).tyFreeVars; simp only [Expr.tyFreeVars, List.mem_append]; exact Or.inr hc)
    obtain ⟨hfE, hfR⟩ := Infer.eliminates hf hctx hΦf hSf
    obtain ⟨hf_τbel, hf_sbel⟩ := Infer.belowFvars hf hctx hΦf
    have hctx1 : CtxBelow Φ₁ (S₁.onCtx ctx) := Subst.onCtx_below hf_sbel hfle hctx
    have hf_dom := Infer.dom_below hf hctx hΦf
    obtain ⟨haE, haR⟩ := Infer.eliminates harg hctx1
      (fun y hy => lt_of_lt_of_le (hΦa y hy) hfle) hSa
    have ha_dom := Infer.dom_below harg hctx1 (fun y hy => lt_of_lt_of_le (hΦa y hy) hfle)
    have hcross12 : ∀ p ∈ S₁, ∀ q ∈ S₂, p.1 ∉ q.2.freeVars := fun p hp q hq =>
      (Infer.eOut_avoid harg (w := p.1) (hf_dom p hp)
        (Subst.eliminates_onCtx (hfE p hp)) (hSa1 p hp)).1 q hq
    have h12E := Subst.eliminates_append hfE haE hcross12
    have hcross123 : ∀ p ∈ S₁ ++ S₂, ∀ q ∈ S₃, p.1 ∉ q.2.freeVars := by
      intro p hp q hq hwq
      have hrm := UnifyRel.range_mem huni q hq p.1 hwq
      rcases List.mem_append.mp hp with hpS₁ | hpS₂
      · have havoid := Infer.eOut_avoid harg (w := p.1) (hf_dom p hpS₁)
          (Subst.eliminates_onCtx (hfE p hpS₁)) (hSa1 p hpS₁)
        rcases hrm with h | h
        · rcases Subst.mem_freeVars_onTy h with h' | ⟨r, hr, hvr⟩
          · exact hfR p hpS₁ h'
          · exact havoid.1 r hr hvr
        · simp only [Ty.freeVars, List.mem_dedup, List.mem_append, List.mem_singleton] at h
          rcases h with h | h
          · exact havoid.2 h
          · have := hf_dom p hpS₁; omega
      · rcases hrm with h | h
        · exact haE p hpS₂ τf h
        · simp only [Ty.freeVars, List.mem_dedup, List.mem_append, List.mem_singleton] at h
          rcases h with h | h
          · exact haR p hpS₂ h
          · have := ha_dom p hpS₂; omega
    refine ⟨Subst.eliminates_append h12E (UnifyRel.eliminates huni) hcross123, ?_⟩
    intro p hp hc
    rcases List.mem_append.mp hp with hp12 | hpS₃
    · rcases Subst.mem_freeVars_onTy hc with h | ⟨q, hq, hvq⟩
      · simp only [Ty.freeVars, List.mem_singleton] at h
        rcases List.mem_append.mp hp12 with hpS₁ | hpS₂
        · have := hf_dom p hpS₁; omega
        · have := ha_dom p hpS₂; omega
      · exact hcross123 p hp12 q hq hvq
    · exact UnifyRel.eliminates huni p hpS₃ (Ty.fvar Φ₂) hc
  | letIn hrhs hbody =>
    expose_names
    have hrle := Infer.frontier_le hrhs
    have hΦr : ∀ y ∈ rhs.tyFreeVars, y < Φ := fun y hy => hΦ y (by
      show y ∈ (Expr.letIn none rhs body).tyFreeVars
      simp only [Expr.tyFreeVars, Option.elim_none, List.nil_append, List.mem_append]; exact Or.inl hy)
    have hΦb : ∀ y ∈ body.tyFreeVars, y < Φ := fun y hy => hΦ y (by
      show y ∈ (Expr.letIn none rhs body).tyFreeVars
      simp only [Expr.tyFreeVars, Option.elim_none, List.nil_append, List.mem_append]; exact Or.inr hy)
    have hSr : ∀ p ∈ S₁, p.1 ∉ rhs.tyFreeVars := fun p hp hc =>
      hSe p (List.mem_append_left _ hp) (by
        show p.1 ∈ (Expr.letIn none rhs body).tyFreeVars
        simp only [Expr.tyFreeVars, Option.elim_none, List.nil_append, List.mem_append]; exact Or.inl hc)
    have hSb1 : ∀ p ∈ S₁, p.1 ∉ body.tyFreeVars := fun p hp hc =>
      hSe p (List.mem_append_left _ hp) (by
        show p.1 ∈ (Expr.letIn none rhs body).tyFreeVars
        simp only [Expr.tyFreeVars, Option.elim_none, List.nil_append, List.mem_append]; exact Or.inr hc)
    have hSb : ∀ p ∈ S₂, p.1 ∉ body.tyFreeVars := fun p hp hc =>
      hSe p (List.mem_append_right _ hp) (by
        show p.1 ∈ (Expr.letIn none rhs body).tyFreeVars
        simp only [Expr.tyFreeVars, Option.elim_none, List.nil_append, List.mem_append]; exact Or.inr hc)
    obtain ⟨hrE, hrR⟩ := Infer.eliminates hrhs hctx hΦr hSr
    obtain ⟨hr_τbel, hr_sbel⟩ := Infer.belowFvars hrhs hctx hΦr
    have hr_dom := Infer.dom_below hrhs hctx hΦr
    have hctxb : CtxBelow Φ₁ { (S₁.onCtx ctx) with
        env := genScheme rhs.tyFreeVars (S₁.onCtx ctx).env τ₁ :: (S₁.onCtx ctx).env } := by
      intro M hM; rcases List.mem_cons.mp hM with rfl | hM
      · exact hr_τbel.closeOver
      · exact (Subst.onCtx_below hr_sbel hrle hctx) M hM
    obtain ⟨hbE, hbR⟩ := Infer.eliminates hbody hctxb
      (fun y hy => lt_of_lt_of_le (hΦb y hy) hrle) hSb
    have hbavoid : ∀ p ∈ S₁, ∀ M ∈ { (S₁.onCtx ctx) with
        env := genScheme rhs.tyFreeVars (S₁.onCtx ctx).env τ₁ :: (S₁.onCtx ctx).env }.env,
        p.1 ∉ M.body.freeVars := by
      intro p hp M hM; rcases List.mem_cons.mp hM with rfl | hM
      · exact fun hc => hrR p hp (Ty.freeVars_closeOver_subset hc)
      · exact Subst.eliminates_onCtx (hrE p hp) M hM
    have hcross : ∀ p ∈ S₁, ∀ q ∈ S₂, p.1 ∉ q.2.freeVars := fun p hp q hq =>
      (Infer.eOut_avoid hbody (w := p.1) (hr_dom p hp) (hbavoid p hp) (hSb1 p hp)).1 q hq
    refine ⟨Subst.eliminates_append hrE hbE hcross, ?_⟩
    intro p hp
    rcases List.mem_append.mp hp with hpS₁ | hpS₂
    · exact (Infer.eOut_avoid hbody (w := p.1) (hr_dom p hpS₁) (hbavoid p hpS₁) (hSb1 p hpS₁)).2
    · exact hbR p hpS₂
  | letInAnn hσwf hΦN hrhs huni hesc1 _hesc2 hbody =>
    expose_names
    have hrle := Infer.frontier_le hrhs
    have hΦσ : ∀ y ∈ σ.body.freeVars, y < Φ := fun y hy => hΦ y (by
      simp only [Expr.tyFreeVars, Option.elim_some, List.mem_append]; exact Or.inl (Or.inl hy))
    have hΦbody : ∀ y ∈ body.tyFreeVars, y < Φ := fun y hy => hΦ y (by
      simp only [Expr.tyFreeVars, Option.elim_some, List.mem_append]; exact Or.inr hy)
    have hΦropen : ∀ y ∈ (rhs.openTyVars (freshVars N σ.paramCount)).tyFreeVars, y < N + σ.paramCount := by
      intro y hy
      rcases Expr.tyFreeVars_openTyVars hy with h | h
      · have := hΦ y (by simp only [Expr.tyFreeVars, Option.elim_some, List.mem_append]
                         exact Or.inl (Or.inr h)); omega
      · have := freshVars_lt y h; omega
    have hSσ1 : ∀ p ∈ S₁, p.1 ∉ σ.body.freeVars := fun p hp hc =>
      hSe p (List.mem_append_left _ (List.mem_append_left _ hp)) (by
        simp only [Expr.tyFreeVars, Option.elim_some, List.mem_append]; exact Or.inl (Or.inl hc))
    have hSσall : ∀ p ∈ S₁ ++ Schk, p.1 ∉ σ.body.freeVars := fun p hp hc =>
      hSe p (List.mem_append_left _ hp) (by
        simp only [Expr.tyFreeVars, Option.elim_some, List.mem_append]; exact Or.inl (Or.inl hc))
    have hSbody : ∀ p ∈ S₁ ++ Schk, p.1 ∉ body.tyFreeVars := fun p hp hc =>
      hSe p (List.mem_append_left _ hp) (by
        simp only [Expr.tyFreeVars, Option.elim_some, List.mem_append]; exact Or.inr hc)
    have hSb2 : ∀ p ∈ S₂, p.1 ∉ body.tyFreeVars := fun p hp hc =>
      hSe p (List.mem_append_right _ hp) (by
        simp only [Expr.tyFreeVars, Option.elim_some, List.mem_append]; exact Or.inr hc)
    have hSropen : ∀ p ∈ S₁, p.1 ∉ (rhs.openTyVars (freshVars N σ.paramCount)).tyFreeVars := by
      intro p hp hc
      rcases Expr.tyFreeVars_openTyVars hc with h | h
      · exact hSe p (List.mem_append_left _ (List.mem_append_left _ hp)) (by
          simp only [Expr.tyFreeVars, Option.elim_some, List.mem_append]; exact Or.inl (Or.inr h))
      · exact hesc1 p.1 h (List.mem_map.mpr ⟨p, List.mem_append_left _ hp, rfl⟩)
    have hctx_pc : CtxBelow (N + σ.paramCount) ctx := fun M hM => (hctx M hM).mono (by omega)
    obtain ⟨hrE, hrR⟩ := Infer.eliminates hrhs hctx_pc hΦropen hSropen
    obtain ⟨hr_τbel, hr_sbel⟩ := Infer.belowFvars hrhs hctx_pc hΦropen
    have hr_dom := Infer.dom_below hrhs hctx_pc hΦropen
    have hσopenbel : Ty.BelowFvars Φ₁ (σ.openVars (freshVars N σ.paramCount)) :=
      Ty.openVars_belowFvars ((Ty.BelowFvars.of_freeVars_lt hΦσ).mono (by omega))
        (fun x hx => by have := freshVars_lt x hx; omega)
    have hSchkbel : ∀ p ∈ Schk, Ty.BelowFvars Φ₁ p.2 := UnifyRel.belowFvars huni hr_τbel hσopenbel
    have hSchkdom : ∀ p ∈ Schk, p.1 < Φ₁ := by
      intro p hp
      rcases UnifyRel.dom_mem huni p hp with h | h
      · exact hr_τbel.mem_lt p.1 h
      · exact hσopenbel.mem_lt p.1 h
    have hctxb : CtxBelow Φ₁ { (Schk.onCtx (S₁.onCtx ctx)) with
        env := σ :: (Schk.onCtx (S₁.onCtx ctx)).env } := by
      intro M hM; rcases List.mem_cons.mp hM with rfl | hM
      · exact (Ty.BelowFvars.of_freeVars_lt hΦσ).mono (by omega)
      · exact (Subst.onCtx_below hSchkbel (le_refl _) (Subst.onCtx_below hr_sbel hrle hctx_pc)) M hM
    obtain ⟨hbE, hbR⟩ := Infer.eliminates hbody hctxb
      (fun y hy => lt_of_lt_of_le (hΦbody y hy) (by omega)) hSb2
    have cross1 : ∀ p ∈ S₁, ∀ q ∈ Schk, p.1 ∉ q.2.freeVars := by
      intro p hp q hq hwq
      rcases UnifyRel.range_mem huni q hq p.1 hwq with h | h
      · exact hrR p hp h
      · rcases Ty.freeVars_openVars_subset p.1 h with h' | h'
        · exact hSσ1 p hp h'
        · exact hesc1 p.1 h' (List.mem_map.mpr ⟨p, List.mem_append_left _ hp, rfl⟩)
    have hE1Schk := Subst.eliminates_append hrE (UnifyRel.eliminates huni) cross1
    have hdomall : ∀ p ∈ S₁ ++ Schk, p.1 < Φ₁ := by
      intro p hp; rcases List.mem_append.mp hp with h | h
      · exact hr_dom p h
      · exact hSchkdom p h
    have hbodyctx : ∀ p ∈ S₁ ++ Schk, ∀ M ∈ ({ (Schk.onCtx (S₁.onCtx ctx)) with
        env := σ :: (Schk.onCtx (S₁.onCtx ctx)).env } : Ctx).env, p.1 ∉ M.body.freeVars := by
      intro p hp M hM; rcases List.mem_cons.mp hM with rfl | hM
      · exact hSσall p hp
      · rcases List.mem_append.mp hp with hpS₁ | hpSchk
        · exact Subst.onCtx_avoid (Subst.eliminates_onCtx (hrE p hpS₁)) (cross1 p hpS₁) M hM
        · exact Subst.eliminates_onCtx (UnifyRel.eliminates huni p hpSchk) M hM
    have cross2 : ∀ p ∈ S₁ ++ Schk, ∀ q ∈ S₂, p.1 ∉ q.2.freeVars := fun p hp q hq =>
      (Infer.eOut_avoid hbody (w := p.1) (hdomall p hp) (hbodyctx p hp) (hSbody p hp)).1 q hq
    refine ⟨Subst.eliminates_append hE1Schk hbE cross2, ?_⟩
    intro p hp
    rcases List.mem_append.mp hp with hp1Schk | hpS₂
    · exact (Infer.eOut_avoid hbody (w := p.1) (hdomall p hp1Schk)
        (hbodyctx p hp1Schk) (hSbody p hp1Schk)).2
    · exact hbR p hpS₂
  | match_ hscrut hne hbr =>
    expose_names
    have hle1 := Infer.frontier_le hscrut
    have hΦs : ∀ y ∈ scrut.tyFreeVars, y < Φ := fun y hy => hΦ y (by
      simp only [Expr.tyFreeVars, List.mem_append]; exact Or.inl hy)
    have hΦbr : ∀ y ∈ Expr.tyFreeVars.BranchList.tyFreeVars branches, y < Φ := fun y hy => hΦ y (by
      simp only [Expr.tyFreeVars, List.mem_append]; exact Or.inr hy)
    have hSs : ∀ p ∈ S₁, p.1 ∉ scrut.tyFreeVars := fun p hp hc =>
      hSe p (List.mem_append_left _ hp) (by simp only [Expr.tyFreeVars, List.mem_append]; exact Or.inl hc)
    have hSs1br : ∀ p ∈ S₁, p.1 ∉ Expr.tyFreeVars.BranchList.tyFreeVars branches := fun p hp hc =>
      hSe p (List.mem_append_left _ hp) (by simp only [Expr.tyFreeVars, List.mem_append]; exact Or.inr hc)
    have hSbr : ∀ p ∈ S₂, p.1 ∉ Expr.tyFreeVars.BranchList.tyFreeVars branches := fun p hp hc =>
      hSe p (List.mem_append_right _ hp) (by simp only [Expr.tyFreeVars, List.mem_append]; exact Or.inr hc)
    obtain ⟨hsE, hsR⟩ := Infer.eliminates hscrut hctx hΦs hSs
    obtain ⟨hs_τbel, hs_sbel⟩ := Infer.belowFvars hscrut hctx hΦs
    have hs_dom := Infer.dom_below hscrut hctx hΦs
    have hbrctx : CtxBelow (Φ₁ + 1) (S₁.onCtx ctx) :=
      Subst.onCtx_below (fun p hp => (hs_sbel p hp).mono (by omega)) (by omega) hctx
    have hbrE := InferBranches.eliminates hbr hbrctx (hs_τbel.mono (by omega)) (.fvar (by omega))
      (fun y hy => by have := hΦbr y hy; omega) hSbr
    have hcross : ∀ p ∈ S₁, ∀ q ∈ S₂, p.1 ∉ q.2.freeVars := fun p hp q hq =>
      (InferBranches.eOut_avoid hbr (w := p.1) (by have := hs_dom p hp; omega)
        (Subst.eliminates_onCtx (hsE p hp)) (hsR p hp)
        (by intro hc; simp only [Ty.freeVars, List.mem_singleton] at hc; have := hs_dom p hp; omega)
        (hSs1br p hp)).1 q hq
    refine ⟨Subst.eliminates_append hsE hbrE hcross, ?_⟩
    intro p hp
    rcases List.mem_append.mp hp with hpS₁ | hpS₂
    · exact (InferBranches.eOut_avoid hbr (w := p.1) (by have := hs_dom p hpS₁; omega)
        (Subst.eliminates_onCtx (hsE p hpS₁)) (hsR p hpS₁)
        (by intro hc; simp only [Ty.freeVars, List.mem_singleton] at hc; have := hs_dom p hpS₁; omega)
        (hSs1br p hpS₁)).2
    · exact hbrE p hpS₂ (Ty.fvar Φ₁)
  | letRec hwf hgroup hceiling hbody =>
    expose_names
    have hlen : bindings.length = anns.length := by
      have h₁ := InferRecGroup.length_eq hgroup
      rw [RecSpec.init_length] at h₁
      exact h₁
    have hgrpLe : Φ + bindings.length ≤ Φ₁ := InferRecGroup.frontier_le hgroup
    simp only [Expr.tyFreeVars, List.mem_append] at hΦ
    have hΦann : ∀ y ∈ Expr.tyFreeVars.AnnList.tyFreeVars anns, y < Φ := fun y hy => hΦ y (Or.inl (Or.inl hy))
    have hΦbind : ∀ y ∈ Expr.tyFreeVars.RecGroup.tyFreeVars bindings, y < Φ := fun y hy => hΦ y (Or.inl (Or.inr hy))
    have hΦbody : ∀ y ∈ body.tyFreeVars, y < Φ := fun y hy => hΦ y (Or.inr hy)
    have hS₁e : ∀ p ∈ S₁, p.1 ∉ Expr.tyFreeVars.RecGroup.tyFreeVars bindings := fun p hp hc =>
      hSe p (List.mem_append_left _ hp) (by
        simp only [Expr.tyFreeVars, List.mem_append]; exact .inl (.inr hc))
    have hS₁ann : ∀ p ∈ S₁, p.1 ∉ Expr.tyFreeVars.AnnList.tyFreeVars anns := fun p hp hc =>
      hSe p (List.mem_append_left _ hp) (by
        simp only [Expr.tyFreeVars, List.mem_append]; exact .inl (.inl hc))
    have hS₁body : ∀ p ∈ S₁, p.1 ∉ body.tyFreeVars := fun p hp hc =>
      hSe p (List.mem_append_left _ hp) (by
        simp only [Expr.tyFreeVars, List.mem_append]; exact .inr hc)
    have hS₂body : ∀ p ∈ S₂, p.1 ∉ body.tyFreeVars := fun p hp hc =>
      hSe p (List.mem_append_right _ hp) (by
        simp only [Expr.tyFreeVars, List.mem_append]; exact .inr hc)
    have hspecs_init : ∀ s ∈ RecSpec.init Φ anns, s.BelowFvars (Φ + bindings.length) := by
      intro s hs
      rcases List.mem_iff_getElem.mp hs with ⟨j, hj, rfl⟩
      have hlenj : j < anns.length := by
        have h₂ := RecSpec.init_length Φ anns
        omega
      have hget : (RecSpec.init Φ anns)[j] = RecSpec.mono (.fvar (Φ + j)) := by
        have h₁ := List.getElem?_eq_getElem hj
        rw [RecSpec.init_getElem? Φ anns j, List.getElem?_eq_getElem hlenj] at h₁
        injection h₁ with hEq
        exact hEq.symm
      rw [hget]
      refine Ty.BelowFvars.fvar ?_
      omega
    have hctxGroup : CtxBelow (Φ + bindings.length)
        { ctx with env := (RecSpec.init Φ anns).map (RecSpec.rhsEntry [] []) ++ ctx.env } := by
      intro M hM
      rcases List.mem_append.mp hM with hM1 | hM2
      · obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hM1
        exact RecSpec.rhsEntry_nil_belowFvars (hspecs_init s hs)
      · exact (hctx M hM2).mono (by omega)
    have hS₁E : ∀ p ∈ S₁, ∀ x : Ty, p.1 ∉ (S₁.onTy x).freeVars :=
      InferRecGroup.eliminates hgroup hctxGroup hspecs_init
        (fun y hy => by have := hΦbind y hy; omega) hS₁e
        (fun p hp σ hσ hc => hS₁ann p hp (Expr.scheme_body_mem_annList_tyFreeVars (RecSpec.poly_mem_init hσ) hc))
    have hS₁bel : ∀ p ∈ S₁, Ty.BelowFvars Φ₁ p.2 :=
      InferRecGroup.belowFvars hgroup hctxGroup hspecs_init
        (fun y hy => by have := hΦbind y hy; omega)
    have hS₁dom : ∀ p ∈ S₁, p.1 < Φ₁ :=
      InferRecGroup.dom_below hgroup hctxGroup hspecs_init
        (fun y hy => by have := hΦbind y hy; omega)
    have hspecs_post : ∀ s' ∈ (RecSpec.init Φ anns).map (RecSpec.onSubst S₁), s'.BelowFvars Φ₁ := by
      intro s' hs'
      obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hs'
      exact RecSpec.BelowFvars.onSubst hS₁bel ((hspecs_init s hs).mono hgrpLe)
    have hbodyCtx : CtxBelow Φ₁
        { (S₁.onCtx ctx) with
          env := RecSpecs.ceilingSchemes
                   (genGroupVars (RecGroup.rigidVars anns bindings) (S₁.onCtx ctx).env
                     (RecSpecs.monoTys ((RecSpec.init Φ anns).map (RecSpec.onSubst S₁))))
                   anns
                   ((RecSpec.init Φ anns).map (RecSpec.onSubst S₁))
                 ++ (S₁.onCtx ctx).env } := by
      intro M hM
      rcases List.mem_append.mp hM with hM1 | hM2
      · obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hM1
        have hpa : p.1 ∈ anns := (List.of_mem_zip hp).1
        have hps : p.2 ∈ (RecSpec.init Φ anns).map (RecSpec.onSubst S₁) := (List.of_mem_zip hp).2
        cases p with
        | mk a s =>
          cases a with
          | some σ =>
            refine Ty.BelowFvars.of_freeVars_lt (fun v hv => ?_)
            have hann := Expr.scheme_body_mem_annList_tyFreeVars hpa hv
            have := hΦ v (.inl (.inl hann))
            omega
          | none =>
            exact RecSpec.bodyScheme_belowFvars (hspecs_post s hps)
      · exact Subst.onCtx_below hS₁bel (by omega) hctx M hM2
    obtain ⟨hbE, hbR⟩ := Infer.eliminates hbody hbodyCtx
      (fun y hy => by have := hΦbody y hy; omega) hS₂body
    have hpbodyCtx : ∀ p ∈ S₁, ∀ M ∈ ({ (S₁.onCtx ctx) with
        env := RecSpecs.ceilingSchemes
                 (genGroupVars (RecGroup.rigidVars anns bindings) (S₁.onCtx ctx).env
                   (RecSpecs.monoTys ((RecSpec.init Φ anns).map (RecSpec.onSubst S₁))))
                 anns
                 ((RecSpec.init Φ anns).map (RecSpec.onSubst S₁))
               ++ (S₁.onCtx ctx).env } : Ctx).env, p.1 ∉ M.body.freeVars := by
      intro p hp M hM
      rcases List.mem_append.mp hM with hM1 | hM2
      · obtain ⟨p0, hp0, rfl⟩ := List.mem_map.mp hM1
        have hpa : p0.1 ∈ anns := (List.of_mem_zip hp0).1
        have hps : p0.2 ∈ (RecSpec.init Φ anns).map (RecSpec.onSubst S₁) := (List.of_mem_zip hp0).2
        cases p0 with
        | mk a s =>
          cases a with
          | some σ =>
            intro hc
            exact hS₁ann p hp (Expr.scheme_body_mem_annList_tyFreeVars hpa hc)
          | none =>
            intro hc
            have hws : p.1 ∈ s.freeVars := RecSpec.mem_bodyScheme_freeVars hc
            obtain ⟨s0, hs0, rfl⟩ := List.mem_map.mp hps
            rcases List.mem_iff_getElem.mp hs0 with ⟨j, hj, rfl⟩
            have hlenj : j < anns.length := by
              have h₂ := RecSpec.init_length Φ anns
              omega
            have hget : (RecSpec.init Φ anns)[j] = RecSpec.mono (.fvar (Φ + j)) := by
              have h₁ := List.getElem?_eq_getElem hj
              rw [RecSpec.init_getElem? Φ anns j, List.getElem?_eq_getElem hlenj] at h₁
              injection h₁ with hEq
              exact hEq.symm
            rw [hget] at hws
            exact absurd hws (hS₁E p hp (Ty.fvar (Φ + j)))
      · exact Subst.eliminates_onCtx (hS₁E p hp) M hM2
    have hcross : ∀ p ∈ S₁, ∀ q ∈ S₂, p.1 ∉ q.2.freeVars := fun p hp q hq =>
      (Infer.eOut_avoid hbody (w := p.1) (hS₁dom p hp) (hpbodyCtx p hp) (hS₁body p hp)).1 q hq
    refine ⟨Subst.eliminates_append hS₁E hbE hcross, ?_⟩
    intro p hp
    rcases List.mem_append.mp hp with hpS₁ | hpS₂
    · exact (Infer.eOut_avoid hbody (w := p.1) (hS₁dom p hpS₁) (hpbodyCtx p hpS₁) (hS₁body p hpS₁)).2
    · exact hbR p hpS₂
termination_by e.size
decreasing_by all_goals (try subst_vars; try simp only [Expr.size, Expr.size_openTyVars]; omega)
theorem InferBranches.eliminates {Φ ctx scrutTy ρ brs Φ' S}
    (h : InferBranches Φ ctx scrutTy ρ brs Φ' S)
    (hctx : CtxBelow Φ ctx) (hsc : Ty.BelowFvars Φ scrutTy) (hρ : Ty.BelowFvars Φ ρ)
    (hΦ : ∀ y ∈ Expr.tyFreeVars.BranchList.tyFreeVars brs, y < Φ)
    (hSe : ∀ p ∈ S, p.1 ∉ Expr.tyFreeVars.BranchList.tyFreeVars brs) :
    (∀ p ∈ S, ∀ x : Ty, p.1 ∉ (S.onTy x).freeVars) := by
  cases h with
  | nil => simp
  | cons hlook hn huni0 hbody huni hrest =>
    expose_names
    have hle0 : Φ + ctor.paramCount ≤ Φ₁ := Infer.frontier_le hbody
    have hΦhead : ∀ y ∈ body.tyFreeVars, y < Φ := fun y hy => hΦ y (by
      simp only [Expr.tyFreeVars.BranchList.tyFreeVars, List.mem_append]; exact Or.inl hy)
    have hΦrest : ∀ y ∈ Expr.tyFreeVars.BranchList.tyFreeVars rest, y < Φ := fun y hy => hΦ y (by
      simp only [Expr.tyFreeVars.BranchList.tyFreeVars, List.mem_append]; exact Or.inr hy)
    have hSbody0 : ∀ p ∈ S₁, p.1 ∉ body.tyFreeVars := fun p hp hc =>
      hSe p (by simp only [List.mem_append]; tauto) (by
        simp only [Expr.tyFreeVars.BranchList.tyFreeVars, List.mem_append]; exact Or.inl hc)
    have hSrestAll : ∀ p ∈ (S₀ ++ S₁) ++ S₂, p.1 ∉ Expr.tyFreeVars.BranchList.tyFreeVars rest :=
      fun p hp hc => hSe p (List.mem_append_left _ hp) (by
        simp only [Expr.tyFreeVars.BranchList.tyFreeVars, List.mem_append]; exact Or.inr hc)
    have hSrest3 : ∀ p ∈ S₃, p.1 ∉ Expr.tyFreeVars.BranchList.tyFreeVars rest := fun p hp hc =>
      hSe p (List.mem_append_right _ hp) (by
        simp only [Expr.tyFreeVars.BranchList.tyFreeVars, List.mem_append]; exact Or.inr hc)
    -- S₀
    have hS₀bel : ∀ p ∈ S₀, Ty.BelowFvars (Φ + ctor.paramCount) p.2 :=
      UnifyRel.belowFvars huni0 (hsc.mono (by omega))
        (.customTy (fun t ht => by obtain ⟨x, hx, rfl⟩ := List.mem_map.mp ht
                                   exact .fvar (by have := freshVars_lt x hx; omega)))
    have hS₀dom : ∀ p ∈ S₀, p.1 < Φ + ctor.paramCount := by
      intro p hp; rcases UnifyRel.dom_mem huni0 p hp with h | h
      · exact (hsc.mono (show Φ ≤ Φ + ctor.paramCount by omega)).mem_lt p.1 h
      · simp only [Ty.freeVars] at h; rw [mem_TyList_freeVars] at h
        obtain ⟨t, ht, hgt⟩ := h; obtain ⟨x, hx, rfl⟩ := List.mem_map.mp ht
        simp only [Ty.freeVars, List.mem_singleton] at hgt; have := freshVars_lt x hx; omega
    have hbctx := branchBindings_below (ctorr := ctor)
      (ta := ((freshVars Φ ctor.paramCount).map (Ty.fvar ·)).map S₀.onTy)
      (Subst.onCtx_below hS₀bel (by omega) hctx)
      (fun t ht => by obtain ⟨v, hv, rfl⟩ := List.mem_map.mp ht
                      obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hv
                      exact Subst.onTy_belowFvars hS₀bel (.fvar (by have := freshVars_lt x hx; omega)))
    obtain ⟨hbE, hbR⟩ := Infer.eliminates hbody hbctx (fun y hy => by have := hΦhead y hy; omega) hSbody0
    obtain ⟨hb_τbel, hb_sbel⟩ := Infer.belowFvars hbody hbctx (fun y hy => by have := hΦhead y hy; omega)
    have hb_dom := Infer.dom_below hbody hbctx (fun y hy => by have := hΦhead y hy; omega)
    have hbranchAvoid : ∀ p ∈ S₀, ∀ M ∈ ({ (S₀.onCtx ctx) with
        env := (ctor.contents.map (Ty.openWith (((freshVars Φ ctor.paramCount).map (Ty.fvar ·)).map S₀.onTy))).map PolyTy.mkTrivial
          ++ (S₀.onCtx ctx).env } : Ctx).env, p.1 ∉ M.body.freeVars := by
      intro p hp M hM; rcases List.mem_append.mp hM with hM | hM
      · obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hM
        obtain ⟨c, hc, rfl⟩ := List.mem_map.mp ht
        simp only [PolyTy.mkTrivial]
        refine Ty.not_mem_freeVars_openWith ?_ ((ctor.closed c hc).not_mem_freeVars p.1)
        intro v hv
        obtain ⟨v0, hv0, rfl⟩ := List.mem_map.mp hv
        obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hv0
        exact UnifyRel.eliminates huni0 p hp (Ty.fvar x)
      · exact Subst.eliminates_onCtx (UnifyRel.eliminates huni0 p hp) M hM
    have heOutBody : ∀ p ∈ S₀, (∀ q ∈ S₁, p.1 ∉ q.2.freeVars) ∧ p.1 ∉ τb.freeVars := fun p hp =>
      Infer.eOut_avoid hbody (w := p.1) (hS₀dom p hp) (hbranchAvoid p hp) (by
        intro hc; exact hSe p (by simp only [List.mem_append]; tauto) (by
          simp only [Expr.tyFreeVars.BranchList.tyFreeVars, List.mem_append]; exact Or.inl hc))
    -- E01
    have cross01 : ∀ p ∈ S₀, ∀ q ∈ S₁, p.1 ∉ q.2.freeVars := fun p hp q hq => (heOutBody p hp).1 q hq
    have hE01 := Subst.eliminates_append (UnifyRel.eliminates huni0) hbE cross01
    -- S₂
    have hρbel : Ty.BelowFvars (Φ + ctor.paramCount) ρ := hρ.mono (by omega)
    have hS₀ρbel : Ty.BelowFvars Φ₁ (S₀.onTy ρ) :=
      (Subst.onTy_belowFvars hS₀bel hρbel).mono hle0
    have hS₁S₀ρbel : Ty.BelowFvars Φ₁ (S₁.onTy (S₀.onTy ρ)) := Subst.onTy_belowFvars hb_sbel hS₀ρbel
    have hS₂bel : ∀ p ∈ S₂, Ty.BelowFvars Φ₁ p.2 := UnifyRel.belowFvars huni hb_τbel hS₁S₀ρbel
    have hS₂dom : ∀ p ∈ S₂, p.1 < Φ₁ := by
      intro p hp; rcases UnifyRel.dom_mem huni p hp with h | h
      · exact hb_τbel.mem_lt p.1 h
      · exact hS₁S₀ρbel.mem_lt p.1 h
    have cross012 : ∀ p ∈ S₀ ++ S₁, ∀ q ∈ S₂, p.1 ∉ q.2.freeVars := by
      intro p hp q hq hwq
      rcases UnifyRel.range_mem huni q hq p.1 hwq with h | h
      · rcases List.mem_append.mp hp with hpS₀ | hpS₁
        · exact (heOutBody p hpS₀).2 h
        · exact hbR p hpS₁ h
      · exact (Subst.onTy_append S₀ S₁ ρ ▸ hE01 p hp ρ) h
    have hE012 := Subst.eliminates_append hE01 (UnifyRel.eliminates huni) cross012
    -- rest
    have hle1 := InferBranches.frontier_le hrest
    have hscrut'bel : Ty.BelowFvars Φ₁ (S₂.onTy (S₁.onTy (S₀.onTy scrutTy))) :=
      Subst.onTy_belowFvars hS₂bel (Subst.onTy_belowFvars hb_sbel
        ((Subst.onTy_belowFvars hS₀bel (hsc.mono (by omega))).mono hle0))
    have hρ'bel : Ty.BelowFvars Φ₁ (S₂.onTy (S₁.onTy (S₀.onTy ρ))) :=
      Subst.onTy_belowFvars hS₂bel hS₁S₀ρbel
    have hctx1 : CtxBelow Φ₁ (S₂.onCtx (S₁.onCtx (S₀.onCtx ctx))) :=
      Subst.onCtx_below hS₂bel (le_refl _) (Subst.onCtx_below hb_sbel (le_refl _)
        (Subst.onCtx_below (fun p hp => (hS₀bel p hp).mono hle0) (by omega) hctx))
    have hrestE := InferBranches.eliminates hrest hctx1 hscrut'bel hρ'bel
      (fun y hy => by have := hΦrest y hy; omega) hSrest3
    have happ3 : ∀ x : Ty, ((S₀ ++ S₁) ++ S₂).onTy x = S₂.onTy (S₁.onTy (S₀.onTy x)) :=
      fun x => by rw [Subst.onTy_append, Subst.onTy_append]
    have honCtx3 : ((S₀ ++ S₁) ++ S₂).onCtx ctx = S₂.onCtx (S₁.onCtx (S₀.onCtx ctx)) := by
      rw [Subst.onCtx_append, Subst.onCtx_append]
    have cross0123 : ∀ p ∈ (S₀ ++ S₁) ++ S₂, ∀ q ∈ S₃, p.1 ∉ q.2.freeVars := by
      intro p hp q hq
      have hpdom : p.1 < Φ₁ := by
        rcases List.mem_append.mp hp with hp01 | hpS₂
        · rcases List.mem_append.mp hp01 with hpS₀ | hpS₁
          · have := hS₀dom p hpS₀; omega
          · exact hb_dom p hpS₁
        · exact hS₂dom p hpS₂
      refine (InferBranches.eOut_avoid hrest (w := p.1) hpdom
        (honCtx3 ▸ Subst.eliminates_onCtx (hE012 p hp))
        (happ3 scrutTy ▸ hE012 p hp scrutTy)
        (happ3 ρ ▸ hE012 p hp ρ) (hSrestAll p hp)).1 q hq
    exact Subst.eliminates_append hE012 hrestE cross0123
  | consWild hbody huni hrest =>
    expose_names
    have hle1 := Infer.frontier_le hbody
    have hΦhead : ∀ y ∈ body.tyFreeVars, y < Φ := fun y hy => hΦ y (by
      simp only [Expr.tyFreeVars.BranchList.tyFreeVars, List.mem_append]; exact Or.inl hy)
    have hΦrest : ∀ y ∈ Expr.tyFreeVars.BranchList.tyFreeVars rest, y < Φ := fun y hy => hΦ y (by
      simp only [Expr.tyFreeVars.BranchList.tyFreeVars, List.mem_append]; exact Or.inr hy)
    have hSbody0 : ∀ p ∈ S₁, p.1 ∉ body.tyFreeVars := fun p hp hc =>
      hSe p (List.mem_append_left _ (List.mem_append_left _ hp)) (by
        simp only [Expr.tyFreeVars.BranchList.tyFreeVars, List.mem_append]; exact Or.inl hc)
    have hSrestAll : ∀ p ∈ S₁ ++ S₂, p.1 ∉ Expr.tyFreeVars.BranchList.tyFreeVars rest :=
      fun p hp hc => hSe p (List.mem_append_left _ hp) (by
        simp only [Expr.tyFreeVars.BranchList.tyFreeVars, List.mem_append]; exact Or.inr hc)
    have hSrest3 : ∀ p ∈ S₃, p.1 ∉ Expr.tyFreeVars.BranchList.tyFreeVars rest := fun p hp hc =>
      hSe p (List.mem_append_right _ hp) (by
        simp only [Expr.tyFreeVars.BranchList.tyFreeVars, List.mem_append]; exact Or.inr hc)
    obtain ⟨hbE, hbR⟩ := Infer.eliminates hbody hctx hΦhead hSbody0
    obtain ⟨hb_τbel, hb_sbel⟩ := Infer.belowFvars hbody hctx hΦhead
    have hb_dom := Infer.dom_below hbody hctx hΦhead
    have hS₁ρbel : Ty.BelowFvars Φ₁ (S₁.onTy ρ) := Subst.onTy_belowFvars hb_sbel (hρ.mono hle1)
    have hS₂bel : ∀ p ∈ S₂, Ty.BelowFvars Φ₁ p.2 := UnifyRel.belowFvars huni hb_τbel hS₁ρbel
    have hS₂dom : ∀ p ∈ S₂, p.1 < Φ₁ := by
      intro p hp; rcases UnifyRel.dom_mem huni p hp with h | h
      · exact hb_τbel.mem_lt p.1 h
      · exact hS₁ρbel.mem_lt p.1 h
    have cross1 : ∀ p ∈ S₁, ∀ q ∈ S₂, p.1 ∉ q.2.freeVars := by
      intro p hp q hq hwq
      rcases UnifyRel.range_mem huni q hq p.1 hwq with h | h
      · exact hbR p hp h
      · exact hbE p hp ρ h
    have hE12 := Subst.eliminates_append hbE (UnifyRel.eliminates huni) cross1
    have hctx1 : CtxBelow Φ₁ (S₂.onCtx (S₁.onCtx ctx)) :=
      Subst.onCtx_below hS₂bel (le_refl _) (Subst.onCtx_below hb_sbel hle1 hctx)
    have hrestE := InferBranches.eliminates hrest hctx1
      (Subst.onTy_belowFvars hS₂bel (Subst.onTy_belowFvars hb_sbel (hsc.mono hle1)))
      (Subst.onTy_belowFvars hS₂bel hS₁ρbel)
      (fun y hy => by have := hΦrest y hy; omega) hSrest3
    have happ2 : ∀ x : Ty, (S₁ ++ S₂).onTy x = S₂.onTy (S₁.onTy x) :=
      fun x => by rw [Subst.onTy_append]
    have honCtx2 : (S₁ ++ S₂).onCtx ctx = S₂.onCtx (S₁.onCtx ctx) := by rw [Subst.onCtx_append]
    have cross2 : ∀ p ∈ S₁ ++ S₂, ∀ q ∈ S₃, p.1 ∉ q.2.freeVars := by
      intro p hp q hq
      have hpdom : p.1 < Φ₁ := by
        rcases List.mem_append.mp hp with hpS₁ | hpS₂
        · exact hb_dom p hpS₁
        · exact hS₂dom p hpS₂
      refine (InferBranches.eOut_avoid hrest (w := p.1) hpdom
        (honCtx2 ▸ Subst.eliminates_onCtx (hE12 p hp))
        (happ2 scrutTy ▸ hE12 p hp scrutTy)
        (happ2 ρ ▸ hE12 p hp ρ) (hSrestAll p hp)).1 q hq
    exact Subst.eliminates_append hE12 hrestE cross2
termination_by Expr.sizeBranches brs
decreasing_by all_goals (try subst_vars; try simp only [Expr.sizeBranches]; omega)
/-- Fused `InferRecGroup` idempotency (consMono + consPoly): a group-substitution
    domain var never survives in any `S`-image. The scheme-avoidance hypothesis
    `hSsch` covers the poly members (their scoped variables are outer-rigid). -/
theorem InferRecGroup.eliminates {Φ ctx bindings specs Φ' S}
    (h : InferRecGroup Φ ctx bindings specs Φ' S)
    (hctx : CtxBelow Φ ctx) (hspecs : ∀ s ∈ specs, s.BelowFvars Φ)
    (hΦ : ∀ y ∈ Expr.tyFreeVars.RecGroup.tyFreeVars bindings, y < Φ)
    (hSe : ∀ p ∈ S, p.1 ∉ Expr.tyFreeVars.RecGroup.tyFreeVars bindings)
    (hSsch : ∀ p ∈ S, ∀ σ, RecSpec.poly σ ∈ specs → p.1 ∉ σ.body.freeVars) :
    (∀ p ∈ S, ∀ x : Ty, p.1 ∉ (S.onTy x).freeVars) := by
  cases h with
  | nil => simp
  | consMono he huni hrest =>
    expose_names
    have hle1 := Infer.frontier_le he
    have hΦe : ∀ y ∈ e.tyFreeVars, y < Φ := fun y hy => hΦ y (by
      simp only [Expr.tyFreeVars.RecGroup.tyFreeVars, List.mem_append]; exact .inl hy)
    have hΦrest : ∀ y ∈ Expr.tyFreeVars.RecGroup.tyFreeVars rest, y < Φ := fun y hy => hΦ y (by
      simp only [Expr.tyFreeVars.RecGroup.tyFreeVars, List.mem_append]; exact .inr hy)
    have hSe1 : ∀ p ∈ S₁, p.1 ∉ e.tyFreeVars := fun p hp hc =>
      hSe p (List.mem_append_left _ (List.mem_append_left _ hp)) (by
        simp only [Expr.tyFreeVars.RecGroup.tyFreeVars, List.mem_append]; exact .inl hc)
    have hSrestAll : ∀ p ∈ S₁ ++ S₂, p.1 ∉ Expr.tyFreeVars.RecGroup.tyFreeVars rest :=
      fun p hp hc => hSe p (List.mem_append_left _ hp) (by
        simp only [Expr.tyFreeVars.RecGroup.tyFreeVars, List.mem_append]; exact .inr hc)
    have hSrest3 : ∀ p ∈ S₃, p.1 ∉ Expr.tyFreeVars.RecGroup.tyFreeVars rest := fun p hp hc =>
      hSe p (List.mem_append_right _ hp) (by
        simp only [Expr.tyFreeVars.RecGroup.tyFreeVars, List.mem_append]; exact .inr hc)
    obtain ⟨heE, heR⟩ := Infer.eliminates he hctx hΦe hSe1
    obtain ⟨he_τbel, he_sbel⟩ := Infer.belowFvars he hctx hΦe
    have he_dom := Infer.dom_below he hctx hΦe
    have hτB : Ty.BelowFvars Φ τ := hspecs (.mono τ) List.mem_cons_self
    have hS₁τbel : Ty.BelowFvars Φ₁ (S₁.onTy τ) := Subst.onTy_belowFvars he_sbel (hτB.mono hle1)
    have hS₂bel : ∀ p ∈ S₂, Ty.BelowFvars Φ₁ p.2 := UnifyRel.belowFvars huni he_τbel hS₁τbel
    have hS₂dom : ∀ p ∈ S₂, p.1 < Φ₁ := by
      intro p hp; rcases UnifyRel.dom_mem huni p hp with h | h
      · exact he_τbel.mem_lt p.1 h
      · exact hS₁τbel.mem_lt p.1 h
    have hctx1 : CtxBelow Φ₁ (S₂.onCtx (S₁.onCtx ctx)) :=
      Subst.onCtx_below hS₂bel (le_refl _) (Subst.onCtx_below he_sbel hle1 hctx)
    have hspecs' : ∀ s' ∈ specs.map (RecSpec.onSubst (S₁ ++ S₂)), s'.BelowFvars Φ₁ := by
      intro s' hs'
      obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hs'
      exact RecSpec.BelowFvars.onSubst
        (fun p hp => (List.mem_append.mp hp).elim (he_sbel p) (hS₂bel p))
        ((hspecs s (List.mem_cons_of_mem _ hs)).mono hle1)
    have hrestE := InferRecGroup.eliminates hrest hctx1 hspecs'
      (fun y hy => lt_of_lt_of_le (hΦrest y hy) hle1) hSrest3
      (fun p hp σ hσ => hSsch p (List.mem_append_right _ hp) σ
        (List.mem_cons_of_mem _ (RecSpec.poly_mem_map_onSubst.mp hσ)))
    have cross_e_S₂ : ∀ p ∈ S₁, ∀ q ∈ S₂, p.1 ∉ q.2.freeVars := by
      intro p hp q hq hwq
      rcases UnifyRel.range_mem huni q hq p.1 hwq with h | h
      · exact heR p hp h
      · exact heE p hp τ h
    have hE1S₂ := Subst.eliminates_append heE (UnifyRel.eliminates huni) cross_e_S₂
    have cross_S₁S₂_S₃ : ∀ p ∈ S₁ ++ S₂, ∀ q ∈ S₃, p.1 ∉ q.2.freeVars := by
      intro p hp q hq
      have hpdom : p.1 < Φ₁ := by
        rcases List.mem_append.mp hp with h | h
        · exact he_dom p h
        · exact hS₂dom p h
      have hpctx : ∀ M ∈ (S₂.onCtx (S₁.onCtx ctx)).env, p.1 ∉ M.body.freeVars := by
        rw [show (S₂.onCtx (S₁.onCtx ctx)) = (S₁ ++ S₂).onCtx ctx
              from (Subst.onCtx_append S₁ S₂ ctx).symm]
        exact Subst.eliminates_onCtx (hE1S₂ p hp)
      have hptg : ∀ s' ∈ specs.map (RecSpec.onSubst (S₁ ++ S₂)), p.1 ∉ s'.freeVars := by
        intro s' hs'
        obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hs'
        cases s with
        | mono τ0 => exact hE1S₂ p hp τ0
        | poly σ0 => exact hSsch p (List.mem_append_left _ hp) σ0 (List.mem_cons_of_mem _ hs)
      exact (InferRecGroup.eOut_avoid hrest (w := p.1) hpdom hpctx hptg (hSrestAll p hp)) q hq
    exact Subst.eliminates_append hE1S₂ hrestE cross_S₁S₂_S₃
  | consPoly hΦN hinfer huni hesc1 hesc2 hrest =>
    expose_names
    have hrle := Infer.frontier_le hinfer
    have hσBel : Ty.BelowFvars Φ σ.body := hspecs (.poly σ) List.mem_cons_self
    have hΦe : ∀ y ∈ e.tyFreeVars, y < Φ := fun y hy => hΦ y (by
      simp only [Expr.tyFreeVars.RecGroup.tyFreeVars, List.mem_append]; exact .inl hy)
    have hΦrest : ∀ y ∈ Expr.tyFreeVars.RecGroup.tyFreeVars rest, y < Φ := fun y hy => hΦ y (by
      simp only [Expr.tyFreeVars.RecGroup.tyFreeVars, List.mem_append]; exact .inr hy)
    have hΦeopen : ∀ y ∈ (e.openTyVars (freshVars N σ.paramCount)).tyFreeVars,
        y < N + σ.paramCount := by
      intro y hy
      rcases Expr.tyFreeVars_openTyVars hy with h | h
      · have := hΦe y h; omega
      · have := freshVars_lt y h; omega
    have hSeopen : ∀ p ∈ S₁, p.1 ∉ (e.openTyVars (freshVars N σ.paramCount)).tyFreeVars := by
      intro p hp hc
      rcases Expr.tyFreeVars_openTyVars hc with h | h
      · exact hSe p (List.mem_append_left _ (List.mem_append_left _ hp)) (by
          simp only [Expr.tyFreeVars.RecGroup.tyFreeVars, List.mem_append]; exact .inl h)
      · exact hesc1 p.1 h (List.mem_map.mpr ⟨p, List.mem_append_left _ hp, rfl⟩)
    have hSσ1 : ∀ p ∈ S₁, p.1 ∉ σ.body.freeVars := fun p hp =>
      hSsch p (List.mem_append_left _ (List.mem_append_left _ hp)) σ List.mem_cons_self
    have hctx_pc : CtxBelow (N + σ.paramCount) ctx := fun M hM => (hctx M hM).mono (by omega)
    obtain ⟨hrE, hrR⟩ := Infer.eliminates hinfer hctx_pc hΦeopen hSeopen
    obtain ⟨hr_τbel, hr_sbel⟩ := Infer.belowFvars hinfer hctx_pc hΦeopen
    have hr_dom := Infer.dom_below hinfer hctx_pc hΦeopen
    have hσopenbel : Ty.BelowFvars Φ₁ (σ.openVars (freshVars N σ.paramCount)) :=
      Ty.openVars_belowFvars (hσBel.mono (by omega))
        (fun x hx => by have := freshVars_lt x hx; omega)
    have hSchkbel : ∀ p ∈ Schk, Ty.BelowFvars Φ₁ p.2 := UnifyRel.belowFvars huni hr_τbel hσopenbel
    have hSchkdom : ∀ p ∈ Schk, p.1 < Φ₁ := by
      intro p hp; rcases UnifyRel.dom_mem huni p hp with h | h
      · exact hr_τbel.mem_lt p.1 h
      · exact hσopenbel.mem_lt p.1 h
    have cross1 : ∀ p ∈ S₁, ∀ q ∈ Schk, p.1 ∉ q.2.freeVars := by
      intro p hp q hq hwq
      rcases UnifyRel.range_mem huni q hq p.1 hwq with h | h
      · exact hrR p hp h
      · rcases Ty.freeVars_openVars_subset p.1 h with h' | h'
        · exact hSσ1 p hp h'
        · exact hesc1 p.1 h' (List.mem_map.mpr ⟨p, List.mem_append_left _ hp, rfl⟩)
    have hE1Schk := Subst.eliminates_append hrE (UnifyRel.eliminates huni) cross1
    have hdomall : ∀ p ∈ S₁ ++ Schk, p.1 < Φ₁ := by
      intro p hp; rcases List.mem_append.mp hp with h | h
      · exact hr_dom p h
      · exact hSchkdom p h
    have hctx1 : CtxBelow Φ₁ (Schk.onCtx (S₁.onCtx ctx)) :=
      Subst.onCtx_below hSchkbel (le_refl _) (Subst.onCtx_below hr_sbel hrle hctx_pc)
    have hΦΦ₁ : Φ ≤ Φ₁ := by omega
    have hspecs' : ∀ s' ∈ specs.map (RecSpec.onSubst (S₁ ++ Schk)), s'.BelowFvars Φ₁ := by
      intro s' hs'
      obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hs'
      exact RecSpec.BelowFvars.onSubst
        (fun p hp => (List.mem_append.mp hp).elim (hr_sbel p) (hSchkbel p))
        ((hspecs s (List.mem_cons_of_mem _ hs)).mono hΦΦ₁)
    have hrestE := InferRecGroup.eliminates hrest hctx1 hspecs'
      (fun y hy => lt_of_lt_of_le (hΦrest y hy) hΦΦ₁)
      (fun p hp hc => hSe p (List.mem_append_right _ hp) (by
        simp only [Expr.tyFreeVars.RecGroup.tyFreeVars, List.mem_append]; exact .inr hc))
      (fun p hp σ' hσ' => hSsch p (List.mem_append_right _ hp) σ'
        (List.mem_cons_of_mem _ (RecSpec.poly_mem_map_onSubst.mp hσ')))
    have cross2 : ∀ p ∈ S₁ ++ Schk, ∀ q ∈ S₂, p.1 ∉ q.2.freeVars := by
      intro p hp q hq
      have hpctx : ∀ M ∈ (Schk.onCtx (S₁.onCtx ctx)).env, p.1 ∉ M.body.freeVars := by
        rw [show Schk.onCtx (S₁.onCtx ctx) = (S₁ ++ Schk).onCtx ctx
              from (Subst.onCtx_append S₁ Schk ctx).symm]
        exact Subst.eliminates_onCtx (hE1Schk p hp)
      have hptg : ∀ s' ∈ specs.map (RecSpec.onSubst (S₁ ++ Schk)), p.1 ∉ s'.freeVars := by
        intro s' hs'
        obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hs'
        cases s with
        | mono τ0 => exact hE1Schk p hp τ0
        | poly σ0 => exact hSsch p (List.mem_append_left _ hp) σ0 (List.mem_cons_of_mem _ hs)
      have hprest : p.1 ∉ Expr.tyFreeVars.RecGroup.tyFreeVars rest := fun h' =>
        hSe p (List.mem_append_left _ hp) (by
          simp only [Expr.tyFreeVars.RecGroup.tyFreeVars, List.mem_append]; exact .inr h')
      exact (InferRecGroup.eOut_avoid hrest (w := p.1) (hdomall p hp) hpctx hptg hprest) q hq
    exact Subst.eliminates_append hE1Schk hrestE cross2
termination_by Expr.sizeRecGroup bindings
decreasing_by
  all_goals (try subst_vars; try simp only [Expr.sizeRecGroup, Expr.size_openTyVars]; omega)

end


/-! ### M4: prefix-fix corollary

DELETED: `Infer.eOut_substTyFvars_eq` (conclusion referenced the removed
elaborated-output `eOut`; its only consumers were the deleted `sound_elab`
family). -/

theorem List.zip_map_left_eq {α β γ : Type _} (f : α → γ) :
    ∀ (l : List α) (r : List β), (l.map f).zip r = (l.zip r).map (fun ab => (f ab.1, ab.2)) := by
  intro l
  induction l with
  | nil => intro r; simp
  | cons hd tl ih =>
    intro r; cases r with
    | nil => simp
    | cons rhd rtl => simp only [List.map_cons, List.zip_cons_cons, ih]

/-! Structural simp lemmas for `openWith` (the analogues for `openVars` already
    exist above, but `openWith` lacks them). -/
@[simp] private theorem Ty.openWith_prim {Vs : List Ty} {p : PrimTy} :
    Ty.openWith Vs (.prim p) = .prim p := rfl
@[simp] private theorem Ty.openWith_fvar {Vs : List Ty} {n : Nat} :
    Ty.openWith Vs (.fvar n) = .fvar n := rfl
@[simp] private theorem Ty.openWith_arrow {Vs : List Ty} {a b : Ty} :
    Ty.openWith Vs (.arrow a b) = .arrow (Ty.openWith Vs a) (Ty.openWith Vs b) := rfl
@[simp] private theorem Ty.openWith_bl {Vs : List Ty} {lo hi : FHM.Bounds.CountSlot} {e : Ty} :
    Ty.openWith Vs (.bl lo hi e) = .bl lo hi (Ty.openWith Vs e) := rfl
@[simp] private theorem Ty.openWith_customTy {Vs : List Ty} {nm : TyName} {tys : List Ty} :
    Ty.openWith Vs (.customTy nm tys) = .customTy nm (tys.map (Ty.openWith Vs)) := by
  unfold Ty.openWith
  simp only [Ty.instantiate, TyList.instantiate_eq_map]

/-- Opening a scheme body with LC args is an instantiation by those args. -/
theorem InstantiatesBy.openWith {Vs : List Ty} {n : Nat} {ty : Ty}
    (hbv : ContainsBvarsUpTo n ty) (hn : n ≤ Vs.length) :
    InstantiatesBy Vs ty (Ty.openWith Vs ty) := by
  induction ty using Ty.rec_strong with
  | prim p => exact .prim
  | fvar m => exact .fvar
  | bvar i =>
    cases hbv with
    | bvar hlt =>
      have hi : i < Vs.length := by omega
      simp only [Ty.openWith, Ty.instantiate, List.getElem?_eq_getElem hi, Option.getD_some]
      exact .bvar (List.getElem?_eq_getElem hi)
  | arrow a b iha ihb => cases hbv with | arrow ha hb => exact .arrow (iha ha) (ihb hb)
  | customTy nm tys ih =>
    cases hbv with
    | customTy hball =>
      simp only [Ty.openWith_customTy]
      exact .customTy (List.forall₂_self_map (fun t ht => ih t ht (hball t ht)))
  | bl lo hi e ih =>
    cases hbv with
    | bl he =>
      simp only [Ty.openWith, Ty.instantiate]
      exact .bl (ih he)

/-- Applying an LC substitution commutes with bvar-instantiation. -/
theorem Subst.onTy_instantiate {S : Subst} (hS : ∀ p ∈ S, p.2.IsLC) (σ : Nat → Ty) (X : Ty) :
    S.onTy (Ty.instantiate σ X) = Ty.instantiate (fun i => S.onTy (σ i)) (S.onTy X) := by
  induction X using Ty.rec_strong with
  | prim p => simp only [Ty.instantiate, Subst.onTy_prim]
  | bvar i => simp only [Ty.instantiate, Subst.onTy_bvar]
  | fvar n =>
    simp only [Ty.instantiate]
    rw [Ty.instantiate_eq_self_of_lc (Subst.onTy_lc hS ContainsBvarsUpTo.fvar)]
  | arrow a b iha ihb => simp only [Ty.instantiate, Subst.onTy_arrow, iha, ihb]
  | customTy nm tys ih =>
    simp only [Ty.instantiate, TyList.instantiate_eq_map, Subst.onTy_customTy, List.map_map]
    apply congrArg (Ty.customTy nm)
    apply List.map_congr_left
    intro t ht
    simp only [Function.comp_apply]
    exact ih t ht
  | bl lo hi e ih =>
    simp only [Ty.instantiate, Subst.onTy_bl, ih]

/-- `onTy` (LC) commutes with `openWith`. -/
theorem Subst.onTy_openWith {S : Subst} (hS : ∀ p ∈ S, p.2.IsLC) (Vs : List Ty) (X : Ty) :
    S.onTy (Ty.openWith Vs X) = Ty.openWith (Vs.map S.onTy) (S.onTy X) := by
  unfold Ty.openWith
  rw [Subst.onTy_instantiate hS]
  have hfun : (fun i => S.onTy ((Vs[i]?).getD (.bvar i)))
      = (fun i => ((Vs.map S.onTy)[i]?).getD (.bvar i)) := by
    funext i
    rw [List.getElem?_map]
    cases Vs[i]? with
    | none => simp
    | some t => simp
  rw [hfun]

/-- Applying `S` to a branch-bindings-extended context commutes with mapping the
    type args by `S`: the constructor contents are closed, so `S` only renames
    inside the opened type args. -/
theorem Subst.onCtx_branchBindings {S : Subst} {ctorr : Ctor} {ta : List Ty} {ctx : Ctx}
    (hS : ∀ p ∈ S, p.2.IsLC) :
    S.onCtx { ctx with
        env := (ctorr.contents.map (Ty.openWith ta)).map PolyTy.mkTrivial ++ ctx.env }
      = { S.onCtx ctx with
        env := (ctorr.contents.map (Ty.openWith (ta.map S.onTy))).map PolyTy.mkTrivial
          ++ (S.onCtx ctx).env } := by
  have key : ∀ c ∈ ctorr.contents,
      S.onPolyTy (PolyTy.mkTrivial (Ty.openWith ta c))
        = PolyTy.mkTrivial (Ty.openWith (ta.map S.onTy) c) := by
    intro c hc
    have hcfix : S.onTy c = c :=
      Ty.substFvars_eq_self_of_no_key
        (fun p _ => NoFreeVars.not_mem_freeVars (ctorr.closed c hc) p.1)
    simp only [Subst.onPolyTy, PolyTy.mkTrivial, Subst.onTy_openWith hS, hcfix]
  have henv : ((ctorr.contents.map (Ty.openWith ta)).map PolyTy.mkTrivial).map S.onPolyTy
      = (ctorr.contents.map (Ty.openWith (ta.map S.onTy))).map PolyTy.mkTrivial := by
    simp only [List.map_map]
    apply List.map_congr_left
    intro c hc
    simp only [Function.comp_apply]
    exact key c hc
  simp only [Subst.onCtx, Subst.onEnv, List.map_append]
  rw [henv]

/-- Erase-level twin of `Subst.onCtx_branchBindings`: `eraseBounds` pushes
    straight through a branch's pattern-binding prefix, landing on the branch
    context built from the ERASED constructor at the ERASED type args. No
    hypotheses — it is pure commutation (`Ty.eraseBounds_openWith` plus
    `Env.eraseBounds_map_mkTrivial`).

    This is what lets the branch tier of Path R completeness line the algorithm's
    body context (built from `freshBlock.map S₀.onTy`, residualised by `R₀`) up
    against the declarative one (built from the `BranchCtorSpec`'s `tyArgs`):
    rewrite with this, then discharge the remaining `ta.map Ty.eraseBounds =
    tyArgs` from `customTy_unify_dodge`'s last clause. -/
theorem Ctx.eraseBounds_branchBindings (ctorr : Ctor) (ta : List Ty) (ctx : Ctx) :
    Ctx.eraseBounds { ctx with
        env := (ctorr.contents.map (Ty.openWith ta)).map PolyTy.mkTrivial ++ ctx.env }
      = { ctx.eraseBounds with
        env := ((Ctor.eraseBounds ctorr).contents.map
            (Ty.openWith (ta.map Ty.eraseBounds))).map PolyTy.mkTrivial
          ++ ctx.eraseBounds.env } := by
  have henv : Env.eraseBounds ((ctorr.contents.map (Ty.openWith ta)).map PolyTy.mkTrivial)
      = ((Ctor.eraseBounds ctorr).contents.map
          (Ty.openWith (ta.map Ty.eraseBounds))).map PolyTy.mkTrivial := by
    simp only [Env.eraseBounds, List.map_map, Ctor.eraseBounds_contents]
    apply List.map_congr_left
    intro c hc
    simp only [Function.comp_apply, PolyTy.eraseBounds_mkTrivial, Ty.eraseBounds_openWith]
  simp only [Ctx.eraseBounds, Env.eraseBounds_append]
  rw [henv]

/-! ### Helper lemmas for the `letRec` soundness case -/

/-- Reverse of mapping the right component of a `zip`: a member of `l.zip (r.map g)`
    comes from a member of `l.zip r`. -/
private theorem List.mem_zip_map_snd {α β γ : Type _} {g : β → γ} :
    ∀ {l : List α} {r : List β} {p : α × γ},
      p ∈ l.zip (r.map g) → ∃ a b, (a, b) ∈ l.zip r ∧ p = (a, g b) := by
  intro l
  induction l with
  | nil => intro r p h; simp at h
  | cons hd tl ih =>
    intro r p h
    cases r with
    | nil => simp at h
    | cons rhd rtl =>
      simp only [List.map_cons, List.zip_cons_cons, List.mem_cons] at h
      cases h with
      | inl heq => exact ⟨hd, rhd, List.mem_cons_self, heq⟩
      | inr h' =>
        obtain ⟨a, b, hmem, heq⟩ := ih h'
        exact ⟨a, b, List.mem_cons_of_mem _ hmem, heq⟩

/-- An element of `freeVarsList` occurs in some member type's free vars. -/
private theorem Ty.mem_freeVarsList_exists {τs : List Ty} {g : Nat}
    (h : g ∈ Ty.freeVarsList τs) : ∃ t ∈ τs, g ∈ t.freeVars := by
  induction τs with
  | nil => simp [Ty.freeVarsList] at h
  | cons hd tl ih =>
    simp only [Ty.freeVarsList, List.mem_dedup, List.mem_append] at h
    rcases h with h | h
    · exact ⟨hd, List.mem_cons_self, h⟩
    · obtain ⟨t, ht, hg⟩ := ih h
      exact ⟨t, List.mem_cons_of_mem _ ht, hg⟩

/-- A free var of a member type is a member of the list's free vars. -/
private theorem Ty.mem_freeVarsList_of_mem {τs : List Ty} {τ : Ty} {w : Nat}
    (hτ : τ ∈ τs) (hw : w ∈ τ.freeVars) : w ∈ Ty.freeVarsList τs := by
  induction τs with
  | nil => simp at hτ
  | cons hd tl ih =>
    simp only [Ty.freeVarsList, List.mem_dedup, List.mem_append]
    rcases List.mem_cons.mp hτ with rfl | hτ'
    · exact .inl hw
    · exact .inr (ih hτ')

/-- The diagonal of `l.zip (l.map g)`: the second component is `g` of the first. -/
private theorem List.mem_zip_self_map' {α β : Type _} {g : α → β} {l : List α} {p : α × β}
    (h : p ∈ l.zip (l.map g)) : p.2 = g p.1 := by
  induction l with
  | nil => simp at h
  | cons hd tl ih =>
    simp only [List.map_cons, List.zip_cons_cons, List.mem_cons] at h
    cases h with
    | inl heq => subst heq; rfl
    | inr h' => exact ih h'

/-- `RecGroup.tyFreeVars` and `flatMap Expr.tyFreeVars` have the same members. -/
private theorem Expr.mem_recGroup_tyFreeVars {bindings : List Expr} {y : Nat} :
    y ∈ Expr.tyFreeVars.RecGroup.tyFreeVars bindings ↔ y ∈ bindings.flatMap Expr.tyFreeVars := by
  induction bindings with
  | nil => simp [Expr.tyFreeVars.RecGroup.tyFreeVars]
  | cons hd tl ih =>
    simp only [Expr.tyFreeVars.RecGroup.tyFreeVars, List.flatMap_cons, List.mem_append, ih]

/-- A substitution whose keys avoid an env's free vars fixes that env. -/
theorem Subst.onEnv_eq_self_of_fresh {S : Subst} {env : Env}
    (h : ∀ p ∈ S, p.1 ∉ env.freeVars) : S.onEnv env = env := by
  show env.map S.onPolyTy = env
  conv_rhs => rw [← List.map_id env]
  apply List.map_congr_left
  intro M hM
  have hbody : S.onTy M.body = M.body :=
    Ty.substFvars_eq_self_of_no_key
      (fun p hp hc => h p hp (Env.mem_freeVars_iff.mpr ⟨M, hM, hc⟩))
  simp only [Subst.onPolyTy, hbody, id_eq]

/-- `genGroupVars` membership: the var occurs in the group's free vars, and is
    neither env-fixed nor rigid. -/
private theorem genGroupVars_spec {rigid : List Nat} {env : Env} {τs : List Ty} {g : Nat}
    (h : g ∈ genGroupVars rigid env τs) :
    g ∈ Ty.freeVarsList τs ∧ g ∉ env.freeVars ∧ g ∉ rigid := by
  simp only [genGroupVars, List.mem_filter, Bool.and_eq_true] at h
  exact ⟨h.1, by simpa using h.2.1, by simpa using h.2.2⟩

/-- Applying the renaming substitution `G ↦ Xs` is `Ty.renameG`. -/
private theorem Subst.onTy_zip_fvar_eq_renameG (G Xs : List Nat) (t : Ty) :
    Subst.onTy (G.zip (Xs.map (Ty.fvar ·))) t = Ty.renameG G Xs t := rfl

/-- Iterated `genGroup`/substitution commutation: a substitution whose domain and
    range both avoid the gen-var pool `G` commutes with `genGroup G`. -/
theorem Subst.onPolyTy_genGroup {G : List Nat} :
    ∀ {S : Subst}, (∀ p ∈ S, p.1 ∉ G) → (∀ p ∈ S, ∀ u ∈ p.2.freeVars, u ∉ G) →
    ∀ {τ : Ty}, Subst.onPolyTy S (PolyTy.genGroup G τ) = PolyTy.genGroup G (Subst.onTy S τ) := by
  intro S
  induction S with
  | nil => intro _ _ τ; simp only [Subst.onPolyTy_nil, Subst.onTy_nil]
  | cons hd S' ih =>
    intro hdom hran
    obtain ⟨Z, U⟩ := hd
    intro τ
    have hZG : Z ∉ G := hdom (Z, U) List.mem_cons_self
    have hUG : ∀ u ∈ U.freeVars, u ∉ G := hran (Z, U) List.mem_cons_self
    have hdom' : ∀ p ∈ S', p.1 ∉ G := fun p hp => hdom p (List.mem_cons_of_mem _ hp)
    have hran' : ∀ p ∈ S', ∀ u ∈ p.2.freeVars, u ∉ G :=
      fun p hp => hran p (List.mem_cons_of_mem _ hp)
    have e0 : Subst.onPolyTy ((Z, U) :: S') (PolyTy.genGroup G τ)
        = Subst.onPolyTy S' (PolyTy.substFvar Z U (PolyTy.genGroup G τ)) := by
      rw [show ((Z, U) :: S') = [(Z, U)] ++ S' from rfl, Subst.onPolyTy_append]; rfl
    have hτeq : Subst.onTy ((Z, U) :: S') τ = Subst.onTy S' (Ty.substFvar Z U τ) := by
      rw [show ((Z, U) :: S') = [(Z, U)] ++ S' from rfl, Subst.onTy_append]; rfl
    rw [e0, PolyTy.genGroup_substFvar hZG hUG, ih hdom' hran', hτeq]

/-- Iterated `substFvars` commutes with `closeOver` when `S` avoids the closed-over
    pool `gs` in domain and range. Plural lift of `Ty.substFvar_closeOver_comm`
    (the `d = 0` companion of Step A's `Ty.substFvars_closeOverFrom`). Used by the
    honest `letIn` soundness case to push `S` through the generalised scheme. -/
theorem Ty.substFvars_closeOver {S : Subst} {gs : List Nat}
    (hS_gs : ∀ p ∈ S, p.1 ∉ gs) (hS_ran : ∀ p ∈ S, ∀ u ∈ p.2.freeVars, u ∉ gs) :
    ∀ {τ : Ty}, Ty.substFvars S (Ty.closeOver gs τ) = Ty.closeOver gs (Ty.substFvars S τ) := by
  induction S with
  | nil => intro τ; rfl
  | cons hd S' ih =>
    obtain ⟨Z, U⟩ := hd
    intro τ
    simp only [Ty.substFvars]
    rw [Ty.substFvar_closeOver_comm (hS_gs (Z, U) List.mem_cons_self)
          (fun g hg hc => hS_ran (Z, U) List.mem_cons_self g hc hg),
        ih (fun p hp => hS_gs p (List.mem_cons_of_mem _ hp))
          (fun p hp => hS_ran p (List.mem_cons_of_mem _ hp))]

/-! ### Domain-locality (avoid form): `Infer.dom_avoid`

The substitution-**domain** twin of `Infer.eOut_avoid`: a var below the input
frontier that avoids the context env and the term's annotation free vars is not
**bound** by the inferred substitution. (`eOut_avoid` only handles the range;
`dom_below` only bounds the domain from above.) The honest soundness `let`/`letRec`
cases need this to show the body substitution leaves the *generalised* variables
untouched. Proof mirrors `eOut_avoid`, using `UnifyRel.dom_mem` (the unifier's
domain lies in the unified types' free vars) where `eOut_avoid` uses
`range_mem`. -/
mutual
theorem Infer.dom_avoid {Φ ctx e Φ' S τ} (h : Infer Φ ctx e Φ' S τ) :
    ∀ {w : Nat}, w < Φ → (∀ M ∈ ctx.env, w ∉ M.body.freeVars) → w ∉ e.tyFreeVars →
    w ∉ S.map Prod.fst := by
  cases h with
  | primLitUnit => intro w _ _ _; simp
  | primLitInt => intro w _ _ _; simp
  | primLitNat => intro w _ _ _; simp
  | primLitChar => intro w _ _ _; simp
  | primBinOpIntAdd => intro w _ _ _; simp
  | primBinOpIntSub => intro w _ _ _; simp
  | primBinOpIntLt _ _ _ _ => intro w _ _ _; simp
  | primBinOpCharLt _ _ _ _ => intro w _ _ _; simp
  | var hlook => intro w _ _ _; simp
  | ctor hlook => intro w _ _ _; simp
  | lambda hseed hbody =>
    intro w hwΦ hctx hwe
    cases hseed with
    | none =>
      simp only [Expr.tyFreeVars, Option.elim_none, List.nil_append] at hwe
      exact Infer.dom_avoid hbody (by omega)
        (by intro M hM; rcases List.mem_cons.mp hM with rfl | hM
            · intro hc; simp only [PolyTy.mkTrivial, Ty.freeVars, List.mem_singleton] at hc; omega
            · exact hctx M hM)
        hwe
    | some T hT =>
      simp only [Expr.tyFreeVars, Option.elim_some, List.mem_append, not_or] at hwe
      exact Infer.dom_avoid hbody hwΦ
        (by intro M hM; rcases List.mem_cons.mp hM with rfl | hM
            · simpa only [PolyTy.mkTrivial] using hwe.1
            · exact hctx M hM)
        hwe.2
  | app hf harg huni =>
    intro w hwΦ hctx hwe
    expose_names
    simp only [Expr.tyFreeVars, List.mem_append, not_or] at hwe
    have hfle := Infer.frontier_le hf
    have hargle := Infer.frontier_le harg
    obtain ⟨hfS, hfτ⟩ := Infer.eOut_avoid hf (w := w) hwΦ hctx hwe.1
    have hfdom := Infer.dom_avoid hf hwΦ hctx hwe.1
    obtain ⟨haS, haτ⟩ := Infer.eOut_avoid harg (w := w) (by omega)
      (Subst.onCtx_avoid hctx hfS) hwe.2
    have hadom := Infer.dom_avoid harg (by omega) (Subst.onCtx_avoid hctx hfS) hwe.2
    intro hc; simp only [List.map_append, List.mem_append] at hc
    rcases hc with (hc | hc) | hc
    · exact hfdom hc
    · exact hadom hc
    · obtain ⟨p, hp, hpw⟩ := List.mem_map.mp hc
      rcases UnifyRel.dom_mem huni p hp with h | h
      · rw [hpw] at h; exact Subst.notMemOnTy haS hfτ h
      · rw [hpw] at h
        simp only [Ty.freeVars, List.mem_dedup, List.mem_append, List.mem_singleton] at h
        rcases h with h | h
        · exact haτ h
        · omega
  | letIn hrhs hbody =>
    intro w hwΦ hctx hwe
    expose_names
    simp only [Expr.tyFreeVars, Option.elim_none, List.nil_append, List.mem_append, not_or] at hwe
    have hrle := Infer.frontier_le hrhs
    obtain ⟨hrS, hrτ⟩ := Infer.eOut_avoid hrhs (w := w) hwΦ hctx hwe.1
    have hrdom := Infer.dom_avoid hrhs hwΦ hctx hwe.1
    have hbdom := Infer.dom_avoid hbody (by omega)
      (by intro M hM; rcases List.mem_cons.mp hM with rfl | hM
          · intro hc; exact hrτ (Ty.freeVars_closeOver_subset hc)
          · exact Subst.onCtx_avoid hctx hrS M hM)
      hwe.2
    intro hc; simp only [List.map_append, List.mem_append] at hc
    rcases hc with hc | hc
    · exact hrdom hc
    · exact hbdom hc
  | letInAnn hσwf hΦN hrhs huni hesc1 hesc2 hbody =>
    intro w hwΦ hctx hwe
    expose_names
    simp only [Expr.tyFreeVars, Option.elim_some, List.mem_append, not_or] at hwe
    have hrle := Infer.frontier_le hrhs
    obtain ⟨hrS, hrτ⟩ := Infer.eOut_avoid hrhs (w := w) (by omega) hctx (by
      intro hc; rcases Expr.tyFreeVars_openTyVars hc with h | h
      · exact hwe.1.2 h
      · have := freshVars_ge w h; omega)
    have hrdom := Infer.dom_avoid hrhs (by omega) hctx (by
      intro hc; rcases Expr.tyFreeVars_openTyVars hc with h | h
      · exact hwe.1.2 h
      · have := freshVars_ge w h; omega)
    have hσopen : w ∉ (σ.openVars (freshVars N σ.paramCount)).freeVars := by
      intro hc; rcases Ty.freeVars_openVars_subset w hc with h | h
      · exact hwe.1.1 h
      · have := freshVars_ge w h; omega
    have hSchk : ∀ p ∈ Schk, w ∉ p.2.freeVars := by
      intro p hp hwp
      rcases UnifyRel.range_mem huni p hp w hwp with h | h
      · exact hrτ h
      · exact hσopen h
    have hSchkdom : w ∉ Schk.map Prod.fst := by
      intro hc; obtain ⟨p, hp, hpw⟩ := List.mem_map.mp hc
      rcases UnifyRel.dom_mem huni p hp with h | h
      · rw [hpw] at h; exact hrτ h
      · rw [hpw] at h; exact hσopen h
    have hbdom := Infer.dom_avoid hbody (by omega)
      (by intro M hM; rcases List.mem_cons.mp hM with rfl | hM
          · exact hwe.1.1
          · exact Subst.onCtx_avoid (Subst.onCtx_avoid hctx hrS) hSchk M hM)
      hwe.2
    intro hc; simp only [List.map_append, List.mem_append] at hc
    rcases hc with (hc | hc) | hc
    · exact hrdom hc
    · exact hSchkdom hc
    · exact hbdom hc
  | match_ hscrut hne hbr =>
    intro w hwΦ hctx hwe
    simp only [Expr.tyFreeVars, List.mem_append, not_or] at hwe
    obtain ⟨hsS, hsτ⟩ := Infer.eOut_avoid hscrut (w := w) hwΦ hctx hwe.1
    have hsdom := Infer.dom_avoid hscrut hwΦ hctx hwe.1
    have hle1 := Infer.frontier_le hscrut
    have hbrdom := InferBranches.dom_avoid hbr (w := w) (by omega)
      (Subst.onCtx_avoid hctx hsS) hsτ
      (by intro hc; simp only [Ty.freeVars, List.mem_singleton] at hc; omega) hwe.2
    intro hc; simp only [List.map_append, List.mem_append] at hc
    rcases hc with hc | hc
    · exact hsdom hc
    · exact hbrdom hc
  | letRec hwf hgroup hceiling hbody =>
    intro w hwΦ hctx hwe
    expose_names
    simp only [Expr.tyFreeVars, List.mem_append] at hwe
    have hwann : w ∉ Expr.tyFreeVars.AnnList.tyFreeVars anns := fun hc => hwe (Or.inl (Or.inl hc))
    have hwbind : w ∉ Expr.tyFreeVars.RecGroup.tyFreeVars bindings := fun hc => hwe (Or.inl (Or.inr hc))
    have hwbody : w ∉ body.tyFreeVars := fun hc => hwe (Or.inr hc)
    have hspecs_init : ∀ s ∈ RecSpec.init Φ anns, w ∉ s.freeVars := by
      intro s hs
      rcases List.mem_iff_getElem.mp hs with ⟨j, hj, rfl⟩
      have hlenj : j < anns.length := by
        have h₂ := RecSpec.init_length Φ anns
        omega
      have hget : (RecSpec.init Φ anns)[j] = RecSpec.mono (.fvar (Φ + j)) := by
        have h₁ := List.getElem?_eq_getElem hj
        rw [RecSpec.init_getElem? Φ anns j, List.getElem?_eq_getElem hlenj] at h₁
        injection h₁ with hEq
        exact hEq.symm
      rw [hget]
      intro hc
      simp only [RecSpec.freeVars, Ty.freeVars, List.mem_singleton] at hc
      omega
    have hctxGroup : ∀ M ∈ ({ ctx with
        env := (RecSpec.init Φ anns).map (RecSpec.rhsEntry [] []) ++ ctx.env } : Ctx).env,
        w ∉ M.body.freeVars := by
      intro M hM
      rcases List.mem_append.mp hM with hM1 | hM2
      · obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hM1
        rw [RecSpec.rhsEntry_nil_body_freeVars]
        exact hspecs_init s hs
      · exact hctx M hM2
    have hS₁ : ∀ p ∈ S₁, w ∉ p.2.freeVars :=
      InferRecGroup.eOut_avoid hgroup (w := w) (by omega)
      hctxGroup (fun s hs => hspecs_init s hs) hwbind
    have hbodyCtx : ∀ M ∈ ({ (S₁.onCtx ctx) with
        env := RecSpecs.ceilingSchemes
                 (genGroupVars (RecGroup.rigidVars anns bindings) (S₁.onCtx ctx).env
                   (RecSpecs.monoTys ((RecSpec.init Φ anns).map (RecSpec.onSubst S₁))))
                 anns
                 ((RecSpec.init Φ anns).map (RecSpec.onSubst S₁))
               ++ (S₁.onCtx ctx).env } : Ctx).env, w ∉ M.body.freeVars := by
      intro M hM
      rcases List.mem_append.mp hM with hM1 | hM2
      · obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hM1
        have hpa : p.1 ∈ anns := (List.of_mem_zip hp).1
        have hps : p.2 ∈ (RecSpec.init Φ anns).map (RecSpec.onSubst S₁) := (List.of_mem_zip hp).2
        cases p with
        | mk a s =>
          cases a with
          | some σ =>
            intro hc
            exact hwann (Expr.scheme_body_mem_annList_tyFreeVars hpa hc)
          | none =>
            intro hc
            have hws : w ∈ s.freeVars := RecSpec.mem_bodyScheme_freeVars hc
            obtain ⟨s0, hs0, rfl⟩ := List.mem_map.mp hps
            rcases List.mem_iff_getElem.mp hs0 with ⟨j, hj, rfl⟩
            have hlenj : j < anns.length := by
              have h₂ := RecSpec.init_length Φ anns
              omega
            have hget : (RecSpec.init Φ anns)[j] = RecSpec.mono (.fvar (Φ + j)) := by
              have h₁ := List.getElem?_eq_getElem hj
              rw [RecSpec.init_getElem? Φ anns j, List.getElem?_eq_getElem hlenj] at h₁
              injection h₁ with hEq
              exact hEq.symm
            rw [hget] at hws
            exact absurd hws (Subst.notMemOnTy hS₁ (by
              intro hc2
              simp only [Ty.freeVars, List.mem_singleton] at hc2
              omega))
      · exact Subst.onCtx_avoid hctx hS₁ M hM2
    have hgrpLe : Φ + bindings.length ≤ Φ₁ := InferRecGroup.frontier_le hgroup
    have hgroupdom : w ∉ S₁.map Prod.fst :=
      InferRecGroup.dom_avoid hgroup (w := w) (by omega) hctxGroup hspecs_init hwbind
    have hbdom : w ∉ S₂.map Prod.fst := Infer.dom_avoid hbody (w := w) (by omega) hbodyCtx hwbody
    intro hc; simp only [List.map_append, List.mem_append] at hc
    rcases hc with hc | hc
    · exact hgroupdom hc
    · exact hbdom hc
termination_by e.size
decreasing_by
  all_goals (try subst_vars; try simp only [Expr.size, Expr.size_openTyVars, Expr.sizeRecGroup]; omega)
theorem InferBranches.dom_avoid {Φ ctx scrutTy ρ brs Φ' S}
    (h : InferBranches Φ ctx scrutTy ρ brs Φ' S) :
    ∀ {w : Nat}, w < Φ → (∀ M ∈ ctx.env, w ∉ M.body.freeVars) → w ∉ scrutTy.freeVars →
    w ∉ ρ.freeVars → w ∉ Expr.tyFreeVars.BranchList.tyFreeVars brs →
    w ∉ S.map Prod.fst := by
  cases h with
  | nil => intro w _ _ _ _ _; simp
  | cons hlook hn huni0 hbody huni hrest =>
    intro w hwΦ hctx hscrut hρ hbrs
    expose_names
    simp only [Expr.tyFreeVars.BranchList.tyFreeVars, List.mem_append, not_or] at hbrs
    have hS₀ : ∀ p ∈ S₀, w ∉ p.2.freeVars := by
      intro p hp hwp
      rcases UnifyRel.range_mem huni0 p hp w hwp with h | h
      · exact hscrut h
      · simp only [Ty.freeVars] at h; rw [mem_TyList_freeVars] at h
        obtain ⟨t, ht, hgt⟩ := h; obtain ⟨x, hx, rfl⟩ := List.mem_map.mp ht
        simp only [Ty.freeVars, List.mem_singleton] at hgt; have := freshVars_ge x hx; omega
    have hS₀dom : w ∉ S₀.map Prod.fst := by
      intro hc; obtain ⟨p, hp, hpw⟩ := List.mem_map.mp hc
      rcases UnifyRel.dom_mem huni0 p hp with h | h
      · rw [hpw] at h; exact hscrut h
      · rw [hpw] at h; simp only [Ty.freeVars] at h; rw [mem_TyList_freeVars] at h
        obtain ⟨t, ht, hgt⟩ := h; obtain ⟨x, hx, rfl⟩ := List.mem_map.mp ht
        simp only [Ty.freeVars, List.mem_singleton] at hgt; have := freshVars_ge x hx; omega
    have hta : ∀ v ∈ (((freshVars Φ ctor.paramCount).map (Ty.fvar ·)).map S₀.onTy), w ∉ v.freeVars := by
      intro v hv hwv; obtain ⟨v0, hv0, rfl⟩ := List.mem_map.mp hv; obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hv0
      rcases Subst.mem_freeVars_onTy hwv with h | ⟨p, hp, hvp⟩
      · simp only [Ty.freeVars, List.mem_singleton] at h; have := freshVars_ge x hx; omega
      · exact hS₀ p hp hvp
    have hle0 := Infer.frontier_le hbody
    obtain ⟨hbS, hbτ⟩ := Infer.eOut_avoid hbody (w := w) (by omega)
      (by intro M hM; rcases List.mem_append.mp hM with hM | hM
          · obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hM; obtain ⟨c, hc, rfl⟩ := List.mem_map.mp ht
            simpa only [PolyTy.mkTrivial] using Ty.not_mem_freeVars_openWith hta ((ctor.closed c hc).not_mem_freeVars w)
          · exact Subst.onCtx_avoid hctx hS₀ M hM)
      hbrs.1
    have hbdom := Infer.dom_avoid hbody (by omega)
      (by intro M hM; rcases List.mem_append.mp hM with hM | hM
          · obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hM; obtain ⟨c, hc, rfl⟩ := List.mem_map.mp ht
            simpa only [PolyTy.mkTrivial] using Ty.not_mem_freeVars_openWith hta ((ctor.closed c hc).not_mem_freeVars w)
          · exact Subst.onCtx_avoid hctx hS₀ M hM)
      hbrs.1
    have hS₂ : ∀ p ∈ S₂, w ∉ p.2.freeVars := by
      intro p hp hwp
      rcases UnifyRel.range_mem huni p hp w hwp with h | h
      · exact hbτ h
      · exact Subst.notMemOnTy hbS (Subst.notMemOnTy hS₀ hρ) h
    have hS₂dom : w ∉ S₂.map Prod.fst := by
      intro hc; obtain ⟨p, hp, hpw⟩ := List.mem_map.mp hc
      rcases UnifyRel.dom_mem huni p hp with h | h
      · rw [hpw] at h; exact hbτ h
      · rw [hpw] at h; exact Subst.notMemOnTy hbS (Subst.notMemOnTy hS₀ hρ) h
    have hrdom := InferBranches.dom_avoid hrest (w := w) (by omega)
      (Subst.onCtx_avoid (Subst.onCtx_avoid (Subst.onCtx_avoid hctx hS₀) hbS) hS₂)
      (Subst.notMemOnTy hS₂ (Subst.notMemOnTy hbS (Subst.notMemOnTy hS₀ hscrut)))
      (Subst.notMemOnTy hS₂ (Subst.notMemOnTy hbS (Subst.notMemOnTy hS₀ hρ)))
      hbrs.2
    intro hc; simp only [List.map_append, List.mem_append] at hc
    rcases hc with ((hc | hc) | hc) | hc
    · exact hS₀dom hc
    · exact hbdom hc
    · exact hS₂dom hc
    · exact hrdom hc
  | consWild hbody huni hrest =>
    intro w hwΦ hctx hscrut hρ hbrs
    expose_names
    simp only [Expr.tyFreeVars.BranchList.tyFreeVars, List.mem_append, not_or] at hbrs
    have hle1 := Infer.frontier_le hbody
    obtain ⟨hbS, hbτ⟩ := Infer.eOut_avoid hbody (w := w) hwΦ hctx hbrs.1
    have hbdom := Infer.dom_avoid hbody hwΦ hctx hbrs.1
    have hS₂ : ∀ p ∈ S₂, w ∉ p.2.freeVars := by
      intro p hp hwp
      rcases UnifyRel.range_mem huni p hp w hwp with h | h
      · exact hbτ h
      · exact Subst.notMemOnTy hbS hρ h
    have hS₂dom : w ∉ S₂.map Prod.fst := by
      intro hc; obtain ⟨p, hp, hpw⟩ := List.mem_map.mp hc
      rcases UnifyRel.dom_mem huni p hp with h | h
      · rw [hpw] at h; exact hbτ h
      · rw [hpw] at h; exact Subst.notMemOnTy hbS hρ h
    have hrdom := InferBranches.dom_avoid hrest (w := w) (by omega)
      (Subst.onCtx_avoid (Subst.onCtx_avoid hctx hbS) hS₂)
      (Subst.notMemOnTy hS₂ (Subst.notMemOnTy hbS hscrut))
      (Subst.notMemOnTy hS₂ (Subst.notMemOnTy hbS hρ))
      hbrs.2
    intro hc; simp only [List.map_append, List.mem_append] at hc
    rcases hc with (hc | hc) | hc
    · exact hbdom hc
    · exact hS₂dom hc
    · exact hrdom hc
termination_by Expr.sizeBranches brs
decreasing_by
  all_goals (try subst_vars; try simp only [Expr.sizeBranches]; omega)
/-- Fused `InferRecGroup` domain-avoidance: a var below the input frontier that
    avoids the context, the specs and the bindings' annotation vars is not bound
    by the group substitution (mono unifiers touch only spec monotypes and binding
    types; poly skolem-checks touch only the opened scheme and binding types). -/
theorem InferRecGroup.dom_avoid {Φ ctx bindings specs Φ' S}
    (h : InferRecGroup Φ ctx bindings specs Φ' S) :
    ∀ {w : Nat}, w < Φ → (∀ M ∈ ctx.env, w ∉ M.body.freeVars) →
    (∀ s ∈ specs, w ∉ s.freeVars) → w ∉ Expr.tyFreeVars.RecGroup.tyFreeVars bindings →
    w ∉ S.map Prod.fst := by
  cases h with
  | nil => intro w _ _ _ _; simp
  | consMono he huni hrest =>
    intro w hwΦ hctx hspecs hbinds
    expose_names
    simp only [Expr.tyFreeVars.RecGroup.tyFreeVars, List.mem_append, not_or] at hbinds
    have hle1 := Infer.frontier_le he
    obtain ⟨heS, heτ⟩ := Infer.eOut_avoid he (w := w) hwΦ hctx hbinds.1
    have hτA : w ∉ τ.freeVars := hspecs (.mono τ) List.mem_cons_self
    have hS₂ : ∀ p ∈ S₂, w ∉ p.2.freeVars := by
      intro p hp hwp
      rcases UnifyRel.range_mem huni p hp w hwp with h | h
      · exact heτ h
      · exact Subst.notMemOnTy heS hτA h
    have hS₂dom : w ∉ S₂.map Prod.fst := by
      intro hc; obtain ⟨p, hp, hpw⟩ := List.mem_map.mp hc
      rcases UnifyRel.dom_mem huni p hp with h | h
      · rw [hpw] at h; exact heτ h
      · rw [hpw] at h; exact Subst.notMemOnTy heS hτA h
    have hd1 : w ∉ S₁.map Prod.fst := Infer.dom_avoid he hwΦ hctx hbinds.1
    have hd3 : w ∉ S₃.map Prod.fst := InferRecGroup.dom_avoid hrest (w := w) (by omega)
      (Subst.onCtx_avoid (Subst.onCtx_avoid hctx heS) hS₂)
      (by intro s' hs'
          obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hs'
          exact RecSpec.notMem_freeVars_onSubst
            (fun p hp => (List.mem_append.mp hp).elim (heS p) (hS₂ p))
            (hspecs s (List.mem_cons_of_mem _ hs)))
      hbinds.2
    intro hc; simp only [List.map_append, List.mem_append] at hc
    rcases hc with (hc | hc) | hc
    · exact hd1 hc
    · exact hS₂dom hc
    · exact hd3 hc
  | consPoly hΦN hinfer huni hesc1 hesc2 hrest =>
    intro w hwΦ hctx hspecs hbinds
    expose_names
    simp only [Expr.tyFreeVars.RecGroup.tyFreeVars, List.mem_append, not_or] at hbinds
    have hσbody : w ∉ σ.body.freeVars := hspecs (.poly σ) List.mem_cons_self
    have hle1 := Infer.frontier_le hinfer
    have hwopen : w ∉ (e.openTyVars (freshVars N σ.paramCount)).tyFreeVars := by
      intro hc
      rcases Expr.tyFreeVars_openTyVars hc with h | h
      · exact hbinds.1 h
      · have := freshVars_ge w h; omega
    obtain ⟨heS, heτ⟩ := Infer.eOut_avoid hinfer (w := w) (by omega) hctx hwopen
    have hσopen : w ∉ (σ.openVars (freshVars N σ.paramCount)).freeVars := by
      intro hc
      rcases Ty.freeVars_openVars_subset w hc with h | h
      · exact hσbody h
      · have := freshVars_ge w h; omega
    have hSchk : ∀ p ∈ Schk, w ∉ p.2.freeVars := by
      intro p hp hwp
      rcases UnifyRel.range_mem huni p hp w hwp with h | h
      · exact heτ h
      · exact hσopen h
    have hSchkdom : w ∉ Schk.map Prod.fst := by
      intro hc; obtain ⟨p, hp, hpw⟩ := List.mem_map.mp hc
      rcases UnifyRel.dom_mem huni p hp with h | h
      · rw [hpw] at h; exact heτ h
      · rw [hpw] at h; exact hσopen h
    have hd1 : w ∉ S₁.map Prod.fst := Infer.dom_avoid hinfer (w := w) (by omega) hctx hwopen
    have hd3 : w ∉ S₂.map Prod.fst := InferRecGroup.dom_avoid hrest (w := w) (by omega)
      (Subst.onCtx_avoid (Subst.onCtx_avoid hctx heS) hSchk)
      (by intro s' hs'
          obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hs'
          exact RecSpec.notMem_freeVars_onSubst
            (fun p hp => (List.mem_append.mp hp).elim (heS p) (hSchk p))
            (hspecs s (List.mem_cons_of_mem _ hs)))
      hbinds.2
    intro hc; simp only [List.map_append, List.mem_append] at hc
    rcases hc with (hc | hc) | hc
    · exact hd1 hc
    · exact hSchkdom hc
    · exact hd3 hc
  termination_by Expr.sizeRecGroup bindings
  decreasing_by
    all_goals (try subst_vars; try simp only [Expr.sizeRecGroup, Expr.size_openTyVars]; omega)
end

/-- **Survival under substitution.** A free var not in `S`'s domain survives
    applying `S` (its occurrences are untouched). Used by the honest `letIn` case
    to show the generalised vars `genV` (which are not env-fixed) are `≥ Φ`. -/
theorem Ty.mem_freeVars_onTy_of_not_dom {S : Subst} {τ : Ty} {g : Nat}
    (hg : g ∈ τ.freeVars) (hdom : ∀ p ∈ S, p.1 ≠ g) : g ∈ (S.onTy τ).freeVars := by
  rw [Subst.onTy, Ty.mem_freeVars_substFvars_image]
  refine ⟨g, hg, ?_⟩
  rw [Ty.substFvars_eq_self_of_no_key (fun p hp hc => by
    simp only [Ty.freeVars, List.mem_singleton] at hc; exact hdom p hp hc)]
  simp [Ty.freeVars]

/-- Env-containment of a type's free vars transports along a substitution: each
    free var of `T.onTy τ` is contributed through some `u ∈ τ.freeVars`, and the
    same `u`-image appears in the substituted env entry that contained `u`. -/
theorem Ty.freeVars_onTy_mem_onEnv {T : Subst} {env : Env} {τ : Ty}
    (hτ : ∀ u ∈ τ.freeVars, u ∈ env.freeVars) :
    ∀ y ∈ (T.onTy τ).freeVars, y ∈ (T.onEnv env).freeVars := by
  intro y hy
  rw [Subst.onTy, Ty.mem_freeVars_substFvars_image] at hy
  obtain ⟨u, hu, hyu⟩ := hy
  obtain ⟨M, hM, huM⟩ := Env.mem_freeVars_iff.mp (hτ u hu)
  refine Env.mem_freeVars_iff.mpr ⟨T.onPolyTy M, List.mem_map.mpr ⟨M, hM, rfl⟩, ?_⟩
  show y ∈ (Ty.substFvars T M.body).freeVars
  rw [Ty.mem_freeVars_substFvars_image]
  exact ⟨u, huM, hyu⟩

/-- Env-containment of a spec's free vars transports along `onSubst` (monotypes by
    `freeVars_onTy_mem_onEnv`; rigid schemes survive because the substitution's
    domain avoids their bodies). -/
theorem RecSpec.freeVars_onSubst_mem_onEnv {T : Subst} {env : Env} {s : RecSpec}
    (hs : ∀ y ∈ s.freeVars, y ∈ env.freeVars)
    (hpoly_dom : ∀ σ, s = RecSpec.poly σ → ∀ p ∈ T, p.1 ∉ σ.body.freeVars) :
    ∀ y ∈ (RecSpec.onSubst T s).freeVars, y ∈ (T.onEnv env).freeVars := by
  cases s with
  | mono τ =>
    intro y hy
    exact Ty.freeVars_onTy_mem_onEnv hs y hy
  | poly σ =>
    intro y hy
    obtain ⟨M, hM, hyM⟩ := Env.mem_freeVars_iff.mp (hs y hy)
    refine Env.mem_freeVars_iff.mpr ⟨T.onPolyTy M, List.mem_map.mpr ⟨M, hM, rfl⟩, ?_⟩
    exact Ty.mem_freeVars_onTy_of_not_dom hyM
      (fun p hp hpeq => hpoly_dom σ rfl p hp (by rw [hpeq]; exact hy))

/-! ### Path R residual soundness (`Infer.sound_elab` family) — DELETED

`Infer.sound_elab` / `InferBranches.sound_elab` / `InferRecGroup.sound_elab`
concluded on the removed elaborated outputs (`TypeOfElabHM … (eOut.substTyFvars S)…`,
`… brsOut …`, `… bindingsOut …`). With the `eOut` index gone they are unstateable;
the surviving coherence theorem is `Infer.sound` (erased-input `TypeOfHM`, below).
The dedicated erased-`letRec`-soundness lemmas in this block are likewise deleted. -/
/-! DELETED: `Infer.sound_closed` (conclusion referenced the removed elaborated
    output `eOut`; it was a thin wrapper over the deleted `Infer.sound_elab`). -/


/-! ## Algorithmic phase, step 2b: completeness (principality) scaffolding

Foundations for `Infer.complete`, independent of how the residual-substitution
obstruction is resolved. -/

/-! ### Completeness foundations: substitution agreement

`Infer` covers the full language, so principality is stated for all
expressions. The agreement lemmas let us swap one substitution for another that
agrees on the in-scope (`< Φ`) variables. -/

/-- Two substitutions agreeing on all vars `< Φ` act identically on a
    below-`Φ` type. -/
theorem Subst.onTy_congr {Φ : Nat} {S T : Subst}
    (hag : ∀ v, v < Φ → S.onTy (.fvar v) = T.onTy (.fvar v)) :
    ∀ {τ : Ty}, Ty.BelowFvars Φ τ → S.onTy τ = T.onTy τ := by
  intro τ hτ
  induction τ using Ty.rec_strong with
  | prim p => simp only [Subst.onTy_prim]
  | bvar i => simp only [Subst.onTy_bvar]
  | fvar n => cases hτ with | fvar hlt => exact hag n hlt
  | arrow a b iha ihb => cases hτ with | arrow ha hb => simp only [Subst.onTy_arrow, iha ha, ihb hb]
  | customTy nm tys ih =>
    cases hτ with
    | customTy hall =>
      simp only [Subst.onTy_customTy]
      apply congrArg (Ty.customTy nm)
      apply List.map_congr_left
      intro t ht
      exact ih t ht (hall t ht)
  | bl lo hi e ih =>
    cases hτ with
    | bl he => simp only [Subst.onTy_bl, ih he]

/-- Agreeing substitutions act identically on a below-`Φ` context. -/
theorem Subst.onCtx_congr {Φ : Nat} {S T : Subst} {ctx : Ctx}
    (hag : ∀ v, v < Φ → S.onTy (.fvar v) = T.onTy (.fvar v)) (hb : CtxBelow Φ ctx) :
    S.onCtx ctx = T.onCtx ctx := by
  simp only [Subst.onCtx, Subst.onEnv]
  congr 1
  apply List.map_congr_left
  intro M hM
  simp only [Subst.onPolyTy, Subst.onTy_congr hag (hb M hM)]

/-- Erase-level analogue of `Subst.onTy_congr`: if two substitutions agree up to
    erasure on every fvar below `Φ`, and `τ` has all free vars below `Φ`, then
    `S.onTy τ` and `T.onTy τ` agree up to erasure. -/
theorem Subst.onTy_congr_hm {Φ : Nat} {S T : Subst}
    (hag : ∀ v, v < Φ → AgreesHM (S.onTy (.fvar v)) (T.onTy (.fvar v))) :
    ∀ {τ : Ty}, Ty.BelowFvars Φ τ → AgreesHM (S.onTy τ) (T.onTy τ) := by
  intro τ hτ
  induction τ using Ty.rec_strong with
  | prim p => simp [AgreesHM]
  | bvar i => simp [AgreesHM]
  | fvar n => cases hτ with | fvar hlt => exact hag n hlt
  | arrow a b iha ihb =>
    cases hτ with
    | arrow ha hb =>
      simp only [AgreesHM, Subst.onTy_arrow, Ty.eraseBounds_arrow]
      rw [Ty.arrow.injEq]
      exact ⟨iha ha, ihb hb⟩
  | customTy nm tys ih =>
    cases hτ with
    | customTy hall =>
      simp only [AgreesHM, Subst.onTy_customTy, Ty.eraseBounds_customTy,
        TyList.eraseBounds_eq_map]
      apply congrArg (Ty.customTy nm)
      rw [List.map_map, List.map_map]
      apply List.map_congr_left
      intro t ht
      exact ih t ht (hall t ht)
  | bl lo hi e ih =>
    cases hτ with
    | bl he =>
      simp only [AgreesHM, Subst.onTy_bl, Ty.eraseBounds_bl]
      apply congrArg bareListTy
      exact ih he

/-- `S` and `T` agree below frontier `Φ` **up to erasure** (`AgreesHM` on every
    `fvar` below `Φ`). This is the "`S₀ = R ∘ S` below `Φ`" agreement clause
    threaded through the principality proofs; a reducible abbreviation so it is
    defeq to the raw `∀`.

    REPAIRED 2026-08-12. This used to demand *structural* equality
    `S.onTy (.fvar v) = T.onTy (.fvar v)`, which is **FALSE** under Path R for any
    case that unifies. Counterexample: `(λ (x : BL 3 5 Int). x) y` with `y : .fvar v`
    and `v < Φ`. `Infer` unifies `.fvar v` against the verbatim-copied annotation
    and binds `v ↦ BL 3 5 Int`, while the declarative side sees only the *erased*
    annotation and needs `S₀.onTy (.fvar v) = List Int`. A `bl` head survives every
    substitution (`Subst.onTy_bl`), so the two agree up to erasure and NOT exactly.
    Equivalently: recovering exact agreement through a unification step IS
    structural factoring, and `FactorsHM.to_structural` / structural `greatest_K`
    were deleted as false in `054e0d8`.

    Erase-level agreement is *exactly enough*: every declarative premise in the
    completeness statements sits at `(…).eraseBounds`, and contexts that agree up to
    erasure have EQUAL erasures — so the induction can still re-enter the IH at the
    new residual. See design memo §4.1.2.

    Used only by the completeness track (and `trans_append` below); the soundness
    layer does not mention it, so weakening it here is contained. -/
abbrev Subst.AgreesBelow (Φ : Nat) (S T : Subst) : Prop :=
  ∀ v, v < Φ → AgreesHM (S.onTy (.fvar v)) (T.onTy (.fvar v))

/-- The recurring agreement-threading step: if `S₀` agrees with `S₁ ++ R₁` below
    `Φ`, and the residual `R₁` agrees with `S₂ ++ R₂` below the larger frontier
    `Φ₁` (which bounds `S₁`'s replacements), then `S₀` agrees with the composed
    `(S₁ ++ S₂) ++ R₂` below `Φ`. Collapses the `calc` repeated verbatim across the
    `pair`/`app`/`match` completeness cases. -/
theorem Subst.AgreesBelow.trans_append {Φ Φ₁ : Nat} {S₀ S₁ R₁ S₂ R₂ : Subst}
    (hle : Φ ≤ Φ₁)
    (hag1 : Subst.AgreesBelow Φ S₀ (S₁ ++ R₁))
    (hbelowS₁ : ∀ p ∈ S₁, Ty.BelowFvars Φ₁ p.2)
    (hag2 : Subst.AgreesBelow Φ₁ R₁ (S₂ ++ R₂)) :
    Subst.AgreesBelow Φ S₀ ((S₁ ++ S₂) ++ R₂) := by
  intro v hv
  have hbv : Ty.BelowFvars Φ₁ (S₁.onTy (.fvar v)) :=
    Subst.onTy_belowFvars hbelowS₁ (.fvar (by omega))
  apply AgreesHM.trans (hag1 v hv)
  rw [List.append_assoc]
  simp only [Subst.onTy_append]
  apply AgreesHM.trans
  · exact Subst.onTy_congr_hm hag2 hbv
  · simp [AgreesHM, Subst.onTy_append]

/-- Erase-level twin of `Subst.onCtx_congr`, and **the** move that makes the
    Path R completeness statements *sufficient* rather than merely true:
    substitutions that differ structurally but agree only up to erasure below `Φ`
    produce EQUAL erased contexts, so an IH stated at `(…).eraseBounds` can be
    re-entered at a new residual (design memo §4.1.2).

    Was inlined verbatim in `Infer.complete_app_aux` (`hctxBridge`) and
    `Infer.complete_letIn_aux` before being named here; the branch/match tier
    needs it once per branch, where inlining it three times would not pay. -/
theorem Subst.onCtx_congr_hm {Φ : Nat} {S T : Subst} {ctx : Ctx}
    (hag : Subst.AgreesBelow Φ S T) (hb : CtxBelow Φ ctx) :
    (S.onCtx ctx).eraseBounds = (T.onCtx ctx).eraseBounds := by
  simp only [Ctx.eraseBounds, Subst.onCtx, Subst.onEnv, Env.eraseBounds, List.map_map]
  congr 1
  apply List.map_congr_left
  intro M hM
  cases M with
  | mk n b =>
    have hbody : Ty.eraseBounds (S.onTy b) = Ty.eraseBounds (T.onTy b) :=
      Subst.onTy_congr_hm hag (hb ⟨n, b⟩ hM)
    simp [Subst.onPolyTy, PolyTy.eraseBounds, hbody]


/-! ### Principality (completeness) — per-expression statement + case lemmas

`Infer.CompleteAt e` packages the principality property at a single expression,
abstracted over the frontier `Φ`, context `ctx`, input specialization `S₀`, and
declarative type `τ₀`. Each syntactic form gets its own case lemma (taking the
sub-expressions' `CompleteAt` as hypotheses, exactly the shape produced by
inducting on `e` with `Expr.rec_strong`); `Infer.completeAt`/`Infer.complete`
then just compose them. Keeping the universally-quantified `Φ ctx S₀ τ₀` inside
the predicate means each case lemma is independently stated and verifiable. -/

/-! ### `TypeOfHM` metatheory (direct induction port from `TypeOfElabHM`)

The forward "sandwich" bridge is dead (elaboration changes term structure for
polymorphic `let`, so no same-skeleton `TypeOfElabHM` typing exists — `toElab` is
false). Instead we port the standard HM metatheory directly. Mirrors the
`TypeOfElabHM` proofs; the `var` case is *simpler* (existential instantiation
witness, no `length = paramCount` premise). -/

/-- Branch disjunction motive for `TypeOfHM.rec_strong` (mirrors
    `TypeOfElabHM.BranchMotive`). -/
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

/-- Strong induction principle for `TypeOfHM` (mirrors `TypeOfElabHM.rec_strong`),
    packaged with a single motive so the metatheory never touches the mutual
    recursor / `motive_2` directly. -/
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
    (letRec : ∀ {ctx bodyCtx : Ctx} {anns : List (Option PolyTy)} {bindings : List Expr}
      {specs : List RecSpec} {τs : List Ty} {G L : List Nat} {body : Expr} {ρ : Ty}
      (hwf : RecSpecs.WF anns bindings specs G)
      (hlen : bindings.length = τs.length)
      (hlink : ∀ p ∈ specs.zip τs, ∀ τ, p.1 = .mono τ → p.2 = τ)
      (hlc : ∀ t ∈ τs, t.IsLC)
      (hmono : RecSpecs.MonoTypedInit TypeOfHM ctx bindings τs G L)
      (heq : bodyCtx = RecSpecs.bodyCtx ctx specs G)
      (hbody : TypeOfHM bodyCtx body ρ),
      (∀ Xs (hf : FreshNames L G.length Xs)
          p (hp : p ∈ bindings.zip τs),
        motive (RecSpecs.rhsCtx ctx (τs.map RecSpec.mono) G Xs)
          p.1 (Ty.renameG G Xs p.2) (hmono Xs hf p hp)) →
      motive bodyCtx body ρ hbody →
      motive ctx (.letRec anns bindings body) ρ (.letRec hwf hlen hlink hlc hmono heq hbody))
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
  | letRec hwf hlen hlink hlc hmono heq hbody ihmono ihbody =>
      exact letRec hwf hlen hlink hlc hmono heq hbody ihmono ihbody
  | mk hspec heq hbodyT ih =>
      subst heq
      exact Or.inl ⟨_, _, _, _, _, rfl, hspec.lookup, hspec.scrut_eq, hspec.arity,
        hspec.bind_count, hspec.fields, hbodyT, ih⟩
  | wildcard hbodyT ih =>
      exact Or.inr ⟨rfl, hbodyT, ih⟩

/-! Local copies of Core-private auxiliary lemmas (needed by the `letRec`/`letRecAnn`
    cases of `typ_subst_preservation_uniform`; cf. the `SpikeLetRecAnn` precedent of
    copying Core-private helpers into the consuming file). -/

private theorem Ty.freeVars_subset_freeVarsList {V : Ty} {Vs : List Ty}
    (h : V ∈ Vs) : ∀ x ∈ V.freeVars, x ∈ Ty.freeVarsList Vs := by
  induction Vs with
  | nil => exact absurd h List.not_mem_nil
  | cons hd tl ih =>
    intro x hx
    simp only [Ty.freeVarsList, List.mem_dedup, List.mem_append]
    cases h with
    | head _ => exact .inl hx
    | tail _ h' => exact .inr (ih h' x hx)

private theorem Ty.IsLC.substFvars {s : List (Nat × Ty)} {τ : Ty}
    (hs : ∀ p ∈ s, p.2.IsLC) (hτ : τ.IsLC) : (Ty.substFvars s τ).IsLC := by
  induction s generalizing τ with
  | nil => exact hτ
  | cons hd tl ih =>
    obtain ⟨Z, U⟩ := hd
    simp only [Ty.substFvars]
    exact ih (fun p hp => hs p (List.mem_cons_of_mem _ hp))
      (Ty.IsLC.substFvar (hs (Z, U) List.mem_cons_self) hτ)

private theorem Ty.renameG_isLC {G Xs : List Nat} {τ : Ty}
    (hτ : τ.IsLC) : (Ty.renameG G Xs τ).IsLC := by
  unfold Ty.renameG
  refine Ty.IsLC.substFvars ?_ hτ
  intro p hp
  obtain ⟨x, _, hx⟩ := List.mem_map.mp (List.of_mem_zip hp).2
  rw [← hx]; exact .fvar

private theorem List.mem_zip_map {α β γ δ : Type _} {f : α → γ} {g : β → δ} :
    ∀ {l : List α} {r : List β} {p : γ × δ},
      p ∈ (l.map f).zip (r.map g) → ∃ a b, (a, b) ∈ l.zip r ∧ p = (f a, g b) := by
  intro l
  induction l with
  | nil => intro r p h; simp at h
  | cons hd tl ih =>
    intro r p h
    cases r with
    | nil => simp at h
    | cons rhd rtl =>
      simp only [List.map_cons, List.zip_cons_cons, List.mem_cons] at h
      cases h with
      | inl heq => exact ⟨hd, rhd, List.mem_cons_self, heq⟩
      | inr h' =>
        obtain ⟨a, b, hmem, heq⟩ := ih h'
        exact ⟨a, b, List.mem_cons_of_mem _ hmem, heq⟩

private theorem List.mem_zip_map_right {α β γ : Type _} {g : β → γ}
    {l : List α} {r : List β} {a : α} {b : β}
    (h : (a, b) ∈ l.zip r) : (a, g b) ∈ l.zip (r.map g) := by
  induction l generalizing r with
  | nil => simp at h
  | cons hd tl ih =>
    cases r with
    | nil => simp at h
    | cons rhd rtl =>
      simp only [List.map_cons, List.zip_cons_cons, List.mem_cons] at h ⊢
      cases h with
      | inl heq =>
        rw [Prod.mk.injEq] at heq
        obtain ⟨rfl, rfl⟩ := heq
        exact Or.inl rfl
      | inr h' => exact Or.inr (ih h')

/-- Single-fvar `substTyFvar` is the one-element iterated `substTyFvars` (defeq).
    Lets the `match_`/`letRec`/`letRecAnn` cases use the *public*
    `Expr.substTyFvars_*` structural lemmas instead of the Core-private single-fvar
    list helpers. -/
private theorem Expr.substTyFvar_eq_substTyFvars_single {Z : Nat} {U : Ty} {e : Expr} :
    Expr.substTyFvar Z U e = Expr.substTyFvars [(Z, U)] e := rfl

/-- **Single-fvar substitution preservation for `TypeOfHM`** (uniform over the whole
    env). Direct induction port of `TypeOfElabHM.typ_subst_preservation_uniform`; the
    `var`/`ctor` cases are simpler (existential instantiation witness, no length
    premise). All auxiliary lemmas (`Ty.renameG_*`, `PolyTy.genGroup_*`,
    `InstantiatesBy.substFvar`, …) are relation-agnostic and reused verbatim.
    The `match_`/`letRec`/`letRecAnn` cases bridge the Core-private single-fvar
    list helpers via `Expr.substTyFvar Z U e ≡ Expr.substTyFvars [(Z, U)] e` (defeq)
    + the public `Expr.substTyFvars_match/_letRec/_letRecAnn`. -/
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
  | letRec hwf hlen hlink hlc hmono heq hbody ihmono ihbody =>
    -- Fused-node port of Core's `TypeOfElabHM.typ_subst_preservation_uniform`
    -- `letRec` case: pool freshening `G ↦ W`, monotypes transported by
    -- `renameG_substFvar_comm`/`renameG_renameG`/`genGroup_renameG`, schemes
    -- substituted pointwise, the env transport split pointwise by `RecSpec`.
    -- (The old `PolyTyped` transport is GONE: the pivot rule types every member
    -- monomorphically at the witnesses `τs`, transported in ONE uniform branch.)
    subst heq
    expose_names
    rw [Expr.substTyFvar_eq_substTyFvars_single, Expr.substTyFvars_letRec]
    obtain ⟨W, hWlen0, hWnodup, hWavoid⟩ :=
      exists_fresh_names (G ++ [Z] ++ U.freeVars ++ specs.flatMap RecSpec.monoFreeVars
        ++ τs.flatMap Ty.freeVars) G.length
    have hWG : ∀ w ∈ W, w ∉ G := fun w hw hc =>
      hWavoid w hw (by simp [List.mem_append, hc])
    have hGW : ∀ g ∈ G, g ∉ W := fun g hg hc => hWG g hc hg
    have hZW : Z ∉ W := fun hc =>
      hWavoid Z hc (by simp [List.mem_append, List.mem_singleton])
    have hUW : ∀ u ∈ U.freeVars, u ∉ W := fun u hu hc =>
      hWavoid u hc (by simp [List.mem_append, hu])
    have hWfree : ∀ τ, RecSpec.mono τ ∈ specs → ∀ w ∈ W, w ∉ τ.freeVars :=
      fun τ hτ w hw hc =>
        have hmem : w ∈ specs.flatMap RecSpec.monoFreeVars :=
          List.mem_flatMap.mpr ⟨.mono τ, hτ, hc⟩
        hWavoid w hw (by simp [List.mem_append, hmem])
    have hWfree_τs : ∀ t, t ∈ τs → ∀ w ∈ W, w ∉ t.freeVars :=
      fun t ht w hw hc =>
        have hmem : w ∈ τs.flatMap Ty.freeVars :=
          List.mem_flatMap.mpr ⟨t, ht, hc⟩
        hWavoid w hw (by simp [List.mem_append, hmem])
    let τs' : List Ty := τs.map (fun t => Ty.substFvar Z U (Ty.renameG G W t))
    refine TypeOfHM.letRec
      (specs := specs.map (RecSpec.substFreshened Z U G W))
      (τs := τs') (G := W) (L := Z :: (G ++ W ++ L))
      ⟨?_, ?_, hWnodup, ?_, ?_⟩ ?_ ?_ ?_ ?_ rfl ?_
    · rw [List.map_map, ← hwf.anns_eq, List.map_map]
      apply List.map_congr_left
      intro s _
      cases s <;> rfl
    · simp only [List.length_map]; exact hwf.length
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
    · -- the witness list transports pointwise (same length)
      simpa [τs', List.length_map] using hlen
    · -- mono-link: structurally true (both lists transport pointwise)
      intro p hp τ hτ
      obtain ⟨a, b, hab, rfl⟩ := List.mem_zip_map (l := specs) (r := τs)
        (f := RecSpec.substFreshened Z U G W)
        (g := fun t => Ty.substFvar Z U (Ty.renameG G W t))
        (by simpa [τs'] using hp)
      cases a with
      | poly σ => exact RecSpec.noConfusion hτ
      | mono τ₀ =>
        injection hτ with hττ
        have hb : b = τ₀ := hlink (RecSpec.mono τ₀, b) hab τ₀ rfl
        simpa [hb] using hττ
    · -- witnesses stay LC under substitution
      intro t' ht'
      obtain ⟨t, ht, rfl⟩ := List.mem_map.mp ht'
      exact Ty.IsLC.substFvar h_U_lc (Ty.renameG_isLC (hlc t ht))
    · -- ALL members (mono + annotated alike): the pivot monomorphic transport
      intro Xs hfresh p hp
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
      have key : ∀ t, t ∈ τs →
          Ty.renameG W Xs (Ty.substFvar Z U (Ty.renameG G W t))
            = Ty.substFvar Z U (Ty.renameG G Xs t) := by
        intro t ht
        rw [Ty.renameG_substFvar_comm h_U_lc hZW hUW hZXs
              (Ty.renameG_isLC (hlc t ht)) hWnodup hfresh.length hWXs,
            Ty.renameG_renameG (hlc t ht) hwf.nodup hWnodup hWlen0 hXlen hGW
              (hWfree_τs t ht) hWXs hGXs]
      have henv_rhs : (τs'.map RecSpec.mono).map (RecSpec.rhsEntry W Xs)
          = Env.substFvar Z U ((τs.map RecSpec.mono).map (RecSpec.rhsEntry G Xs)) := by
        dsimp [τs']
        simp only [List.map_map, Function.comp_def, RecSpec.rhsEntry, PolyTy.mkTrivial,
          Ty.renameG_nil_pool, Env.substFvar]
        apply List.map_congr_left
        intro t ht
        rw [key t ht]
        rfl
      obtain ⟨a, t, hab, rfl⟩ := List.mem_zip_map (l := bindings) (r := τs)
        (f := fun x => Expr.substTyFvars [(Z, U)] x)
        (g := fun t => Ty.substFvar Z U (Ty.renameG G W t))
        (by simpa [τs'] using hp)
      have hIH := ihmono Xs hXsL (a, t) hab
      simp only [RecSpecs.rhsCtx] at hIH
      rw [Env.substFvar_append, ← henv_rhs] at hIH
      rw [key t (List.of_mem_zip hab).2]
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

/-- **Substitution preservation for `TypeOfHM`** (whole substitution). Direct
    induction port (via `onSubstFvar` + `induction S`), mirroring
    `TypeOfElabHM.onSubst`. No `CtxWF` needed. -/
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

/-- Path R: source TypeOfHM residual projection (erase ctx, term, result). -/
theorem TypeOfHM.eraseBounds_of {ctx : Ctx} {e : Expr} {τ : Ty}
    (h : TypeOfHM ctx e τ) :
    TypeOfHM ctx.eraseBounds e.eraseBounds (Ty.eraseBounds τ) := by
  induction h using TypeOfHM.rec_strong with
  | primLitUnit =>
    simp only [Expr.eraseBounds, Ty.eraseBounds_prim]; exact .primLitUnit
  | primLitInt =>
    simp only [Expr.eraseBounds, Ty.eraseBounds_prim]; exact .primLitInt
  | primLitNat =>
    simp only [Expr.eraseBounds, Ty.eraseBounds_prim]; exact .primLitNat
  | primLitChar =>
    simp only [Expr.eraseBounds, Ty.eraseBounds_prim]; exact .primLitChar
  | primBinOpIntAdd =>
    simp only [Expr.eraseBounds, Ty.eraseBounds_arrow, Ty.eraseBounds_prim]
    exact .primBinOpIntAdd
  | primBinOpIntSub =>
    simp only [Expr.eraseBounds, Ty.eraseBounds_arrow, Ty.eraseBounds_prim]
    exact .primBinOpIntSub
  | primBinOpIntLt _ _ ihtrue ihfalse =>
    simp only [Expr.eraseBounds, Ty.eraseBounds_arrow, Ty.eraseBounds_prim,
      Ty.eraseBounds_customTy, TyList.eraseBounds_nil] at ihtrue ihfalse ⊢
    exact .primBinOpIntLt ihtrue ihfalse
  | primBinOpCharLt _ _ ihtrue ihfalse =>
    simp only [Expr.eraseBounds, Ty.eraseBounds_arrow, Ty.eraseBounds_prim,
      Ty.eraseBounds_customTy, TyList.eraseBounds_nil] at ihtrue ihfalse ⊢
    exact .primBinOpCharLt ihtrue ihfalse
  | app _ _ ihf ihinput =>
    simp only [Expr.eraseBounds, Ty.eraseBounds_arrow] at ihf ⊢
    exact .app ihf ihinput
  | @lambda paramTy ann bodyCtx ctx body bodyTy hpc hann heq hbody ihbody =>
    subst heq
    simp only [Expr.eraseBounds, Ty.eraseBounds_arrow]
    refine TypeOfHM.lambda (Ty.IsLC.eraseBounds hpc)
      (Option.Pins.map_eraseBounds hann) rfl ?_
    simpa only [Ctx.eraseBounds, Env.eraseBounds_cons, PolyTy.eraseBounds_mkTrivial]
      using ihbody
  | @var dbl polyTy instArgs ty ctx hlook htyargs hinst =>
    simp only [Expr.eraseBounds, Ctx.eraseBounds]
    refine TypeOfHM.var (polyTy := PolyTy.eraseBounds polyTy)
      (instArgs := instArgs.map Ty.eraseBounds) ?_ ?_ ?_
    · have hlook' := congrArg (Option.map PolyTy.eraseBounds) hlook
      simpa [Env.eraseBounds_getElem?, Option.map_some] using hlook'
    · intro tyArg hmem
      obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hmem
      exact Ty.IsLC.eraseBounds (htyargs t ht)
    · change InstantiatesBy (instArgs.map Ty.eraseBounds)
        (PolyTy.eraseBounds polyTy).body (Ty.eraseBounds ty)
      simpa [PolyTy.eraseBounds_body] using InstantiatesBy.eraseBounds hinst
  | @ctor name ctorr tyArgs ty ctx hlook htyargs hinst =>
    simp only [Expr.eraseBounds, Ctx.eraseBounds]
    refine TypeOfHM.ctor (ctor := Ctor.eraseBounds ctorr)
      (tyArgs := tyArgs.map Ty.eraseBounds) ?_ ?_ ?_
    · have hlook' := congrArg (Option.map Ctor.eraseBounds) hlook
      simpa [CtorEnv.eraseBounds_get?, Option.map_some] using hlook'
    · intro tyArg hmem
      obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hmem
      exact Ty.IsLC.eraseBounds (htyargs t ht)
    · change InstantiatesBy (tyArgs.map Ty.eraseBounds)
        (Ctor.eraseBounds ctorr).toTy.body (Ty.eraseBounds ty)
      rw [Ctor.eraseBounds_toTy, PolyTy.eraseBounds_body]
      exact InstantiatesBy.eraseBounds hinst
  | @letIn ann ctx boundExpr bodyCtx body bodyTy M L hwf hann hcofin heq hbody ihcofin ihbody =>
    subst heq
    simp only [Expr.eraseBounds]
    refine TypeOfHM.letIn (M := PolyTy.eraseBounds M) (L := L)
      (PolyTy.WF.eraseBounds hwf) (Option.Pins.map_eraseBounds_poly hann) ?_ rfl ?_
    · intro Xs hf
      have hf' : FreshNames L M.paramCount Xs := by
        simpa [PolyTy.eraseBounds_paramCount] using hf
      have hbe := ihcofin Xs hf'
      rw [Expr.eraseBounds_openBoundTyVars, PolyTy.eraseBounds_openVars] at hbe
      exact hbe
    · simpa only [Ctx.eraseBounds, Env.eraseBounds_cons] using ihbody
  | @match_ ctx scrutinee scrutTy branches resultTy hscrut hne hbrs ihscrut ihbrs =>
    simp only [Expr.eraseBounds]
    refine TypeOfHM.match_ ihscrut ?_ ?_
    · intro hcontra
      obtain ⟨⟨p, b⟩, rest, hb⟩ := List.exists_cons_of_ne_nil hne
      simp [hb] at hcontra
    · intro branch' hmem'
      obtain ⟨⟨pat, body⟩, hmem, rfl⟩ := List.mem_map.mp hmem'
      rcases ihbrs (pat, body) hmem with
        ⟨ct, c, n, tyArgs, instContents, hpat, hlook, hScrutEq, hpc, hcontents, hinstC,
          _, hbodyIH⟩ |
        ⟨hpat, _, hbodyIH⟩
      · subst hpat
        have hlook' :
            LookupList.get? ctx.eraseBounds.ctors c = some (Ctor.eraseBounds ct) := by
          have := congrArg (Option.map Ctor.eraseBounds) hlook
          simpa [Ctx.eraseBounds, CtorEnv.eraseBounds_get?, Option.map_some] using this
        have hscrut' :
            Ty.eraseBounds scrutTy =
              .customTy (Ctor.eraseBounds ct).tyName (tyArgs.map Ty.eraseBounds) := by
          rw [hScrutEq]
          simp only [Ty.eraseBounds_customTy, TyList.eraseBounds_eq_map,
            Ctor.eraseBounds_tyName]
        have hfields' :
            List.Forall₂ (InstantiatesBy (tyArgs.map Ty.eraseBounds))
              (Ctor.eraseBounds ct).contents (instContents.map Ty.eraseBounds) := by
          simpa [Ctor.eraseBounds_contents] using
            InstantiatesBy.forall2_eraseBounds hinstC
        have hbody' :
            TypeOfHM
              ⟨(instContents.map Ty.eraseBounds).map PolyTy.mkTrivial ++
                  ctx.eraseBounds.env,
                ctx.eraseBounds.ctors⟩
              body.eraseBounds (Ty.eraseBounds resultTy) := by
          simpa only [Ctx.eraseBounds, Env.eraseBounds_append,
            Env.eraseBounds_map_mkTrivial] using hbodyIH
        refine TypeOfMatchBranch.mk
          ⟨hlook', hscrut',
            by simpa [Ctor.eraseBounds_paramCount, List.length_map] using hpc,
            by simpa [Ctor.eraseBounds_contents, List.length_map] using hcontents,
            hfields'⟩
          rfl hbody'
      · subst hpat
        exact TypeOfMatchBranch.wildcard hbodyIH
  | @letRec ctx bodyCtx anns bindings specs τs G L body ρ hwf hlen hlink hlc hmono heq hbody
      ihmono ihbody =>
    subst heq
    simp only [Expr.eraseBounds]
    refine TypeOfHM.letRec
      (bodyCtx := RecSpecs.bodyCtx ctx.eraseBounds (specs.map RecSpec.eraseBounds) G)
      (specs := specs.map RecSpec.eraseBounds) (τs := τs.map Ty.eraseBounds) (G := G) (L := L)
      (RecSpecs.WF.eraseBounds hwf) ?_ ?_ ?_ ?_ rfl ?_
    · simpa [List.length_map] using hlen
    · intro p hp τ hτ
      obtain ⟨e₀, s₀, hmem₀, hpEq⟩ := List.mem_zip_map (l := specs) (r := τs)
        (f := RecSpec.eraseBounds) (g := Ty.eraseBounds) (by simpa using hp)
      subst hpEq
      cases e₀ with
      | poly σ => exact RecSpec.noConfusion hτ
      | mono τ₀ =>
        injection hτ with hττ
        have hs : s₀ = τ₀ := hlink (RecSpec.mono τ₀, s₀) hmem₀ τ₀ rfl
        rw [hs]
        exact hττ
    · intro t' ht'
      obtain ⟨t, ht, rfl⟩ := List.mem_map.mp ht'
      exact Ty.IsLC.eraseBounds (hlc t ht)
    · intro Xs hf p hp
      obtain ⟨e₀, t₀, hmem₀, hpEq⟩ := List.mem_zip_map (l := bindings) (r := τs)
        (f := Expr.eraseBounds) (g := Ty.eraseBounds) (by simpa using hp)
      subst hpEq
      have hmono₀ := ihmono Xs hf (e₀, t₀) hmem₀
      rw [Ty.eraseBounds_renameG] at hmono₀
      rw [RecSpecs.rhsCtx_eraseBounds] at hmono₀
      simpa [List.map_map, RecSpec.eraseBounds, Function.comp_def] using hmono₀
    · rwa [RecSpecs.bodyCtx_eraseBounds] at ihbody

theorem TypeOfHM.onSubst_eraseBounds {ctx : Ctx} {e : Expr} {τ : Ty} (S : Subst)
    (h_lc : ∀ p ∈ S, p.2.IsLC)
    (h : TypeOfHM ctx.eraseBounds e.eraseBounds (Ty.eraseBounds τ)) :
    TypeOfHM (S.onCtx ctx.eraseBounds).eraseBounds
      ((e.eraseBounds).substTyFvars S).eraseBounds
      (Ty.eraseBounds (S.onTy τ)) := by
  have hS := TypeOfHM.onSubst S h_lc h
  have herase := TypeOfHM.eraseBounds_of hS
  rwa [Ty.eraseBounds_onTy_erase] at herase

/-- Preferred residual transport: conclude at `(S.onCtx ctx).eraseBounds`. -/
theorem TypeOfHM.onSubst_eraseBounds' {ctx : Ctx} {e : Expr} {τ : Ty} (S : Subst)
    (h_lc : ∀ p ∈ S, p.2.IsLC)
    (h : TypeOfHM ctx.eraseBounds e.eraseBounds (Ty.eraseBounds τ)) :
    TypeOfHM (S.onCtx ctx).eraseBounds
      ((e.eraseBounds).substTyFvars S).eraseBounds
      (Ty.eraseBounds (S.onTy τ)) := by
  have key := TypeOfHM.onSubst_eraseBounds S h_lc h
  rwa [Ctx.eraseBounds_onCtx_erase] at key

/-- Fixed-ann residual transport: when `S` fixes annotation free vars of `e`,
    residual TypeOf is at `e.eraseBounds` (Path R subject is always erased). -/
theorem TypeOfHM.onSubst_eraseBounds_fixed {ctx : Ctx} {e : Expr} {τ : Ty} (S : Subst)
    (h_lc : ∀ p ∈ S, p.2.IsLC) (h_fix : e.substTyFvars S = e)
    (h : TypeOfHM ctx.eraseBounds e.eraseBounds (Ty.eraseBounds τ)) :
    TypeOfHM (S.onCtx ctx).eraseBounds e.eraseBounds (Ty.eraseBounds (S.onTy τ)) := by
  have key := TypeOfHM.onSubst_eraseBounds' S h_lc h
  -- Collapse the residual subject back to `e.eraseBounds` under `h_fix`.
  -- (e.eraseBounds).substTyFvars S, then erase
  --   = e.eraseBounds.substTyFvars (S.map erase)     [eraseBounds_substTyFvars + idem]
  --   = (e.substTyFvars S).eraseBounds               [eraseBounds_substTyFvars]
  --   = e.eraseBounds                                [h_fix]
  have hterm :
      ((e.eraseBounds).substTyFvars S).eraseBounds = e.eraseBounds := by
    calc ((e.eraseBounds).substTyFvars S).eraseBounds
        = (e.eraseBounds).eraseBounds.substTyFvars
            (S.map fun p => (p.1, Ty.eraseBounds p.2)) :=
          Expr.eraseBounds_substTyFvars S e.eraseBounds
      _ = e.eraseBounds.substTyFvars
            (S.map fun p => (p.1, Ty.eraseBounds p.2)) := by
          rw [Expr.eraseBounds_idem]
      _ = (e.substTyFvars S).eraseBounds :=
          (Expr.eraseBounds_substTyFvars S e).symm
      _ = e.eraseBounds := by rw [h_fix]
  rwa [hterm] at key

/-- **Iterated fixed-env substitution preservation for `TypeOfHM`.** When the
    substitution keys avoid the context env's free vars, the env is unchanged;
    only the term and type are substituted. Direct port of
    `TypeOfElabHM.typ_substs_preservation` (via the single-fvar uniform lemma). -/
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

/-! Regularity for `TypeOfHM`: a declaratively-typed term has a locally-closed type.
    Direct port of `TypeOfElabHM.regular`; `var`/`ctor` via `InstantiatesBy.preserves_bvars`
    on the (existential) LC instantiation witness. -/
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
  | _, _, _, .letRec _ _ _ _ _ _ hbody => TypeOfHM.regular hbody

theorem TypeOfMatchBranch.regular : {ctx : Ctx} → {br : MatchPattern × Expr} →
    {scrutTy : Ty} → {rt : Ty} →
    TypeOfMatchBranch ctx br scrutTy rt → rt.IsLC
  | _, _, _, _, .mk _ _ hbody => TypeOfHM.regular hbody
  | _, _, _, _, .wildcard hbody => TypeOfHM.regular hbody
end

/-! ## Well-typed terms have every free var below the context length

`TypeOfHM` maintains the invariant that a well-typed expression is
`varsBelow ctx.env.length`: the `var` rule forces an in-range context lookup, and
every binder rule extends the env by exactly the amount `varsBelow`'s bookkeeping
expects. Direct port of `TypeOfElabHM.varsBelow` / `TypeOfElabHM.closed`; the
`var` case differs only in that `tyArgs` is ignored. -/

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

/-- **Well-typed ⇒ all free term-vars below the context length.** By induction on
    the (decoration-blind declarative) typing derivation. -/
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
  | letRec hwf hlen hlink hlc hmono heq hbody ihmono ihbody =>
    expose_names
    subst heq
    simp only [Expr.varsBelow, Bool.and_eq_true]
    have hτslen : bindings.length = τs.length := hlen
    refine ⟨?_, ?_⟩
    · -- every binding is closed under the group-extended context
      apply RecGroupClosed.varsBelow_of_forall
      intro bnd hmem
      obtain ⟨t, ht⟩ := mem_zip_of_mem_left hτslen hmem
      obtain ⟨Xs, hXlen, hXnodup, hXavoid⟩ := exists_fresh_names L G.length
      have hc := ihmono Xs ⟨hXlen, hXnodup, hXavoid⟩ (bnd, t) ht
      simp only [RecSpecs.rhsCtx, List.length_append, List.length_map] at hc
      rwa [Nat.add_comm, ← hτslen] at hc
    · -- the body is closed under the group-extended context
      simp only [RecSpecs.bodyCtx, List.length_append, List.length_map] at ihbody
      rwa [Nat.add_comm, ← hwf.length] at ihbody

/-- **Well-typed in the empty context ⇒ closed.** -/
theorem TypeOfHM.closed {ctors : CtorEnv} {e : Expr} {τ : Ty}
    (h : TypeOfHM ⟨[], ctors⟩ e τ) : Expr.varsBelow 0 e = true :=
  TypeOfHM.varsBelow h

/-! ### Cofinite `GeneralisesTo` instantiation (moved from `CekMachine.lean`)

The `TypeOfHM`/`Step` dynamics instantiates a cofinite `let`/`letRec` scheme
premise ("the bound value types at every opening of `M`") at a single type `τ`.
`Ty.substFvars_zip_openVars_eq` is the type-side round-trip (substituting the
zipped fresh names back recovers the `InstantiatesBy` instance), and the two
`GeneralisesTo_inst*` lemmas package it against `TypeOfHM`. These are the
decoration-blind analogues of the CEK leaf's same-named lemmas, restated for
the image of `Expr.erase` (not `IsErased`). -/

/-- Scheme `σ` instantiates to monotype `τ` (the declarative `TypeOfHM.var`
    instantiation: some locally-closed args, no length constraint). -/
def Instantiates (σ : PolyTy) (τ : Ty) : Prop :=
  ∃ instArgs, (∀ a ∈ instArgs, a.IsLC) ∧ σ.InstantiatesTo instArgs τ

/-- Substituting along `Xs.zip Vs` sends `.fvar Xs[i]` to `Vs[i]` (freshness of
    all of `Vs` is required — the `substFvars_zip_openVars_eq` `bvar` case does
    not know which `Vs` entry is selected ahead of time). -/
private theorem Ty.substFvars_zip_fvar_eq'_allVs {Xs : List Nat} {Vs : List Ty}
    {i : Nat} {x : Nat} {v : Ty}
    (h_nodup : Xs.Nodup)
    (h_fresh : ∀ X ∈ Xs, X ∉ Ty.freeVarsList Vs)
    (hx : Xs[i]? = some x)
    (hv : Vs[i]? = some v) :
    Ty.substFvars (Xs.zip Vs) (.fvar x) = v := by
  induction Xs generalizing Vs i x v with
  | nil => simp at hx
  | cons X0 Xs' ih =>
      cases Vs with
      | nil => simp at hv
      | cons V0 Vs' =>
          cases i with
          | zero =>
              simp only [List.getElem?_cons_zero, Option.some.injEq] at hx hv
              simp only [List.zip_cons_cons, Ty.substFvars]
              rw [← hx, show Ty.substFvar X0 V0 (.fvar X0) = V0 by simp [Ty.substFvar], ← hv]
              apply Ty.substFvars_eq_self_of_no_key
              intro p hp hcontra
              have hp1 : p.1 ∈ Xs' := (List.of_mem_zip hp).1
              have hXf : p.1 ∉ Ty.freeVarsList (V0 :: Vs') :=
                h_fresh p.1 (List.mem_cons_of_mem _ hp1)
              simp only [Ty.freeVarsList, List.mem_dedup, List.mem_append] at hXf
              exact hXf (Or.inl hcontra)
          | succ k =>
              simp only [List.getElem?_cons_succ] at hx hv
              have h_X0_notin : X0 ∉ Xs' := (List.nodup_cons.mp h_nodup).1
              have h_x_mem : x ∈ Xs' := List.mem_of_getElem? hx
              have h_ne : x ≠ X0 := fun h => h_X0_notin (h ▸ h_x_mem)
              have h_fresh' : ∀ X ∈ Xs', X ∉ Ty.freeVarsList Vs' := by
                intro X hX hc
                refine h_fresh X (List.mem_cons_of_mem _ hX) ?_
                simp only [Ty.freeVarsList, List.mem_dedup, List.mem_append]
                exact .inr hc
              simp only [List.zip_cons_cons, Ty.substFvars]
              rw [show Ty.substFvar X0 V0 (.fvar x) = .fvar x by simp [Ty.substFvar, h_ne]]
              exact ih (List.nodup_cons.mp h_nodup).2 h_fresh' hx hv

/-- The type-side round-trip: substituting the zipped fresh names `Xs` back to
    `Vs` through `ty.openVars Xs` recovers exactly the `InstantiatesBy Vs ty τ`
    instance, PROVIDED the opened type is locally closed (which
    `TypeOfHM.regular` supplies — the LC hypothesis rules out dangling bvars of
    `ty` beyond `Xs.length`, where the two sides would diverge). -/
theorem Ty.substFvars_zip_openVars_eq {Xs : List Nat} {Vs : List Ty}
    (hXs_nodup : Xs.Nodup)
    (hXs_fresh_Vs : ∀ X ∈ Xs, X ∉ Ty.freeVarsList Vs) :
    ∀ (ty τ : Ty), InstantiatesBy Vs ty τ →
      (∀ X ∈ Xs, X ∉ ty.freeVars) →
      ContainsBvarsUpTo 0 (Ty.openVars Xs ty) →
      Ty.substFvars (Xs.zip Vs) (Ty.openVars Xs ty) = τ := by
  intro ty
  induction ty using Ty.rec_strong with
  | prim p =>
      intro τ h _ _
      cases h
      unfold Ty.openVars
      simp only [Ty.instantiate]
      exact Ty.substFvars_prim
  | arrow a b iha ihb =>
      intro τ h hfresh hLC
      cases h with
      | arrow ha hb =>
          rename_i instFst instSnd
          rw [Ty.openVars_arrow, Ty.substFvars_arrow]
          cases hLC with
          | arrow hLCa hLCb =>
              rw [iha instFst ha (fun X hX hc => hfresh X hX (by
                    simp only [Ty.freeVars, List.mem_dedup, List.mem_append]
                    exact .inl hc)) hLCa,
                  ihb instSnd hb (fun X hX hc => hfresh X hX (by
                    simp only [Ty.freeVars, List.mem_dedup, List.mem_append]
                    exact .inr hc)) hLCb]
  | bvar i =>
      intro τ h hfresh hLC
      cases h with
      | bvar hsome =>
          by_cases hi : i < Xs.length
          · obtain ⟨x, hx⟩ : ∃ x, Xs[i]? = some x := ⟨_, List.getElem?_eq_getElem hi⟩
            simp only [Ty.openVars, Ty.instantiate, hx, Option.elim]
            exact Ty.substFvars_zip_fvar_eq'_allVs hXs_nodup hXs_fresh_Vs hx hsome
          · have hx : Xs[i]? = none := List.getElem?_eq_none (by omega)
            have hLCi : ContainsBvarsUpTo 0 (.bvar i) := by
              simpa only [Ty.openVars, Ty.instantiate, hx, Option.elim] using hLC
            cases hLCi with
            | bvar hlt => omega
  | fvar n =>
      intro τ h hfresh hLC
      cases h
      simp only [Ty.openVars, Ty.instantiate]
      apply Ty.substFvars_eq_self_of_no_key
      intro p hp hcontra
      have hp1 : p.1 ∈ Xs := (List.of_mem_zip hp).1
      have hnf : p.1 ∉ Ty.freeVars (.fvar n) := hfresh p.1 hp1
      simp only [Ty.freeVars, List.mem_singleton] at hnf hcontra
      exact hnf hcontra
  | customTy nm tys ih =>
      intro τ h hfresh hLC
      cases h with
      | customTy hforall =>
          rw [Ty.openVars_customTy, Ty.substFvars_customTy]
          apply congrArg (Ty.customTy nm)
          cases hLC with
          | customTy hball =>
              induction hforall with
              | nil => rfl
              | cons hhd htl ihtl =>
                  rename_i hd_ty hd_inst tl_tys tl_inst
                  have h_hd : Ty.substFvars (Xs.zip Vs) (Ty.openVars Xs hd_ty) = hd_inst :=
                    ih hd_ty List.mem_cons_self hd_inst hhd
                      (fun X hX hc => hfresh X hX (by
                        simp only [Ty.freeVars, TyList.freeVars, List.mem_dedup, List.mem_append]
                        exact .inl hc))
                      (hball (Ty.openVars Xs hd_ty) (by
                        exact List.mem_cons_self))
                  have hfresh_tl : ∀ X ∈ Xs, X ∉ (Ty.customTy nm tl_tys).freeVars := by
                    intro X hX hc
                    exact hfresh X hX (by
                      simp only [Ty.freeVars, TyList.freeVars, List.mem_dedup, List.mem_append]
                      exact .inr hc)
                  have hball_tl :
                      ∀ ty ∈ TyList.instantiate (fun i => Xs[i]?.elim (Ty.bvar i) Ty.fvar) tl_tys,
                        ContainsBvarsUpTo 0 ty :=
                    fun ty ht => hball ty (List.mem_cons_of_mem _ ht)
                  have h_tl : List.map (Ty.substFvars (Xs.zip Vs))
                      (List.map (Ty.openVars Xs) tl_tys) = tl_inst :=
                    ihtl (fun t ht => ih t (List.mem_cons_of_mem _ ht)) hfresh_tl hball_tl
                  simp only [List.map_cons]
                  rw [← h_hd, h_tl]
  | bl lo hi e ih =>
      intro τ h hfresh hLC
      cases h with
      | bl he =>
          rename_i instElem
          rw [Ty.openVars_bl, Ty.substFvars_bl]
          rw [Ty.openVars_bl] at hLC
          cases hLC with
          | bl hLCe =>
              exact congrArg (Ty.bl lo hi) (ih instElem he (fun X hX hc => hfresh X hX hc) hLCe)

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

/-! ### Path R residual source soundness (`TypeOfHM` on erased source)

Source `e` may carry BL anns; pure `TypeOfHM` judges `e.eraseBounds` only.
Mirror of residual `Infer.sound` scaffolding, but conclusions are on **source**
`e.eraseBounds` (not elaboratum) via decoration-blind `TypeOfHM`.
-/

private theorem Ctor.IsBoolCtor.typeOfHM_erase {ctx : Ctx} {name : CtorName} {c : Ctor}
    (hlook : LookupList.get? ctx.ctors name = some c) (hb : c.IsBoolCtor) :
    TypeOfHM ctx.eraseBounds (.ctor name) (.customTy ⟨"Bool"⟩ []) := by
  have hlook' : LookupList.get? ctx.eraseBounds.ctors name = some (Ctor.eraseBounds c) := by
    have := congrArg (Option.map Ctor.eraseBounds) hlook
    simpa [Ctx.eraseBounds, CtorEnv.eraseBounds_get?, Option.map_some] using this
  have hb' : (Ctor.eraseBounds c).IsBoolCtor := by
    obtain ⟨hname, hpc, hcont⟩ := hb
    refine ⟨?_, ?_, ?_⟩
    · simpa [Ctor.eraseBounds_tyName] using hname
    · simpa [Ctor.eraseBounds_paramCount] using hpc
    · simp [Ctor.eraseBounds_contents, hcont]
  exact Ctor.IsBoolCtor.typeOfHM hlook' hb'

/-- Append form of residual fixed-term transport for source subjects. -/
theorem TypeOfHM.onSubst_eraseBounds_fixed_append {ctx : Ctx} {e : Expr} {τ : Ty}
    (S₁ S₂ : Subst)
    (_h₁ : ∀ p ∈ S₁, p.2.IsLC) (h₂ : ∀ p ∈ S₂, p.2.IsLC)
    (_h_fix₁ : e.substTyFvars S₁ = e) (h_fix₂ : e.substTyFvars S₂ = e)
    (h : TypeOfHM (S₁.onCtx ctx).eraseBounds e.eraseBounds (Ty.eraseBounds τ)) :
    TypeOfHM ((S₁ ++ S₂).onCtx ctx).eraseBounds e.eraseBounds
      (Ty.eraseBounds (S₂.onTy τ)) := by
  have key := TypeOfHM.onSubst_eraseBounds_fixed (ctx := S₁.onCtx ctx) (e := e) (τ := τ)
    S₂ h₂ h_fix₂ h
  simpa only [Subst.onCtx_append] using key

/-! ### Source-side rebuild of the fused `letRec` rule at the shared pool.

`Expr.letRecElab_sound` types the ELABORATUM: a Λ-outside nest whose inner
mixed group sits at the EMPTY pool, with the pool-`G` generalisation carried by
the outer `letIn` wrappers. The source node has no such nest — the declarative
`TypeOfHM.letRec` wants its cofinite `RecSpecs.MonoTypedInit` premise stated
at the shared opening `G ↦ Xs`, with every member's witness monotype renamed
(`Ty.renameG G Xs`), in the all-mono-rendered group context.

Inference, however, only ever delivers the group's members at the empty pool
with their SOLVED monotypes. The gap is exactly the renaming substitution
`G.zip (Xs.map Ty.fvar)` — which is what `Ty.renameG` unfolds to — so
`TypeOfHM.onSubst_fixed` transports the empty-pool premises to the pool-`G`
ones, provided `G` is disjoint from everything the renaming must not disturb:
the ambient env, the annotated members' declared schemes, and the bindings'
own annotation free variables. Those three are precisely the `genGroupVars`
side conditions `Infer`'s `letRec` scaffolding already establishes. -/

/-- **Source dual of `Expr.letRecElab_sound`.** Rebuild the declarative source
    `TypeOfHM.letRec` at the shared gen-pool `G` from group premises stated at
    the EMPTY pool: every member's RHS types at its witness monotype
    (`bs.zip τs`) in the ALL-MONO empty-pool context
    (`(τs.map RecSpec.mono).map (RecSpec.rhsEntry [] [])`, i.e. `τs.map mkTrivial`).

    `hG_env` / `hG_bs` say the pool is fresh for the ambient env and for the
    bindings' annotations — so renaming `G ↦ Xs` moves only the shared
    monotypes. (The annotated members' schemes need no pool-freshness anymore:
    they never appear in the RHS context, matching the pivot rule.) -/
theorem TypeOfHM.letRec_of_emptyPool {ctx : Ctx} {Lp G : List Nat}
    {anns : List (Option PolyTy)} {bs : List Expr} {specs : List RecSpec} {τs : List Ty}
    {body : Expr} {ρ : Ty}
    (hwf : RecSpecs.WF anns bs specs G)
    (hlen : bs.length = τs.length)
    (hlink : ∀ p ∈ specs.zip τs, ∀ τ, p.1 = .mono τ → p.2 = τ)
    (hlc : ∀ t ∈ τs, t.IsLC)
    (hG_env : ∀ g ∈ G, g ∉ ctx.env.freeVars)
    (hG_bs : ∀ g ∈ G, ∀ e ∈ bs, g ∉ e.tyFreeVars)
    (hmono : ∀ p ∈ bs.zip τs,
      TypeOfHM ⟨(τs.map RecSpec.mono).map (RecSpec.rhsEntry [] []) ++ ctx.env, ctx.ctors⟩
        p.1 p.2)
    (hbody : TypeOfHM (RecSpecs.bodyCtx ctx specs G) body ρ) :
    TypeOfHM ctx (Expr.letRec anns bs body) ρ := by
  have hctx_eq : ∀ Xs : List Nat,
      Subst.onCtx (G.zip (Xs.map (Ty.fvar ·)))
          ⟨(τs.map RecSpec.mono).map (RecSpec.rhsEntry [] []) ++ ctx.env, ctx.ctors⟩
        = RecSpecs.rhsCtx ctx (τs.map RecSpec.mono) G Xs := by
    intro Xs
    simp only [Subst.onCtx, Subst.onEnv, RecSpecs.rhsCtx, List.map_append]
    congr 1
    congr 1
    · simp only [List.map_map]
      apply List.map_congr_left
      intro t _
      simp only [Function.comp_apply, RecSpec.rhsEntry]
      rw [Ty.renameG_nil_pool]
      rfl
    · simpa only [Subst.onEnv] using
        Subst.onEnv_eq_self_of_fresh (fun p hp => hG_env p.1 (List.of_mem_zip hp).1)
  refine TypeOfHM.letRec (specs := specs) (τs := τs) (G := G) (L := Lp ++ G)
    hwf hlen hlink hlc ?mono rfl hbody
  · intro Xs hXs p hp
    have hctx := hctx_eq Xs
    have hsrc := hmono p hp
    have hLC : ∀ q ∈ G.zip (Xs.map (Ty.fvar ·)), q.2.IsLC := by
      intro q hq
      obtain ⟨x, hx, hxeq⟩ := List.mem_map.mp (List.of_mem_zip hq).2
      rw [← hxeq]; exact ContainsBvarsUpTo.fvar
    have hfix : p.1.substTyFvars (G.zip (Xs.map (Ty.fvar ·))) = p.1 :=
      Expr.substTyFvars_eq_self_of_not_mem_tyFreeVars (fun q hq hc =>
        hG_bs q.1 (List.of_mem_zip hq).1 p.1 (List.of_mem_zip hp).1 hc)
    have hren := TypeOfHM.onSubst_fixed (G.zip (Xs.map (Ty.fvar ·))) hLC hfix hsrc
    rw [hctx] at hren
    simpa [Subst.onTy, Ty.renameG] using hren

/-- Refinement of `Ty.substFvars_zip_fvar_eq` needing freshness only of the
    *selected* value `v` (not all of `Vs`), and no length condition. Substituting
    along `Xs.zip Vs` sends `.fvar Xs[i]` to `Vs[i]`. -/
theorem Ty.substFvars_zip_fvar_eq' {Xs : List Nat} {Vs : List Ty} {i : Nat} {x : Nat} {v : Ty}
    (h_nodup : Xs.Nodup) (hx : Xs[i]? = some x) (hv : Vs[i]? = some v)
    (h_fresh : ∀ X ∈ Xs, X ∉ v.freeVars) :
    Ty.substFvars (Xs.zip Vs) (.fvar x) = v := by
  induction Xs generalizing Vs i x v with
  | nil => simp at hx
  | cons X0 Xs' ih =>
    cases Vs with
    | nil => simp at hv
    | cons V0 Vs' =>
      cases i with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hx hv
        simp only [List.zip_cons_cons, Ty.substFvars]
        rw [← hx, show Ty.substFvar X0 V0 (.fvar X0) = V0 by simp [Ty.substFvar], ← hv]
        apply Ty.substFvars_eq_self_of_no_key
        intro p hp hcontra
        have hp1 : p.1 ∈ Xs' := (List.of_mem_zip hp).1
        exact h_fresh p.1 (List.mem_cons_of_mem _ hp1) (hv ▸ hcontra)
      | succ k =>
        simp only [List.getElem?_cons_succ] at hx hv
        have h_X0_notin : X0 ∉ Xs' := (List.nodup_cons.mp h_nodup).1
        have h_ne : x ≠ X0 := fun h => h_X0_notin (h ▸ List.mem_of_getElem? hx)
        simp only [List.zip_cons_cons, Ty.substFvars]
        rw [show Ty.substFvar X0 V0 (.fvar x) = .fvar x by simp [Ty.substFvar, h_ne]]
        exact ih (List.nodup_cons.mp h_nodup).2 hx hv
          (fun X hX => h_fresh X (List.mem_cons_of_mem _ hX))

/-! ### Unification: MGU residual is LC, and unification completeness

For the `app` completeness case we need: (1) the residual `R` factoring a unifier
`S'` through the MGU `S` is locally-closed when `S'` is (so it can serve as the
next `S₀`); (2) unifiability implies a `UnifyRel` derivation exists. -/

mutual
/-- Real LC residual: `FactorsHM` + LC when the witness is LC. -/
theorem UnifyRel.greatest_lc_factors : {τ₁ τ₂ : Ty} → {S : Subst} → UnifyRel τ₁ τ₂ S →
    ∀ S' : Subst, (∀ p ∈ S', p.2.IsLC) → Unifies S' τ₁ τ₂ →
    ∃ R : Subst, FactorsHM S' S R ∧ (∀ p ∈ R, p.2.IsLC)
  | _, _, _, .prim, S', hlc, _ =>
    ⟨S', ⟨fun τ => by simp only [AgreesHM, Subst.onTy_nil], hlc⟩⟩
  | _, _, _, .fvarRefl, S', hlc, _ =>
    ⟨S', ⟨fun τ => by simp only [AgreesHM, Subst.onTy_nil], hlc⟩⟩
  | _, _, _, @UnifyRel.fvarL n U _ _, S', hlc, hS' => by
    refine ⟨S', ⟨fun τ => ?_, hlc⟩⟩
    simp only [AgreesHM, Subst.onTy] at hS' ⊢
    exact (Subst.onTy_substFvar_erase hS' τ).symm
  | _, _, _, @UnifyRel.fvarR n U _ _, S', hlc, hS' => by
    refine ⟨S', ⟨fun τ => ?_, hlc⟩⟩
    simp only [AgreesHM, Subst.onTy] at hS' ⊢
    exact (Subst.onTy_substFvar_erase hS'.symm τ).symm
  | _, _, _, @UnifyRel.arrow a b c d S₁ S₂ h₁ h₂, S', hlc, hS' => by
    have hac : Unifies S' a c := by
      simp only [Unifies, AgreesHM, Subst.onTy_arrow, Ty.eraseBounds_arrow] at hS'
      exact (Ty.arrow.inj hS').1
    have hbd : Unifies S' b d := by
      simp only [Unifies, AgreesHM, Subst.onTy_arrow, Ty.eraseBounds_arrow] at hS'
      exact (Ty.arrow.inj hS').2
    obtain ⟨R₁, hR₁, hR₁lc⟩ := UnifyRel.greatest_lc_factors h₁ S' hlc hac
    have hR₁bd : Unifies R₁ (S₁.onTy b) (S₁.onTy d) := by
      simp only [Unifies, AgreesHM] at hbd ⊢
      exact (hR₁ b).symm.trans (hbd.trans (hR₁ d))
    obtain ⟨R₂, hR₂, hR₂lc⟩ := UnifyRel.greatest_lc_factors h₂ R₁ hR₁lc hR₁bd
    refine ⟨R₂, ⟨fun τ => ?_, hR₂lc⟩⟩
    simp only [AgreesHM, Subst.onTy_append]
    exact (hR₁ τ).trans (hR₂ (S₁.onTy τ))
  | _, _, _, @UnifyRel.customTy nm tys₁ tys₂ S hl, S', hlc, hS' => by
    have hlist :
        tys₁.map (fun t => Ty.eraseBounds (S'.onTy t)) =
          tys₂.map (fun t => Ty.eraseBounds (S'.onTy t)) := by
      simp only [Unifies, AgreesHM, Subst.onTy_customTy, Ty.eraseBounds_customTy,
        TyList.eraseBounds_eq_map, List.map_map] at hS'
      exact (Ty.customTy.inj hS').2
    exact UnifyRelList.greatest_lc_factors hl S' hlc hlist
  | _, _, _, @UnifyRel.bl lo₁ hi₁ lo₂ hi₂ e₁ e₂ S h, S', hlc, hS' => by
    have hElem : Unifies S' e₁ e₂ := by
      simp only [Unifies, AgreesHM, Subst.onTy_bl, Ty.eraseBounds_bl, bareListTy] at hS' ⊢
      simpa [bareListTy, Ty.customTy.injEq, List.cons.injEq] using hS'
    exact UnifyRel.greatest_lc_factors h S' hlc hElem
  | _, _, _, @UnifyRel.blList lo hi e α S h, S', hlc, hS' => by
    have hElem : Unifies S' e α := by
      simp only [Unifies, AgreesHM, Subst.onTy_bl, Subst.onTy_customTy, Ty.eraseBounds_bl,
        Ty.eraseBounds_customTy, TyList.eraseBounds_eq_map, List.map_cons, List.map_nil,
        bareListTy] at hS' ⊢
      simpa [bareListTy, Ty.customTy.injEq, List.cons.injEq] using hS'
    exact UnifyRel.greatest_lc_factors h S' hlc hElem
  | _, _, _, @UnifyRel.listBl lo hi e α S h, S', hlc, hS' => by
    have hElem : Unifies S' α e := by
      simp only [Unifies, AgreesHM, Subst.onTy_bl, Subst.onTy_customTy, Ty.eraseBounds_bl,
        Ty.eraseBounds_customTy, TyList.eraseBounds_eq_map, List.map_cons, List.map_nil,
        bareListTy] at hS' ⊢
      simpa [bareListTy, Ty.customTy.injEq, List.cons.injEq] using hS'
    exact UnifyRel.greatest_lc_factors h S' hlc hElem

theorem UnifyRelList.greatest_lc_factors : {ts₁ ts₂ : List Ty} → {S : Subst} →
    UnifyRelList ts₁ ts₂ S → ∀ S' : Subst, (∀ p ∈ S', p.2.IsLC) →
      ts₁.map (fun t => Ty.eraseBounds (S'.onTy t)) =
        ts₂.map (fun t => Ty.eraseBounds (S'.onTy t)) →
      ∃ R : Subst, FactorsHM S' S R ∧ (∀ p ∈ R, p.2.IsLC)
  | _, _, _, .nil, S', hlc, _ =>
    ⟨S', ⟨fun τ => by simp only [AgreesHM, Subst.onTy_nil], hlc⟩⟩
  | _, _, _, @UnifyRelList.cons t₁ t₂ ts₁ ts₂ S₁ S₂ h₁ ht, S', hlc, hS' => by
    simp only [List.map_cons, List.cons.injEq] at hS'
    obtain ⟨ht1t2, htail⟩ := hS'
    obtain ⟨R₁, hR₁, hR₁lc⟩ := UnifyRel.greatest_lc_factors h₁ S' hlc ht1t2
    have hlist :
        (ts₁.map S₁.onTy).map (fun t => Ty.eraseBounds (R₁.onTy t)) =
          (ts₂.map S₁.onTy).map (fun t => Ty.eraseBounds (R₁.onTy t)) := by
      have key (l : List Ty) :
          (l.map S₁.onTy).map (fun t => Ty.eraseBounds (R₁.onTy t)) =
            l.map (fun t => Ty.eraseBounds (S'.onTy t)) := by
        rw [List.map_map]
        apply List.map_congr_left
        intro t _
        exact (hR₁ t).symm
      rw [key, key, htail]
    obtain ⟨R₂, hR₂, hR₂lc⟩ := UnifyRelList.greatest_lc_factors ht R₁ hR₁lc hlist
    refine ⟨R₂, ⟨fun τ => ?_, hR₂lc⟩⟩
    simp only [AgreesHM, Subst.onTy_append]
    exact (hR₁ τ).trans (hR₂ (S₁.onTy τ))
end

/- Path R: structural `greatest_lc` is false in general (same BL/List issue).
    Use `UnifyRel.greatest_lc_factors` only. Do not reintroduce a structural form. -/

/-! ### MGU residual preserves a rigid set `K`

For the unification-based principality cases (`app`, `fst`/`snd`, `match`) the
residual `R` that factors a witness unifier `S'` through the MGU `S` must keep
every rigid skolem `k ∈ K` fixed (so it can serve as the next `S₀` and ultimately
feed the enclosing `letInAnn`'s extended `K`). This is *not* the statement that
the MGU `S` avoids `K` — it generally does not (the left-leaning MGU can bind a
skolem facing a fresh var). Rather, `greatest` builds `R` by **threading the
witness**: at every leaf the residual *is* `S'`, and the recursive cases feed the
intermediate residual as the next witness. So "`R` fixes `K`" follows from "`S'`
fixes `K`" by the very same induction as `greatest_lc`. -/

mutual
/-- Real K-fixing residual: `FactorsHM` + LC + fixes `K` when the witness does. -/
theorem UnifyRel.greatest_K_factors {K : List Nat} :
    {τ₁ τ₂ : Ty} → {S : Subst} → UnifyRel τ₁ τ₂ S →
    ∀ S' : Subst, (∀ p ∈ S', p.2.IsLC) → Unifies S' τ₁ τ₂ →
    (∀ k ∈ K, S'.onTy (.fvar k) = .fvar k) →
    ∃ R : Subst, FactorsHM S' S R ∧ (∀ p ∈ R, p.2.IsLC) ∧
      (∀ k ∈ K, R.onTy (.fvar k) = .fvar k)
  | _, _, _, .prim, S', hlc, _, hK =>
    ⟨S', ⟨fun τ => by simp only [AgreesHM, Subst.onTy_nil], hlc, hK⟩⟩
  | _, _, _, .fvarRefl, S', hlc, _, hK =>
    ⟨S', ⟨fun τ => by simp only [AgreesHM, Subst.onTy_nil], hlc, hK⟩⟩
  | _, _, _, @UnifyRel.fvarL n U _ _, S', hlc, hS', hK => by
    refine ⟨S', ⟨fun τ => ?_, hlc, hK⟩⟩
    simp only [AgreesHM, Subst.onTy] at hS' ⊢
    exact (Subst.onTy_substFvar_erase hS' τ).symm
  | _, _, _, @UnifyRel.fvarR n U _ _, S', hlc, hS', hK => by
    refine ⟨S', ⟨fun τ => ?_, hlc, hK⟩⟩
    simp only [AgreesHM, Subst.onTy] at hS' ⊢
    exact (Subst.onTy_substFvar_erase hS'.symm τ).symm
  | _, _, _, @UnifyRel.arrow a b c d S₁ S₂ h₁ h₂, S', hlc, hS', hK => by
    have hac : Unifies S' a c := by
      simp only [Unifies, AgreesHM, Subst.onTy_arrow, Ty.eraseBounds_arrow] at hS'
      exact (Ty.arrow.inj hS').1
    have hbd : Unifies S' b d := by
      simp only [Unifies, AgreesHM, Subst.onTy_arrow, Ty.eraseBounds_arrow] at hS'
      exact (Ty.arrow.inj hS').2
    obtain ⟨R₁, hR₁, hR₁lc, hR₁K⟩ := UnifyRel.greatest_K_factors h₁ S' hlc hac hK
    have hR₁bd : Unifies R₁ (S₁.onTy b) (S₁.onTy d) := by
      simp only [Unifies, AgreesHM] at hbd ⊢
      exact (hR₁ b).symm.trans (hbd.trans (hR₁ d))
    obtain ⟨R₂, hR₂, hR₂lc, hR₂K⟩ := UnifyRel.greatest_K_factors h₂ R₁ hR₁lc hR₁bd hR₁K
    refine ⟨R₂, ⟨fun τ => ?_, hR₂lc, hR₂K⟩⟩
    simp only [AgreesHM, Subst.onTy_append]
    exact (hR₁ τ).trans (hR₂ (S₁.onTy τ))
  | _, _, _, @UnifyRel.customTy nm tys₁ tys₂ S hl, S', hlc, hS', hK => by
    have hlist :
        tys₁.map (fun t => Ty.eraseBounds (S'.onTy t)) =
          tys₂.map (fun t => Ty.eraseBounds (S'.onTy t)) := by
      simp only [Unifies, AgreesHM, Subst.onTy_customTy, Ty.eraseBounds_customTy,
        TyList.eraseBounds_eq_map, List.map_map] at hS'
      exact (Ty.customTy.inj hS').2
    exact UnifyRelList.greatest_K_factors hl S' hlc hlist hK
  | _, _, _, @UnifyRel.bl lo₁ hi₁ lo₂ hi₂ e₁ e₂ S h, S', hlc, hS', hK => by
    have hElem : Unifies S' e₁ e₂ := by
      simp only [Unifies, AgreesHM, Subst.onTy_bl, Ty.eraseBounds_bl, bareListTy] at hS' ⊢
      simpa [bareListTy, Ty.customTy.injEq, List.cons.injEq] using hS'
    exact UnifyRel.greatest_K_factors h S' hlc hElem hK
  | _, _, _, @UnifyRel.blList lo hi e α S h, S', hlc, hS', hK => by
    have hElem : Unifies S' e α := by
      simp only [Unifies, AgreesHM, Subst.onTy_bl, Subst.onTy_customTy, Ty.eraseBounds_bl,
        Ty.eraseBounds_customTy, TyList.eraseBounds_eq_map, List.map_cons, List.map_nil,
        bareListTy] at hS' ⊢
      simpa [bareListTy, Ty.customTy.injEq, List.cons.injEq] using hS'
    exact UnifyRel.greatest_K_factors h S' hlc hElem hK
  | _, _, _, @UnifyRel.listBl lo hi e α S h, S', hlc, hS', hK => by
    have hElem : Unifies S' α e := by
      simp only [Unifies, AgreesHM, Subst.onTy_bl, Subst.onTy_customTy, Ty.eraseBounds_bl,
        Ty.eraseBounds_customTy, TyList.eraseBounds_eq_map, List.map_cons, List.map_nil,
        bareListTy] at hS' ⊢
      simpa [bareListTy, Ty.customTy.injEq, List.cons.injEq] using hS'
    exact UnifyRel.greatest_K_factors h S' hlc hElem hK

theorem UnifyRelList.greatest_K_factors {K : List Nat} :
    {ts₁ ts₂ : List Ty} → {S : Subst} → UnifyRelList ts₁ ts₂ S →
    ∀ S' : Subst, (∀ p ∈ S', p.2.IsLC) →
      ts₁.map (fun t => Ty.eraseBounds (S'.onTy t)) =
        ts₂.map (fun t => Ty.eraseBounds (S'.onTy t)) →
    (∀ k ∈ K, S'.onTy (.fvar k) = .fvar k) →
    ∃ R : Subst, FactorsHM S' S R ∧ (∀ p ∈ R, p.2.IsLC) ∧
      (∀ k ∈ K, R.onTy (.fvar k) = .fvar k)
  | _, _, _, .nil, S', hlc, _, hK =>
    ⟨S', ⟨fun τ => by simp only [AgreesHM, Subst.onTy_nil], hlc, hK⟩⟩
  | _, _, _, @UnifyRelList.cons t₁ t₂ ts₁ ts₂ S₁ S₂ h₁ ht, S', hlc, hS', hK => by
    simp only [List.map_cons, List.cons.injEq] at hS'
    obtain ⟨ht1t2, htail⟩ := hS'
    obtain ⟨R₁, hR₁, hR₁lc, hR₁K⟩ := UnifyRel.greatest_K_factors h₁ S' hlc ht1t2 hK
    have hlist :
        (ts₁.map S₁.onTy).map (fun t => Ty.eraseBounds (R₁.onTy t)) =
          (ts₂.map S₁.onTy).map (fun t => Ty.eraseBounds (R₁.onTy t)) := by
      have key (l : List Ty) :
          (l.map S₁.onTy).map (fun t => Ty.eraseBounds (R₁.onTy t)) =
            l.map (fun t => Ty.eraseBounds (S'.onTy t)) := by
        rw [List.map_map]
        apply List.map_congr_left
        intro t _
        exact (hR₁ t).symm
      rw [key, key, htail]
    obtain ⟨R₂, hR₂, hR₂lc, hR₂K⟩ := UnifyRelList.greatest_K_factors ht R₁ hR₁lc hlist hR₁K
    refine ⟨R₂, ⟨fun τ => ?_, hR₂lc, hR₂K⟩⟩
    simp only [AgreesHM, Subst.onTy_append]
    exact (hR₁ τ).trans (hR₂ (S₁.onTy τ))
end

/- Path R: the structural `UnifyRel.greatest_K` / `UnifyRelList.greatest_K` were
   DELETED, not deferred. They are **false**: `UnifyRel.unifies` only yields
   erase-equality (`AgreesHM`), never tree equality, so a structural MGU cannot
   be recovered. They previously carried `exact False.elim (by sorry)`, which
   made their two (dead) callers *look* proved while resting on `False`.
   Use `UnifyRel.greatest_K_factors` / `UnifyRelList.greatest_K_factors` above,
   which factor up to `AgreesHM` — the honest Path R statement. -/

/-! A structural size on types (own measure; cleaner than `sizeOf` for the
    unification termination argument). -/
mutual
def Ty.size : Ty → Nat
  | .prim _ => 1
  | .bvar _ => 1
  | .fvar _ => 1
  | .arrow a b => 1 + a.size + b.size
  | .customTy _ tys => 1 + TyList.size tys
  | .bl _ _ e => 1 + e.size
def TyList.size : List Ty → Nat
  | [] => 0
  | hd :: tl => hd.size + TyList.size tl
end

theorem TyList.size_mem_le {t : Ty} {tys : List Ty} (h : t ∈ tys) :
    t.size ≤ TyList.size tys := by
  induction tys with
  | nil => exact absurd h List.not_mem_nil
  | cons hd tl ih =>
    rcases List.mem_cons.mp h with rfl | h
    · simp only [TyList.size]; omega
    · have := ih h; simp only [TyList.size]; omega

@[simp] theorem Ty.size_pos : ∀ {τ : Ty}, 0 < τ.size
  | .prim _ => by simp only [Ty.size]; omega
  | .bvar _ => by simp only [Ty.size]; omega
  | .fvar _ => by simp only [Ty.size]; omega
  | .arrow _ _ => by simp only [Ty.size]; omega
  | .customTy _ _ => by simp only [Ty.size]; omega
  | .bl _ _ e => by simp only [Ty.size]; have := @Ty.size_pos e; omega

/-- Occurs-check via size: applying any substitution, a variable's image is no
    bigger than the image of any type containing it. -/
theorem Ty.size_onTy_fvar_le {S : Subst} {n : Nat} :
    ∀ {b : Ty}, n ∈ b.freeVars → (S.onTy (.fvar n)).size ≤ (S.onTy b).size := by
  intro b
  induction b using Ty.rec_strong with
  | prim p => simp [Ty.freeVars]
  | bvar i => simp [Ty.freeVars]
  | fvar m => intro h; simp only [Ty.freeVars, List.mem_singleton] at h; subst h; exact le_refl _
  | arrow a b iha ihb =>
    intro h
    simp only [Ty.freeVars, List.mem_dedup, List.mem_append] at h
    simp only [Subst.onTy_arrow, Ty.size]
    rcases h with h | h
    · have := iha h; omega
    · have := ihb h; omega
  | customTy nm tys ih =>
    intro h
    simp only [Ty.freeVars] at h
    simp only [Subst.onTy_customTy, Ty.size]
    obtain ⟨t, ht, hnt⟩ : ∃ t ∈ tys, n ∈ t.freeVars := by
      by_contra hc; push_neg at hc
      exact (TyList.not_mem_freeVars_iff.mpr hc) h
    have h1 := ih t ht hnt
    have h2 : (S.onTy t).size ≤ TyList.size (tys.map S.onTy) :=
      TyList.size_mem_le (List.mem_map.mpr ⟨t, ht, rfl⟩)
    omega
  | bl lo hi e ih =>
    intro h
    simp only [Ty.freeVars] at h
    simp only [Subst.onTy_bl, Ty.size]
    have := ih h; omega

/-- The strict occurs-check: a variable's image is strictly smaller than the
    image of a *compound* type containing it. -/
theorem Ty.size_onTy_fvar_lt {S : Subst} {n : Nat} {b : Ty}
    (hmem : n ∈ b.freeVars) (hne : b ≠ .fvar n) :
    (S.onTy (.fvar n)).size < (S.onTy b).size := by
  cases b with
  | prim p => simp [Ty.freeVars] at hmem
  | bvar i => simp [Ty.freeVars] at hmem
  | fvar m => simp only [Ty.freeVars, List.mem_singleton] at hmem; subst hmem; exact absurd rfl hne
  | arrow a b =>
    simp only [Ty.freeVars, List.mem_dedup, List.mem_append] at hmem
    simp only [Subst.onTy_arrow, Ty.size]
    rcases hmem with h | h
    · have := Ty.size_onTy_fvar_le (S := S) (n := n) h; have := @Ty.size_pos (S.onTy b); omega
    · have := Ty.size_onTy_fvar_le (S := S) (n := n) h; have := @Ty.size_pos (S.onTy a); omega
  | customTy nm tys =>
    simp only [Ty.freeVars] at hmem
    simp only [Subst.onTy_customTy, Ty.size]
    obtain ⟨t, ht, hnt⟩ : ∃ t ∈ tys, n ∈ t.freeVars := by
      by_contra hc; push_neg at hc
      exact (TyList.not_mem_freeVars_iff.mpr hc) hmem
    have h1 := Ty.size_onTy_fvar_le (S := S) (n := n) hnt
    have h2 : (S.onTy t).size ≤ TyList.size (tys.map S.onTy) :=
      TyList.size_mem_le (List.mem_map.mpr ⟨t, ht, rfl⟩)
    omega
  | bl lo hi e =>
    simp only [Ty.freeVars] at hmem
    simp only [Subst.onTy_bl, Ty.size]
    have := Ty.size_onTy_fvar_le (S := S) (n := n) hmem
    omega

/-! ### Scheme weakening (for the `letIn` principality case)

The algorithm generalises the rhs's principal type with `genScheme`, the
*maximal* generalisation; the declarative scheme `M` is less general. Giving the
let-bound variable a more general scheme preserves typing: every instance the
body used is still available. (`PolyTy.Generalizes`, the relation used here and
by `Infer.letRec`'s ceiling premise, is defined earlier, before `Infer`.) -/

/-- Replacing a context scheme `M` by a more general `M'` preserves `TypeOfHM`.
    Direct port of `TypeOfElabHM.weaken_scheme`; the weakened-position `var` case
    (which would be unprovable for `TypeOfElabHM`, since the stored `tyArgs` instantiate
    the OLD scheme) **dissolves** here: `TypeOfHM.var`'s instantiation witness is existential, so
    `hgen` supplies a fresh witness for `M'` while the term keeps its decoration. -/
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
    | letRec hwf hlen hlink hlc hmono heq hbody ihmono ihbody =>
      intro ep hep
      subst heq
      expose_names
      refine TypeOfHM.letRec (specs := specs) (τs := τs) (G := G) (L := L)
        hwf hlen hlink hlc ?_ rfl ?_
      · intro Xs hfresh p hp
        have hc := ihmono Xs hfresh p hp
          ((τs.map RecSpec.mono).map (RecSpec.rhsEntry G Xs) ++ ep)
          (by simp only [RecSpecs.rhsCtx, hep, List.append_assoc])
        simp only [RecSpecs.rhsCtx, List.append_assoc] at hc ⊢
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

/-- Inserting an environment segment and shifting term de Bruijn indices preserves
    `TypeOfHM`. Direct port of `TypeOfElabHM.weaken_env`: cofinite `letIn`/`letRec`
    re-instantiate under the grown env; `var` remaps lookup (existential `instArgs`
    unchanged). No env-freshness side condition. -/
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
  | letRec hwf hlen hlink hlc hmono heq hbody ihmono ihbody =>
    intro env_pre' hctx
    subst heq
    expose_names
    simp only [Expr.shiftFrom, RecGroup.shiftFrom_eq_map]
    refine TypeOfHM.letRec (specs := specs) (τs := τs) (G := G) (L := L)
      ⟨hwf.anns_eq, ?_, hwf.nodup, hwf.mono_lc, hwf.poly_wf⟩
      (by simpa [List.length_map] using hlen) hlink hlc ?_ rfl ?_
    · rw [List.length_map]; exact hwf.length
    · intro Xs hfresh p hp
      obtain ⟨a, t, _, hq, rfl⟩ := List.mem_zip_map_left hp
      have hc := ihmono Xs hfresh (a, t) hq
        ((τs.map RecSpec.mono).map (RecSpec.rhsEntry G Xs) ++ env_pre')
        (by simp only [RecSpecs.rhsCtx]; rw [hctx, List.append_assoc])
      simp only [RecSpecs.rhsCtx, List.length_append, List.length_map] at hc
      rw [← hlen, Nat.add_comm bindings.length env_pre'.length] at hc
      simp only [RecSpecs.rhsCtx, List.append_assoc] at hc ⊢
      exact hc
    · have hb := ihbody (specs.map (RecSpec.bodyScheme G) ++ env_pre')
        (by simp only [RecSpecs.bodyCtx]; rw [hctx, List.append_assoc])
      simp only [RecSpecs.bodyCtx, List.length_append, List.length_map] at hb
      rw [← hwf.length, Nat.add_comm bindings.length env_pre'.length] at hb
      simp only [RecSpecs.bodyCtx, List.append_assoc] at hb ⊢
      exact hb

/-- Build a `Forall₂` from equal lengths and a pointwise (index-indexed) relation. -/
private theorem List.forall₂_of_getElem {α β : Type*} {R : α → β → Prop}
    {l₁ : List α} {l₂ : List β} (hlen : l₁.length = l₂.length)
    (h : ∀ i (h₁ : i < l₁.length) (h₂ : i < l₂.length), R l₁[i] l₂[i]) :
    List.Forall₂ R l₁ l₂ := by
  induction l₁ generalizing l₂ with
  | nil => cases l₂ with | nil => exact .nil | cons => simp at hlen
  | cons a as ih =>
    cases l₂ with
    | nil => simp at hlen
    | cons b bs =>
      refine .cons (h 0 (by simp) (by simp)) (ih (by simpa using hlen) ?_)
      intro i h₁ h₂
      exact h (i + 1) (by simpa using h₁) (by simpa using h₂)


/-! ### `TypeOfHM`/`Step` dynamics metatheory (step 4, checkpoints 2–4)

The substitution-semantics metatheory for `TypeOfHM` on erased terms. This is
the decoration-blind port of `TypeOfElabHM`'s dynamics (subst_lemma / canonical
forms / progress / preservation), specialised to the image of `Expr.erase`:
`letIn` anns are always `none`, `letRec` specs all-`.mono`, `var` tyArgs `[]`,
so the type-passing machinery (`instTy`/`SubstArgsGe`/`TyBvarBounded`) is
vacuous and the cofinite `openTyVars`-commutation bookkeeping never fires. -/

/-- Decoration-blind "value types at scheme `M`": `v` inhabits every instance of
    `M`. The direct analogue of the type-passing `HasScheme` (`Core.lean`), but
    stated with the declarative `Instantiates` (existential instantiation) rather
    than `instTy`/`openWith`. -/
def HasSchemeHM (ctx : Ctx) (v : Expr) (M : PolyTy) : Prop :=
  ∀ τ : Ty, Instantiates M τ → TypeOfHM ctx v τ

/-- Substituting `vs` (each typed at every instance of its scheme `Ms[j]`) for a
    block of `Ms`-typed binders preserves `TypeOfHM`. Decoration-blind port of
    `TypeOfElabHM.subst_lemma_many`, restricted to the image of `Expr.erase`
    (`h_erased`) per the memo §7 load-bearing restriction: erased `var` tyArgs are
    `[]`, `letIn` anns `none`, `letRec` specs all-`.mono`, so the type-passing
    `instTy`/`openTyVars`-commutation machinery is never needed. -/
theorem TypeOfHM.subst_lemma_many
    {ctors : CtorEnv} {env Ms : Env} {vs : List Expr}
    (h_vs : List.Forall₂ (fun v M => HasSchemeHM ⟨env, ctors⟩ v M) vs Ms) :
    ∀ (n : Nat) (e : Expr), e.size ≤ n → ∀ (env_post : Env) (τ : Ty),
      TypeOfHM ⟨env_post ++ Ms ++ env, ctors⟩ e τ →
      e.erase = e →
      TypeOfHM ⟨env_post ++ env, ctors⟩ (e.substN env_post.length vs) τ := by
  have h_len : vs.length = Ms.length := h_vs.length_eq
  intro n
  induction n with
  | zero => intro e he; exact absurd he (Nat.not_le.mpr (Expr.size_pos e))
  | succ n ih =>
    intro e he env_post τ h_body h_erased
    cases h_body with
    | primLitUnit => exact .primLitUnit
    | primLitInt => exact .primLitInt
    | primLitNat => exact .primLitNat
    | primLitChar => exact .primLitChar
    | primBinOpIntAdd => exact .primBinOpIntAdd
    | primBinOpIntSub => exact .primBinOpIntSub
    | primBinOpIntLt htrue hfalse =>
      cases htrue with
      | ctor hlookT hlcT hinstT =>
        cases hfalse with
        | ctor hlookF hlcF hinstF =>
          exact .primBinOpIntLt (.ctor hlookT hlcT hinstT) (.ctor hlookF hlcF hinstF)
    | primBinOpCharLt htrue hfalse =>
      cases htrue with
      | ctor hlookT hlcT hinstT =>
        cases hfalse with
        | ctor hlookF hlcF hinstF =>
          exact .primBinOpCharLt (.ctor hlookT hlcT hinstT) (.ctor hlookF hlcF hinstF)
    | lambda hpc hann heq hbody =>
      subst heq
      expose_names
      simp only [Expr.size] at he
      simp only [Expr.substN]
      have h_la : Expr.lambda none body.erase = Expr.lambda ann body := by
        simpa using h_erased
      injection h_la with h_ann h_bd
      refine TypeOfHM.lambda hpc hann rfl ?_
      have := ih body (by omega) (PolyTy.mkTrivial paramTy :: env_post) bodyTy hbody h_bd
      simpa using this
    | app hf hi =>
      expose_names
      simp only [Expr.size] at he
      simp only [Expr.substN]
      have h_ap : Expr.app f.erase input.erase = Expr.app f input := by
        simpa using h_erased
      injection h_ap with hf_e hi_e
      exact .app (ih _ (by omega) _ _ hf hf_e) (ih _ (by omega) _ _ hi hi_e)
    | letIn hwf hann hcofin heq hbody =>
      subst heq
      expose_names
      simp only [Expr.size] at he
      simp only [Expr.substN]
      have h_li : Expr.letIn none boundExpr.erase body.erase = Expr.letIn ann boundExpr body := by
        simpa using h_erased
      injection h_li with h_ann_none h_be h_bd
      have h_ann : ann = none := h_ann_none.symm
      subst h_ann
      refine TypeOfHM.letIn (M := M) (L := L) hwf hann (fun Xs hfresh => ?_) rfl ?_
      · have hbe := hcofin Xs hfresh
        simp only [Expr.openBoundTyVars] at hbe
        have hih := ih boundExpr (by omega) env_post (M.openVars Xs) hbe h_be
        simpa [Expr.openBoundTyVars] using hih
      · exact ih body (by omega) (M :: env_post) τ hbody h_bd
    | var h_lookup h_lc h_inst =>
      expose_names
      by_cases h_lt : dbl < env_post.length
      · have h_subst : (Expr.var dbl).substN env_post.length vs = .var dbl := by
          simp [Expr.substN, h_lt]
        rw [h_subst]
        refine .var ?_ h_lc h_inst
        show (env_post ++ env)[dbl]? = some polyTy
        rw [List.getElem?_append_left h_lt]
        rw [List.append_assoc, List.getElem?_append_left h_lt] at h_lookup
        exact h_lookup
      · push_neg at h_lt
        by_cases h_in : dbl - env_post.length < vs.length
        · have hMlt : dbl - env_post.length < Ms.length := by omega
          have h_subst : (Expr.var dbl).substN env_post.length vs
              = (vs[dbl - env_post.length]).shiftFrom 0 env_post.length := by
            simp only [Expr.substN]
            rw [if_neg (by omega), dif_pos h_in]
          rw [h_subst]
          rw [List.append_assoc, List.getElem?_append_right h_lt,
              List.getElem?_append_left hMlt, List.getElem?_eq_getElem hMlt,
              Option.some.injEq] at h_lookup
          subst h_lookup
          have hhs : HasSchemeHM ⟨env, ctors⟩ vs[dbl - env_post.length]
              Ms[dbl - env_post.length] := (List.forall₂_iff_get.mp h_vs).2 _ h_in hMlt
          have hv_typed : TypeOfHM ⟨env, ctors⟩ vs[dbl - env_post.length] τ :=
            hhs τ ⟨instArgs, h_lc, h_inst⟩
          exact TypeOfHM.weaken_env (env_pre := []) (env_extra := env_post) hv_typed
        · push_neg at h_in
          have h_subst : (Expr.var dbl).substN env_post.length vs
              = .var (dbl - vs.length) := by
            simp only [Expr.substN]
            rw [if_neg (by omega), dif_neg (by omega)]
          rw [h_subst]
          refine .var ?_ h_lc h_inst
          rw [List.getElem?_append_right (by omega : env_post.length ≤ dbl - vs.length)]
          rw [List.append_assoc, List.getElem?_append_right h_lt,
              List.getElem?_append_right (by omega : Ms.length ≤ dbl - env_post.length)]
            at h_lookup
          rw [show (dbl - vs.length) - env_post.length
                = (dbl - env_post.length) - Ms.length by omega]
          exact h_lookup
    | ctor h_lookup h_lc h_inst => exact .ctor h_lookup h_lc h_inst
    | match_ h_scrut h_ne h_brs =>
      expose_names
      simp only [Expr.size] at he
      simp only [Expr.substN]
      have h_m : Expr.match_ scrutinee.erase
            (branches.map fun pe => (pe.1, pe.2.erase))
          = Expr.match_ scrutinee branches := by
        simpa using h_erased
      injection h_m with h_sc h_bl
      refine TypeOfHM.match_ (ih scrutinee (by omega) env_post scrutTy h_scrut h_sc) ?_ ?_
      · intro hcontra
        obtain ⟨⟨p, b⟩, rest, hb⟩ := List.exists_cons_of_ne_nil h_ne
        have hmem' := BranchList.mem_substN_of_mem
          (k := env_post.length) (vs := vs)
          (hb ▸ List.mem_cons_self (a := (p, b)))
        rw [hcontra] at hmem'
        exact List.not_mem_nil hmem'
      · intro branch' hmem'
        obtain ⟨pat, body, hmem, rfl⟩ := BranchList.mem_substN hmem'
        have hbsize' : body.size ≤ Expr.sizeBranches branches := by
          clear h_ne he h_erased h_brs h_bl hmem'
          induction branches with
          | nil => exact absurd hmem List.not_mem_nil
          | cons hd tl ihs =>
            obtain ⟨p', b'⟩ := hd
            simp only [Expr.sizeBranches]
            rcases List.mem_cons.mp hmem with heq | hmem
            · rw [Prod.mk.injEq] at heq
              obtain ⟨_, rfl⟩ := heq
              omega
            · have := ihs hmem
              omega
        have hbsize : body.size ≤ n := le_trans hbsize' (by omega)
        have hbe_all : ∀ pe ∈ branches, pe.2.erase = pe.2 := by
          intro pe hpe
          have hmem' : pe ∈ branches.map (fun pb => (pb.1, pb.2.erase)) := by
            rw [h_bl]
            exact hpe
          obtain ⟨⟨p', b'⟩, hb_mem, hb⟩ := List.mem_map.mp hmem'
          have hpe' : b'.erase = pe.2 := by
            simpa using congrArg Prod.snd hb
          rw [hpe'.symm]
          exact Expr.erase_idem b'
        have hbe : body.erase = body := hbe_all (pat, body) hmem
        cases pat with
        | named c m =>
          simp only [MatchPattern.bindCount]
          cases h_brs (.named c m, body) hmem with
          | mk hspec h_ctx h_bodyT =>
            subst h_ctx
            expose_names
            rw [show (instContents.map PolyTy.mkTrivial ++ (env_post ++ Ms ++ env))
                  = (instContents.map PolyTy.mkTrivial ++ env_post) ++ Ms ++ env
                  by rw [List.append_assoc, List.append_assoc, List.append_assoc]] at h_bodyT
            have ih_b := ih body hbsize (instContents.map PolyTy.mkTrivial ++ env_post)
              τ h_bodyT hbe
            simp only [List.length_append, List.length_map] at ih_b
            rw [← hspec.fields.length_eq, ← hspec.bind_count] at ih_b
            rw [show m + env_post.length = env_post.length + m from Nat.add_comm _ _] at ih_b
            refine TypeOfMatchBranch.mk ⟨hspec.lookup, hspec.scrut_eq, hspec.arity,
              hspec.bind_count, hspec.fields⟩ rfl ?_
            rw [List.append_assoc] at ih_b
            exact ih_b
        | wildcard =>
          simp only [MatchPattern.bindCount, Nat.add_zero]
          cases h_brs (.wildcard, body) hmem with
          | wildcard h_bodyT =>
            exact TypeOfMatchBranch.wildcard (ih body hbsize env_post τ h_bodyT hbe)
    | letRec hwf hlen hlink hlc hmono heq hbodyT =>
      subst heq
      expose_names
      simp only [Expr.size] at he
      simp only [Expr.substN, RecGroup.substN_eq_map]
      have h_lr : Expr.letRec (bindings.map (fun _ => none)) (bindings.map Expr.erase)
            body.erase
          = Expr.letRec anns bindings body := by
        simpa using h_erased
      injection h_lr with h_anns h_binds h_bd
      refine TypeOfHM.letRec (specs := specs) (τs := τs) (G := G) (L := L)
        ⟨hwf.anns_eq, ?_, hwf.nodup, hwf.mono_lc, hwf.poly_wf⟩
        (by simpa [List.length_map] using hlen) hlink hlc ?_ rfl ?_
      · rw [List.length_map]; exact hwf.length
      · intro Xs hfresh p hp
        obtain ⟨a, t, hmemBind, hq, rfl⟩ := List.mem_zip_map_left hp
        have hbT := hmono Xs hfresh (a, t) hq
        simp only [RecSpecs.rhsCtx] at hbT
        rw [← List.append_assoc, ← List.append_assoc] at hbT
        have hasize' : a.size ≤ Expr.sizeRecGroup bindings := by
          clear h_erased h_anns h_binds hwf hlen hlink hlc hmono he hp hq
          induction bindings with
          | nil => exact absurd hmemBind List.not_mem_nil
          | cons hd tl ihs =>
            simp only [Expr.sizeRecGroup]
            rcases List.mem_cons.mp hmemBind with heq | hmem
            · subst heq
              omega
            · have := ihs hmem
              omega
        have hasize : a.size ≤ n := le_trans hasize' (by omega)
        have hbe : a.erase = a := by
          have hmem' : a ∈ bindings.map Expr.erase := by
            rw [h_binds]
            exact hmemBind
          obtain ⟨b', hb_mem, hb⟩ := List.mem_map.mp hmem'
          rw [← hb]
          exact Expr.erase_idem b'
        have ihb := ih a hasize ((τs.map RecSpec.mono).map (RecSpec.rhsEntry G Xs) ++ env_post)
          (Ty.renameG G Xs t) hbT hbe
        rw [List.append_assoc] at ihb
        simp only [List.length_append, List.length_map] at ihb
        rw [← hlen, Nat.add_comm bindings.length env_post.length] at ihb
        exact ihb
      · -- body
        simp only [RecSpecs.bodyCtx] at hbodyT
        rw [← List.append_assoc, ← List.append_assoc] at hbodyT
        have ihb := ih body (by omega) (specs.map (RecSpec.bodyScheme G) ++ env_post) τ
          hbodyT h_bd
        rw [List.append_assoc] at ihb
        simp only [List.length_append, List.length_map] at ihb
        rw [← hwf.length, Nat.add_comm bindings.length env_post.length] at ihb
        exact ihb

/-- Single-value substitution (`beta`/`letReduce`): the `Ms = [M]`, `vs = [v]`
    instance of `subst_lemma_many`. -/
theorem TypeOfHM.subst_lemma
    {ctors : CtorEnv} {env_post env : Env}
    {e : Expr} {τ : Ty} {M : PolyTy} {v : Expr}
    (h_body : TypeOfHM ⟨env_post ++ [M] ++ env, ctors⟩ e τ)
    (h_v : HasSchemeHM ⟨env, ctors⟩ v M)
    (h_erased : e.erase = e) :
    TypeOfHM ⟨env_post ++ env, ctors⟩ (e.substN env_post.length [v]) τ :=
  TypeOfHM.subst_lemma_many (Ms := [M]) (vs := [v])
    (List.Forall₂.cons h_v List.Forall₂.nil) e.size e (Nat.le_refl _) env_post τ h_body h_erased

/-- `genGroup` at the empty pool is the trivial scheme (local copy of a
    Core-private lemma, needed by the rewrap's `map_bodyScheme_openAt`). -/
private theorem PolyTy.genGroup_nil {t : Ty} : PolyTy.genGroup [] t = PolyTy.mkTrivial t := by
  have hgf : Ty.genFilter [] t = [] := rfl
  have hcl : Ty.closeOver [] t = t := Ty.closeOver_eq_self_of_fresh (by simp)
  simp only [PolyTy.genGroup, hgf, List.length_nil, hcl, PolyTy.mkTrivial]

/-- `openAt` transports the stored annotations pointwise-identically (local copy
    of a Core-private lemma). -/
private theorem RecSpec.map_ann_openAt (G Xs : List Nat) (specs : List RecSpec) :
    (specs.map (RecSpec.openAt G Xs)).map RecSpec.ann = specs.map RecSpec.ann := by
  rw [List.map_map]
  apply List.map_congr_left
  intro s _
  cases s <;> rfl

/-- The transported specs' empty-pool RHS entries are the original specs'
    pool-opened RHS entries (local copy of a Core-private lemma). -/
private theorem RecSpec.map_rhsEntry_openAt (G Xs Zs : List Nat) (specs : List RecSpec) :
    (specs.map (RecSpec.openAt G Xs)).map (RecSpec.rhsEntry [] Zs)
      = specs.map (RecSpec.rhsEntry G Xs) := by
  rw [List.map_map]
  apply List.map_congr_left
  intro s _
  cases s with
  | mono τ =>
    show PolyTy.mkTrivial (Ty.renameG [] Zs (Ty.renameG G Xs τ)) = _
    rw [Ty.renameG_nil_pool]
    rfl
  | poly σ => rfl

/-- The transported specs' empty-pool BODY schemes are ALSO the original specs'
    pool-opened RHS entries (`genGroup [] = mkTrivial`) — the crux of the
    mono-group trick: body env = RHS env after transport (local copy of a
    Core-private lemma). -/
private theorem RecSpec.map_bodyScheme_openAt (G Xs : List Nat) (specs : List RecSpec) :
    (specs.map (RecSpec.openAt G Xs)).map (RecSpec.bodyScheme [])
      = specs.map (RecSpec.rhsEntry G Xs) := by
  rw [List.map_map]
  apply List.map_congr_left
  intro s _
  cases s with
  | mono τ =>
    show PolyTy.genGroup [] (Ty.renameG G Xs τ) = PolyTy.mkTrivial (Ty.renameG G Xs τ)
    exact PolyTy.genGroup_nil
  | poly σ => rfl

/-- The mono-link transports a mono member's spec-membership to the witness
    list: `(e, .mono τ) ∈ bindings.zip specs` plus `hlen`/`hlink` gives
    `(e, τ) ∈ bindings.zip τs`. -/
private theorem mem_zip_mono_link
    {bindings : List Expr} {specs : List RecSpec} {τs : List Ty} {anns : List (Option PolyTy)}
    {G : List Nat}
    (hwf : RecSpecs.WF anns bindings specs G) (hlen : bindings.length = τs.length)
    (hlink : ∀ p ∈ specs.zip τs, ∀ τ, p.1 = .mono τ → p.2 = τ)
    {e : Expr} {τ : Ty} (hmem : (e, RecSpec.mono τ) ∈ bindings.zip specs) :
    (e, τ) ∈ bindings.zip τs := by
  obtain ⟨j, hjp, hpeq⟩ := List.mem_iff_getElem.mp hmem
  have hjl : j < bindings.length :=
    lt_of_lt_of_le hjp (by rw [List.length_zip]; exact min_le_left _ _)
  have hjs : j < specs.length := by rwa [hwf.length] at hjl
  have hjt : j < τs.length := by rwa [hlen] at hjl
  have hfst : bindings[j]'(hjl) = e := by
    have h := congrArg Prod.fst hpeq
    rw [List.getElem_zip] at h
    exact h
  have hsnd : specs[j]'(hjs) = RecSpec.mono τ := by
    have h := congrArg Prod.snd hpeq
    rw [List.getElem_zip] at h
    exact h
  have hpair : (specs[j]'(hjs), τs[j]'(hjt)) ∈ specs.zip τs := by
    refine List.mem_iff_getElem.mpr ⟨j, ?_, ?_⟩
    · rw [List.length_zip]
      exact lt_min hjs hjt
    · rw [List.getElem_zip]
  have hlinkτ : τs[j]'(hjt) = τ :=
    hlink (specs[j]'(hjs), τs[j]'(hjt)) hpair τ (by simpa using hsnd)
  refine List.mem_iff_getElem.mpr ⟨j, ?_, ?_⟩
  · rw [List.length_zip]
    exact lt_min hjl hjt
  · rw [List.getElem_zip]
    exact Prod.ext hfst hlinkτ

/-- Re-wrap a group member: if `e` types at `t` in the all-mono group RHS
    context at a fresh pool opening `G ↦ Xs`, then the re-wrapped
    `letRec (bindings.map (fun _ => none)) bindings e` types at `t` in the
    ambient context. The rewrap erases the annotations (the rule's all-mono
    reification forces all-`none` anns), which is exactly the shape
    preservation's `letRecUnfold` needs (its subject is erased anyway).
    Decoration-blind port of `TypeOfElabHM.rec_rewrap_typed` (the fused
    mono-group trick). -/
theorem TypeOfHM.rec_rewrap_typed
    {ctors : CtorEnv} {env : Env} {anns : List (Option PolyTy)} {bindings : List Expr}
    {specs : List RecSpec} {τs : List Ty} {G L : List Nat}
    (hwf : RecSpecs.WF anns bindings specs G)
    (hlen : bindings.length = τs.length)
    (hlink : ∀ p ∈ specs.zip τs, ∀ τ, p.1 = .mono τ → p.2 = τ)
    (hlc : ∀ t ∈ τs, t.IsLC)
    (hmono : RecSpecs.MonoTypedInit TypeOfHM ⟨env, ctors⟩ bindings τs G L)
    {Xs : List Nat} (hXs : FreshNames L G.length Xs)
    {e : Expr} {t : Ty}
    (hbody : TypeOfHM (RecSpecs.rhsCtx ⟨env, ctors⟩ (τs.map RecSpec.mono) G Xs) e t) :
    TypeOfHM ⟨env, ctors⟩ (.letRec (bindings.map (fun _ => none)) bindings e) t := by
  refine TypeOfHM.letRec
    (specs := (τs.map (Ty.renameG G Xs)).map RecSpec.mono)
    (τs := τs.map (Ty.renameG G Xs))
    (G := []) (L := L ++ Xs)
    ⟨by
      rw [List.map_map]
      change (τs.map (Ty.renameG G Xs)).map (fun x : Ty => RecSpec.ann (RecSpec.mono x))
        = bindings.map (fun _ => none)
      rw [show (fun x : Ty => RecSpec.ann (RecSpec.mono x)) = (fun _ : Ty => none) from by
        funext x
        rfl]
      rw [show bindings.map (fun _ => none) = (τs.map (Ty.renameG G Xs)).map (fun _ => none) from by
        rw [List.map_const', List.map_const', List.length_map]
        rw [hlen.symm]],
     by rw [List.length_map, List.length_map]; exact hlen,
     List.nodup_nil, ?_, ?_⟩
    (by rw [List.length_map]; exact hlen) ?hlink ?hlc ?mono
    (by
      simp only [RecSpecs.bodyCtx, RecSpecs.rhsCtx, RecSpec.bodyScheme, PolyTy.genGroup_nil,
        RecSpec.rhsEntry, List.map_map, Function.comp_apply]
      congr 1
      congr 1
      apply List.map_congr_left
      intro t _
      simp only [Function.comp_apply, RecSpec.bodyScheme, PolyTy.genGroup_nil, RecSpec.rhsEntry])
    hbody
  · -- reified monotypes are LC
    intro τ' hτ'
    obtain ⟨t, ht, hsubst⟩ := List.mem_map.mp hτ'
    injection hsubst with hττ
    rw [← hττ]
    obtain ⟨t₀, ht₀, hteq⟩ := List.mem_map.mp ht
    rw [← hteq]
    exact Ty.renameG_isLC (hlc t₀ ht₀)
  · -- no annotated members in the reification
    intro σ' hσ'
    obtain ⟨t, ht, hsubst⟩ := List.mem_map.mp hσ'
    exact RecSpec.noConfusion hsubst
  · -- mono-link: structurally true (both lists transport pointwise)
    intro p hp τ hτ
    obtain ⟨a, b, hab, rfl⟩ :=
      List.mem_zip_map (l := τs.map RecSpec.mono) (r := τs)
        (f := RecSpec.openAt G Xs) (g := Ty.renameG G Xs)
        (by simpa using hp)
    cases a with
    | poly σ => exact RecSpec.noConfusion hτ
    | mono τ₀ =>
      injection hτ with hττ
      have hb : b = τ₀ := by
        rcases List.mem_iff_getElem.mp hab with ⟨j, hjp, hpeq⟩
        have hjl' : j < (τs.map RecSpec.mono).length :=
          lt_of_lt_of_le hjp (by rw [List.length_zip]; exact min_le_left _ _)
        have hjr : j < τs.length :=
          lt_of_lt_of_le hjp (by rw [List.length_zip]; exact min_le_right _ _)
        have hpeq' : ((τs.map RecSpec.mono)[j]'(hjl'), τs[j]'(hjr)) = (RecSpec.mono τ₀, b) := by
          rw [List.getElem_zip] at hpeq
          exact hpeq
        have h1 : (τs.map RecSpec.mono)[j]'(hjl') = RecSpec.mono τ₀ := by
          exact congrArg Prod.fst hpeq'
        have h2 : τs[j]'(hjr) = τ₀ := by
          rw [List.getElem_map] at h1
          injection h1
        have h3 : b = τs[j]'(hjr) := (congrArg Prod.snd hpeq').symm
        rw [h3, h2]
      rw [hb]
      exact hττ
  · -- witnesses stay LC under the opening
    intro t' ht'
    obtain ⟨t, ht, rfl⟩ := List.mem_map.mp ht'
    exact Ty.renameG_isLC (hlc t ht)
  · -- mono premise at the empty pool: identical opening, RHS env transported
    intro Zs _hZs p hp
    obtain ⟨a, t₀, hab, rfl⟩ :=
      List.mem_zip_map (l := bindings) (r := τs) (f := id) (g := Ty.renameG G Xs)
        (by simpa using hp)
    have hctx : (RecSpecs.rhsCtx ⟨env, ctors⟩
          ((τs.map (Ty.renameG G Xs)).map RecSpec.mono) [] Zs)
        = RecSpecs.rhsCtx ⟨env, ctors⟩ (τs.map RecSpec.mono) G Xs := by
      simp only [RecSpecs.rhsCtx, List.map_map, RecSpec.rhsEntry, PolyTy.mkTrivial,
        Function.comp_apply]
      rfl
    rw [hctx]
    exact hmono Xs hXs (a, t₀) hab

/-- Each re-wrapped member `letRec anns bindings e` inhabits every instance of
    its generalised body scheme `genGroup G τ` (`HasSchemeHM`). Decoration-blind
    port of `TypeOfElabHM.rewrap_hasScheme_mono`; needed by preservation's
    `letRecUnfold` case. -/
theorem TypeOfHM.rewrap_hasSchemeHM_mono
    {ctors : CtorEnv} {env : Env} {anns : List (Option PolyTy)} {bindings : List Expr}
    {specs : List RecSpec} {τs : List Ty} {G L : List Nat}
    (hwf : RecSpecs.WF anns bindings specs G)
    (hlen : bindings.length = τs.length)
    (hlink : ∀ p ∈ specs.zip τs, ∀ τ, p.1 = .mono τ → p.2 = τ)
    (hlc : ∀ t ∈ τs, t.IsLC)
    (hmono : RecSpecs.MonoTypedInit TypeOfHM ⟨env, ctors⟩ bindings τs G L)
    {e : Expr} {τ : Ty} (hmem : (e, RecSpec.mono τ) ∈ bindings.zip specs) :
    HasSchemeHM ⟨env, ctors⟩ (.letRec (bindings.map (fun _ => none)) bindings e)
      (PolyTy.genGroup G τ) := by
  intro τ' hinst
  rcases hinst with ⟨instArgs, hinstLC, hinstTo⟩
  have hτlc : τ.IsLC := hwf.mono_lc τ (List.of_mem_zip hmem).2
  obtain ⟨Xs, hXlen, hXnodup, hXavoid⟩ :=
    exists_fresh_names
      (L ++ G ++ (specs.map RecSpec.monoFreeVars).flatten
        ++ Env.freeVars (specs.map (RecSpec.bodyScheme G) ++ env)
        ++ env.freeVars
        ++ (Expr.letRec anns bindings e).tyFreeVars
        ++ Ty.freeVarsList instArgs ++ ((PolyTy.genGroup G τ).body).freeVars)
      G.length
  have hXL : ∀ x ∈ Xs, x ∉ L := fun x hx hc =>
    hXavoid x hx (by simp [List.mem_append]; tauto)
  have hXfresh : FreshNames L G.length Xs := ⟨hXlen, hXnodup, hXL⟩
  have hdisj : ∀ g ∈ G, g ∉ Xs := fun g hg hc =>
    hXavoid g hc (by simp [List.mem_append]; tauto)
  have hXs_monos : ∀ s ∈ specs, ∀ x ∈ Xs, x ∉ RecSpec.monoFreeVars s := fun s hs x hx hc =>
    hXavoid x hx (by
      have hflat : x ∈ (specs.map RecSpec.monoFreeVars).flatten :=
        List.mem_flatten.mpr ⟨RecSpec.monoFreeVars s, List.mem_map.mpr ⟨s, hs, rfl⟩, hc⟩
      simp [List.mem_append, hflat])
  have hXsτ : ∀ x ∈ Xs, x ∉ τ.freeVars := hXs_monos (RecSpec.mono τ) (List.of_mem_zip hmem).2
  have hXs_env : ∀ x ∈ Xs, x ∉ env.freeVars := fun x hx hc =>
    hXavoid x hx (by simp [List.mem_append]; tauto)
  have hAnn_nil : ∀ (l : List Expr),
      Expr.tyFreeVars.AnnList.tyFreeVars (l.map (fun _ => none)) = [] := by
    intro l
    induction l with
    | nil => rfl
    | cons b rest ih =>
      simp only [List.map_cons, Expr.tyFreeVars.AnnList.tyFreeVars]
      exact ih
  have hXs_e : ∀ x ∈ Xs, x ∉ (Expr.letRec (bindings.map (fun _ => none)) bindings e).tyFreeVars := fun x hx hc =>
    hXavoid x hx (by
      have hmem' : x ∈ (Expr.letRec anns bindings e).tyFreeVars := by
        simp only [Expr.tyFreeVars, List.mem_append] at hc ⊢
        rw [hAnn_nil bindings] at hc
        rcases hc with hc1 | hc3
        · rcases hc1 with hc1' | hc2
          · exact False.elim (List.not_mem_nil hc1')
          · exact Or.inl (Or.inr hc2)
        · exact Or.inr hc3
      simp [List.mem_append, hmem'])
  have hXs_Vs : ∀ x ∈ Xs, x ∉ Ty.freeVarsList instArgs := fun x hx hc =>
    hXavoid x hx (by simp [List.mem_append]; tauto)
  have hXs_M : ∀ x ∈ Xs, x ∉ ((PolyTy.genGroup G τ).body).freeVars := fun x hx hc =>
    hXavoid x hx (by simp [List.mem_append]; tauto)
  have hb : TypeOfHM ⟨env, ctors⟩ (.letRec (bindings.map (fun _ => none)) bindings e)
      (Ty.renameG G Xs τ) :=
    TypeOfHM.rec_rewrap_typed hwf hlen hlink hlc hmono hXfresh
      (hmono Xs hXfresh (e, τ) (mem_zip_mono_link hwf hlen hlink hmem))
  set Xs' := Ty.genFilter Xs (Ty.renameG G Xs τ) with hXsdef
  have hXlen' : Xs'.length = (Ty.genFilter G τ).length := by
    have h := congrArg PolyTy.paramCount (PolyTy.genGroup_renameG hτlc hXlen hwf.nodup hXnodup hdisj hXsτ)
    simp only [PolyTy.genGroup] at h
    rw [hXsdef]
    exact h.symm
  have hXnodup' : Xs'.Nodup := by rw [hXsdef]; unfold Ty.genFilter; exact hXnodup.filter _
  have hGFnodup : (Ty.genFilter G τ).Nodup := by unfold Ty.genFilter; exact hwf.nodup.filter _
  have hGFdisj : ∀ g ∈ Ty.genFilter G τ, g ∉ Xs' := by
    intro g hg hc
    exact hdisj g (Ty.mem_of_mem_genFilter hg) (by rw [hXsdef] at hc; exact Ty.mem_of_mem_genFilter hc)
  have hrewrite : Ty.renameG G Xs τ = Ty.openVars Xs' (Ty.closeOver (Ty.genFilter G τ) τ) := by
    rw [Ty.renameG_eq_genFilter hXlen hwf.nodup hXnodup hdisj hXsτ]
    exact (Ty.openVars_closeOver_rename hτlc hGFnodup hXlen' hGFdisj).symm
  rw [hrewrite] at hb
  have h_lc : ∀ p ∈ Xs'.zip instArgs, Ty.IsLC p.2 := fun p hp => hinstLC p.2 (List.of_mem_zip hp).2
  have hsub := TypeOfHM.typ_substs_preservation (Xs'.zip instArgs)
    (fun p hp => hXs_env p.1 (Ty.mem_of_mem_genFilter (List.of_mem_zip hp).1)) h_lc hb
  have hfix : Expr.substTyFvars (Xs'.zip instArgs) (Expr.letRec (bindings.map (fun _ => none)) bindings e)
      = Expr.letRec (bindings.map (fun _ => none)) bindings e :=
    Expr.substTyFvars_eq_self_of_not_mem_tyFreeVars (by
      intro p hp
      exact hXs_e p.1 (Ty.mem_of_mem_genFilter (List.of_mem_zip hp).1))
  have hreg : (((PolyTy.genGroup G τ).body).openVars Xs').IsLC := TypeOfHM.regular hb
  have hty : Ty.substFvars (Xs'.zip instArgs) (Ty.openVars Xs' (Ty.closeOver (Ty.genFilter G τ) τ)) = τ' := by
    exact Ty.substFvars_zip_openVars_eq (Xs := Xs') (Vs := instArgs) hXnodup'
      (fun X hX => hXs_Vs X (Ty.mem_of_mem_genFilter hX))
      (Ty.closeOver (Ty.genFilter G τ) τ) τ' hinstTo
      (fun X hX => hXs_M X (Ty.mem_of_mem_genFilter hX)) hreg
  rw [hfix, hty] at hsub
  exact hsub

/-! ### Canonical forms + progress (checkpoint 3)

The `TypeOfHM` analogues of `TypeOfElabHM`'s value-inversion lemmas: a *value*
of a given type has a particular syntactic shape, and a closed well-typed term
is a value or takes a step. These only invert the value constructors, so they
are nearly verbatim ports. -/

/-- A well-typed constructor chain has a `wrapArrows … (customTy …)` type: a
    prefix of arrows ending in a `customTy`. -/
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
  | letIn _ _ _ _ _ => cases h_chain
  | var _          => cases h_chain
  | match_ _ _ _ _ => cases h_chain
  | letRec _ _ _ _ _ => cases h_chain

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
  | letIn _ _ _ _ _ => cases h_chain
  | var _ => cases h_chain
  | match_ _ _ _ _ => cases h_chain
  | letRec _ _ _ _ _ => cases h_chain

/-- Progress: a closed, well-typed term is a value or takes a step. -/
theorem TypeOfHM.progress {ctx : Ctx} {e : Expr} {τ : Ty}
    (h_ty : TypeOfHM ctx e τ) (h_closed : ctx.env = [])
    (h_exh : SmallStep.AllMatchesExhaustive ctx.ctors e) :
    SmallStep.IsValue e ∨ ∃ e', SmallStep.Step e e' := by
  open SmallStep in
  suffices H : ∀ (n : Nat) (e : Expr), e.size ≤ n → ∀ (ctx : Ctx) (τ : Ty),
      TypeOfHM ctx e τ → ctx.env = [] → AllMatchesExhaustive ctx.ctors e →
      IsValue e ∨ ∃ e', Step e e' by
    exact H e.size e (Nat.le_refl _) ctx τ h_ty h_closed h_exh
  intro n
  induction n with
  | zero => intro e he; exact absurd he (Nat.not_le.mpr (Expr.size_pos e))
  | succ n ih =>
    intro e hsize ctx τ h_ty h_closed h_exh
    cases h_ty with
    | primLitUnit => exact .inl (.primLit _)
    | primLitInt => exact .inl (.primLit _)
    | primLitNat => exact .inl (.primLit _)
    | primLitChar => exact .inl (.primLit _)
    | primBinOpIntAdd => exact .inl (.primBinOp _)
    | primBinOpIntSub => exact .inl (.primBinOp _)
    | primBinOpIntLt _ _ => exact .inl (.primBinOp _)
    | primBinOpCharLt _ _ => exact .inl (.primBinOp _)
    | ctor _ _ _ => exact .inl (.ctor _)
    | lambda _ _ _ _ => exact .inl (.lambda _ _)
    | var h_lookup _ _ => rw [h_closed] at h_lookup; simp at h_lookup
    | @app _ f _ _ arg h_f h_arg =>
      cases h_exh with
      | app h_exh_f h_exh_arg =>
        simp only [Expr.size] at hsize
        rcases ih f (by omega) ctx _ h_f h_closed h_exh_f with hvf | ⟨f', hf⟩
        · rcases ih arg (by omega) ctx _ h_arg h_closed h_exh_arg with hva | ⟨arg', harg⟩
          · rcases TypeOfHM.canonical_arrow h_f hvf with
                ⟨ann, body, rfl⟩ | hchain | ⟨op, rfl⟩ | ⟨op, v, rfl⟩
            · exact .inr ⟨_, .beta hva⟩
            · exact .inl (.ctorApp hchain hva)
            · -- `f` is a bare primop; applying one value leaves it one arg short → a value
              exact .inl (.primBinOpPartial hva)
            · -- `f` is a partial primop; this application saturates it → δ-step.
              -- Both operands are values of type `int`, hence literals (canonical_int).
              cases hvf with
              | ctorApp hchain _ => nomatch hchain
              | primBinOpPartial hv =>
                cases h_f with
                | app h_pbo h_v =>
                  cases h_pbo with
                  | primBinOpIntAdd =>
                    obtain ⟨m, rfl⟩ := TypeOfHM.canonical_int h_v hv
                    obtain ⟨n, rfl⟩ := TypeOfHM.canonical_int h_arg hva
                    exact .inr ⟨_, .deltaIntAdd⟩
                  | primBinOpIntSub =>
                    obtain ⟨m, rfl⟩ := TypeOfHM.canonical_int h_v hv
                    obtain ⟨n, rfl⟩ := TypeOfHM.canonical_int h_arg hva
                    exact .inr ⟨_, .deltaIntSub⟩
                  | primBinOpIntLt _ _ =>
                    obtain ⟨m, rfl⟩ := TypeOfHM.canonical_int h_v hv
                    obtain ⟨n, rfl⟩ := TypeOfHM.canonical_int h_arg hva
                    exact .inr ⟨_, .deltaIntLt⟩
                  | primBinOpCharLt _ _ =>
                    obtain ⟨a, rfl⟩ := TypeOfHM.canonical_char h_v hv
                    obtain ⟨b, rfl⟩ := TypeOfHM.canonical_char h_arg hva
                    exact .inr ⟨_, .deltaCharLt⟩
          · exact .inr ⟨_, .appArg hvf harg⟩
        · exact .inr ⟨_, .appFn hf⟩
    | letIn _ _ _ _ _ =>
      -- call-by-name: a `let` always steps via `letReduce` (no rhs reduction).
      exact .inr ⟨_, .letReduce⟩
    | @match_ _ scrut scrutTy branches resultTy h_scrut h_ne h_brs =>
      cases h_exh with
      | match_ h_exh_scrut _ h_branch_ty h_match_exh =>
        simp only [Expr.size] at hsize
        rcases ih scrut (by omega) ctx _ h_scrut h_closed h_exh_scrut with hvs | ⟨scrut', hscrut⟩
        · obtain ⟨⟨pat0, body0⟩, rest0, hbeq⟩ := List.exists_cons_of_ne_nil h_ne
          have hb0 : (pat0, body0) ∈ branches := by rw [hbeq]; exact List.mem_cons_self
          by_cases hchain : IsCtorChain scrut
          · rcases (Expr.rec_strong
                (motive := fun e => IsCtorChain e → ∃ name args, CtorAppliedTo e name args)
                (fun _ h => by cases h)
                (fun _ h => by cases h)
                (fun _ _ _ => by intro h; cases h)
                (fun f v ihf _ => by
                  intro h
                  cases h with
                  | app hf _ =>
                    obtain ⟨name, args, hca⟩ := ihf hf
                    exact ⟨name, args ++ [v], .step hca⟩)
                (fun _ _ _ _ _ => by intro h; cases h)
                (fun _ => by intro h; cases h)
                (fun nm => by
                  intro h
                  cases h
                  exact ⟨nm, [], .base nm⟩)
                (fun _ _ _ _ => by intro h; cases h)
                (fun _ _ _ _ _ => by intro h; cases h)
                scrut hchain) with ⟨name, args, hcat⟩
            have hcover : ∃ pat body, (pat, body) ∈ branches ∧
                pat.matchesCtor name args.length = true := by
              cases pat0 with
              | wildcard => exact ⟨.wildcard, body0, hb0, rfl⟩
              | named c0 n0 =>
                cases h_brs (.named c0 n0, body0) hb0 with
                | mk hspec0 _ _ =>
                  obtain ⟨name', args', ctor, tyArgs', consumed, remaining,
                    hcat', hlook, _, hcontents, hforall, hinst⟩ :=
                    TypeOfHM.ctor_chain_inversion hchain h_scrut
                  obtain ⟨rfl, rfl⟩ : name = name' ∧ args = args' := by
                    exact CtorAppliedTo.det hcat hcat'
                  cases remaining with
                  | cons d rest =>
                    simp only [Ty.wrapArrows] at hinst
                    rw [hspec0.scrut_eq] at hinst; cases hinst
                  | nil =>
                    simp only [Ty.wrapArrows] at hinst
                    rw [List.append_nil] at hcontents
                    have hlen : args.length = ctor.contents.length := by
                      rw [hcontents]; exact hforall.length_eq
                    obtain ⟨ctorB, hlookB, htyB⟩ := h_branch_ty c0 n0 body0 hb0
                    cases hinst with
                    | customTy _ =>
                      obtain ⟨pat, body, hmem, hcov⟩ := h_match_exh name ctor hlook (by
                        injection hspec0.scrut_eq with hn _
                        rw [hn, Option.some.inj (hspec0.lookup.symm.trans hlookB)]; exact htyB)
                      exact ⟨pat, body, hmem, by rw [hlen]; exact hcov⟩
            obtain ⟨pat, body, hmem, hcov⟩ := hcover
            obtain ⟨e', hfmb⟩ := findMatchingBranch_of_exists ⟨pat, body, hmem, hcov⟩
            rcases (List.rec
              (motive := fun l => findMatchingBranch name args l = some e' →
                  ∃ pat body, FirstMatchingBranch name args.length l pat body ∧
                    e' = body.substN 0 (args.take pat.bindCount))
              (fun h => by simp [findMatchingBranch] at h)
              (fun hd tl ih => by
                obtain ⟨pat, body⟩ := hd
                intro h
                simp only [findMatchingBranch] at h
                split at h
                · rename_i hm
                  simp at h
                  exact ⟨pat, body, .here hm, h.symm⟩
                · rename_i hnm
                  obtain ⟨p, b, hfirst, heq⟩ := ih h
                  exact ⟨p, b, .there ((Bool.not_eq_true _).mp hnm) hfirst, heq⟩)
              branches hfmb) with ⟨pat', body', hfirst, _⟩
            exact .inr ⟨_, .matchReduce hvs hcat hfirst⟩
          · have hwild : pat0 = .wildcard := by
              cases pat0 with
              | wildcard => rfl
              | named c0 n0 =>
                cases h_brs (.named c0 n0, body0) hb0 with
                | mk hspecA _ _ =>
                  exact absurd (TypeOfHM.canonical_customTy (hspecA.scrut_eq ▸ h_scrut) hvs) hchain
            subst hwild
            rw [hbeq]
            exact .inr ⟨body0, .matchWildReduce hvs hchain⟩
        · exact .inr ⟨_, .matchScrut hscrut⟩
    | letRec _ _ _ _ _ => exact .inr ⟨_, .letRecUnfold⟩

/-! ### Preservation + type safety (checkpoint 4)

The `TypeOfHM`/`Step` subject-reduction tower, stated for erased terms (`h_erased`)
per the memo §7 restriction. -/

/-- Instantiation of a closed type is trivial: if `ty` has no bound variables,
    any `InstantiatesBy` instance of it forces the instance to equal `ty`. -/
theorem InstantiatesBy.eq_of_closed {tyArgs : List Ty} {ty τ : Ty}
    (h : ContainsBvarsUpTo 0 ty) (hinst : InstantiatesBy tyArgs ty τ) : τ = ty := by
  induction ty using Ty.rec_strong generalizing τ with
  | prim p =>
      cases hinst
      rfl
  | arrow a b iha ihb =>
      cases h with
      | arrow ha hb =>
          cases hinst with
          | arrow hinstA hinstB =>
              rw [iha ha hinstA, ihb hb hinstB]
  | bvar i =>
      cases h with
      | bvar hlt => exact absurd hlt (by omega)
  | fvar n =>
      cases hinst
      rfl
  | customTy nm tys ih =>
      cases h with
      | customTy hall =>
          cases hinst with
          | customTy hforall =>
              refine congrArg (Ty.customTy nm) ?_
              revert hall
              induction hforall with
              | nil => intro hall; rfl
              | cons hhd htl ihtl =>
                  rename_i a b l₁ l₂
                  intro hall
                  rw [List.cons.injEq]
                  constructor
                  · exact ih a List.mem_cons_self (hall a List.mem_cons_self) hhd
                  · exact ihtl (fun t ht => ih t (List.mem_cons_of_mem _ ht))
                      (fun ty hty => hall ty (List.mem_cons_of_mem _ hty))
  | bl lo hi e ih =>
      cases h with
      | bl he =>
          cases hinst with
          | bl hinstElem =>
              exact congrArg (Ty.bl lo hi) (ih he hinstElem)

/-- A well-typed value inhabits every instance of its trivial scheme
    (`mkTrivial τ`): instantiation of the closed `τ` is trivial. -/
theorem HasSchemeHM.ofTypeOfHM {ctx : Ctx} {v : Expr} {τ : Ty}
    (h : TypeOfHM ctx v τ) : HasSchemeHM ctx v (PolyTy.mkTrivial τ) := by
  intro τ' hinst
  rcases hinst with ⟨instArgs, hinstLC, hinstTo⟩
  have hclosed : ContainsBvarsUpTo 0 τ := TypeOfHM.regular h
  have hτ' : τ' = τ := InstantiatesBy.eq_of_closed hclosed hinstTo
  rw [hτ']
  exact h

/-- Assemble the per-argument `HasSchemeHM` list for the `match` reduction: each
    matched argument is well-typed at the corresponding instantiated field type
    (the two instantiations coincide by `det_agree`), so it has the trivial
    scheme of that type. -/
private theorem InstantiatesBy.build_match_vs
    {ctx : Ctx} {n : Nat} {tyArgs tyArgsS : List Ty}
    (hag : ∀ k, k < n → tyArgs[k]? = tyArgsS[k]?) :
    ∀ {contents instContents : List Ty} {args : List Expr},
      (∀ c ∈ contents, ContainsBvarsUpTo n c) →
      List.Forall₂ (InstantiatesBy tyArgs) contents instContents →
      List.Forall₂ (fun a c => ∃ ct, InstantiatesBy tyArgsS c ct ∧ TypeOfHM ctx a ct)
        args contents →
      List.Forall₂ (fun v M => HasSchemeHM ctx v M) args (instContents.map PolyTy.mkTrivial) := by
  intro contents
  induction contents with
  | nil =>
    intro instContents args _ hinst hfor
    cases hinst
    cases hfor
    exact .nil
  | cons hd tl ih =>
    intro instContents args hbound hinst hfor
    cases hinst with
    | cons hihd hitl =>
      cases hfor with
      | cons hfhd hftl =>
        obtain ⟨ct, hctS, htyA⟩ := hfhd
        have hdet := InstantiatesBy.det_agree hag (hbound hd List.mem_cons_self) hihd hctS
        refine List.Forall₂.cons ?_
          (ih (fun c hc => hbound c (List.mem_cons_of_mem _ hc)) hitl hftl)
        rw [hdet]
        exact HasSchemeHM.ofTypeOfHM htyA

/-- `erase` preserves match-exhaustiveness: it drops only type annotations,
    never a match's patterns or the ctor env, so coverage is unchanged. -/
theorem SmallStep.AllMatchesExhaustive.erase {ctors : CtorEnv} {e : Expr}
    (h : SmallStep.AllMatchesExhaustive ctors e) :
    SmallStep.AllMatchesExhaustive ctors (e.erase) := by
  induction e using Expr.rec_strong with
  | primLit p => simp only [Expr.erase]; exact .primLit
  | primBinOp op => simp only [Expr.erase]; exact .primBinOp
  | var i  => simp only [Expr.erase_var]; exact .var
  | ctor nm => simp only [Expr.erase]; exact .ctor
  | lambda ann body ih =>
    cases h with | lambda hb => simp only [Expr.erase_lambda]; exact .lambda (ih hb)
  | app f arg ihf iharg =>
    cases h with | app hf ha => simp only [Expr.erase_app]; exact .app (ihf hf) (iharg ha)
  | letIn ann rhs body ihr ihb =>
    cases h with | letIn hr hb => simp only [Expr.erase_letIn]; exact .letIn (ihr hr) (ihb hb)
  | match_ scrut branches ihs ihbr =>
    have hbodies : ∀ {brs : List (MatchPattern × Expr)},
        (∀ pat e, (pat, e) ∈ brs → AllMatchesExhaustive ctors e →
          AllMatchesExhaustive ctors e.erase) →
        AllBranchBodiesExhaustive ctors brs →
        AllBranchBodiesExhaustive ctors (brs.map (fun pe => (pe.1, pe.2.erase))) := by
      intro brs
      induction brs with
      | nil => intro ih h; cases h; exact .nil
      | cons hd tl ih_tl =>
        intro ih h
        obtain ⟨pat, body⟩ := hd
        cases h with
        | cons hbody hrest =>
          simp only [List.map_cons]
          exact .cons (ih pat body List.mem_cons_self hbody)
            (ih_tl (fun p e hm hae => ih p e (List.mem_cons_of_mem _ hm) hae) hrest)
    cases h with
    | match_ hscrut hbranches hpinned hcover =>
      expose_names
      simp only [Expr.erase_match]
      refine .match_ (tyName := tyName) (ihs hscrut) (hbodies ihbr hbranches)
        (fun c n body hmem => by
          obtain ⟨pe, hpe, heq⟩ := List.mem_map.mp hmem
          cases pe with | mk p b =>
          simp only [Prod.mk.injEq] at heq
          obtain ⟨rfl, hb⟩ := heq
          exact hpinned c n b hpe)
        (fun ctorName ctor hlook htyn => by
          obtain ⟨pat, body, hmem, hcov⟩ := hcover ctorName ctor hlook htyn
          exact ⟨pat, body.erase,
            List.mem_map_of_mem (f := fun pe => (pe.1, pe.2.erase)) hmem, hcov⟩)
  | letRec anns bindings body ihbs ihb =>
    cases h with
    | letRec hbs hb =>
      simp only [Expr.erase_letRec]
      refine .letRec ?_ (ihb hb)
      intro e' he'
      obtain ⟨e0, he0, rfl⟩ := List.mem_map.mp he'
      exact ihbs e0 he0 (hbs e0 he0)

/-- Bounds-erasing the ctor env preserves match-exhaustiveness: `eraseBounds`
    preserves `tyName` and `contents.length`, and the term's match structure is
    untouched. -/
theorem SmallStep.AllMatchesExhaustive.eraseCtorBounds {ctors : CtorEnv} {e : Expr}
    (h : SmallStep.AllMatchesExhaustive ctors e) :
    SmallStep.AllMatchesExhaustive (CtorEnv.eraseBounds ctors) e := by
  induction e using Expr.rec_strong with
  | primLit p => exact .primLit
  | primBinOp op => exact .primBinOp
  | var i  => exact .var
  | ctor nm => exact .ctor
  | lambda ann body ih =>
    cases h with | lambda hb => exact .lambda (ih hb)
  | app f arg ihf iharg =>
    cases h with | app hf ha => exact .app (ihf hf) (iharg ha)
  | letIn ann rhs body ihr ihb =>
    cases h with | letIn hr hb => exact .letIn (ihr hr) (ihb hb)
  | match_ scrut branches ihs ihbr =>
    have hbodies : ∀ {brs : List (MatchPattern × Expr)},
        (∀ pat e, (pat, e) ∈ brs → AllMatchesExhaustive ctors e →
          AllMatchesExhaustive (CtorEnv.eraseBounds ctors) e) →
        AllBranchBodiesExhaustive ctors brs →
        AllBranchBodiesExhaustive (CtorEnv.eraseBounds ctors) brs := by
      intro brs
      induction brs with
      | nil => intro ih h; cases h; exact .nil
      | cons hd tl ih_tl =>
        intro ih h
        obtain ⟨pat, body⟩ := hd
        cases h with
        | cons hbody hrest =>
          exact .cons (ih pat body List.mem_cons_self hbody)
            (ih_tl (fun p e hm hae => ih p e (List.mem_cons_of_mem _ hm) hae) hrest)
    cases h with
    | match_ hscrut hbranches hpinned hcover =>
      expose_names
      refine .match_ (tyName := tyName) (ihs hscrut) (hbodies ihbr hbranches)
        (fun c n body hmem => by
          obtain ⟨ctor, hget, hty⟩ := hpinned c n body hmem
          refine ⟨Ctor.eraseBounds ctor, ?_, ?_⟩
          · rw [CtorEnv.eraseBounds_get?]
            simp [hget]
          · simpa [Ctor.eraseBounds_tyName] using hty)
        (fun ctorName ctor' hlook htyName => by
          rw [CtorEnv.eraseBounds_get?] at hlook
          cases hg : LookupList.get? ctors ctorName with
          | none => simp [hg] at hlook
          | some ctor =>
            simp [hg] at hlook
            have hty : ctor.tyName = tyName := by
              rw [← Ctor.eraseBounds_tyName, hlook]
              exact htyName
            obtain ⟨pat, body, hmem, hcov⟩ := hcover ctorName ctor hg hty
            refine ⟨pat, body, hmem, ?_⟩
            · rw [← hlook, Ctor.eraseBounds_contents, List.length_map]
              exact hcov)
  | letRec anns bindings body ihbs ihb =>
    cases h with
    | letRec hbs hb =>
      refine .letRec ?_ (ihb hb)
      intro e' he'
      exact ihbs e' he' (hbs e' he')

/-- `Step` preserves erasedness: an erased term steps to an erased term. -/
theorem SmallStep.Step.preserves_erased {e e' : Expr}
    (h_erased : e.erase = e) (h_step : SmallStep.Step e e') : e'.erase = e' := by
  have expr_shiftFrom_erase : ∀ (threshold n : Nat) (e : Expr),
      e.erase = e → (e.shiftFrom threshold n).erase = e.shiftFrom threshold n := by
    intro threshold n e
    revert threshold n
    induction e using Expr.rec_strong with
    | primLit p =>
        intro threshold n h_erased
        simp [Expr.shiftFrom, Expr.erase]
    | primBinOp op =>
        intro threshold n h_erased
        simp [Expr.shiftFrom, Expr.erase]
    | ctor c =>
        intro threshold n h_erased
        simp [Expr.shiftFrom, Expr.erase]
    | var i =>
        intro threshold n h_erased
        simp only [Expr.erase, Expr.shiftFrom]
        split <;> simp [Expr.erase_var]
    | lambda ann body ih =>
        intro threshold n h_erased
        have h_la : Expr.lambda none body.erase = Expr.lambda ann body := by simpa using h_erased
        injection h_la with h_ann h_bd
        simp only [Expr.shiftFrom]
        rw [show ann = none from h_ann.symm]
        rw [Expr.erase_lambda]
        congr 1
        exact ih (threshold + 1) n h_bd
    | app f arg ihf iha =>
        intro threshold n h_erased
        have h_ap : Expr.app f.erase arg.erase = Expr.app f arg := by simpa using h_erased
        injection h_ap with hf_e ha_e
        simp only [Expr.shiftFrom, Expr.erase_app]
        congr 1
        · exact ihf threshold n hf_e
        · exact iha threshold n ha_e
    | letIn ann rhs body ihr ihb =>
        intro threshold n h_erased
        have h_li : Expr.letIn none rhs.erase body.erase = Expr.letIn ann rhs body := by simpa using h_erased
        injection h_li with h_ann_none h_re h_bd
        have h_ann : ann = none := h_ann_none.symm
        subst h_ann
        simp only [Expr.shiftFrom, Expr.erase_letIn]
        congr 1
        · exact ihr threshold n h_re
        · exact ihb (threshold + 1) n h_bd
    | match_ scrut branches ihs ihbs =>
        intro threshold n h_erased
        have h_m : Expr.match_ scrut.erase (branches.map fun pe => (pe.1, pe.2.erase))
            = Expr.match_ scrut branches := by simpa using h_erased
        injection h_m with h_sc h_bl
        have hbe_all : ∀ pe ∈ branches, pe.2.erase = pe.2 := by
          intro pe hpe
          have hmem' : pe ∈ branches.map (fun pb => (pb.1, pb.2.erase)) := by
            rw [h_bl]
            exact hpe
          obtain ⟨⟨p', b'⟩, hb_mem, hb⟩ := List.mem_map.mp hmem'
          have hpe' : b'.erase = pe.2 := by simpa using congrArg Prod.snd hb
          rw [hpe'.symm]
          exact Expr.erase_idem b'
        simp only [Expr.shiftFrom, Expr.erase_match]
        congr 1
        · exact ihs threshold n h_sc
        · exact List.map_eq_self_of_forall_eq_id (fun pe : MatchPattern × Expr => (pe.1, pe.2.erase)) _ (by
            intro pe hpe
            obtain ⟨pat, body, hmem, rfl⟩ := BranchList.mem_shiftFrom hpe
            simpa using congrArg (fun b => (pat, b))
              (ihbs pat body hmem (threshold + pat.bindCount) n (hbe_all (pat, body) hmem)))
    | letRec anns bindings body ihbs ihb =>
        intro threshold n h_erased
        have h_lr : Expr.letRec (bindings.map (fun _ => none)) (bindings.map Expr.erase) body.erase
            = Expr.letRec anns bindings body := by simpa using h_erased
        injection h_lr with h_anns h_binds h_bd
        have hbe_all : ∀ b, b ∈ bindings → b.erase = b := by
          intro b hmem
          have hmem' : b ∈ bindings.map Expr.erase := by
            rw [h_binds]
            exact hmem
          obtain ⟨b', hb_mem, hb⟩ := List.mem_map.mp hmem'
          rw [← hb]
          exact Expr.erase_idem b'
        have hmap : ∀ (k : Nat) (l : List Expr), RecGroup.shiftFrom k n l = l.map (fun e => e.shiftFrom k n) := by
          intro k l
          induction l with
          | nil => rfl
          | cons b rest ih2 =>
            simp only [RecGroup.shiftFrom, List.map_cons, ih2]
        have hanns' : (RecGroup.shiftFrom (threshold + bindings.length) n bindings).map (fun _ : Expr => (none : Option PolyTy))
            = bindings.map (fun _ : Expr => (none : Option PolyTy)) := by
          rw [hmap, List.map_map]
          rfl
        have hbinds_shift : (RecGroup.shiftFrom (threshold + bindings.length) n bindings).map Expr.erase
            = RecGroup.shiftFrom (threshold + bindings.length) n bindings := by
          rw [hmap, List.map_map]
          apply List.map_congr_left
          intro b hmem
          simpa using (ihbs b hmem (threshold + bindings.length) n (hbe_all b hmem))
        simp only [Expr.shiftFrom]
        rw [Expr.erase_letRec, hanns', h_anns, hbinds_shift]
        congr 1
        exact ihb (threshold + bindings.length) n h_bd
  have expr_substN_erase : ∀ (k : Nat) (vs : List Expr) (e : Expr),
      e.erase = e → (∀ v ∈ vs, v.erase = v) → (e.substN k vs).erase = e.substN k vs := by
    intro k vs e
    revert k vs
    induction e using Expr.rec_strong with
    | primLit p =>
        intro k vs h_erased hvs
        simp [Expr.substN, Expr.erase]
    | primBinOp op =>
        intro k vs h_erased hvs
        simp [Expr.substN, Expr.erase]
    | ctor c =>
        intro k vs h_erased hvs
        simp [Expr.substN, Expr.erase]
    | var i =>
        intro k vs h_erased hvs
        simp only [Expr.substN, Expr.erase]
        split
        · simp [Expr.erase_var]
        · split
          · next h_in =>
              show (vs[i - k].shiftFrom 0 k).erase = vs[i - k].shiftFrom 0 k
              rw [expr_shiftFrom_erase 0 k (vs[i - k])
                (hvs (vs[i - k]) (List.getElem_mem h_in))]
          · simp [Expr.erase_var]
    | lambda ann body ih =>
        intro k vs h_erased hvs
        have h_la : Expr.lambda none body.erase = Expr.lambda ann body := by simpa using h_erased
        injection h_la with h_ann h_bd
        simp only [Expr.substN]
        rw [show ann = none from h_ann.symm]
        rw [Expr.erase_lambda]
        congr 1
        exact ih (k + 1) vs h_bd hvs
    | app f arg ihf iha =>
        intro k vs h_erased hvs
        have h_ap : Expr.app f.erase arg.erase = Expr.app f arg := by simpa using h_erased
        injection h_ap with hf_e ha_e
        simp only [Expr.substN, Expr.erase_app]
        congr 1
        · exact ihf k vs hf_e hvs
        · exact iha k vs ha_e hvs
    | letIn ann rhs body ihr ihb =>
        intro k vs h_erased hvs
        have h_li : Expr.letIn none rhs.erase body.erase = Expr.letIn ann rhs body := by simpa using h_erased
        injection h_li with h_ann_none h_re h_bd
        have h_ann : ann = none := h_ann_none.symm
        subst h_ann
        simp only [Expr.substN, Expr.erase_letIn]
        congr 1
        · exact ihr k vs h_re hvs
        · exact ihb (k + 1) vs h_bd hvs
    | match_ scrut branches ihs ihbs =>
        intro k vs h_erased hvs
        have h_m : Expr.match_ scrut.erase (branches.map fun pe => (pe.1, pe.2.erase))
            = Expr.match_ scrut branches := by simpa using h_erased
        injection h_m with h_sc h_bl
        have hbe_all : ∀ pe ∈ branches, pe.2.erase = pe.2 := by
          intro pe hpe
          have hmem' : pe ∈ branches.map (fun pb => (pb.1, pb.2.erase)) := by
            rw [h_bl]
            exact hpe
          obtain ⟨⟨p', b'⟩, hb_mem, hb⟩ := List.mem_map.mp hmem'
          have hpe' : b'.erase = pe.2 := by simpa using congrArg Prod.snd hb
          rw [hpe'.symm]
          exact Expr.erase_idem b'
        simp only [Expr.substN, Expr.erase_match]
        congr 1
        · exact ihs k vs h_sc hvs
        · exact List.map_eq_self_of_forall_eq_id (fun pe : MatchPattern × Expr => (pe.1, pe.2.erase)) _ (by
            intro pe hpe
            obtain ⟨pat, body, hmem, rfl⟩ := BranchList.mem_substN hpe
            simpa using congrArg (fun b => (pat, b))
              (ihbs pat body hmem (k + pat.bindCount) vs (hbe_all (pat, body) hmem) hvs))
    | letRec anns bindings body ihbs ihb =>
        intro k vs h_erased hvs
        have h_lr : Expr.letRec (bindings.map (fun _ => none)) (bindings.map Expr.erase) body.erase
            = Expr.letRec anns bindings body := by simpa using h_erased
        injection h_lr with h_anns h_binds h_bd
        have hbe_all : ∀ b, b ∈ bindings → b.erase = b := by
          intro b hmem
          have hmem' : b ∈ bindings.map Expr.erase := by
            rw [h_binds]
            exact hmem
          obtain ⟨b', hb_mem, hb⟩ := List.mem_map.mp hmem'
          rw [← hb]
          exact Expr.erase_idem b'
        have hanns' : (RecGroup.substN (k + bindings.length) vs bindings).map (fun _ : Expr => (none : Option PolyTy))
            = bindings.map (fun _ : Expr => (none : Option PolyTy)) := by
          rw [RecGroup.substN_eq_map, List.map_map]
          rfl
        have hbinds_subst : (RecGroup.substN (k + bindings.length) vs bindings).map Expr.erase
            = RecGroup.substN (k + bindings.length) vs bindings := by
          rw [RecGroup.substN_eq_map, List.map_map]
          apply List.map_congr_left
          intro b hmem
          simpa using (ihbs b hmem (k + bindings.length) vs (hbe_all b hmem) hvs)
        simp only [Expr.substN]
        rw [Expr.erase_letRec, hanns', h_anns, hbinds_subst]
        congr 1
        exact ihb (k + bindings.length) vs h_bd hvs
  induction h_step with
  | beta hval =>
      rename_i ann body v
      have h_ap : Expr.app (Expr.lambda none body.erase) v.erase = Expr.app (Expr.lambda ann body) v := by
        simpa using h_erased
      injection h_ap with h_lam h_v
      injection h_lam with h_ann h_bd
      exact expr_substN_erase 0 [v] body h_bd (by
        intro x hx
        rw [List.mem_singleton] at hx
        subst hx
        exact h_v)
  | letReduce =>
      rename_i ann rhs body
      have h_li : Expr.letIn none rhs.erase body.erase = Expr.letIn ann rhs body := by simpa using h_erased
      injection h_li with h_ann h_rhs h_bd
      exact expr_substN_erase 0 [rhs] body h_bd (by
        intro x hx
        rw [List.mem_singleton] at hx
        subst hx
        exact h_rhs)
  | deltaIntAdd => simp [Expr.erase]
  | deltaIntSub => simp [Expr.erase]
  | deltaIntLt => simp [Expr.erase]
  | deltaCharLt => simp [Expr.erase]
  | matchReduce hval hctor hfirst =>
      rename_i scrut branches name args pat body
      have h_m : Expr.match_ scrut.erase (branches.map fun pe => (pe.1, pe.2.erase))
          = Expr.match_ scrut branches := by simpa using h_erased
      injection h_m with h_sc h_bl
      have hbe_all : ∀ pe ∈ branches, pe.2.erase = pe.2 := by
        intro pe hpe
        have hmem' : pe ∈ branches.map (fun pb => (pb.1, pb.2.erase)) := by
          rw [h_bl]
          exact hpe
        obtain ⟨⟨p', b'⟩, hb_mem, hb⟩ := List.mem_map.mp hmem'
        have hpe' : b'.erase = pe.2 := by simpa using congrArg Prod.snd hb
        rw [hpe'.symm]
        exact Expr.erase_idem b'
      have hb : body.erase = body := hbe_all (pat, body) hfirst.mem
      have hargs_erased : ∀ a, a ∈ args → a.erase = a := by
        intro a ha
        clear hval hfirst h_erased
        induction hctor generalizing a with
        | base _ =>
            simp at ha
        | step hf ih =>
            simp [Expr.erase_app] at h_sc
            rcases h_sc with ⟨hf_e, ha_e⟩
            simp only [List.mem_append, List.mem_singleton] at ha
            rcases ha with ha' | rfl
            · exact ih hf_e a ha'
            · exact ha_e
      exact expr_substN_erase 0 (args.take pat.bindCount) body hb (by
        intro v hv
        exact hargs_erased v (List.mem_of_mem_take hv))
  | matchWildReduce hval hnc =>
      rename_i scrut body rest
      have h_m : Expr.match_ scrut.erase (((.wildcard, body) :: rest).map fun pe => (pe.1, pe.2.erase))
          = Expr.match_ scrut ((.wildcard, body) :: rest) := by simpa using h_erased
      injection h_m with h_sc h_bl
      have hb : body.erase = body := by
        have hmem' : (.wildcard, body) ∈ ((.wildcard, body) :: rest).map (fun pb => (pb.1, pb.2.erase)) := by
          rw [h_bl]
          exact List.mem_cons_self
        obtain ⟨⟨p', b'⟩, hb_mem, hb⟩ := List.mem_map.mp hmem'
        have hpe' : b'.erase = body := by simpa using congrArg Prod.snd hb
        rw [hpe'.symm]
        exact Expr.erase_idem b'
      exact hb
  | appFn _ ih =>
      simp [Expr.erase_app] at h_erased
      rcases h_erased with ⟨hf_e, ha_e⟩
      simp [Expr.erase_app, ih hf_e, ha_e]
  | appArg hv _ ih =>
      simp [Expr.erase_app] at h_erased
      rcases h_erased with ⟨hv_e, ha_e⟩
      simp [Expr.erase_app, hv_e, ih ha_e]
  | matchScrut _ ih =>
      simp [Expr.erase_match] at h_erased
      rcases h_erased with ⟨h_sc, h_bl⟩
      simp [Expr.erase_match, ih h_sc, h_bl]
  | letRecUnfold =>
      rename_i anns bindings body
      have h_lr : Expr.letRec (bindings.map (fun _ => none)) (bindings.map Expr.erase) body.erase
          = Expr.letRec anns bindings body := by simpa using h_erased
      injection h_lr with h_anns h_binds h_bd
      have hbe : ∀ b, b ∈ bindings → b.erase = b := by
        intro b hmem
        have hmem' : b ∈ bindings.map Expr.erase := by
          rw [h_binds]
          exact hmem
        obtain ⟨b', hb_mem, hb⟩ := List.mem_map.mp hmem'
        rw [← hb]
        exact Expr.erase_idem b'
      have hvs_erased : ∀ v, v ∈ bindings.map (fun e => Expr.letRec anns bindings e) → v.erase = v := by
        intro v hv
        obtain ⟨e', he', rfl⟩ := List.mem_map.mp hv
        simp only [Expr.erase_letRec]
        rw [h_anns, h_binds, hbe e' he']
      exact expr_substN_erase 0 (bindings.map (fun e => Expr.letRec anns bindings e)) body h_bd hvs_erased
theorem TypeOfHM.preservation {ctx : Ctx} {e e' : Expr} {τ : Ty}
    (h_step : SmallStep.Step e e') (h_ty : TypeOfHM ctx e τ) (h_erased : e.erase = e) :
    TypeOfHM ctx e' τ := by
  induction h_step generalizing τ with
  | beta hval =>
    cases h_ty with
    | app hf hi =>
      cases hf with
      | lambda hpc _ heq hbody =>
        subst heq
        simp [Expr.erase_app, Expr.erase_lambda] at h_erased
        rcases h_erased with ⟨h_e1, _⟩
        rcases h_e1 with ⟨_, h_bd⟩
        exact TypeOfHM.subst_lemma (env_post := []) (M := PolyTy.mkTrivial _)
          hbody (HasSchemeHM.ofTypeOfHM hi) h_bd
  | letReduce =>
    cases h_ty with
    | letIn hwf _ hcofin heq hbody =>
      subst heq
      simp [Expr.erase_letIn] at h_erased
      rcases h_erased with ⟨h_ann, h_re, h_bd⟩
      exact TypeOfHM.subst_lemma (env_post := []) hbody
        (fun τ' hinst => GeneralisesTo_inst (by simpa [h_ann.symm] using hcofin) hinst) h_bd
  | deltaIntAdd =>
    cases h_ty with
    | app h_f _ => cases h_f with
      | app h_pbo _ => cases h_pbo; exact .primLitInt
  | deltaIntSub =>
    cases h_ty with
    | app h_f _ => cases h_f with
      | app h_pbo _ => cases h_pbo; exact .primLitInt
  | deltaIntLt =>
    cases h_ty with
    | app h_f _ => cases h_f with
      | app h_pbo _ => cases h_pbo with
        | primBinOpIntLt htrue hfalse => split <;> assumption
  | deltaCharLt =>
    cases h_ty with
    | app h_f _ => cases h_f with
      | app h_pbo _ => cases h_pbo with
        | primBinOpCharLt htrue hfalse => split <;> assumption
  | matchReduce hval hctor hfirst =>
    rename_i scrut branches name args pat body
    cases h_ty with
    | match_ h_scrut h_ne h_brs =>
      have hmem := hfirst.mem
      have hpeq := hfirst.ctor_eq
      simp [Expr.erase_match] at h_erased
      rcases h_erased with ⟨_, h_bl⟩
      have hbe_all : ∀ pe ∈ branches, pe.2.erase = pe.2 := by
        intro pe hpe
        have hmem' : pe ∈ branches.map (fun pb => (pb.1, pb.2.erase)) := by
          rw [h_bl]
          exact hpe
        obtain ⟨⟨p', b'⟩, hb_mem, hb⟩ := List.mem_map.mp hmem'
        have hpe' : b'.erase = pe.2 := by simpa using congrArg Prod.snd hb
        rw [hpe'.symm]
        exact Expr.erase_idem b'
      have hb : body.erase = body := hbe_all (pat, body) hmem
      cases pat with
      | wildcard =>
        simp only [MatchPattern.bindCount, List.take_zero]
        cases h_brs (.wildcard, body) hmem with
        | wildcard hbodyW =>
          exact TypeOfHM.subst_lemma_many (Ms := []) List.Forall₂.nil
            body.size body (Nat.le_refl _) [] _ hbodyW hb
      | named c n =>
        simp only [MatchPattern.matchesCtor, Bool.and_eq_true, beq_iff_eq] at hpeq
        obtain ⟨hcname, hnlen⟩ := hpeq
        simp only [MatchPattern.bindCount]
        rw [hnlen, List.take_length]
        cases h_brs (.named c n, body) hmem with
        | @mk _ _ _ _ ctorB _ _ _ tyArgsB instContents hspecB hctxB hbodyB =>
          subst hctxB
          have hlookB := hspecB.lookup
          have hScrutB := hspecB.scrut_eq
          have hpcB := hspecB.arity
          have hinstB := hspecB.fields
          rw [hScrutB] at h_scrut
          have hchain := TypeOfHM.canonical_customTy h_scrut hval
          obtain ⟨name', args', ctorS, tyArgsS, consumedS, remainingS,
            hcatS, hlookS, htyargsS, hcontentsS, hforallS, hinstS⟩ :=
            TypeOfHM.ctor_chain_inversion hchain h_scrut
          obtain ⟨hnEq, haEq⟩ := hctor.det hcatS
          subst hnEq
          subst haEq
          rw [hcname] at hlookB
          have hcc := Option.some.inj (hlookS.symm.trans hlookB)
          subst ctorB
          cases remainingS with
          | cons d rest => simp only [Ty.wrapArrows] at hinstS; cases hinstS
          | nil =>
            rw [List.append_nil] at hcontentsS
            subst hcontentsS
            simp only [Ty.wrapArrows] at hinstS
            cases hinstS with
            | customTy hbvr =>
              have hpc_len : tyArgsB.length = ctorS.paramCount := hpcB.symm
              have hagree : ∀ k, k < ctorS.paramCount → tyArgsB[k]? = tyArgsS[k]? := by
                intro k hk
                have hkt : k < tyArgsB.length := by omega
                have hkr : k < (Ty.bvarRange ctorS.paramCount).length := by
                  rw [hbvr.length_eq]; exact hkt
                have hrel := List.Forall₂.get hbvr hkr hkt
                simp only [List.get_eq_getElem] at hrel
                have helem : (Ty.bvarRange ctorS.paramCount)[k] = Ty.bvar k := by
                  have h1 := Ty.bvarRange_getElem? (n := ctorS.paramCount) (k := k) hk
                  rw [List.getElem?_eq_getElem hkr] at h1
                  exact Option.some.inj h1
                rw [helem] at hrel
                cases hrel with
                | bvar hsome =>
                  rw [hsome]
                  exact List.getElem?_eq_getElem hkt
              have h_vs := InstantiatesBy.build_match_vs hagree ctorS.bound hinstB hforallS
              exact TypeOfHM.subst_lemma_many h_vs
                body.size body (Nat.le_refl _) [] _ hbodyB hb
  | matchWildReduce hval hnc =>
    rename_i scrut body rest
    cases h_ty with
    | match_ h_scrut h_ne h_brs =>
      cases h_brs (.wildcard, body) (List.mem_cons_self ..) with
      | wildcard hbodyW => exact hbodyW
  | appFn _ ih =>
    cases h_ty with
    | app hf hi =>
      simp [Expr.erase_app] at h_erased
      rcases h_erased with ⟨hf_e, _⟩
      exact .app (ih hf hf_e) hi
  | appArg hv _ ih =>
    cases h_ty with
    | app hf hi =>
      simp [Expr.erase_app] at h_erased
      rcases h_erased with ⟨_, ha_e⟩
      exact .app hf (ih hi ha_e)
  | matchScrut _ ih =>
    cases h_ty with
    | match_ h_scrut h_ne h_brs =>
      simp [Expr.erase_match] at h_erased
      rcases h_erased with ⟨h_sc, _⟩
      exact .match_ (ih h_scrut h_sc) h_ne h_brs
  | letRecUnfold =>
    rename_i anns bindings body
    cases h_ty with
    | letRec hwf hlenP hlinkP hlcP hmonoP heq hbodyT =>
      subst heq
      expose_names
      have h_lr : Expr.letRec (bindings.map (fun _ => none)) (bindings.map Expr.erase) body.erase
          = Expr.letRec anns bindings body := by simpa using h_erased
      injection h_lr with h_anns h_binds h_bd
      have h_vs : List.Forall₂ (fun v M' => HasSchemeHM ⟨ctx.env, ctx.ctors⟩ v M')
          (bindings.map (fun e => Expr.letRec anns bindings e))
          (specs.map (RecSpec.bodyScheme G)) := by
        rw [List.forall₂_map_left_iff, List.forall₂_map_right_iff]
        refine List.forall₂_of_mem_zip hwf.length ?_
        rintro ⟨a, b⟩ hp
        cases b with
        | mono τ =>
          simp only [RecSpec.bodyScheme]
          rw [← h_anns]
          exact TypeOfHM.rewrap_hasSchemeHM_mono hwf hlenP hlinkP hlcP hmonoP hp
        | poly σ =>
          have hann : RecSpec.ann (RecSpec.poly σ) = none := by
            have hs_mem : RecSpec.poly σ ∈ specs := (List.of_mem_zip hp).2
            have hmem' : RecSpec.ann (RecSpec.poly σ) ∈ specs.map RecSpec.ann :=
              List.mem_map.mpr ⟨RecSpec.poly σ, hs_mem, rfl⟩
            rw [hwf.anns_eq, ← h_anns] at hmem'
            obtain ⟨b, hb_mem, hb⟩ := List.mem_map.mp hmem'
            exact hb.symm
          obtain ⟨t, ht⟩ := RecSpec.ann_eq_none hann
          cases ht
      have hfinal := TypeOfHM.subst_lemma_many (env := ctx.env)
        (Ms := specs.map (RecSpec.bodyScheme G))
        (ctors := ctx.ctors) h_vs body.size body (Nat.le_refl _) [] _ hbodyT h_bd
      simpa using hfinal

/-- Iterated preservation: typing, erasedness, and exhaustiveness are preserved
    across the reflexive-transitive closure of `Step`. -/
theorem TypeOfHM.preservation_star {ctors : CtorEnv} {e e' : Expr} {τ : Ty}
    (h_rtc : Relation.ReflTransGen SmallStep.Step e e')
    (h_ty : TypeOfHM ⟨[], ctors⟩ e τ)
    (h_erased : e.erase = e)
    (h_exh : SmallStep.AllMatchesExhaustive ctors e) :
    TypeOfHM ⟨[], ctors⟩ e' τ ∧ e'.erase = e' ∧ SmallStep.AllMatchesExhaustive ctors e' := by
  induction h_rtc with
  | refl => exact ⟨h_ty, h_erased, h_exh⟩
  | tail _ h_bc ih =>
    obtain ⟨h_ty_b, h_erased_b, h_exh_b⟩ := ih
    exact ⟨TypeOfHM.preservation h_bc h_ty_b h_erased_b,
      SmallStep.Step.preserves_erased h_erased_b h_bc,
      SmallStep.Step.preserves_exhaustive h_exh_b h_bc⟩

/-- **Type safety** ("well-typed erased programs don't go wrong"): a closed,
    erased, exhaustive, well-typed program makes progress (value or steps) and
    every step preserves typing. -/
theorem TypeOfHM.type_safety {ctors : CtorEnv} {e : Expr} {τ : Ty}
    (h_ty : TypeOfHM ⟨[], ctors⟩ e τ) (h_erased : e.erase = e)
    (h_exh : SmallStep.AllMatchesExhaustive ctors e) :
    (SmallStep.IsValue e ∨ ∃ e', SmallStep.Step e e') ∧
    (∀ e', SmallStep.Step e e' → TypeOfHM ⟨[], ctors⟩ e' τ) :=
  ⟨TypeOfHM.progress h_ty rfl h_exh,
   fun _ hstep => TypeOfHM.preservation hstep h_ty h_erased⟩

/-- **Iterated type safety**: every term reachable from a closed, erased,
    exhaustive, well-typed program is well-typed and itself progresses. -/
theorem TypeOfHM.type_safety_star {ctors : CtorEnv} {e : Expr} {τ : Ty}
    (h_ty : TypeOfHM ⟨[], ctors⟩ e τ) (h_erased : e.erase = e)
    (h_exh : SmallStep.AllMatchesExhaustive ctors e) :
    ∀ e', Relation.ReflTransGen SmallStep.Step e e' →
      TypeOfHM ⟨[], ctors⟩ e' τ ∧ (SmallStep.IsValue e' ∨ ∃ e'', SmallStep.Step e' e'') := by
  intro e' h_rtc
  obtain ⟨h_ty', h_erased', h_exh'⟩ := TypeOfHM.preservation_star h_rtc h_ty h_erased h_exh
  exact ⟨h_ty', TypeOfHM.progress h_ty' rfl h_exh'⟩

/-- Term-var shifting preserves `TyBvarBounded` (it only renames term `bvar`s, never
    touching type annotations). (Re-based off `NoRecAnn`: shifting recurses through
    `letRecAnn` schemes/bindings without touching their type bvars.) -/
theorem Expr.shiftFrom_tyBvarBounded (n : Nat) {e : Expr} :
    ∀ (t d : Nat), e.TyBvarBounded d → (e.shiftFrom t n).TyBvarBounded d := by
  induction e using Expr.rec_strong with
  | primLit p => intro t d _; exact trivial
  | primBinOp op => intro t d _; exact trivial
  | ctor c => intro t d _; exact trivial
  | var i =>
    intro t d hb; simp only [Expr.TyBvarBounded] at hb ⊢
    simp only [Expr.shiftFrom]; split <;> exact hb
  | lambda ann body ih =>
    intro t d hb
    simp only [Expr.TyBvarBounded] at hb
    simp only [Expr.shiftFrom, Expr.TyBvarBounded]
    exact ⟨hb.1, ih (t + 1) d hb.2⟩
  | app f arg ihf iharg =>
    intro t d hb
    simp only [Expr.TyBvarBounded] at hb
    simp only [Expr.shiftFrom, Expr.TyBvarBounded]
    exact ⟨ihf t d hb.1, iharg t d hb.2⟩
  | letIn ann rhs body ihr ihb =>
    intro t d hb
    cases ann with
    | none =>
      simp only [Expr.TyBvarBounded] at hb
      simp only [Expr.shiftFrom, Expr.TyBvarBounded]
      exact ⟨ihr t d hb.1, ihb (t + 1) d hb.2⟩
    | some σ =>
      simp only [Expr.TyBvarBounded] at hb
      simp only [Expr.shiftFrom, Expr.TyBvarBounded]
      exact ⟨hb.1, ihr t (d + σ.paramCount) hb.2.1, ihb (t + 1) d hb.2.2⟩
  | match_ scrut branches ihs ihbr =>
    intro t d hb
    simp only [Expr.TyBvarBounded] at hb
    simp only [Expr.shiftFrom, Expr.TyBvarBounded]
    refine ⟨ihs t d hb.1, ?_⟩
    obtain ⟨_, hbbr⟩ := hb
    induction branches with
    | nil => exact trivial
    | cons hd tl ihtl =>
      obtain ⟨p, b⟩ := hd
      exact ⟨ihbr p b List.mem_cons_self (t + p.bindCount) d hbbr.1,
             ihtl (fun p' b' hmem => ihbr p' b' (List.mem_cons_of_mem _ hmem)) hbbr.2⟩
  | letRec anns bindings body ihbs ihb =>
    intro t d hb
    obtain ⟨hsch, hbs, hbody⟩ := hb
    refine ⟨hsch, ?_, ihb (t + bindings.length) d hbody⟩
    generalize t + bindings.length = thr
    clear hsch hbody
    induction bindings generalizing anns with
    | nil => cases anns <;> exact trivial
    | cons hd tl ihtl =>
      cases anns with
      | nil =>
        exact ⟨ihbs hd List.mem_cons_self thr d hbs.1,
               ihtl [] (fun e' hm => ihbs e' (List.mem_cons_of_mem _ hm)) hbs.2⟩
      | cons a as =>
        exact ⟨ihbs hd List.mem_cons_self thr (d + RecAnn.params a) hbs.1,
               ihtl as (fun e' hm => ihbs e' (List.mem_cons_of_mem _ hm)) hbs.2⟩

/-! ### The coherence theorem (`Infer.sound`, vs declarative `TypeOfHM`)

The erasure-on-`Step` migration's single soundness theorem
(`briefs/design-memo-erasure-migration.md` §3.6): the source checker `Infer` is
coherent with the erased machine relation `TypeOfHM`. Unlike the `*_elab` family
(vs `TypeOfElabHM`, deleted in a later step), the conclusion ranges over the
ERASED INPUT term (`e.erase`), with `eOut` ignored. The conclusion threads
`eraseBounds` because `Infer` produces `bl`-annotated types while `TypeOfHM` never
inhabits them; the `K`-list escape conditions are the ones from the old
`Infer.sound_elab`. Placed after the `TypeOfHM` metatheory it depends on
(`typ_subst_preservation`, `onSubst`, `weaken_scheme`). -/

set_option maxRecDepth 10_000 in
mutual

theorem Infer.sound {Φ ctx e Φ' S τ} (h : Infer Φ ctx e Φ' S τ) :
    CtxWF ctx → CtxBelow Φ ctx → (K : List Nat) → (∀ k ∈ K, k < Φ) →
    (∀ y ∈ e.tyFreeVars, y ∈ K) → (∀ p ∈ S, p.1 ∉ K) →
    TypeOfHM (S.onCtx ctx).eraseBounds e.erase (Ty.eraseBounds (S.onTy τ)) := by
  intro hctx hbelow K hKΦ hKe hSK
  rw [show S.onTy τ = τ from Ty.substFvars_eq_self_of_no_key (fun p hp =>
    (Infer.eliminates h hbelow (fun y hy => hKΦ y (hKe y hy))
      (fun p hp hc => hSK p hp (hKe p.1 hc))).2 p hp)]
  have herase_tfv : ∀ e : Expr, (e.erase).tyFreeVars = [] := by
    intro e
    induction e using Expr.rec_strong with
    | primLit p => simp [Expr.erase, Expr.tyFreeVars]
    | primBinOp op => simp [Expr.erase, Expr.tyFreeVars]
    | ctor c => simp [Expr.erase, Expr.tyFreeVars]
    | var i  => simp [Expr.erase, Expr.tyFreeVars]
    | app f arg ihf iha => simp [Expr.erase_app, Expr.tyFreeVars, ihf, iha]
    | lambda ann body ih => simp [Expr.erase_lambda, Expr.tyFreeVars, ih, Option.elim_none]
    | letIn ann rhs body ihr ihb =>
      simp [Expr.erase_letIn, Expr.tyFreeVars, ihr, ihb, Option.elim_none]
    | match_ scrut branches ihs ihbs =>
      simp only [Expr.erase_match, Expr.tyFreeVars, ihs]
      induction branches with
      | nil => rfl
      | cons pe rest ih =>
        cases pe with
        | mk pat body =>
          simp only [Expr.tyFreeVars.BranchList.tyFreeVars, List.map_cons]
          rw [ihbs pat body (List.mem_cons_self ..)]
          rw [ih (fun pat₁ e mem => ihbs pat₁ e (List.mem_cons_of_mem _ mem))]
          simp
    | letRec anns bindings body ihbs ihb =>
      have hpair : Expr.tyFreeVars.AnnList.tyFreeVars
          (bindings.map (fun _ => none)) = [] ∧
          Expr.tyFreeVars.RecGroup.tyFreeVars (bindings.map Expr.erase) = [] := by
        induction bindings with
        | nil =>
          simp [Expr.tyFreeVars.AnnList.tyFreeVars, Expr.tyFreeVars.RecGroup.tyFreeVars]
        | cons b rest ih =>
          rcases ih (fun e mem => ihbs e (List.mem_cons_of_mem b mem)) with ⟨hA, hR⟩
          constructor
          · simp only [Expr.tyFreeVars.AnnList.tyFreeVars, List.map_cons, Option.elim_none]
            rw [hA]
            simp
          · simp only [Expr.tyFreeVars.RecGroup.tyFreeVars, List.map_cons]
            rw [ihbs b (List.mem_cons_self ..), hR]
            simp
      simp only [Expr.erase_letRec, Expr.tyFreeVars, ihb]
      rw [hpair.1, hpair.2]
      simp
  have herase_eraseBounds : ∀ e : Expr, (e.erase).eraseBounds = e.erase := by
    intro e
    induction e using Expr.rec_strong with
    | primLit p => simp [Expr.erase, Expr.eraseBounds]
    | primBinOp op => simp [Expr.erase, Expr.eraseBounds]
    | ctor c => simp [Expr.erase, Expr.eraseBounds]
    | var i  => simp [Expr.erase, Expr.eraseBounds]
    | app f arg ihf iha => simp only [Expr.erase_app, Expr.eraseBounds_app, ihf, iha]
    | lambda ann body ih =>
      simp only [Expr.erase_lambda, Expr.eraseBounds_lambda, Option.map_none, ih]
    | letIn ann rhs body ihr ihb =>
      simp only [Expr.erase_letIn, Expr.eraseBounds_letIn, Option.map_none, ihr, ihb]
    | match_ scrut branches ihs ihbs =>
      have hb : (branches.map (fun pe => (pe.1, pe.2.erase))).map
          (fun pe => (pe.1, pe.2.eraseBounds)) = branches.map (fun pe => (pe.1, pe.2.erase)) := by
        rw [List.map_map]
        apply List.map_congr_left
        intro pe hpe
        cases pe with
        | mk pat body => simp [ihbs pat body hpe]
      simp only [Expr.erase_match, Expr.eraseBounds]
      rw [ihs, hb]
    | letRec anns bindings body ihbs ihb =>
      have hanns : (bindings.map (fun _ => none)).map (Option.map PolyTy.eraseBounds) =
          bindings.map (fun _ => none) := by
        rw [List.map_map]
        apply List.map_congr_left
        intro b _
        rfl
      have hbs : (bindings.map Expr.erase).map Expr.eraseBounds = bindings.map Expr.erase := by
        rw [List.map_map]
        apply List.map_congr_left
        intro b hb
        exact ihbs b hb
      simp only [Expr.erase_letRec, Expr.eraseBounds]
      rw [hanns, hbs, ihb]
  have herase_subst : ∀ (e : Expr) (S : Subst), (e.erase).substTyFvars S = e.erase := by
    intro e S
    exact Expr.substTyFvars_eq_self_of_not_mem_tyFreeVars (fun p hp hc => by
      rw [herase_tfv e] at hc
      simp at hc)
  cases h with
  | primLitUnit =>
    simp only [Subst.onCtx_nil, Expr.erase, Ty.eraseBounds_prim]
    exact .primLitUnit
  | primLitInt =>
    simp only [Subst.onCtx_nil, Expr.erase, Ty.eraseBounds_prim]
    exact .primLitInt
  | primLitNat =>
    simp only [Subst.onCtx_nil, Expr.erase, Ty.eraseBounds_prim]
    exact .primLitNat
  | primLitChar =>
    simp only [Subst.onCtx_nil, Expr.erase, Ty.eraseBounds_prim]
    exact .primLitChar
  | primBinOpIntAdd =>
    simp only [Subst.onCtx_nil, Expr.erase, Ty.eraseBounds_arrow, Ty.eraseBounds_prim]
    exact .primBinOpIntAdd
  | primBinOpIntSub =>
    simp only [Subst.onCtx_nil, Expr.erase, Ty.eraseBounds_arrow, Ty.eraseBounds_prim]
    exact .primBinOpIntSub
  | primBinOpIntLt hlookT hbT hlookF hbF =>
    simp only [Subst.onCtx_nil, Expr.erase, Ty.eraseBounds_arrow, Ty.eraseBounds_prim,
      Ty.eraseBounds_customTy, TyList.eraseBounds_nil]
    exact .primBinOpIntLt (Ctor.IsBoolCtor.typeOfHM_erase hlookT hbT)
      (Ctor.IsBoolCtor.typeOfHM_erase hlookF hbF)
  | primBinOpCharLt hlookT hbT hlookF hbF =>
    simp only [Subst.onCtx_nil, Expr.erase, Ty.eraseBounds_arrow, Ty.eraseBounds_prim,
      Ty.eraseBounds_customTy, TyList.eraseBounds_nil]
    exact .primBinOpCharLt (Ctor.IsBoolCtor.typeOfHM_erase hlookT hbT)
      (Ctor.IsBoolCtor.typeOfHM_erase hlookF hbF)
  | lambda hseed hbody =>
    expose_names
    rw [Expr.erase_lambda]
    cases hseed
    case none =>
      simp only [Expr.tyFreeVars, Option.elim_none, List.nil_append] at hKe
      have hbodyWF : CtxWF { ctx with env := PolyTy.mkTrivial (.fvar Φ) :: ctx.env } := by
        intro M hM; rcases List.mem_cons.mp hM with rfl | hM
        · exact ContainsBvarsUpTo.fvar
        · exact hctx M hM
      have hbodyBelow : CtxBelow (Φ + 1) { ctx with env := PolyTy.mkTrivial (.fvar Φ) :: ctx.env } := by
        intro M hM; rcases List.mem_cons.mp hM with rfl | hM
        · exact .fvar (by omega)
        · exact (hbelow M hM).mono (by omega)
      have ih0 := Infer.sound hbody hbodyWF hbodyBelow K
        (fun k hk => by have := hKΦ k hk; omega) hKe hSK
      have hSτb : S.onTy τb = τb := Ty.substFvars_eq_self_of_no_key (fun p hp =>
        (Infer.eliminates hbody hbodyBelow (fun y hy => by
            have := hKΦ y (hKe y hy); omega)
          (fun p hp hc => hSK p hp (hKe p.1 hc))).2 p hp)
      have ih : TypeOfHM (S.onCtx { ctx with env := PolyTy.mkTrivial (.fvar Φ) :: ctx.env }).eraseBounds
          body.erase (Ty.eraseBounds τb) := by
        rwa [hSτb] at ih0
      refine TypeOfHM.lambda
        (Ty.IsLC.eraseBounds (Subst.onTy_lc (Infer.lc hbody hbodyWF).2 ContainsBvarsUpTo.fvar))
        (fun T hT => by cases hT) rfl ?_
      simpa only [Ctx.eraseBounds, Subst.onCtx, Env.eraseBounds_cons,
        PolyTy.eraseBounds_mkTrivial, Subst.onEnv, List.map_cons, Ty.eraseBounds_arrow]
        using ih
    case some hcl =>
      expose_names
      simp only [Expr.tyFreeVars, Option.elim_some, List.mem_append] at hKe
      have hbodyWF : CtxWF { ctx with env := PolyTy.mkTrivial paramTy :: ctx.env } := by
        intro M hM; rcases List.mem_cons.mp hM with rfl | hM
        · exact hcl
        · exact hctx M hM
      have hbodyBelow : CtxBelow Φ { ctx with env := PolyTy.mkTrivial paramTy :: ctx.env } := by
        intro M hM; rcases List.mem_cons.mp hM with rfl | hM
        · exact Ty.BelowFvars.of_freeVars_lt (fun v hv => hKΦ v (hKe v (.inl hv)))
        · exact hbelow M hM
      have ih0 := Infer.sound hbody hbodyWF hbodyBelow K
        (fun k hk => by have := hKΦ k hk; omega)
        (fun y hy => hKe y (.inr hy)) hSK
      have hSτb : S.onTy τb = τb := Ty.substFvars_eq_self_of_no_key (fun p hp =>
        (Infer.eliminates hbody hbodyBelow (fun y hy => by
            have := hKΦ y (hKe y (.inr hy)); omega)
          (fun p hp hc => hSK p hp (hKe p.1 (.inr hc)))).2 p hp)
      have ih : TypeOfHM (S.onCtx { ctx with env := PolyTy.mkTrivial paramTy :: ctx.env }).eraseBounds
          body.erase (Ty.eraseBounds τb) := by
        rwa [hSτb] at ih0
      refine TypeOfHM.lambda
        (Ty.IsLC.eraseBounds (Subst.onTy_lc (Infer.lc hbody hbodyWF).2 hcl))
        (fun T hT => by cases hT) rfl ?_
      simpa only [Ctx.eraseBounds, Subst.onCtx, Env.eraseBounds_cons,
        PolyTy.eraseBounds_mkTrivial, Subst.onEnv, List.map_cons, Ty.eraseBounds_arrow]
        using ih
  | app hf harg huni =>
    expose_names
    simp only [Expr.tyFreeVars, List.mem_append] at hKe
    obtain ⟨hf_lc, hf_s⟩ := Infer.lc hf hctx
    have hctx1 := Subst.onCtx_wf hf_s hctx
    obtain ⟨harg_lc, harg_s⟩ := Infer.lc harg hctx1
    have hf_below := Infer.belowFvars hf hbelow (fun y hy => hKΦ y (hKe y (.inl hy)))
    have hbelow1 := Subst.onCtx_below hf_below.2 (Infer.frontier_le hf) hbelow
    have hs3 := huni.lc (Subst.onTy_lc harg_s hf_lc) (.arrow harg_lc ContainsBvarsUpTo.fvar)
    have hf_sound := Infer.sound hf hctx hbelow K hKΦ (fun y hy => hKe y (.inl hy))
      (fun p hp => hSK p (List.mem_append_left _ (List.mem_append_left _ hp)))
    have hf_sound' : TypeOfHM (S₁.onCtx ctx).eraseBounds f.erase (Ty.eraseBounds τf) := by
      have hS₁τf : S₁.onTy τf = τf := Ty.substFvars_eq_self_of_no_key (fun p hp =>
        (Infer.eliminates hf hbelow (fun y hy => hKΦ y (hKe y (.inl hy)))
          (fun p hp hc => hSK p (List.mem_append_left _ (List.mem_append_left _ hp))
            (hKe p.1 (.inl hc)))).2 p hp)
      rwa [hS₁τf] at hf_sound
    have harg_sound := Infer.sound harg hctx1 hbelow1 K
      (fun k hk => lt_of_lt_of_le (hKΦ k hk) (Infer.frontier_le hf))
      (fun y hy => hKe y (.inr hy))
      (fun p hp => hSK p (List.mem_append_left _ (List.mem_append_right _ hp)))
    have harg_sound' : TypeOfHM (S₂.onCtx (S₁.onCtx ctx)).eraseBounds arg.erase (Ty.eraseBounds τa) := by
      have hS₂τa : S₂.onTy τa = τa := Ty.substFvars_eq_self_of_no_key (fun p hp =>
        (Infer.eliminates harg hbelow1 (fun y hy => by
            have := hKΦ y (hKe y (.inr hy)); have := Infer.frontier_le hf; omega)
          (fun p hp hc => hSK p (List.mem_append_left _ (List.mem_append_right _ hp))
            (hKe p.1 (.inr hc)))).2 p hp)
      rwa [hS₂τa] at harg_sound
    have hf2 := TypeOfHM.onSubst_eraseBounds_fixed_append S₁ S₂ hf_s harg_s
      (herase_subst f S₁) (herase_subst f S₂)
      (by simpa only [herase_eraseBounds f] using hf_sound')
    have hf3 := TypeOfHM.onSubst_eraseBounds_fixed (ctx := (S₁ ++ S₂).onCtx ctx)
      (e := f.erase) (τ := S₂.onTy τf) S₃ hs3 (herase_subst f S₃)
      (by simpa only [herase_eraseBounds f] using hf2)
    have hueq : Ty.eraseBounds (S₃.onTy (S₂.onTy τf)) =
        Ty.eraseBounds (S₃.onTy (.arrow τa (.fvar Φ₂))) := huni.unifies
    have hf_arr : TypeOfHM ((S₁ ++ S₂ ++ S₃).onCtx ctx).eraseBounds f.erase
        (.arrow (Ty.eraseBounds (S₃.onTy τa)) (Ty.eraseBounds (S₃.onTy (.fvar Φ₂)))) := by
      have key := hf3
      rw [hueq, Subst.onTy_arrow, Ty.eraseBounds_arrow] at key
      have hctx_eq : (S₃.onCtx ((S₁ ++ S₂).onCtx ctx)).eraseBounds =
          ((S₁ ++ S₂ ++ S₃).onCtx ctx).eraseBounds := by
        rw [← Subst.onCtx_append]
      rwa [hctx_eq, herase_eraseBounds f] at key
    have harg3 := TypeOfHM.onSubst_eraseBounds_fixed (ctx := S₂.onCtx (S₁.onCtx ctx))
      (e := arg.erase) (τ := τa) S₃ hs3 (herase_subst arg S₃)
      (by simpa only [herase_eraseBounds arg] using harg_sound')
    have harg_arr : TypeOfHM ((S₁ ++ S₂ ++ S₃).onCtx ctx).eraseBounds arg.erase
        (Ty.eraseBounds (S₃.onTy τa)) := by
      have hctx_eq : (S₃.onCtx (S₂.onCtx (S₁.onCtx ctx))).eraseBounds =
          ((S₁ ++ S₂ ++ S₃).onCtx ctx).eraseBounds := by
        simp only [← Subst.onCtx_append, List.append_assoc]
      have key := harg3
      rwa [hctx_eq, herase_eraseBounds arg] at key
    rw [Expr.erase_app]
    exact TypeOfHM.app hf_arr harg_arr
  | @var Φ ctx i polyTy hlook =>
    simp only [Subst.onCtx_nil, Expr.erase_var]
    refine TypeOfHM.var (polyTy := PolyTy.eraseBounds polyTy)
      (instArgs := ((freshVars Φ polyTy.paramCount).map Ty.fvar).map Ty.eraseBounds) ?_ ?_ ?_
    · have hlook' := congrArg (Option.map PolyTy.eraseBounds) hlook
      simpa [Ctx.eraseBounds, Env.eraseBounds_getElem?, Option.map_some] using hlook'
    · intro tyArg ht
      simp only [List.map_map, Function.comp_def, Ty.eraseBounds_fvar] at ht
      obtain ⟨n, _, rfl⟩ := List.mem_map.mp ht
      exact ContainsBvarsUpTo.fvar
    · change (PolyTy.eraseBounds polyTy).InstantiatesTo
        (((freshVars Φ polyTy.paramCount).map Ty.fvar).map Ty.eraseBounds)
        (Ty.eraseBounds (polyTy.openVars (freshVars Φ polyTy.paramCount)))
      simp only [List.map_map, Function.comp_def, Ty.eraseBounds_fvar]
      rw [PolyTy.eraseBounds_openVars]
      exact InstantiatesBy.openVars
        (PolyTy.WF.eraseBounds (hctx _ (List.mem_of_getElem? hlook)))
        (by simp [freshVars_length, PolyTy.eraseBounds_paramCount])
  | @ctor Φ ctx name ctor hlook =>
    simp only [Subst.onCtx_nil, Expr.erase]
    refine TypeOfHM.ctor (ctor := Ctor.eraseBounds ctor)
      (tyArgs := (freshVars Φ ctor.paramCount).map Ty.fvar) ?_ ?_ ?_
    · have hlook' := congrArg (Option.map Ctor.eraseBounds) hlook
      simpa [Ctx.eraseBounds, CtorEnv.eraseBounds_get?, Option.map_some] using hlook'
    · intro tyArg ht
      obtain ⟨x, _, rfl⟩ := List.mem_map.mp ht
      exact ContainsBvarsUpTo.fvar
    · change (Ctor.eraseBounds ctor).toTy.InstantiatesTo
        ((freshVars Φ ctor.paramCount).map Ty.fvar)
        (Ty.eraseBounds (ctor.toTy.openVars (freshVars Φ ctor.paramCount)))
      rw [Ctor.eraseBounds_toTy, PolyTy.eraseBounds_openVars]
      exact InstantiatesBy.openVars
        (PolyTy.WF.eraseBounds (Ctor.toTy_wf ctor))
        (by simp [Ctor.toTy, freshVars_length, PolyTy.eraseBounds_paramCount])
  | letIn hrhs hbody =>
    expose_names
    simp only [Expr.tyFreeVars, Option.elim_none, List.nil_append, List.mem_append] at hKe
    obtain ⟨hrhs_lc, hrhs_s⟩ := Infer.lc hrhs hctx
    have hrhs_below := Infer.belowFvars hrhs hbelow (fun y hy => hKΦ y (hKe y (.inl hy)))
    have hbelow1 := Subst.onCtx_below hrhs_below.2 (Infer.frontier_le hrhs) hbelow
    have helimR := Infer.eliminates hrhs hbelow (fun y hy => hKΦ y (hKe y (.inl hy)))
      (fun p hp hc => hSK p (List.mem_append_left _ hp) (hKe p.1 (.inl hc)))
    have hS₁τ₁ : S₁.onTy τ₁ = τ₁ := Ty.substFvars_eq_self_of_no_key (fun p hp => helimR.2 p hp)
    have hbodyWF : CtxWF { (S₁.onCtx ctx) with
        env := genScheme rhs.tyFreeVars (S₁.onCtx ctx).env τ₁ :: (S₁.onCtx ctx).env } := by
      intro M hM; rcases List.mem_cons.mp hM with rfl | hM
      · exact genScheme_wf hrhs_lc
      · exact (Subst.onCtx_wf hrhs_s hctx) M hM
    have hbodyBelow : CtxBelow Φ₁ { (S₁.onCtx ctx) with
        env := genScheme rhs.tyFreeVars (S₁.onCtx ctx).env τ₁ :: (S₁.onCtx ctx).env } := by
      intro M hM; rcases List.mem_cons.mp hM with rfl | hM
      · exact hrhs_below.1.closeOver
      · exact hbelow1 M hM
    have hbody_s := (Infer.lc hbody hbodyWF).2
    set genV := genVars rhs.tyFreeVars (S₁.onCtx ctx).env τ₁ with hgenV_def
    have hgenV_τ₁ : ∀ g ∈ genV, g ∈ τ₁.freeVars :=
      fun g hg => by simp only [genV, genVars, List.mem_filter] at hg; exact hg.1
    have hgenV_env : ∀ g ∈ genV, g ∉ (S₁.onCtx ctx).env.freeVars :=
      fun g hg => by simp only [genV] at hg; exact genVars_not_mem hg
    have hgenV_lt : ∀ g ∈ genV, g < Φ₁ :=
      fun g hg => hrhs_below.1.mem_lt g (hgenV_τ₁ g hg)
    have hgenV_ge : ∀ g ∈ genV, Φ ≤ g := by
      intro g hg
      by_contra hlt; push_neg at hlt
      have hg_S₁dom : ∀ p ∈ S₁, p.1 ≠ g := fun p hp hpeq => helimR.2 p hp (hpeq ▸ hgenV_τ₁ g hg)
      have hg_ctxenv : ∀ M ∈ ctx.env, g ∉ M.body.freeVars := by
        intro M₀ hM₀ hgM
        exact hgenV_env g hg (Env.mem_freeVars_iff.mpr ⟨S₁.onPolyTy M₀,
          List.mem_map.mpr ⟨M₀, hM₀, rfl⟩, Ty.mem_freeVars_onTy_of_not_dom hgM hg_S₁dom⟩)
      have hg_rigid : g ∉ rhs.tyFreeVars := by
        simp only [genV] at hg; exact genVars_not_mem_rigid hg
      exact (Infer.eOut_avoid hrhs (w := g) hlt hg_ctxenv hg_rigid).2 (hgenV_τ₁ g hg)
    have hgenV_body : ∀ g ∈ genV, g ∉ body.tyFreeVars :=
      fun g hg hc => by have := hKΦ g (hKe g (.inr hc)); have := hgenV_ge g hg; omega
    have hbodyCtxAvoid : ∀ g ∈ genV,
        ∀ M ∈ (genScheme rhs.tyFreeVars (S₁.onCtx ctx).env τ₁ :: (S₁.onCtx ctx).env),
          g ∉ M.body.freeVars := by
      intro g hg M hM
      rcases List.mem_cons.mp hM with rfl | hM
      · exact Ty.not_mem_closeOver_freeVars (by simpa [genV] using hg)
      · exact fun hc2 => hgenV_env g hg (Env.mem_freeVars_iff.mpr ⟨M, hM, hc2⟩)
    have hS₂genV : ∀ p ∈ S₂, p.1 ∉ genV := by
      intro p hp hc
      exact Infer.dom_avoid hbody (hgenV_lt p.1 hc) (hbodyCtxAvoid p.1 hc)
        (fun hc2 => hSK p (List.mem_append_right _ hp) (hKe p.1 (.inr hc2)))
        (List.mem_map.mpr ⟨p, hp, rfl⟩)
    have hS₂genVran : ∀ p ∈ S₂, ∀ u ∈ p.2.freeVars, u ∉ genV := by
      intro p hp u hu hc
      exact (Infer.eOut_avoid hbody (w := u) (hgenV_lt u hc) (hbodyCtxAvoid u hc)
        (hgenV_body u hc)).1 p hp hu
    have hSτ₁ : (S₁ ++ S₂).onTy τ₁ = S₂.onTy τ₁ := by rw [Subst.onTy_append, hS₁τ₁]
    have hschemebody : S₂.onTy (Ty.closeOver genV τ₁) =
        Ty.closeOver genV ((S₁ ++ S₂).onTy τ₁) := by
      have h1 : S₂.onTy (Ty.closeOver genV τ₁) = Ty.closeOver genV (S₂.onTy τ₁) :=
        Ty.substFvars_closeOver hS₂genV hS₂genVran
      rw [h1, ← hSτ₁]
    have hgenV_env' : ∀ g ∈ genV, g ∉ ((S₁ ++ S₂).onCtx ctx).env.freeVars := by
      intro g hg hc
      rw [Subst.onCtx_append, Env.mem_freeVars_iff] at hc
      obtain ⟨M, hM, hgM⟩ := hc
      simp only [Subst.onCtx, Subst.onEnv] at hM
      obtain ⟨M₀, hM₀, rfl⟩ := List.mem_map.mp hM
      exact Subst.notMemOnTy (fun p hp hgp => hS₂genVran p hp g hgp hg)
        (fun hc2 => hgenV_env g hg (Env.mem_freeVars_iff.mpr ⟨M₀, hM₀, hc2⟩)) hgM
    have hschemeeq : Subst.onPolyTy S₂ (genScheme rhs.tyFreeVars (S₁.onCtx ctx).env τ₁)
        = ⟨genV.length, Ty.closeOver genV ((S₁ ++ S₂).onTy τ₁)⟩ := by
      simp only [Subst.onPolyTy, genScheme, ← hgenV_def]
      exact congrArg (fun b => PolyTy.mk genV.length b) hschemebody
    have heqbodyctx : Subst.onCtx S₂ { (S₁.onCtx ctx) with
          env := genScheme rhs.tyFreeVars (S₁.onCtx ctx).env τ₁ :: (S₁.onCtx ctx).env }
        = { (S₁ ++ S₂).onCtx ctx with
          env := Subst.onPolyTy S₂ (genScheme rhs.tyFreeVars (S₁.onCtx ctx).env τ₁)
            :: ((S₁ ++ S₂).onCtx ctx).env } := by
      rw [Subst.onCtx_append]
      simp only [Subst.onCtx, Subst.onEnv, List.map_cons]
    -- residual source typings
    have hrhs_sound := Infer.sound hrhs hctx hbelow K hKΦ (fun y hy => hKe y (.inl hy))
      (fun p hp => hSK p (List.mem_append_left _ hp))
    have hrhs_sound' : TypeOfHM (S₁.onCtx ctx).eraseBounds rhs.erase (Ty.eraseBounds τ₁) := by
      rwa [hS₁τ₁] at hrhs_sound
    have hr2 := TypeOfHM.onSubst_eraseBounds_fixed (ctx := S₁.onCtx ctx)
      (e := rhs.erase) (τ := τ₁) S₂ hbody_s (herase_subst rhs S₂)
      (by simpa only [herase_eraseBounds rhs] using hrhs_sound')
    have hbase : TypeOfHM ((S₁ ++ S₂).onCtx ctx).eraseBounds rhs.erase
        (Ty.eraseBounds ((S₁ ++ S₂).onTy τ₁)) := by
      have key := hr2
      rw [← Subst.onCtx_append, ← hSτ₁] at key
      simpa only [herase_eraseBounds rhs] using key
    have hbody_sound := Infer.sound hbody hbodyWF hbodyBelow K
      (fun k hk => lt_of_lt_of_le (hKΦ k hk) (Infer.frontier_le hrhs))
      (fun y hy => hKe y (.inr hy)) (fun p hp => hSK p (List.mem_append_right _ hp))
    have hbody_sound' : TypeOfHM
        (S₂.onCtx { (S₁.onCtx ctx) with
            env := genScheme rhs.tyFreeVars (S₁.onCtx ctx).env τ₁ :: (S₁.onCtx ctx).env }).eraseBounds
        body.erase (Ty.eraseBounds τ) := by
      have hS₂τ : S₂.onTy τ = τ := Ty.substFvars_eq_self_of_no_key (fun p hp =>
        (Infer.eliminates hbody hbodyBelow (fun y hy => by
            have := hKΦ y (hKe y (.inr hy)); have := Infer.frontier_le hrhs; omega)
          (fun p hp hc => hSK p (List.mem_append_right _ hp) (hKe p.1 (.inr hc)))).2 p hp)
      rwa [hS₂τ] at hbody_sound
    have hbody_pack : TypeOfHM
        { ((S₁ ++ S₂).onCtx ctx).eraseBounds with
          env := PolyTy.eraseBounds ⟨genV.length, Ty.closeOver genV ((S₁ ++ S₂).onTy τ₁)⟩
            :: ((S₁ ++ S₂).onCtx ctx).env.eraseBounds }
        body.erase (Ty.eraseBounds τ) := by
      have key := hbody_sound'
      have hctx_eq :
          (S₂.onCtx { (S₁.onCtx ctx) with
              env := genScheme rhs.tyFreeVars (S₁.onCtx ctx).env τ₁ :: (S₁.onCtx ctx).env
            }).eraseBounds
          = { ((S₁ ++ S₂).onCtx ctx).eraseBounds with
              env := PolyTy.eraseBounds
                  (S₂.onPolyTy (genScheme rhs.tyFreeVars (S₁.onCtx ctx).env τ₁))
                :: ((S₁ ++ S₂).onCtx ctx).env.eraseBounds } := by
        rw [heqbodyctx]
        simp only [Ctx.eraseBounds, Env.eraseBounds, List.map_cons]
      rw [hctx_eq, hschemeeq] at key
      exact key
    have hS₁S₂lc : ∀ p ∈ S₁ ++ S₂, p.2.IsLC :=
      fun p hp => (List.mem_append.mp hp).elim (fun h => hrhs_s p h) (fun h => hbody_s p h)
    -- residual source letIn none: Pins vacuous; cofinite via rename of genV
    rw [Expr.erase_letIn]
    set Mres : PolyTy :=
      PolyTy.eraseBounds ⟨genV.length, Ty.closeOver genV ((S₁ ++ S₂).onTy τ₁)⟩ with hMres
    have hMres_eq : Mres = ⟨genV.length, Ty.closeOver genV (Ty.eraseBounds ((S₁ ++ S₂).onTy τ₁))⟩ := by
      simp only [Mres, PolyTy.eraseBounds, Ty.eraseBounds_closeOver]
    refine TypeOfHM.letIn (M := Mres) (L := genV)
      (by
        change (PolyTy.eraseBounds ⟨genV.length, Ty.closeOver genV ((S₁ ++ S₂).onTy τ₁)⟩).WF
        exact PolyTy.WF.eraseBounds
          (σ := ⟨genV.length, Ty.closeOver genV ((S₁ ++ S₂).onTy τ₁)⟩)
          (Ty.closeOver_preserves_bvars (vars := genV)
            (Subst.onTy_lc hS₁S₂lc hrhs_lc)))
      (fun σ' h => by cases h) ?_ rfl ?_
    · intro Xs hXfresh
      -- openBoundTyVars none = id; type is Mres.openVars Xs
      simp only [Expr.openBoundTyVars]
      have htype : Mres.openVars Xs =
          Ty.substFvars (genV.zip (Xs.map (Ty.fvar ·)))
            (Ty.eraseBounds ((S₁ ++ S₂).onTy τ₁)) := by
        rw [hMres_eq]
        simp only [PolyTy.openVars]
        exact Ty.openVars_closeOver_rename
          (Ty.IsLC.eraseBounds (Subst.onTy_lc hS₁S₂lc hrhs_lc))
          (by simp only [genV]; exact genVars_nodup) hXfresh.length
          (fun g hg hgX => hXfresh.avoid g hgX hg)
      rw [htype]
      have hfixE : (rhs.erase).substTyFvars (genV.zip (Xs.map (Ty.fvar ·))) = rhs.erase :=
        herase_subst rhs (genV.zip (Xs.map (Ty.fvar ·)))
      have hren := TypeOfHM.onSubst_fixed (genV.zip (Xs.map (Ty.fvar ·)))
        (fun p hp => by
          obtain ⟨_, hp2⟩ := List.of_mem_zip hp
          obtain ⟨x, _, hxeq⟩ := List.mem_map.mp hp2
          rw [← hxeq]; exact ContainsBvarsUpTo.fvar)
        hfixE hbase
      have hctxfix : Subst.onCtx (genV.zip (Xs.map (Ty.fvar ·)))
          ((S₁ ++ S₂).onCtx ctx).eraseBounds =
          ((S₁ ++ S₂).onCtx ctx).eraseBounds := by
        conv_lhs => rw [Subst.onCtx]
        refine congrArg (fun E => (⟨E, ((S₁ ++ S₂).onCtx ctx).eraseBounds.ctors⟩ : Ctx)) ?_
        exact Subst.onEnv_eq_self_of_fresh (fun p hp hc =>
          hgenV_env' p.1 (List.of_mem_zip hp).1
            ((Env.mem_freeVars_eraseBounds _ p.1).mp (by simpa [Ctx.eraseBounds] using hc)))
      rwa [hctxfix] at hren
    · simpa only [Mres, hschemeeq] using hbody_pack
  | letInAnn hσwf hΦN hrhs huni hesc1 hesc2 hbody =>
    expose_names
    simp only [Expr.tyFreeVars, Option.elim_some, List.mem_append] at hKe
    have hrle := Infer.frontier_le hrhs
    have hctx_pc : CtxBelow (N + σ.paramCount) ctx := fun M hM => (hbelow M hM).mono (by omega)
    have hσbody : Ty.BelowFvars Φ σ.body :=
      Ty.BelowFvars.of_freeVars_lt (fun v hv => hKΦ v (hKe v (.inl (.inl hv))))
    obtain ⟨hrhs_lc, hrhs_s⟩ := Infer.lc hrhs hctx
    set Ys := freshVars N σ.paramCount with hYs_def
    have hΦ_rhs : ∀ y ∈ (rhs.openTyVars Ys).tyFreeVars, y < N + σ.paramCount := by
      intro y hy
      rcases Expr.tyFreeVars_openTyVars hy with h | h
      · have := hKΦ y (hKe y (.inl (.inr h))); have := hΦN; omega
      · simp only [Ys] at h; have := freshVars_lt y h; omega
    have hSe_rhs : ∀ p ∈ S₁, p.1 ∉ (rhs.openTyVars Ys).tyFreeVars := by
      intro p hp hc
      rcases Expr.tyFreeVars_openTyVars hc with h | h
      · exact hSK p (List.mem_append_left _ (List.mem_append_left _ hp)) (hKe p.1 (.inl (.inr h)))
      · simp only [Ys] at h
        exact hesc1 p.1 h (List.mem_map.mpr ⟨p, List.mem_append_left _ hp, rfl⟩)
    obtain ⟨hr_τ, hr_s⟩ := Infer.belowFvars hrhs hctx_pc hΦ_rhs
    have hσopen : Ty.BelowFvars Φ₁ (σ.openVars Ys) :=
      Ty.openVars_belowFvars (hσbody.mono (by omega))
        (fun x hx => by simp only [Ys] at hx; have := freshVars_lt x hx; omega)
    have hSchk_below : ∀ p ∈ Schk, Ty.BelowFvars Φ₁ p.2 := UnifyRel.belowFvars huni hr_τ hσopen
    have hSchk_lc : ∀ p ∈ Schk, p.2.IsLC :=
      UnifyRel.lc huni hrhs_lc (PolyTy.openVars_isLC hσwf (by simp [Ys]))
    have hbodyWF : CtxWF { (Schk.onCtx (S₁.onCtx ctx)) with
        env := σ :: (Schk.onCtx (S₁.onCtx ctx)).env } := by
      intro M hM; rcases List.mem_cons.mp hM with rfl | hM
      · exact hσwf
      · exact (Subst.onCtx_wf hSchk_lc (Subst.onCtx_wf hrhs_s hctx)) M hM
    have hbodyBelow : CtxBelow Φ₁ { (Schk.onCtx (S₁.onCtx ctx)) with
        env := σ :: (Schk.onCtx (S₁.onCtx ctx)).env } := by
      intro M hM; rcases List.mem_cons.mp hM with rfl | hM
      · exact hσbody.mono (by omega)
      · exact (Subst.onCtx_below hSchk_below (le_refl _)
          (Subst.onCtx_below hr_s hrle hctx_pc)) M hM
    have hbody_s := (Infer.lc hbody hbodyWF).2
    have hYs_lt : ∀ y ∈ Ys, y < Φ₁ :=
      fun y hy => by simp only [Ys] at hy; have := freshVars_lt y hy; have := hrle; omega
    have hYs_bodyCtx : ∀ y ∈ Ys,
        ∀ M ∈ (σ :: (Schk.onCtx (S₁.onCtx ctx)).env), y ∉ M.body.freeVars := by
      intro y hy M hM
      rcases List.mem_cons.mp hM with rfl | hM
      · exact fun hc => by
          have := hKΦ y (hKe y (.inl (.inl hc)))
          simp only [Ys] at hy; have := freshVars_ge y hy; omega
      · exact fun hc => by
          simp only [Ys] at hy
          exact hesc2 y hy (Env.mem_freeVars_iff.mpr ⟨M, hM, hc⟩)
    have hYs_body : ∀ y ∈ Ys, y ∉ body.tyFreeVars :=
      fun y hy hc => by
        have := hKΦ y (hKe y (.inr hc))
        simp only [Ys] at hy; have := freshVars_ge y hy; omega
    have hS₂Ys : ∀ p ∈ S₂, p.1 ∉ Ys := by
      intro p hp hc
      exact Infer.dom_avoid hbody (hYs_lt p.1 hc) (hYs_bodyCtx p.1 hc) (hYs_body p.1 hc)
        (List.mem_map.mpr ⟨p, hp, rfl⟩)
    have hS₂Ysran : ∀ p ∈ S₂, ∀ u ∈ p.2.freeVars, u ∉ Ys := by
      intro p hp u hu hc
      exact (Infer.eOut_avoid hbody (w := u) (hYs_lt u hc) (hYs_bodyCtx u hc)
        (hYs_body u hc)).1 p hp hu
    have hSYs : ∀ p ∈ S₁ ++ Schk ++ S₂, p.1 ∉ Ys := by
      intro p hp
      rcases List.mem_append.mp hp with hp | hp
      · exact fun hc => by
          simp only [Ys] at hc
          exact hesc1 p.1 hc (List.mem_map.mpr ⟨p, hp, rfl⟩)
      · exact hS₂Ys p hp
    have hSfix_σopen : ∀ p ∈ S₁ ++ Schk ++ S₂, p.1 ∉ (σ.openVars Ys).freeVars := by
      intro p hp hc
      rcases Ty.freeVars_openVars_subset p.1 hc with h | h
      · exact hSK p hp (hKe p.1 (.inl (.inl h)))
      · exact hSYs p hp h
    have hSchk_fix : Schk.onTy (σ.openVars Ys) = σ.openVars Ys :=
      Ty.substFvars_eq_self_of_no_key
        (fun p hp => hSfix_σopen p (List.mem_append_left _ (List.mem_append_right _ hp)))
    have hS₂fix : S₂.onTy (σ.openVars Ys) = σ.openVars Ys :=
      Ty.substFvars_eq_self_of_no_key (fun p hp => hSfix_σopen p (List.mem_append_right _ hp))
    have hrhs_sound := Infer.sound hrhs hctx hctx_pc (K ++ Ys)
      (fun k hk => by
        rcases List.mem_append.mp hk with h | h
        · have := hKΦ k h; have := hΦN; omega
        · simp only [Ys] at h; have := freshVars_lt k h; omega)
      (fun y hy => by
        rcases Expr.tyFreeVars_openTyVars hy with h | h
        · exact List.mem_append_left _ (hKe y (.inl (.inr h)))
        · simp only [Ys]; exact List.mem_append_right _ h)
      (fun p hp hc => by
        rcases List.mem_append.mp hc with h | h
        · exact hSK p (List.mem_append_left _ (List.mem_append_left _ hp)) h
        · simp only [Ys] at h
          exact hesc1 p.1 h (List.mem_map.mpr ⟨p, List.mem_append_left _ hp, rfl⟩))
    have hS₁τ₁ : S₁.onTy τ₁ = τ₁ := Ty.substFvars_eq_self_of_no_key (fun p hp =>
      (Infer.eliminates hrhs hctx_pc hΦ_rhs hSe_rhs).2 p hp)
    have hrhs_sound' : TypeOfHM (S₁.onCtx ctx).eraseBounds (rhs.openTyVars Ys).erase
        (Ty.eraseBounds τ₁) := by
      rwa [hS₁τ₁] at hrhs_sound
    have hr1 := TypeOfHM.onSubst_eraseBounds_fixed (ctx := S₁.onCtx ctx)
      (e := (rhs.openTyVars Ys).erase) (τ := τ₁) Schk hSchk_lc
      (herase_subst (rhs.openTyVars Ys) Schk)
      (by simpa only [herase_eraseBounds (rhs.openTyVars Ys)] using hrhs_sound')
    have hu : Ty.eraseBounds (Schk.onTy τ₁) = Ty.eraseBounds (Schk.onTy (σ.openVars Ys)) :=
      huni.unifies
    have hr1' : TypeOfHM ((S₁ ++ Schk).onCtx ctx).eraseBounds
        ((rhs.openTyVars Ys).erase) (Ty.eraseBounds (σ.openVars Ys)) := by
      have key := hr1
      rwa [← Subst.onCtx_append, hu, hSchk_fix, herase_eraseBounds (rhs.openTyVars Ys)] at key
    have hr2 := TypeOfHM.onSubst_eraseBounds_fixed (ctx := (S₁ ++ Schk).onCtx ctx)
      (e := (rhs.openTyVars Ys).erase) (τ := σ.openVars Ys) S₂ hbody_s
      (herase_subst (rhs.openTyVars Ys) S₂)
      (by simpa only [herase_eraseBounds (rhs.openTyVars Ys)] using hr1')
    have hr2' : TypeOfHM ((S₁ ++ Schk ++ S₂).onCtx ctx).eraseBounds
        ((rhs.openTyVars Ys).erase) (Ty.eraseBounds (σ.openVars Ys)) := by
      have key := hr2
      rw [hS₂fix] at key
      rw [← Subst.onCtx_append] at key
      simpa only [herase_eraseBounds (rhs.openTyVars Ys)] using key
    have hYs_env : ∀ y ∈ Ys, y ∉ ((S₁ ++ Schk ++ S₂).onCtx ctx).env.freeVars := by
      intro y hy hc
      rw [show (S₁ ++ Schk ++ S₂).onCtx ctx = S₂.onCtx ((S₁ ++ Schk).onCtx ctx) from by
            rw [show (S₁ ++ Schk ++ S₂ : Subst) = (S₁ ++ Schk) ++ S₂ from rfl,
                Subst.onCtx_append],
          Env.mem_freeVars_iff] at hc
      obtain ⟨M, hM, hyM⟩ := hc
      rw [show (S₂.onCtx ((S₁ ++ Schk).onCtx ctx)).env
            = ((S₁ ++ Schk).onCtx ctx).env.map (Subst.onPolyTy S₂) from rfl,
        List.mem_map] at hM
      obtain ⟨M₀, hM₀, rfl⟩ := hM
      refine Subst.notMemOnTy (fun p hp hyp => hS₂Ysran p hp y hyp hy) (fun hc2 => ?_) hyM
      rw [Subst.onCtx_append] at hM₀
      simp only [Ys] at hy
      exact hesc2 y hy (Env.mem_freeVars_iff.mpr ⟨M₀, hM₀, hc2⟩)
    have hYs_σ : ∀ y ∈ Ys, y ∉ σ.body.freeVars := by
      intro y hy hc
      have := hKΦ y (hKe y (.inl (.inl hc)))
      simp only [Ys] at hy; have := freshVars_ge y hy; omega
    have hS₂σ : Subst.onPolyTy S₂ σ = σ := by
      simp only [Subst.onPolyTy]
      rw [show S₂.onTy σ.body = σ.body from
        Ty.substFvars_eq_self_of_no_key (fun p hp hc =>
          hSK p (List.mem_append_right _ hp) (hKe p.1 (.inl (.inl hc))))]
    have heqbodyctx : Subst.onCtx S₂ { (Schk.onCtx (S₁.onCtx ctx)) with
          env := σ :: (Schk.onCtx (S₁.onCtx ctx)).env }
        = { (S₁ ++ Schk ++ S₂).onCtx ctx with
          env := σ :: ((S₁ ++ Schk ++ S₂).onCtx ctx).env } := by
      rw [show (S₁ ++ Schk ++ S₂) = (S₁ ++ Schk) ++ S₂ from rfl, Subst.onCtx_append,
        Subst.onCtx_append]
      simp only [Subst.onCtx, Subst.onEnv, List.map_cons, hS₂σ]
    have hbody_sound := Infer.sound hbody hbodyWF hbodyBelow K
      (fun k hk => by have := hKΦ k hk; have := hΦN; have := hrle; omega)
      (fun y hy => hKe y (.inr hy)) (fun p hp => hSK p (List.mem_append_right _ hp))
    have hbody_sound' : TypeOfHM
        (S₂.onCtx { (Schk.onCtx (S₁.onCtx ctx)) with
            env := σ :: (Schk.onCtx (S₁.onCtx ctx)).env }).eraseBounds
        body.erase (Ty.eraseBounds τ) := by
      have hS₂τ : S₂.onTy τ = τ := Ty.substFvars_eq_self_of_no_key (fun p hp =>
        (Infer.eliminates hbody hbodyBelow (fun y hy => by
            have := hKΦ y (hKe y (.inr hy)); have := hΦN; have := hrle; omega)
          (fun p hp hc => hSK p (List.mem_append_right _ hp) (hKe p.1 (.inr hc)))).2 p hp)
      rwa [hS₂τ] at hbody_sound
    have hbody_pack : TypeOfHM
        { ((S₁ ++ Schk ++ S₂).onCtx ctx).eraseBounds with
          env := PolyTy.eraseBounds σ
            :: ((S₁ ++ Schk ++ S₂).onCtx ctx).env.eraseBounds }
        body.erase (Ty.eraseBounds τ) := by
      have key := hbody_sound'
      have hctx_eq :
          (S₂.onCtx { (Schk.onCtx (S₁.onCtx ctx)) with
              env := σ :: (Schk.onCtx (S₁.onCtx ctx)).env }).eraseBounds
          = { ((S₁ ++ Schk ++ S₂).onCtx ctx).eraseBounds with
              env := PolyTy.eraseBounds σ
                :: ((S₁ ++ Schk ++ S₂).onCtx ctx).env.eraseBounds } := by
        rw [heqbodyctx]
        simp only [Ctx.eraseBounds, Env.eraseBounds, List.map_cons]
      rwa [hctx_eq] at key
    rw [Expr.erase_letIn]
    refine TypeOfHM.letIn (M := PolyTy.eraseBounds σ) (L := Ys)
      (PolyTy.WF.eraseBounds hσwf)
      (fun σ' h => by cases h) ?_ rfl hbody_pack
    intro Xs hXfresh
    simp only [Expr.openBoundTyVars]
    have hYsX : ∀ y ∈ Ys, y ∉ Xs := fun y hy hc => hXfresh.avoid y hc hy
    have hXlen : Xs.length = Ys.length := by
      have h1 := hXfresh.length
      simp only [PolyTy.eraseBounds_paramCount, Ys, freshVars_length] at h1 ⊢
      exact h1
    have htypeeq : Subst.onTy (Ys.zip (Xs.map (Ty.fvar ·)))
          (Ty.eraseBounds (σ.openVars Ys)) =
          Ty.eraseBounds (σ.openVars Xs) := by
      have h := Ty.openWith_eq_substFvars_openVars (ty := σ.body)
        (Vs := Xs.map (Ty.fvar ·)) (Xs := Ys)
        ⟨by rw [List.length_map, hXlen], fun V hV => by
          obtain ⟨x, _, rfl⟩ := List.mem_map.mp hV; exact ContainsBvarsUpTo.fvar⟩
        (by simp only [Ys]; exact freshVars_nodup) hYs_σ
        (fun y hy hc => hYsX y hy (Ty.mem_freeVarsList_map_fvar.mp hc))
      have h' : PolyTy.openVars Xs σ =
          Ty.substFvars (Ys.zip (Xs.map (Ty.fvar ·))) (σ.openVars Ys) := by
        simp only [PolyTy.openVars]
        rw [Ty.openVars_eq_openWith]; exact h
      have hcomm := Ty.eraseBounds_substFvars (Ys.zip (Xs.map (Ty.fvar ·))) (σ.openVars Ys)
      rw [List.map_eraseBounds_zip_fvar] at hcomm
      calc Subst.onTy (Ys.zip (Xs.map (Ty.fvar ·))) (Ty.eraseBounds (σ.openVars Ys))
          = Ty.eraseBounds (Ty.substFvars (Ys.zip (Xs.map (Ty.fvar ·))) (σ.openVars Ys)) :=
            hcomm.symm
        _ = Ty.eraseBounds (σ.openVars Xs) := by rw [← h']
    have hren := TypeOfHM.onSubst (Ys.zip (Xs.map (Ty.fvar ·)))
      (fun p hp => by
        obtain ⟨_, hp2⟩ := List.of_mem_zip hp
        obtain ⟨x, _, hxeq⟩ := List.mem_map.mp hp2
        rw [← hxeq]; exact ContainsBvarsUpTo.fvar)
      hr2'
    have hctxfix : Subst.onCtx (Ys.zip (Xs.map (Ty.fvar ·)))
          ((S₁ ++ Schk ++ S₂).onCtx ctx).eraseBounds =
          ((S₁ ++ Schk ++ S₂).onCtx ctx).eraseBounds := by
      conv_lhs => rw [Subst.onCtx]
      refine congrArg (fun E =>
        (⟨E, ((S₁ ++ Schk ++ S₂).onCtx ctx).eraseBounds.ctors⟩ : Ctx)) ?_
      exact Subst.onEnv_eq_self_of_fresh (fun p hp hc =>
        hYs_env p.1 (List.of_mem_zip hp).1
          ((Env.mem_freeVars_eraseBounds _ p.1).mp (by simpa [Ctx.eraseBounds] using hc)))
    have hgoal_ty : (PolyTy.eraseBounds σ).openVars Xs =
        Ty.eraseBounds (σ.openVars Xs) := (PolyTy.eraseBounds_openVars Xs σ).symm
    rw [hctxfix] at hren
    rw [herase_subst (rhs.openTyVars Ys) (Ys.zip (Xs.map (Ty.fvar ·))),
      Expr.erase_openTyVars Ys rhs, htypeeq] at hren
    rw [hgoal_ty]
    exact hren
  | match_ hscrut hne hbr =>
    expose_names
    simp only [Expr.tyFreeVars, List.mem_append] at hKe
    obtain ⟨hτs_lc, hS₁⟩ := Infer.lc hscrut hctx
    have hle1 := Infer.frontier_le hscrut
    have hscrut_below := Infer.belowFvars hscrut hbelow (fun y hy => hKΦ y (hKe y (.inl hy)))
    have hctx1 := Subst.onCtx_wf hS₁ hctx
    have hbelow1 := Subst.onCtx_below hscrut_below.2 hle1 hbelow
    have hS₂lc := (InferBranches.lc hbr hctx1 hτs_lc ContainsBvarsUpTo.fvar).2
    have hscrut_sound := Infer.sound hscrut hctx hbelow K hKΦ (fun y hy => hKe y (.inl hy))
      (fun p hp => hSK p (List.mem_append_left _ hp))
    have hscrut_sound' : TypeOfHM (S₁.onCtx ctx).eraseBounds scrut.erase (Ty.eraseBounds τs) := by
      have hS₁τs : S₁.onTy τs = τs := Ty.substFvars_eq_self_of_no_key (fun p hp =>
        (Infer.eliminates hscrut hbelow (fun y hy => hKΦ y (hKe y (.inl hy)))
          (fun p hp hc => hSK p (List.mem_append_left _ hp) (hKe p.1 (.inl hc)))).2 p hp)
      rwa [hS₁τs] at hscrut_sound
    have hscrut_decl := TypeOfHM.onSubst_eraseBounds_fixed (ctx := S₁.onCtx ctx)
      (e := scrut.erase) (τ := τs) S₂ hS₂lc (herase_subst scrut S₂)
      (by simpa only [herase_eraseBounds scrut] using hscrut_sound')
    have hbr_sound := InferBranches.sound hbr hctx1
      (fun M hM => (hbelow1 M hM).mono (by omega))
      hτs_lc ContainsBvarsUpTo.fvar
      (hscrut_below.1.mono (by omega)) (.fvar (by omega)) K
      (fun k hk => by have := hKΦ k hk; omega)
      (fun y hy => hKe y (.inr hy)) (fun p hp => hSK p (List.mem_append_right _ hp))
    simp only [Expr.erase_match]
    refine TypeOfHM.match_
      (by
        have hctx_eq : (S₂.onCtx (S₁.onCtx ctx)).eraseBounds =
            ((S₁ ++ S₂).onCtx ctx).eraseBounds := by rw [← Subst.onCtx_append]
        rwa [hctx_eq, herase_eraseBounds scrut] at hscrut_decl)
      (by
        intro hcontra
        obtain ⟨⟨p, b⟩, rest, hb⟩ := List.exists_cons_of_ne_nil hne
        simp [hb] at hcontra) ?_
    intro br hbr_mem
    obtain ⟨pb, hpb, rfl⟩ := List.mem_map.mp hbr_mem
    have hbrp := hbr_sound pb hpb
    have hctx_eq : (S₂.onCtx (S₁.onCtx ctx)).eraseBounds =
        ((S₁ ++ S₂).onCtx ctx).eraseBounds := by rw [← Subst.onCtx_append]
    rwa [← hctx_eq]
  | letRec hwfanns hgroup hceiling hbody =>
    expose_names
    simp only [Expr.tyFreeVars, List.mem_append] at hKe
    have hlen : bindings.length = anns.length := by
      have h₁ := InferRecGroup.length_eq hgroup
      rw [RecSpec.init_length] at h₁
      exact h₁
    have hinit_spec : ∀ s ∈ RecSpec.init Φ anns,
        ∃ j, j < anns.length ∧ s = RecSpec.mono (.fvar (Φ + j)) := by
      intro s hs
      rcases List.mem_iff_getElem.mp hs with ⟨j, hj, rfl⟩
      have hlenj : j < anns.length := by
        have h₂ := RecSpec.init_length Φ anns
        rw [h₂] at hj
        exact hj
      have hget : (RecSpec.init Φ anns)[j] = RecSpec.mono (.fvar (Φ + j)) := by
        have h₁ := List.getElem?_eq_getElem hj
        rw [RecSpec.init_getElem? Φ anns j, List.getElem?_eq_getElem hlenj] at h₁
        injection h₁ with hEq
        exact hEq.symm
      exact ⟨j, hlenj, hget⟩
    have hspecs_init : ∀ s ∈ RecSpec.init Φ anns, s.BelowFvars (Φ + bindings.length) := by
      intro s hs
      obtain ⟨j, hlenj, hsj⟩ := hinit_spec s hs
      rw [hsj]
      refine Ty.BelowFvars.fvar ?_
      omega
    have hspecsLC : ∀ s ∈ RecSpec.init Φ anns, s.LC := by
      intro s hs
      obtain ⟨j, hlenj, hsj⟩ := hinit_spec s hs
      rw [hsj]
      exact ContainsBvarsUpTo.fvar
    have hgrpLe : Φ + bindings.length ≤ Φ₁ := InferRecGroup.frontier_le hgroup
    have hctxGroup : CtxBelow (Φ + bindings.length)
        { ctx with env := (RecSpec.init Φ anns).map (RecSpec.rhsEntry [] []) ++ ctx.env } := by
      intro M hM
      rcases List.mem_append.mp hM with hM1 | hM2
      · obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hM1
        exact RecSpec.rhsEntry_nil_belowFvars (hspecs_init s hs)
      · exact (hbelow M hM2).mono (by omega)
    have hctxG : CtxWF
        { ctx with env := (RecSpec.init Φ anns).map (RecSpec.rhsEntry [] []) ++ ctx.env } := by
      intro M hM
      rcases List.mem_append.mp hM with hM1 | hM2
      · obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hM1
        exact RecSpec.rhsEntry_nil_wf (hspecsLC s hs)
      · exact hctx M hM2
    have htfv_group : ∀ y ∈ Expr.tyFreeVars.RecGroup.tyFreeVars bindings,
        y < Φ + bindings.length := by
      intro y hy
      have := hKΦ y (hKe y (.inl (.inr hy)))
      omega
    have hS₁ : ∀ p ∈ S₁, Ty.BelowFvars Φ₁ p.2 :=
      InferRecGroup.belowFvars hgroup hctxGroup hspecs_init htfv_group
    have hS₁_dom : ∀ p ∈ S₁, p.1 < Φ₁ :=
      InferRecGroup.dom_below hgroup hctxGroup hspecs_init htfv_group
    have hS₁lc : ∀ p ∈ S₁, p.2.IsLC :=
      InferRecGroup.lc hgroup hctxG hspecsLC
    have hspecsEnv : ∀ s ∈ RecSpec.init Φ anns, ∀ y ∈ s.freeVars,
        y ∈ ({ ctx with env := (RecSpec.init Φ anns).map (RecSpec.rhsEntry [] []) ++ ctx.env }).env.freeVars := by
      intro s hs y hy
      obtain ⟨j, hlenj, hsj⟩ := hinit_spec s hs
      rw [hsj] at hy
      simp only [RecSpec.freeVars, Ty.freeVars, List.mem_singleton] at hy
      subst hy
      refine Env.mem_freeVars_iff.mpr ?_
      refine ⟨RecSpec.rhsEntry [] [] (RecSpec.mono (.fvar (Φ + j))),
        List.mem_append_left _ (List.mem_map.mpr ⟨RecSpec.mono (.fvar (Φ + j)),
          ?hmem, rfl⟩), ?_⟩
      · refine List.mem_iff_getElem.mpr ⟨j, ?_, ?_⟩
        · rw [RecSpec.init_length Φ anns]
          exact hlenj
        · have hlen_init : j < (RecSpec.init Φ anns).length := by
            rw [RecSpec.init_length Φ anns]
            exact hlenj
          have hg : (RecSpec.init Φ anns)[j]? = some (RecSpec.mono (.fvar (Φ + j))) := by
            rw [RecSpec.init_getElem? Φ anns j]
            simp [hlenj]
          have hge : (RecSpec.init Φ anns)[j]? = some ((RecSpec.init Φ anns)[j]) :=
            List.getElem?_eq_getElem hlen_init
          have hg' : some ((RecSpec.init Φ anns)[j]) = some (RecSpec.mono (.fvar (Φ + j))) := by
            rw [hge] at hg
            exact hg
          simpa using hg'
      · simp [RecSpec.rhsEntry, PolyTy.mkTrivial, Ty.renameG, Ty.substFvars, Ty.freeVars]
    have hgrp := InferRecGroup.sound hgroup hctxG hctxGroup hspecsLC hspecs_init hspecsEnv K
      (fun k hk => by have := hKΦ k hk; omega) (fun y hy => hKe y (.inl (.inr hy)))
      (fun σ hσ y hy => by
        rcases hinit_spec (RecSpec.poly σ) hσ with ⟨j, hj, hc⟩
        cases hc)
      (fun p hp => hSK p (List.mem_append_left _ hp))
    -- local abbreviations for the post-S₁ specs, the pool, the erased+post-S₂ specs
    let specs₁ : List RecSpec := (RecSpec.init Φ anns).map (RecSpec.onSubst S₁)
    let G : List Nat := genGroupVars (RecGroup.rigidVars anns bindings) (S₁.onCtx ctx).env
        (RecSpecs.monoTys specs₁)
    let specsE : List RecSpec := (specs₁.map (RecSpec.onSubst S₂)).map RecSpec.eraseBounds
    let ctx' : Ctx := ((S₁ ++ S₂).onCtx ctx).eraseBounds
    let bs' : List Expr := bindings.map Expr.erase
    let anns' : List (Option PolyTy) := bindings.map (fun _ => none)
    have hspecs_post : ∀ s' ∈ specs₁, s'.BelowFvars Φ₁ := by
      intro s' hs'
      obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hs'
      exact RecSpec.BelowFvars.onSubst hS₁ ((hspecs_init s hs).mono hgrpLe)
    have hbodyWF : CtxWF
        { (S₁.onCtx ctx) with
          env := RecSpecs.ceilingSchemes G anns specs₁ ++ (S₁.onCtx ctx).env } := by
      intro M hM
      rcases List.mem_append.mp hM with hM1 | hM2
      · obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hM1
        have hpa : p.1 ∈ anns := (List.of_mem_zip hp).1
        have hps : p.2 ∈ specs₁ := (List.of_mem_zip hp).2
        cases p with
        | mk a s =>
          cases a with
          | some σ => exact hwfanns σ hpa
          | none =>
            obtain ⟨s₀, hs₀, rfl⟩ := List.mem_map.mp hps
            exact RecSpec.bodyScheme_wf (RecSpec.LC.onSubst hS₁lc (hspecsLC s₀ hs₀))
      · exact Subst.onCtx_wf hS₁lc hctx M hM2
    have hbodyBelow : CtxBelow Φ₁
        { (S₁.onCtx ctx) with
          env := RecSpecs.ceilingSchemes G anns specs₁ ++ (S₁.onCtx ctx).env } := by
      intro M hM
      rcases List.mem_append.mp hM with hM1 | hM2
      · obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hM1
        have hpa : p.1 ∈ anns := (List.of_mem_zip hp).1
        have hps : p.2 ∈ specs₁ := (List.of_mem_zip hp).2
        cases p with
        | mk a s =>
          cases a with
          | some σ =>
            refine Ty.BelowFvars.of_freeVars_lt (fun v hv => ?_)
            have hann := Expr.scheme_body_mem_annList_tyFreeVars hpa hv
            have := hKΦ v (hKe v (.inl (.inl hann)))
            omega
          | none =>
            exact RecSpec.bodyScheme_belowFvars (hspecs_post s hps)
      · exact Subst.onCtx_below hS₁ (by omega) hbelow M hM2
    have hS₂lc : ∀ p ∈ S₂, p.2.IsLC := (Infer.lc hbody hbodyWF).2
    have hrhs_onSubst : ∀ (S : Subst) (s : RecSpec), s ∈ RecSpec.init Φ anns →
        S.onPolyTy (RecSpec.rhsEntry [] [] s) = RecSpec.rhsEntry [] [] (RecSpec.onSubst S s) := by
      intro S s hs
      obtain ⟨j, hlenj, hsj⟩ := hinit_spec s hs
      rw [hsj]
      simp [RecSpec.rhsEntry, RecSpec.onSubst, Subst.onPolyTy, Ty.renameG, Ty.substFvars,
        PolyTy.mkTrivial]
    have hctxG_eq : S₁.onCtx { ctx with env := (RecSpec.init Φ anns).map (RecSpec.rhsEntry [] []) ++ ctx.env }
        = { (S₁.onCtx ctx) with env := specs₁.map (RecSpec.rhsEntry [] []) ++ (S₁.onCtx ctx).env } := by
      simp only [Subst.onCtx, Subst.onEnv, List.map_append, List.map_map, specs₁]
      congr 1
      congr 1
      apply List.map_congr_left
      intro s hs
      exact hrhs_onSubst S₁ s hs
    have hspecsE_mono : ∀ s ∈ specsE, ∃ τ, s = RecSpec.mono τ := by
      intro s hs
      obtain ⟨s₁, hs₁, hsub₁⟩ := List.mem_map.mp hs
      obtain ⟨s₀, hs₀, hsub₀⟩ := List.mem_map.mp hs₁
      obtain ⟨s₀₀, hs₀₀, hsub₀₀⟩ := List.mem_map.mp hs₀
      obtain ⟨j, hlenj, hsj⟩ := hinit_spec s₀₀ hs₀₀
      rw [hsj] at hsub₀₀
      rw [← hsub₀₀] at hsub₀
      rw [← hsub₀] at hsub₁
      rw [← hsub₁]
      exact ⟨Ty.eraseBounds (S₂.onTy (S₁.onTy (.fvar (Φ + j)))), rfl⟩
    -- the all-mono witnesses `τsE`: one solved monotype per member
    let monoTy : RecSpec → Ty := fun s => match s with | .mono τ => τ | .poly σ => σ.body
    let τsE : List Ty := specsE.map monoTy
    have hspecsE_re : specsE = τsE.map RecSpec.mono := by
      dsimp [τsE, monoTy]
      rw [List.map_map]
      conv_lhs => rw [← List.map_id specsE]
      apply List.map_congr_left
      intro s hs
      obtain ⟨τ, hτ⟩ := hspecsE_mono s hs
      rw [hτ]
      rfl
    have hctxτ : (τsE.map RecSpec.mono).map (RecSpec.rhsEntry [] [])
        = specsE.map (RecSpec.rhsEntry [] []) := by
      rw [← hspecsE_re]
    have hmono : ∀ p ∈ bs'.zip τsE,
        TypeOfHM ⟨(τsE.map RecSpec.mono).map (RecSpec.rhsEntry [] []) ++ ctx'.env, ctx'.ctors⟩
          p.1 p.2 := by
      intro p hp
      rcases List.mem_iff_getElem.mp hp with ⟨j, hjp, hpeq⟩
      have hlen_b' : j < bs'.length :=
        lt_of_lt_of_le hjp (by rw [List.length_zip]; exact min_le_left _ _)
      have hlen_t' : j < τsE.length :=
        lt_of_lt_of_le hjp (by rw [List.length_zip]; exact min_le_right _ _)
      have hzip : (bs'[j]'(hlen_b'), τsE[j]'(hlen_t')) = p := by
        rw [List.getElem_zip] at hpeq
        exact hpeq
      cases hzip
      have hlen_b : j < bindings.length := by
        rwa [List.length_map] at hlen_b'
      have hlen_init : j < (RecSpec.init Φ anns).length := by
        rw [RecSpec.init_length]
        omega
      have hlen_specs₁ : j < specs₁.length := by
        dsimp [τsE] at hlen_t'
        rwa [List.length_map, List.length_map, List.length_map] at hlen_t'
      have hlen_anns : j < anns.length := by
        exact lt_of_lt_of_le hlen_b (by rw [hlen])
      have hinit_j : (RecSpec.init Φ anns)[j] = RecSpec.mono (.fvar (Φ + j)) := by
        have hg : (RecSpec.init Φ anns)[j]? = some (RecSpec.mono (.fvar (Φ + j))) := by
          rw [RecSpec.init_getElem? Φ anns j]
          simp [hlen_anns]
        have hge : (RecSpec.init Φ anns)[j]? = some ((RecSpec.init Φ anns)[j]) :=
          List.getElem?_eq_getElem hlen_init
        have hg' : some ((RecSpec.init Φ anns)[j]) = some (RecSpec.mono (.fvar (Φ + j))) := by
          rw [hge] at hg
          exact hg
        simpa using hg'
      have hspecs₁j : specs₁[j] = RecSpec.mono (S₁.onTy (.fvar (Φ + j))) := by
        rw [List.getElem_map]
        rw [hinit_j]
        rfl
      have hpair_mem : (bindings[j], specs₁[j]) ∈ bindings.zip specs₁ := by
        refine List.mem_iff_getElem.mpr ⟨j, ?_, ?_⟩
        · rw [List.length_zip]
          exact lt_min hlen_b hlen_specs₁
        · rw [List.getElem_zip]
      have hgrp_p := hgrp (bindings[j], specs₁[j]) hpair_mem (S₁.onTy (.fvar (Φ + j))) hspecs₁j
      have hg1 : TypeOfHM
          { (S₁.onCtx ctx) with env := specs₁.map (RecSpec.rhsEntry [] []) ++ (S₁.onCtx ctx).env }.eraseBounds
          (bindings[j]).erase (Ty.eraseBounds (S₁.onTy (.fvar (Φ + j)))) := by
        rwa [hctxG_eq] at hgrp_p
      have hg2 := TypeOfHM.onSubst_eraseBounds_fixed
        (ctx := { (S₁.onCtx ctx) with env := specs₁.map (RecSpec.rhsEntry [] []) ++ (S₁.onCtx ctx).env })
        (e := (bindings[j]).erase) (τ := S₁.onTy (.fvar (Φ + j))) S₂ hS₂lc
        (herase_subst (bindings[j]) S₂) (by simpa only [herase_eraseBounds (bindings[j])] using hg1)
      have hmono_ctx : (S₂.onCtx { (S₁.onCtx ctx) with
            env := specs₁.map (RecSpec.rhsEntry [] []) ++ (S₁.onCtx ctx).env }).eraseBounds
          = ⟨specsE.map (RecSpec.rhsEntry [] []) ++ ctx'.env, ctx'.ctors⟩ := by
        have hS₂onCtx : S₂.onCtx { (S₁.onCtx ctx) with
              env := specs₁.map (RecSpec.rhsEntry [] []) ++ (S₁.onCtx ctx).env }
            = { (S₂.onCtx (S₁.onCtx ctx)) with
              env := S₂.onEnv (specs₁.map (RecSpec.rhsEntry [] []) ++ (S₁.onCtx ctx).env) } := by
          simp only [Subst.onCtx, Subst.onEnv, List.map_append]
        rw [hS₂onCtx]
        rw [← Subst.onCtx_append]
        simp only [Ctx.eraseBounds, Subst.onEnv, List.map_append, Env.eraseBounds, List.map_map,
          specsE]
        congr 1
        · congr 1
          · apply List.map_congr_left
            intro s hs
            obtain ⟨s₀, hs₀, rfl⟩ := List.mem_map.mp hs
            obtain ⟨j, hlenj, hsj⟩ := hinit_spec s₀ hs₀
            rw [hsj]
            simp [RecSpec.rhsEntry, RecSpec.onSubst, RecSpec.eraseBounds, Subst.onPolyTy,
              Ty.renameG, Ty.substFvars, PolyTy.eraseBounds_mkTrivial, PolyTy.mkTrivial,
              PolyTy.eraseBounds]
          · simp only [Ctx.eraseBounds, Subst.onCtx, Subst.onEnv, Env.eraseBounds, List.map_map,
              ctx']
            apply List.map_congr_left
            intro M hM
            simp [Subst.onPolyTy, Subst.onTy_append, PolyTy.eraseBounds]
      have hlen_e' : j < specsE.length := by
        dsimp [τsE] at hlen_t'
        rwa [List.length_map] at hlen_t'
      have hspecsE_j : specsE[j]'(hlen_e') =
          RecSpec.mono (Ty.eraseBounds (S₂.onTy (S₁.onTy (.fvar (Φ + j))))) := by
        rw [List.getElem_map]
        rw [List.getElem_map]
        rw [hspecs₁j]
        rfl
      have hτsE_j : τsE[j]'(hlen_t') = Ty.eraseBounds (S₂.onTy (S₁.onTy (.fvar (Φ + j)))) := by
        rw [List.getElem_map]
        rw [hspecsE_j]
      have hg3 : TypeOfHM ⟨(τsE.map RecSpec.mono).map (RecSpec.rhsEntry [] []) ++ ctx'.env, ctx'.ctors⟩
          (bindings[j]).erase (τsE[j]'(hlen_t')) := by
        rw [hctxτ]
        rw [hτsE_j]
        rw [hmono_ctx] at hg2
        simpa [herase_eraseBounds (bindings[j])] using hg2
      have hbsj : (bs'[j]'(hlen_b'), τsE[j]'(hlen_t')).1 = (bindings[j]).erase := by
        rw [List.getElem_map]
      rw [hbsj]
      exact hg3
    -- pool facts: S₂ avoids the gen-var pool G (domain and range)
    have hsubstFvar_preserve : ∀ {Z : Nat} {U τ : Ty} {u : Nat}, u ≠ Z → u ∈ τ.freeVars →
        u ∈ (Ty.substFvar Z U τ).freeVars := by
      intro Z U τ u hZ hτ
      induction τ using Ty.rec_strong with
      | fvar m =>
        simp only [Ty.substFvar, Ty.freeVars, List.mem_singleton] at hτ ⊢
        subst hτ
        simp [hZ, Ty.freeVars]
      | prim p => simp [Ty.substFvar, Ty.freeVars] at hτ
      | bvar i => simp [Ty.substFvar, Ty.freeVars] at hτ
      | arrow a b iha ihb =>
        simp only [Ty.substFvar, Ty.freeVars, List.mem_dedup, List.mem_append] at hτ ⊢
        rcases hτ with hτ | hτ
        · exact Or.inl (iha hτ)
        · exact Or.inr (ihb hτ)
      | customTy nm tys ih =>
        simp only [Ty.substFvar, Ty.freeVars, TyList.substFvar_eq_map] at hτ ⊢
        rw [mem_TyList_freeVars] at hτ ⊢
        obtain ⟨t, ht, hτt⟩ := hτ
        exact ⟨Ty.substFvar Z U t, List.mem_map.mpr ⟨t, ht, rfl⟩, ih t ht hτt⟩
      | bl lo hi e ih =>
        simp only [Ty.substFvar, Ty.freeVars] at hτ ⊢
        exact ih hτ
    have honTy_preserve : ∀ (S : Subst) (τ : Ty) (u : Nat), u ∈ τ.freeVars →
        u ∉ S.map Prod.fst → u ∈ (S.onTy τ).freeVars := by
      intro S τ u hτ hdom
      induction S generalizing τ with
      | nil => simpa [Subst.onTy] using hτ
      | cons hd tl ih =>
        obtain ⟨Z, U⟩ := hd
        have hZ : u ≠ Z := by
          intro hc
          exact hdom (List.mem_map.mpr ⟨(Z, U), List.mem_cons_self, hc.symm⟩)
        have hdom' : u ∉ tl.map Prod.fst := fun hc => by
          obtain ⟨q, hq, hqeq⟩ := List.mem_map.mp hc
          exact hdom (List.mem_map.mpr ⟨q, List.mem_cons_of_mem _ hq, hqeq⟩)
        exact ih (Ty.substFvar Z U τ) (hsubstFvar_preserve hZ hτ) hdom'
    have hgenGroup_avoid : ∀ {G : List Nat} {τ : Ty} {g : Nat}, g ∈ G → g ∉ (PolyTy.genGroup G τ).body.freeVars := by
      intro G τ g hg hc
      have hτ : g ∈ τ.freeVars := Ty.freeVars_closeOver_subset (by simpa [PolyTy.genGroup] using hc)
      have hgfilter : g ∈ Ty.genFilter G τ := by
        exact List.mem_filter.mpr ⟨hg, by simp [hτ]⟩
      exact Ty.not_mem_closeOver_freeVars hgfilter (by simpa [PolyTy.genGroup] using hc)
    have hcloseOver_preserve : ∀ {gs : List Nat} {τ : Ty} {g : Nat}, g ∈ τ.freeVars → g ∉ gs →
        g ∈ (Ty.closeOver gs τ).freeVars := by
      intro gs τ g hτ hg
      induction τ using Ty.rec_strong with
      | fvar n =>
        rw [Ty.closeOver.eq_6]
        cases h_idx : gs.idxOf? n with
        | some i =>
          simp only [Ty.freeVars, List.mem_singleton] at hτ
          have hgn : g = n := hτ
          have hn : n ∈ gs := by
            by_contra hn
            have hnone : gs.idxOf? n = none := List.idxOf?_eq_none_iff.mpr hn
            rw [h_idx] at hnone
            simp at hnone
          simp [Ty.freeVars]
          exact hg (by simpa [hgn] using hn)
        | none =>
          simp only [Ty.freeVars, List.mem_singleton] at hτ
          subst hτ
          simpa [Ty.closeOver, h_idx, Ty.freeVars]
      | prim p => simp [Ty.closeOver, Ty.freeVars] at hτ
      | bvar i => simp [Ty.closeOver, Ty.freeVars] at hτ
      | arrow a b iha ihb =>
        simp only [Ty.closeOver, Ty.freeVars, List.mem_dedup, List.mem_append] at hτ ⊢
        rcases hτ with hτ | hτ
        · exact Or.inl (iha hτ)
        · exact Or.inr (ihb hτ)
      | customTy nm tys ih =>
        simp only [Ty.closeOver, Ty.freeVars, TyList.closeOver_eq_map] at hτ ⊢
        rw [mem_TyList_freeVars] at hτ ⊢
        obtain ⟨t, ht, hτt⟩ := hτ
        exact ⟨Ty.closeOver gs t, List.mem_map.mpr ⟨t, ht, rfl⟩, ih t ht hτt⟩
      | bl lo hi e ih =>
        simp only [Ty.closeOver, Ty.freeVars] at hτ ⊢
        exact ih hτ
    have hG_member : ∀ g ∈ G, ∃ j, j < bindings.length ∧ g ∈ (S₁.onTy (.fvar (Φ + j))).freeVars := by
      intro g hg
      have hg' := genGroupVars_spec hg
      obtain ⟨τ, hτin, hgτ⟩ := Ty.mem_freeVarsList_exists hg'.1
      rcases List.mem_filterMap.mp hτin with ⟨s, hs, hmono⟩
      have hsmono : s = RecSpec.mono τ := by
        cases s with
        | mono τ' => simpa [RecSpec.monoTy?] using hmono
        | poly σ => simp [RecSpec.monoTy?] at hmono
      obtain ⟨s₀, hs₀, hsub⟩ := List.mem_map.mp hs
      obtain ⟨j, hlenj, hsj⟩ := hinit_spec s₀ hs₀
      rw [hsj] at hsub
      rw [← hsub] at hsmono
      injection hsmono with hτeq
      exact ⟨j, (by rwa [← hlen] at hlenj), by simpa [hτeq] using hgτ⟩
    have hG_not_domS₁ : ∀ g ∈ G, g ∉ S₁.map Prod.fst := by
      intro g hg hc
      obtain ⟨p, hp, hpeq⟩ := List.mem_map.mp hc
      obtain ⟨j, hlenj, hgτ⟩ := hG_member g hg
      have helim := InferRecGroup.eliminates hgroup hctxGroup hspecs_init htfv_group
        (fun p hp' hc' => hSK p (List.mem_append_left _ hp') (hKe p.1 (.inl (.inr hc'))))
        (fun p hp' σ hσ => by
          rcases hinit_spec (RecSpec.poly σ) hσ with ⟨j', hj', hc'⟩
          cases hc')
      subst hpeq
      exact helim p hp (Ty.fvar (Φ + j)) hgτ
    have hG_below : ∀ g ∈ G, g < Φ₁ := by
      intro g hg
      obtain ⟨j, hlenj, hgτ⟩ := hG_member g hg
      rcases Subst.mem_freeVars_onTy hgτ with h | h
      · simp only [Ty.freeVars, List.mem_singleton] at h
        subst h
        omega
      · obtain ⟨p, hp, hgp⟩ := h
        exact (hS₁ p hp).mem_lt g hgp
    have hG_notK : ∀ g ∈ G, g ∉ K := by
      intro g hg hgK
      have hgΦ : g < Φ := hKΦ g hgK
      obtain ⟨j, hlenj, hgτ⟩ := hG_member g hg
      rcases Subst.mem_freeVars_onTy hgτ with h | h
      · simp only [Ty.freeVars, List.mem_singleton] at h
        subst h
        omega
      · obtain ⟨p, hp, hgp⟩ := h
        have hctxG_avoid : ∀ M ∈ ({ ctx with
              env := (RecSpec.init Φ anns).map (RecSpec.rhsEntry [] []) ++ ctx.env } : Ctx).env,
            g ∉ M.body.freeVars := by
          intro M hM
          rcases List.mem_append.mp hM with hM1 | hM2
          · obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hM1
            rw [RecSpec.rhsEntry_nil_body_freeVars]
            rcases hinit_spec s hs with ⟨j', hlenj', hsj'⟩
            rw [hsj']
            intro hc
            simp only [RecSpec.freeVars, Ty.freeVars, List.mem_singleton] at hc
            omega
          · intro hc
            have hgc : g ∈ (S₁.onCtx ctx).env.freeVars := by
              refine Env.mem_freeVars_iff.mpr ⟨S₁.onPolyTy M, List.mem_map.mpr ⟨M, hM2, rfl⟩, ?_⟩
              exact honTy_preserve S₁ M.body g hc (hG_not_domS₁ g hg)
            exact (genGroupVars_spec hg).2.1 hgc
        have hspecsG_avoid : ∀ s ∈ RecSpec.init Φ anns, g ∉ s.freeVars := by
          intro s hs
          rcases hinit_spec s hs with ⟨j', hlenj', hsj'⟩
          rw [hsj']
          intro hc
          simp only [RecSpec.freeVars, Ty.freeVars, List.mem_singleton] at hc
          omega
        have hRecGroup_sub : ∀ (bs : List Expr) (g : Nat), g ∈ Expr.tyFreeVars.RecGroup.tyFreeVars bs →
            g ∈ bs.flatMap Expr.tyFreeVars := by
          intro bs g
          induction bs with
          | nil => intro hc; simp [Expr.tyFreeVars.RecGroup.tyFreeVars] at hc
          | cons b bs' ih =>
            intro hc
            simp only [Expr.tyFreeVars.RecGroup.tyFreeVars, List.mem_append] at hc
            rcases hc with hc | hc
            · exact List.mem_flatMap.mpr ⟨b, List.mem_cons_self, hc⟩
            · rcases List.mem_flatMap.mp (ih hc) with ⟨a, ha, hga⟩
              exact List.mem_flatMap.mpr ⟨a, List.mem_cons_of_mem _ ha, hga⟩
        have hbindsG_avoid : g ∉ Expr.tyFreeVars.RecGroup.tyFreeVars bindings := by
          intro hc
          exact (genGroupVars_spec hg).2.2 (List.mem_append_right _ (hRecGroup_sub bindings g hc))
        have hgrp_avoid := InferRecGroup.eOut_avoid hgroup (w := g) (by omega)
          hctxG_avoid hspecsG_avoid hbindsG_avoid
        exact hgrp_avoid p hp hgp
    have hG_body : ∀ g ∈ G, g ∉ body.tyFreeVars := fun g hg hc =>
      hG_notK g hg (hKe g (.inr hc))
    have hG_bodyCtx_env : ∀ g ∈ G, ∀ M ∈ ({ (S₁.onCtx ctx) with
        env := RecSpecs.ceilingSchemes G anns specs₁ ++ (S₁.onCtx ctx).env } : Ctx).env,
        g ∉ M.body.freeVars := by
      intro g hg M hM
      rcases List.mem_append.mp hM with hM1 | hM2
      · obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hM1
        have hpa : p.1 ∈ anns := (List.of_mem_zip hp).1
        have hps : p.2 ∈ specs₁ := (List.of_mem_zip hp).2
        cases p with
        | mk a s =>
          cases a with
          | some σ =>
            intro hc
            exact (genGroupVars_spec hg).2.2 (List.mem_append_left _ (Expr.scheme_body_mem_annList_tyFreeVars hpa hc))
          | none =>
            obtain ⟨s₀, hs₀, rfl⟩ := List.mem_map.mp hps
            obtain ⟨j', hlenj', hsj'⟩ := hinit_spec s₀ hs₀
            rw [hsj']
            exact hgenGroup_avoid hg
      · intro hc
        exact (genGroupVars_spec hg).2.1 (Env.mem_freeVars_iff.mpr ⟨M, hM2, hc⟩)
    have hS₂_dom_G : ∀ g ∈ G, g ∉ S₂.map Prod.fst := fun g hg =>
      Infer.dom_avoid hbody (w := g) (hG_below g hg) (hG_bodyCtx_env g hg) (hG_body g hg)
    have hS₂_ran_G : ∀ g ∈ G, ∀ p ∈ S₂, g ∉ p.2.freeVars := fun g hg =>
      (Infer.eOut_avoid hbody (w := g) (hG_below g hg) (hG_bodyCtx_env g hg) (hG_body g hg)).1
    have hS₂_domG : ∀ p ∈ S₂, p.1 ∉ G := fun p hp hc =>
      hS₂_dom_G p.1 hc (List.mem_map.mpr ⟨p, hp, rfl⟩)
    have hS₂_ranG : ∀ p ∈ S₂, ∀ u ∈ p.2.freeVars, u ∉ G := fun p hp u hu hc =>
      hS₂_ran_G u hc p hp hu
    -- hwf for the empty-pool letRec
    have hwf : RecSpecs.WF anns' bs' specsE G := by
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · rw [show anns' = List.replicate bindings.length none from by simp [anns']]
        rw [show specsE.map RecSpec.ann = List.replicate specsE.length none from by
          rw [← List.map_const]
          apply List.map_congr_left
          intro s hs
          obtain ⟨τ, hτ⟩ := hspecsE_mono s hs
          rw [hτ]
          rfl]
        congr 1
        dsimp [specsE, specs₁]
        simp [List.length_map, RecSpec.init_length, hlen]
      · dsimp [bs', specsE, specs₁]
        simp [List.length_map, RecSpec.init_length, hlen]
      · exact genGroupVars_nodup
      · intro τ hτ
        obtain ⟨s₁, hs₁, hsub₁⟩ := List.mem_map.mp hτ
        obtain ⟨s₀, hs₀, hsub₀⟩ := List.mem_map.mp hs₁
        obtain ⟨s₀₀, hs₀₀, hsub₀₀⟩ := List.mem_map.mp hs₀
        obtain ⟨j, hlenj, hsj⟩ := hinit_spec s₀₀ hs₀₀
        rw [hsj] at hsub₀₀
        rw [← hsub₀₀] at hsub₀
        rw [← hsub₀] at hsub₁
        change RecSpec.eraseBounds (RecSpec.mono (S₂.onTy (S₁.onTy (.fvar (Φ + j))))) = RecSpec.mono τ at hsub₁
        injection hsub₁ with hτeq
        rw [← hτeq]
        exact Ty.IsLC.eraseBounds (Subst.onTy_lc hS₂lc (Subst.onTy_lc hS₁lc ContainsBvarsUpTo.fvar))
      · intro σ hσ
        obtain ⟨τ, hτ⟩ := hspecsE_mono (RecSpec.poly σ) hσ
        cases hτ
    -- pool freshness for the final context
    have hG_env : ∀ g ∈ G, g ∉ ctx'.env.freeVars := by
      intro g hg hc
      have hc' : g ∈ ((S₁ ++ S₂).onCtx ctx).env.freeVars :=
        (Env.mem_freeVars_eraseBounds _ g).mp (by simpa [ctx'] using hc)
      rw [Subst.onCtx_append] at hc'
      obtain ⟨M', hM', hgM'⟩ := Env.mem_freeVars_iff.mp hc'
      rcases List.mem_map.mp hM' with ⟨M, hM, rfl⟩
      rcases Subst.mem_freeVars_onTy hgM' with h | h
      · exact (genGroupVars_spec hg).2.1 (Env.mem_freeVars_iff.mpr ⟨M, hM, h⟩)
      · obtain ⟨p, hp, hgp⟩ := h
        exact hS₂_ran_G g hg p hp hgp
    have hG_bs : ∀ g ∈ G, ∀ e ∈ bs', g ∉ e.tyFreeVars := by
      intro g hg e he
      obtain ⟨b, hb, rfl⟩ := List.mem_map.mp he
      rw [herase_tfv b]
      simp
    -- the body lift: from `Infer.sound hbody` to `RecSpecs.bodyCtx ctx' specsE G`
    have hbody_sound := Infer.sound hbody hbodyWF hbodyBelow K
      (fun k hk => by have := hKΦ k hk; have := hgrpLe; omega)
      (fun y hy => hKe y (.inr hy)) (fun p hp => hSK p (List.mem_append_right _ hp))
    have hΦbody : ∀ y ∈ body.tyFreeVars, y < Φ₁ := fun y hy => by
      have := hKΦ y (hKe y (.inr hy))
      have := hgrpLe
      omega
    have hSebody : ∀ p ∈ S₂, p.1 ∉ body.tyFreeVars := fun p hp hc =>
      hSK p (List.mem_append_right _ hp) (hKe p.1 (.inr hc))
    have hS₂τ_body : S₂.onTy τ = τ :=
      Ty.substFvars_eq_self_of_no_key (fun p hp =>
        (Infer.eliminates hbody hbodyBelow hΦbody hSebody).2 p hp)
    have hbody_ctx : (S₂.onCtx { (S₁.onCtx ctx) with
        env := RecSpecs.ceilingSchemes G anns specs₁ ++ (S₁.onCtx ctx).env }).eraseBounds
        = ⟨(S₂.onEnv (RecSpecs.ceilingSchemes G anns specs₁)).eraseBounds
            ++ (((S₁ ++ S₂).onCtx ctx).eraseBounds).env,
            (((S₁ ++ S₂).onCtx ctx).eraseBounds).ctors⟩ := by
      have hS₂onCtx : S₂.onCtx { (S₁.onCtx ctx) with
            env := RecSpecs.ceilingSchemes G anns specs₁ ++ (S₁.onCtx ctx).env }
          = { (S₂.onCtx (S₁.onCtx ctx)) with
            env := S₂.onEnv (RecSpecs.ceilingSchemes G anns specs₁ ++ (S₁.onCtx ctx).env) } := by
        simp only [Subst.onCtx, Subst.onEnv, List.map_append]
      rw [hS₂onCtx]
      rw [← Subst.onCtx_append]
      simp only [Ctx.eraseBounds, Subst.onEnv, List.map_append, Env.eraseBounds, List.map_map]
      congr 1
      congr 1
      all_goals try rfl
      · simp only [Subst.onCtx, Subst.onEnv, Env.eraseBounds, List.map_map]
        apply List.map_congr_left
        intro M hM
        simp [Subst.onPolyTy, Subst.onTy_append, PolyTy.eraseBounds]
    have hbody_pack : TypeOfHM
        ⟨(S₂.onEnv (RecSpecs.ceilingSchemes G anns specs₁)).eraseBounds
          ++ (((S₁ ++ S₂).onCtx ctx).eraseBounds).env, (((S₁ ++ S₂).onCtx ctx).eraseBounds).ctors⟩
        body.erase (Ty.eraseBounds τ) := by
      rwa [hbody_ctx, hS₂τ_body] at hbody_sound
    -- ceiling memberwise: `Generalizes (genGroup G τj) (eraseBounds σ)` for annotated,
    -- equality for unannotated — all via the ceiling + S₂-avoids-G
    have hS₂τ_fix : ∀ {τ₁ : Ty}, (∀ v ∈ (Ty.eraseBounds τ₁).freeVars, v ∈ G ∨ v ∈ K) →
        S₂.onTy τ₁ = τ₁ := by
      intro τ₁ hfv
      exact Ty.substFvars_eq_self_of_no_key (fun p hp hc => by
        rcases hfv p.1 ((Ty.mem_freeVars_eraseBounds τ₁ p.1).mpr hc) with h | h
        · exact hS₂_dom_G p.1 h (List.mem_map.mpr ⟨p, hp, rfl⟩)
        · exact hSK p (List.mem_append_right _ hp) h)
    have hforall₂_mem : ∀ {as : List (Option PolyTy)} {bs : List RecSpec},
        List.Forall₂ (fun a s => match a with
          | some σ' => PolyTy.Generalizes (PolyTy.eraseBounds (RecSpec.bodyScheme G s)) (PolyTy.eraseBounds σ')
          | none => True) as bs →
        ∀ {a b}, (a, b) ∈ as.zip bs →
          match a with
          | some σ' => PolyTy.Generalizes (PolyTy.eraseBounds (RecSpec.bodyScheme G b)) (PolyTy.eraseBounds σ')
          | none => True := by
      intro as bs hf
      induction hf with
      | nil => intro a b hp; simp at hp
      | cons hhd htl ih =>
        intro a b hp
        simp only [List.zip_cons_cons, List.mem_cons] at hp
        rcases hp with hpair | hp
        · injection hpair with ha hb
          subst ha
          subst hb
          exact hhd
        · exact ih hp
    have hper : ∀ p ∈ anns.zip specs₁,
        PolyTy.Generalizes
          (RecSpec.bodyScheme G (RecSpec.eraseBounds (RecSpec.onSubst S₂ p.2)))
          (PolyTy.eraseBounds (S₂.onPolyTy (match p.1 with
            | some σ => σ
            | none => RecSpec.bodyScheme G p.2))) := by
      intro p hp
      cases p with
      | mk a s =>
        cases a with
        | some σ =>
          have hps : s ∈ specs₁ := (List.of_mem_zip hp).2
          obtain ⟨s₀, hs₀, hsub₀⟩ := List.mem_map.mp hps
          obtain ⟨j, hlenj, hsj⟩ := hinit_spec s₀ hs₀
          rw [hsj] at hsub₀
          rw [← hsub₀] at hp ⊢
          have hce : PolyTy.Generalizes
              (PolyTy.genGroup G (Ty.eraseBounds (S₁.onTy (.fvar (Φ + j)))))
              (PolyTy.eraseBounds σ) := by
            simpa [RecSpec.bodyScheme, RecSpec.onSubst, PolyTy.eraseBounds_genGroup] using (hforall₂_mem hceiling hp)
          -- hce : Generalizes (genGroup G (eraseBounds (S₁.onTy (fvar (Φ+j))))) (eraseBounds σ)
          have hfix : S₂.onTy σ.body = σ.body := by
            exact Ty.substFvars_eq_self_of_no_key (fun p hp' hc =>
              hSK p (List.mem_append_right _ hp')
                (hKe p.1 (.inl (.inl (Expr.scheme_body_mem_annList_tyFreeVars (List.of_mem_zip hp).1 hc)))))
          have hS₂σ : S₂.onPolyTy σ = σ := by
            cases σ
            simp [Subst.onPolyTy, hfix]
          have hτ₁_fix : S₂.onTy (S₁.onTy (.fvar (Φ + j))) = S₁.onTy (.fvar (Φ + j)) := by
            apply hS₂τ_fix
            intro v hv
            by_cases hvG : v ∈ G
            · exact Or.inl hvG
            · right
              have hsubset := PolyTy.Generalizes.freeVars_subset hce
              have hvbody : v ∈ (PolyTy.genGroup G (Ty.eraseBounds (S₁.onTy (.fvar (Φ + j))))).body.freeVars := by
                exact hcloseOver_preserve (by simpa using hv) (by simp [Ty.genFilter, hvG])
              have hvσ : v ∈ σ.body.freeVars := by
                have hv1 : v ∈ (Ty.eraseBounds σ.body).freeVars := hsubset (by simpa using hvbody)
                exact (Ty.mem_freeVars_eraseBounds σ.body v).mp hv1
              exact hKe v (.inl (.inl (Expr.scheme_body_mem_annList_tyFreeVars (List.of_mem_zip hp).1 hvσ)))
          change PolyTy.Generalizes
            (PolyTy.genGroup G (Ty.eraseBounds (S₂.onTy (S₁.onTy (.fvar (Φ + j))))))
            (PolyTy.eraseBounds (S₂.onPolyTy σ))
          rw [hτ₁_fix, hS₂σ]
          exact hce
        | none =>
          obtain ⟨s₀, hs₀, hsub₀⟩ := List.mem_map.mp (List.of_mem_zip hp).2
          obtain ⟨j, hlenj, hsj⟩ := hinit_spec s₀ hs₀
          rw [hsj] at hsub₀
          rw [← hsub₀]
          have heq : PolyTy.eraseBounds (S₂.onPolyTy (RecSpec.bodyScheme G (RecSpec.mono (S₁.onTy (.fvar (Φ + j))))))
              = RecSpec.bodyScheme G (RecSpec.eraseBounds (RecSpec.onSubst S₂ (RecSpec.mono (S₁.onTy (.fvar (Φ + j)))))) := by
            simp [RecSpec.bodyScheme, RecSpec.eraseBounds, RecSpec.onSubst,
              Subst.onPolyTy_genGroup (G := G) (S := S₂) hS₂_domG hS₂_ranG, PolyTy.eraseBounds_genGroup]
          simp only [Prod.fst, Prod.snd]
          simp only [RecSpec.onSubst]
          rw [heq]
          intro tyArgs ty hlc hinst
          exact ⟨tyArgs, hlc, hinst⟩
    have hzip_snd : ∀ {α : Type} {β : Type} {γ : Type} (as : List α) (bs : List β)
        (f : β → γ), as.length = bs.length → (as.zip bs).map (fun p => f p.2) = bs.map f := by
      intro α β γ as bs f
      induction as generalizing bs with
      | nil => intro h; cases bs with | nil => rfl | cons b bs' => simp at h
      | cons a as' ih =>
        intro h
        cases bs with
        | nil => simp at h
        | cons b bs' =>
          have ih' := ih bs' (by simpa using h)
          simpa [List.zip_cons_cons, List.map_cons] using (congrArg (fun l => f b :: l) ih')
    have hlen_zip : (anns.zip specs₁).length = specs₁.length := by
      rw [List.length_zip]
      all_goals dsimp [specs₁]
      all_goals simp [List.length_map, RecSpec.init_length, hlen]
    have hlen₁ : anns.length = specs₁.length := by
      dsimp [specs₁]
      simp [List.length_map, RecSpec.init_length]
    have hgen_tgt : specsE.map (RecSpec.bodyScheme G)
        = (anns.zip specs₁).map (fun p => RecSpec.bodyScheme G (RecSpec.eraseBounds (RecSpec.onSubst S₂ p.2))) := by
      rw [show specsE = (specs₁.map (RecSpec.onSubst S₂)).map RecSpec.eraseBounds from rfl]
      rw [List.map_map, List.map_map]
      rw [hzip_snd anns specs₁ (fun s => RecSpec.bodyScheme G (RecSpec.eraseBounds (RecSpec.onSubst S₂ s))) hlen₁]
      rfl
    have hgen_src : (S₂.onEnv (RecSpecs.ceilingSchemes G anns specs₁)).eraseBounds
        = (anns.zip specs₁).map (fun p => PolyTy.eraseBounds (S₂.onPolyTy (match p.1 with
            | some σ => σ
            | none => RecSpec.bodyScheme G p.2))) := by
      rw [show RecSpecs.ceilingSchemes G anns specs₁
          = (anns.zip specs₁).map (fun p => match p.1 with | some σ => σ | none => RecSpec.bodyScheme G p.2) from rfl]
      simp only [Subst.onEnv, Env.eraseBounds, List.map_map]
      rfl
    have hgen : List.Forall₂ PolyTy.Generalizes
        (specsE.map (RecSpec.bodyScheme G))
        ((S₂.onEnv (RecSpecs.ceilingSchemes G anns specs₁)).eraseBounds) := by
      rw [hgen_tgt, hgen_src]
      have haux : ∀ (l : List (Option PolyTy × RecSpec)),
          (∀ x ∈ l, PolyTy.Generalizes
            (RecSpec.bodyScheme G (RecSpec.eraseBounds (RecSpec.onSubst S₂ x.2)))
            (PolyTy.eraseBounds (S₂.onPolyTy (match x.1 with | some σ => σ | none => RecSpec.bodyScheme G x.2)))) →
          List.Forall₂ PolyTy.Generalizes
            (l.map (fun x => RecSpec.bodyScheme G (RecSpec.eraseBounds (RecSpec.onSubst S₂ x.2))))
            (l.map (fun x => PolyTy.eraseBounds (S₂.onPolyTy (match x.1 with | some σ => σ | none => RecSpec.bodyScheme G x.2)))) := by
        intro l h
        induction l with
        | nil => exact .nil
        | cons x xs ih =>
          exact .cons (h x (List.mem_cons_self)) (ih (fun y hy => h y (List.mem_cons_of_mem _ hy)))
      exact haux (anns.zip specs₁) hper
    have hbody_final := TypeOfHM.weaken_schemes hgen hbody_pack
    have hbody_lift : TypeOfHM (RecSpecs.bodyCtx ctx' specsE G) body.erase (Ty.eraseBounds τ) := by
      simpa [RecSpecs.bodyCtx, ctx'] using hbody_final
    -- assemble the empty-pool letRec
    have hτsE_len : bs'.length = τsE.length := by
      simpa [bs', τsE, List.length_map] using hwf.length
    have hτsE_link : ∀ p ∈ specsE.zip τsE, ∀ τ, p.1 = RecSpec.mono τ → p.2 = τ := by
      intro p hp τ hτ
      rcases List.mem_iff_getElem.mp hp with ⟨j, hjp, hpeq⟩
      have hjl_e : j < specsE.length :=
        lt_of_lt_of_le hjp (by rw [List.length_zip]; exact min_le_left _ _)
      have hjl_t : j < τsE.length :=
        lt_of_lt_of_le hjp (by rw [List.length_zip]; exact min_le_right _ _)
      have hpeq' : (specsE[j]'(hjl_e), τsE[j]'(hjl_t)) = p := by
        rw [List.getElem_zip] at hpeq
        exact hpeq
      have hfst : specsE[j]'(hjl_e) = RecSpec.mono τ := by
        have h := congrArg Prod.fst hpeq'
        simpa [hτ] using h
      have hsnd : p.2 = τ := by
        rw [← hpeq']
        dsimp [τsE]
        rw [List.getElem_map, hfst]
      exact hsnd
    have hτsE_lc : ∀ t ∈ τsE, t.IsLC := by
      intro t ht
      obtain ⟨s, hs, rfl⟩ := List.mem_map.mp ht
      obtain ⟨τ, hτ⟩ := hspecsE_mono s hs
      rw [hτ]
      exact hwf.mono_lc τ (by simpa [hτ] using hs)
    have hletrec := TypeOfHM.letRec_of_emptyPool (ctx := ctx') (Lp := []) (G := G)
      (anns := anns') (bs := bs') (specs := specsE) (τs := τsE)
      (body := body.erase) (ρ := Ty.eraseBounds τ)
      hwf hτsE_len hτsE_link hτsE_lc hG_env hG_bs hmono hbody_lift
    simpa [Expr.erase_letRec, anns', bs', ctx', List.map_const] using hletrec
  termination_by e.size
  decreasing_by
    all_goals (try subst_vars; try simp only [Expr.size, Expr.size_openTyVars]; omega)

theorem InferBranches.sound {Φ ctx scrutTy ρ brs Φ' S}
    (h : InferBranches Φ ctx scrutTy ρ brs Φ' S)
    (hctx : CtxWF ctx) (hbelow : CtxBelow Φ ctx)
    (hscrutTy : scrutTy.IsLC) (hρ : ρ.IsLC)
    (hscrutB : Ty.BelowFvars Φ scrutTy) (hρB : Ty.BelowFvars Φ ρ) (K : List Nat)
    (hKΦ : ∀ k ∈ K, k < Φ)
    (hKbr : ∀ y ∈ Expr.tyFreeVars.BranchList.tyFreeVars brs, y ∈ K)
    (hSK : ∀ p ∈ S, p.1 ∉ K) :
    ∀ p ∈ brs,
      TypeOfMatchBranch (S.onCtx ctx).eraseBounds
        (p.1, p.2.erase)
        (Ty.eraseBounds (S.onTy scrutTy)) (Ty.eraseBounds (S.onTy ρ)) := by
  have herase_tfv : ∀ e : Expr, (e.erase).tyFreeVars = [] := by
    intro e
    induction e using Expr.rec_strong with
    | primLit p => simp [Expr.erase, Expr.tyFreeVars]
    | primBinOp op => simp [Expr.erase, Expr.tyFreeVars]
    | ctor c => simp [Expr.erase, Expr.tyFreeVars]
    | var i  => simp [Expr.erase, Expr.tyFreeVars]
    | app f arg ihf iha => simp [Expr.erase_app, Expr.tyFreeVars, ihf, iha]
    | lambda ann body ih => simp [Expr.erase_lambda, Expr.tyFreeVars, ih, Option.elim_none]
    | letIn ann rhs body ihr ihb =>
      simp [Expr.erase_letIn, Expr.tyFreeVars, ihr, ihb, Option.elim_none]
    | match_ scrut branches ihs ihbs =>
      simp only [Expr.erase_match, Expr.tyFreeVars, ihs]
      induction branches with
      | nil => rfl
      | cons pe rest ih =>
        cases pe with
        | mk pat body =>
          simp only [Expr.tyFreeVars.BranchList.tyFreeVars, List.map_cons]
          rw [ihbs pat body (List.mem_cons_self ..)]
          rw [ih (fun pat₁ e mem => ihbs pat₁ e (List.mem_cons_of_mem _ mem))]
          simp
    | letRec anns bindings body ihbs ihb =>
      have hpair : Expr.tyFreeVars.AnnList.tyFreeVars
          (bindings.map (fun _ => none)) = [] ∧
          Expr.tyFreeVars.RecGroup.tyFreeVars (bindings.map Expr.erase) = [] := by
        induction bindings with
        | nil =>
          simp [Expr.tyFreeVars.AnnList.tyFreeVars, Expr.tyFreeVars.RecGroup.tyFreeVars]
        | cons b rest ih =>
          rcases ih (fun e mem => ihbs e (List.mem_cons_of_mem b mem)) with ⟨hA, hR⟩
          constructor
          · simp only [Expr.tyFreeVars.AnnList.tyFreeVars, List.map_cons, Option.elim_none]
            rw [hA]
            simp
          · simp only [Expr.tyFreeVars.RecGroup.tyFreeVars, List.map_cons]
            rw [ihbs b (List.mem_cons_self ..), hR]
            simp
      simp only [Expr.erase_letRec, Expr.tyFreeVars, ihb]
      rw [hpair.1, hpair.2]
      simp
  have herase_eraseBounds : ∀ e : Expr, (e.erase).eraseBounds = e.erase := by
    intro e
    induction e using Expr.rec_strong with
    | primLit p => simp [Expr.erase, Expr.eraseBounds]
    | primBinOp op => simp [Expr.erase, Expr.eraseBounds]
    | ctor c => simp [Expr.erase, Expr.eraseBounds]
    | var i  => simp [Expr.erase, Expr.eraseBounds]
    | app f arg ihf iha => simp only [Expr.erase_app, Expr.eraseBounds_app, ihf, iha]
    | lambda ann body ih =>
      simp only [Expr.erase_lambda, Expr.eraseBounds_lambda, Option.map_none, ih]
    | letIn ann rhs body ihr ihb =>
      simp only [Expr.erase_letIn, Expr.eraseBounds_letIn, Option.map_none, ihr, ihb]
    | match_ scrut branches ihs ihbs =>
      have hb : (branches.map (fun pe => (pe.1, pe.2.erase))).map
          (fun pe => (pe.1, pe.2.eraseBounds)) = branches.map (fun pe => (pe.1, pe.2.erase)) := by
        rw [List.map_map]
        apply List.map_congr_left
        intro pe hpe
        cases pe with
        | mk pat body => simp [ihbs pat body hpe]
      simp only [Expr.erase_match, Expr.eraseBounds]
      rw [ihs, hb]
    | letRec anns bindings body ihbs ihb =>
      have hanns : (bindings.map (fun _ => none)).map (Option.map PolyTy.eraseBounds) =
          bindings.map (fun _ => none) := by
        rw [List.map_map]
        apply List.map_congr_left
        intro b _
        rfl
      have hbs : (bindings.map Expr.erase).map Expr.eraseBounds = bindings.map Expr.erase := by
        rw [List.map_map]
        apply List.map_congr_left
        intro b hb
        exact ihbs b hb
      simp only [Expr.erase_letRec, Expr.eraseBounds]
      rw [hanns, hbs, ihb]
  have herase_subst : ∀ (e : Expr) (S : Subst), (e.erase).substTyFvars S = e.erase := by
    intro e S
    exact Expr.substTyFvars_eq_self_of_not_mem_tyFreeVars (fun p hp hc => by
      rw [herase_tfv e] at hc
      simp at hc)
  cases h with
  | nil => intro p hp; simp at hp
  | cons hlook hn huni0 hbody huni hrest =>
    expose_names
    have hΦ : ∀ y ∈ Expr.tyFreeVars.BranchList.tyFreeVars
        ((MatchPattern.named c n, body) :: rest), y < Φ :=
      fun y hy => hKΦ y (hKbr y hy)
    have hSe : ∀ p ∈ S₀ ++ S₁ ++ S₂ ++ S₃,
        p.1 ∉ Expr.tyFreeVars.BranchList.tyFreeVars
          ((MatchPattern.named c n, body) :: rest) :=
      fun p hp hc => hSK p hp (hKbr p.1 hc)
    have hle0 : Φ + ctor.paramCount ≤ Φ₁ := Infer.frontier_le hbody
    have hΦhead : ∀ y ∈ body.tyFreeVars, y < Φ := fun y hy => hΦ y (by
      simp only [Expr.tyFreeVars.BranchList.tyFreeVars, List.mem_append]; exact Or.inl hy)
    have hS₀lc := huni0.lc hscrutTy
      (.customTy (fun t ht => by
        obtain ⟨x, _, rfl⟩ := List.mem_map.mp ht; exact ContainsBvarsUpTo.fvar))
    have hbodyWF := branchBindings_wf (ctorr := ctor)
      (ta := ((freshVars Φ ctor.paramCount).map (Ty.fvar ·)).map S₀.onTy)
      (Subst.onCtx_wf hS₀lc hctx)
      (fun t ht => by
        obtain ⟨v, hv, rfl⟩ := List.mem_map.mp ht
        obtain ⟨x, _, rfl⟩ := List.mem_map.mp hv
        exact Subst.onTy_lc hS₀lc ContainsBvarsUpTo.fvar)
      (by simp)
    obtain ⟨hτb_lc, hS₁lc⟩ := Infer.lc hbody hbodyWF
    have hS₂lc := huni.lc hτb_lc (Subst.onTy_lc hS₁lc (Subst.onTy_lc hS₀lc hρ))
    have hctx1WF := Subst.onCtx_wf hS₂lc (Subst.onCtx_wf hS₁lc (Subst.onCtx_wf hS₀lc hctx))
    have hS₃lc := (InferBranches.lc hrest hctx1WF
      (Subst.onTy_lc hS₂lc (Subst.onTy_lc hS₁lc (Subst.onTy_lc hS₀lc hscrutTy)))
      (Subst.onTy_lc hS₂lc (Subst.onTy_lc hS₁lc (Subst.onTy_lc hS₀lc hρ)))).2
    have hS₀bel : ∀ p ∈ S₀, Ty.BelowFvars (Φ + ctor.paramCount) p.2 :=
      UnifyRel.belowFvars huni0 (hscrutB.mono (by omega))
        (.customTy (fun t ht => by
          obtain ⟨x, hx, rfl⟩ := List.mem_map.mp ht
          exact .fvar (by have := freshVars_lt x hx; omega)))
    have hbodyBelow := branchBindings_below (ctorr := ctor)
      (ta := ((freshVars Φ ctor.paramCount).map (Ty.fvar ·)).map S₀.onTy)
      (Subst.onCtx_below hS₀bel (by omega) hbelow)
      (fun t ht => by
        obtain ⟨v, hv, rfl⟩ := List.mem_map.mp ht
        obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hv
        exact Subst.onTy_belowFvars hS₀bel
          (.fvar (by have := freshVars_lt x hx; omega)))
    obtain ⟨hb_τbel, hb_sbel⟩ := Infer.belowFvars hbody hbodyBelow
      (fun y hy => by have := hΦhead y hy; omega)
    have hS₀ρbel : Ty.BelowFvars Φ₁ (S₀.onTy ρ) :=
      (Subst.onTy_belowFvars hS₀bel (hρB.mono (by omega))).mono hle0
    have hS₀scrutbel : Ty.BelowFvars Φ₁ (S₀.onTy scrutTy) :=
      (Subst.onTy_belowFvars hS₀bel (hscrutB.mono (by omega))).mono hle0
    have hS₁S₀ρbel : Ty.BelowFvars Φ₁ (S₁.onTy (S₀.onTy ρ)) :=
      Subst.onTy_belowFvars hb_sbel hS₀ρbel
    have hS₂bel : ∀ p ∈ S₂, Ty.BelowFvars Φ₁ p.2 :=
      UnifyRel.belowFvars huni hb_τbel hS₁S₀ρbel
    have hctx1bel : CtxBelow Φ₁ (S₂.onCtx (S₁.onCtx (S₀.onCtx ctx))) :=
      Subst.onCtx_below hS₂bel (le_refl _) (Subst.onCtx_below hb_sbel (le_refl _)
        (Subst.onCtx_below (fun p hp => (hS₀bel p hp).mono hle0) (by omega) hbelow))
    have hscrut'bel : Ty.BelowFvars Φ₁ (S₂.onTy (S₁.onTy (S₀.onTy scrutTy))) :=
      Subst.onTy_belowFvars hS₂bel (Subst.onTy_belowFvars hb_sbel hS₀scrutbel)
    have hρ'bel : Ty.BelowFvars Φ₁ (S₂.onTy (S₁.onTy (S₀.onTy ρ))) :=
      Subst.onTy_belowFvars hS₂bel hS₁S₀ρbel
    have hrest_sound := InferBranches.sound hrest hctx1WF hctx1bel
      (Subst.onTy_lc hS₂lc (Subst.onTy_lc hS₁lc (Subst.onTy_lc hS₀lc hscrutTy)))
      (Subst.onTy_lc hS₂lc (Subst.onTy_lc hS₁lc (Subst.onTy_lc hS₀lc hρ)))
      hscrut'bel hρ'bel K (fun k hk => by have := hKΦ k hk; omega)
      (fun y hy => hKbr y (by
        simp only [Expr.tyFreeVars.BranchList.tyFreeVars, List.mem_append]; exact Or.inr hy))
      (fun p hp => hSK p (List.mem_append_right _ hp))
    intro p hp
    rcases List.mem_cons.mp hp with rfl | hp_rest
    · -- head named source branch
      set ta0 : List Ty := (freshVars Φ ctor.paramCount).map (Ty.fvar ·) with hta0
      set taS₀ : List Ty := ta0.map S₀.onTy with htaS₀
      set bodyCtx : Ctx :=
        { (S₀.onCtx ctx) with
          env := (ctor.contents.map (Ty.openWith taS₀)).map PolyTy.mkTrivial
            ++ (S₀.onCtx ctx).env }
      have h0 : TypeOfHM (S₁.onCtx bodyCtx).eraseBounds body.erase
          (Ty.eraseBounds (S₁.onTy τb)) :=
        Infer.sound hbody hbodyWF hbodyBelow K
          (fun k hk => by have := hKΦ k hk; have := hle0; omega)
          (fun y hy => hKbr y (by
            simp only [Expr.tyFreeVars.BranchList.tyFreeVars, List.mem_append]; exact Or.inl hy))
          (fun p hp => hSK p (List.mem_append_left _ (List.mem_append_left _
              (List.mem_append_right _ hp))))
      have hS₁τb : S₁.onTy τb = τb := Ty.substFvars_eq_self_of_no_key (fun p hp =>
        (Infer.eliminates hbody hbodyBelow (fun y hy => by
            have := hKΦ y (hKbr y (by
              simp only [Expr.tyFreeVars.BranchList.tyFreeVars, List.mem_append]; exact Or.inl hy))
            have := hle0
            omega)
          (fun p hp hc => hSe p (List.mem_append_left _ (List.mem_append_left _
              (List.mem_append_right _ hp)))
            (by simp only [Expr.tyFreeVars.BranchList.tyFreeVars, List.mem_append]; exact Or.inl hc))).2 p hp)
      have h0' : TypeOfHM (S₁.onCtx bodyCtx).eraseBounds body.erase
          (Ty.eraseBounds τb) := by
        rwa [hS₁τb] at h0
      have h1 := TypeOfHM.onSubst_eraseBounds_fixed (ctx := S₁.onCtx bodyCtx)
        (e := body.erase) (τ := τb) S₂ hS₂lc (herase_subst body S₂)
        (by simpa only [herase_eraseBounds body] using h0')
      have huni_eq := huni.unifies
      have h1s : TypeOfHM (S₂.onCtx (S₁.onCtx bodyCtx)).eraseBounds body.erase
          (Ty.eraseBounds (S₂.onTy τb)) := by
        simpa only [herase_eraseBounds body] using h1
      have h1ρ : TypeOfHM (S₂.onCtx (S₁.onCtx bodyCtx)).eraseBounds body.erase
          (Ty.eraseBounds (S₂.onTy (S₁.onTy (S₀.onTy ρ)))) := by
        rwa [huni_eq] at h1s
      have h2 := TypeOfHM.onSubst_eraseBounds_fixed
        (ctx := S₂.onCtx (S₁.onCtx bodyCtx)) (e := body.erase)
        (τ := S₂.onTy (S₁.onTy (S₀.onTy ρ))) S₃ hS₃lc (herase_subst body S₃)
        (by simpa only [herase_eraseBounds body] using h1ρ)
      set taFull : List Ty :=
        ((((ta0.map S₀.onTy).map S₁.onTy).map S₂.onTy).map S₃.onTy) with htaFull
      set instContents : List Ty := ctor.contents.map (Ty.openWith taFull) with hinst
      have hbb123 :
          S₃.onCtx (S₂.onCtx (S₁.onCtx bodyCtx)) =
            { (S₃.onCtx (S₂.onCtx (S₁.onCtx (S₀.onCtx ctx)))) with
              env := instContents.map PolyTy.mkTrivial
                ++ (S₃.onCtx (S₂.onCtx (S₁.onCtx (S₀.onCtx ctx)))).env } := by
        have hb1 := Subst.onCtx_branchBindings (ctorr := ctor) (ta := taS₀)
          (ctx := S₀.onCtx ctx) hS₁lc
        have hb2 := Subst.onCtx_branchBindings (ctorr := ctor)
          (ta := taS₀.map S₁.onTy) (ctx := S₁.onCtx (S₀.onCtx ctx)) hS₂lc
        have hb3 := Subst.onCtx_branchBindings (ctorr := ctor)
          (ta := (taS₀.map S₁.onTy).map S₂.onTy)
          (ctx := S₂.onCtx (S₁.onCtx (S₀.onCtx ctx))) hS₃lc
        simp only at hb1
        have step1 : S₁.onCtx bodyCtx =
            { (S₁.onCtx (S₀.onCtx ctx)) with
              env := (ctor.contents.map (Ty.openWith (taS₀.map S₁.onTy))).map
                  PolyTy.mkTrivial
                ++ (S₁.onCtx (S₀.onCtx ctx)).env } := by
          simp only [bodyCtx]; exact hb1
        rw [step1, hb2, hb3]
      have hctx_pack :
          (S₃.onCtx (S₂.onCtx (S₁.onCtx (S₀.onCtx ctx)))).eraseBounds =
            ((S₀ ++ S₁ ++ S₂ ++ S₃).onCtx ctx).eraseBounds := by
        simp only [← Subst.onCtx_append, List.append_assoc]
      have hτ_pack : Ty.eraseBounds (S₃.onTy (S₂.onTy (S₁.onTy (S₀.onTy ρ)))) =
          Ty.eraseBounds ((S₀ ++ S₁ ++ S₂ ++ S₃).onTy ρ) := by
        simp only [Subst.onTy_append, List.append_assoc]
      have hbody_final : TypeOfHM
          { ((S₀ ++ S₁ ++ S₂ ++ S₃).onCtx ctx).eraseBounds with
            env := (instContents.map Ty.eraseBounds).map PolyTy.mkTrivial
              ++ ((S₀ ++ S₁ ++ S₂ ++ S₃).onCtx ctx).env.eraseBounds }
          body.erase
          (Ty.eraseBounds ((S₀ ++ S₁ ++ S₂ ++ S₃).onTy ρ)) := by
        have key := h2
        rw [hbb123] at key
        simp only [Ctx.eraseBounds, Env.eraseBounds_append, Env.eraseBounds_map_mkTrivial]
          at key
        have henv := congrArg Ctx.env hctx_pack
        have hctors := congrArg Ctx.ctors hctx_pack
        simp only [Ctx.eraseBounds] at henv hctors
        rw [henv, hctors, hτ_pack] at key
        simpa only [herase_eraseBounds body] using key
      have hlook' :
          LookupList.get? ((S₀ ++ S₁ ++ S₂ ++ S₃).onCtx ctx).eraseBounds.ctors c =
            some (Ctor.eraseBounds ctor) := by
        have := congrArg (Option.map Ctor.eraseBounds) hlook
        have hctors : ((S₀ ++ S₁ ++ S₂ ++ S₃).onCtx ctx).ctors = ctx.ctors := by
          simp only [Subst.onCtx]
        simpa [Ctx.eraseBounds, hctors, CtorEnv.eraseBounds_get?, Option.map_some] using this
      have hscrut' :
          Ty.eraseBounds ((S₀ ++ S₁ ++ S₂ ++ S₃).onTy scrutTy) =
            .customTy (Ctor.eraseBounds ctor).tyName (taFull.map Ty.eraseBounds) := by
        have hu := huni0.unifies
        simp only [Unifies, AgreesHM, Subst.onTy_customTy] at hu
        have hu' := Ty.eraseBounds_onTy_congr (S₁ ++ S₂ ++ S₃) hu
        have hl : Ty.eraseBounds ((S₁ ++ S₂ ++ S₃).onTy (S₀.onTy scrutTy)) =
            Ty.eraseBounds ((S₀ ++ S₁ ++ S₂ ++ S₃).onTy scrutTy) := by
          have : (S₀ ++ S₁ ++ S₂ ++ S₃).onTy scrutTy =
              (S₁ ++ S₂ ++ S₃).onTy (S₀.onTy scrutTy) := by
            rw [show S₀ ++ S₁ ++ S₂ ++ S₃ = S₀ ++ (S₁ ++ S₂ ++ S₃) from by
                  simp only [List.append_assoc], Subst.onTy_append]
          rw [this]
        have hr : Ty.eraseBounds ((S₁ ++ S₂ ++ S₃).onTy
            (.customTy ctor.tyName (ta0.map S₀.onTy))) =
            .customTy (Ctor.eraseBounds ctor).tyName (taFull.map Ty.eraseBounds) := by
          simp only [Subst.onTy_customTy, Ty.eraseBounds_customTy, TyList.eraseBounds_eq_map,
            Ctor.eraseBounds_tyName, List.map_map, taFull, ta0]
          congr 1
          refine List.map_congr_left fun x _hx => ?_
          change Ty.eraseBounds ((S₁ ++ S₂ ++ S₃).onTy (S₀.onTy (.fvar x))) =
            Ty.eraseBounds (S₃.onTy (S₂.onTy (S₁.onTy (S₀.onTy (.fvar x)))))
          simp only [Subst.onTy_append, List.append_assoc]
        calc Ty.eraseBounds ((S₀ ++ S₁ ++ S₂ ++ S₃).onTy scrutTy)
            = Ty.eraseBounds ((S₁ ++ S₂ ++ S₃).onTy (S₀.onTy scrutTy)) := hl.symm
          _ = Ty.eraseBounds ((S₁ ++ S₂ ++ S₃).onTy
                (.customTy ctor.tyName (ta0.map S₀.onTy))) := hu'
          _ = .customTy (Ctor.eraseBounds ctor).tyName (taFull.map Ty.eraseBounds) := hr
      have hfields' :
          List.Forall₂ (InstantiatesBy (taFull.map Ty.eraseBounds))
            (Ctor.eraseBounds ctor).contents (instContents.map Ty.eraseBounds) := by
        have hstruct : List.Forall₂ (InstantiatesBy taFull) ctor.contents instContents := by
          simp only [instContents]
          exact List.forall₂_self_map (fun c0 hc0 =>
            InstantiatesBy.openWith (ctor.bound c0 hc0) (by
              simp only [taFull, ta0, List.length_map, freshVars_length]; exact Nat.le_refl _))
        simpa [Ctor.eraseBounds_contents] using InstantiatesBy.forall2_eraseBounds hstruct
      refine TypeOfMatchBranch.mk
        (ctor := Ctor.eraseBounds ctor)
        (tyArgs := taFull.map Ty.eraseBounds)
        (instContents := instContents.map Ty.eraseBounds)
        ⟨hlook', hscrut',
          by simp [Ctor.eraseBounds_paramCount, taFull, ta0, List.length_map, freshVars_length],
          by simp [Ctor.eraseBounds_contents, List.length_map, hn],
          hfields'⟩
        rfl hbody_final
    · -- rest source branches
      have hctx_eq : (S₃.onCtx (S₂.onCtx (S₁.onCtx (S₀.onCtx ctx)))).eraseBounds =
          ((S₀ ++ S₁ ++ S₂ ++ S₃).onCtx ctx).eraseBounds := by
        simp only [← Subst.onCtx_append, List.append_assoc]
      have hscrut_eq : Ty.eraseBounds (S₃.onTy (S₂.onTy (S₁.onTy (S₀.onTy scrutTy)))) =
          Ty.eraseBounds ((S₀ ++ S₁ ++ S₂ ++ S₃).onTy scrutTy) := by
        simp only [Subst.onTy_append, List.append_assoc]
      have hρ_eq : Ty.eraseBounds (S₃.onTy (S₂.onTy (S₁.onTy (S₀.onTy ρ)))) =
          Ty.eraseBounds ((S₀ ++ S₁ ++ S₂ ++ S₃).onTy ρ) := by
        simp only [Subst.onTy_append, List.append_assoc]
      have key := hrest_sound p hp_rest
      rwa [hctx_eq, hscrut_eq, hρ_eq] at key
  | consWild hbody huni hrest =>
    expose_names
    have hSe : ∀ p ∈ S₁ ++ S₂ ++ S₃,
        p.1 ∉ Expr.tyFreeVars.BranchList.tyFreeVars ((MatchPattern.wildcard, body) :: rest) :=
      fun p hp hc => hSK p hp (hKbr p.1 hc)
    have hle1 := Infer.frontier_le hbody
    obtain ⟨hτb_lc, hS₁lc⟩ := Infer.lc hbody hctx
    have hS₂lc := huni.lc hτb_lc (Subst.onTy_lc hS₁lc hρ)
    have hctx1WF := Subst.onCtx_wf hS₂lc (Subst.onCtx_wf hS₁lc hctx)
    have hS₃lc := (InferBranches.lc hrest hctx1WF
      (Subst.onTy_lc hS₂lc (Subst.onTy_lc hS₁lc hscrutTy))
      (Subst.onTy_lc hS₂lc (Subst.onTy_lc hS₁lc hρ))).2
    obtain ⟨hb_τbel, hb_sbel⟩ := Infer.belowFvars hbody hbelow
      (fun y hy => hKΦ y (hKbr y (by
        simp only [Expr.tyFreeVars.BranchList.tyFreeVars, List.mem_append]; exact Or.inl hy)))
    have hS₁ρbel : Ty.BelowFvars Φ₁ (S₁.onTy ρ) := Subst.onTy_belowFvars hb_sbel (hρB.mono hle1)
    have hS₂bel : ∀ p ∈ S₂, Ty.BelowFvars Φ₁ p.2 := UnifyRel.belowFvars huni hb_τbel hS₁ρbel
    have hctx1bel : CtxBelow Φ₁ (S₂.onCtx (S₁.onCtx ctx)) :=
      Subst.onCtx_below hS₂bel (le_refl _) (Subst.onCtx_below hb_sbel hle1 hbelow)
    have hscrut'bel : Ty.BelowFvars Φ₁ (S₂.onTy (S₁.onTy scrutTy)) :=
      Subst.onTy_belowFvars hS₂bel (Subst.onTy_belowFvars hb_sbel (hscrutB.mono hle1))
    have hρ'bel : Ty.BelowFvars Φ₁ (S₂.onTy (S₁.onTy ρ)) :=
      Subst.onTy_belowFvars hS₂bel hS₁ρbel
    have hrest_sound := InferBranches.sound hrest hctx1WF hctx1bel
      (Subst.onTy_lc hS₂lc (Subst.onTy_lc hS₁lc hscrutTy))
      (Subst.onTy_lc hS₂lc (Subst.onTy_lc hS₁lc hρ))
      hscrut'bel hρ'bel K (fun k hk => by have := hKΦ k hk; omega)
      (fun y hy => hKbr y (by
        simp only [Expr.tyFreeVars.BranchList.tyFreeVars, List.mem_append]; exact Or.inr hy))
      (fun p hp => hSK p (List.mem_append_right _ hp))
    intro p hp
    rcases List.mem_cons.mp hp with rfl | hp_rest
    · have h0 : TypeOfHM (S₁.onCtx ctx).eraseBounds body.erase
          (Ty.eraseBounds (S₁.onTy τb)) :=
        Infer.sound hbody hctx hbelow K hKΦ
          (fun y hy => hKbr y (by
            simp only [Expr.tyFreeVars.BranchList.tyFreeVars, List.mem_append]; exact Or.inl hy))
          (fun p hp => hSK p (List.mem_append_left _ (List.mem_append_left _ hp)))
      have hS₁τb : S₁.onTy τb = τb := Ty.substFvars_eq_self_of_no_key (fun p hp =>
        (Infer.eliminates hbody hbelow (fun y hy => hKΦ y (hKbr y (by
            simp only [Expr.tyFreeVars.BranchList.tyFreeVars, List.mem_append]; exact Or.inl hy)))
          (fun p hp hc => hSe p (List.mem_append_left _ (List.mem_append_left _ hp))
            (by simp only [Expr.tyFreeVars.BranchList.tyFreeVars, List.mem_append]; exact Or.inl hc))).2 p hp)
      have h0' : TypeOfHM (S₁.onCtx ctx).eraseBounds body.erase (Ty.eraseBounds τb) := by
        rwa [hS₁τb] at h0
      have h1 := TypeOfHM.onSubst_eraseBounds_fixed_append S₁ S₂ hS₁lc hS₂lc
        (herase_subst body S₁) (herase_subst body S₂)
        (by simpa only [herase_eraseBounds body] using h0')
      have huni_eq := huni.unifies
      have h1s : TypeOfHM ((S₁ ++ S₂).onCtx ctx).eraseBounds body.erase
          (Ty.eraseBounds (S₂.onTy τb)) := by
        simpa only [herase_eraseBounds body] using h1
      have h1ρ : TypeOfHM ((S₁ ++ S₂).onCtx ctx).eraseBounds body.erase
          (Ty.eraseBounds (S₂.onTy (S₁.onTy ρ))) := by
        rwa [huni_eq] at h1s
      have h2 := TypeOfHM.onSubst_eraseBounds_fixed (ctx := (S₁ ++ S₂).onCtx ctx)
        (e := body.erase) (τ := S₂.onTy (S₁.onTy ρ)) S₃ hS₃lc (herase_subst body S₃)
        (by simpa only [herase_eraseBounds body] using h1ρ)
      have hctx_eq : (S₃.onCtx ((S₁ ++ S₂).onCtx ctx)).eraseBounds =
          ((S₁ ++ S₂ ++ S₃).onCtx ctx).eraseBounds := by rw [← Subst.onCtx_append]
      have hτ_eq : Ty.eraseBounds (S₃.onTy (S₂.onTy (S₁.onTy ρ))) =
          Ty.eraseBounds ((S₁ ++ S₂ ++ S₃).onTy ρ) := by
        rw [Subst.onTy_append, Subst.onTy_append]
      have hfinal : TypeOfHM ((S₁ ++ S₂ ++ S₃).onCtx ctx).eraseBounds body.erase
          (Ty.eraseBounds ((S₁ ++ S₂ ++ S₃).onTy ρ)) := by
        have key := h2
        rw [hctx_eq, hτ_eq] at key
        simpa only [herase_eraseBounds body] using key
      exact TypeOfMatchBranch.wildcard hfinal
    · have hctx_eq : (S₃.onCtx (S₂.onCtx (S₁.onCtx ctx))).eraseBounds =
          ((S₁ ++ S₂ ++ S₃).onCtx ctx).eraseBounds := by
        simp only [← Subst.onCtx_append, List.append_assoc]
      have hscrut_eq : Ty.eraseBounds (S₃.onTy (S₂.onTy (S₁.onTy scrutTy))) =
          Ty.eraseBounds ((S₁ ++ S₂ ++ S₃).onTy scrutTy) := by
        simp only [Subst.onTy_append, List.append_assoc]
      have hρ_eq : Ty.eraseBounds (S₃.onTy (S₂.onTy (S₁.onTy ρ))) =
          Ty.eraseBounds ((S₁ ++ S₂ ++ S₃).onTy ρ) := by
        simp only [Subst.onTy_append, List.append_assoc]
      have key := hrest_sound p hp_rest
      rwa [hctx_eq, hscrut_eq, hρ_eq] at key
  termination_by Expr.sizeBranches brs
  decreasing_by
    all_goals (try subst_vars; try simp only [Expr.sizeBranches]; omega)

theorem InferRecGroup.sound {Φ ctx bindings specs Φ' S}
    (h : InferRecGroup Φ ctx bindings specs Φ' S)
    (hctx : CtxWF ctx) (hbelow : CtxBelow Φ ctx)
    (hspecs : ∀ s ∈ specs, s.LC) (hspecsB : ∀ s ∈ specs, s.BelowFvars Φ)
    (hspecs_env : ∀ s ∈ specs, ∀ y ∈ s.freeVars, y ∈ ctx.env.freeVars)
    (K : List Nat) (hKΦ : ∀ k ∈ K, k < Φ)
    (hKbr : ∀ y ∈ Expr.tyFreeVars.RecGroup.tyFreeVars bindings, y ∈ K)
    (hKsch : ∀ σ, RecSpec.poly σ ∈ specs → ∀ y ∈ σ.body.freeVars, y ∈ K)
    (hSK : ∀ p ∈ S, p.1 ∉ K) :
    ∀ p ∈ bindings.zip (specs.map (RecSpec.onSubst S)), ∀ τ, p.2 = RecSpec.mono τ →
        TypeOfHM (S.onCtx ctx).eraseBounds p.1.erase (Ty.eraseBounds τ) := by
  have herase_tfv : ∀ e : Expr, (e.erase).tyFreeVars = [] := by
    intro e
    induction e using Expr.rec_strong with
    | primLit p => simp [Expr.erase, Expr.tyFreeVars]
    | primBinOp op => simp [Expr.erase, Expr.tyFreeVars]
    | ctor c => simp [Expr.erase, Expr.tyFreeVars]
    | var i  => simp [Expr.erase, Expr.tyFreeVars]
    | app f arg ihf iha => simp [Expr.erase_app, Expr.tyFreeVars, ihf, iha]
    | lambda ann body ih => simp [Expr.erase_lambda, Expr.tyFreeVars, ih, Option.elim_none]
    | letIn ann rhs body ihr ihb =>
      simp [Expr.erase_letIn, Expr.tyFreeVars, ihr, ihb, Option.elim_none]
    | match_ scrut branches ihs ihbs =>
      simp only [Expr.erase_match, Expr.tyFreeVars, ihs]
      induction branches with
      | nil => rfl
      | cons pe rest ih =>
        cases pe with
        | mk pat body =>
          simp only [Expr.tyFreeVars.BranchList.tyFreeVars, List.map_cons]
          rw [ihbs pat body (List.mem_cons_self ..)]
          rw [ih (fun pat₁ e mem => ihbs pat₁ e (List.mem_cons_of_mem _ mem))]
          simp
    | letRec anns bindings body ihbs ihb =>
      have hpair : Expr.tyFreeVars.AnnList.tyFreeVars
          (bindings.map (fun _ => none)) = [] ∧
          Expr.tyFreeVars.RecGroup.tyFreeVars (bindings.map Expr.erase) = [] := by
        induction bindings with
        | nil =>
          simp [Expr.tyFreeVars.AnnList.tyFreeVars, Expr.tyFreeVars.RecGroup.tyFreeVars]
        | cons b rest ih =>
          rcases ih (fun e mem => ihbs e (List.mem_cons_of_mem b mem)) with ⟨hA, hR⟩
          constructor
          · simp only [Expr.tyFreeVars.AnnList.tyFreeVars, List.map_cons, Option.elim_none]
            rw [hA]
            simp
          · simp only [Expr.tyFreeVars.RecGroup.tyFreeVars, List.map_cons]
            rw [ihbs b (List.mem_cons_self ..), hR]
            simp
      simp only [Expr.erase_letRec, Expr.tyFreeVars, ihb]
      rw [hpair.1, hpair.2]
      simp
  have herase_eraseBounds : ∀ e : Expr, (e.erase).eraseBounds = e.erase := by
    intro e
    induction e using Expr.rec_strong with
    | primLit p => simp [Expr.erase, Expr.eraseBounds]
    | primBinOp op => simp [Expr.erase, Expr.eraseBounds]
    | ctor c => simp [Expr.erase, Expr.eraseBounds]
    | var i  => simp [Expr.erase, Expr.eraseBounds]
    | app f arg ihf iha => simp only [Expr.erase_app, Expr.eraseBounds_app, ihf, iha]
    | lambda ann body ih =>
      simp only [Expr.erase_lambda, Expr.eraseBounds_lambda, Option.map_none, ih]
    | letIn ann rhs body ihr ihb =>
      simp only [Expr.erase_letIn, Expr.eraseBounds_letIn, Option.map_none, ihr, ihb]
    | match_ scrut branches ihs ihbs =>
      have hb : (branches.map (fun pe => (pe.1, pe.2.erase))).map
          (fun pe => (pe.1, pe.2.eraseBounds)) = branches.map (fun pe => (pe.1, pe.2.erase)) := by
        rw [List.map_map]
        apply List.map_congr_left
        intro pe hpe
        cases pe with
        | mk pat body => simp [ihbs pat body hpe]
      simp only [Expr.erase_match, Expr.eraseBounds]
      rw [ihs, hb]
    | letRec anns bindings body ihbs ihb =>
      have hanns : (bindings.map (fun _ => none)).map (Option.map PolyTy.eraseBounds) =
          bindings.map (fun _ => none) := by
        rw [List.map_map]
        apply List.map_congr_left
        intro b _
        rfl
      have hbs : (bindings.map Expr.erase).map Expr.eraseBounds = bindings.map Expr.erase := by
        rw [List.map_map]
        apply List.map_congr_left
        intro b hb
        exact ihbs b hb
      simp only [Expr.erase_letRec, Expr.eraseBounds]
      rw [hanns, hbs, ihb]
  have herase_subst : ∀ (e : Expr) (S : Subst), (e.erase).substTyFvars S = e.erase := by
    intro e S
    exact Expr.substTyFvars_eq_self_of_not_mem_tyFreeVars (fun p hp hc => by
      rw [herase_tfv e] at hc
      simp at hc)
  cases h with
  | nil =>
    intro p hp τ hτ
    simp at hp
  | consMono he huni hrest =>
    intro p hp τ0 hτ0
    expose_names
    simp only [Expr.tyFreeVars.RecGroup.tyFreeVars, List.mem_append] at hKbr
    obtain ⟨hτ'_lc, hS₁⟩ := Infer.lc he hctx
    have hτ_lc : τ.IsLC := hspecs (.mono τ) List.mem_cons_self
    have hS₂ := huni.lc hτ'_lc (Subst.onTy_lc hS₁ hτ_lc)
    have hle1 := Infer.frontier_le he
    have he_below := Infer.belowFvars he hbelow (fun y hy => hKΦ y (hKbr y (.inl hy)))
    have hτ_below : Ty.BelowFvars Φ τ := hspecsB (.mono τ) List.mem_cons_self
    have hS₁τ := Subst.onTy_belowFvars he_below.2 (hτ_below.mono hle1)
    have hS₂below := UnifyRel.belowFvars huni he_below.1 hS₁τ
    have hS₂dom : ∀ p ∈ S₂, p.1 < Φ₁ := by
      intro p hp
      rcases UnifyRel.dom_mem huni p hp with h | h
      · exact he_below.1.mem_lt p.1 h
      · exact hS₁τ.mem_lt p.1 h
    have hbelow2 := Subst.onCtx_below hS₂below (le_refl _)
      (Subst.onCtx_below he_below.2 hle1 hbelow)
    have hctx2 := Subst.onCtx_wf hS₂ (Subst.onCtx_wf hS₁ hctx)
    have hK1 : ∀ p ∈ S₁, p.1 ∉ K := fun p hp =>
      hSK p (List.mem_append_left _ (List.mem_append_left _ hp))
    have hK2 : ∀ p ∈ S₂, p.1 ∉ K := fun p hp =>
      hSK p (List.mem_append_left _ (List.mem_append_right _ hp))
    have hK3 : ∀ p ∈ S₃, p.1 ∉ K := fun p hp => hSK p (List.mem_append_right _ hp)
    have hspecs' : ∀ s' ∈ specs.map (RecSpec.onSubst (S₁ ++ S₂)), s'.LC := by
      intro s' hs'
      obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hs'
      exact RecSpec.LC.onSubst (fun p hp => (List.mem_append.mp hp).elim (hS₁ p) (hS₂ p))
        (hspecs s (List.mem_cons_of_mem _ hs))
    have hspecsB' : ∀ s' ∈ specs.map (RecSpec.onSubst (S₁ ++ S₂)), s'.BelowFvars Φ₁ := by
      intro s' hs'
      obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hs'
      exact RecSpec.BelowFvars.onSubst
        (fun p hp => (List.mem_append.mp hp).elim (fun h => he_below.2 p h)
          (fun h => hS₂below p h))
        ((hspecsB s (List.mem_cons_of_mem _ hs)).mono hle1)
    have hspecs_env' : ∀ s' ∈ specs.map (RecSpec.onSubst (S₁ ++ S₂)),
        ∀ y ∈ s'.freeVars, y ∈ (S₂.onCtx (S₁.onCtx ctx)).env.freeVars := by
      intro s' hs' y hy
      obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hs'
      have h1 := RecSpec.freeVars_onSubst_mem_onEnv
        (hspecs_env s (List.mem_cons_of_mem _ hs))
        (fun σ' hseq q hq hc => (List.mem_append.mp hq).elim
          (fun hq1 => hK1 q hq1 (hKsch σ' (List.mem_cons_of_mem _ (hseq ▸ hs)) q.1 hc))
          (fun hq2 => hK2 q hq2 (hKsch σ' (List.mem_cons_of_mem _ (hseq ▸ hs)) q.1 hc)))
        y hy
      rw [Subst.onEnv_append] at h1
      exact h1
    have hS₃lc : ∀ p ∈ S₃, p.2.IsLC := InferRecGroup.lc hrest hctx2 hspecs'
    have hmono_tail := InferRecGroup.sound hrest hctx2 hbelow2
      hspecs' hspecsB' hspecs_env' K (fun k hk => lt_of_lt_of_le (hKΦ k hk) hle1)
      (fun y hy => hKbr y (.inr hy))
      (fun σ' hσ' => hKsch σ' (List.mem_cons_of_mem _ (RecSpec.poly_mem_map_onSubst.mp hσ')))
      hK3
    have hspecmap : specs.map (RecSpec.onSubst (S₁ ++ S₂ ++ S₃))
        = (specs.map (RecSpec.onSubst (S₁ ++ S₂))).map (RecSpec.onSubst S₃) := by
      rw [List.map_map]
      exact List.map_congr_left (fun s _ => RecSpec.onSubst_append (S₁ ++ S₂) S₃ s)
    simp only [List.map_cons, List.zip_cons_cons, List.mem_cons] at hp
    rcases hp with rfl | hp_rest
    · have hred : RecSpec.onSubst (S₁ ++ S₂ ++ S₃) (RecSpec.mono τ)
          = RecSpec.mono ((S₁ ++ S₂ ++ S₃).onTy τ) := rfl
      rw [hred] at hτ0
      injection hτ0 with hτeq
      subst hτeq
      have h0 := Infer.sound he hctx hbelow K hKΦ (fun y hy => hKbr y (.inl hy)) hK1
      have hS₁τ' : S₁.onTy τ' = τ' := Ty.substFvars_eq_self_of_no_key (fun p hp =>
        (Infer.eliminates he hbelow (fun y hy => hKΦ y (hKbr y (.inl hy)))
          (fun p hp hc => hK1 p hp (hKbr p.1 (.inl hc)))).2 p hp)
      have h0' : TypeOfHM (S₁.onCtx ctx).eraseBounds e.erase (Ty.eraseBounds τ') := by
        rwa [hS₁τ'] at h0
      have h1 := TypeOfHM.onSubst_eraseBounds_fixed_append S₁ S₂ hS₁ hS₂
        (herase_subst e S₁) (herase_subst e S₂)
        (by simpa only [herase_eraseBounds e] using h0')
      have huni_eq := huni.unifies
      have h1s : TypeOfHM ((S₁ ++ S₂).onCtx ctx).eraseBounds e.erase
          (Ty.eraseBounds (S₂.onTy τ')) := by
        simpa only [herase_eraseBounds e] using h1
      have h1' : TypeOfHM ((S₁ ++ S₂).onCtx ctx).eraseBounds e.erase
          (Ty.eraseBounds (S₂.onTy (S₁.onTy τ))) := by
        rwa [huni_eq] at h1s
      have h2 := TypeOfHM.onSubst_eraseBounds_fixed (ctx := (S₁ ++ S₂).onCtx ctx)
        (e := e.erase) (τ := S₂.onTy (S₁.onTy τ)) S₃ hS₃lc (herase_subst e S₃)
        (by simpa only [herase_eraseBounds e] using h1')
      have hctx_eq : (S₃.onCtx ((S₁ ++ S₂).onCtx ctx)).eraseBounds =
          ((S₁ ++ S₂ ++ S₃).onCtx ctx).eraseBounds := by rw [← Subst.onCtx_append]
      have hty_eq : Ty.eraseBounds (S₃.onTy (S₂.onTy (S₁.onTy τ))) =
          Ty.eraseBounds ((S₁ ++ S₂ ++ S₃).onTy τ) := by
        simp only [Subst.onTy_append]
      have h2s : TypeOfHM ((S₁ ++ S₂ ++ S₃).onCtx ctx).eraseBounds e.erase
          (Ty.eraseBounds ((S₁ ++ S₂ ++ S₃).onTy τ)) := by
        have key := h2
        rw [hctx_eq, hty_eq] at key
        simpa only [herase_eraseBounds e] using key
      exact h2s
    · rw [hspecmap] at hp_rest
      have hctx_eq : (S₃.onCtx (S₂.onCtx (S₁.onCtx ctx))).eraseBounds =
          ((S₁ ++ S₂ ++ S₃).onCtx ctx).eraseBounds := by
        simp only [← Subst.onCtx_append, List.append_assoc]
      have htail := hmono_tail p hp_rest τ0 hτ0
      rwa [hctx_eq] at htail
  | consPoly hN he huni hesc1 hesc2 hrest =>
    intro p hp τ0 hτ0
    expose_names
    simp only [Expr.tyFreeVars.RecGroup.tyFreeVars, List.mem_append] at hKbr
    have hσwf : σ.WF := hspecs (.poly σ) List.mem_cons_self
    have hrle : N + σ.paramCount ≤ Φ₁ := Infer.frontier_le he
    have hΦN' : Φ ≤ Φ₁ := le_trans hN (le_trans (Nat.le_add_right _ _) hrle)
    have hctx_pc : CtxBelow (N + σ.paramCount) ctx := fun M hM => (hbelow M hM).mono (by omega)
    have hσbody : Ty.BelowFvars Φ σ.body :=
      Ty.BelowFvars.of_freeVars_lt (fun v hv => hKΦ v (hKsch σ List.mem_cons_self v hv))
    obtain ⟨hrhs_lc, hrhs_s⟩ := Infer.lc he hctx
    set Ys := freshVars N σ.paramCount with hYs_def
    have hΦ_rhs : ∀ y ∈ (Expr.openTyVars Ys e).tyFreeVars, y < N + σ.paramCount := by
      intro y hy
      rcases Expr.tyFreeVars_openTyVars hy with h | h
      · have := hKΦ y (hKbr y (.inl h)); omega
      · simp only [Ys] at h; have := freshVars_lt y h; omega
    have hK1 : ∀ p ∈ S₁, p.1 ∉ K := fun p hp =>
      hSK p (List.mem_append_left _ (List.mem_append_left _ hp))
    have hKchk : ∀ p ∈ Schk, p.1 ∉ K := fun p hp =>
      hSK p (List.mem_append_left _ (List.mem_append_right _ hp))
    have hK2 : ∀ p ∈ S₂, p.1 ∉ K := fun p hp => hSK p (List.mem_append_right _ hp)
    have hSe_rhs : ∀ p ∈ S₁, p.1 ∉ (Expr.openTyVars Ys e).tyFreeVars := by
      intro p hp hc
      rcases Expr.tyFreeVars_openTyVars hc with h | h
      · exact hK1 p hp (hKbr p.1 (.inl h))
      · simp only [Ys] at h
        exact hesc1 p.1 h (List.mem_map.mpr ⟨p, List.mem_append_left _ hp, rfl⟩)
    obtain ⟨hr_τ, hr_s⟩ := Infer.belowFvars he hctx_pc hΦ_rhs
    have hσopen : Ty.BelowFvars Φ₁ (σ.openVars Ys) :=
      Ty.openVars_belowFvars (hσbody.mono hΦN')
        (fun x hx => by simp only [Ys] at hx; have := freshVars_lt x hx; omega)
    have hSchk_below : ∀ p ∈ Schk, Ty.BelowFvars Φ₁ p.2 := UnifyRel.belowFvars huni hr_τ hσopen
    have hSchk_lc : ∀ p ∈ Schk, p.2.IsLC :=
      UnifyRel.lc huni hrhs_lc (PolyTy.openVars_isLC hσwf (by simp [Ys]))
    have hctx' : CtxWF (Schk.onCtx (S₁.onCtx ctx)) :=
      Subst.onCtx_wf hSchk_lc (Subst.onCtx_wf hrhs_s hctx)
    have hbelow' : CtxBelow Φ₁ (Schk.onCtx (S₁.onCtx ctx)) :=
      Subst.onCtx_below hSchk_below (le_refl _) (Subst.onCtx_below hr_s hrle hctx_pc)
    have hspecs' : ∀ s' ∈ specs.map (RecSpec.onSubst (S₁ ++ Schk)), s'.LC := by
      intro s' hs'
      obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hs'
      exact RecSpec.LC.onSubst (fun p hp => (List.mem_append.mp hp).elim (hrhs_s p) (hSchk_lc p))
        (hspecs s (List.mem_cons_of_mem _ hs))
    have hspecsB' : ∀ s' ∈ specs.map (RecSpec.onSubst (S₁ ++ Schk)), s'.BelowFvars Φ₁ := by
      intro s' hs'
      obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hs'
      exact RecSpec.BelowFvars.onSubst
        (fun p hp => (List.mem_append.mp hp).elim (fun h1 => hr_s p h1)
          (fun h2 => hSchk_below p h2))
        ((hspecsB s (List.mem_cons_of_mem _ hs)).mono (by omega))
    have hspecs_env' : ∀ s' ∈ specs.map (RecSpec.onSubst (S₁ ++ Schk)),
        ∀ y ∈ s'.freeVars, y ∈ (Schk.onCtx (S₁.onCtx ctx)).env.freeVars := by
      intro s' hs' y hy
      obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hs'
      have h1 := RecSpec.freeVars_onSubst_mem_onEnv
        (hspecs_env s (List.mem_cons_of_mem _ hs))
        (fun σ' hseq q hq hc => (List.mem_append.mp hq).elim
          (fun hq1 => hK1 q hq1 (hKsch σ' (List.mem_cons_of_mem _ (hseq ▸ hs)) q.1 hc))
          (fun hq2 => hKchk q hq2 (hKsch σ' (List.mem_cons_of_mem _ (hseq ▸ hs)) q.1 hc)))
        y hy
      rw [Subst.onEnv_append] at h1
      exact h1
    have hKbr' : ∀ y ∈ Expr.tyFreeVars.RecGroup.tyFreeVars rest, y ∈ K :=
      fun y hy => hKbr y (.inr hy)
    have hKsch' : ∀ σ', RecSpec.poly σ' ∈ specs.map (RecSpec.onSubst (S₁ ++ Schk)) →
        ∀ y ∈ σ'.body.freeVars, y ∈ K := fun σ' hσ' =>
      hKsch σ' (List.mem_cons_of_mem _ (RecSpec.poly_mem_map_onSubst.mp hσ'))
    have hS₂lc : ∀ p ∈ S₂, p.2.IsLC := InferRecGroup.lc hrest hctx' hspecs'
    have hmono_tail := InferRecGroup.sound hrest hctx' hbelow'
      hspecs' hspecsB' hspecs_env' K (fun k hk => by have := hKΦ k hk; omega)
      hKbr' hKsch' hK2
    have hctxbridge : S₂.onCtx (Schk.onCtx (S₁.onCtx ctx)) = (S₁ ++ Schk ++ S₂).onCtx ctx := by
      rw [show (S₁ ++ Schk ++ S₂ : Subst) = (S₁ ++ Schk) ++ S₂ from rfl,
          Subst.onCtx_append, Subst.onCtx_append]
    have hspecmap : specs.map (RecSpec.onSubst (S₁ ++ Schk ++ S₂))
        = (specs.map (RecSpec.onSubst (S₁ ++ Schk))).map (RecSpec.onSubst S₂) := by
      rw [List.map_map]
      exact List.map_congr_left (fun s _ => RecSpec.onSubst_append (S₁ ++ Schk) S₂ s)
    simp only [List.map_cons, List.zip_cons_cons, List.mem_cons] at hp
    rcases hp with rfl | hp_rest
    · exact absurd hτ0 (by simp [RecSpec.onSubst])
    · rw [hspecmap] at hp_rest
      have hctx_eq : (S₂.onCtx (Schk.onCtx (S₁.onCtx ctx))).eraseBounds =
          ((S₁ ++ Schk ++ S₂).onCtx ctx).eraseBounds := by rw [hctxbridge]
      have htail := hmono_tail p hp_rest τ0 hτ0
      rwa [hctx_eq] at htail
  termination_by Expr.sizeRecGroup bindings
  decreasing_by
    all_goals (try subst_vars; try simp only [Expr.sizeRecGroup, Expr.size_openTyVars]; omega)

end


/-! ### Generalisation/substitution commutation lemmas (for `letIn` principality) -/

/-- For a nodup list, `idxOf?` of the element at index `i` is `some i`. -/
private theorem List.idxOf?_getElem_self {α : Type*} [BEq α] [LawfulBEq α]
    {l : List α} (hnd : l.Nodup) {i : Nat} (hi : i < l.length) :
    l.idxOf? l[i] = some i := by
  induction l generalizing i with
  | nil => simp at hi
  | cons x xs ih =>
    rw [List.nodup_cons] at hnd
    cases i with
    | zero => simp [List.idxOf?_cons]
    | succ j =>
      have hj : j < xs.length := by simpa using hi
      have hmem : xs[j] ∈ xs := List.getElem_mem hj
      have hxne : (x == xs[j]) = false := by
        simp only [beq_eq_false_iff_ne, ne_eq]
        intro h; exact hnd.1 (h ▸ hmem)
      rw [List.getElem_cons_succ, List.idxOf?_cons, hxne]
      simp [ih hnd.2 hj]

/-- Closing names fresh for `X` commutes into an `openWith`. -/
theorem Ty.closeOver_openWith_comm {Xs : List Nat} {Vs : List Ty} {X : Ty}
    (hfresh : ∀ x ∈ Xs, x ∉ X.freeVars) :
    Ty.closeOver Xs (Ty.openWith Vs X) = Ty.openWith (Vs.map (Ty.closeOver Xs)) X := by
  induction X using Ty.rec_strong with
  | prim p => rfl
  | bvar i =>
    simp only [Ty.openWith, Ty.instantiate]
    rw [List.getElem?_map]
    cases Vs[i]? with
    | none => simp [Ty.closeOver]
    | some t => simp
  | fvar n =>
    have hn : n ∉ Xs := fun h => hfresh n h (by simp [Ty.freeVars])
    simp only [Ty.openWith_fvar]
    rw [Ty.closeOver.eq_6, List.idxOf?_eq_none_iff.mpr hn]
  | arrow a b iha ihb =>
    have hfa : ∀ x ∈ Xs, x ∉ a.freeVars := fun x hx hc =>
      hfresh x hx (List.mem_dedup.mpr (List.mem_append.mpr (Or.inl hc)))
    have hfb : ∀ x ∈ Xs, x ∉ b.freeVars := fun x hx hc =>
      hfresh x hx (List.mem_dedup.mpr (List.mem_append.mpr (Or.inr hc)))
    simp only [Ty.openWith_arrow, Ty.closeOver, iha hfa, ihb hfb]
  | customTy nm tys ih =>
    simp only [Ty.openWith_customTy, Ty.closeOver, TyList.closeOver_eq_map, List.map_map]
    apply congrArg (Ty.customTy nm)
    apply List.map_congr_left
    intro t ht
    simp only [Function.comp_apply]
    exact ih t ht (fun x hx hc => hfresh x hx (TyList.mem_freeVars_of_mem ht hc))
  | bl lo hi e ih =>
    have he : ∀ x ∈ Xs, x ∉ e.freeVars := fun x hx hc =>
      hfresh x hx (by simpa only [Ty.freeVars] using hc)
    simp only [Ty.openWith_bl, Ty.closeOver, ih he]

/-- Composition of openings (when `X`'s bvars are covered by the inner args). -/
theorem Ty.openWith_openWith {Vs Ws : List Ty} {X : Ty}
    (hbv : ContainsBvarsUpTo Ws.length X) :
    Ty.openWith Vs (Ty.openWith Ws X) = Ty.openWith (Ws.map (Ty.openWith Vs)) X := by
  induction X using Ty.rec_strong with
  | prim p => rfl
  | fvar n => rfl
  | bvar i =>
    cases hbv with
    | bvar hlt =>
      have hi : Ws[i]? = some Ws[i] := List.getElem?_eq_getElem hlt
      have e1 : Ty.openWith Ws (.bvar i) = Ws[i] := by
        simp only [Ty.openWith, Ty.instantiate, hi, Option.getD_some]
      have e2 : Ty.openWith (Ws.map (Ty.openWith Vs)) (.bvar i) = Ty.openWith Vs (Ws[i]) := by
        simp only [Ty.openWith, Ty.instantiate, List.getElem?_map, hi, Option.map_some,
          Option.getD_some]
      rw [e1, e2]
  | arrow a b iha ihb =>
    cases hbv with
    | arrow hba hbb =>
      simp only [Ty.openWith_arrow, iha hba, ihb hbb]
  | customTy nm tys ih =>
    cases hbv with
    | customTy hball =>
      simp only [Ty.openWith_customTy, List.map_map]
      apply congrArg (Ty.customTy nm)
      apply List.map_congr_left
      intro t ht
      simp only [Function.comp_apply]
      exact ih t ht (hball t ht)
  | bl lo hi e ih =>
    cases hbv with
    | bl he =>
      simp only [Ty.openWith_bl, ih he]

/-! ### Free-var bounds (for the `letIn` principality freshness obligation) -/

/-- Every free var of `S.onTy Z` traces back to a free var of `Z`. -/
theorem Ty.mem_freeVars_onTy_iff {S : Subst} {x : Nat} {Z : Ty} :
    x ∈ (S.onTy Z).freeVars ↔ ∃ v ∈ Z.freeVars, x ∈ (S.onTy (.fvar v)).freeVars := by
  induction Z using Ty.rec_strong with
  | prim p => simp [Subst.onTy_prim, Ty.freeVars]
  | bvar i => simp [Subst.onTy_bvar, Ty.freeVars]
  | fvar n => simp only [Ty.freeVars, List.mem_singleton, exists_eq_left]
  | arrow a b iha ihb =>
    simp only [Subst.onTy_arrow, Ty.freeVars, List.mem_dedup, List.mem_append]
    rw [iha, ihb]
    constructor
    · rintro (⟨v, hv, hx⟩ | ⟨v, hv, hx⟩)
      · exact ⟨v, .inl hv, hx⟩
      · exact ⟨v, .inr hv, hx⟩
    · rintro ⟨v, (hv | hv), hx⟩
      · exact .inl ⟨v, hv, hx⟩
      · exact .inr ⟨v, hv, hx⟩
  | customTy nm tys ih =>
    simp only [Subst.onTy_customTy, Ty.freeVars]
    rw [TyList.mem_freeVars_iff]
    constructor
    · rintro ⟨t', ht', hx⟩
      obtain ⟨t, ht, rfl⟩ := List.mem_map.mp ht'
      obtain ⟨v, hv, hxv⟩ := (ih t ht).mp hx
      exact ⟨v, TyList.mem_freeVars_iff.mpr ⟨t, ht, hv⟩, hxv⟩
    · rintro ⟨v, hv, hx⟩
      obtain ⟨t, ht, hvt⟩ := TyList.mem_freeVars_iff.mp hv
      exact ⟨S.onTy t, List.mem_map.mpr ⟨t, ht, rfl⟩, (ih t ht).mpr ⟨v, hvt, hx⟩⟩
  | bl lo hi e ih =>
    simp only [Subst.onTy_bl, Ty.freeVars]
    exact ih

/-- Closing over vars only removes free vars. -/
theorem Ty.closeOver_freeVars_subset {gs : List Nat} {τ : Ty} :
    (Ty.closeOver gs τ).freeVars ⊆ τ.freeVars := by
  induction τ using Ty.rec_strong with
  | prim p => simp [Ty.closeOver, Ty.freeVars]
  | bvar i => simp [Ty.closeOver, Ty.freeVars]
  | fvar n =>
    rw [Ty.closeOver.eq_6]
    cases gs.idxOf? n with
    | none => exact fun x hx => hx
    | some i => simp [Ty.freeVars]
  | arrow a b iha ihb =>
    intro x hx
    simp only [Ty.closeOver, Ty.freeVars, List.mem_dedup, List.mem_append] at hx ⊢
    rcases hx with h | h
    · exact .inl (iha h)
    · exact .inr (ihb h)
  | customTy nm tys ih =>
    intro x hx
    simp only [Ty.closeOver, Ty.freeVars, TyList.closeOver_eq_map] at hx ⊢
    obtain ⟨t', ht', hxt⟩ := TyList.mem_freeVars_iff.mp hx
    obtain ⟨t, ht, rfl⟩ := List.mem_map.mp ht'
    exact TyList.mem_freeVars_iff.mpr ⟨t, ht, ih t ht hxt⟩
  | bl lo hi e ih =>
    intro x hx
    simp only [Ty.closeOver, Ty.freeVars] at hx ⊢
    exact ih hx


/-! ### Principal generalization generalizes the declarative scheme -/

/-- General form: closing `τ₁` over *any* variable set `g` (transported by the
    residual `R`) yields a scheme at least as general as a declarative scheme `M`
    whose fresh opening factors as `R.onTy τ₁`. The crux of `let`/`letPair`
    principality: the body, declaratively typed under `M`, can be retyped under
    the more general scheme the algorithm produces. (The proof barely uses what
    `g` is, so `genScheme` and the pair schemes are all instances.) -/
theorem closeOver_generalizes {g : List Nat} {τ₁ : Ty} {R : Subst} {M : PolyTy} {Xs : List Nat}
    (hτ₁ : τ₁.IsLC) (hR : ∀ p ∈ R, p.2.IsLC) (hMwf : M.WF)
    (hXnodup : Xs.Nodup) (hXlen : Xs.length = M.paramCount)
    (hXMbody : ∀ x ∈ Xs, x ∉ M.body.freeVars)
    (htyr : Ty.openVars Xs M.body = R.onTy τ₁)
    (hXM'' : ∀ x ∈ Xs, x ∉ (R.onPolyTy ⟨g.length, Ty.closeOver g τ₁⟩).body.freeVars) :
    (R.onPolyTy ⟨g.length, Ty.closeOver g τ₁⟩).Generalizes M := by
  intro tyArgs ty htyargs_lc hinst
  -- `ty = openWith Vs M.body` for the length-`paramCount` prefix `Vs` of `tyArgs`.
  have hty_eq : ty = Ty.openWith
      ((List.range M.paramCount).map (fun i => (tyArgs[i]?).getD (.prim .unit))) M.body :=
    hinst.eq_openWith_range hMwf
  set Vs := (List.range M.paramCount).map (fun i => (tyArgs[i]?).getD (.prim .unit)) with hVsdef
  have hVs_len : Vs.length = M.paramCount := by rw [hVsdef]; simp
  have hVs_lc : ∀ v ∈ Vs, v.IsLC := by
    intro v hv
    rw [hVsdef] at hv
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp hv
    cases hh : tyArgs[i]? with
    | none => simp only [Option.getD_none]; exact ContainsBvarsUpTo.prim
    | some t => simp only [Option.getD_some]; exact htyargs_lc t (List.mem_of_getElem? hh)
  -- `M.body = closeOver Xs (R.onTy τ₁)` (close the just-opened fresh names).
  have hMbody : M.body = Ty.closeOver Xs (R.onTy τ₁) := by
    have hbv : ContainsBvarsUpTo Xs.length M.body := by rw [hXlen]; exact hMwf
    have hrt := Ty.closeOver_openVars_self hXnodup hbv hXMbody
    rw [htyr] at hrt
    exact hrt.symm
  -- `R.onTy τ₁ = openWith Wg M'.body` where `Wg = R` applied to each gen var.
  have hRτ₁ : R.onTy τ₁ = Ty.openWith
      (g.map (fun gj => R.onTy (Ty.fvar gj)))
      ((R.onPolyTy ⟨g.length, Ty.closeOver g τ₁⟩).body) := by
    show R.onTy τ₁ = Ty.openWith (g.map (fun gj => R.onTy (Ty.fvar gj)))
      (R.onTy (Ty.closeOver g τ₁))
    conv_lhs => rw [← Ty.openVars_closeOver_self (gs := g) hτ₁]
    rw [Ty.openVars_eq_openWith, Subst.onTy_openWith hR, List.map_map]
    simp only [Function.comp_def]
  -- Round-trip to `M'.body`, then re-open with the composed args.
  have hbv1 : ContainsBvarsUpTo
      ((g.map (fun gj => R.onTy (Ty.fvar gj))).map (Ty.closeOver Xs)).length
      ((R.onPolyTy ⟨g.length, Ty.closeOver g τ₁⟩).body) := by
    have hwf := Subst.onPolyTy_wf hR (M := ⟨g.length, Ty.closeOver g τ₁⟩)
      (Ty.closeOver_preserves_bvars hτ₁)
    have hlen : ((g.map (fun gj => R.onTy (Ty.fvar gj))).map (Ty.closeOver Xs)).length
        = (R.onPolyTy ⟨g.length, Ty.closeOver g τ₁⟩).paramCount := by
      simp only [List.length_map]; rfl
    rw [hlen]; exact hwf
  have hty_final : ty = Ty.openWith
      (((g.map (fun gj => R.onTy (Ty.fvar gj))).map (Ty.closeOver Xs)).map (Ty.openWith Vs))
      ((R.onPolyTy ⟨g.length, Ty.closeOver g τ₁⟩).body) :=
    calc ty
        = Ty.openWith Vs M.body := hty_eq
      _ = Ty.openWith Vs (Ty.closeOver Xs (R.onTy τ₁)) := by rw [hMbody]
      _ = Ty.openWith Vs (Ty.closeOver Xs (Ty.openWith
            (g.map (fun gj => R.onTy (Ty.fvar gj)))
            ((R.onPolyTy ⟨g.length, Ty.closeOver g τ₁⟩).body))) := by rw [hRτ₁]
      _ = Ty.openWith Vs (Ty.openWith
            ((g.map (fun gj => R.onTy (Ty.fvar gj))).map (Ty.closeOver Xs))
            ((R.onPolyTy ⟨g.length, Ty.closeOver g τ₁⟩).body)) := by
              rw [Ty.closeOver_openWith_comm hXM'']
      _ = Ty.openWith
            (((g.map (fun gj => R.onTy (Ty.fvar gj))).map (Ty.closeOver Xs)).map
              (Ty.openWith Vs))
            ((R.onPolyTy ⟨g.length, Ty.closeOver g τ₁⟩).body) := by rw [Ty.openWith_openWith hbv1]
  -- The composed args are LC and witness the instantiation.
  refine ⟨((g.map (fun gj => R.onTy (Ty.fvar gj))).map (Ty.closeOver Xs)).map
      (Ty.openWith Vs), ?_, ?_⟩
  · intro v hv
    obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hv
    obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hz
    obtain ⟨gj, _, rfl⟩ := List.mem_map.mp hw
    have hwlc : (R.onTy (Ty.fvar gj)).IsLC := Subst.onTy_lc hR ContainsBvarsUpTo.fvar
    have hzbv : ContainsBvarsUpTo Xs.length (Ty.closeOver Xs (R.onTy (Ty.fvar gj))) :=
      Ty.closeOver_preserves_bvars hwlc
    exact Ty.openWith_isLC hVs_lc hzbv (by rw [hVs_len]; exact hXlen.le)
  · have hwf := Subst.onPolyTy_wf hR (M := ⟨g.length, Ty.closeOver g τ₁⟩)
      (Ty.closeOver_preserves_bvars hτ₁)
    have hVs'len : (((g.map (fun gj => R.onTy (Ty.fvar gj))).map
        (Ty.closeOver Xs)).map (Ty.openWith Vs)).length
        = (R.onPolyTy ⟨g.length, Ty.closeOver g τ₁⟩).paramCount := by
      simp only [List.length_map]; rfl
    have hinstW := InstantiatesBy.openWith hwf (le_of_eq hVs'len.symm)
    rw [hty_final]
    exact hinstW

/-- A mono spec's monotype sits in the group's shared-monotype pool. -/
private theorem RecSpecs.monoTy_mem_monoTys {specs : List RecSpec} {τ : Ty}
    (h : RecSpec.mono τ ∈ specs) : τ ∈ RecSpecs.monoTys specs := by
  simp only [RecSpecs.monoTys, List.mem_filterMap]
  exact ⟨RecSpec.mono τ, h, rfl⟩

/-! ## Stage 4: the executable `unify` and `infer`

Everything above specifies and certifies the *relations* `UnifyRel` and `Infer`.
This final stage gives the actual *functions* (`unify`, `infer`) and proves they
**refine** those relations. The only non-trivial part is `unify`'s termination,
discharged with the standard lexicographic measure `(#distinct free vars, size)`:
each var-elimination step strictly drops the variable count, while the structural
decompositions (`arrow`/`pair`/`customTy`) drop `Ty.size`. The supporting
variable-tracking lemmas about `UnifyRel`-substitutions are proved first. -/

/-! (Variable-tracking lemmas for substitutions and `UnifyRel` relocated to the
    soundness-prerequisites section above, before `Infer.sound`.) -/

/-! ### Termination measure for `unify`

`pairVars`/`listVars` count the distinct free vars of a pair of types / type
lists; these are the primary (lexicographic) component of `unify`'s measure,
with `Ty.size`/`TyList.size` as the tiebreak. The six `unifyDec_*` lemmas package
the decrease of each recursive call. -/

/-- Distinct free type vars of a pair of monotypes. -/
def pairVars (a b : Ty) : List Nat := (a.freeVars ++ b.freeVars).dedup

/-- Distinct free type vars of a pair of monotype lists. -/
def listVars (as bs : List Ty) : List Nat := (TyList.freeVars as ++ TyList.freeVars bs).dedup

theorem mem_pairVars {a b : Ty} {v : Nat} :
    v ∈ pairVars a b ↔ v ∈ a.freeVars ∨ v ∈ b.freeVars := by
  simp [pairVars, List.mem_dedup, List.mem_append]

theorem mem_listVars {as bs : List Ty} {v : Nat} :
    v ∈ listVars as bs ↔ (∃ t ∈ as, v ∈ t.freeVars) ∨ (∃ t ∈ bs, v ∈ t.freeVars) := by
  simp only [listVars, List.mem_dedup, List.mem_append, mem_TyList_freeVars]

theorem pairVars_nodup {a b : Ty} : (pairVars a b).Nodup := List.nodup_dedup _
theorem listVars_nodup {as bs : List Ty} : (listVars as bs).Nodup := List.nodup_dedup _

theorem nodup_length_le {l₁ l₂ : List Nat} (h : l₁.Nodup) (hsub : l₁ ⊆ l₂) :
    l₁.length ≤ l₂.length := (h.subperm hsub).length_le

theorem nodup_length_lt {l₁ l₂ : List Nat} (h : l₁.Nodup) (hsub : l₁ ⊆ l₂)
    {z : Nat} (hz2 : z ∈ l₂) (hz1 : z ∉ l₁) : l₁.length < l₂.length := by
  have hcons : (z :: l₁).Nodup := List.nodup_cons.mpr ⟨hz1, h⟩
  have hsub2 : (z :: l₁) ⊆ l₂ := List.cons_subset.mpr ⟨hz2, hsub⟩
  have := nodup_length_le hcons hsub2
  simpa using this

theorem lexLt_left {a₁ a₂ b₁ b₂ : Nat} (h : a₁ < a₂) :
    Prod.Lex (· < ·) (· < ·) (a₁, b₁) (a₂, b₂) := Prod.Lex.left _ _ h

theorem lexLt_of_le_of_lt {a₁ a₂ b₁ b₂ : Nat} (ha : a₁ ≤ a₂) (hb : b₁ < b₂) :
    Prod.Lex (· < ·) (· < ·) (a₁, b₁) (a₂, b₂) := by
  rcases Nat.lt_or_ge a₁ a₂ with h | h
  · exact Prod.Lex.left _ _ h
  · have heq : a₁ = a₂ := Nat.le_antisymm ha h
    subst heq; exact Prod.Lex.right _ hb

theorem Subst.map_onTy_nil (ts : List Ty) : ts.map (Subst.onTy []) = ts := by
  induction ts with
  | nil => rfl
  | cons hd tl ih => simp only [List.map_cons, Subst.onTy_nil, ih]

/-- First structural subcall of `arrow`: strictly smaller (by size). -/
theorem unifyDec_arrow1 {a₁ a₂ c₁ c₂ : Ty} :
    Prod.Lex (· < ·) (· < ·)
      ((pairVars a₁ c₁).length, a₁.size + c₁.size)
      ((pairVars (.arrow a₁ a₂) (.arrow c₁ c₂)).length,
        (Ty.arrow a₁ a₂).size + (Ty.arrow c₁ c₂).size) := by
  apply lexLt_of_le_of_lt
  · refine nodup_length_le pairVars_nodup (fun v hv => ?_)
    rw [mem_pairVars] at hv ⊢
    rcases hv with h | h
    · exact Or.inl (Ty.mem_freeVars_arrowL h)
    · exact Or.inr (Ty.mem_freeVars_arrowL h)
  · simp only [Ty.size]; have := @Ty.size_pos a₂; have := @Ty.size_pos c₂; omega

/-- Second subcall of `arrow` (after applying the first unifier): strictly fewer
    distinct vars when the unifier is nontrivial, else strictly smaller by size. -/
theorem unifyDec_arrow2 {a₁ a₂ c₁ c₂ : Ty} {S₁ : Subst} (hS₁ : UnifyRel a₁ c₁ S₁) :
    Prod.Lex (· < ·) (· < ·)
      ((pairVars (S₁.onTy a₂) (S₁.onTy c₂)).length,
        (S₁.onTy a₂).size + (S₁.onTy c₂).size)
      ((pairVars (.arrow a₁ a₂) (.arrow c₁ c₂)).length,
        (Ty.arrow a₁ a₂).size + (Ty.arrow c₁ c₂).size) := by
  have hsub : pairVars (S₁.onTy a₂) (S₁.onTy c₂)
      ⊆ pairVars (.arrow a₁ a₂) (.arrow c₁ c₂) := by
    intro v hv
    rw [mem_pairVars] at hv ⊢
    rcases hv with hv | hv
    · rcases Subst.mem_freeVars_onTy hv with h | ⟨q, hq, hvq⟩
      · exact Or.inl (Ty.mem_freeVars_arrowR h)
      · rcases UnifyRel.range_mem hS₁ q hq v hvq with h' | h'
        · exact Or.inl (Ty.mem_freeVars_arrowL h')
        · exact Or.inr (Ty.mem_freeVars_arrowL h')
    · rcases Subst.mem_freeVars_onTy hv with h | ⟨q, hq, hvq⟩
      · exact Or.inr (Ty.mem_freeVars_arrowR h)
      · rcases UnifyRel.range_mem hS₁ q hq v hvq with h' | h'
        · exact Or.inl (Ty.mem_freeVars_arrowL h')
        · exact Or.inr (Ty.mem_freeVars_arrowL h')
  by_cases hnil : S₁ = []
  · subst hnil
    simp only [Subst.onTy_nil] at hsub ⊢
    apply lexLt_of_le_of_lt (nodup_length_le pairVars_nodup hsub)
    simp only [Ty.size]; have := @Ty.size_pos a₁; have := @Ty.size_pos c₁; omega
  · obtain ⟨p, rest, rfl⟩ := List.exists_cons_of_ne_nil hnil
    apply lexLt_left
    refine nodup_length_lt pairVars_nodup hsub (z := p.1) ?_ ?_
    · rw [mem_pairVars]
      rcases UnifyRel.dom_mem hS₁ p List.mem_cons_self with h | h
      · exact Or.inl (Ty.mem_freeVars_arrowL h)
      · exact Or.inr (Ty.mem_freeVars_arrowL h)
    · rw [mem_pairVars]; push_neg
      exact ⟨UnifyRel.eliminates hS₁ p List.mem_cons_self a₂,
             UnifyRel.eliminates hS₁ p List.mem_cons_self c₂⟩

/-- `customTy` subcall delegates to `unifyList` (strictly smaller by size). -/
theorem unifyDec_customTy {n₁ n₂ : TyName} {ts₁ ts₂ : List Ty} :
    Prod.Lex (· < ·) (· < ·)
      ((listVars ts₁ ts₂).length, TyList.size ts₁ + TyList.size ts₂ + 1)
      ((pairVars (.customTy n₁ ts₁) (.customTy n₂ ts₂)).length,
        (Ty.customTy n₁ ts₁).size + (Ty.customTy n₂ ts₂).size) := by
  apply lexLt_of_le_of_lt
  · refine nodup_length_le listVars_nodup (fun v hv => ?_)
    rw [mem_listVars] at hv; rw [mem_pairVars]
    rcases hv with ⟨t, ht, h⟩ | ⟨t, ht, h⟩
    · exact Or.inl (Ty.mem_freeVars_customTy ht h)
    · exact Or.inr (Ty.mem_freeVars_customTy ht h)
  · simp only [Ty.size]; omega

/-- `bl` subcall: strictly smaller by size (walk element only). -/
theorem unifyDec_bl {lo₁ hi₁ lo₂ hi₂ : FHM.Bounds.CountSlot} {e₁ e₂ : Ty} :
    Prod.Lex (· < ·) (· < ·)
      ((pairVars e₁ e₂).length, e₁.size + e₂.size)
      ((pairVars (.bl lo₁ hi₁ e₁) (.bl lo₂ hi₂ e₂)).length,
        (Ty.bl lo₁ hi₁ e₁).size + (Ty.bl lo₂ hi₂ e₂).size) := by
  apply lexLt_of_le_of_lt
  · refine nodup_length_le pairVars_nodup (fun v hv => ?_)
    rw [mem_pairVars] at hv ⊢
    rcases hv with h | h
    · exact Or.inl (Ty.mem_freeVars_bl h)
    · exact Or.inr (Ty.mem_freeVars_bl h)
  · simp only [Ty.size]; omega

/-- `BL` ~ bare `List` element unify is size-smaller. -/
theorem unifyDec_blList {lo hi : FHM.Bounds.CountSlot} {e α : Ty} :
    Prod.Lex (· < ·) (· < ·)
      ((pairVars e α).length, e.size + α.size)
      ((pairVars (.bl lo hi e) (.customTy listTyName [α])).length,
        (Ty.bl lo hi e).size + (Ty.customTy listTyName [α]).size) := by
  apply lexLt_of_le_of_lt
  · refine nodup_length_le pairVars_nodup (fun v hv => ?_)
    rw [mem_pairVars] at hv ⊢
    rcases hv with h | h
    · exact Or.inl (Ty.mem_freeVars_bl h)
    · exact Or.inr (Ty.mem_freeVars_customTy List.mem_cons_self h)
  · -- sizes: bl = 1+e, List[α] = 1+α
    change e.size + α.size < (1 + e.size) + (1 + TyList.size [α])
    change e.size + α.size < (1 + e.size) + (1 + (α.size + TyList.size ([] : List Ty)))
    simp only [TyList.size]; omega

theorem unifyDec_listBl {lo hi : FHM.Bounds.CountSlot} {e α : Ty} :
    Prod.Lex (· < ·) (· < ·)
      ((pairVars α e).length, α.size + e.size)
      ((pairVars (.customTy listTyName [α]) (.bl lo hi e)).length,
        (Ty.customTy listTyName [α]).size + (Ty.bl lo hi e).size) := by
  apply lexLt_of_le_of_lt
  · refine nodup_length_le pairVars_nodup (fun v hv => ?_)
    rw [mem_pairVars] at hv ⊢
    rcases hv with h | h
    · exact Or.inl (Ty.mem_freeVars_customTy List.mem_cons_self h)
    · exact Or.inr (Ty.mem_freeVars_bl h)
  · change α.size + e.size < (1 + TyList.size [α]) + (1 + e.size)
    change α.size + e.size < (1 + (α.size + TyList.size ([] : List Ty))) + (1 + e.size)
    simp only [TyList.size]; omega

/-- First subcall of `unifyList`'s `cons` (the head element). -/
theorem unifyDec_cons1 {t₁ t₂ : Ty} {ts₁ ts₂ : List Ty} :
    Prod.Lex (· < ·) (· < ·)
      ((pairVars t₁ t₂).length, t₁.size + t₂.size)
      ((listVars (t₁ :: ts₁) (t₂ :: ts₂)).length,
        TyList.size (t₁ :: ts₁) + TyList.size (t₂ :: ts₂) + 1) := by
  apply lexLt_of_le_of_lt
  · refine nodup_length_le pairVars_nodup (fun v hv => ?_)
    rw [mem_pairVars] at hv; rw [mem_listVars]
    rcases hv with h | h
    · exact Or.inl ⟨t₁, List.mem_cons_self, h⟩
    · exact Or.inr ⟨t₂, List.mem_cons_self, h⟩
  · simp only [TyList.size]; omega

/-- Second subcall of `unifyList`'s `cons` (the tail, after the head unifier). -/
theorem unifyDec_cons2 {t₁ t₂ : Ty} {ts₁ ts₂ : List Ty} {S₁ : Subst}
    (hS₁ : UnifyRel t₁ t₂ S₁) :
    Prod.Lex (· < ·) (· < ·)
      ((listVars (ts₁.map S₁.onTy) (ts₂.map S₁.onTy)).length,
        TyList.size (ts₁.map S₁.onTy) + TyList.size (ts₂.map S₁.onTy) + 1)
      ((listVars (t₁ :: ts₁) (t₂ :: ts₂)).length,
        TyList.size (t₁ :: ts₁) + TyList.size (t₂ :: ts₂) + 1) := by
  have hsub : listVars (ts₁.map S₁.onTy) (ts₂.map S₁.onTy)
      ⊆ listVars (t₁ :: ts₁) (t₂ :: ts₂) := by
    intro v hv
    rw [mem_listVars] at hv ⊢
    rcases hv with ⟨t, ht, h⟩ | ⟨t, ht, h⟩
    · obtain ⟨t0, ht0, rfl⟩ := List.mem_map.mp ht
      rcases Subst.mem_freeVars_onTy h with hh | ⟨q, hq, hvq⟩
      · exact Or.inl ⟨t0, List.mem_cons_of_mem _ ht0, hh⟩
      · rcases UnifyRel.range_mem hS₁ q hq v hvq with h' | h'
        · exact Or.inl ⟨t₁, List.mem_cons_self, h'⟩
        · exact Or.inr ⟨t₂, List.mem_cons_self, h'⟩
    · obtain ⟨t0, ht0, rfl⟩ := List.mem_map.mp ht
      rcases Subst.mem_freeVars_onTy h with hh | ⟨q, hq, hvq⟩
      · exact Or.inr ⟨t0, List.mem_cons_of_mem _ ht0, hh⟩
      · rcases UnifyRel.range_mem hS₁ q hq v hvq with h' | h'
        · exact Or.inl ⟨t₁, List.mem_cons_self, h'⟩
        · exact Or.inr ⟨t₂, List.mem_cons_self, h'⟩
  by_cases hnil : S₁ = []
  · subst hnil
    simp only [Subst.map_onTy_nil] at hsub ⊢
    apply lexLt_of_le_of_lt (nodup_length_le listVars_nodup hsub)
    simp only [TyList.size]; have := @Ty.size_pos t₁; have := @Ty.size_pos t₂; omega
  · obtain ⟨p, rest, rfl⟩ := List.exists_cons_of_ne_nil hnil
    apply lexLt_left
    refine nodup_length_lt listVars_nodup hsub (z := p.1) ?_ ?_
    · rw [mem_listVars]
      rcases UnifyRel.dom_mem hS₁ p List.mem_cons_self with h | h
      · exact Or.inl ⟨t₁, List.mem_cons_self, h⟩
      · exact Or.inr ⟨t₂, List.mem_cons_self, h⟩
    · rw [mem_listVars]; push_neg
      refine ⟨fun t ht hc => ?_, fun t ht hc => ?_⟩
      · obtain ⟨t0, ht0, rfl⟩ := List.mem_map.mp ht
        exact UnifyRel.eliminates hS₁ p List.mem_cons_self t0 hc
      · obtain ⟨t0, ht0, rfl⟩ := List.mem_map.mp ht
        exact UnifyRel.eliminates hS₁ p List.mem_cons_self t0 hc

/-! ### The `unify` function

`unify` is the plain-`Option Subst` erasure of `unifyCore`, the verified unifier
that returns a substitution *together with* its `UnifyRel` derivation. `unifyCore`
is the `K = []` instance of the rigidity-aware `unifyCoreK` (defined below), so
soundness is immediate (the derivation is carried) and completeness reduces to
`unifyCoreK_complete` at the empty rigid set. -/

mutual
/-- **Rigidity-aware unifier.** Like `unifyCore`, but refuses to bind any variable
    in the rigid set `K`: at a variable step it orients the binding toward the
    non-rigid side, and fails when forced to equate a rigid var with a non-variable
    or with a different rigid var. This is the executable mirror of the relational
    `UnifyRel.complete_K`; the resulting MGU **avoids `K` by construction** (carried
    in the result), so the executable keeps scoped-type-variable skolems rigid —
    which plain left-leaning `unifyCore` does not (it would bind a skolem sitting on
    the left of a flexible unification, spuriously failing the annotated-`let`
    escape check). With `K = []` it coincides with `unifyCore`. -/
def unifyCoreK (K : List Nat) (a b : Ty) :
    Option { S : Subst // UnifyRel a b S ∧ (∀ p ∈ S, p.1 ∉ K) } :=
  match a, b with
  | .prim p, .prim q =>
      if h : p = q then some ⟨[], by subst h; exact .prim, by simp⟩ else none
  | .fvar n, .fvar m =>
      if h : n = m then some ⟨[], by subst h; exact .fvarRefl, by simp⟩
      else if hnK : n ∈ K then
        if hmK : m ∈ K then none
        else some ⟨[(m, .fvar n)],
          .fvarR (by simp only [ne_eq, Ty.fvar.injEq]; omega)
            (by simp only [Ty.freeVars, List.mem_singleton]; omega),
          by intro p hp; rw [List.mem_singleton] at hp; subst hp; exact hmK⟩
      else some ⟨[(n, .fvar m)],
        .fvarL (by simp only [ne_eq, Ty.fvar.injEq]; omega)
          (by simp only [Ty.freeVars, List.mem_singleton]; omega),
        by intro p hp; rw [List.mem_singleton] at hp; subst hp; exact hnK⟩
  | .arrow a₁ a₂, .arrow c₁ c₂ =>
      match unifyCoreK K a₁ c₁ with
      | none => none
      | some ⟨S₁, hS₁, hav₁⟩ =>
        match unifyCoreK K (S₁.onTy a₂) (S₁.onTy c₂) with
        | none => none
        | some ⟨S₂, hS₂, hav₂⟩ => some ⟨S₁ ++ S₂, .arrow hS₁ hS₂, by
            intro p hp; rcases List.mem_append.mp hp with hp | hp
            · exact hav₁ p hp
            · exact hav₂ p hp⟩
  | .customTy n₁ ts₁, .customTy n₂ ts₂ =>
      if h : n₁ = n₂ then
        match unifyListCoreK K ts₁ ts₂ with
        | none => none
        | some ⟨S, hS, hav⟩ => some ⟨S, by subst h; exact .customTy hS, hav⟩
      else none
  | .bl _lo₁ _hi₁ e₁, .bl _lo₂ _hi₂ e₂ =>
      match unifyCoreK K e₁ e₂ with
      | none => none
      | some ⟨S, hS, hav⟩ => some ⟨S, .bl hS, hav⟩
  | .bl _lo _hi e, .customTy n [α] =>
      if hn : n = listTyName then
        match unifyCoreK K e α with
        | none => none
        | some ⟨S, hS, hav⟩ => some ⟨S, by subst hn; exact .blList hS, hav⟩
      else none
  | .customTy n [α], .bl _lo _hi e =>
      if hn : n = listTyName then
        match unifyCoreK K α e with
        | none => none
        | some ⟨S, hS, hav⟩ => some ⟨S, by subst hn; exact .listBl hS, hav⟩
      else none
  | .fvar n, b =>
      if hnK : n ∈ K then none
      else if h : n ∈ b.freeVars then none
      else some ⟨[(n, b)],
        .fvarL (by intro he; subst he; exact h (by simp [Ty.freeVars])) h,
        by intro p hp; rw [List.mem_singleton] at hp; subst hp; exact hnK⟩
  | a, .fvar n =>
      if hnK : n ∈ K then none
      else if h : n ∈ a.freeVars then none
      else some ⟨[(n, a)],
        .fvarR (by intro he; subst he; exact h (by simp [Ty.freeVars])) h,
        by intro p hp; rw [List.mem_singleton] at hp; subst hp; exact hnK⟩
  | _, _ => none
termination_by ((pairVars a b).length, a.size + b.size)
decreasing_by
  · exact unifyDec_arrow1
  · exact unifyDec_arrow2 hS₁
  · exact unifyDec_customTy
  · exact unifyDec_bl
  · -- bl ~ List
    exact unifyDec_blList
  · exact unifyDec_listBl

def unifyListCoreK (K : List Nat) (as bs : List Ty) :
    Option { S : Subst // UnifyRelList as bs S ∧ (∀ p ∈ S, p.1 ∉ K) } :=
  match as, bs with
  | [], [] => some ⟨[], .nil, by simp⟩
  | t₁ :: ts₁, t₂ :: ts₂ =>
      match unifyCoreK K t₁ t₂ with
      | none => none
      | some ⟨S₁, hS₁, hav₁⟩ =>
        match unifyListCoreK K (ts₁.map S₁.onTy) (ts₂.map S₁.onTy) with
        | none => none
        | some ⟨S₂, hS₂, hav₂⟩ => some ⟨S₁ ++ S₂, .cons hS₁ hS₂, by
            intro p hp; rcases List.mem_append.mp hp with hp | hp
            · exact hav₁ p hp
            · exact hav₂ p hp⟩
  | _, _ => none
termination_by ((listVars as bs).length, TyList.size as + TyList.size bs + 1)
decreasing_by
  · exact unifyDec_cons1
  · exact unifyDec_cons2 hS₁
end

/-- `unifyCore` is the `K = []` instance of the rigidity-aware `unifyCoreK` (no
    variable is off-limits), projected to drop the now-trivial avoids-`[]`
    component of the carried invariant. -/
def unifyCore (a b : Ty) : Option { S : Subst // UnifyRel a b S } :=
  (unifyCoreK [] a b).map (fun r => ⟨r.1, r.2.1⟩)

/-- `unifyListCore` is the `K = []` instance of `unifyListCoreK`. -/
def unifyListCore (as bs : List Ty) : Option { S : Subst // UnifyRelList as bs S } :=
  (unifyListCoreK [] as bs).map (fun r => ⟨r.1, r.2.1⟩)

/-- The executable unifier, refining `UnifyRel`. -/
def unify (a b : Ty) : Option Subst := (unifyCore a b).map (·.1)

/-- `unify` soundness: a returned substitution is a genuine `UnifyRel` unifier
    (immediate — `unifyCore` carries the derivation). -/
theorem unify_sound {a b : Ty} {S : Subst} (h : unify a b = some S) : UnifyRel a b S := by
  rw [unify] at h
  rcases hc : unifyCore a b with _ | ⟨S', hS'⟩ <;> rw [hc] at h
  · exact absurd h (by simp)
  · simp only [Option.map_some, Option.some.injEq] at h
    subst h
    exact hS'

/-! ### The decidable `letRec` ceiling check

`Infer.letRec` carries a `RecSpecs.ceilingOK` premise: every annotation must be
generalised *by* the solved scheme. The executable `inferCore` decides it by
ONE-WAY matching: open `σ` at fresh skolems, then unify `τ` against the opened
`σ` with the skolems and every non-pool variable held rigid — so only the
gen-pool variables of `τ` can move. -/

/-- Decidable ceiling check for ONE annotated member: `genGroup G τ` generalises
    `σ` (both erased) iff `τ` matches the skolem-opened `σ`. Folded into the
    check (so the soundness lemma needs no external facts): `τ` is LC, the
    skolems are fresh, `σ`'s free vars are rigid (in `rigid`/`env`), and the
    BOUNDS-ERASED `τ` matches the bounds-erased, skolem-opened `σ` structurally. -/
def ceilingOk (Φ : Nat) (rigid : List Nat) (env : Env) (τ : Ty) (σ : PolyTy) : Bool :=
  let Ys := freshVars Φ σ.paramCount
  let avoid := Ys.all (fun y => !(τ.freeVars ++ env.freeVars ++ rigid ++ σ.body.freeVars).contains y)
  let σrigid := σ.body.freeVars.all (fun y => (rigid ++ env.freeVars).contains y)
  (Ty.bvarsBelow 0 τ) && avoid && σrigid
    && (unifyCoreK (rigid ++ env.freeVars ++ Ys) (Ty.eraseBounds τ) (Ty.eraseBounds (σ.openVars Ys))).isSome

/-- Decidable ceiling check for a whole group: every annotated member's solved
    monotype generalises its annotation. -/
def ceilingOKB (Φ : Nat) (rigid : List Nat) (env : Env)
    (anns : List (Option PolyTy)) (specs : List RecSpec) : Bool :=
  (anns.zip specs).all (fun p => match p.1, p.2 with
    | some σ, .mono τ => ceilingOk Φ rigid env τ σ
    | some σ, .poly _ => false
    | none, _ => true)

/-- Membership in the group gen-pool: the free vars of the member types that are
    neither env-fixed nor rigid. -/
lemma mem_genGroupVars {rigid : List Nat} {env : Env} {τs : List Ty} {x : Nat} :
    x ∈ genGroupVars rigid env τs ↔ x ∈ Ty.freeVarsList τs ∧ x ∉ env.freeVars ∧ x ∉ rigid := by
  simp [genGroupVars, List.mem_filter]

/-- A member-type free var excluded from the group pool is rigid or env-fixed. -/
lemma not_mem_genGroupVars {rigid : List Nat} {env : Env} {τs : List Ty} {x : Nat}
    (hx : x ∈ Ty.freeVarsList τs) (hxG : x ∉ genGroupVars rigid env τs) :
    x ∈ rigid ∨ x ∈ env.freeVars := by
  by_cases h1 : x ∈ env.freeVars
  · exact Or.inr h1
  · by_cases h2 : x ∈ rigid
    · exact Or.inl h2
    · exfalso
      exact hxG ((mem_genGroupVars).mpr ⟨hx, h1, h2⟩)

/-- The general-pool form of `ceilingOk_sound`: the pool `G` need only cover the
    non-rigid free vars of `τ` (`hG`). The unifier is bounds-blind (it works on
    erased types), so the generalising scheme is the erased `genGroup G τ`; the
    witness uses the erased unifier `S` (its images re-erased), which avoids the
    rigid names and the skolems and hence fixes the annotation's opening. -/
private theorem ceilingOk_sound_gen {Φ : Nat} {rigid : List Nat} {env : Env} {τ : Ty} {σ : PolyTy}
    {G : List Nat}
    (hG : ∀ z ∈ τ.freeVars, z ∉ G → z ∈ rigid ∨ z ∈ env.freeVars)
    (hσwf : σ.WF)
    (h : ceilingOk Φ rigid env τ σ = true) :
    PolyTy.Generalizes (PolyTy.eraseBounds (PolyTy.genGroup G τ)) (PolyTy.eraseBounds σ) := by
  set Ys := freshVars Φ σ.paramCount
  unfold ceilingOk at h
  dsimp at h
  rw [Bool.and_eq_true] at h
  obtain ⟨hτbl, hunif⟩ := h
  rw [Bool.and_eq_true] at hτbl
  obtain ⟨hτbl', hσrigidb⟩ := hτbl
  rw [Bool.and_eq_true] at hτbl'
  obtain ⟨hτbl, havoidb⟩ := hτbl'
  have hτlc : τ.IsLC := (Ty.bvarsBelow_iff τ).mp hτbl
  have havoid : ∀ y ∈ Ys, y ∉ (τ.freeVars ++ env.freeVars ++ rigid ++ σ.body.freeVars) := by
    intro y hy
    intro hc
    have hb := (List.all_eq_true.mp havoidb) y hy
    have hbf : (τ.freeVars ++ env.freeVars ++ rigid ++ σ.body.freeVars).contains y = false := by
      simpa [Bool.not_eq_true] using hb
    have hb' : (τ.freeVars ++ env.freeVars ++ rigid ++ σ.body.freeVars).contains y = true := by
      simpa [List.contains_eq_mem] using hc
    rw [hb'] at hbf
    contradiction
  have hYσ : ∀ y ∈ Ys, y ∉ σ.body.freeVars := fun y hy hc =>
    havoid y hy (by simp [List.mem_append]; exact Or.inr (Or.inr (Or.inr hc)))
  have hYenv : ∀ y ∈ Ys, y ∉ env.freeVars := fun y hy hc =>
    havoid y hy (by simp [List.mem_append]; exact Or.inr (Or.inl hc))
  have hYrigid : ∀ y ∈ Ys, y ∉ rigid := fun y hy hc =>
    havoid y hy (by simp [List.mem_append]; exact Or.inr (Or.inr (Or.inl hc)))
  have hσrigid' : ∀ y ∈ σ.body.freeVars, y ∈ rigid ++ env.freeVars := by
    intro y hy
    simpa [List.contains_eq_mem] using (List.all_eq_true.mp hσrigidb) y hy
  have hunif' : ∃ S, UnifyRel (Ty.eraseBounds τ) (Ty.eraseBounds (σ.openVars Ys)) S ∧
      (∀ p ∈ S, p.1 ∉ rigid ++ env.freeVars ++ Ys) := by
    rw [Option.isSome_iff_exists] at hunif
    rcases hunif with ⟨u, hu⟩
    cases u with
    | mk S hS =>
      exact ⟨S, hS.1, hS.2⟩
  obtain ⟨S, hS, havS⟩ := hunif'
  have hτelc : (Ty.eraseBounds τ).IsLC := Ty.IsLC.eraseBounds hτlc
  have hσopen_lc : (σ.openVars Ys).IsLC := PolyTy.openVars_isLC hσwf (by simp [Ys])
  have hS_lc : ∀ p ∈ S, p.2.IsLC := UnifyRel.lc hS hτelc (Ty.IsLC.eraseBounds hσopen_lc)
  have hSfix : S.onTy (Ty.eraseBounds (σ.openVars Ys)) = Ty.eraseBounds (σ.openVars Ys) := by
    show Ty.substFvars S (Ty.eraseBounds (σ.openVars Ys)) = Ty.eraseBounds (σ.openVars Ys)
    rw [Ty.substFvars_eq_self_of_no_key]
    intro p hp hz
    have hz' : p.1 ∈ (σ.openVars Ys).freeVars := (Ty.mem_freeVars_eraseBounds (σ.openVars Ys) p.1).mp hz
    rcases Ty.freeVars_openVars_subset p.1 hz' with h1 | h1
    · exact havS p hp (List.mem_append_left Ys (hσrigid' p.1 h1))
    · exact havS p hp (List.mem_append_right (rigid ++ env.freeVars) h1)
  have heq : Ty.eraseBounds (S.onTy (Ty.eraseBounds τ)) = Ty.eraseBounds (S.onTy (Ty.eraseBounds (σ.openVars Ys))) :=
    UnifyRel.unifies hS
  have heq' : Ty.eraseBounds (S.onTy (Ty.eraseBounds τ)) = Ty.eraseBounds (σ.openVars Ys) := by
    calc Ty.eraseBounds (S.onTy (Ty.eraseBounds τ))
        = Ty.eraseBounds (S.onTy (Ty.eraseBounds (σ.openVars Ys))) := heq
      _ = Ty.eraseBounds (Ty.eraseBounds (σ.openVars Ys)) := by rw [hSfix]
      _ = Ty.eraseBounds (σ.openVars Ys) := Ty.eraseBounds_idem (σ.openVars Ys)
  let S' : Subst := S.map (fun p => (p.1, Ty.eraseBounds p.2))
  have hS'τe : S'.onTy (Ty.eraseBounds τ) = Ty.eraseBounds (S.onTy (Ty.eraseBounds τ)) := by
    show Ty.substFvars (S.map (fun p => (p.1, Ty.eraseBounds p.2))) (Ty.eraseBounds τ)
      = Ty.eraseBounds (Ty.substFvars S (Ty.eraseBounds τ))
    rw [Ty.eraseBounds_substFvars, Ty.eraseBounds_idem]
  have htyr : Ty.openVars Ys (Ty.eraseBounds σ.body) = S'.onTy (Ty.eraseBounds τ) := by
    rw [hS'τe, heq', PolyTy.eraseBounds_openVars]
    rfl
  have hS'lc : ∀ p ∈ S', p.2.IsLC := by
    intro p hp
    rcases (by simpa [S'] using hp) with ⟨z, u, hz, hu⟩
    rw [← hu]
    exact Ty.IsLC.eraseBounds (hS_lc (z, u) hz)
  have hS'K : ∀ p ∈ S', p.1 ∉ rigid ++ env.freeVars ++ Ys := by
    intro p hp
    rcases (by simpa [S'] using hp) with ⟨z, u, hz, hu⟩
    rw [← hu]
    exact havS (z, u) hz
  let g := Ty.genFilter G (Ty.eraseBounds τ)
  have hS'fixg : S'.onTy (Ty.closeOver g (Ty.eraseBounds τ)) = Ty.closeOver g (Ty.eraseBounds τ) := by
    show Ty.substFvars S' (Ty.closeOver g (Ty.eraseBounds τ)) = Ty.closeOver g (Ty.eraseBounds τ)
    rw [Ty.substFvars_eq_self_of_no_key]
    intro p hp hz
    have hzτ : p.1 ∈ (Ty.eraseBounds τ).freeVars := Ty.freeVars_closeOver_subset hz
    have hzτ' : p.1 ∈ τ.freeVars := (Ty.mem_freeVars_eraseBounds τ p.1).mp hzτ
    have hzG : p.1 ∉ G := by
      intro hG'
      have hmem : p.1 ∈ g := by
        exact List.mem_filter.mpr ⟨hG', by simpa using hzτ⟩
      exact Ty.not_mem_closeOver_freeVars hmem hz
    rcases hG p.1 hzτ' hzG with h1 | h1
    · exact hS'K p hp (List.mem_append_left Ys (List.mem_append_left env.freeVars h1))
    · exact hS'K p hp (List.mem_append_left Ys (List.mem_append_right rigid h1))
  have hXM'' : ∀ y ∈ Ys, y ∉ (S'.onPolyTy ⟨g.length, Ty.closeOver g (Ty.eraseBounds τ)⟩).body.freeVars := by
    intro y hy
    change y ∉ (S'.onTy (Ty.closeOver g (Ty.eraseBounds τ))).freeVars
    rw [hS'fixg]
    intro hc
    have hyτ : y ∈ τ.freeVars := (Ty.mem_freeVars_eraseBounds τ y).mp (Ty.freeVars_closeOver_subset hc)
    exact havoid y hy (by simp [List.mem_append]; exact Or.inl hyτ)
  have hMwf : (PolyTy.eraseBounds σ).WF := PolyTy.WF.eraseBounds hσwf
  have hYsnodup : Ys.Nodup := by
    simpa [Ys] using freshVars_nodup
  have hYslen : Ys.length = (PolyTy.eraseBounds σ).paramCount := by
    simp [Ys]
  have hYsmbody : ∀ x ∈ Ys, x ∉ (PolyTy.eraseBounds σ).body.freeVars := by
    intro y hy
    intro hc
    exact hYσ y hy ((Ty.mem_freeVars_eraseBounds σ.body y).mp hc)
  have hres := closeOver_generalizes (g := g) (τ₁ := Ty.eraseBounds τ) (R := S') (M := PolyTy.eraseBounds σ) (Xs := Ys)
    hτelc hS'lc hMwf hYsnodup hYslen hYsmbody htyr hXM''
  have hM'eq : S'.onPolyTy ⟨g.length, Ty.closeOver g (Ty.eraseBounds τ)⟩
      = PolyTy.eraseBounds (PolyTy.genGroup G τ) := by
    change ⟨g.length, S'.onTy (Ty.closeOver g (Ty.eraseBounds τ))⟩
      = PolyTy.eraseBounds (PolyTy.genGroup G τ)
    rw [hS'fixg]
    rw [PolyTy.eraseBounds_genGroup]
    rfl
  rw [hM'eq] at hres
  exact hres

/-- `ceilingOk` is sound: success means the solved scheme (generalised over the
    single-member pool), erased, generalises the erased annotation. The unifier is
    bounds-blind (identifies `bl lo hi α` with `List α`), so everything happens on
    erased types; `σ`'s free vars are rigid by the check, so the generalising
    scheme is the erased `genGroup` over `τ`'s non-rigid free vars. -/
theorem ceilingOk_sound {Φ : Nat} {rigid : List Nat} {env : Env} {τ : Ty} {σ : PolyTy}
    (hσwf : σ.WF)
    (h : ceilingOk Φ rigid env τ σ = true) :
    PolyTy.Generalizes
      (PolyTy.eraseBounds (PolyTy.genGroup (genGroupVars rigid env [τ]) τ))
      (PolyTy.eraseBounds σ) := by
  refine ceilingOk_sound_gen (G := genGroupVars rigid env [τ]) ?_ hσwf h
  intro z hz hzG
  exact not_mem_genGroupVars (Ty.mem_freeVarsList_of_mem (hτ := by simp) hz) hzG

/-- `ceilingOKB` is sound: success means the group's ceiling premise
    (`RecSpecs.ceilingOK`) holds for the shared pool. The length hypothesis is
    load-bearing: `ceilingOKB` zips `anns`/`specs` (which truncates), while
    `RecSpecs.ceilingOK` is `List.Forall₂` (which requires equal lengths). -/
theorem ceilingOKB_sound {Φ : Nat} {rigid : List Nat} {env : Env}
    {anns : List (Option PolyTy)} {specs : List RecSpec}
    (hLen : specs.length = anns.length)
    (hannsWF : ∀ σ, some σ ∈ anns → σ.WF)
    (h : ceilingOKB Φ rigid env anns specs = true) :
    RecSpecs.ceilingOK (genGroupVars rigid env (RecSpecs.monoTys specs)) anns specs := by
  unfold ceilingOKB at h
  unfold RecSpecs.ceilingOK
  refine List.forall₂_of_mem_zip (l₁ := anns) (l₂ := specs) hLen.symm ?_
  intro p hp
  have hpair := (List.all_eq_true.mp h) p hp
  rcases p with ⟨a, s⟩
  cases a with
  | none => simp
  | some σ =>
      cases s with
      | mono τ =>
          have hσwf : σ.WF := hannsWF σ (List.of_mem_zip hp).1
          have hτin : τ ∈ RecSpecs.monoTys specs :=
            RecSpecs.monoTy_mem_monoTys (by simpa using (List.of_mem_zip hp).2)
          refine ceilingOk_sound_gen
            (G := genGroupVars rigid env (RecSpecs.monoTys specs)) ?_ hσwf hpair
          intro z hz hzG
          exact not_mem_genGroupVars (Ty.mem_freeVarsList_of_mem hτin hz) hzG
      | poly σ' =>
          simp at hpair



/-! ### The `infer` function (Algorithm W)

`inferCore`/`inferBranchesCore` mirror `Infer`/`InferBranches` exactly, building
the `Infer` derivation alongside the output (soundness by construction);
recursion is structural on the expression / branch list. The `match_` case reads
the type name + arity off the first branch's constructor (branches are nonempty).
The public `infer` erases the derivation. -/
mutual
def inferCore (K : List Nat) (Φ : Nat) (ctx : Ctx) (e : Expr) :
    Option { r : Nat × Subst × Ty //
      Infer Φ ctx e r.1 r.2.1 r.2.2 ∧ (∀ p ∈ r.2.1, p.1 ∉ K) } :=
  match e with
  | .primLit .unit => some ⟨(Φ, [], .prim .unit), .primLitUnit, by simp⟩
  | .primLit (.int n) => some ⟨(Φ, [], .prim .int), .primLitInt, by simp⟩
  | .primLit (.nat n) => some ⟨(Φ, [], .prim .nat), .primLitNat, by simp⟩
  | .primLit (.char c) => some ⟨(Φ, [], .prim .char), .primLitChar, by simp⟩
  | .primBinOp .intAdd =>
      some ⟨(Φ, [], .arrow (.prim .int) (.arrow (.prim .int) (.prim .int))), .primBinOpIntAdd, by simp⟩
  | .primBinOp .intSub =>
      some ⟨(Φ, [], .arrow (.prim .int) (.arrow (.prim .int) (.prim .int))), .primBinOpIntSub, by simp⟩
  | .primBinOp .intLt =>
      match hT : LookupList.get? ctx.ctors ⟨"True"⟩ with
      | none => none
      | some tc =>
        match hF : LookupList.get? ctx.ctors ⟨"False"⟩ with
        | none => none
        | some fc =>
          if htc : tc.isBoolCtor = true then
            if hfc : fc.isBoolCtor = true then
              some ⟨(Φ, [], .arrow (.prim .int) (.arrow (.prim .int) (.customTy ⟨"Bool"⟩ []))),
                    .primBinOpIntLt hT (Ctor.isBoolCtor_iff.mp htc) hF (Ctor.isBoolCtor_iff.mp hfc), by simp⟩
            else none
          else none
  | .primBinOp .charLt =>
      match hT : LookupList.get? ctx.ctors ⟨"True"⟩ with
      | none => none
      | some tc =>
        match hF : LookupList.get? ctx.ctors ⟨"False"⟩ with
        | none => none
        | some fc =>
          if htc : tc.isBoolCtor = true then
            if hfc : fc.isBoolCtor = true then
              some ⟨(Φ, [], .arrow (.prim .char) (.arrow (.prim .char) (.customTy ⟨"Bool"⟩ []))),
                    .primBinOpCharLt hT (Ctor.isBoolCtor_iff.mp htc) hF (Ctor.isBoolCtor_iff.mp hfc), by simp⟩
            else none
          else none
  | .lambda none body =>
      match inferCore K (Φ + 1) { ctx with env := PolyTy.mkTrivial (.fvar Φ) :: ctx.env } body with
      | none => none
      | some ⟨(Φ', S, τb), hbody, hav⟩ =>
        some ⟨(Φ', S, .arrow (S.onTy (.fvar Φ)) τb), .lambda .none hbody, hav⟩
  | .lambda (some T) body =>
      if hT : Ty.bvarsBelow 0 T = true then
        match inferCore K Φ { ctx with env := PolyTy.mkTrivial T :: ctx.env } body with
        | none => none
        | some ⟨(Φ', S, τb), hbody, hav⟩ =>
          some ⟨(Φ', S, .arrow (S.onTy T) τb),
            .lambda (.some T ((Ty.bvarsBelow_iff T).mp hT)) hbody, hav⟩
      else none
  | .app f arg =>
      match inferCore K Φ ctx f with
      | none => none
      | some ⟨(Φ₁, S₁, τf), hf, hav₁⟩ =>
        match inferCore K Φ₁ (S₁.onCtx ctx) arg with
        | none => none
        | some ⟨(Φ₂, S₂, τa), harg, hav₂⟩ =>
          match unifyCoreK K (S₂.onTy τf) (.arrow τa (.fvar Φ₂)) with
          | none => none
          | some ⟨S₃, h₃, hav₃⟩ =>
            some ⟨(Φ₂ + 1, S₁ ++ S₂ ++ S₃, S₃.onTy (.fvar Φ₂)), .app hf harg h₃, by
              intro p hp; rcases List.mem_append.mp hp with h | h
              · rcases List.mem_append.mp h with h | h
                · exact hav₁ p h
                · exact hav₂ p h
              · exact hav₃ p h⟩
  | .var i =>
      match h : ctx.env[i]? with
      | none => none
      | some polyTy =>
        some ⟨(Φ + polyTy.paramCount, [], polyTy.openVars (freshVars Φ polyTy.paramCount)), .var h, by simp⟩
  | .ctor name =>
      match h : LookupList.get? ctx.ctors name with
      | none => none
      | some ctorr =>
        some ⟨(Φ + ctorr.paramCount, [], ctorr.toTy.openVars (freshVars Φ ctorr.paramCount)),
          .ctor h, by simp⟩
  | .letIn ann rhs body =>
      match ann with
      | none =>
        match inferCore K Φ ctx rhs with
        | none => none
        | some ⟨(Φ₁, S₁, τ₁), hrhs, hav₁⟩ =>
        match inferCore K Φ₁
            { (S₁.onCtx ctx) with
              env := genScheme rhs.tyFreeVars (S₁.onCtx ctx).env τ₁ :: (S₁.onCtx ctx).env }
            body with
        | none => none
        | some ⟨(Φ₂, S₂, τ₂), hbody, hav₂⟩ =>
          some ⟨(Φ₂, S₁ ++ S₂, τ₂),
            .letIn hrhs hbody, by
            intro p hp; rcases List.mem_append.mp hp with h | h
            · exact hav₁ p h
            · exact hav₂ p h⟩
      | some σ =>
        -- Annotated `let`: skolemize `σ` with `Ys = freshVars Φ pc`, infer the
        -- *opened* rhs `rhs.openTyVars Ys` at frontier `Φ + pc` **with `Ys` added to
        -- the rigid set** (so the rigidity-aware `unifyCoreK` keeps the skolems
        -- rigid), unify the result against the skolem opening, escape-check, and
        -- type the body under `σ` at the outer rigid set `K`. `σ` may carry outer
        -- scoped type variables — no closedness requirement.
        if hσwf : Ty.bvarsBelow σ.paramCount σ.body then
          match inferCore (K ++ freshVars Φ σ.paramCount) (Φ + σ.paramCount) ctx
              (rhs.openTyVars (freshVars Φ σ.paramCount)) with
          | none => none
          | some ⟨(Φ₁, S₁, τ₁), hrhs, hav₁⟩ =>
            match unifyCoreK (K ++ freshVars Φ σ.paramCount) τ₁
                (σ.openVars (freshVars Φ σ.paramCount)) with
            | none => none
            | some ⟨Schk, hSchk, havS⟩ =>
              if hesc1 : (∀ y ∈ freshVars Φ σ.paramCount, y ∉ (S₁ ++ Schk).map Prod.fst) then
                if hesc2 : (∀ y ∈ freshVars Φ σ.paramCount,
                    y ∉ (Schk.onCtx (S₁.onCtx ctx)).env.freeVars) then
                  match inferCore K Φ₁
                      { (Schk.onCtx (S₁.onCtx ctx)) with
                        env := σ :: (Schk.onCtx (S₁.onCtx ctx)).env }
                      body with
                  | none => none
                  | some ⟨(Φ₂, S₂, τ₂), hbody, hav₂⟩ =>
                    some ⟨(Φ₂, S₁ ++ Schk ++ S₂, τ₂),
                      .letInAnn (PolyTy.wf_iff_bvarsBelow.mp hσwf) (Nat.le_refl Φ)
                        hrhs hSchk hesc1 hesc2 hbody, by
                      intro p hp; rcases List.mem_append.mp hp with h | h
                      · rcases List.mem_append.mp h with h | h
                        · exact fun hc => hav₁ p h (List.mem_append_left _ hc)
                        · exact fun hc => havS p h (List.mem_append_left _ hc)
                      · exact hav₂ p h⟩
                else none
              else none
        else none
  | .match_ scrut branches =>
      match inferCore K Φ ctx scrut with
      | none => none
      | some ⟨(Φ₁, S₁, τs), hscrut, hav₁⟩ =>
        match hh : branches.head? with
        | none => none
        | some _ =>
          match inferBranchesCore K (Φ₁ + 1) (S₁.onCtx ctx) τs (.fvar Φ₁) branches with
          | none => none
          | some ⟨(Φ₂, S₂), hbranches, hav₂⟩ =>
            some ⟨(Φ₂, S₁ ++ S₂, S₂.onTy (.fvar Φ₁)),
                  .match_ hscrut (by intro hc; rw [hc] at hh; simp at hh) hbranches, by
                  intro p hp; rcases List.mem_append.mp hp with h | h
                  · exact hav₁ p h
                  · exact hav₂ p h⟩
  | .letRec anns bindings body =>
      -- DM monomorphic recursion: decidably check each ANNOTATED scheme is WF,
      -- build `RecSpec.init Φ anns` (a fresh monotype var per member), thread the
      -- mono-only `inferRecGroupCore`, check the CEILING (`ceilingOKB`: each
      -- annotation generalised by its solved scheme), type the body under the
      -- ceiling schemes.
      if hwf : (∀ a ∈ anns, ∀ σ, a = some σ → Ty.bvarsBelow σ.paramCount σ.body = true) then
        match inferRecGroupCore K (Φ + bindings.length)
            { ctx with env := (RecSpec.init Φ anns).map (RecSpec.rhsEntry [] []) ++ ctx.env }
            bindings (RecSpec.init Φ anns) with
        | none => none
        | some ⟨(Φ₁, S₁), hgroup, hav₁⟩ =>
          let solvedSpecs := (RecSpec.init Φ anns).map (RecSpec.onSubst S₁)
          let G := genGroupVars (RecGroup.rigidVars anns bindings) (S₁.onCtx ctx).env
                     (RecSpecs.monoTys solvedSpecs)
          if hceiling : ceilingOKB Φ₁ (RecGroup.rigidVars anns bindings) (S₁.onCtx ctx).env
              anns solvedSpecs = true then
            match inferCore K Φ₁
                { (S₁.onCtx ctx) with
                  env := RecSpecs.ceilingSchemes G anns solvedSpecs ++ (S₁.onCtx ctx).env }
                body with
            | none => none
            | some ⟨(Φ₂, S₂, τ₂), hbody, hav₂⟩ =>
              some ⟨(Φ₂, S₁ ++ S₂, τ₂),
                .letRec (fun σ hσ => PolyTy.wf_iff_bvarsBelow.mp (hwf (some σ) hσ σ rfl))
                  hgroup
                  (ceilingOKB_sound
                    (by simp [List.length_map, RecSpec.init_length])
                    (fun σ hσ => PolyTy.wf_iff_bvarsBelow.mp (hwf (some σ) hσ σ rfl)) hceiling)
                  hbody, by
                intro p hp; rcases List.mem_append.mp hp with h | h
                · exact hav₁ p h
                · exact hav₂ p h⟩
          else none
      else none
termination_by e.size
decreasing_by
  all_goals (try simp only [Expr.size, Expr.size_openTyVars]; omega)

def inferBranchesCore (K : List Nat) (Φ : Nat) (ctx : Ctx) (scrutTy : Ty) (ρ : Ty)
    (branches : List (MatchPattern × Expr)) :
    Option { r : Nat × Subst //
      InferBranches Φ ctx scrutTy ρ branches r.1 r.2 ∧ (∀ p ∈ r.2, p.1 ∉ K) } :=
  match branches with
  | [] => some ⟨(Φ, []), .nil, by simp⟩
  | (.wildcard, body) :: rest =>
      match inferCore K Φ ctx body with
      | none => none
      | some ⟨(Φ₁, S₁, τb), hbody, hav₁⟩ =>
        match unifyCoreK K τb (S₁.onTy ρ) with
        | none => none
        | some ⟨S₂, huni, hav₂⟩ =>
          match inferBranchesCore K Φ₁ (S₂.onCtx (S₁.onCtx ctx))
              (S₂.onTy (S₁.onTy scrutTy)) (S₂.onTy (S₁.onTy ρ)) rest with
          | none => none
          | some ⟨(Φ₂, S₃), hrest, hav₃⟩ =>
            some ⟨(Φ₂, S₁ ++ S₂ ++ S₃),
                .consWild hbody huni hrest, by
              intro p hp; rcases List.mem_append.mp hp with h | h
              · rcases List.mem_append.mp h with h | h
                · exact hav₁ p h
                · exact hav₂ p h
              · exact hav₃ p h⟩
  | (.named c n, body) :: rest =>
      match hget : LookupList.get? ctx.ctors c with
      | none => none
      | some ctorr =>
        if hcont : n = ctorr.contents.length then
          match unifyCoreK K scrutTy
              (.customTy ctorr.tyName ((freshVars Φ ctorr.paramCount).map (Ty.fvar ·))) with
          | none => none
          | some ⟨S₀, huni0, hav0⟩ =>
            match inferCore K (Φ + ctorr.paramCount)
                { (S₀.onCtx ctx) with
                  env := (ctorr.contents.map (Ty.openWith
                      (((freshVars Φ ctorr.paramCount).map (Ty.fvar ·)).map S₀.onTy))).map PolyTy.mkTrivial
                    ++ (S₀.onCtx ctx).env }
                body with
            | none => none
            | some ⟨(Φ₁, S₁, τb), hbody, hav₁⟩ =>
              match unifyCoreK K τb (S₁.onTy (S₀.onTy ρ)) with
              | none => none
              | some ⟨S₂, huni, hav₂⟩ =>
                match inferBranchesCore K Φ₁ (S₂.onCtx (S₁.onCtx (S₀.onCtx ctx)))
                    (S₂.onTy (S₁.onTy (S₀.onTy scrutTy))) (S₂.onTy (S₁.onTy (S₀.onTy ρ))) rest with
                | none => none
                | some ⟨(Φ₂, S₃), hrest, hav₃⟩ =>
                  some ⟨(Φ₂, S₀ ++ S₁ ++ S₂ ++ S₃),
                      .cons hget hcont huni0 hbody huni hrest, by
                    intro p hp
                    rcases List.mem_append.mp hp with h | h
                    · rcases List.mem_append.mp h with h | h
                      · rcases List.mem_append.mp h with h | h
                        · exact hav0 p h
                        · exact hav₁ p h
                      · exact hav₂ p h
                    · exact hav₃ p h⟩
        else none
termination_by Expr.sizeBranches branches
decreasing_by
  all_goals (try simp only [Expr.sizeBranches]; omega)

/-- Thread check-and-elaborate through a recursion group (DM monomorphic
    recursion): each member is `mono τ`, inferred and unified against `S₁.onTy τ`,
    threading the remaining specs via `RecSpec.onSubst`. (`RecSpec.init` emits only
    `.mono`; a `.poly` spec here is unreachable and falls through to `none`.) -/
def inferRecGroupCore (K : List Nat) (Φ : Nat) (ctx : Ctx) (bindings : List Expr) (specs : List RecSpec) :
    Option { r : Nat × Subst //
      InferRecGroup Φ ctx bindings specs r.1 r.2 ∧ (∀ p ∈ r.2, p.1 ∉ K) } :=
  match bindings, specs with
  | [], [] => some ⟨(Φ, []), .nil, by simp⟩
  | e :: rest, .mono τ :: specs' =>
      match inferCore K Φ ctx e with
      | none => none
      | some ⟨(Φ₁, S₁, τ'), he, hav₁⟩ =>
        match unifyCoreK K τ' (S₁.onTy τ) with
        | none => none
        | some ⟨S₂, huni, hav₂⟩ =>
          match inferRecGroupCore K Φ₁ (S₂.onCtx (S₁.onCtx ctx)) rest
              (specs'.map (RecSpec.onSubst (S₁ ++ S₂))) with
          | none => none
          | some ⟨(Φ₂, S₃), hrest, hav₃⟩ =>
            some ⟨(Φ₂, S₁ ++ S₂ ++ S₃), .consMono he huni hrest, by
              intro p hp; rcases List.mem_append.mp hp with h | h
              · rcases List.mem_append.mp h with h | h
                · exact hav₁ p h
                · exact hav₂ p h
              · exact hav₃ p h⟩
  | _, _ => none
termination_by Expr.sizeRecGroup bindings
decreasing_by
  all_goals (try simp only [Expr.sizeRecGroup, Expr.size_openTyVars]; omega)
end

/-- The executable type inferer, refining `Infer`. Runs from the empty rigid set
    (top-level programs have no in-scope scoped type variables); annotated `let`s
    extend it internally with their skolem block. -/
def infer (Φ : Nat) (ctx : Ctx) (e : Expr) : Option (Nat × Subst × Ty) :=
  (inferCore [] Φ ctx e).map (·.1)

/-- Lightweight `Repr` for the elaborated output term, so the `#eval` sanity
    checks (which now print a 4-tuple including `eOut`) elaborate. -/
instance : Repr Expr := ⟨fun _ _ => Std.Format.text "‹elaborated-term›"⟩

/-- `infer` soundness: a returned `(Φ', S, τ)` is a genuine `Infer` derivation
    (immediate — `inferCore` carries it). -/
theorem infer_sound {Φ : Nat} {ctx : Ctx} {e : Expr} {Φ' : Nat} {S : Subst} {τ : Ty}
    (h : infer Φ ctx e = some (Φ', S, τ)) : Infer Φ ctx e Φ' S τ := by
  rw [infer] at h
  rcases hc : inferCore [] Φ ctx e with _ | ⟨r, hr⟩ <;> rw [hc] at h
  · exact absurd h (by simp)
  · simp only [Option.map_some, Option.some.injEq] at h
    subst h
    exact hr.1

/-! ### Sanity checks: the algorithm actually runs

The first time the algorithm is executed (guards against an operationally-wrong
but provable relation). `unify` and `infer` reduce only under the compiler
(`#eval`), since both rest on well-founded recursion. -/

-- `unify (α → α) (Int → β) = [α ↦ Int, β ↦ Int]`

-- Bounds-blind unify: different BL endpoints; BL ~ bare List
#guard (unify (.bl (.solid (.lit 0)) (.solid (.lit 0)) (.prim .int))
              (.bl (.solid (.lit 1)) (.solid (.lit 1)) (.prim .int))).isSome
#guard (unify (.bl (.solid (.lit 0)) (.solid (.lit 2)) (.prim .int))
              (bareListTy (.prim .int))).isSome

-- #eval unify (.arrow (.fvar 0) (.fvar 0)) (.arrow (.prim .int) (.fvar 1))
-- `unify Int String = none` (constructor clash)
-- #eval unify (.prim .int) (.prim .char)
-- `unify α (α → α) = none` (occurs check)
-- #eval unify (.fvar 0) (.arrow (.fvar 0) (.fvar 0))
-- `infer (λx. x) = α → α`
-- #eval infer 0 { env := [], ctors := [] } (.lambda none (.var 0))
-- `infer (λx. λy. x) = α → β → α`
-- #eval infer 0 { env := [], ctors := [] } (.lambda none (.lambda none (.var 1)))
-- `infer ((λx. x) 5) = Int`
-- #eval infer 0 { env := [], ctors := [] } (.app (.lambda none (.var 0)) (.primLit (.int 5)))
-- `infer (5 5) = none` (Int is not a function)
-- #eval infer 0 { env := [], ctors := [] } (.app (.primLit (.int 5)) (.primLit (.int 5)))


theorem CtxWF.empty {ctors : CtorEnv} : CtxWF ⟨[], ctors⟩ := by
  intro M hM; simp at hM

theorem CtxBelow.empty {Φ : Nat} {ctors : CtorEnv} : CtxBelow Φ ⟨[], ctors⟩ := by
  intro M hM; simp at hM

@[simp] theorem Subst.onCtx_empty {S : Subst} {ctors : CtorEnv} :
    S.onCtx ⟨[], ctors⟩ = ⟨[], ctors⟩ := rfl

/-- A type with no free vars at all (`NoFreeVars`) is exactly one whose `freeVars`
    list is uninhabited (the converse of `NoFreeVars.not_mem_freeVars`). -/
theorem NoFreeVars.of_forall_not_mem {τ : Ty} (h : ∀ Z, Z ∉ τ.freeVars) :
    NoFreeVars τ := by
  induction τ using Ty.rec_strong with
  | prim p => exact .prim
  | bvar i => exact .bvar
  | fvar n => exact absurd (by simp [Ty.freeVars]) (h n)
  | arrow a b iha ihb =>
      refine .arrow (iha ?_) (ihb ?_)
      · intro Z hZ; exact h Z (List.mem_dedup.mpr (List.mem_append.mpr (Or.inl hZ)))
      · intro Z hZ; exact h Z (List.mem_dedup.mpr (List.mem_append.mpr (Or.inr hZ)))
  | customTy nm tys ih =>
      refine .customTy fun t ht => ih t ht ?_
      intro Z hZ; exact h Z (mem_TyList_freeVars.mpr ⟨t, ht, hZ⟩)
  | bl lo hi e ih =>
    refine .bl (ih fun z hz => ?_)
    exact h z (by simpa only [Ty.freeVars] using hz)

/-- A strict upper bound for a list of `fvar` indices: every member is `< this`. -/
def tyVarCeil : List Nat → Nat
  | [] => 0
  | x :: xs => max (x + 1) (tyVarCeil xs)

theorem lt_tyVarCeil {y : Nat} {L : List Nat} (h : y ∈ L) : y < tyVarCeil L := by
  induction L with
  | nil => simp at h
  | cons x xs ih =>
    rcases List.mem_cons.mp h with rfl | h
    · exact Nat.lt_of_lt_of_le (Nat.lt_succ_self _) (Nat.le_max_left _ _)
    · exact Nat.lt_of_lt_of_le (ih h) (Nat.le_max_right _ _)

/-- The fresh-variable floor for `e`: a frontier strictly above every free type
    variable occurring in `e`'s annotations. Inference is started here (rather
    than at `0`) so those in-scope type variables are never re-minted as fresh,
    and — paired with the rigid set `K := e.tyFreeVars` — they stay *rigid*
    (the rigidity-aware `unifyCoreK` refuses to bind them). -/
def Expr.freshFloor (e : Expr) : Nat := tyVarCeil e.tyFreeVars

theorem Expr.lt_freshFloor {e : Expr} {y : Nat} (h : y ∈ e.tyFreeVars) :
    y < e.freshFloor := lt_tyVarCeil h

/-- The principal *monotype* of a program: run Algorithm W from the empty
    environment, keeping just the resulting type (the inferer's `Φ`/`S` are
    internal). `typecheck` generalizes this into a closed scheme.

    Inference seeds the rigid set with `e.tyFreeVars` and the frontier with
    `e.freshFloor`, so any free type variable appearing in a top-level annotation
    is treated as a **rigid scoped constant** (it is never bound by unification).
    For a *closed* program this is exactly `inferCore [] 0 …`. -/
def principalType (ctors : CtorEnv) (e : Expr) : Option Ty :=
  (inferCore e.tyFreeVars e.freshFloor ⟨[], ctors⟩ e).map (·.val.2.2)

/-- Monotype soundness (erasure-on-`Step`): a computed principal type types the
    **erased** term (`e.erase`) in the erased ctor env (`ctors.eraseBounds`).
    Holds for *any* `e`: free top-level annotation variables stay rigid
    (`K := e.tyFreeVars`). Glued by `Infer.sound` at `K := e.tyFreeVars` — the
    `Infer.eliminates` locality shows `S.onTy τ = τ`. -/
theorem principalType_sound {ctors : CtorEnv} {e : Expr} {τ : Ty}
    (h : principalType ctors e = some τ) :
    TypeOfHM ⟨[], ctors.eraseBounds⟩ e.erase (Ty.eraseBounds τ) := by
  rw [principalType] at h
  rcases hc : inferCore e.tyFreeVars e.freshFloor ⟨[], ctors⟩ e with _ | ⟨⟨Φ', S, τ'⟩, hInfer, hSK⟩ <;>
    rw [hc] at h
  · simp at h
  · simp only [Option.map_some, Option.some.injEq] at h
    subst h
    have helim := Infer.eliminates hInfer CtxBelow.empty
      (fun y hy => Expr.lt_freshFloor hy)
      (fun p hp => hSK p hp)
    have hSτ : S.onTy _ = _ :=
      Ty.substFvars_eq_self_of_no_key (fun p hp => helim.2 p hp)
    simpa [Subst.onCtx, Subst.onEnv, Ctx.eraseBounds, Env.eraseBounds, hSτ] using
      Infer.sound hInfer CtxWF.empty CtxBelow.empty
        e.tyFreeVars (fun k hk => Expr.lt_freshFloor hk) (fun y hy => hy) hSK

/-- **Type-check a closed program** — the intended entry point. Run Algorithm W
    from the empty environment and *generalize* the result into a closed type
    scheme. At an empty environment every remaining free type variable is
    generalizable, so the output is always a genuine closed scheme. -/
def typecheck (ctors : CtorEnv) (e : Expr) : Option PolyTy :=
  (principalType ctors e).map (genScheme [] [])

/-- **`typecheck`'s output is a genuine closed type scheme.** Its body contains
    no free type variables (`NoFreeVars`) and no dangling bound variables
    (`PolyTy.WF` — every `bvar` is bound by the scheme's own quantifier). So a
    successful `typecheck` always yields a concrete (possibly polymorphic) type:
    never a leftover unification variable, never a naked bound variable. -/
theorem typecheck_closed {ctors : CtorEnv} {e : Expr} {σ : PolyTy}
    (h : typecheck ctors e = some σ) : NoFreeVars σ.body ∧ σ.WF := by
  rw [typecheck, principalType] at h
  rcases hi : inferCore e.tyFreeVars e.freshFloor ⟨[], ctors⟩ e with _ | ⟨⟨Φ', S, τ⟩, hInfer, hSK⟩ <;>
    rw [hi] at h
  · simp at h
  · simp only [Option.map_some, Option.some.injEq] at h
    subst h
    have hlc : τ.IsLC := (Infer.lc hInfer CtxWF.empty).1
    refine ⟨?_, genScheme_wf hlc⟩
    apply NoFreeVars.of_forall_not_mem
    intro Z hZ
    have hsub : Z ∈ τ.freeVars := Ty.closeOver_freeVars_subset hZ
    have hin : Z ∈ genVars [] [] τ := List.mem_filter.mpr ⟨hsub, rfl⟩
    exact Ty.not_mem_closeOver_freeVars hin hZ

/-- Whole-program soundness (erasure-on-`Step`): successful `typecheck`
    generalizes a pure-HM type of the **erased** program. -/
theorem typecheck_sound {ctors : CtorEnv} {e : Expr} {σ : PolyTy}
    (h : typecheck ctors e = some σ) :
    ∃ τ, TypeOfHM ⟨[], ctors.eraseBounds⟩ e.erase (Ty.eraseBounds τ) ∧
      σ = genScheme [] [] τ := by
  rw [typecheck] at h
  rcases hc : principalType ctors e with _ | τ <;> rw [hc] at h
  · simp at h
  · simp only [Option.map_some, Option.some.injEq] at h
    exact ⟨τ, principalType_sound hc, h.symm⟩

-- (The whole-program progress/preservation theorems and the type-erasure helper
-- lemmas that lived here have been removed: the type-passing Core has no erasure
-- layer, so `eraseTyAnnots`/`IsTyErased`/`erased_type_safety`/`erase_preserves_typing`
-- no longer exist. Whole-program safety is now the literal `TypeOfHM.type_safety`
-- chain in `Core` (no erasure premise).)

-- `typecheck [] (λx. x) = some ⟨1, bvar 0 → bvar 0⟩`  (i.e. the closed scheme `∀a. a → a`)
-- #eval (typecheck [] (.lambda none (.var 0))).map (fun σ => (σ.paramCount, σ.body))
-- `typecheck [] (5 5) = none`
-- #eval (typecheck [] (.app (.primLit (.int 5)) (.primLit (.int 5)))).map (fun σ => (σ.paramCount, σ.body))



-- `infer (λx. x) = α → α`
-- #eval infer 0 { env := [], ctors := [] } (.lambda none (.var 0))
-- `infer (λx. λy. x) = α → β → α`
-- #eval infer 0 { env := [], ctors := [] } (.lambda none (.lambda none (.var 1)))
-- `infer ((λx. x) 5) = Int`
-- #eval infer 0 { env := [], ctors := [] } (.app (.lambda none (.var 0)) (.primLit (.int 5)))
-- annotated param: `infer (λ(x : Int). x) = Int → Int`
-- #eval infer 0 { env := [], ctors := [] } (.lambda (some (.prim .int)) (.var 0))
-- free annotation var `λ(x : α). x` ⇒ `α → α` (α is treated as a scoped/rigid
-- type variable by the rigidity-aware inferer — sound: the result type carries α free)
-- #eval infer 0 { env := [], ctors := [] } (.lambda (some (.fvar 5)) (.var 0))

/-! ### Acceptance tests for annotated `let` (threading design) -/

-- THE WITNESS: `λx. let f : Int = x in f`  ⇒  `Int → Int`
-- (the annotation `f : Int` refines the outer param `x : α` via threading `α := Int`)
-- #eval infer 0 { env := [], ctors := [] }
  -- (.lambda none (.letIn (some ⟨0, .prim .int⟩) (.var 0) (.var 0)))
-- `let f : Int → Int = (λx. x) in f`  ⇒  `Int → Int`  (less general than principal, valid)
-- #eval infer 0 { env := [], ctors := [] }
  -- (.letIn (some ⟨0, .arrow (.prim .int) (.prim .int)⟩) (.lambda none (.var 0)) (.var 0))
-- `let id : ∀a. a → a = (λx. x) in id`  ⇒  `α → α`  (exact principal, valid)
-- #eval infer 0 { env := [], ctors := [] }
  -- (.letIn (some ⟨1, .arrow (.bvar 0) (.bvar 0)⟩) (.lambda none (.var 0)) (.var 0))
-- over-general: `let f : ∀a b. a → b = (λx. x) in f`  ⇒  `none`  (skolem escape ⇒ rejected)
-- #eval infer 0 { env := [], ctors := [] }
  -- (.letIn (some ⟨2, .arrow (.bvar 0) (.bvar 1)⟩) (.lambda none (.var 0)) (.var 0))
-- unannotated `let f = λx. x in f`  ⇒  `α → α`  (full generalization, unchanged)
-- #eval infer 0 { env := [], ctors := [] }
  -- (.letIn none (.lambda none (.var 0)) (.var 0))

/-! ### Rigid top-level type variables (the `principalType`/`typecheck` entry seeds
    `K := e.tyFreeVars`, so an unbound annotation var is a rigid scoped constant). -/

-- open identity `λ(x : α). x`  ⇒  `some (α → α)`  (α kept rigid; this IS declaratively typeable)
-- #eval principalType [] (.lambda (some (.fvar 5)) (.var 0))
-- open misuse `(λ(x : α). x) 5`  ⇒  `none`  (forcing α := Int would bind the rigid var —
-- rejected; declaratively untypeable. `infer`/`inferCore []` used to wrongly return `some Int`.)
-- #eval principalType [] (.app (.lambda (some (.fvar 5)) (.var 0)) (.primLit (.int 5)))
-- closed program: seeding is a no-op (`K = []`, floor `= 0`)  ⇒  `∀a. a → a`
-- #eval (typecheck [] (.lambda none (.var 0))).map (fun σ => (σ.paramCount, σ.body))


/-! ## Audit capstone: the headlines fire on concrete programs

A vacuous theorem (an unsatisfiable premise) cannot be *instantiated* to produce a
positive result, so the most convincing anti-vacuity check is to drive the public
pipeline end-to-end on concrete inputs. Because `inferCore`/`unifyCoreK` use
well-founded recursion (they do not reduce by `rfl`), we witness "`typecheck`
succeeds" by building the *declarative* `TypeOfHM` derivation and crossing the `↔`
headlines — never `decide`/`native_decide`. -/

namespace AuditCapstone

/-! ### A typeable program — all three headlines fire -/

/-- `λx. x`. -/
def polyId : Expr := .lambda none (.var 0)

theorem polyId_typeable : TypeOfHM ⟨[], []⟩ polyId (.arrow (.fvar 0) (.fvar 0)) :=
  TypeOfHM.lambda .fvar (fun _ h => Option.noConfusion h) rfl
    (TypeOfHM.var (instArgs := []) rfl (by intro t ht; cases ht) .fvar)

/-! ### Headline demos keep EXACT principality (`τ₀ = R.onTy τ`)

Unlike the general theorems above, the four `*_headlines_fire` demos are stated
with exact equality and that is **correct, not an oversight**. Their terms carry no
`bl` anywhere, so the computed `τ` is erase-normal *and* all-variable (`polyId` ⇒
`.fvar 0 → .fvar 0`); every `τ₀` agreeing up to erasure is then a genuine
substitution instance, including the `bl`-decorated ones that
`TypeOfHM.var`'s existential `instArgs` makes derivable.

Consequence for the farm: these four do **not** depend on the completeness engine.
Like `appFiveFive_untypeable`, each is a direct inversion of `TypeOfHM` on a
closed, tiny term — `polyId`'s inversion gives `τ₀ = paramTy → paramTy`, so
`R = [(0, paramTy)]`. Prove them standalone and early; do not block them on
`complete'`. -/

/-! #### Shared machinery for the four demos

Two ingredients recur.

* **Computing the principal type.** `inferCore`/`unifyCoreK`/… are well-founded
  recursions, so they do **not** reduce by `rfl`/`decide` (and we deliberately do
  not reach for `native_decide`). Instead we unfold their *equation lemmas* with
  `simp only [inferCore, …]` — which fires because each recursive call sits at a
  syntactically concrete `Expr` — and then discharge the residual pure-`Prop`-free
  arithmetic/matching with `with_unfolding_all rfl`. `unifyCoreK`'s arguments are
  bound by the surrounding `match`es, so its equations cannot fire; one syntactic
  `unfold unifyCoreK` per unification depth exposes the body, after which
  `with_unfolding_all rfl` finishes.

* **Inverting the derivation.** Each demo's principal type is all-variable (plus,
  for `matchWild`, a rigid `Int`), so ordinary `cases` inversion on `TypeOfHM`
  pins `τ₀`'s shape exactly and the witness substitution reads off directly. The
  only supporting lemma needed is that instantiation is trivial on a
  locally-closed body. -/

/-- Instantiation is the identity on a locally-closed type: this is the converse
    of `InstantiatesBy.refl_of_closed`, and it is what turns a `lambda`'s
    `paramTy.IsLC` premise into "the bound variable's use has type `paramTy`". -/
theorem instBy_eq_of_lc {tyArgs : List Ty} :
    ∀ {ty : Ty}, ty.IsLC → ∀ (τ : Ty), InstantiatesBy tyArgs ty τ → τ = ty := by
  intro ty
  induction ty using Ty.rec_strong with
  | prim p => intro _ τ h; cases h; rfl
  | arrow a b iha ihb =>
      intro hlc τ h
      cases hlc with
      | arrow ha hb => cases h with | arrow h1 h2 => rw [iha ha _ h1, ihb hb _ h2]
  | bvar n => intro hlc τ h; cases hlc with | bvar hlt => omega
  | fvar n => intro _ τ h; cases h; rfl
  | customTy nm tys ih =>
      intro hlc τ h
      cases hlc with
      | customTy hall =>
        cases h with
        | customTy hf =>
          refine congrArg _ ?_
          have aux : ∀ (ts is : List Ty), (∀ t ∈ ts, t.IsLC) →
              (∀ t ∈ ts, ∀ u, InstantiatesBy tyArgs t u → u = t) →
              List.Forall₂ (InstantiatesBy tyArgs) ts is → is = ts := by
            intro ts
            induction ts with
            | nil => intro is _ _ hff; cases hff; rfl
            | cons hd tl iht =>
              intro is hall' ih' hff
              cases hff with
              | cons hhd htl =>
                rw [iht _ (fun t ht => hall' t (List.mem_cons_of_mem _ ht))
                      (fun t ht => ih' t (List.mem_cons_of_mem _ ht)) htl,
                    ih' hd (List.mem_cons_self ..) _ hhd]
          exact aux tys _ hall (fun t ht => ih t ht (hall t ht)) hf
  | bl lo hi e ihe =>
      intro hlc τ h
      cases hlc with | bl he => cases h with | bl h1 => rw [ihe he _ h1]

set_option maxRecDepth 100_000 in
/-- `λx. x` has principal monotype `α → α` (computed, not postulated). -/
theorem polyId_principalType : principalType [] polyId = some (.arrow (.fvar 0) (.fvar 0)) := by
  show (inferCore [] 0 ⟨[], []⟩ (Expr.lambda none (Expr.var 0))).map (·.val.2.2) = _
  simp only [inferCore, List.getElem?_cons_zero]
  with_unfolding_all rfl

/-- `polyId` carries no `bl`, so erase-projection is the identity. -/
theorem polyId_eraseBounds : polyId.eraseBounds = polyId := by
  simp [Expr.eraseBounds, polyId]

/-- `typecheck` succeeds, produces a genuine residual declarative type (Path R
    soundness), and that type is principal. -/
theorem polyId_headlines_fire :
    ∃ σ τ, typecheck [] polyId = some σ ∧ σ = genScheme [] [] τ ∧
      TypeOfHM ⟨[], []⟩ polyId.eraseBounds (Ty.eraseBounds τ) ∧
      ∀ τ₀, TypeOfHM ⟨[], []⟩ polyId.eraseBounds τ₀ → ∃ R : Subst, τ₀ = R.onTy τ := by
  refine ⟨genScheme [] [] (.arrow (.fvar 0) (.fvar 0)), .arrow (.fvar 0) (.fvar 0),
    ?_, rfl, ?_, ?_⟩
  · show (principalType [] polyId).map (genScheme [] []) = _
    rw [polyId_principalType]; rfl
  · rw [polyId_eraseBounds]; exact polyId_typeable
  · rw [polyId_eraseBounds]
    intro τ₀ h
    -- Inversion: `λx. x`'s only derivations are `paramTy → paramTy`.
    cases h with
    | lambda hlc hpins heq hbody =>
      subst heq
      cases hbody with
      | var hlook hargs hinst =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hlook
        subst hlook
        have hb := instBy_eq_of_lc hlc _ hinst
        subst hb
        exact ⟨[(0, _)], rfl⟩

/-! ### An ill-typed program — completeness's contrapositive is not vacuous -/

/-- `5 5` — applying a non-function. -/
def appFiveFive : Expr := .app (.primLit (.int 5)) (.primLit (.int 5))

theorem appFiveFive_untypeable : ¬ ∃ τ, TypeOfHM ⟨[], []⟩ appFiveFive.erase τ := by
  rintro ⟨τ, h⟩
  simp [Expr.erase, appFiveFive] at h
  cases h with
  | app hf hx =>
    cases hf

/-- The algorithm rejects `5 5`. Honest route without the deleted completeness
    campaign: if `typecheck` succeeded, `typecheck_sound` would give a declarative
    typing of the erased term — contradicting `appFiveFive_untypeable`. -/
theorem appFiveFive_rejected : ¬ (typecheck [] appFiveFive).isSome := by
  rintro h
  obtain ⟨σ, hσ⟩ := Option.isSome_iff_exists.mp h
  rcases typecheck_sound hσ with ⟨τ, hty, -⟩
  exact appFiveFive_untypeable ⟨Ty.eraseBounds τ, by simpa using hty⟩

/-! ### Open programs — a free top-level annotation var is a RIGID scoped constant
    (the soundness fix this session). -/

/-- `λ(x : α). x`, with `α` free at the top level. -/
def openId : Expr := .lambda (some (.fvar 5)) (.var 0)

/-- Accepted, and sound: `α` is rigid, so the only declarative type is `α → α`. -/
theorem openId_typeable : TypeOfHM ⟨[], []⟩ openId (.arrow (.fvar 5) (.fvar 5)) :=
  TypeOfHM.lambda .fvar (fun _ h => by cases h; rfl) rfl
    (TypeOfHM.var (instArgs := []) rfl (by intro t ht; cases ht) .fvar)

/-- `(λ(x : α). x) 5` — forcing `α := Int` would bind the rigid var. Declaratively
    untypeable (`α` cannot equal `Int`); the rigidity-seeded executable correctly
    returns `none`. Before the fix, `inferCore []` wrongly returned `some Int`. -/
def openMisuse : Expr := .app openId (.primLit (.int 5))

theorem openMisuse_untypeable : ¬ ∃ τ, TypeOfHM ⟨[], []⟩ openMisuse.eraseBounds τ := by
  rintro ⟨τ, h⟩
  simp [Expr.eraseBounds, openMisuse, openId] at h
  cases h with
  | app hf hx =>
    cases hf with
    | lambda hlc hpins heq hbody =>
      have hpin := hpins (.fvar 5) rfl
      rw [hpin] at hx
      cases hx

-- The algorithm rejects `openMisuse` too, but that rejection was a corollary of
-- the deleted completeness campaign (and note the fully *erased* term `(λx. x) 5`
-- IS ordinary well-typed HM, so no soundness-only route recovers it).

/-! ### A polymorphic program — let-generalization + double instantiation -/

/-- `let id : ∀a. a → a = λx. x in id id`. -/
def idid : Expr :=
  .letIn (some ⟨1, .arrow (.bvar 0) (.bvar 0)⟩) (.lambda none (.var 0))
    (.app (.var 0) (.var 0))

theorem idid_typeable : TypeOfHM ⟨[], []⟩ idid (.arrow (.fvar 0) (.fvar 0)) := by
  apply TypeOfHM.letIn (M := ⟨1, .arrow (.bvar 0) (.bvar 0)⟩) (L := [])
  · show ContainsBvarsUpTo 1 (Ty.arrow (Ty.bvar 0) (Ty.bvar 0))
    exact .arrow (.bvar (by omega)) (.bvar (by omega))
  · intro σ' h; cases h; rfl
  · intro Xs hfresh
    have hlen : Xs.length = 1 := hfresh.length
    rcases Xs with _ | ⟨X, _ | ⟨Y, tl⟩⟩
    · simp at hlen
    · have hterm : Expr.openBoundTyVars (some (⟨1, .arrow (.bvar 0) (.bvar 0)⟩ : PolyTy)) [X]
            (.lambda none (.var 0)) = .lambda none (.var 0) := rfl
      have htype : (⟨1, .arrow (.bvar 0) (.bvar 0)⟩ : PolyTy).openVars [X]
            = .arrow (.fvar X) (.fvar X) := rfl
      rw [hterm, htype]
      exact TypeOfHM.lambda .fvar (fun _ h => Option.noConfusion h) rfl
        (TypeOfHM.var (instArgs := []) rfl (by intro t ht; cases ht) .fvar)
    · simp at hlen
  · rfl
  · exact TypeOfHM.app
      (TypeOfHM.var (polyTy := ⟨1, .arrow (.bvar 0) (.bvar 0)⟩)
        (instArgs := [.arrow (.fvar 0) (.fvar 0)]) rfl
        (by intro t ht; simp only [List.mem_singleton] at ht; subst ht; exact .arrow .fvar .fvar)
        (.arrow (.bvar rfl) (.bvar rfl)))
      (TypeOfHM.var (polyTy := ⟨1, .arrow (.bvar 0) (.bvar 0)⟩)
        (instArgs := [.fvar 0]) rfl
        (by intro t ht; simp only [List.mem_singleton] at ht; subst ht; exact .fvar)
        (.arrow (.bvar rfl) (.bvar rfl)))

set_option maxRecDepth 100_000 in
/-- `idid`'s principal monotype. The seeded rigid set is `idid.tyFreeVars = [0,0]`
    and the frontier `idid.freshFloor = 0`, so the residual variable is `3`. -/
theorem idid_principalType : principalType [] idid = some (.arrow (.fvar 3) (.fvar 3)) := by
  simp only [principalType, idid]
  simp only [inferCore, Expr.openTyVars, Expr.openTyVarsAux, freshVars, List.range,
    List.range.loop, List.map, PolyTy.openVars, List.getElem?_cons_zero, Option.map_none]
  unfold unifyCoreK
  unfold unifyCoreK
  with_unfolding_all rfl

theorem idid_eraseBounds : idid.eraseBounds = idid := by
  simp [Expr.eraseBounds, idid, PolyTy.eraseBounds, Ty.eraseBounds]

/-- `idid_typeable` at the computed principal variable `4` (the `var` rule is
    decoration-blind, so the stored `tyArgs` need not match `instArgs`). -/
theorem idid_typeable_fvar3 : TypeOfHM ⟨[], []⟩ idid (.arrow (.fvar 3) (.fvar 3)) := by
  apply TypeOfHM.letIn (M := ⟨1, .arrow (.bvar 0) (.bvar 0)⟩) (L := [])
  · show ContainsBvarsUpTo 1 (Ty.arrow (Ty.bvar 0) (Ty.bvar 0))
    exact .arrow (.bvar (by omega)) (.bvar (by omega))
  · intro σ' h; cases h; rfl
  · intro Xs hfresh
    have hlen : Xs.length = 1 := hfresh.length
    rcases Xs with _ | ⟨X, _ | ⟨Y, tl⟩⟩
    · simp at hlen
    · have hterm : Expr.openBoundTyVars (some (⟨1, .arrow (.bvar 0) (.bvar 0)⟩ : PolyTy)) [X]
            (.lambda none (.var 0)) = .lambda none (.var 0) := rfl
      have htype : (⟨1, .arrow (.bvar 0) (.bvar 0)⟩ : PolyTy).openVars [X]
            = .arrow (.fvar X) (.fvar X) := rfl
      rw [hterm, htype]
      exact TypeOfHM.lambda .fvar (fun _ h => Option.noConfusion h) rfl
        (TypeOfHM.var (instArgs := []) rfl (by intro t ht; cases ht) .fvar)
    · simp at hlen
  · rfl
  · exact TypeOfHM.app
      (TypeOfHM.var (polyTy := ⟨1, .arrow (.bvar 0) (.bvar 0)⟩)
        (instArgs := [.arrow (.fvar 3) (.fvar 3)]) rfl
        (by intro t ht; simp only [List.mem_singleton] at ht; subst ht; exact .arrow .fvar .fvar)
        (.arrow (.bvar rfl) (.bvar rfl)))
      (TypeOfHM.var (polyTy := ⟨1, .arrow (.bvar 0) (.bvar 0)⟩)
        (instArgs := [.fvar 3]) rfl
        (by intro t ht; simp only [List.mem_singleton] at ht; subst ht; exact .fvar)
        (.arrow (.bvar rfl) (.bvar rfl)))

theorem idid_headlines_fire :
    ∃ σ τ, typecheck [] idid = some σ ∧ σ = genScheme [] [] τ ∧
      TypeOfHM ⟨[], []⟩ idid.eraseBounds (Ty.eraseBounds τ) ∧
      ∀ τ₀, TypeOfHM ⟨[], []⟩ idid.eraseBounds τ₀ → ∃ R : Subst, τ₀ = R.onTy τ := by
  refine ⟨genScheme [] [] (.arrow (.fvar 3) (.fvar 3)), .arrow (.fvar 3) (.fvar 3),
    ?_, rfl, ?_, ?_⟩
  · show (principalType [] idid).map (genScheme [] []) = _
    rw [idid_principalType]; rfl
  · rw [idid_eraseBounds]; exact idid_typeable_fvar3
  · rw [idid_eraseBounds]
    intro τ₀ h
    -- Inversion: the annotation pins `M = ∀a. a → a`; the two uses then force
    -- `τ₀ = A → A` where `A` is the argument's own instantiation witness.
    cases h with
    | letIn hwf hpins hgen heq hbody =>
      have hM := hpins _ rfl
      subst hM
      subst heq
      cases hbody with
      | app hf hx =>
        cases hf with
        | var hlook1 hargs1 hinst1 =>
          cases hx with
          | var hlook2 hargs2 hinst2 =>
            simp only [List.getElem?_cons_zero, Option.some.injEq] at hlook1 hlook2
            subst hlook1; subst hlook2
            cases hinst2 with
            | arrow g1 g2 =>
              cases g1 with
              | bvar e1 =>
                cases g2 with
                | bvar e2 =>
                  have hAB : _ = _ := Option.some.inj (e1.symm.trans e2)
                  subst hAB
                  cases hinst1 with
                  | arrow f1 f2 =>
                    cases f1 with
                    | bvar d1 =>
                      cases f2 with
                      | bvar d2 =>
                        have hτ : _ = _ := Option.some.inj (d2.symm.trans d1)
                        subst hτ
                        exact ⟨[(3, _)], rfl⟩

/-! ### Progress / preservation fire on a concrete erased program -/

/-- `(λx. x) 5` — already annotation-free; beta-reduces to `5`. -/
def appIdFive : Expr := .app (.lambda none (.var 0)) (.primLit (.int 5))

theorem appIdFive_typeable : TypeOfHM ⟨[], []⟩ appIdFive (.prim .int) :=
  TypeOfHM.app
    (TypeOfHM.lambda .prim (fun _ h => Option.noConfusion h) rfl
      (TypeOfHM.var (instArgs := []) rfl (by intro t ht; cases ht) .prim))
    TypeOfHM.primLitInt

-- (The progress/preservation capstone examples referenced the now-removed type-erasure
-- layer — `Expr.eraseTyAnnots` / `typecheck_progress` / `typecheck_preservation` no longer
-- exist; whole-program safety is the literal `TypeOfHM.type_safety` chain in `Core`.
-- These two examples are dropped accordingly.)

/-! ### Core v2: an all-wildcard match has a principal type (the match-fix witness) -/

/-- `λx. match x with | _ => 0`. Under Core v1's unconditional-`customTy` match rule
    this had NO principal type (the scrutinee's `customTy` name was unconstrained);
    after the §1 fix the scrutinee type is free, so the principal type is `∀α. α → Int`. -/
def matchWild : Expr := .lambda none (.match_ (.var 0) [(.wildcard, .primLit (.int 0))])

theorem matchWild_typeable : TypeOfHM ⟨[], []⟩ matchWild (.arrow (.fvar 0) (.prim .int)) := by
  refine TypeOfHM.lambda .fvar (fun _ h => Option.noConfusion h) rfl ?_
  refine TypeOfHM.match_ (scrutTy := .fvar 0)
    (TypeOfHM.var (instArgs := []) rfl (by intro t ht; cases ht) .fvar) (by simp) ?_
  intro branch hbr
  rw [List.mem_singleton] at hbr; subst hbr
  exact TypeOfMatchBranch.wildcard TypeOfHM.primLitInt

set_option maxRecDepth 100_000 in
theorem matchWild_principalType :
    principalType [] matchWild = some (.arrow (.fvar 0) (.prim .int)) := by
  show (inferCore [] 0 ⟨[], []⟩
      (Expr.lambda none ((Expr.var 0).match_
        [(MatchPattern.wildcard, Expr.primLit (.int 0))]))).map (·.val.2.2) = _
  simp only [inferCore, inferBranchesCore, List.getElem?_cons_zero]
  unfold unifyCoreK
  with_unfolding_all rfl

theorem matchWild_eraseBounds : matchWild.eraseBounds = matchWild := by
  simp [Expr.eraseBounds, matchWild]

/-- All three headlines fire on the all-wildcard match: it typechecks, the produced
    type is a genuine declarative type (soundness), and it is principal. -/
theorem matchWild_headlines_fire :
    ∃ σ τ, typecheck [] matchWild = some σ ∧ σ = genScheme [] [] τ ∧
      TypeOfHM ⟨[], []⟩ matchWild.eraseBounds (Ty.eraseBounds τ) ∧
      ∀ τ₀, TypeOfHM ⟨[], []⟩ matchWild.eraseBounds τ₀ → ∃ R : Subst, τ₀ = R.onTy τ := by
  refine ⟨genScheme [] [] (.arrow (.fvar 0) (.prim .int)), .arrow (.fvar 0) (.prim .int),
    ?_, rfl, ?_, ?_⟩
  · show (principalType [] matchWild).map (genScheme [] []) = _
    rw [matchWild_principalType]; rfl
  · rw [matchWild_eraseBounds]; exact matchWild_typeable
  · rw [matchWild_eraseBounds]
    intro τ₀ h
    -- Inversion: the wildcard branch imposes nothing on the scrutinee, and its
    -- body is `0`, so the result is `Int` and the parameter stays free.
    cases h with
    | lambda hlc hpins heq hbody =>
      subst heq
      cases hbody with
      | match_ hscrut hne hbr =>
        have hb := hbr (MatchPattern.wildcard, Expr.primLit (.int 0)) (by simp)
        cases hb with
        | wildcard hbody2 =>
          cases hbody2
          exact ⟨[(0, _)], rfl⟩

/-! ### A recursive program — `letRec` typechecks at its principal type

The mutually-recursive group `letRec [f := g; g := f] in f` (`f = g`, `g = f`).
Under the old disjoint-slice `openGroup` rule this group could NOT be given the
polymorphic schemes `[∀a.a, ∀a.a]` (the disjoint opening severed the `f`/`g`
type-sharing — proved unsound vs Damas–Milner for `n > 1`); the shared-monotype
rule does. Its principal type is `∀a. a`. This is the capstone witness that the
recursive-binding inference fires end-to-end at the principal type. -/

/-- `letRec [none, none] [var 1, var 0] (var 0)` — the `f = g; g = f` mutual loop
    (both unannotated) returning `f`. -/
def mutualRec : Expr := .letRec [none, none] [.var 1, .var 0] (.var 0)

/-- The all-`none` mutual group types at its principal monotype under the fused
    `TypeOfHM.letRec`: `specs = [.mono (fvar 100), .mono (fvar 100)]`, witnesses
    `τs = [fvar 100, fvar 100]`, pool `[100]`. Inside the group both members sit
    at the opened shared monotype `fvar X`; the body sees them generalised to
    `∀a. a` and instantiates at `fvar 0`. -/
theorem mutualRec_typeable : TypeOfHM ⟨[], []⟩ mutualRec (.fvar 0) := by
  refine TypeOfHM.letRec (specs := [.mono (.fvar 100), .mono (.fvar 100)])
    (τs := [.fvar 100, .fvar 100]) (G := [100])
    (L := []) ⟨rfl, rfl, by simp, ?_, ?_⟩ rfl ?_ ?_ ?_ rfl ?_
  · -- shared monotypes are LC
    intro τ hτ
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hτ
    rcases hτ with h | h <;> (injection h with h'; rw [h']; exact .fvar)
  · -- no annotated members
    intro σ hσ
    simp only [List.mem_cons, List.not_mem_nil, reduceCtorEq, or_self] at hσ
  · -- mono-link: witnesses are exactly the spec monotypes
    intro p hp τ hτ
    simp only [List.zip_cons_cons, List.zip_nil_right, List.mem_cons, List.not_mem_nil,
      or_false] at hp
    rcases hp with rfl | rfl <;> (injection hτ with h')
  · -- witnesses are LC
    intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with h | h <;> (rw [h]; exact .fvar)
  · -- MonoTypedInit: both members at the opened shared monotype `fvar X`
    intro Xs hfresh p hp
    obtain ⟨X, rfl⟩ : ∃ X, Xs = [X] := List.length_eq_one_iff.mp hfresh.length
    simp only [List.zip_cons_cons, List.zip_nil_right, List.mem_cons, List.not_mem_nil,
      or_false] at hp
    rcases hp with rfl | rfl
    · -- `f = g`: look up `g` at index 1
      show TypeOfHM ⟨[PolyTy.mkTrivial (.fvar X), PolyTy.mkTrivial (.fvar X)], []⟩
        (.var 1) (.fvar X)
      exact TypeOfHM.var (polyTy := PolyTy.mkTrivial (.fvar X)) (instArgs := []) rfl
        (by intro t ht; cases ht) .fvar
    · -- `g = f`: look up `f` at index 0
      show TypeOfHM ⟨[PolyTy.mkTrivial (.fvar X), PolyTy.mkTrivial (.fvar X)], []⟩
        (.var 0) (.fvar X)
      exact TypeOfHM.var (polyTy := PolyTy.mkTrivial (.fvar X)) (instArgs := []) rfl
        (by intro t ht; cases ht) .fvar
  · -- the body sees `f`/`g` generalised to `∀a. a` and instantiates at `fvar 0`
    show TypeOfHM ⟨[⟨1, .bvar 0⟩, ⟨1, .bvar 0⟩], []⟩ (.var 0) (.fvar 0)
    exact TypeOfHM.var (polyTy := ⟨1, .bvar 0⟩) (instArgs := [.fvar 0]) rfl
      (by intro t ht; simp only [List.mem_singleton] at ht; subst ht; exact .fvar)
      (.bvar rfl)

set_option maxRecDepth 100_000 in
/-- The group's principal monotype is a bare variable (`∀a. a` after
    generalisation); with `mutualRec.tyFreeVars = [0]` and frontier `1` the
    residual variable is `3`. -/
theorem mutualRec_principalType : principalType [] mutualRec = some (.fvar 2) := by
  simp only [principalType, mutualRec]
  simp only [inferCore, inferRecGroupCore, RecSpec.init, RecSpec.onSubst, RecSpec.rhsEntry,
    freshVars, List.range, List.map, PolyTy.openVars]
  unfold unifyCoreK
  with_unfolding_all rfl

theorem mutualRec_eraseBounds : mutualRec.eraseBounds = mutualRec := by
  simp [Expr.eraseBounds, mutualRec]

/-- `mutualRec_typeable` at the computed principal variable `3`. -/
theorem mutualRec_typeable_fvar2 : TypeOfHM ⟨[], []⟩ mutualRec (.fvar 2) := by
  refine TypeOfHM.letRec (specs := [.mono (.fvar 100), .mono (.fvar 100)])
    (τs := [.fvar 100, .fvar 100]) (G := [100])
    (L := []) ⟨rfl, rfl, by simp, ?_, ?_⟩ rfl ?_ ?_ ?_ rfl ?_
  · intro τ hτ
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hτ
    rcases hτ with h | h <;> (injection h with h'; rw [h']; exact .fvar)
  · intro σ hσ
    simp only [List.mem_cons, List.not_mem_nil, reduceCtorEq, or_self] at hσ
  · intro p hp τ hτ
    simp only [List.zip_cons_cons, List.zip_nil_right, List.mem_cons, List.not_mem_nil,
      or_false] at hp
    rcases hp with rfl | rfl <;> (injection hτ with h')
  · intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with h | h <;> (rw [h]; exact .fvar)
  · intro Xs hfresh p hp
    obtain ⟨X, rfl⟩ : ∃ X, Xs = [X] := List.length_eq_one_iff.mp hfresh.length
    simp only [List.zip_cons_cons, List.zip_nil_right, List.mem_cons, List.not_mem_nil,
      or_false] at hp
    rcases hp with rfl | rfl
    · show TypeOfHM ⟨[PolyTy.mkTrivial (.fvar X), PolyTy.mkTrivial (.fvar X)], []⟩
        (.var 1) (.fvar X)
      exact TypeOfHM.var (polyTy := PolyTy.mkTrivial (.fvar X)) (instArgs := []) rfl
        (by intro t ht; cases ht) .fvar
    · show TypeOfHM ⟨[PolyTy.mkTrivial (.fvar X), PolyTy.mkTrivial (.fvar X)], []⟩
        (.var 0) (.fvar X)
      exact TypeOfHM.var (polyTy := PolyTy.mkTrivial (.fvar X)) (instArgs := []) rfl
        (by intro t ht; cases ht) .fvar
  · show TypeOfHM ⟨[⟨1, .bvar 0⟩, ⟨1, .bvar 0⟩], []⟩ (.var 0) (.fvar 2)
    exact TypeOfHM.var (polyTy := ⟨1, .bvar 0⟩) (instArgs := [.fvar 2]) rfl
      (by intro t ht; simp only [List.mem_singleton] at ht; subst ht; exact .fvar)
      (.bvar rfl)

/-- All headlines fire on the recursive group: `typecheck` succeeds, the produced
    type is a genuine residual declarative type (erase-normal soundness), and it
    is principal. -/
theorem mutualRec_headlines_fire :
    ∃ σ τ, typecheck [] mutualRec = some σ ∧ σ = genScheme [] [] τ ∧
      TypeOfHM ⟨[], []⟩ mutualRec.eraseBounds (Ty.eraseBounds τ) ∧
      ∀ τ₀, TypeOfHM ⟨[], []⟩ mutualRec.eraseBounds τ₀ → ∃ R : Subst, τ₀ = R.onTy τ := by
  refine ⟨genScheme [] [] (.fvar 2), .fvar 2, ?_, rfl, ?_, ?_⟩
  · show (principalType [] mutualRec).map (genScheme [] []) = _
    rw [mutualRec_principalType]; rfl
  · rw [mutualRec_eraseBounds]; exact mutualRec_typeable_fvar2
  · -- The principal type is a *bare* variable, so every `τ₀` is trivially an
    -- instance: no inversion needed.
    rw [mutualRec_eraseBounds]
    intro τ₀ _
    exact ⟨[(2, τ₀)], rfl⟩

end AuditCapstone
