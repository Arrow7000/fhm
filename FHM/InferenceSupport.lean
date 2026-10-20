import FHM.CorePath
import FHM.RuntimeTyping
import FHM.Scc.Kosaraju

/-!
# Shared foundations for inference

Substitution algebra, rigid unification and its executable implementation,
fresh-variable allocation and generalization, recursive dependency scheduling,
and the declarative typing lemmas used by inference and surface lowering.
This module defines no expression-inference relation or worker.
-/


-- These pure `Ty`-level lemmas now live in `Core` (they were originally developed
-- here). Core declares them without `@[simp]`, but the InferW proofs below rely on
-- them firing as simp lemmas, so re-grant the attribute here.
attribute [simp] Ty.openVars_arrow Ty.openVars_customTy

/-! ## Algorithmic phase, step 1: substitution algebra

The declarative `TypeOfHM` treats `.fvar`s as rigid/abstract type variables.
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

/-- Internal binder-scheme fact. `tyDepth` records how many nested source scheme
    binders surround the site, so an enclosing annotated RHS can close its
    temporary skolems at the correct offset. -/
structure InferredBinderScheme where
  site : CoreBinderSite
  scheme : PolyTy
  tyDepth : Nat

abbrev InferredBinderSchemes := List InferredBinderScheme

/-- Internal node-type fact. `tyDepth` is needed only while inference is nested
    beneath annotated RHSs: it makes closing a temporary skolem block respect
    any intervening source scheme binders. The public artifact drops this
    bookkeeping and exposes an ordinary `NodeTypeMap`. -/
structure InferredNodeType where
  path : CorePath
  ty : Ty
  tyDepth : Nat

abbrev InferredNodeTypes := List InferredNodeType

namespace InferredNodeTypes

def root (ty : Ty) : InferredNodeTypes :=
  [{ path := [], ty, tyDepth := 0 }]

def below (step : CoreStep) (types : InferredNodeTypes) : InferredNodeTypes :=
  types.map fun fact => { fact with path := step :: fact.path }

def onSubst (S : Subst) (types : InferredNodeTypes) : InferredNodeTypes :=
  types.map fun fact => { fact with ty := S.onTy fact.ty }

def underTyBinders (count : Nat) (types : InferredNodeTypes) : InferredNodeTypes :=
  types.map fun fact => { fact with tyDepth := fact.tyDepth + count }

/-- Account for the scheme binders contributed by the enclosing recursive
    member. Facts have already been path-prefixed with `letRecRhs`. -/
def underRecRhsBinders (anns : List (Option PolyTy))
    (types : InferredNodeTypes) : InferredNodeTypes :=
  types.map fun fact =>
    match fact.path with
    | .letRecRhs member :: _ =>
        { fact with tyDepth := fact.tyDepth + RecAnn.params (anns[member]?.getD none) }
    | _ => fact

def closeTyVars (Xs : List Nat) (types : InferredNodeTypes) : InferredNodeTypes :=
  types.map fun fact =>
    { fact with ty := Ty.closeVarsFrom fact.tyDepth Xs fact.ty }

def toMap (types : InferredNodeTypes) : NodeTypeMap :=
  types.map fun fact => (fact.path, fact.ty)

end InferredNodeTypes

namespace InferredBinderSchemes

def below (step : CoreStep) (schemes : InferredBinderSchemes) : InferredBinderSchemes :=
  schemes.map fun fact => { fact with site := fact.site.below step }

def onSubst (S : Subst) (schemes : InferredBinderSchemes) : InferredBinderSchemes :=
  schemes.map fun fact => { fact with scheme := S.onPolyTy fact.scheme }

def underTyBinders (count : Nat) (schemes : InferredBinderSchemes) : InferredBinderSchemes :=
  schemes.map fun fact => { fact with tyDepth := fact.tyDepth + count }

/-- Account for the scheme binders contributed by the enclosing member of a
    recursion group. Facts have already been path-prefixed with `letRecRhs`. -/
def underRecRhsBinders (anns : List (Option PolyTy))
    (schemes : InferredBinderSchemes) : InferredBinderSchemes :=
  schemes.map fun fact =>
    match fact.site.paths with
    | (.letRecRhs member :: _) :: _ =>
        { fact with tyDepth := fact.tyDepth + RecAnn.params (anns[member]?.getD none) }
    | _ => fact

def closeTyVars (Xs : List Nat) (schemes : InferredBinderSchemes) : InferredBinderSchemes :=
  schemes.map fun fact =>
    { fact with scheme := { fact.scheme with
        body := Ty.closeVarsFrom (fact.tyDepth + fact.scheme.paramCount) Xs fact.scheme.body } }

def toMap (schemes : InferredBinderSchemes) : BinderSchemeMap :=
  schemes.map fun fact => (fact.site, fact.scheme)

end InferredBinderSchemes

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

/-- Iterated annotation substitution composes in the same left-to-right order
    as the substitution threaded by inference. -/
theorem Expr.substTyFvars_append (S T : Subst) (e : Expr) :
    e.substTyFvars (S ++ T) = (e.substTyFvars S).substTyFvars T := by
  induction S generalizing e with
  | nil => rfl
  | cons hd S ih =>
    obtain ⟨Z, U⟩ := hd
    simp only [List.cons_append, Expr.substTyFvars]
    exact ih (Expr.substTyFvar Z U e)


/-- A type-fvar substitution whose keys avoid a term's annotation free vars
    leaves the term fixed (collapse of `Expr.substTyFvars` to a no-op). -/
theorem Expr.substTyFvars_eq_self_of_tyFreeVars_nil {e : Expr} (S : Subst)
    (h : e.tyFreeVars = []) : e.substTyFvars S = e := by
  apply Expr.substTyFvars_eq_self_of_not_mem_tyFreeVars
  intro p _
  simp [h]

/-- `map f xs = xs` when `f` is the identity on every member. -/
theorem List.map_eq_self_of_forall_eq_id {α : Type _} (f : α → α) :
    ∀ (xs : List α), (∀ x ∈ xs, f x = x) → xs.map f = xs
  | [], _ => rfl
  | x :: xs, h => by
    simp only [List.map_cons, List.cons.injEq]
    exact ⟨h x List.mem_cons_self, List.map_eq_self_of_forall_eq_id f xs
      (fun y hy => h y (List.mem_cons_of_mem _ hy))⟩


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

/-- `S` makes `τ₁` and `τ₂` syntactically equal. -/
def Unifies (S : Subst) (τ₁ τ₂ : Ty) : Prop := S.onTy τ₁ = S.onTy τ₂

/-- `S` is a most-general unifier of `τ₁` and `τ₂`: it unifies them, and any
    other unifier `S'` is an extension of `S` (factors as `S` then some `R`). -/
structure IsMGU (S : Subst) (τ₁ τ₂ : Ty) : Prop where
  unifies : Unifies S τ₁ τ₂
  greatest : ∀ S', Unifies S' τ₁ τ₂ → ∃ R : Subst, ∀ τ, S'.onTy τ = R.onTy (S.onTy τ)


/-! ### The unification relation

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

/-- Mapping a composed substitution over a list = mapping each factor in turn. -/
theorem Subst.map_onTy_append (S T : Subst) (ts : List Ty) :
    ts.map (S ++ T).onTy = (ts.map S.onTy).map T.onTy := by
  rw [List.map_map]
  apply List.map_congr_left
  intro x _
  exact Subst.onTy_append S T x


/-! ### Soundness, part 1: a derived substitution is a unifier -/

mutual

/-- Any substitution produced by `UnifyRel` actually unifies the two types. -/
theorem UnifyRel.unifies : {τ₁ τ₂ : Ty} → {S : Subst} → UnifyRel τ₁ τ₂ S →
    Unifies S τ₁ τ₂
  | _, _, _, .prim => rfl
  | _, _, _, .fvarRefl => rfl
  | _, _, _, .fvarL _ hocc => by
    simp [Unifies, Subst.onTy, Ty.substFvars, Ty.substFvar, Ty.substFvar_fresh hocc]
  | _, _, _, .fvarR _ hocc => by
    simp [Unifies, Subst.onTy, Ty.substFvars, Ty.substFvar, Ty.substFvar_fresh hocc]
  | _, _, _, .arrow h₁ h₂ => by
    have e1 := UnifyRel.unifies h₁
    have e2 := UnifyRel.unifies h₂
    simp only [Unifies, Subst.onTy_append, Subst.onTy_arrow] at e1 e2 ⊢
    rw [Ty.arrow.injEq]
    exact ⟨by rw [e1], e2⟩
  | _, _, _, .customTy hl => by
    have el := UnifyRelList.unifies hl
    simp only [Unifies, Subst.onTy_customTy, el]

/-- The list version: a list-unifier equalises the two lists pointwise. -/
theorem UnifyRelList.unifies : {ts₁ ts₂ : List Ty} → {S : Subst} →
    UnifyRelList ts₁ ts₂ S → ts₁.map S.onTy = ts₂.map S.onTy
  | _, _, _, .nil => rfl
  | _, _, _, .cons h₁ ht => by
    have e1 := UnifyRel.unifies h₁
    have et := UnifyRelList.unifies ht
    simp only [Unifies] at e1
    simp only [List.map_cons, Subst.onTy_append, Subst.map_onTy_append]
    rw [e1, et]

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

/-! Every substitution produced by `UnifyRel` is a *most general* unifier: any
    other unifier `S'` factors through it. The compound cases thread the
    sub-problem unifiers (`R₁` then `R₂`) and return the final `R₂`; the var
    cases use `onTy_substFvar`. -/
mutual

theorem UnifyRel.greatest : {τ₁ τ₂ : Ty} → {S : Subst} → UnifyRel τ₁ τ₂ S →
    ∀ S' : Subst, Unifies S' τ₁ τ₂ → ∃ R : Subst, ∀ τ, S'.onTy τ = R.onTy (S.onTy τ)
  | _, _, _, .prim, S', _ => ⟨S', fun τ => by simp only [Subst.onTy_nil]⟩
  | _, _, _, .fvarRefl, S', _ => ⟨S', fun τ => by simp only [Subst.onTy_nil]⟩
  | _, _, _, .fvarL _ _, S', hS' =>
    ⟨S', fun τ => (Subst.onTy_substFvar hS' τ).symm⟩
  | _, _, _, .fvarR _ _, S', hS' =>
    ⟨S', fun τ => (Subst.onTy_substFvar (Eq.symm hS') τ).symm⟩
  | _, _, _, @UnifyRel.arrow a b c d S₁ S₂ h₁ h₂, S', hS' => by
    simp only [Unifies, Subst.onTy_arrow, Ty.arrow.injEq] at hS'
    obtain ⟨hac, hbd⟩ := hS'
    obtain ⟨R₁, hR₁⟩ := UnifyRel.greatest h₁ S' hac
    have hR₁bd : Unifies R₁ (S₁.onTy b) (S₁.onTy d) := by
      show R₁.onTy (S₁.onTy b) = R₁.onTy (S₁.onTy d)
      rw [← hR₁ b, ← hR₁ d]; exact hbd
    obtain ⟨R₂, hR₂⟩ := UnifyRel.greatest h₂ R₁ hR₁bd
    refine ⟨R₂, fun τ => ?_⟩
    rw [Subst.onTy_append, ← hR₂ (S₁.onTy τ), hR₁ τ]
  | _, _, _, .customTy hl, S', hS' => by
    simp only [Unifies, Subst.onTy_customTy, Ty.customTy.injEq, true_and] at hS'
    exact UnifyRelList.greatest hl S' hS'

theorem UnifyRelList.greatest : {ts₁ ts₂ : List Ty} → {S : Subst} →
    UnifyRelList ts₁ ts₂ S → ∀ S' : Subst, ts₁.map S'.onTy = ts₂.map S'.onTy →
      ∃ R : Subst, ∀ τ, S'.onTy τ = R.onTy (S.onTy τ)
  | _, _, _, .nil, S', _ => ⟨S', fun τ => by simp only [Subst.onTy_nil]⟩
  | _, _, _, @UnifyRelList.cons t₁ t₂ ts₁ ts₂ S₁ S₂ h₁ ht, S', hS' => by
    simp only [List.map_cons, List.cons.injEq] at hS'
    obtain ⟨ht1t2, htail⟩ := hS'
    obtain ⟨R₁, hR₁⟩ := UnifyRel.greatest h₁ S' ht1t2
    have key : ∀ (l : List Ty), l.map (R₁.onTy ∘ S₁.onTy) = l.map S'.onTy := by
      intro l; apply List.map_congr_left; intro t _; exact (hR₁ t).symm
    have hlist : (ts₁.map S₁.onTy).map R₁.onTy = (ts₂.map S₁.onTy).map R₁.onTy := by
      rw [List.map_map, List.map_map, key, key]; exact htail
    obtain ⟨R₂, hR₂⟩ := UnifyRelList.greatest ht R₁ hlist
    refine ⟨R₂, fun τ => ?_⟩
    rw [Subst.onTy_append, ← hR₂ (S₁.onTy τ), hR₁ τ]

end

/-- Unification soundness, assembled: a derivation yields a most-general unifier. -/
theorem UnifyRel.isMGU {τ₁ τ₂ : Ty} {S : Subst} (h : UnifyRel τ₁ τ₂ S) :
    IsMGU S τ₁ τ₂ :=
  ⟨h.unifies, h.greatest⟩


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

/-! ### Residual dependency SCCs for recursive inference

The runtime `letRec` group remains the SCC selected by the Surface pass.  For
type inference, however, a complete annotation is a dependency cut.  The graph
below therefore retains edges only between unannotated members.  Annotated
vertices are isolated by construction and discarded after Kosaraju; the
remaining components are ordered dependency-first by the proved finite
reachability ranking in `Scc.rankedSccs`.

This second partition is intentionally derived from Core de Bruijn references,
not carried as elaboration metadata. -/

def RecGroup.isUnsignedAt (anns : List (Option PolyTy)) (i : Nat) : Bool :=
  match anns[i]? with
  | some none => true
  | _ => false

theorem RecGroup.isUnsignedAt_eq_true_iff
    (anns : List (Option PolyTy)) (i : Nat) :
    RecGroup.isUnsignedAt anns i = true ↔ RecGroups.UnsignedAt anns i := by
  simp only [RecGroup.isUnsignedAt, RecGroups.UnsignedAt]
  cases anns[i]? <;> simp
  case some ann => cases ann <;> simp

def RecGroup.inferenceSucc (anns : List (Option PolyTy))
    (bindings : List Expr) (i : Nat) : List Nat :=
  if RecGroup.isUnsignedAt anns i then
    match bindings[i]? with
    | none => []
    | some rhs =>
        (rhs.recGroupRefs bindings.length 0).filter
          (fun j => RecGroup.isUnsignedAt anns j)
  else []

def RecGroup.inferenceDigraph (anns : List (Option PolyTy))
    (bindings : List Expr) : Scc.Digraph (Fin bindings.length) where
  succ := fun i =>
    ((RecGroup.inferenceSucc anns bindings i.val).filterMap fun j =>
      if h : j < bindings.length then some ⟨j, h⟩ else none).toFinset

theorem RecGroup.mem_inferenceDigraph_succ_iff
    {anns : List (Option PolyTy)} {bindings : List Expr}
    (source target : Fin bindings.length) :
    target ∈ (RecGroup.inferenceDigraph anns bindings).succ source ↔
      target.val ∈ RecGroup.inferenceSucc anns bindings source.val := by
  simp only [RecGroup.inferenceDigraph, List.mem_toFinset, List.mem_filterMap]
  constructor
  · rintro ⟨member, hmember, hsome⟩
    split at hsome
    · have hval := congrArg Fin.val (Option.some.inj hsome)
      simpa [← hval] using hmember
    · simp at hsome
  · intro hmember
    exact ⟨target.val, hmember, by simp [target.isLt]⟩

/-- The fine residual-SCC schedule.  `rankedSccs` orders Kosaraju components
by a proved finite reachability rank, after which annotated singleton
components erase to empty and are discarded. -/
private def RecGroup.projectInferenceComponent (anns : List (Option PolyTy))
    (component : List (Fin n)) : List Nat :=
  (component.map Fin.val).filter (fun i => RecGroup.isUnsignedAt anns i)

private def RecGroup.inferenceSccProjected (anns : List (Option PolyTy))
    (bindings : List Expr) : List (List Nat) :=
  (Scc.rankedSccs (RecGroup.inferenceDigraph anns bindings)).map
    (RecGroup.projectInferenceComponent anns)

def RecGroup.inferenceSccs (anns : List (Option PolyTy))
    (bindings : List Expr) : List (List Nat) :=
  (RecGroup.inferenceSccProjected anns bindings).filter (!·.isEmpty)

private theorem RecGroup.inferenceSccProjected_flatten
    (anns : List (Option PolyTy)) (bindings : List Expr) :
    (RecGroup.inferenceSccProjected anns bindings).flatten =
      ((Scc.rankedSccs (RecGroup.inferenceDigraph anns bindings)).flatten.map Fin.val).filter
        (fun i => RecGroup.isUnsignedAt anns i) := by
  simp only [RecGroup.inferenceSccProjected]
  induction Scc.rankedSccs (RecGroup.inferenceDigraph anns bindings) with
  | nil => simp
  | cons component components ih =>
    simp only [List.map_cons, List.flatten_cons, List.map_append, List.filter_append, ih,
      RecGroup.projectInferenceComponent]

private theorem RecGroup.inferenceSccs_flatten
    (anns : List (Option PolyTy)) (bindings : List Expr) :
    (RecGroup.inferenceSccs anns bindings).flatten =
      (RecGroup.inferenceSccProjected anns bindings).flatten := by
  simp only [RecGroup.inferenceSccs]
  induction RecGroup.inferenceSccProjected anns bindings with
  | nil => simp
  | cons component components ih =>
    cases component <;> simp [ih]

private theorem RecGroup.inferenceSccs_flatten_nodup
    (anns : List (Option PolyTy)) (bindings : List Expr) :
    (RecGroup.inferenceSccs anns bindings).flatten.Nodup := by
  rw [RecGroup.inferenceSccs_flatten, RecGroup.inferenceSccProjected_flatten]
  have hfin := (Scc.rankedSccs_flatten_nodup
    (RecGroup.inferenceDigraph anns bindings)).map (fun a b hab => Fin.ext hab)
  exact hfin.filter _

private theorem RecGroup.inferenceSccs_nonempty
    (anns : List (Option PolyTy)) (bindings : List Expr) :
    ∀ component ∈ RecGroup.inferenceSccs anns bindings, component ≠ [] := by
  intro component hcomponent hempty
  subst component
  simp [RecGroup.inferenceSccs] at hcomponent

private theorem RecGroup.inferenceSccs_bounded
    (anns : List (Option PolyTy)) (bindings : List Expr) :
    ∀ member ∈ (RecGroup.inferenceSccs anns bindings).flatten,
      member < bindings.length := by
  intro member hmember
  rw [RecGroup.inferenceSccs_flatten,
    RecGroup.inferenceSccProjected_flatten] at hmember
  obtain ⟨hmember, _⟩ := List.mem_filter.mp hmember
  obtain ⟨vertex, _hvertex, hval⟩ := List.mem_map.mp hmember
  exact hval ▸ vertex.isLt

/-- Members projected into the same executable residual component are mutually
    reachable in the unsigned dependency graph.  Completeness uses this public
    SCC fact to show that an arbitrary valid declarative partition cannot split
    one of the algorithm's fine components. -/
theorem RecGroup.inferenceSccs_sameScc
    (anns : List (Option PolyTy)) (bindings : List Expr)
    {stage : Nat} {component : List Nat} {left right : Nat}
    (hcomponent : (RecGroup.inferenceSccs anns bindings)[stage]? = some component)
    (hleft : left ∈ component) (hright : right ∈ component)
    (hleftBound : left < bindings.length) (hrightBound : right < bindings.length) :
    Scc.Mutual (RecGroup.inferenceDigraph anns bindings)
      ⟨left, hleftBound⟩ ⟨right, hrightBound⟩ := by
  have hcomponentMem : component ∈ RecGroup.inferenceSccs anns bindings :=
    List.mem_of_getElem? hcomponent
  simp only [RecGroup.inferenceSccs, List.mem_filter] at hcomponentMem
  obtain ⟨hprojected, _⟩ := hcomponentMem
  simp only [RecGroup.inferenceSccProjected, List.mem_map] at hprojected
  obtain ⟨sourceComponent, hsourceMem, hproject⟩ := hprojected
  have hleftProjected : left ∈ RecGroup.projectInferenceComponent anns sourceComponent := by
    simpa [hproject] using hleft
  have hrightProjected : right ∈ RecGroup.projectInferenceComponent anns sourceComponent := by
    simpa [hproject] using hright
  simp only [RecGroup.projectInferenceComponent, List.mem_filter] at hleftProjected
  simp only [RecGroup.projectInferenceComponent, List.mem_filter] at hrightProjected
  obtain ⟨hleftMap, _⟩ := hleftProjected
  obtain ⟨hrightMap, _⟩ := hrightProjected
  obtain ⟨leftFin, hleftFinMem, hleftVal⟩ := List.mem_map.mp hleftMap
  obtain ⟨rightFin, hrightFinMem, hrightVal⟩ := List.mem_map.mp hrightMap
  have hsourceKosaraju : sourceComponent ∈
      Scc.kosaraju (RecGroup.inferenceDigraph anns bindings) :=
    (List.Perm.mem_iff (Scc.rankedSccs_perm
      (RecGroup.inferenceDigraph anns bindings))).mp hsourceMem
  have hmutual := (Scc.kosaraju_sound
    (RecGroup.inferenceDigraph anns bindings)).sameScc
      sourceComponent hsourceKosaraju leftFin hleftFinMem rightFin hrightFinMem
  have hleftEq : leftFin = ⟨left, hleftBound⟩ := Fin.ext hleftVal
  have hrightEq : rightFin = ⟨right, hrightBound⟩ := Fin.ext hrightVal
  simpa [hleftEq, hrightEq] using hmutual

private theorem RecGroup.mem_inferenceSccs_flatten_iff
    (anns : List (Option PolyTy)) (bindings : List Expr)
    {member : Nat} (hbound : member < bindings.length) :
    member ∈ (RecGroup.inferenceSccs anns bindings).flatten ↔
      RecGroups.UnsignedAt anns member := by
  rw [RecGroup.inferenceSccs_flatten,
    RecGroup.inferenceSccProjected_flatten, List.mem_filter]
  constructor
  · intro h
    exact (RecGroup.isUnsignedAt_eq_true_iff anns member).mp h.2
  · intro hu
    refine ⟨?_, (RecGroup.isUnsignedAt_eq_true_iff anns member).mpr hu⟩
    let vertex : Fin bindings.length := ⟨member, hbound⟩
    have hcover := (Scc.kosaraju_sound
      (RecGroup.inferenceDigraph anns bindings)).cover vertex
    have hranked : vertex ∈
        (Scc.rankedSccs (RecGroup.inferenceDigraph anns bindings)).flatten := by
      obtain ⟨component, hcomponent, hvertex⟩ := hcover
      apply List.mem_flatten.mpr
      refine ⟨component, (List.Perm.mem_iff
        (Scc.rankedSccs_perm (RecGroup.inferenceDigraph anns bindings))).mpr hcomponent,
        hvertex⟩
    exact List.mem_map.mpr ⟨vertex, hranked, rfl⟩

private def RecGroup.NoForwardEdge (anns : List (Option PolyTy))
    (bindings : List Expr) (earlier later : List Nat) : Prop :=
  ∀ source ∈ earlier, ∀ target ∈ later,
    ∀ (hsource : source < bindings.length) (htarget : target < bindings.length),
      (⟨target, htarget⟩ : Fin bindings.length) ∉
        (RecGroup.inferenceDigraph anns bindings).succ ⟨source, hsource⟩

private theorem RecGroup.inferenceSccs_noForward
    (anns : List (Option PolyTy)) (bindings : List Expr) :
    (RecGroup.inferenceSccs anns bindings).Pairwise
      (RecGroup.NoForwardEdge anns bindings) := by
  let graph := RecGroup.inferenceDigraph anns bindings
  have hranked : (Scc.rankedSccs graph).Pairwise fun earlier later =>
      ∀ source ∈ earlier, ∀ target ∈ later, target ∉ graph.succ source := by
    rw [List.pairwise_iff_getElem]
    intro i j hi hj hij source hsource target htarget hedge
    have hbefore := Scc.rankedSccs_dependency_first graph
      (dependentStage := i) (dependencyStage := j)
      (dependent := (Scc.rankedSccs graph)[i])
      (dependency := (Scc.rankedSccs graph)[j])
      (source := source) (target := target)
      (List.getElem?_eq_getElem hi) (List.getElem?_eq_getElem hj)
      hsource htarget hedge
    omega
  have hprojected : (RecGroup.inferenceSccProjected anns bindings).Pairwise
      (RecGroup.NoForwardEdge anns bindings) := by
    apply hranked.map (RecGroup.projectInferenceComponent anns)
    intro earlier later hrel source hsource target htarget hsourceBound htargetBound hedge
    have hsourceMap := (List.mem_filter.mp hsource).1
    have htargetMap := (List.mem_filter.mp htarget).1
    obtain ⟨sourceFin, hsourceFin, hsourceVal⟩ := List.mem_map.mp hsourceMap
    obtain ⟨targetFin, htargetFin, htargetVal⟩ := List.mem_map.mp htargetMap
    have hedge' : targetFin ∈ graph.succ sourceFin := by
      have hsEq : sourceFin = ⟨source, hsourceBound⟩ := Fin.ext hsourceVal
      have htEq : targetFin = ⟨target, htargetBound⟩ := Fin.ext htargetVal
      simpa [hsEq, htEq, graph] using hedge
    exact hrel sourceFin hsourceFin targetFin htargetFin hedge'
  exact hprojected.filter _

/-- The fine residual scheduler always returns a valid dependency-first SCC
partition.  The only precondition is the constructor's ordinary parallel-list
length invariant. -/
theorem RecGroup.inferenceSccs_valid
    {anns : List (Option PolyTy)} {bindings : List Expr}
    (hlength : anns.length = bindings.length) :
    RecGroups.ValidResidualGroups anns bindings
      (RecGroup.inferenceSccs anns bindings) := by
  refine {
    length := hlength
    nonempty := RecGroup.inferenceSccs_nonempty anns bindings
    flatten_nodup := RecGroup.inferenceSccs_flatten_nodup anns bindings
    bounded := RecGroup.inferenceSccs_bounded anns bindings
    covers_unsigned := ?_
    dependencies_first := ?_ }
  · intro member hbound
    exact RecGroup.mem_inferenceSccs_flatten_iff anns bindings hbound
  · intro stage dependencyStage component dependencyComponent source target rhs
      hcomponent hdependencyComponent hsource htarget hrhs href
    by_contra hnotle
    have hstageLt : stage < dependencyStage := Nat.lt_of_not_ge hnotle
    have hsourceFlat : source ∈
        (RecGroup.inferenceSccs anns bindings).flatten :=
      List.mem_flatten.mpr ⟨component, List.mem_of_getElem? hcomponent, hsource⟩
    have htargetFlat : target ∈
        (RecGroup.inferenceSccs anns bindings).flatten :=
      List.mem_flatten.mpr
        ⟨dependencyComponent, List.mem_of_getElem? hdependencyComponent, htarget⟩
    have hsourceBound := RecGroup.inferenceSccs_bounded anns bindings
      source hsourceFlat
    have htargetBound := RecGroup.inferenceSccs_bounded anns bindings
      target htargetFlat
    have hsourceUnsigned :=
      (RecGroup.mem_inferenceSccs_flatten_iff anns bindings hsourceBound).mp
        hsourceFlat
    have htargetUnsigned :=
      (RecGroup.mem_inferenceSccs_flatten_iff anns bindings htargetBound).mp
        htargetFlat
    have hsucc : target ∈ RecGroup.inferenceSucc anns bindings source := by
      have hsourceBool := (RecGroup.isUnsignedAt_eq_true_iff anns source).mpr hsourceUnsigned
      have htargetBool := (RecGroup.isUnsignedAt_eq_true_iff anns target).mpr htargetUnsigned
      simp only [RecGroup.inferenceSucc, hsourceBool, if_true, hrhs, List.mem_filter]
      exact ⟨href, htargetBool⟩
    have hedge : (⟨target, htargetBound⟩ : Fin bindings.length) ∈
        (RecGroup.inferenceDigraph anns bindings).succ ⟨source, hsourceBound⟩ :=
      (RecGroup.mem_inferenceDigraph_succ_iff _ _).mpr hsucc
    have hpairwise := RecGroup.inferenceSccs_noForward anns bindings
    have hnoedge := (List.pairwise_iff_getElem.mp hpairwise) stage dependencyStage
      (List.getElem?_eq_some_iff.mp hcomponent).1
      (List.getElem?_eq_some_iff.mp hdependencyComponent).1 hstageLt
    rw [(List.getElem?_eq_some_iff.mp hcomponent).2,
      (List.getElem?_eq_some_iff.mp hdependencyComponent).2] at hnoedge
    exact hnoedge source hsource target htarget hsourceBound htargetBound hedge

theorem Expr.mem_flatMap_tyFreeVars_iff_recGroup {bindings : List Expr} {x : Nat} :
    x ∈ bindings.flatMap Expr.tyFreeVars ↔
      x ∈ Expr.tyFreeVars.RecGroup.tyFreeVars bindings := by
  induction bindings with
  | nil => simp [Expr.tyFreeVars.RecGroup.tyFreeVars]
  | cons e bindings ih =>
    simp only [List.flatMap_cons, Expr.tyFreeVars.RecGroup.tyFreeVars,
      List.mem_append, ih]

/-- `Ty.freeVarsList` is always duplicate-free (it dedups). -/
theorem Ty.freeVarsList_nodup {τs : List Ty} : (Ty.freeVarsList τs).Nodup := by
  cases τs with
  | nil => simp [Ty.freeVarsList]
  | cons hd tl => simp [Ty.freeVarsList, List.nodup_dedup]

/-- The group generalization candidates are duplicate-free. -/
theorem genGroupVars_nodup {rigid : List Nat} {env : Env} {τs : List Ty} :
    (genGroupVars rigid env τs).Nodup :=
  Ty.freeVarsList_nodup.filter _

/-! ### Algorithmic `RecSpec` helpers

The recursive inference rule threads a `List RecSpec` (Core's per-binding datum:
`mono τ` for an unannotated member's solved monotype, `poly σ` for an annotated
member's declared scheme). These small helpers are the algorithmic counterparts
of Core's `RecSpec.rhsEntry`/`bodyScheme`: build the initial specs positionally
from the stored `anns`, thread a substitution through the mono members (schemes
stay RIGID), and project out the mono monotypes for the shared gen-var pool. -/

/-- Thread a substitution through a spec: an unannotated member's solved monotype
    moves under `S`; an annotated member's declared scheme remains rigid. -/
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

/-- Monotypes belonging to one residual component, selected in the component's
original recursive-group coordinates. -/
def RecSpecs.monoTysAt (specs : List RecSpec) (members : List Nat) : List Ty :=
  members.filterMap fun member => (specs[member]?).bind RecSpec.monoTy?

/-- Algorithmic environment entry while residual components are processed.
Completed inferred members are schemes; annotated members are always schemes;
current and later inferred members retain their positional monotypes. -/
def RecSpec.algorithmStageEntry (done G : List Nat) (member : Nat)
    (spec : RecSpec) : PolyTy :=
  match spec with
  | .poly σ => σ
  | .mono τ =>
      if member ∈ done then PolyTy.genGroup G τ else PolyTy.mkTrivial τ

def RecSpecs.algorithmStageCtx (ctx : Ctx) (specs : List RecSpec)
    (done G : List Nat) : Ctx :=
  { ctx with env := specs.mapIdx (RecSpec.algorithmStageEntry done G) ++ ctx.env }

/-- Only contracts and already-completed components constrain generalisation of
the next residual SCC. Current/later monotype placeholders retain positions in
the inference environment but are excluded from this free-variable boundary. -/
def RecSpecs.fixedSchemes (specs : List RecSpec) (done G : List Nat) : List PolyTy :=
  specs.mapIdx (fun member spec =>
    match spec with
    | .poly σ => some σ
    | .mono τ => if member ∈ done then some (PolyTy.genGroup G τ) else none)
  |>.filterMap id

def RecSpecs.generalizationCtx (ctx : Ctx) (specs : List RecSpec)
    (done G : List Nat) : Ctx :=
  { ctx with env := RecSpecs.fixedSchemes specs done G ++ ctx.env }

/-- Well-formedness of a single algorithmic `RecSpec`: an unannotated member's
    solved monotype is locally closed; an annotated member's declared scheme is
    `WF`. The spec-level lift of `RecSpecs.WF`'s `mono_lc`/`poly_wf` fields. -/
def RecSpec.LC : RecSpec → Prop
  | .mono τ => τ.IsLC
  | .poly σ => σ.WF

/-- Free type variables a `RecSpec` contributes to recursive-group
    generalisation and scoped-variable checks: an
    unannotated member's monotype free vars, an annotated member's scheme-body free
    vars (its scoped variables). -/
def RecSpec.freeVars : RecSpec → List Nat
  | .mono τ => τ.freeVars
  | .poly σ => σ.body.freeVars

/-- Initial recursive specs. Unannotated members receive a fresh monotype;
    annotated members expose their declared scheme throughout the block. -/
def RecSpec.init (Φ : Nat) : List (Option PolyTy) → List RecSpec
  | []            => []
  | none :: as    => RecSpec.mono (.fvar Φ) :: RecSpec.init (Φ + 1) as
  | some σ :: as  => RecSpec.poly σ :: RecSpec.init (Φ + 1) as

/-- Initial specs retain the stored annotations. -/
theorem RecSpec.map_ann_init (Φ : Nat) (anns : List (Option PolyTy)) :
    (RecSpec.init Φ anns).map RecSpec.ann = anns := by
  induction anns generalizing Φ with
  | nil => rfl
  | cons a as ih => cases a <;> simp only [RecSpec.init, List.map_cons, RecSpec.ann, ih (Φ + 1)]

/-- `init` produces one spec per stored annotation. -/
theorem RecSpec.init_length (Φ : Nat) (anns : List (Option PolyTy)) :
    (RecSpec.init Φ anns).length = anns.length := by
  induction anns generalizing Φ with
  | nil => rfl
  | cons a as ih => cases a <;> simp only [RecSpec.init, List.length_cons, ih (Φ + 1)]

/-- Positional initial spec lookup. -/
theorem RecSpec.init_getElem? (Φ : Nat) (anns : List (Option PolyTy)) (j : Nat) :
    (RecSpec.init Φ anns)[j]? = (anns[j]?).map
      (fun a => match a with | none => .mono (.fvar (Φ + j)) | some σ => .poly σ) := by
  induction anns generalizing Φ j with
  | nil => simp [RecSpec.init]
  | cons a as ih =>
    cases j with
    | zero => cases a <;> simp [RecSpec.init]
    | succ j =>
      cases a <;> simp only [RecSpec.init, List.getElem?_cons_succ, ih (Φ + 1) j, Nat.add_assoc,
        Nat.add_comm 1 j]

/-- Every initial spec is a fresh monotype or a stored annotated scheme. -/
theorem RecSpec.mem_init {s : RecSpec} :
    ∀ {Φ : Nat} {anns : List (Option PolyTy)}, s ∈ RecSpec.init Φ anns →
      (∃ m, Φ ≤ m ∧ m < Φ + anns.length ∧ s = .mono (.fvar m)) ∨
      (∃ σ, some σ ∈ anns ∧ s = .poly σ) := by
  intro Φ anns
  induction anns generalizing Φ with
  | nil => intro h; simp [RecSpec.init] at h
  | cons a as ih =>
    intro h
    cases a with
    | none =>
      rcases List.mem_cons.mp h with rfl | h
      · exact .inl ⟨Φ, le_refl _, by simp only [List.length_cons]; omega, rfl⟩
      · rcases ih h with ⟨m, h1, h2, h3⟩ | ⟨σ, h1, h2⟩
        · exact .inl ⟨m, by omega, by simp only [List.length_cons]; omega, h3⟩
        · exact .inr ⟨σ, List.mem_cons_of_mem _ h1, h2⟩
    | some σ =>
    rcases List.mem_cons.mp h with rfl | h
    · exact .inr ⟨σ, List.mem_cons_self, rfl⟩
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


mutual
/-- Boolean: all `.bvar`s in `t` are `< n`. Decides `ContainsBvarsUpTo n t`. -/
def Ty.bvarsBelow (n : Nat) : Ty → Bool
  | .prim _          => true
  | .arrow a b       => Ty.bvarsBelow n a && Ty.bvarsBelow n b
  | .fvar _          => true
  | .bvar i          => decide (i < n)
  | .customTy _ tys  => TyList.bvarsBelow n tys
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

/-- Decidability of scheme well-formedness, via `Ty.bvarsBelow`. -/
theorem PolyTy.wf_iff_bvarsBelow {M : PolyTy} :
    Ty.bvarsBelow M.paramCount M.body = true ↔ M.WF := Ty.bvarsBelow_iff M.body

/-- Executable local-closedness test for the solver's input specs. -/
def RecSpec.isLCB : RecSpec → Bool
  | .mono τ => Ty.bvarsBelow 0 τ
  | .poly σ => Ty.bvarsBelow σ.paramCount σ.body

theorem RecSpec.isLCB_iff (s : RecSpec) : s.isLCB = true ↔ s.LC := by
  cases s with
  | mono τ => exact Ty.bvarsBelow_iff τ
  | poly σ => exact PolyTy.wf_iff_bvarsBelow

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

/-- A type has no free vars iff its `freeVars` list is empty (decidable bridge). -/
theorem Ty.noFreeVars_iff_freeVars_nil {t : Ty} :
    NoFreeVars t ↔ t.freeVars = [] := by
  refine ⟨fun h => List.eq_nil_iff_forall_not_mem.mpr (fun z => h.not_mem_freeVars z), fun h => ?_⟩
  exact Ty.noFreeVars_of_forall_not_mem (fun z hz => by rw [h] at hz; simp at hz)

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


/-- A substitution whose domain avoids every free variable of a scheme leaves
    that scheme literally unchanged. -/
theorem Subst.onPolyTy_eq_self_of_dom_avoids {S : Subst} {σ : PolyTy}
    (hdom : ∀ p ∈ S, p.1 ∉ σ.body.freeVars) : S.onPolyTy σ = σ := by
  obtain ⟨pc, body⟩ := σ
  simp only [Subst.onPolyTy, PolyTy.mk.injEq, true_and]
  exact Ty.substFvars_eq_self_of_no_key hdom


/-! Algorithm W as a type-directed inference relation over the source `Expr`.
    Its outputs are only the fresh-variable frontier, substitution, and inferred
    monotype; runtime execution uses the independently defined erased source term.
    Its first index records the ambient rigid variables. Recursive children
    retain that index; annotated RHS children extend it with their skolems.
    The relation is mutually defined with the branch and recursive-group
    threaders below. Generalization still uses source annotation variables. -/
/-- Unification at an inference step may solve only non-rigid variables. -/
structure RigidUnify (K : List Nat) (a b : Ty) (S : Subst) : Prop where
  unifies : UnifyRel a b S
  dom_avoids : ∀ p ∈ S, p.1 ∉ K

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


private theorem domAvoids_append {K : List Nat} {S T : Subst}
    (hS : ∀ p ∈ S, p.1 ∉ K) (hT : ∀ p ∈ T, p.1 ∉ K) :
    ∀ p ∈ S ++ T, p.1 ∉ K :=
  fun p hp => (List.mem_append.mp hp).elim (hS p) (hT p)


theorem Subst.skolem_dom_avoids {κ Ys : List Nat} {S T : Subst}
    (hS : ∀ p ∈ S, p.1 ∉ κ ++ Ys) (hT : ∀ p ∈ T, p.1 ∉ κ ++ Ys) :
    ∀ y ∈ Ys, y ∉ (S ++ T).map Prod.fst := by
  intro y hy hm
  obtain ⟨p, hp, he⟩ := List.mem_map.mp hm
  exact domAvoids_append hS hT p hp (he ▸ List.mem_append_right _ hy)

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


theorem RecSpec.algorithmStageEntry_wf {s : RecSpec} (h : s.LC)
    (done G : List Nat) (member : Nat) :
    (RecSpec.algorithmStageEntry done G member s).WF := by
  cases s with
  | mono τ =>
    simp only [RecSpec.algorithmStageEntry]
    split
    · exact PolyTy.genGroup_wf h
    · exact h
  | poly σ => exact h

theorem RecSpecs.algorithmStageCtx_wf {ctx : Ctx} {specs : List RecSpec}
    (hctx : CtxWF ctx) (hspecs : ∀ s ∈ specs, s.LC) (done G : List Nat) :
    CtxWF (RecSpecs.algorithmStageCtx ctx specs done G) := by
  intro M hM
  rcases List.mem_append.mp hM with hM | hM
  · obtain ⟨i, hi, rfl⟩ := List.mem_mapIdx.mp hM
    exact RecSpec.algorithmStageEntry_wf (hspecs _ (List.getElem_mem hi)) done G i
  · exact hctx M hM

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

theorem Ty.BelowFvars.mono {Φ Φ' : Nat} {τ : Ty} (hle : Φ ≤ Φ')
    (h : Ty.BelowFvars Φ τ) : Ty.BelowFvars Φ' τ := by
  induction h with
  | prim => exact .prim
  | arrow _ _ iha ihb => exact .arrow iha ihb
  | bvar => exact .bvar
  | fvar hlt => exact .fvar (by omega)
  | customTy _ ih => exact .customTy (fun t ht => ih t ht)

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


def CtxBelow (Φ : Nat) (ctx : Ctx) : Prop := ∀ M ∈ ctx.env, Ty.BelowFvars Φ M.body


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

/-- A type with no free variables is below any frontier. -/
theorem Ty.BelowFvars.of_noFreeVars {Φ : Nat} {τ : Ty} (h : NoFreeVars τ) :
    Ty.BelowFvars Φ τ := by
  induction h with
  | prim => exact .prim
  | arrow _ _ iha ihb => exact .arrow iha ihb
  | bvar => exact .bvar
  | customTy _ ih => exact .customTy (fun t ht => ih t ht)

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

/-- Executable frontier check for a recursion specification. -/
def RecSpec.belowFvarsB (Φ : Nat) (s : RecSpec) : Bool :=
  s.freeVars.all (fun x => decide (x < Φ))

theorem RecSpec.belowFvarsB_iff {Φ : Nat} (s : RecSpec) :
    s.belowFvarsB Φ = true ↔ s.BelowFvars Φ := by
  unfold RecSpec.belowFvarsB
  constructor
  · intro h
    cases s with
    | mono τ =>
        apply Ty.BelowFvars.of_freeVars_lt
        intro x hx
        exact of_decide_eq_true (List.all_eq_true.mp h x hx)
    | poly σ =>
        apply Ty.BelowFvars.of_freeVars_lt
        intro x hx
        exact of_decide_eq_true (List.all_eq_true.mp h x hx)
  · intro h
    apply List.all_eq_true.mpr
    intro x hx
    apply decide_eq_true
    cases s with
    | mono τ => exact h.mem_lt x hx
    | poly σ => exact h.mem_lt x hx


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
    rw [Ty.closeOver]
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

/-- A body scheme's body is frontier-bounded when its spec is (mono: closing only
    removes free vars). -/
theorem RecSpec.bodyScheme_belowFvars {Φ : Nat} {G : List Nat} {s : RecSpec}
    (h : s.BelowFvars Φ) : Ty.BelowFvars Φ (RecSpec.bodyScheme G s).body := by
  cases s with
  | mono τ => exact Ty.BelowFvars.closeOver h
  | poly σ => exact h

theorem RecSpec.algorithmStageEntry_belowFvars {Φ : Nat} {s : RecSpec}
    (h : s.BelowFvars Φ) (done G : List Nat) (member : Nat) :
    Ty.BelowFvars Φ (RecSpec.algorithmStageEntry done G member s).body := by
  cases s with
  | mono τ =>
    simp only [RecSpec.algorithmStageEntry]
    split
    · exact Ty.BelowFvars.closeOver h
    · exact h
  | poly σ => exact h

theorem RecSpecs.algorithmStageCtx_below {Φ : Nat} {ctx : Ctx} {specs : List RecSpec}
    (hctx : CtxBelow Φ ctx) (hspecs : ∀ s ∈ specs, s.BelowFvars Φ) (done G : List Nat) :
    CtxBelow Φ (RecSpecs.algorithmStageCtx ctx specs done G) := by
  intro M hM
  rcases List.mem_append.mp hM with hM | hM
  · obtain ⟨i, hi, rfl⟩ := List.mem_mapIdx.mp hM
    exact RecSpec.algorithmStageEntry_belowFvars (hspecs _ (List.getElem_mem hi)) done G i
  · exact hctx M hM

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

/-- Every free type variable of a recursive group comes from its annotations,
    a member spec, a raw binding, or the body. Shifting and closing introduce no
    new free variables. -/
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

/-- A free type var of `e.substTyFvars S` comes from `e` or one of the image
    types. Uses the public `substTyFvars_*` distribution lemmas. -/
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

theorem RecSpec.algorithmStageEntry_freeVars_subset {s : RecSpec} {done G : List Nat}
    {member w : Nat} (h : w ∈ (RecSpec.algorithmStageEntry done G member s).body.freeVars) :
    w ∈ s.freeVars := by
  cases s with
  | mono τ =>
    simp only [RecSpec.algorithmStageEntry] at h
    split at h
    · exact Ty.freeVars_closeOver_subset h
    · exact h
  | poly σ => exact h

theorem RecSpecs.algorithmStageCtx_avoid {ctx : Ctx} {specs : List RecSpec} {w : Nat}
    (hctx : ∀ M ∈ ctx.env, w ∉ M.body.freeVars) (hspecs : ∀ s ∈ specs, w ∉ s.freeVars)
    (done G : List Nat) :
    ∀ M ∈ (RecSpecs.algorithmStageCtx ctx specs done G).env, w ∉ M.body.freeVars := by
  intro M hM
  rcases List.mem_append.mp hM with hM | hM
  · obtain ⟨i, hi, rfl⟩ := List.mem_mapIdx.mp hM
    exact fun hc => hspecs _ (List.getElem_mem hi) (RecSpec.algorithmStageEntry_freeVars_subset hc)
  · exact hctx M hM

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

private theorem Expr.length_le_sizeRecGroup (bindings : List Expr) :
    bindings.length ≤ Expr.sizeRecGroup bindings := by
  induction bindings with
  | nil => simp [Expr.sizeRecGroup]
  | cons e rest ih =>
    simp only [List.length_cons, Expr.sizeRecGroup]
    have := Expr.size_pos e
    omega

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

/-! ## Principality foundations -/


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

/-- Agreeing substitutions act identically on a below-`Φ` context. -/
theorem Subst.onCtx_congr {Φ : Nat} {S T : Subst} {ctx : Ctx}
    (hag : ∀ v, v < Φ → S.onTy (.fvar v) = T.onTy (.fvar v)) (hb : CtxBelow Φ ctx) :
    S.onCtx ctx = T.onCtx ctx := by
  simp only [Subst.onCtx, Subst.onEnv]
  congr 1
  apply List.map_congr_left
  intro M hM
  simp only [Subst.onPolyTy, Subst.onTy_congr hag (hb M hM)]

/-- `S` and `T` agree (act identically on every `fvar`) below frontier `Φ`. -/
abbrev Subst.AgreesBelow (Φ : Nat) (S T : Subst) : Prop :=
  ∀ v, v < Φ → S.onTy (.fvar v) = T.onTy (.fvar v)

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
  calc S₀.onTy (.fvar v)
      = (S₁ ++ R₁).onTy (.fvar v) := hag1 v hv
    _ = R₁.onTy (S₁.onTy (.fvar v)) := by rw [Subst.onTy_append]
    _ = (S₂ ++ R₂).onTy (S₁.onTy (.fvar v)) := Subst.onTy_congr hag2 hbv
    _ = ((S₁ ++ S₂) ++ R₂).onTy (.fvar v) := by
          rw [List.append_assoc, Subst.onTy_append S₁ (S₂ ++ R₂)]


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

/-- A predicate on the free de Bruijn indices actually used by an expression.
    `depth` excludes local binders; annotations do not affect term references. -/
def Expr.ForallOuter (P : Nat → Prop) (depth : Nat) (e : Expr) : Prop :=
  Expr.rec_strong (motive := fun _ => Nat → Prop)
    (fun _ _ => True) (fun _ _ => True)
    (fun _ _ ih d => ih (d + 1))
    (fun _ _ ihf iha d => ihf d ∧ iha d)
    (fun _ _ _ ihr ihb d => ihr d ∧ ihb (d + 1))
    (fun i d => d ≤ i → P (i - d))
    (fun _ _ => True)
    (fun _ _ ihs ihbr d =>
      ihs d ∧ ∀ pat body h, ihbr pat body h (d + pat.bindCount))
    (fun _ bindings _ ihbs ihb d =>
      (∀ rhs h, ihbs rhs h (d + bindings.length)) ∧ ihb (d + bindings.length)) e depth

theorem Expr.ForallOuter.mono {P Q : Nat → Prop} {depth : Nat} {e : Expr}
    (h : e.ForallOuter P depth) (hPQ : ∀ i, P i → Q i) : e.ForallOuter Q depth := by
  induction e using Expr.rec_strong generalizing depth with
  | primLit _ => simp only [Expr.ForallOuter, Expr.rec_strong] at h ⊢
  | primBinOp _ => simp only [Expr.ForallOuter, Expr.rec_strong] at h ⊢
  | ctor _ => simp only [Expr.ForallOuter, Expr.rec_strong] at h ⊢
  | var i => simp only [Expr.ForallOuter, Expr.rec_strong] at h ⊢; exact fun hd => hPQ _ (h hd)
  | lambda _ _ ih => simp only [Expr.ForallOuter, Expr.rec_strong] at h ⊢; exact ih h
  | app _ _ ihf iha => simp only [Expr.ForallOuter, Expr.rec_strong] at h ⊢; exact ⟨ihf h.1, iha h.2⟩
  | letIn _ _ _ ihr ihb => simp only [Expr.ForallOuter, Expr.rec_strong] at h ⊢; exact ⟨ihr h.1, ihb h.2⟩
  | match_ _ _ ihs ihbr => simp only [Expr.ForallOuter, Expr.rec_strong] at h ⊢; exact ⟨ihs h.1, fun p b hb => ihbr p b hb (h.2 p b hb)⟩
  | letRec _ _ _ ihbs ihb => simp only [Expr.ForallOuter, Expr.rec_strong] at h ⊢; exact ⟨fun rhs hrhs => ihbs rhs hrhs (h.1 rhs hrhs), ihb h.2⟩

theorem Expr.ForallOuter.prepend {P Q : Nat → Prop} {depth count : Nat} {e : Expr}
    (h : e.ForallOuter P (depth + count))
    (hbound : ∀ i, i < count → Q i) (houter : ∀ i, P i → Q (count + i)) :
    e.ForallOuter Q depth := by
  induction e using Expr.rec_strong generalizing depth with
  | primLit _ => simp only [Expr.ForallOuter, Expr.rec_strong] at h ⊢
  | primBinOp _ => simp only [Expr.ForallOuter, Expr.rec_strong] at h ⊢
  | ctor _ => simp only [Expr.ForallOuter, Expr.rec_strong] at h ⊢
  | var i =>
    simp only [Expr.ForallOuter, Expr.rec_strong] at h ⊢
    intro hi
    by_cases hib : i < depth + count
    · exact hbound (i - depth) (by omega)
    · have hout := houter (i - (depth + count)) (h (by omega))
      rwa [show count + (i - (depth + count)) = i - depth by omega] at hout
  | lambda _ _ ih =>
    simp only [Expr.ForallOuter, Expr.rec_strong] at h ⊢
    apply ih
    simpa only [Expr.ForallOuter, show depth + 1 + count = depth + count + 1 by omega] using h
  | app _ _ ihf iha => simp only [Expr.ForallOuter, Expr.rec_strong] at h ⊢; exact ⟨ihf h.1, iha h.2⟩
  | letIn _ _ _ ihr ihb =>
    simp only [Expr.ForallOuter, Expr.rec_strong] at h ⊢
    refine ⟨ihr h.1, ihb ?_⟩
    simpa only [Expr.ForallOuter, show depth + 1 + count = depth + count + 1 by omega] using h.2
  | match_ _ _ ihs ihbr =>
    simp only [Expr.ForallOuter, Expr.rec_strong] at h ⊢
    refine ⟨ihs h.1, fun p b hb => ihbr p b hb ?_⟩
    simpa only [Expr.ForallOuter, show depth + p.bindCount + count = depth + count + p.bindCount by omega] using h.2 p b hb
  | letRec _ bindings _ ihbs ihb =>
    simp only [Expr.ForallOuter, Expr.rec_strong] at h ⊢
    refine ⟨fun rhs hrhs => ihbs rhs hrhs ?_, ihb ?_⟩
    · simpa only [Expr.ForallOuter, show depth + bindings.length + count = depth + count + bindings.length by omega] using h.1 rhs hrhs
    · simpa only [Expr.ForallOuter, show depth + bindings.length + count = depth + count + bindings.length by omega] using h.2

theorem Expr.ForallOuter.substTyFvars {P : Nat → Prop} {depth : Nat} {e : Expr}
    (h : e.ForallOuter P depth) (S : Subst) : (e.substTyFvars S).ForallOuter P depth := by
  induction e using Expr.rec_strong generalizing depth with
  | primLit p => simp only [Expr.ForallOuter, Expr.rec_strong] at h ⊢; induction S <;> simp_all [Expr.substTyFvars, Expr.substTyFvar, Expr.rec_strong]
  | primBinOp p => simp only [Expr.ForallOuter, Expr.rec_strong] at h ⊢; induction S <;> simp_all [Expr.substTyFvars, Expr.substTyFvar, Expr.rec_strong]
  | ctor c => simp only [Expr.ForallOuter, Expr.rec_strong] at h ⊢; induction S <;> simp_all [Expr.substTyFvars, Expr.substTyFvar, Expr.rec_strong]
  | var i => simp only [Expr.ForallOuter, Expr.rec_strong] at h ⊢; simpa only [Expr.substTyFvars_var, Expr.rec_strong] using h
  | lambda ann body ih => simp only [Expr.ForallOuter, Expr.rec_strong] at h ⊢; rw [Expr.substTyFvars_lambda]; simp only [Expr.rec_strong]; exact ih h
  | app f arg ihf iha => simp only [Expr.ForallOuter, Expr.rec_strong] at h ⊢; rw [Expr.substTyFvars_app]; simp only [Expr.rec_strong]; exact ⟨ihf h.1, iha h.2⟩
  | letIn ann rhs body ihr ihb => simp only [Expr.ForallOuter, Expr.rec_strong] at h ⊢; rw [Expr.substTyFvars_letIn]; simp only [Expr.rec_strong]; exact ⟨ihr h.1, ihb h.2⟩
  | match_ scrut branches ihs ihbr =>
    simp only [Expr.ForallOuter, Expr.rec_strong] at h ⊢
    rw [Expr.substTyFvars_match]
    simp only [Expr.rec_strong]
    refine ⟨ihs h.1, ?_⟩
    intro p b hb
    obtain ⟨⟨p0, b0⟩, hb0, heq⟩ := List.mem_map.mp hb
    cases heq
    exact ihbr p0 b0 hb0 (h.2 p0 b0 hb0)
  | letRec anns bindings body ihbs ihb =>
    simp only [Expr.ForallOuter, Expr.rec_strong] at h ⊢
    rw [Expr.substTyFvars_letRec]
    simp only [Expr.rec_strong]
    change (∀ rhs ∈ bindings.map (Expr.substTyFvars S), rhs.ForallOuter P
      (depth + (bindings.map (Expr.substTyFvars S)).length)) ∧ _
    rw [List.length_map]
    refine ⟨?_, ihb h.2⟩
    intro rhs hrhs
    obtain ⟨old, hold, rfl⟩ := List.mem_map.mp hrhs
    exact ihbs old hold (h.1 old hold)

theorem Expr.ForallOuter.erase_iff {P : Nat → Prop} {depth : Nat} (e : Expr) :
    e.erase.ForallOuter P depth ↔ e.ForallOuter P depth := by
  induction e using Expr.rec_strong generalizing depth with
  | primLit _ => simp [Expr.ForallOuter, Expr.rec_strong, Expr.erase]
  | primBinOp _ => simp [Expr.ForallOuter, Expr.rec_strong, Expr.erase]
  | ctor _ => simp [Expr.ForallOuter, Expr.rec_strong, Expr.erase]
  | var _ => simp [Expr.ForallOuter, Expr.rec_strong]
  | lambda _ _ ih => simp only [Expr.erase_lambda, Expr.ForallOuter, Expr.rec_strong]; exact ih
  | app _ _ ihf iha => simp only [Expr.erase_app, Expr.ForallOuter, Expr.rec_strong]; exact and_congr ihf iha
  | letIn _ _ _ ihr ihb => simp only [Expr.erase_letIn, Expr.ForallOuter, Expr.rec_strong]; exact and_congr ihr ihb
  | match_ scrut branches ihs ihbr =>
    simp only [Expr.erase_match, Expr.ForallOuter, Expr.rec_strong]
    refine and_congr ihs ?_
    constructor
    · intro h p b hb
      exact (ihbr p b hb).mp (h p b.erase (List.mem_map.mpr ⟨(p,b), hb, rfl⟩))
    · intro h p b hb
      obtain ⟨⟨p0,b0⟩, hb0, heq⟩ := List.mem_map.mp hb
      cases heq
      exact (ihbr p0 b0 hb0).mpr (h p0 b0 hb0)
  | letRec anns bindings body ihbs ihb =>
    simp only [Expr.erase_letRec, Expr.ForallOuter, Expr.rec_strong, List.length_map]
    refine and_congr ?_ ihb
    constructor
    · intro h rhs hrhs
      exact (ihbs rhs hrhs).mp (h rhs.erase (List.mem_map.mpr ⟨rhs,hrhs,rfl⟩))
    · intro h rhs hrhs
      obtain ⟨old,hold,rfl⟩ := List.mem_map.mp hrhs
      exact (ihbs old hold).mpr (h old hold)

theorem Expr.ForallOuter.openTyVars {P : Nat → Prop} {depth : Nat} {e : Expr}
    (h : e.ForallOuter P depth) (Xs : List Nat) : (e.openTyVars Xs).ForallOuter P depth := by
  apply (Expr.ForallOuter.erase_iff _).mp
  rw [Expr.erase_openTyVars]
  exact (Expr.ForallOuter.erase_iff e).mpr h

theorem Expr.ForallOuter.openBoundTyVars {P : Nat → Prop} {depth : Nat} {e : Expr}
    (h : e.ForallOuter P depth) (ann : Option PolyTy) (Xs : List Nat) :
    (e.openBoundTyVars ann Xs).ForallOuter P depth := by
  apply (Expr.ForallOuter.erase_iff _).mp
  rw [Expr.erase_openBoundTyVars]
  exact (Expr.ForallOuter.erase_iff e).mpr h

/-- Avoidance at the environment slots a source expression actually reads is
    preserved when an avoiding substitution is threaded through the context. -/
theorem Expr.ForallOuter.lookupAvoid_onSubst {e : Expr} {depth w : Nat}
    {ctx : Ctx} {S : Subst}
    (h : e.ForallOuter
      (fun i => ∀ M, ctx.env[i]? = some M → w ∉ M.body.freeVars) depth)
    (hS : ∀ p ∈ S, w ∉ p.2.freeVars) :
    e.ForallOuter
      (fun i => ∀ M, (S.onCtx ctx).env[i]? = some M → w ∉ M.body.freeVars) depth := by
  apply h.mono
  intro i hi M hM
  simp only [Subst.onCtx, Subst.onEnv, List.getElem?_map] at hM
  cases hlookup : ctx.env[i]? with
  | none => simp [hlookup] at hM
  | some M₀ =>
    simp only [hlookup, Option.map_some, Option.some.injEq] at hM
    subst M
    simpa only [Subst.onPolyTy] using Subst.notMemOnTy hS (hi M₀ hlookup)

/-- Extend lookup-only avoidance under a prefix whose entries avoid `w`. -/
theorem Expr.ForallOuter.lookupAvoid_prepend {e : Expr} {depth w : Nat}
    {env pre : Env}
    (h : e.ForallOuter
      (fun i => ∀ M, env[i]? = some M → w ∉ M.body.freeVars)
      (depth + pre.length))
    (hpre : ∀ M ∈ pre, w ∉ M.body.freeVars) :
    e.ForallOuter
      (fun i => ∀ M, (pre ++ env)[i]? = some M → w ∉ M.body.freeVars)
      depth := by
  apply h.prepend
  · intro i hi M hM
    rw [List.getElem?_append_left hi] at hM
    exact hpre M (List.mem_of_getElem? hM)
  · intro i hi M hM
    rw [List.getElem?_append_right (by omega)] at hM
    exact hi M (by simpa using hM)

/-- The recursive stage prefix avoids `w` whenever its underlying specs do. -/
theorem RecSpecs.algorithmStageEntries_avoid {specs : List RecSpec} {w : Nat}
    (hspecs : ∀ s ∈ specs, w ∉ s.freeVars) (done G : List Nat) :
    ∀ M ∈ specs.mapIdx (RecSpec.algorithmStageEntry done G),
      w ∉ M.body.freeVars := by
  intro M hM
  obtain ⟨i, hi, rfl⟩ := List.mem_mapIdx.mp hM
  exact fun hc =>
    hspecs _ (List.getElem_mem hi) (RecSpec.algorithmStageEntry_freeVars_subset hc)

/-- Lookup-sensitive range, result, and domain locality for one inference. -/

private theorem UnifyRel.sourceAvoid {t u : Ty} {S : Subst} {w : Nat}
    (h : UnifyRel t u S) (ht : w ∉ t.freeVars) (hu : w ∉ u.freeVars) :
    (∀ p ∈ S, w ∉ p.2.freeVars) ∧ w ∉ S.map Prod.fst := by
  constructor
  · intro p hp hw
    exact (h.range_mem p hp w hw).elim ht hu
  · intro hw
    obtain ⟨p, hp, heq⟩ := List.mem_map.mp hw
    have hm := h.dom_mem p hp
    rw [heq] at hm
    exact hm.elim ht hu

private theorem Subst.sourceAvoid_append {S T : Subst} {w : Nat}
    (hS : (∀ p ∈ S, w ∉ p.2.freeVars) ∧ w ∉ S.map Prod.fst)
    (hT : (∀ p ∈ T, w ∉ p.2.freeVars) ∧ w ∉ T.map Prod.fst) :
    (∀ p ∈ S ++ T, w ∉ p.2.freeVars) ∧ w ∉ (S ++ T).map Prod.fst := by
  exact ⟨fun p hp => (List.mem_append.mp hp).elim (hS.1 p) (hT.1 p),
    by simpa only [List.map_append, List.mem_append, not_or] using And.intro hS.2 hT.2⟩

private theorem Expr.sourceLocality_size_mem {e : Expr} {es : List Expr} (h : e ∈ es) :
    e.size ≤ Expr.sizeRecGroup es := by
  induction es with
  | nil => simp at h
  | cons a es ih =>
    simp only [Expr.sizeRecGroup]
    rcases List.mem_cons.mp h with rfl | h
    · omega
    · have := ih h; omega

theorem RecGroupRefs.mem_branches {n depth i : Nat} {pat : MatchPattern} {body : Expr}
    {branches : List (MatchPattern × Expr)} (hb : (pat,body) ∈ branches)
    (hi : i ∈ body.recGroupRefs n (depth + pat.bindCount)) :
    i ∈ RecGroupRefs.branches n depth branches := by
  induction branches with
  | nil => simp at hb
  | cons pb rest ih =>
    simp only [RecGroupRefs.branches, List.mem_dedup, List.mem_append]
    rcases List.mem_cons.mp hb with heq | hb
    · cases heq; exact Or.inl hi
    · exact Or.inr (ih hb)

theorem RecGroupRefs.mem_bindings {n depth i : Nat} {rhs : Expr} {bindings : List Expr}
    (hb : rhs ∈ bindings) (hi : i ∈ rhs.recGroupRefs n depth) :
    i ∈ RecGroupRefs.bindings n depth bindings := by
  induction bindings with
  | nil => simp at hb
  | cons e rest ih =>
    simp only [RecGroupRefs.bindings, List.mem_dedup, List.mem_append]
    rcases List.mem_cons.mp hb with heq | hb
    · cases heq; exact Or.inl hi
    · exact Or.inr (ih hb)

theorem Expr.ForallOuter.of_recGroupRefs {P : Nat → Prop} {e : Expr} {n depth : Nat}
    (h : ∀ i ∈ e.recGroupRefs n depth, P i) :
    e.ForallOuter (fun i => i < n → P i) depth := by
  induction e using Expr.rec_strong generalizing depth with
  | primLit _ => simp [Expr.ForallOuter, Expr.rec_strong]
  | primBinOp _ => simp [Expr.ForallOuter, Expr.rec_strong]
  | ctor _ => simp [Expr.ForallOuter, Expr.rec_strong]
  | var i =>
    simp only [Expr.ForallOuter, Expr.rec_strong]
    intro hd hi
    apply h (i-depth)
    simp [Expr.recGroupRefs, hd, show i < depth+n by omega]
  | lambda _ _ ih =>
    simp only [Expr.ForallOuter, Expr.rec_strong]
    exact ih h
  | app _ _ ihf iha =>
    simp only [Expr.ForallOuter, Expr.rec_strong]
    refine ⟨ihf (fun i hi => h i ?_), iha (fun i hi => h i ?_)⟩
    · simpa only [Expr.recGroupRefs, List.mem_dedup, List.mem_append] using Or.inl hi
    · simpa only [Expr.recGroupRefs, List.mem_dedup, List.mem_append] using Or.inr hi
  | letIn _ _ _ ihr ihb =>
    simp only [Expr.ForallOuter, Expr.rec_strong]
    refine ⟨ihr (fun i hi => h i ?_), ihb (fun i hi => h i ?_)⟩
    · simpa only [Expr.recGroupRefs, List.mem_dedup, List.mem_append] using Or.inl hi
    · simpa only [Expr.recGroupRefs, List.mem_dedup, List.mem_append] using Or.inr hi
  | match_ scrut branches ihs ihbr =>
    simp only [Expr.ForallOuter, Expr.rec_strong]
    refine ⟨ihs (fun i hi => h i ?_), fun p b hb => ihbr p b hb (fun i hi => h i ?_)⟩
    · simpa only [Expr.recGroupRefs, List.mem_dedup, List.mem_append] using Or.inl hi
    · simp only [Expr.recGroupRefs, List.mem_dedup, List.mem_append]
      exact Or.inr (RecGroupRefs.mem_branches hb hi)
  | letRec anns bindings body ihbs ihb =>
    simp only [Expr.ForallOuter, Expr.rec_strong]
    refine ⟨fun rhs hrhs => ihbs rhs hrhs (fun i hi => h i ?_), ihb (fun i hi => h i ?_)⟩
    · simp only [Expr.recGroupRefs, List.mem_dedup, List.mem_append]
      exact Or.inl (RecGroupRefs.mem_bindings hrhs hi)
    · simpa only [Expr.recGroupRefs, List.mem_dedup, List.mem_append] using Or.inr hi

theorem Expr.recGroupRefs_substTyFvars (S : Subst) (e : Expr) (n depth : Nat) :
    (e.substTyFvars S).recGroupRefs n depth = e.recGroupRefs n depth := by
  induction e using Expr.rec_strong generalizing depth with
  | primLit p => induction S <;> simp_all [Expr.substTyFvars, Expr.substTyFvar, Expr.recGroupRefs]
  | primBinOp p => induction S <;> simp_all [Expr.substTyFvars, Expr.substTyFvar, Expr.recGroupRefs]
  | ctor c => induction S <;> simp_all [Expr.substTyFvars, Expr.substTyFvar, Expr.recGroupRefs]
  | var i => simp [Expr.substTyFvars_var]
  | lambda ann body ih => simp [Expr.substTyFvars_lambda, Expr.recGroupRefs, ih]
  | app f arg ihf iha => simp [Expr.substTyFvars_app, Expr.recGroupRefs, ihf, iha]
  | letIn ann rhs body ihr ihb => simp [Expr.substTyFvars_letIn, Expr.recGroupRefs, ihr, ihb]
  | match_ scrut branches ihs ihbr =>
    rw [Expr.substTyFvars_match]
    simp only [Expr.recGroupRefs, ihs]
    congr 2
    induction branches with
    | nil => rfl
    | cons pb rest ih =>
      simp only [List.map_cons, RecGroupRefs.branches]
      rw [ihbr pb.1 pb.2 List.mem_cons_self, ih (fun p b h => ihbr p b (List.mem_cons_of_mem _ h))]
  | letRec anns bindings body ihbs ihb =>
    rw [Expr.substTyFvars_letRec]
    simp only [Expr.recGroupRefs, List.length_map, ihb]
    congr 2
    generalize depth + bindings.length = innerDepth
    induction bindings generalizing innerDepth with
    | nil => rfl
    | cons rhs rest ih =>
      simp only [List.map_cons, RecGroupRefs.bindings]
      rw [ihbs rhs List.mem_cons_self, ih (fun e h => ihbs e (List.mem_cons_of_mem _ h)) innerDepth]

theorem RecGroups.ValidResidualGroups.map_bindings {anns anns' : List (Option PolyTy)}
    {bindings : List Expr} {groups : List (List Nat)}
    (h : RecGroups.ValidResidualGroups anns bindings groups) (f : Expr → Expr)
    (hlen : anns'.length = anns.length)
    (hu : ∀ i, RecGroups.UnsignedAt anns' i ↔ RecGroups.UnsignedAt anns i)
    (href : ∀ e ∈ bindings, (f e).recGroupRefs bindings.length 0 = e.recGroupRefs bindings.length 0) :
    RecGroups.ValidResidualGroups anns' (bindings.map f) groups := by
  refine ⟨by simpa using hlen.trans h.length, h.nonempty, h.flatten_nodup,
    by simpa using h.bounded, ?_, ?_⟩
  · intro member hm
    rw [List.length_map] at hm
    exact (h.covers_unsigned member hm).trans (hu member).symm
  · intro stage dependencyStage component dependencyComponent source target rhs
      hc hd hs ht hrhs href'
    rw [List.getElem?_map] at hrhs
    obtain ⟨old, hold, rfl⟩ := Option.map_eq_some_iff.mp hrhs
    apply h.dependencies_first hc hd hs ht hold
    rw [List.length_map, href old (List.mem_of_getElem? hold)] at href'
    exact href'

theorem RecGroups.ValidResidualGroups.substTyFvars {anns : List (Option PolyTy)}
    {bindings : List Expr} {groups : List (List Nat)}
    (h : RecGroups.ValidResidualGroups anns bindings groups) (S : Subst) :
    RecGroups.ValidResidualGroups (anns.map (RecAnn.substFvars S))
      (bindings.map (Expr.substTyFvars S)) groups := by
  apply h.map_bindings (Expr.substTyFvars S) (by simp)
  · intro i
    simp only [RecGroups.UnsignedAt, List.getElem?_map]
    cases anns[i]? with
    | none => simp
    | some ann => cases ann <;> simp
  · intro e _
    exact Expr.recGroupRefs_substTyFvars S e _ _

theorem Expr.recGroupRefs_shiftFrom (e : Expr) (n depth cutoff amount : Nat)
    (hcutoff : depth + n ≤ cutoff) :
    (e.shiftFrom cutoff amount).recGroupRefs n depth = e.recGroupRefs n depth := by
  induction e using Expr.rec_strong generalizing depth cutoff with
  | primLit p => rfl
  | primBinOp p => rfl
  | ctor c => rfl
  | var i =>
    simp only [Expr.shiftFrom]
    split
    · rfl
    · simp only [Expr.recGroupRefs]
      have hhi : ¬ i + amount < depth + n := by omega
      have hi : ¬ i < depth + n := by omega
      simp [hhi, hi]
  | lambda ann body ih => simp only [Expr.shiftFrom, Expr.recGroupRefs]; exact ih _ _ (by omega)
  | app f arg ihf iha => simp [Expr.shiftFrom, Expr.recGroupRefs, ihf _ _ hcutoff, iha _ _ hcutoff]
  | letIn ann rhs body ihr ihb =>
    simp [Expr.shiftFrom, Expr.recGroupRefs, ihr depth cutoff hcutoff,
      ihb (depth + 1) (cutoff + 1) (by omega)]
  | match_ scrut branches ihs ihbr =>
    simp only [Expr.shiftFrom, Expr.recGroupRefs, ihs _ _ hcutoff]
    congr 2
    induction branches with
    | nil => rfl
    | cons pb rest ih =>
      change ((pb.2.shiftFrom (cutoff + pb.1.bindCount) amount).recGroupRefs n
        (depth + pb.1.bindCount) ++ _).dedup = _
      simp only [RecGroupRefs.branches]
      rw [ihbr pb.1 pb.2 List.mem_cons_self _ _ (by omega),
        ih (fun p b h => ihbr p b (List.mem_cons_of_mem _ h))]
  | letRec anns bindings body ihbs ihb =>
    simp only [Expr.shiftFrom, RecGroup.shiftFrom_eq_map, Expr.recGroupRefs, List.length_map,
      ihb (depth + bindings.length) (cutoff + bindings.length) (by omega)]
    congr 2
    generalize hd : depth + bindings.length = innerDepth
    generalize hc : cutoff + bindings.length = innerCutoff
    have hinner : innerDepth + n ≤ innerCutoff := by omega
    clear hd hc hcutoff
    induction bindings generalizing innerDepth innerCutoff with
    | nil => rfl
    | cons rhs rest ih =>
      simp only [List.map_cons, RecGroupRefs.bindings]
      rw [ihbs rhs List.mem_cons_self _ _ hinner,
        ih (fun e h => ihbs e (List.mem_cons_of_mem _ h)) innerDepth innerCutoff hinner]

theorem RecGroups.ValidResidualGroups.shiftFrom {anns : List (Option PolyTy)}
    {bindings : List Expr} {groups : List (List Nat)}
    (h : RecGroups.ValidResidualGroups anns bindings groups) (cutoff amount : Nat)
    (hc : bindings.length ≤ cutoff) :
    RecGroups.ValidResidualGroups anns (bindings.map (Expr.shiftFrom cutoff amount)) groups := by
  apply h.map_bindings (Expr.shiftFrom cutoff amount) rfl (fun _ => Iff.rfl)
  intro e _
  exact Expr.recGroupRefs_shiftFrom e _ _ cutoff amount (by simpa using hc)

/-- Strong induction principle for `TypeOfHM`, packaged with a single motive. -/
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
      {specs : List RecSpec} {groups : List (List Nat)} {G L : List Nat} {body : Expr} {ρ : Ty}
      (hvalid : RecGroups.ValidResidualGroups anns bindings groups)
      (hwf : RecSpecs.WF anns bindings specs G)
      (hmono : RecSpecs.StratifiedMonoTyped TypeOfHM ctx bindings specs groups G L)
      (hpoly : RecSpecs.PolyTypedFinal TypeOfHM ctx bindings specs G L)
      (heq : bodyCtx = RecSpecs.bodyCtx ctx specs G)
      (hbody : TypeOfHM bodyCtx body ρ),
      (∀ stage component (hc : groups[stage]? = some component)
          Xs (hf : FreshNames L G.length Xs) member (hm : member ∈ component) rhs τ
          (hrhs : bindings[member]? = some rhs) (hτ : specs[member]? = some (.mono τ)),
        motive (RecSpecs.stageCtx ctx specs (groups.take stage).flatten G Xs)
          rhs (Ty.renameG G Xs τ) (hmono stage component hc Xs hf member hm rhs τ hrhs hτ)) →
      (∀ p (hp : p ∈ bindings.zip specs) σ (hσ : p.2 = .poly σ)
          Ys (hfY : FreshNames L σ.paramCount Ys),
        motive (RecSpecs.bodyCtx ctx specs G)
          (p.1.openTyVars Ys) (σ.openVars Ys) (hpoly p hp σ hσ Ys hfY)) →
      motive bodyCtx body ρ hbody →
      motive ctx (.letRec anns bindings body) ρ (.letRec hvalid hwf hmono hpoly heq hbody))
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

theorem Expr.ForallOuter.prepend_env {env env' pre : Env} {e : Expr} {depth : Nat}
    (h : e.ForallOuter (fun i => env'[i]? = env[i]?) (depth + pre.length)) :
    e.ForallOuter (fun i => (pre ++ env')[i]? = (pre ++ env)[i]?) depth := by
  apply h.prepend
  · intro i hi
    rw [List.getElem?_append_left hi, List.getElem?_append_left hi]
  · intro i hi
    rw [List.getElem?_append_right (by omega), List.getElem?_append_right (by omega)]
    simpa using hi

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
    · intro stage component hc Xs hf member hm rhs τ hrhs hτ
      apply ihmono stage component hc Xs hf member hm rhs τ hrhs hτ
      apply Expr.ForallOuter.prepend_env
      simpa only [List.length_mapIdx, Nat.zero_add, hwf.length] using
        hag.1 rhs (List.mem_of_getElem? hrhs)
    · intro p hp σ hσ Ys hYs
      apply ihpoly p hp σ hσ Ys hYs
      apply Expr.ForallOuter.prepend_env
      have h := Expr.ForallOuter.openTyVars (e := p.1) (depth := bindings.length)
        (P := fun i => env'[i]? = ctx_1.env[i]?)
        (hag.1 p.1 (List.of_mem_zip hp).1) Ys
      simpa only [List.length_map, Nat.zero_add, hwf.length] using h
    · apply ihbody
      apply Expr.ForallOuter.prepend_env
      simpa only [List.length_map, Nat.zero_add, hwf.length] using hag.2

/-! Local copies of Core-private auxiliary lemmas needed by the recursive-group
case of `typ_subst_preservation_uniform`. -/

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
    Lets the `match_` and `letRec` cases use the public
    `Expr.substTyFvars_*` structural lemmas instead of the Core-private single-fvar
    list helpers. -/
private theorem Expr.substTyFvar_eq_substTyFvars_single {Z : Nat} {U : Ty} {e : Expr} :
    Expr.substTyFvar Z U e = Expr.substTyFvars [(Z, U)] e := rfl

/-- Replacing `Z` by a fresh proxy `Y` and then restoring `Y` recovers the
    original type. This protects arbitrary instantiation arguments while a
    substitution is transported through `Generalizes`. -/
private theorem Ty.substFvar_proxy_roundtrip {Z Y : Nat} {t : Ty}
    (hY : Y ∉ t.freeVars) :
    Ty.substFvar Y (.fvar Z) (Ty.substFvar Z (.fvar Y) t) = t := by
  induction t using Ty.rec_strong with
  | prim p => rfl
  | bvar i => rfl
  | fvar n =>
      simp only [Ty.freeVars, List.mem_singleton] at hY
      by_cases hnZ : n = Z
      · subst n
        simp [Ty.substFvar]
      · have hnY : n ≠ Y := fun h => hY h.symm
        simp [Ty.substFvar, hnZ, hnY]
  | arrow a b iha ihb =>
      simp only [Ty.freeVars, List.mem_dedup, List.mem_append, not_or] at hY
      simp only [Ty.substFvar, Ty.arrow.injEq]
      exact ⟨iha hY.1, ihb hY.2⟩
  | customTy nm tys ih =>
      have hYall : ∀ t ∈ tys, Y ∉ t.freeVars := TyList.not_mem_freeVars_iff.mp hY
      simp only [Ty.substFvar, TyList.substFvar_eq_map, List.map_map,
        Ty.customTy.injEq, true_and]
      conv_rhs => rw [← List.map_id tys]
      apply List.map_congr_left
      intro t ht
      simpa [Function.comp_apply] using ih t ht (hYall t ht)

/-- `substFvar` commutes with arbitrary type-argument opening. -/
private theorem Ty.substFvar_openWith {Z : Nat} {U : Ty} (hU : U.IsLC)
    (Vs : List Ty) (X : Ty) :
    Ty.substFvar Z U (Ty.openWith Vs X) =
      Ty.openWith (Vs.map (Ty.substFvar Z U)) (Ty.substFvar Z U X) := by
  simpa [Subst.onTy, Ty.substFvars] using
    (Subst.onTy_openWith (S := [(Z, U)])
      (by intro p hp; simp only [List.mem_singleton] at hp; subst p; exact hU) Vs X)

/-- Generality is stable under an LC free-variable substitution. The fresh
    proxy is essential: instantiation arguments themselves may contain the
    substituted variable. -/
theorem PolyTy.Generalizes.substFvar {A B : PolyTy} {Z : Nat} {U : Ty}
    (h : A.Generalizes B) (hBwf : B.WF) (hU : U.IsLC) :
    (A.substFvar Z U).Generalizes (B.substFvar Z U) := by
  intro args ty hargs hinst
  let Vs := (List.range B.paramCount).map
    (fun i => (args[i]?).getD (.prim .unit))
  have hty : ty = Ty.openWith Vs (Ty.substFvar Z U B.body) := by
    simpa [Vs, PolyTy.substFvar] using
      hinst.eq_openWith_range (PolyTy.WF.substFvar hU hBwf)
  have hVslen : Vs.length = B.paramCount := by simp [Vs]
  have hVslc : ∀ v ∈ Vs, v.IsLC := by
    intro v hv
    dsimp [Vs] at hv
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp hv
    cases hi : args[i]? with
    | none => exact .prim
    | some t => exact hargs t (List.mem_of_getElem? hi)
  obtain ⟨Ys, hYslen, _hYsnodup, hYsavoid⟩ :=
    exists_fresh_names
      ([Z] ++ U.freeVars ++ A.body.freeVars ++ B.body.freeVars ++ Vs.flatMap Ty.freeVars) 1
  obtain ⟨Y, rfl⟩ : ∃ Y, Ys = [Y] := List.length_eq_one_iff.mp hYslen
  have hYavoid : Y ∉ [Z] ++ U.freeVars ++ A.body.freeVars ++ B.body.freeVars ++
      Vs.flatMap Ty.freeVars := hYsavoid Y List.mem_cons_self
  have hYZ : Y ≠ Z := by
    intro hEq
    exact hYavoid (by simp [hEq])
  have hYU : Y ∉ U.freeVars := by
    intro hmem
    exact hYavoid (by simp [List.mem_append, hmem])
  have hYA : Y ∉ A.body.freeVars := by
    intro hmem
    exact hYavoid (by simp [List.mem_append, hmem])
  have hYB : Y ∉ B.body.freeVars := by
    intro hmem
    exact hYavoid (by simp [List.mem_append, hmem])
  have hYVs : ∀ v ∈ Vs, Y ∉ v.freeVars := by
    intro v hv hmem
    have hflat : Y ∈ Vs.flatMap Ty.freeVars := by
      rw [List.mem_flatMap]
      exact ⟨v, hv, hmem⟩
    exact hYavoid (by
      simp only [List.mem_append]
      exact Or.inr hflat)
  let Vs0 := Vs.map (Ty.substFvar Z (.fvar Y))
  have hVs0lc : ∀ v ∈ Vs0, v.IsLC := by
    intro v hv
    obtain ⟨v0, hv0, rfl⟩ := List.mem_map.mp hv
    exact Ty.IsLC.substFvar .fvar (hVslc v0 hv0)
  have hinst0 : InstantiatesBy Vs0 B.body (Ty.openWith Vs0 B.body) :=
    InstantiatesBy.openWith hBwf (by simp [Vs0, hVslen])
  obtain ⟨Ws, hWlc, hWinst⟩ := h Vs0 _ hVs0lc hinst0
  have h1 := InstantiatesBy.substFvar (Z := Z) (U := U) hU hWinst
  have h2 := InstantiatesBy.substFvar (Z := Y) (U := .fvar Z) ContainsBvarsUpTo.fvar h1
  have hYA_sub : Y ∉ (Ty.substFvar Z U A.body).freeVars := by
    intro hmem
    rcases Ty.mem_freeVars_substFvar hmem with hmem | hmem
    · exact hYA hmem
    · exact hYU hmem
  rw [Ty.substFvar_fresh hYA_sub] at h2
  have hVs0_Z : Vs0.map (Ty.substFvar Z U) = Vs0 := by
    conv_rhs => rw [← List.map_id Vs0]
    apply List.map_congr_left
    intro v hv
    dsimp [Vs0] at hv
    obtain ⟨v0, _hv0, rfl⟩ := List.mem_map.mp hv
    apply Ty.substFvar_fresh
    exact Ty.not_mem_freeVars_substFvar_self
      (by simpa [Ty.freeVars] using Ne.symm hYZ)
  have hVs0_restore : Vs0.map (Ty.substFvar Y (.fvar Z)) = Vs := by
    dsimp [Vs0]
    rw [List.map_map]
    conv_rhs => rw [← List.map_id Vs]
    apply List.map_congr_left
    intro v hv
    exact Ty.substFvar_proxy_roundtrip (hYVs v hv)
  have hYB_sub : Y ∉ (Ty.substFvar Z U B.body).freeVars := by
    intro hmem
    rcases Ty.mem_freeVars_substFvar hmem with hmem | hmem
    · exact hYB hmem
    · exact hYU hmem
  refine ⟨(Ws.map (Ty.substFvar Z U)).map (Ty.substFvar Y (.fvar Z)), ?_, ?_⟩
  · intro w hw
    obtain ⟨w1, hw1, rfl⟩ := List.mem_map.mp hw
    obtain ⟨w0, hw0, rfl⟩ := List.mem_map.mp hw1
    exact Ty.IsLC.substFvar .fvar (Ty.IsLC.substFvar hU (hWlc w0 hw0))
  · rw [Ty.substFvar_openWith hU, hVs0_Z,
      Ty.substFvar_openWith ContainsBvarsUpTo.fvar, hVs0_restore,
      Ty.substFvar_fresh hYB_sub] at h2
    rwa [← hty] at h2

/-- Generality is stable under an LC substitution applied to both schemes. -/
theorem PolyTy.Generalizes.onSubst {A B : PolyTy} {S : Subst}
    (h : A.Generalizes B) (hBwf : B.WF) (hS : ∀ p ∈ S, p.2.IsLC) :
    (S.onPolyTy A).Generalizes (S.onPolyTy B) := by
  induction S generalizing A B with
  | nil => simpa using h
  | cons p S ih =>
      obtain ⟨Z, U⟩ := p
      have hU := hS (Z, U) List.mem_cons_self
      have hstep := PolyTy.Generalizes.substFvar (Z := Z) (U := U) h hBwf hU
      have hBwf' := PolyTy.WF.substFvar (Z := Z) (U := U) hU hBwf
      have hrest := ih hstep hBwf' (fun p hp => hS p (List.mem_cons_of_mem _ hp))
      simpa [Subst.onPolyTy, Subst.onTy, Ty.substFvars] using hrest

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
      ⟨?_, ?_, hWnodup, ?_, ?_⟩ ?_ ?_ rfl ?_
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
    · -- UNANNOTATED members: the historical `letRec` transport
      intro stage component hc Xs hfresh member hm rhs τ' hrhs hτ'
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
      rw [List.getElem?_map] at hrhs hτ'
      obtain ⟨a, ha, rfl⟩ := Option.map_eq_some_iff.mp hrhs
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
      obtain ⟨a, b, hab, rfl⟩ := List.mem_zip_map hp
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
        have hu : RecGroups.UnsignedAt anns member := by
          rw [RecGroups.UnsignedAt, ← hwf.anns_eq, List.getElem?_map, hspec]
          rfl
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

private theorem Ctor.IsBoolCtor.typeOfHM_direct {ctx : Ctx} {name : CtorName} {c : Ctor}
    (hlook : LookupList.get? ctx.ctors name = some c) (hb : c.IsBoolCtor) :
    TypeOfHM ctx (.ctor name) (.customTy ⟨"Bool"⟩ []) :=
  Ctor.IsBoolCtor.typeOfHM hlook hb

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
    {anns : List (Option PolyTy)} {bs : List Expr} {specs : List RecSpec}
    {groups : List (List Nat)}
    {body : Expr} {ρ : Ty}
    (hvalid : RecGroups.ValidResidualGroups anns bs groups)
    (hwf : RecSpecs.WF anns bs specs G)
    (hG_env : ∀ g ∈ G, g ∉ ctx.env.freeVars)
    (hG_specs : ∀ g ∈ G, ∀ σ, RecSpec.poly σ ∈ specs → g ∉ σ.body.freeVars)
    (hG_bs : ∀ g ∈ G, ∀ e ∈ bs, g ∉ e.tyFreeVars)
    (hmono : ∀ stage component, groups[stage]? = some component →
      ∀ member ∈ component, ∀ rhs τ,
      bs[member]? = some rhs → specs[member]? = some (.mono τ) →
      TypeOfHM (RecSpecs.algorithmStageCtx ctx specs (groups.take stage).flatten G) rhs τ)
    (hpoly : ∀ p ∈ bs.zip specs, ∀ σ, p.2 = RecSpec.poly σ →
      ∀ Ys, FreshNames Lp σ.paramCount Ys →
        TypeOfHM (RecSpecs.bodyCtx ctx specs G)
          (p.1.openTyVars Ys) (σ.openVars Ys))
    (hbody : TypeOfHM (RecSpecs.bodyCtx ctx specs G) body ρ) :
    TypeOfHM ctx (Expr.letRec anns bs body) ρ := by
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
  · intro stage component hc Xs hXs member hm rhs τ hrhs hτ
    have hctx := hctx_eq (groups.take stage).flatten Xs
    have hsrc := hmono stage component hc member hm rhs τ hrhs hτ
    have hLC : ∀ q ∈ G.zip (Xs.map (Ty.fvar ·)), q.2.IsLC := by
      intro q hq
      obtain ⟨x, hx, hxeq⟩ := List.mem_map.mp (List.of_mem_zip hq).2
      rw [← hxeq]; exact ContainsBvarsUpTo.fvar
    have hfix : rhs.substTyFvars (G.zip (Xs.map (Ty.fvar ·))) = rhs :=
      Expr.substTyFvars_eq_self_of_not_mem_tyFreeVars (fun q hq hc =>
        hG_bs q.1 (List.of_mem_zip hq).1 rhs (List.mem_of_getElem? hrhs) hc)
    have hren := TypeOfHM.onSubst_fixed (G.zip (Xs.map (Ty.fvar ·))) hLC hfix hsrc
    rw [hctx] at hren
    simpa [Subst.onTy, Ty.renameG] using hren
  · intro p hp σ hσ Ys hYs
    have hYs' : FreshNames Lp σ.paramCount Ys := by
      refine ⟨hYs.length, hYs.nodup, ?_⟩
      intro y hy hc
      exact hYs.avoid y hy (List.mem_append_left G hc)
    exact hpoly p hp σ hσ Ys hYs'

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
/-- Like `UnifyRel.greatest`, but the residual `R` is also LC when `S'` is. -/
theorem UnifyRel.greatest_lc : {τ₁ τ₂ : Ty} → {S : Subst} → UnifyRel τ₁ τ₂ S →
    ∀ S' : Subst, (∀ p ∈ S', p.2.IsLC) → Unifies S' τ₁ τ₂ →
    ∃ R : Subst, (∀ τ, S'.onTy τ = R.onTy (S.onTy τ)) ∧ (∀ p ∈ R, p.2.IsLC)
  | _, _, _, .prim, S', hlc, _ => ⟨S', fun τ => by simp only [Subst.onTy_nil], hlc⟩
  | _, _, _, .fvarRefl, S', hlc, _ => ⟨S', fun τ => by simp only [Subst.onTy_nil], hlc⟩
  | _, _, _, .fvarL _ _, S', hlc, hS' => ⟨S', fun τ => (Subst.onTy_substFvar hS' τ).symm, hlc⟩
  | _, _, _, .fvarR _ _, S', hlc, hS' => ⟨S', fun τ => (Subst.onTy_substFvar (Eq.symm hS') τ).symm, hlc⟩
  | _, _, _, @UnifyRel.arrow a b c d S₁ S₂ h₁ h₂, S', hlc, hS' => by
    simp only [Unifies, Subst.onTy_arrow, Ty.arrow.injEq] at hS'
    obtain ⟨hac, hbd⟩ := hS'
    obtain ⟨R₁, hR₁, hR₁lc⟩ := UnifyRel.greatest_lc h₁ S' hlc hac
    have hR₁bd : Unifies R₁ (S₁.onTy b) (S₁.onTy d) := by
      show R₁.onTy (S₁.onTy b) = R₁.onTy (S₁.onTy d)
      rw [← hR₁ b, ← hR₁ d]; exact hbd
    obtain ⟨R₂, hR₂, hR₂lc⟩ := UnifyRel.greatest_lc h₂ R₁ hR₁lc hR₁bd
    exact ⟨R₂, fun τ => by rw [Subst.onTy_append, ← hR₂ (S₁.onTy τ), hR₁ τ], hR₂lc⟩
  | _, _, _, .customTy hl, S', hlc, hS' => by
    simp only [Unifies, Subst.onTy_customTy, Ty.customTy.injEq, true_and] at hS'
    exact UnifyRelList.greatest_lc hl S' hlc hS'

theorem UnifyRelList.greatest_lc : {ts₁ ts₂ : List Ty} → {S : Subst} →
    UnifyRelList ts₁ ts₂ S → ∀ S' : Subst, (∀ p ∈ S', p.2.IsLC) →
      ts₁.map S'.onTy = ts₂.map S'.onTy →
      ∃ R : Subst, (∀ τ, S'.onTy τ = R.onTy (S.onTy τ)) ∧ (∀ p ∈ R, p.2.IsLC)
  | _, _, _, .nil, S', hlc, _ => ⟨S', fun τ => by simp only [Subst.onTy_nil], hlc⟩
  | _, _, _, @UnifyRelList.cons t₁ t₂ ts₁ ts₂ S₁ S₂ h₁ ht, S', hlc, hS' => by
    simp only [List.map_cons, List.cons.injEq] at hS'
    obtain ⟨ht1t2, htail⟩ := hS'
    obtain ⟨R₁, hR₁, hR₁lc⟩ := UnifyRel.greatest_lc h₁ S' hlc ht1t2
    have key : ∀ (l : List Ty), l.map (R₁.onTy ∘ S₁.onTy) = l.map S'.onTy := by
      intro l; apply List.map_congr_left; intro t _; exact (hR₁ t).symm
    have hlist : (ts₁.map S₁.onTy).map R₁.onTy = (ts₂.map S₁.onTy).map R₁.onTy := by
      rw [List.map_map, List.map_map, key, key]; exact htail
    obtain ⟨R₂, hR₂, hR₂lc⟩ := UnifyRelList.greatest_lc ht R₁ hR₁lc hlist
    exact ⟨R₂, fun τ => by rw [Subst.onTy_append, ← hR₂ (S₁.onTy τ), hR₁ τ], hR₂lc⟩
end

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
/-- `greatest_lc` augmented: the residual `R` also fixes every `k ∈ K` whenever
    the witness `S'` does. -/
theorem UnifyRel.greatest_K {K : List Nat} :
    {τ₁ τ₂ : Ty} → {S : Subst} → UnifyRel τ₁ τ₂ S →
    ∀ S' : Subst, (∀ p ∈ S', p.2.IsLC) → Unifies S' τ₁ τ₂ →
    (∀ k ∈ K, S'.onTy (.fvar k) = .fvar k) →
    ∃ R : Subst, (∀ τ, S'.onTy τ = R.onTy (S.onTy τ)) ∧ (∀ p ∈ R, p.2.IsLC) ∧
      (∀ k ∈ K, R.onTy (.fvar k) = .fvar k)
  | _, _, _, .prim, S', hlc, _, hK => ⟨S', fun τ => by simp only [Subst.onTy_nil], hlc, hK⟩
  | _, _, _, .fvarRefl, S', hlc, _, hK => ⟨S', fun τ => by simp only [Subst.onTy_nil], hlc, hK⟩
  | _, _, _, .fvarL _ _, S', hlc, hS', hK =>
    ⟨S', fun τ => (Subst.onTy_substFvar hS' τ).symm, hlc, hK⟩
  | _, _, _, .fvarR _ _, S', hlc, hS', hK =>
    ⟨S', fun τ => (Subst.onTy_substFvar (Eq.symm hS') τ).symm, hlc, hK⟩
  | _, _, _, @UnifyRel.arrow a b c d S₁ S₂ h₁ h₂, S', hlc, hS', hK => by
    simp only [Unifies, Subst.onTy_arrow, Ty.arrow.injEq] at hS'
    obtain ⟨hac, hbd⟩ := hS'
    obtain ⟨R₁, hR₁, hR₁lc, hR₁K⟩ := UnifyRel.greatest_K h₁ S' hlc hac hK
    have hR₁bd : Unifies R₁ (S₁.onTy b) (S₁.onTy d) := by
      show R₁.onTy (S₁.onTy b) = R₁.onTy (S₁.onTy d)
      rw [← hR₁ b, ← hR₁ d]; exact hbd
    obtain ⟨R₂, hR₂, hR₂lc, hR₂K⟩ := UnifyRel.greatest_K h₂ R₁ hR₁lc hR₁bd hR₁K
    exact ⟨R₂, fun τ => by rw [Subst.onTy_append, ← hR₂ (S₁.onTy τ), hR₁ τ], hR₂lc, hR₂K⟩
  | _, _, _, .customTy hl, S', hlc, hS', hK => by
    simp only [Unifies, Subst.onTy_customTy, Ty.customTy.injEq, true_and] at hS'
    exact UnifyRelList.greatest_K hl S' hlc hS' hK
theorem UnifyRelList.greatest_K {K : List Nat} :
    {ts₁ ts₂ : List Ty} → {S : Subst} → UnifyRelList ts₁ ts₂ S →
    ∀ S' : Subst, (∀ p ∈ S', p.2.IsLC) → ts₁.map S'.onTy = ts₂.map S'.onTy →
    (∀ k ∈ K, S'.onTy (.fvar k) = .fvar k) →
    ∃ R : Subst, (∀ τ, S'.onTy τ = R.onTy (S.onTy τ)) ∧ (∀ p ∈ R, p.2.IsLC) ∧
      (∀ k ∈ K, R.onTy (.fvar k) = .fvar k)
  | _, _, _, .nil, S', hlc, _, hK => ⟨S', fun τ => by simp only [Subst.onTy_nil], hlc, hK⟩
  | _, _, _, @UnifyRelList.cons t₁ t₂ ts₁ ts₂ S₁ S₂ h₁ ht, S', hlc, hS', hK => by
    simp only [List.map_cons, List.cons.injEq] at hS'
    obtain ⟨ht1t2, htail⟩ := hS'
    obtain ⟨R₁, hR₁, hR₁lc, hR₁K⟩ := UnifyRel.greatest_K h₁ S' hlc ht1t2 hK
    have key : ∀ (l : List Ty), l.map (R₁.onTy ∘ S₁.onTy) = l.map S'.onTy := by
      intro l; apply List.map_congr_left; intro t _; exact (hR₁ t).symm
    have hlist : (ts₁.map S₁.onTy).map R₁.onTy = (ts₂.map S₁.onTy).map R₁.onTy := by
      rw [List.map_map, List.map_map, key, key]; exact htail
    obtain ⟨R₂, hR₂, hR₂lc, hR₂K⟩ := UnifyRelList.greatest_K ht R₁ hR₁lc hlist hR₁K
    exact ⟨R₂, fun τ => by rw [Subst.onTy_append, ← hR₂ (S₁.onTy τ), hR₁ τ], hR₂lc, hR₂K⟩
end

/-! A structural size on types (own measure; cleaner than `sizeOf` for the
    unification termination argument). -/
mutual
def Ty.size : Ty → Nat
  | .prim _ => 1
  | .bvar _ => 1
  | .fvar _ => 1
  | .arrow a b => 1 + a.size + b.size
  | .customTy _ tys => 1 + TyList.size tys
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

/-! ### Scheme weakening (for the `letIn` principality case)

The algorithm generalises the rhs's principal type with `genScheme`, the
*maximal* generalisation; the declarative scheme `M` is less general. Giving the
let-bound variable a more general scheme preserves typing: every instance the
body used is still available. `PolyTy.Generalizes` states that every instance
of the original scheme is also an instance of its replacement. -/

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
      ⟨hwf.anns_eq, ?_, hwf.nodup, hwf.mono_lc, hwf.poly_wf⟩ ?_ ?_ rfl ?_
    · rw [List.length_map]; exact hwf.length
    · intro stage component hcomponent Xs hfresh member hm rhs τ hrhs hτ
      rw [List.getElem?_map] at hrhs
      obtain ⟨a, ha, rfl⟩ := Option.map_eq_some_iff.mp hrhs
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
    (h_exh : SmallStep.AllMatchesExhaustive ctx.ctors e) (h_erased : e.erase = e) :
    SmallStep.IsValue e ∨ ∃ e', SmallStep.Step e e' := by
  have hrun := TypeOfHM.erase_preserves_typing h_ty
  rw [h_erased] at hrun
  exact RuntimeTyping.RunWT.progress hrun h_closed h_exh h_erased

/-! ### Preservation and type safety

Source checking erases into `RuntimeTyping.RunWT`; runtime subject reduction
then carries the source type through evaluation. Both the erased-input
compatibility statements and the annotated-source safety statements appear below. -/

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
        simp only [Expr.shiftFrom]
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
        simp only [Expr.substN]
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

/-- Term-variable shifting preserves `TyBvarBounded`: it renames term variables
    without changing type annotations. -/
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


set_option maxRecDepth 10_000 in
theorem PolyTy.genGroup_append_of_avoid {G H : List Nat} {τ : Ty}
    (hH : ∀ g ∈ H, g ∉ τ.freeVars) :
    PolyTy.genGroup (G ++ H) τ = PolyTy.genGroup G τ := by
  have hf : H.filter (fun g => decide (g ∈ τ.freeVars)) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro g hg
    simp [hH g hg]
  simp only [PolyTy.genGroup, Ty.genFilter, List.filter_append, hf, List.append_nil]

theorem Ty.mem_closeOver_freeVars_of_notMem_pool {G : List Nat} {τ : Ty} {g : Nat}
    (hlc : τ.IsLC) (hg : g ∈ τ.freeVars) (hG : g ∉ G) :
    g ∈ (Ty.closeOver G τ).freeVars := by
  have hopen : g ∈ (Ty.openVars G (Ty.closeOver G τ)).freeVars := by
    rwa [Ty.openVars_closeOver_self hlc]
  rcases Ty.freeVars_openVars_subset g hopen with h | h
  · exact h
  · exact False.elim (hG h)

theorem RecSpecs.genGroup_mem_fixedSchemes {specs : List RecSpec} {done G : List Nat}
    {member : Nat} {τ : Ty} (hspec : specs[member]? = some (.mono τ))
    (hdone : member ∈ done) : PolyTy.genGroup G τ ∈ RecSpecs.fixedSchemes specs done G := by
  unfold RecSpecs.fixedSchemes
  apply List.mem_filterMap.mpr
  refine ⟨some (PolyTy.genGroup G τ), ?_, rfl⟩
  apply List.mem_of_getElem? (i := member)
  rw [List.getElem?_mapIdx, hspec]
  simp [hdone]

theorem RecSpecs.newPool_avoids_done {rigid G done : List Nat} {ctx : Ctx}
    {specs : List RecSpec} {component : List Nat} {member g : Nat} {τ : Ty}
    (hlc : τ.IsLC) (hspec : specs[member]? = some (.mono τ)) (hdone : member ∈ done)
    (hg : g ∈ genGroupVars (rigid ++ G)
      (RecSpecs.generalizationCtx ctx specs done G).env (RecSpecs.monoTysAt specs component)) :
    g ∉ τ.freeVars := by
  have hs := genGroupVars_spec hg
  have hgG : g ∉ G := fun h => hs.2.2 (List.mem_append_right _ h)
  intro hc
  apply hs.2.1
  apply Env.mem_freeVars_iff.mpr
  refine ⟨PolyTy.genGroup G τ, ?_, ?_⟩
  · exact List.mem_append_left _ (RecSpecs.genGroup_mem_fixedSchemes hspec hdone)
  · exact Ty.mem_closeOver_freeVars_of_notMem_pool hlc hc
      (fun h => hgG (Ty.mem_of_mem_genFilter h))

theorem RecGroups.ValidResidualGroups.refs_available {anns : List (Option PolyTy)}
    {bindings : List Expr} {groups : List (List Nat)} {specs : List RecSpec}
    {stage source target : Nat} {component : List Nat} {rhs : Expr} {τ : Ty}
    (hvalid : RecGroups.ValidResidualGroups anns bindings groups)
    (hanns : specs.map RecSpec.ann = anns) (hlen : bindings.length = specs.length)
    (hc : groups[stage]? = some component) (hs : source ∈ component)
    (hrhs : bindings[source]? = some rhs) (ht : specs[target]? = some (.mono τ))
    (href : target ∈ rhs.recGroupRefs bindings.length 0) :
    target ∈ (groups.take stage).flatten ∨ target ∈ component := by
  have htlt : target < bindings.length := by
    rw [hlen]
    exact (List.getElem?_eq_some_iff.mp ht).1
  have hunsigned : RecGroups.UnsignedAt anns target := by
    rw [RecGroups.UnsignedAt, ← hanns, List.getElem?_map, ht]
    rfl
  have htflat := (hvalid.covers_unsigned target htlt).mpr hunsigned
  obtain ⟨dep, hdep, htdep⟩ := List.mem_flatten.mp htflat
  obtain ⟨dependencyStage, hdep⟩ := List.mem_iff_getElem?.mp hdep
  have hle := hvalid.dependencies_first hc hdep hs htdep hrhs href
  by_cases heq : dependencyStage = stage
  · subst dependencyStage
    have := Option.some.inj (hdep.symm.trans hc)
    subst dep
    exact Or.inr htdep
  · apply Or.inl
    apply List.mem_flatten.mpr
    refine ⟨dep, List.mem_iff_getElem?.mpr ⟨dependencyStage, ?_⟩, htdep⟩
    rw [List.getElem?_take, if_pos (by omega)]
    exact hdep

theorem RecSpecs.algorithmStageCtx_onSubst {S : Subst} {ctx : Ctx}
    {specs : List RecSpec} {done G : List Nat}
    (hdom : ∀ p ∈ S, p.1 ∉ G) (hran : ∀ p ∈ S, ∀ g ∈ p.2.freeVars, g ∉ G)
    (hpoly : ∀ σ, .poly σ ∈ specs → ∀ p ∈ S, p.1 ∉ σ.body.freeVars) :
    S.onCtx (RecSpecs.algorithmStageCtx ctx specs done G) =
      RecSpecs.algorithmStageCtx (S.onCtx ctx) (specs.map (RecSpec.onSubst S)) done G := by
  simp only [Subst.onCtx, Subst.onEnv, RecSpecs.algorithmStageCtx, List.map_append]
  congr 1
  · congr 1
    apply List.ext_getElem?
    intro i
    simp only [List.getElem?_map, List.getElem?_mapIdx, Option.map_map]
    cases hi : specs[i]? with
    | none => rfl
    | some spec =>
      simp only [Option.map_some]
      cases spec with
      | mono τ =>
        simp only [Function.comp_apply, RecSpec.algorithmStageEntry, RecSpec.onSubst]
        split
        · rw [Subst.onPolyTy_genGroup hdom hran]
        · rfl
      | poly σ =>
        simp only [Function.comp_apply, RecSpec.algorithmStageEntry, RecSpec.onSubst, Subst.onPolyTy]
        rw [show S.onTy σ.body = σ.body from
          Ty.substFvars_eq_self_of_no_key
            (fun p hp => hpoly σ (List.mem_of_getElem? hi) p hp)]

theorem RecSpecs.algorithmStageCtx_pool_append {ctx : Ctx} {specs : List RecSpec}
    {done G H : List Nat}
    (hH : ∀ member τ, specs[member]? = some (.mono τ) → member ∈ done →
      ∀ g ∈ H, g ∉ τ.freeVars) :
    RecSpecs.algorithmStageCtx ctx specs done (G ++ H) =
      RecSpecs.algorithmStageCtx ctx specs done G := by
  simp only [RecSpecs.algorithmStageCtx]
  congr 1
  · congr 1
    apply List.ext_getElem?
    intro member
    simp only [List.getElem?_mapIdx]
    cases hs : specs[member]? with
    | none => rfl
    | some spec =>
      simp only [Option.map_some]
      cases spec with
      | poly σ => rfl
      | mono τ =>
        simp only [RecSpec.algorithmStageEntry]
        split
        · rw [PolyTy.genGroup_append_of_avoid (hH member τ hs (by assumption))]
        · rfl

theorem RecSpecs.bodyCtx_onSubst {S : Subst} {ctx : Ctx} {specs : List RecSpec} {G : List Nat}
    (hdom : ∀ p ∈ S, p.1 ∉ G) (hran : ∀ p ∈ S, ∀ g ∈ p.2.freeVars, g ∉ G)
    (hpoly : ∀ σ, .poly σ ∈ specs → ∀ p ∈ S, p.1 ∉ σ.body.freeVars) :
    S.onCtx (RecSpecs.bodyCtx ctx specs G) =
      RecSpecs.bodyCtx (S.onCtx ctx) (specs.map (RecSpec.onSubst S)) G := by
  simp only [Subst.onCtx, Subst.onEnv, RecSpecs.bodyCtx, List.map_append]
  congr 1
  congr 1
  rw [List.map_map, List.map_map]
  apply List.map_congr_left
  intro s hs
  cases s with
  | mono τ => exact Subst.onPolyTy_genGroup hdom hran
  | poly σ =>
    simp only [Function.comp_apply, RecSpec.bodyScheme, RecSpec.onSubst, Subst.onPolyTy]
    rw [show S.onTy σ.body = σ.body from
      Ty.substFvars_eq_self_of_no_key (fun p hp => hpoly σ hs p hp)]

/-- Per-stage frozen-pool certificate. This is only proof bookkeeping: the
    executable relation remains unchanged. -/

theorem RecSpec.mono_getElem?_map_onSubst {specs : List RecSpec} {S : Subst}
    {member : Nat} {τ : Ty} (h : (specs.map (RecSpec.onSubst S))[member]? = some (.mono τ)) :
    ∃ t, specs[member]? = some (.mono t) ∧ τ = S.onTy t := by
  rw [List.getElem?_map] at h
  cases hs : specs[member]? with
  | none => simp [hs] at h
  | some spec =>
    cases spec with
    | poly σ => simp [hs, RecSpec.onSubst] at h
    | mono t =>
      simp only [hs, Option.map_some, RecSpec.onSubst, Option.some.injEq, RecSpec.mono.injEq] at h
      exact ⟨t, rfl, h.symm⟩

/-- The unsigned members not yet completed retain their own original fresh
    placeholder. No other spec or outer-environment entry mentions that seed. -/
structure RecSpecs.PendingSeeds (base : Nat) (ctx : Ctx) (specs : List RecSpec)
    (done : List Nat) : Prop where
  mono : ∀ member τ, specs[member]? = some (.mono τ) → member ∉ done →
    τ = .fvar (base + member)
  other : ∀ member τ, specs[member]? = some (.mono τ) → member ∉ done →
    ∀ j s, specs[j]? = some s → j ≠ member → base + member ∉ s.freeVars
  env : ∀ member τ, specs[member]? = some (.mono τ) → member ∉ done →
    ∀ M ∈ ctx.env, base + member ∉ M.body.freeVars

theorem RecSpecs.PendingSeeds.onSubst {base : Nat} {ctx : Ctx} {specs : List RecSpec}
    {done done' : List Nat} {S : Subst} (h : RecSpecs.PendingSeeds base ctx specs done)
    (hdone : ∀ member ∈ done, member ∈ done')
    (havoid : ∀ member τ, specs[member]? = some (.mono τ) → member ∉ done' →
      (∀ p ∈ S, base + member ∉ p.2.freeVars) ∧ base + member ∉ S.map Prod.fst) :
    RecSpecs.PendingSeeds base (S.onCtx ctx) (specs.map (RecSpec.onSubst S)) done' := by
  constructor
  · intro member τ hτ hm
    obtain ⟨t, ht, rfl⟩ := RecSpec.mono_getElem?_map_onSubst hτ
    rw [h.mono member t ht (fun hc => hm (hdone member hc))]
    apply Ty.substFvars_eq_self_of_no_key
    intro p hp hc
    apply (havoid member t ht hm).2
    apply List.mem_map.mpr
    refine ⟨p, hp, ?_⟩
    simpa only [Ty.freeVars, List.mem_singleton] using hc
  · intro member τ hτ hm j s hs hj
    obtain ⟨t, ht, _⟩ := RecSpec.mono_getElem?_map_onSubst hτ
    rw [List.getElem?_map] at hs
    obtain ⟨old,hold,rfl⟩ := Option.map_eq_some_iff.mp hs
    exact RecSpec.notMem_freeVars_onSubst (havoid member t ht hm).1
      (h.other member t ht (fun hc => hm (hdone member hc)) j old hold hj)
  · intro member τ hτ hm
    obtain ⟨t, ht, _⟩ := RecSpec.mono_getElem?_map_onSubst hτ
    exact Subst.onCtx_avoid (h.env member t ht (fun hc => hm (hdone member hc)))
      (havoid member t ht hm).1

theorem RecSpecs.PendingSeeds.init {base : Nat} {ctx : Ctx} {anns : List (Option PolyTy)}
    (hctx : CtxBelow base ctx)
    (hanns : ∀ σ, some σ ∈ anns → Ty.BelowFvars base σ.body) :
    RecSpecs.PendingSeeds base ctx (RecSpec.init base anns) [] := by
  have hmono {member : Nat} {τ : Ty} (ht : (RecSpec.init base anns)[member]? = some (.mono τ)) :
      τ = .fvar (base + member) := by
    rw [RecSpec.init_getElem?] at ht
    cases ha : anns[member]? with
    | none => simp [ha] at ht
    | some ann =>
      cases ann with
      | some σ => simp [ha] at ht
      | none => simpa only [ha, Option.map_some, Option.some.injEq, RecSpec.mono.injEq] using ht.symm
  constructor
  · intro member τ ht _; exact hmono ht
  · intro member τ ht _ j s hs hj
    rw [RecSpec.init_getElem?] at hs
    cases ha : anns[j]? with
    | none => simp [ha] at hs
    | some ann =>
      cases ann with
      | none =>
        simp only [ha, Option.map_some, Option.some.injEq] at hs
        subst s
        simp only [RecSpec.freeVars, Ty.freeVars, List.mem_singleton]
        omega
      | some σ =>
        simp only [ha, Option.map_some, Option.some.injEq] at hs
        subst s
        intro hc
        have := Ty.BelowFvars.mem_lt (hanns σ (List.mem_of_getElem? ha)) _ hc
        omega
  · intro member τ ht _ M hM hc
    have := Ty.BelowFvars.mem_lt (hctx M hM) _ hc
    omega

theorem Expr.ForallOuter.of_recGroupRefs_with_outer {P : Nat → Prop} {e : Expr} {n depth : Nat}
    (hrefs : ∀ i ∈ e.recGroupRefs n depth, P i) (houter : ∀ i, n ≤ i → P i) :
    e.ForallOuter P depth := by
  apply (Expr.ForallOuter.of_recGroupRefs hrefs).mono
  intro i hi
  by_cases hlt : i < n
  · exact hi hlt
  · exact houter i (by omega)

theorem RecSpecs.PendingSeeds.stage_lookupAvoid_other {base : Nat} {ctx : Ctx}
    {specs : List RecSpec} {done G : List Nat} (h : RecSpecs.PendingSeeds base ctx specs done)
    {member : Nat} {τ : Ty} (ht : specs[member]? = some (.mono τ)) (hm : member ∉ done)
    {i : Nat} (hi : i ≠ member) :
    ∀ M, (RecSpecs.algorithmStageCtx ctx specs done G).env[i]? = some M →
      base + member ∉ M.body.freeVars := by
  intro M hM
  by_cases hil : i < specs.length
  · rw [RecSpecs.algorithmStageCtx, List.getElem?_append_left (by simpa using hil),
      List.getElem?_mapIdx] at hM
    obtain ⟨s, hs, heq⟩ := Option.map_eq_some_iff.mp hM
    subst M
    exact fun hc => h.other member τ ht hm i s hs hi
      (RecSpec.algorithmStageEntry_freeVars_subset hc)
  · rw [RecSpecs.algorithmStageCtx, List.getElem?_append_right
      (by simp only [List.length_mapIdx]; omega)] at hM
    exact h.env member τ ht hm M (List.mem_of_getElem? hM)

theorem RecSpecs.PendingSeeds.stage_lookupAvoid_of_no_ref {base : Nat} {ctx : Ctx}
    {specs : List RecSpec} {done G : List Nat} (h : RecSpecs.PendingSeeds base ctx specs done)
    {member : Nat} {τ : Ty} (ht : specs[member]? = some (.mono τ)) (hm : member ∉ done)
    {rhs : Expr} (href : member ∉ rhs.recGroupRefs specs.length 0) :
    rhs.ForallOuter (fun i => ∀ M,
      (RecSpecs.algorithmStageCtx ctx specs done G).env[i]? = some M →
      base + member ∉ M.body.freeVars) 0 := by
  apply Expr.ForallOuter.of_recGroupRefs_with_outer
    (n := specs.length)
  · intro i hi
    apply h.stage_lookupAvoid_other ht hm
    exact fun heq => href (heq ▸ hi)
  · intro i hi
    apply h.stage_lookupAvoid_other ht hm
    have hmlt := (List.getElem?_eq_some_iff.mp ht).1
    omega

theorem RecGroups.ValidResidualGroups.pending_no_ref {anns : List (Option PolyTy)}
    {bindings : List Expr} {specs : List RecSpec} {past : List (List Nat)}
    {component : List Nat} {rest : List (List Nat)} {source member : Nat} {rhs : Expr} {τ : Ty}
    (hvalid : RecGroups.ValidResidualGroups anns bindings (past ++ component :: rest))
    (hanns : specs.map RecSpec.ann = anns) (hlen : bindings.length = specs.length)
    (hs : source ∈ component) (hrhs : bindings[source]? = some rhs)
    (ht : specs[member]? = some (.mono τ))
    (hm : member ∉ past.flatten ++ component) :
    member ∉ rhs.recGroupRefs specs.length 0 := by
  intro hc
  have hcomponent : (past ++ component :: rest)[past.length]? = some component := by
    rw [List.getElem?_append_right (by omega), Nat.sub_self]
    rfl
  have havailable := hvalid.refs_available hanns hlen hcomponent hs hrhs ht (hlen ▸ hc)
  rw [List.take_left] at havailable
  exact hm (List.mem_append.mpr havailable)

theorem RecSpecs.PendingSeeds.seed_notMem_newPool {base : Nat} {ctx : Ctx}
    {specs : List RecSpec} {done boundaryDone G rigid : List Nat}
    (h : RecSpecs.PendingSeeds base ctx specs done) {member : Nat} {τ : Ty}
    (ht : specs[member]? = some (.mono τ)) (hm : member ∉ done)
    {component : List Nat} (hcompleted : ∀ j ∈ component, j ∈ done) :
    base + member ∉ genGroupVars rigid
      (RecSpecs.generalizationCtx ctx specs boundaryDone G).env (RecSpecs.monoTysAt specs component) := by
  intro hg
  obtain ⟨t, htmem, hgτ⟩ := Ty.mem_freeVarsList_exists (genGroupVars_spec hg).1
  obtain ⟨j,hj,hlook⟩ := List.mem_filterMap.mp htmem
  cases hs : specs[j]? with
  | none => simp [hs] at hlook
  | some spec =>
    cases spec with
    | poly σ => simp [hs, RecSpec.monoTy?] at hlook
    | mono t0 =>
      simp only [hs, Option.bind_some, RecSpec.monoTy?, Option.some.injEq] at hlook
      subst t
      exact h.other member τ ht hm j (.mono t0) hs
        (fun heq => hm (heq ▸ hcompleted j hj)) hgτ

theorem PolyTy.genGroup_notMem_pool {G : List Nat} {τ : Ty} {g : Nat}
    (hg : g ∈ G) : g ∉ (PolyTy.genGroup G τ).body.freeVars := by
  intro hc
  have hgτ := Ty.freeVars_closeOver_subset hc
  exact Ty.not_mem_closeOver_freeVars
    (gs := Ty.genFilter G τ) (by simp only [Ty.genFilter, List.mem_filter, decide_eq_true_eq]; exact ⟨hg,hgτ⟩) hc

theorem RecSpecs.PendingSeeds.stage_avoid_pool {base : Nat} {ctx : Ctx}
    {specs : List RecSpec} {done G : List Nat} (h : RecSpecs.PendingSeeds base ctx specs done)
    (hseed : ∀ member τ, specs[member]? = some (.mono τ) → member ∉ done → base + member ∉ G)
    (hctx : ∀ g ∈ G, ∀ M ∈ ctx.env, g ∉ M.body.freeVars)
    (hpoly : ∀ σ, .poly σ ∈ specs → ∀ g ∈ G, g ∉ σ.body.freeVars) :
    ∀ g ∈ G, ∀ M ∈ (RecSpecs.algorithmStageCtx ctx specs done G).env, g ∉ M.body.freeVars := by
  intro g hg M hM
  rcases List.mem_append.mp hM with hM | hM
  · obtain ⟨i, hi, rfl⟩ := List.mem_mapIdx.mp hM
    have hs : specs[i]? = some specs[i] := List.getElem?_eq_getElem hi
    cases hspec : specs[i] with
    | poly σ => exact hpoly σ (hspec ▸ List.getElem_mem hi) g hg
    | mono τ =>
      simp only [RecSpec.algorithmStageEntry]
      split
      · exact PolyTy.genGroup_notMem_pool hg
      · rename_i hindone
        have ht : specs[i]? = some (.mono τ) := hspec ▸ hs
        rw [h.mono i τ ht hindone]
        simp only [PolyTy.mkTrivial, Ty.freeVars, List.mem_singleton]
        exact fun heq => hseed i τ ht hindone (heq ▸ hg)
  · exact hctx g hg M hM

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
    rw [Ty.closeOver, List.idxOf?_eq_none_iff.mpr hn]
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

/-- Closing over vars only removes free vars. -/
theorem Ty.closeOver_freeVars_subset {gs : List Nat} {τ : Ty} :
    (Ty.closeOver gs τ).freeVars ⊆ τ.freeVars := by
  induction τ using Ty.rec_strong with
  | prim p => simp [Ty.closeOver, Ty.freeVars]
  | bvar i => simp [Ty.closeOver, Ty.freeVars]
  | fvar n =>
    rw [Ty.closeOver]
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


/-- Emit scheme facts for the genuinely generalized members of a recursion
    group. Annotated members are declarations, not inference-produced schemes,
    so they are omitted. -/

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

/-! ## 1. The renaming / swap / block-swap kit

Injective renamings dodge the fresh-binder obstruction: a clean override of
`S₀` mapping a fresh var to the declarative type is unrealisable as a `List`
substitution once the fresh var occurs in `S₀`'s range; swapping it away with
a fresh name restores cleanliness. Type-level only; ported nearly verbatim
-/

mutual
/-- Relabel every free type variable by `f`. An α-renaming when `f` is injective. -/
def Ty.rename (f : Nat → Nat) : Ty → Ty
  | .prim p          => .prim p
  | .arrow a b       => .arrow (a.rename f) (b.rename f)
  | .bvar i          => .bvar i
  | .fvar n          => .fvar (f n)
  | .customTy nm tys => .customTy nm (TyList.rename f tys)

private def TyList.rename (f : Nat → Nat) : List Ty → List Ty
  | []       => []
  | hd :: tl => hd.rename f :: TyList.rename f tl
end

/-! The range guard's orientation lemma.  The executable unifier is called
with the annotation opening on the right and that opening protected in its
rigid set.  Consequently any returned substitution which avoids the protected
set can only put protected variables in its raw images. -/

mutual
theorem UnifyRel.range_within_rhs {K : List Nat} :
    {a b : Ty} → {S : Subst} → UnifyRel a b S →
    (∀ p ∈ S, p.1 ∉ K) →
    (∀ x ∈ b.freeVars, x ∈ K) →
    ∀ p ∈ S, ∀ x ∈ p.2.freeVars, x ∈ K
  | _, _, _, .prim, _, _, p, hp, x, hx => by simp at hp
  | _, _, _, .fvarRefl, _, _, p, hp, x, hx => by simp at hp
  | _, _, _, @UnifyRel.fvarL n t _ _, hav, hb, p, hp, x, hx => by
      rw [List.mem_singleton] at hp
      subst p
      exact hb x hx
  | _, _, _, @UnifyRel.fvarR n t _ _, hav, hb, p, hp, x, hx => by
      have hn : n ∈ K := hb n (by simp [Ty.freeVars])
      exact False.elim (hav (n, t) (by simp) hn)
  | _, _, _, @UnifyRel.arrow a b c d S₁ S₂ h₁ h₂, hav, hright, p, hp, x, hx => by
      have hc : ∀ y ∈ c.freeVars, y ∈ K :=
        fun y hy => hright y (Ty.mem_freeVars_arrowL hy)
      have hd : ∀ y ∈ d.freeVars, y ∈ K :=
        fun y hy => hright y (Ty.mem_freeVars_arrowR hy)
      have hav₁ : ∀ q ∈ S₁, q.1 ∉ K := fun q hq =>
        hav q (List.mem_append_left _ hq)
      have hav₂ : ∀ q ∈ S₂, q.1 ∉ K := fun q hq =>
        hav q (List.mem_append_right _ hq)
      have h₁range := UnifyRel.range_within_rhs h₁ hav₁ hc
      have hd_fixed : S₁.onTy d = d :=
        Ty.substFvars_eq_self_of_no_key (fun q hq hy => hav₁ q hq (hd q.1 hy))
      rw [List.mem_append] at hp
      rcases hp with hp | hp
      · exact h₁range p hp x hx
      · have h₂range := UnifyRel.range_within_rhs h₂ hav₂ (by
          intro y hy
          rw [hd_fixed] at hy
          exact hd y hy)
        exact h₂range p hp x hx
  | _, _, _, @UnifyRel.customTy nm as bs S hs, hav, hright, p, hp, x, hx => by
      exact UnifyRelList.range_within_rhs hs hav (by
        intro t ht y hy
        exact hright y (Ty.mem_freeVars_customTy ht hy)
        ) p hp x hx

theorem UnifyRelList.range_within_rhs {K : List Nat} :
    {as bs : List Ty} → {S : Subst} → UnifyRelList as bs S →
    (∀ p ∈ S, p.1 ∉ K) →
    (∀ t ∈ bs, ∀ x ∈ t.freeVars, x ∈ K) →
    ∀ p ∈ S, ∀ x ∈ p.2.freeVars, x ∈ K
  | _, _, _, .nil, _, _, p, hp, x, hx => by simp at hp
  | _, _, _, @UnifyRelList.cons a b as bs S₁ S₂ h₁ h₂, hav, hright, p, hp, x, hx => by
      have hb : ∀ y ∈ b.freeVars, y ∈ K := hright b List.mem_cons_self
      have hbs : ∀ t ∈ bs, ∀ y ∈ t.freeVars, y ∈ K :=
        fun t ht => hright t (List.mem_cons_of_mem _ ht)
      have hav₁ : ∀ q ∈ S₁, q.1 ∉ K := fun q hq =>
        hav q (List.mem_append_left _ hq)
      have hav₂ : ∀ q ∈ S₂, q.1 ∉ K := fun q hq =>
        hav q (List.mem_append_right _ hq)
      have h₁range := UnifyRel.range_within_rhs h₁ hav₁ hb
      have hbs_fixed : ∀ t ∈ bs, S₁.onTy t = t := by
        intro t ht
        exact Ty.substFvars_eq_self_of_no_key (fun q hq hy => hav₁ q hq (hbs t ht q.1 hy))
      rw [List.mem_append] at hp
      rcases hp with hp | hp
      · exact h₁range p hp x hx
      · apply UnifyRelList.range_within_rhs h₂ hav₂
          (by
            intro t ht y hy
            obtain ⟨t0, ht0, rfl⟩ := List.mem_map.mp ht
            rw [hbs_fixed t0 ht0] at hy
            exact hbs t0 ht0 y hy) p hp x hx
end

theorem TyList.rename_eq_map (f : Nat → Nat) (tys : List Ty) :
    TyList.rename f tys = tys.map (Ty.rename f) := by
  induction tys with
  | nil => rfl
  | cons hd tl ih => simp only [TyList.rename, List.map_cons, ih]

@[simp] theorem Ty.rename_prim {f : Nat → Nat} {p : PrimTy} :
    Ty.rename f (.prim p) = .prim p := rfl
@[simp] theorem Ty.rename_bvar {f : Nat → Nat} {i : Nat} :
    Ty.rename f (.bvar i) = .bvar i := rfl
@[simp] theorem Ty.rename_fvar {f : Nat → Nat} {n : Nat} :
    Ty.rename f (.fvar n) = .fvar (f n) := rfl
@[simp] theorem Ty.rename_arrow {f : Nat → Nat} {a b : Ty} :
    Ty.rename f (.arrow a b) = .arrow (Ty.rename f a) (Ty.rename f b) := rfl
@[simp] theorem Ty.rename_customTy {f : Nat → Nat} {nm : TyName} {tys : List Ty} :
    Ty.rename f (.customTy nm tys) = .customTy nm (tys.map (Ty.rename f)) := by
  simp [Ty.rename, TyList.rename_eq_map]
/-- Renaming by a function that fixes `τ`'s free vars is the identity. -/
theorem Ty.rename_eq_self {f : Nat → Nat} {τ : Ty}
    (h : ∀ v ∈ τ.freeVars, f v = v) : Ty.rename f τ = τ := by
  induction τ using Ty.rec_strong with
  | prim _ => rfl
  | arrow a b ih_a ih_b =>
    simp only [Ty.rename_arrow, Ty.arrow.injEq]
    refine ⟨ih_a (fun v hv => h v ?_), ih_b (fun v hv => h v ?_)⟩
    · simp only [Ty.freeVars, List.mem_dedup, List.mem_append]; exact Or.inl hv
    · simp only [Ty.freeVars, List.mem_dedup, List.mem_append]; exact Or.inr hv
  | bvar _ => rfl
  | fvar n =>
    have hn := h n (by simp [Ty.freeVars])
    simp only [Ty.rename_fvar, hn]
  | customTy nm tys ih =>
    simp only [Ty.rename_customTy, Ty.customTy.injEq, true_and]
    conv_rhs => rw [← List.map_id tys]
    apply List.map_congr_left
    intro t ht
    exact ih t ht (fun v hv => h v (TyList.mem_freeVars_of_mem ht hv))

/-- Renaming preserves the bvar bound (it only touches `fvar`s). -/
theorem Ty.rename_containsBvars {f : Nat → Nat} {n : Nat} {τ : Ty}
    (h : ContainsBvarsUpTo n τ) : ContainsBvarsUpTo n (Ty.rename f τ) := by
  induction τ using Ty.rec_strong with
  | prim p => exact .prim
  | bvar i => cases h with | bvar hlt => exact .bvar hlt
  | fvar m => exact .fvar
  | arrow a b iha ihb => cases h with | arrow ha hb => exact .arrow (iha ha) (ihb hb)
  | customTy nm tys ih =>
    cases h with
    | customTy hall =>
      simp only [Ty.rename_customTy]
      apply ContainsBvarsUpTo.customTy
      intro t ht
      obtain ⟨t0, ht0, rfl⟩ := List.mem_map.mp ht
      exact ih t0 ht0 (hall t0 ht0)

/-- Renaming preserves local-closedness. -/
theorem Ty.rename_isLC {f : Nat → Nat} {τ : Ty} (h : τ.IsLC) :
    (Ty.rename f τ).IsLC := Ty.rename_containsBvars h

/-- Renaming by an injective `f` commutes with single-var substitution. -/
theorem Ty.rename_substFvar {f : Nat → Nat} (hf : Function.Injective f)
    (z : Nat) (u t : Ty) :
    Ty.rename f (Ty.substFvar z u t)
      = Ty.substFvar (f z) (Ty.rename f u) (Ty.rename f t) := by
  induction t using Ty.rec_strong with
  | prim p => rfl
  | arrow a b iha ihb => simp only [Ty.substFvar, Ty.rename_arrow, iha, ihb]
  | bvar i => rfl
  | fvar m =>
    simp only [Ty.substFvar, Ty.rename_fvar]
    by_cases hm : m = z
    · rw [if_pos hm, if_pos (congrArg f hm)]
    · rw [if_neg hm, if_neg (fun heq => hm (hf heq)), Ty.rename_fvar]
  | customTy nm tys ih =>
    simp only [Ty.substFvar, TyList.substFvar_eq_map, Ty.rename_customTy, List.map_map,
               Ty.customTy.injEq, true_and]
    apply List.map_congr_left
    intro t0 ht0
    exact ih t0 ht0

/-- Swap two naturals. -/
def swapNat (a b n : Nat) : Nat := if n = a then b else if n = b then a else n

@[simp] theorem swapNat_left (a b : Nat) : swapNat a b a = b := by simp [swapNat]
theorem swapNat_right (a b : Nat) : swapNat a b b = a := by
  simp only [swapNat]; split <;> simp_all
theorem swapNat_other {a b n : Nat} (ha : n ≠ a) (hb : n ≠ b) : swapNat a b n = n := by
  simp [swapNat, ha, hb]
theorem swapNat_involutive (a b n : Nat) : swapNat a b (swapNat a b n) = n := by
  by_cases hna : n = a
  · subst hna; rw [swapNat_left, swapNat_right]
  · by_cases hnb : n = b
    · subst hnb; rw [swapNat_right, swapNat_left]
    · rw [swapNat_other hna hnb, swapNat_other hna hnb]
theorem swapNat_injective (a b : Nat) : Function.Injective (swapNat a b) :=
  Function.Involutive.injective (swapNat_involutive a b)

/-- Conjugate a substitution by a renaming: relabel both keys and values. -/
def Subst.conj (f : Nat → Nat) (S : Subst) : Subst :=
  S.map (fun p => (f p.1, Ty.rename f p.2))

/-- Conjugation preserves LC of the replacement types. -/
theorem Subst.conj_lc {f : Nat → Nat} {S : Subst} (hS : ∀ p ∈ S, p.2.IsLC) :
    ∀ p ∈ Subst.conj f S, p.2.IsLC := by
  intro p hp
  simp only [Subst.conj, List.mem_map] at hp
  obtain ⟨p0, hp0, rfl⟩ := hp
  exact Ty.rename_isLC (hS p0 hp0)

/-- The defining property of conjugation: it intertwines `onTy` with the
    renaming (for injective `f`). -/
theorem Subst.onTy_conj {f : Nat → Nat} (hf : Function.Injective f) (S : Subst) (τ : Ty) :
    (Subst.conj f S).onTy (Ty.rename f τ) = Ty.rename f (S.onTy τ) := by
  induction S generalizing τ with
  | nil => simp only [Subst.conj, List.map_nil, Subst.onTy_nil]
  | cons hd S' ih =>
    obtain ⟨z, u⟩ := hd
    show Subst.onTy (Subst.conj f S') (Ty.substFvar (f z) (Ty.rename f u) (Ty.rename f τ))
        = Ty.rename f (Subst.onTy S' (Ty.substFvar z u τ))
    rw [← Ty.rename_substFvar hf, ih]

/-- The 3-element list realising the swap `a ↔ b` (with a fresh intermediate `c`),
    usable with `TypeOfHM.onSubst`. -/
def swapSubst (a b c : Nat) : Subst := [(a, .fvar c), (b, .fvar a), (c, .fvar b)]

theorem swapSubst_lc (a b c : Nat) : ∀ p ∈ swapSubst a b c, p.2.IsLC := by
  intro p hp
  simp only [swapSubst, List.mem_cons, List.not_mem_nil, or_false] at hp
  obtain rfl | rfl | rfl := hp <;> exact ContainsBvarsUpTo.fvar

/-- The swap list acts as `rename (swapNat a b)` on types avoiding the fresh `c`. -/
theorem swapSubst_onTy {a b c : Nat} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    {τ : Ty} (hc : c ∉ τ.freeVars) :
    (swapSubst a b c).onTy τ = Ty.rename (swapNat a b) τ := by
  induction τ using Ty.rec_strong with
  | prim p => simp only [Subst.onTy_prim, Ty.rename_prim]
  | bvar i => simp only [Subst.onTy_bvar, Ty.rename_bvar]
  | arrow a' b' iha ihb =>
    simp only [Ty.freeVars, List.mem_dedup, List.mem_append, not_or] at hc
    simp only [Subst.onTy_arrow, Ty.rename_arrow]
    exact congrArg₂ Ty.arrow (iha hc.1) (ihb hc.2)
  | fvar n =>
    simp only [Ty.freeVars, List.mem_singleton] at hc
    have hnc : n ≠ c := fun h => hc h.symm
    by_cases hna : n = a
    · subst hna
      simp [swapSubst, Subst.onTy, Ty.substFvars, Ty.substFvar, hbc.symm]
    · by_cases hnb : n = b
      · subst hnb
        simp [swapSubst, Subst.onTy, Ty.substFvars, Ty.substFvar, swapNat_right,
              hab.symm, hac]
      · simp [swapSubst, Subst.onTy, Ty.substFvars, Ty.substFvar,
              swapNat_other hna hnb, hna, hnb, hnc]
  | customTy nm tys ih =>
    simp only [Ty.freeVars] at hc
    simp only [Subst.onTy_customTy, Ty.rename_customTy, Ty.customTy.injEq, true_and]
    apply List.map_congr_left
    intro t ht
    exact ih t ht (fun hct => hc (TyList.mem_freeVars_of_mem ht hct))

/-- After swapping `Φ ↔ W`, the var `Φ` is absent provided `W` was absent
    (the only source of `Φ` would have been a pre-existing `W`). -/
theorem Ty.rename_swap_not_mem_left {Φ W : Nat} {Y : Ty} (h : W ∉ Y.freeVars) :
    Φ ∉ (Ty.rename (swapNat Φ W) Y).freeVars := by
  induction Y using Ty.rec_strong with
  | prim p => simp [Ty.freeVars]
  | bvar i => simp [Ty.freeVars]
  | fvar n =>
    simp only [Ty.freeVars, List.mem_singleton] at h
    simp only [Ty.rename_fvar, Ty.freeVars, List.mem_singleton, swapNat]
    split_ifs <;> omega
  | arrow a b iha ihb =>
    simp only [Ty.freeVars, List.mem_dedup, List.mem_append, not_or] at h
    simp only [Ty.rename_arrow, Ty.freeVars, List.mem_dedup, List.mem_append, not_or]
    exact ⟨iha h.1, ihb h.2⟩
  | customTy nm tys ih =>
    simp only [Ty.freeVars] at h
    simp only [Ty.rename_customTy, Ty.freeVars]
    rw [TyList.not_mem_freeVars_iff]
    intro t' ht'
    obtain ⟨t, ht, rfl⟩ := List.mem_map.mp ht'
    exact ih t ht (fun hct => h (TyList.mem_freeVars_of_mem ht hct))

/-- Map-back: substituting `W ↦ Φ` undoes the swap `Φ ↔ W` on a `W`-free type. -/
theorem Ty.substFvar_rename_swap {Φ W : Nat} {X : Ty} (h : W ∉ X.freeVars) :
    Ty.substFvar W (.fvar Φ) (Ty.rename (swapNat Φ W) X) = X := by
  induction X using Ty.rec_strong with
  | prim p => rfl
  | bvar i => rfl
  | fvar n =>
    simp only [Ty.freeVars, List.mem_singleton] at h
    simp only [Ty.rename_fvar, Ty.substFvar]
    by_cases hn : n = Φ
    · subst hn; simp [swapNat]
    · rw [swapNat_other hn (fun he => h he.symm), if_neg (fun he => h he.symm)]
  | arrow a b iha ihb =>
    simp only [Ty.freeVars, List.mem_dedup, List.mem_append, not_or] at h
    simp only [Ty.rename_arrow, Ty.substFvar, iha h.1, ihb h.2]
  | customTy nm tys ih =>
    simp only [Ty.freeVars] at h
    simp only [Ty.rename_customTy, Ty.substFvar, TyList.substFvar_eq_map, List.map_map]
    refine congrArg (Ty.customTy nm) ?_
    conv_rhs => rw [← List.map_id tys]
    apply List.map_congr_left
    intro t ht
    exact ih t ht (fun hct => h (TyList.mem_freeVars_of_mem ht hct))

/-- Two distinct fresh names, both `≥ Φ` and avoiding a given finite set. -/
theorem exists_fresh_two_ge (Φ : Nat) (avoid : List Nat) :
    ∃ W c, Φ ≤ W ∧ Φ ≤ c ∧ W ≠ c ∧ W ∉ avoid ∧ c ∉ avoid := by
  obtain ⟨Xs, hlen, hnodup, hav⟩ := exists_fresh_names (List.range Φ ++ avoid) 2
  obtain ⟨W, c, rfl⟩ : ∃ W c, Xs = [W, c] := by
    match Xs, hlen with
    | [W, c], _ => exact ⟨W, c, rfl⟩
  have hWmem : W ∈ [W, c] := by simp
  have hcmem : c ∈ [W, c] := by simp
  have hWav := hav W hWmem
  have hcav := hav c hcmem
  simp only [List.mem_append, not_or] at hWav hcav
  refine ⟨W, c, ?_, ?_, ?_, hWav.2, hcav.2⟩
  · have := hWav.1; simp only [List.mem_range, not_lt] at this; omega
  · have := hcav.1; simp only [List.mem_range, not_lt] at this; omega
  · simp only [List.nodup_cons, List.mem_singleton, List.not_mem_nil, not_false_eq_true,
      List.nodup_nil, and_true] at hnodup
    exact hnodup

/-- `substFvar` keeps `W` fresh when `W` is fresh for the input and the replacement. -/
theorem Ty.not_mem_freeVars_substFvar {Z W : Nat} {U τ : Ty}
    (hτ : W ∉ τ.freeVars) (hU : W ∉ U.freeVars) :
    W ∉ (Ty.substFvar Z U τ).freeVars := by
  induction τ using Ty.rec_strong with
  | prim p => simp [Ty.substFvar, Ty.freeVars]
  | bvar i => simp [Ty.substFvar, Ty.freeVars]
  | fvar n =>
    simp only [Ty.freeVars, List.mem_singleton] at hτ
    simp only [Ty.substFvar]
    by_cases hn : n = Z
    · simp only [if_pos hn]; exact hU
    · simp only [if_neg hn, Ty.freeVars, List.mem_singleton]; exact hτ
  | arrow a b iha ihb =>
    simp only [Ty.freeVars, List.mem_dedup, List.mem_append, not_or] at hτ
    simp only [Ty.substFvar, Ty.freeVars, List.mem_dedup, List.mem_append, not_or]
    exact ⟨iha hτ.1, ihb hτ.2⟩
  | customTy nm tys ih =>
    simp only [Ty.freeVars] at hτ
    simp only [Ty.substFvar, Ty.freeVars, TyList.substFvar_eq_map]
    rw [TyList.not_mem_freeVars_iff]
    intro t' ht'
    obtain ⟨t, ht, rfl⟩ := List.mem_map.mp ht'
    exact ih t ht (fun hct => hτ (TyList.mem_freeVars_of_mem ht hct))

/-- A whole substitution keeps `W` fresh when `W` avoids its range and the input. -/
theorem Subst.not_mem_onTy_freeVars {S : Subst} {W : Nat} {τ : Ty}
    (hS : ∀ p ∈ S, W ∉ p.2.freeVars) (hτ : W ∉ τ.freeVars) :
    W ∉ (S.onTy τ).freeVars := by
  induction S generalizing τ with
  | nil => simpa using hτ
  | cons hd S' ih =>
    obtain ⟨Z, U⟩ := hd
    rw [show ((Z, U) :: S') = [(Z, U)] ++ S' from rfl, Subst.onTy_append]
    refine ih (fun p hp => hS p (List.mem_cons_of_mem _ hp)) ?_
    exact Ty.not_mem_freeVars_substFvar hτ (hS (Z, U) List.mem_cons_self)

/-- A substitution that fixes every free variable of a type fixes the whole
    type. (Unlike `substFvars_eq_self_of_no_key`, the keys *may* occur, as long
    as the composite acts as the identity on them.) -/
theorem Subst.onTy_eq_self_of_fixes {S : Subst} :
    ∀ {t : Ty}, (∀ v ∈ t.freeVars, S.onTy (.fvar v) = .fvar v) → S.onTy t = t := by
  intro t
  induction t using Ty.rec_strong with
  | prim p => intro _; simp only [Subst.onTy_prim]
  | bvar i => intro _; simp only [Subst.onTy_bvar]
  | fvar n => intro h; exact h n (by simp [Ty.freeVars])
  | arrow a b iha ihb =>
    intro h
    rw [Subst.onTy_arrow,
        iha (fun v hv => h v (by
          simp only [Ty.freeVars, List.mem_dedup, List.mem_append]; exact Or.inl hv)),
        ihb (fun v hv => h v (by
          simp only [Ty.freeVars, List.mem_dedup, List.mem_append]; exact Or.inr hv))]
  | customTy nm tys ih =>
    intro h
    rw [Subst.onTy_customTy]
    refine congrArg (Ty.customTy nm) ?_
    conv_rhs => rw [← List.map_id tys]
    apply List.map_congr_left
    intro t0 ht0
    exact ih t0 ht0 (fun v hv => h v (TyList.mem_freeVars_of_mem ht0 hv))

/-! ### Block renaming (for the `var`/`letIn` cases, which allocate a block of
    fresh vars at once). Generalises the single-var swap: `blockSwap Φ W k`
    transposes `[Φ,Φ+k)` with `[W,W+k)` (disjoint when `Φ+k ≤ W`). On types that
    avoid the `W`-block, the forward list `blockList` realises it, and the
    backward list `blockListBack` is the map-back. -/

/-- Transpose the blocks `[Φ,Φ+k)` and `[W,W+k)` (disjoint when `Φ+k ≤ W`). -/
def blockSwap (Φ W k n : Nat) : Nat :=
  if Φ ≤ n ∧ n < Φ + k then n + (W - Φ)
  else if W ≤ n ∧ n < W + k then n - (W - Φ)
  else n

/-- Forward renaming list: `Φ+i ↦ .fvar (W+i)`. -/
def blockList (Φ W k : Nat) : Subst := (List.range k).map (fun i => (Φ + i, Ty.fvar (W + i)))

/-- Backward renaming list: `W+i ↦ .fvar (Φ+i)`. -/
def blockListBack (Φ W k : Nat) : Subst := (List.range k).map (fun i => (W + i, Ty.fvar (Φ + i)))

theorem blockSwap_lt {Φ W k n : Nat} (hle : Φ ≤ W) (h : n < Φ) :
    blockSwap Φ W k n = n := by
  simp only [blockSwap]; split_ifs <;> omega

theorem blockSwap_involutive {Φ W k : Nat} (hd : Φ + k ≤ W) (n : Nat) :
    blockSwap Φ W k (blockSwap Φ W k n) = n := by
  simp only [blockSwap]; split_ifs <;> omega

theorem blockSwap_injective {Φ W k : Nat} (hd : Φ + k ≤ W) :
    Function.Injective (blockSwap Φ W k) :=
  Function.Involutive.injective (blockSwap_involutive hd)

theorem blockList_lc (Φ W k : Nat) : ∀ p ∈ blockList Φ W k, p.2.IsLC := by
  intro p hp
  simp only [blockList, List.mem_map] at hp
  obtain ⟨i, _, rfl⟩ := hp
  exact ContainsBvarsUpTo.fvar

theorem blockListBack_lc (Φ W k : Nat) : ∀ p ∈ blockListBack Φ W k, p.2.IsLC := by
  intro p hp
  simp only [blockListBack, List.mem_map] at hp
  obtain ⟨i, _, rfl⟩ := hp
  exact ContainsBvarsUpTo.fvar

/-- A `range`-indexed list of single-var substitutions `a+i ↦ .fvar (b+i)`
    acts on a free variable `n` exactly like the block transposition: if `n`
    is in `[a, a+k)` it becomes `n - a + b`, otherwise it is unchanged. The
    disjointness premise prevents a relabelled var from being touched again. -/
private theorem rangeMapList_onTy_fvar (a b : Nat) (k : Nat)
    (hdisj : a + k ≤ b ∨ b + k ≤ a) (n : Nat) :
    Subst.onTy ((List.range k).map (fun i => (a + i, Ty.fvar (b + i)))) (Ty.fvar n)
      = Ty.fvar (if a ≤ n ∧ n < a + k then n - a + b else n) := by
  induction k with
  | zero =>
    simp only [List.range_zero, List.map_nil, Subst.onTy_nil, Nat.add_zero]
    split_ifs <;> first | rfl | omega
  | succ k ih =>
    have hdisj' : a + k ≤ b ∨ b + k ≤ a := by omega
    simp only [List.range_succ, List.map_append, List.map_cons, List.map_nil,
               Subst.onTy_append]
    rw [ih hdisj']
    simp only [Subst.onTy, Ty.substFvars, Ty.substFvar]
    split_ifs <;> first | rfl | omega | (rw [Ty.fvar.injEq]; omega)

/-- The forward list realises `blockSwap` on `W`-block-avoiding types. -/
theorem blockList_onTy {Φ W k : Nat} (hd : Φ + k ≤ W) {τ : Ty}
    (hτ : ∀ v ∈ τ.freeVars, ¬ (W ≤ v ∧ v < W + k)) :
    (blockList Φ W k).onTy τ = Ty.rename (blockSwap Φ W k) τ := by
  induction τ using Ty.rec_strong with
  | prim p => simp only [Subst.onTy_prim, Ty.rename_prim]
  | bvar i => simp only [Subst.onTy_bvar, Ty.rename_bvar]
  | arrow a b iha ihb =>
    simp only [Subst.onTy_arrow, Ty.rename_arrow]
    refine congrArg₂ Ty.arrow (iha (fun v hv => hτ v ?_)) (ihb (fun v hv => hτ v ?_))
    · simp only [Ty.freeVars, List.mem_dedup, List.mem_append]; exact Or.inl hv
    · simp only [Ty.freeVars, List.mem_dedup, List.mem_append]; exact Or.inr hv
  | fvar n =>
    have hWn : ¬ (W ≤ n ∧ n < W + k) :=
      hτ n (by simp only [Ty.freeVars, List.mem_singleton])
    simp only [blockList]
    rw [rangeMapList_onTy_fvar Φ W k (Or.inl hd) n, Ty.rename_fvar]
    simp only [blockSwap]
    split_ifs <;> first | rfl | omega | (rw [Ty.fvar.injEq]; omega)
  | customTy nm tys ih =>
    simp only [Subst.onTy_customTy, Ty.rename_customTy, Ty.customTy.injEq, true_and]
    apply List.map_congr_left
    intro t ht
    exact ih t ht (fun v hv => hτ v (TyList.mem_freeVars_of_mem ht hv))

/-- Map-back: the backward list undoes `blockSwap` on `W`-block-avoiding types. -/
theorem blockListBack_onTy_rename {Φ W k : Nat} (hd : Φ + k ≤ W) {X : Ty}
    (hX : ∀ v ∈ X.freeVars, ¬ (W ≤ v ∧ v < W + k)) :
    (blockListBack Φ W k).onTy (Ty.rename (blockSwap Φ W k) X) = X := by
  induction X using Ty.rec_strong with
  | prim p => simp only [Ty.rename_prim, Subst.onTy_prim]
  | bvar i => simp only [Ty.rename_bvar, Subst.onTy_bvar]
  | arrow a b iha ihb =>
    simp only [Ty.rename_arrow, Subst.onTy_arrow]
    refine congrArg₂ Ty.arrow (iha (fun v hv => hX v ?_)) (ihb (fun v hv => hX v ?_))
    · simp only [Ty.freeVars, List.mem_dedup, List.mem_append]; exact Or.inl hv
    · simp only [Ty.freeVars, List.mem_dedup, List.mem_append]; exact Or.inr hv
  | fvar n =>
    have hWn : ¬ (W ≤ n ∧ n < W + k) :=
      hX n (by simp only [Ty.freeVars, List.mem_singleton])
    simp only [Ty.rename_fvar, blockListBack]
    rw [rangeMapList_onTy_fvar W Φ k (Or.inr hd) (blockSwap Φ W k n)]
    simp only [blockSwap]
    split_ifs <;> first | rfl | omega | (rw [Ty.fvar.injEq]; omega)
  | customTy nm tys ih =>
    simp only [Ty.rename_customTy, Subst.onTy_customTy, List.map_map, Ty.customTy.injEq, true_and]
    conv_rhs => rw [← List.map_id tys]
    apply List.map_congr_left
    intro t ht
    exact ih t ht (fun v hv => hX v (TyList.mem_freeVars_of_mem ht hv))

/-- The `Φ`-block is absent after renaming a `W`-block-avoiding type. -/
theorem blockSwap_rename_not_mem {Φ W k : Nat} (hd : Φ + k ≤ W) {Y : Ty}
    (hY : ∀ v ∈ Y.freeVars, ¬ (W ≤ v ∧ v < W + k)) :
    ∀ v, Φ ≤ v → v < Φ + k → v ∉ (Ty.rename (blockSwap Φ W k) Y).freeVars := by
  induction Y using Ty.rec_strong with
  | prim p => simp [Ty.freeVars]
  | bvar i => simp [Ty.freeVars]
  | fvar n =>
    intro v hv1 hv2
    have hWn : ¬ (W ≤ n ∧ n < W + k) :=
      hY n (by simp only [Ty.freeVars, List.mem_singleton])
    simp only [Ty.rename_fvar, Ty.freeVars, List.mem_singleton, blockSwap]
    split_ifs <;> omega
  | arrow a b iha ihb =>
    intro v hv1 hv2
    simp only [Ty.rename_arrow, Ty.freeVars, List.mem_dedup, List.mem_append, not_or]
    refine ⟨iha (fun w hw => hY w ?_) v hv1 hv2, ihb (fun w hw => hY w ?_) v hv1 hv2⟩
    · simp only [Ty.freeVars, List.mem_dedup, List.mem_append]; exact Or.inl hw
    · simp only [Ty.freeVars, List.mem_dedup, List.mem_append]; exact Or.inr hw
  | customTy nm tys ih =>
    intro v hv1 hv2
    simp only [Ty.rename_customTy, Ty.freeVars]
    rw [TyList.not_mem_freeVars_iff]
    intro t' ht'
    obtain ⟨t, ht, rfl⟩ := List.mem_map.mp ht'
    exact ih t ht (fun w hw => hY w (TyList.mem_freeVars_of_mem ht hw)) v hv1 hv2

/-- Bridge for the `var` completeness case: if `ty` instantiates to `τ` under
    `tyArgs`, then opening `ty` with fresh names `Xs` (nodup, fresh for `τ`) and
    substituting `Xs ↦ tyArgs` recovers `τ`. Only the result `τ`'s freshness is
    needed (used `tyArgs` are subterms of `τ`); unused `tyArgs` never matter, as
    the induction only visits `ty`'s actual bound vars. -/
theorem InstantiatesBy.onTy_openVars_zip {Xs : List Nat} {ty τ : Ty} {tyArgs : List Ty}
    (hinst : InstantiatesBy tyArgs ty τ)
    (hbv : ContainsBvarsUpTo Xs.length ty)
    (hnodup : Xs.Nodup)
    (hXfresh : ∀ x ∈ Xs, x ∉ τ.freeVars) :
    Subst.onTy (Xs.zip tyArgs) (Ty.openVars Xs ty) = τ := by
  induction ty using Ty.rec_strong generalizing τ with
  | prim p => cases hinst; simp only [Ty.openVars_prim, Subst.onTy_prim]
  | fvar n =>
    cases hinst
    simp only [Ty.openVars, Ty.instantiate]
    apply Ty.substFvars_eq_self_of_no_key
    intro p hp hc
    simp only [Ty.freeVars, List.mem_singleton] at hc
    subst hc
    exact hXfresh p.1 (List.of_mem_zip hp).1 (by simp [Ty.freeVars])
  | bvar i =>
    cases hinst with
    | bvar hsome =>
      cases hbv with
      | bvar hlt =>
        have hxi : Xs[i]? = some Xs[i] := List.getElem?_eq_getElem hlt
        simp only [Ty.openVars, Ty.instantiate, hxi, Option.elim_some]
        exact Ty.substFvars_zip_fvar_eq' hnodup hxi hsome hXfresh
  | arrow a b iha ihb =>
    cases hinst with
    | arrow ha hb =>
      cases hbv with
      | arrow hba hbb =>
        simp only [Ty.openVars_arrow, Subst.onTy_arrow]
        refine congrArg₂ Ty.arrow (iha ha hba ?_) (ihb hb hbb ?_)
        · intro x hx hc; exact hXfresh x hx (by
            simp only [Ty.freeVars, List.mem_dedup, List.mem_append]; exact .inl hc)
        · intro x hx hc; exact hXfresh x hx (by
            simp only [Ty.freeVars, List.mem_dedup, List.mem_append]; exact .inr hc)
  | customTy nm tys ih =>
    cases hinst with
    | customTy hforall =>
      cases hbv with
      | customTy hball =>
        simp only [Ty.openVars_customTy, Subst.onTy_customTy]
        refine congrArg (Ty.customTy nm) ?_
        induction hforall with
        | nil => rfl
        | cons hhd htl ihtl =>
          rename_i a instA tys' instTys'
          simp only [List.map_cons, List.cons.injEq]
          refine ⟨ih a List.mem_cons_self hhd (hball a List.mem_cons_self) ?_, ?_⟩
          · intro x hx hc
            apply hXfresh x hx
            simp only [Ty.freeVars, TyList.freeVars, List.mem_dedup, List.mem_append]
            exact Or.inl hc
          · refine ihtl (fun t ht => ih t (List.mem_cons_of_mem _ ht)) ?_
              (fun t ht => hball t (List.mem_cons_of_mem _ ht))
            intro x hx hc
            apply hXfresh x hx
            simp only [Ty.freeVars, TyList.freeVars, List.mem_dedup, List.mem_append] at hc ⊢
            exact Or.inr hc

/-- A single fresh name `W` starting a block `[W,W+k)` disjoint from `[Φ,Φ+k)`
    and above a finite `avoid` set. -/
theorem exists_fresh_block (avoid : List Nat) (Φ k : Nat) :
    ∃ W, Φ + k ≤ W ∧ ∀ v ∈ avoid, v < W := by
  refine ⟨avoid.foldr max 0 + Φ + k + 1, by omega, ?_⟩
  intro v hv
  have := List.le_foldr_max hv
  omega

/-- Opening a scheme body at `[Φ, Φ+k)` and then swapping that block with a
    fresh block `[W, W+k)` is the same as opening directly at the fresh block,
    provided the body's free variables lie below `Φ`. -/
theorem Ty.rename_openVars_blockSwap {Φ W k : Nat} (hd : Φ + k ≤ W) (ty : Ty)
    (hty : ∀ v ∈ ty.freeVars, v < Φ) :
    Ty.rename (blockSwap Φ W k) (Ty.openVars (freshVars Φ k) ty) =
      Ty.openVars (freshVars W k) ty := by
  induction ty using Ty.rec_strong with
  | prim p => simp only [Ty.openVars_prim, Ty.rename_prim]
  | bvar i =>
    simp only [Ty.openVars, Ty.instantiate]
    by_cases hi : i < k
    · have hf : (freshVars Φ k)[i]? = some (Φ + i) := by
        simp only [freshVars, List.getElem?_map, List.getElem?_range hi, Option.map_some]
      have hw : (freshVars W k)[i]? = some (W + i) := by
        simp only [freshVars, List.getElem?_map, List.getElem?_range hi, Option.map_some]
      simp only [hf, hw, Option.elim_some, Ty.rename_fvar, Ty.fvar.injEq, blockSwap]
      split_ifs <;> omega
    · have hf : (freshVars Φ k)[i]? = none :=
        List.getElem?_eq_none (by simp [freshVars_length]; omega)
      have hw : (freshVars W k)[i]? = none :=
        List.getElem?_eq_none (by simp [freshVars_length]; omega)
      simp only [hf, hw, Option.elim_none, Ty.rename_bvar]
  | fvar n =>
    have hn : n < Φ := hty n (by simp [Ty.freeVars])
    simp only [Ty.openVars, Ty.instantiate, Ty.rename_fvar, Ty.fvar.injEq]
    rw [blockSwap_lt (by omega) hn]
  | arrow a b iha ihb =>
    simp only [Ty.openVars_arrow, Ty.rename_arrow]
    refine congrArg₂ Ty.arrow (iha ?_) (ihb ?_)
    · intro v hv; exact hty v (by
        simp only [Ty.freeVars, List.mem_dedup, List.mem_append]; exact Or.inl hv)
    · intro v hv; exact hty v (by
        simp only [Ty.freeVars, List.mem_dedup, List.mem_append]; exact Or.inr hv)
  | customTy nm tys ih =>
    simp only [Ty.openVars_customTy, Ty.rename_customTy, List.map_map]
    congr 1
    apply List.map_congr_left
    intro t ht
    exact ih t ht (fun v hv => hty v (TyList.mem_freeVars_of_mem ht hv))

/-! ## 2. Unification completeness

If two LC types admit an LC unifier, a `UnifyRel` derivation exists (plain and
rigidity-aware forms), and the executable unifiers realise them. -/


/-- Unification completeness (+ the list version), bounded by the measure
    `2 * (size of the unified result) + flag` so a single strong induction on the
    bound `N` covers all recursive calls (`flag = 0` for `UnifyRel`, `1` for the
    list — the offset makes the singleton-list ↔ element step strictly decrease). -/
theorem UnifyRel.complete_aux : ∀ (N : Nat),
    (∀ {a b : Ty} {U : Subst}, 2 * (U.onTy a).size < N → a.IsLC → b.IsLC →
        Unifies U a b → ∃ S, UnifyRel a b S) ∧
    (∀ {as bs : List Ty} {U : Subst}, 2 * TyList.size (as.map U.onTy) + 1 < N →
        (∀ t ∈ as, t.IsLC) → (∀ t ∈ bs, t.IsLC) → as.length = bs.length →
        as.map U.onTy = bs.map U.onTy → ∃ S, UnifyRelList as bs S) := by
  intro N
  induction N with
  | zero => exact ⟨fun h => absurd h (by omega), fun h => absurd h (by omega)⟩
  | succ N ih =>
    obtain ⟨ihU, ihL⟩ := ih
    refine ⟨?_, ?_⟩
    · -- UnifyRel
      intro a b U hsz ha hb hU
      cases a with
      | bvar i => cases ha with | bvar h => omega
      | prim p =>
        cases b with
        | bvar i => cases hb with | bvar h => omega
        | prim q =>
          simp only [Unifies, Subst.onTy_prim, Ty.prim.injEq] at hU
          subst hU; exact ⟨[], .prim⟩
        | fvar m => exact ⟨[(m, .prim p)], .fvarR (by simp) (by simp [Ty.freeVars])⟩
        | arrow b₁ b₂ => simp [Unifies] at hU
        | customTy nm bs => simp [Unifies] at hU
      | fvar n =>
        cases b with
        | bvar i => cases hb with | bvar h => omega
        | fvar m =>
          by_cases hnm : n = m
          · subst hnm; exact ⟨[], .fvarRefl⟩
          · exact ⟨[(n, .fvar m)], .fvarL (by simp only [ne_eq, Ty.fvar.injEq]; omega)
              (by simp only [Ty.freeVars, List.mem_singleton]; omega)⟩
        | prim q =>
          by_cases hocc : n ∈ (Ty.prim q).freeVars
          · have hlt := Ty.size_onTy_fvar_lt (S := U) hocc (by simp)
            simp only [Unifies] at hU; rw [hU] at hlt; omega
          · exact ⟨[(n, .prim q)], .fvarL (by simp) hocc⟩
        | arrow b₁ b₂ =>
          by_cases hocc : n ∈ (Ty.arrow b₁ b₂).freeVars
          · have hlt := Ty.size_onTy_fvar_lt (S := U) hocc (by simp)
            simp only [Unifies] at hU; rw [hU] at hlt; omega
          · exact ⟨[(n, .arrow b₁ b₂)], .fvarL (by simp) hocc⟩
        | customTy nm bs =>
          by_cases hocc : n ∈ (Ty.customTy nm bs).freeVars
          · have hlt := Ty.size_onTy_fvar_lt (S := U) hocc (by simp)
            simp only [Unifies] at hU; rw [hU] at hlt; omega
          · exact ⟨[(n, .customTy nm bs)], .fvarL (by simp) hocc⟩
      | arrow a₁ a₂ =>
        cases ha with
        | arrow ha₁ ha₂ =>
        cases b with
        | bvar i => cases hb with | bvar h => omega
        | fvar m =>
          by_cases hocc : m ∈ (Ty.arrow a₁ a₂).freeVars
          · have hlt := Ty.size_onTy_fvar_lt (S := U) hocc (by simp)
            simp only [Unifies] at hU; rw [hU] at hlt; omega
          · exact ⟨[(m, .arrow a₁ a₂)], .fvarR (by simp) hocc⟩
        | prim q => simp [Unifies] at hU
        | customTy nm bs => simp [Unifies] at hU
        | arrow b₁ b₂ =>
          cases hb with
          | arrow hb₁ hb₂ =>
          have hpsz : (U.onTy (.arrow a₁ a₂)).size
              = 1 + (U.onTy a₁).size + (U.onTy a₂).size := by simp [Subst.onTy_arrow, Ty.size]
          simp only [Unifies, Subst.onTy_arrow, Ty.arrow.injEq] at hU
          obtain ⟨S₁, h₁⟩ := ihU (a := a₁) (b := b₁) (U := U)
            (by rw [hpsz] at hsz; omega) ha₁ hb₁ hU.1
          obtain ⟨R, hR⟩ := UnifyRel.greatest h₁ U hU.1
          have hS₁lc := UnifyRel.lc h₁ ha₁ hb₁
          obtain ⟨S₂, h₂⟩ := ihU (a := S₁.onTy a₂) (b := S₁.onTy b₂) (U := R)
            (by rw [← hR a₂]; rw [hpsz] at hsz; omega)
            (Subst.onTy_lc hS₁lc ha₂) (Subst.onTy_lc hS₁lc hb₂)
            (by show R.onTy (S₁.onTy a₂) = R.onTy (S₁.onTy b₂); rw [← hR a₂, ← hR b₂]; exact hU.2)
          exact ⟨S₁ ++ S₂, .arrow h₁ h₂⟩
      | customTy nm tys₁ =>
        cases b with
        | bvar i => cases hb with | bvar h => omega
        | fvar m =>
          by_cases hocc : m ∈ (Ty.customTy nm tys₁).freeVars
          · have hlt := Ty.size_onTy_fvar_lt (S := U) hocc (by simp)
            simp only [Unifies] at hU; rw [hU] at hlt; omega
          · exact ⟨[(m, .customTy nm tys₁)], .fvarR (by simp) hocc⟩
        | prim q => simp [Unifies] at hU
        | arrow b₁ b₂ => simp [Unifies] at hU
        | customTy nm' tys₂ =>
          have hcsz : (U.onTy (.customTy nm tys₁)).size
              = 1 + TyList.size (tys₁.map U.onTy) := by simp [Subst.onTy_customTy, Ty.size]
          simp only [Unifies, Subst.onTy_customTy, Ty.customTy.injEq] at hU
          obtain ⟨rfl, hmapeq⟩ := hU
          have hlen : tys₁.length = tys₂.length := by
            have := congrArg List.length hmapeq; simpa using this
          obtain ⟨S, hS⟩ := ihL (as := tys₁) (bs := tys₂) (U := U)
            (by rw [hcsz] at hsz; omega)
            (fun t ht => by cases ha with | customTy h => exact h t ht)
            (fun t ht => by cases hb with | customTy h => exact h t ht)
            hlen hmapeq
          exact ⟨S, .customTy hS⟩
    · -- UnifyRelList
      intro as bs U hsz has hbs hlen hmap
      cases as with
      | nil =>
        cases bs with
        | nil => exact ⟨[], .nil⟩
        | cons t₂ ts₂ => simp at hlen
      | cons t₁ ts₁ =>
        cases bs with
        | nil => simp at hlen
        | cons t₂ ts₂ =>
          simp only [List.map_cons, List.cons.injEq] at hmap
          have htsz : TyList.size ((t₁ :: ts₁).map U.onTy)
              = (U.onTy t₁).size + TyList.size (ts₁.map U.onTy) := by
            simp [List.map_cons, TyList.size]
          have ht1pos := @Ty.size_pos (U.onTy t₁)
          obtain ⟨S₁, h₁⟩ := ihU (a := t₁) (b := t₂) (U := U)
            (by rw [htsz] at hsz; omega) (has t₁ List.mem_cons_self)
            (hbs t₂ List.mem_cons_self) hmap.1
          obtain ⟨R, hR⟩ := UnifyRel.greatest h₁ U hmap.1
          have hS₁lc := UnifyRel.lc h₁ (has t₁ List.mem_cons_self) (hbs t₂ List.mem_cons_self)
          have key : ∀ l : List Ty, l.map (R.onTy ∘ S₁.onTy) = l.map U.onTy := by
            intro l; apply List.map_congr_left; intro t _; exact (hR t).symm
          have hkey1 : (ts₁.map S₁.onTy).map R.onTy = ts₁.map U.onTy := by
            rw [List.map_map]; exact key ts₁
          have hmaptail : (ts₁.map S₁.onTy).map R.onTy = (ts₂.map S₁.onTy).map R.onTy := by
            rw [List.map_map, List.map_map, key, key]; exact hmap.2
          obtain ⟨S₂, h₂⟩ := ihL (as := ts₁.map S₁.onTy) (bs := ts₂.map S₁.onTy) (U := R)
            (by rw [hkey1]; rw [htsz] at hsz; omega)
            (by
              intro t ht; obtain ⟨t0, ht0, rfl⟩ := List.mem_map.mp ht
              exact Subst.onTy_lc hS₁lc (has t0 (List.mem_cons_of_mem _ ht0)))
            (by
              intro t ht; obtain ⟨t0, ht0, rfl⟩ := List.mem_map.mp ht
              exact Subst.onTy_lc hS₁lc (hbs t0 (List.mem_cons_of_mem _ ht0)))
            (by simp only [List.length_map]; have := hlen; simpa using this)
            hmaptail
          exact ⟨S₁ ++ S₂, .cons h₁ h₂⟩

/-- Unification completeness: if `a` and `b` (both LC) have a unifier `U`, then a
    `UnifyRel` derivation exists. -/
theorem UnifyRel.complete {a b : Ty} {U : Subst}
    (ha : a.IsLC) (hb : b.IsLC) (hU : Unifies U a b) : ∃ S, UnifyRel a b S :=
  (UnifyRel.complete_aux (2 * (U.onTy a).size + 1)).1 (by omega) ha hb hU

/-! ### Rigidity-aware unification completeness

The **symmetric** `UnifyRel` can always be oriented to **avoid a rigid set `K`**,
given only that some LC unifier `U` keeps every `k ∈ K` fixed — crucially with NO
restriction that one operand's free vars lie in `K`. The structural recursion
threads the `K`-fixing witness via `greatest_K`: var–var is oriented away from
`K`, and a rigid var meeting a non-variable is *vacuous* (`U` fixes it, so it
can't equal a non-var image). The produced `S` avoids `K` by construction, so the
no-skolem-escape obligation (`hesc1`) is structural rather than a property to
re-establish — this is what replaced the old post-hoc escape-check approach. -/
theorem UnifyRel.complete_K_aux {K : List Nat} : ∀ (N : Nat),
    (∀ {a b : Ty} {U : Subst}, 2 * (U.onTy a).size < N → a.IsLC → b.IsLC →
        (∀ p ∈ U, p.2.IsLC) → Unifies U a b → (∀ k ∈ K, U.onTy (.fvar k) = .fvar k) →
        ∃ S, UnifyRel a b S ∧ (∀ p ∈ S, p.1 ∉ K)) ∧
    (∀ {as bs : List Ty} {U : Subst}, 2 * TyList.size (as.map U.onTy) + 1 < N →
        (∀ t ∈ as, t.IsLC) → (∀ t ∈ bs, t.IsLC) → (∀ p ∈ U, p.2.IsLC) →
        as.length = bs.length → as.map U.onTy = bs.map U.onTy →
        (∀ k ∈ K, U.onTy (.fvar k) = .fvar k) →
        ∃ S, UnifyRelList as bs S ∧ (∀ p ∈ S, p.1 ∉ K)) := by
  intro N
  induction N with
  | zero => exact ⟨fun h => absurd h (by omega), fun h => absurd h (by omega)⟩
  | succ N ih =>
    obtain ⟨ihU, ihL⟩ := ih
    refine ⟨?_, ?_⟩
    · intro a b U hsz ha hb hUlc hU hUK
      cases a with
      | bvar i => cases ha with | bvar h => omega
      | prim p =>
        cases b with
        | bvar i => cases hb with | bvar h => omega
        | prim q =>
          simp only [Unifies, Subst.onTy_prim, Ty.prim.injEq] at hU
          subst hU; exact ⟨[], .prim, by simp⟩
        | fvar m =>
          have hmK : m ∉ K := fun hmK => by
            have h1 : U.onTy (Ty.prim p) = U.onTy (Ty.fvar m) := hU
            rw [hUK m hmK, Subst.onTy_prim] at h1; exact absurd h1 (by simp)
          exact ⟨[(m, .prim p)], .fvarR (by simp) (by simp [Ty.freeVars]),
            by intro p' hp'; rw [List.mem_singleton] at hp'; subst hp'; exact hmK⟩
        | arrow b₁ b₂ => simp [Unifies] at hU
        | customTy nm bs => simp [Unifies] at hU
      | fvar n =>
        cases b with
        | bvar i => cases hb with | bvar h => omega
        | fvar m =>
          by_cases hnm : n = m
          · subst hnm; exact ⟨[], .fvarRefl, by simp⟩
          · by_cases hnK : n ∈ K
            · have hmK : m ∉ K := fun hmK => by
                have h1 : U.onTy (Ty.fvar n) = U.onTy (Ty.fvar m) := hU
                rw [hUK n hnK, hUK m hmK] at h1
                simp only [Ty.fvar.injEq] at h1; exact hnm h1
              exact ⟨[(m, .fvar n)], .fvarR (by simp only [ne_eq, Ty.fvar.injEq]; omega)
                (by simp only [Ty.freeVars, List.mem_singleton]; omega),
                by intro p' hp'; rw [List.mem_singleton] at hp'; subst hp'; exact hmK⟩
            · exact ⟨[(n, .fvar m)], .fvarL (by simp only [ne_eq, Ty.fvar.injEq]; omega)
                (by simp only [Ty.freeVars, List.mem_singleton]; omega),
                by intro p' hp'; rw [List.mem_singleton] at hp'; subst hp'; exact hnK⟩
        | prim q =>
          by_cases hocc : n ∈ (Ty.prim q).freeVars
          · have hlt := Ty.size_onTy_fvar_lt (S := U) hocc (by simp)
            simp only [Unifies] at hU; rw [hU] at hlt; omega
          · by_cases hnK : n ∈ K
            · exfalso
              have h1 : U.onTy (Ty.fvar n) = U.onTy (Ty.prim q) := hU
              rw [hUK n hnK, Subst.onTy_prim] at h1; exact absurd h1 (by simp)
            · exact ⟨[(n, .prim q)], .fvarL (by simp) hocc,
                by intro p' hp'; rw [List.mem_singleton] at hp'; subst hp'; exact hnK⟩
        | arrow b₁ b₂ =>
          by_cases hocc : n ∈ (Ty.arrow b₁ b₂).freeVars
          · have hlt := Ty.size_onTy_fvar_lt (S := U) hocc (by simp)
            simp only [Unifies] at hU; rw [hU] at hlt; omega
          · by_cases hnK : n ∈ K
            · exfalso
              have h1 : U.onTy (Ty.fvar n) = U.onTy (Ty.arrow b₁ b₂) := hU
              rw [hUK n hnK, Subst.onTy_arrow] at h1; exact absurd h1 (by simp)
            · exact ⟨[(n, .arrow b₁ b₂)], .fvarL (by simp) hocc,
                by intro p' hp'; rw [List.mem_singleton] at hp'; subst hp'; exact hnK⟩
        | customTy nm bs =>
          by_cases hocc : n ∈ (Ty.customTy nm bs).freeVars
          · have hlt := Ty.size_onTy_fvar_lt (S := U) hocc (by simp)
            simp only [Unifies] at hU; rw [hU] at hlt; omega
          · by_cases hnK : n ∈ K
            · exfalso
              have h1 : U.onTy (Ty.fvar n) = U.onTy (Ty.customTy nm bs) := hU
              rw [hUK n hnK, Subst.onTy_customTy] at h1; exact absurd h1 (by simp)
            · exact ⟨[(n, .customTy nm bs)], .fvarL (by simp) hocc,
                by intro p' hp'; rw [List.mem_singleton] at hp'; subst hp'; exact hnK⟩
      | arrow a₁ a₂ =>
        cases ha with
        | arrow ha₁ ha₂ =>
        cases b with
        | bvar i => cases hb with | bvar h => omega
        | fvar m =>
          by_cases hocc : m ∈ (Ty.arrow a₁ a₂).freeVars
          · have hlt := Ty.size_onTy_fvar_lt (S := U) hocc (by simp)
            simp only [Unifies] at hU; rw [hU] at hlt; omega
          · by_cases hmK : m ∈ K
            · exfalso
              have h1 : U.onTy (Ty.arrow a₁ a₂) = U.onTy (Ty.fvar m) := hU
              rw [hUK m hmK, Subst.onTy_arrow] at h1; exact absurd h1 (by simp)
            · exact ⟨[(m, .arrow a₁ a₂)], .fvarR (by simp) hocc,
                by intro p' hp'; rw [List.mem_singleton] at hp'; subst hp'; exact hmK⟩
        | prim q => simp [Unifies] at hU
        | customTy nm bs => simp [Unifies] at hU
        | arrow b₁ b₂ =>
          cases hb with
          | arrow hb₁ hb₂ =>
          have hpsz : (U.onTy (.arrow a₁ a₂)).size = 1 + (U.onTy a₁).size + (U.onTy a₂).size := by
            simp [Subst.onTy_arrow, Ty.size]
          simp only [Unifies, Subst.onTy_arrow, Ty.arrow.injEq] at hU
          obtain ⟨S₁, h₁, hS₁K⟩ := ihU (a := a₁) (b := b₁) (U := U)
            (by rw [hpsz] at hsz; omega) ha₁ hb₁ hUlc hU.1 hUK
          have hS₁lc := UnifyRel.lc h₁ ha₁ hb₁
          obtain ⟨R, hR, hRlc, hRK⟩ := UnifyRel.greatest_K h₁ U hUlc hU.1 hUK
          obtain ⟨S₂, h₂, hS₂K⟩ := ihU (a := S₁.onTy a₂) (b := S₁.onTy b₂) (U := R)
            (by rw [← hR a₂]; rw [hpsz] at hsz; omega)
            (Subst.onTy_lc hS₁lc ha₂) (Subst.onTy_lc hS₁lc hb₂) hRlc
            (by show R.onTy (S₁.onTy a₂) = R.onTy (S₁.onTy b₂); rw [← hR a₂, ← hR b₂]; exact hU.2) hRK
          exact ⟨S₁ ++ S₂, .arrow h₁ h₂, by
            intro p hp; rcases List.mem_append.mp hp with h | h
            · exact hS₁K p h
            · exact hS₂K p h⟩
      | customTy nm tys₁ =>
        cases b with
        | bvar i => cases hb with | bvar h => omega
        | fvar m =>
          by_cases hocc : m ∈ (Ty.customTy nm tys₁).freeVars
          · have hlt := Ty.size_onTy_fvar_lt (S := U) hocc (by simp)
            simp only [Unifies] at hU; rw [hU] at hlt; omega
          · by_cases hmK : m ∈ K
            · exfalso
              have h1 : U.onTy (Ty.customTy nm tys₁) = U.onTy (Ty.fvar m) := hU
              rw [hUK m hmK, Subst.onTy_customTy] at h1; exact absurd h1 (by simp)
            · exact ⟨[(m, .customTy nm tys₁)], .fvarR (by simp) hocc,
                by intro p' hp'; rw [List.mem_singleton] at hp'; subst hp'; exact hmK⟩
        | prim q => simp [Unifies] at hU
        | arrow b₁ b₂ => simp [Unifies] at hU
        | customTy nm' tys₂ =>
          have hcsz : (U.onTy (.customTy nm tys₁)).size = 1 + TyList.size (tys₁.map U.onTy) := by
            simp [Subst.onTy_customTy, Ty.size]
          simp only [Unifies, Subst.onTy_customTy, Ty.customTy.injEq] at hU
          obtain ⟨rfl, hmapeq⟩ := hU
          have hlen : tys₁.length = tys₂.length := by
            have := congrArg List.length hmapeq; simpa using this
          obtain ⟨S, hS, hSK⟩ := ihL (as := tys₁) (bs := tys₂) (U := U)
            (by rw [hcsz] at hsz; omega)
            (fun t ht => by cases ha with | customTy h => exact h t ht)
            (fun t ht => by cases hb with | customTy h => exact h t ht)
            hUlc hlen hmapeq hUK
          exact ⟨S, .customTy hS, hSK⟩
    · intro as bs U hsz has hbs hUlc hlen hmap hUK
      cases as with
      | nil =>
        cases bs with
        | nil => exact ⟨[], .nil, by simp⟩
        | cons t₂ ts₂ => simp at hlen
      | cons t₁ ts₁ =>
        cases bs with
        | nil => simp at hlen
        | cons t₂ ts₂ =>
          simp only [List.map_cons, List.cons.injEq] at hmap
          have htsz : TyList.size ((t₁ :: ts₁).map U.onTy)
              = (U.onTy t₁).size + TyList.size (ts₁.map U.onTy) := by simp [List.map_cons, TyList.size]
          have ht1pos := @Ty.size_pos (U.onTy t₁)
          obtain ⟨S₁, h₁, hS₁K⟩ := ihU (a := t₁) (b := t₂) (U := U)
            (by rw [htsz] at hsz; omega) (has t₁ List.mem_cons_self) (hbs t₂ List.mem_cons_self)
            hUlc hmap.1 hUK
          have hS₁lc := UnifyRel.lc h₁ (has t₁ List.mem_cons_self) (hbs t₂ List.mem_cons_self)
          obtain ⟨R, hR, hRlc, hRK⟩ := UnifyRel.greatest_K h₁ U hUlc hmap.1 hUK
          have key : ∀ l : List Ty, l.map (R.onTy ∘ S₁.onTy) = l.map U.onTy := by
            intro l; apply List.map_congr_left; intro t _; exact (hR t).symm
          have hkey1 : (ts₁.map S₁.onTy).map R.onTy = ts₁.map U.onTy := by
            rw [List.map_map]; exact key ts₁
          have hmaptail : (ts₁.map S₁.onTy).map R.onTy = (ts₂.map S₁.onTy).map R.onTy := by
            rw [List.map_map, List.map_map, key, key]; exact hmap.2
          obtain ⟨S₂, h₂, hS₂K⟩ := ihL (as := ts₁.map S₁.onTy) (bs := ts₂.map S₁.onTy) (U := R)
            (by rw [hkey1]; rw [htsz] at hsz; omega)
            (by intro t ht; obtain ⟨t0, ht0, rfl⟩ := List.mem_map.mp ht
                exact Subst.onTy_lc hS₁lc (has t0 (List.mem_cons_of_mem _ ht0)))
            (by intro t ht; obtain ⟨t0, ht0, rfl⟩ := List.mem_map.mp ht
                exact Subst.onTy_lc hS₁lc (hbs t0 (List.mem_cons_of_mem _ ht0)))
            hRlc
            (by simp only [List.length_map]; have := hlen; simpa using this)
            hmaptail hRK
          exact ⟨S₁ ++ S₂, .cons h₁ h₂, by
            intro p hp; rcases List.mem_append.mp hp with h | h
            · exact hS₁K p h
            · exact hS₂K p h⟩

/-- A `K`-fixing LC unifier of two LC types yields a `UnifyRel` derivation that
    **avoids `K`** — with no side-condition on the operands' free variables. The
    rigidity-aware orientation that makes annotated-`let` completeness's `hesc1`
    structural. -/
theorem UnifyRel.complete_K {K : List Nat} {a b : Ty} {U : Subst}
    (ha : a.IsLC) (hb : b.IsLC) (hUlc : ∀ p ∈ U, p.2.IsLC)
    (hU : Unifies U a b) (hUK : ∀ k ∈ K, U.onTy (.fvar k) = .fvar k) :
    ∃ S, UnifyRel a b S ∧ (∀ p ∈ S, p.1 ∉ K) :=
  (UnifyRel.complete_K_aux (2 * (U.onTy a).size + 1)).1 (by omega) ha hb hUlc hU hUK


/-! ### Completeness of the executable unifier -/

/-- **Rigidity-aware unify completeness.** When the (LC) inputs admit an LC unifier
    `U` that keeps every `k ∈ K` rigid, the rigidity-aware `unifyCoreK K` succeeds.
    Fuses the size induction of `unifyCore_complete_aux` with the orientation
    reasoning of `UnifyRel.complete_K_aux`: at a variable step the `K`-fixing `U`
    rules out the branch that `unifyCoreK` would refuse (binding a rigid var). -/
theorem unifyCoreK_complete_aux {K : List Nat} : ∀ (N : Nat),
    (∀ {a b : Ty} {U : Subst}, 2 * (U.onTy a).size < N → a.IsLC → b.IsLC →
        (∀ p ∈ U, p.2.IsLC) → Unifies U a b → (∀ k ∈ K, U.onTy (.fvar k) = .fvar k) →
        (unifyCoreK K a b).isSome) ∧
    (∀ {as bs : List Ty} {U : Subst}, 2 * TyList.size (as.map U.onTy) + 1 < N →
        (∀ t ∈ as, t.IsLC) → (∀ t ∈ bs, t.IsLC) → (∀ p ∈ U, p.2.IsLC) →
        as.length = bs.length → as.map U.onTy = bs.map U.onTy →
        (∀ k ∈ K, U.onTy (.fvar k) = .fvar k) →
        (unifyListCoreK K as bs).isSome) := by
  intro N
  induction N with
  | zero => exact ⟨fun h => absurd h (by omega), fun h => absurd h (by omega)⟩
  | succ N ih =>
    obtain ⟨ihU, ihL⟩ := ih
    refine ⟨?_, ?_⟩
    · intro a b U hsz ha hb hUlc hU hUK
      cases a with
      | bvar i => cases ha with | bvar h => omega
      | prim p =>
        cases b with
        | bvar i => cases hb with | bvar h => omega
        | prim q => simp only [Unifies, Subst.onTy_prim, Ty.prim.injEq] at hU; subst hU; simp [unifyCoreK]
        | fvar m =>
          have hmK : m ∉ K := fun hmK => by
            have h1 : U.onTy (Ty.prim p) = U.onTy (Ty.fvar m) := hU
            rw [hUK m hmK, Subst.onTy_prim] at h1; exact absurd h1 (by simp)
          simp [unifyCoreK, hmK, Ty.freeVars]
        | arrow b₁ b₂ => simp [Unifies] at hU
        | customTy nm bs => simp [Unifies] at hU
      | fvar n =>
        cases b with
        | bvar i => cases hb with | bvar h => omega
        | fvar m =>
          by_cases hnm : n = m
          · subst hnm; simp [unifyCoreK]
          · by_cases hnK : n ∈ K
            · have hmK : m ∉ K := fun hmK => by
                have h1 : U.onTy (Ty.fvar n) = U.onTy (Ty.fvar m) := hU
                rw [hUK n hnK, hUK m hmK] at h1; simp only [Ty.fvar.injEq] at h1; exact hnm h1
              simp [unifyCoreK, hnm, hnK, hmK]
            · simp [unifyCoreK, hnm, hnK]
        | prim q =>
          by_cases hocc : n ∈ (Ty.prim q).freeVars
          · have hlt := Ty.size_onTy_fvar_lt (S := U) hocc (by simp)
            simp only [Unifies] at hU; rw [hU] at hlt; omega
          · by_cases hnK : n ∈ K
            · exfalso
              have h1 : U.onTy (Ty.fvar n) = U.onTy (Ty.prim q) := hU
              rw [hUK n hnK, Subst.onTy_prim] at h1; exact absurd h1 (by simp)
            · simp [unifyCoreK, hnK, hocc]
        | arrow b₁ b₂ =>
          by_cases hocc : n ∈ (Ty.arrow b₁ b₂).freeVars
          · have hlt := Ty.size_onTy_fvar_lt (S := U) hocc (by simp)
            simp only [Unifies] at hU; rw [hU] at hlt; omega
          · by_cases hnK : n ∈ K
            · exfalso
              have h1 : U.onTy (Ty.fvar n) = U.onTy (Ty.arrow b₁ b₂) := hU
              rw [hUK n hnK, Subst.onTy_arrow] at h1; exact absurd h1 (by simp)
            · simp [unifyCoreK, hnK, hocc]
        | customTy nm bs =>
          by_cases hocc : n ∈ (Ty.customTy nm bs).freeVars
          · have hlt := Ty.size_onTy_fvar_lt (S := U) hocc (by simp)
            simp only [Unifies] at hU; rw [hU] at hlt; omega
          · by_cases hnK : n ∈ K
            · exfalso
              have h1 : U.onTy (Ty.fvar n) = U.onTy (Ty.customTy nm bs) := hU
              rw [hUK n hnK, Subst.onTy_customTy] at h1; exact absurd h1 (by simp)
            · simp [unifyCoreK, hnK, hocc]
      | arrow a₁ a₂ =>
        cases ha with
        | arrow ha₁ ha₂ =>
        cases b with
        | bvar i => cases hb with | bvar h => omega
        | fvar m =>
          by_cases hocc : m ∈ (Ty.arrow a₁ a₂).freeVars
          · have hlt := Ty.size_onTy_fvar_lt (S := U) hocc (by simp)
            simp only [Unifies] at hU; rw [hU] at hlt; omega
          · by_cases hmK : m ∈ K
            · exfalso
              have h1 : U.onTy (Ty.arrow a₁ a₂) = U.onTy (Ty.fvar m) := hU
              rw [hUK m hmK, Subst.onTy_arrow] at h1; exact absurd h1 (by simp)
            · simp [unifyCoreK, hmK, hocc]
        | prim q => simp [Unifies] at hU
        | customTy nm bs => simp [Unifies] at hU
        | arrow b₁ b₂ =>
          cases hb with
          | arrow hb₁ hb₂ =>
          have hpsz : (U.onTy (.arrow a₁ a₂)).size = 1 + (U.onTy a₁).size + (U.onTy a₂).size := by
            simp [Subst.onTy_arrow, Ty.size]
          simp only [Unifies, Subst.onTy_arrow, Ty.arrow.injEq] at hU
          obtain ⟨⟨S₁, h₁, _⟩, he1⟩ := Option.isSome_iff_exists.mp
            (ihU (a := a₁) (b := b₁) (U := U) (by rw [hpsz] at hsz; omega) ha₁ hb₁ hUlc hU.1 hUK)
          have hS₁lc := UnifyRel.lc h₁ ha₁ hb₁
          obtain ⟨R, hR, hRlc, hRK⟩ := UnifyRel.greatest_K h₁ U hUlc hU.1 hUK
          obtain ⟨⟨S₂, h₂, _⟩, he2⟩ := Option.isSome_iff_exists.mp
            (ihU (a := S₁.onTy a₂) (b := S₁.onTy b₂) (U := R) (by rw [← hR a₂]; rw [hpsz] at hsz; omega)
              (Subst.onTy_lc hS₁lc ha₂) (Subst.onTy_lc hS₁lc hb₂) hRlc
              (by show R.onTy (S₁.onTy a₂) = R.onTy (S₁.onTy b₂); rw [← hR a₂, ← hR b₂]; exact hU.2) hRK)
          rw [unifyCoreK]; simp only [he1, he2, Option.isSome_some]
      | customTy nm tys₁ =>
        cases b with
        | bvar i => cases hb with | bvar h => omega
        | fvar m =>
          by_cases hocc : m ∈ (Ty.customTy nm tys₁).freeVars
          · have hlt := Ty.size_onTy_fvar_lt (S := U) hocc (by simp)
            simp only [Unifies] at hU; rw [hU] at hlt; omega
          · by_cases hmK : m ∈ K
            · exfalso
              have h1 : U.onTy (Ty.customTy nm tys₁) = U.onTy (Ty.fvar m) := hU
              rw [hUK m hmK, Subst.onTy_customTy] at h1; exact absurd h1 (by simp)
            · simp [unifyCoreK, hmK, hocc]
        | prim q => simp [Unifies] at hU
        | arrow b₁ b₂ => simp [Unifies] at hU
        | customTy nm' tys₂ =>
          have hcsz : (U.onTy (.customTy nm tys₁)).size = 1 + TyList.size (tys₁.map U.onTy) := by
            simp [Subst.onTy_customTy, Ty.size]
          simp only [Unifies, Subst.onTy_customTy, Ty.customTy.injEq] at hU
          obtain ⟨rfl, hmapeq⟩ := hU
          have hlen : tys₁.length = tys₂.length := by
            have := congrArg List.length hmapeq; simpa using this
          obtain ⟨⟨S, hS, _⟩, heL⟩ := Option.isSome_iff_exists.mp
            (ihL (as := tys₁) (bs := tys₂) (U := U) (by rw [hcsz] at hsz; omega)
              (fun t ht => by cases ha with | customTy h => exact h t ht)
              (fun t ht => by cases hb with | customTy h => exact h t ht)
              hUlc hlen hmapeq hUK)
          rw [unifyCoreK]; simp [heL]
    · intro as bs U hsz has hbs hUlc hlen hmap hUK
      cases as with
      | nil =>
        cases bs with
        | nil => simp [unifyListCoreK]
        | cons t₂ ts₂ => simp at hlen
      | cons t₁ ts₁ =>
        cases bs with
        | nil => simp at hlen
        | cons t₂ ts₂ =>
          simp only [List.map_cons, List.cons.injEq] at hmap
          have htsz : TyList.size ((t₁ :: ts₁).map U.onTy)
              = (U.onTy t₁).size + TyList.size (ts₁.map U.onTy) := by simp [List.map_cons, TyList.size]
          have ht1pos := @Ty.size_pos (U.onTy t₁)
          obtain ⟨⟨S₁, h₁, _⟩, he1⟩ := Option.isSome_iff_exists.mp
            (ihU (a := t₁) (b := t₂) (U := U) (by rw [htsz] at hsz; omega)
              (has t₁ List.mem_cons_self) (hbs t₂ List.mem_cons_self) hUlc hmap.1 hUK)
          have hS₁lc := UnifyRel.lc h₁ (has t₁ List.mem_cons_self) (hbs t₂ List.mem_cons_self)
          obtain ⟨R, hR, hRlc, hRK⟩ := UnifyRel.greatest_K h₁ U hUlc hmap.1 hUK
          have key : ∀ l : List Ty, l.map (R.onTy ∘ S₁.onTy) = l.map U.onTy := by
            intro l; apply List.map_congr_left; intro t _; exact (hR t).symm
          have hkey1 : (ts₁.map S₁.onTy).map R.onTy = ts₁.map U.onTy := by
            rw [List.map_map]; exact key ts₁
          have hmaptail : (ts₁.map S₁.onTy).map R.onTy = (ts₂.map S₁.onTy).map R.onTy := by
            rw [List.map_map, List.map_map, key, key]; exact hmap.2
          obtain ⟨⟨S₂, h₂, _⟩, he2⟩ := Option.isSome_iff_exists.mp
            (ihL (as := ts₁.map S₁.onTy) (bs := ts₂.map S₁.onTy) (U := R)
              (by rw [hkey1]; rw [htsz] at hsz; omega)
              (by intro t ht; obtain ⟨t0, ht0, rfl⟩ := List.mem_map.mp ht
                  exact Subst.onTy_lc hS₁lc (has t0 (List.mem_cons_of_mem _ ht0)))
              (by intro t ht; obtain ⟨t0, ht0, rfl⟩ := List.mem_map.mp ht
                  exact Subst.onTy_lc hS₁lc (hbs t0 (List.mem_cons_of_mem _ ht0)))
              hRlc (by simp only [List.length_map]; have := hlen; simpa using this) hmaptail hRK)
          rw [unifyListCoreK]; simp only [he1, he2, Option.isSome_some]

/-- `unifyCoreK` completeness wrapper. -/
theorem unifyCoreK_complete {K : List Nat} {a b : Ty} {U : Subst}
    (ha : a.IsLC) (hb : b.IsLC) (hUlc : ∀ p ∈ U, p.2.IsLC)
    (hU : Unifies U a b) (hUK : ∀ k ∈ K, U.onTy (.fvar k) = .fvar k) :
    (unifyCoreK K a b).isSome :=
  (unifyCoreK_complete_aux (2 * (U.onTy a).size + 1)).1 (by omega) ha hb hUlc hU hUK

/-- `unify` completeness: `unify` succeeds whenever the (LC) inputs are unifiable.
    Reduces to `unifyCoreK_complete` at the empty rigid set — the MGU `S` is LC by
    `UnifyRel.lc`, and the empty-`K` fixing condition is vacuous. -/
theorem unify_complete {a b : Ty} {S : Subst} (h : UnifyRel a b S)
    (ha : a.IsLC) (hb : b.IsLC) : (unify a b).isSome := by
  have hcore : (unifyCore a b).isSome := by
    have := unifyCoreK_complete (K := []) ha hb (UnifyRel.lc h ha hb) h.unifies (by simp)
    simpa [unifyCore, Option.isSome_map] using this
  simpa [unify, Option.isSome_map] using hcore

def RecSpec.tfvs : RecSpec → List Nat
  | .mono τ => τ.freeVars
  | .poly σ => σ.body.freeVars

/-- A whole substitution applied to an interval-avoiding type yields an
    interval-avoiding type. -/
theorem Subst.onTy_avoidsItv {lo hi : Nat} :
    ∀ {S : Subst}, (∀ p ∈ S, ∀ v ∈ p.2.freeVars, v < lo ∨ hi ≤ v) →
    ∀ {τ : Ty}, (∀ v ∈ τ.freeVars, v < lo ∨ hi ≤ v) →
    ∀ v ∈ (S.onTy τ).freeVars, v < lo ∨ hi ≤ v := by
  intro S
  induction S with
  | nil => intro _ τ hτ v hv; rw [Subst.onTy_nil] at hv; exact hτ v hv
  | cons hd S' ih =>
    obtain ⟨Z, U⟩ := hd
    intro hS τ hτ v hv
    rw [show ((Z, U) :: S') = [(Z, U)] ++ S' from rfl, Subst.onTy_append] at hv
    refine ih (fun p hp => hS p (List.mem_cons_of_mem _ hp)) ?_ v hv
    intro w hw
    rcases Ty.mem_freeVars_substFvar hw with h | h
    · exact hτ w h
    · exact hS (Z, U) (List.mem_cons_self ..) w h

/-- A whole substitution applied to an interval-avoiding context env stays
    interval-avoiding. -/
theorem Subst.onCtx_avoidsItv {lo hi : Nat} {S : Subst} {ctx : Ctx}
    (hS : ∀ p ∈ S, ∀ v ∈ p.2.freeVars, v < lo ∨ hi ≤ v)
    (hctx : ∀ M ∈ ctx.env, ∀ v ∈ M.body.freeVars, v < lo ∨ hi ≤ v) :
    ∀ M ∈ (S.onCtx ctx).env, ∀ v ∈ M.body.freeVars, v < lo ∨ hi ≤ v := by
  intro M hM
  simp only [Subst.onCtx, Subst.onEnv] at hM
  obtain ⟨M0, hM0, rfl⟩ := List.mem_map.mp hM
  simp only [Subst.onPolyTy]
  exact Subst.onTy_avoidsItv hS (hctx M0 hM0)

/-- Opening with interval-avoiding type args preserves interval-avoidance. -/
theorem Ty.openWith_avoidsItv {lo hi : Nat} {Vs : List Ty}
    (hVs : ∀ t ∈ Vs, ∀ v ∈ t.freeVars, v < lo ∨ hi ≤ v) :
    ∀ {X : Ty}, (∀ v ∈ X.freeVars, v < lo ∨ hi ≤ v) →
    ∀ v ∈ (Ty.openWith Vs X).freeVars, v < lo ∨ hi ≤ v := by
  intro X
  induction X using Ty.rec_strong with
  | prim p => intro _ v hv; simp [Ty.openWith, Ty.instantiate, Ty.freeVars] at hv
  | fvar n =>
    intro hX v hv
    simp only [Ty.openWith, Ty.instantiate, Ty.freeVars, List.mem_singleton] at hv
    rw [hv]; exact hX n (by simp [Ty.freeVars])
  | bvar i =>
    intro _ v hv
    simp only [Ty.openWith, Ty.instantiate] at hv
    cases h : Vs[i]? with
    | none => rw [h] at hv; simp [Ty.freeVars] at hv
    | some t =>
      rw [h] at hv; simp only [Option.getD_some] at hv
      exact hVs t (List.mem_of_getElem? h) v hv
  | arrow a b iha ihb =>
    intro hX v hv
    have haa : ∀ w ∈ a.freeVars, w < lo ∨ hi ≤ w := fun w hw =>
      hX w (by simp only [Ty.freeVars, List.mem_dedup, List.mem_append]; exact Or.inl hw)
    have hab : ∀ w ∈ b.freeVars, w < lo ∨ hi ≤ w := fun w hw =>
      hX w (by simp only [Ty.freeVars, List.mem_dedup, List.mem_append]; exact Or.inr hw)
    simp only [Ty.openWith, Ty.instantiate, Ty.freeVars, List.mem_dedup, List.mem_append] at hv
    rcases hv with hv | hv
    · exact iha haa v hv
    · exact ihb hab v hv
  | customTy nm tys ih =>
    intro hX v hv
    simp only [Ty.openWith, Ty.instantiate, TyList.instantiate_eq_map, Ty.freeVars] at hv
    obtain ⟨t', ht', hvt'⟩ := TyList.mem_freeVars_iff.mp hv
    obtain ⟨t, ht, rfl⟩ := List.mem_map.mp ht'
    exact ih t ht (fun w hw => hX w (by rw [Ty.freeVars]; exact TyList.mem_freeVars_of_mem ht hw)) v hvt'

mutual
/-- Unifying interval-avoiding monotypes yields an interval-avoiding substitution
    (both domain and range avoid `[lo, hi)`). -/
theorem UnifyRel.gap_avoid {lo hi : Nat} : {a b : Ty} → {S : Subst} → UnifyRel a b S →
    (∀ v ∈ a.freeVars, v < lo ∨ hi ≤ v) → (∀ v ∈ b.freeVars, v < lo ∨ hi ≤ v) →
    (∀ p ∈ S, p.1 < lo ∨ hi ≤ p.1) ∧ (∀ p ∈ S, ∀ v ∈ p.2.freeVars, v < lo ∨ hi ≤ v)
  | _, _, _, .prim, _, _ => ⟨by simp, by simp⟩
  | _, _, _, .fvarRefl, _, _ => ⟨by simp, by simp⟩
  | _, _, _, @UnifyRel.fvarL n τ _ _, ha, hb => by
    refine ⟨?_, ?_⟩
    · intro p hp; rw [List.mem_singleton] at hp; subst hp; exact ha n (by simp [Ty.freeVars])
    · intro p hp v hv; rw [List.mem_singleton] at hp; subst hp; exact hb v hv
  | _, _, _, @UnifyRel.fvarR n τ _ _, ha, hb => by
    refine ⟨?_, ?_⟩
    · intro p hp; rw [List.mem_singleton] at hp; subst hp; exact hb n (by simp [Ty.freeVars])
    · intro p hp v hv; rw [List.mem_singleton] at hp; subst hp; exact ha v hv
  | _, _, _, @UnifyRel.arrow a b c d S₁ S₂ h₁ h₂, ha, hb => by
    have haa : ∀ v ∈ a.freeVars, v < lo ∨ hi ≤ v := fun v hv =>
      ha v (by simp only [Ty.freeVars, List.mem_dedup, List.mem_append]; exact .inl hv)
    have hab : ∀ v ∈ b.freeVars, v < lo ∨ hi ≤ v := fun v hv =>
      ha v (by simp only [Ty.freeVars, List.mem_dedup, List.mem_append]; exact .inr hv)
    have hbc : ∀ v ∈ c.freeVars, v < lo ∨ hi ≤ v := fun v hv =>
      hb v (by simp only [Ty.freeVars, List.mem_dedup, List.mem_append]; exact .inl hv)
    have hbd : ∀ v ∈ d.freeVars, v < lo ∨ hi ≤ v := fun v hv =>
      hb v (by simp only [Ty.freeVars, List.mem_dedup, List.mem_append]; exact .inr hv)
    obtain ⟨hd₁, hr₁⟩ := UnifyRel.gap_avoid h₁ haa hbc
    obtain ⟨hd₂, hr₂⟩ := UnifyRel.gap_avoid h₂ (Subst.onTy_avoidsItv hr₁ hab)
      (Subst.onTy_avoidsItv hr₁ hbd)
    refine ⟨?_, ?_⟩
    · intro p hp; simp only [List.mem_append] at hp; rcases hp with hp | hp
      · exact hd₁ p hp
      · exact hd₂ p hp
    · intro p hp; simp only [List.mem_append] at hp; rcases hp with hp | hp
      · exact hr₁ p hp
      · exact hr₂ p hp
  | _, _, _, @UnifyRel.customTy nm tys₁ tys₂ S hl, ha, hb => by
    exact UnifyRelList.gap_avoid hl
      (fun t ht v hv => ha v (by rw [Ty.freeVars]; exact TyList.mem_freeVars_of_mem ht hv))
      (fun t ht v hv => hb v (by rw [Ty.freeVars]; exact TyList.mem_freeVars_of_mem ht hv))

theorem UnifyRelList.gap_avoid {lo hi : Nat} : {as bs : List Ty} → {S : Subst} →
    UnifyRelList as bs S →
    (∀ t ∈ as, ∀ v ∈ t.freeVars, v < lo ∨ hi ≤ v) →
    (∀ t ∈ bs, ∀ v ∈ t.freeVars, v < lo ∨ hi ≤ v) →
    (∀ p ∈ S, p.1 < lo ∨ hi ≤ p.1) ∧ (∀ p ∈ S, ∀ v ∈ p.2.freeVars, v < lo ∨ hi ≤ v)
  | _, _, _, .nil, _, _ => ⟨by simp, by simp⟩
  | _, _, _, @UnifyRelList.cons t₁ t₂ ts₁ ts₂ S₁ S₂ h₁ ht, ha, hb => by
    obtain ⟨hd₁, hr₁⟩ := UnifyRel.gap_avoid h₁ (ha t₁ List.mem_cons_self)
      (hb t₂ List.mem_cons_self)
    have hmap_a : ∀ t ∈ ts₁.map S₁.onTy, ∀ v ∈ t.freeVars, v < lo ∨ hi ≤ v := by
      intro t htm; obtain ⟨t0, ht0, rfl⟩ := List.mem_map.mp htm
      exact Subst.onTy_avoidsItv hr₁ (ha t0 (List.mem_cons_of_mem _ ht0))
    have hmap_b : ∀ t ∈ ts₂.map S₁.onTy, ∀ v ∈ t.freeVars, v < lo ∨ hi ≤ v := by
      intro t htm; obtain ⟨t0, ht0, rfl⟩ := List.mem_map.mp htm
      exact Subst.onTy_avoidsItv hr₁ (hb t0 (List.mem_cons_of_mem _ ht0))
    obtain ⟨hd₂, hr₂⟩ := UnifyRelList.gap_avoid ht hmap_a hmap_b
    refine ⟨?_, ?_⟩
    · intro p hp; simp only [List.mem_append] at hp; rcases hp with hp | hp
      · exact hd₁ p hp
      · exact hd₂ p hp
    · intro p hp; simp only [List.mem_append] at hp; rcases hp with hp | hp
      · exact hr₁ p hp
      · exact hr₂ p hp
end

def Subst.Factors (U S R : Subst) : Prop :=
  ∀ τ, U.onTy τ = R.onTy (S.onTy τ)

theorem customTy_factor_dodge {Φ : Nat} {scrutTy : Ty} {R S₀ : Subst}
    {K : List Nat} {ctor : Ctor} {tyArgs : List Ty}
    (h₀ : UnifyRel scrutTy
      (.customTy ctor.tyName ((freshVars Φ ctor.paramCount).map (Ty.fvar ·))) S₀)
    (hbscrut : Ty.BelowFvars Φ scrutTy)
    (hR : ∀ p ∈ R, p.2.IsLC)
    (hKΦ : ∀ k ∈ K, k < Φ)
    (hKfix : ∀ k ∈ K, R.onTy (.fvar k) = .fvar k)
    (hpc : ctor.paramCount = tyArgs.length)
    (htyArgs_lc : ∀ t ∈ tyArgs, t.IsLC)
    (hscrutImg : .customTy ctor.tyName tyArgs = R.onTy scrutTy) :
    ∃ R₀ : Subst,
      (∀ p ∈ R₀, p.2.IsLC) ∧
      (∀ k ∈ K, R₀.onTy (.fvar k) = .fvar k) ∧
      (∀ v, v < Φ → R.onTy (.fvar v) = R₀.onTy (S₀.onTy (.fvar v))) ∧
      ((freshVars Φ ctor.paramCount).map (Ty.fvar ·) |>.map S₀.onTy |>.map R₀.onTy)
        = tyArgs := by
  obtain ⟨W, hWge, hWfresh⟩ := exists_fresh_block
    (R.map Prod.fst ++ R.flatMap (fun p => p.2.freeVars) ++
      tyArgs.flatMap Ty.freeVars ++ List.range Φ) Φ ctor.paramCount
  obtain ⟨U, hUdef⟩ : ∃ U : Subst,
    U = (freshVars Φ ctor.paramCount).zip ((freshVars W ctor.paramCount).map (Ty.fvar ·))
        ++ R ++ (freshVars W ctor.paramCount).zip tyArgs := ⟨_, rfl⟩
  have hUonTy : ∀ x, U.onTy x =
      Subst.onTy ((freshVars W ctor.paramCount).zip tyArgs)
        (R.onTy (Subst.onTy ((freshVars Φ ctor.paramCount).zip
          ((freshVars W ctor.paramCount).map (Ty.fvar ·))) x)) := by
    intro x; rw [hUdef, Subst.onTy_append, Subst.onTy_append]
  have hF_i : ∀ (i : Nat) (hi : i < ctor.paramCount),
      (freshVars Φ ctor.paramCount)[i]? = some (Φ + i) := by
    intro i hi
    rw [List.getElem?_eq_getElem (by simpa [freshVars] using hi)]
    simp only [freshVars, List.getElem_map, List.getElem_range]
  have hWi : ∀ (i : Nat) (hi : i < ctor.paramCount),
      (freshVars W ctor.paramCount)[i]? = some (W + i) := by
    intro i hi
    rw [List.getElem?_eq_getElem (by simpa [freshVars] using hi)]
    simp only [freshVars, List.getElem_map, List.getElem_range]
  have htyArgs_belowW : ∀ t ∈ tyArgs, Ty.BelowFvars W t := by
    intro t ht; apply Ty.BelowFvars.of_freeVars_lt
    intro v hv
    exact hWfresh v (by
      simp only [List.mem_append]
      exact Or.inl (Or.inr (List.mem_flatMap.mpr ⟨t, ht, hv⟩)))
  have hA_id : ∀ {x : Ty}, Ty.BelowFvars Φ x →
      Subst.onTy ((freshVars Φ ctor.paramCount).zip
        ((freshVars W ctor.paramCount).map (Ty.fvar ·))) x = x := by
    intro x hx
    apply Ty.substFvars_eq_self_of_no_key
    intro p hp hc
    have hp1 : p.1 ∈ freshVars Φ ctor.paramCount := (List.of_mem_zip hp).1
    have hge := freshVars_ge p.1 hp1
    have hlt := hx.mem_lt p.1 hc
    omega
  have hB_fix : ∀ {t : Ty}, (∀ p ∈ R, ∀ v ∈ p.2.freeVars, v ∉ (freshVars W ctor.paramCount)) →
      (∀ v ∈ t.freeVars, v ∉ freshVars W ctor.paramCount) →
      Subst.onTy ((freshVars W ctor.paramCount).zip tyArgs) t = t := by
    intro t hR hB
    apply Ty.substFvars_eq_self_of_no_key
    intro p hp hc
    have hp1 : p.1 ∈ freshVars W ctor.paramCount := (List.of_mem_zip hp).1
    exact hB p.1 hc hp1
  have hU_fvar : ∀ v, v < Φ → U.onTy (Ty.fvar v) = R.onTy (Ty.fvar v) := by
    intro v hv
    rw [hUonTy]
    rw [hA_id (Ty.BelowFvars.fvar hv)]
    apply hB_fix
    · intro p hp w hw' hwW
      have hwge : W ≤ w := freshVars_ge w hwW
      have := hWfresh w (by
        simp only [List.mem_append]
        exact Or.inl (Or.inl (Or.inr (List.mem_flatMap.mpr ⟨p, hp, hw'⟩))))
      omega
    · intro w hw' hwW
      have hc' : w ∈ (R.onTy (Ty.fvar v)).freeVars := hw'
      rcases Subst.mem_freeVars_onTy hc' with h'' | ⟨q, hq, h''⟩
      · simp only [Ty.freeVars, List.mem_singleton] at h''
        have hvW : w < Φ := h'' ▸ hv
        have hwge : W ≤ w := freshVars_ge w hwW
        have := hWfresh w (by
          simp only [List.mem_append]
          exact Or.inr (List.mem_range.mpr hvW))
        omega
      · have hwge : W ≤ w := freshVars_ge w hwW
        have := hWfresh w (by
          simp only [List.mem_append]
          exact Or.inl (Or.inl (Or.inr (List.mem_flatMap.mpr ⟨q, hq, h''⟩))))
        omega
  have hU_index : ∀ (i : Nat) (hi : i < ctor.paramCount),
      U.onTy (Ty.fvar (Φ + i)) = tyArgs[i]'(by simpa [hpc] using hi) := by
    intro i hi
    have hi' : i < tyArgs.length := by simpa [hpc] using hi
    rw [hUonTy]
    have hfx : (freshVars Φ ctor.paramCount)[i]? = some (Φ + i) := hF_i i hi
    have hWx : (freshVars W ctor.paramCount)[i]? = some (W + i) := hWi i hi
    have hL1 : Subst.onTy ((freshVars Φ ctor.paramCount).zip
        ((freshVars W ctor.paramCount).map (Ty.fvar ·))) (Ty.fvar (Φ + i))
        = Ty.fvar (W + i) := by
      apply Ty.substFvars_zip_fvar_eq' freshVars_nodup hfx
      · rw [List.getElem?_map, hWi i hi]; rfl
      · intro X hX hc
        simp only [Ty.freeVars, List.mem_singleton] at hc
        have hlt := freshVars_lt X hX
        omega
    rw [hL1]
    have hL2 : R.onTy (Ty.fvar (W + i)) = Ty.fvar (W + i) := by
      apply Ty.substFvars_eq_self_of_no_key
      intro p hp hc
      simp only [Ty.freeVars, List.mem_singleton] at hc
      have hkey : p.1 ∈ R.map Prod.fst := List.mem_map.mpr ⟨p, hp, rfl⟩
      rw [hc] at hkey
      have := hWfresh (W + i) (by
        simp only [List.mem_append]
        exact Or.inl (Or.inl (Or.inl hkey)))
      have hge : W ≤ W + i := by omega
      omega
    rw [hL2]
    have htyx : tyArgs[i]? = some (tyArgs[i]) := by
      rw [List.getElem?_eq_getElem hi']
    apply Ty.substFvars_zip_fvar_eq' freshVars_nodup hWx htyx
    intro w hw hc
    have hwge := freshVars_ge w hw
    have hvmem : tyArgs[i] ∈ tyArgs := List.mem_of_getElem? (List.getElem?_eq_getElem hi')
    have := (htyArgs_belowW (tyArgs[i]) hvmem).mem_lt w hc
    omega
  have hmap_U : ((freshVars Φ ctor.paramCount).map (Ty.fvar ·)).map U.onTy = tyArgs := by
    apply List.ext_getElem
    · simp [hpc]
    · intro i hi _
      have hi' : i < (freshVars Φ ctor.paramCount).length := by
        simpa [freshVars_length] using hi
      have hx := hF_i i (by simpa [freshVars_length] using hi')
      have hxi : (freshVars Φ ctor.paramCount)[i] = Φ + i := by
        rw [List.getElem?_eq_getElem hi'] at hx
        exact Option.some.inj hx
      rw [List.getElem_map, List.getElem_map, hxi]
      exact hU_index i (by simpa [hpc] using hi')
  have hUni : Unifies U scrutTy
      (.customTy ctor.tyName ((freshVars Φ ctor.paramCount).map (Ty.fvar ·))) := by
    have hRHS : U.onTy (.customTy ctor.tyName
        ((freshVars Φ ctor.paramCount).map (Ty.fvar ·))) = .customTy ctor.tyName tyArgs := by
      rw [Subst.onTy_customTy, hmap_U]
    show U.onTy scrutTy = U.onTy (.customTy ctor.tyName
      ((freshVars Φ ctor.paramCount).map (Ty.fvar ·)))
    rw [hRHS]
    rw [hUonTy]
    rw [hA_id hbscrut]
    have hB : Subst.onTy ((freshVars W ctor.paramCount).zip tyArgs)
        (R.onTy scrutTy) = R.onTy scrutTy := hB_fix
      (by
        intro p hp w hw' hwW
        have hwge : W ≤ w := freshVars_ge w hwW
        have := hWfresh w (by
          simp only [List.mem_append]
          exact Or.inl (Or.inl (Or.inr (List.mem_flatMap.mpr ⟨p, hp, hw'⟩))))
        omega)
      (by
        intro w hw' hwW
        have hwge : W ≤ w := freshVars_ge w hwW
        rcases Subst.mem_freeVars_onTy hw' with h' | ⟨q, hq, h'⟩
        · have hlt := hbscrut.mem_lt w h'
          have := hWfresh w (by
            simp only [List.mem_append]
            exact Or.inr (List.mem_range.mpr hlt))
          omega
        · have := hWfresh w (by
            simp only [List.mem_append]
            exact Or.inl (Or.inl (Or.inr (List.mem_flatMap.mpr ⟨q, hq, h'⟩))))
          omega)
    rw [hB]
    exact hscrutImg.symm
  have hUlc : ∀ p ∈ U, p.2.IsLC := by
    rw [hUdef]
    intro p hp
    rcases List.mem_append.mp hp with hp' | hp'
    · rcases List.mem_append.mp hp' with hp'' | hp''
      · have hmem := (List.of_mem_zip hp'').2
        obtain ⟨x, _, hxeq⟩ := List.mem_map.mp hmem
        rw [← hxeq]; exact ContainsBvarsUpTo.fvar
      · exact hR p hp''
    · have hmem := (List.of_mem_zip hp').2
      exact htyArgs_lc p.2 hmem
  have hUK : ∀ k ∈ K, U.onTy (Ty.fvar k) = Ty.fvar k := fun k hk =>
    (hU_fvar k (hKΦ k hk)).trans (hKfix k hk)
  obtain ⟨R₀, hR₀fac, hR₀lc, hR₀K⟩ :=
    UnifyRel.greatest_K h₀ U hUlc hUni hUK
  refine ⟨R₀, hR₀lc, hR₀K, ?_, ?_⟩
  · intro v hv
    have h := hR₀fac (Ty.fvar v)
    rwa [hU_fvar v hv] at h
  · rw [List.map_map, List.map_map]
    apply List.ext_getElem?
    intro i
    by_cases hi : i < ctor.paramCount
    · have hx : (freshVars Φ ctor.paramCount)[i]? = some (Φ + i) := hF_i i hi
      rw [List.getElem?_map, hx]
      simp only [Option.map_some, Function.comp_apply]
      rw [List.getElem?_eq_getElem (by simpa [hpc] using hi)]
      have h := hR₀fac (Ty.fvar (Φ + i))
      rw [hU_index i hi] at h
      exact congrArg some h.symm
    · have hlen₁ : i ≥ (freshVars Φ ctor.paramCount).length := by
        rw [freshVars_length]; exact Nat.le_of_not_gt hi
      have hlen₂ : i ≥ tyArgs.length := by
        rw [← hpc]; exact Nat.le_of_not_gt hi
      rw [List.getElem?_eq_none (by simpa [List.length_map, freshVars_length] using hlen₁)]
      rw [List.getElem?_eq_none (by simpa [List.length_map] using hlen₂)]

mutual
/-- A unifier of an equation absorbs its `UnifyRel` solution. -/
theorem UnifyRel.factors_self : {a b : Ty} → {S : Subst} → UnifyRel a b S →
    ∀ U : Subst, Unifies U a b → Subst.Factors U S U
  | _, _, _, .prim, U, _ => fun t => by simp only [Subst.onTy_nil]
  | _, _, _, .fvarRefl, U, _ => fun t => by simp only [Subst.onTy_nil]
  | _, _, _, @UnifyRel.fvarL n t _ _, U, hU => by
      intro x
      simp only [Unifies, Subst.onTy] at hU ⊢
      simpa [Subst.onTy] using (Subst.onTy_substFvar hU x).symm
  | _, _, _, @UnifyRel.fvarR n t _ _, U, hU => by
      intro x
      simp only [Unifies, Subst.onTy] at hU ⊢
      simpa [Subst.onTy] using (Subst.onTy_substFvar hU.symm x).symm
  | _, _, _, @UnifyRel.arrow a b c d S₁ S₂ h₁ h₂, U, hU => by
      have hac : Unifies U a c := by
        simp only [Unifies, Subst.onTy_arrow] at hU
        exact (Ty.arrow.inj hU).1
      have hbd : Unifies U b d := by
        simp only [Unifies, Subst.onTy_arrow] at hU
        exact (Ty.arrow.inj hU).2
      have h₁U := UnifyRel.factors_self h₁ U hac
      have h₂U : Unifies U (S₁.onTy b) (S₁.onTy d) := by
        simp only [Unifies] at hbd ⊢
        exact (h₁U b).symm.trans (hbd.trans (h₁U d))
      have h₂Ufac := UnifyRel.factors_self h₂ U h₂U
      intro x
      simp only [Subst.Factors, Subst.onTy_append] at h₁U h₂Ufac ⊢
      exact (h₁U x).trans (h₂Ufac (S₁.onTy x))
  | _, _, _, @UnifyRel.customTy nm as bs S hs, U, hU => by
      have hlist : as.map U.onTy = bs.map U.onTy := by
        simp only [Unifies, Subst.onTy_customTy] at hU
        exact (Ty.customTy.inj hU).2
      exact UnifyRelList.factors_self hs U hlist

/-- List counterpart of `UnifyRel.factors_self`. -/
theorem UnifyRelList.factors_self : {as bs : List Ty} → {S : Subst} →
    UnifyRelList as bs S → ∀ U : Subst,
      as.map U.onTy = bs.map U.onTy → Subst.Factors U S U
  | _, _, _, .nil, U, _ => fun t => by simp only [Subst.onTy_nil]
  | _, _, _, @UnifyRelList.cons a b as bs S₁ S₂ h₁ h₂, U, hU => by
      simp only [List.map_cons, List.cons.injEq] at hU
      obtain ⟨hab, htail⟩ := hU
      have h₁U := UnifyRel.factors_self h₁ U hab
      have h₂U := UnifyRelList.factors_self h₂ U (by
        rw [List.map_map, List.map_map]
        calc
          as.map (fun t => U.onTy (S₁.onTy t)) = as.map U.onTy := by
                apply List.map_congr_left
                intro t _
                exact (h₁U t).symm
          _ = bs.map U.onTy := htail
          _ = bs.map (fun t => U.onTy (S₁.onTy t)) := by
                apply List.map_congr_left
                intro t _
                exact h₁U t)
      intro x
      simp only [Subst.Factors, Subst.onTy_append] at h₁U h₂U ⊢
      exact (h₁U x).trans (h₂U (S₁.onTy x))
end

/-- Pointwise satisfaction of a substitution's raw bindings makes the
    substitution self-absorbing. -/
theorem Subst.Factors.of_satisfies {U S : Subst}
    (h : ∀ p ∈ S, U.onTy (.fvar p.1) = U.onTy p.2) :
    Subst.Factors U S U := by
  induction S with
  | nil => intro t; simp only [Subst.onTy_nil]
  | cons hd tl ih =>
      obtain ⟨z, u⟩ := hd
      have hhead : U.onTy (.fvar z) = U.onTy u :=
        h (z, u) List.mem_cons_self
      have htail : Subst.Factors U tl U := ih (fun p hp =>
        h p (List.mem_cons_of_mem _ hp))
      intro t
      have hsubst := Subst.onTy_substFvar hhead t
      simp only [Subst.Factors, Subst.onTy] at htail ⊢
      exact hsubst.symm.trans (htail (Ty.substFvar z u t))

/-- A self-absorbing residual preserves generalization across a substitution
    whose domains and ranges avoid the generalization pool. -/
theorem Subst.Factors.genGroup_stable {U Sc : Subst} {G : List Nat} {τ : Ty}
    (hfac : Subst.Factors U Sc U)
    (hdom : ∀ p ∈ Sc, p.1 ∉ G)
    (hran : ∀ p ∈ Sc, ∀ u ∈ p.2.freeVars, u ∉ G) :
     (U.onPolyTy (PolyTy.genGroup G (Sc.onTy τ))) =
       (U.onPolyTy (PolyTy.genGroup G τ)) := by
  rw [← Subst.onPolyTy_genGroup hdom hran]
  apply congrArg₂ PolyTy.mk rfl
  exact (hfac (PolyTy.genGroup G τ).body).symm

/-! A `UnifyRel` trace supplies pointwise satisfaction of each raw binding,
in addition to equality after applying the whole substitution. -/
mutual
theorem UnifyRel.binding_satisfies : {a b : Ty} → {S : Subst} → UnifyRel a b S →
    ∀ U : Subst, Unifies U a b →
      ∀ p ∈ S, U.onTy (.fvar p.1) = U.onTy p.2
  | _, _, _, .prim, U, hU, p, hp => by simp at hp
  | _, _, _, .fvarRefl, U, hU, p, hp => by simp at hp
  | _, _, _, @UnifyRel.fvarL n t _ _, U, hU, p, hp => by
      rw [List.mem_singleton] at hp
      subst p
      exact hU
  | _, _, _, @UnifyRel.fvarR n t _ _, U, hU, p, hp => by
      rw [List.mem_singleton] at hp
      subst p
      exact hU.symm
  | _, _, _, @UnifyRel.arrow a b c d S₁ S₂ h₁ h₂, U, hU, p, hp => by
      have hac : Unifies U a c := by
        simp only [Unifies, Subst.onTy_arrow] at hU
        exact (Ty.arrow.inj hU).1
      have hbd : Unifies U b d := by
        simp only [Unifies, Subst.onTy_arrow] at hU
        exact (Ty.arrow.inj hU).2
      have h₁fac := UnifyRel.factors_self h₁ U hac
      have h₂uni : Unifies U (S₁.onTy b) (S₁.onTy d) := by
        simp only [Unifies] at hbd ⊢
        exact (h₁fac b).symm.trans (hbd.trans (h₁fac d))
      rw [List.mem_append] at hp
      exact hp.elim
        (fun hp => UnifyRel.binding_satisfies h₁ U hac p hp)
        (fun hp => UnifyRel.binding_satisfies h₂ U h₂uni p hp)
  | _, _, _, @UnifyRel.customTy nm as bs S hs, U, hU, p, hp => by
      have hlist : as.map U.onTy = bs.map U.onTy := by
        simp only [Unifies, Subst.onTy_customTy] at hU
        exact (Ty.customTy.inj hU).2
      exact UnifyRelList.binding_satisfies hs U hlist p hp

theorem UnifyRelList.binding_satisfies : {as bs : List Ty} → {S : Subst} →
    UnifyRelList as bs S → ∀ U : Subst,
      as.map U.onTy = bs.map U.onTy →
      ∀ p ∈ S, U.onTy (.fvar p.1) = U.onTy p.2
  | _, _, _, .nil, U, hU, p, hp => by simp at hp
  | _, _, _, @UnifyRelList.cons a b as bs S₁ S₂ h₁ h₂, U, hU, p, hp => by
      simp only [List.map_cons, List.cons.injEq] at hU
      obtain ⟨hab, htail⟩ := hU
      have h₁fac := UnifyRel.factors_self h₁ U hab
      have htail' :
          (as.map S₁.onTy).map U.onTy = (bs.map S₁.onTy).map U.onTy := by
        rw [List.map_map, List.map_map]
        calc
          as.map (fun t => U.onTy (S₁.onTy t)) = as.map U.onTy := by
                apply List.map_congr_left
                intro t _
                exact (h₁fac t).symm
          _ = bs.map U.onTy := htail
          _ = bs.map (fun t => U.onTy (S₁.onTy t)) := by
                apply List.map_congr_left
                intro t _
                exact h₁fac t
      rw [List.mem_append] at hp
      exact hp.elim
        (fun hp => UnifyRel.binding_satisfies h₁ U hab p hp)
        (fun hp => UnifyRelList.binding_satisfies h₂ U htail' p hp)
end

private theorem RecGroups.ValidResidualGroups.stage_unique
    {anns : List (Option PolyTy)} {bindings : List Expr}
    {groups : List (List Nat)}
    (h : RecGroups.ValidResidualGroups anns bindings groups)
    {leftStage rightStage member : Nat} {left right : List Nat}
    (hleft : groups[leftStage]? = some left)
    (hright : groups[rightStage]? = some right)
    (hmemLeft : member ∈ left) (hmemRight : member ∈ right) :
    leftStage = rightStage := by
  have hleftBound := (List.getElem?_eq_some_iff.mp hleft).1
  have hrightBound := (List.getElem?_eq_some_iff.mp hright).1
  rcases lt_trichotomy leftStage rightStage with hlt | heq | hgt
  · have hdisjoint := (List.pairwise_iff_getElem.mp
      (List.nodup_flatten.mp h.flatten_nodup).2)
      leftStage rightStage hleftBound hrightBound hlt
    rw [(List.getElem?_eq_some_iff.mp hleft).2,
      (List.getElem?_eq_some_iff.mp hright).2] at hdisjoint
    exact (List.disjoint_left.mp hdisjoint hmemLeft hmemRight).elim
  · exact heq
  · have hdisjoint := (List.pairwise_iff_getElem.mp
      (List.nodup_flatten.mp h.flatten_nodup).2)
      rightStage leftStage hrightBound hleftBound hgt
    rw [(List.getElem?_eq_some_iff.mp hright).2,
      (List.getElem?_eq_some_iff.mp hleft).2] at hdisjoint
    exact (List.disjoint_left.mp hdisjoint hmemRight hmemLeft).elim

private theorem RecGroups.ValidResidualGroups.not_mem_take_of_mem
    {anns : List (Option PolyTy)} {bindings : List Expr}
    {groups : List (List Nat)}
    (h : RecGroups.ValidResidualGroups anns bindings groups)
    {stage member : Nat} {component : List Nat}
    (hcomponent : groups[stage]? = some component) (hmember : member ∈ component) :
    member ∉ (groups.take stage).flatten := by
  intro hprefix
  obtain ⟨prior, hpriorIn, hmemberPrior⟩ := List.mem_flatten.mp hprefix
  obtain ⟨priorStage, hpriorStage⟩ := List.mem_iff_getElem?.mp hpriorIn
  have hpriorLt : priorStage < stage := by
    have := (List.getElem?_eq_some_iff.mp hpriorStage).1
    simp only [List.length_take] at this
    have hstageBound := (List.getElem?_eq_some_iff.mp hcomponent).1
    omega
  have hpriorOriginal : groups[priorStage]? = some prior := by
    rw [List.getElem?_take, if_pos hpriorLt] at hpriorStage
    exact hpriorStage
  have heq := h.stage_unique hpriorOriginal hcomponent hmemberPrior hmember
  omega

private theorem RecGroups.ValidResidualGroups.stage_of_unsigned
    {anns : List (Option PolyTy)} {bindings : List Expr}
    {groups : List (List Nat)}
    (h : RecGroups.ValidResidualGroups anns bindings groups)
    {member : Nat} (hbound : member < bindings.length)
    (hunsigned : RecGroups.UnsignedAt anns member) :
    ∃ (stage : Nat) (component : List Nat),
      groups[stage]? = some component ∧ member ∈ component := by
  have hflat : member ∈ groups.flatten :=
    (h.covers_unsigned member hbound).2 hunsigned
  obtain ⟨component, hcomponent, hmember⟩ := List.mem_flatten.mp hflat
  obtain ⟨stage, hstage, heq⟩ := List.mem_iff_getElem.mp hcomponent
  exact ⟨stage, component, by rw [List.getElem?_eq_getElem hstage, heq], hmember⟩

private theorem RecGroups.ValidResidualGroups.edge_stage_le
    {anns : List (Option PolyTy)} {bindings : List Expr}
    {groups : List (List Nat)}
    (h : RecGroups.ValidResidualGroups anns bindings groups)
    {sourceStage targetStage source target : Nat}
    {sourceComponent targetComponent : List Nat}
    (hsourceComponent : groups[sourceStage]? = some sourceComponent)
    (htargetComponent : groups[targetStage]? = some targetComponent)
    (hsource : source ∈ sourceComponent) (htarget : target ∈ targetComponent)
    (hsourceBound : source < bindings.length)
    (htargetBound : target < bindings.length)
    (hedge : (⟨target, htargetBound⟩ : Fin bindings.length) ∈
      (RecGroup.inferenceDigraph anns bindings).succ ⟨source, hsourceBound⟩) :
    targetStage ≤ sourceStage := by
  have hsourceUnsigned : RecGroups.UnsignedAt anns source :=
    (h.covers_unsigned source hsourceBound).1
      (List.mem_flatten.mpr ⟨sourceComponent,
        List.mem_of_getElem? hsourceComponent, hsource⟩)
  have hsourceBool := (RecGroup.isUnsignedAt_eq_true_iff anns source).2
    hsourceUnsigned
  have hedge' := (RecGroup.mem_inferenceDigraph_succ_iff
    (⟨source, hsourceBound⟩ : Fin bindings.length)
    ⟨target, htargetBound⟩).1 hedge
  have hrhs : bindings[source]? = some bindings[source] :=
    List.getElem?_eq_getElem hsourceBound
  simp only [RecGroup.inferenceSucc, hsourceBool, if_true, hrhs,
    List.mem_filter] at hedge'
  exact h.dependencies_first hsourceComponent htargetComponent
    hsource htarget hrhs hedge'.1

private theorem RecGroups.ValidResidualGroups.reach_stage_le
    {anns : List (Option PolyTy)} {bindings : List Expr}
    {groups : List (List Nat)}
    (h : RecGroups.ValidResidualGroups anns bindings groups)
    {source target : Fin bindings.length}
    (hreach : Scc.Reach (RecGroup.inferenceDigraph anns bindings) source target)
    {sourceStage targetStage : Nat} {sourceComponent targetComponent : List Nat}
    (hsourceComponent : groups[sourceStage]? = some sourceComponent)
    (htargetComponent : groups[targetStage]? = some targetComponent)
    (hsource : source.val ∈ sourceComponent)
    (htarget : target.val ∈ targetComponent) :
    targetStage ≤ sourceStage := by
  induction hreach generalizing sourceStage sourceComponent with
  | refl =>
      exact Nat.le_of_eq (h.stage_unique hsourceComponent htargetComponent hsource htarget).symm
  | @tail source middle target hedge htail ih =>
      have hedge' := (RecGroup.mem_inferenceDigraph_succ_iff source middle).1 hedge
      have hsourceUnsigned : RecGroups.UnsignedAt anns source.val :=
        (h.covers_unsigned source.val source.isLt).1
          (List.mem_flatten.mpr ⟨sourceComponent,
            List.mem_of_getElem? hsourceComponent, hsource⟩)
      have hsourceBool := (RecGroup.isUnsignedAt_eq_true_iff anns source.val).2
        hsourceUnsigned
      have hrhs : bindings[source.val]? = some bindings[source.val] :=
        List.getElem?_eq_getElem source.isLt
      simp only [RecGroup.inferenceSucc, hsourceBool, if_true, hrhs,
        List.mem_filter] at hedge'
      have hmiddleUnsigned : RecGroups.UnsignedAt anns middle.val :=
        (RecGroup.isUnsignedAt_eq_true_iff anns middle.val).1 hedge'.2
      obtain ⟨middleStage, middleComponent, hmiddleComponent, hmiddle⟩ :=
        h.stage_of_unsigned middle.isLt hmiddleUnsigned
      have hstep : middleStage ≤ sourceStage :=
        h.edge_stage_le hsourceComponent hmiddleComponent hsource hmiddle
          source.isLt middle.isLt hedge
      exact Nat.le_trans (ih hmiddleComponent hmiddle htarget) hstep

private theorem RecGroups.ValidResidualGroups.same_inference_component_stage
    {anns : List (Option PolyTy)} {bindings : List Expr}
    {groups : List (List Nat)}
    (h : RecGroups.ValidResidualGroups anns bindings groups)
    {algorithmStage : Nat} {algorithmComponent : List Nat}
    (halgorithm : (RecGroup.inferenceSccs anns bindings)[algorithmStage]? =
      some algorithmComponent)
    {left right leftStage rightStage : Nat}
    {leftComponent rightComponent : List Nat}
    (hleft : left ∈ algorithmComponent) (hright : right ∈ algorithmComponent)
    (hleftComponent : groups[leftStage]? = some leftComponent)
    (hrightComponent : groups[rightStage]? = some rightComponent)
    (hleftDecl : left ∈ leftComponent) (hrightDecl : right ∈ rightComponent) :
    leftStage = rightStage := by
  have hleftBound : left < bindings.length := by
    apply (RecGroup.inferenceSccs_valid h.length).bounded left
    exact List.mem_flatten.mpr ⟨algorithmComponent,
      List.mem_of_getElem? halgorithm, hleft⟩
  have hrightBound : right < bindings.length := by
    apply (RecGroup.inferenceSccs_valid h.length).bounded right
    exact List.mem_flatten.mpr ⟨algorithmComponent,
      List.mem_of_getElem? halgorithm, hright⟩
  have hmutual := RecGroup.inferenceSccs_sameScc anns bindings halgorithm
    hleft hright hleftBound hrightBound
  have hrl := h.reach_stage_le hmutual.1 hleftComponent hrightComponent
    hleftDecl hrightDecl
  have hlr := h.reach_stage_le hmutual.2 hrightComponent hleftComponent
    hrightDecl hleftDecl
  omega

private theorem RecGroups.ValidResidualGroups.inference_component_contained
    {anns : List (Option PolyTy)} {bindings : List Expr}
    {groups : List (List Nat)}
    (h : RecGroups.ValidResidualGroups anns bindings groups)
    {algorithmStage : Nat} {algorithmComponent : List Nat}
    (halgorithm : (RecGroup.inferenceSccs anns bindings)[algorithmStage]? =
      some algorithmComponent) :
    ∃ (declStage : Nat) (declComponent : List Nat),
      groups[declStage]? = some declComponent ∧
      ∀ member ∈ algorithmComponent, member ∈ declComponent := by
  have halgValid := RecGroup.inferenceSccs_valid h.length
  have hnonempty := halgValid.nonempty algorithmComponent
    (List.mem_of_getElem? halgorithm)
  obtain ⟨anchor, rest, heq⟩ := List.exists_cons_of_ne_nil hnonempty
  subst algorithmComponent
  have hanchor : anchor ∈ anchor :: rest := List.mem_cons_self
  have hanchorBound := halgValid.bounded anchor
    (List.mem_flatten.mpr ⟨anchor :: rest,
      List.mem_of_getElem? halgorithm, hanchor⟩)
  have hanchorUnsigned := (halgValid.covers_unsigned anchor hanchorBound).1
    (List.mem_flatten.mpr ⟨anchor :: rest,
      List.mem_of_getElem? halgorithm, hanchor⟩)
  obtain ⟨declStage, declComponent, hdeclComponent, hanchorDecl⟩ :=
    h.stage_of_unsigned hanchorBound hanchorUnsigned
  refine ⟨declStage, declComponent, hdeclComponent, ?_⟩
  intro member hmember
  have hmemberBound := halgValid.bounded member
    (List.mem_flatten.mpr ⟨anchor :: rest,
      List.mem_of_getElem? halgorithm, hmember⟩)
  have hmemberUnsigned := (halgValid.covers_unsigned member hmemberBound).1
    (List.mem_flatten.mpr ⟨anchor :: rest,
      List.mem_of_getElem? halgorithm, hmember⟩)
  obtain ⟨memberStage, memberComponent, hmemberComponent, hmemberDecl⟩ :=
    h.stage_of_unsigned hmemberBound hmemberUnsigned
  have hstageEq := h.same_inference_component_stage halgorithm hanchor hmember
    hdeclComponent hmemberComponent hanchorDecl hmemberDecl
  subst memberStage
  have hcomponentEq : memberComponent = declComponent :=
    Option.some.inj (hmemberComponent.symm.trans hdeclComponent)
  simpa [hcomponentEq] using hmemberDecl


/-- Every canonical inference component is contained in one component of any
valid declarative residual partition. -/
theorem RecGroups.ValidResidualGroups.canonical_component_contained
    {anns : List (Option PolyTy)} {bindings : List Expr}
    {groups : List (List Nat)}
    (h : RecGroups.ValidResidualGroups anns bindings groups)
    {algorithmStage : Nat} {algorithmComponent : List Nat}
    (halgorithm : (RecGroup.inferenceSccs anns bindings)[algorithmStage]? =
      some algorithmComponent) :
    ∃ (declStage : Nat) (declComponent : List Nat),
      groups[declStage]? = some declComponent ∧
      ∀ member ∈ algorithmComponent, member ∈ declComponent :=
  h.inference_component_contained halgorithm

theorem exists_instantiation_residual {Φ k : Nat} {S₀ : Subst} {K : List Nat}
    {ty : Ty} {instArgs : List Ty} {τ₀ : Ty}
    (hS₀ : ∀ p ∈ S₀, p.2.IsLC)
    (hKΦ : ∀ k ∈ K, k < Φ)
    (hKfix : ∀ k ∈ K, S₀.onTy (Ty.fvar k) = Ty.fvar k)
    (hinst : InstantiatesBy instArgs ( (S₀.onTy ty)) τ₀)
    (hbv : ContainsBvarsUpTo k ty)
    (htyfree : ∀ v ∈ ty.freeVars, v < Φ)
    (hinstLC : ∀ t ∈ instArgs, t.IsLC) :
    ∃ R : Subst, (∀ p ∈ R, p.2.IsLC) ∧
      (∀ k ∈ K, R.onTy (Ty.fvar k) = Ty.fvar k) ∧
      (∀ v, v < Φ → R.onTy (Ty.fvar v) = S₀.onTy (Ty.fvar v)) ∧
      Eq τ₀ (R.onTy (Ty.openVars (freshVars Φ k) ty)) := by
  obtain ⟨W, hWge, hWfresh⟩ := exists_fresh_block
    (S₀.map Prod.fst ++ S₀.flatMap (fun p => p.2.freeVars) ++ τ₀.freeVars) Φ k
  set proxy : Subst := blockList Φ W k with hproxy_def
  set breal : Subst := (freshVars W k).zip instArgs with hbreal_def
  set R : Subst := proxy ++ S₀ ++ breal with hR_def
  have hWΦ : Φ ≤ W := by omega
  have hW_S₀key : ∀ p ∈ S₀, p.1 < W := by
    intro p hp
    exact hWfresh p.1 (List.mem_append_left _ (List.mem_append_left _
      (List.mem_map.mpr ⟨p, hp, rfl⟩)))
  have hW_S₀ran : ∀ p ∈ S₀, ∀ u ∈ p.2.freeVars, u < W := by
    intro p hp u hu
    exact hWfresh u (List.mem_append_left _ (List.mem_append_right _
      (List.mem_flatMap.mpr ⟨p, hp, hu⟩)))
  have hW_τ₀ : ∀ u ∈ τ₀.freeVars, u < W := by
    intro u hu
    exact hWfresh u (List.mem_append_right _ hu)
  have hproxyfix : ∀ m, m < Φ → proxy.onTy (Ty.fvar m) = Ty.fvar m := by
    intro m hm
    rw [hproxy_def]
    apply Ty.substFvars_eq_self_of_no_key
    intro p hp hc
    simp only [blockList, List.mem_map] at hp
    obtain ⟨i, _, rfl⟩ := hp
    simp only [Ty.freeVars, List.mem_singleton] at hc
    omega
  have hτW : ∀ v ∈ (Ty.openVars (freshVars Φ k) ty).freeVars,
      ¬ (W ≤ v ∧ v < W + k) := by
    intro v hv
    rcases Ty.freeVars_openVars_subset v hv with h | h
    · have hvW : v < W := lt_of_lt_of_le (htyfree v h) hWΦ
      omega
    · have hge : Φ ≤ v := freshVars_ge v h
      have hlt : v < Φ + k := freshVars_lt v h
      omega
  have hproxy : proxy.onTy (Ty.openVars (freshVars Φ k) ty) =
      Ty.openVars (freshVars W k) ty := by
    rw [hproxy_def]
    rw [blockList_onTy (Φ := Φ) (W := W) (k := k) hWge hτW]
    exact Ty.rename_openVars_blockSwap hWge ty htyfree
  have hS₀comm : S₀.onTy (Ty.openVars (freshVars W k) ty) =
      Ty.openVars (freshVars W k) (S₀.onTy ty) :=
    Subst.onTy_openVars hS₀ (fun p hp hc => by
      have hlt : p.1 < W := hW_S₀key p hp
      simp only [freshVars, List.mem_map, List.mem_range] at hc
      obtain ⟨i, _, hpq⟩ := hc
      omega)
  have hbv' : ContainsBvarsUpTo k ( (S₀.onTy ty)) :=
    ContainsBvarsUpTo.substFvars hS₀ hbv
  have hzip := InstantiatesBy.onTy_openVars_zip (Xs := freshVars W k)
    (ty :=  (S₀.onTy ty)) (τ := τ₀) (tyArgs := instArgs) hinst
    (by simpa [freshVars_length] using hbv') freshVars_nodup
    (fun x hx hu => by
      have hge : W ≤ x := freshVars_ge x hx
      have hlt : x < W := hW_τ₀ x hu
      omega)
  have hzip' : breal.onTy
      ( (Ty.openVars (freshVars W k) (S₀.onTy ty))) = τ₀ := by
    simpa [hbreal_def] using hzip
  refine ⟨R, ?_, ?_, ?_, ?_⟩
  · intro p hp
    rw [hR_def] at hp
    rcases List.mem_append.mp hp with hp' | hp'
    · rcases List.mem_append.mp hp' with hp'' | hp''
      · rw [hproxy_def] at hp''
        exact blockList_lc Φ W k p hp''
      · exact hS₀ p hp''
    · rw [hbreal_def] at hp'
      exact hinstLC p.2 (List.of_mem_zip hp').2
  · intro k hk
    have hklt := hKΦ k hk
    calc R.onTy (Ty.fvar k)
        = breal.onTy (S₀.onTy (proxy.onTy (Ty.fvar k))) := by
            rw [hR_def, Subst.onTy_append, Subst.onTy_append]
      _ = breal.onTy (S₀.onTy (Ty.fvar k)) := by rw [hproxyfix k hklt]
      _ = breal.onTy (Ty.fvar k) := by rw [hKfix k hk]
      _ = Ty.fvar k := by
        rw [hbreal_def]
        apply Ty.substFvars_eq_self_of_no_key
        intro p hp hc
        have hge : W ≤ p.1 := freshVars_ge p.1 (List.of_mem_zip hp).1
        simp only [Ty.freeVars, List.mem_singleton] at hc
        omega
  · intro v hv
    calc R.onTy (Ty.fvar v)
        = breal.onTy (S₀.onTy (proxy.onTy (Ty.fvar v))) := by
            rw [hR_def, Subst.onTy_append, Subst.onTy_append]
      _ = breal.onTy (S₀.onTy (Ty.fvar v)) := by rw [hproxyfix v hv]
      _ = S₀.onTy (Ty.fvar v) := by
        rw [hbreal_def]
        apply Ty.substFvars_eq_self_of_no_key
        intro p hp hc
        have hge : W ≤ p.1 := freshVars_ge p.1 (List.of_mem_zip hp).1
        have hp_notmem : p.1 ∉ (S₀.onTy (Ty.fvar v)).freeVars :=
          Subst.not_mem_onTy_freeVars
            (fun q hq hcq => by have := hW_S₀ran q hq p.1 hcq; omega)
            (by simp only [Ty.freeVars, List.mem_singleton]; omega)
        exact hp_notmem hc
  · show  τ₀ =
       (R.onTy (Ty.openVars (freshVars Φ k) ty))
    rw [hR_def, Subst.onTy_append, Subst.onTy_append, hproxy, hS₀comm]
    exact hzip'.symm
