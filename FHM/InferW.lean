import FHM.CorePath
import FHM.RuntimeTyping

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


/-! ## The Algorithm W inference relation

`Infer Φ ctx e Φ' S τ` is Algorithm W phrased as a *relation* (no function /
termination obligation in the relation itself). It reads: starting with the
fresh-variable frontier `Φ` (every unification var in play is `< Φ`), expression
`e` infers type `τ` under the most-general substitution `S`, allocating fresh
vars up to the new frontier `Φ'`. `.fvar`s are the unification variables;
composition of the threaded substitutions is `++`.

This covers the full language and is connected to the declarative `TypeOfHM`
source judgment by `Infer.sourceSound`, and to the runnable erased term by
`Infer.sound`. Principality and completeness are proved in `FHM.Completeness`. -/

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

/-! The ceiling solver below is retained as auxiliary substitution algebra from
the monomorphic-recursion implementation. Mixed recursive inference does not
call it: annotated members are checked by `InferRecGroup.consPoly`. -/

/-- The legacy recursive BODY environment under a ceiling: annotated members at their
    (opened) annotation, unannotated members at their generalised scheme
    `genGroup G τⱼ`. -/
def RecSpecs.ceilingSchemes (G : List Nat) (anns : List (Option PolyTy)) (specs : List RecSpec) : List PolyTy :=
  (anns.zip specs).map (fun p => match p.1 with
    | some σ => σ
    | none => RecSpec.bodyScheme G p.2)

/-! ### Sequential recursive-annotation constraints

The recursive-group worker uses a small, certified constraint pass: an
annotation is compared with the *current* monotype, and
only the non-pool part of that comparison is committed to later members.  The
pool is deliberately fixed: equations over a generalisation variable are
useful for checking this annotation, but must not rewrite the rest of the
group.

The relation is stated separately so its fixed-pool invariant can be reused by
the relational and executable inference proofs. -/

/-- Discard bindings whose domain is in the fixed generalisation pool. -/
def Subst.dropDomains (G : List Nat) (S : Subst) : Subst :=
  S.filter (fun p => !G.contains p.1)

theorem Subst.mem_dropDomains {G : List Nat} {S : Subst} {p : Nat × Ty} :
    p ∈ S.dropDomains G ↔ p ∈ S ∧ p.1 ∉ G := by
  simp [Subst.dropDomains, List.mem_filter, List.contains_eq_mem]

/-- Boolean range guard used by the executable constraint pass.  Requiring all
    committed images to mention only `rigid` names simultaneously prevents
    skolem/pool leakage and makes the pool-preservation invariant explicit.
    Environment free variables are intentionally not added here: they remain
    flexible domains which an annotation may refine, while any stable fvar an
    annotation can introduce already occurs in its source and hence in `rigid`. -/
def Subst.rangesWithin (rigid G : List Nat) (S : Subst) : Bool :=
  S.all (fun p => p.2.freeVars.all (fun x => rigid.contains x && !G.contains x))

theorem Subst.rangesWithin_iff {rigid G : List Nat} {S : Subst} :
    S.rangesWithin rigid G = true ↔
      ∀ p ∈ S, ∀ x ∈ p.2.freeVars, x ∈ rigid ∧ x ∉ G := by
  constructor
  · intro h p hp x hx
    change S.all (fun p => p.2.freeVars.all
      (fun x => rigid.contains x && !G.contains x)) = true at h
    have hp' := List.all_eq_true.mp h p hp
    have hx' := List.all_eq_true.mp hp' x hx
    simpa [List.contains_eq_mem] using hx'
  · intro h
    change S.all (fun p => p.2.freeVars.all
      (fun x => rigid.contains x && !G.contains x)) = true
    apply List.all_eq_true.mpr
    intro p hp
    apply List.all_eq_true.mpr
    intro x hx
    simpa [List.contains_eq_mem] using h p hp x hx

/-- Sequential ceiling constraints for a recursive group.

For an annotated monomorphic member, `full` is the complete rigid unifier of
the current type and the freshly opened annotation.  `step` is exactly
`full` projected away from `G`; only `step` is threaded through the remaining
specifications.  We retain `full` (rather than merely its equality result) so
the later principality proof can invoke `UnifyRel.greatest_factors`.

Each annotation body is required to have its free variables among `rigid`.
Consequently the domain-avoidance invariant below proves that all committed
substitutions leave annotations literally unchanged. -/
def RecCeilingConstraints (K rigid G : List Nat) (Φ : Nat) :
    List (Option PolyTy) → List RecSpec → Subst → Prop
  | [], [], S => S = []
  | none :: anns, _ :: specs, S =>
      RecCeilingConstraints K rigid G Φ anns specs S
  | some σ :: anns, .mono τ :: specs, S =>
      ∃ full step tail,
        UnifyRel τ (σ.openVars (freshVars Φ σ.paramCount)) full ∧
        (∀ p ∈ full, p.1 ∉ K ++ rigid ++ freshVars Φ σ.paramCount) ∧
        step = Subst.dropDomains G full ∧
        (∀ p ∈ step, ∀ x ∈ p.2.freeVars, x ∈ rigid ∧ x ∉ G) ∧
        (∀ p ∈ step, p.2.IsLC) ∧
        σ.WF ∧
        (∀ x ∈ σ.body.freeVars, x ∈ rigid) ∧
        RecCeilingConstraints K rigid G Φ anns
          (specs.map (RecSpec.onSubst step)) tail ∧
        S = step ++ tail
  | some _ :: _, .poly _ :: _, _ => False
  | _, _, _ => False

/-- Every committed substitution in a sequential ceiling derivation has locally
    closed images. -/
theorem RecCeilingConstraints.lc {K rigid G Φ anns specs S}
    (h : RecCeilingConstraints K rigid G Φ anns specs S) :
    ∀ p ∈ S, p.2.IsLC := by
  induction anns generalizing specs S with
  | nil =>
    cases specs <;> simp [RecCeilingConstraints] at h
    subst S; simp
  | cons a anns ih =>
    cases a with
    | none =>
      cases specs with
      | nil => simp [RecCeilingConstraints] at h
      | cons s specs => exact ih h
    | some σ =>
      cases specs with
      | nil => simp [RecCeilingConstraints] at h
      | cons s specs =>
        cases s with
        | poly σ' => simp [RecCeilingConstraints] at h
        | mono τ =>
          rcases h with ⟨full, step, tail, _, _, _, _, hstepLC, _, _, htail, rfl⟩
          intro p hp
          rcases List.mem_append.mp hp with hp | hp
          · exact hstepLC p hp
          · exact ih htail p hp

/-- The committed output never binds a name in the ambient rigid set, the
    annotation skolems, or the fixed pool. -/
theorem RecCeilingConstraints.dom_avoids {K rigid G Φ anns specs S}
    (h : RecCeilingConstraints K rigid G Φ anns specs S) :
    ∀ p ∈ S, p.1 ∉ K ∧ p.1 ∉ rigid ∧ p.1 ∉ G := by
  induction anns generalizing specs S with
  | nil =>
    cases specs <;> simp [RecCeilingConstraints] at h
    subst S; simp
  | cons a anns ih =>
    cases a with
    | none =>
      cases specs with
      | nil => simp [RecCeilingConstraints] at h
      | cons s specs => exact ih h
    | some σ =>
      cases specs with
      | nil => simp [RecCeilingConstraints] at h
      | cons s specs =>
        cases s with
        | poly σ' => simp [RecCeilingConstraints] at h
        | mono τ =>
          rcases h with ⟨full, step, tail, _, hfull, hproj, _, _, _, _, htail, rfl⟩
          intro p hp
          rcases List.mem_append.mp hp with hp | hp
          · rw [hproj] at hp
            have hp' := Subst.mem_dropDomains.mp hp
            refine ⟨?_, ?_, hp'.2⟩
            · intro hk
              exact hfull p hp'.1 (by simp [List.mem_append, hk])
            · intro hr
              exact hfull p hp'.1 (by simp [List.mem_append, hr])
          · exact ih htail p hp

/-- Every committed image mentions only ambient rigid names. -/
theorem RecCeilingConstraints.range_subset_rigid {K rigid G Φ anns specs S}
    (h : RecCeilingConstraints K rigid G Φ anns specs S) :
    ∀ p ∈ S, ∀ x ∈ p.2.freeVars, x ∈ rigid := by
  induction anns generalizing specs S with
  | nil =>
    cases specs <;> simp [RecCeilingConstraints] at h
    subst S; simp
  | cons a anns ih =>
    cases a with
    | none =>
      cases specs with
      | nil => simp [RecCeilingConstraints] at h
      | cons s specs => exact ih h
    | some σ =>
      cases specs with
      | nil => simp [RecCeilingConstraints] at h
      | cons s specs =>
        cases s with
        | poly σ' => simp [RecCeilingConstraints] at h
        | mono τ =>
          rcases h with ⟨full, step, tail, _, _, _, hrange, _, _, _, htail, rfl⟩
          intro p hp x hx
          exact (List.mem_append.mp hp).elim
            (fun hp => (hrange p hp x hx).1) (fun hp => ih htail p hp x hx)

/-- No committed image can reintroduce a pool variable. -/
theorem RecCeilingConstraints.range_avoids_pool {K rigid G Φ anns specs S}
    (h : RecCeilingConstraints K rigid G Φ anns specs S) :
    ∀ p ∈ S, ∀ x ∈ p.2.freeVars, x ∉ G := by
  induction anns generalizing specs S with
  | nil =>
    cases specs <;> simp [RecCeilingConstraints] at h
    subst S; simp
  | cons a anns ih =>
    cases a with
    | none =>
      cases specs with
      | nil => simp [RecCeilingConstraints] at h
      | cons s specs => exact ih h
    | some σ =>
      cases specs with
      | nil => simp [RecCeilingConstraints] at h
      | cons s specs =>
        cases s with
        | poly σ' => simp [RecCeilingConstraints] at h
        | mono τ =>
          rcases h with ⟨full, step, tail, _, _, _, hrange, _, _, _, htail, rfl⟩
          intro p hp x hx
          exact (List.mem_append.mp hp).elim
            (fun hp => (hrange p hp x hx).2) (fun hp => ih htail p hp x hx)

/-- A committed output fixes every pool variable. -/
theorem RecCeilingConstraints.fixes_pool {K rigid G Φ anns specs S}
    (h : RecCeilingConstraints K rigid G Φ anns specs S) :
    ∀ g ∈ G, S.onTy (.fvar g) = .fvar g := by
  intro g hg
  change Ty.substFvars S (.fvar g) = .fvar g
  apply Ty.substFvars_eq_self_of_no_key
  intro p hp heq
  have hpEq : p.1 = g := by simpa [Ty.freeVars] using heq
  exact (h.dom_avoids p hp).2.2 (hpEq ▸ hg)

/-- A substitution whose domain avoids every free variable of a scheme leaves
    that scheme literally unchanged. -/
theorem Subst.onPolyTy_eq_self_of_dom_avoids {S : Subst} {σ : PolyTy}
    (hdom : ∀ p ∈ S, p.1 ∉ σ.body.freeVars) : S.onPolyTy σ = σ := by
  obtain ⟨pc, body⟩ := σ
  simp only [Subst.onPolyTy, PolyTy.mk.injEq, true_and]
  exact Ty.substFvars_eq_self_of_no_key hdom

/-- The relation records that every stored annotation is scoped by `rigid`. -/
theorem RecCeilingConstraints.annotation_fv_rigid {K rigid G Φ anns specs S}
    (h : RecCeilingConstraints K rigid G Φ anns specs S) :
    ∀ σ, some σ ∈ anns → ∀ x ∈ σ.body.freeVars, x ∈ rigid := by
  induction anns generalizing specs S with
  | nil => simp
  | cons a anns ih =>
    cases a with
    | none =>
      cases specs with
      | nil => simp [RecCeilingConstraints] at h
      | cons s specs =>
        intro σ hmem x hx
        exact ih h σ (by simpa using hmem) x hx
    | some σ0 =>
      cases specs with
      | nil => simp [RecCeilingConstraints] at h
      | cons s specs =>
        cases s with
        | poly σ' => simp [RecCeilingConstraints] at h
        | mono τ =>
          rcases h with ⟨full, step, tail, _, _, _, _, _, _, hσ0rigid, htail, rfl⟩
          intro σ hmem
          simp only [List.mem_cons, Option.some.injEq] at hmem
          rcases hmem with rfl | hmem
          · exact hσ0rigid
          · exact ih htail σ hmem

/-- All stored annotations remain fixed by the total committed substitution. -/
theorem RecCeilingConstraints.fixes_annotations {K rigid G Φ anns specs S}
    (h : RecCeilingConstraints K rigid G Φ anns specs S) :
    ∀ σ, some σ ∈ anns → S.onPolyTy σ = σ := by
  intro σ hσ
  apply Subst.onPolyTy_eq_self_of_dom_avoids
  intro p hp hfv
  exact (h.dom_avoids p hp).2.1 (h.annotation_fv_rigid σ hσ p.1 hfv)

/-! Algorithm W as a type-directed inference relation over the source `Expr`.
    Its outputs are only the fresh-variable frontier, substitution, and inferred
    monotype; runtime execution uses the independently defined erased source term.
    The relation is mutually defined with the `match_` and `letRec` threaders
    `InferBranches` and `InferRecGroup`. -/
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
  /-- Annotated `let` with scoped type variables. The bound scheme is
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
  /-- Mixed recursive groups: inferred members recurse monomorphically;
      annotated members are checked at their declared schemes and may be used
      polymorphically throughout the group. -/
  | letRec {Φ ctx anns bindings body Φ₁ Φ₂ S₁ S₂ τ₂ G specs1} :
    (∀ σ, some σ ∈ anns → σ.WF) →
    InferRecGroup (Φ + bindings.length)
        { ctx with env := (RecSpec.init Φ anns).map (RecSpec.rhsEntry [] []) ++ ctx.env }
        bindings
        (RecSpec.init Φ anns)
        Φ₁ S₁ →
    specs1 = (RecSpec.init Φ anns).map (RecSpec.onSubst S₁) →
    G = genGroupVars (RecGroup.rigidVars anns bindings) (S₁.onCtx ctx).env
      (RecSpecs.monoTys specs1) →
    Infer Φ₁
      { (S₁.onCtx ctx) with
        env := specs1.map (RecSpec.bodyScheme G) ++ (S₁.onCtx ctx).env }
      body Φ₂ S₂ τ₂ →
    Infer Φ ctx (.letRec anns bindings body) Φ₂ (S₁ ++ S₂) τ₂

/-- Threads inference through a `match_`'s branch list. Carries the scrutinee type
    `scrutTy` (which each *named* pattern constrains to its ADT by unifying it with a
    fresh `customTy` instance) and a running result type `ρ` that each branch body's
    type is unified against, with substitutions propagated to the next branch. An
    all-wildcard list leaves `scrutTy` free. -/
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

/-- Threads inference through a recursive group, solving unannotated monotypes
    and checking annotated members under fresh rigid scoped type variables. -/
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
    Infer (N + σ.paramCount) ctx
      (e.openTyVars (freshVars N σ.paramCount)) Φ₁ S₁ τ →
    UnifyRel τ (σ.openVars (freshVars N σ.paramCount)) Schk →
    (∀ y ∈ freshVars N σ.paramCount, y ∉ (S₁ ++ Schk).map Prod.fst) →
    (∀ y ∈ freshVars N σ.paramCount,
      y ∉ (Schk.onCtx (S₁.onCtx ctx)).env.freeVars) →
    InferRecGroup Φ₁ (Schk.onCtx (S₁.onCtx ctx)) rest
      (specs.map (RecSpec.onSubst (S₁ ++ Schk))) Φ₂ S₂ →
    InferRecGroup Φ ctx (e :: rest) (.poly σ :: specs) Φ₂ (S₁ ++ Schk ++ S₂)
end


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
  | letRec _ hgroup _ _ hbody =>
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

/-! ### Scoped-variable invariants

An annotated bound expression is inferred after opening it at rigid skolems, so
its annotation free variables are the in-scope skolems rather than necessarily
being empty. Soundness threads an ambient rigid-skolem set `K`; substitutions
avoid `K`, and the cofinite premise is recovered by renaming `K` to fresh names
through `Expr.substTyFvars_zip_openTyVars`. -/

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
  | letRec hwfanns hgroup hspecs1 hG hbody =>
    intro hctx
    expose_names
    subst specs1 G
    have hinitLC : ∀ s ∈ RecSpec.init Φ anns, s.LC := by
      intro s hs
      rcases RecSpec.mem_init hs with ⟨m, _, _, rfl⟩ | ⟨σ, hσ, rfl⟩
      · exact ContainsBvarsUpTo.fvar
      · exact hwfanns σ hσ
    have hctxg : CtxWF { ctx with
        env := (RecSpec.init Φ anns).map (RecSpec.rhsEntry [] []) ++ ctx.env } := by
      intro M hM
      rcases List.mem_append.mp hM with hM | hM
      · obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hM
        exact RecSpec.rhsEntry_nil_wf (hinitLC s hs)
      · exact hctx M hM
    have hS₁lc := InferRecGroup.lc hgroup hctxg hinitLC
    obtain ⟨hbody_lc, hbody_s⟩ := Infer.lc hbody (by
      intro M hM
      rcases List.mem_append.mp hM with hM | hM
      · obtain ⟨s', hs', rfl⟩ := List.mem_map.mp hM
        obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hs'
        exact RecSpec.bodyScheme_wf (RecSpec.LC.onSubst hS₁lc (hinitLC s hs))
      · exact (Subst.onCtx_wf hS₁lc hctx) M hM)
    refine ⟨hbody_lc, ?_⟩
    intro p hp; rw [List.mem_append] at hp
    rcases hp with hp | hp
    · exact hS₁lc p hp
    · exact hbody_s p hp
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
/-- `InferRecGroup` local-closedness: from a
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

/-- The committed part of a ceiling pass stays below any frontier containing
    its ambient rigid names.  This is intentionally stated independently of
    the full unifiers: only the committed range is relevant to later W phases. -/
theorem RecCeilingConstraints.belowFvars {K rigid G Φ anns specs S Ψ}
    (h : RecCeilingConstraints K rigid G Φ anns specs S)
    (hrigid : ∀ x ∈ rigid, x < Ψ) :
    ∀ p ∈ S, Ty.BelowFvars Ψ p.2 := by
  intro p hp
  apply Ty.BelowFvars.of_freeVars_lt
  intro x hx
  exact hrigid x (RecCeilingConstraints.range_subset_rigid h p hp x hx)

/-- A name outside the ambient rigid set cannot occur in the committed range.
    This is the ceiling pass's locality fact used when threading the body. -/
theorem RecCeilingConstraints.range_avoids {K rigid G Φ anns specs S} {w : Nat}
    (h : RecCeilingConstraints K rigid G Φ anns specs S) (hw : w ∉ rigid) :
    ∀ p ∈ S, w ∉ p.2.freeVars := by
  intro p hp hwf
  exact hw (RecCeilingConstraints.range_subset_rigid h p hp w hwf)

/-- A ceiling pass introduces no domain name above a frontier which already
    bounds both its current specs and the ambient rigid names.  Annotation-body
    names and opening skolems cannot be the source of a committed binding:
    the full comparison holds both sets rigid before the projection. -/
theorem RecCeilingConstraints.dom_below {K rigid G Φ anns specs S Ψ}
    (h : RecCeilingConstraints K rigid G Φ anns specs S)
    (hrigid : ∀ x ∈ rigid, x < Ψ)
    (hspecs : ∀ s ∈ specs, s.BelowFvars Ψ) :
    ∀ p ∈ S, p.1 < Ψ := by
  induction anns generalizing specs S with
  | nil =>
    cases specs <;> simp [RecCeilingConstraints] at h
    subst S
    simp
  | cons a anns ih =>
    cases a with
    | none =>
      cases specs with
      | nil => simp [RecCeilingConstraints] at h
      | cons s specs =>
        exact ih h (fun s' hs' => hspecs s' (List.mem_cons_of_mem _ hs'))
    | some σ =>
      cases specs with
      | nil => simp [RecCeilingConstraints] at h
      | cons s specs =>
        cases s with
        | poly σ' => simp [RecCeilingConstraints] at h
        | mono τ =>
          rcases h with ⟨full, step, tail, hfull, havoid, hstep, hrange, _, _, hσrigid,
            htail, rfl⟩
          have hstepBelow : ∀ q ∈ step, Ty.BelowFvars Ψ q.2 := by
            intro q hq
            apply Ty.BelowFvars.of_freeVars_lt
            intro x hx
            exact hrigid x (hrange q hq x hx).1
          intro p hp
          rcases List.mem_append.mp hp with hp | hp
          · rw [hstep] at hp
            have hpfull := (Subst.mem_dropDomains.mp hp).1
            rcases UnifyRel.dom_mem hfull p hpfull with hτ | hσ
            · exact (hspecs (.mono τ) List.mem_cons_self).mem_lt p.1 hτ
            · have hσ' : p.1 ∈ (σ.openVars (freshVars Φ σ.paramCount)).freeVars := hσ
              rcases Ty.freeVars_openVars_subset p.1 hσ' with hbody | hfresh
              · exact False.elim (havoid p hpfull (by
                  simp [List.mem_append, hσrigid p.1 hbody]))
              · exact False.elim (havoid p hpfull (by
                  simp [List.mem_append, hfresh]))
          · exact ih htail (fun s' hs' => by
              obtain ⟨s0, hs0, rfl⟩ := List.mem_map.mp hs'
              exact RecSpec.BelowFvars.onSubst hstepBelow
                (hspecs s0 (List.mem_cons_of_mem _ hs0))) p hp

/-- If a name is absent from the ambient rigid set and every current spec,
    a ceiling pass cannot add it to its domain.  The frontier premise excludes
    the freshly-opened annotation variables. -/
theorem RecCeilingConstraints.dom_avoid {K rigid G Φ anns specs S} {w : Nat}
    (h : RecCeilingConstraints K rigid G Φ anns specs S)
    (hwRigid : w ∉ rigid) (hwΦ : w < Φ)
    (hspecs : ∀ s ∈ specs, w ∉ s.freeVars) :
    w ∉ S.map Prod.fst := by
  have hkeys : ∀ p ∈ S, p.1 ≠ w := by
    induction anns generalizing specs S with
    | nil =>
      cases specs <;> simp [RecCeilingConstraints] at h
      subst S
      simp
    | cons a anns ih =>
      cases a with
      | none =>
        cases specs with
        | nil => simp [RecCeilingConstraints] at h
        | cons s specs =>
          exact ih h (fun s' hs' => hspecs s' (List.mem_cons_of_mem _ hs'))
      | some σ =>
        cases specs with
        | nil => simp [RecCeilingConstraints] at h
        | cons s specs =>
          cases s with
          | poly σ' => simp [RecCeilingConstraints] at h
          | mono τ =>
            rcases h with ⟨full, step, tail, hfull, _, hstep, hrange, _, _, hσrigid, htail, rfl⟩
            have hstepAvoid : ∀ q ∈ step, w ∉ q.2.freeVars := by
              intro q hq hwq
              exact hwRigid (hrange q hq w hwq).1
            intro p hp hpw
            rcases List.mem_append.mp hp with hp | hp
            · rw [hstep] at hp
              have hpfull := (Subst.mem_dropDomains.mp hp).1
              rcases UnifyRel.dom_mem hfull p hpfull with hτ | hσ
              · exact hspecs (.mono τ) List.mem_cons_self (by
                  simpa [RecSpec.freeVars, hpw] using hτ)
              · have hσ' : p.1 ∈ (σ.openVars (freshVars Φ σ.paramCount)).freeVars := hσ
                rcases Ty.freeVars_openVars_subset p.1 hσ' with hbody | hfresh
                · exact hwRigid (by simpa [hpw] using hσrigid p.1 hbody)
                · have := freshVars_ge w (by simpa [hpw] using hfresh)
                  omega
            · apply ih htail (fun s' hs' => by
                obtain ⟨s0, hs0, rfl⟩ := List.mem_map.mp hs'
                cases s0 with
                | mono τ0 =>
                  intro hc
                  rcases Subst.mem_freeVars_onTy hc with hτ | ⟨q, hq, hqfv⟩
                  · exact (hspecs (.mono τ0) (List.mem_cons_of_mem _ hs0))
                      (by simpa [RecSpec.freeVars] using hτ)
                  · exact hstepAvoid q hq hqfv
                | poly σ0 =>
                  simpa [RecSpec.onSubst, RecSpec.freeVars] using
                    hspecs (.poly σ0) (List.mem_cons_of_mem _ hs0)) p hp hpw
  intro hwS
  obtain ⟨p, hp, hpw⟩ := List.mem_map.mp hwS
  exact hkeys p hp hpw

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
  | letRec hwfanns hgroup hspecs1 hG hbody =>
    intro hctx htfv
    expose_names
    subst specs1 G
    simp only [Expr.tyFreeVars, List.mem_append] at htfv
    have hlen : bindings.length = anns.length :=
      (InferRecGroup.length_eq hgroup).trans (RecSpec.init_length Φ anns)
    have hSch : ∀ σ, some σ ∈ anns → Ty.BelowFvars Φ σ.body := fun σ hσ =>
      Ty.BelowFvars.of_freeVars_lt (fun v hv =>
        htfv v (.inl (.inl (Expr.scheme_body_mem_annList_tyFreeVars hσ hv))))
    have hinitB : ∀ s ∈ RecSpec.init Φ anns, s.BelowFvars (Φ + bindings.length) := by
      intro s hs
      rcases RecSpec.mem_init hs with ⟨m, _, hm2, rfl⟩ | ⟨σ, hσ, rfl⟩
      · exact .fvar (by omega)
      · exact (hSch σ hσ).mono (by omega)
    have hctxgB : CtxBelow (Φ + bindings.length) { ctx with
        env := (RecSpec.init Φ anns).map (RecSpec.rhsEntry [] []) ++ ctx.env } := by
      intro M hM
      rcases List.mem_append.mp hM with hM | hM
      · obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hM
        exact RecSpec.rhsEntry_nil_belowFvars (hinitB s hs)
      · exact (hctx M hM).mono (by omega)
    have hgrle := InferRecGroup.frontier_le hgroup
    have hS₁ := InferRecGroup.belowFvars hgroup hctxgB hinitB
      (fun y hy => lt_of_lt_of_le (htfv y (.inl (.inr hy))) (by omega))
    obtain ⟨hb_τ, hb_s⟩ := Infer.belowFvars hbody (by
      intro M hM
      rcases List.mem_append.mp hM with hM | hM
      · obtain ⟨s', hs', rfl⟩ := List.mem_map.mp hM
        obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hs'
        exact RecSpec.bodyScheme_belowFvars
          (RecSpec.BelowFvars.onSubst hS₁ ((hinitB s hs).mono hgrle))
      · exact (Subst.onCtx_below hS₁ (by omega) hctx) M hM)
      (fun y hy => lt_of_lt_of_le (htfv y (.inr hy)) (by omega))
    have hble := Infer.frontier_le hbody
    refine ⟨hb_τ, ?_⟩
    intro p hp; rw [List.mem_append] at hp
    rcases hp with hp | hp
    · exact (hS₁ p hp).mono hble
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
/-- `InferRecGroup` frontier bound: every replacement
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


/-! ### M2: substitution-domain and inferred-result free-variable locality

`Infer.dom_below` extends the frontier discipline to the substitution **domain**
(`∀ p ∈ S, p.1 < Φ'`, via `UnifyRel.dom_mem` + `Infer.belowFvars`).
`Infer.range_avoid` is the corresponding avoid-form locality theorem: a variable
below the input frontier that avoids both the context env and the source's
annotation free vars cannot appear in the inferred type or substitution range.
Together with
idempotency (`Infer.eliminates`, M3), this yields the prefix-fix corollary (M4)
used by soundness. -/

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
  | letRec hwfanns hgroup hspecs1 hG hbody =>
    intro hctx htfv
    expose_names
    subst specs1 G
    simp only [Expr.tyFreeVars, List.mem_append] at htfv
    have hlen : bindings.length = anns.length :=
      (InferRecGroup.length_eq hgroup).trans (RecSpec.init_length Φ anns)
    have hSch : ∀ σ, some σ ∈ anns → Ty.BelowFvars Φ σ.body := fun σ hσ =>
      Ty.BelowFvars.of_freeVars_lt (fun v hv =>
        htfv v (.inl (.inl (Expr.scheme_body_mem_annList_tyFreeVars hσ hv))))
    have hinitB : ∀ s ∈ RecSpec.init Φ anns, s.BelowFvars (Φ + bindings.length) := by
      intro s hs
      rcases RecSpec.mem_init hs with ⟨m, _, hm2, rfl⟩ | ⟨σ, hσ, rfl⟩
      · exact .fvar (by omega)
      · exact (hSch σ hσ).mono (by omega)
    have hctxgB : CtxBelow (Φ + bindings.length) { ctx with
        env := (RecSpec.init Φ anns).map (RecSpec.rhsEntry [] []) ++ ctx.env } := by
      intro M hM
      rcases List.mem_append.mp hM with hM | hM
      · obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hM
        exact RecSpec.rhsEntry_nil_belowFvars (hinitB s hs)
      · exact (hctx M hM).mono (by omega)
    have hgrle := InferRecGroup.frontier_le hgroup
    have hgtfv : ∀ y ∈ Expr.tyFreeVars.RecGroup.tyFreeVars bindings, y < Φ + bindings.length :=
      fun y hy => lt_of_lt_of_le (htfv y (.inl (.inr hy))) (by omega)
    have hg_dom := InferRecGroup.dom_below hgroup hctxgB hinitB hgtfv
    have hS₁ := InferRecGroup.belowFvars hgroup hctxgB hinitB hgtfv
    have hb_dom := Infer.dom_below hbody (by
      intro M hM
      rcases List.mem_append.mp hM with hM | hM
      · obtain ⟨s', hs', rfl⟩ := List.mem_map.mp hM
        obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hs'
        exact RecSpec.bodyScheme_belowFvars
          (RecSpec.BelowFvars.onSubst hS₁ ((hinitB s hs).mono hgrle))
      · exact (Subst.onCtx_below hS₁ (by omega) hctx) M hM)
      (fun y hy => lt_of_lt_of_le (htfv y (.inr hy)) (by omega))
    have hble := Infer.frontier_le hbody
    intro p hp; rw [List.mem_append] at hp
    rcases hp with hp | hp
    · have := hg_dom p hp; omega
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
/-- `InferRecGroup` substitution-domain bound. -/
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

mutual
/-- **Locality (avoid form).** A var below the input frontier that avoids the
    context env and the source annotation free vars also avoids the inferred
    substitution range and result type. -/
theorem Infer.range_avoid {Φ ctx e Φ' S τ} (h : Infer Φ ctx e Φ' S τ) :
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
      obtain ⟨hbS, hbτ⟩ := Infer.range_avoid hbody (w := w) (by omega)
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
      obtain ⟨hbS, hbτ⟩ := Infer.range_avoid hbody (w := w) hwΦ
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
    obtain ⟨hfS, hfτ⟩ := Infer.range_avoid hf (w := w) hwΦ hctx hwe.1
    have hfle := Infer.frontier_le hf
    have hargle := Infer.frontier_le harg
    obtain ⟨haS, haτ⟩ := Infer.range_avoid harg (w := w) (by omega)
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
    obtain ⟨hrS, hrτ⟩ := Infer.range_avoid hrhs (w := w) hwΦ hctx hwe.1
    have hrle := Infer.frontier_le hrhs
    have hMbody : w ∉ (genScheme rhs.tyFreeVars (S₁.onCtx ctx).env τ₁).body.freeVars :=
      fun hc => hrτ (Ty.freeVars_closeOver_subset hc)
    obtain ⟨hbS, hbτ⟩ := Infer.range_avoid hbody (w := w) (by omega)
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
    obtain ⟨hrS, hrτ⟩ := Infer.range_avoid hrhs (w := w) (by omega) hctx (by
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
    obtain ⟨hbS, hbτ⟩ := Infer.range_avoid hbody (w := w) (by omega)
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
    obtain ⟨hsS, hsτ⟩ := Infer.range_avoid hscrut (w := w) hwΦ hctx hwe.1
    have hle1 := Infer.frontier_le hscrut
    obtain ⟨hbrS, hbrρ⟩ := InferBranches.range_avoid hbr (w := w) (by omega)
      (Subst.onCtx_avoid hctx hsS) hsτ
      (by intro hc; simp only [Ty.freeVars, List.mem_singleton] at hc; omega) hwe.2
    refine ⟨?_, hbrρ⟩
    intro p hp; rw [List.mem_append] at hp
    rcases hp with hp | hp
    · exact hsS p hp
    · exact hbrS p hp
  | letRec hwfanns hgroup hspecs1 hG hbody =>
    intro w hwΦ hctx hwe
    expose_names
    subst specs1 G
    simp only [Expr.tyFreeVars, List.mem_append, not_or] at hwe
    have hgle := InferRecGroup.frontier_le hgroup
    have hspecsA : ∀ s ∈ RecSpec.init Φ anns, w ∉ s.freeVars := by
      intro s hs
      rcases RecSpec.mem_init hs with ⟨m, hm1, _, rfl⟩ | ⟨σ, hσ, rfl⟩
      · show w ∉ (Ty.fvar m).freeVars
        simp only [Ty.freeVars, List.mem_singleton]
        omega
      · exact fun hc => hwe.1.1 (Expr.scheme_body_mem_annList_tyFreeVars hσ hc)
    have hgS := InferRecGroup.range_avoid hgroup (w := w) (by omega)
      (by intro M hM
          rcases List.mem_append.mp hM with hM | hM
          · obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hM
            rw [RecSpec.rhsEntry_nil_body_freeVars]
            exact hspecsA s hs
          · exact hctx M hM)
      hspecsA hwe.1.2
    have hsolvedA : ∀ s' ∈ (RecSpec.init Φ anns).map (RecSpec.onSubst S₁), w ∉ s'.freeVars := by
      intro s' hs'
      obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hs'
      exact RecSpec.notMem_freeVars_onSubst hgS (hspecsA s hs)
    obtain ⟨hbS, hbτ⟩ := Infer.range_avoid hbody (w := w) (by omega)
      (by intro M hM
          rcases List.mem_append.mp hM with hM | hM
          · obtain ⟨s', hs', rfl⟩ := List.mem_map.mp hM
            exact fun hc => hsolvedA s' hs' (RecSpec.mem_bodyScheme_freeVars hc)
          · exact Subst.onCtx_avoid hctx hgS M hM)
      hwe.2
    refine ⟨?_, hbτ⟩
    · intro p hp; rw [List.mem_append] at hp
      rcases hp with hp | hp
      · exact hgS p hp
      · exact hbS p hp
termination_by e.size
decreasing_by
  all_goals (try subst_vars; try simp only [Expr.size, Expr.size_openTyVars]; omega)
theorem InferBranches.range_avoid {Φ ctx scrutTy ρ brs Φ' S}
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
    obtain ⟨hbS, hbτ⟩ := Infer.range_avoid hbody (w := w) (by omega)
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
    obtain ⟨hrS, hrρ⟩ := InferBranches.range_avoid hrest (w := w) (by omega)
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
    obtain ⟨hbS, hbτ⟩ := Infer.range_avoid hbody (w := w) hwΦ hctx hbrs.1
    have hS₂ : ∀ p ∈ S₂, w ∉ p.2.freeVars := by
      intro p hp hwp
      rcases UnifyRel.range_mem huni p hp w hwp with h | h
      · exact hbτ h
      · exact Subst.notMemOnTy hbS hρ h
    obtain ⟨hrS, hrρ⟩ := InferBranches.range_avoid hrest (w := w) (by omega)
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
/-- `InferRecGroup` locality (avoid form): a var below the input frontier
    that avoids the context, specs, and binding annotation vars is absent from
    the substitution range. -/
theorem InferRecGroup.range_avoid {Φ ctx bindings specs Φ' S}
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
    obtain ⟨heS, heτ⟩ := Infer.range_avoid he (w := w) hwΦ hctx hbinds.1
    have hτA : w ∉ τ.freeVars := hspecs (.mono τ) List.mem_cons_self
    have hS₂ : ∀ p ∈ S₂, w ∉ p.2.freeVars := by
      intro p hp hwp
      rcases UnifyRel.range_mem huni p hp w hwp with h | h
      · exact heτ h
      · exact Subst.notMemOnTy heS hτA h
    have hrS : ∀ p ∈ S₃, w ∉ p.2.freeVars :=
      InferRecGroup.range_avoid hrest (w := w) (by omega)
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
    obtain ⟨heS, heτ⟩ := Infer.range_avoid hinfer (w := w) (by omega) hctx hwopen
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
      InferRecGroup.range_avoid hrest (w := w) (by omega)
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
`B` is inferred in a world avoiding `dom(A)`), discharged via `Infer.range_avoid`. -/

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

/- Projection away from a domain set preserves the occurs-check/idempotence
    invariant of a structural unifier.  This is stronger than the ceiling pass
    needs, but it is the key reason `dropDomains G full` is a safe committed
    substitution rather than merely a bookkeeping filter. -/
mutual
theorem UnifyRel.dropDomains_eliminates : {a b : Ty} → {S : Subst} →
    UnifyRel a b S → ∀ G : List Nat, ∀ p ∈ S.dropDomains G, ∀ x : Ty,
      p.1 ∉ ((S.dropDomains G).onTy x).freeVars
  | _, _, _, .prim => by simp [Subst.dropDomains]
  | _, _, _, .fvarRefl => by simp [Subst.dropDomains]
  | _, _, _, .fvarL _ hocc => by
    intro G p hp x
    simp only [Subst.dropDomains, List.filter_cons, List.filter_nil] at hp ⊢
    split at hp <;> simp_all
    exact Ty.not_mem_freeVars_substFvar_self hocc
  | _, _, _, .fvarR _ hocc => by
    intro G p hp x
    simp only [Subst.dropDomains, List.filter_cons, List.filter_nil] at hp ⊢
    split at hp <;> simp_all
    exact Ty.not_mem_freeVars_substFvar_self hocc
  | _, _, _, @UnifyRel.arrow a b c d S₁ S₂ h₁ h₂ => by
    intro G p hp x
    rw [show Subst.dropDomains G (S₁ ++ S₂) =
      Subst.dropDomains G S₁ ++ Subst.dropDomains G S₂ by simp [Subst.dropDomains]] at hp ⊢
    refine Subst.eliminates_append (UnifyRel.dropDomains_eliminates h₁ G)
      (UnifyRel.dropDomains_eliminates h₂ G) ?_ p hp x
    intro q hq r hr hqrange
    have hqfull : q ∈ S₁ := (Subst.mem_dropDomains.mp hq).1
    have hrfull : r ∈ S₂ := (Subst.mem_dropDomains.mp hr).1
    rcases UnifyRel.range_mem h₂ r hrfull q.1 hqrange with h | h
    · exact UnifyRel.eliminates h₁ q hqfull b h
    · exact UnifyRel.eliminates h₁ q hqfull d h
  | _, _, _, .customTy hl => by
    intro G
    exact UnifyRelList.dropDomains_eliminates hl G
theorem UnifyRelList.dropDomains_eliminates : {as bs : List Ty} → {S : Subst} →
    UnifyRelList as bs S → ∀ G : List Nat, ∀ p ∈ S.dropDomains G, ∀ x : Ty,
      p.1 ∉ ((S.dropDomains G).onTy x).freeVars
  | _, _, _, .nil => by simp [Subst.dropDomains]
  | _, _, _, @UnifyRelList.cons t₁ t₂ ts₁ ts₂ S₁ S₂ h₁ h₂ => by
    intro G p hp x
    rw [show Subst.dropDomains G (S₁ ++ S₂) =
      Subst.dropDomains G S₁ ++ Subst.dropDomains G S₂ by simp [Subst.dropDomains]] at hp ⊢
    refine Subst.eliminates_append (UnifyRel.dropDomains_eliminates h₁ G)
      (UnifyRelList.dropDomains_eliminates h₂ G) ?_ p hp x
    intro q hq r hr hqrange
    have hqfull : q ∈ S₁ := (Subst.mem_dropDomains.mp hq).1
    have hrfull : r ∈ S₂ := (Subst.mem_dropDomains.mp hr).1
    rcases UnifyRelList.range_mem h₂ r hrfull q.1 hqrange with
      ⟨t, ht, hfv⟩ | ⟨t, ht, hfv⟩
    · obtain ⟨t0, ht0, rfl⟩ := List.mem_map.mp ht
      exact UnifyRel.eliminates h₁ q hqfull t0 hfv
    · obtain ⟨t0, ht0, rfl⟩ := List.mem_map.mp ht
      exact UnifyRel.eliminates h₁ q hqfull t0 hfv
end

/-- The whole committed ceiling substitution is idempotent.  At each
    sequential boundary, an earlier committed domain avoids `rigid`, while the
    later committed range is contained in `rigid`; this is exactly the cross
    condition for substitution composition. -/
theorem RecCeilingConstraints.eliminates {K rigid G Φ anns specs S}
    (h : RecCeilingConstraints K rigid G Φ anns specs S) :
    ∀ p ∈ S, ∀ x : Ty, p.1 ∉ (S.onTy x).freeVars := by
  induction anns generalizing specs S with
  | nil =>
    cases specs <;> simp [RecCeilingConstraints] at h
    subst S
    simp
  | cons a anns ih =>
    cases a with
    | none =>
      cases specs with
      | nil => simp [RecCeilingConstraints] at h
      | cons s specs => exact ih h
    | some σ =>
      cases specs with
      | nil => simp [RecCeilingConstraints] at h
      | cons s specs =>
        cases s with
        | poly σ' => simp [RecCeilingConstraints] at h
        | mono τ =>
          rcases h with ⟨full, step, tail, hfull, havoid, hstep, _, _, _, _, htail, rfl⟩
          subst step
          intro p hp x
          refine Subst.eliminates_append (UnifyRel.dropDomains_eliminates hfull G) (ih htail)
            ?_ p hp x
          intro p hp q hq hpq
          have hpfull := (Subst.mem_dropDomains.mp hp).1
          have hpRigid : p.1 ∉ rigid := by
            intro hpR
            exact havoid p hpfull (by simp [List.mem_append, hpR])
          exact hpRigid (RecCeilingConstraints.range_subset_rigid htail q hq p.1 hpq)

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
      (Infer.range_avoid harg (w := p.1) (hf_dom p hp)
        (Subst.eliminates_onCtx (hfE p hp)) (hSa1 p hp)).1 q hq
    have h12E := Subst.eliminates_append hfE haE hcross12
    have hcross123 : ∀ p ∈ S₁ ++ S₂, ∀ q ∈ S₃, p.1 ∉ q.2.freeVars := by
      intro p hp q hq hwq
      have hrm := UnifyRel.range_mem huni q hq p.1 hwq
      rcases List.mem_append.mp hp with hpS₁ | hpS₂
      · have havoid := Infer.range_avoid harg (w := p.1) (hf_dom p hpS₁)
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
      (Infer.range_avoid hbody (w := p.1) (hr_dom p hp) (hbavoid p hp) (hSb1 p hp)).1 q hq
    refine ⟨Subst.eliminates_append hrE hbE hcross, ?_⟩
    intro p hp
    rcases List.mem_append.mp hp with hpS₁ | hpS₂
    · exact (Infer.range_avoid hbody (w := p.1) (hr_dom p hpS₁) (hbavoid p hpS₁) (hSb1 p hpS₁)).2
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
      (Infer.range_avoid hbody (w := p.1) (hdomall p hp) (hbodyctx p hp) (hSbody p hp)).1 q hq
    refine ⟨Subst.eliminates_append hE1Schk hbE cross2, ?_⟩
    intro p hp
    rcases List.mem_append.mp hp with hp1Schk | hpS₂
    · exact (Infer.range_avoid hbody (w := p.1) (hdomall p hp1Schk)
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
      (InferBranches.range_avoid hbr (w := p.1) (by have := hs_dom p hp; omega)
        (Subst.eliminates_onCtx (hsE p hp)) (hsR p hp)
        (by intro hc; simp only [Ty.freeVars, List.mem_singleton] at hc; have := hs_dom p hp; omega)
        (hSs1br p hp)).1 q hq
    refine ⟨Subst.eliminates_append hsE hbrE hcross, ?_⟩
    intro p hp
    rcases List.mem_append.mp hp with hpS₁ | hpS₂
    · exact (InferBranches.range_avoid hbr (w := p.1) (by have := hs_dom p hpS₁; omega)
        (Subst.eliminates_onCtx (hsE p hpS₁)) (hsR p hpS₁)
        (by intro hc; simp only [Ty.freeVars, List.mem_singleton] at hc; have := hs_dom p hpS₁; omega)
        (hSs1br p hpS₁)).2
    · exact hbrE p hpS₂ (Ty.fvar Φ₁)
  | letRec hwfanns hgroup hspecs1 hG hbody =>
    expose_names
    subst specs1 G
    have hgle := InferRecGroup.frontier_le hgroup
    have hΦbind : ∀ y ∈ Expr.tyFreeVars.RecGroup.tyFreeVars bindings, y < Φ := fun y hy => hΦ y (by
      simp only [Expr.tyFreeVars, List.mem_append]; exact .inl (.inr hy))
    have hΦanns : ∀ y ∈ Expr.tyFreeVars.AnnList.tyFreeVars anns, y < Φ := fun y hy => hΦ y (by
      simp only [Expr.tyFreeVars, List.mem_append]; exact .inl (.inl hy))
    have hΦbody : ∀ y ∈ body.tyFreeVars, y < Φ := fun y hy => hΦ y (by
      simp only [Expr.tyFreeVars, List.mem_append]; exact .inr hy)
    have hSbind : ∀ p ∈ S₁, p.1 ∉ Expr.tyFreeVars.RecGroup.tyFreeVars bindings := fun p hp hc =>
      hSe p (List.mem_append_left _ hp) (by
        simp only [Expr.tyFreeVars, List.mem_append]; exact .inl (.inr hc))
    have hSanns : ∀ p ∈ S₁, ∀ σ, some σ ∈ anns → p.1 ∉ σ.body.freeVars := fun p hp σ hσ hc =>
      hSe p (List.mem_append_left _ hp) (by
        simp only [Expr.tyFreeVars, List.mem_append]
        exact .inl (.inl (Expr.scheme_body_mem_annList_tyFreeVars hσ hc)))
    have hSbody1 : ∀ p ∈ S₁, p.1 ∉ body.tyFreeVars := fun p hp hc =>
      hSe p (List.mem_append_left _ hp) (by
        simp only [Expr.tyFreeVars, List.mem_append]; exact .inr hc)
    have hSbody2 : ∀ p ∈ S₂, p.1 ∉ body.tyFreeVars := fun p hp hc =>
      hSe p (List.mem_append_right _ hp) (by
        simp only [Expr.tyFreeVars, List.mem_append]; exact .inr hc)
    have hlen : bindings.length = anns.length :=
      (InferRecGroup.length_eq hgroup).trans (RecSpec.init_length Φ anns)
    have hSch : ∀ σ, some σ ∈ anns → Ty.BelowFvars Φ σ.body := fun σ hσ =>
      Ty.BelowFvars.of_freeVars_lt (fun v hv =>
        hΦanns v (Expr.scheme_body_mem_annList_tyFreeVars hσ hv))
    have hinitB : ∀ s ∈ RecSpec.init Φ anns, s.BelowFvars (Φ + bindings.length) := by
      intro s hs
      rcases RecSpec.mem_init hs with ⟨m, _, hm2, rfl⟩ | ⟨σ, hσ, rfl⟩
      · exact .fvar (by omega)
      · exact (hSch σ hσ).mono (by omega)
    have hctxgB : CtxBelow (Φ + bindings.length) { ctx with
        env := (RecSpec.init Φ anns).map (RecSpec.rhsEntry [] []) ++ ctx.env } := by
      intro M hM
      rcases List.mem_append.mp hM with hM | hM
      · obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hM
        exact RecSpec.rhsEntry_nil_belowFvars (hinitB s hs)
      · exact (hctx M hM).mono (by omega)
    have hgtfv : ∀ y ∈ Expr.tyFreeVars.RecGroup.tyFreeVars bindings, y < Φ + bindings.length :=
      fun y hy => lt_of_lt_of_le (hΦbind y hy) (by omega)
    have hgE := InferRecGroup.eliminates hgroup hctxgB hinitB hgtfv hSbind
      (fun p hp σ hσ => hSanns p hp σ (RecSpec.poly_mem_init hσ))
    have hg_dom := InferRecGroup.dom_below hgroup hctxgB hinitB hgtfv
    have hS₁bel := InferRecGroup.belowFvars hgroup hctxgB hinitB hgtfv
    have hbodyctxB : CtxBelow Φ₁ { (S₁.onCtx ctx) with
        env := ((RecSpec.init Φ anns).map (RecSpec.onSubst S₁)).map
                 (RecSpec.bodyScheme (genGroupVars (RecGroup.rigidVars anns bindings)
                   (S₁.onCtx ctx).env
                   (RecSpecs.monoTys ((RecSpec.init Φ anns).map (RecSpec.onSubst S₁)))))
               ++ (S₁.onCtx ctx).env } := by
      intro M hM
      rcases List.mem_append.mp hM with hM | hM
      · obtain ⟨s', hs', rfl⟩ := List.mem_map.mp hM
        obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hs'
        exact RecSpec.bodyScheme_belowFvars
          (RecSpec.BelowFvars.onSubst hS₁bel ((hinitB s hs).mono hgle))
      · exact (Subst.onCtx_below hS₁bel (by omega) hctx) M hM
    obtain ⟨hbE, hbR⟩ := Infer.eliminates hbody hbodyctxB
      (fun y hy => lt_of_lt_of_le (hΦbody y hy) (by omega)) hSbody2
    have hbodyctx : ∀ p ∈ S₁, ∀ M ∈ ({ (S₁.onCtx ctx) with
        env := ((RecSpec.init Φ anns).map (RecSpec.onSubst S₁)).map
                 (RecSpec.bodyScheme (genGroupVars (RecGroup.rigidVars anns bindings)
                   (S₁.onCtx ctx).env
                   (RecSpecs.monoTys ((RecSpec.init Φ anns).map (RecSpec.onSubst S₁)))))
               ++ (S₁.onCtx ctx).env } : Ctx).env, p.1 ∉ M.body.freeVars := by
      intro p hp M hM hc
      rcases List.mem_append.mp hM with hM | hM
      · obtain ⟨s', hs', rfl⟩ := List.mem_map.mp hM
        obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hs'
        have hc' := RecSpec.mem_bodyScheme_freeVars hc
        cases s with
        | mono τ0 => exact hgE p hp τ0 hc'
        | poly σ0 => exact hSanns p hp σ0 (RecSpec.poly_mem_init hs) hc'
      · exact Subst.eliminates_onCtx (hgE p hp) M hM hc
    have hcross : ∀ p ∈ S₁, ∀ q ∈ S₂, p.1 ∉ q.2.freeVars := fun p hp q hq =>
      (Infer.range_avoid hbody (w := p.1) (hg_dom p hp) (hbodyctx p hp) (hSbody1 p hp)).1 q hq
    refine ⟨Subst.eliminates_append hgE hbE hcross, ?_⟩
    intro p hp
    rcases List.mem_append.mp hp with hpS₁ | hpS₂
    · exact (Infer.range_avoid hbody (w := p.1) (hg_dom p hpS₁) (hbodyctx p hpS₁)
        (hSbody1 p hpS₁)).2
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
      Infer.range_avoid hbody (w := p.1) (hS₀dom p hp) (hbranchAvoid p hp) (by
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
      refine (InferBranches.range_avoid hrest (w := p.1) hpdom
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
      refine (InferBranches.range_avoid hrest (w := p.1) hpdom
        (honCtx2 ▸ Subst.eliminates_onCtx (hE12 p hp))
        (happ2 scrutTy ▸ hE12 p hp scrutTy)
        (happ2 ρ ▸ hE12 p hp ρ) (hSrestAll p hp)).1 q hq
    exact Subst.eliminates_append hE12 hrestE cross2
termination_by Expr.sizeBranches brs
decreasing_by all_goals (try subst_vars; try simp only [Expr.sizeBranches]; omega)
/-- `InferRecGroup` idempotency: a group-substitution
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
      exact (InferRecGroup.range_avoid hrest (w := p.1) hpdom hpctx hptg (hSrestAll p hp)) q hq
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
      exact (InferRecGroup.range_avoid hrest (w := p.1) (hdomall p hp) hpctx hptg hprest) q hq
    exact Subst.eliminates_append hE1Schk hrestE cross2
termination_by Expr.sizeRecGroup bindings
decreasing_by
  all_goals (try subst_vars; try simp only [Expr.sizeRecGroup, Expr.size_openTyVars]; omega)

end


/-! ### Prefix-fix corollary -/

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

The substitution-**domain** twin of `Infer.range_avoid`: a var below the input
frontier that avoids the context env and the term's annotation free vars is not
**bound** by the inferred substitution. (`range_avoid` only handles the range;
`dom_below` only bounds the domain from above.) The honest soundness `let`/`letRec`
cases need this to show the body substitution leaves the *generalised* variables
untouched. Proof mirrors `range_avoid`, using `UnifyRel.dom_mem` (the unifier's
domain lies in the unified types' free vars) where `range_avoid` uses
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
    obtain ⟨hfS, hfτ⟩ := Infer.range_avoid hf (w := w) hwΦ hctx hwe.1
    have hfdom := Infer.dom_avoid hf hwΦ hctx hwe.1
    obtain ⟨haS, haτ⟩ := Infer.range_avoid harg (w := w) (by omega)
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
    obtain ⟨hrS, hrτ⟩ := Infer.range_avoid hrhs (w := w) hwΦ hctx hwe.1
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
    obtain ⟨hrS, hrτ⟩ := Infer.range_avoid hrhs (w := w) (by omega) hctx (by
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
    obtain ⟨hsS, hsτ⟩ := Infer.range_avoid hscrut (w := w) hwΦ hctx hwe.1
    have hsdom := Infer.dom_avoid hscrut hwΦ hctx hwe.1
    have hle1 := Infer.frontier_le hscrut
    have hbrdom := InferBranches.dom_avoid hbr (w := w) (by omega)
      (Subst.onCtx_avoid hctx hsS) hsτ
      (by intro hc; simp only [Ty.freeVars, List.mem_singleton] at hc; omega) hwe.2
    intro hc; simp only [List.map_append, List.mem_append] at hc
    rcases hc with hc | hc
    · exact hsdom hc
    · exact hbrdom hc
  | letRec hwfanns hgroup hspecs1 hG hbody =>
    intro w hwΦ hctx hwe
    expose_names
    subst specs1 G
    simp only [Expr.tyFreeVars, List.mem_append, not_or] at hwe
    have hgle := InferRecGroup.frontier_le hgroup
    have hspecsA : ∀ s ∈ RecSpec.init Φ anns, w ∉ s.freeVars := by
      intro s hs
      rcases RecSpec.mem_init hs with ⟨m, hm1, _, rfl⟩ | ⟨σ, hσ, rfl⟩
      · show w ∉ (Ty.fvar m).freeVars
        simp only [Ty.freeVars, List.mem_singleton]
        omega
      · exact fun hc => hwe.1.1 (Expr.scheme_body_mem_annList_tyFreeVars hσ hc)
    have hctxg : ∀ M ∈ ((RecSpec.init Φ anns).map (RecSpec.rhsEntry [] []) ++ ctx.env),
        w ∉ M.body.freeVars := by
      intro M hM
      rcases List.mem_append.mp hM with hM | hM
      · obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hM
        rw [RecSpec.rhsEntry_nil_body_freeVars]
        exact hspecsA s hs
      · exact hctx M hM
    have hgS := InferRecGroup.range_avoid hgroup (w := w) (by omega) hctxg
      hspecsA hwe.1.2
    have hgdom := InferRecGroup.dom_avoid hgroup (w := w) (by omega) hctxg
      hspecsA hwe.1.2
    have hsolvedA : ∀ s' ∈ (RecSpec.init Φ anns).map (RecSpec.onSubst S₁), w ∉ s'.freeVars := by
      intro s' hs'
      obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hs'
      exact RecSpec.notMem_freeVars_onSubst hgS (hspecsA s hs)
    have hbdom := Infer.dom_avoid hbody (w := w) (by omega)
      (by intro M hM
          rcases List.mem_append.mp hM with hM | hM
          · obtain ⟨s', hs', rfl⟩ := List.mem_map.mp hM
            exact fun hc => hsolvedA s' hs' (RecSpec.mem_bodyScheme_freeVars hc)
          · exact Subst.onCtx_avoid hctx hgS M hM)
      hwe.2
    intro hc; simp only [List.map_append, List.mem_append] at hc
    rcases hc with hc | hc
    · exact hgdom hc
    · exact hbdom hc
termination_by e.size
decreasing_by
  all_goals (try subst_vars; try simp only [Expr.size, Expr.size_openTyVars]; omega)
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
    obtain ⟨hbS, hbτ⟩ := Infer.range_avoid hbody (w := w) (by omega)
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
    obtain ⟨hbS, hbτ⟩ := Infer.range_avoid hbody (w := w) hwΦ hctx hbrs.1
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
    obtain ⟨heS, heτ⟩ := Infer.range_avoid he (w := w) hwΦ hctx hbinds.1
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
    obtain ⟨heS, heτ⟩ := Infer.range_avoid hinfer (w := w) (by omega) hctx hwopen
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

/-! ## Principality foundations -/

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


/-! ### Principality (completeness) — per-expression statement + case lemmas

`Infer.CompleteAt e` packages the principality property at a single expression,
abstracted over the frontier `Φ`, context `ctx`, input specialization `S₀`, and
declarative type `τ₀`. Each syntactic form gets its own case lemma (taking the
sub-expressions' `CompleteAt` as hypotheses, exactly the shape produced by
inducting on `e` with `Expr.rec_strong`); `Infer.completeAt`/`Infer.complete`
then just compose them. Keeping the universally-quantified `Φ ctx S₀ τ₀` inside
the predicate means each case lemma is independently stated and verifiable. -/

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

/-- Strong induction principle for `TypeOfHM`,
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
      {specs : List RecSpec} {G L : List Nat} {body : Expr} {ρ : Ty}
      (hwf : RecSpecs.WF anns bindings specs G)
      (hmono : RecSpecs.MonoTyped TypeOfHM ctx bindings specs G L)
      (hpoly : RecSpecs.PolyTyped TypeOfHM ctx bindings specs G L)
      (heq : bodyCtx = RecSpecs.bodyCtx ctx specs G)
      (hbody : TypeOfHM bodyCtx body ρ),
      (∀ Xs (hf : FreshNames L G.length Xs)
          p (hp : p ∈ bindings.zip specs) τ (hτ : p.2 = .mono τ),
        motive (RecSpecs.rhsCtx ctx specs G Xs)
          p.1 (Ty.renameG G Xs τ) (hmono Xs hf p hp τ hτ)) →
      (∀ Xs (hf : FreshNames L G.length Xs)
          p (hp : p ∈ bindings.zip specs) σ (hσ : p.2 = .poly σ)
          Ys (hfY : FreshNames (L ++ Xs) σ.paramCount Ys),
        motive (RecSpecs.rhsCtx ctx specs G Xs)
          (p.1.openTyVars Ys) (σ.openVars Ys) (hpoly Xs hf p hp σ hσ Ys hfY)) →
      motive bodyCtx body ρ hbody →
      motive ctx (.letRec anns bindings body) ρ (.letRec hwf hmono hpoly heq hbody))
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
  | letRec hwf hmono hpoly heq hbody ihmono ihpoly ihbody =>
      exact letRec hwf hmono hpoly heq hbody ihmono ihpoly ihbody
  | mk hspec heq hbodyT ih =>
      subst heq
      exact Or.inl ⟨_, _, _, _, _, rfl, hspec.lookup, hspec.scrut_eq, hspec.arity,
        hspec.bind_count, hspec.fields, hbodyT, ih⟩
  | wildcard hbodyT ih =>
      exact Or.inr ⟨rfl, hbodyT, ih⟩

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
  | letRec hwf hmono hpoly heq hbody ihmono ihpoly ihbody =>
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
      (G := W) (L := Z :: (G ++ W ++ L))
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
      intro Xs hfresh p hp τ' hτ'
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
      have henv_rhs : (specs.map (RecSpec.substFreshened Z U G W)).map (RecSpec.rhsEntry W Xs)
          = Env.substFvar Z U (specs.map (RecSpec.rhsEntry G Xs)) := by
        show _ = (specs.map (RecSpec.rhsEntry G Xs)).map (PolyTy.substFvar Z U)
        rw [List.map_map, List.map_map]
        apply List.map_congr_left
        intro s hs
        cases s with
        | mono τ =>
          show PolyTy.mkTrivial (Ty.renameG W Xs (Ty.substFvar Z U (Ty.renameG G W τ)))
            = PolyTy.substFvar Z U (PolyTy.mkTrivial (Ty.renameG G Xs τ))
          rw [key τ hs]
          rfl
        | poly σ => rfl
      obtain ⟨a, b, hab, rfl⟩ := List.mem_zip_map hp
      cases b with
      | poly σ => exact RecSpec.noConfusion hτ'
      | mono τ =>
        injection hτ' with hττ
        rw [← hττ, key τ (List.of_mem_zip hab).2]
        have hIH := ihmono Xs hXsL (a, .mono τ) hab τ rfl
        simp only [RecSpecs.rhsCtx] at hIH
        rw [Env.substFvar_append, ← henv_rhs] at hIH
        exact hIH
    · -- ANNOTATED members: the historical `letRecAnn` transport, nested inside
      -- the pool opening
      intro Xs hfresh p hp σ' hσ' Ys hYs
      have hXlen : Xs.length = G.length := hfresh.length.trans hWlen0
      have hZXs : Z ∉ Xs := fun hc => hfresh.avoid Z hc List.mem_cons_self
      have hXsL : FreshNames L G.length Xs :=
        ⟨hXlen, hfresh.nodup, fun x hx hc =>
          hfresh.avoid x hx (List.mem_cons_of_mem _ (List.mem_append_right _ hc))⟩
      have hWXs : ∀ w ∈ W, w ∉ Xs := fun w hw hc =>
        hfresh.avoid w hc (List.mem_cons_of_mem _
          (List.mem_append_left _ (List.mem_append_right _ hw)))
      have key : ∀ τ, RecSpec.mono τ ∈ specs →
          Ty.renameG W Xs (Ty.substFvar Z U (Ty.renameG G W τ))
            = Ty.substFvar Z U (Ty.renameG G Xs τ) := by
        intro τ hτ
        have hGXs : ∀ g ∈ G, g ∉ Xs := fun g hg hc =>
          hfresh.avoid g hc (List.mem_cons_of_mem _
            (List.mem_append_left _ (List.mem_append_left _ hg)))
        rw [Ty.renameG_substFvar_comm h_U_lc hZW hUW hZXs
              (Ty.renameG_isLC (hwf.mono_lc τ hτ)) hWnodup hfresh.length hWXs,
            Ty.renameG_renameG (hwf.mono_lc τ hτ) hwf.nodup hWnodup hWlen0 hXlen hGW
              (hWfree τ hτ) hWXs hGXs]
      have henv_rhs : (specs.map (RecSpec.substFreshened Z U G W)).map (RecSpec.rhsEntry W Xs)
          = Env.substFvar Z U (specs.map (RecSpec.rhsEntry G Xs)) := by
        show _ = (specs.map (RecSpec.rhsEntry G Xs)).map (PolyTy.substFvar Z U)
        rw [List.map_map, List.map_map]
        apply List.map_congr_left
        intro s hs
        cases s with
        | mono τ =>
          show PolyTy.mkTrivial (Ty.renameG W Xs (Ty.substFvar Z U (Ty.renameG G W τ)))
            = PolyTy.substFvar Z U (PolyTy.mkTrivial (Ty.renameG G Xs τ))
          rw [key τ hs]
          rfl
        | poly σ => rfl
      obtain ⟨a, b, hab, rfl⟩ := List.mem_zip_map hp
      cases b with
      | mono τ => exact RecSpec.noConfusion hσ'
      | poly σ =>
        injection hσ' with hσσ
        rw [← hσσ]
        have hpc : σ'.paramCount = σ.paramCount := by rw [← hσσ]; rfl
        have hZYs : Z ∉ Ys := fun hc =>
          hYs.avoid Z hc (List.mem_append_left _ List.mem_cons_self)
        have hYsOld : FreshNames (L ++ Xs) σ.paramCount Ys := by
          refine ⟨hYs.length.trans hpc, hYs.nodup, ?_⟩
          intro y hy hc
          rcases List.mem_append.mp hc with hcL | hcXs
          · exact hYs.avoid y hy (List.mem_append_left _
              (List.mem_cons_of_mem _ (List.mem_append_right _ hcL)))
          · exact hYs.avoid y hy (List.mem_append_right _ hcXs)
        have hIH := ihpoly Xs hXsL (a, .poly σ) hab σ rfl Ys hYsOld
        simp only [RecSpecs.rhsCtx] at hIH
        rw [Expr.substTyFvar_openTyVars h_U_lc hZYs,
            ← PolyTy.substFvar_openVars h_U_lc hZYs,
            Env.substFvar_append, ← henv_rhs] at hIH
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
  | _, _, _, .letRec _ _ _ _ hbody => TypeOfHM.regular hbody

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
  | letRec hwf hmono hpoly heq hbody ihmono ihpoly ihbody =>
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
      · have hc := ihmono Xs ⟨hXlen, hXnodup, hXavoid⟩ (bnd, .mono τ) hs τ rfl
        simp only [RecSpecs.rhsCtx, List.length_append, List.length_map] at hc
        rwa [Nat.add_comm, ← hspecslen] at hc
      · obtain ⟨Ys, hYlen, hYnodup, hYavoid⟩ := exists_fresh_names (L ++ Xs) σ.paramCount
        have hc := ihpoly Xs ⟨hXlen, hXnodup, hXavoid⟩ (bnd, .poly σ) hs σ rfl Ys
          ⟨hYlen, hYnodup, hYavoid⟩
        simp only [RecSpecs.rhsCtx, List.length_append, List.length_map] at hc
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

/-! ### Source-side rebuild of the fused `letRec` rule at the shared pool.

The declarative `TypeOfHM.letRec` rule states its cofinite mixed premises at
the shared opening `G ↦ Xs`. Ordinary members use their shared opened monotypes;
annotated members retain their complete schemes in the recursive environment.

Inference delivers the group's mixed premises at the empty pool. The gap is
exactly the renaming substitution
`G.zip (Xs.map Ty.fvar)` — which is what `Ty.renameG` unfolds to — so
`TypeOfHM.onSubst_fixed` transports the empty-pool premises to the pool-`G`
ones, provided `G` is disjoint from everything the renaming must not disturb:
the ambient env, the annotated members' declared schemes, and the bindings'
own annotation free variables. Those three are precisely the `genGroupVars`
side conditions `Infer`'s `letRec` scaffolding already establishes. -/

/-- Rebuild the mixed source rule at pool `G` from empty-pool checks.
    `hG_env`, `hG_specs`, and `hG_bs` ensure the renaming moves only the shared
    monotypes: the ambient environment, annotated schemes, and scoped source
    annotations keep their meaning. -/
theorem TypeOfHM.letRec_of_emptyPool {ctx : Ctx} {Lp G : List Nat}
    {anns : List (Option PolyTy)} {bs : List Expr} {specs : List RecSpec}
    {body : Expr} {ρ : Ty}
    (hwf : RecSpecs.WF anns bs specs G)
    (hG_env : ∀ g ∈ G, g ∉ ctx.env.freeVars)
    (hG_specs : ∀ g ∈ G, ∀ σ, RecSpec.poly σ ∈ specs → g ∉ σ.body.freeVars)
    (hG_bs : ∀ g ∈ G, ∀ e ∈ bs, g ∉ e.tyFreeVars)
    (hmono : ∀ p ∈ bs.zip specs, ∀ τ, p.2 = RecSpec.mono τ →
      TypeOfHM ⟨specs.map (RecSpec.rhsEntry [] []) ++ ctx.env, ctx.ctors⟩ p.1 τ)
    (hpoly : ∀ p ∈ bs.zip specs, ∀ σ, p.2 = RecSpec.poly σ →
      ∀ Ys, FreshNames Lp σ.paramCount Ys →
        TypeOfHM ⟨specs.map (RecSpec.rhsEntry [] []) ++ ctx.env, ctx.ctors⟩
          (p.1.openTyVars Ys) (σ.openVars Ys))
    (hbody : TypeOfHM (RecSpecs.bodyCtx ctx specs G) body ρ) :
    TypeOfHM ctx (Expr.letRec anns bs body) ρ := by
  have hctx_eq : ∀ Xs : List Nat,
      Subst.onCtx (G.zip (Xs.map (Ty.fvar ·)))
          ⟨specs.map (RecSpec.rhsEntry [] []) ++ ctx.env, ctx.ctors⟩
        = RecSpecs.rhsCtx ctx specs G Xs := by
    intro Xs
    simp only [Subst.onCtx, Subst.onEnv, RecSpecs.rhsCtx, List.map_append]
    congr 1
    congr 1
    · rw [List.map_map]
      apply List.map_congr_left
      intro s hs
      cases s with
      | mono τ =>
        simp only [Function.comp_apply, RecSpec.rhsEntry]
        rw [Ty.renameG_nil_pool]
        rfl
      | poly σ =>
        have hfix : Subst.onTy (G.zip (Xs.map (Ty.fvar ·))) σ.body = σ.body :=
          Ty.substFvars_eq_self_of_no_key (fun p hp hc =>
            hG_specs p.1 (List.of_mem_zip hp).1 σ hs hc)
        simp only [Function.comp_apply, RecSpec.rhsEntry]
        rw [Subst.onPolyTy, hfix]
    · simpa only [Subst.onEnv] using
        Subst.onEnv_eq_self_of_fresh (fun p hp => hG_env p.1 (List.of_mem_zip hp).1)
  refine TypeOfHM.letRec (specs := specs) (G := G) (L := Lp ++ G)
    hwf ?mono ?poly rfl hbody
  · intro Xs hXs p hp τ hτ
    have hctx := hctx_eq Xs
    have hsrc := hmono p hp τ hτ
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
  · intro Xs hXs p hp σ hσ Ys hYs
    have hctx := hctx_eq Xs
    have hYs' : FreshNames Lp σ.paramCount Ys := by
      refine ⟨hYs.length, hYs.nodup, ?_⟩
      intro y hy hc
      exact hYs.avoid y hy (List.mem_append_left Xs (List.mem_append_left G hc))
    have hG_Ys : ∀ g ∈ G, g ∉ Ys := by
      intro g hg hc
      exact hYs.avoid g hc (List.mem_append_left Xs (List.mem_append_right Lp hg))
    have hsrc := hpoly p hp σ hσ Ys hYs'
    have hLC : ∀ q ∈ G.zip (Xs.map (Ty.fvar ·)), q.2.IsLC := by
      intro q hq
      obtain ⟨x, hx, hxeq⟩ := List.mem_map.mp (List.of_mem_zip hq).2
      rw [← hxeq]; exact ContainsBvarsUpTo.fvar
    have hfix : (p.1.openTyVars Ys).substTyFvars (G.zip (Xs.map (Ty.fvar ·))) = p.1.openTyVars Ys :=
      Expr.substTyFvars_eq_self_of_not_mem_tyFreeVars (fun q hq hc => by
        rcases Expr.tyFreeVars_openTyVars hc with h | h
        · exact hG_bs q.1 (List.of_mem_zip hq).1 p.1 (List.of_mem_zip hp).1 h
        · exact hG_Ys q.1 (List.of_mem_zip hq).1 h)
    have htyfix : Subst.onTy (G.zip (Xs.map (Ty.fvar ·))) (σ.openVars Ys) = σ.openVars Ys := by
      simp only [Subst.onTy]
      exact Ty.substFvars_eq_self_of_no_key (fun q hq hc => by
        rcases Ty.freeVars_openVars_subset q.1 hc with h | h
        · exact hG_specs q.1 (List.of_mem_zip hq).1 σ (by simpa [hσ] using (List.of_mem_zip hp).2) h
        · exact hG_Ys q.1 (List.of_mem_zip hq).1 h)
    have hren := TypeOfHM.onSubst_fixed (G.zip (Xs.map (Ty.fvar ·))) hLC hfix hsrc
    rw [hctx, htyfix] at hren
    exact hren

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
    | letRec hwf hmono hpoly heq hbody ihmono ihpoly ihbody =>
      intro ep hep
      subst heq
      expose_names
      refine TypeOfHM.letRec (specs := specs) (G := G) (L := L) hwf ?_ ?_ rfl ?_
      · intro Xs hfresh p hp τ' hτ'
        have hc := ihmono Xs hfresh p hp τ' hτ'
          (specs.map (RecSpec.rhsEntry G Xs) ++ ep)
          (by simp only [RecSpecs.rhsCtx, hep, List.append_assoc])
        simp only [RecSpecs.rhsCtx, List.append_assoc] at hc ⊢
        exact hc
      · intro Xs hfresh p hp σ' hσ' Ys hYs
        have hc := ihpoly Xs hfresh p hp σ' hσ' Ys hYs
          (specs.map (RecSpec.rhsEntry G Xs) ++ ep)
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
  | letRec hwf hmono hpoly heq hbody ihmono ihpoly ihbody =>
    intro env_pre' hctx
    subst heq
    expose_names
    simp only [Expr.shiftFrom, RecGroup.shiftFrom_eq_map]
    refine TypeOfHM.letRec (specs := specs) (G := G) (L := L)
      ⟨hwf.anns_eq, ?_, hwf.nodup, hwf.mono_lc, hwf.poly_wf⟩ ?_ ?_ rfl ?_
    · rw [List.length_map]; exact hwf.length
    · intro Xs hfresh p hp τ hτ
      obtain ⟨a, b, _, hq, rfl⟩ := List.mem_zip_map_left hp
      have hc := ihmono Xs hfresh (a, b) hq τ hτ
        (specs.map (RecSpec.rhsEntry G Xs) ++ env_pre')
        (by simp only [RecSpecs.rhsCtx]; rw [hctx, List.append_assoc])
      simp only [RecSpecs.rhsCtx, List.length_append, List.length_map] at hc
      rw [← hwf.length, Nat.add_comm bindings.length env_pre'.length] at hc
      simp only [RecSpecs.rhsCtx, List.append_assoc] at hc ⊢
      exact hc
    · intro Xs hfresh p hp σ hσ Ys hYs
      obtain ⟨a, b, _, hq, rfl⟩ := List.mem_zip_map_left hp
      have hc := ihpoly Xs hfresh (a, b) hq σ hσ Ys hYs
        (specs.map (RecSpec.rhsEntry G Xs) ++ env_pre')
        (by simp only [RecSpecs.rhsCtx]; rw [hctx, List.append_assoc])
      rw [Expr.shiftFrom_openTyVars] at hc
      simp only [RecSpecs.rhsCtx, List.length_append, List.length_map] at hc
      rw [← hwf.length, Nat.add_comm bindings.length env_pre'.length] at hc
      simp only [RecSpecs.rhsCtx, List.append_assoc] at hc ⊢
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

/-! ### Source and runtime coherence with declarative `TypeOfHM`

Inference has two soundness views. `Infer.sourceSound` retains source
annotations; `Infer.sound` types the runnable, fully erased term (`e.erase`).
The `K`-list
escape conditions keep source annotation variables rigid while inference
threads substitutions. These proofs sit after the `TypeOfHM` substitution and
weakening infrastructure on which they depend. -/

set_option maxRecDepth 10_000 in
set_option maxHeartbeats 800_000 in
mutual
/-- Backward soundness: inference implies declarative typing for the source term. -/
theorem Infer.sourceSound {Φ ctx e Φ' S τ} (h : Infer Φ ctx e Φ' S τ) :
    CtxWF ctx → CtxBelow Φ ctx → (K : List Nat) → (∀ k ∈ K, k < Φ) →
    (∀ y ∈ e.tyFreeVars, y ∈ K) → (∀ p ∈ S, p.1 ∉ K) →
    TypeOfHM (S.onCtx ctx) e τ := by
  cases h with
  | primLitUnit =>
    intro _ _ _ _ _ _
    simp only [Subst.onCtx_nil]
    exact .primLitUnit
  | primLitInt =>
    intro _ _ _ _ _ _
    simp only [Subst.onCtx_nil]
    exact .primLitInt
  | primLitNat =>
    intro _ _ _ _ _ _
    simp only [Subst.onCtx_nil]
    exact .primLitNat
  | primLitChar =>
    intro _ _ _ _ _ _
    simp only [Subst.onCtx_nil]
    exact .primLitChar
  | primBinOpIntAdd =>
    intro _ _ _ _ _ _
    simp only [Subst.onCtx_nil]
    exact .primBinOpIntAdd
  | primBinOpIntSub =>
    intro _ _ _ _ _ _
    simp only [Subst.onCtx_nil]
    exact .primBinOpIntSub
  | primBinOpIntLt hlookT hbT hlookF hbF =>
    intro _ _ _ _ _ _
    simp only [Subst.onCtx_nil]
    exact .primBinOpIntLt (Ctor.IsBoolCtor.typeOfHM hlookT hbT)
      (Ctor.IsBoolCtor.typeOfHM hlookF hbF)
  | primBinOpCharLt hlookT hbT hlookF hbF =>
    intro _ _ _ _ _ _
    simp only [Subst.onCtx_nil]
    exact .primBinOpCharLt (Ctor.IsBoolCtor.typeOfHM hlookT hbT)
      (Ctor.IsBoolCtor.typeOfHM hlookF hbF)
  | lambda hseed hbody =>
    intro hctx hbelow K hKΦ hKe hSK
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
      have ih := Infer.sourceSound hbody hbodyWF hbodyBelow K
        (fun k hk => by have := hKΦ k hk; omega) hKe hSK
      refine TypeOfHM.lambda
        ((Subst.onTy_lc (Infer.lc hbody hbodyWF).2 ContainsBvarsUpTo.fvar))
        (fun T hT => by cases hT) rfl ?_
      simpa only [Subst.onCtx, Subst.onEnv, List.map_cons]
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
      have ih := Infer.sourceSound hbody hbodyWF hbodyBelow K
        (fun k hk => by have := hKΦ k hk; omega)
        (fun y hy => hKe y (.inr hy)) hSK
      have hSparam : S.onTy paramTy = paramTy :=
        Ty.substFvars_eq_self_of_no_key (fun p hp hc => hSK p hp (hKe p.1 (.inl hc)))
      refine TypeOfHM.lambda
        ((Subst.onTy_lc (Infer.lc hbody hbodyWF).2 hcl))
        (fun T hT => by
          simp only [Option.some.injEq] at hT
          -- hT : erase paramTy = T; goal: erase (S.onTy paramTy) = T
          rwa [hSparam]) rfl ?_
      simpa only [Subst.onCtx, Subst.onEnv, List.map_cons]
        using ih
  | app hf harg huni =>
    intro hctx hbelow K hKΦ hKe hSK
    expose_names
    simp only [Expr.tyFreeVars, List.mem_append] at hKe
    obtain ⟨hf_lc, hf_s⟩ := Infer.lc hf hctx
    have hctx1 := Subst.onCtx_wf hf_s hctx
    obtain ⟨harg_lc, harg_s⟩ := Infer.lc harg hctx1
    have hf_below := Infer.belowFvars hf hbelow (fun y hy => hKΦ y (hKe y (.inl hy)))
    have hbelow1 := Subst.onCtx_below hf_below.2 (Infer.frontier_le hf) hbelow
    have hs3 := huni.lc (Subst.onTy_lc harg_s hf_lc) (.arrow harg_lc ContainsBvarsUpTo.fvar)
    have hf_sound := Infer.sourceSound hf hctx hbelow K hKΦ (fun y hy => hKe y (.inl hy))
      (fun p hp => hSK p (List.mem_append_left _ (List.mem_append_left _ hp)))
    have harg_sound := Infer.sourceSound harg hctx1 hbelow1 K
      (fun k hk => lt_of_lt_of_le (hKΦ k hk) (Infer.frontier_le hf))
      (fun y hy => hKe y (.inr hy))
      (fun p hp => hSK p (List.mem_append_left _ (List.mem_append_right _ hp)))
    have hffix23 : f.substTyFvars (S₂ ++ S₃) = f :=
      Expr.substTyFvars_eq_self_of_not_mem_tyFreeVars (fun p hp hc =>
        (List.mem_append.mp hp).elim
          (fun h => hSK p (List.mem_append_left _ (List.mem_append_right _ h)) (hKe p.1 (.inl hc)))
          (fun h => hSK p (List.mem_append_right _ h) (hKe p.1 (.inl hc))))
    have hffix2 : f.substTyFvars S₂ = f :=
      Expr.substTyFvars_eq_self_of_not_mem_tyFreeVars (fun p hp hc =>
        hSK p (List.mem_append_left _ (List.mem_append_right _ hp)) (hKe p.1 (.inl hc)))
    have hffix3 : f.substTyFvars S₃ = f :=
      Expr.substTyFvars_eq_self_of_not_mem_tyFreeVars (fun p hp hc =>
        hSK p (List.mem_append_right _ hp) (hKe p.1 (.inl hc)))
    have hargfix3 : arg.substTyFvars S₃ = arg :=
      Expr.substTyFvars_eq_self_of_not_mem_tyFreeVars (fun p hp hc =>
        hSK p (List.mem_append_right _ hp) (hKe p.1 (.inr hc)))
    have hf2 := TypeOfHM.onSubst_fixed_append S₁ S₂ hf_s harg_s
      (Expr.substTyFvars_eq_self_of_not_mem_tyFreeVars (fun p hp hc =>
        hSK p (List.mem_append_left _ (List.mem_append_left _ hp)) (hKe p.1 (.inl hc))))
      hffix2 hf_sound
    have hf3 := TypeOfHM.onSubst_fixed (ctx := (S₁ ++ S₂).onCtx ctx)
      (e := f) (τ := S₂.onTy τf) S₃ hs3 hffix3
      (by simpa only [Subst.onCtx_append] using hf2)
    have hueq : (S₃.onTy (S₂.onTy τf)) =
        (S₃.onTy (.arrow τa (.fvar Φ₂))) := huni.unifies
    have hf_arr : TypeOfHM ((S₁ ++ S₂ ++ S₃).onCtx ctx) f
        (.arrow ((S₃.onTy τa)) ((S₃.onTy (.fvar Φ₂)))) := by
      have key := hf3
      rw [hueq, Subst.onTy_arrow] at key
      have hctx_eq : (S₃.onCtx ((S₁ ++ S₂).onCtx ctx)) =
          ((S₁ ++ S₂ ++ S₃).onCtx ctx) := by
        rw [← Subst.onCtx_append]
      rwa [hctx_eq] at key
    have harg3 := TypeOfHM.onSubst_fixed (ctx := S₂.onCtx (S₁.onCtx ctx))
      (e := arg) (τ := τa) S₃ hs3 hargfix3 harg_sound
    have harg_arr : TypeOfHM ((S₁ ++ S₂ ++ S₃).onCtx ctx) arg
        ((S₃.onTy τa)) := by
      have hctx_eq : (S₃.onCtx (S₂.onCtx (S₁.onCtx ctx))) =
          ((S₁ ++ S₂ ++ S₃).onCtx ctx) := by
        simp only [← Subst.onCtx_append, List.append_assoc]
      rwa [hctx_eq] at harg3
    exact TypeOfHM.app hf_arr harg_arr
  | @var Φ ctx i polyTy hlook =>
    intro hctx _ _ _ _ _
    simp only [Subst.onCtx_nil]
    refine TypeOfHM.var (polyTy := polyTy)
      (instArgs := (freshVars Φ polyTy.paramCount).map Ty.fvar) hlook ?_ ?_
    · intro tyArg ht
      obtain ⟨n, _, rfl⟩ := List.mem_map.mp ht
      exact ContainsBvarsUpTo.fvar
    · exact InstantiatesBy.openVars
        (hctx _ (List.mem_of_getElem? hlook)) (by simp [freshVars_length])
  | @ctor Φ ctx name ctor hlook =>
    intro _ _ _ _ _ _
    simp only [Subst.onCtx_nil]
    refine TypeOfHM.ctor (ctor := ctor)
      (tyArgs := (freshVars Φ ctor.paramCount).map Ty.fvar) hlook ?_ ?_
    · intro tyArg ht
      obtain ⟨x, _, rfl⟩ := List.mem_map.mp ht
      exact ContainsBvarsUpTo.fvar
    · exact InstantiatesBy.openVars (Ctor.toTy_wf ctor)
        (by simp [Ctor.toTy, freshVars_length])
  | letIn hrhs hbody =>
    intro hctx hbelow K hKΦ hKe hSK
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
    have hS₁S₂lc : ∀ p ∈ S₁ ++ S₂, p.2.IsLC :=
      fun p hp => (List.mem_append.mp hp).elim (fun h => hrhs_s p h) (fun h => hbody_s p h)
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
      exact (Infer.range_avoid hrhs (w := g) hlt hg_ctxenv hg_rigid).2 (hgenV_τ₁ g hg)
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
      exact (Infer.range_avoid hbody (w := u) (hgenV_lt u hc) (hbodyCtxAvoid u hc)
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
    have hrhs_sound := Infer.sourceSound hrhs hctx hbelow K hKΦ (fun y hy => hKe y (.inl hy))
      (fun p hp => hSK p (List.mem_append_left S₂ hp))
    have hrhsfixS2 : rhs.substTyFvars S₂ = rhs :=
      Expr.substTyFvars_eq_self_of_not_mem_tyFreeVars
        (fun p hp hc => hSK p (List.mem_append_right _ hp) (hKe p.1 (.inl hc)))
    have hr2 := TypeOfHM.onSubst_fixed (ctx := S₁.onCtx ctx) (e := rhs) (τ := τ₁)
      S₂ hbody_s hrhsfixS2 hrhs_sound
    have hbase : TypeOfHM ((S₁ ++ S₂).onCtx ctx) rhs
        (((S₁ ++ S₂).onTy τ₁)) := by
      have key := hr2
      rw [← Subst.onCtx_append, ← hSτ₁] at key
      exact key
    have hbody_sound := Infer.sourceSound hbody hbodyWF hbodyBelow K
      (fun k hk => lt_of_lt_of_le (hKΦ k hk) (Infer.frontier_le hrhs))
      (fun y hy => hKe y (.inr hy)) (fun p hp => hSK p (List.mem_append_right _ hp))
    have hbody_pack : TypeOfHM
        { ((S₁ ++ S₂).onCtx ctx) with
          env := ⟨genV.length, Ty.closeOver genV ((S₁ ++ S₂).onTy τ₁)⟩
            :: ((S₁ ++ S₂).onCtx ctx).env }
        body τ := by
      have key := hbody_sound
      have hctx_eq :
          (S₂.onCtx { (S₁.onCtx ctx) with
              env := genScheme rhs.tyFreeVars (S₁.onCtx ctx).env τ₁ :: (S₁.onCtx ctx).env
            })
          = { ((S₁ ++ S₂).onCtx ctx) with
              env := S₂.onPolyTy (genScheme rhs.tyFreeVars (S₁.onCtx ctx).env τ₁)
                :: ((S₁ ++ S₂).onCtx ctx).env } := by
        rw [heqbodyctx]
      rw [hctx_eq, hschemeeq] at key
      exact key
    -- residual source letIn none: Pins vacuous; cofinite via rename of genV
    set Mres : PolyTy :=
      ⟨genV.length, Ty.closeOver genV ((S₁ ++ S₂).onTy τ₁)⟩ with hMres
    have hMres_eq : Mres = ⟨genV.length, Ty.closeOver genV (((S₁ ++ S₂).onTy τ₁))⟩ := by
      rfl
    refine TypeOfHM.letIn (M := Mres) (L := genV)
      (by
        exact Ty.closeOver_preserves_bvars (vars := genV)
          (Subst.onTy_lc hS₁S₂lc hrhs_lc))
      (fun σ' h => by cases h) ?_ rfl ?_
    · intro Xs hXfresh
      -- openBoundTyVars none = id; type is Mres.openVars Xs
      simp only [Expr.openBoundTyVars]
      have htype : Mres.openVars Xs =
          Ty.substFvars (genV.zip (Xs.map (Ty.fvar ·)))
            (((S₁ ++ S₂).onTy τ₁)) := by
        rw [hMres_eq]
        simp only [PolyTy.openVars]
        exact Ty.openVars_closeOver_rename
          ((Subst.onTy_lc hS₁S₂lc hrhs_lc))
          (by simp only [genV]; exact genVars_nodup) hXfresh.length
          (fun g hg hgX => hXfresh.avoid g hgX hg)
      rw [htype]
      have hfixE : (rhs).substTyFvars (genV.zip (Xs.map (Ty.fvar ·))) =
          rhs :=
        Expr.substTyFvars_eq_self_of_not_mem_tyFreeVars (fun p hp hc => by
          -- genV excludes rigid = rhs.tyFreeVars; erase preserves tyFreeVars membership
          have hrigid : p.1 ∉ rhs.tyFreeVars := by
            simp only [genV] at hp
            exact genVars_not_mem_rigid (List.of_mem_zip hp).1
          exact hrigid hc)
      have hren := TypeOfHM.onSubst_fixed (genV.zip (Xs.map (Ty.fvar ·)))
        (fun p hp => by
          obtain ⟨_, hp2⟩ := List.of_mem_zip hp
          obtain ⟨x, _, hxeq⟩ := List.mem_map.mp hp2
          rw [← hxeq]; exact ContainsBvarsUpTo.fvar)
        hfixE hbase
      have hctxfix : Subst.onCtx (genV.zip (Xs.map (Ty.fvar ·)))
          ((S₁ ++ S₂).onCtx ctx) =
          ((S₁ ++ S₂).onCtx ctx) := by
        conv_lhs => rw [Subst.onCtx]
        refine congrArg (fun E => (⟨E, ((S₁ ++ S₂).onCtx ctx).ctors⟩ : Ctx)) ?_
        exact Subst.onEnv_eq_self_of_fresh (fun p hp hc =>
          hgenV_env' p.1 (List.of_mem_zip hp).1 hc)
      rwa [hctxfix] at hren
    · simpa only [Mres, hschemeeq] using hbody_pack
  | letInAnn hσwf hΦN hrhs huni hesc1 hesc2 hbody =>
    intro hctx hbelow K hKΦ hKe hSK
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
      exact (Infer.range_avoid hbody (w := u) (hYs_lt u hc) (hYs_bodyCtx u hc)
        (hYs_body u hc)).1 p hp hu
    have hSYs : ∀ p ∈ S₁ ++ Schk ++ S₂, p.1 ∉ Ys := by
      intro p hp
      rcases List.mem_append.mp hp with hp | hp
      · exact fun hc => by
          simp only [Ys] at hc
          exact hesc1 p.1 hc (List.mem_map.mpr ⟨p, hp, rfl⟩)
      · exact hS₂Ys p hp
    have hSσbody : (S₁ ++ Schk ++ S₂).onTy σ.body = σ.body :=
      Ty.substFvars_eq_self_of_no_key
        (fun p hp hc => hSK p hp (hKe p.1 (.inl (.inl hc))))
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
    have hrhsfix : (rhs.openTyVars Ys).substTyFvars (Schk ++ S₂) = rhs.openTyVars Ys := by
      refine Expr.substTyFvars_eq_self_of_not_mem_tyFreeVars (fun p hp hc => ?_)
      have hpS : p ∈ S₁ ++ Schk ++ S₂ := by
        rcases List.mem_append.mp hp with h | h
        · exact List.mem_append_left _ (List.mem_append_right _ h)
        · exact List.mem_append_right _ h
      rcases Expr.tyFreeVars_openTyVars hc with h | h
      · exact hSK p hpS (hKe p.1 (.inl (.inr h)))
      · exact hSYs p hpS h
    have hrhs_sound := Infer.sourceSound hrhs hctx hctx_pc (K ++ Ys)
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
    have hr1 := TypeOfHM.onSubst_fixed (ctx := S₁.onCtx ctx)
      (e := rhs.openTyVars Ys) (τ := τ₁) Schk hSchk_lc
      (Expr.substTyFvars_eq_self_of_not_mem_tyFreeVars (fun p hp hc => by
        rcases Expr.tyFreeVars_openTyVars hc with h | h
        · exact hSK p (List.mem_append_left S₂ (List.mem_append_right S₁ hp))
            (hKe p.1 (.inl (.inr h)))
        · simp only [Ys] at h
          exact hesc1 p.1 h (List.mem_map.mpr ⟨p, List.mem_append_right _ hp, rfl⟩)))
      hrhs_sound
    have hu : (Schk.onTy τ₁) = (Schk.onTy (σ.openVars Ys)) :=
      huni.unifies
    have hr1' : TypeOfHM ((S₁ ++ Schk).onCtx ctx)
        ((rhs.openTyVars Ys)) ((σ.openVars Ys)) := by
      have key := hr1
      rwa [← Subst.onCtx_append, hu, hSchk_fix] at key
    have hr2 := TypeOfHM.onSubst_fixed (ctx := (S₁ ++ Schk).onCtx ctx)
      (e := rhs.openTyVars Ys) (τ := σ.openVars Ys) S₂ hbody_s
      (by
        have hSchk_rhs : (rhs.openTyVars Ys).substTyFvars Schk = rhs.openTyVars Ys :=
          Expr.substTyFvars_eq_self_of_not_mem_tyFreeVars (fun p hp hc => by
            rcases Expr.tyFreeVars_openTyVars hc with h | h
            · exact hSK p (List.mem_append_left S₂ (List.mem_append_right S₁ hp))
                (hKe p.1 (.inl (.inr h)))
            · simp only [Ys] at h
              exact hesc1 p.1 h (List.mem_map.mpr ⟨p, List.mem_append_right _ hp, rfl⟩))
        rw [Expr.substTyFvars_append, hSchk_rhs] at hrhsfix
        exact hrhsfix) hr1'
    have hr2' : TypeOfHM ((S₁ ++ Schk ++ S₂).onCtx ctx)
        ((rhs.openTyVars Ys)) ((σ.openVars Ys)) := by
      have key := hr2
      rw [hS₂fix] at key
      convert key using 1
      rw [← Subst.onCtx_append]
    have hYs_env : ∀ y ∈ Ys, y ∉ ((S₁ ++ Schk ++ S₂).onCtx ctx).env.freeVars := by
      intro y hy hc
      rw [show (S₁ ++ Schk ++ S₂).onCtx ctx = S₂.onCtx ((S₁ ++ Schk).onCtx ctx) from by
            rw [show (S₁ ++ Schk ++ S₂) = (S₁ ++ Schk) ++ S₂ from rfl, Subst.onCtx_append],
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
    have hbody_sound := Infer.sourceSound hbody hbodyWF hbodyBelow K
      (fun k hk => by have := hKΦ k hk; have := hΦN; have := hrle; omega)
      (fun y hy => hKe y (.inr hy)) (fun p hp => hSK p (List.mem_append_right _ hp))
    have hbody_pack : TypeOfHM
        { ((S₁ ++ Schk ++ S₂).onCtx ctx) with
          env := σ
            :: ((S₁ ++ Schk ++ S₂).onCtx ctx).env }
        body τ := by
      have key := hbody_sound
      have hctx_eq :
          (S₂.onCtx { (Schk.onCtx (S₁.onCtx ctx)) with
              env := σ :: (Schk.onCtx (S₁.onCtx ctx)).env })
          = { ((S₁ ++ Schk ++ S₂).onCtx ctx) with
              env := σ
                :: ((S₁ ++ Schk ++ S₂).onCtx ctx).env } := by
        rw [heqbodyctx]
      rwa [hctx_eq] at key
    refine TypeOfHM.letIn (M := σ) (L := Ys)
      hσwf
      (fun σ' h => by cases h; rfl) ?_ rfl hbody_pack
    intro Xs hXfresh
    simp only [Expr.openBoundTyVars]
    have hYsX : ∀ y ∈ Ys, y ∉ Xs := fun y hy hc => hXfresh.avoid y hc hy
    have hXlen : Xs.length = Ys.length := by
      have h1 := hXfresh.length
      simp only [Ys, freshVars_length] at h1 ⊢
      exact h1
    have hraw : (rhs.openTyVars Ys).substTyFvars (Ys.zip (Xs.map (Ty.fvar ·))) =
        rhs.openTyVars Xs :=
      Expr.substTyFvars_zip_openTyVars hXlen.symm
        (by simp only [Ys]; exact freshVars_nodup)
        (fun y hy hc => by
          have := hKΦ y (hKe y (.inl (.inr hc)))
          simp only [Ys] at hy; have := freshVars_ge y hy; omega)
        hYsX
    have htermeq : ((rhs.openTyVars Ys)).substTyFvars
          (Ys.zip (Xs.map (Ty.fvar ·))) = (rhs.openTyVars Xs) := by
      exact hraw
    have htypeeq : Subst.onTy (Ys.zip (Xs.map (Ty.fvar ·)))
          ((σ.openVars Ys)) =
          (σ.openVars Xs) := by
      have h := Ty.openWith_eq_substFvars_openVars (ty := σ.body)
        (Vs := Xs.map (Ty.fvar ·)) (Xs := Ys)
        ⟨by rw [List.length_map, hXlen], fun V hV => by
          obtain ⟨x, _, rfl⟩ := List.mem_map.mp hV; exact ContainsBvarsUpTo.fvar⟩
        (by simp only [Ys]; exact freshVars_nodup) hYs_σ
        (fun y hy hc => hYsX y hy (Ty.mem_freeVarsList_map_fvar.mp hc))
      -- h : openWith Xs σ.body = substFvars (Ys.zip fvars Xs) (openVars Ys σ)
      have h' : PolyTy.openVars Xs σ =
          Ty.substFvars (Ys.zip (Xs.map (Ty.fvar ·))) (σ.openVars Ys) := by
        simp only [PolyTy.openVars]
        rw [Ty.openVars_eq_openWith]; exact h
      exact h'.symm
    have hren := TypeOfHM.onSubst (Ys.zip (Xs.map (Ty.fvar ·)))
      (fun p hp => by
        obtain ⟨_, hp2⟩ := List.of_mem_zip hp
        obtain ⟨x, _, hxeq⟩ := List.mem_map.mp hp2
        rw [← hxeq]; exact ContainsBvarsUpTo.fvar)
      hr2'
    have hctxfix : Subst.onCtx (Ys.zip (Xs.map (Ty.fvar ·)))
          ((S₁ ++ Schk ++ S₂).onCtx ctx) =
          ((S₁ ++ Schk ++ S₂).onCtx ctx) := by
      conv_lhs => rw [Subst.onCtx]
      refine congrArg (fun E =>
        (⟨E, ((S₁ ++ Schk ++ S₂).onCtx ctx).ctors⟩ : Ctx)) ?_
      exact Subst.onEnv_eq_self_of_fresh (fun p hp hc =>
        hYs_env p.1 (List.of_mem_zip hp).1 hc)
    rwa [hctxfix, htermeq, htypeeq] at hren
  | match_ hscrut hne hbr =>
    intro hctx hbelow K hKΦ hKe hSK
    expose_names
    simp only [Expr.tyFreeVars, List.mem_append] at hKe
    obtain ⟨hτs_lc, hS₁⟩ := Infer.lc hscrut hctx
    have hle1 := Infer.frontier_le hscrut
    have hscrut_below := Infer.belowFvars hscrut hbelow (fun y hy => hKΦ y (hKe y (.inl hy)))
    have hctx1 := Subst.onCtx_wf hS₁ hctx
    have hbelow1 := Subst.onCtx_below hscrut_below.2 hle1 hbelow
    have hS₂lc := (InferBranches.lc hbr hctx1 hτs_lc ContainsBvarsUpTo.fvar).2
    have hscrut_sound := Infer.sourceSound hscrut hctx hbelow K hKΦ (fun y hy => hKe y (.inl hy))
      (fun p hp => hSK p (List.mem_append_left _ hp))
    have hscrutfix : scrut.substTyFvars S₂ = scrut :=
      Expr.substTyFvars_eq_self_of_not_mem_tyFreeVars (fun p hp hc =>
        hSK p (List.mem_append_right _ hp) (hKe p.1 (.inl hc)))
    have hscrut_decl := TypeOfHM.onSubst_fixed (ctx := S₁.onCtx ctx)
      (e := scrut) (τ := τs) S₂ hS₂lc hscrutfix hscrut_sound
    have hbr_sound := InferBranches.sourceSound hbr hctx1
      (fun M hM => (hbelow1 M hM).mono (by omega))
      hτs_lc ContainsBvarsUpTo.fvar
      (hscrut_below.1.mono (by omega)) (.fvar (by omega)) K
      (fun k hk => by have := hKΦ k hk; omega)
      (fun y hy => hKe y (.inr hy)) (fun p hp => hSK p (List.mem_append_right _ hp))
    refine TypeOfHM.match_
      (by
        have hctx_eq : (S₂.onCtx (S₁.onCtx ctx)) =
            ((S₁ ++ S₂).onCtx ctx) := by rw [← Subst.onCtx_append]
        rwa [hctx_eq] at hscrut_decl)
      (by
        intro hcontra
        obtain ⟨⟨p, b⟩, rest, hb⟩ := List.exists_cons_of_ne_nil hne
        simp [hb] at hcontra) ?_
    intro br hbr_mem
    have hbrp := hbr_sound br hbr_mem
    have hctx_eq : (S₂.onCtx (S₁.onCtx ctx)) =
        ((S₁ ++ S₂).onCtx ctx) := by rw [← Subst.onCtx_append]
    rwa [← hctx_eq]
  | letRec hwfanns hgroup hspecs1 hG hbody =>
    intro hctx hbelow K hKΦ hKe hSK
    expose_names
    subst specs1
    simp only [Expr.tyFreeVars, List.mem_append] at hKe
    have hlen_ab : anns.length = bindings.length := by
      have h1 := InferRecGroup.length_eq hgroup
      rw [RecSpec.init_length] at h1
      omega
    have hinitLC : ∀ s ∈ RecSpec.init Φ anns, s.LC := by
      intro s hs
      rcases RecSpec.mem_init hs with ⟨m, _, _, rfl⟩ | ⟨σ, hσ, rfl⟩
      · exact ContainsBvarsUpTo.fvar
      · exact hwfanns σ hσ
    have hKsch : ∀ σ, some σ ∈ anns → ∀ y ∈ σ.body.freeVars, y ∈ K := fun σ hσ y hy =>
      hKe y (.inl (.inl (Expr.scheme_body_mem_annList_tyFreeVars hσ hy)))
    have hKbind : ∀ y ∈ Expr.tyFreeVars.RecGroup.tyFreeVars bindings, y ∈ K :=
      fun y hy => hKe y (.inl (.inr hy))
    have hinitB : ∀ s ∈ RecSpec.init Φ anns, s.BelowFvars (Φ + bindings.length) := by
      intro s hs
      rcases RecSpec.mem_init hs with ⟨m, hm1, hm2, rfl⟩ | ⟨σ, hσ, rfl⟩
      · refine Ty.BelowFvars.of_freeVars_lt (fun v hv => ?_)
        simp only [Ty.freeVars, List.mem_singleton] at hv
        omega
      · refine Ty.BelowFvars.of_freeVars_lt (fun v hv => ?_)
        have := hKΦ v (hKsch σ hσ v hv); omega
    have hctxgWF : CtxWF { ctx with
        env := (RecSpec.init Φ anns).map (RecSpec.rhsEntry [] []) ++ ctx.env } := by
      intro M hM
      rcases List.mem_append.mp hM with hM | hM
      · obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hM
        exact RecSpec.rhsEntry_nil_wf (hinitLC s hs)
      · exact hctx M hM
    have hctxgBelow : CtxBelow (Φ + bindings.length) { ctx with
        env := (RecSpec.init Φ anns).map (RecSpec.rhsEntry [] []) ++ ctx.env } := by
      intro M hM
      rcases List.mem_append.mp hM with hM | hM
      · obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hM
        exact RecSpec.rhsEntry_nil_belowFvars (hinitB s hs)
      · exact (hbelow M hM).mono (by omega)
    have hinitEnv : ∀ s ∈ RecSpec.init Φ anns, ∀ y ∈ s.freeVars,
        y ∈ ({ ctx with env := (RecSpec.init Φ anns).map (RecSpec.rhsEntry [] [])
                ++ ctx.env } : Ctx).env.freeVars := by
      intro s hs y hy
      refine Env.mem_freeVars_iff.mpr ⟨RecSpec.rhsEntry [] [] s,
        List.mem_append_left _ (List.mem_map.mpr ⟨s, hs, rfl⟩), ?_⟩
      rw [RecSpec.rhsEntry_nil_body_freeVars]
      exact hy
    have hgrle := InferRecGroup.frontier_le hgroup
    have hS₁K : ∀ p ∈ S₁, p.1 ∉ K := fun p hp => hSK p (List.mem_append_left _ hp)
    have hS₂K : ∀ p ∈ S₂, p.1 ∉ K := fun p hp => hSK p (List.mem_append_right _ hp)
    have hS₁lc : ∀ p ∈ S₁, p.2.IsLC := InferRecGroup.lc hgroup hctxgWF hinitLC
    have htfv_below : ∀ y ∈ Expr.tyFreeVars.RecGroup.tyFreeVars bindings,
        y < Φ + bindings.length := fun y hy => by have := hKΦ y (hKbind y hy); omega
    have hS₁below : ∀ p ∈ S₁, Ty.BelowFvars Φ₁ p.2 :=
      InferRecGroup.belowFvars hgroup hctxgBelow hinitB htfv_below
    have hS₁dom_below : ∀ p ∈ S₁, p.1 < Φ₁ :=
      InferRecGroup.dom_below hgroup hctxgBelow hinitB htfv_below
    have helimG : ∀ p ∈ S₁, ∀ x : Ty, p.1 ∉ (S₁.onTy x).freeVars :=
      InferRecGroup.eliminates hgroup hctxgBelow hinitB htfv_below
        (fun p hp hc => hS₁K p hp (hKbind p.1 hc))
        (fun p hp σ hσs hc => hS₁K p hp (hKsch σ (RecSpec.poly_mem_init hσs) p.1 hc))
    -- fused group soundness (at the group context)
    obtain ⟨hmonoS, L₀, hpolyS⟩ := InferRecGroup.sourceSound hgroup hctxgWF hctxgBelow
      hinitLC hinitB hinitEnv K (fun k hk => by have := hKΦ k hk; omega)
      hKbind (fun σ hσs => hKsch σ (RecSpec.poly_mem_init hσs)) hS₁K
    -- scheme rigidity under S₁ and the group-ctx bridge
    have hσfixS₁ : ∀ σ0, some σ0 ∈ anns → Subst.onPolyTy S₁ σ0 = σ0 := by
      intro σ0 hσ0
      simp only [Subst.onPolyTy]
      rw [show Subst.onTy S₁ σ0.body = σ0.body from
        Ty.substFvars_eq_self_of_no_key (fun p hp hc => hS₁K p hp (hKsch σ0 hσ0 p.1 hc))]
    have hentryS₁ : ∀ s ∈ RecSpec.init Φ anns,
        Subst.onPolyTy S₁ (RecSpec.rhsEntry [] [] s)
          = RecSpec.rhsEntry [] [] (RecSpec.onSubst S₁ s) := by
      intro s hs
      cases s with
      | mono τ0 => rfl
      | poly σ0 => exact hσfixS₁ σ0 (RecSpec.poly_mem_init hs)
    have hbridge1 : S₁.onCtx { ctx with
          env := (RecSpec.init Φ anns).map (RecSpec.rhsEntry [] []) ++ ctx.env }
        = { (S₁.onCtx ctx) with
            env := ((RecSpec.init Φ anns).map (RecSpec.onSubst S₁)).map (RecSpec.rhsEntry [] [])
              ++ (S₁.onCtx ctx).env } := by
      show (⟨Subst.onEnv S₁ ((RecSpec.init Φ anns).map (RecSpec.rhsEntry [] []) ++ ctx.env),
          ctx.ctors⟩ : Ctx) = _
      rw [Subst.onEnv, List.map_append]
      refine congrArg (fun E => (⟨E ++ (S₁.onCtx ctx).env, ctx.ctors⟩ : Ctx)) ?_
      rw [List.map_map, List.map_map]
      exact List.map_congr_left (fun s hs => hentryS₁ s hs)
    rw [hbridge1] at hmonoS hpolyS
    -- the shared gen-pool `G` and the solved specs' facts
    have hsolvedLC : ∀ s ∈ (RecSpec.init Φ anns).map (RecSpec.onSubst S₁), s.LC := by
      intro s' hs'
      obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hs'
      exact RecSpec.LC.onSubst hS₁lc (hinitLC s hs)
    have hpoly_mem_anns : ∀ σ0, RecSpec.poly σ0 ∈ (RecSpec.init Φ anns).map (RecSpec.onSubst S₁) →
        some σ0 ∈ anns :=
      fun σ0 hσ0 => RecSpec.poly_mem_init (RecSpec.poly_mem_map_onSubst.mp hσ0)
    have hmonoTys_mem : ∀ τ ∈ RecSpecs.monoTys ((RecSpec.init Φ anns).map (RecSpec.onSubst S₁)),
        RecSpec.mono τ ∈ (RecSpec.init Φ anns).map (RecSpec.onSubst S₁) := by
      intro τ hτ
      simp only [RecSpecs.monoTys, List.mem_filterMap] at hτ
      obtain ⟨s', hs', hmt⟩ := hτ
      cases s' with
      | mono τ0 =>
        simp only [RecSpec.monoTy?, Option.some.injEq] at hmt
        exact hmt ▸ hs'
      | poly σ0 => exact absurd hmt (by simp [RecSpec.monoTy?])
    have hmono_shape : ∀ τ, RecSpec.mono τ ∈ (RecSpec.init Φ anns).map (RecSpec.onSubst S₁) →
        ∃ m, Φ ≤ m ∧ m < Φ + anns.length ∧ τ = S₁.onTy (Ty.fvar m) := by
      intro τ hτ
      obtain ⟨s, hs, hseq⟩ := List.mem_map.mp hτ
      cases s with
      | mono τ0 =>
        rcases RecSpec.mem_init hs with ⟨m, h1, h2, heq⟩ | ⟨σ0, _, heq⟩
        · cases heq
          injection hseq with hseq'
          exact ⟨m, h1, h2, hseq'.symm⟩
        · exact absurd heq (by simp)
      | poly σ0 => exact absurd hseq (by simp [RecSpec.onSubst])
    have hτs_below : ∀ τ ∈ RecSpecs.monoTys ((RecSpec.init Φ anns).map (RecSpec.onSubst S₁)),
        Ty.BelowFvars Φ₁ τ := by
      intro τ hτ
      obtain ⟨m, hm1, hm2, rfl⟩ := hmono_shape τ (hmonoTys_mem τ hτ)
      refine Ty.BelowFvars.of_freeVars_lt (fun v hv => ?_)
      rcases Subst.mem_freeVars_onTy hv with h | ⟨p, hp, hvp⟩
      · simp only [Ty.freeVars, List.mem_singleton] at h
        omega
      · exact (hS₁below p hp).mem_lt v hvp
    -- body context WF/Below
    have hbodyWF : CtxWF { (S₁.onCtx ctx) with
        env := ((RecSpec.init Φ anns).map (RecSpec.onSubst S₁)).map (RecSpec.bodyScheme G)
          ++ (S₁.onCtx ctx).env } := by
      intro M hM
      rcases List.mem_append.mp hM with hM | hM
      · obtain ⟨s', hs', rfl⟩ := List.mem_map.mp hM
        exact RecSpec.bodyScheme_wf (hsolvedLC s' hs')
      · exact (Subst.onCtx_wf hS₁lc hctx) M hM
    have hbodyBelow : CtxBelow Φ₁ { (S₁.onCtx ctx) with
        env := ((RecSpec.init Φ anns).map (RecSpec.onSubst S₁)).map (RecSpec.bodyScheme G)
          ++ (S₁.onCtx ctx).env } := by
      intro M hM
      rcases List.mem_append.mp hM with hM | hM
      · obtain ⟨s', hs', rfl⟩ := List.mem_map.mp hM
        cases s' with
        | mono τ =>
          have hb : Ty.BelowFvars Φ₁ τ := by
            obtain ⟨m, _, hm2, rfl⟩ := hmono_shape τ hs'
            refine Ty.BelowFvars.of_freeVars_lt (fun v hv => ?_)
            rcases Subst.mem_freeVars_onTy hv with h | ⟨p, hp, hvp⟩
            · simp only [Ty.freeVars, List.mem_singleton] at h; omega
            · exact (hS₁below p hp).mem_lt v hvp
          exact hb.closeOver
        | poly σ0 =>
          refine Ty.BelowFvars.of_freeVars_lt (fun v hv => ?_)
          have := hKΦ v (hKsch σ0 (hpoly_mem_anns σ0 hs') v hv)
          omega
      · exact Subst.onCtx_below hS₁below (by omega) hbelow M hM
    have hS₂lc : ∀ p ∈ S₂, p.2.IsLC := (Infer.lc hbody hbodyWF).2
    -- gen-pool facts
    have hG_τs : ∀ g ∈ G, g ∈ Ty.freeVarsList
        (RecSpecs.monoTys ((RecSpec.init Φ anns).map (RecSpec.onSubst S₁))) :=
      fun g hg => (genGroupVars_spec (hG ▸ hg)).1
    have hG_envS₁ : ∀ g ∈ G, g ∉ (S₁.onCtx ctx).env.freeVars :=
      fun g hg => (genGroupVars_spec (hG ▸ hg)).2.1
    have hG_rigid : ∀ g ∈ G, g ∉ RecGroup.rigidVars anns bindings :=
      fun g hg => (genGroupVars_spec (hG ▸ hg)).2.2
    have hG_anns : ∀ g ∈ G, ∀ σ0, some σ0 ∈ anns → g ∉ σ0.body.freeVars := by
      intro g hg σ0 hσ0 hc
      exact hG_rigid g hg
        (List.mem_append_left _ (Expr.scheme_body_mem_annList_tyFreeVars hσ0 hc))
    have hG_bind : ∀ g ∈ G, g ∉ Expr.tyFreeVars.RecGroup.tyFreeVars bindings := by
      intro g hg hc
      exact hG_rigid g hg (List.mem_append_right _ (Expr.mem_recGroup_tyFreeVars.mp hc))
    have hG_lt : ∀ g ∈ G, g < Φ₁ := fun g hg => by
      obtain ⟨τ, hτ, hgτ⟩ := Ty.mem_freeVarsList_exists (hG_τs g hg)
      exact (hτs_below τ hτ).mem_lt g hgτ
    have hG_S₁dom : ∀ g ∈ G, ∀ p ∈ S₁, p.1 ≠ g := by
      intro g hg p hp hpeq
      obtain ⟨τ, hτ, hgτ⟩ := Ty.mem_freeVarsList_exists (hG_τs g hg)
      obtain ⟨m, _, _, rfl⟩ := hmono_shape τ (hmonoTys_mem τ hτ)
      exact helimG p hp (Ty.fvar m) (hpeq ▸ hgτ)
    have hG_ctxenv : ∀ g ∈ G, ∀ M ∈ ctx.env, g ∉ M.body.freeVars := by
      intro g hg M hM hc
      exact hG_envS₁ g hg (by
        rw [Env.mem_freeVars_iff]
        exact ⟨S₁.onPolyTy M, List.mem_map.mpr ⟨M, hM, rfl⟩,
          Ty.mem_freeVars_onTy_of_not_dom hc (fun p hp hpeq => hG_S₁dom g hg p hp hpeq)⟩)
    have hG_ge : ∀ g ∈ G, Φ ≤ g := by
      intro g hg
      by_contra hlt
      push_neg at hlt
      obtain ⟨τ, hτ, hgτ⟩ := Ty.mem_freeVarsList_exists (hG_τs g hg)
      obtain ⟨m, hm1, _, rfl⟩ := hmono_shape τ (hmonoTys_mem τ hτ)
      have hgrange := (InferRecGroup.range_avoid hgroup (w := g) (by omega)
        (by intro M hM
            rcases List.mem_append.mp hM with hM | hM
            · obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hM
              rw [RecSpec.rhsEntry_nil_body_freeVars]
              intro hcc
              rcases RecSpec.mem_init hs with ⟨m', hm'1, _, rfl⟩ | ⟨σ0, hσ0, rfl⟩
              · simp only [RecSpec.freeVars, Ty.freeVars, List.mem_singleton] at hcc
                omega
              · exact hG_anns g hg σ0 hσ0 hcc
            · exact hG_ctxenv g hg M hM)
        (by intro s hs hcc
            rcases RecSpec.mem_init hs with ⟨m', hm'1, _, rfl⟩ | ⟨σ0, hσ0, rfl⟩
            · simp only [RecSpec.freeVars, Ty.freeVars, List.mem_singleton] at hcc
              omega
            · exact hG_anns g hg σ0 hσ0 hcc)
        (fun hc => hG_bind g hg hc))
      rcases Subst.mem_freeVars_onTy hgτ with h | ⟨p, hp, hgp⟩
      · simp only [Ty.freeVars, List.mem_singleton] at h
        omega
      · exact hgrange p hp hgp
    have hG_body : ∀ g ∈ G, g ∉ body.tyFreeVars :=
      fun g hg hc => by have := hKΦ g (hKe g (.inr hc)); have := hG_ge g hg; omega
    have hG_bodyCtx : ∀ g ∈ G, ∀ M ∈ (((RecSpec.init Φ anns).map (RecSpec.onSubst S₁)).map
        (RecSpec.bodyScheme G) ++ (S₁.onCtx ctx).env), g ∉ M.body.freeVars := by
      intro g hg M hM hc
      rcases List.mem_append.mp hM with hM | hM
      · obtain ⟨s', hs', rfl⟩ := List.mem_map.mp hM
        cases s' with
        | mono τ =>
          simp only [RecSpec.bodyScheme, PolyTy.genGroup] at hc
          by_cases hgτ : g ∈ τ.freeVars
          · exact Ty.not_mem_closeOver_freeVars
              (by simp only [Ty.genFilter, List.mem_filter, decide_eq_true_eq]
                  exact ⟨hg, hgτ⟩) hc
          · exact hgτ (Ty.freeVars_closeOver_subset hc)
        | poly σ0 =>
          exact hG_anns g hg σ0 (hpoly_mem_anns σ0 hs') hc
      · exact hG_envS₁ g hg (Env.mem_freeVars_iff.mpr ⟨M, hM, hc⟩)
    have hS₂G : ∀ p ∈ S₂, p.1 ∉ G := fun p hp hc =>
      Infer.dom_avoid hbody (hG_lt p.1 hc) (hG_bodyCtx p.1 hc) (hG_body p.1 hc)
        (List.mem_map.mpr ⟨p, hp, rfl⟩)
    have hS₂Gran : ∀ p ∈ S₂, ∀ u ∈ p.2.freeVars, u ∉ G := fun p hp u hu hc =>
      (Infer.range_avoid hbody (w := u) (hG_lt u hc) (hG_bodyCtx u hc) (hG_body u hc)).1 p hp hu
    have hS₁bc : ∀ p ∈ S₁, ∀ M ∈ (((RecSpec.init Φ anns).map (RecSpec.onSubst S₁)).map
        (RecSpec.bodyScheme G) ++ (S₁.onCtx ctx).env), p.1 ∉ M.body.freeVars := by
      intro p hp M hM hc
      rcases List.mem_append.mp hM with hM | hM
      · obtain ⟨s', hs', rfl⟩ := List.mem_map.mp hM
        obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hs'
        cases s with
        | mono τ0 =>
          rcases RecSpec.mem_init hs with ⟨m, _, _, heq⟩ | ⟨σ0, _, heq⟩
          · cases heq
            simp only [RecSpec.onSubst, RecSpec.bodyScheme, PolyTy.genGroup] at hc
            exact helimG p hp (Ty.fvar m) (Ty.freeVars_closeOver_subset hc)
          · exact absurd heq (by simp)
        | poly σ0 =>
          exact hS₁K p hp (hKsch σ0 (RecSpec.poly_mem_init hs) p.1 hc)
      · simp only [Subst.onCtx, Subst.onEnv] at hM
        obtain ⟨M₀, hM₀, rfl⟩ := List.mem_map.mp hM
        exact helimG p hp M₀.body hc
    -- rigidity of schemes under S₂ and the two bridges
    have hσfixS₂ : ∀ σ0, some σ0 ∈ anns → Subst.onPolyTy S₂ σ0 = σ0 := by
      intro σ0 hσ0
      simp only [Subst.onPolyTy]
      rw [show Subst.onTy S₂ σ0.body = σ0.body from
        Ty.substFvars_eq_self_of_no_key (fun p hp hc => hS₂K p hp (hKsch σ0 hσ0 p.1 hc))]
    have hentryS₂ : ∀ s' ∈ (RecSpec.init Φ anns).map (RecSpec.onSubst S₁),
        Subst.onPolyTy S₂ (RecSpec.rhsEntry [] [] s')
          = RecSpec.rhsEntry [] [] (RecSpec.onSubst S₂ s') := by
      intro s' hs'
      cases s' with
      | mono τ0 => rfl
      | poly σ0 => exact hσfixS₂ σ0 (hpoly_mem_anns σ0 hs')
    have hmapeq2 : ∀ (l : List RecSpec),
        (∀ s' ∈ l, Subst.onPolyTy S₂ (RecSpec.rhsEntry [] [] s')
          = RecSpec.rhsEntry [] [] (RecSpec.onSubst S₂ s')) →
        (l.map (RecSpec.rhsEntry [] [])).map (Subst.onPolyTy S₂)
          = (l.map (RecSpec.onSubst S₂)).map (RecSpec.rhsEntry [] []) := by
      intro l hl
      rw [List.map_map, List.map_map]
      exact List.map_congr_left (fun s' hs' => hl s' hs')
    have hbridge2 : S₂.onCtx { (S₁.onCtx ctx) with
          env := ((RecSpec.init Φ anns).map (RecSpec.onSubst S₁)).map (RecSpec.rhsEntry [] [])
            ++ (S₁.onCtx ctx).env }
        = { ((S₁ ++ S₂).onCtx ctx) with
            env := (((RecSpec.init Φ anns).map (RecSpec.onSubst S₁)).map
                (RecSpec.onSubst S₂)).map (RecSpec.rhsEntry [] [])
              ++ ((S₁ ++ S₂).onCtx ctx).env } := by
      rw [Subst.onCtx_append]
      show (⟨Subst.onEnv S₂ (((RecSpec.init Φ anns).map (RecSpec.onSubst S₁)).map
            (RecSpec.rhsEntry [] []) ++ (S₁.onCtx ctx).env), ctx.ctors⟩ : Ctx) = _
      rw [Subst.onEnv, List.map_append]
      refine congrArg (fun E => (⟨E ++ (S₂.onCtx (S₁.onCtx ctx)).env, ctx.ctors⟩ : Ctx)) ?_
      exact hmapeq2 _ hentryS₂
    have hbodysound := Infer.sourceSound hbody hbodyWF hbodyBelow K
      (fun k hk => by have := hKΦ k hk; omega)
      (fun y hy => hKe y (.inr hy)) hS₂K
    -- assemble residual packing via `TypeOfHM.letRec_of_emptyPool` at the residual ctx
    set init0 : List RecSpec := RecSpec.init Φ anns with hinit0
    set specsS₁ : List RecSpec := init0.map (RecSpec.onSubst S₁) with hspecsS₁
    set specsS : List RecSpec := specsS₁.map (RecSpec.onSubst S₂) with hspecsS
    -- body-scheme bridge under S₂ (twin of hbridge2 / hentryS₂)
    have hentryS₂_body : ∀ s' ∈ specsS₁,
        Subst.onPolyTy S₂ (RecSpec.bodyScheme G s')
          = RecSpec.bodyScheme G (RecSpec.onSubst S₂ s') := by
      intro s' hs'
      cases s' with
      | mono τ0 => exact Subst.onPolyTy_genGroup hS₂G hS₂Gran
      | poly σ0 => exact hσfixS₂ σ0 (hpoly_mem_anns σ0 hs')
    have hmapeq2_body : ∀ (l : List RecSpec),
        (∀ s' ∈ l, Subst.onPolyTy S₂ (RecSpec.bodyScheme G s')
          = RecSpec.bodyScheme G (RecSpec.onSubst S₂ s')) →
        (l.map (RecSpec.bodyScheme G)).map (Subst.onPolyTy S₂)
          = (l.map (RecSpec.onSubst S₂)).map (RecSpec.bodyScheme G) := by
      intro l hl
      rw [List.map_map, List.map_map]
      exact List.map_congr_left (fun s' hs' => hl s' hs')
    have hbridge_body : S₂.onCtx { (S₁.onCtx ctx) with
          env := specsS₁.map (RecSpec.bodyScheme G) ++ (S₁.onCtx ctx).env }
        = { ((S₁ ++ S₂).onCtx ctx) with
            env := specsS.map (RecSpec.bodyScheme G) ++ ((S₁ ++ S₂).onCtx ctx).env } := by
      rw [Subst.onCtx_append]
      show (⟨Subst.onEnv S₂ (specsS₁.map (RecSpec.bodyScheme G) ++ (S₁.onCtx ctx).env),
          ctx.ctors⟩ : Ctx) = _
      rw [Subst.onEnv, List.map_append]
      refine congrArg (fun E => (⟨E ++ (S₂.onCtx (S₁.onCtx ctx)).env, ctx.ctors⟩ : Ctx)) ?_
      exact hmapeq2_body _ hentryS₂_body
    -- residual RecSpecs.WF on solved/S₂-transported specs, then erase
    have hwfSrc : RecSpecs.WF anns bindings specsS G := by
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · -- anns_eq: onSubst preserves ann, init recovers anns
        simp only [specsS, specsS₁, init0]
        rw [RecSpec.map_ann_onSubst, RecSpec.map_ann_onSubst, RecSpec.map_ann_init]
      · -- length
        simp only [specsS, specsS₁, init0, List.length_map]
        exact InferRecGroup.length_eq hgroup
      · -- nodup of gen-pool
        rw [hG]; exact genGroupVars_nodup
      · -- mono_lc after S₂
        intro τ hτ
        obtain ⟨s1, hs1, heq⟩ := List.mem_map.mp (show RecSpec.mono τ ∈ specsS₁.map (RecSpec.onSubst S₂)
          from by simpa only [specsS] using hτ)
        cases s1 with
        | mono τ0 =>
          injection heq with hτeq
          exact hτeq ▸ Subst.onTy_lc hS₂lc (hsolvedLC (.mono τ0) hs1)
        | poly _ => exact absurd heq (by simp [RecSpec.onSubst])
      · -- poly_wf: schemes rigid, come from user anns
        intro σ hσ
        have hσs : RecSpec.poly σ ∈ specsS₁ :=
          RecSpec.poly_mem_map_onSubst.mp (by simpa only [specsS] using hσ)
        exact hwfanns σ (hpoly_mem_anns σ hσs)
    set rhsS₁ : Ctx :=
      { (S₁.onCtx ctx) with
        env := specsS₁.map (RecSpec.rhsEntry [] []) ++ (S₁.onCtx ctx).env }
    set rhsS : Ctx :=
      { ((S₁ ++ S₂).onCtx ctx) with
        env := specsS.map (RecSpec.rhsEntry [] []) ++ ((S₁ ++ S₂).onCtx ctx).env }
    have hbridge2' : S₂.onCtx rhsS₁ = rhsS := by
      simpa only [rhsS₁, rhsS, specsS₁, specsS] using hbridge2
    have hzip : bindings.zip specsS =
        (bindings.zip specsS₁).map (fun p => (p.1, RecSpec.onSubst S₂ p.2)) := by
      simp only [specsS]
      rw [List.zip_map_right]
      exact List.map_congr_left (fun _ _ => rfl)
    set Lp : List Nat := L₀ ++ S₂.map Prod.fst
    refine TypeOfHM.letRec_of_emptyPool (ctx := (S₁ ++ S₂).onCtx ctx)
      (Lp := Lp) (G := G) (anns := anns) (bs := bindings)
      (specs := specsS) (body := body) hwfSrc ?_ ?_ ?_ ?_ ?_ ?_
    · intro g hg hc
      rw [Subst.onCtx_append, Env.mem_freeVars_iff] at hc
      obtain ⟨M, hM, hgM⟩ := hc
      obtain ⟨M₀, hM₀, rfl⟩ := List.mem_map.mp hM
      exact Subst.notMemOnTy (fun p hp hgp => hS₂Gran p hp g hgp hg)
        (fun hc => hG_envS₁ g hg (Env.mem_freeVars_iff.mpr ⟨M₀, hM₀, hc⟩)) hgM
    · intro g hg σ hσ
      exact hG_anns g hg σ
        (hpoly_mem_anns σ (RecSpec.poly_mem_map_onSubst.mp hσ))
    · intro g hg e he hc
      exact hG_bind g hg (Expr.mem_recGroup_tyFreeVars.mpr
        (List.mem_flatMap.mpr ⟨e, he, hc⟩))
    · intro p hp τm hτm
      rw [hzip] at hp
      obtain ⟨⟨rhs, spec⟩, hpair, rfl⟩ := List.mem_map.mp hp
      cases spec with
      | poly σ => simp [RecSpec.onSubst] at hτm
      | mono τ₀ =>
        simp only [RecSpec.onSubst, RecSpec.mono.injEq] at hτm
        subst τm
        have h0 := hmonoS (rhs, .mono τ₀) hpair τ₀ rfl
        have hfix : rhs.substTyFvars S₂ = rhs :=
          Expr.substTyFvars_eq_self_of_not_mem_tyFreeVars (fun p hp hc =>
            hS₂K p hp (hKbind p.1 (Expr.mem_recGroup_tyFreeVars.mpr
              (List.mem_flatMap.mpr ⟨rhs, (List.of_mem_zip hpair).1, hc⟩))))
        have h1 := TypeOfHM.onSubst_fixed S₂ hS₂lc hfix h0
        rw [hbridge2'] at h1
        exact h1
    · intro p hp σ hσ Ys hYs
      rw [hzip] at hp
      obtain ⟨⟨rhs, spec⟩, hpair, rfl⟩ := List.mem_map.mp hp
      cases spec with
      | mono τ₀ => simp [RecSpec.onSubst] at hσ
      | poly σ₀ =>
        simp only [RecSpec.onSubst, RecSpec.poly.injEq] at hσ
        subst σ
        have hYs0 : FreshNames L₀ σ₀.paramCount Ys :=
          ⟨hYs.length, hYs.nodup,
            fun x hx hc => hYs.avoid x hx (List.mem_append_left _ hc)⟩
        have hS₂Ys : ∀ q ∈ S₂, q.1 ∉ Ys := fun q hq hc =>
          hYs.avoid q.1 hc (List.mem_append_right _
            (List.mem_map.mpr ⟨q, hq, rfl⟩))
        have hσmem : some σ₀ ∈ anns :=
          hpoly_mem_anns σ₀ (List.of_mem_zip hpair).2
        have h0 := hpolyS (rhs, .poly σ₀) hpair σ₀ rfl Ys hYs0
        have hfix : (rhs.openTyVars Ys).substTyFvars S₂ = rhs.openTyVars Ys :=
          Expr.substTyFvars_eq_self_of_not_mem_tyFreeVars (fun q hq hc => by
            rcases Expr.tyFreeVars_openTyVars hc with h | h
            · exact hS₂K q hq (hKbind q.1 (Expr.mem_recGroup_tyFreeVars.mpr
                (List.mem_flatMap.mpr ⟨rhs, (List.of_mem_zip hpair).1, h⟩)))
            · exact hS₂Ys q hq h)
        have h1 := TypeOfHM.onSubst_fixed S₂ hS₂lc hfix h0
        have hσfix : S₂.onTy (σ₀.openVars Ys) = σ₀.openVars Ys :=
          Ty.substFvars_eq_self_of_no_key (fun q hq hc => by
            rcases Ty.freeVars_openVars_subset q.1 hc with h | h
            · exact hS₂K q hq (hKsch σ₀ hσmem q.1 h)
            · exact hS₂Ys q hq h)
        rwa [hbridge2', hσfix] at h1
    · change TypeOfHM { ((S₁ ++ S₂).onCtx ctx) with
        env := specsS.map (RecSpec.bodyScheme G) ++ ((S₁ ++ S₂).onCtx ctx).env }
        body τ
      rwa [hbridge_body] at hbodysound
termination_by e.size
decreasing_by
  all_goals (try subst_vars; try simp only [Expr.size, Expr.size_openTyVars]; omega)

theorem InferBranches.sourceSound {Φ ctx scrutTy ρ brs Φ' S}
    (h : InferBranches Φ ctx scrutTy ρ brs Φ' S)
    (hctx : CtxWF ctx) (hbelow : CtxBelow Φ ctx)
    (hscrutTy : scrutTy.IsLC) (hρ : ρ.IsLC)
    (hscrutB : Ty.BelowFvars Φ scrutTy) (hρB : Ty.BelowFvars Φ ρ) (K : List Nat)
    (hKΦ : ∀ k ∈ K, k < Φ)
    (hKbr : ∀ y ∈ Expr.tyFreeVars.BranchList.tyFreeVars brs, y ∈ K)
    (hSK : ∀ p ∈ S, p.1 ∉ K) :
    ∀ p ∈ brs,
      TypeOfMatchBranch (S.onCtx ctx)
        (p.1, p.2)
        ((S.onTy scrutTy)) ((S.onTy ρ)) := by
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
    have hrest_sound := InferBranches.sourceSound hrest hctx1WF hctx1bel
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
      have h0 : TypeOfHM (S₁.onCtx bodyCtx) body
          τb :=
        Infer.sourceSound hbody hbodyWF hbodyBelow K
          (fun k hk => by have := hKΦ k hk; have := hle0; omega)
          (fun y hy => hKbr y (by
            simp only [Expr.tyFreeVars.BranchList.tyFreeVars, List.mem_append]; exact Or.inl hy))
          (fun p hp => hSK p (List.mem_append_left _ (List.mem_append_left _
              (List.mem_append_right _ hp))))
      have hbodyfixS2 : body.substTyFvars S₂ = body :=
        Expr.substTyFvars_eq_self_of_not_mem_tyFreeVars (fun p hp hc =>
          hSe p (List.mem_append_left _ (List.mem_append_right _ hp))
            (by simp only [Expr.tyFreeVars.BranchList.tyFreeVars, List.mem_append]; exact Or.inl hc))
      have h1 := TypeOfHM.onSubst_fixed (ctx := S₁.onCtx bodyCtx)
        (e := body) (τ := τb) S₂ hS₂lc hbodyfixS2 h0
      have huni_eq := huni.unifies
      have h1ρ : TypeOfHM (S₂.onCtx (S₁.onCtx bodyCtx)) body
          ((S₂.onTy (S₁.onTy (S₀.onTy ρ)))) := by
        rwa [huni_eq] at h1
      have hbodyfixS3 : body.substTyFvars S₃ = body :=
        Expr.substTyFvars_eq_self_of_not_mem_tyFreeVars (fun p hp hc =>
          hSe p (List.mem_append_right _ hp)
            (by simp only [Expr.tyFreeVars.BranchList.tyFreeVars, List.mem_append]; exact Or.inl hc))
      have h2 := TypeOfHM.onSubst_fixed
        (ctx := S₂.onCtx (S₁.onCtx bodyCtx)) (e := body)
        (τ := S₂.onTy (S₁.onTy (S₀.onTy ρ))) S₃ hS₃lc hbodyfixS3 h1ρ
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
          (S₃.onCtx (S₂.onCtx (S₁.onCtx (S₀.onCtx ctx)))) =
            ((S₀ ++ S₁ ++ S₂ ++ S₃).onCtx ctx) := by
        simp only [← Subst.onCtx_append, List.append_assoc]
      have hτ_pack : (S₃.onTy (S₂.onTy (S₁.onTy (S₀.onTy ρ)))) =
          ((S₀ ++ S₁ ++ S₂ ++ S₃).onTy ρ) := by
        simp only [Subst.onTy_append, List.append_assoc]
      have hbody_final : TypeOfHM
          { ((S₀ ++ S₁ ++ S₂ ++ S₃).onCtx ctx) with
            env := instContents.map PolyTy.mkTrivial
              ++ ((S₀ ++ S₁ ++ S₂ ++ S₃).onCtx ctx).env }
          body
          (((S₀ ++ S₁ ++ S₂ ++ S₃).onTy ρ)) := by
        rw [hbb123] at h2
        simpa only [hctx_pack, hτ_pack] using h2
      have hlook' :
          LookupList.get? ((S₀ ++ S₁ ++ S₂ ++ S₃).onCtx ctx).ctors c =
            some ctor := by
        have hctors : ((S₀ ++ S₁ ++ S₂ ++ S₃).onCtx ctx).ctors = ctx.ctors := by
          simp only [Subst.onCtx]
        simpa [hctors] using hlook
      have hscrut' :
          ((S₀ ++ S₁ ++ S₂ ++ S₃).onTy scrutTy) =
            .customTy ctor.tyName taFull := by
        have hu1 := congrArg S₁.onTy huni0.unifies
        have hu2 := congrArg S₂.onTy hu1
        have hu3 := congrArg S₃.onTy hu2
        simpa only [Subst.onTy_append, Subst.onTy_customTy, List.map_map,
          List.append_assoc, taFull, ta0, Function.comp_apply] using hu3
      have hfields' :
          List.Forall₂ (InstantiatesBy taFull) ctor.contents instContents := by
        simp only [instContents]
        exact List.forall₂_self_map (fun c0 hc0 =>
          InstantiatesBy.openWith (ctor.bound c0 hc0) (by
            simp only [taFull, ta0, List.length_map, freshVars_length]; exact Nat.le_refl _))
      refine TypeOfMatchBranch.mk
        (ctor := ctor)
        (tyArgs := taFull)
        (instContents := instContents)
        ⟨hlook', hscrut',
          by simp [taFull, ta0, List.length_map, freshVars_length],
          by simp [hn],
          hfields'⟩
        rfl hbody_final
    · -- rest source branches
      have hctx_eq : (S₃.onCtx (S₂.onCtx (S₁.onCtx (S₀.onCtx ctx)))) =
          ((S₀ ++ S₁ ++ S₂ ++ S₃).onCtx ctx) := by
        simp only [← Subst.onCtx_append, List.append_assoc]
      have hscrut_eq : (S₃.onTy (S₂.onTy (S₁.onTy (S₀.onTy scrutTy)))) =
          ((S₀ ++ S₁ ++ S₂ ++ S₃).onTy scrutTy) := by
        simp only [Subst.onTy_append, List.append_assoc]
      have hρ_eq : (S₃.onTy (S₂.onTy (S₁.onTy (S₀.onTy ρ)))) =
          ((S₀ ++ S₁ ++ S₂ ++ S₃).onTy ρ) := by
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
    have hrest_sound := InferBranches.sourceSound hrest hctx1WF hctx1bel
      (Subst.onTy_lc hS₂lc (Subst.onTy_lc hS₁lc hscrutTy))
      (Subst.onTy_lc hS₂lc (Subst.onTy_lc hS₁lc hρ))
      hscrut'bel hρ'bel K (fun k hk => by have := hKΦ k hk; omega)
      (fun y hy => hKbr y (by
        simp only [Expr.tyFreeVars.BranchList.tyFreeVars, List.mem_append]; exact Or.inr hy))
      (fun p hp => hSK p (List.mem_append_right _ hp))
    intro p hp
    rcases List.mem_cons.mp hp with rfl | hp_rest
    · have h0 := Infer.sourceSound hbody hctx hbelow K hKΦ
        (fun y hy => hKbr y (by
          simp only [Expr.tyFreeVars.BranchList.tyFreeVars, List.mem_append]; exact Or.inl hy))
        (fun p hp => hSK p (List.mem_append_left _ (List.mem_append_left _ hp)))
      have hbodyfixS2 : body.substTyFvars S₂ = body :=
        Expr.substTyFvars_eq_self_of_not_mem_tyFreeVars (fun p hp hc =>
          hSe p (List.mem_append_left _ (List.mem_append_right _ hp))
            (by simp only [Expr.tyFreeVars.BranchList.tyFreeVars, List.mem_append]; exact Or.inl hc))
      have h1 := TypeOfHM.onSubst_fixed_append S₁ S₂ hS₁lc hS₂lc
        (Expr.substTyFvars_eq_self_of_not_mem_tyFreeVars (fun p hp hc =>
          hSe p (List.mem_append_left _ (List.mem_append_left _ hp))
            (by simp only [Expr.tyFreeVars.BranchList.tyFreeVars, List.mem_append]; exact Or.inl hc)))
        hbodyfixS2 h0
      have huni_eq := huni.unifies
      have h1ρ : TypeOfHM ((S₁ ++ S₂).onCtx ctx) body
          ((S₂.onTy (S₁.onTy ρ))) := by
        rwa [huni_eq] at h1
      have hbodyfixS3 : body.substTyFvars S₃ = body :=
        Expr.substTyFvars_eq_self_of_not_mem_tyFreeVars (fun p hp hc =>
          hSe p (List.mem_append_right _ hp)
            (by simp only [Expr.tyFreeVars.BranchList.tyFreeVars, List.mem_append]; exact Or.inl hc))
      have h2 := TypeOfHM.onSubst_fixed (ctx := (S₁ ++ S₂).onCtx ctx)
        (e := body) (τ := S₂.onTy (S₁.onTy ρ)) S₃ hS₃lc hbodyfixS3 h1ρ
      have hctx_eq : (S₃.onCtx ((S₁ ++ S₂).onCtx ctx)) =
          ((S₁ ++ S₂ ++ S₃).onCtx ctx) := by rw [← Subst.onCtx_append]
      have hτ_eq : (S₃.onTy (S₂.onTy (S₁.onTy ρ))) =
          ((S₁ ++ S₂ ++ S₃).onTy ρ) := by
        rw [Subst.onTy_append, Subst.onTy_append]
      have hfinal : TypeOfHM ((S₁ ++ S₂ ++ S₃).onCtx ctx) body
          (((S₁ ++ S₂ ++ S₃).onTy ρ)) := by
        rwa [hctx_eq, hτ_eq] at h2
      exact TypeOfMatchBranch.wildcard hfinal
    · have hctx_eq : (S₃.onCtx (S₂.onCtx (S₁.onCtx ctx))) =
          ((S₁ ++ S₂ ++ S₃).onCtx ctx) := by
        simp only [← Subst.onCtx_append, List.append_assoc]
      have hscrut_eq : (S₃.onTy (S₂.onTy (S₁.onTy scrutTy))) =
          ((S₁ ++ S₂ ++ S₃).onTy scrutTy) := by
        simp only [Subst.onTy_append, List.append_assoc]
      have hρ_eq : (S₃.onTy (S₂.onTy (S₁.onTy ρ))) =
          ((S₁ ++ S₂ ++ S₃).onTy ρ) := by
        simp only [Subst.onTy_append, List.append_assoc]
      have key := hrest_sound p hp_rest
      rwa [hctx_eq, hscrut_eq, hρ_eq] at key
termination_by Expr.sizeBranches brs
decreasing_by
  all_goals (try subst_vars; try simp only [Expr.sizeBranches]; omega)

/-- Source soundness of recursive-group inference (mutual with `Infer.sourceSound`). -/
theorem InferRecGroup.sourceSound {Φ ctx bindings specs Φ' S}
    (h : InferRecGroup Φ ctx bindings specs Φ' S)
    (hctx : CtxWF ctx) (hbelow : CtxBelow Φ ctx)
    (hspecs : ∀ s ∈ specs, s.LC) (hspecsB : ∀ s ∈ specs, s.BelowFvars Φ)
    (hspecs_env : ∀ s ∈ specs, ∀ y ∈ s.freeVars, y ∈ ctx.env.freeVars)
    (K : List Nat) (hKΦ : ∀ k ∈ K, k < Φ)
    (hKbr : ∀ y ∈ Expr.tyFreeVars.RecGroup.tyFreeVars bindings, y ∈ K)
    (hKsch : ∀ σ, RecSpec.poly σ ∈ specs → ∀ y ∈ σ.body.freeVars, y ∈ K)
    (hSK : ∀ p ∈ S, p.1 ∉ K) :
    (∀ p ∈ bindings.zip (specs.map (RecSpec.onSubst S)), ∀ τ, p.2 = RecSpec.mono τ →
        TypeOfHM (S.onCtx ctx)
          p.1 τ)
      ∧ (∃ L : List Nat, ∀ p ∈ bindings.zip (specs.map (RecSpec.onSubst S)),
          ∀ σ, p.2 = RecSpec.poly σ → ∀ Xs, FreshNames L σ.paramCount Xs →
            TypeOfHM (S.onCtx ctx)
              ((p.1.openTyVars Xs))
              ((σ.openVars Xs))) := by
  cases h with
  | nil =>
    refine ⟨?_, [], ?_⟩
    · intro p hp; simp at hp
    · intro p hp; simp at hp
  | consMono he huni hrest =>
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
    obtain ⟨hmono_tail, L_tail, hpoly_tail⟩ := InferRecGroup.sourceSound hrest hctx2 hbelow2
      hspecs' hspecsB' hspecs_env' K (fun k hk => lt_of_lt_of_le (hKΦ k hk) hle1)
      (fun y hy => hKbr y (.inr hy))
      (fun σ' hσ' => hKsch σ' (List.mem_cons_of_mem _ (RecSpec.poly_mem_map_onSubst.mp hσ')))
      hK3
    have hspecmap : specs.map (RecSpec.onSubst (S₁ ++ S₂ ++ S₃))
        = (specs.map (RecSpec.onSubst (S₁ ++ S₂))).map (RecSpec.onSubst S₃) := by
      rw [List.map_map]
      exact List.map_congr_left (fun s _ => RecSpec.onSubst_append (S₁ ++ S₂) S₃ s)
    refine ⟨?_, L_tail, ?_⟩
    · intro p hp τ0 hτ0
      simp only [List.map_cons, List.zip_cons_cons, List.mem_cons] at hp
      rcases hp with rfl | hp_rest
      · have hred : RecSpec.onSubst (S₁ ++ S₂ ++ S₃) (RecSpec.mono τ)
            = RecSpec.mono ((S₁ ++ S₂ ++ S₃).onTy τ) := rfl
        rw [hred] at hτ0
        injection hτ0 with hτeq
        subst hτeq
        have h0 := Infer.sourceSound he hctx hbelow K hKΦ (fun y hy => hKbr y (.inl hy)) hK1
        have hefixS2 : e.substTyFvars S₂ = e :=
          Expr.substTyFvars_eq_self_of_not_mem_tyFreeVars (fun p hp hc =>
            hK2 p hp (hKbr p.1 (.inl hc)))
        have h1 := TypeOfHM.onSubst_fixed_append S₁ S₂ hS₁ hS₂
          (Expr.substTyFvars_eq_self_of_not_mem_tyFreeVars (fun p hp hc =>
            hK1 p hp (hKbr p.1 (.inl hc)))) hefixS2 h0
        have huni_eq := huni.unifies
        have h1' : TypeOfHM ((S₁ ++ S₂).onCtx ctx) e
            ((S₂.onTy (S₁.onTy τ))) := by
          rwa [huni_eq] at h1
        have hefixS3 : e.substTyFvars S₃ = e :=
          Expr.substTyFvars_eq_self_of_not_mem_tyFreeVars (fun p hp hc =>
            hK3 p hp (hKbr p.1 (.inl hc)))
        have h2 := TypeOfHM.onSubst_fixed (ctx := (S₁ ++ S₂).onCtx ctx)
          (e := e) (τ := S₂.onTy (S₁.onTy τ)) S₃ hS₃lc hefixS3 h1'
        have hctx_eq : (S₃.onCtx ((S₁ ++ S₂).onCtx ctx)) =
            ((S₁ ++ S₂ ++ S₃).onCtx ctx) := by rw [← Subst.onCtx_append]
        have hty_eq : (S₃.onTy (S₂.onTy (S₁.onTy τ))) =
            ((S₁ ++ S₂ ++ S₃).onTy τ) := by
          simp only [Subst.onTy_append]
        rwa [hctx_eq, hty_eq] at h2
      · rw [hspecmap] at hp_rest
        have hctx_eq : (S₃.onCtx (S₂.onCtx (S₁.onCtx ctx))) =
            ((S₁ ++ S₂ ++ S₃).onCtx ctx) := by
          simp only [← Subst.onCtx_append, List.append_assoc]
        have htail := hmono_tail p hp_rest τ0 hτ0
        rwa [hctx_eq] at htail
    · intro p hp σ0 hσ0 Xs hXs
      simp only [List.map_cons, List.zip_cons_cons, List.mem_cons] at hp
      rcases hp with rfl | hp_rest
      · exact absurd hσ0 (by simp [RecSpec.onSubst])
      · rw [hspecmap] at hp_rest
        have hctx_eq : (S₃.onCtx (S₂.onCtx (S₁.onCtx ctx))) =
            ((S₁ ++ S₂ ++ S₃).onCtx ctx) := by
          simp only [← Subst.onCtx_append, List.append_assoc]
        have htail := hpoly_tail p hp_rest σ0 hσ0 Xs hXs
        rwa [hctx_eq] at htail
  | consPoly hN he huni hesc1 hesc2 hrest =>
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
    have hYs_lt : ∀ y ∈ Ys, y < Φ₁ :=
      fun y hy => by simp only [Ys] at hy; have := freshVars_lt y hy; omega
    have hYs_ctx : ∀ y ∈ Ys,
        ∀ M ∈ (Schk.onCtx (S₁.onCtx ctx)).env, y ∉ M.body.freeVars :=
      fun y hy M hM hc => by
        simp only [Ys] at hy
        exact hesc2 y hy (Env.mem_freeVars_iff.mpr ⟨M, hM, hc⟩)
    have hYs_specs : ∀ y ∈ Ys,
        ∀ s' ∈ specs.map (RecSpec.onSubst (S₁ ++ Schk)), y ∉ s'.freeVars :=
      fun y hy s' hs' hc => by
        simp only [Ys] at hy
        exact hesc2 y hy (hspecs_env' s' hs' y hc)
    have hYs_rest : ∀ y ∈ Ys, y ∉ Expr.tyFreeVars.RecGroup.tyFreeVars rest :=
      fun y hy hc => by
        have := hKΦ y (hKbr' y hc)
        simp only [Ys] at hy; have := freshVars_ge y hy; omega
    have hS₂Ys : ∀ p ∈ S₂, p.1 ∉ Ys := fun p hp hc =>
      InferRecGroup.dom_avoid hrest (hYs_lt p.1 hc) (hYs_ctx p.1 hc)
        (fun s' hs' => hYs_specs p.1 hc s' hs') (hYs_rest p.1 hc)
        (List.mem_map.mpr ⟨p, hp, rfl⟩)
    have hrhs_sound := Infer.sourceSound he hctx hctx_pc (K ++ Ys)
      (fun k hk => by
        rcases List.mem_append.mp hk with h | h
        · have := hKΦ k h; omega
        · simp only [Ys] at h; have := freshVars_lt k h; omega)
      (fun y hy => by
        rcases Expr.tyFreeVars_openTyVars hy with h | h
        · exact List.mem_append_left _ (hKbr y (.inl h))
        · simp only [Ys]; exact List.mem_append_right _ h)
      (fun p hp hc => by
        rcases List.mem_append.mp hc with h | h
        · exact hK1 p hp h
        · simp only [Ys] at h
          exact hesc1 p.1 h (List.mem_map.mpr ⟨p, List.mem_append_left _ hp, rfl⟩))
    have he_open_fix : (e.openTyVars Ys).substTyFvars Schk = e.openTyVars Ys :=
      Expr.substTyFvars_eq_self_of_not_mem_tyFreeVars (fun p hp hc => by
        rcases Expr.tyFreeVars_openTyVars hc with h | h
        · exact hKchk p hp (hKbr p.1 (.inl h))
        · simp only [Ys] at h
          exact hesc1 p.1 h (List.mem_map.mpr ⟨p, List.mem_append_right _ hp, rfl⟩))
    have hr1 := TypeOfHM.onSubst_fixed (ctx := S₁.onCtx ctx)
      (e := e.openTyVars Ys) (τ := τ) Schk hSchk_lc he_open_fix hrhs_sound
    have hu := huni.unifies
    have hSchk_fix : Schk.onTy (σ.openVars Ys) = σ.openVars Ys :=
      Ty.substFvars_eq_self_of_no_key (fun p hp hc => by
        rcases Ty.freeVars_openVars_subset p.1 hc with h | h
        · exact hKchk p hp (hKsch σ List.mem_cons_self p.1 h)
        · simp only [Ys] at h ⊢
          exact hesc1 p.1 h (List.mem_map.mpr ⟨p, List.mem_append_right _ hp, rfl⟩))
    have hr1' : TypeOfHM ((S₁ ++ Schk).onCtx ctx)
        ((e.openTyVars Ys)) ((σ.openVars Ys)) := by
      have key := hr1
      rwa [← Subst.onCtx_append, hu, hSchk_fix] at key
    have he_open_fix2 : (e.openTyVars Ys).substTyFvars S₂ = e.openTyVars Ys :=
      Expr.substTyFvars_eq_self_of_not_mem_tyFreeVars (fun p hp hc => by
        rcases Expr.tyFreeVars_openTyVars hc with h | h
        · exact hK2 p hp (hKbr p.1 (.inl h))
        · exact hS₂Ys p hp h)
    have hr2 := TypeOfHM.onSubst_fixed (ctx := (S₁ ++ Schk).onCtx ctx)
      (e := e.openTyVars Ys) (τ := σ.openVars Ys) S₂ hS₂lc he_open_fix2 hr1'
    have hS₂fix : S₂.onTy (σ.openVars Ys) = σ.openVars Ys :=
      Ty.substFvars_eq_self_of_no_key (fun p hp hc => by
        rcases Ty.freeVars_openVars_subset p.1 hc with h | h
        · exact hK2 p hp (hKsch σ List.mem_cons_self p.1 h)
        · exact hS₂Ys p hp h)
    have hr2' : TypeOfHM ((S₁ ++ Schk ++ S₂).onCtx ctx)
        ((e.openTyVars Ys)) ((σ.openVars Ys)) := by
      have key := hr2
      rw [hS₂fix] at key
      convert key using 1
      rw [← Subst.onCtx_append]
    have hYs_env : ∀ y ∈ Ys, y ∉ ((S₁ ++ Schk ++ S₂).onCtx ctx).env.freeVars := by
      intro y hy hc
      rw [show (S₁ ++ Schk ++ S₂).onCtx ctx = S₂.onCtx ((S₁ ++ Schk).onCtx ctx) from by
            rw [show (S₁ ++ Schk ++ S₂ : Subst) = (S₁ ++ Schk) ++ S₂ from rfl,
                Subst.onCtx_append],
          Env.mem_freeVars_iff] at hc
      obtain ⟨M, hM, hyM⟩ := hc
      rw [show (S₂.onCtx ((S₁ ++ Schk).onCtx ctx)).env
            = ((S₁ ++ Schk).onCtx ctx).env.map (Subst.onPolyTy S₂) from rfl, List.mem_map] at hM
      obtain ⟨M₀, hM₀, rfl⟩ := hM
      have hS₂Ysran : ∀ p ∈ S₂, ∀ u ∈ p.2.freeVars, u ∉ Ys :=
        fun p hp u hu hc' =>
          (InferRecGroup.range_avoid hrest (w := u) (hYs_lt u hc') (hYs_ctx u hc')
            (fun s' hs' => hYs_specs u hc' s' hs') (hYs_rest u hc')) p hp hu
      refine Subst.notMemOnTy (fun p hp hyp => hS₂Ysran p hp y hyp hy) (fun hc2 => ?_) hyM
      rw [Subst.onCtx_append] at hM₀
      simp only [Ys] at hy
      exact hesc2 y hy (Env.mem_freeVars_iff.mpr ⟨M₀, hM₀, hc2⟩)
    have hYs_σ : ∀ y ∈ Ys, y ∉ σ.body.freeVars :=
      fun y hy hc => by
        have := hKΦ y (hKsch σ List.mem_cons_self y hc)
        simp only [Ys] at hy; have := freshVars_ge y hy; omega
    obtain ⟨hmono_tail, L_tail, hpoly_tail⟩ := InferRecGroup.sourceSound hrest hctx' hbelow'
      hspecs' hspecsB' hspecs_env' K (fun k hk => by have := hKΦ k hk; omega) hKbr' hKsch' hK2
    have hctxbridge : S₂.onCtx (Schk.onCtx (S₁.onCtx ctx)) = (S₁ ++ Schk ++ S₂).onCtx ctx := by
      rw [show (S₁ ++ Schk ++ S₂ : Subst) = (S₁ ++ Schk) ++ S₂ from rfl,
          Subst.onCtx_append, Subst.onCtx_append]
    have hspecmap : specs.map (RecSpec.onSubst (S₁ ++ Schk ++ S₂))
        = (specs.map (RecSpec.onSubst (S₁ ++ Schk))).map (RecSpec.onSubst S₂) := by
      rw [List.map_map]
      exact List.map_congr_left (fun s _ => RecSpec.onSubst_append (S₁ ++ Schk) S₂ s)
    refine ⟨?_, Ys ++ L_tail, ?_⟩
    · intro p hp τ0 hτ0
      simp only [List.map_cons, List.zip_cons_cons, List.mem_cons] at hp
      rcases hp with rfl | hp_rest
      · exact absurd hτ0 (by simp [RecSpec.onSubst])
      · rw [hspecmap] at hp_rest
        have hctx_eq : (S₂.onCtx (Schk.onCtx (S₁.onCtx ctx))) =
            ((S₁ ++ Schk ++ S₂).onCtx ctx) := by rw [hctxbridge]
        have htail := hmono_tail p hp_rest τ0 hτ0
        rwa [hctx_eq] at htail
    · intro p hp σ0 hσ0 Xs hXs
      simp only [List.map_cons, List.zip_cons_cons, List.mem_cons] at hp
      rcases hp with rfl | hp_rest
      · -- head poly: source e, rename Ys→Xs of residual open at Ys
        have hσeq : σ = σ0 := by
          simp only [RecSpec.onSubst] at hσ0
          injection hσ0
        subst hσeq
        have hYsX : ∀ y ∈ Ys, y ∉ Xs := fun y hy hc => hXs.avoid y hc (List.mem_append_left _ hy)
        have hXlen : Xs.length = Ys.length := by
          have := hXs.length
          simp only [Ys, freshVars_length] at this ⊢
          exact this
        have hraw : (e.openTyVars Ys).substTyFvars (Ys.zip (Xs.map (Ty.fvar ·))) =
            e.openTyVars Xs :=
          Expr.substTyFvars_zip_openTyVars hXlen.symm
            (by simp only [Ys]; exact freshVars_nodup)
            (fun y hy hc => by

              have := hKΦ y (hKbr y (.inl hc))
              simp only [Ys] at hy; have := freshVars_ge y hy; omega)
            hYsX
        have htermeq : ((e.openTyVars Ys)).substTyFvars
              (Ys.zip (Xs.map (Ty.fvar ·))) = (e.openTyVars Xs) := by
          exact hraw
        have htypeeq : Subst.onTy (Ys.zip (Xs.map (Ty.fvar ·)))
              ((σ.openVars Ys)) = (σ.openVars Xs) := by
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
          exact h'.symm
        have hren := TypeOfHM.onSubst (Ys.zip (Xs.map (Ty.fvar ·)))
          (fun p hp => by
            obtain ⟨_, hp2⟩ := List.of_mem_zip hp
            obtain ⟨x, _, hxeq⟩ := List.mem_map.mp hp2
            rw [← hxeq]; exact ContainsBvarsUpTo.fvar)
          hr2'
        have hctxfix : Subst.onCtx (Ys.zip (Xs.map (Ty.fvar ·)))
              ((S₁ ++ Schk ++ S₂).onCtx ctx) =
              ((S₁ ++ Schk ++ S₂).onCtx ctx) := by
          conv_lhs => rw [Subst.onCtx]
          refine congrArg (fun E =>
            (⟨E, ((S₁ ++ Schk ++ S₂).onCtx ctx).ctors⟩ : Ctx)) ?_
          exact Subst.onEnv_eq_self_of_fresh (fun p hp hc =>
            hYs_env p.1 (List.of_mem_zip hp).1 hc)
        have htypeeq' : Subst.onTy (Ys.zip (Xs.map (Ty.fvar ·)))
            ((PolyTy.openVars Ys σ)) = (PolyTy.openVars Xs σ) := by
          simpa only [PolyTy.openVars] using htypeeq
        rwa [hctxfix, htermeq, htypeeq'] at hren
      · rw [hspecmap] at hp_rest
        have htail := hpoly_tail p hp_rest σ0 hσ0 Xs
          ⟨hXs.length, hXs.nodup, fun x hx hc => hXs.avoid x hx (List.mem_append_right _ hc)⟩
        have hctx_eq : (S₂.onCtx (Schk.onCtx (S₁.onCtx ctx))) =
            ((S₁ ++ Schk ++ S₂).onCtx ctx) := by rw [hctxbridge]
        rwa [hctx_eq] at htail
termination_by Expr.sizeRecGroup bindings
decreasing_by
  all_goals (try subst_vars; try simp only [Expr.sizeRecGroup, Expr.size_openTyVars]; omega)
end


/-- Runtime soundness follows by erasing a source-sound typing derivation. -/
theorem Infer.sound {Φ ctx e Φ' S τ} (h : Infer Φ ctx e Φ' S τ) :
    CtxWF ctx → CtxBelow Φ ctx → (K : List Nat) → (∀ k ∈ K, k < Φ) →
    (∀ y ∈ e.tyFreeVars, y ∈ K) → (∀ p ∈ S, p.1 ∉ K) →
    RuntimeTyping.RunWT (S.onCtx ctx) e.erase τ := by
  intro hctx hbelow K hKΦ hKe hSK
  exact (Infer.sourceSound h hctx hbelow K hKΦ hKe hSK).erase_preserves_typing


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

/-- Execute the legacy sequential recursive-ceiling constraint pass, formerly the middle
    `Sc` phase of recursive inference. It threads only committed non-pool
    substitutions between annotation checks and into the body. The
    three proof arguments are the ordinary prevalidated inputs of that phase
    (well-formed annotations, their rigid scoping, and locally-closed current
    specs).

The subtype carries both the relational trace and the ambient-`K` avoidance
fact, so clients do not need to recover either from boolean control flow. -/
def solveRecCeilingConstraints (K rigid G : List Nat) (Φ : Nat)
    (anns : List (Option PolyTy)) (specs : List RecSpec)
    (hannsWF : ∀ σ, some σ ∈ anns → σ.WF)
    (hannsRigid : ∀ σ, some σ ∈ anns → ∀ x ∈ σ.body.freeVars, x ∈ rigid)
    (hspecsLC : ∀ s ∈ specs, s.LC) :
    Option { S : Subst // RecCeilingConstraints K rigid G Φ anns specs S ∧
      ∀ p ∈ S, p.1 ∉ K } :=
  match anns, specs with
  | [], [] => some ⟨[], by simp [RecCeilingConstraints]⟩
  | none :: anns, _ :: specs =>
      match solveRecCeilingConstraints K rigid G Φ anns specs
        (fun σ hσ => hannsWF σ (List.mem_cons_of_mem _ hσ))
        (fun σ hσ => hannsRigid σ (List.mem_cons_of_mem _ hσ))
        (fun s hs => hspecsLC s (List.mem_cons_of_mem _ hs)) with
      | none => none
      | some ⟨tail, htail, htailK⟩ => some ⟨tail, htail, htailK⟩
  | some σ :: anns, .mono τ :: specs =>
      let Ys := freshVars Φ σ.paramCount
      match unifyCoreK (K ++ rigid ++ Ys) τ
          ((σ.openVars Ys)) with
      | none => none
      | some ⟨full, hfull, hfullAvoid⟩ =>
        let step := Subst.dropDomains G full
        if hrange : step.rangesWithin rigid G = true then
          let hτlc : τ.IsLC := hspecsLC (.mono τ) List.mem_cons_self
          let hopenlc : (σ.openVars Ys).IsLC :=
            PolyTy.openVars_isLC (hannsWF σ List.mem_cons_self)
              (by simp [Ys])
          let hstepLC : ∀ p ∈ step, p.2.IsLC := by
            intro p hp
            have hpfull : p ∈ full := (Subst.mem_dropDomains.mp hp).1
            exact UnifyRel.lc hfull hτlc hopenlc p hpfull
          match solveRecCeilingConstraints K rigid G Φ anns
            (specs.map (RecSpec.onSubst step))
            (fun σ' hσ' => hannsWF σ' (List.mem_cons_of_mem _ hσ'))
            (fun σ' hσ' => hannsRigid σ' (List.mem_cons_of_mem _ hσ'))
            (fun s' hs' => by
              obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hs'
              exact RecSpec.LC.onSubst hstepLC
                (hspecsLC s (List.mem_cons_of_mem _ hs))) with
          | none => none
          | some ⟨tail, htail, htailK⟩ =>
            let hrel : RecCeilingConstraints K rigid G Φ (some σ :: anns)
                (.mono τ :: specs) (step ++ tail) :=
              ⟨full, step, tail, hfull, hfullAvoid, rfl,
                Subst.rangesWithin_iff.mp hrange, hstepLC,
                hannsWF σ List.mem_cons_self,
                hannsRigid σ List.mem_cons_self, htail, rfl⟩
            some ⟨step ++ tail, ⟨hrel, fun p hp =>
              (RecCeilingConstraints.dom_avoids hrel p hp).1⟩⟩
        else none
  | _, _ => none
termination_by anns.length

/-- Refinement is definitionally carried by the worker's result. -/
theorem solveRecCeilingConstraints_sound {K rigid G Φ anns specs S}
    {hannsWF hannsRigid hspecsLC}
    (h : solveRecCeilingConstraints K rigid G Φ anns specs hannsWF hannsRigid hspecsLC = some S) :
    RecCeilingConstraints K rigid G Φ anns specs S.1 ∧
      ∀ p ∈ S.1, p.1 ∉ K := by
  cases hsolver : solveRecCeilingConstraints K rigid G Φ anns specs
      hannsWF hannsRigid hspecsLC with
  | none => simp [hsolver] at h
  | some S' =>
    rw [hsolver] at h
    simp only [Option.some.injEq] at h
    subst S
    exact S'.property

/-- Removing the bindings whose domains lie in `G` does not change a type which
    already avoids `G`, provided every retained image also avoids `G`.  This is
    the small algebraic fact behind the relational ceiling proof: the discarded
    bindings are precisely the choices later abstracted by `genGroup G`. -/
private theorem Subst.onTy_dropDomains_eq_of_avoids {G : List Nat} {S : Subst} {t : Ty}
    (ht : ∀ g ∈ G, g ∉ t.freeVars)
    (hran : ∀ p ∈ S.dropDomains G, ∀ g ∈ G, g ∉ p.2.freeVars) :
    S.onTy t = (S.dropDomains G).onTy t := by
  induction S generalizing t with
  | nil => rfl
  | cons p S ih =>
    obtain ⟨z, u⟩ := p
    simp only [Subst.onTy, Ty.substFvars, Subst.dropDomains, List.filter_cons]
    split
    · rename_i hkeep
      have hz : z ∉ G := by simpa [List.contains_eq_mem] using hkeep
      apply ih
      · intro g hg
        rw [Ty.mem_freeVars_substFvar_of (by
          intro heq
          subst g
          exact hz hg)]
        · exact ht g hg
        · exact hran (z, u) (by simp [Subst.dropDomains, hz]) g hg
      · intro q hq g hg
        have hq' : q ∈ Subst.dropDomains G ((z, u) :: S) :=
          Subst.mem_dropDomains.mpr ⟨List.mem_cons_of_mem _
            (Subst.mem_dropDomains.mp hq).1, (Subst.mem_dropDomains.mp hq).2⟩
        exact hran q hq' g hg
    · rename_i hdrop
      have hz : z ∈ G := by
        by_contra hz
        exact hdrop (by simpa [List.contains_eq_mem] using hz)
      rw [Ty.substFvar_fresh (ht z hz)]
      apply ih ht
      intro q hq g hg
      have hq' : q ∈ Subst.dropDomains G ((z, u) :: S) :=
        Subst.mem_dropDomains.mpr ⟨List.mem_cons_of_mem _
          (Subst.mem_dropDomains.mp hq).1, (Subst.mem_dropDomains.mp hq).2⟩
      exact hran q hq' g hg

/-- `genGroup G` closes every `G` variable which actually occurs and cannot
    manufacture the others, so its body is free of the whole supplied pool. -/
private theorem PolyTy.genGroup_avoids_pool {G : List Nat} {t : Ty} :
    ∀ g ∈ G, g ∉ (PolyTy.genGroup G t).body.freeVars := by
  intro g hg hbody
  have ht : g ∈ t.freeVars := Ty.freeVars_closeOver_subset
    (by simpa [PolyTy.genGroup] using hbody)
  have hgf : g ∈ Ty.genFilter G t := by simp [Ty.genFilter, hg, ht]
  exact Ty.not_mem_closeOver_freeVars hgf (by simpa [PolyTy.genGroup] using hbody)

/-- One relational ceiling constraint entails the declarative ceiling for the
    committed member.  The current type and rigid names being below `Φ` is the
    freshness fact which rules out the classic `Φ = 0`, `fvar 0`, `∀a.a`
    skolem-collision counterexample. -/
private theorem RecCeilingConstraints.member_generalizes
    {K rigid G : List Nat} {Φ : Nat} {τ : Ty} {σ : PolyTy} {full step : Subst}
    (hfull : UnifyRel τ
      ((σ.openVars (freshVars Φ σ.paramCount))) full)
    (havoid : ∀ p ∈ full, p.1 ∉ K ++ rigid ++ freshVars Φ σ.paramCount)
    (hstep : step = Subst.dropDomains G full)
    (hrange : ∀ p ∈ step, ∀ x ∈ p.2.freeVars, x ∈ rigid ∧ x ∉ G)
    (hτlc : τ.IsLC) (hσwf : σ.WF)
    (hσrigid : ∀ x ∈ σ.body.freeVars, x ∈ rigid)
    (hτbelow : τ.BelowFvars Φ) (hrigid : ∀ x ∈ rigid, x < Φ) :
    PolyTy.Generalizes
      ((PolyTy.genGroup G (step.onTy τ)))
      σ := by
  let Ys := freshVars Φ σ.paramCount
  have hYge : ∀ y ∈ Ys, Φ ≤ y := by
    intro y hy
    exact freshVars_ge y (by simpa [Ys] using hy)
  have hYbody : ∀ y ∈ Ys, y ∉ σ.body.freeVars := by
    intro y hy hybody
    exact Nat.not_le_of_gt (hrigid y (hσrigid y hybody)) (hYge y hy)
  have hYτ : ∀ y ∈ Ys, y ∉ τ.freeVars := by
    intro y hy hyτ
    exact Nat.not_le_of_gt (hτbelow.mem_lt y hyτ) (hYge y hy)
  have hopenLC : (σ.openVars Ys).IsLC :=
    PolyTy.openVars_isLC hσwf (by simp [Ys])
  have hfullLC : ∀ p ∈ full, p.2.IsLC :=
    UnifyRel.lc hfull hτlc (by simpa [Ys] using hopenLC)
  have hfullFix : full.onTy (σ.openVars Ys) = σ.openVars Ys := by
    apply Ty.substFvars_eq_self_of_no_key
    intro p hp hpbody
    rcases Ty.freeVars_openVars_subset p.1 hpbody with hbody | hY
    · exact havoid p hp (by simp [List.mem_append, hσrigid p.1 hbody])
    · exact havoid p hp (by simp [List.mem_append, hY, Ys])
  have htyr : Ty.openVars Ys σ.body = full.onTy τ := by
    have hu := hfull.unifies
    calc
      Ty.openVars Ys σ.body = σ.openVars Ys := rfl
      _ = full.onTy (σ.openVars Ys) := hfullFix.symm
      _ = full.onTy τ := hu.symm
  have hstepDom : ∀ p ∈ step, p.1 ∉ G := by
    intro p hp
    rw [hstep] at hp
    exact (Subst.mem_dropDomains.mp hp).2
  have hstepRan : ∀ p ∈ step, ∀ g ∈ G, g ∉ p.2.freeVars := by
    intro p hp g hg hgp
    exact (hrange p hp g hgp).2 hg
  have hschemeEq :
      full.onPolyTy (PolyTy.genGroup G τ) =
        (PolyTy.genGroup G (step.onTy τ)) := by
    have hprojBody : full.onTy (PolyTy.genGroup G τ).body =
        step.onTy (PolyTy.genGroup G τ).body := by
      rw [Subst.onTy_dropDomains_eq_of_avoids PolyTy.genGroup_avoids_pool]
      · rw [← hstep]
      · intro p hp g hg
        rw [← hstep] at hp
        exact hstepRan p hp g hg
    have hprojScheme : full.onPolyTy (PolyTy.genGroup G τ) =
        step.onPolyTy (PolyTy.genGroup G τ) := by
      unfold Subst.onPolyTy
      rw [hprojBody]
    rw [hprojScheme]
    rw [Subst.onPolyTy_genGroup hstepDom
      (fun p hp u hu hG => hstepRan p hp u hG hu)]
  have hYscheme : ∀ y ∈ Ys,
      y ∉ (full.onPolyTy (PolyTy.genGroup G τ)).body.freeVars := by
    intro y hy
    rw [hschemeEq]
    intro hybody
    have hystep : y ∈ (step.onTy τ).freeVars :=
      Ty.freeVars_closeOver_subset
        (by simpa [PolyTy.genGroup] using hybody)
    rcases Subst.mem_freeVars_onTy hystep with hyτ | ⟨p, hp, hyp⟩
    · exact hYτ y hy hyτ
    · exact Nat.not_le_of_gt (hrigid y (hrange p hp y hyp).1) (hYge y hy)
  have hres := closeOver_generalizes
    (g := Ty.genFilter G τ) (R := full)
    (M := σ) (Xs := Ys)
    hτlc hfullLC hσwf
    (by simpa [Ys] using freshVars_nodup)
    (by simp [Ys])
    (by intro y hy hybody; exact hYbody y hy hybody)
    htyr hYscheme
  change (full.onPolyTy (PolyTy.genGroup G τ)).Generalizes σ at hres
  rw [hschemeEq] at hres
  exact hres

/-- The sequential relational pass itself entails the group's declarative
    annotation ceiling.  No second executable acceptance test is needed: local
    closedness plus the inference-frontier bounds make every skolem opening
    genuinely fresh, while the relation's domain/range invariants preserve the
    fixed pool through the remaining constraints. -/
theorem RecCeilingConstraints.ceilingOK {K rigid G : List Nat} {Φ : Nat}
    {anns : List (Option PolyTy)} {specs : List RecSpec} {S : Subst}
    (h : RecCeilingConstraints K rigid G Φ anns specs S)
    (hlc : ∀ s ∈ specs, s.LC)
    (hbelow : ∀ s ∈ specs, s.BelowFvars Φ)
    (hrigid : ∀ x ∈ rigid, x < Φ) :
    RecSpecs.ceilingOK G anns (specs.map (RecSpec.onSubst S)) := by
  induction anns generalizing specs S with
  | nil =>
      cases specs <;> simp [RecCeilingConstraints] at h
      subst S
      simp [RecSpecs.ceilingOK]
  | cons ann anns ih =>
      cases ann with
      | none =>
          cases specs with
          | nil => simp [RecCeilingConstraints] at h
          | cons s specs =>
              unfold RecSpecs.ceilingOK
              exact .cons trivial (ih h
                (fun s' hs' => hlc s' (List.mem_cons_of_mem _ hs'))
                (fun s' hs' => hbelow s' (List.mem_cons_of_mem _ hs')))
      | some σ =>
          cases specs with
          | nil => simp [RecCeilingConstraints] at h
          | cons spec specs =>
              cases spec with
              | poly σ' => simp [RecCeilingConstraints] at h
              | mono τ =>
                  rcases h with ⟨full, step, tail, hfull, havoid, hstep, hrange,
                    hstepLC, hσwf, hσrigid, htail, rfl⟩
                  have hstepBelow : ∀ p ∈ step, Ty.BelowFvars Φ p.2 := by
                    intro p hp
                    apply Ty.BelowFvars.of_freeVars_lt
                    intro x hx
                    exact hrigid x (hrange p hp x hx).1
                  have htailCeiling := ih htail
                    (fun s' hs' => by
                      obtain ⟨s0, hs0, rfl⟩ := List.mem_map.mp hs'
                      exact RecSpec.LC.onSubst hstepLC
                        (hlc s0 (List.mem_cons_of_mem _ hs0)))
                    (fun s' hs' => by
                      obtain ⟨s0, hs0, rfl⟩ := List.mem_map.mp hs'
                      exact RecSpec.BelowFvars.onSubst hstepBelow
                        (hbelow s0 (List.mem_cons_of_mem _ hs0)))
                  have hhead0 := RecCeilingConstraints.member_generalizes
                    hfull havoid hstep hrange
                    (hlc (.mono τ) List.mem_cons_self) hσwf hσrigid
                    (hbelow (.mono τ) List.mem_cons_self) hrigid
                  have htailDom : ∀ p ∈ tail, p.1 ∉ G := fun p hp =>
                    (htail.dom_avoids p hp).2.2
                  have htailRan : ∀ p ∈ tail, ∀ u ∈ p.2.freeVars, u ∉ G :=
                    fun p hp u hu => htail.range_avoids_pool p hp u hu
                  have htailFix : tail.onPolyTy σ = σ := by
                    apply Subst.onPolyTy_eq_self_of_dom_avoids
                    intro p hp hfv
                    exact (htail.dom_avoids p hp).2.1 (hσrigid p.1 hfv)
                  have hhead := PolyTy.Generalizes.onSubst hhead0
                    hσwf htail.lc
                  have hleft :
                      tail.onPolyTy
                          ((PolyTy.genGroup G (step.onTy τ))) =
                        PolyTy.genGroup G ((step ++ tail).onTy τ) := by
                    rw [Subst.onPolyTy_genGroup htailDom htailRan]
                    rw [Subst.onTy_append]
                  rw [hleft, htailFix] at hhead
                  have hcons : RecSpecs.ceilingOK G (some σ :: anns)
                      (.mono ((step ++ tail).onTy τ) ::
                        (specs.map (RecSpec.onSubst step)).map (RecSpec.onSubst tail)) := by
                    unfold RecSpecs.ceilingOK
                    exact .cons hhead htailCeiling
                  have htailMap :
                      (specs.map (RecSpec.onSubst step)).map (RecSpec.onSubst tail) =
                        specs.map (RecSpec.onSubst (step ++ tail)) := by
                    rw [List.map_map]
                    apply List.map_congr_left
                    intro s hs
                    exact (RecSpec.onSubst_append step tail s).symm
                  rw [htailMap] at hcons
                  change RecSpecs.ceilingOK G (some σ :: anns)
                    (.mono ((step ++ tail).onTy τ) ::
                      specs.map (RecSpec.onSubst (step ++ tail)))
                  exact hcons

/-- Emit scheme facts for the genuinely generalized members of a recursion
    group. Annotated members are declarations, not inference-produced schemes,
    so they are omitted. -/
def inferredLetRecSchemes : Nat → List (Option PolyTy) → List PolyTy → InferredBinderSchemes
  | _, [], _ => []
  | _, _, [] => []
  | member, none :: anns, scheme :: schemes =>
      { site := .letRec [] member, scheme, tyDepth := 0 } ::
        inferredLetRecSchemes (member + 1) anns schemes
  | member, some _ :: anns, _ :: schemes =>
      inferredLetRecSchemes (member + 1) anns schemes



/-! ### The `infer` function (Algorithm W)

`inferWithTypesCore`/`inferBranchesWithTypesCore` mirror `Infer`/`InferBranches` exactly,
building the `Infer` derivation and a path-keyed node-type side table alongside
the output (soundness by construction);
recursion is structural on the expression / branch list. The `match_` case reads
the type name + arity off the first branch's constructor (branches are nonempty).
The public `infer` erases the derivation. -/
mutual
def inferWithTypesCore (K : List Nat) (Φ : Nat) (ctx : Ctx) (e : Expr) :
    Option { r : Nat × Subst × Ty × InferredNodeTypes × InferredBinderSchemes //
      Infer Φ ctx e r.1 r.2.1 r.2.2.1 ∧ (∀ p ∈ r.2.1, p.1 ∉ K) } :=
  match e with
  | .primLit .unit => some ⟨(Φ, [], .prim .unit, .root (.prim .unit), []), .primLitUnit, by simp⟩
  | .primLit (.int n) => some ⟨(Φ, [], .prim .int, .root (.prim .int), []), .primLitInt, by simp⟩
  | .primLit (.nat n) => some ⟨(Φ, [], .prim .nat, .root (.prim .nat), []), .primLitNat, by simp⟩
  | .primLit (.char c) => some ⟨(Φ, [], .prim .char, .root (.prim .char), []), .primLitChar, by simp⟩
  | .primBinOp .intAdd =>
      let ty := .arrow (.prim .int) (.arrow (.prim .int) (.prim .int))
      some ⟨(Φ, [], ty, .root ty, []), .primBinOpIntAdd, by simp⟩
  | .primBinOp .intSub =>
      let ty := .arrow (.prim .int) (.arrow (.prim .int) (.prim .int))
      some ⟨(Φ, [], ty, .root ty, []), .primBinOpIntSub, by simp⟩
  | .primBinOp .intLt =>
      match hT : LookupList.get? ctx.ctors ⟨"True"⟩ with
      | none => none
      | some tc =>
        match hF : LookupList.get? ctx.ctors ⟨"False"⟩ with
        | none => none
        | some fc =>
          if htc : tc.isBoolCtor = true then
            if hfc : fc.isBoolCtor = true then
              let ty := .arrow (.prim .int) (.arrow (.prim .int) (.customTy ⟨"Bool"⟩ []))
              some ⟨(Φ, [], ty, .root ty, []),
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
              let ty := .arrow (.prim .char) (.arrow (.prim .char) (.customTy ⟨"Bool"⟩ []))
              some ⟨(Φ, [], ty, .root ty, []),
                    .primBinOpCharLt hT (Ctor.isBoolCtor_iff.mp htc) hF (Ctor.isBoolCtor_iff.mp hfc), by simp⟩
            else none
          else none
  | .lambda none body =>
      match inferWithTypesCore K (Φ + 1) { ctx with env := PolyTy.mkTrivial (.fvar Φ) :: ctx.env } body with
      | none => none
      | some ⟨(Φ', S, τb, bodyTypes, bodySchemes), hbody, hav⟩ =>
        let ty := .arrow (S.onTy (.fvar Φ)) τb
        some ⟨(Φ', S, ty, .root ty ++ bodyTypes.below .lambdaBody,
            bodySchemes.below .lambdaBody), .lambda .none hbody, hav⟩
  | .lambda (some T) body =>
      if hT : Ty.bvarsBelow 0 T = true then
        match inferWithTypesCore K Φ { ctx with env := PolyTy.mkTrivial T :: ctx.env } body with
        | none => none
        | some ⟨(Φ', S, τb, bodyTypes, bodySchemes), hbody, hav⟩ =>
          let ty := .arrow (S.onTy T) τb
          some ⟨(Φ', S, ty, .root ty ++ bodyTypes.below .lambdaBody,
              bodySchemes.below .lambdaBody),
            .lambda (.some T ((Ty.bvarsBelow_iff T).mp hT)) hbody, hav⟩
      else none
  | .app f arg =>
      match inferWithTypesCore K Φ ctx f with
      | none => none
      | some ⟨(Φ₁, S₁, τf, fTypes, fSchemes), hf, hav₁⟩ =>
        match inferWithTypesCore K Φ₁ (S₁.onCtx ctx) arg with
        | none => none
        | some ⟨(Φ₂, S₂, τa, argTypes, argSchemes), harg, hav₂⟩ =>
          match unifyCoreK K (S₂.onTy τf) (.arrow τa (.fvar Φ₂)) with
          | none => none
          | some ⟨S₃, h₃, hav₃⟩ =>
            let ty := S₃.onTy (.fvar Φ₂)
            let nodeTypes := .root ty ++
              (fTypes.onSubst (S₂ ++ S₃)).below .appFun ++
              (argTypes.onSubst S₃).below .appArg
            let schemes := (fSchemes.onSubst (S₂ ++ S₃)).below .appFun ++
              (argSchemes.onSubst S₃).below .appArg
            some ⟨(Φ₂ + 1, S₁ ++ S₂ ++ S₃, ty, nodeTypes, schemes), .app hf harg h₃, by
              intro p hp; rcases List.mem_append.mp hp with h | h
              · rcases List.mem_append.mp h with h | h
                · exact hav₁ p h
                · exact hav₂ p h
              · exact hav₃ p h⟩
  | .var i =>
      match h : ctx.env[i]? with
      | none => none
      | some polyTy =>
        let ty := polyTy.openVars (freshVars Φ polyTy.paramCount)
        some ⟨(Φ + polyTy.paramCount, [], ty, .root ty, []), .var h, by simp⟩
  | .ctor name =>
      match h : LookupList.get? ctx.ctors name with
      | none => none
      | some ctorr =>
        let ty := ctorr.toTy.openVars (freshVars Φ ctorr.paramCount)
        some ⟨(Φ + ctorr.paramCount, [], ty, .root ty, []),
          .ctor h, by simp⟩
  | .letIn ann rhs body =>
      match ann with
      | none =>
        match inferWithTypesCore K Φ ctx rhs with
        | none => none
        | some ⟨(Φ₁, S₁, τ₁, rhsTypes, rhsSchemes), hrhs, hav₁⟩ =>
        match inferWithTypesCore K Φ₁
            { (S₁.onCtx ctx) with
              env := genScheme rhs.tyFreeVars (S₁.onCtx ctx).env τ₁ :: (S₁.onCtx ctx).env }
            body with
        | none => none
        | some ⟨(Φ₂, S₂, τ₂, bodyTypes, bodySchemes), hbody, hav₂⟩ =>
          let binderScheme := genScheme rhs.tyFreeVars (S₁.onCtx ctx).env τ₁
          let binderFact : InferredBinderScheme :=
            { site := .letIn [], scheme := S₂.onPolyTy binderScheme, tyDepth := 0 }
          let schemes := binderFact ::
            (rhsSchemes.onSubst S₂).below .letRhs ++ bodySchemes.below .letBody
          let nodeTypes := .root τ₂ ++
            (rhsTypes.onSubst S₂).below .letRhs ++ bodyTypes.below .letBody
          some ⟨(Φ₂, S₁ ++ S₂, τ₂, nodeTypes, schemes),
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
          match inferWithTypesCore (K ++ freshVars Φ σ.paramCount) (Φ + σ.paramCount) ctx
              (rhs.openTyVars (freshVars Φ σ.paramCount)) with
          | none => none
          | some ⟨(Φ₁, S₁, τ₁, rhsTypes, rhsSchemes), hrhs, hav₁⟩ =>
            match unifyCoreK (K ++ freshVars Φ σ.paramCount) τ₁
                (σ.openVars (freshVars Φ σ.paramCount)) with
            | none => none
            | some ⟨Schk, hSchk, havS⟩ =>
              if hesc1 : (∀ y ∈ freshVars Φ σ.paramCount, y ∉ (S₁ ++ Schk).map Prod.fst) then
                if hesc2 : (∀ y ∈ freshVars Φ σ.paramCount,
                    y ∉ (Schk.onCtx (S₁.onCtx ctx)).env.freeVars) then
                  match inferWithTypesCore K Φ₁
                      { (Schk.onCtx (S₁.onCtx ctx)) with
                        env := σ :: (Schk.onCtx (S₁.onCtx ctx)).env }
                      body with
                  | none => none
                  | some ⟨(Φ₂, S₂, τ₂, bodyTypes, bodySchemes), hbody, hav₂⟩ =>
                    let Ys := freshVars Φ σ.paramCount
                    let rhsFinalTypes :=
                      (((rhsTypes.onSubst Schk).closeTyVars Ys).onSubst S₂)
                        |>.underTyBinders σ.paramCount
                        |>.below .letRhs
                    let rhsFinalSchemes :=
                      (((rhsSchemes.onSubst Schk).closeTyVars Ys).onSubst S₂)
                        |>.underTyBinders σ.paramCount
                        |>.below .letRhs
                    let schemes := rhsFinalSchemes ++ bodySchemes.below .letBody
                    let nodeTypes := .root τ₂ ++ rhsFinalTypes ++ bodyTypes.below .letBody
                    some ⟨(Φ₂, S₁ ++ Schk ++ S₂, τ₂, nodeTypes, schemes),
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
      match inferWithTypesCore K Φ ctx scrut with
      | none => none
      | some ⟨(Φ₁, S₁, τs, scrutTypes, scrutSchemes), hscrut, hav₁⟩ =>
        match hh : branches.head? with
        | none => none
        | some _ =>
          match inferBranchesWithTypesCore K (Φ₁ + 1) (S₁.onCtx ctx) τs (.fvar Φ₁) 0 branches with
          | none => none
          | some ⟨(Φ₂, S₂, branchTypes, branchSchemes), hbranches, hav₂⟩ =>
            let ty := S₂.onTy (.fvar Φ₁)
            let schemes := (scrutSchemes.onSubst S₂).below .matchScrut ++ branchSchemes
            let nodeTypes := .root ty ++
              (scrutTypes.onSubst S₂).below .matchScrut ++ branchTypes
            some ⟨(Φ₂, S₁ ++ S₂, ty, nodeTypes, schemes),
                  .match_ hscrut (by intro hc; rw [hc] at hh; simp at hh) hbranches, by
                  intro p hp; rcases List.mem_append.mp hp with h | h
                  · exact hav₁ p h
                  · exact hav₂ p h⟩
  | .letRec anns bindings body =>
      -- Annotated entries are schemes in the recursive environment. The worker
      -- checks their RHSs under rigid skolems; inferred entries stay monotypes.
      if hwf : (∀ a ∈ anns, ∀ σ, a = some σ → Ty.bvarsBelow σ.paramCount σ.body = true) then
        match inferRecGroupWithTypesCore K (Φ + bindings.length)
            { ctx with env := (RecSpec.init Φ anns).map (RecSpec.rhsEntry [] []) ++ ctx.env }
            0 bindings (RecSpec.init Φ anns) with
        | none => none
        | some ⟨(Φ₁, S₁, bindingTypes, bindingSchemes), hgroup, hav₁⟩ =>
          let specs1 := (RecSpec.init Φ anns).map (RecSpec.onSubst S₁)
          let G := genGroupVars (RecGroup.rigidVars anns bindings) (S₁.onCtx ctx).env
                     (RecSpecs.monoTys specs1)
          match inferWithTypesCore K Φ₁
              { (S₁.onCtx ctx) with
                env := specs1.map (RecSpec.bodyScheme G) ++ (S₁.onCtx ctx).env }
              body with
          | none => none
          | some ⟨(Φ₂, S₂, τ₂, bodyTypes, bodySchemes), hbody, hav₂⟩ =>
            let groupSchemes := inferredLetRecSchemes 0 anns
              ((specs1.map (RecSpec.bodyScheme G)).map S₂.onPolyTy)
            let schemes := groupSchemes ++
              (bindingSchemes.underRecRhsBinders anns).onSubst S₂ ++
              bodySchemes.below .letRecBody
            let nodeTypes := .root τ₂ ++
              (bindingTypes.underRecRhsBinders anns).onSubst S₂ ++
              bodyTypes.below .letRecBody
            some ⟨(Φ₂, S₁ ++ S₂, τ₂, nodeTypes, schemes),
              .letRec (fun σ hσ => PolyTy.wf_iff_bvarsBelow.mp (hwf (some σ) hσ σ rfl))
                hgroup rfl rfl hbody, by
              intro p hp
              exact (List.mem_append.mp hp).elim (hav₁ p) (hav₂ p)⟩
      else none
termination_by e.size
decreasing_by
  all_goals (try simp only [Expr.size, Expr.size_openTyVars]; omega)

def inferBranchesWithTypesCore (K : List Nat) (Φ : Nat) (ctx : Ctx) (scrutTy : Ty) (ρ : Ty)
    (branchIndex : Nat) (branches : List (MatchPattern × Expr)) :
    Option { r : Nat × Subst × InferredNodeTypes × InferredBinderSchemes //
      InferBranches Φ ctx scrutTy ρ branches r.1 r.2.1 ∧ (∀ p ∈ r.2.1, p.1 ∉ K) } :=
  match branches with
  | [] => some ⟨(Φ, [], [], []), .nil, by simp⟩
  | (.wildcard, body) :: rest =>
      match inferWithTypesCore K Φ ctx body with
      | none => none
      | some ⟨(Φ₁, S₁, τb, bodyTypes, bodySchemes), hbody, hav₁⟩ =>
        match unifyCoreK K τb (S₁.onTy ρ) with
        | none => none
        | some ⟨S₂, huni, hav₂⟩ =>
          match inferBranchesWithTypesCore K Φ₁ (S₂.onCtx (S₁.onCtx ctx))
              (S₂.onTy (S₁.onTy scrutTy)) (S₂.onTy (S₁.onTy ρ)) (branchIndex + 1) rest with
          | none => none
          | some ⟨(Φ₂, S₃, restTypes, restSchemes), hrest, hav₃⟩ =>
            let schemes := (bodySchemes.onSubst (S₂ ++ S₃)).below
              (.matchBranch branchIndex) ++ restSchemes
            let nodeTypes := (bodyTypes.onSubst (S₂ ++ S₃)).below
              (.matchBranch branchIndex) ++ restTypes
            some ⟨(Φ₂, S₁ ++ S₂ ++ S₃,
                nodeTypes, schemes),
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
            match inferWithTypesCore K (Φ + ctorr.paramCount)
                { (S₀.onCtx ctx) with
                  env := (ctorr.contents.map (Ty.openWith
                      (((freshVars Φ ctorr.paramCount).map (Ty.fvar ·)).map S₀.onTy))).map PolyTy.mkTrivial
                    ++ (S₀.onCtx ctx).env }
                body with
            | none => none
            | some ⟨(Φ₁, S₁, τb, bodyTypes, bodySchemes), hbody, hav₁⟩ =>
              match unifyCoreK K τb (S₁.onTy (S₀.onTy ρ)) with
              | none => none
              | some ⟨S₂, huni, hav₂⟩ =>
                match inferBranchesWithTypesCore K Φ₁ (S₂.onCtx (S₁.onCtx (S₀.onCtx ctx)))
                    (S₂.onTy (S₁.onTy (S₀.onTy scrutTy))) (S₂.onTy (S₁.onTy (S₀.onTy ρ)))
                    (branchIndex + 1) rest with
                | none => none
                | some ⟨(Φ₂, S₃, restTypes, restSchemes), hrest, hav₃⟩ =>
                  let schemes := (bodySchemes.onSubst (S₂ ++ S₃)).below
                    (.matchBranch branchIndex) ++ restSchemes
                  let nodeTypes := (bodyTypes.onSubst (S₂ ++ S₃)).below
                    (.matchBranch branchIndex) ++ restTypes
                  some ⟨(Φ₂, S₀ ++ S₁ ++ S₂ ++ S₃,
                      nodeTypes, schemes),
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

/-- Thread inference and node-type production through a recursion group.  A
    `mono τ` member follows the Damas--Milner infer-and-unify path; a `poly σ`
    member is checked against fresh rigid skolems, with the resulting node and
    binder metadata retained in the same side tables.  `RecSpec.init` still
    emits only `.mono`, so the polymorphic path is staged but not yet selected
    by source `letRec` inference. -/
def inferRecGroupWithTypesCore (K : List Nat) (Φ : Nat) (ctx : Ctx) (memberIndex : Nat)
    (bindings : List Expr) (specs : List RecSpec) :
    Option { r : Nat × Subst × InferredNodeTypes × InferredBinderSchemes //
      InferRecGroup Φ ctx bindings specs r.1 r.2.1 ∧ (∀ p ∈ r.2.1, p.1 ∉ K) } :=
  match bindings, specs with
  | [], [] => some ⟨(Φ, [], [], []), .nil, by simp⟩
  | e :: rest, .mono τ :: specs' =>
      match inferWithTypesCore K Φ ctx e with
      | none => none
      | some ⟨(Φ₁, S₁, τ', eTypes, eSchemes), he, hav₁⟩ =>
        match unifyCoreK K τ' (S₁.onTy τ) with
        | none => none
        | some ⟨S₂, huni, hav₂⟩ =>
          match inferRecGroupWithTypesCore K Φ₁ (S₂.onCtx (S₁.onCtx ctx)) (memberIndex + 1) rest
              (specs'.map (RecSpec.onSubst (S₁ ++ S₂))) with
          | none => none
          | some ⟨(Φ₂, S₃, restTypes, restSchemes), hrest, hav₃⟩ =>
            let schemes := (eSchemes.onSubst (S₂ ++ S₃)).below (.letRecRhs memberIndex) ++
              restSchemes
            let nodeTypes := (eTypes.onSubst (S₂ ++ S₃)).below (.letRecRhs memberIndex) ++
              restTypes
            some ⟨(Φ₂, S₁ ++ S₂ ++ S₃,
                nodeTypes, schemes), .consMono he huni hrest, by
              intro p hp; rcases List.mem_append.mp hp with h | h
              · rcases List.mem_append.mp h with h | h
                · exact hav₁ p h
                · exact hav₂ p h
              · exact hav₃ p h⟩
  | e :: rest, .poly σ :: specs' =>
      let Ys := freshVars Φ σ.paramCount
      match inferWithTypesCore (K ++ Ys) (Φ + σ.paramCount) ctx
          (e.openTyVars Ys) with
      | none => none
      | some ⟨(Φ₁, S₁, τ, eTypes, eSchemes), he, hav₁⟩ =>
        match unifyCoreK (K ++ Ys) τ (σ.openVars Ys) with
        | none => none
        | some ⟨Schk, hSchk, havS⟩ =>
          if hesc1 : (∀ y ∈ Ys, y ∉ (S₁ ++ Schk).map Prod.fst) then
            if hesc2 : (∀ y ∈ Ys,
                y ∉ (Schk.onCtx (S₁.onCtx ctx)).env.freeVars) then
              match inferRecGroupWithTypesCore K Φ₁ (Schk.onCtx (S₁.onCtx ctx))
                  (memberIndex + 1) rest
                  (specs'.map (RecSpec.onSubst (S₁ ++ Schk))) with
              | none => none
              | some ⟨(Φ₂, S₂, restTypes, restSchemes), hrest, hav₂⟩ =>
                let schemes := (((eSchemes.onSubst Schk).closeTyVars Ys).onSubst S₂).below
                    (.letRecRhs memberIndex) ++ restSchemes
                let nodeTypes := (((eTypes.onSubst Schk).closeTyVars Ys).onSubst S₂).below
                    (.letRecRhs memberIndex) ++ restTypes
                some ⟨(Φ₂, S₁ ++ Schk ++ S₂, nodeTypes, schemes),
                  .consPoly (Nat.le_refl Φ) he hSchk hesc1 hesc2 hrest, by
                  intro p hp; rcases List.mem_append.mp hp with h | h
                  · rcases List.mem_append.mp h with h | h
                    · exact fun hc => hav₁ p h (List.mem_append_left _ hc)
                    · exact fun hc => havS p h (List.mem_append_left _ hc)
                  · exact hav₂ p h⟩
            else none
          else none
  | _, _ => none
termination_by Expr.sizeRecGroup bindings
decreasing_by
  all_goals (try simp only [Expr.sizeRecGroup, Expr.size_openTyVars]; omega)
end

/-- Compatibility projection of the authoritative metadata-producing worker. No
    inference is repeated and existing proof-facing callers keep their API. -/
def inferCore (K : List Nat) (Φ : Nat) (ctx : Ctx) (e : Expr) :
    Option { r : Nat × Subst × Ty //
      Infer Φ ctx e r.1 r.2.1 r.2.2 ∧ (∀ p ∈ r.2.1, p.1 ∉ K) } :=
  match inferWithTypesCore K Φ ctx e with
  | none => none
  | some ⟨(Φ', S, ty, _nodeTypes, _schemes), hInfer, hAvoid⟩ =>
      some ⟨(Φ', S, ty), hInfer, hAvoid⟩

/-- Public inference output with the discovered type at every logical Core node. -/
structure InferenceResult where
  frontier : Nat
  subst : Subst
  ty : Ty
  nodeTypes : NodeTypeMap
  binderSchemes : BinderSchemeMap

/-- The executable type inferer, refining `Infer`. Runs from the empty rigid set
    (top-level programs have no in-scope scoped type variables); annotated `let`s
    extend it internally with their skolem block. -/
def infer (Φ : Nat) (ctx : Ctx) (e : Expr) : Option (Nat × Subst × Ty) :=
  (inferCore [] Φ ctx e).map (·.1)

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

/-! ### Executable sanity checks

These guard against an operationally wrong but provable relation. `unify` and
`infer` reduce only under the compiler
(`#eval`), since both rest on well-founded recursion. -/

-- `unify (α → α) (Int → β) = [α ↦ Int, β ↦ Int]`

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

/-- Safe top-level metadata-producing inference. As with `principalType`, source
    annotation fvars are made rigid and the fresh frontier is seeded above them;
    this freshness is also what makes annotated-RHS open/close shape-preserving. -/
def inferWithTypes (ctors : CtorEnv) (e : Expr) : Option InferenceResult :=
  (inferWithTypesCore e.tyFreeVars e.freshFloor ⟨[], ctors⟩ e).map fun r =>
    { frontier := r.1.1
      subst := r.1.2.1
      ty := r.1.2.2.1
      nodeTypes := r.1.2.2.2.1.toMap
      binderSchemes := r.1.2.2.2.2.toMap }

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
    **erased** term (`e.erase`) in the erased ctor env (`ctors`).
    Holds for *any* `e`: free top-level annotation variables stay rigid
    (`K := e.tyFreeVars`). Glued by `Infer.sound` at `K := e.tyFreeVars` — the
    `Infer.eliminates` locality shows `S.onTy τ = τ`. -/
theorem principalType_sound {ctors : CtorEnv} {e : Expr} {τ : Ty}
    (h : principalType ctors e = some τ) :
    RuntimeTyping.RunWT ⟨[], ctors⟩ e.erase τ := by
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
    simpa [Subst.onCtx, Subst.onEnv, hSτ] using
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
    ∃ τ, RuntimeTyping.RunWT ⟨[], ctors⟩ e.erase τ ∧
      σ = genScheme [] [] τ := by
  rw [typecheck] at h
  rcases hc : principalType ctors e with _ | τ <;> rw [hc] at h
  · simp at h
  · simp only [Option.map_some, Option.some.injEq] at h
    exact ⟨τ, principalType_sound hc, h.symm⟩

-- Whole-program safety is the direct `TypeOfHM.type_safety(_star)` chain above,
-- applied to the runtime term produced by `Expr.erase`.

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
with exact equality and that is **correct, not an oversight**. Their computed
types are all-variable (`polyId` ⇒ `.fvar 0 → .fvar 0`), so every declarative
result is a genuine substitution instance.

Consequence for the farm: these four do **not** depend on the completeness engine.
Like `appFiveFive_untypeable`, each is a direct inversion of `TypeOfHM` on a
closed, tiny term — `polyId`'s inversion gives `τ₀ = paramTy → paramTy`, so
`R = [(0, paramTy)]`. Prove them standalone and early; do not block them on
`complete'`. -/

/-! #### Shared machinery for the four demos

Two ingredients recur.

* **Computing the principal type.** `inferCore`/`unifyCoreK`/… are well-founded
  recursions, so the small non-recursive examples are proved by unfolding their
  equation lemmas with `simp only [inferCore, …]` and then discharging the
  residual arithmetic/matching with `with_unfolding_all rfl`.  The mutual-`letRec`
  worker additionally carries dependent proof certificates through its sequential
  group worker; its concrete witness uses `native_decide` only for a Boolean
  *shape* projection, followed by ordinary constructor inversion to recover the
  propositional equality.  It does not install a `DecidableEq Ty` or compare the
  proof-carrying worker result itself.

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

set_option maxRecDepth 100_000 in
/-- `λx. x` has principal monotype `α → α` (computed, not postulated). -/
theorem polyId_principalType : principalType [] polyId = some (.arrow (.fvar 0) (.fvar 0)) := by
  show (inferCore [] 0 ⟨[], []⟩ (Expr.lambda none (Expr.var 0))).map (·.val.2.2) = _
  simp only [inferCore, inferWithTypesCore, List.getElem?_cons_zero]
  with_unfolding_all rfl

/-- `typecheck` succeeds, produces a genuine declarative type, and that type is
    principal. -/
theorem polyId_headlines_fire :
    ∃ σ τ, typecheck [] polyId = some σ ∧ σ = genScheme [] [] τ ∧
      TypeOfHM ⟨[], []⟩ polyId τ ∧
      ∀ τ₀, TypeOfHM ⟨[], []⟩ polyId τ₀ → ∃ R : Subst, τ₀ = R.onTy τ := by
  refine ⟨genScheme [] [] (.arrow (.fvar 0) (.fvar 0)), .arrow (.fvar 0) (.fvar 0),
    ?_, rfl, ?_, ?_⟩
  · show (principalType [] polyId).map (genScheme [] []) = _
    rw [polyId_principalType]; rfl
  · exact polyId_typeable
  ·
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

/-- The algorithm rejects `5 5`: if `typecheck` succeeded, `typecheck_sound`
    would give a declarative
    typing of the erased term — contradicting `appFiveFive_untypeable`. -/
theorem appFiveFive_rejected : ¬ (typecheck [] appFiveFive).isSome := by
  rintro h
  obtain ⟨σ, hσ⟩ := Option.isSome_iff_exists.mp h
  rcases typecheck_sound hσ with ⟨τ, hty, -⟩
  simp [Expr.erase, appFiveFive] at hty
  cases hty with
  | app hf _ => cases hf

/-! ### Open programs: a free top-level annotation variable is rigid -/

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

theorem openMisuse_untypeable : ¬ ∃ τ, TypeOfHM ⟨[], []⟩ openMisuse τ := by
  rintro ⟨τ, h⟩
  simp [openMisuse, openId] at h
  cases h with
  | app hf hx =>
    cases hf with
    | lambda hlc hpins heq hbody =>
      have hpin := hpins (.fvar 5) rfl
      rw [hpin] at hx
      cases hx

-- The algorithm rejects `openMisuse` too by completeness. The fully erased term
-- `(λx. x) 5` is ordinary well-typed HM; the rejection concerns the rigid source
-- annotation, so soundness alone cannot establish it.

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
  simp only [inferCore, inferWithTypesCore, Expr.openTyVars, Expr.openTyVarsAux, freshVars, List.range,
    List.range.loop, List.map, PolyTy.openVars, List.getElem?_cons_zero, Option.map_none]
  unfold unifyCoreK
  unfold unifyCoreK
  with_unfolding_all rfl

/-- `idid_typeable` at the computed principal variable `3`. Each `var` rule
    supplies the appropriate existential instantiation witness. -/
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
      TypeOfHM ⟨[], []⟩ idid τ ∧
      ∀ τ₀, TypeOfHM ⟨[], []⟩ idid τ₀ → ∃ R : Subst, τ₀ = R.onTy τ := by
  refine ⟨genScheme [] [] (.arrow (.fvar 3) (.fvar 3)), .arrow (.fvar 3) (.fvar 3),
    ?_, rfl, ?_, ?_⟩
  · show (principalType [] idid).map (genScheme [] []) = _
    rw [idid_principalType]; rfl
  · exact idid_typeable_fvar3
  ·
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

/-! ### Progress and preservation on a concrete program -/

/-- `(λx. x) 5` — already annotation-free; beta-reduces to `5`. -/
def appIdFive : Expr := .app (.lambda none (.var 0)) (.primLit (.int 5))

theorem appIdFive_typeable : TypeOfHM ⟨[], []⟩ appIdFive (.prim .int) :=
  TypeOfHM.app
    (TypeOfHM.lambda .prim (fun _ h => Option.noConfusion h) rfl
      (TypeOfHM.var (instArgs := []) rfl (by intro t ht; cases ht) .prim))
    TypeOfHM.primLitInt

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
  simp only [inferCore, inferWithTypesCore, inferBranchesWithTypesCore,
    List.getElem?_cons_zero]
  unfold unifyCoreK
  with_unfolding_all rfl

/-- All three headlines fire on the all-wildcard match: it typechecks, the produced
    type is a genuine declarative type (soundness), and it is principal. -/
theorem matchWild_headlines_fire :
    ∃ σ τ, typecheck [] matchWild = some σ ∧ σ = genScheme [] [] τ ∧
      TypeOfHM ⟨[], []⟩ matchWild τ ∧
      ∀ τ₀, TypeOfHM ⟨[], []⟩ matchWild τ₀ → ∃ R : Subst, τ₀ = R.onTy τ := by
  refine ⟨genScheme [] [] (.arrow (.fvar 0) (.prim .int)), .arrow (.fvar 0) (.prim .int),
    ?_, rfl, ?_, ?_⟩
  · show (principalType [] matchWild).map (genScheme [] []) = _
    rw [matchWild_principalType]; rfl
  · exact matchWild_typeable
  ·
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

/-- The all-`none` mutual group types at its principal monotype under
    `TypeOfHM.letRec`: `specs = [.mono (fvar 100), .mono (fvar 100)]`, witnesses
    `τs = [fvar 100, fvar 100]`, pool `[100]`. Inside the group both members sit
    at the opened shared monotype `fvar X`; the body sees them generalised to
    `∀a. a` and instantiates at `fvar 0`. -/
theorem mutualRec_typeable_at (n : Nat) : TypeOfHM ⟨[], []⟩ mutualRec (.fvar n) := by
  refine TypeOfHM.letRec (specs := [.mono (.fvar 100), .mono (.fvar 100)])
    (G := [100]) (L := []) ⟨rfl, rfl, by simp, ?_, ?_⟩ ?_ ?_ rfl ?_
  · intro τ hτ
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hτ
    rcases hτ with h | h <;> (injection h with h'; rw [h']; exact .fvar)
  · intro σ hσ
    simp only [List.mem_cons, List.not_mem_nil, reduceCtorEq, or_self] at hσ
  · intro Xs hfresh p hp τ hτ
    obtain ⟨X, rfl⟩ : ∃ X, Xs = [X] := List.length_eq_one_iff.mp hfresh.length
    simp only [List.zip_cons_cons, List.zip_nil_right, List.mem_cons, List.not_mem_nil,
      or_false] at hp
    rcases hp with rfl | rfl <;> (simp only [RecSpec.mono.injEq] at hτ; subst τ)
    · show TypeOfHM ⟨[PolyTy.mkTrivial (.fvar X), PolyTy.mkTrivial (.fvar X)], []⟩
        (.var 1) (.fvar X)
      exact TypeOfHM.var (instArgs := []) rfl (by simp) .fvar
    · show TypeOfHM ⟨[PolyTy.mkTrivial (.fvar X), PolyTy.mkTrivial (.fvar X)], []⟩
        (.var 0) (.fvar X)
      exact TypeOfHM.var (instArgs := []) rfl (by simp) .fvar
  · intro Xs hfresh p hp σ hσ
    simp only [List.zip_cons_cons, List.zip_nil_right, List.mem_cons, List.not_mem_nil,
      or_false] at hp
    rcases hp with rfl | rfl <;> cases hσ
  · show TypeOfHM ⟨[⟨1, .bvar 0⟩, ⟨1, .bvar 0⟩], []⟩ (.var 0) (.fvar n)
    exact TypeOfHM.var (polyTy := ⟨1, .bvar 0⟩) (instArgs := [.fvar n]) rfl
      (by intro t ht; simp only [List.mem_singleton] at ht; subst ht; exact .fvar)
      (.bvar rfl)

theorem mutualRec_typeable : TypeOfHM ⟨[], []⟩ mutualRec (.fvar 0) :=
  mutualRec_typeable_at 0

set_option maxRecDepth 100_000 in
/-- The group's principal monotype is a bare variable (`∀a. a` after
    generalisation); `mutualRec.tyFreeVars = []`, and the two fresh group
    monotypes leave residual variable `2` for the body instantiation. -/
theorem mutualRec_principalType : principalType [] mutualRec = some (.fvar 2) := by
  have hshape : (match principalType [] mutualRec with
      | some (.fvar 2) => true
      | _ => false) = true := by
    native_decide
  generalize hresult : principalType [] mutualRec = result at hshape ⊢
  cases result with
  | none => cases hshape
  | some ty =>
    cases ty with
    | fvar n =>
      cases n with
      | zero => cases hshape
      | succ n =>
        cases n with
        | zero => cases hshape
        | succ n =>
          cases n with
          | zero => rfl
          | succ _ => cases hshape
    | prim _ => cases hshape
    | arrow _ _ => cases hshape
    | bvar _ => cases hshape
    | customTy _ _ => cases hshape

/-- `mutualRec_typeable` at the computed principal variable `2`. -/
theorem mutualRec_typeable_fvar2 : TypeOfHM ⟨[], []⟩ mutualRec (.fvar 2) :=
  mutualRec_typeable_at 2

/-- All headlines fire on the recursive group: `typecheck` succeeds, the produced
    type is a genuine declarative type, and it is principal. -/
theorem mutualRec_headlines_fire :
    ∃ σ τ, typecheck [] mutualRec = some σ ∧ σ = genScheme [] [] τ ∧
      TypeOfHM ⟨[], []⟩ mutualRec τ ∧
      ∀ τ₀, TypeOfHM ⟨[], []⟩ mutualRec τ₀ → ∃ R : Subst, τ₀ = R.onTy τ := by
  refine ⟨genScheme [] [] (.fvar 2), .fvar 2, ?_, rfl, ?_, ?_⟩
  · show (principalType [] mutualRec).map (genScheme [] []) = _
    rw [mutualRec_principalType]; rfl
  · exact mutualRec_typeable_fvar2
  · -- The principal type is a *bare* variable, so every `τ₀` is trivially an
    -- instance: no inversion needed.
    intro τ₀ _
    exact ⟨[(2, τ₀)], rfl⟩

end AuditCapstone
