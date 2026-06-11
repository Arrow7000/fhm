import Experiments.FreshTypeSystem.Core

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


/-! ### Substitution preserves typing

Substituting over the *whole* context needs no environment-freshness side
condition (the freshness premise of `typ_subst_preservation` is vacuous with an
empty outer env) — only that each replacement type is locally-closed. This is
the workhorse for `Infer` soundness: applying the threaded substitution to a
`TypeOfHM` derivation yields another. -/

/-- Single-variable substitution preserves typing across the whole context. -/
theorem TypeOfHM.onSubstFvar {ctx : Ctx} {e : Expr} {τ : Ty} (Z : Nat) (U : Ty)
    (hU : U.IsLC) (h : TypeOfHM ctx e τ) :
    TypeOfHM (Subst.onCtx [(Z, U)] ctx) e (Subst.onTy [(Z, U)] τ) := by
  have key := TypeOfHM.typ_subst_preservation (ctors := ctx.ctors) (env_post := ctx.env)
    (env_outer := []) (Z := Z) (U := U) (by simp [Env.freeVars]) hU
    (by rw [List.append_nil]; exact h)
  rw [List.append_nil] at key
  exact key

/-- A whole substitution preserves typing, given each replacement is LC. -/
theorem TypeOfHM.onSubst {ctx : Ctx} {e : Expr} {τ : Ty} (S : Subst)
    (h_lc : ∀ p ∈ S, p.2.IsLC) (h : TypeOfHM ctx e τ) :
    TypeOfHM (S.onCtx ctx) e (S.onTy τ) := by
  induction S generalizing ctx τ with
  | nil => simpa using h
  | cons hd S' ih =>
    obtain ⟨Z, U⟩ := hd
    have hU : U.IsLC := h_lc (Z, U) (List.mem_cons_self ..)
    have hS' : ∀ p ∈ S', p.2.IsLC := fun p hp => h_lc p (List.mem_cons_of_mem _ hp)
    have step := TypeOfHM.onSubstFvar Z U hU h
    have rest := ih hS' step
    rw [show ((Z, U) :: S') = [(Z, U)] ++ S' from rfl, Subst.onCtx_append, Subst.onTy_append]
    exact rest


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

  | pair {a b c d S₁ S₂} :
    UnifyRel a c S₁ →
    UnifyRel (S₁.onTy b) (S₁.onTy d) S₂ →
    UnifyRel (.pair a b) (.pair c d) (S₁ ++ S₂)

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

@[simp] theorem Subst.onTy_pair {S : Subst} {a b : Ty} :
    S.onTy (.pair a b) = .pair (S.onTy a) (S.onTy b) := Ty.substFvars_pair

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
  | _, _, _, .pair h₁ h₂ => by
    have e1 := UnifyRel.unifies h₁
    have e2 := UnifyRel.unifies h₂
    simp only [Unifies, Subst.onTy_append, Subst.onTy_pair] at e1 e2 ⊢
    rw [Ty.pair.injEq]
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
  | pair a b iha ihb => simp only [Ty.substFvar, Subst.onTy_pair, iha, ihb]
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
  | _, _, _, @UnifyRel.pair a b c d S₁ S₂ h₁ h₂, S', hS' => by
    simp only [Unifies, Subst.onTy_pair, Ty.pair.injEq] at hS'
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
  | _, _, _, .pair h₁ h₂, ha, hb => by
    cases ha with | pair ha_a ha_b => cases hb with | pair hb_c hb_d =>
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


/-! ## Algorithmic phase, step 2: the inference relation (Algorithm W, relational)

`Infer Φ ctx e Φ' S τ` is Algorithm W phrased as a *relation* (no function /
termination obligation yet — that is stage 3). It reads: starting with the
fresh-variable frontier `Φ` (every unification var in play is `< Φ`), expression
`e` infers type `τ` under the most-general substitution `S`, allocating fresh
vars up to the new frontier `Φ'`. `.fvar`s are the unification variables;
composition of the threaded substitutions is `++`.

This covers the full language (`primLit`, `pair`, `lambda`, `app`, `var`,
`letIn`, `fst`, `snd`, `ctor`, `match_`), bridging to `TypeOfHM` via soundness.

The plan: prove `Infer.sound` (algo type ⟹ declarative type, iterating
`typ_subst_preservation` and using `UnifyRel.isMGU`), then completeness. -/

/-- The `k` fresh unification-var names starting at frontier `Φ`. -/
def freshVars (Φ k : Nat) : List Nat := (List.range k).map (Φ + ·)

/-- Generalization candidates: the free unification vars of `τ` that are *not*
    fixed by `env` (these are the ones a `let` may generalize over). -/
def genVars (env : Env) (τ : Ty) : List Nat :=
  τ.freeVars.filter (fun x => !env.freeVars.contains x)

/-- The principal generalization of `τ` relative to `env`: the scheme quantifying
    over exactly the free vars of `τ` not fixed by `env` (`genVars`). Reuses the
    existing `Ty.closeOver` (`fvar` ↦ `bvar` by position), whose
    `closeOver_preserves_bvars` immediately gives `genScheme … |>.WF`. -/
def genScheme (env : Env) (τ : Ty) : PolyTy :=
  { paramCount := (genVars env τ).length, body := Ty.closeOver (genVars env τ) τ }

/-- A generalized scheme is well-formed when its body type is locally-closed —
    closing introduces only the `paramCount`-many fresh bound vars. -/
theorem genScheme_wf {env : Env} {τ : Ty} (hτ : τ.IsLC) : (genScheme env τ).WF :=
  Ty.closeOver_preserves_bvars hτ

/-- `freeVars` is always duplicate-free (it dedups). -/
theorem Ty.freeVars_nodup {τ : Ty} : τ.freeVars.Nodup := by
  cases τ with
  | prim => simp [Ty.freeVars]
  | bvar => simp [Ty.freeVars]
  | fvar => simp [Ty.freeVars]
  | pair a b => simp [Ty.freeVars, List.nodup_dedup]
  | arrow a b => simp [Ty.freeVars, List.nodup_dedup]
  | customTy nm tys =>
    cases tys with
    | nil => simp [Ty.freeVars, TyList.freeVars]
    | cons hd tl => simp [Ty.freeVars, TyList.freeVars, List.nodup_dedup]

/-- The generalization candidates are duplicate-free. -/
theorem genVars_nodup {env : Env} {τ : Ty} : (genVars env τ).Nodup :=
  Ty.freeVars_nodup.filter _

/-! Algorithm W as a substitution-threading relation, mutually defined with
    `InferBranches` (the `match_` branch threader). -/
mutual
inductive Infer : Nat → Ctx → Expr → Nat → Subst → Ty → Prop
  | primLitUnit {Φ ctx} :
    Infer Φ ctx (.primLit .unit) Φ [] (.prim .unit)
  | primLitInt {Φ ctx n} :
    Infer Φ ctx (.primLit (.int n)) Φ [] (.prim .int)
  | primLitNat {Φ ctx n} :
    Infer Φ ctx (.primLit (.nat n)) Φ [] (.prim .nat)
  | primLitBool {Φ ctx b} :
    Infer Φ ctx (.primLit (.bool b)) Φ [] (.prim .bool)
  | primLitStr {Φ ctx s} :
    Infer Φ ctx (.primLit (.str s)) Φ [] (.prim .str)
  | pair {Φ ctx a b Φ₁ Φ₂ S₁ S₂ τa τb} :
    Infer Φ ctx a Φ₁ S₁ τa →
    Infer Φ₁ (S₁.onCtx ctx) b Φ₂ S₂ τb →
    Infer Φ ctx (.pair a b) Φ₂ (S₁ ++ S₂) (.pair (S₂.onTy τa) τb)
  | lambda {Φ ctx body Φ' S τb} :
    Infer (Φ + 1) { ctx with env := PolyTy.mkTrivial (.fvar Φ) :: ctx.env } body Φ' S τb →
    Infer Φ ctx (.lambda body) Φ' S (.arrow (S.onTy (.fvar Φ)) τb)
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
        env := genScheme (S₁.onCtx ctx).env τ₁ :: (S₁.onCtx ctx).env }
      body Φ₂ S₂ τ₂ →
    Infer Φ ctx (.letIn rhs body) Φ₂ (S₁ ++ S₂) τ₂
  | fst {Φ ctx e Φ₁ S₁ S₂ τe} :
    Infer Φ ctx e Φ₁ S₁ τe →
    UnifyRel τe (.pair (.fvar Φ₁) (.fvar (Φ₁ + 1))) S₂ →
    Infer Φ ctx (.fst e) (Φ₁ + 2) (S₁ ++ S₂) (S₂.onTy (.fvar Φ₁))
  | snd {Φ ctx e Φ₁ S₁ S₂ τe} :
    Infer Φ ctx e Φ₁ S₁ τe →
    UnifyRel τe (.pair (.fvar Φ₁) (.fvar (Φ₁ + 1))) S₂ →
    Infer Φ ctx (.snd e) (Φ₁ + 2) (S₁ ++ S₂) (S₂.onTy (.fvar (Φ₁ + 1)))
  | match_ {Φ ctx scrut branches Φ₁ Φ₃ S₁ S₂ S₃ tyName arity τs} :
    Infer Φ ctx scrut Φ₁ S₁ τs →
    branches ≠ [] →
    UnifyRel τs (.customTy tyName ((freshVars Φ₁ arity).map (Ty.fvar ·))) S₂ →
    InferBranches (Φ₁ + arity + 1) (S₂.onCtx (S₁.onCtx ctx)) tyName
      (((freshVars Φ₁ arity).map (Ty.fvar ·)).map S₂.onTy) (S₂.onTy (.fvar (Φ₁ + arity)))
      branches Φ₃ S₃ →
    Infer Φ ctx (.match_ scrut branches) Φ₃ (S₁ ++ S₂ ++ S₃)
      (S₃.onTy (S₂.onTy (.fvar (Φ₁ + arity))))

/-- Threads inference through a `match_`'s branch list: a shared `tyName`/`tyArgs`
    (for instantiating each ctor's contents into monomorphic pattern bindings) and
    a running result type `ρ` that each branch's body type is unified against, with
    the substitution propagated to the next branch. -/
inductive InferBranches :
    Nat → Ctx → TyName → List Ty → Ty → List (MatchPattern × Expr) → Nat → Subst → Prop
  | nil {Φ ctx tyName tyArgs ρ} :
    InferBranches Φ ctx tyName tyArgs ρ [] Φ []
  | cons {Φ ctx tyName tyArgs ρ pat body rest ctor Φ₁ Φ₂ S₁ S₂ S₃ τb} :
    LookupList.get? ctx.ctors pat.ctor = some ctor →
    ctor.tyName = tyName →
    ctor.paramCount = tyArgs.length →
    pat.contents = ctor.contents.length →
    Infer Φ
      { ctx with env := (ctor.contents.map (Ty.openWith tyArgs)).map PolyTy.mkTrivial ++ ctx.env }
      body Φ₁ S₁ τb →
    UnifyRel τb (S₁.onTy ρ) S₂ →
    InferBranches Φ₁ (S₂.onCtx (S₁.onCtx ctx)) tyName
      (tyArgs.map (fun t => S₂.onTy (S₁.onTy t))) (S₂.onTy (S₁.onTy ρ)) rest Φ₂ S₃ →
    InferBranches Φ ctx tyName tyArgs ρ ((pat, body) :: rest) Φ₂ (S₁ ++ S₂ ++ S₃)
end


/-! ### Invariant layer for `Infer` soundness -/

/-! The fresh-variable frontier only ever grows (`Infer.frontier_le`). -/
mutual
theorem Infer.frontier_le {Φ ctx e Φ' S τ} (h : Infer Φ ctx e Φ' S τ) : Φ ≤ Φ' := by
  cases h with
  | primLitUnit => omega
  | primLitInt => omega
  | primLitNat => omega
  | primLitBool => omega
  | primLitStr => omega
  | pair ha hb => have := Infer.frontier_le ha; have := Infer.frontier_le hb; omega
  | lambda hbody => have := Infer.frontier_le hbody; omega
  | app hf harg _ => have := Infer.frontier_le hf; have := Infer.frontier_le harg; omega
  | var => omega
  | ctor => omega
  | letIn hrhs hbody => have := Infer.frontier_le hrhs; have := Infer.frontier_le hbody; omega
  | fst he _ => have := Infer.frontier_le he; omega
  | snd he _ => have := Infer.frontier_le he; omega
  | match_ hscrut _ _ hbr =>
    have := Infer.frontier_le hscrut; have := InferBranches.frontier_le hbr; omega
theorem InferBranches.frontier_le {Φ ctx tn ta ρ brs Φ' S} (h : InferBranches Φ ctx tn ta ρ brs Φ' S) :
    Φ ≤ Φ' := by
  cases h with
  | nil => omega
  | cons _ _ _ _ hbody _ hrest =>
    have := Infer.frontier_le hbody; have := InferBranches.frontier_le hrest; omega
end

/-- A context is well-formed when every scheme in its env is well-formed. -/
def CtxWF (ctx : Ctx) : Prop := ∀ M ∈ ctx.env, M.WF

@[simp] theorem freshVars_length (Φ k : Nat) : (freshVars Φ k).length = k := by
  simp [freshVars]

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
  | pair a b iha ihb => cases hty with | pair ha hb => exact .pair (iha ha) (ihb hb)
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
  | primLitBool => intro _; exact ⟨.prim, by simp⟩
  | primLitStr => intro _; exact ⟨.prim, by simp⟩
  | pair ha hb =>
    intro hctx
    obtain ⟨ha_lc, ha_s⟩ := Infer.lc ha hctx
    obtain ⟨hb_lc, hb_s⟩ := Infer.lc hb (Subst.onCtx_wf ha_s hctx)
    refine ⟨.pair (Subst.onTy_lc hb_s ha_lc) hb_lc, ?_⟩
    intro p hp; rw [List.mem_append] at hp
    rcases hp with hp | hp
    · exact ha_s p hp
    · exact hb_s p hp
  | lambda hbody =>
    intro hctx
    obtain ⟨hb_lc, hb_s⟩ := Infer.lc hbody (by
      intro M hM
      rcases List.mem_cons.mp hM with rfl | hM
      · exact ContainsBvarsUpTo.fvar
      · exact hctx M hM)
    exact ⟨.arrow (Subst.onTy_lc hb_s ContainsBvarsUpTo.fvar) hb_lc, hb_s⟩
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
  | fst he huni =>
    intro hctx
    obtain ⟨he_lc, he_s⟩ := Infer.lc he hctx
    have hs2 := huni.lc he_lc (.pair ContainsBvarsUpTo.fvar ContainsBvarsUpTo.fvar)
    refine ⟨Subst.onTy_lc hs2 ContainsBvarsUpTo.fvar, ?_⟩
    intro p hp; rw [List.mem_append] at hp
    rcases hp with hp | hp
    · exact he_s p hp
    · exact hs2 p hp
  | snd he huni =>
    intro hctx
    obtain ⟨he_lc, he_s⟩ := Infer.lc he hctx
    have hs2 := huni.lc he_lc (.pair ContainsBvarsUpTo.fvar ContainsBvarsUpTo.fvar)
    refine ⟨Subst.onTy_lc hs2 ContainsBvarsUpTo.fvar, ?_⟩
    intro p hp; rw [List.mem_append] at hp
    rcases hp with hp | hp
    · exact he_s p hp
    · exact hs2 p hp
  | match_ hscrut hne huni hbr =>
    intro hctx
    obtain ⟨hscrut_lc, hS₁⟩ := Infer.lc hscrut hctx
    have hS₂ := huni.lc hscrut_lc
      (.customTy (fun t ht => by obtain ⟨x, _, rfl⟩ := List.mem_map.mp ht; exact ContainsBvarsUpTo.fvar))
    obtain ⟨hρ_lc, hS₃⟩ := InferBranches.lc hbr
      (Subst.onCtx_wf hS₂ (Subst.onCtx_wf hS₁ hctx))
      (fun t ht => by
        obtain ⟨s, hs, rfl⟩ := List.mem_map.mp ht
        obtain ⟨x, _, rfl⟩ := List.mem_map.mp hs
        exact Subst.onTy_lc hS₂ ContainsBvarsUpTo.fvar)
      (Subst.onTy_lc hS₂ ContainsBvarsUpTo.fvar)
    refine ⟨hρ_lc, ?_⟩
    intro p hp; rw [List.mem_append, List.mem_append] at hp
    rcases hp with (hp | hp) | hp
    · exact hS₁ p hp
    · exact hS₂ p hp
    · exact hS₃ p hp
theorem InferBranches.lc {Φ ctx tn ta ρ brs Φ' S} (h : InferBranches Φ ctx tn ta ρ brs Φ' S)
    (hctx : CtxWF ctx) (hta : ∀ t ∈ ta, t.IsLC) (hρ : ρ.IsLC) :
    (S.onTy ρ).IsLC ∧ (∀ p ∈ S, p.2.IsLC) := by
  cases h with
  | nil => exact ⟨by simpa using hρ, by simp⟩
  | cons hlook htyName hpc hpc2 hbody huni hrest =>
    obtain ⟨hτb_lc, hS₁⟩ := Infer.lc hbody (branchBindings_wf hctx hta hpc)
    have hS₂ := huni.lc hτb_lc (Subst.onTy_lc hS₁ hρ)
    obtain ⟨hres, hS₃⟩ := InferBranches.lc hrest
      (Subst.onCtx_wf hS₂ (Subst.onCtx_wf hS₁ hctx))
      (fun t ht => by
        obtain ⟨t0, ht0, rfl⟩ := List.mem_map.mp ht
        exact Subst.onTy_lc hS₂ (Subst.onTy_lc hS₁ (hta t0 ht0)))
      (Subst.onTy_lc hS₂ (Subst.onTy_lc hS₁ hρ))
    refine ⟨?_, ?_⟩
    · rw [Subst.onTy_append, Subst.onTy_append]; exact hres
    · intro p hp; rw [List.mem_append, List.mem_append] at hp
      rcases hp with (hp | hp) | hp
      · exact hS₁ p hp
      · exact hS₂ p hp
      · exact hS₃ p hp
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
  | pair a b iha ihb => cases hty with | pair ha hb => exact .pair (iha ha) (ihb hb)
  | arrow a b iha ihb => cases hty with | arrow ha hb => exact .arrow (iha ha) (ihb hb)
  | customTy nm tys ih =>
    cases hty with
    | customTy hball =>
      simp only [Ty.openVars, Ty.instantiate, TyList.instantiate_eq_map]
      exact .customTy (List.forall₂_self_map (fun t ht => ih t ht (hball t ht)))


/-! ### Cofinite-generalization machinery for the `letIn` soundness case -/

/-- A generalization candidate is, by construction, not fixed by the env. -/
theorem genVars_not_mem {env : Env} {τ : Ty} {g : Nat}
    (h : g ∈ genVars env τ) : g ∉ env.freeVars := by
  simp only [genVars, List.mem_filter] at h
  simpa using h.2

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
@[simp] theorem Ty.openVars_pair {Xs : List Nat} {a b : Ty} :
    Ty.openVars Xs (.pair a b) = .pair (Ty.openVars Xs a) (Ty.openVars Xs b) := rfl
@[simp] theorem Ty.openVars_arrow {Xs : List Nat} {a b : Ty} :
    Ty.openVars Xs (.arrow a b) = .arrow (Ty.openVars Xs a) (Ty.openVars Xs b) := rfl

@[simp] theorem Ty.openVars_customTy {Xs : List Nat} {nm : TyName} {tys : List Ty} :
    Ty.openVars Xs (.customTy nm tys) = .customTy nm (tys.map (Ty.openVars Xs)) := by
  unfold Ty.openVars
  simp only [Ty.instantiate, TyList.instantiate_eq_map]

/-- Opening with fresh *names* `Xs` is opening with those names as `fvar` types. -/
theorem Ty.openVars_eq_openWith {Xs : List Nat} {ty : Ty} :
    Ty.openVars Xs ty = Ty.openWith (Xs.map (Ty.fvar ·)) ty := by
  unfold Ty.openVars Ty.openWith
  congr 1
  funext i
  rcases h : Xs[i]? with _ | x
  · simp [h]
  · simp [h, List.getElem?_map]

/-- `idxOf?` pinpoints the element: if it returns index `i`, then `l[i]? = a`. -/
private theorem List.getElem?_of_idxOf? {α : Type*} [BEq α] [LawfulBEq α]
    {l : List α} {a : α} {i : Nat} (h : l.idxOf? a = some i) : l[i]? = some a := by
  induction l generalizing i with
  | nil => simp [List.idxOf?_nil] at h
  | cons x xs ih =>
    rw [List.idxOf?_cons] at h
    split at h
    · rename_i hxa
      simp only [Option.some.injEq] at h
      subst h
      simp [eq_of_beq hxa]
    · obtain ⟨j, hj, rfl⟩ := Option.map_eq_some_iff.mp h
      simpa using ih hj

private theorem TyList.closeOver_eq_map (gs : List Nat) (tys : List Ty) :
    TyList.closeOver gs tys = tys.map (Ty.closeOver gs) := by
  induction tys with
  | nil => rfl
  | cons hd tl ih => simp [TyList.closeOver, ih]

/-- Closing over `gs` then opening with the *same* `gs` is the identity on an LC
    type (`gs` nodup ⇒ each closed var reopens to itself). -/
theorem Ty.openVars_closeOver_self {gs : List Nat} :
    ∀ {τ : Ty}, τ.IsLC → Ty.openVars gs (Ty.closeOver gs τ) = τ := by
  intro τ hτ
  induction τ using Ty.rec_strong with
  | prim p => rfl
  | bvar i => cases hτ with | bvar h => omega
  | fvar n =>
    rw [Ty.closeOver.eq_6]
    cases h_idx : gs.idxOf? n with
    | none => simp [Ty.openVars, Ty.instantiate]
    | some i =>
      have hgi : gs[i]? = some n := List.getElem?_of_idxOf? h_idx
      simp [Ty.openVars, Ty.instantiate, hgi]
  | pair a b iha ihb =>
    cases hτ with | pair ha hb => simp only [Ty.closeOver, Ty.openVars_pair, iha ha, ihb hb]
  | arrow a b iha ihb =>
    cases hτ with | arrow ha hb => simp only [Ty.closeOver, Ty.openVars_arrow, iha ha, ihb hb]
  | customTy nm tys ih =>
    cases hτ with
    | customTy hall =>
      simp only [Ty.closeOver, TyList.closeOver_eq_map, Ty.openVars_customTy, List.map_map]
      apply congrArg (Ty.customTy nm)
      conv_rhs => rw [← List.map_id tys]
      apply List.map_congr_left
      intro t ht
      exact ih t ht (hall t ht)

/-- The free vars of a list of `fvar`s are exactly the names. -/
theorem Ty.mem_freeVarsList_map_fvar {Xs : List Nat} {g : Nat} :
    g ∈ Ty.freeVarsList (Xs.map (Ty.fvar ·)) ↔ g ∈ Xs := by
  induction Xs with
  | nil => simp [Ty.freeVarsList]
  | cons x xs ih =>
    simp [Ty.freeVarsList, Ty.freeVars, ih]

/-- A closed-over var no longer occurs free. -/
theorem Ty.not_mem_closeOver_freeVars {gs : List Nat} {g : Nat} (hg : g ∈ gs) :
    ∀ {τ : Ty}, g ∉ (Ty.closeOver gs τ).freeVars := by
  intro τ
  induction τ using Ty.rec_strong with
  | prim p => simp [Ty.closeOver, Ty.freeVars]
  | bvar i => simp [Ty.closeOver, Ty.freeVars]
  | fvar n =>
    rw [Ty.closeOver.eq_6]
    cases h_idx : gs.idxOf? n with
    | none =>
      have hn : n ∉ gs := List.idxOf?_eq_none_iff.mp h_idx
      simp only [Ty.freeVars, List.mem_singleton]
      intro hgn; exact hn (hgn ▸ hg)
    | some i => simp [Ty.freeVars]
  | pair a b iha ihb => simp [Ty.closeOver, Ty.freeVars, List.mem_dedup, List.mem_append, iha, ihb]
  | arrow a b iha ihb => simp [Ty.closeOver, Ty.freeVars, List.mem_dedup, List.mem_append, iha, ihb]
  | customTy nm tys ih =>
    simp only [Ty.closeOver, Ty.freeVars, TyList.closeOver_eq_map]
    rw [TyList.not_mem_freeVars_iff]
    intro t' ht'
    obtain ⟨t, ht, rfl⟩ := List.mem_map.mp ht'
    exact ih t ht

/-- The full round-trip: closing over `gs` then opening with fresh `Xs` renames
    each `gs[i]` to `Xs[i]`. -/
theorem Ty.openVars_closeOver_rename {gs Xs : List Nat} {τ : Ty}
    (hτ : τ.IsLC) (h_gs_nodup : gs.Nodup) (h_len : Xs.length = gs.length)
    (h_disj : ∀ g ∈ gs, g ∉ Xs) :
    Ty.openVars Xs (Ty.closeOver gs τ)
      = Ty.substFvars (gs.zip (Xs.map (Ty.fvar ·))) τ := by
  rw [Ty.openVars_eq_openWith,
    Ty.openWith_eq_substFvars_openVars (Xs := gs) (Vs := Xs.map (Ty.fvar ·))
      ⟨by simp [h_len], fun V hV => by obtain ⟨x, _, rfl⟩ := List.mem_map.mp hV; exact .fvar⟩
      h_gs_nodup
      (fun g hg => Ty.not_mem_closeOver_freeVars hg)
      (fun g hg hc => h_disj g hg (Ty.mem_freeVarsList_map_fvar.mp hc)),
    Ty.openVars_closeOver_self hτ]

/-- The `letIn` soundness case, factored out (named binders avoid the
    inaccessible-name problem inside the `Infer.sound` induction). The cofinite
    premise is built by renaming the generalization candidates `genVars` to the
    fresh `Xs` (they are not fixed by the env, `genVars_not_mem`), then pushing
    `S₂` through (it avoids `Xs` by the cofinite `L`). -/
theorem Infer.sound_letIn {ctx : Ctx} {rhs body : Expr} {S₁ S₂ : Subst} {τ₁ τ₂ : Ty}
    (hrhs_ty : TypeOfHM (S₁.onCtx ctx) rhs τ₁) (hrhs_lc : τ₁.IsLC)
    (hbody_s : ∀ p ∈ S₂, p.2.IsLC)
    (hbody_ty : TypeOfHM (S₂.onCtx
      { (S₁.onCtx ctx) with
        env := genScheme (S₁.onCtx ctx).env τ₁ :: (S₁.onCtx ctx).env }) body τ₂) :
    TypeOfHM ((S₁ ++ S₂).onCtx ctx) (.letIn rhs body) τ₂ := by
  rw [Subst.onCtx_append]
  refine TypeOfHM.letIn (M := Subst.onPolyTy S₂ (genScheme (S₁.onCtx ctx).env τ₁))
    (L := genVars (S₁.onCtx ctx).env τ₁ ++ S₂.map Prod.fst)
    (Subst.onPolyTy_wf hbody_s (genScheme_wf hrhs_lc)) ?cofin rfl hbody_ty
  intro Xs hXfresh
  obtain ⟨hXlen, hXnodup, hXavoid⟩ := hXfresh
  have hgs_X : ∀ g ∈ genVars (S₁.onCtx ctx).env τ₁, g ∉ Xs :=
    fun g hg hc => hXavoid g hc (List.mem_append_left _ hg)
  have hX_S₂ : ∀ p ∈ S₂, p.1 ∉ Xs :=
    fun p hp hc => hXavoid p.1 hc (List.mem_append_right _ (List.mem_map.mpr ⟨p, hp, rfl⟩))
  have hrename : TypeOfHM (S₁.onCtx ctx) rhs
      (Ty.substFvars ((genVars (S₁.onCtx ctx).env τ₁).zip (Xs.map (Ty.fvar ·))) τ₁) := by
    refine TypeOfHM.typ_substs_preservation _ ?_ ?_ hrhs_ty
    · intro p hp; exact genVars_not_mem (List.of_mem_zip hp).1
    · intro p hp
      obtain ⟨x, _, hx⟩ := List.mem_map.mp (List.of_mem_zip hp).2
      exact hx ▸ ContainsBvarsUpTo.fvar
  rw [← Ty.openVars_closeOver_rename hrhs_lc genVars_nodup hXlen hgs_X] at hrename
  have hfin := TypeOfHM.onSubst S₂ hbody_s hrename
  rw [Subst.onTy_openVars hbody_s hX_S₂] at hfin
  exact hfin

/-- The `fst` soundness case, factored out (named binders avoid the
    inaccessible-name problem inside the `Infer.sound` induction). A unification
    step turns `e`'s type into a pair of the two fresh component vars; the result
    is the (substituted) first component. -/
theorem Infer.sound_fst {ctx : Ctx} {e : Expr} {S₁ S₂ : Subst}
    {Φ₁ : Nat} {τe : Ty}
    (he_ty : TypeOfHM (S₁.onCtx ctx) e τe)
    (huni : UnifyRel τe (.pair (.fvar Φ₁) (.fvar (Φ₁ + 1))) S₂)
    (hS₂ : ∀ p ∈ S₂, p.2.IsLC) :
    TypeOfHM ((S₁ ++ S₂).onCtx ctx) (.fst e) (S₂.onTy (.fvar Φ₁)) := by
  rw [Subst.onCtx_append]
  have h := TypeOfHM.onSubst S₂ hS₂ he_ty
  have hu := huni.unifies
  simp only [Unifies, Subst.onTy_pair] at hu
  rw [hu] at h
  exact .fst h

/-- The `snd` soundness case, mirror of `Infer.sound_fst`. -/
theorem Infer.sound_snd {ctx : Ctx} {e : Expr} {S₁ S₂ : Subst}
    {Φ₁ : Nat} {τe : Ty}
    (he_ty : TypeOfHM (S₁.onCtx ctx) e τe)
    (huni : UnifyRel τe (.pair (.fvar Φ₁) (.fvar (Φ₁ + 1))) S₂)
    (hS₂ : ∀ p ∈ S₂, p.2.IsLC) :
    TypeOfHM ((S₁ ++ S₂).onCtx ctx) (.snd e) (S₂.onTy (.fvar (Φ₁ + 1))) := by
  rw [Subst.onCtx_append]
  have h := TypeOfHM.onSubst S₂ hS₂ he_ty
  have hu := huni.unifies
  simp only [Unifies, Subst.onTy_pair] at hu
  rw [hu] at h
  exact .snd h

/-! Structural simp lemmas for `openWith` (the analogues for `openVars` already
    exist above, but `openWith` lacks them). -/
@[simp] private theorem Ty.openWith_prim {Vs : List Ty} {p : PrimTy} :
    Ty.openWith Vs (.prim p) = .prim p := rfl
@[simp] private theorem Ty.openWith_fvar {Vs : List Ty} {n : Nat} :
    Ty.openWith Vs (.fvar n) = .fvar n := rfl
@[simp] private theorem Ty.openWith_pair {Vs : List Ty} {a b : Ty} :
    Ty.openWith Vs (.pair a b) = .pair (Ty.openWith Vs a) (Ty.openWith Vs b) := rfl
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
  | pair a b iha ihb => cases hbv with | pair ha hb => exact .pair (iha ha) (ihb hb)
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
  | pair a b iha ihb => simp only [Ty.instantiate, Subst.onTy_pair, iha, ihb]
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

/-! Soundness of `Infer` against the declarative `TypeOfHM`: applying the
    inferred substitution to the context yields a declarative typing. -/
mutual
theorem Infer.sound {Φ ctx e Φ' S τ} (h : Infer Φ ctx e Φ' S τ) :
    CtxWF ctx → TypeOfHM (S.onCtx ctx) e τ := by
  cases h with
  | primLitUnit => intro _; simp only [Subst.onCtx_nil]; exact .primLitUnit
  | primLitInt => intro _; simp only [Subst.onCtx_nil]; exact .primLitInt
  | primLitNat => intro _; simp only [Subst.onCtx_nil]; exact .primLitNat
  | primLitBool => intro _; simp only [Subst.onCtx_nil]; exact .primLitBool
  | primLitStr => intro _; simp only [Subst.onCtx_nil]; exact .primLitStr
  | pair ha hb =>
    intro hctx
    have ha_s := (Infer.lc ha hctx).2
    have hb_s := (Infer.lc hb (Subst.onCtx_wf ha_s hctx)).2
    have ha_ty := TypeOfHM.onSubst _ hb_s (Infer.sound ha hctx)
    rw [Subst.onCtx_append]
    exact .pair ha_ty (Infer.sound hb (Subst.onCtx_wf ha_s hctx))
  | lambda hbody =>
    intro hctx
    exact TypeOfHM.lambda
      (Subst.onTy_lc (Infer.lc hbody (by
        intro M hM; rcases List.mem_cons.mp hM with rfl | hM
        · exact ContainsBvarsUpTo.fvar
        · exact hctx M hM)).2 ContainsBvarsUpTo.fvar)
      rfl
      (Infer.sound hbody (by
        intro M hM; rcases List.mem_cons.mp hM with rfl | hM
        · exact ContainsBvarsUpTo.fvar
        · exact hctx M hM))
  | app hf harg huni =>
    intro hctx
    obtain ⟨hf_lc, hf_s⟩ := Infer.lc hf hctx
    have hctx1 := Subst.onCtx_wf hf_s hctx
    obtain ⟨harg_lc, harg_s⟩ := Infer.lc harg hctx1
    have hs3 := huni.lc (Subst.onTy_lc harg_s hf_lc) (.arrow harg_lc ContainsBvarsUpTo.fvar)
    have f2 := TypeOfHM.onSubst _ hs3 (TypeOfHM.onSubst _ harg_s (Infer.sound hf hctx))
    have a1 := TypeOfHM.onSubst _ hs3 (Infer.sound harg hctx1)
    have hueq := huni.unifies
    simp only [Unifies, Subst.onTy_arrow] at hueq
    rw [hueq] at f2
    rw [Subst.onCtx_append, Subst.onCtx_append]
    exact .app f2 a1
  | var hlook =>
    intro hctx
    simp only [Subst.onCtx_nil]
    refine TypeOfHM.var hlook (fun tyArg ht => ?_)
      (InstantiatesBy.openVars (hctx _ (List.mem_of_getElem? hlook)) (by simp))
    obtain ⟨x, _, rfl⟩ := List.mem_map.mp ht
    exact .fvar
  | ctor hlook =>
    intro _
    simp only [Subst.onCtx_nil]
    refine TypeOfHM.ctor hlook (fun tyArg ht => ?_)
      (InstantiatesBy.openVars (Ctor.toTy_wf _) (by simp [Ctor.toTy]))
    obtain ⟨x, _, rfl⟩ := List.mem_map.mp ht
    exact .fvar
  | letIn hrhs hbody =>
    intro hctx
    obtain ⟨hrhs_lc, hrhs_s⟩ := Infer.lc hrhs hctx
    exact Infer.sound_letIn (Infer.sound hrhs hctx) hrhs_lc
      (Infer.lc hbody (by
        intro M hM; rcases List.mem_cons.mp hM with rfl | hM
        · exact genScheme_wf hrhs_lc
        · exact (Subst.onCtx_wf hrhs_s hctx) M hM)).2
      (Infer.sound hbody (by
        intro M hM; rcases List.mem_cons.mp hM with rfl | hM
        · exact genScheme_wf hrhs_lc
        · exact (Subst.onCtx_wf hrhs_s hctx) M hM))
  | fst he huni =>
    intro hctx
    obtain ⟨he_lc, _⟩ := Infer.lc he hctx
    have hs2 := huni.lc he_lc (.pair ContainsBvarsUpTo.fvar ContainsBvarsUpTo.fvar)
    exact Infer.sound_fst (Infer.sound he hctx) huni hs2
  | snd he huni =>
    intro hctx
    obtain ⟨he_lc, _⟩ := Infer.lc he hctx
    have hs2 := huni.lc he_lc (.pair ContainsBvarsUpTo.fvar ContainsBvarsUpTo.fvar)
    exact Infer.sound_snd (Infer.sound he hctx) huni hs2
  | match_ hscrut hne huni hbr =>
    intro hctx
    expose_names
    rw [Subst.onCtx_append, Subst.onCtx_append]
    obtain ⟨hscrut_lc, hS₁⟩ := Infer.lc hscrut hctx
    have hS₂ := huni.lc hscrut_lc
      (.customTy (fun t ht => by obtain ⟨x, _, rfl⟩ := List.mem_map.mp ht; exact ContainsBvarsUpTo.fvar))
    have hctxbr := Subst.onCtx_wf hS₂ (Subst.onCtx_wf hS₁ hctx)
    have htabr : ∀ t ∈ (((freshVars Φ₁ arity).map (Ty.fvar ·)).map S₂.onTy), t.IsLC := by
      intro t ht
      obtain ⟨s, hs, rfl⟩ := List.mem_map.mp ht
      obtain ⟨x, _, rfl⟩ := List.mem_map.mp hs
      exact Subst.onTy_lc hS₂ ContainsBvarsUpTo.fvar
    have hρbr : (S₂.onTy (.fvar (Φ₁ + arity))).IsLC := Subst.onTy_lc hS₂ ContainsBvarsUpTo.fvar
    have hS₃ := (InferBranches.lc hbr hctxbr htabr hρbr).2
    have hscrut_decl : TypeOfHM (S₃.onCtx (S₂.onCtx (S₁.onCtx ctx))) scrut
        (.customTy tyName ((((freshVars Φ₁ arity).map (Ty.fvar ·)).map S₂.onTy).map S₃.onTy)) := by
      have h0 := TypeOfHM.onSubst S₃ hS₃ (TypeOfHM.onSubst S₂ hS₂ (Infer.sound hscrut hctx))
      have hu := huni.unifies
      simp only [Unifies] at hu
      rw [hu] at h0
      simp only [Subst.onTy_customTy] at h0
      exact h0
    refine TypeOfHM.match_ hscrut_decl hne ?_
    exact InferBranches.sound hbr hctxbr htabr hρbr
theorem InferBranches.sound {Φ ctx tn ta ρ brs Φ' S}
    (h : InferBranches Φ ctx tn ta ρ brs Φ' S)
    (hctx : CtxWF ctx) (hta : ∀ t ∈ ta, t.IsLC) (hρ : ρ.IsLC) :
    ∀ br ∈ brs, TypeOfMatchBranch (S.onCtx ctx) br tn (ta.map S.onTy) (S.onTy ρ) := by
  cases h with
  | nil => intro br hbr; simp at hbr
  | cons hlook htyName hpc hpc2 hbody huni hrest =>
    expose_names
    have hbodyWF := branchBindings_wf hctx hta hpc
    obtain ⟨hτb_lc, hS₁⟩ := Infer.lc hbody hbodyWF
    have hS₂ := huni.lc hτb_lc (Subst.onTy_lc hS₁ hρ)
    have hS₃ := (InferBranches.lc hrest
      (Subst.onCtx_wf hS₂ (Subst.onCtx_wf hS₁ hctx))
      (fun t ht => by
        obtain ⟨t0, ht0, rfl⟩ := List.mem_map.mp ht
        exact Subst.onTy_lc hS₂ (Subst.onTy_lc hS₁ (hta t0 ht0)))
      (Subst.onTy_lc hS₂ (Subst.onTy_lc hS₁ hρ))).2
    have hS : ∀ p ∈ S₁ ++ S₂ ++ S₃, p.2.IsLC := by
      intro p hp; rw [List.mem_append, List.mem_append] at hp
      rcases hp with (hp | hp) | hp
      · exact hS₁ p hp
      · exact hS₂ p hp
      · exact hS₃ p hp
    intro br hbr
    rcases List.mem_cons.mp hbr with rfl | hbr_rest
    · have h0 := Infer.sound hbody hbodyWF
      have h1 := TypeOfHM.onSubst S₃ hS₃ (TypeOfHM.onSubst S₂ hS₂ h0)
      have huni_eq := huni.unifies
      simp only [Unifies] at huni_eq
      rw [huni_eq] at h1
      refine TypeOfMatchBranch.mk hlook htyName ?_ hpc2
        (List.forall₂_self_map (fun c hc => InstantiatesBy.openWith
          (n := (ta.map (S₁ ++ S₂ ++ S₃).onTy).length)
          (by rw [List.length_map]; exact hpc ▸ ctor.bound c hc)
          (le_refl _)))
        rfl rfl ?_
      · rw [List.length_map]; exact hpc
      · rw [(Subst.onCtx_branchBindings hS).symm,
            Subst.onCtx_append, Subst.onCtx_append, Subst.onTy_append, Subst.onTy_append]
        exact h1
    · have hta_eq : ta.map (S₁ ++ S₂ ++ S₃).onTy
          = (ta.map (fun t => S₂.onTy (S₁.onTy t))).map S₃.onTy := by
        rw [List.map_map]
        apply List.map_congr_left
        intro t _
        simp only [Subst.onTy_append, Function.comp_apply]
      rw [Subst.onCtx_append, Subst.onCtx_append, Subst.onTy_append, Subst.onTy_append, hta_eq]
      exact InferBranches.sound hrest
        (Subst.onCtx_wf hS₂ (Subst.onCtx_wf hS₁ hctx))
        (fun t ht => by
          obtain ⟨t0, ht0, rfl⟩ := List.mem_map.mp ht
          exact Subst.onTy_lc hS₂ (Subst.onTy_lc hS₁ (hta t0 ht0)))
        (Subst.onTy_lc hS₂ (Subst.onTy_lc hS₁ hρ))
        br hbr_rest
end


/-! ## Algorithmic phase, step 2b: completeness (principality) scaffolding

Foundations for `Infer.complete`, independent of how the residual-substitution
obstruction is resolved. -/

/-- All free type vars of `τ` are below `Φ`. The `fvar` analogue of
    `ContainsBvarsUpTo`; clean to push through substitution. -/
inductive Ty.BelowFvars (Φ : Nat) : Ty → Prop
  | prim : Ty.BelowFvars Φ (.prim p)
  | pair : Ty.BelowFvars Φ a → Ty.BelowFvars Φ b → Ty.BelowFvars Φ (.pair a b)
  | arrow : Ty.BelowFvars Φ a → Ty.BelowFvars Φ b → Ty.BelowFvars Φ (.arrow a b)
  | bvar : Ty.BelowFvars Φ (.bvar i)
  | fvar : i < Φ → Ty.BelowFvars Φ (.fvar i)
  | customTy : (∀ t ∈ tys, Ty.BelowFvars Φ t) → Ty.BelowFvars Φ (.customTy nm tys)

theorem Ty.BelowFvars.mono {Φ Φ' : Nat} {τ : Ty} (hle : Φ ≤ Φ')
    (h : Ty.BelowFvars Φ τ) : Ty.BelowFvars Φ' τ := by
  induction h with
  | prim => exact .prim
  | pair _ _ iha ihb => exact .pair iha ihb
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
  | pair a b iha ihb => cases h with | pair ha hb => exact .pair (iha ha) (ihb hb)
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
  | pair _ _ iha ihb =>
    intro v hv; simp only [Ty.freeVars, List.mem_dedup, List.mem_append] at hv
    rcases hv with h | h
    · exact iha v h
    · exact ihb v h
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

/-- A whole substitution preserves context-below (with frontier growth). -/
theorem Subst.onCtx_below {Φ Φ' : Nat} {S : Subst} {ctx : Ctx}
    (hS : ∀ p ∈ S, Ty.BelowFvars Φ' p.2) (hle : Φ ≤ Φ') (hb : CtxBelow Φ ctx) :
    CtxBelow Φ' (S.onCtx ctx) := by
  intro M hM
  simp only [Subst.onCtx, Subst.onEnv] at hM
  obtain ⟨M0, hM0, rfl⟩ := List.mem_map.mp hM
  exact Subst.onTy_belowFvars hS ((hb M0 hM0).mono hle)

/-- The `k` fresh names allocated from frontier `Φ` are all `< Φ + k`. -/
theorem freshVars_lt {Φ k : Nat} : ∀ x ∈ freshVars Φ k, x < Φ + k := by
  intro x hx
  simp only [freshVars, List.mem_map, List.mem_range] at hx
  obtain ⟨i, hi, rfl⟩ := hx
  omega

/-- Opening a below-`Φ` type with fresh names all `< Φ` stays below-`Φ`. -/
theorem Ty.openVars_belowFvars {Φ : Nat} {Xs : List Nat} {τ : Ty}
    (hτ : Ty.BelowFvars Φ τ) (hXs : ∀ x ∈ Xs, x < Φ) :
    Ty.BelowFvars Φ (Ty.openVars Xs τ) := by
  induction τ using Ty.rec_strong with
  | prim p => exact .prim
  | pair a b iha ihb => cases hτ with | pair ha hb => exact .pair (iha ha) (ihb hb)
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
  | pair _ _ iha ihb => exact .pair iha ihb
  | arrow _ _ iha ihb => exact .arrow iha ihb
  | bvar => exact .bvar
  | customTy _ ih => exact .customTy (fun t ht => ih t ht)

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
  | pair a b iha ihb => cases hX with | pair ha hb => exact .pair (iha ha) (ihb hb)
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
  | _, _, _, .pair h₁ h₂, ha, hb => by
    cases ha with | pair ha_a ha_b => cases hb with | pair hb_c hb_d =>
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
    rw [Ty.closeOver.eq_6]
    cases h_idx : gs.idxOf? n with
    | none => cases h with | fvar hlt => exact .fvar hlt
    | some i => exact .bvar
  | pair a b iha ihb => cases h with | pair ha hb => exact .pair (iha ha) (ihb hb)
  | arrow a b iha ihb => cases h with | arrow ha hb => exact .arrow (iha ha) (ihb hb)
  | customTy nm tys ih =>
    cases h with
    | customTy hall =>
      simp only [Ty.closeOver, TyList.closeOver_eq_map]
      apply Ty.BelowFvars.customTy
      intro t' ht'; obtain ⟨t, ht, rfl⟩ := List.mem_map.mp ht'
      exact ih t ht (hall t ht)

/-! Regularity: any declaratively-typed term has a locally-closed type. (Each
    rule produces an LC type; `var`/`ctor` via `InstantiatesBy.preserves_bvars`
    on LC `tyArgs`, `lambda` via the LC param premise, the rest by induction.) -/
mutual
theorem TypeOfHM.regular : {ctx : Ctx} → {e : Expr} → {τ : Ty} →
    TypeOfHM ctx e τ → τ.IsLC
  | _, _, _, .primLitUnit => .prim
  | _, _, _, .primLitInt => .prim
  | _, _, _, .primLitNat => .prim
  | _, _, _, .primLitBool => .prim
  | _, _, _, .primLitStr => .prim
  | _, _, _, .pair ha hb => .pair (TypeOfHM.regular ha) (TypeOfHM.regular hb)
  | _, _, _, .lambda hpc _ hbody => .arrow hpc (TypeOfHM.regular hbody)
  | _, _, _, .app hf _ => by
    have := TypeOfHM.regular hf; cases this with | arrow _ hret => exact hret
  | _, _, _, .letIn _ _ _ hbody => TypeOfHM.regular hbody
  | _, _, _, .fst he => by
    have := TypeOfHM.regular he; cases this with | pair hf _ => exact hf
  | _, _, _, .snd he => by
    have := TypeOfHM.regular he; cases this with | pair _ hs => exact hs
  | _, _, _, .var _ htyargs hinst => InstantiatesBy.preserves_bvars htyargs hinst
  | _, _, _, .ctor _ htyargs hinst => InstantiatesBy.preserves_bvars htyargs hinst
  | _, _, _, @TypeOfHM.match_ _ _ _ _ branches _ hscrut hne hbrs => by
    obtain ⟨hd, tl, rfl⟩ := List.exists_cons_of_ne_nil hne
    exact TypeOfMatchBranch.regular (hbrs hd (List.mem_cons_self ..))

theorem TypeOfMatchBranch.regular : {ctx : Ctx} → {br : MatchPattern × Expr} →
    {tn : TyName} → {ta : List Ty} → {rt : Ty} →
    TypeOfMatchBranch ctx br tn ta rt → rt.IsLC
  | _, _, _, _, _, .mk _ _ _ _ _ _ _ hbody => TypeOfHM.regular hbody
end

/-! Frontier invariant (`Infer.belowFvars`): from a context whose schemes are below
    the input frontier `Φ`, `Infer` yields a type and a substitution whose
    replacements are all below the *output* frontier `Φ'` (so `mono` everything up
    to `Φ'`). (Named `belowFvars` rather than `below`, since `Infer.below` is
    reserved by Lean's auto-generated recursor for the `Infer` inductive.) -/
mutual
theorem Infer.belowFvars {Φ ctx e Φ' S τ} (h : Infer Φ ctx e Φ' S τ) :
    CtxBelow Φ ctx → Ty.BelowFvars Φ' τ ∧ (∀ p ∈ S, Ty.BelowFvars Φ' p.2) := by
  cases h with
  | primLitUnit => intro _; exact ⟨.prim, by simp⟩
  | primLitInt => intro _; exact ⟨.prim, by simp⟩
  | primLitNat => intro _; exact ⟨.prim, by simp⟩
  | primLitBool => intro _; exact ⟨.prim, by simp⟩
  | primLitStr => intro _; exact ⟨.prim, by simp⟩
  | pair ha hb =>
    intro hctx
    obtain ⟨ha_τ, ha_s⟩ := Infer.belowFvars ha hctx
    have hctx1 := Subst.onCtx_below ha_s (Infer.frontier_le ha) hctx
    obtain ⟨hb_τ, hb_s⟩ := Infer.belowFvars hb hctx1
    have hle := Infer.frontier_le hb
    refine ⟨.pair (Subst.onTy_belowFvars hb_s (ha_τ.mono hle)) hb_τ, ?_⟩
    intro p hp; rw [List.mem_append] at hp
    rcases hp with hp | hp
    · exact (ha_s p hp).mono hle
    · exact hb_s p hp
  | lambda hbody =>
    intro hctx
    obtain ⟨hb_τ, hb_s⟩ := Infer.belowFvars hbody (by
      intro M hM
      rcases List.mem_cons.mp hM with rfl | hM
      · exact .fvar (by omega)
      · exact (hctx M hM).mono (by omega))
    refine ⟨.arrow (Subst.onTy_belowFvars hb_s (.fvar ?_)) hb_τ, hb_s⟩
    have := Infer.frontier_le hbody
    omega
  | app hf harg huni =>
    intro hctx
    obtain ⟨hf_τ, hf_s⟩ := Infer.belowFvars hf hctx
    have hctx1 := Subst.onCtx_below hf_s (Infer.frontier_le hf) hctx
    obtain ⟨harg_τ, harg_s⟩ := Infer.belowFvars harg hctx1
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
    intro hctx
    refine ⟨?_, by simp⟩
    exact Ty.openVars_belowFvars ((hctx _ (List.mem_of_getElem? hlook)).mono (by omega))
      (fun x hx => by have := freshVars_lt x hx; omega)
  | ctor hlook =>
    intro _
    refine ⟨?_, by simp⟩
    refine Ty.openVars_belowFvars
      (Ty.BelowFvars.of_noFreeVars (Ctor.toTy_body_noFreeVars _))
      (fun x hx => by have := freshVars_lt x hx; omega)
  | letIn hrhs hbody =>
    intro hctx
    obtain ⟨hr_τ, hr_s⟩ := Infer.belowFvars hrhs hctx
    have hctx1 := Subst.onCtx_below hr_s (Infer.frontier_le hrhs) hctx
    obtain ⟨hb_τ, hb_s⟩ := Infer.belowFvars hbody (by
      intro M hM
      rcases List.mem_cons.mp hM with rfl | hM
      · exact hr_τ.closeOver
      · exact hctx1 M hM)
    refine ⟨hb_τ, ?_⟩
    intro p hp; rw [List.mem_append] at hp
    rcases hp with hp | hp
    · exact (hr_s p hp).mono (Infer.frontier_le hbody)
    · exact hb_s p hp
  | fst he huni =>
    intro hctx
    expose_names
    obtain ⟨he_τ, he_s⟩ := Infer.belowFvars he hctx
    have hel := Infer.frontier_le he
    have hs2_below : ∀ p ∈ S₂, Ty.BelowFvars (Φ₁ + 2) p.2 :=
      UnifyRel.belowFvars huni (he_τ.mono (by omega))
        (.pair (.fvar (by omega)) (.fvar (by omega)))
    refine ⟨Subst.onTy_belowFvars hs2_below (.fvar (by omega)), ?_⟩
    intro p hp; rw [List.mem_append] at hp
    rcases hp with hp | hp
    · exact (he_s p hp).mono (by omega)
    · exact hs2_below p hp
  | snd he huni =>
    intro hctx
    expose_names
    obtain ⟨he_τ, he_s⟩ := Infer.belowFvars he hctx
    have hel := Infer.frontier_le he
    have hs2_below : ∀ p ∈ S₂, Ty.BelowFvars (Φ₁ + 2) p.2 :=
      UnifyRel.belowFvars huni (he_τ.mono (by omega))
        (.pair (.fvar (by omega)) (.fvar (by omega)))
    refine ⟨Subst.onTy_belowFvars hs2_below (.fvar (by omega)), ?_⟩
    intro p hp; rw [List.mem_append] at hp
    rcases hp with hp | hp
    · exact (he_s p hp).mono (by omega)
    · exact hs2_below p hp
  | match_ hscrut hne huni hbr =>
    intro hctx
    expose_names
    obtain ⟨hscrut_τ, hS₁⟩ := Infer.belowFvars hscrut hctx
    have hle1 := Infer.frontier_le hscrut
    have hbrle := InferBranches.frontier_le hbr
    have hctx1 := Subst.onCtx_below hS₁ hle1 hctx
    have hS₂ : ∀ p ∈ S₂, Ty.BelowFvars (Φ₁ + arity + 1) p.2 :=
      UnifyRel.belowFvars huni (hscrut_τ.mono (by omega))
        (.customTy (fun t ht => by
          obtain ⟨x, hx, rfl⟩ := List.mem_map.mp ht
          exact .fvar (by have := freshVars_lt x hx; omega)))
    obtain ⟨hρ_below, hS₃⟩ := InferBranches.belowFvars hbr
      (Subst.onCtx_below hS₂ (by omega) hctx1)
      (fun t ht => by
        obtain ⟨s, hs, rfl⟩ := List.mem_map.mp ht
        obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hs
        exact Subst.onTy_belowFvars hS₂ (.fvar (by have := freshVars_lt x hx; omega)))
      (Subst.onTy_belowFvars hS₂ (.fvar (by omega)))
    refine ⟨hρ_below, ?_⟩
    intro p hp; rw [List.mem_append, List.mem_append] at hp
    rcases hp with (hp | hp) | hp
    · exact (hS₁ p hp).mono (by omega)
    · exact (hS₂ p hp).mono (by omega)
    · exact hS₃ p hp
theorem InferBranches.belowFvars {Φ ctx tn ta ρ brs Φ' S}
    (h : InferBranches Φ ctx tn ta ρ brs Φ' S)
    (hctx : CtxBelow Φ ctx) (hta : ∀ t ∈ ta, Ty.BelowFvars Φ t) (hρ : Ty.BelowFvars Φ ρ) :
    Ty.BelowFvars Φ' (S.onTy ρ) ∧ (∀ p ∈ S, Ty.BelowFvars Φ' p.2) := by
  cases h with
  | nil => exact ⟨by simpa using hρ, by simp⟩
  | cons hlook htyName hpc hpc2 hbody huni hrest =>
    obtain ⟨hτb, hS₁⟩ := Infer.belowFvars hbody (branchBindings_below hctx hta)
    have hle1 := Infer.frontier_le hbody
    have hS₁ρ := Subst.onTy_belowFvars hS₁ (hρ.mono hle1)
    have hS₂ := UnifyRel.belowFvars huni hτb hS₁ρ
    have hctx1 := Subst.onCtx_below hS₂ (le_refl _) (Subst.onCtx_below hS₁ hle1 hctx)
    obtain ⟨hres, hS₃⟩ := InferBranches.belowFvars hrest hctx1
      (fun t ht => by
        obtain ⟨t0, ht0, rfl⟩ := List.mem_map.mp ht
        exact Subst.onTy_belowFvars hS₂ (Subst.onTy_belowFvars hS₁ ((hta t0 ht0).mono hle1)))
      (Subst.onTy_belowFvars hS₂ (Subst.onTy_belowFvars hS₁ (hρ.mono hle1)))
    have hbrle := InferBranches.frontier_le hrest
    refine ⟨?_, ?_⟩
    · rw [Subst.onTy_append, Subst.onTy_append]; exact hres
    · intro p hp; rw [List.mem_append, List.mem_append] at hp
      rcases hp with (hp | hp) | hp
      · exact (hS₁ p hp).mono (by omega)
      · exact (hS₂ p hp).mono (by omega)
      · exact hS₃ p hp
end


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
  | pair a b iha ihb => cases hτ with | pair ha hb => simp only [Subst.onTy_pair, iha ha, ihb hb]
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

/-- `S` and `T` agree (act identically on every `fvar`) below frontier `Φ`. This
    is the "`S₀ = R ∘ S` below `Φ`" agreement clause threaded through the
    principality proofs; a reducible abbreviation so it is defeq to the raw `∀`. -/
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

/-- The principality property at `e`: for *any* declarative typing of `e` under
    an LC specialization `S₀` of a WF, frontier-bounded context, `Infer`
    succeeds with `(S, τ)` and the typing factors through it via an LC residual
    `R` (`S₀ = R ∘ S` below the frontier, `τ₀ = R.onTy τ`). -/
def Infer.CompleteAt (e : Expr) : Prop :=
  ∀ {Φ : Nat} {ctx : Ctx} {S₀ : Subst} {τ₀ : Ty},
    CtxWF ctx → CtxBelow Φ ctx → (∀ p ∈ S₀, p.2.IsLC) →
    TypeOfHM (S₀.onCtx ctx) e τ₀ →
    ∃ Φ' S τ R,
      Infer Φ ctx e Φ' S τ ∧
      Subst.AgreesBelow Φ S₀ (S ++ R) ∧
      τ₀ = R.onTy τ ∧
      (∀ p ∈ R, p.2.IsLC)

/-- Principality, primitive-literal case: `Infer` returns the literal's type
    with the empty substitution; the residual is `S₀` unchanged. -/
theorem Infer.complete_prim {p : PrimLitExpr} : Infer.CompleteAt (.primLit p) := by
  intro Φ ctx S₀ τ₀ _ _ hS₀ hty
  cases hty with
  | primLitUnit => exact ⟨Φ, [], _, S₀, .primLitUnit, fun v _ => by rw [List.nil_append], by simp, hS₀⟩
  | primLitInt  => exact ⟨Φ, [], _, S₀, .primLitInt,  fun v _ => by rw [List.nil_append], by simp, hS₀⟩
  | primLitNat  => exact ⟨Φ, [], _, S₀, .primLitNat,  fun v _ => by rw [List.nil_append], by simp, hS₀⟩
  | primLitBool => exact ⟨Φ, [], _, S₀, .primLitBool, fun v _ => by rw [List.nil_append], by simp, hS₀⟩
  | primLitStr  => exact ⟨Φ, [], _, S₀, .primLitStr,  fun v _ => by rw [List.nil_append], by simp, hS₀⟩

/-- Principality, pair case. No fresh variables are introduced here, so no
    renaming is needed: the residual `R₁` from the first component becomes the
    specialization for the second (it reproduces `S₀` on `ctx` by the agreement
    clause + `onCtx_congr`), and the second residual `R₂` serves as the pair's
    residual. The first component's type is transported across the agreement via
    `onTy_congr` (it is below the intermediate frontier `Φ₁`). -/
theorem Infer.complete_pair {a b : Expr}
    (iha : Infer.CompleteAt a) (ihb : Infer.CompleteAt b) :
    Infer.CompleteAt (.pair a b) := by
  intro Φ ctx S₀ τ₀ hwf hbelow hS₀ hty
  cases hty with
  | pair hta htb =>
    obtain ⟨Φ₁, S₁, τa, R₁, hinfa, haga, htya, hR₁⟩ := iha hwf hbelow hS₀ hta
    have hS₁ : ∀ p ∈ S₁, p.2.IsLC := (Infer.lc hinfa hwf).2
    have hle : Φ ≤ Φ₁ := Infer.frontier_le hinfa
    have hbelowτa : Ty.BelowFvars Φ₁ τa := (Infer.belowFvars hinfa hbelow).1
    have hbelowS₁ : ∀ p ∈ S₁, Ty.BelowFvars Φ₁ p.2 := (Infer.belowFvars hinfa hbelow).2
    have hwf₁ : CtxWF (S₁.onCtx ctx) := Subst.onCtx_wf hS₁ hwf
    have hbelow₁ : CtxBelow Φ₁ (S₁.onCtx ctx) := Subst.onCtx_below hbelowS₁ hle hbelow
    have hctx_eq : R₁.onCtx (S₁.onCtx ctx) = S₀.onCtx ctx := by
      rw [← Subst.onCtx_append]
      exact Subst.onCtx_congr (fun v hv => (haga v hv).symm) hbelow
    have htb' : TypeOfHM (R₁.onCtx (S₁.onCtx ctx)) b _ := hctx_eq ▸ htb
    obtain ⟨Φ₂, S₂, τb, R₂, hinfb, hagb, htyb, hR₂⟩ := ihb hwf₁ hbelow₁ hR₁ htb'
    refine ⟨Φ₂, S₁ ++ S₂, .pair (S₂.onTy τa) τb, R₂, .pair hinfa hinfb, ?_, ?_, hR₂⟩
    · exact Subst.AgreesBelow.trans_append hle haga hbelowS₁ hagb
    · rw [Subst.onTy_pair]
      refine congrArg₂ Ty.pair ?_ htyb
      rw [htya, ← Subst.onTy_append]
      exact Subst.onTy_congr hagb hbelowτa


/-! ### Injective renaming of free type variables (principality binder cases)

The list-substitution residual hits an obstruction at fresh binders: a clean
override of `S₀` mapping the fresh var to the declarative type is unrealisable as
a `List` once the fresh var occurs in `S₀`'s range (or the declarative
instantiation types). We dodge it by α-renaming the declarative derivation with a
*swap* `Φ ↔ W` (`W` fresh) so the clash disappears, then mapping the residual
back. `Ty.rename` applies a variable relabelling; the swap is realised as the
3-element list `swapSubst` (with a fresh intermediate `c`) so the existing
`TypeOfHM.onSubst` carries the renaming through the derivation. -/

mutual
/-- Relabel every free type variable by `f`. An α-renaming when `f` is injective. -/
def Ty.rename (f : Nat → Nat) : Ty → Ty
  | .prim p          => .prim p
  | .pair a b        => .pair (a.rename f) (b.rename f)
  | .arrow a b       => .arrow (a.rename f) (b.rename f)
  | .bvar i          => .bvar i
  | .fvar n          => .fvar (f n)
  | .customTy nm tys => .customTy nm (TyList.rename f tys)

private def TyList.rename (f : Nat → Nat) : List Ty → List Ty
  | []       => []
  | hd :: tl => hd.rename f :: TyList.rename f tl
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
@[simp] theorem Ty.rename_pair {f : Nat → Nat} {a b : Ty} :
    Ty.rename f (.pair a b) = .pair (Ty.rename f a) (Ty.rename f b) := rfl
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
  | pair a b ih_a ih_b =>
    simp only [Ty.rename_pair, Ty.pair.injEq]
    refine ⟨ih_a (fun v hv => h v ?_), ih_b (fun v hv => h v ?_)⟩
    · simp only [Ty.freeVars, List.mem_dedup, List.mem_append]; exact Or.inl hv
    · simp only [Ty.freeVars, List.mem_dedup, List.mem_append]; exact Or.inr hv
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
  | pair a b iha ihb => cases h with | pair ha hb => exact .pair (iha ha) (ihb hb)
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
  | pair a b iha ihb => simp only [Ty.substFvar, Ty.rename_pair, iha, ihb]
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
  | pair a' b' iha ihb =>
    simp only [Ty.freeVars, List.mem_dedup, List.mem_append, not_or] at hc
    simp only [Subst.onTy_pair, Ty.rename_pair]
    exact congrArg₂ Ty.pair (iha hc.1) (ihb hc.2)
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
  | pair a b iha ihb =>
    simp only [Ty.freeVars, List.mem_dedup, List.mem_append, not_or] at h
    simp only [Ty.rename_pair, Ty.freeVars, List.mem_dedup, List.mem_append, not_or]
    exact ⟨iha h.1, ihb h.2⟩
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
  | pair a b iha ihb =>
    simp only [Ty.freeVars, List.mem_dedup, List.mem_append, not_or] at h
    simp only [Ty.rename_pair, Ty.substFvar, iha h.1, ihb h.2]
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
  | pair a b iha ihb =>
    simp only [Ty.freeVars, List.mem_dedup, List.mem_append, not_or] at hτ
    simp only [Ty.substFvar, Ty.freeVars, List.mem_dedup, List.mem_append, not_or]
    exact ⟨iha hτ.1, ihb hτ.2⟩
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

/-- Principality, lambda case (factored with named binders to avoid the
    inaccessible-name problem). The fresh param var `Φ` may clash with `S₀`'s
    range, so we α-rename the declarative derivation by the swap `Φ ↔ W`
    (`W` fresh), apply the IH to the body under the conjugated specialization
    `S₀ᵃ ++ [(Φ, paramTyᵃ)]` (now `Φ ∉ dom`), then map the residual back with
    `[(W, .fvar Φ)]` (the swap's involution recovers the originals). -/
theorem Infer.complete_lambda_aux {body : Expr} {Φ : Nat} {ctx : Ctx} {S₀ : Subst}
    {paramTy bodyTy : Ty}
    (ih : Infer.CompleteAt body)
    (hwf : CtxWF ctx) (hbelow : CtxBelow Φ ctx) (hS₀ : ∀ p ∈ S₀, p.2.IsLC)
    (hparamLC : paramTy.IsLC)
    (hbodyty : TypeOfHM { (S₀.onCtx ctx) with
        env := PolyTy.mkTrivial paramTy :: (S₀.onCtx ctx).env } body bodyTy) :
    ∃ Φ' S τ R,
      Infer Φ ctx (.lambda body) Φ' S τ ∧
      Subst.AgreesBelow Φ S₀ (S ++ R) ∧
      Ty.arrow paramTy bodyTy = R.onTy τ ∧
      (∀ p ∈ R, p.2.IsLC) := by
  -- STEP 0: fresh names
  obtain ⟨W, c, hΦW, hΦc, hWc, hWav, hcav⟩ := exists_fresh_two_ge Φ
    ([Φ] ++ S₀.map Prod.fst ++ S₀.flatMap (fun p => p.2.freeVars)
      ++ paramTy.freeVars ++ bodyTy.freeVars)
  simp only [List.mem_append, List.mem_singleton, List.mem_map, List.mem_flatMap] at hWav hcav
  push_neg at hWav hcav
  obtain ⟨⟨⟨⟨hWΦ, hWkey⟩, hWrange⟩, hWparam⟩, hWbody⟩ := hWav
  obtain ⟨⟨⟨⟨hcΦ, hckey⟩, hcrange⟩, hcparam⟩, hcbody⟩ := hcav
  have finj : Function.Injective (swapNat Φ W) := swapNat_injective Φ W
  have hfix : ∀ v, v < Φ → swapNat Φ W v = v := fun v hv =>
    swapNat_other (by omega) (by omega)
  have hWonTy : ∀ {τ : Ty}, W ∉ τ.freeVars → W ∉ (S₀.onTy τ).freeVars :=
    fun h => Subst.not_mem_onTy_freeVars hWrange h
  have hconΦ : ∀ p ∈ Subst.conj (swapNat Φ W) S₀, p.1 ≠ Φ := by
    intro p hp
    simp only [Subst.conj, List.mem_map] at hp
    obtain ⟨q, hq, rfl⟩ := hp
    intro hc
    apply hWkey q hq
    have hc' : swapNat Φ W q.1 = Φ := hc
    simp only [swapNat] at hc'
    split_ifs at hc' <;> omega
  have hSconjΦ : (Subst.conj (swapNat Φ W) S₀).onTy (.fvar Φ) = .fvar Φ := by
    apply Ty.substFvars_eq_self_of_no_key
    intro p hp hc
    simp only [Ty.freeVars, List.mem_singleton] at hc
    exact hconΦ p hp hc
  -- STEP 1: rename the body derivation and reinterpret its context
  have hctxeq : (swapSubst Φ W c).onCtx
        { (S₀.onCtx ctx) with env := PolyTy.mkTrivial paramTy :: (S₀.onCtx ctx).env }
      = (Subst.conj (swapNat Φ W) S₀ ++ [(Φ, Ty.rename (swapNat Φ W) paramTy)]).onCtx
        { ctx with env := PolyTy.mkTrivial (.fvar Φ) :: ctx.env } := by
    simp only [Subst.onCtx, Subst.onEnv, List.map_cons, List.map_map]
    congr 1
    congr 1
    · -- head
      simp only [Subst.onPolyTy, PolyTy.mkTrivial, PolyTy.mk.injEq, true_and]
      rw [swapSubst_onTy (Ne.symm hWΦ) (Ne.symm hcΦ) hWc hcparam,
          Subst.onTy_append (Subst.conj (swapNat Φ W) S₀)
            [(Φ, Ty.rename (swapNat Φ W) paramTy)] (.fvar Φ),
          hSconjΦ]
      simp only [Subst.onTy, Ty.substFvars, Ty.substFvar, if_pos]
    · -- tail
      apply List.map_congr_left
      intro M hM
      have hMbelow : ∀ v ∈ M.body.freeVars, v < Φ := (hbelow M hM).mem_lt
      have hrenM : Ty.rename (swapNat Φ W) M.body = M.body :=
        Ty.rename_eq_self (fun v hv => hfix v (hMbelow v hv))
      have hΦnotin : Φ ∉ (Ty.rename (swapNat Φ W) (S₀.onTy M.body)).freeVars :=
        Ty.rename_swap_not_mem_left (hWonTy (τ := M.body) (fun hv => by have := hMbelow _ hv; omega))
      simp only [Function.comp, Subst.onPolyTy, PolyTy.mk.injEq, true_and]
      rw [swapSubst_onTy (Ne.symm hWΦ) (Ne.symm hcΦ) hWc
            (Subst.not_mem_onTy_freeVars hcrange (fun hv => by have := hMbelow _ hv; omega)),
          Subst.onTy_append (Subst.conj (swapNat Φ W) S₀)
            [(Φ, Ty.rename (swapNat Φ W) paramTy)] M.body]
      conv_rhs => rw [← hrenM, Subst.onTy_conj finj]
      exact (Ty.substFvar_fresh hΦnotin).symm
  have hbodyTyeq : (swapSubst Φ W c).onTy bodyTy = Ty.rename (swapNat Φ W) bodyTy :=
    swapSubst_onTy (Ne.symm hWΦ) (Ne.symm hcΦ) hWc hcbody
  have hren := TypeOfHM.onSubst (swapSubst Φ W c) (swapSubst_lc Φ W c) hbodyty
  rw [hctxeq, hbodyTyeq] at hren
  -- STEP 2: apply the IH to the body under the conjugated specialization
  have hwf_b : CtxWF { ctx with env := PolyTy.mkTrivial (.fvar Φ) :: ctx.env } := by
    intro M hM
    rcases List.mem_cons.mp hM with rfl | hM
    · exact ContainsBvarsUpTo.fvar
    · exact hwf M hM
  have hbelow_b : CtxBelow (Φ + 1) { ctx with env := PolyTy.mkTrivial (.fvar Φ) :: ctx.env } := by
    intro M hM
    rcases List.mem_cons.mp hM with rfl | hM
    · exact .fvar (by omega)
    · exact (hbelow M hM).mono (by omega)
  have hT_lc : ∀ p ∈ Subst.conj (swapNat Φ W) S₀ ++ [(Φ, Ty.rename (swapNat Φ W) paramTy)],
      p.2.IsLC := by
    intro p hp
    rw [List.mem_append] at hp
    rcases hp with hp | hp
    · exact Subst.conj_lc hS₀ p hp
    · rw [List.mem_singleton] at hp
      subst hp
      exact Ty.rename_isLC hparamLC
  obtain ⟨Φ', S, τb, R_b, hinfb, hagb, htyb, hR_b⟩ := ih hwf_b hbelow_b hT_lc hren
  -- STEP 3: assemble the conclusion
  refine ⟨Φ', S, .arrow (S.onTy (.fvar Φ)) τb, R_b ++ [(W, .fvar Φ)], ?_, ?_, ?_, ?_⟩
  · exact Infer.lambda hinfb
  · -- agreement below Φ
    intro v hv
    have hWv : W ∉ (Ty.fvar v).freeVars := by
      simp only [Ty.freeVars, List.mem_singleton]; omega
    have hconjv : (Subst.conj (swapNat Φ W) S₀).onTy (.fvar v)
        = Ty.rename (swapNat Φ W) (S₀.onTy (.fvar v)) := by
      have h := Subst.onTy_conj finj S₀ (.fvar v)
      rw [Ty.rename_fvar, hfix v hv] at h
      exact h
    have hTv : (Subst.conj (swapNat Φ W) S₀ ++ [(Φ, Ty.rename (swapNat Φ W) paramTy)]).onTy (.fvar v)
        = Ty.rename (swapNat Φ W) (S₀.onTy (.fvar v)) := by
      rw [Subst.onTy_append (Subst.conj (swapNat Φ W) S₀)
            [(Φ, Ty.rename (swapNat Φ W) paramTy)] (.fvar v), hconjv]
      exact Ty.substFvar_fresh (Ty.rename_swap_not_mem_left (hWonTy (τ := .fvar v) hWv))
    rw [← List.append_assoc, Subst.onTy_append (S ++ R_b) [(W, .fvar Φ)] (.fvar v),
        ← hagb v (by omega), hTv]
    exact (Ty.substFvar_rename_swap (hWonTy (τ := .fvar v) hWv)).symm
  · -- the arrow type is recovered
    have hTΦ : (Subst.conj (swapNat Φ W) S₀ ++ [(Φ, Ty.rename (swapNat Φ W) paramTy)]).onTy (.fvar Φ)
        = Ty.rename (swapNat Φ W) paramTy := by
      rw [Subst.onTy_append (Subst.conj (swapNat Φ W) S₀)
            [(Φ, Ty.rename (swapNat Φ W) paramTy)] (.fvar Φ), hSconjΦ]
      simp only [Subst.onTy, Ty.substFvars, Ty.substFvar, if_pos]
    rw [Subst.onTy_arrow]
    refine congrArg₂ Ty.arrow ?_ ?_
    · rw [Subst.onTy_append R_b [(W, .fvar Φ)] (S.onTy (.fvar Φ)),
          ← Subst.onTy_append S R_b (.fvar Φ),
          ← hagb Φ (by omega), hTΦ]
      exact (Ty.substFvar_rename_swap hWparam).symm
    · rw [Subst.onTy_append R_b [(W, .fvar Φ)] τb, ← htyb]
      exact (Ty.substFvar_rename_swap hWbody).symm
  · -- residual is LC
    intro p hp
    rw [List.mem_append] at hp
    rcases hp with hp | hp
    · exact hR_b p hp
    · rw [List.mem_singleton] at hp
      subst hp
      exact ContainsBvarsUpTo.fvar

/-- Principality, lambda case. -/
theorem Infer.complete_lambda {body : Expr}
    (ih : Infer.CompleteAt body) : Infer.CompleteAt (.lambda body) := by
  intro Φ ctx S₀ τ₀ hwf hbelow hS₀ hty
  cases hty with
  | lambda hparamLC heq hbodyty =>
    subst heq
    exact Infer.complete_lambda_aux ih hwf hbelow hS₀ hparamLC hbodyty


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
  | pair a b iha ihb =>
    simp only [Subst.onTy_pair, Ty.rename_pair]
    refine congrArg₂ Ty.pair (iha (fun v hv => hτ v ?_)) (ihb (fun v hv => hτ v ?_))
    · simp only [Ty.freeVars, List.mem_dedup, List.mem_append]; exact Or.inl hv
    · simp only [Ty.freeVars, List.mem_dedup, List.mem_append]; exact Or.inr hv
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
  | pair a b iha ihb =>
    simp only [Ty.rename_pair, Subst.onTy_pair]
    refine congrArg₂ Ty.pair (iha (fun v hv => hX v ?_)) (ihb (fun v hv => hX v ?_))
    · simp only [Ty.freeVars, List.mem_dedup, List.mem_append]; exact Or.inl hv
    · simp only [Ty.freeVars, List.mem_dedup, List.mem_append]; exact Or.inr hv
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
    simp only [Ty.rename_customTy, Subst.onTy_customTy, List.map_map, Ty.customTy.injEq,
               true_and]
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
  | pair a b iha ihb =>
    intro v hv1 hv2
    simp only [Ty.rename_pair, Ty.freeVars, List.mem_dedup, List.mem_append, not_or]
    refine ⟨iha (fun w hw => hY w ?_) v hv1 hv2, ihb (fun w hw => hY w ?_) v hv1 hv2⟩
    · simp only [Ty.freeVars, List.mem_dedup, List.mem_append]; exact Or.inl hw
    · simp only [Ty.freeVars, List.mem_dedup, List.mem_append]; exact Or.inr hw
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
  | pair a b iha ihb =>
    cases hinst with
    | pair ha hb =>
      cases hbv with
      | pair hba hbb =>
        simp only [Ty.openVars_pair, Subst.onTy_pair]
        refine congrArg₂ Ty.pair (iha ha hba ?_) (ihb hb hbb ?_)
        · intro x hx hc; exact hXfresh x hx (by
            simp only [Ty.freeVars, List.mem_dedup, List.mem_append]; exact .inl hc)
        · intro x hx hc; exact hXfresh x hx (by
            simp only [Ty.freeVars, List.mem_dedup, List.mem_append]; exact .inr hc)
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

/-- Converse of `Ty.BelowFvars.mem_lt`: all free vars `< Φ` gives `BelowFvars Φ`. -/
theorem Ty.BelowFvars.of_freeVars_lt {Φ : Nat} {τ : Ty}
    (h : ∀ v ∈ τ.freeVars, v < Φ) : Ty.BelowFvars Φ τ := by
  induction τ using Ty.rec_strong with
  | prim p => exact .prim
  | bvar i => exact .bvar
  | fvar n => exact .fvar (h n (by simp [Ty.freeVars]))
  | pair a b iha ihb =>
    refine .pair (iha fun v hv => h v ?_) (ihb fun v hv => h v ?_)
    · simp only [Ty.freeVars, List.mem_dedup, List.mem_append]; exact .inl hv
    · simp only [Ty.freeVars, List.mem_dedup, List.mem_append]; exact .inr hv
  | arrow a b iha ihb =>
    refine .arrow (iha fun v hv => h v ?_) (ihb fun v hv => h v ?_)
    · simp only [Ty.freeVars, List.mem_dedup, List.mem_append]; exact .inl hv
    · simp only [Ty.freeVars, List.mem_dedup, List.mem_append]; exact .inr hv
  | customTy nm tys ih =>
    refine .customTy fun t ht => ih t ht (fun v hv => h v ?_)
    simp only [Ty.freeVars]
    exact TyList.mem_freeVars_of_mem ht hv

theorem freshVars_nodup {Φ k : Nat} : (freshVars Φ k).Nodup :=
  (List.nodup_range).map (fun _ _ h => by omega)

theorem freshVars_ge {Φ k : Nat} : ∀ x ∈ freshVars Φ k, Φ ≤ x := by
  intro x hx
  simp only [freshVars, List.mem_map, List.mem_range] at hx
  obtain ⟨i, _, rfl⟩ := hx
  omega

/-- A single fresh name `W` starting a block `[W,W+k)` disjoint from `[Φ,Φ+k)`
    and above a finite `avoid` set. -/
theorem exists_fresh_block (avoid : List Nat) (Φ k : Nat) :
    ∃ W, Φ + k ≤ W ∧ ∀ v ∈ avoid, v < W := by
  refine ⟨avoid.foldr max 0 + Φ + k + 1, by omega, ?_⟩
  intro v hv
  have := List.le_foldr_max hv
  omega

/-- Principality, variable case. The algorithm opens the looked-up scheme with a
    fresh block `[Φ,Φ+pc)`; these may clash with `S₀`'s range or the declarative
    instantiation `tyArgs`, so we α-rename the derivation by the block-swap
    `[Φ,Φ+pc) ↔ [W,W+pc)` (`W` fresh), read off the residual from the clean
    (block-avoiding) renamed instantiation via `InstantiatesBy.onTy_openVars_zip`,
    then map back with `blockListBack`. -/
theorem Infer.complete_var {i : Nat} : Infer.CompleteAt (.var i) := by
  intro Φ ctx S₀ τ₀ hwf hbelow hS₀ hty
  -- STEP 0: looked-up scheme from `ctx`, without consuming `hty`.
  obtain ⟨polyTy, hlook_orig⟩ : ∃ pt, ctx.env[i]? = some pt := by
    cases hty with
    | var hlook _ _ =>
      have hmap : (S₀.onCtx ctx).env[i]? = (ctx.env[i]?).map S₀.onPolyTy := by
        show (ctx.env.map S₀.onPolyTy)[i]? = _
        rw [List.getElem?_map]
      rw [hmap] at hlook
      obtain ⟨pt, h, _⟩ := Option.map_eq_some_iff.mp hlook
      exact ⟨pt, h⟩
  have hmem : polyTy ∈ ctx.env := List.mem_of_getElem? hlook_orig
  set pc := polyTy.paramCount with hpc
  have hwfpoly : ContainsBvarsUpTo pc polyTy.body := hwf polyTy hmem
  -- STEP 1: fresh block start `W`.
  obtain ⟨W, hd, hWfresh⟩ := exists_fresh_block
    (S₀.map Prod.fst ++ S₀.flatMap (fun p => p.2.freeVars) ++ τ₀.freeVars) Φ pc
  have hτ₀W : ∀ v ∈ τ₀.freeVars, ¬ (W ≤ v ∧ v < W + pc) := by
    intro v hv hc
    have := hWfresh v (List.mem_append_right _ hv)
    omega
  have hSrange_lt : ∀ p ∈ S₀, ∀ v ∈ p.2.freeVars, v < W := by
    intro p hp v hv
    exact hWfresh v (List.mem_append_left _
      (List.mem_append_right _ (List.mem_flatMap.mpr ⟨p, hp, hv⟩)))
  have hSkey_lt : ∀ p ∈ S₀, p.1 < W := by
    intro p hp
    exact hWfresh p.1 (List.mem_append_left _
      (List.mem_append_left _ (List.mem_map.mpr ⟨p, hp, rfl⟩)))
  have hS₀belowW : ∀ p ∈ S₀, Ty.BelowFvars W p.2 :=
    fun p hp => Ty.BelowFvars.of_freeVars_lt (fun v hv => hSrange_lt p hp v hv)
  have hWblock_of_belowW : ∀ {t : Ty}, Ty.BelowFvars W t →
      ∀ v ∈ t.freeVars, ¬ (W ≤ v ∧ v < W + pc) :=
    fun {t} ht v hv => by have := ht.mem_lt v hv; omega
  have finj : Function.Injective (blockSwap Φ W pc) := blockSwap_injective hd
  have hffix : ∀ v, v < Φ → blockSwap Φ W pc v = v := fun v hv => blockSwap_lt (by omega) hv
  -- STEP 2: rename `hty` by the block-swap, reinterpret as a `conj`.
  have hren := TypeOfHM.onSubst (blockList Φ W pc) (blockList_lc Φ W pc) hty
  have hctxeq : (blockList Φ W pc).onCtx (S₀.onCtx ctx)
      = (Subst.conj (blockSwap Φ W pc) S₀).onCtx ctx := by
    simp only [Subst.onCtx, Subst.onEnv, List.map_map]
    congr 1
    apply List.map_congr_left
    intro M hM
    simp only [Function.comp_apply, Subst.onPolyTy]
    congr 1
    rw [blockList_onTy hd
        (hWblock_of_belowW (Subst.onTy_belowFvars hS₀belowW ((hbelow M hM).mono (by omega))))]
    conv_rhs => rw [← Ty.rename_eq_self (f := blockSwap Φ W pc) (τ := M.body)
      (fun v hv => hffix v ((hbelow M hM).mem_lt v hv))]
    rw [Subst.onTy_conj finj]
  have htyeq : (blockList Φ W pc).onTy τ₀ = Ty.rename (blockSwap Φ W pc) τ₀ :=
    blockList_onTy hd hτ₀W
  have hren2 : TypeOfHM ((Subst.conj (blockSwap Φ W pc) S₀).onCtx ctx) (.var i)
      (Ty.rename (blockSwap Φ W pc) τ₀) := by
    rw [hctxeq, htyeq] at hren
    exact hren
  -- STEP 3: invert renamed derivation.
  cases hren2 with
  | var hlook2 htyargs2 hinst2 =>
    rename_i polyTy2 tyArgs2
    have hlook2' : ((Subst.conj (blockSwap Φ W pc) S₀).onCtx ctx).env[i]?
        = some ((Subst.conj (blockSwap Φ W pc) S₀).onPolyTy polyTy) := by
      show (ctx.env.map (Subst.conj (blockSwap Φ W pc) S₀).onPolyTy)[i]? = _
      simp only [List.getElem?_map, hlook_orig, Option.map_some]
    have hpolyTy2 : polyTy2 = (Subst.conj (blockSwap Φ W pc) S₀).onPolyTy polyTy :=
      Option.some.inj (hlook2.symm.trans hlook2')
    subst hpolyTy2
    simp only [Subst.onPolyTy] at hinst2
    -- STEP 4: assemble.
    have hdomfresh : ∀ p ∈ Subst.conj (blockSwap Φ W pc) S₀, p.1 ∉ freshVars Φ pc := by
      intro p hp hmemf
      simp only [Subst.conj, List.mem_map] at hp
      obtain ⟨q, hq, rfl⟩ := hp
      have hq1 : q.1 < W := hSkey_lt q hq
      have hge := freshVars_ge _ hmemf
      have hlt := freshVars_lt _ hmemf
      simp only [blockSwap] at hge hlt
      split_ifs at hge hlt <;> omega
    have hbv2 : ContainsBvarsUpTo (freshVars Φ pc).length
        ((Subst.conj (blockSwap Φ W pc) S₀).onTy polyTy.body) := by
      rw [freshVars_length]
      exact Subst.onTy_containsBvars (Subst.conj_lc hS₀) hwfpoly
    have hXfresh2 : ∀ x ∈ freshVars Φ pc, x ∉ (Ty.rename (blockSwap Φ W pc) τ₀).freeVars :=
      fun x hx => blockSwap_rename_not_mem hd hτ₀W x (freshVars_ge x hx) (freshVars_lt x hx)
    have hR'eq : Subst.onTy (Subst.conj (blockSwap Φ W pc) S₀ ++ (freshVars Φ pc).zip tyArgs2)
        (polyTy.openVars (freshVars Φ pc)) = Ty.rename (blockSwap Φ W pc) τ₀ := by
      rw [Subst.onTy_append]
      simp only [PolyTy.openVars]
      rw [Subst.onTy_openVars (Subst.conj_lc hS₀) hdomfresh]
      exact InstantiatesBy.onTy_openVars_zip hinst2 hbv2 freshVars_nodup hXfresh2
    refine ⟨Φ + pc, [], polyTy.openVars (freshVars Φ pc),
      (Subst.conj (blockSwap Φ W pc) S₀ ++ (freshVars Φ pc).zip tyArgs2) ++ blockListBack Φ W pc,
      Infer.var hlook_orig, ?_, ?_, ?_⟩
    · -- agreement below the frontier
      intro v hv
      have hbelowfv : Ty.BelowFvars W (S₀.onTy (.fvar v)) :=
        Subst.onTy_belowFvars hS₀belowW (Ty.BelowFvars.fvar (show v < W by omega))
      have hconjv : Subst.onTy (Subst.conj (blockSwap Φ W pc) S₀) (.fvar v)
          = Ty.rename (blockSwap Φ W pc) (S₀.onTy (.fvar v)) := by
        conv_lhs => rw [show (Ty.fvar v) = Ty.rename (blockSwap Φ W pc) (Ty.fvar v) by
          rw [Ty.rename_fvar, hffix v hv]]
        rw [Subst.onTy_conj finj]
      have hzipnoop : Subst.onTy ((freshVars Φ pc).zip tyArgs2)
          (Ty.rename (blockSwap Φ W pc) (S₀.onTy (.fvar v)))
          = Ty.rename (blockSwap Φ W pc) (S₀.onTy (.fvar v)) :=
        Ty.substFvars_eq_self_of_no_key (fun p hp =>
          blockSwap_rename_not_mem hd (hWblock_of_belowW hbelowfv) p.1
            (freshVars_ge p.1 (List.of_mem_zip hp).1) (freshVars_lt p.1 (List.of_mem_zip hp).1))
      have hback : Subst.onTy (blockListBack Φ W pc)
          (Ty.rename (blockSwap Φ W pc) (S₀.onTy (.fvar v))) = S₀.onTy (.fvar v) :=
        blockListBack_onTy_rename hd (hWblock_of_belowW hbelowfv)
      rw [List.nil_append, Subst.onTy_append, Subst.onTy_append, hconjv, hzipnoop, hback]
    · -- declarative type factors through the residual
      rw [Subst.onTy_append, hR'eq, blockListBack_onTy_rename hd hτ₀W]
    · -- residual is locally closed
      intro p hp
      rw [List.mem_append] at hp
      rcases hp with hp | hp
      · rw [List.mem_append] at hp
        rcases hp with hp | hp
        · exact Subst.conj_lc hS₀ p hp
        · exact htyargs2 p.2 (List.of_mem_zip hp).2
      · exact blockListBack_lc Φ W pc p hp

/-- Principality, constructor case. Structurally identical to `complete_var`,
    but the looked-up scheme `ctor.toTy` lives in `ctx.ctors` (untouched by
    `S₀.onCtx`) and its body is closed (`Ctor.toTy_body_noFreeVars`), so the
    substitution `S₀`/`conj` never fires on it. -/
theorem Infer.complete_ctor {name : CtorName} : Infer.CompleteAt (.ctor name) := by
  intro Φ ctx S₀ τ₀ hwf hbelow hS₀ hty
  -- STEP 0: looked-up ctor from `ctx.ctors` (unchanged by `S₀.onCtx`), without consuming `hty`.
  obtain ⟨ctor, hlook_orig⟩ : ∃ c, LookupList.get? ctx.ctors name = some c := by
    cases hty with
    | ctor hlook _ _ => exact ⟨_, hlook⟩
  set pc := ctor.paramCount with hpc
  have hwfpoly : ContainsBvarsUpTo pc ctor.toTy.body := Ctor.toTy_wf ctor
  -- STEP 1: fresh block start `W`.
  obtain ⟨W, hd, hWfresh⟩ := exists_fresh_block
    (S₀.map Prod.fst ++ S₀.flatMap (fun p => p.2.freeVars) ++ τ₀.freeVars) Φ pc
  have hτ₀W : ∀ v ∈ τ₀.freeVars, ¬ (W ≤ v ∧ v < W + pc) := by
    intro v hv hc
    have := hWfresh v (List.mem_append_right _ hv)
    omega
  have hSrange_lt : ∀ p ∈ S₀, ∀ v ∈ p.2.freeVars, v < W := by
    intro p hp v hv
    exact hWfresh v (List.mem_append_left _
      (List.mem_append_right _ (List.mem_flatMap.mpr ⟨p, hp, hv⟩)))
  have hSkey_lt : ∀ p ∈ S₀, p.1 < W := by
    intro p hp
    exact hWfresh p.1 (List.mem_append_left _
      (List.mem_append_left _ (List.mem_map.mpr ⟨p, hp, rfl⟩)))
  have hS₀belowW : ∀ p ∈ S₀, Ty.BelowFvars W p.2 :=
    fun p hp => Ty.BelowFvars.of_freeVars_lt (fun v hv => hSrange_lt p hp v hv)
  have hWblock_of_belowW : ∀ {t : Ty}, Ty.BelowFvars W t →
      ∀ v ∈ t.freeVars, ¬ (W ≤ v ∧ v < W + pc) :=
    fun {t} ht v hv => by have := ht.mem_lt v hv; omega
  have finj : Function.Injective (blockSwap Φ W pc) := blockSwap_injective hd
  have hffix : ∀ v, v < Φ → blockSwap Φ W pc v = v := fun v hv => blockSwap_lt (by omega) hv
  -- STEP 2: rename `hty` by the block-swap, reinterpret as a `conj`.
  have hren := TypeOfHM.onSubst (blockList Φ W pc) (blockList_lc Φ W pc) hty
  have hctxeq : (blockList Φ W pc).onCtx (S₀.onCtx ctx)
      = (Subst.conj (blockSwap Φ W pc) S₀).onCtx ctx := by
    simp only [Subst.onCtx, Subst.onEnv, List.map_map]
    congr 1
    apply List.map_congr_left
    intro M hM
    simp only [Function.comp_apply, Subst.onPolyTy]
    congr 1
    rw [blockList_onTy hd
        (hWblock_of_belowW (Subst.onTy_belowFvars hS₀belowW ((hbelow M hM).mono (by omega))))]
    conv_rhs => rw [← Ty.rename_eq_self (f := blockSwap Φ W pc) (τ := M.body)
      (fun v hv => hffix v ((hbelow M hM).mem_lt v hv))]
    rw [Subst.onTy_conj finj]
  have htyeq : (blockList Φ W pc).onTy τ₀ = Ty.rename (blockSwap Φ W pc) τ₀ :=
    blockList_onTy hd hτ₀W
  have hren2 : TypeOfHM ((Subst.conj (blockSwap Φ W pc) S₀).onCtx ctx) (.ctor name)
      (Ty.rename (blockSwap Φ W pc) τ₀) := by
    rw [hctxeq, htyeq] at hren
    exact hren
  -- STEP 3: invert renamed derivation.
  cases hren2 with
  | ctor hlook2 htyargs2 hinst2 =>
    rename_i ctor2 tyArgs2
    have hctor2 : ctor = ctor2 := by
      have hlook2' : LookupList.get? ctx.ctors name = some ctor2 := hlook2
      exact Option.some.inj (hlook_orig.symm.trans hlook2')
    subst hctor2
    -- STEP 4: assemble.
    have hdomfresh : ∀ p ∈ Subst.conj (blockSwap Φ W pc) S₀, p.1 ∉ freshVars Φ pc := by
      intro p hp hmemf
      simp only [Subst.conj, List.mem_map] at hp
      obtain ⟨q, hq, rfl⟩ := hp
      have hq1 : q.1 < W := hSkey_lt q hq
      have hge := freshVars_ge _ hmemf
      have hlt := freshVars_lt _ hmemf
      simp only [blockSwap] at hge hlt
      split_ifs at hge hlt <;> omega
    have hbv2 : ContainsBvarsUpTo (freshVars Φ pc).length ctor.toTy.body := by
      rw [freshVars_length]; exact hwfpoly
    have hXfresh2 : ∀ x ∈ freshVars Φ pc, x ∉ (Ty.rename (blockSwap Φ W pc) τ₀).freeVars :=
      fun x hx => blockSwap_rename_not_mem hd hτ₀W x (freshVars_ge x hx) (freshVars_lt x hx)
    have hR'eq : Subst.onTy (Subst.conj (blockSwap Φ W pc) S₀ ++ (freshVars Φ pc).zip tyArgs2)
        (ctor.toTy.openVars (freshVars Φ pc)) = Ty.rename (blockSwap Φ W pc) τ₀ := by
      rw [Subst.onTy_append]
      simp only [PolyTy.openVars]
      rw [Subst.onTy_openVars (Subst.conj_lc hS₀) hdomfresh]
      rw [show (Subst.conj (blockSwap Φ W pc) S₀).onTy ctor.toTy.body = ctor.toTy.body from
        Ty.substFvars_eq_self_of_no_key
          (fun p _ => NoFreeVars.not_mem_freeVars (Ctor.toTy_body_noFreeVars ctor) p.1)]
      exact InstantiatesBy.onTy_openVars_zip hinst2 hbv2 freshVars_nodup hXfresh2
    refine ⟨Φ + pc, [], ctor.toTy.openVars (freshVars Φ pc),
      (Subst.conj (blockSwap Φ W pc) S₀ ++ (freshVars Φ pc).zip tyArgs2) ++ blockListBack Φ W pc,
      Infer.ctor hlook_orig, ?_, ?_, ?_⟩
    · -- agreement below the frontier
      intro v hv
      have hbelowfv : Ty.BelowFvars W (S₀.onTy (.fvar v)) :=
        Subst.onTy_belowFvars hS₀belowW (Ty.BelowFvars.fvar (show v < W by omega))
      have hconjv : Subst.onTy (Subst.conj (blockSwap Φ W pc) S₀) (.fvar v)
          = Ty.rename (blockSwap Φ W pc) (S₀.onTy (.fvar v)) := by
        conv_lhs => rw [show (Ty.fvar v) = Ty.rename (blockSwap Φ W pc) (Ty.fvar v) by
          rw [Ty.rename_fvar, hffix v hv]]
        rw [Subst.onTy_conj finj]
      have hzipnoop : Subst.onTy ((freshVars Φ pc).zip tyArgs2)
          (Ty.rename (blockSwap Φ W pc) (S₀.onTy (.fvar v)))
          = Ty.rename (blockSwap Φ W pc) (S₀.onTy (.fvar v)) :=
        Ty.substFvars_eq_self_of_no_key (fun p hp =>
          blockSwap_rename_not_mem hd (hWblock_of_belowW hbelowfv) p.1
            (freshVars_ge p.1 (List.of_mem_zip hp).1) (freshVars_lt p.1 (List.of_mem_zip hp).1))
      have hback : Subst.onTy (blockListBack Φ W pc)
          (Ty.rename (blockSwap Φ W pc) (S₀.onTy (.fvar v))) = S₀.onTy (.fvar v) :=
        blockListBack_onTy_rename hd (hWblock_of_belowW hbelowfv)
      rw [List.nil_append, Subst.onTy_append, Subst.onTy_append, hconjv, hzipnoop, hback]
    · -- declarative type factors through the residual
      rw [Subst.onTy_append, hR'eq, blockListBack_onTy_rename hd hτ₀W]
    · -- residual is locally closed
      intro p hp
      rw [List.mem_append] at hp
      rcases hp with hp | hp
      · rw [List.mem_append] at hp
        rcases hp with hp | hp
        · exact Subst.conj_lc hS₀ p hp
        · exact htyargs2 p.2 (List.of_mem_zip hp).2
      · exact blockListBack_lc Φ W pc p hp


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
  | _, _, _, @UnifyRel.pair a b c d S₁ S₂ h₁ h₂, S', hlc, hS' => by
    simp only [Unifies, Subst.onTy_pair, Ty.pair.injEq] at hS'
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

/-! A structural size on types (own measure; cleaner than `sizeOf` for the
    unification termination argument). -/
mutual
def Ty.size : Ty → Nat
  | .prim _ => 1
  | .bvar _ => 1
  | .fvar _ => 1
  | .pair a b => 1 + a.size + b.size
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
  | .pair _ _ => by simp only [Ty.size]; omega
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
  | pair a b iha ihb =>
    intro h
    simp only [Ty.freeVars, List.mem_dedup, List.mem_append] at h
    simp only [Subst.onTy_pair, Ty.size]
    rcases h with h | h
    · have := iha h; omega
    · have := ihb h; omega
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
  | pair a b =>
    simp only [Ty.freeVars, List.mem_dedup, List.mem_append] at hmem
    simp only [Subst.onTy_pair, Ty.size]
    rcases hmem with h | h
    · have := Ty.size_onTy_fvar_le (S := S) (n := n) h; have := @Ty.size_pos (S.onTy b); omega
    · have := Ty.size_onTy_fvar_le (S := S) (n := n) h; have := @Ty.size_pos (S.onTy a); omega
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
        | pair b₁ b₂ => simp [Unifies] at hU
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
        | pair b₁ b₂ =>
          by_cases hocc : n ∈ (Ty.pair b₁ b₂).freeVars
          · have hlt := Ty.size_onTy_fvar_lt (S := U) hocc (by simp)
            simp only [Unifies] at hU; rw [hU] at hlt; omega
          · exact ⟨[(n, .pair b₁ b₂)], .fvarL (by simp) hocc⟩
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
      | pair a₁ a₂ =>
        cases ha with
        | pair ha₁ ha₂ =>
        cases b with
        | bvar i => cases hb with | bvar h => omega
        | fvar m =>
          by_cases hocc : m ∈ (Ty.pair a₁ a₂).freeVars
          · have hlt := Ty.size_onTy_fvar_lt (S := U) hocc (by simp)
            simp only [Unifies] at hU; rw [hU] at hlt; omega
          · exact ⟨[(m, .pair a₁ a₂)], .fvarR (by simp) hocc⟩
        | prim q => simp [Unifies] at hU
        | arrow b₁ b₂ => simp [Unifies] at hU
        | customTy nm bs => simp [Unifies] at hU
        | pair b₁ b₂ =>
          cases hb with
          | pair hb₁ hb₂ =>
          have hpsz : (U.onTy (.pair a₁ a₂)).size
              = 1 + (U.onTy a₁).size + (U.onTy a₂).size := by simp [Subst.onTy_pair, Ty.size]
          simp only [Unifies, Subst.onTy_pair, Ty.pair.injEq] at hU
          obtain ⟨S₁, h₁⟩ := ihU (a := a₁) (b := b₁) (U := U)
            (by rw [hpsz] at hsz; omega) ha₁ hb₁ hU.1
          obtain ⟨R, hR⟩ := UnifyRel.greatest h₁ U hU.1
          have hS₁lc := UnifyRel.lc h₁ ha₁ hb₁
          obtain ⟨S₂, h₂⟩ := ihU (a := S₁.onTy a₂) (b := S₁.onTy b₂) (U := R)
            (by rw [← hR a₂]; rw [hpsz] at hsz; omega)
            (Subst.onTy_lc hS₁lc ha₂) (Subst.onTy_lc hS₁lc hb₂)
            (by show R.onTy (S₁.onTy a₂) = R.onTy (S₁.onTy b₂); rw [← hR a₂, ← hR b₂]; exact hU.2)
          exact ⟨S₁ ++ S₂, .pair h₁ h₂⟩
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
        | pair b₁ b₂ => simp [Unifies] at hU
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
        | pair b₁ b₂ => simp [Unifies] at hU
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

/-- Principality, application case (factored with named binders). Recurse on `f`
    then `arg`; the declarative typing yields a unifier of `S₂.onTy τf` and
    `arrow τa (.fvar Φ₂)` — exhibited explicitly as `[(Φ₂,.fvar W)] ++ R₂ ++ [(W,τ₀)]`
    (`W` fresh) so no derivation renaming is needed — which `UnifyRel.complete`
    realises as a derivation `S₃`, and `greatest_lc` factors through to the
    residual. -/
theorem Infer.complete_app_aux {f arg : Expr} {Φ : Nat} {ctx : Ctx} {S₀ : Subst}
    {argTy τ₀ : Ty}
    (ihf : Infer.CompleteAt f) (iharg : Infer.CompleteAt arg)
    (hwf : CtxWF ctx) (hbelow : CtxBelow Φ ctx) (hS₀ : ∀ p ∈ S₀, p.2.IsLC)
    (hf : TypeOfHM (S₀.onCtx ctx) f (.arrow argTy τ₀))
    (harg : TypeOfHM (S₀.onCtx ctx) arg argTy) :
    ∃ Φ' S τ R,
      Infer Φ ctx (.app f arg) Φ' S τ ∧
      Subst.AgreesBelow Φ S₀ (S ++ R) ∧
      τ₀ = R.onTy τ ∧
      (∀ p ∈ R, p.2.IsLC) := by
  -- STEP 1: recurse on `f`.
  obtain ⟨Φ₁, S₁, τf, R₁, hinff, hagf, htyf, hR₁⟩ := ihf hwf hbelow hS₀ hf
  have hS₁ := (Infer.lc hinff hwf).2
  have hbf := Infer.belowFvars hinff hbelow
  have hle1 := Infer.frontier_le hinff
  have hwf₁ := Subst.onCtx_wf hS₁ hwf
  have hbelow₁ := Subst.onCtx_below hbf.2 hle1 hbelow
  -- STEP 2: recurse on `arg`.
  have hctxeq : R₁.onCtx (S₁.onCtx ctx) = S₀.onCtx ctx := by
    rw [← Subst.onCtx_append]
    exact Subst.onCtx_congr (fun v hv => (hagf v hv).symm) hbelow
  have harg' : TypeOfHM (R₁.onCtx (S₁.onCtx ctx)) arg argTy := by
    rw [hctxeq]; exact harg
  obtain ⟨Φ₂, S₂, τa, R₂, hinfa, haga, htya, hR₂⟩ := iharg hwf₁ hbelow₁ hR₁ harg'
  have hS₂ := (Infer.lc hinfa hwf₁).2
  have hba := Infer.belowFvars hinfa hbelow₁
  have hle2 := Infer.frontier_le hinfa
  have hτfLC := (Infer.lc hinff hwf).1
  have hτaLC := (Infer.lc hinfa hwf₁).1
  -- STEP 3: key equalities.
  have hcongr_f : R₁.onTy τf = (S₂ ++ R₂).onTy τf := Subst.onTy_congr haga hbf.1
  have hP : R₂.onTy (S₂.onTy τf) = Ty.arrow argTy τ₀ := by
    rw [← Subst.onTy_append, ← hcongr_f]; exact htyf.symm
  have hΦ₂τf : Φ₂ ∉ (S₂.onTy τf).freeVars := fun hm => by
    have := (Subst.onTy_belowFvars hba.2 (hbf.1.mono hle2)).mem_lt _ hm
    omega
  have hΦ₂τa : Φ₂ ∉ τa.freeVars := fun hm => by
    have := hba.1.mem_lt _ hm
    omega
  have hτ₀LC : τ₀.IsLC := by
    have hreg := TypeOfHM.regular hf
    cases hreg with
    | arrow _ hT => exact hT
  -- STEP 4: a fresh variable `W`.
  obtain ⟨W, hWge, hWfresh⟩ := exists_fresh_block
    (R₂.map Prod.fst ++ R₂.flatMap (fun p => p.2.freeVars) ++ argTy.freeVars ++ τ₀.freeVars) Φ₂ 1
  have hWdom : ∀ p ∈ R₂, p.1 ≠ W := by
    intro p hp he
    have := hWfresh p.1 (List.mem_append_left _ (List.mem_append_left _
      (List.mem_append_left _ (List.mem_map.mpr ⟨p, hp, rfl⟩))))
    omega
  have hWrange : ∀ p ∈ R₂, W ∉ p.2.freeVars := by
    intro p hp hc
    have := hWfresh W (List.mem_append_left _ (List.mem_append_left _
      (List.mem_append_right _ (List.mem_flatMap.mpr ⟨p, hp, hc⟩))))
    omega
  have hWargTy : W ∉ argTy.freeVars := fun hc => by
    have := hWfresh W (List.mem_append_left _ (List.mem_append_right _ hc)); omega
  have hWτ₀ : W ∉ τ₀.freeVars := fun hc => by
    have := hWfresh W (List.mem_append_right _ hc); omega
  have hR₂Wfvar : R₂.onTy (Ty.fvar W) = Ty.fvar W := by
    apply Ty.substFvars_eq_self_of_no_key
    intro p hp hc
    simp only [Ty.freeVars, List.mem_singleton] at hc
    exact hWdom p hp hc
  -- STEP 5: the explicit unifier `U`.
  obtain ⟨U, hUdef⟩ : ∃ U : Subst, U = [(Φ₂, Ty.fvar W)] ++ R₂ ++ [(W, τ₀)] := ⟨_, rfl⟩
  have hsingle : ∀ (Z : Nat) (V y : Ty), Subst.onTy [(Z, V)] y = Ty.substFvar Z V y :=
    fun _ _ _ => rfl
  have hsubArrow : ∀ (Z : Nat) (V a b : Ty),
      Ty.substFvar Z V (Ty.arrow a b) = Ty.arrow (Ty.substFvar Z V a) (Ty.substFvar Z V b) :=
    fun _ _ _ _ => rfl
  have hUonTy : ∀ x, U.onTy x = Ty.substFvar W τ₀ (R₂.onTy (Ty.substFvar Φ₂ (Ty.fvar W) x)) := by
    intro x
    rw [hUdef, Subst.onTy_append, Subst.onTy_append, hsingle, hsingle]
  have e1 : Ty.substFvar Φ₂ (Ty.fvar W) (Ty.fvar Φ₂) = Ty.fvar W := by simp [Ty.substFvar]
  have e2 : Ty.substFvar W τ₀ (Ty.fvar W) = τ₀ := by simp [Ty.substFvar]
  have hUniL : U.onTy (S₂.onTy τf) = Ty.arrow argTy τ₀ := by
    rw [hUonTy, Ty.substFvar_fresh hΦ₂τf, hP, hsubArrow,
        Ty.substFvar_fresh hWargTy, Ty.substFvar_fresh hWτ₀]
  have hUniR : U.onTy (Ty.arrow τa (Ty.fvar Φ₂)) = Ty.arrow argTy τ₀ := by
    rw [hUonTy, hsubArrow, Ty.substFvar_fresh hΦ₂τa, e1, Subst.onTy_arrow,
        hR₂Wfvar, ← htya, hsubArrow, Ty.substFvar_fresh hWargTy, e2]
  have hUni : Unifies U (S₂.onTy τf) (Ty.arrow τa (Ty.fvar Φ₂)) := by
    show U.onTy (S₂.onTy τf) = U.onTy (Ty.arrow τa (Ty.fvar Φ₂))
    rw [hUniL, hUniR]
  -- STEP 6: realise the unifier as a derivation `S₃`.
  obtain ⟨S₃, h₃⟩ := UnifyRel.complete (Subst.onTy_lc hS₂ hτfLC)
    (.arrow hτaLC ContainsBvarsUpTo.fvar) hUni
  -- STEP 7: factor `U` through `S₃`.
  have hUlc : ∀ p ∈ U, p.2.IsLC := by
    rw [hUdef]
    intro p hp
    rcases List.mem_append.mp hp with hp' | hp'
    · rcases List.mem_append.mp hp' with hp'' | hp''
      · obtain rfl := List.mem_singleton.mp hp''
        exact ContainsBvarsUpTo.fvar
      · exact hR₂ p hp''
    · obtain rfl := List.mem_singleton.mp hp'
      exact hτ₀LC
  obtain ⟨R₃, hR₃, hR₃lc⟩ := UnifyRel.greatest_lc h₃ U hUlc hUni
  -- STEP 8: assemble.
  refine ⟨Φ₂ + 1, S₁ ++ S₂ ++ S₃, S₃.onTy (Ty.fvar Φ₂), R₃,
    Infer.app hinff hinfa h₃, ?_, ?_, hR₃lc⟩
  · intro v hv
    have ht1 : Ty.BelowFvars Φ₁ (S₁.onTy (Ty.fvar v)) :=
      Subst.onTy_belowFvars hbf.2 (Ty.BelowFvars.fvar (by omega))
    have ht : Ty.BelowFvars Φ₂ (S₂.onTy (S₁.onTy (Ty.fvar v))) :=
      Subst.onTy_belowFvars hba.2 (ht1.mono hle2)
    have hΦ₂t : Φ₂ ∉ (S₂.onTy (S₁.onTy (Ty.fvar v))).freeVars := fun hm => by
      have := ht.mem_lt _ hm; omega
    have hWt : W ∉ (S₂.onTy (S₁.onTy (Ty.fvar v))).freeVars := fun hm => by
      have := ht.mem_lt _ hm; omega
    have hWR₂t : W ∉ (R₂.onTy (S₂.onTy (S₁.onTy (Ty.fvar v)))).freeVars :=
      Subst.not_mem_onTy_freeVars hWrange hWt
    simp only [Subst.onTy_append]
    rw [← hR₃ (S₂.onTy (S₁.onTy (Ty.fvar v))), hUonTy,
        Ty.substFvar_fresh hΦ₂t, Ty.substFvar_fresh hWR₂t,
        hagf v hv, Subst.onTy_append, Subst.onTy_congr haga ht1, Subst.onTy_append]
  · rw [← hR₃ (Ty.fvar Φ₂), hUonTy, e1, hR₂Wfvar, e2]

/-- Principality, application case. -/
theorem Infer.complete_app {f arg : Expr}
    (ihf : Infer.CompleteAt f) (iharg : Infer.CompleteAt arg) :
    Infer.CompleteAt (.app f arg) := by
  intro Φ ctx S₀ τ₀ hwf hbelow hS₀ hty
  cases hty with
  | app hf harg => exact Infer.complete_app_aux ihf iharg hwf hbelow hS₀ hf harg


/-! ### Scheme weakening (for the `letIn` principality case)

The algorithm generalises the rhs's principal type with `genScheme`, the
*maximal* generalisation; the declarative scheme `M` is less general. Giving the
let-bound variable a more general scheme preserves typing: every instance the
body used is still available. -/

/-- `M'` is at least as general as `M`: every instantiation of `M` is also an
    instantiation of `M'`. -/
def PolyTy.Generalizes (M' M : PolyTy) : Prop :=
  ∀ tyArgs ty, (∀ t ∈ tyArgs, t.IsLC) → InstantiatesBy tyArgs M.body ty →
    ∃ tyArgs', (∀ t ∈ tyArgs', t.IsLC) ∧ InstantiatesBy tyArgs' M'.body ty

/-- Replacing a context scheme `M` by a more general `M'` preserves typing. -/
theorem TypeOfHM.weaken_scheme {ctors : CtorEnv} {env_post env : Env} {M M' : PolyTy}
    {e : Expr} {τ : Ty}
    (hgen : M'.Generalizes M)
    (h : TypeOfHM ⟨env_post ++ [M] ++ env, ctors⟩ e τ) :
    TypeOfHM ⟨env_post ++ [M'] ++ env, ctors⟩ e τ := by
  induction e using Expr.rec_strong generalizing env_post τ with
  | primLit p =>
    cases h <;> constructor
  | pair a b ih_a ih_b =>
    cases h with
    | pair ha hb => exact .pair (ih_a ha) (ih_b hb)
  | app f inp ih_f ih_i =>
    cases h with
    | app hf hi => exact .app (ih_f hf) (ih_i hi)
  | lambda body ih =>
    cases h with
    | lambda hpc heq hbody =>
      subst heq
      refine TypeOfHM.lambda hpc rfl ?_
      exact ih (env_post := PolyTy.mkTrivial _ :: env_post) hbody
  | letIn be body ih_be ih_body =>
    cases h with
    | letIn hsch hcofin heq hbody =>
      subst heq
      refine TypeOfHM.letIn hsch (fun Xs hfresh => ih_be (hcofin Xs hfresh)) rfl ?_
      exact ih_body (env_post := _ :: env_post) hbody
  | fst e ih =>
    cases h with
    | fst he => exact .fst (ih he)
  | snd e ih =>
    cases h with
    | snd he => exact .snd (ih he)
  | ctor name =>
    cases h with
    | ctor hlook htyargs hinst => exact .ctor hlook htyargs hinst
  | var i =>
    cases h with
    | var hlook htyargs hinst =>
      rcases lt_trichotomy i env_post.length with hlt | heq | hgt
      · -- i < env_post.length: lookup falls in env_post (unchanged)
        refine TypeOfHM.var ?_ htyargs hinst
        show (env_post ++ [M'] ++ env)[i]? = _
        rw [List.append_assoc, List.getElem?_append_left hlt]
        rw [List.append_assoc, List.getElem?_append_left hlt] at hlook
        exact hlook
      · -- i = env_post.length: the M slot, use hgen
        subst heq
        rw [List.append_assoc, List.getElem?_append_right (Nat.le_refl _),
            Nat.sub_self] at hlook
        simp only [List.singleton_append, List.getElem?_cons_zero,
          Option.some.injEq] at hlook
        subst hlook
        obtain ⟨tyArgs', htyargs', hinst'⟩ := hgen _ _ htyargs hinst
        refine TypeOfHM.var ?_ htyargs' hinst'
        show (env_post ++ [M'] ++ env)[env_post.length]? = _
        rw [List.append_assoc, List.getElem?_append_right (Nat.le_refl _),
            Nat.sub_self]
        simp only [List.singleton_append, List.getElem?_cons_zero]
      · -- i > env_post.length: lookup falls in env (unchanged); slot length is 1
        refine TypeOfHM.var ?_ htyargs hinst
        show (env_post ++ [M'] ++ env)[i]? = _
        have hle : env_post.length ≤ i := by omega
        rw [List.append_assoc, List.getElem?_append_right hle] at hlook
        rw [List.append_assoc, List.getElem?_append_right hle]
        rw [show ([M] ++ env) = M :: env from rfl] at hlook
        rw [show ([M'] ++ env) = M' :: env from rfl]
        rw [show (i - env_post.length) = (i - env_post.length - 1) + 1 from by omega]
            at hlook ⊢
        simp only [List.getElem?_cons_succ] at hlook ⊢
        exact hlook
  | match_ scrut branches ih_scrut ih_branches =>
    cases h with
    | match_ h_scrut h_ne h_brs =>
      refine TypeOfHM.match_ (ih_scrut h_scrut) h_ne ?_
      intro branch h_mem
      obtain ⟨pat, body⟩ := branch
      have h_branch := h_brs (pat, body) h_mem
      cases h_branch with
      | mk h_lookup h_tyName h_paramCount h_contents h_inst h_pb h_ctx h_body =>
        subst h_ctx
        subst h_pb
        expose_names
        rw [show (instContents.map PolyTy.mkTrivial ++ (env_post ++ [M] ++ env))
              = (instContents.map PolyTy.mkTrivial ++ env_post) ++ [M] ++ env
              by rw [List.append_assoc, List.append_assoc, List.append_assoc]]
          at h_body
        have ih_body :=
          ih_branches pat body h_mem
            (env_post := instContents.map PolyTy.mkTrivial ++ env_post)
            h_body
        rw [show (instContents.map PolyTy.mkTrivial ++ env_post) ++ [M'] ++ env
              = instContents.map PolyTy.mkTrivial ++ (env_post ++ [M'] ++ env)
              by rw [List.append_assoc, List.append_assoc, List.append_assoc]]
          at ih_body
        exact TypeOfMatchBranch.mk h_lookup h_tyName h_paramCount h_contents
          h_inst rfl rfl ih_body


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

/-- Open-then-close round-trip: closing the just-opened fresh names recovers the
    scheme body. (Converse of `Ty.openVars_closeOver_self`.) -/
theorem Ty.closeOver_openVars_self {Xs : List Nat} {ty : Ty}
    (hnodup : Xs.Nodup) (hbv : ContainsBvarsUpTo Xs.length ty)
    (hfresh : ∀ x ∈ Xs, x ∉ ty.freeVars) :
    Ty.closeOver Xs (Ty.openVars Xs ty) = ty := by
  induction ty using Ty.rec_strong with
  | prim p => rfl
  | bvar i =>
    cases hbv with
    | bvar hlt =>
      simp only [Ty.openVars, Ty.instantiate, List.getElem?_eq_getElem hlt, Option.elim_some]
      rw [Ty.closeOver.eq_6, List.idxOf?_getElem_self hnodup hlt]
  | fvar n =>
    have hn : n ∉ Xs := fun h => hfresh n h (by simp [Ty.freeVars])
    simp only [Ty.openVars, Ty.instantiate]
    rw [Ty.closeOver.eq_6, List.idxOf?_eq_none_iff.mpr hn]
  | pair a b iha ihb =>
    cases hbv with
    | pair hba hbb =>
      have hfa : ∀ x ∈ Xs, x ∉ a.freeVars := fun x hx hc =>
        hfresh x hx (List.mem_dedup.mpr (List.mem_append.mpr (Or.inl hc)))
      have hfb : ∀ x ∈ Xs, x ∉ b.freeVars := fun x hx hc =>
        hfresh x hx (List.mem_dedup.mpr (List.mem_append.mpr (Or.inr hc)))
      simp only [Ty.openVars_pair, Ty.closeOver, iha hba hfa, ihb hbb hfb]
  | arrow a b iha ihb =>
    cases hbv with
    | arrow hba hbb =>
      have hfa : ∀ x ∈ Xs, x ∉ a.freeVars := fun x hx hc =>
        hfresh x hx (List.mem_dedup.mpr (List.mem_append.mpr (Or.inl hc)))
      have hfb : ∀ x ∈ Xs, x ∉ b.freeVars := fun x hx hc =>
        hfresh x hx (List.mem_dedup.mpr (List.mem_append.mpr (Or.inr hc)))
      simp only [Ty.openVars_arrow, Ty.closeOver, iha hba hfa, ihb hbb hfb]
  | customTy nm tys ih =>
    cases hbv with
    | customTy hball =>
      simp only [Ty.openVars_customTy, Ty.closeOver, TyList.closeOver_eq_map, List.map_map]
      apply congrArg (Ty.customTy nm)
      conv_rhs => rw [← List.map_id tys]
      apply List.map_congr_left
      intro t ht
      exact ih t ht (hball t ht)
        (fun x hx hc => hfresh x hx (TyList.mem_freeVars_of_mem ht hc))

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
  | pair a b iha ihb =>
    have hfa : ∀ x ∈ Xs, x ∉ a.freeVars := fun x hx hc =>
      hfresh x hx (List.mem_dedup.mpr (List.mem_append.mpr (Or.inl hc)))
    have hfb : ∀ x ∈ Xs, x ∉ b.freeVars := fun x hx hc =>
      hfresh x hx (List.mem_dedup.mpr (List.mem_append.mpr (Or.inr hc)))
    simp only [Ty.openWith_pair, Ty.closeOver, iha hfa, ihb hfb]
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
  | pair a b iha ihb =>
    cases hbv with
    | pair hba hbb =>
      simp only [Ty.openWith_pair, iha hba, ihb hbb]
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

/-- Membership in a type-list's free vars iff in some element's. -/
theorem TyList.mem_freeVars_iff {x : Nat} {tys : List Ty} :
    x ∈ TyList.freeVars tys ↔ ∃ t ∈ tys, x ∈ t.freeVars := by
  induction tys with
  | nil => simp [TyList.freeVars]
  | cons hd tl ih =>
    simp only [TyList.freeVars, List.mem_dedup, List.mem_append, List.mem_cons]
    rw [ih]
    constructor
    · rintro (h | ⟨t, ht, hx⟩)
      · exact ⟨hd, .inl rfl, h⟩
      · exact ⟨t, .inr ht, hx⟩
    · rintro ⟨t, (rfl | ht), hx⟩
      · exact .inl hx
      · exact .inr ⟨t, ht, hx⟩

/-- Every free var of `S.onTy Z` traces back to a free var of `Z`. -/
theorem Ty.mem_freeVars_onTy_iff {S : Subst} {x : Nat} {Z : Ty} :
    x ∈ (S.onTy Z).freeVars ↔ ∃ v ∈ Z.freeVars, x ∈ (S.onTy (.fvar v)).freeVars := by
  induction Z using Ty.rec_strong with
  | prim p => simp [Subst.onTy_prim, Ty.freeVars]
  | bvar i => simp [Subst.onTy_bvar, Ty.freeVars]
  | fvar n => simp only [Ty.freeVars, List.mem_singleton, exists_eq_left]
  | pair a b iha ihb =>
    simp only [Subst.onTy_pair, Ty.freeVars, List.mem_dedup, List.mem_append]
    rw [iha, ihb]
    constructor
    · rintro (⟨v, hv, hx⟩ | ⟨v, hv, hx⟩)
      · exact ⟨v, .inl hv, hx⟩
      · exact ⟨v, .inr hv, hx⟩
    · rintro ⟨v, (hv | hv), hx⟩
      · exact .inl ⟨v, hv, hx⟩
      · exact .inr ⟨v, hv, hx⟩
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
    rw [Ty.closeOver.eq_6]
    cases gs.idxOf? n with
    | none => exact fun x hx => hx
    | some i => simp [Ty.freeVars]
  | pair a b iha ihb =>
    intro x hx
    simp only [Ty.closeOver, Ty.freeVars, List.mem_dedup, List.mem_append] at hx ⊢
    rcases hx with h | h
    · exact .inl (iha h)
    · exact .inr (ihb h)
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

/-- `genScheme env τ₁` (transported by `R`) generalizes any `M` it factors. The
    `g := genVars env τ₁` instance of `closeOver_generalizes`. -/
theorem genScheme_generalizes {env : Env} {τ₁ : Ty} {R : Subst} {M : PolyTy} {Xs : List Nat}
    (hτ₁ : τ₁.IsLC) (hR : ∀ p ∈ R, p.2.IsLC) (hMwf : M.WF)
    (hXnodup : Xs.Nodup) (hXlen : Xs.length = M.paramCount)
    (hXMbody : ∀ x ∈ Xs, x ∉ M.body.freeVars)
    (htyr : Ty.openVars Xs M.body = R.onTy τ₁)
    (hXM'' : ∀ x ∈ Xs, x ∉ (R.onPolyTy (genScheme env τ₁)).body.freeVars) :
    (R.onPolyTy (genScheme env τ₁)).Generalizes M :=
  closeOver_generalizes (g := genVars env τ₁) hτ₁ hR hMwf hXnodup hXlen hXMbody htyr hXM''

/-! ### Principality, `letIn` case -/

/-- The `letIn` principality core (inverted form, with the declarative scheme `M`
    and cofinite-fresh-set `L` named). Mirrors `Infer.sound_letIn`'s factoring to
    sidestep inaccessible binders. The algorithm infers the rhs to `(S₁, τ₁)` and
    generalizes with the principal `genScheme`; `genScheme_generalizes` shows that
    scheme weakens the declarative `M`, so the body — declaratively typed under
    `M` — retypes (`weaken_scheme`) under the algorithm's scheme, ready for the
    body IH. Assembly then mirrors `complete_pair`. -/
theorem Infer.complete_letIn_aux {Φ : Nat} {ctx : Ctx} {S₀ : Subst} {rhs body : Expr}
    {M : PolyTy} {L : List Nat} {τ₀ : Ty}
    (iha : Infer.CompleteAt rhs) (ihb : Infer.CompleteAt body)
    (hwf : CtxWF ctx) (hbelow : CtxBelow Φ ctx) (hS₀ : ∀ p ∈ S₀, p.2.IsLC)
    (hMwf : M.WF)
    (hcofin : ∀ Xs : List Nat, FreshNames L M.paramCount Xs →
      TypeOfHM (S₀.onCtx ctx) rhs (M.openVars Xs))
    (hbody : TypeOfHM { (S₀.onCtx ctx) with env := M :: (S₀.onCtx ctx).env } body τ₀) :
    ∃ Φ' S τ R,
      Infer Φ ctx (.letIn rhs body) Φ' S τ ∧
      Subst.AgreesBelow Φ S₀ (S ++ R) ∧
      τ₀ = R.onTy τ ∧
      (∀ p ∈ R, p.2.IsLC) := by
  -- A fresh opening avoiding `L`, `M.body`, and the (substituted) env.
  obtain ⟨Xs, hXlen, hXnodup, hXavoid⟩ :=
    exists_fresh_names (L ++ M.body.freeVars ++ (S₀.onCtx ctx).env.freeVars) M.paramCount
  have hXfreshL : FreshNames L M.paramCount Xs :=
    ⟨hXlen, hXnodup,
      fun x hx hc => hXavoid x hx (List.mem_append_left _ (List.mem_append_left _ hc))⟩
  have hXMbody : ∀ x ∈ Xs, x ∉ M.body.freeVars :=
    fun x hx hc => hXavoid x hx (List.mem_append_left _ (List.mem_append_right _ hc))
  have hXenv : ∀ x ∈ Xs, x ∉ (S₀.onCtx ctx).env.freeVars :=
    fun x hx hc => hXavoid x hx (List.mem_append_right _ hc)
  -- Apply the rhs IH at the fresh opening.
  obtain ⟨Φ₁, S₁, τ₁, R₁, hinfa, haga, htya, hR₁⟩ :=
    iha hwf hbelow hS₀ (hcofin Xs hXfreshL)
  have hS₁ : ∀ p ∈ S₁, p.2.IsLC := (Infer.lc hinfa hwf).2
  have hτ₁lc : τ₁.IsLC := (Infer.lc hinfa hwf).1
  have hle : Φ ≤ Φ₁ := Infer.frontier_le hinfa
  have hbelowτ₁ : Ty.BelowFvars Φ₁ τ₁ := (Infer.belowFvars hinfa hbelow).1
  have hbelowS₁ : ∀ p ∈ S₁, Ty.BelowFvars Φ₁ p.2 := (Infer.belowFvars hinfa hbelow).2
  have hwf₁ : CtxWF (S₁.onCtx ctx) := Subst.onCtx_wf hS₁ hwf
  have hbelow₁ : CtxBelow Φ₁ (S₁.onCtx ctx) := Subst.onCtx_below hbelowS₁ hle hbelow
  have hctxeq : R₁.onCtx (S₁.onCtx ctx) = S₀.onCtx ctx := by
    rw [← Subst.onCtx_append]
    exact Subst.onCtx_congr (fun v hv => (haga v hv).symm) hbelow
  -- Well-formedness / below-frontier for the algorithm's body context.
  have hwfBody : CtxWF { (S₁.onCtx ctx) with
      env := genScheme (S₁.onCtx ctx).env τ₁ :: (S₁.onCtx ctx).env } := by
    intro N hN
    rcases List.mem_cons.mp hN with rfl | hN
    · exact genScheme_wf hτ₁lc
    · exact hwf₁ N hN
  have hbelowBody : CtxBelow Φ₁ { (S₁.onCtx ctx) with
      env := genScheme (S₁.onCtx ctx).env τ₁ :: (S₁.onCtx ctx).env } := by
    intro N hN
    rcases List.mem_cons.mp hN with rfl | hN
    · show Ty.BelowFvars Φ₁ (Ty.closeOver (genVars (S₁.onCtx ctx).env τ₁) τ₁)
      exact hbelowτ₁.closeOver
    · exact hbelow₁ N hN
  -- The freshness obligation for `genScheme_generalizes`: the fresh `Xs` don't
  -- occur free in the (substituted) principal scheme body.
  have hXM'' : ∀ x ∈ Xs,
      x ∉ (R₁.onPolyTy (genScheme (S₁.onCtx ctx).env τ₁)).body.freeVars := by
    intro x hx hmem
    change x ∈ (R₁.onTy (Ty.closeOver (genVars (S₁.onCtx ctx).env τ₁) τ₁)).freeVars at hmem
    obtain ⟨v, hv, hxv⟩ := Ty.mem_freeVars_onTy_iff.mp hmem
    have hvτ₁ : v ∈ τ₁.freeVars := Ty.closeOver_freeVars_subset hv
    have hvg : v ∉ genVars (S₁.onCtx ctx).env τ₁ := fun hg => Ty.not_mem_closeOver_freeVars hg hv
    have hvenv : v ∈ (S₁.onCtx ctx).env.freeVars := by
      by_contra hc
      exact hvg (by
        simp only [genVars, List.mem_filter]
        exact ⟨hvτ₁, by simpa using hc⟩)
    obtain ⟨pt, hpt, hvpt⟩ := Env.mem_freeVars_iff.mp hvenv
    have hx_onTy : x ∈ (R₁.onTy pt.body).freeVars :=
      Ty.mem_freeVars_onTy_iff.mpr ⟨v, hvpt, hxv⟩
    have hpt_mem : R₁.onPolyTy pt ∈ (S₀.onCtx ctx).env := by
      have hmem2 : R₁.onPolyTy pt ∈ (R₁.onCtx (S₁.onCtx ctx)).env := by
        simp only [Subst.onCtx, Subst.onEnv]
        exact List.mem_map.mpr ⟨pt, hpt, rfl⟩
      rw [hctxeq] at hmem2; exact hmem2
    exact hXenv x hx (Env.mem_freeVars_iff.mpr ⟨R₁.onPolyTy pt, hpt_mem, hx_onTy⟩)
  -- Weaken the declarative body typing to the algorithm's (more general) scheme.
  have hgen : (R₁.onPolyTy (genScheme (S₁.onCtx ctx).env τ₁)).Generalizes M :=
    genScheme_generalizes hτ₁lc hR₁ hMwf hXnodup hXlen hXMbody htya hXM''
  have hbody' : TypeOfHM
      ⟨R₁.onPolyTy (genScheme (S₁.onCtx ctx).env τ₁) :: (S₀.onCtx ctx).env,
        (S₀.onCtx ctx).ctors⟩ body τ₀ :=
    TypeOfHM.weaken_scheme (env_post := []) (env := (S₀.onCtx ctx).env) (M := M) hgen hbody
  have hbody'' : TypeOfHM (R₁.onCtx { (S₁.onCtx ctx) with
      env := genScheme (S₁.onCtx ctx).env τ₁ :: (S₁.onCtx ctx).env }) body τ₀ := by
    show TypeOfHM ⟨R₁.onPolyTy (genScheme (S₁.onCtx ctx).env τ₁) :: R₁.onEnv (S₁.onCtx ctx).env,
        (S₁.onCtx ctx).ctors⟩ body τ₀
    rw [show R₁.onEnv (S₁.onCtx ctx).env = (S₀.onCtx ctx).env from congrArg Ctx.env hctxeq]
    exact hbody'
  -- Apply the body IH (specialization is `R₁`).
  obtain ⟨Φ₂, S₂, τ₂, R₂, hinfb, hagb, htyb, hR₂⟩ :=
    ihb hwfBody hbelowBody hR₁ hbody''
  refine ⟨Φ₂, S₁ ++ S₂, τ₂, R₂, .letIn hinfa hinfb, ?_, htyb, hR₂⟩
  exact Subst.AgreesBelow.trans_append hle haga hbelowS₁ hagb

/-- Principality, `letIn` case. -/
theorem Infer.complete_letIn {rhs body : Expr}
    (iha : Infer.CompleteAt rhs) (ihb : Infer.CompleteAt body) :
    Infer.CompleteAt (.letIn rhs body) := by
  intro Φ ctx S₀ τ₀ hwf hbelow hS₀ hty
  cases hty with
  | letIn hMwf hcofin heq hbody =>
    subst heq
    exact Infer.complete_letIn_aux iha ihb hwf hbelow hS₀ hMwf hcofin hbody


/-! ### Principality, `fst`/`snd` cases -/

/-- Shared core for the `fst`/`snd` principality cases. Given that `e` types as a
    pair `τα × τβ` under the specialization `S₀`, the algorithm infers a type for
    `e` and unifies it with a pair of two fresh vars; the explicit unifier (the
    `complete_app_aux` dodge, *doubled* with two fresh names `W`, `W+1`) sends those
    two component vars to `τα`/`τβ`. Returns the inference + unification, the
    `S₀`-agreement, and that the residual recovers both components. -/
theorem Infer.complete_pair_unify_aux {Φ : Nat} {ctx : Ctx} {S₀ : Subst} {e : Expr}
    {τα τβ : Ty}
    (ihe : Infer.CompleteAt e)
    (hwf : CtxWF ctx) (hbelow : CtxBelow Φ ctx) (hS₀ : ∀ p ∈ S₀, p.2.IsLC)
    (he : TypeOfHM (S₀.onCtx ctx) e (.pair τα τβ)) :
    ∃ Φ₁ S₁ S₂ τe R,
      Infer Φ ctx e Φ₁ S₁ τe ∧
      UnifyRel τe (.pair (.fvar Φ₁) (.fvar (Φ₁ + 1))) S₂ ∧
      Subst.AgreesBelow Φ S₀ ((S₁ ++ S₂) ++ R) ∧
      R.onTy (S₂.onTy (.fvar Φ₁)) = τα ∧
      R.onTy (S₂.onTy (.fvar (Φ₁ + 1))) = τβ ∧
      (∀ p ∈ R, p.2.IsLC) := by
  have hαLC : τα.IsLC := by
    have := TypeOfHM.regular he; cases this with | pair h _ => exact h
  have hβLC : τβ.IsLC := by
    have := TypeOfHM.regular he; cases this with | pair _ h => exact h
  -- STEP 1: recurse on `e`.
  obtain ⟨Φ₁, S₁, τe, R₁, hinfe, hage, htye, hR₁⟩ := ihe hwf hbelow hS₀ he
  have hS₁ : ∀ p ∈ S₁, p.2.IsLC := (Infer.lc hinfe hwf).2
  have hτeLC : τe.IsLC := (Infer.lc hinfe hwf).1
  have hle1 : Φ ≤ Φ₁ := Infer.frontier_le hinfe
  have hbe := Infer.belowFvars hinfe hbelow
  have hΦ₁τe : Φ₁ ∉ τe.freeVars := fun hm => by have := hbe.1.mem_lt _ hm; omega
  have hΦ₁1τe : Φ₁ + 1 ∉ τe.freeVars := fun hm => by have := hbe.1.mem_lt _ hm; omega
  -- STEP 2: the explicit unifier `U` (the `app` dodge, doubled).
  obtain ⟨W, hWge, hWfresh⟩ := exists_fresh_block
    (R₁.map Prod.fst ++ R₁.flatMap (fun p => p.2.freeVars)
      ++ τα.freeVars ++ τβ.freeVars) Φ₁ 2
  have hWdom : ∀ p ∈ R₁, p.1 ≠ W := by
    intro p hp _heq
    have := hWfresh p.1 (List.mem_append_left _ (List.mem_append_left _
      (List.mem_append_left _ (List.mem_map.mpr ⟨p, hp, rfl⟩))))
    omega
  have hW1dom : ∀ p ∈ R₁, p.1 ≠ W + 1 := by
    intro p hp _heq
    have := hWfresh p.1 (List.mem_append_left _ (List.mem_append_left _
      (List.mem_append_left _ (List.mem_map.mpr ⟨p, hp, rfl⟩))))
    omega
  have hWrng : ∀ p ∈ R₁, W ∉ p.2.freeVars := by
    intro p hp hc
    have := hWfresh W (List.mem_append_left _ (List.mem_append_left _
      (List.mem_append_right _ (List.mem_flatMap.mpr ⟨p, hp, hc⟩))))
    omega
  have hW1rng : ∀ p ∈ R₁, W + 1 ∉ p.2.freeVars := by
    intro p hp hc
    have := hWfresh (W + 1) (List.mem_append_left _ (List.mem_append_left _
      (List.mem_append_right _ (List.mem_flatMap.mpr ⟨p, hp, hc⟩))))
    omega
  have hWP : W ∉ τα.freeVars := fun hc => by
    have := hWfresh W (List.mem_append_left _ (List.mem_append_right _ hc)); omega
  have hW1P : W + 1 ∉ τα.freeVars := fun hc => by
    have := hWfresh (W + 1) (List.mem_append_left _ (List.mem_append_right _ hc)); omega
  have hWQ : W ∉ τβ.freeVars := fun hc => by
    have := hWfresh W (List.mem_append_right _ hc); omega
  have hW1Q : W + 1 ∉ τβ.freeVars := fun hc => by
    have := hWfresh (W + 1) (List.mem_append_right _ hc); omega
  obtain ⟨U, hUdef⟩ : ∃ U : Subst,
    U = [(Φ₁, Ty.fvar W), (Φ₁ + 1, Ty.fvar (W + 1))] ++ R₁
        ++ [(W, τα), (W + 1, τβ)] := ⟨_, rfl⟩
  have hUonTy : ∀ x, U.onTy x =
      Subst.onTy [(W, τα), (W + 1, τβ)]
        (R₁.onTy (Subst.onTy [(Φ₁, Ty.fvar W), (Φ₁ + 1, Ty.fvar (W + 1))] x)) := by
    intro x
    rw [hUdef, Subst.onTy_append, Subst.onTy_append]
  -- Identities used by the unifier computations.
  have hR₁W : R₁.onTy (Ty.fvar W) = Ty.fvar W := by
    apply Ty.substFvars_eq_self_of_no_key
    intro p hp hc
    simp only [Ty.freeVars, List.mem_singleton] at hc
    exact hWdom p hp hc
  have hR₁W1 : R₁.onTy (Ty.fvar (W + 1)) = Ty.fvar (W + 1) := by
    apply Ty.substFvars_eq_self_of_no_key
    intro p hp hc
    simp only [Ty.freeVars, List.mem_singleton] at hc
    exact hW1dom p hp hc
  have hprefix_Φ₁ :
      Subst.onTy [(Φ₁, Ty.fvar W), (Φ₁ + 1, Ty.fvar (W + 1))] (Ty.fvar Φ₁) = Ty.fvar W := by
    show Ty.substFvar (Φ₁ + 1) (Ty.fvar (W + 1)) (Ty.substFvar Φ₁ (Ty.fvar W) (Ty.fvar Φ₁))
        = Ty.fvar W
    rw [show Ty.substFvar Φ₁ (Ty.fvar W) (Ty.fvar Φ₁) = Ty.fvar W from by simp [Ty.substFvar]]
    exact Ty.substFvar_fresh (by simp only [Ty.freeVars, List.mem_singleton]; omega)
  have hprefix_Φ₂ :
      Subst.onTy [(Φ₁, Ty.fvar W), (Φ₁ + 1, Ty.fvar (W + 1))] (Ty.fvar (Φ₁ + 1)) = Ty.fvar (W + 1) := by
    show Ty.substFvar (Φ₁ + 1) (Ty.fvar (W + 1)) (Ty.substFvar Φ₁ (Ty.fvar W) (Ty.fvar (Φ₁ + 1)))
        = Ty.fvar (W + 1)
    rw [show Ty.substFvar Φ₁ (Ty.fvar W) (Ty.fvar (Φ₁ + 1)) = Ty.fvar (Φ₁ + 1) from
      Ty.substFvar_fresh (by simp only [Ty.freeVars, List.mem_singleton]; omega)]
    simp [Ty.substFvar]
  have hsufW :
      Subst.onTy [(W, τα), (W + 1, τβ)] (Ty.fvar W) = τα := by
    show Ty.substFvar (W + 1) τβ (Ty.substFvar W τα (Ty.fvar W)) = τα
    rw [show Ty.substFvar W τα (Ty.fvar W) = τα from by simp [Ty.substFvar]]
    exact Ty.substFvar_fresh hW1P
  have hsufW1 :
      Subst.onTy [(W, τα), (W + 1, τβ)] (Ty.fvar (W + 1)) = τβ := by
    show Ty.substFvar (W + 1) τβ (Ty.substFvar W τα (Ty.fvar (W + 1))) = τβ
    rw [show Ty.substFvar W τα (Ty.fvar (W + 1)) = Ty.fvar (W + 1) from
      Ty.substFvar_fresh (by simp only [Ty.freeVars, List.mem_singleton]; omega)]
    simp [Ty.substFvar]
  have hUφ₁ : U.onTy (Ty.fvar Φ₁) = τα := by
    rw [hUonTy, hprefix_Φ₁, hR₁W, hsufW]
  have hUφ₂ : U.onTy (Ty.fvar (Φ₁ + 1)) = τβ := by
    rw [hUonTy, hprefix_Φ₂, hR₁W1, hsufW1]
  have hUvar : ∀ v, v < Φ₁ → U.onTy (Ty.fvar v) = R₁.onTy (Ty.fvar v) := by
    intro v hv
    rw [hUonTy]
    rw [show Subst.onTy [(Φ₁, Ty.fvar W), (Φ₁ + 1, Ty.fvar (W + 1))] (Ty.fvar v) = Ty.fvar v from by
      show Ty.substFvar (Φ₁ + 1) (Ty.fvar (W + 1)) (Ty.substFvar Φ₁ (Ty.fvar W) (Ty.fvar v))
          = Ty.fvar v
      rw [show Ty.substFvar Φ₁ (Ty.fvar W) (Ty.fvar v) = Ty.fvar v from
        Ty.substFvar_fresh (by simp only [Ty.freeVars, List.mem_singleton]; omega)]
      exact Ty.substFvar_fresh (by simp only [Ty.freeVars, List.mem_singleton]; omega)]
    apply Ty.substFvars_eq_self_of_no_key
    intro p hp
    rcases List.mem_cons.mp hp with rfl | hp'
    · exact Subst.not_mem_onTy_freeVars hWrng
        (by simp only [Ty.freeVars, List.mem_singleton]; omega)
    · obtain rfl := List.mem_singleton.mp hp'
      exact Subst.not_mem_onTy_freeVars hW1rng
        (by simp only [Ty.freeVars, List.mem_singleton]; omega)
  have hUτe : U.onTy τe = Ty.pair τα τβ := by
    rw [hUonTy]
    rw [show Subst.onTy [(Φ₁, Ty.fvar W), (Φ₁ + 1, Ty.fvar (W + 1))] τe = τe from
      Ty.substFvars_eq_self_of_no_key (by
        intro p hp
        rcases List.mem_cons.mp hp with rfl | hp'
        · exact hΦ₁τe
        · obtain rfl := List.mem_singleton.mp hp'
          exact hΦ₁1τe)]
    rw [← htye]
    apply Ty.substFvars_eq_self_of_no_key
    intro p hp
    rcases List.mem_cons.mp hp with rfl | hp'
    · simp only [Ty.freeVars, List.mem_dedup, List.mem_append, not_or]
      exact ⟨hWP, hWQ⟩
    · obtain rfl := List.mem_singleton.mp hp'
      simp only [Ty.freeVars, List.mem_dedup, List.mem_append, not_or]
      exact ⟨hW1P, hW1Q⟩
  have hUni : Unifies U τe (Ty.pair (Ty.fvar Φ₁) (Ty.fvar (Φ₁ + 1))) := by
    show U.onTy τe = U.onTy (Ty.pair (Ty.fvar Φ₁) (Ty.fvar (Φ₁ + 1)))
    rw [hUτe, Subst.onTy_pair, hUφ₁, hUφ₂]
  -- Realise the unifier as `S₂`, and factor `U` through it.
  obtain ⟨S₂, h₂⟩ := UnifyRel.complete hτeLC
    (ContainsBvarsUpTo.pair ContainsBvarsUpTo.fvar ContainsBvarsUpTo.fvar) hUni
  have hUlc : ∀ p ∈ U, p.2.IsLC := by
    rw [hUdef]
    intro p hp
    rcases List.mem_append.mp hp with hp' | hp'
    · rcases List.mem_append.mp hp' with hp'' | hp''
      · rcases List.mem_cons.mp hp'' with rfl | hp'''
        · exact ContainsBvarsUpTo.fvar
        · obtain rfl := List.mem_singleton.mp hp'''
          exact ContainsBvarsUpTo.fvar
      · exact hR₁ p hp''
    · rcases List.mem_cons.mp hp' with rfl | hp''
      · exact hαLC
      · obtain rfl := List.mem_singleton.mp hp''
        exact hβLC
  obtain ⟨R₂, hR₂, hR₂lc⟩ := UnifyRel.greatest_lc h₂ U hUlc hUni
  -- Assemble.
  refine ⟨Φ₁, S₁, S₂, τe, R₂, hinfe, h₂, ?_, ?_, ?_, hR₂lc⟩
  · intro v hv
    have ht1 : Ty.BelowFvars Φ₁ (S₁.onTy (Ty.fvar v)) :=
      Subst.onTy_belowFvars hbe.2 (Ty.BelowFvars.fvar (by omega))
    have hΦ₁t : Φ₁ ∉ (S₁.onTy (Ty.fvar v)).freeVars := fun hm => by
      have := ht1.mem_lt _ hm; omega
    have hΦ₁1t : Φ₁ + 1 ∉ (S₁.onTy (Ty.fvar v)).freeVars := fun hm => by
      have := ht1.mem_lt _ hm; omega
    have hWt : W ∉ (S₁.onTy (Ty.fvar v)).freeVars := fun hm => by
      have := ht1.mem_lt _ hm; omega
    have hW1t : W + 1 ∉ (S₁.onTy (Ty.fvar v)).freeVars := fun hm => by
      have := ht1.mem_lt _ hm; omega
    have hWR₁t : W ∉ (R₁.onTy (S₁.onTy (Ty.fvar v))).freeVars :=
      Subst.not_mem_onTy_freeVars hWrng hWt
    have hW1R₁t : W + 1 ∉ (R₁.onTy (S₁.onTy (Ty.fvar v))).freeVars :=
      Subst.not_mem_onTy_freeVars hW1rng hW1t
    calc S₀.onTy (Ty.fvar v)
        = (S₁ ++ R₁).onTy (Ty.fvar v) := hage v hv
      _ = R₁.onTy (S₁.onTy (Ty.fvar v)) := by rw [Subst.onTy_append]
      _ = U.onTy (S₁.onTy (Ty.fvar v)) := by
            rw [hUonTy,
              show Subst.onTy [(Φ₁, Ty.fvar W), (Φ₁ + 1, Ty.fvar (W + 1))]
                  (S₁.onTy (Ty.fvar v)) = S₁.onTy (Ty.fvar v) from
                Ty.substFvars_eq_self_of_no_key (by
                  intro p hp
                  rcases List.mem_cons.mp hp with rfl | hp'
                  · exact hΦ₁t
                  · obtain rfl := List.mem_singleton.mp hp'
                    exact hΦ₁1t)]
            exact (Ty.substFvars_eq_self_of_no_key (by
              intro p hp
              rcases List.mem_cons.mp hp with rfl | hp'
              · exact hWR₁t
              · obtain rfl := List.mem_singleton.mp hp'
                exact hW1R₁t)).symm
      _ = R₂.onTy (S₂.onTy (S₁.onTy (Ty.fvar v))) := hR₂ (S₁.onTy (Ty.fvar v))
      _ = ((S₁ ++ S₂) ++ R₂).onTy (Ty.fvar v) := by simp only [Subst.onTy_append]
  · rw [← hR₂ (Ty.fvar Φ₁), hUφ₁]
  · rw [← hR₂ (Ty.fvar (Φ₁ + 1)), hUφ₂]

/-- Principality, `fst` case. -/
theorem Infer.complete_fst {e : Expr} (ihe : Infer.CompleteAt e) :
    Infer.CompleteAt (.fst e) := by
  intro Φ ctx S₀ τ₀ hwf hbelow hS₀ hty
  cases hty with
  | fst he =>
    obtain ⟨Φ₁, S₁, S₂, τe, R, hinfe, huni, hag, hα, _, hRlc⟩ :=
      Infer.complete_pair_unify_aux ihe hwf hbelow hS₀ he
    exact ⟨Φ₁ + 2, S₁ ++ S₂, S₂.onTy (.fvar Φ₁), R, .fst hinfe huni, hag, hα.symm, hRlc⟩

/-- Principality, `snd` case. -/
theorem Infer.complete_snd {e : Expr} (ihe : Infer.CompleteAt e) :
    Infer.CompleteAt (.snd e) := by
  intro Φ ctx S₀ τ₀ hwf hbelow hS₀ hty
  cases hty with
  | snd he =>
    obtain ⟨Φ₁, S₁, S₂, τe, R, hinfe, huni, hag, _, hβ, hRlc⟩ :=
      Infer.complete_pair_unify_aux ihe hwf hbelow hS₀ he
    exact ⟨Φ₁ + 2, S₁ ++ S₂, S₂.onTy (.fvar (Φ₁ + 1)), R, .snd hinfe huni, hag, hβ.symm, hRlc⟩
/-- Reconstruct a list from the length-indexed lookups into it. The map of
    `Vs[i]?.getD d` over `range Vs.length` is just `Vs`. -/
private theorem range_length_map_getD {Vs : List Ty} {d : Ty} :
    (List.range Vs.length).map (fun i => (Vs[i]?).getD d) = Vs := by
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp only [List.getElem_map, List.getElem_range]
    rw [List.getElem?_eq_getElem h2]
    rfl

/-- The instantiation list of a `Forall₂ (InstantiatesBy Vs)` (when every source
    type's bvars are within `Vs.length`) is exactly the element-wise `openWith Vs`. -/
private theorem instContents_eq_openWith {Vs : List Ty} {cs insts : List Ty}
    (hforall : List.Forall₂ (InstantiatesBy Vs) cs insts)
    (hbv : ∀ c ∈ cs, ContainsBvarsUpTo Vs.length c) :
    insts = cs.map (Ty.openWith Vs) := by
  induction hforall with
  | nil => rfl
  | @cons c inst cs' insts' hhead _ ih =>
    simp only [List.map_cons]
    have hc_bv : ContainsBvarsUpTo Vs.length c := hbv c List.mem_cons_self
    have heq := InstantiatesBy.eq_openWith_range hhead hc_bv
    rw [range_length_map_getD] at heq
    rw [heq]
    congr 1
    exact ih (fun c' hc' => hbv c' (List.mem_cons_of_mem _ hc'))

/-- A composition law for `Subst.onCtx`: if two substitutions compose on every
    monotype, they compose on whole contexts. -/
private theorem Subst.onCtx_comp_of_onTy_eq {A B C : Subst} {ctx : Ctx}
    (h : ∀ τ, A.onTy τ = B.onTy (C.onTy τ)) :
    A.onCtx ctx = B.onCtx (C.onCtx ctx) := by
  simp only [Subst.onCtx, Subst.onEnv, List.map_map]
  congr 1
  apply List.map_congr_left
  intro M _
  simp only [Subst.onPolyTy, Function.comp_apply, h M.body]


/-- **Branch-list completeness** companion of `Infer.complete`: if each branch
    body is principal (`CompleteAt`), and every branch types declaratively under
    a residual `R` (an LC specialization, below the frontier `Φ`), then
    `InferBranches` succeeds and the declarative typing factors through it via an
    LC residual `R'` (`R = R' ∘ S` below `Φ`). The companion to `match_`
    principality. -/
theorem InferBranches.complete {branches : List (MatchPattern × Expr)} :
    ∀ {Φ : Nat} {ctx : Ctx} {tyName : TyName} {ta : List Ty} {ρ : Ty} {R : Subst},
    (∀ br ∈ branches, Infer.CompleteAt br.2) →
    CtxWF ctx → CtxBelow Φ ctx →
    (∀ t ∈ ta, t.IsLC) → (∀ t ∈ ta, Ty.BelowFvars Φ t) →
    ρ.IsLC → Ty.BelowFvars Φ ρ →
    (∀ p ∈ R, p.2.IsLC) →
    (∀ br ∈ branches, TypeOfMatchBranch (R.onCtx ctx) br tyName (ta.map R.onTy) (R.onTy ρ)) →
    ∃ Φ' S R',
      InferBranches Φ ctx tyName ta ρ branches Φ' S ∧
      Subst.AgreesBelow Φ R (S ++ R') ∧
      (∀ p ∈ R', p.2.IsLC) := by
  induction branches with
  | nil =>
    intro Φ ctx tyName ta ρ R _ihbr _hwf _hbelow _hta _hbta _hρ _hbρ hR _hdecl
    exact ⟨Φ, [], R, InferBranches.nil, fun v _ => by rw [List.nil_append], hR⟩
  | cons head rest ih =>
    intro Φ ctx tyName ta ρ R ihbr hwf hbelow hta hbta hρ hbρ hR hdecl
    obtain ⟨pat, body⟩ := head
    have hdhead := hdecl (pat, body) (List.mem_cons_self ..)
    cases hdhead with
    | mk hlook htyName hpc hpc2 hforall hpb hbctx hbodyty =>
      expose_names
      -- paramCount equality, in the un-substituted `ta` form
      have hpc' : ctor.paramCount = ta.length := hpc.trans (by rw [List.length_map])
      -- the declarative instantiations are exactly `openWith` of the substituted tyArgs
      have hinsts : instContents = ctor.contents.map (Ty.openWith (ta.map R.onTy)) :=
        instContents_eq_openWith hforall (fun c hc => hpc ▸ ctor.bound c hc)
      -- recast `hbodyty` over the algorithmic body context `R.onCtx bodyCtx_alg`
      rw [hbctx, hpb, hinsts] at hbodyty
      have hbodyWF : CtxWF { ctx with
          env := (ctor.contents.map (Ty.openWith ta)).map PolyTy.mkTrivial ++ ctx.env } :=
        branchBindings_wf hwf hta hpc'
      have hbodyBelow : CtxBelow Φ { ctx with
          env := (ctor.contents.map (Ty.openWith ta)).map PolyTy.mkTrivial ++ ctx.env } :=
        branchBindings_below hbelow hbta
      have hbodyty2 : TypeOfHM (R.onCtx { ctx with
          env := (ctor.contents.map (Ty.openWith ta)).map PolyTy.mkTrivial ++ ctx.env })
          body (R.onTy ρ) := by
        rw [Subst.onCtx_branchBindings hR]; exact hbodyty
      -- STEP: apply the head branch's IH (principality of `body`)
      obtain ⟨Φ_b, S_b, τ_b, R_b, hinfbody, hagbody, htybody, hR_b⟩ :=
        ihbr (pat, body) (List.mem_cons_self ..) hbodyWF hbodyBelow hR hbodyty2
      have hbodyLC := Infer.lc hinfbody hbodyWF
      have hτb_lc : τ_b.IsLC := hbodyLC.1
      have hS_b : ∀ p ∈ S_b, p.2.IsLC := hbodyLC.2
      have hbb := Infer.belowFvars hinfbody hbodyBelow
      have hle_b : Φ ≤ Φ_b := Infer.frontier_le hinfbody
      -- STEP: `R_b` already unifies `τ_b` with `S_b.onTy ρ`
      have hUni : Unifies R_b τ_b (S_b.onTy ρ) := by
        show R_b.onTy τ_b = R_b.onTy (S_b.onTy ρ)
        rw [← htybody, ← Subst.onTy_append]
        exact Subst.onTy_congr hagbody hbρ
      obtain ⟨S_u, h_u⟩ := UnifyRel.complete hτb_lc (Subst.onTy_lc hS_b hρ) hUni
      obtain ⟨R_u, hR_u_eq, hR_u⟩ := UnifyRel.greatest_lc h_u R_b hR_b hUni
      have hS_u : ∀ p ∈ S_u, p.2.IsLC := UnifyRel.lc h_u hτb_lc (Subst.onTy_lc hS_b hρ)
      have hS_u_below : ∀ p ∈ S_u, Ty.BelowFvars Φ_b p.2 :=
        UnifyRel.belowFvars h_u hbb.1 (Subst.onTy_belowFvars hbb.2 (hbρ.mono hle_b))
      -- STEP: hypotheses for the recursion on `rest`
      have hwf' : CtxWF (S_u.onCtx (S_b.onCtx ctx)) :=
        Subst.onCtx_wf hS_u (Subst.onCtx_wf hS_b hwf)
      have hbelow_Sb : CtxBelow Φ_b (S_b.onCtx ctx) := Subst.onCtx_below hbb.2 hle_b hbelow
      have hbelow' : CtxBelow Φ_b (S_u.onCtx (S_b.onCtx ctx)) :=
        Subst.onCtx_below hS_u_below (le_refl _) hbelow_Sb
      have hta' : ∀ t ∈ ta.map (fun t => S_u.onTy (S_b.onTy t)), t.IsLC := by
        intro t' ht'; obtain ⟨t0, ht0, rfl⟩ := List.mem_map.mp ht'
        exact Subst.onTy_lc hS_u (Subst.onTy_lc hS_b (hta t0 ht0))
      have hbta' : ∀ t ∈ ta.map (fun t => S_u.onTy (S_b.onTy t)), Ty.BelowFvars Φ_b t := by
        intro t' ht'; obtain ⟨t0, ht0, rfl⟩ := List.mem_map.mp ht'
        exact Subst.onTy_belowFvars hS_u_below
          (Subst.onTy_belowFvars hbb.2 ((hbta t0 ht0).mono hle_b))
      have hρ' : (S_u.onTy (S_b.onTy ρ)).IsLC := Subst.onTy_lc hS_u (Subst.onTy_lc hS_b hρ)
      have hbρ' : Ty.BelowFvars Φ_b (S_u.onTy (S_b.onTy ρ)) :=
        Subst.onTy_belowFvars hS_u_below (Subst.onTy_belowFvars hbb.2 (hbρ.mono hle_b))
      -- STEP: factoring identities for the recursion's declarative typings
      have key_t : ∀ {t : Ty}, Ty.BelowFvars Φ t →
          R_u.onTy (S_u.onTy (S_b.onTy t)) = R.onTy t := by
        intro t ht
        rw [← hR_u_eq (S_b.onTy t), ← Subst.onTy_append]
        exact (Subst.onTy_congr hagbody ht).symm
      have hctx_eq : R_u.onCtx (S_u.onCtx (S_b.onCtx ctx)) = R.onCtx ctx := by
        rw [← Subst.onCtx_comp_of_onTy_eq hR_u_eq, ← Subst.onCtx_append]
        exact Subst.onCtx_congr (fun v hv => (hagbody v hv).symm) hbelow
      have hta_eq : (ta.map (fun t => S_u.onTy (S_b.onTy t))).map R_u.onTy = ta.map R.onTy := by
        rw [List.map_map]
        apply List.map_congr_left
        intro t ht
        simpa using key_t (hbta t ht)
      have hρ_eq : R_u.onTy (S_u.onTy (S_b.onTy ρ)) = R.onTy ρ := key_t hbρ
      have hdecl' : ∀ br ∈ rest, TypeOfMatchBranch (R_u.onCtx (S_u.onCtx (S_b.onCtx ctx)))
          br tyName ((ta.map (fun t => S_u.onTy (S_b.onTy t))).map R_u.onTy)
          (R_u.onTy (S_u.onTy (S_b.onTy ρ))) := by
        intro br hbr
        rw [hctx_eq, hta_eq, hρ_eq]
        exact hdecl br (List.mem_cons_of_mem _ hbr)
      -- STEP: recurse on `rest`
      obtain ⟨Φ', S_r, R_r, hinfrest, hagrest, hR_r⟩ :=
        ih (fun br hbr => ihbr br (List.mem_cons_of_mem _ hbr))
          hwf' hbelow' hta' hbta' hρ' hbρ' hR_u hdecl'
      -- STEP: assemble
      refine ⟨Φ', S_b ++ S_u ++ S_r, R_r, ?_, ?_, hR_r⟩
      · exact InferBranches.cons hlook htyName hpc' hpc2 hinfbody h_u hinfrest
      · intro v hv
        have hbv1 : Ty.BelowFvars Φ_b (S_b.onTy (.fvar v)) :=
          Subst.onTy_belowFvars hbb.2 (.fvar (by omega))
        have hbv2 : Ty.BelowFvars Φ_b (S_u.onTy (S_b.onTy (.fvar v))) :=
          Subst.onTy_belowFvars hS_u_below hbv1
        calc R.onTy (.fvar v)
            = (S_b ++ R_b).onTy (.fvar v) := hagbody v hv
          _ = R_b.onTy (S_b.onTy (.fvar v)) := by rw [Subst.onTy_append]
          _ = R_u.onTy (S_u.onTy (S_b.onTy (.fvar v))) := hR_u_eq (S_b.onTy (.fvar v))
          _ = (S_r ++ R_r).onTy (S_u.onTy (S_b.onTy (.fvar v))) := Subst.onTy_congr hagrest hbv2
          _ = ((S_b ++ S_u ++ S_r) ++ R_r).onTy (.fvar v) := by simp only [Subst.onTy_append]


/-- The `i`-th allocated fresh name (`i < k`) is `Φ + i`. -/
private theorem freshVars_getElem? {Φ k i : Nat} (hi : i < k) :
    (freshVars Φ k)[i]? = some (Φ + i) := by
  simp only [freshVars, List.getElem?_map, List.getElem?_range hi, Option.map_some]


/-- Principality, `match_` case (factored with named binders). Recurse on the
    scrutinee, then realise the `customTy`-unifier explicitly via the `app`-style
    dodge generalised to `arity + 1` fresh variables (the `arity` scrutinee-type
    arguments plus the result variable), realise it with `UnifyRel.complete` and
    factor through with `greatest_lc`, thread the branch list with
    `InferBranches.complete`, and assemble the agreement chain. -/
theorem Infer.complete_match_aux {scrut : Expr} {branches : List (MatchPattern × Expr)}
    {Φ : Nat} {ctx : Ctx} {S₀ : Subst} {tyName : TyName} {tyArgs : List Ty} {τ₀ : Ty}
    (ihscrut : Infer.CompleteAt scrut)
    (ihbranches : ∀ br ∈ branches, Infer.CompleteAt br.2)
    (hwf : CtxWF ctx) (hbelow : CtxBelow Φ ctx) (hS₀ : ∀ p ∈ S₀, p.2.IsLC)
    (hscrut_decl : TypeOfHM (S₀.onCtx ctx) scrut (.customTy tyName tyArgs))
    (hne : branches ≠ [])
    (hbranches_decl : ∀ br ∈ branches, TypeOfMatchBranch (S₀.onCtx ctx) br tyName tyArgs τ₀) :
    ∃ Φ' S τ R,
      Infer Φ ctx (.match_ scrut branches) Φ' S τ ∧
      Subst.AgreesBelow Φ S₀ (S ++ R) ∧
      τ₀ = R.onTy τ ∧ (∀ p ∈ R, p.2.IsLC) := by
  -- STEP 1: scrutinee IH.
  obtain ⟨Φ₁, S₁, τs, R₁, hinfs, hags, htys, hR₁⟩ := ihscrut hwf hbelow hS₀ hscrut_decl
  have hS₁ := (Infer.lc hinfs hwf).2
  have hτsLC := (Infer.lc hinfs hwf).1
  have hbs := Infer.belowFvars hinfs hbelow
  have hle1 := Infer.frontier_le hinfs
  have hwf₁ := Subst.onCtx_wf hS₁ hwf
  have hbelow₁ := Subst.onCtx_below hbs.2 hle1 hbelow
  have hctxeq : R₁.onCtx (S₁.onCtx ctx) = S₀.onCtx ctx := by
    rw [← Subst.onCtx_append]
    exact Subst.onCtx_congr (fun v hv => (hags v hv).symm) hbelow
  have htyArgs_lc : ∀ t ∈ tyArgs, t.IsLC := by
    have hreg := TypeOfHM.regular hscrut_decl
    cases hreg with
    | customTy h => exact h
  have hτ₀_lc : τ₀.IsLC := by
    obtain ⟨hd, tl, hcons⟩ := List.exists_cons_of_ne_nil hne
    have hmem_hd : hd ∈ branches := by rw [hcons]; exact List.mem_cons_self ..
    exact TypeOfMatchBranch.regular (hbranches_decl hd hmem_hd)
  -- STEP 2: super-fresh block and the explicit unifier `U`.
  obtain ⟨W₀, hW₀ge, hW₀fresh⟩ := exists_fresh_block
    (R₁.map Prod.fst ++ R₁.flatMap (fun p => p.2.freeVars)
      ++ tyArgs.flatMap Ty.freeVars ++ τ₀.freeVars) Φ₁ (tyArgs.length + 1)
  obtain ⟨U, hUdef⟩ : ∃ U : Subst,
    U = (freshVars Φ₁ (tyArgs.length + 1)).zip ((freshVars W₀ (tyArgs.length + 1)).map (Ty.fvar ·))
        ++ R₁ ++ (freshVars W₀ (tyArgs.length + 1)).zip (tyArgs ++ [τ₀]) := ⟨_, rfl⟩
  have hUonTy : ∀ x, U.onTy x =
      Subst.onTy ((freshVars W₀ (tyArgs.length + 1)).zip (tyArgs ++ [τ₀]))
        (R₁.onTy (Subst.onTy ((freshVars Φ₁ (tyArgs.length + 1)).zip
          ((freshVars W₀ (tyArgs.length + 1)).map (Ty.fvar ·))) x)) := by
    intro x
    rw [hUdef, Subst.onTy_append, Subst.onTy_append]
  -- Freshness facts about the super-fresh block `[W₀, W₀ + arity + 1)`.
  have hWi_mem : ∀ {i : Nat}, i < tyArgs.length + 1 →
      W₀ + i ∈ freshVars W₀ (tyArgs.length + 1) := by
    intro i hi
    simp only [freshVars, List.mem_map, List.mem_range]
    exact ⟨i, hi, rfl⟩
  have hWs_notin_R₁keys : ∀ w ∈ freshVars W₀ (tyArgs.length + 1), w ∉ R₁.map Prod.fst := by
    intro w hw hc
    have hwge := freshVars_ge w hw
    have := hW₀fresh w (List.mem_append_left _ (List.mem_append_left _
      (List.mem_append_left _ hc)))
    omega
  have hWs_R₁range : ∀ w ∈ freshVars W₀ (tyArgs.length + 1), ∀ q ∈ R₁, w ∉ q.2.freeVars := by
    intro w hw q hq hc
    have hwge := freshVars_ge w hw
    have := hW₀fresh w (List.mem_append_left _ (List.mem_append_left _
      (List.mem_append_right _ (List.mem_flatMap.mpr ⟨q, hq, hc⟩))))
    omega
  have htyArgs_belowW₀ : ∀ t ∈ tyArgs, Ty.BelowFvars W₀ t := by
    intro t ht
    apply Ty.BelowFvars.of_freeVars_lt
    intro v hv
    exact hW₀fresh v (List.mem_append_left _ (List.mem_append_right _
      (List.mem_flatMap.mpr ⟨t, ht, hv⟩)))
  have hτ₀_belowW₀ : Ty.BelowFvars W₀ τ₀ := by
    apply Ty.BelowFvars.of_freeVars_lt
    intro v hv
    exact hW₀fresh v (List.mem_append_right _ hv)
  -- STEP 3: the key per-index value of `U` (= `tyArgs[i]` for `i < arity`, `τ₀` at `arity`).
  have hU_index : ∀ (i : Nat) (v : Ty), i < tyArgs.length + 1 →
      (tyArgs ++ [τ₀])[i]? = some v → U.onTy (Ty.fvar (Φ₁ + i)) = v := by
    intro i v hi hvi
    rw [hUonTy]
    have hL1 : Subst.onTy ((freshVars Φ₁ (tyArgs.length + 1)).zip
        ((freshVars W₀ (tyArgs.length + 1)).map (Ty.fvar ·))) (Ty.fvar (Φ₁ + i))
        = Ty.fvar (W₀ + i) := by
      apply Ty.substFvars_zip_fvar_eq' freshVars_nodup (freshVars_getElem? hi)
      · rw [List.getElem?_map, freshVars_getElem? hi]; rfl
      · intro X hX hc
        simp only [Ty.freeVars, List.mem_singleton] at hc
        have hXlt := freshVars_lt X hX
        omega
    rw [hL1]
    have hL2 : R₁.onTy (Ty.fvar (W₀ + i)) = Ty.fvar (W₀ + i) := by
      apply Ty.substFvars_eq_self_of_no_key
      intro p hp hc
      simp only [Ty.freeVars, List.mem_singleton] at hc
      have hkey : p.1 ∈ R₁.map Prod.fst := List.mem_map.mpr ⟨p, hp, rfl⟩
      rw [hc] at hkey
      exact hWs_notin_R₁keys (W₀ + i) (hWi_mem hi) hkey
    rw [hL2]
    apply Ty.substFvars_zip_fvar_eq' freshVars_nodup (freshVars_getElem? hi) hvi
    intro w hw hc
    have hwge := freshVars_ge w hw
    have hvmem : v ∈ (tyArgs ++ [τ₀]) := List.mem_of_getElem? hvi
    have hvbelow : Ty.BelowFvars W₀ v := by
      rcases List.mem_append.mp hvmem with hvt | hvτ
      · exact htyArgs_belowW₀ v hvt
      · have hvτ₀ : v = τ₀ := List.mem_singleton.mp hvτ
        rw [hvτ₀]; exact hτ₀_belowW₀
    have := hvbelow.mem_lt w hc
    omega
  -- STEP 4: `U` unifies `τs` with the fresh `customTy`.
  have hmap_eq : ((freshVars Φ₁ tyArgs.length).map (Ty.fvar ·)).map U.onTy = tyArgs := by
    apply List.ext_getElem?
    intro i
    rcases Nat.lt_or_ge i tyArgs.length with hi | hi
    · rw [List.getElem?_map, List.getElem?_map, freshVars_getElem? hi]
      simp only [Option.map_some]
      rw [List.getElem?_eq_getElem hi]
      congr 1
      exact hU_index i (tyArgs[i]'hi) (by omega)
        (by rw [List.getElem?_append_left hi, List.getElem?_eq_getElem hi])
    · rw [List.getElem?_eq_none (by simp only [List.length_map, freshVars_length]; exact hi),
        List.getElem?_eq_none hi]
  have hA_id_τs : Subst.onTy ((freshVars Φ₁ (tyArgs.length + 1)).zip
      ((freshVars W₀ (tyArgs.length + 1)).map (Ty.fvar ·))) τs = τs := by
    apply Ty.substFvars_eq_self_of_no_key
    intro p hp hc
    have hp1 : p.1 ∈ freshVars Φ₁ (tyArgs.length + 1) := (List.of_mem_zip hp).1
    have hge := freshVars_ge p.1 hp1
    have hlt := hbs.1.mem_lt p.1 hc
    omega
  have hC_id_custom : Subst.onTy ((freshVars W₀ (tyArgs.length + 1)).zip (tyArgs ++ [τ₀]))
      (Ty.customTy tyName tyArgs) = Ty.customTy tyName tyArgs := by
    apply Ty.substFvars_eq_self_of_no_key
    intro p hp hc
    have hp1 : p.1 ∈ freshVars W₀ (tyArgs.length + 1) := (List.of_mem_zip hp).1
    have hge := freshVars_ge p.1 hp1
    have hcb : Ty.BelowFvars W₀ (Ty.customTy tyName tyArgs) := .customTy htyArgs_belowW₀
    have hlt := hcb.mem_lt p.1 hc
    omega
  have hUL : U.onTy τs = Ty.customTy tyName tyArgs := by
    rw [hUonTy, hA_id_τs, ← htys]
    exact hC_id_custom
  have hUR : U.onTy (Ty.customTy tyName ((freshVars Φ₁ tyArgs.length).map (Ty.fvar ·)))
      = Ty.customTy tyName tyArgs := by
    rw [Subst.onTy_customTy, hmap_eq]
  have hUni : Unifies U τs (Ty.customTy tyName ((freshVars Φ₁ tyArgs.length).map (Ty.fvar ·))) := by
    show U.onTy τs = U.onTy (Ty.customTy tyName ((freshVars Φ₁ tyArgs.length).map (Ty.fvar ·)))
    rw [hUL, hUR]
  -- STEP 5: realise the unifier as `S₂`, factor `U` through it.
  have hcustomTy_lc : (Ty.customTy tyName ((freshVars Φ₁ tyArgs.length).map (Ty.fvar ·))).IsLC :=
    ContainsBvarsUpTo.customTy (fun t ht => by
      obtain ⟨x, _, rfl⟩ := List.mem_map.mp ht; exact ContainsBvarsUpTo.fvar)
  obtain ⟨S₂, h₂⟩ := UnifyRel.complete hτsLC hcustomTy_lc hUni
  have hUlc : ∀ p ∈ U, p.2.IsLC := by
    rw [hUdef]
    intro p hp
    rcases List.mem_append.mp hp with hp' | hp'
    · rcases List.mem_append.mp hp' with hp'' | hp''
      · have hmem := (List.of_mem_zip hp'').2
        obtain ⟨x, _, hxeq⟩ := List.mem_map.mp hmem
        rw [← hxeq]; exact ContainsBvarsUpTo.fvar
      · exact hR₁ p hp''
    · have hmem := (List.of_mem_zip hp').2
      rcases List.mem_append.mp hmem with ht | hτ
      · exact htyArgs_lc p.2 ht
      · have hpτ₀ : p.2 = τ₀ := List.mem_singleton.mp hτ
        rw [hpτ₀]; exact hτ₀_lc
  obtain ⟨R₂, hR₂_eq, hR₂lc⟩ := UnifyRel.greatest_lc h₂ U hUlc hUni
  have hS₂ : ∀ p ∈ S₂, p.2.IsLC := UnifyRel.lc h₂ hτsLC hcustomTy_lc
  have hbS₂ : ∀ p ∈ S₂, Ty.BelowFvars (Φ₁ + tyArgs.length + 1) p.2 := by
    apply UnifyRel.belowFvars h₂ (hbs.1.mono (by omega))
    apply Ty.BelowFvars.customTy
    intro t ht
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp ht
    exact Ty.BelowFvars.fvar (by have := freshVars_lt x hx; omega)
  -- STEP 6: residual facts connecting `R₂` to the declarative data.
  have hUeqR₁ : ∀ v, v < Φ₁ → U.onTy (Ty.fvar v) = R₁.onTy (Ty.fvar v) := by
    intro v hv
    rw [hUonTy]
    have hA_id : Subst.onTy ((freshVars Φ₁ (tyArgs.length + 1)).zip
        ((freshVars W₀ (tyArgs.length + 1)).map (Ty.fvar ·))) (Ty.fvar v) = Ty.fvar v := by
      apply Ty.substFvars_eq_self_of_no_key
      intro p hp hc
      simp only [Ty.freeVars, List.mem_singleton] at hc
      have hp1 : p.1 ∈ freshVars Φ₁ (tyArgs.length + 1) := (List.of_mem_zip hp).1
      have := freshVars_ge p.1 hp1
      omega
    rw [hA_id]
    apply Ty.substFvars_eq_self_of_no_key
    intro p hp hc
    have hp1 : p.1 ∈ freshVars W₀ (tyArgs.length + 1) := (List.of_mem_zip hp).1
    have hge := freshVars_ge p.1 hp1
    exact Subst.not_mem_onTy_freeVars (hWs_R₁range p.1 hp1)
      (by simp only [Ty.freeVars, List.mem_singleton]; omega) hc
  have hR₂ctx : R₂.onCtx (S₂.onCtx (S₁.onCtx ctx)) = S₀.onCtx ctx := by
    rw [← Subst.onCtx_comp_of_onTy_eq hR₂_eq, Subst.onCtx_congr hUeqR₁ hbelow₁, hctxeq]
  have hta_lc : ∀ t ∈ ((freshVars Φ₁ tyArgs.length).map (Ty.fvar ·)).map S₂.onTy, t.IsLC := by
    intro t ht
    obtain ⟨t0, ht0, rfl⟩ := List.mem_map.mp ht
    obtain ⟨x, _, rfl⟩ := List.mem_map.mp ht0
    exact Subst.onTy_lc hS₂ ContainsBvarsUpTo.fvar
  have hta_below : ∀ t ∈ ((freshVars Φ₁ tyArgs.length).map (Ty.fvar ·)).map S₂.onTy,
      Ty.BelowFvars (Φ₁ + tyArgs.length + 1) t := by
    intro t ht
    obtain ⟨t0, ht0, rfl⟩ := List.mem_map.mp ht
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp ht0
    exact Subst.onTy_belowFvars hbS₂ (Ty.BelowFvars.fvar (by have := freshVars_lt x hx; omega))
  have hρ_lc : (S₂.onTy (Ty.fvar (Φ₁ + tyArgs.length))).IsLC :=
    Subst.onTy_lc hS₂ ContainsBvarsUpTo.fvar
  have hρ_below : Ty.BelowFvars (Φ₁ + tyArgs.length + 1)
      (S₂.onTy (Ty.fvar (Φ₁ + tyArgs.length))) :=
    Subst.onTy_belowFvars hbS₂ (Ty.BelowFvars.fvar (by omega))
  have hta_R₂ : (((freshVars Φ₁ tyArgs.length).map (Ty.fvar ·)).map S₂.onTy).map R₂.onTy
      = tyArgs := by
    rw [List.map_map]
    exact Eq.trans (List.map_congr_left (fun t _ => (hR₂_eq t).symm)) hmap_eq
  have hρ_R₂ : R₂.onTy (S₂.onTy (Ty.fvar (Φ₁ + tyArgs.length))) = τ₀ := by
    rw [← hR₂_eq]
    exact hU_index tyArgs.length τ₀ (by omega)
      (by rw [List.getElem?_append_right (Nat.le_refl _)]; simp)
  -- STEP 7: branch declarative typings, recast over the algorithmic data.
  have hbr' : ∀ br ∈ branches,
      TypeOfMatchBranch (R₂.onCtx (S₂.onCtx (S₁.onCtx ctx))) br tyName
        ((((freshVars Φ₁ tyArgs.length).map (Ty.fvar ·)).map S₂.onTy).map R₂.onTy)
        (R₂.onTy (S₂.onTy (Ty.fvar (Φ₁ + tyArgs.length)))) := by
    intro br hbr
    rw [hR₂ctx, hta_R₂, hρ_R₂]
    exact hbranches_decl br hbr
  -- STEP 8: thread the branch list with `InferBranches.complete`.
  obtain ⟨Φ₃, S₃, R₃, hinfbr, hagbr, hR₃lc⟩ :=
    InferBranches.complete ihbranches (Subst.onCtx_wf hS₂ hwf₁)
      (Subst.onCtx_below hbS₂ (by omega) hbelow₁)
      hta_lc hta_below hρ_lc hρ_below hR₂lc hbr'
  -- STEP 9: assemble.
  refine ⟨Φ₃, S₁ ++ S₂ ++ S₃, S₃.onTy (S₂.onTy (Ty.fvar (Φ₁ + tyArgs.length))), R₃,
    Infer.match_ hinfs hne h₂ hinfbr, ?_, ?_, hR₃lc⟩
  · intro v hv
    have hag2 : ∀ w, w < Φ₁ → R₁.onTy (Ty.fvar w) = (S₂ ++ R₂).onTy (Ty.fvar w) := by
      intro w hw
      rw [Subst.onTy_append, ← hR₂_eq]
      exact (hUeqR₁ w hw).symm
    have ht1 : Ty.BelowFvars Φ₁ (S₁.onTy (Ty.fvar v)) :=
      Subst.onTy_belowFvars hbs.2 (Ty.BelowFvars.fvar (by omega))
    have ht2 : Ty.BelowFvars (Φ₁ + tyArgs.length + 1) (S₂.onTy (S₁.onTy (Ty.fvar v))) :=
      Subst.onTy_belowFvars hbS₂ (ht1.mono (by omega))
    calc S₀.onTy (Ty.fvar v)
        = (S₁ ++ R₁).onTy (Ty.fvar v) := hags v hv
      _ = R₁.onTy (S₁.onTy (Ty.fvar v)) := by rw [Subst.onTy_append]
      _ = (S₂ ++ R₂).onTy (S₁.onTy (Ty.fvar v)) := Subst.onTy_congr hag2 ht1
      _ = R₂.onTy (S₂.onTy (S₁.onTy (Ty.fvar v))) := by rw [Subst.onTy_append]
      _ = (S₃ ++ R₃).onTy (S₂.onTy (S₁.onTy (Ty.fvar v))) := Subst.onTy_congr hagbr ht2
      _ = ((S₁ ++ S₂ ++ S₃) ++ R₃).onTy (Ty.fvar v) := by simp only [Subst.onTy_append]
  · calc τ₀ = R₂.onTy (S₂.onTy (Ty.fvar (Φ₁ + tyArgs.length))) := hρ_R₂.symm
      _ = (S₃ ++ R₃).onTy (S₂.onTy (Ty.fvar (Φ₁ + tyArgs.length))) :=
            Subst.onTy_congr hagbr hρ_below
      _ = R₃.onTy (S₃.onTy (S₂.onTy (Ty.fvar (Φ₁ + tyArgs.length)))) := by rw [Subst.onTy_append]

/-- Principality, `match_` case. -/
theorem Infer.complete_match {scrut : Expr} {branches : List (MatchPattern × Expr)}
    (ihscrut : Infer.CompleteAt scrut)
    (ihbranches : ∀ br ∈ branches, Infer.CompleteAt br.2) :
    Infer.CompleteAt (.match_ scrut branches) := by
  intro Φ ctx S₀ τ₀ hwf hbelow hS₀ hty
  cases hty with
  | match_ hscrut_decl hne hbranches_decl =>
    exact Infer.complete_match_aux ihscrut ihbranches hwf hbelow hS₀ hscrut_decl hne hbranches_decl


/-! ### Principality, assembled -/

/-- Every expression satisfies the principality property `CompleteAt`,
    assembled from the per-form case lemmas by structural induction on `e`. -/
theorem Infer.completeAt (e : Expr) : Infer.CompleteAt e := by
  induction e using Expr.rec_strong with
  | primLit p => exact Infer.complete_prim
  | pair a b iha ihb => exact Infer.complete_pair iha ihb
  | lambda body ih => exact Infer.complete_lambda ih
  | app f inp ihf ihi => exact Infer.complete_app ihf ihi
  | letIn be body ihbe ihbody => exact Infer.complete_letIn ihbe ihbody
  | fst e ih => exact Infer.complete_fst ih
  | snd e ih => exact Infer.complete_snd ih
  | var i => exact Infer.complete_var
  | ctor name => exact Infer.complete_ctor
  | match_ scrut branches ihscrut ihbranches =>
    refine Infer.complete_match ihscrut (fun br hbr => ?_)
    obtain ⟨pat, body⟩ := br
    exact ihbranches pat body hbr

/-- **Principality of `Infer`** (Damas–Milner completeness). For any declarative
    typing of `e` under an LC specialization `S₀` of a WF, frontier-bounded
    context, `Infer` succeeds with `(S, τ)` and the declarative typing factors
    through it via an LC residual `R` (`S₀ = R ∘ S` below the frontier,
    `τ₀ = R.onTy τ`). Combined with `Infer.sound`, this is full principality:
    `Infer` computes a most general typing. -/
theorem Infer.complete {Φ : Nat} {ctx : Ctx} {e : Expr} {S₀ : Subst} {τ₀ : Ty}
    (hwf : CtxWF ctx) (hbelow : CtxBelow Φ ctx)
    (hS₀ : ∀ p ∈ S₀, p.2.IsLC) (hty : TypeOfHM (S₀.onCtx ctx) e τ₀) :
    ∃ Φ' S τ R,
      Infer Φ ctx e Φ' S τ ∧
      Subst.AgreesBelow Φ S₀ (S ++ R) ∧
      τ₀ = R.onTy τ ∧
      (∀ p ∈ R, p.2.IsLC) :=
  Infer.completeAt e hwf hbelow hS₀ hty


/-! ### Cleaner corollaries of principality

`Infer.complete` carries two extra side-conclusions beyond `τ₀ = R.onTy τ` — the
agreement clause `S₀ = R ∘ S` (below `Φ`) and `R` locally-closed — purely to
sustain the induction (the `app`/`pair`/`letIn` cases compose specialisations and
reuse `R` as an inner `S₀`). The corollaries below project that engine down to the
parts a caller usually wants. -/

/-- Principality, type-only form: the type of *any* declarative typing is a
    substitution instance of the type `Infer` computes. -/
theorem Infer.complete_instance {Φ : Nat} {ctx : Ctx} {e : Expr} {S₀ : Subst} {τ₀ : Ty}
    (hwf : CtxWF ctx) (hbelow : CtxBelow Φ ctx)
    (hS₀ : ∀ p ∈ S₀, p.2.IsLC) (hty : TypeOfHM (S₀.onCtx ctx) e τ₀) :
    ∃ Φ' S τ R, Infer Φ ctx e Φ' S τ ∧ τ₀ = Subst.onTy R τ := by
  obtain ⟨Φ', S, τ, R, hInfer, _, hτeq, _⟩ := Infer.complete hwf hbelow hS₀ hty
  exact ⟨Φ', S, τ, R, hInfer, hτeq⟩

/-- Specialised to the identity input substitution: any declarative type of `e`
    in `ctx` itself is an instance of the inferred type. -/
theorem Infer.complete_id {Φ : Nat} {ctx : Ctx} {e : Expr} {τ₀ : Ty}
    (hwf : CtxWF ctx) (hbelow : CtxBelow Φ ctx)
    (hty : TypeOfHM ctx e τ₀) :
    ∃ Φ' S τ R, Infer Φ ctx e Φ' S τ ∧ τ₀ = Subst.onTy R τ := by
  refine Infer.complete_instance hwf hbelow (S₀ := []) (by simp) ?_
  simpa using hty

/-- **Algorithm W decides typeability.** `e` is declaratively typeable under some
    locally-closed specialisation of `ctx` iff `Infer` succeeds on `e` in `ctx`.
    (The specialisation is necessary: `Infer` may instantiate `ctx`'s free type
    variables — rigid in the declarative system — so success does not entail
    typeability of the *unspecialised* `ctx`.) -/
theorem Infer.iff_typeable {Φ : Nat} {ctx : Ctx} {e : Expr}
    (hwf : CtxWF ctx) (hbelow : CtxBelow Φ ctx) :
    (∃ (S : Subst) (τ : Ty), (∀ p ∈ S, p.2.IsLC) ∧ TypeOfHM (S.onCtx ctx) e τ)
      ↔ (∃ Φ' S τ, Infer Φ ctx e Φ' S τ) := by
  constructor
  · rintro ⟨S, τ, hS, hty⟩
    obtain ⟨Φ', S', τ', _, hInfer, _⟩ := Infer.complete_instance hwf hbelow hS hty
    exact ⟨Φ', S', τ', hInfer⟩
  · rintro ⟨Φ', S, τ, hInfer⟩
    exact ⟨S, τ, (Infer.lc hInfer hwf).2, Infer.sound hInfer hwf⟩

/-- **Algorithm W computes principal types** — soundness and principality bundled
    into one statement. From any declarative typing of a core `e` under an LC
    specialization `S₀` of a WF, frontier-bounded `ctx`, `Infer` succeeds with a
    result `(S, τ)` that

      * is itself a valid declarative typing (`TypeOfHM (S.onCtx ctx) e τ`), and
      * subsumes the given typing (`τ₀ = R.onTy τ`, i.e. `τ` is more general).

    (The stronger per-output `IsPrincipal ctx e S τ` predicate — "this very `τ`
    subsumes *every* typing" — is proved below via `Infer.complete'` /
    `Infer.output_unique`; see `Infer.isPrincipal`.) -/
theorem Infer.principal {Φ : Nat} {ctx : Ctx} {e : Expr} {S₀ : Subst} {τ₀ : Ty}
    (hwf : CtxWF ctx) (hbelow : CtxBelow Φ ctx)
    (hS₀ : ∀ p ∈ S₀, p.2.IsLC) (hty : TypeOfHM (S₀.onCtx ctx) e τ₀) :
    ∃ Φ' S τ R,
      Infer Φ ctx e Φ' S τ ∧ TypeOfHM (S.onCtx ctx) e τ ∧ τ₀ = Subst.onTy R τ := by
  obtain ⟨Φ', S, τ, R, hInfer, hτeq⟩ := Infer.complete_instance hwf hbelow hS₀ hty
  exact ⟨Φ', S, τ, R, hInfer, Infer.sound hInfer hwf, hτeq⟩


/-! ### Principality of a given inference (`complete'`) → output-uniqueness + `IsPrincipal`

`Infer.complete'` is `Infer.complete` reoriented: rather than *producing* a
derivation from a typing, it takes a *given* derivation and shows every typing
factors through *its* output. Pulling the typing back through one derivation
avoids the diverging-substituted-context problem that an `output_unique`-by-
two-derivations attack would hit. -/

mutual
/-- Principality of a *given* derivation: if `Infer` derived `(S, τ)` for `e`,
    then any declarative typing `τ₀` of `e` (under an LC specialization `S₀` of a
    WF, frontier-bounded `ctx`) factors through `τ` via an LC residual `R`, with
    `S₀ = R ∘ S` below `Φ`. -/
theorem Infer.complete' {Φ ctx e Φ' S τ} (h : Infer Φ ctx e Φ' S τ)
    (hwf : CtxWF ctx) (hbelow : CtxBelow Φ ctx) {S₀ : Subst} {τ₀ : Ty}
    (hS₀ : ∀ p ∈ S₀, p.2.IsLC) (hty : TypeOfHM (S₀.onCtx ctx) e τ₀) :
    ∃ R, Subst.AgreesBelow Φ S₀ (S ++ R) ∧ τ₀ = R.onTy τ ∧ (∀ p ∈ R, p.2.IsLC) := by
  cases h with
  | primLitUnit => cases hty; exact ⟨S₀, fun v _ => by rw [List.nil_append], by simp, hS₀⟩
  | primLitInt  => cases hty; exact ⟨S₀, fun v _ => by rw [List.nil_append], by simp, hS₀⟩
  | primLitNat  => cases hty; exact ⟨S₀, fun v _ => by rw [List.nil_append], by simp, hS₀⟩
  | primLitBool => cases hty; exact ⟨S₀, fun v _ => by rw [List.nil_append], by simp, hS₀⟩
  | primLitStr  => cases hty; exact ⟨S₀, fun v _ => by rw [List.nil_append], by simp, hS₀⟩
  | var hlook =>
    obtain ⟨_, _, _, R, hinf, hag, hfac, hRlc⟩ := Infer.complete_var hwf hbelow hS₀ hty
    cases hinf with
    | var hlook' =>
      obtain rfl := Option.some.inj (hlook.symm.trans hlook')
      exact ⟨R, hag, hfac, hRlc⟩
  | ctor hlook =>
    obtain ⟨_, _, _, R, hinf, hag, hfac, hRlc⟩ := Infer.complete_ctor hwf hbelow hS₀ hty
    cases hinf with
    | ctor hlook' =>
      obtain rfl := Option.some.inj (hlook.symm.trans hlook')
      exact ⟨R, hag, hfac, hRlc⟩
  | pair Da Db =>
    cases hty with
    | pair hta htb =>
      expose_names
      obtain ⟨R₁, haga, htya, hR₁⟩ := Infer.complete' Da hwf hbelow hS₀ hta
      have hS₁ := (Infer.lc Da hwf).2
      have hle := Infer.frontier_le Da
      have hbelowτa := (Infer.belowFvars Da hbelow).1
      have hbelowS₁ := (Infer.belowFvars Da hbelow).2
      have hwf₁ := Subst.onCtx_wf hS₁ hwf
      have hbelow₁ := Subst.onCtx_below hbelowS₁ hle hbelow
      have hctx_eq : R₁.onCtx (S₁.onCtx ctx) = S₀.onCtx ctx := by
        rw [← Subst.onCtx_append]
        exact Subst.onCtx_congr (fun v hv => (haga v hv).symm) hbelow
      have htb' : TypeOfHM (R₁.onCtx (S₁.onCtx ctx)) b _ := hctx_eq ▸ htb
      obtain ⟨R₂, hagb, htyb, hR₂⟩ := Infer.complete' Db hwf₁ hbelow₁ hR₁ htb'
      refine ⟨R₂, ?_, ?_, hR₂⟩
      · exact Subst.AgreesBelow.trans_append hle haga hbelowS₁ hagb
      · rw [Subst.onTy_pair]
        refine congrArg₂ Ty.pair ?_ htyb
        rw [htya, ← Subst.onTy_append]
        exact Subst.onTy_congr hagb hbelowτa
  | lambda Dbody =>
    cases hty with
    | lambda hparamLC heq hbodyty =>
      subst heq
      expose_names
      -- STEP 0: fresh names
      obtain ⟨W, c, hΦW, hΦc, hWc, hWav, hcav⟩ := exists_fresh_two_ge Φ
        ([Φ] ++ S₀.map Prod.fst ++ S₀.flatMap (fun p => p.2.freeVars)
          ++ paramTy.freeVars ++ bodyTy.freeVars)
      simp only [List.mem_append, List.mem_singleton, List.mem_map, List.mem_flatMap] at hWav hcav
      push_neg at hWav hcav
      obtain ⟨⟨⟨⟨hWΦ, hWkey⟩, hWrange⟩, hWparam⟩, hWbody⟩ := hWav
      obtain ⟨⟨⟨⟨hcΦ, hckey⟩, hcrange⟩, hcparam⟩, hcbody⟩ := hcav
      have finj : Function.Injective (swapNat Φ W) := swapNat_injective Φ W
      have hfix : ∀ v, v < Φ → swapNat Φ W v = v := fun v hv =>
        swapNat_other (by omega) (by omega)
      have hWonTy : ∀ {τ : Ty}, W ∉ τ.freeVars → W ∉ (S₀.onTy τ).freeVars :=
        fun h => Subst.not_mem_onTy_freeVars hWrange h
      have hconΦ : ∀ p ∈ Subst.conj (swapNat Φ W) S₀, p.1 ≠ Φ := by
        intro p hp
        simp only [Subst.conj, List.mem_map] at hp
        obtain ⟨q, hq, rfl⟩ := hp
        intro hc
        apply hWkey q hq
        have hc' : swapNat Φ W q.1 = Φ := hc
        simp only [swapNat] at hc'
        split_ifs at hc' <;> omega
      have hSconjΦ : (Subst.conj (swapNat Φ W) S₀).onTy (.fvar Φ) = .fvar Φ := by
        apply Ty.substFvars_eq_self_of_no_key
        intro p hp hc
        simp only [Ty.freeVars, List.mem_singleton] at hc
        exact hconΦ p hp hc
      -- STEP 1: rename the body derivation and reinterpret its context
      have hctxeq : (swapSubst Φ W c).onCtx
            { (S₀.onCtx ctx) with env := PolyTy.mkTrivial paramTy :: (S₀.onCtx ctx).env }
          = (Subst.conj (swapNat Φ W) S₀ ++ [(Φ, Ty.rename (swapNat Φ W) paramTy)]).onCtx
            { ctx with env := PolyTy.mkTrivial (.fvar Φ) :: ctx.env } := by
        simp only [Subst.onCtx, Subst.onEnv, List.map_cons, List.map_map]
        congr 1
        congr 1
        · -- head
          simp only [Subst.onPolyTy, PolyTy.mkTrivial, PolyTy.mk.injEq, true_and]
          rw [swapSubst_onTy (Ne.symm hWΦ) (Ne.symm hcΦ) hWc hcparam,
              Subst.onTy_append (Subst.conj (swapNat Φ W) S₀)
                [(Φ, Ty.rename (swapNat Φ W) paramTy)] (.fvar Φ),
              hSconjΦ]
          simp only [Subst.onTy, Ty.substFvars, Ty.substFvar, if_pos]
        · -- tail
          apply List.map_congr_left
          intro M hM
          have hMbelow : ∀ v ∈ M.body.freeVars, v < Φ := (hbelow M hM).mem_lt
          have hrenM : Ty.rename (swapNat Φ W) M.body = M.body :=
            Ty.rename_eq_self (fun v hv => hfix v (hMbelow v hv))
          have hΦnotin : Φ ∉ (Ty.rename (swapNat Φ W) (S₀.onTy M.body)).freeVars :=
            Ty.rename_swap_not_mem_left (hWonTy (τ := M.body) (fun hv => by have := hMbelow _ hv; omega))
          simp only [Function.comp, Subst.onPolyTy, PolyTy.mk.injEq, true_and]
          rw [swapSubst_onTy (Ne.symm hWΦ) (Ne.symm hcΦ) hWc
                (Subst.not_mem_onTy_freeVars hcrange (fun hv => by have := hMbelow _ hv; omega)),
              Subst.onTy_append (Subst.conj (swapNat Φ W) S₀)
                [(Φ, Ty.rename (swapNat Φ W) paramTy)] M.body]
          conv_rhs => rw [← hrenM, Subst.onTy_conj finj]
          exact (Ty.substFvar_fresh hΦnotin).symm
      have hbodyTyeq : (swapSubst Φ W c).onTy bodyTy = Ty.rename (swapNat Φ W) bodyTy :=
        swapSubst_onTy (Ne.symm hWΦ) (Ne.symm hcΦ) hWc hcbody
      have hren := TypeOfHM.onSubst (swapSubst Φ W c) (swapSubst_lc Φ W c) hbodyty
      rw [hctxeq, hbodyTyeq] at hren
      -- STEP 2: apply the body IH under the conjugated specialization
      have hwf_b : CtxWF { ctx with env := PolyTy.mkTrivial (.fvar Φ) :: ctx.env } := by
        intro M hM
        rcases List.mem_cons.mp hM with rfl | hM
        · exact ContainsBvarsUpTo.fvar
        · exact hwf M hM
      have hbelow_b : CtxBelow (Φ + 1) { ctx with env := PolyTy.mkTrivial (.fvar Φ) :: ctx.env } := by
        intro M hM
        rcases List.mem_cons.mp hM with rfl | hM
        · exact .fvar (by omega)
        · exact (hbelow M hM).mono (by omega)
      have hT_lc : ∀ p ∈ Subst.conj (swapNat Φ W) S₀ ++ [(Φ, Ty.rename (swapNat Φ W) paramTy)],
          p.2.IsLC := by
        intro p hp
        rw [List.mem_append] at hp
        rcases hp with hp | hp
        · exact Subst.conj_lc hS₀ p hp
        · rw [List.mem_singleton] at hp
          subst hp
          exact Ty.rename_isLC hparamLC
      obtain ⟨R_b, hagb, htyb, hR_b⟩ := Infer.complete' Dbody hwf_b hbelow_b hT_lc hren
      -- STEP 3: assemble the conclusion
      refine ⟨R_b ++ [(W, .fvar Φ)], ?_, ?_, ?_⟩
      · -- agreement below Φ
        intro v hv
        have hWv : W ∉ (Ty.fvar v).freeVars := by
          simp only [Ty.freeVars, List.mem_singleton]; omega
        have hconjv : (Subst.conj (swapNat Φ W) S₀).onTy (.fvar v)
            = Ty.rename (swapNat Φ W) (S₀.onTy (.fvar v)) := by
          have h := Subst.onTy_conj finj S₀ (.fvar v)
          rw [Ty.rename_fvar, hfix v hv] at h
          exact h
        have hTv : (Subst.conj (swapNat Φ W) S₀ ++ [(Φ, Ty.rename (swapNat Φ W) paramTy)]).onTy (.fvar v)
            = Ty.rename (swapNat Φ W) (S₀.onTy (.fvar v)) := by
          rw [Subst.onTy_append (Subst.conj (swapNat Φ W) S₀)
                [(Φ, Ty.rename (swapNat Φ W) paramTy)] (.fvar v), hconjv]
          exact Ty.substFvar_fresh (Ty.rename_swap_not_mem_left (hWonTy (τ := .fvar v) hWv))
        rw [← List.append_assoc, Subst.onTy_append (S ++ R_b) [(W, .fvar Φ)] (.fvar v),
            ← hagb v (by omega), hTv]
        exact (Ty.substFvar_rename_swap (hWonTy (τ := .fvar v) hWv)).symm
      · -- the arrow type is recovered
        have hTΦ : (Subst.conj (swapNat Φ W) S₀ ++ [(Φ, Ty.rename (swapNat Φ W) paramTy)]).onTy (.fvar Φ)
            = Ty.rename (swapNat Φ W) paramTy := by
          rw [Subst.onTy_append (Subst.conj (swapNat Φ W) S₀)
                [(Φ, Ty.rename (swapNat Φ W) paramTy)] (.fvar Φ), hSconjΦ]
          simp only [Subst.onTy, Ty.substFvars, Ty.substFvar, if_pos]
        rw [Subst.onTy_arrow]
        refine congrArg₂ Ty.arrow ?_ ?_
        · rw [Subst.onTy_append R_b [(W, .fvar Φ)] (S.onTy (.fvar Φ)),
              ← Subst.onTy_append S R_b (.fvar Φ),
              ← hagb Φ (by omega), hTΦ]
          exact (Ty.substFvar_rename_swap hWparam).symm
        · rw [Subst.onTy_append R_b [(W, .fvar Φ)] τb, ← htyb]
          exact (Ty.substFvar_rename_swap hWbody).symm
      · -- residual is LC
        intro p hp
        rw [List.mem_append] at hp
        rcases hp with hp | hp
        · exact hR_b p hp
        · rw [List.mem_singleton] at hp
          subst hp
          exact ContainsBvarsUpTo.fvar
  | app Df Darg Duni =>
    cases hty with
    | app hf harg =>
      expose_names
      -- STEP 1: recurse on `f`.
      obtain ⟨R₁, hagf, htyf, hR₁⟩ := Infer.complete' Df hwf hbelow hS₀ hf
      have hS₁ := (Infer.lc Df hwf).2
      have hbf := Infer.belowFvars Df hbelow
      have hle1 := Infer.frontier_le Df
      have hwf₁ := Subst.onCtx_wf hS₁ hwf
      have hbelow₁ := Subst.onCtx_below hbf.2 hle1 hbelow
      -- STEP 2: recurse on `arg`.
      have hctxeq : R₁.onCtx (S₁.onCtx ctx) = S₀.onCtx ctx := by
        rw [← Subst.onCtx_append]
        exact Subst.onCtx_congr (fun v hv => (hagf v hv).symm) hbelow
      have harg' : TypeOfHM (R₁.onCtx (S₁.onCtx ctx)) arg argTy := by
        rw [hctxeq]; exact harg
      obtain ⟨R₂, haga, htya, hR₂⟩ := Infer.complete' Darg hwf₁ hbelow₁ hR₁ harg'
      have hS₂ := (Infer.lc Darg hwf₁).2
      have hba := Infer.belowFvars Darg hbelow₁
      have hle2 := Infer.frontier_le Darg
      -- STEP 3: key equalities.
      have hcongr_f : R₁.onTy τf = (S₂ ++ R₂).onTy τf := Subst.onTy_congr haga hbf.1
      have hP : R₂.onTy (S₂.onTy τf) = Ty.arrow argTy τ₀ := by
        rw [← Subst.onTy_append, ← hcongr_f]; exact htyf.symm
      have hΦ₂τf : Φ₂ ∉ (S₂.onTy τf).freeVars := fun hm => by
        have := (Subst.onTy_belowFvars hba.2 (hbf.1.mono hle2)).mem_lt _ hm
        omega
      have hΦ₂τa : Φ₂ ∉ τa.freeVars := fun hm => by
        have := hba.1.mem_lt _ hm
        omega
      have hτ₀LC : τ₀.IsLC := by
        have hreg := TypeOfHM.regular hf
        cases hreg with
        | arrow _ hT => exact hT
      -- STEP 4: a fresh variable `W`.
      obtain ⟨W, hWge, hWfresh⟩ := exists_fresh_block
        (R₂.map Prod.fst ++ R₂.flatMap (fun p => p.2.freeVars) ++ argTy.freeVars ++ τ₀.freeVars) Φ₂ 1
      have hWdom : ∀ p ∈ R₂, p.1 ≠ W := by
        intro p hp he
        have := hWfresh p.1 (List.mem_append_left _ (List.mem_append_left _
          (List.mem_append_left _ (List.mem_map.mpr ⟨p, hp, rfl⟩))))
        omega
      have hWrange : ∀ p ∈ R₂, W ∉ p.2.freeVars := by
        intro p hp hc
        have := hWfresh W (List.mem_append_left _ (List.mem_append_left _
          (List.mem_append_right _ (List.mem_flatMap.mpr ⟨p, hp, hc⟩))))
        omega
      have hWargTy : W ∉ argTy.freeVars := fun hc => by
        have := hWfresh W (List.mem_append_left _ (List.mem_append_right _ hc)); omega
      have hWτ₀ : W ∉ τ₀.freeVars := fun hc => by
        have := hWfresh W (List.mem_append_right _ hc); omega
      have hR₂Wfvar : R₂.onTy (Ty.fvar W) = Ty.fvar W := by
        apply Ty.substFvars_eq_self_of_no_key
        intro p hp hc
        simp only [Ty.freeVars, List.mem_singleton] at hc
        exact hWdom p hp hc
      -- STEP 5: the explicit unifier `U`.
      obtain ⟨U, hUdef⟩ : ∃ U : Subst, U = [(Φ₂, Ty.fvar W)] ++ R₂ ++ [(W, τ₀)] := ⟨_, rfl⟩
      have hsingle : ∀ (Z : Nat) (V y : Ty), Subst.onTy [(Z, V)] y = Ty.substFvar Z V y :=
        fun _ _ _ => rfl
      have hsubArrow : ∀ (Z : Nat) (V a b : Ty),
          Ty.substFvar Z V (Ty.arrow a b) = Ty.arrow (Ty.substFvar Z V a) (Ty.substFvar Z V b) :=
        fun _ _ _ _ => rfl
      have hUonTy : ∀ x, U.onTy x = Ty.substFvar W τ₀ (R₂.onTy (Ty.substFvar Φ₂ (Ty.fvar W) x)) := by
        intro x
        rw [hUdef, Subst.onTy_append, Subst.onTy_append, hsingle, hsingle]
      have e1 : Ty.substFvar Φ₂ (Ty.fvar W) (Ty.fvar Φ₂) = Ty.fvar W := by simp [Ty.substFvar]
      have e2 : Ty.substFvar W τ₀ (Ty.fvar W) = τ₀ := by simp [Ty.substFvar]
      have hUniL : U.onTy (S₂.onTy τf) = Ty.arrow argTy τ₀ := by
        rw [hUonTy, Ty.substFvar_fresh hΦ₂τf, hP, hsubArrow,
            Ty.substFvar_fresh hWargTy, Ty.substFvar_fresh hWτ₀]
      have hUniR : U.onTy (Ty.arrow τa (Ty.fvar Φ₂)) = Ty.arrow argTy τ₀ := by
        rw [hUonTy, hsubArrow, Ty.substFvar_fresh hΦ₂τa, e1, Subst.onTy_arrow,
            hR₂Wfvar, ← htya, hsubArrow, Ty.substFvar_fresh hWargTy, e2]
      have hUni : Unifies U (S₂.onTy τf) (Ty.arrow τa (Ty.fvar Φ₂)) := by
        show U.onTy (S₂.onTy τf) = U.onTy (Ty.arrow τa (Ty.fvar Φ₂))
        rw [hUniL, hUniR]
      -- STEP 6: the MGU `S₃` is the *given* `Duni`.
      have h₃ := Duni
      -- STEP 7: factor `U` through `S₃`.
      have hUlc : ∀ p ∈ U, p.2.IsLC := by
        rw [hUdef]
        intro p hp
        rcases List.mem_append.mp hp with hp' | hp'
        · rcases List.mem_append.mp hp' with hp'' | hp''
          · obtain rfl := List.mem_singleton.mp hp''
            exact ContainsBvarsUpTo.fvar
          · exact hR₂ p hp''
        · obtain rfl := List.mem_singleton.mp hp'
          exact hτ₀LC
      obtain ⟨R₃, hR₃, hR₃lc⟩ := UnifyRel.greatest_lc h₃ U hUlc hUni
      -- STEP 8: assemble.
      refine ⟨R₃, ?_, ?_, hR₃lc⟩
      · intro v hv
        have ht1 : Ty.BelowFvars Φ₁ (S₁.onTy (Ty.fvar v)) :=
          Subst.onTy_belowFvars hbf.2 (Ty.BelowFvars.fvar (by omega))
        have ht : Ty.BelowFvars Φ₂ (S₂.onTy (S₁.onTy (Ty.fvar v))) :=
          Subst.onTy_belowFvars hba.2 (ht1.mono hle2)
        have hΦ₂t : Φ₂ ∉ (S₂.onTy (S₁.onTy (Ty.fvar v))).freeVars := fun hm => by
          have := ht.mem_lt _ hm; omega
        have hWt : W ∉ (S₂.onTy (S₁.onTy (Ty.fvar v))).freeVars := fun hm => by
          have := ht.mem_lt _ hm; omega
        have hWR₂t : W ∉ (R₂.onTy (S₂.onTy (S₁.onTy (Ty.fvar v)))).freeVars :=
          Subst.not_mem_onTy_freeVars hWrange hWt
        simp only [Subst.onTy_append]
        rw [← hR₃ (S₂.onTy (S₁.onTy (Ty.fvar v))), hUonTy,
            Ty.substFvar_fresh hΦ₂t, Ty.substFvar_fresh hWR₂t,
            hagf v hv, Subst.onTy_append, Subst.onTy_congr haga ht1, Subst.onTy_append]
      · rw [← hR₃ (Ty.fvar Φ₂), hUonTy, e1, hR₂Wfvar, e2]
  | letIn Drhs Dbody =>
    cases hty with
    | letIn hMwf hcofin heq hbody =>
      subst heq
      expose_names
      obtain ⟨Xs, hXlen, hXnodup, hXavoid⟩ :=
        exists_fresh_names (L ++ M.body.freeVars ++ (S₀.onCtx ctx).env.freeVars) M.paramCount
      have hXfreshL : FreshNames L M.paramCount Xs :=
        ⟨hXlen, hXnodup,
          fun x hx hc => hXavoid x hx (List.mem_append_left _ (List.mem_append_left _ hc))⟩
      have hXMbody : ∀ x ∈ Xs, x ∉ M.body.freeVars :=
        fun x hx hc => hXavoid x hx (List.mem_append_left _ (List.mem_append_right _ hc))
      have hXenv : ∀ x ∈ Xs, x ∉ (S₀.onCtx ctx).env.freeVars :=
        fun x hx hc => hXavoid x hx (List.mem_append_right _ hc)
      obtain ⟨R₁, haga, htya, hR₁⟩ := Infer.complete' Drhs hwf hbelow hS₀ (hcofin Xs hXfreshL)
      have hS₁ := (Infer.lc Drhs hwf).2
      have hτ₁lc := (Infer.lc Drhs hwf).1
      have hle := Infer.frontier_le Drhs
      have hbelowτ₁ := (Infer.belowFvars Drhs hbelow).1
      have hbelowS₁ := (Infer.belowFvars Drhs hbelow).2
      have hwf₁ := Subst.onCtx_wf hS₁ hwf
      have hbelow₁ := Subst.onCtx_below hbelowS₁ hle hbelow
      have hctxeq : R₁.onCtx (S₁.onCtx ctx) = S₀.onCtx ctx := by
        rw [← Subst.onCtx_append]
        exact Subst.onCtx_congr (fun v hv => (haga v hv).symm) hbelow
      have hwfBody : CtxWF { (S₁.onCtx ctx) with
          env := genScheme (S₁.onCtx ctx).env τ₁ :: (S₁.onCtx ctx).env } := by
        intro N hN
        rcases List.mem_cons.mp hN with rfl | hN
        · exact genScheme_wf hτ₁lc
        · exact hwf₁ N hN
      have hbelowBody : CtxBelow Φ₁ { (S₁.onCtx ctx) with
          env := genScheme (S₁.onCtx ctx).env τ₁ :: (S₁.onCtx ctx).env } := by
        intro N hN
        rcases List.mem_cons.mp hN with rfl | hN
        · show Ty.BelowFvars Φ₁ (Ty.closeOver (genVars (S₁.onCtx ctx).env τ₁) τ₁)
          exact hbelowτ₁.closeOver
        · exact hbelow₁ N hN
      have hXM'' : ∀ x ∈ Xs,
          x ∉ (R₁.onPolyTy (genScheme (S₁.onCtx ctx).env τ₁)).body.freeVars := by
        intro x hx hmem
        change x ∈ (R₁.onTy (Ty.closeOver (genVars (S₁.onCtx ctx).env τ₁) τ₁)).freeVars at hmem
        obtain ⟨v, hv, hxv⟩ := Ty.mem_freeVars_onTy_iff.mp hmem
        have hvτ₁ : v ∈ τ₁.freeVars := Ty.closeOver_freeVars_subset hv
        have hvg : v ∉ genVars (S₁.onCtx ctx).env τ₁ := fun hg => Ty.not_mem_closeOver_freeVars hg hv
        have hvenv : v ∈ (S₁.onCtx ctx).env.freeVars := by
          by_contra hc
          exact hvg (by
            simp only [genVars, List.mem_filter]
            exact ⟨hvτ₁, by simpa using hc⟩)
        obtain ⟨pt, hpt, hvpt⟩ := Env.mem_freeVars_iff.mp hvenv
        have hx_onTy : x ∈ (R₁.onTy pt.body).freeVars :=
          Ty.mem_freeVars_onTy_iff.mpr ⟨v, hvpt, hxv⟩
        have hpt_mem : R₁.onPolyTy pt ∈ (S₀.onCtx ctx).env := by
          have hmem2 : R₁.onPolyTy pt ∈ (R₁.onCtx (S₁.onCtx ctx)).env := by
            simp only [Subst.onCtx, Subst.onEnv]
            exact List.mem_map.mpr ⟨pt, hpt, rfl⟩
          rw [hctxeq] at hmem2; exact hmem2
        exact hXenv x hx (Env.mem_freeVars_iff.mpr ⟨R₁.onPolyTy pt, hpt_mem, hx_onTy⟩)
      have hgen : (R₁.onPolyTy (genScheme (S₁.onCtx ctx).env τ₁)).Generalizes M :=
        genScheme_generalizes hτ₁lc hR₁ hMwf hXnodup hXlen hXMbody htya hXM''
      have hbody' : TypeOfHM
          ⟨R₁.onPolyTy (genScheme (S₁.onCtx ctx).env τ₁) :: (S₀.onCtx ctx).env,
            (S₀.onCtx ctx).ctors⟩ body τ₀ :=
        TypeOfHM.weaken_scheme (env_post := []) (env := (S₀.onCtx ctx).env) (M := M) hgen hbody
      have hbody'' : TypeOfHM (R₁.onCtx { (S₁.onCtx ctx) with
          env := genScheme (S₁.onCtx ctx).env τ₁ :: (S₁.onCtx ctx).env }) body τ₀ := by
        show TypeOfHM ⟨R₁.onPolyTy (genScheme (S₁.onCtx ctx).env τ₁) :: R₁.onEnv (S₁.onCtx ctx).env,
            (S₁.onCtx ctx).ctors⟩ body τ₀
        rw [show R₁.onEnv (S₁.onCtx ctx).env = (S₀.onCtx ctx).env from congrArg Ctx.env hctxeq]
        exact hbody'
      obtain ⟨R₂, hagb, htyb, hR₂⟩ := Infer.complete' Dbody hwfBody hbelowBody hR₁ hbody''
      refine ⟨R₂, ?_, htyb, hR₂⟩
      exact Subst.AgreesBelow.trans_append hle haga hbelowS₁ hagb
  | fst De Duni =>
    cases hty with
    | fst he =>
      expose_names
      obtain ⟨τβ, he⟩ : ∃ τβ, TypeOfHM (S₀.onCtx ctx) e (.pair τ₀ τβ) := ⟨_, he⟩
      have hαLC : τ₀.IsLC := by
        have := TypeOfHM.regular he; cases this with | pair h _ => exact h
      have hβLC : τβ.IsLC := by
        have := TypeOfHM.regular he; cases this with | pair _ h => exact h
      obtain ⟨R₁, hage, htye, hR₁⟩ := Infer.complete' De hwf hbelow hS₀ he
      have hS₁ := (Infer.lc De hwf).2
      have hτeLC := (Infer.lc De hwf).1
      have hle1 := Infer.frontier_le De
      have hbe := Infer.belowFvars De hbelow
      have hΦ₁τe : Φ₁ ∉ τe.freeVars := fun hm => by have := hbe.1.mem_lt _ hm; omega
      have hΦ₁1τe : Φ₁ + 1 ∉ τe.freeVars := fun hm => by have := hbe.1.mem_lt _ hm; omega
      obtain ⟨W, hWge, hWfresh⟩ := exists_fresh_block
        (R₁.map Prod.fst ++ R₁.flatMap (fun p => p.2.freeVars)
          ++ τ₀.freeVars ++ τβ.freeVars) Φ₁ 2
      have hWdom : ∀ p ∈ R₁, p.1 ≠ W := by
        intro p hp _heq
        have := hWfresh p.1 (List.mem_append_left _ (List.mem_append_left _
          (List.mem_append_left _ (List.mem_map.mpr ⟨p, hp, rfl⟩))))
        omega
      have hW1dom : ∀ p ∈ R₁, p.1 ≠ W + 1 := by
        intro p hp _heq
        have := hWfresh p.1 (List.mem_append_left _ (List.mem_append_left _
          (List.mem_append_left _ (List.mem_map.mpr ⟨p, hp, rfl⟩))))
        omega
      have hWrng : ∀ p ∈ R₁, W ∉ p.2.freeVars := by
        intro p hp hc
        have := hWfresh W (List.mem_append_left _ (List.mem_append_left _
          (List.mem_append_right _ (List.mem_flatMap.mpr ⟨p, hp, hc⟩))))
        omega
      have hW1rng : ∀ p ∈ R₁, W + 1 ∉ p.2.freeVars := by
        intro p hp hc
        have := hWfresh (W + 1) (List.mem_append_left _ (List.mem_append_left _
          (List.mem_append_right _ (List.mem_flatMap.mpr ⟨p, hp, hc⟩))))
        omega
      have hWP : W ∉ τ₀.freeVars := fun hc => by
        have := hWfresh W (List.mem_append_left _ (List.mem_append_right _ hc)); omega
      have hW1P : W + 1 ∉ τ₀.freeVars := fun hc => by
        have := hWfresh (W + 1) (List.mem_append_left _ (List.mem_append_right _ hc)); omega
      have hWQ : W ∉ τβ.freeVars := fun hc => by
        have := hWfresh W (List.mem_append_right _ hc); omega
      have hW1Q : W + 1 ∉ τβ.freeVars := fun hc => by
        have := hWfresh (W + 1) (List.mem_append_right _ hc); omega
      obtain ⟨U, hUdef⟩ : ∃ U : Subst,
        U = [(Φ₁, Ty.fvar W), (Φ₁ + 1, Ty.fvar (W + 1))] ++ R₁
            ++ [(W, τ₀), (W + 1, τβ)] := ⟨_, rfl⟩
      have hUonTy : ∀ x, U.onTy x =
          Subst.onTy [(W, τ₀), (W + 1, τβ)]
            (R₁.onTy (Subst.onTy [(Φ₁, Ty.fvar W), (Φ₁ + 1, Ty.fvar (W + 1))] x)) := by
        intro x
        rw [hUdef, Subst.onTy_append, Subst.onTy_append]
      have hR₁W : R₁.onTy (Ty.fvar W) = Ty.fvar W := by
        apply Ty.substFvars_eq_self_of_no_key
        intro p hp hc
        simp only [Ty.freeVars, List.mem_singleton] at hc
        exact hWdom p hp hc
      have hR₁W1 : R₁.onTy (Ty.fvar (W + 1)) = Ty.fvar (W + 1) := by
        apply Ty.substFvars_eq_self_of_no_key
        intro p hp hc
        simp only [Ty.freeVars, List.mem_singleton] at hc
        exact hW1dom p hp hc
      have hprefix_Φ₁ :
          Subst.onTy [(Φ₁, Ty.fvar W), (Φ₁ + 1, Ty.fvar (W + 1))] (Ty.fvar Φ₁) = Ty.fvar W := by
        show Ty.substFvar (Φ₁ + 1) (Ty.fvar (W + 1)) (Ty.substFvar Φ₁ (Ty.fvar W) (Ty.fvar Φ₁))
            = Ty.fvar W
        rw [show Ty.substFvar Φ₁ (Ty.fvar W) (Ty.fvar Φ₁) = Ty.fvar W from by simp [Ty.substFvar]]
        exact Ty.substFvar_fresh (by simp only [Ty.freeVars, List.mem_singleton]; omega)
      have hprefix_Φ₂ :
          Subst.onTy [(Φ₁, Ty.fvar W), (Φ₁ + 1, Ty.fvar (W + 1))] (Ty.fvar (Φ₁ + 1)) = Ty.fvar (W + 1) := by
        show Ty.substFvar (Φ₁ + 1) (Ty.fvar (W + 1)) (Ty.substFvar Φ₁ (Ty.fvar W) (Ty.fvar (Φ₁ + 1)))
            = Ty.fvar (W + 1)
        rw [show Ty.substFvar Φ₁ (Ty.fvar W) (Ty.fvar (Φ₁ + 1)) = Ty.fvar (Φ₁ + 1) from
          Ty.substFvar_fresh (by simp only [Ty.freeVars, List.mem_singleton]; omega)]
        simp [Ty.substFvar]
      have hsufW :
          Subst.onTy [(W, τ₀), (W + 1, τβ)] (Ty.fvar W) = τ₀ := by
        show Ty.substFvar (W + 1) τβ (Ty.substFvar W τ₀ (Ty.fvar W)) = τ₀
        rw [show Ty.substFvar W τ₀ (Ty.fvar W) = τ₀ from by simp [Ty.substFvar]]
        exact Ty.substFvar_fresh hW1P
      have hsufW1 :
          Subst.onTy [(W, τ₀), (W + 1, τβ)] (Ty.fvar (W + 1)) = τβ := by
        show Ty.substFvar (W + 1) τβ (Ty.substFvar W τ₀ (Ty.fvar (W + 1))) = τβ
        rw [show Ty.substFvar W τ₀ (Ty.fvar (W + 1)) = Ty.fvar (W + 1) from
          Ty.substFvar_fresh (by simp only [Ty.freeVars, List.mem_singleton]; omega)]
        simp [Ty.substFvar]
      have hUφ₁ : U.onTy (Ty.fvar Φ₁) = τ₀ := by
        rw [hUonTy, hprefix_Φ₁, hR₁W, hsufW]
      have hUφ₂ : U.onTy (Ty.fvar (Φ₁ + 1)) = τβ := by
        rw [hUonTy, hprefix_Φ₂, hR₁W1, hsufW1]
      have hUvar : ∀ v, v < Φ₁ → U.onTy (Ty.fvar v) = R₁.onTy (Ty.fvar v) := by
        intro v hv
        rw [hUonTy]
        rw [show Subst.onTy [(Φ₁, Ty.fvar W), (Φ₁ + 1, Ty.fvar (W + 1))] (Ty.fvar v) = Ty.fvar v from by
          show Ty.substFvar (Φ₁ + 1) (Ty.fvar (W + 1)) (Ty.substFvar Φ₁ (Ty.fvar W) (Ty.fvar v))
              = Ty.fvar v
          rw [show Ty.substFvar Φ₁ (Ty.fvar W) (Ty.fvar v) = Ty.fvar v from
            Ty.substFvar_fresh (by simp only [Ty.freeVars, List.mem_singleton]; omega)]
          exact Ty.substFvar_fresh (by simp only [Ty.freeVars, List.mem_singleton]; omega)]
        apply Ty.substFvars_eq_self_of_no_key
        intro p hp
        rcases List.mem_cons.mp hp with rfl | hp'
        · exact Subst.not_mem_onTy_freeVars hWrng
            (by simp only [Ty.freeVars, List.mem_singleton]; omega)
        · obtain rfl := List.mem_singleton.mp hp'
          exact Subst.not_mem_onTy_freeVars hW1rng
            (by simp only [Ty.freeVars, List.mem_singleton]; omega)
      have hUτe : U.onTy τe = Ty.pair τ₀ τβ := by
        rw [hUonTy]
        rw [show Subst.onTy [(Φ₁, Ty.fvar W), (Φ₁ + 1, Ty.fvar (W + 1))] τe = τe from
          Ty.substFvars_eq_self_of_no_key (by
            intro p hp
            rcases List.mem_cons.mp hp with rfl | hp'
            · exact hΦ₁τe
            · obtain rfl := List.mem_singleton.mp hp'
              exact hΦ₁1τe)]
        rw [← htye]
        apply Ty.substFvars_eq_self_of_no_key
        intro p hp
        rcases List.mem_cons.mp hp with rfl | hp'
        · simp only [Ty.freeVars, List.mem_dedup, List.mem_append, not_or]
          exact ⟨hWP, hWQ⟩
        · obtain rfl := List.mem_singleton.mp hp'
          simp only [Ty.freeVars, List.mem_dedup, List.mem_append, not_or]
          exact ⟨hW1P, hW1Q⟩
      have hUni : Unifies U τe (Ty.pair (Ty.fvar Φ₁) (Ty.fvar (Φ₁ + 1))) := by
        show U.onTy τe = U.onTy (Ty.pair (Ty.fvar Φ₁) (Ty.fvar (Φ₁ + 1)))
        rw [hUτe, Subst.onTy_pair, hUφ₁, hUφ₂]
      -- The MGU `S₂` is the *given* `Duni`; factor `U` through it.
      have h₂ := Duni
      have hUlc : ∀ p ∈ U, p.2.IsLC := by
        rw [hUdef]
        intro p hp
        rcases List.mem_append.mp hp with hp' | hp'
        · rcases List.mem_append.mp hp' with hp'' | hp''
          · rcases List.mem_cons.mp hp'' with rfl | hp'''
            · exact ContainsBvarsUpTo.fvar
            · obtain rfl := List.mem_singleton.mp hp'''
              exact ContainsBvarsUpTo.fvar
          · exact hR₁ p hp''
        · rcases List.mem_cons.mp hp' with rfl | hp''
          · exact hαLC
          · obtain rfl := List.mem_singleton.mp hp''
            exact hβLC
      obtain ⟨R₂, hR₂, hR₂lc⟩ := UnifyRel.greatest_lc h₂ U hUlc hUni
      refine ⟨R₂, ?_, ?_, hR₂lc⟩
      · intro v hv
        have ht1 : Ty.BelowFvars Φ₁ (S₁.onTy (Ty.fvar v)) :=
          Subst.onTy_belowFvars hbe.2 (Ty.BelowFvars.fvar (by omega))
        have hΦ₁t : Φ₁ ∉ (S₁.onTy (Ty.fvar v)).freeVars := fun hm => by
          have := ht1.mem_lt _ hm; omega
        have hΦ₁1t : Φ₁ + 1 ∉ (S₁.onTy (Ty.fvar v)).freeVars := fun hm => by
          have := ht1.mem_lt _ hm; omega
        have hWt : W ∉ (S₁.onTy (Ty.fvar v)).freeVars := fun hm => by
          have := ht1.mem_lt _ hm; omega
        have hW1t : W + 1 ∉ (S₁.onTy (Ty.fvar v)).freeVars := fun hm => by
          have := ht1.mem_lt _ hm; omega
        have hWR₁t : W ∉ (R₁.onTy (S₁.onTy (Ty.fvar v))).freeVars :=
          Subst.not_mem_onTy_freeVars hWrng hWt
        have hW1R₁t : W + 1 ∉ (R₁.onTy (S₁.onTy (Ty.fvar v))).freeVars :=
          Subst.not_mem_onTy_freeVars hW1rng hW1t
        calc S₀.onTy (Ty.fvar v)
            = (S₁ ++ R₁).onTy (Ty.fvar v) := hage v hv
          _ = R₁.onTy (S₁.onTy (Ty.fvar v)) := by rw [Subst.onTy_append]
          _ = U.onTy (S₁.onTy (Ty.fvar v)) := by
                rw [hUonTy,
                  show Subst.onTy [(Φ₁, Ty.fvar W), (Φ₁ + 1, Ty.fvar (W + 1))]
                      (S₁.onTy (Ty.fvar v)) = S₁.onTy (Ty.fvar v) from
                    Ty.substFvars_eq_self_of_no_key (by
                      intro p hp
                      rcases List.mem_cons.mp hp with rfl | hp'
                      · exact hΦ₁t
                      · obtain rfl := List.mem_singleton.mp hp'
                        exact hΦ₁1t)]
                exact (Ty.substFvars_eq_self_of_no_key (by
                  intro p hp
                  rcases List.mem_cons.mp hp with rfl | hp'
                  · exact hWR₁t
                  · obtain rfl := List.mem_singleton.mp hp'
                    exact hW1R₁t)).symm
          _ = R₂.onTy (S₂.onTy (S₁.onTy (Ty.fvar v))) := hR₂ (S₁.onTy (Ty.fvar v))
          _ = ((S₁ ++ S₂) ++ R₂).onTy (Ty.fvar v) := by simp only [Subst.onTy_append]
      · rw [← hR₂ (Ty.fvar Φ₁), hUφ₁]
  | snd De Duni =>
    cases hty with
    | snd he =>
      expose_names
      obtain ⟨τα, he⟩ : ∃ τα, TypeOfHM (S₀.onCtx ctx) e (.pair τα τ₀) := ⟨_, he⟩
      have hαLC : τα.IsLC := by
        have := TypeOfHM.regular he; cases this with | pair h _ => exact h
      have hβLC : τ₀.IsLC := by
        have := TypeOfHM.regular he; cases this with | pair _ h => exact h
      obtain ⟨R₁, hage, htye, hR₁⟩ := Infer.complete' De hwf hbelow hS₀ he
      have hS₁ := (Infer.lc De hwf).2
      have hle1 := Infer.frontier_le De
      have hbe := Infer.belowFvars De hbelow
      have hΦ₁τe : Φ₁ ∉ τe.freeVars := fun hm => by have := hbe.1.mem_lt _ hm; omega
      have hΦ₁1τe : Φ₁ + 1 ∉ τe.freeVars := fun hm => by have := hbe.1.mem_lt _ hm; omega
      obtain ⟨W, hWge, hWfresh⟩ := exists_fresh_block
        (R₁.map Prod.fst ++ R₁.flatMap (fun p => p.2.freeVars)
          ++ τα.freeVars ++ τ₀.freeVars) Φ₁ 2
      have hWdom : ∀ p ∈ R₁, p.1 ≠ W := by
        intro p hp _heq
        have := hWfresh p.1 (List.mem_append_left _ (List.mem_append_left _
          (List.mem_append_left _ (List.mem_map.mpr ⟨p, hp, rfl⟩))))
        omega
      have hW1dom : ∀ p ∈ R₁, p.1 ≠ W + 1 := by
        intro p hp _heq
        have := hWfresh p.1 (List.mem_append_left _ (List.mem_append_left _
          (List.mem_append_left _ (List.mem_map.mpr ⟨p, hp, rfl⟩))))
        omega
      have hWrng : ∀ p ∈ R₁, W ∉ p.2.freeVars := by
        intro p hp hc
        have := hWfresh W (List.mem_append_left _ (List.mem_append_left _
          (List.mem_append_right _ (List.mem_flatMap.mpr ⟨p, hp, hc⟩))))
        omega
      have hW1rng : ∀ p ∈ R₁, W + 1 ∉ p.2.freeVars := by
        intro p hp hc
        have := hWfresh (W + 1) (List.mem_append_left _ (List.mem_append_left _
          (List.mem_append_right _ (List.mem_flatMap.mpr ⟨p, hp, hc⟩))))
        omega
      have hWP : W ∉ τα.freeVars := fun hc => by
        have := hWfresh W (List.mem_append_left _ (List.mem_append_right _ hc)); omega
      have hW1P : W + 1 ∉ τα.freeVars := fun hc => by
        have := hWfresh (W + 1) (List.mem_append_left _ (List.mem_append_right _ hc)); omega
      have hWQ : W ∉ τ₀.freeVars := fun hc => by
        have := hWfresh W (List.mem_append_right _ hc); omega
      have hW1Q : W + 1 ∉ τ₀.freeVars := fun hc => by
        have := hWfresh (W + 1) (List.mem_append_right _ hc); omega
      obtain ⟨U, hUdef⟩ : ∃ U : Subst,
        U = [(Φ₁, Ty.fvar W), (Φ₁ + 1, Ty.fvar (W + 1))] ++ R₁
            ++ [(W, τα), (W + 1, τ₀)] := ⟨_, rfl⟩
      have hUonTy : ∀ x, U.onTy x =
          Subst.onTy [(W, τα), (W + 1, τ₀)]
            (R₁.onTy (Subst.onTy [(Φ₁, Ty.fvar W), (Φ₁ + 1, Ty.fvar (W + 1))] x)) := by
        intro x
        rw [hUdef, Subst.onTy_append, Subst.onTy_append]
      have hR₁W : R₁.onTy (Ty.fvar W) = Ty.fvar W := by
        apply Ty.substFvars_eq_self_of_no_key
        intro p hp hc
        simp only [Ty.freeVars, List.mem_singleton] at hc
        exact hWdom p hp hc
      have hR₁W1 : R₁.onTy (Ty.fvar (W + 1)) = Ty.fvar (W + 1) := by
        apply Ty.substFvars_eq_self_of_no_key
        intro p hp hc
        simp only [Ty.freeVars, List.mem_singleton] at hc
        exact hW1dom p hp hc
      have hprefix_Φ₁ :
          Subst.onTy [(Φ₁, Ty.fvar W), (Φ₁ + 1, Ty.fvar (W + 1))] (Ty.fvar Φ₁) = Ty.fvar W := by
        show Ty.substFvar (Φ₁ + 1) (Ty.fvar (W + 1)) (Ty.substFvar Φ₁ (Ty.fvar W) (Ty.fvar Φ₁))
            = Ty.fvar W
        rw [show Ty.substFvar Φ₁ (Ty.fvar W) (Ty.fvar Φ₁) = Ty.fvar W from by simp [Ty.substFvar]]
        exact Ty.substFvar_fresh (by simp only [Ty.freeVars, List.mem_singleton]; omega)
      have hprefix_Φ₂ :
          Subst.onTy [(Φ₁, Ty.fvar W), (Φ₁ + 1, Ty.fvar (W + 1))] (Ty.fvar (Φ₁ + 1)) = Ty.fvar (W + 1) := by
        show Ty.substFvar (Φ₁ + 1) (Ty.fvar (W + 1)) (Ty.substFvar Φ₁ (Ty.fvar W) (Ty.fvar (Φ₁ + 1)))
            = Ty.fvar (W + 1)
        rw [show Ty.substFvar Φ₁ (Ty.fvar W) (Ty.fvar (Φ₁ + 1)) = Ty.fvar (Φ₁ + 1) from
          Ty.substFvar_fresh (by simp only [Ty.freeVars, List.mem_singleton]; omega)]
        simp [Ty.substFvar]
      have hsufW :
          Subst.onTy [(W, τα), (W + 1, τ₀)] (Ty.fvar W) = τα := by
        show Ty.substFvar (W + 1) τ₀ (Ty.substFvar W τα (Ty.fvar W)) = τα
        rw [show Ty.substFvar W τα (Ty.fvar W) = τα from by simp [Ty.substFvar]]
        exact Ty.substFvar_fresh hW1P
      have hsufW1 :
          Subst.onTy [(W, τα), (W + 1, τ₀)] (Ty.fvar (W + 1)) = τ₀ := by
        show Ty.substFvar (W + 1) τ₀ (Ty.substFvar W τα (Ty.fvar (W + 1))) = τ₀
        rw [show Ty.substFvar W τα (Ty.fvar (W + 1)) = Ty.fvar (W + 1) from
          Ty.substFvar_fresh (by simp only [Ty.freeVars, List.mem_singleton]; omega)]
        simp [Ty.substFvar]
      have hUφ₁ : U.onTy (Ty.fvar Φ₁) = τα := by
        rw [hUonTy, hprefix_Φ₁, hR₁W, hsufW]
      have hUφ₂ : U.onTy (Ty.fvar (Φ₁ + 1)) = τ₀ := by
        rw [hUonTy, hprefix_Φ₂, hR₁W1, hsufW1]
      have hUvar : ∀ v, v < Φ₁ → U.onTy (Ty.fvar v) = R₁.onTy (Ty.fvar v) := by
        intro v hv
        rw [hUonTy]
        rw [show Subst.onTy [(Φ₁, Ty.fvar W), (Φ₁ + 1, Ty.fvar (W + 1))] (Ty.fvar v) = Ty.fvar v from by
          show Ty.substFvar (Φ₁ + 1) (Ty.fvar (W + 1)) (Ty.substFvar Φ₁ (Ty.fvar W) (Ty.fvar v))
              = Ty.fvar v
          rw [show Ty.substFvar Φ₁ (Ty.fvar W) (Ty.fvar v) = Ty.fvar v from
            Ty.substFvar_fresh (by simp only [Ty.freeVars, List.mem_singleton]; omega)]
          exact Ty.substFvar_fresh (by simp only [Ty.freeVars, List.mem_singleton]; omega)]
        apply Ty.substFvars_eq_self_of_no_key
        intro p hp
        rcases List.mem_cons.mp hp with rfl | hp'
        · exact Subst.not_mem_onTy_freeVars hWrng
            (by simp only [Ty.freeVars, List.mem_singleton]; omega)
        · obtain rfl := List.mem_singleton.mp hp'
          exact Subst.not_mem_onTy_freeVars hW1rng
            (by simp only [Ty.freeVars, List.mem_singleton]; omega)
      have hUτe : U.onTy τe = Ty.pair τα τ₀ := by
        rw [hUonTy]
        rw [show Subst.onTy [(Φ₁, Ty.fvar W), (Φ₁ + 1, Ty.fvar (W + 1))] τe = τe from
          Ty.substFvars_eq_self_of_no_key (by
            intro p hp
            rcases List.mem_cons.mp hp with rfl | hp'
            · exact hΦ₁τe
            · obtain rfl := List.mem_singleton.mp hp'
              exact hΦ₁1τe)]
        rw [← htye]
        apply Ty.substFvars_eq_self_of_no_key
        intro p hp
        rcases List.mem_cons.mp hp with rfl | hp'
        · simp only [Ty.freeVars, List.mem_dedup, List.mem_append, not_or]
          exact ⟨hWP, hWQ⟩
        · obtain rfl := List.mem_singleton.mp hp'
          simp only [Ty.freeVars, List.mem_dedup, List.mem_append, not_or]
          exact ⟨hW1P, hW1Q⟩
      have hUni : Unifies U τe (Ty.pair (Ty.fvar Φ₁) (Ty.fvar (Φ₁ + 1))) := by
        show U.onTy τe = U.onTy (Ty.pair (Ty.fvar Φ₁) (Ty.fvar (Φ₁ + 1)))
        rw [hUτe, Subst.onTy_pair, hUφ₁, hUφ₂]
      have h₂ := Duni
      have hUlc : ∀ p ∈ U, p.2.IsLC := by
        rw [hUdef]
        intro p hp
        rcases List.mem_append.mp hp with hp' | hp'
        · rcases List.mem_append.mp hp' with hp'' | hp''
          · rcases List.mem_cons.mp hp'' with rfl | hp'''
            · exact ContainsBvarsUpTo.fvar
            · obtain rfl := List.mem_singleton.mp hp'''
              exact ContainsBvarsUpTo.fvar
          · exact hR₁ p hp''
        · rcases List.mem_cons.mp hp' with rfl | hp''
          · exact hαLC
          · obtain rfl := List.mem_singleton.mp hp''
            exact hβLC
      obtain ⟨R₂, hR₂, hR₂lc⟩ := UnifyRel.greatest_lc h₂ U hUlc hUni
      refine ⟨R₂, ?_, ?_, hR₂lc⟩
      · intro v hv
        have ht1 : Ty.BelowFvars Φ₁ (S₁.onTy (Ty.fvar v)) :=
          Subst.onTy_belowFvars hbe.2 (Ty.BelowFvars.fvar (by omega))
        have hΦ₁t : Φ₁ ∉ (S₁.onTy (Ty.fvar v)).freeVars := fun hm => by
          have := ht1.mem_lt _ hm; omega
        have hΦ₁1t : Φ₁ + 1 ∉ (S₁.onTy (Ty.fvar v)).freeVars := fun hm => by
          have := ht1.mem_lt _ hm; omega
        have hWt : W ∉ (S₁.onTy (Ty.fvar v)).freeVars := fun hm => by
          have := ht1.mem_lt _ hm; omega
        have hW1t : W + 1 ∉ (S₁.onTy (Ty.fvar v)).freeVars := fun hm => by
          have := ht1.mem_lt _ hm; omega
        have hWR₁t : W ∉ (R₁.onTy (S₁.onTy (Ty.fvar v))).freeVars :=
          Subst.not_mem_onTy_freeVars hWrng hWt
        have hW1R₁t : W + 1 ∉ (R₁.onTy (S₁.onTy (Ty.fvar v))).freeVars :=
          Subst.not_mem_onTy_freeVars hW1rng hW1t
        calc S₀.onTy (Ty.fvar v)
            = (S₁ ++ R₁).onTy (Ty.fvar v) := hage v hv
          _ = R₁.onTy (S₁.onTy (Ty.fvar v)) := by rw [Subst.onTy_append]
          _ = U.onTy (S₁.onTy (Ty.fvar v)) := by
                rw [hUonTy,
                  show Subst.onTy [(Φ₁, Ty.fvar W), (Φ₁ + 1, Ty.fvar (W + 1))]
                      (S₁.onTy (Ty.fvar v)) = S₁.onTy (Ty.fvar v) from
                    Ty.substFvars_eq_self_of_no_key (by
                      intro p hp
                      rcases List.mem_cons.mp hp with rfl | hp'
                      · exact hΦ₁t
                      · obtain rfl := List.mem_singleton.mp hp'
                        exact hΦ₁1t)]
                exact (Ty.substFvars_eq_self_of_no_key (by
                  intro p hp
                  rcases List.mem_cons.mp hp with rfl | hp'
                  · exact hWR₁t
                  · obtain rfl := List.mem_singleton.mp hp'
                    exact hW1R₁t)).symm
          _ = R₂.onTy (S₂.onTy (S₁.onTy (Ty.fvar v))) := hR₂ (S₁.onTy (Ty.fvar v))
          _ = ((S₁ ++ S₂) ++ R₂).onTy (Ty.fvar v) := by simp only [Subst.onTy_append]
      · rw [← hR₂ (Ty.fvar (Φ₁ + 1)), hUφ₂]
  | match_ Dscrut hne Duni Dbr =>
    expose_names
    -- Extract the declarative scrutinee/branch typings with explicit names.
    obtain ⟨tnD, taD, hscrutD, hbrsD⟩ :
        ∃ tn ta, TypeOfHM (S₀.onCtx ctx) scrut (.customTy tn ta) ∧
          ∀ br ∈ branches, TypeOfMatchBranch (S₀.onCtx ctx) br tn ta τ₀ := by
      cases hty with
      | match_ h1 _ h3 => exact ⟨_, _, h1, h3⟩
    -- Reconcile the declarative type name/arity with the algorithm's (via the first branch).
    obtain ⟨htn, har⟩ : tnD = tyName ∧ arity = taD.length := by
      obtain ⟨pat0, body0, rest0, hbeq⟩ : ∃ p b r, branches = (p, b) :: r := by
        cases branches with
        | nil => exact absurd rfl hne
        | cons hd tl => obtain ⟨p, b⟩ := hd; exact ⟨p, b, tl, rfl⟩
      have hmem0 : (pat0, body0) ∈ branches := by rw [hbeq]; exact List.mem_cons_self ..
      cases hbrsD (pat0, body0) hmem0 with
      | mk hlookD htyNameD hpcD _ _ _ _ _ =>
        rw [hbeq] at Dbr
        cases Dbr with
        | cons hlookA htyNameA hpcA _ _ _ _ =>
          have hco := Option.some.inj (hlookD.symm.trans hlookA)
          subst hco
          refine ⟨htyNameD.symm.trans htyNameA, ?_⟩
          have hlen : (((freshVars Φ₁ arity).map (Ty.fvar ·)).map S₂.onTy).length = arity := by
            simp only [List.length_map, freshVars_length]
          rw [← hpcD, hpcA, hlen]
    subst tnD
    subst arity
    -- STEP 1: scrutinee IH (from the *given* `Dscrut`).
    obtain ⟨R₁, hags, htys, hR₁⟩ := Infer.complete' Dscrut hwf hbelow hS₀ hscrutD
    have hS₁ := (Infer.lc Dscrut hwf).2
    have hτsLC := (Infer.lc Dscrut hwf).1
    have hbs := Infer.belowFvars Dscrut hbelow
    have hle1 := Infer.frontier_le Dscrut
    have hwf₁ := Subst.onCtx_wf hS₁ hwf
    have hbelow₁ := Subst.onCtx_below hbs.2 hle1 hbelow
    have hctxeq : R₁.onCtx (S₁.onCtx ctx) = S₀.onCtx ctx := by
      rw [← Subst.onCtx_append]
      exact Subst.onCtx_congr (fun v hv => (hags v hv).symm) hbelow
    have htyArgs_lc : ∀ t ∈ taD, t.IsLC := by
      have hreg := TypeOfHM.regular hscrutD
      cases hreg with
      | customTy h => exact h
    have hτ₀_lc : τ₀.IsLC := by
      obtain ⟨hd, tl, hcons⟩ := List.exists_cons_of_ne_nil hne
      have hmem_hd : hd ∈ branches := by rw [hcons]; exact List.mem_cons_self ..
      exact TypeOfMatchBranch.regular (hbrsD hd hmem_hd)
    -- STEP 2: super-fresh block and the explicit unifier `U`.
    obtain ⟨W₀, hW₀ge, hW₀fresh⟩ := exists_fresh_block
      (R₁.map Prod.fst ++ R₁.flatMap (fun p => p.2.freeVars)
        ++ taD.flatMap Ty.freeVars ++ τ₀.freeVars) Φ₁ (taD.length + 1)
    obtain ⟨U, hUdef⟩ : ∃ U : Subst,
      U = (freshVars Φ₁ (taD.length + 1)).zip ((freshVars W₀ (taD.length + 1)).map (Ty.fvar ·))
          ++ R₁ ++ (freshVars W₀ (taD.length + 1)).zip (taD ++ [τ₀]) := ⟨_, rfl⟩
    have hUonTy : ∀ x, U.onTy x =
        Subst.onTy ((freshVars W₀ (taD.length + 1)).zip (taD ++ [τ₀]))
          (R₁.onTy (Subst.onTy ((freshVars Φ₁ (taD.length + 1)).zip
            ((freshVars W₀ (taD.length + 1)).map (Ty.fvar ·))) x)) := by
      intro x
      rw [hUdef, Subst.onTy_append, Subst.onTy_append]
    have hWi_mem : ∀ {i : Nat}, i < taD.length + 1 →
        W₀ + i ∈ freshVars W₀ (taD.length + 1) := by
      intro i hi
      simp only [freshVars, List.mem_map, List.mem_range]
      exact ⟨i, hi, rfl⟩
    have hWs_notin_R₁keys : ∀ w ∈ freshVars W₀ (taD.length + 1), w ∉ R₁.map Prod.fst := by
      intro w hw hc
      have hwge := freshVars_ge w hw
      have := hW₀fresh w (List.mem_append_left _ (List.mem_append_left _
        (List.mem_append_left _ hc)))
      omega
    have hWs_R₁range : ∀ w ∈ freshVars W₀ (taD.length + 1), ∀ q ∈ R₁, w ∉ q.2.freeVars := by
      intro w hw q hq hc
      have hwge := freshVars_ge w hw
      have := hW₀fresh w (List.mem_append_left _ (List.mem_append_left _
        (List.mem_append_right _ (List.mem_flatMap.mpr ⟨q, hq, hc⟩))))
      omega
    have htyArgs_belowW₀ : ∀ t ∈ taD, Ty.BelowFvars W₀ t := by
      intro t ht
      apply Ty.BelowFvars.of_freeVars_lt
      intro v hv
      exact hW₀fresh v (List.mem_append_left _ (List.mem_append_right _
        (List.mem_flatMap.mpr ⟨t, ht, hv⟩)))
    have hτ₀_belowW₀ : Ty.BelowFvars W₀ τ₀ := by
      apply Ty.BelowFvars.of_freeVars_lt
      intro v hv
      exact hW₀fresh v (List.mem_append_right _ hv)
    have hU_index : ∀ (i : Nat) (v : Ty), i < taD.length + 1 →
        (taD ++ [τ₀])[i]? = some v → U.onTy (Ty.fvar (Φ₁ + i)) = v := by
      intro i v hi hvi
      rw [hUonTy]
      have hL1 : Subst.onTy ((freshVars Φ₁ (taD.length + 1)).zip
          ((freshVars W₀ (taD.length + 1)).map (Ty.fvar ·))) (Ty.fvar (Φ₁ + i))
          = Ty.fvar (W₀ + i) := by
        apply Ty.substFvars_zip_fvar_eq' freshVars_nodup (freshVars_getElem? hi)
        · rw [List.getElem?_map, freshVars_getElem? hi]; rfl
        · intro X hX hc
          simp only [Ty.freeVars, List.mem_singleton] at hc
          have hXlt := freshVars_lt X hX
          omega
      rw [hL1]
      have hL2 : R₁.onTy (Ty.fvar (W₀ + i)) = Ty.fvar (W₀ + i) := by
        apply Ty.substFvars_eq_self_of_no_key
        intro p hp hc
        simp only [Ty.freeVars, List.mem_singleton] at hc
        have hkey : p.1 ∈ R₁.map Prod.fst := List.mem_map.mpr ⟨p, hp, rfl⟩
        rw [hc] at hkey
        exact hWs_notin_R₁keys (W₀ + i) (hWi_mem hi) hkey
      rw [hL2]
      apply Ty.substFvars_zip_fvar_eq' freshVars_nodup (freshVars_getElem? hi) hvi
      intro w hw hc
      have hwge := freshVars_ge w hw
      have hvmem : v ∈ (taD ++ [τ₀]) := List.mem_of_getElem? hvi
      have hvbelow : Ty.BelowFvars W₀ v := by
        rcases List.mem_append.mp hvmem with hvt | hvτ
        · exact htyArgs_belowW₀ v hvt
        · have hvτ₀ : v = τ₀ := List.mem_singleton.mp hvτ
          rw [hvτ₀]; exact hτ₀_belowW₀
      have := hvbelow.mem_lt w hc
      omega
    have hmap_eq : ((freshVars Φ₁ taD.length).map (Ty.fvar ·)).map U.onTy = taD := by
      apply List.ext_getElem?
      intro i
      rcases Nat.lt_or_ge i taD.length with hi | hi
      · rw [List.getElem?_map, List.getElem?_map, freshVars_getElem? hi]
        simp only [Option.map_some]
        rw [List.getElem?_eq_getElem hi]
        congr 1
        exact hU_index i (taD[i]'hi) (by omega)
          (by rw [List.getElem?_append_left hi, List.getElem?_eq_getElem hi])
      · rw [List.getElem?_eq_none (by simp only [List.length_map, freshVars_length]; exact hi),
          List.getElem?_eq_none hi]
    have hA_id_τs : Subst.onTy ((freshVars Φ₁ (taD.length + 1)).zip
        ((freshVars W₀ (taD.length + 1)).map (Ty.fvar ·))) τs = τs := by
      apply Ty.substFvars_eq_self_of_no_key
      intro p hp hc
      have hp1 : p.1 ∈ freshVars Φ₁ (taD.length + 1) := (List.of_mem_zip hp).1
      have hge := freshVars_ge p.1 hp1
      have hlt := hbs.1.mem_lt p.1 hc
      omega
    have hC_id_custom : Subst.onTy ((freshVars W₀ (taD.length + 1)).zip (taD ++ [τ₀]))
        (Ty.customTy tyName taD) = Ty.customTy tyName taD := by
      apply Ty.substFvars_eq_self_of_no_key
      intro p hp hc
      have hp1 : p.1 ∈ freshVars W₀ (taD.length + 1) := (List.of_mem_zip hp).1
      have hge := freshVars_ge p.1 hp1
      have hcb : Ty.BelowFvars W₀ (Ty.customTy tyName taD) := .customTy htyArgs_belowW₀
      have hlt := hcb.mem_lt p.1 hc
      omega
    have hUL : U.onTy τs = Ty.customTy tyName taD := by
      rw [hUonTy, hA_id_τs, ← htys]
      exact hC_id_custom
    have hUR : U.onTy (Ty.customTy tyName ((freshVars Φ₁ taD.length).map (Ty.fvar ·)))
        = Ty.customTy tyName taD := by
      rw [Subst.onTy_customTy, hmap_eq]
    have hUni : Unifies U τs (Ty.customTy tyName ((freshVars Φ₁ taD.length).map (Ty.fvar ·))) := by
      show U.onTy τs = U.onTy (Ty.customTy tyName ((freshVars Φ₁ taD.length).map (Ty.fvar ·)))
      rw [hUL, hUR]
    have hcustomTy_lc : (Ty.customTy tyName ((freshVars Φ₁ taD.length).map (Ty.fvar ·))).IsLC :=
      ContainsBvarsUpTo.customTy (fun t ht => by
        obtain ⟨x, _, rfl⟩ := List.mem_map.mp ht; exact ContainsBvarsUpTo.fvar)
    -- STEP 5: the MGU `S₂` is the *given* `Duni`; factor `U` through it.
    have h₂ := Duni
    have hUlc : ∀ p ∈ U, p.2.IsLC := by
      rw [hUdef]
      intro p hp
      rcases List.mem_append.mp hp with hp' | hp'
      · rcases List.mem_append.mp hp' with hp'' | hp''
        · have hmem := (List.of_mem_zip hp'').2
          obtain ⟨x, _, hxeq⟩ := List.mem_map.mp hmem
          rw [← hxeq]; exact ContainsBvarsUpTo.fvar
        · exact hR₁ p hp''
      · have hmem := (List.of_mem_zip hp').2
        rcases List.mem_append.mp hmem with ht | hτ
        · exact htyArgs_lc p.2 ht
        · have hpτ₀ : p.2 = τ₀ := List.mem_singleton.mp hτ
          rw [hpτ₀]; exact hτ₀_lc
    obtain ⟨R₂, hR₂_eq, hR₂lc⟩ := UnifyRel.greatest_lc h₂ U hUlc hUni
    have hS₂ : ∀ p ∈ S₂, p.2.IsLC := UnifyRel.lc h₂ hτsLC hcustomTy_lc
    have hbS₂ : ∀ p ∈ S₂, Ty.BelowFvars (Φ₁ + taD.length + 1) p.2 := by
      apply UnifyRel.belowFvars h₂ (hbs.1.mono (by omega))
      apply Ty.BelowFvars.customTy
      intro t ht
      obtain ⟨x, hx, rfl⟩ := List.mem_map.mp ht
      exact Ty.BelowFvars.fvar (by have := freshVars_lt x hx; omega)
    -- STEP 6: residual facts connecting `R₂` to the declarative data.
    have hUeqR₁ : ∀ v, v < Φ₁ → U.onTy (Ty.fvar v) = R₁.onTy (Ty.fvar v) := by
      intro v hv
      rw [hUonTy]
      have hA_id : Subst.onTy ((freshVars Φ₁ (taD.length + 1)).zip
          ((freshVars W₀ (taD.length + 1)).map (Ty.fvar ·))) (Ty.fvar v) = Ty.fvar v := by
        apply Ty.substFvars_eq_self_of_no_key
        intro p hp hc
        simp only [Ty.freeVars, List.mem_singleton] at hc
        have hp1 : p.1 ∈ freshVars Φ₁ (taD.length + 1) := (List.of_mem_zip hp).1
        have := freshVars_ge p.1 hp1
        omega
      rw [hA_id]
      apply Ty.substFvars_eq_self_of_no_key
      intro p hp hc
      have hp1 : p.1 ∈ freshVars W₀ (taD.length + 1) := (List.of_mem_zip hp).1
      have hge := freshVars_ge p.1 hp1
      exact Subst.not_mem_onTy_freeVars (hWs_R₁range p.1 hp1)
        (by simp only [Ty.freeVars, List.mem_singleton]; omega) hc
    have hR₂ctx : R₂.onCtx (S₂.onCtx (S₁.onCtx ctx)) = S₀.onCtx ctx := by
      rw [← Subst.onCtx_comp_of_onTy_eq hR₂_eq, Subst.onCtx_congr hUeqR₁ hbelow₁, hctxeq]
    have hta_lc : ∀ t ∈ ((freshVars Φ₁ taD.length).map (Ty.fvar ·)).map S₂.onTy, t.IsLC := by
      intro t ht
      obtain ⟨t0, ht0, rfl⟩ := List.mem_map.mp ht
      obtain ⟨x, _, rfl⟩ := List.mem_map.mp ht0
      exact Subst.onTy_lc hS₂ ContainsBvarsUpTo.fvar
    have hta_below : ∀ t ∈ ((freshVars Φ₁ taD.length).map (Ty.fvar ·)).map S₂.onTy,
        Ty.BelowFvars (Φ₁ + taD.length + 1) t := by
      intro t ht
      obtain ⟨t0, ht0, rfl⟩ := List.mem_map.mp ht
      obtain ⟨x, hx, rfl⟩ := List.mem_map.mp ht0
      exact Subst.onTy_belowFvars hbS₂ (Ty.BelowFvars.fvar (by have := freshVars_lt x hx; omega))
    have hρ_lc : (S₂.onTy (Ty.fvar (Φ₁ + taD.length))).IsLC :=
      Subst.onTy_lc hS₂ ContainsBvarsUpTo.fvar
    have hρ_below : Ty.BelowFvars (Φ₁ + taD.length + 1)
        (S₂.onTy (Ty.fvar (Φ₁ + taD.length))) :=
      Subst.onTy_belowFvars hbS₂ (Ty.BelowFvars.fvar (by omega))
    have hta_R₂ : (((freshVars Φ₁ taD.length).map (Ty.fvar ·)).map S₂.onTy).map R₂.onTy
        = taD := by
      rw [List.map_map]
      exact Eq.trans (List.map_congr_left (fun t _ => (hR₂_eq t).symm)) hmap_eq
    have hρ_R₂ : R₂.onTy (S₂.onTy (Ty.fvar (Φ₁ + taD.length))) = τ₀ := by
      rw [← hR₂_eq]
      exact hU_index taD.length τ₀ (by omega)
        (by rw [List.getElem?_append_right (Nat.le_refl _)]; simp)
    -- STEP 7: branch declarative typings, recast over the algorithmic data.
    have hbr' : ∀ br ∈ branches,
        TypeOfMatchBranch (R₂.onCtx (S₂.onCtx (S₁.onCtx ctx))) br tyName
          ((((freshVars Φ₁ taD.length).map (Ty.fvar ·)).map S₂.onTy).map R₂.onTy)
          (R₂.onTy (S₂.onTy (Ty.fvar (Φ₁ + taD.length)))) := by
      intro br hbr_mem
      rw [hR₂ctx, hta_R₂, hρ_R₂]
      exact hbrsD br hbr_mem
    -- STEP 8: thread the branch list with the *given* `Dbr`.
    obtain ⟨R₃, hagbr, hR₃lc⟩ :=
      InferBranches.complete' Dbr (Subst.onCtx_wf hS₂ hwf₁)
        (Subst.onCtx_below hbS₂ (by omega) hbelow₁)
        hta_lc hta_below hρ_lc hρ_below hR₂lc hbr'
    -- STEP 9: assemble.
    refine ⟨R₃, ?_, ?_, hR₃lc⟩
    · intro v hv
      have hag2 : ∀ w, w < Φ₁ → R₁.onTy (Ty.fvar w) = (S₂ ++ R₂).onTy (Ty.fvar w) := by
        intro w hw
        rw [Subst.onTy_append, ← hR₂_eq]
        exact (hUeqR₁ w hw).symm
      have ht1 : Ty.BelowFvars Φ₁ (S₁.onTy (Ty.fvar v)) :=
        Subst.onTy_belowFvars hbs.2 (Ty.BelowFvars.fvar (by omega))
      have ht2 : Ty.BelowFvars (Φ₁ + taD.length + 1) (S₂.onTy (S₁.onTy (Ty.fvar v))) :=
        Subst.onTy_belowFvars hbS₂ (ht1.mono (by omega))
      calc S₀.onTy (Ty.fvar v)
          = (S₁ ++ R₁).onTy (Ty.fvar v) := hags v hv
        _ = R₁.onTy (S₁.onTy (Ty.fvar v)) := by rw [Subst.onTy_append]
        _ = (S₂ ++ R₂).onTy (S₁.onTy (Ty.fvar v)) := Subst.onTy_congr hag2 ht1
        _ = R₂.onTy (S₂.onTy (S₁.onTy (Ty.fvar v))) := by rw [Subst.onTy_append]
        _ = (S₃ ++ R₃).onTy (S₂.onTy (S₁.onTy (Ty.fvar v))) := Subst.onTy_congr hagbr ht2
        _ = ((S₁ ++ S₂ ++ S₃) ++ R₃).onTy (Ty.fvar v) := by simp only [Subst.onTy_append]
    · calc τ₀ = R₂.onTy (S₂.onTy (Ty.fvar (Φ₁ + taD.length))) := hρ_R₂.symm
        _ = (S₃ ++ R₃).onTy (S₂.onTy (Ty.fvar (Φ₁ + taD.length))) :=
              Subst.onTy_congr hagbr hρ_below
        _ = R₃.onTy (S₃.onTy (S₂.onTy (Ty.fvar (Φ₁ + taD.length)))) := by rw [Subst.onTy_append]

theorem InferBranches.complete' {Φ ctx tn ta ρ branches Φ' S}
    (h : InferBranches Φ ctx tn ta ρ branches Φ' S)
    (hwf : CtxWF ctx) (hbelow : CtxBelow Φ ctx)
    (hta : ∀ t ∈ ta, t.IsLC) (hbta : ∀ t ∈ ta, Ty.BelowFvars Φ t)
    (hρ : ρ.IsLC) (hbρ : Ty.BelowFvars Φ ρ)
    {R₀ : Subst} (hR₀ : ∀ p ∈ R₀, p.2.IsLC)
    (hbr : ∀ br ∈ branches, TypeOfMatchBranch (R₀.onCtx ctx) br tn (ta.map R₀.onTy) (R₀.onTy ρ)) :
    ∃ R', Subst.AgreesBelow Φ R₀ (S ++ R') ∧ (∀ p ∈ R', p.2.IsLC) := by
  cases h with
  | nil => exact ⟨R₀, fun v _ => by rw [List.nil_append], hR₀⟩
  | cons hlook htyName hpc hpc2 Dbody Duni Drest =>
      expose_names
      have hbodyWF : CtxWF { ctx with
          env := (ctor.contents.map (Ty.openWith ta)).map PolyTy.mkTrivial ++ ctx.env } :=
        branchBindings_wf hwf hta hpc
      have hbodyBelow : CtxBelow Φ { ctx with
          env := (ctor.contents.map (Ty.openWith ta)).map PolyTy.mkTrivial ++ ctx.env } :=
        branchBindings_below hbelow hbta
      have hbodyty2 : TypeOfHM (R₀.onCtx { ctx with
          env := (ctor.contents.map (Ty.openWith ta)).map PolyTy.mkTrivial ++ ctx.env })
          body (R₀.onTy ρ) := by
        cases hbr (pat, body) (List.mem_cons_self ..) with
        | mk hlookD htyNameD hpcD hpc2D hforallD hpbD hbctxD hbodytyD =>
          have hco := Option.some.inj (hlook.symm.trans hlookD)
          subst hco
          have hinsts := instContents_eq_openWith hforallD (fun c hc => hpcD ▸ ctor.bound c hc)
          rw [hbctxD, hpbD, hinsts] at hbodytyD
          rw [Subst.onCtx_branchBindings hR₀]
          exact hbodytyD
      -- STEP: head branch body principality from the *given* derivation `Dbody`.
      obtain ⟨R_b, hagbody, htybody, hR_b⟩ :=
        Infer.complete' Dbody hbodyWF hbodyBelow hR₀ hbodyty2
      have hbodyLC := Infer.lc Dbody hbodyWF
      have hτb_lc := hbodyLC.1
      have hS_b := hbodyLC.2
      have hbb := Infer.belowFvars Dbody hbodyBelow
      have hle_b := Infer.frontier_le Dbody
      -- STEP: `R_b` unifies `τb` with `S₁.onTy ρ`; the MGU is the *given* `Duni`.
      have hUni : Unifies R_b τb (S₁.onTy ρ) := by
        show R_b.onTy τb = R_b.onTy (S₁.onTy ρ)
        rw [← htybody, ← Subst.onTy_append]
        exact Subst.onTy_congr hagbody hbρ
      have h_u := Duni
      obtain ⟨R_u, hR_u_eq, hR_u⟩ := UnifyRel.greatest_lc h_u R_b hR_b hUni
      have hS_u := UnifyRel.lc h_u hτb_lc (Subst.onTy_lc hS_b hρ)
      have hS_u_below := UnifyRel.belowFvars h_u hbb.1 (Subst.onTy_belowFvars hbb.2 (hbρ.mono hle_b))
      -- STEP: hypotheses for the recursion on `rest`.
      have hwf' : CtxWF (S₂.onCtx (S₁.onCtx ctx)) :=
        Subst.onCtx_wf hS_u (Subst.onCtx_wf hS_b hwf)
      have hbelow_Sb : CtxBelow Φ₁ (S₁.onCtx ctx) := Subst.onCtx_below hbb.2 hle_b hbelow
      have hbelow' : CtxBelow Φ₁ (S₂.onCtx (S₁.onCtx ctx)) :=
        Subst.onCtx_below hS_u_below (le_refl _) hbelow_Sb
      have hta' : ∀ t ∈ ta.map (fun t => S₂.onTy (S₁.onTy t)), t.IsLC := by
        intro t' ht'; obtain ⟨t0, ht0, rfl⟩ := List.mem_map.mp ht'
        exact Subst.onTy_lc hS_u (Subst.onTy_lc hS_b (hta t0 ht0))
      have hbta' : ∀ t ∈ ta.map (fun t => S₂.onTy (S₁.onTy t)), Ty.BelowFvars Φ₁ t := by
        intro t' ht'; obtain ⟨t0, ht0, rfl⟩ := List.mem_map.mp ht'
        exact Subst.onTy_belowFvars hS_u_below
          (Subst.onTy_belowFvars hbb.2 ((hbta t0 ht0).mono hle_b))
      have hρ' : (S₂.onTy (S₁.onTy ρ)).IsLC := Subst.onTy_lc hS_u (Subst.onTy_lc hS_b hρ)
      have hbρ' : Ty.BelowFvars Φ₁ (S₂.onTy (S₁.onTy ρ)) :=
        Subst.onTy_belowFvars hS_u_below (Subst.onTy_belowFvars hbb.2 (hbρ.mono hle_b))
      -- STEP: factoring identities for the recursion's declarative typings.
      have key_t : ∀ {t : Ty}, Ty.BelowFvars Φ t →
          R_u.onTy (S₂.onTy (S₁.onTy t)) = R₀.onTy t := by
        intro t ht
        rw [← hR_u_eq (S₁.onTy t), ← Subst.onTy_append]
        exact (Subst.onTy_congr hagbody ht).symm
      have hctx_eq : R_u.onCtx (S₂.onCtx (S₁.onCtx ctx)) = R₀.onCtx ctx := by
        rw [← Subst.onCtx_comp_of_onTy_eq hR_u_eq, ← Subst.onCtx_append]
        exact Subst.onCtx_congr (fun v hv => (hagbody v hv).symm) hbelow
      have hta_eq : (ta.map (fun t => S₂.onTy (S₁.onTy t))).map R_u.onTy = ta.map R₀.onTy := by
        rw [List.map_map]
        apply List.map_congr_left
        intro t ht
        simpa using key_t (hbta t ht)
      have hρ_eq : R_u.onTy (S₂.onTy (S₁.onTy ρ)) = R₀.onTy ρ := key_t hbρ
      have hdecl' : ∀ br ∈ rest, TypeOfMatchBranch (R_u.onCtx (S₂.onCtx (S₁.onCtx ctx)))
          br tn ((ta.map (fun t => S₂.onTy (S₁.onTy t))).map R_u.onTy)
          (R_u.onTy (S₂.onTy (S₁.onTy ρ))) := by
        intro br hbr2
        rw [hctx_eq, hta_eq, hρ_eq]
        exact hbr br (List.mem_cons_of_mem _ hbr2)
      -- STEP: recurse on `rest` via the *given* `Drest`.
      obtain ⟨R_r, hagrest, hR_r⟩ :=
        InferBranches.complete' Drest hwf' hbelow' hta' hbta' hρ' hbρ' hR_u hdecl'
      -- STEP: assemble.
      refine ⟨R_r, ?_, hR_r⟩
      intro v hv
      have hbv1 : Ty.BelowFvars Φ₁ (S₁.onTy (.fvar v)) :=
        Subst.onTy_belowFvars hbb.2 (.fvar (by omega))
      have hbv2 : Ty.BelowFvars Φ₁ (S₂.onTy (S₁.onTy (.fvar v))) :=
        Subst.onTy_belowFvars hS_u_below hbv1
      calc R₀.onTy (.fvar v)
          = (S₁ ++ R_b).onTy (.fvar v) := hagbody v hv
        _ = R_b.onTy (S₁.onTy (.fvar v)) := by rw [Subst.onTy_append]
        _ = R_u.onTy (S₂.onTy (S₁.onTy (.fvar v))) := hR_u_eq (S₁.onTy (.fvar v))
        _ = (S₃ ++ R_r).onTy (S₂.onTy (S₁.onTy (.fvar v))) := Subst.onTy_congr hagrest hbv2
        _ = ((S₁ ++ S₂ ++ S₃) ++ R_r).onTy (.fvar v) := by simp only [Subst.onTy_append]
end

/-- Output-uniqueness up to instance: any two `Infer` results on the same input
    are mutual substitution-instances. (From `complete'` of the first applied to
    the `sound` typing of the second.) -/
theorem Infer.output_unique {Φ ctx e Φ'₁ S₁ τ₁ Φ'₂ S₂ τ₂}
    (h₁ : Infer Φ ctx e Φ'₁ S₁ τ₁) (h₂ : Infer Φ ctx e Φ'₂ S₂ τ₂)
    (hwf : CtxWF ctx) (hbelow : CtxBelow Φ ctx) :
    ∃ R, τ₂ = Subst.onTy R τ₁ ∧ (∀ p ∈ R, p.2.IsLC) := by
  obtain ⟨R, _, hfac, hRlc⟩ :=
    h₁.complete' hwf hbelow (Infer.lc h₂ hwf).2 (Infer.sound h₂ hwf)
  exact ⟨R, hfac, hRlc⟩

/-- `(S, τ)` is a *principal typing* of `e` in `ctx`: a valid declarative typing
    of which every declarative typing (under any LC specialization of `ctx`) is a
    substitution instance. -/
structure Infer.IsPrincipal (ctx : Ctx) (e : Expr) (S : Subst) (τ : Ty) : Prop where
  typing : TypeOfHM (S.onCtx ctx) e τ
  principal : ∀ {S₀ : Subst} {τ₀ : Ty}, (∀ p ∈ S₀, p.2.IsLC) →
    TypeOfHM (S₀.onCtx ctx) e τ₀ → ∃ R, τ₀ = Subst.onTy R τ

/-- Every `Infer` result is a principal typing. With `Infer.complete`'s existence
    half, `Infer` computes the principal type of any typeable `e`. -/
theorem Infer.isPrincipal {Φ ctx e Φ' S τ} (h : Infer Φ ctx e Φ' S τ)
    (hwf : CtxWF ctx) (hbelow : CtxBelow Φ ctx) :
    Infer.IsPrincipal ctx e S τ where
  typing := Infer.sound h hwf
  principal := fun hS₀ hty => by
    obtain ⟨R, _, hfac, _⟩ := h.complete' hwf hbelow hS₀ hty
    exact ⟨R, hfac⟩





/-! ## Stage 4: the executable `unify` and `infer`

Everything above specifies and certifies the *relations* `UnifyRel` and `Infer`.
This final stage gives the actual *functions* (`unify`, `infer`) and proves they
**refine** those relations. The only non-trivial part is `unify`'s termination,
discharged with the standard lexicographic measure `(#distinct free vars, size)`:
each var-elimination step strictly drops the variable count, while the structural
decompositions (`arrow`/`pair`/`customTy`) drop `Ty.size`. The supporting
variable-tracking lemmas about `UnifyRel`-substitutions are proved first. -/

/-! ### Variable-tracking lemmas for substitutions and `UnifyRel`

`Subst.mem_freeVars_onTy` bounds the free vars of a substituted type by the
input's vars plus the substitution's range; `UnifyRel.range_mem` / `.dom_mem`
locate a derived substitution's range/domain inside the inputs' vars; and
`UnifyRel.eliminates` is the occurs-check at the variable-set level (a domain
variable never survives in any image). Together they make the termination
measure of `unify` strictly decrease. -/

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
  | pair a b iha ihb =>
    simp only [Ty.substFvar, Ty.freeVars, List.mem_dedup, List.mem_append] at hv
    rcases hv with h | h
    · rcases iha h with h' | h'
      · exact Or.inl (by simp only [Ty.freeVars, List.mem_dedup, List.mem_append]; exact Or.inl h')
      · exact Or.inr h'
    · rcases ihb h with h' | h'
      · exact Or.inl (by simp only [Ty.freeVars, List.mem_dedup, List.mem_append]; exact Or.inr h')
      · exact Or.inr h'
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
theorem Ty.mem_freeVars_pairL {a b : Ty} {v : Nat} (h : v ∈ a.freeVars) :
    v ∈ (Ty.pair a b).freeVars := by
  simp only [Ty.freeVars, List.mem_dedup, List.mem_append]; exact Or.inl h
theorem Ty.mem_freeVars_pairR {a b : Ty} {v : Nat} (h : v ∈ b.freeVars) :
    v ∈ (Ty.pair a b).freeVars := by
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
  | pair a b iha ihb =>
    simp only [Ty.substFvar, Ty.freeVars, List.mem_dedup, List.mem_append, not_or]
    exact ⟨iha, ihb⟩
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
  | _, _, _, @UnifyRel.pair a b c d S₁ S₂ h₁ h₂ => by
    intro p hp v hv
    rw [List.mem_append] at hp
    rcases hp with hp | hp
    · rcases UnifyRel.range_mem h₁ p hp v hv with h | h
      · exact Or.inl (Ty.mem_freeVars_pairL h)
      · exact Or.inr (Ty.mem_freeVars_pairL h)
    · rcases UnifyRel.range_mem h₂ p hp v hv with h | h
      · rcases Subst.mem_freeVars_onTy h with hb | ⟨q, hq, hvq⟩
        · exact Or.inl (Ty.mem_freeVars_pairR hb)
        · rcases UnifyRel.range_mem h₁ q hq v hvq with h' | h'
          · exact Or.inl (Ty.mem_freeVars_pairL h')
          · exact Or.inr (Ty.mem_freeVars_pairL h')
      · rcases Subst.mem_freeVars_onTy h with hd | ⟨q, hq, hvq⟩
        · exact Or.inr (Ty.mem_freeVars_pairR hd)
        · rcases UnifyRel.range_mem h₁ q hq v hvq with h' | h'
          · exact Or.inl (Ty.mem_freeVars_pairL h')
          · exact Or.inr (Ty.mem_freeVars_pairL h')
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
  | _, _, _, @UnifyRel.pair a b c d S₁ S₂ h₁ h₂ => by
    intro p hp
    rw [List.mem_append] at hp
    rcases hp with hp | hp
    · rcases UnifyRel.dom_mem h₁ p hp with h | h
      · exact Or.inl (Ty.mem_freeVars_pairL h)
      · exact Or.inr (Ty.mem_freeVars_pairL h)
    · rcases UnifyRel.dom_mem h₂ p hp with h | h
      · rcases Subst.mem_freeVars_onTy h with hb | ⟨q, hq, hvq⟩
        · exact Or.inl (Ty.mem_freeVars_pairR hb)
        · rcases UnifyRel.range_mem h₁ q hq p.1 hvq with h' | h'
          · exact Or.inl (Ty.mem_freeVars_pairL h')
          · exact Or.inr (Ty.mem_freeVars_pairL h')
      · rcases Subst.mem_freeVars_onTy h with hd | ⟨q, hq, hvq⟩
        · exact Or.inr (Ty.mem_freeVars_pairR hd)
        · rcases UnifyRel.range_mem h₁ q hq p.1 hvq with h' | h'
          · exact Or.inl (Ty.mem_freeVars_pairL h')
          · exact Or.inr (Ty.mem_freeVars_pairL h')
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
  | _, _, _, @UnifyRel.pair a b c d S₁ S₂ h₁ h₂ => by
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

/-- First structural subcall of `pair`. -/
theorem unifyDec_pair1 {a₁ a₂ c₁ c₂ : Ty} :
    Prod.Lex (· < ·) (· < ·)
      ((pairVars a₁ c₁).length, a₁.size + c₁.size)
      ((pairVars (.pair a₁ a₂) (.pair c₁ c₂)).length,
        (Ty.pair a₁ a₂).size + (Ty.pair c₁ c₂).size) := by
  apply lexLt_of_le_of_lt
  · refine nodup_length_le pairVars_nodup (fun v hv => ?_)
    rw [mem_pairVars] at hv ⊢
    rcases hv with h | h
    · exact Or.inl (Ty.mem_freeVars_pairL h)
    · exact Or.inr (Ty.mem_freeVars_pairL h)
  · simp only [Ty.size]; have := @Ty.size_pos a₂; have := @Ty.size_pos c₂; omega

/-- Second subcall of `pair`. -/
theorem unifyDec_pair2 {a₁ a₂ c₁ c₂ : Ty} {S₁ : Subst} (hS₁ : UnifyRel a₁ c₁ S₁) :
    Prod.Lex (· < ·) (· < ·)
      ((pairVars (S₁.onTy a₂) (S₁.onTy c₂)).length,
        (S₁.onTy a₂).size + (S₁.onTy c₂).size)
      ((pairVars (.pair a₁ a₂) (.pair c₁ c₂)).length,
        (Ty.pair a₁ a₂).size + (Ty.pair c₁ c₂).size) := by
  have hsub : pairVars (S₁.onTy a₂) (S₁.onTy c₂)
      ⊆ pairVars (.pair a₁ a₂) (.pair c₁ c₂) := by
    intro v hv
    rw [mem_pairVars] at hv ⊢
    rcases hv with hv | hv
    · rcases Subst.mem_freeVars_onTy hv with h | ⟨q, hq, hvq⟩
      · exact Or.inl (Ty.mem_freeVars_pairR h)
      · rcases UnifyRel.range_mem hS₁ q hq v hvq with h' | h'
        · exact Or.inl (Ty.mem_freeVars_pairL h')
        · exact Or.inr (Ty.mem_freeVars_pairL h')
    · rcases Subst.mem_freeVars_onTy hv with h | ⟨q, hq, hvq⟩
      · exact Or.inr (Ty.mem_freeVars_pairR h)
      · rcases UnifyRel.range_mem hS₁ q hq v hvq with h' | h'
        · exact Or.inl (Ty.mem_freeVars_pairL h')
        · exact Or.inr (Ty.mem_freeVars_pairL h')
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
      · exact Or.inl (Ty.mem_freeVars_pairL h)
      · exact Or.inr (Ty.mem_freeVars_pairL h)
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

`unifyCore`/`unifyListCore` are the verified unifier: they return, on success, a
substitution *together with* its `UnifyRel` derivation. Carrying the derivation
is what lets the `decreasing_by` goals invoke the variable-tracking lemmas
(`unifyDec_*`) on the prefix unifier. The plain-`Option Subst` `unify` is the
erasure of this; soundness is then immediate and completeness is a short
structural argument. -/
mutual
def unifyCore (a b : Ty) : Option { S : Subst // UnifyRel a b S } :=
  match a, b with
  | .prim p, .prim q =>
      if h : p = q then some ⟨[], by subst h; exact .prim⟩ else none
  | .fvar n, .fvar m =>
      if h : n = m then some ⟨[], by subst h; exact .fvarRefl⟩
      else some ⟨[(n, .fvar m)], .fvarL (by simp only [ne_eq, Ty.fvar.injEq]; omega)
        (by simp only [Ty.freeVars, List.mem_singleton]; omega)⟩
  | .arrow a₁ a₂, .arrow c₁ c₂ =>
      match unifyCore a₁ c₁ with
      | none => none
      | some ⟨S₁, hS₁⟩ =>
        match unifyCore (S₁.onTy a₂) (S₁.onTy c₂) with
        | none => none
        | some ⟨S₂, hS₂⟩ => some ⟨S₁ ++ S₂, .arrow hS₁ hS₂⟩
  | .pair a₁ a₂, .pair c₁ c₂ =>
      match unifyCore a₁ c₁ with
      | none => none
      | some ⟨S₁, hS₁⟩ =>
        match unifyCore (S₁.onTy a₂) (S₁.onTy c₂) with
        | none => none
        | some ⟨S₂, hS₂⟩ => some ⟨S₁ ++ S₂, .pair hS₁ hS₂⟩
  | .customTy n₁ ts₁, .customTy n₂ ts₂ =>
      if h : n₁ = n₂ then
        match unifyListCore ts₁ ts₂ with
        | none => none
        | some ⟨S, hS⟩ => some ⟨S, by subst h; exact .customTy hS⟩
      else none
  | .fvar n, b =>
      if h : n ∈ b.freeVars then none
      else some ⟨[(n, b)], .fvarL (by intro he; subst he; exact h (by simp [Ty.freeVars])) h⟩
  | a, .fvar n =>
      if h : n ∈ a.freeVars then none
      else some ⟨[(n, a)], .fvarR (by intro he; subst he; exact h (by simp [Ty.freeVars])) h⟩
  | _, _ => none
termination_by ((pairVars a b).length, a.size + b.size)
decreasing_by
  · exact unifyDec_arrow1
  · exact unifyDec_arrow2 hS₁
  · exact unifyDec_pair1
  · exact unifyDec_pair2 hS₁
  · exact unifyDec_customTy

def unifyListCore (as bs : List Ty) : Option { S : Subst // UnifyRelList as bs S } :=
  match as, bs with
  | [], [] => some ⟨[], .nil⟩
  | t₁ :: ts₁, t₂ :: ts₂ =>
      match unifyCore t₁ t₂ with
      | none => none
      | some ⟨S₁, hS₁⟩ =>
        match unifyListCore (ts₁.map S₁.onTy) (ts₂.map S₁.onTy) with
        | none => none
        | some ⟨S₂, hS₂⟩ => some ⟨S₁ ++ S₂, .cons hS₁ hS₂⟩
  | _, _ => none
termination_by ((listVars as bs).length, TyList.size as + TyList.size bs + 1)
decreasing_by
  · exact unifyDec_cons1
  · exact unifyDec_cons2 hS₁
end

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


/-! ### The `infer` function (Algorithm W)

`inferCore`/`inferBranchesCore` mirror `Infer`/`InferBranches` exactly, building
the `Infer` derivation alongside the output (soundness by construction);
recursion is structural on the expression / branch list. The `match_` case reads
the type name + arity off the first branch's constructor (branches are nonempty).
The public `infer` erases the derivation. -/
mutual
def inferCore (Φ : Nat) (ctx : Ctx) (e : Expr) :
    Option { r : Nat × Subst × Ty // Infer Φ ctx e r.1 r.2.1 r.2.2 } :=
  match e with
  | .primLit .unit => some ⟨(Φ, [], .prim .unit), .primLitUnit⟩
  | .primLit (.int _) => some ⟨(Φ, [], .prim .int), .primLitInt⟩
  | .primLit (.nat _) => some ⟨(Φ, [], .prim .nat), .primLitNat⟩
  | .primLit (.bool _) => some ⟨(Φ, [], .prim .bool), .primLitBool⟩
  | .primLit (.str _) => some ⟨(Φ, [], .prim .str), .primLitStr⟩
  | .pair a b =>
      match inferCore Φ ctx a with
      | none => none
      | some ⟨(Φ₁, S₁, τa), ha⟩ =>
        match inferCore Φ₁ (S₁.onCtx ctx) b with
        | none => none
        | some ⟨(Φ₂, S₂, τb), hb⟩ =>
          some ⟨(Φ₂, S₁ ++ S₂, .pair (S₂.onTy τa) τb), .pair ha hb⟩
  | .lambda body =>
      match inferCore (Φ + 1) { ctx with env := PolyTy.mkTrivial (.fvar Φ) :: ctx.env } body with
      | none => none
      | some ⟨(Φ', S, τb), hbody⟩ =>
        some ⟨(Φ', S, .arrow (S.onTy (.fvar Φ)) τb), .lambda hbody⟩
  | .app f arg =>
      match inferCore Φ ctx f with
      | none => none
      | some ⟨(Φ₁, S₁, τf), hf⟩ =>
        match inferCore Φ₁ (S₁.onCtx ctx) arg with
        | none => none
        | some ⟨(Φ₂, S₂, τa), harg⟩ =>
          match unifyCore (S₂.onTy τf) (.arrow τa (.fvar Φ₂)) with
          | none => none
          | some ⟨S₃, h₃⟩ =>
            some ⟨(Φ₂ + 1, S₁ ++ S₂ ++ S₃, S₃.onTy (.fvar Φ₂)), .app hf harg h₃⟩
  | .var i =>
      match h : ctx.env[i]? with
      | none => none
      | some polyTy =>
        some ⟨(Φ + polyTy.paramCount, [], polyTy.openVars (freshVars Φ polyTy.paramCount)), .var h⟩
  | .ctor name =>
      match h : LookupList.get? ctx.ctors name with
      | none => none
      | some ctorr =>
        some ⟨(Φ + ctorr.paramCount, [], ctorr.toTy.openVars (freshVars Φ ctorr.paramCount)), .ctor h⟩
  | .letIn rhs body =>
      match inferCore Φ ctx rhs with
      | none => none
      | some ⟨(Φ₁, S₁, τ₁), hrhs⟩ =>
        match inferCore Φ₁
            { (S₁.onCtx ctx) with env := genScheme (S₁.onCtx ctx).env τ₁ :: (S₁.onCtx ctx).env }
            body with
        | none => none
        | some ⟨(Φ₂, S₂, τ₂), hbody⟩ =>
          some ⟨(Φ₂, S₁ ++ S₂, τ₂), .letIn hrhs hbody⟩
  | .fst e =>
      match inferCore Φ ctx e with
      | none => none
      | some ⟨(Φ₁, S₁, τe), he⟩ =>
        match unifyCore τe (.pair (.fvar Φ₁) (.fvar (Φ₁ + 1))) with
        | none => none
        | some ⟨S₂, huni⟩ =>
          some ⟨(Φ₁ + 2, S₁ ++ S₂, S₂.onTy (.fvar Φ₁)), .fst he huni⟩
  | .snd e =>
      match inferCore Φ ctx e with
      | none => none
      | some ⟨(Φ₁, S₁, τe), he⟩ =>
        match unifyCore τe (.pair (.fvar Φ₁) (.fvar (Φ₁ + 1))) with
        | none => none
        | some ⟨S₂, huni⟩ =>
          some ⟨(Φ₁ + 2, S₁ ++ S₂, S₂.onTy (.fvar (Φ₁ + 1))), .snd he huni⟩
  | .match_ scrut branches =>
      match inferCore Φ ctx scrut with
      | none => none
      | some ⟨(Φ₁, S₁, τs), hscrut⟩ =>
        match hh : branches.head? with
        | none => none
        | some b0 =>
          match hget : LookupList.get? ctx.ctors b0.1.ctor with
          | none => none
          | some ctor0 =>
            match unifyCore τs (.customTy ctor0.tyName ((freshVars Φ₁ ctor0.paramCount).map (Ty.fvar ·))) with
            | none => none
            | some ⟨S₂, huni⟩ =>
              match inferBranchesCore (Φ₁ + ctor0.paramCount + 1) (S₂.onCtx (S₁.onCtx ctx)) ctor0.tyName
                  (((freshVars Φ₁ ctor0.paramCount).map (Ty.fvar ·)).map S₂.onTy)
                  (S₂.onTy (.fvar (Φ₁ + ctor0.paramCount))) branches with
              | none => none
              | some ⟨(Φ₃, S₃), hbranches⟩ =>
                some ⟨(Φ₃, S₁ ++ S₂ ++ S₃, S₃.onTy (S₂.onTy (.fvar (Φ₁ + ctor0.paramCount)))),
                      .match_ hscrut (by intro hc; rw [hc] at hh; simp at hh) huni hbranches⟩

def inferBranchesCore (Φ : Nat) (ctx : Ctx) (tyName : TyName) (tyArgs : List Ty) (ρ : Ty)
    (branches : List (MatchPattern × Expr)) :
    Option { r : Nat × Subst // InferBranches Φ ctx tyName tyArgs ρ branches r.1 r.2 } :=
  match branches with
  | [] => some ⟨(Φ, []), .nil⟩
  | (pat, body) :: rest =>
      match hget : LookupList.get? ctx.ctors pat.ctor with
      | none => none
      | some ctorr =>
        if htn : ctorr.tyName = tyName then
          if hpc : ctorr.paramCount = tyArgs.length then
            if hcont : pat.contents = ctorr.contents.length then
              match inferCore Φ
                  { ctx with env := (ctorr.contents.map (Ty.openWith tyArgs)).map PolyTy.mkTrivial ++ ctx.env }
                  body with
              | none => none
              | some ⟨(Φ₁, S₁, τb), hbody⟩ =>
                match unifyCore τb (S₁.onTy ρ) with
                | none => none
                | some ⟨S₂, huni⟩ =>
                  match inferBranchesCore Φ₁ (S₂.onCtx (S₁.onCtx ctx)) tyName
                      (tyArgs.map (fun t => S₂.onTy (S₁.onTy t))) (S₂.onTy (S₁.onTy ρ)) rest with
                  | none => none
                  | some ⟨(Φ₂, S₃), hrest⟩ =>
                    some ⟨(Φ₂, S₁ ++ S₂ ++ S₃), .cons hget htn hpc hcont hbody huni hrest⟩
            else none
          else none
        else none
end

/-- The executable type inferer, refining `Infer`. -/
def infer (Φ : Nat) (ctx : Ctx) (e : Expr) : Option (Nat × Subst × Ty) :=
  (inferCore Φ ctx e).map (·.1)

/-- `infer` soundness: a returned `(Φ', S, τ)` is a genuine `Infer` derivation
    (immediate — `inferCore` carries it). -/
theorem infer_sound {Φ : Nat} {ctx : Ctx} {e : Expr} {Φ' : Nat} {S : Subst} {τ : Ty}
    (h : infer Φ ctx e = some (Φ', S, τ)) : Infer Φ ctx e Φ' S τ := by
  rw [infer] at h
  rcases hc : inferCore Φ ctx e with _ | ⟨r, hr⟩ <;> rw [hc] at h
  · exact absurd h (by simp)
  · simp only [Option.map_some, Option.some.injEq] at h
    subst h
    exact hr

/-! ### Capstone: the executable inferer computes the principal type

Composing `infer_sound` with `Infer.isPrincipal`: whenever `infer` returns a
type, that type is *the principal typing* — every declarative typing of `e`
(under any LC specialization of a well-formed, frontier-bounded `ctx`) is a
substitution instance of it. The executable Algorithm W computes principal
types, machine-verified. -/
theorem infer_isPrincipal {Φ : Nat} {ctx : Ctx} {e : Expr} {Φ' : Nat} {S : Subst} {τ : Ty}
    (h : infer Φ ctx e = some (Φ', S, τ)) (hwf : CtxWF ctx) (hbelow : CtxBelow Φ ctx) :
    Infer.IsPrincipal ctx e S τ :=
  Infer.isPrincipal (infer_sound h) hwf hbelow

/-! ### Sanity checks: the algorithm actually runs

The first time the algorithm is executed (guards against an operationally-wrong
but provable relation). `unify` and `infer` reduce only under the compiler
(`#eval`), since both rest on well-founded recursion. -/

-- `unify (α → α) (Int → β) = [α ↦ Int, β ↦ Int]`
#eval unify (.arrow (.fvar 0) (.fvar 0)) (.arrow (.prim .int) (.fvar 1))
-- `unify Int Bool = none` (constructor clash)
#eval unify (.prim .int) (.prim .bool)
-- `unify α (α → α) = none` (occurs check)
#eval unify (.fvar 0) (.arrow (.fvar 0) (.fvar 0))
-- `infer (λx. x) = α → α`
#eval infer 0 { env := [], ctors := [] } (.lambda (.var 0))
-- `infer (λx. λy. x) = α → β → α`
#eval infer 0 { env := [], ctors := [] } (.lambda (.lambda (.var 1)))
-- `infer ((λx. x) 5) = Int`
#eval infer 0 { env := [], ctors := [] } (.app (.lambda (.var 0)) (.primLit (.int 5)))
-- `infer (5 5) = none` (Int is not a function)
#eval infer 0 { env := [], ctors := [] } (.app (.primLit (.int 5)) (.primLit (.int 5)))


/-! ### `unify` completeness

`unify` succeeds whenever the inputs are unifiable. Like the relational
`UnifyRel.complete`, this needs a strong induction on the unifier-bounded size
measure `2 * (U.onTy a).size (+1)`, because `unify` decomposes through its *own*
computed prefix unifier (not the witness's). The proof mirrors
`UnifyRel.complete_aux` step for step, concluding `.isSome` instead of producing
a derivation. -/
theorem unifyCore_complete_aux : ∀ (N : Nat),
    (∀ {a b : Ty} {U : Subst}, 2 * (U.onTy a).size < N → a.IsLC → b.IsLC →
        Unifies U a b → (unifyCore a b).isSome) ∧
    (∀ {as bs : List Ty} {U : Subst}, 2 * TyList.size (as.map U.onTy) + 1 < N →
        (∀ t ∈ as, t.IsLC) → (∀ t ∈ bs, t.IsLC) → as.length = bs.length →
        as.map U.onTy = bs.map U.onTy → (unifyListCore as bs).isSome) := by
  intro N
  induction N with
  | zero => exact ⟨fun h => absurd h (by omega), fun h => absurd h (by omega)⟩
  | succ N ih =>
    obtain ⟨ihU, ihL⟩ := ih
    refine ⟨?_, ?_⟩
    · intro a b U hsz ha hb hU
      cases a with
      | bvar i => cases ha with | bvar h => omega
      | prim p =>
        cases b with
        | bvar i => cases hb with | bvar h => omega
        | prim q =>
          simp only [Unifies, Subst.onTy_prim, Ty.prim.injEq] at hU
          subst hU; simp [unifyCore]
        | fvar m => simp [unifyCore, Ty.freeVars]
        | pair b₁ b₂ => simp [Unifies] at hU
        | arrow b₁ b₂ => simp [Unifies] at hU
        | customTy nm bs => simp [Unifies] at hU
      | fvar n =>
        cases b with
        | bvar i => cases hb with | bvar h => omega
        | fvar m =>
          by_cases hnm : n = m
          · subst hnm; simp [unifyCore]
          · simp [unifyCore, hnm]
        | prim q =>
          by_cases hocc : n ∈ (Ty.prim q).freeVars
          · have hlt := Ty.size_onTy_fvar_lt (S := U) hocc (by simp)
            simp only [Unifies] at hU; rw [hU] at hlt; omega
          · simp [unifyCore, hocc]
        | pair b₁ b₂ =>
          by_cases hocc : n ∈ (Ty.pair b₁ b₂).freeVars
          · have hlt := Ty.size_onTy_fvar_lt (S := U) hocc (by simp)
            simp only [Unifies] at hU; rw [hU] at hlt; omega
          · simp [unifyCore, hocc]
        | arrow b₁ b₂ =>
          by_cases hocc : n ∈ (Ty.arrow b₁ b₂).freeVars
          · have hlt := Ty.size_onTy_fvar_lt (S := U) hocc (by simp)
            simp only [Unifies] at hU; rw [hU] at hlt; omega
          · simp [unifyCore, hocc]
        | customTy nm bs =>
          by_cases hocc : n ∈ (Ty.customTy nm bs).freeVars
          · have hlt := Ty.size_onTy_fvar_lt (S := U) hocc (by simp)
            simp only [Unifies] at hU; rw [hU] at hlt; omega
          · simp [unifyCore, hocc]
      | pair a₁ a₂ =>
        cases ha with
        | pair ha₁ ha₂ =>
        cases b with
        | bvar i => cases hb with | bvar h => omega
        | fvar m =>
          by_cases hocc : m ∈ (Ty.pair a₁ a₂).freeVars
          · have hlt := Ty.size_onTy_fvar_lt (S := U) hocc (by simp)
            simp only [Unifies] at hU; rw [hU] at hlt; omega
          · simp [unifyCore, hocc]
        | prim q => simp [Unifies] at hU
        | arrow b₁ b₂ => simp [Unifies] at hU
        | customTy nm bs => simp [Unifies] at hU
        | pair b₁ b₂ =>
          cases hb with
          | pair hb₁ hb₂ =>
          have hpsz : (U.onTy (.pair a₁ a₂)).size
              = 1 + (U.onTy a₁).size + (U.onTy a₂).size := by simp [Subst.onTy_pair, Ty.size]
          simp only [Unifies, Subst.onTy_pair, Ty.pair.injEq] at hU
          have hsome1 := ihU (a := a₁) (b := b₁) (U := U) (by rw [hpsz] at hsz; omega) ha₁ hb₁ hU.1
          obtain ⟨⟨S₁', hS₁'⟩, he1⟩ := Option.isSome_iff_exists.mp hsome1
          obtain ⟨R, hR⟩ := UnifyRel.greatest hS₁' U hU.1
          have hS₁'lc := UnifyRel.lc hS₁' ha₁ hb₁
          have hsome2 := ihU (a := S₁'.onTy a₂) (b := S₁'.onTy b₂) (U := R)
            (by rw [← hR a₂]; rw [hpsz] at hsz; omega)
            (Subst.onTy_lc hS₁'lc ha₂) (Subst.onTy_lc hS₁'lc hb₂)
            (by show R.onTy (S₁'.onTy a₂) = R.onTy (S₁'.onTy b₂); rw [← hR a₂, ← hR b₂]; exact hU.2)
          obtain ⟨⟨S₂', hS₂'⟩, he2⟩ := Option.isSome_iff_exists.mp hsome2
          rw [unifyCore]; simp only [he1, he2, Option.isSome_some]
      | arrow a₁ a₂ =>
        cases ha with
        | arrow ha₁ ha₂ =>
        cases b with
        | bvar i => cases hb with | bvar h => omega
        | fvar m =>
          by_cases hocc : m ∈ (Ty.arrow a₁ a₂).freeVars
          · have hlt := Ty.size_onTy_fvar_lt (S := U) hocc (by simp)
            simp only [Unifies] at hU; rw [hU] at hlt; omega
          · simp [unifyCore, hocc]
        | prim q => simp [Unifies] at hU
        | pair b₁ b₂ => simp [Unifies] at hU
        | customTy nm bs => simp [Unifies] at hU
        | arrow b₁ b₂ =>
          cases hb with
          | arrow hb₁ hb₂ =>
          have hpsz : (U.onTy (.arrow a₁ a₂)).size
              = 1 + (U.onTy a₁).size + (U.onTy a₂).size := by simp [Subst.onTy_arrow, Ty.size]
          simp only [Unifies, Subst.onTy_arrow, Ty.arrow.injEq] at hU
          have hsome1 := ihU (a := a₁) (b := b₁) (U := U) (by rw [hpsz] at hsz; omega) ha₁ hb₁ hU.1
          obtain ⟨⟨S₁', hS₁'⟩, he1⟩ := Option.isSome_iff_exists.mp hsome1
          obtain ⟨R, hR⟩ := UnifyRel.greatest hS₁' U hU.1
          have hS₁'lc := UnifyRel.lc hS₁' ha₁ hb₁
          have hsome2 := ihU (a := S₁'.onTy a₂) (b := S₁'.onTy b₂) (U := R)
            (by rw [← hR a₂]; rw [hpsz] at hsz; omega)
            (Subst.onTy_lc hS₁'lc ha₂) (Subst.onTy_lc hS₁'lc hb₂)
            (by show R.onTy (S₁'.onTy a₂) = R.onTy (S₁'.onTy b₂); rw [← hR a₂, ← hR b₂]; exact hU.2)
          obtain ⟨⟨S₂', hS₂'⟩, he2⟩ := Option.isSome_iff_exists.mp hsome2
          rw [unifyCore]; simp only [he1, he2, Option.isSome_some]
      | customTy nm tys₁ =>
        cases b with
        | bvar i => cases hb with | bvar h => omega
        | fvar m =>
          by_cases hocc : m ∈ (Ty.customTy nm tys₁).freeVars
          · have hlt := Ty.size_onTy_fvar_lt (S := U) hocc (by simp)
            simp only [Unifies] at hU; rw [hU] at hlt; omega
          · simp [unifyCore, hocc]
        | prim q => simp [Unifies] at hU
        | pair b₁ b₂ => simp [Unifies] at hU
        | arrow b₁ b₂ => simp [Unifies] at hU
        | customTy nm' tys₂ =>
          have hcsz : (U.onTy (.customTy nm tys₁)).size
              = 1 + TyList.size (tys₁.map U.onTy) := by simp [Subst.onTy_customTy, Ty.size]
          simp only [Unifies, Subst.onTy_customTy, Ty.customTy.injEq] at hU
          obtain ⟨rfl, hmapeq⟩ := hU
          have hlen : tys₁.length = tys₂.length := by
            have := congrArg List.length hmapeq; simpa using this
          have hsomeL := ihL (as := tys₁) (bs := tys₂) (U := U)
            (by rw [hcsz] at hsz; omega)
            (fun t ht => by cases ha with | customTy h => exact h t ht)
            (fun t ht => by cases hb with | customTy h => exact h t ht)
            hlen hmapeq
          obtain ⟨⟨S, hS⟩, heL⟩ := Option.isSome_iff_exists.mp hsomeL
          rw [unifyCore]; simp [heL]
    · intro as bs U hsz has hbs hlen hmap
      cases as with
      | nil =>
        cases bs with
        | nil => simp [unifyListCore]
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
          have hsome1 := ihU (a := t₁) (b := t₂) (U := U)
            (by rw [htsz] at hsz; omega) (has t₁ List.mem_cons_self)
            (hbs t₂ List.mem_cons_self) hmap.1
          obtain ⟨⟨S₁', hS₁'⟩, he1⟩ := Option.isSome_iff_exists.mp hsome1
          obtain ⟨R, hR⟩ := UnifyRel.greatest hS₁' U hmap.1
          have hS₁'lc := UnifyRel.lc hS₁' (has t₁ List.mem_cons_self) (hbs t₂ List.mem_cons_self)
          have key : ∀ l : List Ty, l.map (R.onTy ∘ S₁'.onTy) = l.map U.onTy := by
            intro l; apply List.map_congr_left; intro t _; exact (hR t).symm
          have hkey1 : (ts₁.map S₁'.onTy).map R.onTy = ts₁.map U.onTy := by
            rw [List.map_map]; exact key ts₁
          have hmaptail : (ts₁.map S₁'.onTy).map R.onTy = (ts₂.map S₁'.onTy).map R.onTy := by
            rw [List.map_map, List.map_map, key, key]; exact hmap.2
          have hsome2 := ihL (as := ts₁.map S₁'.onTy) (bs := ts₂.map S₁'.onTy) (U := R)
            (by rw [hkey1]; rw [htsz] at hsz; omega)
            (by
              intro t ht; obtain ⟨t0, ht0, rfl⟩ := List.mem_map.mp ht
              exact Subst.onTy_lc hS₁'lc (has t0 (List.mem_cons_of_mem _ ht0)))
            (by
              intro t ht; obtain ⟨t0, ht0, rfl⟩ := List.mem_map.mp ht
              exact Subst.onTy_lc hS₁'lc (hbs t0 (List.mem_cons_of_mem _ ht0)))
            (by simp only [List.length_map]; have := hlen; simpa using this)
            hmaptail
          obtain ⟨⟨S₂', hS₂'⟩, he2⟩ := Option.isSome_iff_exists.mp hsome2
          rw [unifyListCore]; simp only [he1, he2, Option.isSome_some]

/-- `unify` completeness: `unify` succeeds whenever the (LC) inputs are unifiable. -/
theorem unify_complete {a b : Ty} {S : Subst} (h : UnifyRel a b S)
    (ha : a.IsLC) (hb : b.IsLC) : (unify a b).isSome := by
  have hcore : (unifyCore a b).isSome :=
    (unifyCore_complete_aux (2 * (S.onTy a).size + 1)).1 (by omega) ha hb h.unifies
  simpa [unify, Option.isSome_map] using hcore


/-! ### `infer` completeness

`infer` succeeds whenever `e` is declaratively typeable. Like `unify_complete`,
the obstacle is that `inferCore` decomposes through its *own* computed
substitutions/fresh-vars, so this is Algorithm-W completeness *for the function*:
each recursive case transfers the typing to the function's intermediate state
(reusing `Infer.complete'` / `InferBranches.complete'`), and `app`/`fst`/`snd`/
`match_` additionally rebuild the explicit unifier (mirroring the `complete_*_aux`
dodges) to discharge `unifyCore` via `unifyCore_complete_aux`. -/

/-- The function-completeness property at `e`: given a (well-formed,
    frontier-bounded) `Infer` derivation, `inferCore` succeeds. We induct over a
    *given* derivation (not declarative typeability) so the binder cases compose
    without an α-renaming dodge: `Infer`'s sub-derivations already live in the
    exact intermediate states `inferCore` recurses into for `lambda`/`var`/`ctor`,
    while the compositional cases re-derive the second sub-problem under the
    function's own prefix via `complete'` + `Infer.complete`. -/
def InferCoreComplete (e : Expr) : Prop :=
  ∀ {Φ : Nat} {ctx : Ctx} {Φ' : Nat} {S : Subst} {τ : Ty},
    CtxWF ctx → CtxBelow Φ ctx → Infer Φ ctx e Φ' S τ → (inferCore Φ ctx e).isSome

theorem inferCore_complete_prim {p : PrimLitExpr} : InferCoreComplete (.primLit p) := by
  intro Φ ctx Φ' S τ _ _ h
  cases h <;> simp [inferCore]

theorem inferCore_complete_var {i : Nat} : InferCoreComplete (.var i) := by
  intro Φ ctx Φ' S τ _ _ h
  cases h with
  | var hlook =>
    rw [inferCore]
    split
    · rename_i heq; rw [heq] at hlook; simp at hlook
    · rfl

theorem inferCore_complete_ctor {name : CtorName} : InferCoreComplete (.ctor name) := by
  intro Φ ctx Φ' S τ _ _ h
  cases h with
  | ctor hlook =>
    rw [inferCore]
    split
    · rename_i heq; rw [heq] at hlook; simp at hlook
    · rfl

/-- A trivial scheme `mkTrivial (.fvar Φ)` extends a WF context to a WF context. -/
theorem CtxWF.cons_fvar {Φ : Nat} {ctx : Ctx} (hwf : CtxWF ctx) :
    CtxWF { ctx with env := PolyTy.mkTrivial (.fvar Φ) :: ctx.env } := by
  intro M hM
  rcases List.mem_cons.mp hM with rfl | hM
  · exact ContainsBvarsUpTo.fvar
  · exact hwf M hM

theorem CtxBelow.cons_fvar {Φ : Nat} {ctx : Ctx} (hbelow : CtxBelow Φ ctx) :
    CtxBelow (Φ + 1) { ctx with env := PolyTy.mkTrivial (.fvar Φ) :: ctx.env } := by
  intro M hM
  rcases List.mem_cons.mp hM with rfl | hM
  · exact .fvar (by omega)
  · exact (hbelow M hM).mono (by omega)

theorem inferCore_complete_lambda {body : Expr} (ih : InferCoreComplete body) :
    InferCoreComplete (.lambda body) := by
  intro Φ ctx Φ' S τ hwf hbelow h
  cases h with
  | lambda hbody =>
    have hsome := ih hwf.cons_fvar hbelow.cons_fvar hbody
    obtain ⟨⟨⟨Φ'', S'', τb'⟩, hbody'⟩, he⟩ := Option.isSome_iff_exists.mp hsome
    rw [inferCore]; simp only [he, Option.isSome_some]

theorem inferCore_complete_pair {a b : Expr}
    (iha : InferCoreComplete a) (ihb : InferCoreComplete b) :
    InferCoreComplete (.pair a b) := by
  intro Φ ctx Φ' S τ hwf hbelow h
  cases h with
  | @pair _ _ _ _ Φ₁ Φ₂ S₁ S₂ τa τb ha hb =>
    -- recurse on `a`, get the function's first output `(Φ₁', S₁', τa')`
    have hsa := iha hwf hbelow ha
    obtain ⟨⟨⟨Φ₁', S₁', τa'⟩, ha'⟩, hea⟩ := Option.isSome_iff_exists.mp hsa
    -- factor the derivation's `S₁` through the function's principal `ha'`
    have hS₁ := (Infer.lc ha hwf).2
    obtain ⟨R₁, hag1, _, hR₁⟩ := Infer.complete' ha' hwf hbelow hS₁ (Infer.sound ha hwf)
    have hS₁' := (Infer.lc ha' hwf).2
    have hbf := Infer.belowFvars ha' hbelow
    have hle1 := Infer.frontier_le ha'
    have hwf₁ := Subst.onCtx_wf hS₁' hwf
    have hbelow₁ := Subst.onCtx_below hbf.2 hle1 hbelow
    have hctxeq : R₁.onCtx (S₁'.onCtx ctx) = S₁.onCtx ctx := by
      rw [← Subst.onCtx_append]; exact Subst.onCtx_congr (fun v hv => (hag1 v hv).symm) hbelow
    -- transfer `b`'s typing to the function's intermediate context, re-derive via `Infer.complete`
    have hwfS₁ := Subst.onCtx_wf hS₁ hwf
    have htyb' : TypeOfHM ((R₁ ++ S₂).onCtx (S₁'.onCtx ctx)) b τb := by
      rw [Subst.onCtx_append, hctxeq]; exact Infer.sound hb hwfS₁
    have hR₁S₂lc : ∀ p ∈ R₁ ++ S₂, p.2.IsLC := by
      intro p hp; rcases List.mem_append.mp hp with hp | hp
      · exact hR₁ p hp
      · exact (Infer.lc hb hwfS₁).2 p hp
    obtain ⟨_, _, _, _, hinfb, _, _, _⟩ := Infer.complete hwf₁ hbelow₁ hR₁S₂lc htyb'
    have hsb := ihb hwf₁ hbelow₁ hinfb
    obtain ⟨⟨⟨Φ₂', S₂', τb'⟩, hb'⟩, heb⟩ := Option.isSome_iff_exists.mp hsb
    rw [inferCore]; simp only [hea, heb, Option.isSome_some]

/-- The explicit unifier behind `app`'s `unify` step (factored from
    `Infer.complete_app_aux`): with `R₂` factoring the residual and a fresh `W`,
    `[(Φ₂, fvar W)] ++ R₂ ++ [(W, τ₀)]` unifies `A` with `arrow τa (fvar Φ₂)`. -/
theorem exists_app_unifier {A τa τ₀ argTy : Ty} {Φ₂ : Nat} {R₂ : Subst}
    (hP : R₂.onTy A = Ty.arrow argTy τ₀) (htya : argTy = R₂.onTy τa)
    (hΦ₂A : Φ₂ ∉ A.freeVars) (hΦ₂τa : Φ₂ ∉ τa.freeVars)
    (hR₂ : ∀ p ∈ R₂, p.2.IsLC) (hτ₀LC : τ₀.IsLC) :
    ∃ U, Unifies U A (Ty.arrow τa (Ty.fvar Φ₂)) ∧ (∀ p ∈ U, p.2.IsLC) := by
  obtain ⟨W, hWge, hWfresh⟩ := exists_fresh_block
    (R₂.map Prod.fst ++ R₂.flatMap (fun p => p.2.freeVars) ++ argTy.freeVars ++ τ₀.freeVars) Φ₂ 1
  have hWdom : ∀ p ∈ R₂, p.1 ≠ W := by
    intro p hp he
    have := hWfresh p.1 (List.mem_append_left _ (List.mem_append_left _
      (List.mem_append_left _ (List.mem_map.mpr ⟨p, hp, rfl⟩))))
    omega
  have hWrange : ∀ p ∈ R₂, W ∉ p.2.freeVars := by
    intro p hp hc
    have := hWfresh W (List.mem_append_left _ (List.mem_append_left _
      (List.mem_append_right _ (List.mem_flatMap.mpr ⟨p, hp, hc⟩))))
    omega
  have hWargTy : W ∉ argTy.freeVars := fun hc => by
    have := hWfresh W (List.mem_append_left _ (List.mem_append_right _ hc)); omega
  have hWτ₀ : W ∉ τ₀.freeVars := fun hc => by
    have := hWfresh W (List.mem_append_right _ hc); omega
  have hR₂Wfvar : R₂.onTy (Ty.fvar W) = Ty.fvar W := by
    apply Ty.substFvars_eq_self_of_no_key
    intro p hp hc
    simp only [Ty.freeVars, List.mem_singleton] at hc
    exact hWdom p hp hc
  obtain ⟨U, hUdef⟩ : ∃ U : Subst, U = [(Φ₂, Ty.fvar W)] ++ R₂ ++ [(W, τ₀)] := ⟨_, rfl⟩
  have hsingle : ∀ (Z : Nat) (V y : Ty), Subst.onTy [(Z, V)] y = Ty.substFvar Z V y :=
    fun _ _ _ => rfl
  have hsubArrow : ∀ (Z : Nat) (V a b : Ty),
      Ty.substFvar Z V (Ty.arrow a b) = Ty.arrow (Ty.substFvar Z V a) (Ty.substFvar Z V b) :=
    fun _ _ _ _ => rfl
  have hUonTy : ∀ x, U.onTy x = Ty.substFvar W τ₀ (R₂.onTy (Ty.substFvar Φ₂ (Ty.fvar W) x)) := by
    intro x
    rw [hUdef, Subst.onTy_append, Subst.onTy_append, hsingle, hsingle]
  have e1 : Ty.substFvar Φ₂ (Ty.fvar W) (Ty.fvar Φ₂) = Ty.fvar W := by simp [Ty.substFvar]
  have e2 : Ty.substFvar W τ₀ (Ty.fvar W) = τ₀ := by simp [Ty.substFvar]
  have hUniL : U.onTy A = Ty.arrow argTy τ₀ := by
    rw [hUonTy, Ty.substFvar_fresh hΦ₂A, hP, hsubArrow,
        Ty.substFvar_fresh hWargTy, Ty.substFvar_fresh hWτ₀]
  have hUniR : U.onTy (Ty.arrow τa (Ty.fvar Φ₂)) = Ty.arrow argTy τ₀ := by
    rw [hUonTy, hsubArrow, Ty.substFvar_fresh hΦ₂τa, e1, Subst.onTy_arrow,
        hR₂Wfvar, ← htya, hsubArrow, Ty.substFvar_fresh hWargTy, e2]
  refine ⟨U, by show U.onTy A = U.onTy (Ty.arrow τa (Ty.fvar Φ₂)); rw [hUniL, hUniR], ?_⟩
  rw [hUdef]
  intro p hp
  rcases List.mem_append.mp hp with hp' | hp'
  · rcases List.mem_append.mp hp' with hp'' | hp''
    · obtain rfl := List.mem_singleton.mp hp''
      exact ContainsBvarsUpTo.fvar
    · exact hR₂ p hp''
  · obtain rfl := List.mem_singleton.mp hp'
    exact hτ₀LC

theorem inferCore_complete_app {f arg : Expr}
    (ihf : InferCoreComplete f) (iharg : InferCoreComplete arg) :
    InferCoreComplete (.app f arg) := by
  intro Φ ctx Φ' S τ hwf hbelow h
  -- declarative typing of the whole app (its arrow structure comes from `huni`)
  have happ := Infer.sound h hwf
  cases h with
  | @app _ _ _ _ Φ₁ Φ₂ S₁ S₂ S₃ τf τa hf harg huni =>
    -- invert the declarative app typing to expose `argTy` and the result `τ₀`
    obtain ⟨argTy, hfty, hargty⟩ : ∃ argTy,
        TypeOfHM ((S₁ ++ S₂ ++ S₃).onCtx ctx) f (.arrow argTy (S₃.onTy (.fvar Φ₂))) ∧
        TypeOfHM ((S₁ ++ S₂ ++ S₃).onCtx ctx) arg argTy := by
      cases happ with | app hfty hargty => exact ⟨_, hfty, hargty⟩
    have hSlc : ∀ p ∈ S₁ ++ S₂ ++ S₃, p.2.IsLC := (Infer.lc (Infer.app hf harg huni) hwf).2
    -- recurse on `f`, factor the f-typing through the function's principal output
    have hsf := ihf hwf hbelow hf
    obtain ⟨⟨⟨Φ₁', S₁', τf'⟩, hf'⟩, hef⟩ := Option.isSome_iff_exists.mp hsf
    obtain ⟨R_f, hagf, hStepf, hR_f⟩ := Infer.complete' hf' hwf hbelow hSlc hfty
    have hS₁' := (Infer.lc hf' hwf).2
    have hbf := Infer.belowFvars hf' hbelow
    have hle1 := Infer.frontier_le hf'
    have hwf₁ := Subst.onCtx_wf hS₁' hwf
    have hbelow₁ := Subst.onCtx_below hbf.2 hle1 hbelow
    have hctxeq : R_f.onCtx (S₁'.onCtx ctx) = (S₁ ++ S₂ ++ S₃).onCtx ctx := by
      rw [← Subst.onCtx_append]; exact Subst.onCtx_congr (fun v hv => (hagf v hv).symm) hbelow
    -- transfer arg's typing, re-derive under the function's intermediate state
    have hargty' : TypeOfHM (R_f.onCtx (S₁'.onCtx ctx)) arg argTy := by rw [hctxeq]; exact hargty
    obtain ⟨_, _, _, _, hinfa, _, _, _⟩ := Infer.complete hwf₁ hbelow₁ hR_f hargty'
    have hsa := iharg hwf₁ hbelow₁ hinfa
    obtain ⟨⟨⟨Φ₂', S₂', τa'⟩, harg'⟩, hea⟩ := Option.isSome_iff_exists.mp hsa
    obtain ⟨R_a, haga, hStepa, hR_a⟩ := Infer.complete' harg' hwf₁ hbelow₁ hR_f hargty'
    -- build the app unifier on the function's `(S₂'.onTy τf')`, `arrow τa' (fvar Φ₂')`
    have hba := Infer.belowFvars harg' hbelow₁
    have hle2 := Infer.frontier_le harg'
    have hcongr_f : R_f.onTy τf' = (S₂' ++ R_a).onTy τf' := Subst.onTy_congr haga hbf.1
    have hP : R_a.onTy (S₂'.onTy τf') = Ty.arrow argTy (S₃.onTy (.fvar Φ₂)) := by
      rw [← Subst.onTy_append, ← hcongr_f]; exact hStepf.symm
    have hΦ₂τf : Φ₂' ∉ (S₂'.onTy τf').freeVars := fun hm => by
      have := (Subst.onTy_belowFvars hba.2 (hbf.1.mono hle2)).mem_lt _ hm; omega
    have hΦ₂τa : Φ₂' ∉ τa'.freeVars := fun hm => by have := hba.1.mem_lt _ hm; omega
    have hτ₀LC : (S₃.onTy (.fvar Φ₂)).IsLC := by
      have hreg := TypeOfHM.regular hfty; cases hreg with | arrow _ hT => exact hT
    obtain ⟨U, hUni, _⟩ := exists_app_unifier hP hStepa hΦ₂τf hΦ₂τa hR_a hτ₀LC
    have hτfLC := (Infer.lc hf' hwf).1
    have hτaLC := (Infer.lc harg' hwf₁).1
    have hS₂' := (Infer.lc harg' hwf₁).2
    have huniSome : (unifyCore (S₂'.onTy τf') (Ty.arrow τa' (Ty.fvar Φ₂'))).isSome :=
      (unifyCore_complete_aux (2 * (U.onTy (S₂'.onTy τf')).size + 1)).1 (by omega)
        (Subst.onTy_lc hS₂' hτfLC) (.arrow hτaLC ContainsBvarsUpTo.fvar) hUni
    obtain ⟨⟨S₃', _⟩, he3⟩ := Option.isSome_iff_exists.mp huniSome
    rw [inferCore]; simp only [hef, hea, he3, Option.isSome_some]

theorem inferCore_complete_letIn {rhs body : Expr}
    (iha : InferCoreComplete rhs) (ihb : InferCoreComplete body) :
    InferCoreComplete (.letIn rhs body) := by
  intro Φ ctx Φ' S τ hwf hbelow h
  have happ := Infer.sound h hwf
  have hSlc : ∀ p ∈ S, p.2.IsLC := (Infer.lc h hwf).2
  cases h with
  | @letIn _ _ _ _ Φ1d Φ2d S1d S2d τ1d τ2 hrhs hbody =>
    cases happ with
    | letIn hMwf hcofin heqctx hbodyD =>
      expose_names
      subst heqctx
      -- fresh opening avoiding `L`, `M.body`, and the (substituted) env
      obtain ⟨Xs, hXlen, hXnodup, hXavoid⟩ :=
        exists_fresh_names (L ++ M.body.freeVars ++ ((S1d ++ S2d).onCtx ctx).env.freeVars) M.paramCount
      have hXfreshL : FreshNames L M.paramCount Xs :=
        ⟨hXlen, hXnodup,
          fun x hx hc => hXavoid x hx (List.mem_append_left _ (List.mem_append_left _ hc))⟩
      have hXMbody : ∀ x ∈ Xs, x ∉ M.body.freeVars :=
        fun x hx hc => hXavoid x hx (List.mem_append_left _ (List.mem_append_right _ hc))
      have hXenv : ∀ x ∈ Xs, x ∉ ((S1d ++ S2d).onCtx ctx).env.freeVars :=
        fun x hx hc => hXavoid x hx (List.mem_append_right _ hc)
      -- recurse on rhs; factor the rhs-opening typing through the function's output
      have hsa := iha hwf hbelow hrhs
      obtain ⟨⟨⟨Φ₁', S₁', τ₁'⟩, hrhs'⟩, herhs⟩ := Option.isSome_iff_exists.mp hsa
      obtain ⟨R₁, haga, htya, hR₁⟩ := Infer.complete' hrhs' hwf hbelow hSlc (hcofin Xs hXfreshL)
      have hS₁ : ∀ p ∈ S₁', p.2.IsLC := (Infer.lc hrhs' hwf).2
      have hτ₁lc : τ₁'.IsLC := (Infer.lc hrhs' hwf).1
      have hle : Φ ≤ Φ₁' := Infer.frontier_le hrhs'
      have hbelowτ₁ : Ty.BelowFvars Φ₁' τ₁' := (Infer.belowFvars hrhs' hbelow).1
      have hbelowS₁ : ∀ p ∈ S₁', Ty.BelowFvars Φ₁' p.2 := (Infer.belowFvars hrhs' hbelow).2
      have hwf₁ : CtxWF (S₁'.onCtx ctx) := Subst.onCtx_wf hS₁ hwf
      have hbelow₁ : CtxBelow Φ₁' (S₁'.onCtx ctx) := Subst.onCtx_below hbelowS₁ hle hbelow
      have hctxeq : R₁.onCtx (S₁'.onCtx ctx) = (S1d ++ S2d).onCtx ctx := by
        rw [← Subst.onCtx_append]
        exact Subst.onCtx_congr (fun v hv => (haga v hv).symm) hbelow
      have hwfBody : CtxWF { (S₁'.onCtx ctx) with
          env := genScheme (S₁'.onCtx ctx).env τ₁' :: (S₁'.onCtx ctx).env } := by
        intro N hN
        rcases List.mem_cons.mp hN with rfl | hN
        · exact genScheme_wf hτ₁lc
        · exact hwf₁ N hN
      have hbelowBody : CtxBelow Φ₁' { (S₁'.onCtx ctx) with
          env := genScheme (S₁'.onCtx ctx).env τ₁' :: (S₁'.onCtx ctx).env } := by
        intro N hN
        rcases List.mem_cons.mp hN with rfl | hN
        · show Ty.BelowFvars Φ₁' (Ty.closeOver (genVars (S₁'.onCtx ctx).env τ₁') τ₁')
          exact hbelowτ₁.closeOver
        · exact hbelow₁ N hN
      have hXM'' : ∀ x ∈ Xs,
          x ∉ (R₁.onPolyTy (genScheme (S₁'.onCtx ctx).env τ₁')).body.freeVars := by
        intro x hx hmem
        change x ∈ (R₁.onTy (Ty.closeOver (genVars (S₁'.onCtx ctx).env τ₁') τ₁')).freeVars at hmem
        obtain ⟨v, hv, hxv⟩ := Ty.mem_freeVars_onTy_iff.mp hmem
        have hvτ₁ : v ∈ τ₁'.freeVars := Ty.closeOver_freeVars_subset hv
        have hvg : v ∉ genVars (S₁'.onCtx ctx).env τ₁' := fun hg => Ty.not_mem_closeOver_freeVars hg hv
        have hvenv : v ∈ (S₁'.onCtx ctx).env.freeVars := by
          by_contra hc
          exact hvg (by
            simp only [genVars, List.mem_filter]
            exact ⟨hvτ₁, by simpa using hc⟩)
        obtain ⟨pt, hpt, hvpt⟩ := Env.mem_freeVars_iff.mp hvenv
        have hx_onTy : x ∈ (R₁.onTy pt.body).freeVars :=
          Ty.mem_freeVars_onTy_iff.mpr ⟨v, hvpt, hxv⟩
        have hpt_mem : R₁.onPolyTy pt ∈ ((S1d ++ S2d).onCtx ctx).env := by
          have hmem2 : R₁.onPolyTy pt ∈ (R₁.onCtx (S₁'.onCtx ctx)).env := by
            simp only [Subst.onCtx, Subst.onEnv]
            exact List.mem_map.mpr ⟨pt, hpt, rfl⟩
          rw [hctxeq] at hmem2; exact hmem2
        exact hXenv x hx (Env.mem_freeVars_iff.mpr ⟨R₁.onPolyTy pt, hpt_mem, hx_onTy⟩)
      have hgen : (R₁.onPolyTy (genScheme (S₁'.onCtx ctx).env τ₁')).Generalizes M :=
        genScheme_generalizes hτ₁lc hR₁ hMwf hXnodup hXlen hXMbody htya hXM''
      have hbody' : TypeOfHM
          ⟨R₁.onPolyTy (genScheme (S₁'.onCtx ctx).env τ₁') :: ((S1d ++ S2d).onCtx ctx).env,
            ((S1d ++ S2d).onCtx ctx).ctors⟩ body τ :=
        TypeOfHM.weaken_scheme (env_post := []) (env := ((S1d ++ S2d).onCtx ctx).env) (M := M) hgen hbodyD
      have hbody'' : TypeOfHM (R₁.onCtx { (S₁'.onCtx ctx) with
          env := genScheme (S₁'.onCtx ctx).env τ₁' :: (S₁'.onCtx ctx).env }) body τ := by
        show TypeOfHM ⟨R₁.onPolyTy (genScheme (S₁'.onCtx ctx).env τ₁') :: R₁.onEnv (S₁'.onCtx ctx).env,
            (S₁'.onCtx ctx).ctors⟩ body τ
        rw [show R₁.onEnv (S₁'.onCtx ctx).env = ((S1d ++ S2d).onCtx ctx).env from congrArg Ctx.env hctxeq]
        exact hbody'
      obtain ⟨_, _, _, _, hinfb, _, _, _⟩ := Infer.complete hwfBody hbelowBody hR₁ hbody''
      have hsb := ihb hwfBody hbelowBody hinfb
      obtain ⟨⟨⟨Φ₂', S₂', τ₂'⟩, hbody'⟩, hebody⟩ := Option.isSome_iff_exists.mp hsb
      rw [inferCore]; simp only [herhs, hebody, Option.isSome_some]

/-- The explicit unifier behind the `fst`/`snd` `unify` step: a *doubled*
    `exists_app_unifier` (two fresh names `W`, `W+1`). Given a residual `R₁`
    sending `τe` to `pair τα τβ`, `U` unifies `τe` with the pair of fresh vars. -/
theorem exists_pair_unifier {τe τα τβ : Ty} {Φ₁ : Nat} {R₁ : Subst}
    (htye : R₁.onTy τe = Ty.pair τα τβ)
    (hΦ₁τe : Φ₁ ∉ τe.freeVars) (hΦ₁1τe : Φ₁ + 1 ∉ τe.freeVars)
    (hR₁ : ∀ p ∈ R₁, p.2.IsLC) (hαLC : τα.IsLC) (hβLC : τβ.IsLC) :
    ∃ U, Unifies U τe (Ty.pair (Ty.fvar Φ₁) (Ty.fvar (Φ₁ + 1))) ∧ (∀ p ∈ U, p.2.IsLC) := by
  obtain ⟨W, hWge, hWfresh⟩ := exists_fresh_block
    (R₁.map Prod.fst ++ R₁.flatMap (fun p => p.2.freeVars)
      ++ τα.freeVars ++ τβ.freeVars) Φ₁ 2
  have hWdom : ∀ p ∈ R₁, p.1 ≠ W := by
    intro p hp _heq
    have := hWfresh p.1 (List.mem_append_left _ (List.mem_append_left _
      (List.mem_append_left _ (List.mem_map.mpr ⟨p, hp, rfl⟩))))
    omega
  have hW1dom : ∀ p ∈ R₁, p.1 ≠ W + 1 := by
    intro p hp _heq
    have := hWfresh p.1 (List.mem_append_left _ (List.mem_append_left _
      (List.mem_append_left _ (List.mem_map.mpr ⟨p, hp, rfl⟩))))
    omega
  have hWrng : ∀ p ∈ R₁, W ∉ p.2.freeVars := by
    intro p hp hc
    have := hWfresh W (List.mem_append_left _ (List.mem_append_left _
      (List.mem_append_right _ (List.mem_flatMap.mpr ⟨p, hp, hc⟩))))
    omega
  have hW1rng : ∀ p ∈ R₁, W + 1 ∉ p.2.freeVars := by
    intro p hp hc
    have := hWfresh (W + 1) (List.mem_append_left _ (List.mem_append_left _
      (List.mem_append_right _ (List.mem_flatMap.mpr ⟨p, hp, hc⟩))))
    omega
  have hWP : W ∉ τα.freeVars := fun hc => by
    have := hWfresh W (List.mem_append_left _ (List.mem_append_right _ hc)); omega
  have hW1P : W + 1 ∉ τα.freeVars := fun hc => by
    have := hWfresh (W + 1) (List.mem_append_left _ (List.mem_append_right _ hc)); omega
  have hWQ : W ∉ τβ.freeVars := fun hc => by
    have := hWfresh W (List.mem_append_right _ hc); omega
  have hW1Q : W + 1 ∉ τβ.freeVars := fun hc => by
    have := hWfresh (W + 1) (List.mem_append_right _ hc); omega
  obtain ⟨U, hUdef⟩ : ∃ U : Subst,
    U = [(Φ₁, Ty.fvar W), (Φ₁ + 1, Ty.fvar (W + 1))] ++ R₁
        ++ [(W, τα), (W + 1, τβ)] := ⟨_, rfl⟩
  have hUonTy : ∀ x, U.onTy x =
      Subst.onTy [(W, τα), (W + 1, τβ)]
        (R₁.onTy (Subst.onTy [(Φ₁, Ty.fvar W), (Φ₁ + 1, Ty.fvar (W + 1))] x)) := by
    intro x
    rw [hUdef, Subst.onTy_append, Subst.onTy_append]
  have hR₁W : R₁.onTy (Ty.fvar W) = Ty.fvar W := by
    apply Ty.substFvars_eq_self_of_no_key
    intro p hp hc
    simp only [Ty.freeVars, List.mem_singleton] at hc
    exact hWdom p hp hc
  have hR₁W1 : R₁.onTy (Ty.fvar (W + 1)) = Ty.fvar (W + 1) := by
    apply Ty.substFvars_eq_self_of_no_key
    intro p hp hc
    simp only [Ty.freeVars, List.mem_singleton] at hc
    exact hW1dom p hp hc
  have hprefix_Φ₁ :
      Subst.onTy [(Φ₁, Ty.fvar W), (Φ₁ + 1, Ty.fvar (W + 1))] (Ty.fvar Φ₁) = Ty.fvar W := by
    show Ty.substFvar (Φ₁ + 1) (Ty.fvar (W + 1)) (Ty.substFvar Φ₁ (Ty.fvar W) (Ty.fvar Φ₁))
        = Ty.fvar W
    rw [show Ty.substFvar Φ₁ (Ty.fvar W) (Ty.fvar Φ₁) = Ty.fvar W from by simp [Ty.substFvar]]
    exact Ty.substFvar_fresh (by simp only [Ty.freeVars, List.mem_singleton]; omega)
  have hprefix_Φ₂ :
      Subst.onTy [(Φ₁, Ty.fvar W), (Φ₁ + 1, Ty.fvar (W + 1))] (Ty.fvar (Φ₁ + 1)) = Ty.fvar (W + 1) := by
    show Ty.substFvar (Φ₁ + 1) (Ty.fvar (W + 1)) (Ty.substFvar Φ₁ (Ty.fvar W) (Ty.fvar (Φ₁ + 1)))
        = Ty.fvar (W + 1)
    rw [show Ty.substFvar Φ₁ (Ty.fvar W) (Ty.fvar (Φ₁ + 1)) = Ty.fvar (Φ₁ + 1) from
      Ty.substFvar_fresh (by simp only [Ty.freeVars, List.mem_singleton]; omega)]
    simp [Ty.substFvar]
  have hsufW :
      Subst.onTy [(W, τα), (W + 1, τβ)] (Ty.fvar W) = τα := by
    show Ty.substFvar (W + 1) τβ (Ty.substFvar W τα (Ty.fvar W)) = τα
    rw [show Ty.substFvar W τα (Ty.fvar W) = τα from by simp [Ty.substFvar]]
    exact Ty.substFvar_fresh hW1P
  have hsufW1 :
      Subst.onTy [(W, τα), (W + 1, τβ)] (Ty.fvar (W + 1)) = τβ := by
    show Ty.substFvar (W + 1) τβ (Ty.substFvar W τα (Ty.fvar (W + 1))) = τβ
    rw [show Ty.substFvar W τα (Ty.fvar (W + 1)) = Ty.fvar (W + 1) from
      Ty.substFvar_fresh (by simp only [Ty.freeVars, List.mem_singleton]; omega)]
    simp [Ty.substFvar]
  have hUφ₁ : U.onTy (Ty.fvar Φ₁) = τα := by
    rw [hUonTy, hprefix_Φ₁, hR₁W, hsufW]
  have hUφ₂ : U.onTy (Ty.fvar (Φ₁ + 1)) = τβ := by
    rw [hUonTy, hprefix_Φ₂, hR₁W1, hsufW1]
  have hUτe : U.onTy τe = Ty.pair τα τβ := by
    rw [hUonTy]
    rw [show Subst.onTy [(Φ₁, Ty.fvar W), (Φ₁ + 1, Ty.fvar (W + 1))] τe = τe from
      Ty.substFvars_eq_self_of_no_key (by
        intro p hp
        rcases List.mem_cons.mp hp with rfl | hp'
        · exact hΦ₁τe
        · obtain rfl := List.mem_singleton.mp hp'
          exact hΦ₁1τe)]
    rw [htye]
    apply Ty.substFvars_eq_self_of_no_key
    intro p hp
    rcases List.mem_cons.mp hp with rfl | hp'
    · simp only [Ty.freeVars, List.mem_dedup, List.mem_append, not_or]
      exact ⟨hWP, hWQ⟩
    · obtain rfl := List.mem_singleton.mp hp'
      simp only [Ty.freeVars, List.mem_dedup, List.mem_append, not_or]
      exact ⟨hW1P, hW1Q⟩
  refine ⟨U, ?_, ?_⟩
  · show U.onTy τe = U.onTy (Ty.pair (Ty.fvar Φ₁) (Ty.fvar (Φ₁ + 1)))
    rw [hUτe, Subst.onTy_pair, hUφ₁, hUφ₂]
  · rw [hUdef]
    intro p hp
    rcases List.mem_append.mp hp with hp' | hp'
    · rcases List.mem_append.mp hp' with hp'' | hp''
      · rcases List.mem_cons.mp hp'' with rfl | hp'''
        · exact ContainsBvarsUpTo.fvar
        · obtain rfl := List.mem_singleton.mp hp'''
          exact ContainsBvarsUpTo.fvar
      · exact hR₁ p hp''
    · rcases List.mem_cons.mp hp' with rfl | hp''
      · exact hαLC
      · obtain rfl := List.mem_singleton.mp hp''
        exact hβLC

/-- Executable completeness, `fst` case. -/
theorem inferCore_complete_fst {e : Expr} (ihe : InferCoreComplete e) :
    InferCoreComplete (.fst e) := by
  intro Φ ctx Φ' S τ hwf hbelow h
  have happ := Infer.sound h hwf
  have hSlc : ∀ p ∈ S, p.2.IsLC := (Infer.lc h hwf).2
  cases h with
  | @fst _ _ _ Φ1d S1d S2d τed hpe huniD =>
    obtain ⟨τβ, hfty⟩ : ∃ τβ,
        TypeOfHM ((S1d ++ S2d).onCtx ctx) e (.pair (S2d.onTy (.fvar Φ1d)) τβ) := by
      cases happ with | fst hh => exact ⟨_, hh⟩
    have hαLC : (S2d.onTy (.fvar Φ1d)).IsLC := by
      have := TypeOfHM.regular hfty; cases this with | pair h _ => exact h
    have hβLC : τβ.IsLC := by
      have := TypeOfHM.regular hfty; cases this with | pair _ h => exact h
    have hspe := ihe hwf hbelow hpe
    obtain ⟨⟨⟨Φ₁, S₁, τe⟩, hinfe⟩, hee⟩ := Option.isSome_iff_exists.mp hspe
    obtain ⟨R₁, hagpe, htye, hR₁⟩ := Infer.complete' hinfe hwf hbelow hSlc hfty
    have hτeLC : τe.IsLC := (Infer.lc hinfe hwf).1
    have hbpe := Infer.belowFvars hinfe hbelow
    have hΦ₁τe : Φ₁ ∉ τe.freeVars := fun hm => by have := hbpe.1.mem_lt _ hm; omega
    have hΦ₁1τe : Φ₁ + 1 ∉ τe.freeVars := fun hm => by have := hbpe.1.mem_lt _ hm; omega
    obtain ⟨U, hUni, _⟩ := exists_pair_unifier htye.symm hΦ₁τe hΦ₁1τe hR₁ hαLC hβLC
    have huniSome : (unifyCore τe (Ty.pair (Ty.fvar Φ₁) (Ty.fvar (Φ₁ + 1)))).isSome :=
      (unifyCore_complete_aux (2 * (U.onTy τe).size + 1)).1 (by omega)
        hτeLC (ContainsBvarsUpTo.pair ContainsBvarsUpTo.fvar ContainsBvarsUpTo.fvar) hUni
    obtain ⟨⟨S₂', _⟩, heuni⟩ := Option.isSome_iff_exists.mp huniSome
    rw [inferCore]; simp only [hee, heuni, Option.isSome_some]

/-- Executable completeness, `snd` case. -/
theorem inferCore_complete_snd {e : Expr} (ihe : InferCoreComplete e) :
    InferCoreComplete (.snd e) := by
  intro Φ ctx Φ' S τ hwf hbelow h
  have happ := Infer.sound h hwf
  have hSlc : ∀ p ∈ S, p.2.IsLC := (Infer.lc h hwf).2
  cases h with
  | @snd _ _ _ Φ1d S1d S2d τed hpe huniD =>
    obtain ⟨τα, hfty⟩ : ∃ τα,
        TypeOfHM ((S1d ++ S2d).onCtx ctx) e (.pair τα (S2d.onTy (.fvar (Φ1d + 1)))) := by
      cases happ with | snd hh => exact ⟨_, hh⟩
    have hαLC : τα.IsLC := by
      have := TypeOfHM.regular hfty; cases this with | pair h _ => exact h
    have hβLC : (S2d.onTy (.fvar (Φ1d + 1))).IsLC := by
      have := TypeOfHM.regular hfty; cases this with | pair _ h => exact h
    have hspe := ihe hwf hbelow hpe
    obtain ⟨⟨⟨Φ₁, S₁, τe⟩, hinfe⟩, hee⟩ := Option.isSome_iff_exists.mp hspe
    obtain ⟨R₁, hagpe, htye, hR₁⟩ := Infer.complete' hinfe hwf hbelow hSlc hfty
    have hτeLC : τe.IsLC := (Infer.lc hinfe hwf).1
    have hbpe := Infer.belowFvars hinfe hbelow
    have hΦ₁τe : Φ₁ ∉ τe.freeVars := fun hm => by have := hbpe.1.mem_lt _ hm; omega
    have hΦ₁1τe : Φ₁ + 1 ∉ τe.freeVars := fun hm => by have := hbpe.1.mem_lt _ hm; omega
    obtain ⟨U, hUni, _⟩ := exists_pair_unifier htye.symm hΦ₁τe hΦ₁1τe hR₁ hαLC hβLC
    have huniSome : (unifyCore τe (Ty.pair (Ty.fvar Φ₁) (Ty.fvar (Φ₁ + 1)))).isSome :=
      (unifyCore_complete_aux (2 * (U.onTy τe).size + 1)).1 (by omega)
        hτeLC (ContainsBvarsUpTo.pair ContainsBvarsUpTo.fvar ContainsBvarsUpTo.fvar) hUni
    obtain ⟨⟨S₂', _⟩, heuni⟩ := Option.isSome_iff_exists.mp huniSome
    rw [inferCore]; simp only [hee, heuni, Option.isSome_some]
/-- Function-completeness for a branch list: given a (well-formed,
    frontier-bounded) `InferBranches` derivation, `inferBranchesCore` succeeds.
    Mirrors `InferBranches.complete`, but concludes `.isSome` instead of producing
    a derivation, driving each branch body via `InferCoreComplete`. -/
def InferBranchesCoreComplete (branches : List (MatchPattern × Expr)) : Prop :=
  ∀ {Φ : Nat} {ctx : Ctx} {tyName : TyName} {ta : List Ty} {ρ : Ty} {Φ' : Nat} {S : Subst},
    CtxWF ctx → CtxBelow Φ ctx → (∀ t ∈ ta, t.IsLC) → (∀ t ∈ ta, Ty.BelowFvars Φ t) →
    ρ.IsLC → Ty.BelowFvars Φ ρ →
    InferBranches Φ ctx tyName ta ρ branches Φ' S →
    (inferBranchesCore Φ ctx tyName ta ρ branches).isSome

theorem inferBranchesCore_complete : ∀ (branches : List (MatchPattern × Expr)),
    (∀ br ∈ branches, InferCoreComplete br.2) → InferBranchesCoreComplete branches := by
  intro branches
  induction branches with
  | nil =>
    intro _ Φ ctx tyName ta ρ Φ' S _ _ _ _ _ _ _
    simp [inferBranchesCore]
  | cons head rest ih =>
    intro ihbr
    obtain ⟨pat, body⟩ := head
    intro Φ ctx tyName ta ρ Φ' S hwf hbelow hta hbta hρ hbρ h
    -- declarative branch typings + LC facts from the given derivation
    have hsound := InferBranches.sound h hwf hta hρ
    have hSlc : ∀ p ∈ S, p.2.IsLC := (InferBranches.lc h hwf hta hρ).2
    -- invert the head branch's declarative typing (at the residual `S`)
    have hdhead := hsound (pat, body) (List.mem_cons_self ..)
    cases hdhead with
    | mk hlook htyName hpc hpc2 hforall hpb hbctx hbodyty =>
      expose_names
      simp only [Subst.onCtx] at hlook
      have hpc' : ctor.paramCount = ta.length := hpc.trans (by rw [List.length_map])
      have hinsts : instContents = ctor.contents.map (Ty.openWith (ta.map S.onTy)) :=
        instContents_eq_openWith hforall (fun c hc => hpc ▸ ctor.bound c hc)
      rw [hbctx, hpb, hinsts] at hbodyty
      have hbodyWF : CtxWF { ctx with
          env := (ctor.contents.map (Ty.openWith ta)).map PolyTy.mkTrivial ++ ctx.env } :=
        branchBindings_wf hwf hta hpc'
      have hbodyBelow : CtxBelow Φ { ctx with
          env := (ctor.contents.map (Ty.openWith ta)).map PolyTy.mkTrivial ++ ctx.env } :=
        branchBindings_below hbelow hbta
      have hbodyty2 : TypeOfHM (S.onCtx { ctx with
          env := (ctor.contents.map (Ty.openWith ta)).map PolyTy.mkTrivial ++ ctx.env })
          body (S.onTy ρ) := by
        rw [Subst.onCtx_branchBindings hSlc]; exact hbodyty
      -- STEP: drive the head branch body IH (functionally), then factor via `complete'`
      obtain ⟨_, _, _, _, hbodyderiv, _, _, _⟩ := Infer.complete hbodyWF hbodyBelow hSlc hbodyty2
      have hbodysome := (ihbr (pat, body) (List.mem_cons_self ..)) hbodyWF hbodyBelow hbodyderiv
      obtain ⟨⟨⟨Φ_b, S_b, τ_b⟩, hinfbody⟩, hebody⟩ := Option.isSome_iff_exists.mp hbodysome
      obtain ⟨R_b, hagbody, htybody, hR_b⟩ := Infer.complete' hinfbody hbodyWF hbodyBelow hSlc hbodyty2
      have hτb_lc : τ_b.IsLC := (Infer.lc hinfbody hbodyWF).1
      have hS_b : ∀ p ∈ S_b, p.2.IsLC := (Infer.lc hinfbody hbodyWF).2
      have hbb := Infer.belowFvars hinfbody hbodyBelow
      have hle_b := Infer.frontier_le hinfbody
      -- STEP: `R_b` unifies `τ_b` with `S_b.onTy ρ`; realise the function's MGU via `unifyCore`
      have hUni : Unifies R_b τ_b (S_b.onTy ρ) := by
        show R_b.onTy τ_b = R_b.onTy (S_b.onTy ρ)
        rw [← htybody, ← Subst.onTy_append]
        exact Subst.onTy_congr hagbody hbρ
      have huniSome : (unifyCore τ_b (S_b.onTy ρ)).isSome :=
        (unifyCore_complete_aux (2 * (R_b.onTy τ_b).size + 1)).1 (by omega)
          hτb_lc (Subst.onTy_lc hS_b hρ) hUni
      obtain ⟨⟨S_u, h_u⟩, heuni⟩ := Option.isSome_iff_exists.mp huniSome
      obtain ⟨R_u, hR_u_eq, hR_u⟩ := UnifyRel.greatest_lc h_u R_b hR_b hUni
      have hS_u : ∀ p ∈ S_u, p.2.IsLC := UnifyRel.lc h_u hτb_lc (Subst.onTy_lc hS_b hρ)
      have hS_u_below : ∀ p ∈ S_u, Ty.BelowFvars Φ_b p.2 :=
        UnifyRel.belowFvars h_u hbb.1 (Subst.onTy_belowFvars hbb.2 (hbρ.mono hle_b))
      -- STEP: hypotheses for the recursion on `rest` (in the function's intermediate state)
      have hwf' : CtxWF (S_u.onCtx (S_b.onCtx ctx)) :=
        Subst.onCtx_wf hS_u (Subst.onCtx_wf hS_b hwf)
      have hbelow_Sb : CtxBelow Φ_b (S_b.onCtx ctx) := Subst.onCtx_below hbb.2 hle_b hbelow
      have hbelow' : CtxBelow Φ_b (S_u.onCtx (S_b.onCtx ctx)) :=
        Subst.onCtx_below hS_u_below (le_refl _) hbelow_Sb
      have hta' : ∀ t ∈ ta.map (fun t => S_u.onTy (S_b.onTy t)), t.IsLC := by
        intro t' ht'; obtain ⟨t0, ht0, rfl⟩ := List.mem_map.mp ht'
        exact Subst.onTy_lc hS_u (Subst.onTy_lc hS_b (hta t0 ht0))
      have hbta' : ∀ t ∈ ta.map (fun t => S_u.onTy (S_b.onTy t)), Ty.BelowFvars Φ_b t := by
        intro t' ht'; obtain ⟨t0, ht0, rfl⟩ := List.mem_map.mp ht'
        exact Subst.onTy_belowFvars hS_u_below
          (Subst.onTy_belowFvars hbb.2 ((hbta t0 ht0).mono hle_b))
      have hρ' : (S_u.onTy (S_b.onTy ρ)).IsLC := Subst.onTy_lc hS_u (Subst.onTy_lc hS_b hρ)
      have hbρ' : Ty.BelowFvars Φ_b (S_u.onTy (S_b.onTy ρ)) :=
        Subst.onTy_belowFvars hS_u_below (Subst.onTy_belowFvars hbb.2 (hbρ.mono hle_b))
      -- STEP: factoring identities for the recursion's declarative typings
      have key_t : ∀ {t : Ty}, Ty.BelowFvars Φ t →
          R_u.onTy (S_u.onTy (S_b.onTy t)) = S.onTy t := by
        intro t ht
        rw [← hR_u_eq (S_b.onTy t), ← Subst.onTy_append]
        exact (Subst.onTy_congr hagbody ht).symm
      have hctx_eq : R_u.onCtx (S_u.onCtx (S_b.onCtx ctx)) = S.onCtx ctx := by
        rw [← Subst.onCtx_comp_of_onTy_eq hR_u_eq, ← Subst.onCtx_append]
        exact Subst.onCtx_congr (fun v hv => (hagbody v hv).symm) hbelow
      have hta_eq : (ta.map (fun t => S_u.onTy (S_b.onTy t))).map R_u.onTy = ta.map S.onTy := by
        rw [List.map_map]
        apply List.map_congr_left
        intro t ht
        simpa using key_t (hbta t ht)
      have hρ_eq : R_u.onTy (S_u.onTy (S_b.onTy ρ)) = S.onTy ρ := key_t hbρ
      have hdecl' : ∀ br ∈ rest, TypeOfMatchBranch (R_u.onCtx (S_u.onCtx (S_b.onCtx ctx)))
          br tyName ((ta.map (fun t => S_u.onTy (S_b.onTy t))).map R_u.onTy)
          (R_u.onTy (S_u.onTy (S_b.onTy ρ))) := by
        intro br hbr
        rw [hctx_eq, hta_eq, hρ_eq]
        exact hsound br (List.mem_cons_of_mem _ hbr)
      -- STEP: re-derive `rest` in the function's intermediate state, then recurse via the list IH
      obtain ⟨Φ_rr, S_r, R_r, hinfrest, _hagrest, _hR_r⟩ :=
        InferBranches.complete (fun br _ => Infer.completeAt br.2)
          hwf' hbelow' hta' hbta' hρ' hbρ' hR_u hdecl'
      have hrestsome := ih (fun br hbr => ihbr br (List.mem_cons_of_mem _ hbr))
        hwf' hbelow' hta' hbta' hρ' hbρ' hinfrest
      obtain ⟨⟨⟨Φ_r, S_r2⟩, hrest'⟩, herest⟩ := Option.isSome_iff_exists.mp hrestsome
      -- STEP: conclude by unfolding `inferBranchesCore` and discharging the guards
      rw [inferBranchesCore]
      split
      · rename_i heqn; rw [hlook] at heqn; exact absurd heqn (by simp)
      · rename_i ctorr heqs
        obtain rfl : ctorr = ctor := by rw [hlook] at heqs; exact (Option.some.inj heqs).symm
        rw [dif_pos htyName, dif_pos hpc', dif_pos hpc2]
        simp only [hebody, heuni, herest, Option.isSome_some]

theorem inferCore_complete_match {scrut : Expr} {branches : List (MatchPattern × Expr)}
    (ihscrut : InferCoreComplete scrut)
    (ihbranches : ∀ pat e, (pat, e) ∈ branches → InferCoreComplete e) :
    InferCoreComplete (.match_ scrut branches) := by
  intro Φ ctx Φ' S τ hwf hbelow h
  have happ := Infer.sound h hwf
  have hSlc : ∀ p ∈ S, p.2.IsLC := (Infer.lc h hwf).2
  cases h with
  | @match_ _ _ _ _ Φ1d Φ3d S1d S2d S3d tyNamed arityd τsd hscrutderiv hne huniD hbranchesderiv =>
    cases happ with
    | match_ hscrut_decl hne' hbranches_decl =>
      expose_names
      set S₀ := S1d ++ S2d ++ S3d with hS₀def
      set τ₀ := S3d.onTy (S2d.onTy (Ty.fvar (Φ1d + arityd))) with hτ₀def
      -- decompose the (nonempty) branch list and relate the head ctor to `tyName`/`tyArgs`
      obtain ⟨b0, brest, hbeq⟩ := List.exists_cons_of_ne_nil hne'
      subst hbeq
      obtain ⟨pat0, body0⟩ := b0
      have hhead_decl := hbranches_decl (pat0, body0) (List.mem_cons_self ..)
      have hτ₀_lc : τ₀.IsLC := TypeOfMatchBranch.regular hhead_decl
      obtain ⟨ctor0, hlook0, htyName0, hpc0⟩ :
          ∃ ctor0, LookupList.get? ctx.ctors pat0.ctor = some ctor0 ∧
            ctor0.tyName = tyName ∧ ctor0.paramCount = tyArgs.length := by
        cases hhead_decl with
        | mk hlk htn hpc _ _ _ _ _ => exact ⟨_, by simpa [Subst.onCtx] using hlk, htn, hpc⟩
      -- STEP 1: scrutinee function IH, then factor via `complete'`.
      have hsscrut := ihscrut hwf hbelow hscrutderiv
      obtain ⟨⟨⟨Φ₁, S₁, τs⟩, hinfs⟩, hescrut⟩ := Option.isSome_iff_exists.mp hsscrut
      obtain ⟨R₁, hags, htys, hR₁⟩ := Infer.complete' hinfs hwf hbelow hSlc hscrut_decl
      have hS₁ : ∀ p ∈ S₁, p.2.IsLC := (Infer.lc hinfs hwf).2
      have hτsLC : τs.IsLC := (Infer.lc hinfs hwf).1
      have hbs : Ty.BelowFvars Φ₁ τs ∧ ∀ p ∈ S₁, Ty.BelowFvars Φ₁ p.2 :=
        Infer.belowFvars hinfs hbelow
      have hle1 : Φ ≤ Φ₁ := Infer.frontier_le hinfs
      have hwf₁ : CtxWF (S₁.onCtx ctx) := Subst.onCtx_wf hS₁ hwf
      have hbelow₁ : CtxBelow Φ₁ (S₁.onCtx ctx) := Subst.onCtx_below hbs.2 hle1 hbelow
      have hctxeq : R₁.onCtx (S₁.onCtx ctx) = S₀.onCtx ctx := by
        rw [← Subst.onCtx_append]
        exact Subst.onCtx_congr (fun v hv => (hags v hv).symm) hbelow
      have htyArgs_lc : ∀ t ∈ tyArgs, t.IsLC := by
        have hreg := TypeOfHM.regular hscrut_decl
        cases hreg with
        | customTy h => exact h
      -- STEP 2: super-fresh block and the explicit unifier `U`.
      obtain ⟨W₀, hW₀ge, hW₀fresh⟩ := exists_fresh_block
        (R₁.map Prod.fst ++ R₁.flatMap (fun p => p.2.freeVars)
          ++ tyArgs.flatMap Ty.freeVars ++ τ₀.freeVars) Φ₁ (tyArgs.length + 1)
      obtain ⟨U, hUdef⟩ : ∃ U : Subst,
        U = (freshVars Φ₁ (tyArgs.length + 1)).zip ((freshVars W₀ (tyArgs.length + 1)).map (Ty.fvar ·))
            ++ R₁ ++ (freshVars W₀ (tyArgs.length + 1)).zip (tyArgs ++ [τ₀]) := ⟨_, rfl⟩
      have hUonTy : ∀ x, U.onTy x =
          Subst.onTy ((freshVars W₀ (tyArgs.length + 1)).zip (tyArgs ++ [τ₀]))
            (R₁.onTy (Subst.onTy ((freshVars Φ₁ (tyArgs.length + 1)).zip
              ((freshVars W₀ (tyArgs.length + 1)).map (Ty.fvar ·))) x)) := by
        intro x
        rw [hUdef, Subst.onTy_append, Subst.onTy_append]
      have hWi_mem : ∀ {i : Nat}, i < tyArgs.length + 1 →
          W₀ + i ∈ freshVars W₀ (tyArgs.length + 1) := by
        intro i hi
        simp only [freshVars, List.mem_map, List.mem_range]
        exact ⟨i, hi, rfl⟩
      have hWs_notin_R₁keys : ∀ w ∈ freshVars W₀ (tyArgs.length + 1), w ∉ R₁.map Prod.fst := by
        intro w hw hc
        have hwge := freshVars_ge w hw
        have := hW₀fresh w (List.mem_append_left _ (List.mem_append_left _
          (List.mem_append_left _ hc)))
        omega
      have hWs_R₁range : ∀ w ∈ freshVars W₀ (tyArgs.length + 1), ∀ q ∈ R₁, w ∉ q.2.freeVars := by
        intro w hw q hq hc
        have hwge := freshVars_ge w hw
        have := hW₀fresh w (List.mem_append_left _ (List.mem_append_left _
          (List.mem_append_right _ (List.mem_flatMap.mpr ⟨q, hq, hc⟩))))
        omega
      have htyArgs_belowW₀ : ∀ t ∈ tyArgs, Ty.BelowFvars W₀ t := by
        intro t ht
        apply Ty.BelowFvars.of_freeVars_lt
        intro v hv
        exact hW₀fresh v (List.mem_append_left _ (List.mem_append_right _
          (List.mem_flatMap.mpr ⟨t, ht, hv⟩)))
      have hτ₀_belowW₀ : Ty.BelowFvars W₀ τ₀ := by
        apply Ty.BelowFvars.of_freeVars_lt
        intro v hv
        exact hW₀fresh v (List.mem_append_right _ hv)
      have hU_index : ∀ (i : Nat) (v : Ty), i < tyArgs.length + 1 →
          (tyArgs ++ [τ₀])[i]? = some v → U.onTy (Ty.fvar (Φ₁ + i)) = v := by
        intro i v hi hvi
        rw [hUonTy]
        have hL1 : Subst.onTy ((freshVars Φ₁ (tyArgs.length + 1)).zip
            ((freshVars W₀ (tyArgs.length + 1)).map (Ty.fvar ·))) (Ty.fvar (Φ₁ + i))
            = Ty.fvar (W₀ + i) := by
          apply Ty.substFvars_zip_fvar_eq' freshVars_nodup (freshVars_getElem? hi)
          · rw [List.getElem?_map, freshVars_getElem? hi]; rfl
          · intro X hX hc
            simp only [Ty.freeVars, List.mem_singleton] at hc
            have hXlt := freshVars_lt X hX
            omega
        rw [hL1]
        have hL2 : R₁.onTy (Ty.fvar (W₀ + i)) = Ty.fvar (W₀ + i) := by
          apply Ty.substFvars_eq_self_of_no_key
          intro p hp hc
          simp only [Ty.freeVars, List.mem_singleton] at hc
          have hkey : p.1 ∈ R₁.map Prod.fst := List.mem_map.mpr ⟨p, hp, rfl⟩
          rw [hc] at hkey
          exact hWs_notin_R₁keys (W₀ + i) (hWi_mem hi) hkey
        rw [hL2]
        apply Ty.substFvars_zip_fvar_eq' freshVars_nodup (freshVars_getElem? hi) hvi
        intro w hw hc
        have hwge := freshVars_ge w hw
        have hvmem : v ∈ (tyArgs ++ [τ₀]) := List.mem_of_getElem? hvi
        have hvbelow : Ty.BelowFvars W₀ v := by
          rcases List.mem_append.mp hvmem with hvt | hvτ
          · exact htyArgs_belowW₀ v hvt
          · have hvτ₀ : v = τ₀ := List.mem_singleton.mp hvτ
            rw [hvτ₀]; exact hτ₀_belowW₀
        have := hvbelow.mem_lt w hc
        omega
      -- STEP 4: `U` unifies `τs` with the fresh `customTy`.
      have hmap_eq : ((freshVars Φ₁ tyArgs.length).map (Ty.fvar ·)).map U.onTy = tyArgs := by
        apply List.ext_getElem?
        intro i
        rcases Nat.lt_or_ge i tyArgs.length with hi | hi
        · rw [List.getElem?_map, List.getElem?_map, freshVars_getElem? hi]
          simp only [Option.map_some]
          rw [List.getElem?_eq_getElem hi]
          congr 1
          exact hU_index i (tyArgs[i]'hi) (by omega)
            (by rw [List.getElem?_append_left hi, List.getElem?_eq_getElem hi])
        · rw [List.getElem?_eq_none (by simp only [List.length_map, freshVars_length]; exact hi),
            List.getElem?_eq_none hi]
      have hA_id_τs : Subst.onTy ((freshVars Φ₁ (tyArgs.length + 1)).zip
          ((freshVars W₀ (tyArgs.length + 1)).map (Ty.fvar ·))) τs = τs := by
        apply Ty.substFvars_eq_self_of_no_key
        intro p hp hc
        have hp1 : p.1 ∈ freshVars Φ₁ (tyArgs.length + 1) := (List.of_mem_zip hp).1
        have hge := freshVars_ge p.1 hp1
        have hlt := hbs.1.mem_lt p.1 hc
        omega
      have hC_id_custom : Subst.onTy ((freshVars W₀ (tyArgs.length + 1)).zip (tyArgs ++ [τ₀]))
          (Ty.customTy tyName tyArgs) = Ty.customTy tyName tyArgs := by
        apply Ty.substFvars_eq_self_of_no_key
        intro p hp hc
        have hp1 : p.1 ∈ freshVars W₀ (tyArgs.length + 1) := (List.of_mem_zip hp).1
        have hge := freshVars_ge p.1 hp1
        have hcb : Ty.BelowFvars W₀ (Ty.customTy tyName tyArgs) := .customTy htyArgs_belowW₀
        have hlt := hcb.mem_lt p.1 hc
        omega
      have hUL : U.onTy τs = Ty.customTy tyName tyArgs := by
        rw [hUonTy, hA_id_τs, ← htys]
        exact hC_id_custom
      have hUR : U.onTy (Ty.customTy tyName ((freshVars Φ₁ tyArgs.length).map (Ty.fvar ·)))
          = Ty.customTy tyName tyArgs := by
        rw [Subst.onTy_customTy, hmap_eq]
      have hUni : Unifies U τs (Ty.customTy tyName ((freshVars Φ₁ tyArgs.length).map (Ty.fvar ·))) := by
        show U.onTy τs = U.onTy (Ty.customTy tyName ((freshVars Φ₁ tyArgs.length).map (Ty.fvar ·)))
        rw [hUL, hUR]
      -- STEP 5: realise the unifier as the *function's* MGU `S₂` (via `unifyCore`), factor `U`.
      have hcustomTy_lc : (Ty.customTy tyName ((freshVars Φ₁ tyArgs.length).map (Ty.fvar ·))).IsLC :=
        ContainsBvarsUpTo.customTy (fun t ht => by
          obtain ⟨x, _, rfl⟩ := List.mem_map.mp ht; exact ContainsBvarsUpTo.fvar)
      have hUlc : ∀ p ∈ U, p.2.IsLC := by
        rw [hUdef]
        intro p hp
        rcases List.mem_append.mp hp with hp' | hp'
        · rcases List.mem_append.mp hp' with hp'' | hp''
          · have hmem := (List.of_mem_zip hp'').2
            obtain ⟨x, _, hxeq⟩ := List.mem_map.mp hmem
            rw [← hxeq]; exact ContainsBvarsUpTo.fvar
          · exact hR₁ p hp''
        · have hmem := (List.of_mem_zip hp').2
          rcases List.mem_append.mp hmem with ht | hτ
          · exact htyArgs_lc p.2 ht
          · have hpτ₀ : p.2 = τ₀ := List.mem_singleton.mp hτ
            rw [hpτ₀]; exact hτ₀_lc
      have huniSome : (unifyCore τs
          (Ty.customTy tyName ((freshVars Φ₁ tyArgs.length).map (Ty.fvar ·)))).isSome :=
        (unifyCore_complete_aux (2 * (U.onTy τs).size + 1)).1 (by omega) hτsLC hcustomTy_lc hUni
      obtain ⟨⟨S₂, h₂⟩, heuni⟩ := Option.isSome_iff_exists.mp huniSome
      obtain ⟨R₂, hR₂_eq, hR₂lc⟩ := UnifyRel.greatest_lc h₂ U hUlc hUni
      have hS₂ : ∀ p ∈ S₂, p.2.IsLC := UnifyRel.lc h₂ hτsLC hcustomTy_lc
      have hbS₂ : ∀ p ∈ S₂, Ty.BelowFvars (Φ₁ + tyArgs.length + 1) p.2 := by
        apply UnifyRel.belowFvars h₂ (hbs.1.mono (by omega))
        apply Ty.BelowFvars.customTy
        intro t ht
        obtain ⟨x, hx, rfl⟩ := List.mem_map.mp ht
        exact Ty.BelowFvars.fvar (by have := freshVars_lt x hx; omega)
      -- STEP 6: residual facts connecting `R₂` to the declarative data.
      have hUeqR₁ : ∀ v, v < Φ₁ → U.onTy (Ty.fvar v) = R₁.onTy (Ty.fvar v) := by
        intro v hv
        rw [hUonTy]
        have hA_id : Subst.onTy ((freshVars Φ₁ (tyArgs.length + 1)).zip
            ((freshVars W₀ (tyArgs.length + 1)).map (Ty.fvar ·))) (Ty.fvar v) = Ty.fvar v := by
          apply Ty.substFvars_eq_self_of_no_key
          intro p hp hc
          simp only [Ty.freeVars, List.mem_singleton] at hc
          have hp1 : p.1 ∈ freshVars Φ₁ (tyArgs.length + 1) := (List.of_mem_zip hp).1
          have := freshVars_ge p.1 hp1
          omega
        rw [hA_id]
        apply Ty.substFvars_eq_self_of_no_key
        intro p hp hc
        have hp1 : p.1 ∈ freshVars W₀ (tyArgs.length + 1) := (List.of_mem_zip hp).1
        have hge := freshVars_ge p.1 hp1
        exact Subst.not_mem_onTy_freeVars (hWs_R₁range p.1 hp1)
          (by simp only [Ty.freeVars, List.mem_singleton]; omega) hc
      have hR₂ctx : R₂.onCtx (S₂.onCtx (S₁.onCtx ctx)) = S₀.onCtx ctx := by
        rw [← Subst.onCtx_comp_of_onTy_eq hR₂_eq, Subst.onCtx_congr hUeqR₁ hbelow₁, hctxeq]
      have hta_lc : ∀ t ∈ ((freshVars Φ₁ tyArgs.length).map (Ty.fvar ·)).map S₂.onTy, t.IsLC := by
        intro t ht
        obtain ⟨t0, ht0, rfl⟩ := List.mem_map.mp ht
        obtain ⟨x, _, rfl⟩ := List.mem_map.mp ht0
        exact Subst.onTy_lc hS₂ ContainsBvarsUpTo.fvar
      have hta_below : ∀ t ∈ ((freshVars Φ₁ tyArgs.length).map (Ty.fvar ·)).map S₂.onTy,
          Ty.BelowFvars (Φ₁ + tyArgs.length + 1) t := by
        intro t ht
        obtain ⟨t0, ht0, rfl⟩ := List.mem_map.mp ht
        obtain ⟨x, hx, rfl⟩ := List.mem_map.mp ht0
        exact Subst.onTy_belowFvars hbS₂ (Ty.BelowFvars.fvar (by have := freshVars_lt x hx; omega))
      have hρ_lc : (S₂.onTy (Ty.fvar (Φ₁ + tyArgs.length))).IsLC :=
        Subst.onTy_lc hS₂ ContainsBvarsUpTo.fvar
      have hρ_below : Ty.BelowFvars (Φ₁ + tyArgs.length + 1)
          (S₂.onTy (Ty.fvar (Φ₁ + tyArgs.length))) :=
        Subst.onTy_belowFvars hbS₂ (Ty.BelowFvars.fvar (by omega))
      have hta_R₂ : (((freshVars Φ₁ tyArgs.length).map (Ty.fvar ·)).map S₂.onTy).map R₂.onTy
          = tyArgs := by
        rw [List.map_map]
        exact Eq.trans (List.map_congr_left (fun t _ => (hR₂_eq t).symm)) hmap_eq
      have hρ_R₂ : R₂.onTy (S₂.onTy (Ty.fvar (Φ₁ + tyArgs.length))) = τ₀ := by
        rw [← hR₂_eq]
        exact hU_index tyArgs.length τ₀ (by omega)
          (by rw [List.getElem?_append_right (Nat.le_refl _)]; simp)
      -- STEP 7: branch declarative typings, recast over the algorithmic data.
      have hbr' : ∀ br ∈ ((pat0, body0) :: brest),
          TypeOfMatchBranch (R₂.onCtx (S₂.onCtx (S₁.onCtx ctx))) br tyName
            ((((freshVars Φ₁ tyArgs.length).map (Ty.fvar ·)).map S₂.onTy).map R₂.onTy)
            (R₂.onTy (S₂.onTy (Ty.fvar (Φ₁ + tyArgs.length)))) := by
        intro br hbr
        rw [hR₂ctx, hta_R₂, hρ_R₂]
        exact hbranches_decl br hbr
      -- STEP 8: thread the branch list with `InferBranches.complete`, then drive the helper.
      obtain ⟨Φ₃f, S₃f, R₃, hinfbr, _hagbr, _hR₃lc⟩ :=
        InferBranches.complete (fun br _ => Infer.completeAt br.2)
          (Subst.onCtx_wf hS₂ hwf₁) (Subst.onCtx_below hbS₂ (by omega) hbelow₁)
          hta_lc hta_below hρ_lc hρ_below hR₂lc hbr'
      have hbranchesSome := inferBranchesCore_complete ((pat0, body0) :: brest)
        (fun br hbr => by obtain ⟨p, e⟩ := br; exact ihbranches p e hbr)
        (Subst.onCtx_wf hS₂ hwf₁) (Subst.onCtx_below hbS₂ (by omega) hbelow₁)
        hta_lc hta_below hρ_lc hρ_below hinfbr
      obtain ⟨⟨⟨Φ₃b, S₃b⟩, hbrf⟩, hbr_eq⟩ := Option.isSome_iff_exists.mp hbranchesSome
      -- STEP 9: conclude by unfolding `inferCore`'s `.match_` arm.
      rw [inferCore]
      simp only [hescrut, List.head?_cons]
      split
      · rename_i heqn; rw [hlook0] at heqn; exact absurd heqn (by simp)
      · rename_i ctor0' heqs
        obtain rfl : ctor0' = ctor0 := by rw [hlook0] at heqs; exact (Option.some.inj heqs).symm
        -- The function's match discriminants are stated with `ctor0'.tyName`/`ctor0'.paramCount`,
        -- while the success facts use the declarative `tyName`/`tyArgs.length`. They are equal
        -- (`htyName0`/`hpc0`), but the matcher's dependent motive forbids rewriting the
        -- discriminant in place; instead we rebuild each success fact at the exact discriminant
        -- (where `Option.isSome`/the unify result type is polymorphic, so the `rw` is legal),
        -- then reduce each match by rewriting the *whole* discriminant.
        have harg_eq : Ty.customTy ctor0'.tyName ((freshVars Φ₁ ctor0'.paramCount).map (Ty.fvar ·))
            = Ty.customTy tyName ((freshVars Φ₁ tyArgs.length).map (Ty.fvar ·)) := by
          rw [htyName0, hpc0]
        have hD1 : (unifyCore τs (Ty.customTy ctor0'.tyName
            ((freshVars Φ₁ ctor0'.paramCount).map (Ty.fvar ·)))).isSome := by
          rw [harg_eq, heuni]; exact Option.isSome_some
        obtain ⟨⟨S₂x, h₂x⟩, hD1eq⟩ := Option.isSome_iff_exists.mp hD1
        have hSeq : S₂ = S₂x := by
          have key : Option.map Subtype.val (unifyCore τs (Ty.customTy ctor0'.tyName
                ((freshVars Φ₁ ctor0'.paramCount).map (Ty.fvar ·))))
              = Option.map Subtype.val (unifyCore τs (Ty.customTy tyName
                ((freshVars Φ₁ tyArgs.length).map (Ty.fvar ·)))) := by
            rw [harg_eq]
          rw [hD1eq, heuni] at key
          simpa using key.symm
        subst hSeq
        have hD2 : (inferBranchesCore (Φ₁ + ctor0'.paramCount + 1) (S₂.onCtx (S₁.onCtx ctx))
            ctor0'.tyName (((freshVars Φ₁ ctor0'.paramCount).map (Ty.fvar ·)).map S₂.onTy)
            (S₂.onTy (Ty.fvar (Φ₁ + ctor0'.paramCount))) ((pat0, body0) :: brest)).isSome := by
          rw [htyName0, hpc0, hbr_eq]; exact Option.isSome_some
        obtain ⟨⟨⟨Φ₃z, S₃z⟩, hbz⟩, hD2eq⟩ := Option.isSome_iff_exists.mp hD2
        simp only [hD1eq, hD2eq, Option.isSome_some]

/-- **`inferCore` completeness, assembled.** For every expression, a (WF,
    frontier-bounded) `Infer` derivation entails that `inferCore` succeeds. -/
theorem inferCore_complete : ∀ e, InferCoreComplete e := by
  intro e
  induction e using Expr.rec_strong with
  | primLit p => exact inferCore_complete_prim
  | pair a b iha ihb => exact inferCore_complete_pair iha ihb
  | lambda body ih => exact inferCore_complete_lambda ih
  | app f inp ihf ihi => exact inferCore_complete_app ihf ihi
  | letIn be body ihbe ihbody => exact inferCore_complete_letIn ihbe ihbody
  | fst e ih => exact inferCore_complete_fst ih
  | snd e ih => exact inferCore_complete_snd ih
  | var n => exact inferCore_complete_var
  | ctor nm => exact inferCore_complete_ctor
  | match_ scrut branches ihscrut ihbranches => exact inferCore_complete_match ihscrut ihbranches

/-- **`infer` completeness.** Algorithm W succeeds whenever the expression is
    declaratively typeable under a well-formed, frontier-bounded context. -/
theorem infer_complete {Φ : Nat} {ctx : Ctx} {e : Expr} {Φ' : Nat} {S : Subst} {τ : Ty}
    (h : Infer Φ ctx e Φ' S τ) (hwf : CtxWF ctx) (hbelow : CtxBelow Φ ctx) :
    (infer Φ ctx e).isSome := by
  have := inferCore_complete e hwf hbelow h
  simpa [infer, Option.isSome_map] using this


/-! ### Sound + complete, packaged as equivalences

Bundling each refinement into a single `↔`: the executable succeeds exactly when
the corresponding relation is inhabited, and (composing with `Infer.iff_typeable`)
exactly when the expression is declaratively typeable. -/

/-- `unify` succeeds iff the (LC) monotypes are unifiable. -/
theorem unify_iff {a b : Ty} (ha : a.IsLC) (hb : b.IsLC) :
    (unify a b).isSome ↔ ∃ S, UnifyRel a b S := by
  constructor
  · intro h
    obtain ⟨S, hS⟩ := Option.isSome_iff_exists.mp h
    exact ⟨S, unify_sound hS⟩
  · rintro ⟨S, hS⟩
    exact unify_complete hS ha hb

/-- `infer` succeeds iff the `Infer` relation is inhabited (for a well-formed,
    frontier-bounded context). -/
theorem infer_iff {Φ : Nat} {ctx : Ctx} {e : Expr}
    (hwf : CtxWF ctx) (hbelow : CtxBelow Φ ctx) :
    (infer Φ ctx e).isSome ↔ ∃ Φ' S τ, Infer Φ ctx e Φ' S τ := by
  constructor
  · intro h
    obtain ⟨⟨Φ', S, τ⟩, he⟩ := Option.isSome_iff_exists.mp h
    exact ⟨Φ', S, τ, infer_sound he⟩
  · rintro ⟨Φ', S, τ, hInfer⟩
    exact infer_complete hInfer hwf hbelow

/-- **The executable typechecker decides typeability.** `infer` succeeds iff `e`
    is declaratively typeable under some LC specialization of `ctx` — the
    full-circle bridge from the executable function all the way to `TypeOfHM`. -/
theorem infer_iff_typeable {Φ : Nat} {ctx : Ctx} {e : Expr}
    (hwf : CtxWF ctx) (hbelow : CtxBelow Φ ctx) :
    (infer Φ ctx e).isSome ↔
      ∃ (S : Subst) (τ : Ty), (∀ p ∈ S, p.2.IsLC) ∧ TypeOfHM (S.onCtx ctx) e τ := by
  rw [infer_iff hwf hbelow]
  exact (Infer.iff_typeable hwf hbelow).symm


/-! ### Whole-program typechecking

For a *closed* program — context `⟨[], ctors⟩` with an empty term-variable
environment — the algorithmic side-conditions (`CtxWF`, `CtxBelow 0`) hold
vacuously, and a substitution does nothing to an empty env (`Subst.onCtx_empty`).
So the leaky `Φ`/`S` machinery disappears from the statements entirely.

`principalType` keeps just the inferred monotype (sound, principal, decides
typeability — `principalType_*`). `typecheck` then **generalizes** it: at an
empty environment every remaining free type variable is generalizable, so the
output is a genuine *closed* type scheme — no free type variables, no dangling
bound variables (`typecheck_closed`). `typecheck` is the intended entry point;
everything else is in service of it, up to the declarative `TypeOfHM`. -/

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
  | pair a b iha ihb =>
      refine .pair (iha ?_) (ihb ?_)
      · intro Z hZ; exact h Z (List.mem_dedup.mpr (List.mem_append.mpr (Or.inl hZ)))
      · intro Z hZ; exact h Z (List.mem_dedup.mpr (List.mem_append.mpr (Or.inr hZ)))
  | arrow a b iha ihb =>
      refine .arrow (iha ?_) (ihb ?_)
      · intro Z hZ; exact h Z (List.mem_dedup.mpr (List.mem_append.mpr (Or.inl hZ)))
      · intro Z hZ; exact h Z (List.mem_dedup.mpr (List.mem_append.mpr (Or.inr hZ)))
  | customTy nm tys ih =>
      refine .customTy fun t ht => ih t ht ?_
      intro Z hZ; exact h Z (mem_TyList_freeVars.mpr ⟨t, ht, hZ⟩)

/-- The principal *monotype* of a closed program: run Algorithm W from the empty
    environment and keep just the resulting type (the inferer's `Φ`/`S` are
    internal). `typecheck` generalizes this into a closed scheme. -/
def principalType (ctors : CtorEnv) (e : Expr) : Option Ty :=
  (infer 0 ⟨[], ctors⟩ e).map (·.2.2)

/-- Monotype soundness: a computed principal type is a genuine declarative type. -/
theorem principalType_sound {ctors : CtorEnv} {e : Expr} {τ : Ty}
    (h : principalType ctors e = some τ) : TypeOfHM ⟨[], ctors⟩ e τ := by
  rw [principalType] at h
  rcases hc : infer 0 ⟨[], ctors⟩ e with _ | ⟨Φ', S, τ'⟩ <;> rw [hc] at h
  · simp at h
  · simp only [Option.map_some, Option.some.injEq] at h
    subst h
    have := Infer.sound (infer_sound hc) CtxWF.empty
    rwa [Subst.onCtx_empty] at this

/-- Monotype principality: every declarative type of the program is a
    substitution instance of the computed principal type. -/
theorem principalType_principal {ctors : CtorEnv} {e : Expr} {τ : Ty}
    (h : principalType ctors e = some τ) :
    ∀ τ₀, TypeOfHM ⟨[], ctors⟩ e τ₀ → ∃ R : Subst, τ₀ = R.onTy τ := by
  rw [principalType] at h
  rcases hc : infer 0 ⟨[], ctors⟩ e with _ | ⟨Φ', S, τ'⟩ <;> rw [hc] at h
  · simp at h
  · simp only [Option.map_some, Option.some.injEq] at h
    subst h
    have hP := infer_isPrincipal hc CtxWF.empty CtxBelow.empty
    intro τ₀ hτ₀
    exact hP.principal (S₀ := []) (by simp) (by rwa [Subst.onCtx_nil])

/-- Monotype decidability: `principalType` succeeds iff the program is typeable. -/
theorem principalType_iff {ctors : CtorEnv} {e : Expr} :
    (principalType ctors e).isSome ↔ ∃ τ, TypeOfHM ⟨[], ctors⟩ e τ := by
  constructor
  · intro h
    obtain ⟨τ, hτ⟩ := Option.isSome_iff_exists.mp h
    exact ⟨τ, principalType_sound hτ⟩
  · rintro ⟨τ, hτ⟩
    have hinfer : (infer 0 ⟨[], ctors⟩ e).isSome := by
      rw [infer_iff_typeable CtxWF.empty CtxBelow.empty]
      exact ⟨[], τ, by simp, by rwa [Subst.onCtx_nil]⟩
    simpa [principalType, Option.isSome_map] using hinfer

/-- **Type-check a closed program** — the intended entry point. Run Algorithm W
    from the empty environment and *generalize* the result into a closed type
    scheme. At an empty environment every remaining free type variable is
    generalizable, so the output is always a genuine closed scheme. -/
def typecheck (ctors : CtorEnv) (e : Expr) : Option PolyTy :=
  (principalType ctors e).map (genScheme [])

/-- **`typecheck`'s output is a genuine closed type scheme.** Its body contains
    no free type variables (`NoFreeVars`) and no dangling bound variables
    (`PolyTy.WF` — every `bvar` is bound by the scheme's own quantifier). So a
    successful `typecheck` always yields a concrete (possibly polymorphic) type:
    never a leftover unification variable, never a naked bound variable. -/
theorem typecheck_closed {ctors : CtorEnv} {e : Expr} {σ : PolyTy}
    (h : typecheck ctors e = some σ) : NoFreeVars σ.body ∧ σ.WF := by
  rw [typecheck, principalType] at h
  rcases hi : infer 0 ⟨[], ctors⟩ e with _ | ⟨Φ', S, τ⟩ <;> rw [hi] at h
  · simp at h
  · simp only [Option.map_some, Option.some.injEq] at h
    subst h
    have hlc : τ.IsLC := (Infer.lc (infer_sound hi) CtxWF.empty).1
    refine ⟨?_, genScheme_wf hlc⟩
    apply NoFreeVars.of_forall_not_mem
    intro Z hZ
    have hsub : Z ∈ τ.freeVars := Ty.closeOver_freeVars_subset hZ
    have hin : Z ∈ genVars [] τ := List.mem_filter.mpr ⟨hsub, rfl⟩
    exact Ty.not_mem_closeOver_freeVars hin hZ

/-- Whole-program soundness: a successful `typecheck` generalizes a genuine
    declarative type of the program. -/
theorem typecheck_sound {ctors : CtorEnv} {e : Expr} {σ : PolyTy}
    (h : typecheck ctors e = some σ) :
    ∃ τ, TypeOfHM ⟨[], ctors⟩ e τ ∧ σ = genScheme [] τ := by
  rw [typecheck] at h
  rcases hc : principalType ctors e with _ | τ <;> rw [hc] at h
  · simp at h
  · simp only [Option.map_some, Option.some.injEq] at h
    exact ⟨τ, principalType_sound hc, h.symm⟩

/-- Whole-program principality: the output scheme generalizes a principal monotype
    `τ` of which every declarative type of the program is a substitution
    instance. -/
theorem typecheck_principal {ctors : CtorEnv} {e : Expr} {σ : PolyTy}
    (h : typecheck ctors e = some σ) :
    ∃ τ, σ = genScheme [] τ ∧ TypeOfHM ⟨[], ctors⟩ e τ ∧
      ∀ τ₀, TypeOfHM ⟨[], ctors⟩ e τ₀ → ∃ R : Subst, τ₀ = R.onTy τ := by
  rw [typecheck] at h
  rcases hc : principalType ctors e with _ | τ <;> rw [hc] at h
  · simp at h
  · simp only [Option.map_some, Option.some.injEq] at h
    exact ⟨τ, h.symm, principalType_sound hc, principalType_principal hc⟩

/-- Whole-program decidability: `typecheck` succeeds iff the program is
    declaratively typeable. -/
theorem typecheck_iff {ctors : CtorEnv} {e : Expr} :
    (typecheck ctors e).isSome ↔ ∃ τ, TypeOfHM ⟨[], ctors⟩ e τ := by
  simp only [typecheck, Option.isSome_map]
  exact principalType_iff

open SmallStep in
/-- Whole-program progress (via `typecheck`): a typeable closed program whose
    matches are exhaustive is either a value or can take a step. -/
theorem typecheck_progress {ctors : CtorEnv} {e : Expr}
    (h : (typecheck ctors e).isSome) (h_exh : AllMatchesExhaustive ctors e) :
    IsValue e ∨ ∃ e', Step e e' := by
  obtain ⟨τ, hτ⟩ := typecheck_iff.mp h
  exact TypeOfHM.progress hτ rfl h_exh

open SmallStep in
/-- **Whole-program preservation, sharpened.** After a step the reduct still
    type-checks, and its principal scheme is *at least as general* as the
    original's: the original's principal monotype `τ` is a substitution instance
    of the reduct's principal monotype `τ'` (`τ = R.onTy τ'`, so `τ'` — hence the
    reduct's scheme `σ'` — subsumes the original).

    Reduction can make it **strictly** more general, because duplicating a value
    un-shares its type variable: `(λf. (f, f)) (λx. x)` has principal scheme
    `∀a. (a → a) × (a → a)`, but its reduct `((λx. x), (λx. x))` has the more
    general `∀a b. (a → a) × (b → b)`. That is exactly why we cannot state
    preservation as "`= some σ` with the *same* `σ`". -/
theorem typecheck_preservation {ctors : CtorEnv} {e e' : Expr} {σ : PolyTy}
    (h : typecheck ctors e = some σ) (h_step : Step e e') :
    ∃ σ' τ τ', typecheck ctors e' = some σ' ∧
      σ = genScheme [] τ ∧ σ' = genScheme [] τ' ∧ ∃ R : Subst, τ = R.onTy τ' := by
  obtain ⟨τ, hτ, hσeq⟩ := typecheck_sound h
  have hτ' : TypeOfHM ⟨[], ctors⟩ e' τ := TypeOfHM.preservation h_step hτ
  obtain ⟨τ', hpt'eq⟩ :=
    Option.isSome_iff_exists.mp (principalType_iff.mpr ⟨τ, hτ'⟩)
  obtain ⟨R, hR⟩ := principalType_principal hpt'eq τ hτ'
  refine ⟨genScheme [] τ', τ, τ', ?_, hσeq, rfl, R, hR⟩
  simp only [typecheck, hpt'eq, Option.map_some]

-- `typecheck [] (λx. x) = some ⟨1, bvar 0 → bvar 0⟩`  (i.e. the closed scheme `∀a. a → a`)
#eval (typecheck [] (.lambda (.var 0))).map (fun σ => (σ.paramCount, σ.body))
-- `typecheck [] (5 5) = none`
#eval (typecheck [] (.app (.primLit (.int 5)) (.primLit (.int 5)))).map (fun σ => (σ.paramCount, σ.body))



-- `infer (λx. x) = α → α`
#eval infer 0 { env := [], ctors := [] } (.lambda (.var 0))
-- `infer (λx. λy. x) = α → β → α`
#eval infer 0 { env := [], ctors := [] } (.lambda (.lambda (.var 1)))
-- `infer ((λx. x) 5) = Int`
#eval infer 0 { env := [], ctors := [] } (.app (.lambda (.var 0)) (.primLit (.int 5)))
