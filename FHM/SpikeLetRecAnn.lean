import Experiments.FreshTypeSystem.InferW

/-! # SPIKE: annotated polymorphic recursion (`letRecAnn`)

Standalone validation of the Stage-3 declarative rule **before** touching frozen
`Core`. We state Pottier's `LetRecPoly` rule as a derived predicate
`TypeOfLetRecAnn` over the existing `TypeOfHM` (the recursive group lives in the
environment at its FULL given schemes), then:

1. prove a genuine *polymorphic*-recursion witness types under the rule;
2. show the same group's *monomorphic* reading (a plain `letRec`) does NOT type —
   i.e. the recursion schemes are load-bearing for typeability, so erasure cannot
   drop them (the design point that motivates "keep schemes through erasure");
3. sanity-check `weaken_env` / `typ_subst` tractability for the rule;
4. probe the scoped-variable / free-`fvar` safety question.

No edits to `Core`/`InferW`. -/

namespace SpikeLetRecAnn

/-- Local copy of Core's private `List.mem_zip_map_left` (needed for `weaken_env`). -/
private theorem mem_zip_map_left {α β γ : Type _} {f : α → γ} :
    ∀ {l : List α} {r : List β} {p : γ × β},
      p ∈ (l.map f).zip r → ∃ a b, a ∈ l ∧ (a, b) ∈ l.zip r ∧ p = (f a, b) := by
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
      | inl heq => exact ⟨hd, rhd, List.mem_cons_self, List.mem_cons_self, heq⟩
      | inr h' =>
        obtain ⟨a, b, ha, hmem, heq⟩ := ih h'
        exact ⟨a, b, List.mem_cons_of_mem _ ha, List.mem_cons_of_mem _ hmem, heq⟩

/-- Pottier's `LetRecPoly`, locally-nameless / cofinite, as a standalone
    predicate. The group is in scope at the FULL given schemes `σs` in BOTH the
    RHSs and the body — so recursive occurrences may instantiate `σⱼ` at
    different types (that is the polymorphic recursion). Each RHS is checked at
    its scheme's *own* disjoint skolem slice (`PolyTy.openGroup`); there is NO
    generalisation step (the schemes are given, not inferred), which is why the
    discarded `openGroup` opening — wrong for the monomorphic rule — is exactly
    right here. -/
def TypeOfLetRecAnn (ctx : Ctx) (σs : List PolyTy) (bindings : List Expr)
    (body : Expr) (ρ : Ty) : Prop :=
  ∃ L : List Nat,
    bindings.length = σs.length ∧
    (∀ σ ∈ σs, σ.WF) ∧
    (∀ Xs, FreshNames L (PolyTy.totalParams σs) Xs →
        ∀ p ∈ bindings.zip (PolyTy.openGroup σs Xs),
          TypeOfHM { ctx with env := σs ++ ctx.env } p.1 p.2) ∧
    TypeOfHM { ctx with env := σs ++ ctx.env } body ρ

/-! ## A genuine polymorphic-recursion witness

`let rec (f : ∀a. a → a) = λx. let _ = f 0 in let _ = f () in x in f`.

Inside the RHS, `f` is used at `Int → Int` AND at `Unit → Unit`: two distinct
instantiations of its scheme in its own body. That is polymorphic recursion. The
*monomorphic* reading of the same group forces `f`'s parameter to be both `Int`
and `Unit` and is rejected (see `monoRec_untypeable` below). -/

/-- `σ = ∀a. a → a`. -/
def selfSig : PolyTy := ⟨1, .arrow (.bvar 0) (.bvar 0)⟩

/-- `λx. let _ = f 0 in let _ = f () in x`. Under the λ, `f = var 1`; after the
    first `let`, `f = var 2`; the body returns `x`. -/
def polyRecRhs : Expr :=
  .lambda none
    (.letIn none (.app (.var 1) (.primLit (.int 0)))
      (.letIn none (.app (.var 2) (.primLit .unit))
        (.var 2)))

/-- The RHS types at every skolem opening `X → X` of `σ`, with `f : σ` in scope
    (polymorphic). This is the cofinite premise's content. -/
theorem polyRecRhs_typeable (X : Nat) :
    TypeOfHM ⟨[selfSig], []⟩ polyRecRhs (.arrow (.fvar X) (.fvar X)) := by
  -- λ : (fvar X) → (fvar X); body typed with x : fvar X, f : σ in scope.
  refine TypeOfHM.lambda .fvar (fun T h => Option.noConfusion h) rfl ?_
  -- first `let _ = f 0`: `f` instantiated at `Int`, so the binding has type `Int`.
  refine TypeOfHM.letIn (M := PolyTy.mkTrivial (.prim .int)) (L := [])
    .prim (fun σ h => Option.noConfusion h) ?_ rfl ?_
  · intro Xs hfresh
    obtain rfl : Xs = [] := List.eq_nil_of_length_eq_zero hfresh.length
    refine TypeOfHM.app ?_ TypeOfHM.primLitInt
    exact TypeOfHM.var (polyTy := selfSig) (tyArgs := [.prim .int]) rfl
      (by intro t ht; simp only [List.mem_singleton] at ht; subst ht; exact .prim)
      (.arrow (.bvar rfl) (.bvar rfl))
  -- second `let _ = f ()`: `f` instantiated at `Unit`.
  refine TypeOfHM.letIn (M := PolyTy.mkTrivial (.prim .unit)) (L := [])
    .prim (fun σ h => Option.noConfusion h) ?_ rfl ?_
  · intro Xs hfresh
    obtain rfl : Xs = [] := List.eq_nil_of_length_eq_zero hfresh.length
    refine TypeOfHM.app ?_ TypeOfHM.primLitUnit
    exact TypeOfHM.var (polyTy := selfSig) (tyArgs := [.prim .unit]) rfl
      (by intro t ht; simp only [List.mem_singleton] at ht; subst ht; exact .prim)
      (.arrow (.bvar rfl) (.bvar rfl))
  -- body: return `x : fvar X`.
  exact TypeOfHM.var (polyTy := PolyTy.mkTrivial (.fvar X)) (tyArgs := []) rfl
    (by intro t ht; cases ht) .fvar

/-- The headline: the annotated group **types** at its principal-ish instance
    `(fvar 0) → (fvar 0)` — polymorphic recursion accepted. -/
theorem polyRec_typeable :
    TypeOfLetRecAnn ⟨[], []⟩ [selfSig] [polyRecRhs] (.var 0)
      (.arrow (.fvar 0) (.fvar 0)) := by
  refine ⟨[], rfl, ?_, ?_, ?_⟩
  · intro σ hσ
    simp only [List.mem_singleton] at hσ; subst hσ
    show ContainsBvarsUpTo 1 (Ty.arrow (Ty.bvar 0) (Ty.bvar 0))
    exact .arrow (.bvar (by omega)) (.bvar (by omega))
  · intro Xs hfresh p hp
    obtain ⟨X, rfl⟩ : ∃ X, Xs = [X] :=
      List.length_eq_one_iff.mp hfresh.length
    have hog : PolyTy.openGroup [selfSig] [X] = [(Ty.fvar X).arrow (Ty.fvar X)] := rfl
    rw [hog] at hp
    simp only [List.zip_cons_cons, List.zip_nil_right, List.mem_singleton] at hp
    subst hp
    exact polyRecRhs_typeable X
  · -- body `var 0` = `f`, instantiated at `fvar 0`.
    exact TypeOfHM.var (polyTy := selfSig) (tyArgs := [.fvar 0]) rfl
      (by intro t ht; simp only [List.mem_singleton] at ht; subst ht; exact .fvar)
      (.arrow (.bvar rfl) (.bvar rfl))

/-! ## The monomorphic reading is NOT typeable

The *same* program read as an annotation-free `letRec` (the would-be erasure that
drops the scheme) is rejected — `f`'s monotype parameter cannot be both `Int` and
`Unit`. This is the concrete evidence that the recursion scheme is load-bearing
for typeability and therefore must survive erasure. -/

/-- `let rec f = λx. let _ = f 0 in let _ = f () in x in f` (no annotation). -/
def monoRecProg : Expr := .letRec [polyRecRhs] (.var 0)

-- Sanity check (matches `Examples.lean`'s `ill-typed` for this exact shape): the
-- monomorphic reading is rejected, so dropping the scheme loses typeability.
#eval (typecheck [] monoRecProg).isSome  -- expect: false

/-! ## Tractability 1: `weaken_env` (the historically dangerous lemma)

The §2.3 monomorphic redesign died because an *existential* premise pinned the
opening and weakening could capture it. Our premise is **cofinite** and the
schemes are **ctx-free**, so weakening goes through by delegating each RHS/body to
`TypeOfHM.weaken_env` — with NO env-freshness side condition and NO need to grow
`L`. This is the key structural check that the rule is weakening-sound. -/
theorem TypeOfLetRecAnn.weaken_env_front {ctors : CtorEnv}
    {env_extra env : Env} {σs : List PolyTy} {bindings : List Expr} {body : Expr}
    {ρ : Ty} (h : TypeOfLetRecAnn ⟨env, ctors⟩ σs bindings body ρ) :
    TypeOfLetRecAnn ⟨env_extra ++ env, ctors⟩ σs
      (bindings.map (·.shiftFrom σs.length env_extra.length))
      (body.shiftFrom σs.length env_extra.length) ρ := by
  obtain ⟨L, hlen, hwf, hcofin, hbody⟩ := h
  refine ⟨L, ?_, hwf, ?_, ?_⟩
  · rw [List.length_map]; exact hlen
  · intro Xs hfresh p hp
    obtain ⟨a, b, _, hq, rfl⟩ := mem_zip_map_left hp
    have hw := TypeOfHM.weaken_env (env_pre := σs) (env_extra := env_extra)
      (env := env) (hcofin Xs hfresh (a, b) hq)
    rw [List.append_assoc] at hw
    exact hw
  · have hw := TypeOfHM.weaken_env (env_pre := σs) (env_extra := env_extra)
      (env := env) hbody
    rw [List.append_assoc] at hw
    exact hw

/-! ## A scoped variable in a kept scheme is a free `fvar` — and that is safe

A recursion scheme may mention an enclosing scope's type variable. Once in scope
that variable is a free `fvar` (a rigid skolem), NOT a danglable `bvar`, and
`PolyTy.WF` permits free `fvar`s (it only bounds *bound* variables). So a kept
scheme referencing scoped variables is well-formed — no expressiveness is lost.
Here `Z` is such a rigid constant: `f : Z → Z` self-recurses, and `Z` is never
bound/closed by anything, yet everything types (exactly like `openId`). -/

/-- `Z → Z` with `Z` a free (scoped/rigid) type variable. -/
def rigidSig (Z : Nat) : PolyTy := ⟨0, .arrow (.fvar Z) (.fvar Z)⟩

/-- `λx. f x`, self-recursive at the rigid scheme `Z → Z`. -/
def scopedRhs : Expr := .lambda none (.app (.var 1) (.var 0))

theorem scopedRhs_typeable (Z : Nat) :
    TypeOfHM ⟨[rigidSig Z], []⟩ scopedRhs (.arrow (.fvar Z) (.fvar Z)) := by
  refine TypeOfHM.lambda .fvar (fun T h => Option.noConfusion h) rfl ?_
  refine TypeOfHM.app (argTy := .fvar Z) ?_ ?_
  · exact TypeOfHM.var (polyTy := rigidSig Z) (tyArgs := []) rfl
      (by intro t ht; cases ht) (.arrow .fvar .fvar)
  · exact TypeOfHM.var (polyTy := PolyTy.mkTrivial (.fvar Z)) (tyArgs := []) rfl
      (by intro t ht; cases ht) .fvar

/-- The kept scheme `Z → Z` mentions the free/rigid `Z`, is WF, and the group
    types — so referencing a scoped variable in a recursion scheme is fully
    supported (the concern that we'd have to forbid it is unfounded). -/
theorem scopedRec_typeable (Z : Nat) :
    TypeOfLetRecAnn ⟨[], []⟩ [rigidSig Z] [scopedRhs] (.var 0)
      (.arrow (.fvar Z) (.fvar Z)) := by
  refine ⟨[], rfl, ?_, ?_, ?_⟩
  · intro σ hσ; simp only [List.mem_singleton] at hσ; subst hσ
    exact .arrow .fvar .fvar
  · intro Xs hfresh p hp
    obtain rfl : Xs = [] := List.eq_nil_of_length_eq_zero hfresh.length
    have hog : PolyTy.openGroup [rigidSig Z] [] = [(Ty.fvar Z).arrow (Ty.fvar Z)] := rfl
    rw [hog] at hp
    simp only [List.zip_cons_cons, List.zip_nil_right, List.mem_singleton] at hp
    subst hp
    exact scopedRhs_typeable Z
  · exact TypeOfHM.var (polyTy := rigidSig Z) (tyArgs := []) rfl
      (by intro t ht; cases ht) (.arrow .fvar .fvar)

/-! ## Tractability 2: `typ_subst` — and it is *simpler* than the monomorphic rule

Pushing `[Z ↦ U]` through the rule needs only: schemes substituted pointwise
(`PolyTy.WF.substFvar` keeps them WF — `substFvar` touches the free `fvar` `Z`,
never a `bvar`), the opening/subst commutation `PolyTy.openGroup_map_substFvar`
(already in Core, built for the monomorphic rule, and needing only `Z ∉ Xs`), and
`TypeOfHM.typ_subst_preservation` on the RHSs/body. There is NO gen-var freshening
(`genGroup_renameG`), because the schemes are *given* — so this is strictly cheaper
than the shipped monomorphic `letRec`. -/

/-- Local copy of Core's private `List.mem_zip_map` (both lists mapped). -/
private theorem mem_zip_map {α β γ δ : Type _} {f : α → γ} {g : β → δ} :
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

theorem TypeOfLetRecAnn.typ_subst {ctors : CtorEnv} {env : Env}
    {σs : List PolyTy} {bindings : List Expr} {body : Expr} {ρ : Ty} {Z : Nat} {U : Ty}
    (hZ : Z ∉ env.freeVars) (hUlc : U.IsLC)
    (h : TypeOfLetRecAnn ⟨env, ctors⟩ σs bindings body ρ) :
    TypeOfLetRecAnn ⟨env, ctors⟩ (σs.map (PolyTy.substFvar Z U))
      (bindings.map (·.substTyFvar Z U)) (body.substTyFvar Z U) (Ty.substFvar Z U ρ) := by
  obtain ⟨L, hlen, hwf, hcofin, hbody⟩ := h
  refine ⟨Z :: L, ?_, ?_, ?_, ?_⟩
  · rw [List.length_map, List.length_map]; exact hlen
  · intro σ' hσ'
    obtain ⟨σ, hσ, rfl⟩ := List.mem_map.mp hσ'
    exact PolyTy.WF.substFvar hUlc (hwf σ hσ)
  · intro Xs hfresh p hp
    have hZXs : Z ∉ Xs := fun hc => hfresh.avoid Z hc List.mem_cons_self
    have hfreshL : FreshNames L (PolyTy.totalParams σs) Xs :=
      ⟨by have := hfresh.length; rwa [PolyTy.totalParams_map_substFvar] at this,
       hfresh.nodup, fun x hx hc => hfresh.avoid x hx (List.mem_cons_of_mem _ hc)⟩
    rw [PolyTy.openGroup_map_substFvar hUlc σs hZXs] at hp
    obtain ⟨a, b, hq, rfl⟩ := mem_zip_map hp
    have hsub := TypeOfHM.typ_subst_preservation (env_post := σs) (env_outer := env)
      hZ hUlc (hcofin Xs hfreshL (a, b) hq)
    simpa only [Env.substFvar] using hsub
  · have hsub := TypeOfHM.typ_subst_preservation (env_post := σs) (env_outer := env)
      hZ hUlc hbody
    simpa only [Env.substFvar] using hsub

end SpikeLetRecAnn
