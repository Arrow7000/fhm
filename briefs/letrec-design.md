<!-- Design doc: adding recursion (`letRec`) to the Core HM language.
     Status: DESIGN / not yet implemented. Companion to next-agent-brief-corev2-and-surface.md (§2 "Recursion"). -->

# Design: recursion in Core via `letRec`

## 0. Decisions (resolved)

1. **Keep `letIn` and add a separate `letRec` node.** The two differ in *when*
   generalisation happens and *what is in scope in the RHS*:
   - `letIn ann rhs body`: the bound name is **not** in scope in `rhs`; the scheme
     is generalised **before** use in `body`. (Textbook Damas–Milner `let`.)
   - `letRec bindings body`: the whole group is in scope (at **monotypes**) in
     **every** RHS *and* the body; generalisation happens **once, after** the
     group is solved, for the body only.
   Encoding both behaviours in one node would need a flag + conditional logic in
   the typing rule (and in every proof). Keeping them separate leaves `letIn`'s
   already-proven metatheory untouched and makes each rule uniform.

2. **`letRec` always assumes recursion.** Its rule binds the group monomorphically
   in the RHSs *unconditionally* — it never inspects whether a binding actually
   self-/mutually-references. A non-recursive binding placed in a `letRec` still
   types soundly (the in-scope-but-unused monomorphic binding is harmless), so we
   don't have to *prove* a binding is recursive to use `letRec`.

3. **The "is it recursive? / dependency-SCC" analysis lives in elaboration.** The
   surface language has `let`-blocks; elaboration builds the binding-dependency
   graph, computes strongly-connected components, topologically sorts them, and
   emits — per SCC, in dependency order — either a `letIn` (singleton SCC with no
   self-reference) or a `letRec` (any SCC that recurses: size-1 self-rec, or
   size > 1 mutual). Core stays free of graph algorithms; the same machinery later
   handles top-level mutually-recursive `def` groups.

4. **No exotic invariants in Core / the typing rules.** We do *not* need a premise
   like "only `letRec` bindings may be recursive." A self-reference inside a
   `letIn` RHS simply refers to an *outer* binding (the let var isn't in scope
   there) or is ill-scoped, and won't typecheck as recursion. The distinction is
   **structural** — which environment the RHS is checked in — and self-documenting
   by the node name. Nothing extra to carry.

---

## 1. The `Expr` node

```lean
| letRec (bindings : List Expr) (body : Expr)
```

- `bindings = [e₀, …, e_{n-1}]` are the `n` mutually-recursive RHSs; `body` is the
  scope they're visible in.
- **v1 is annotation-free** (monomorphic recursion only). A later extension adds
  per-binding `Option PolyTy` annotations to enable *polymorphic* recursion
  (decidable when annotated), reusing the existing annotated-`let` skolem
  machinery. Out of scope for the first cut.
- `n = 1` is the self-recursive case and coincides exactly with `fix` (see §3.2):
  `letRec [e] body` behaves like `let f = fix (λf. e) in body`. So we get `fix`
  "for free" as a special case and never add a separate `fix` constructor.

### de Bruijn scoping (the bookkeeping to get right)

The `n` group binders are in scope in **all** RHSs **and** the body, occupying the
front of the environment, with binding `j` at de Bruijn index `j`:

```
env_for_RHSs_and_body  =  [slot₀, …, slot_{n-1}] ++ ctx.env      -- var j ↦ binding j
```

So inside any `eᵢ` (and `body`): `var j` (for `j < n`) is binding `j`; `var (n+k)`
is outer variable `k`. This matches the existing match-branch convention
(`patternBindings ++ ctx.env`, field 0 at index 0). `substN` with an `n`-element
list is exactly the right tool to discharge the group at the front.

---

## 2. Declarative typing — `TypeOfHM.letRec`

### 2.1 The rule (math)

```
∀ j < n.   Γ, f₀:τ₀, …, f_{n-1}:τ_{n-1}  ⊢  eⱼ : τⱼ        (group bound MONO-morphically)
           Γ, f₀:gen(Γ;τ₀), …, f_{n-1}:gen(Γ;τ_{n-1})  ⊢  body : ρ
──────────────────────────────────────────────────────────────────────
           Γ  ⊢  letRec [e₀…e_{n-1}] body : ρ
```
where `gen(Γ;τ) = ∀ (ftv(τ) \ ftv(Γ)). τ`. Standard Damas–Milner letrec.

### 2.2 The key subtlety (why this is NOT just `letIn` with a list)

`letIn`'s cofinite premise reads "`rhs` types at **every** opening `M.openVars Xs`"
— i.e. the rhs is genuinely polymorphic. **We must NOT reuse that shape for the
group**, because inside the RHSs the recursive occurrences are **monomorphic**
(bound at `mkTrivial τⱼ`, `paramCount = 0`). Asserting the RHSs type at every
opening would be *polymorphic recursion*, which is undecidable. So:

- **Group RHSs**: typed **once**, at monotypes, with all `fⱼ : mkTrivial τⱼ` in
  scope simultaneously (a `List.Forall₂`-style premise).
- **Generalisation**: a **separate**, per-binding step that turns each `τⱼ` into a
  body-scheme `Mⱼ` — generalisation happens for the *body*, not via the RHS typing.

### 2.3 Lean form (locally-nameless, **cofinite** like `letIn`)

The implemented (and corrected) rule. ⚠️ The first-attempt **existential** premise (b)
(`∃ ctx-fresh Xs, M.openVars Xs = τ`) was **unsound for the metatheory**: it pins one
`Xs`, so `weaken_env` (which has *no* env-freshness side-condition) is false for
`letRec` — inserting `env_extra` can capture the pinned `Xs` and you can't re-choose
it. `letIn` survives only because it is **cofinite** (`∀ fresh Xs`), letting weakening
dodge `env_extra`. So `letRec` must be cofinite too. A single cofinite premise both
encodes monomorphic recursion (the group is bound mono at each opening) and replaces
the separate generalisation premise:

```lean
| letRec :
    (∀ M ∈ Ms, M.WF) →
    bindings.length = Ms.length →
    -- for every sufficiently-fresh opening `Xs` of the group's schemes, bind the
    -- group MONOMORPHICALLY at that opening and type each RHS at its opened type:
    (∀ Xs, FreshNames L (PolyTy.totalParams Ms) Xs →
        ∀ p ∈ bindings.zip (PolyTy.openGroup Ms Xs),
          TypeOfHM { ctx with env := (PolyTy.openGroup Ms Xs).map PolyTy.mkTrivial ++ ctx.env }
            p.1 p.2) →
    bodyCtx = { ctx with env := Ms ++ ctx.env } →
    TypeOfHM bodyCtx body ρ →
    TypeOfHM ctx (.letRec bindings body) ρ
```

with helpers `PolyTy.totalParams Ms := (Ms.map paramCount).sum` and
`PolyTy.openGroup Ms Xs` opening each `Mⱼ` at its consecutive slice of `Xs`
(`Xs.take/drop M.paramCount`). The recursive occurrences are monomorphic (the group
is `mkTrivial`-bound at the opening); cofinite `∀ Xs` mirrors `letIn` and keeps
generalisation sound under weakening/substitution. The `∀ p ∈ … zip …` (rather than
`List.Forall₂ (TypeOfHM …)`) is forced — Lean rejects a recursive occurrence nested
inside `List.Forall₂` with local-variable parameters.

Notes:
- `rec_strong`'s `letRec` minor premise threads per-binding IHs over the group under
  the same cofinite `∀ Xs` shape.
- Preservation's `letRecUnfold` case: each re-wrapped `letRec bindings eⱼ` has scheme
  `Mⱼ` via the cofinite premise (re-apply the rule with body `eⱼ`), i.e. `HasSchemeVars`,
  then `subst_lemma_many` discharges the body.

### 2.5 Literature (this design is standard; we are not freelancing)

- **F. Pottier, MPRI 2-4-2 notes** — the derived `LetRec` rule
  `Γ,f:T₁ ⊢ λx.t₁:T₁ ; X̄#Γ,t₁ ; Γ,f:∀X̄.T₁ ⊢ t₂:T₂  ⟹  Γ ⊢ let rec f x = t₁ in t₂ : T₂`,
  i.e. monomorphic recursive occurrence, generalise after. Also: polymorphic
  recursion (Mycroft) needs a **mandatory annotation** ⇒ our deferral is standard.
- **langdev / OCaml** — for *mutual* recursion: collect the SCC, bind fresh
  monotypes, infer RHSs (recursive refs look up the monotype), generalise after.
  Confirmed "essentially what OCaml does." Matches §4's algorithm.
- **Chargueraud, "Engineering Formal Metatheory" / the LN library** — the
  locally-nameless + cofinite-quantification style our `Core.lean` already uses;
  the generalisation premise (b) is encoded exactly as `letIn`'s cofinite premise.
- **`rafaelcgs10/W-in-Coq`** (after Dubois) — a full Coq mechanisation of
  Damas–Milner + Algorithm W soundness **and** completeness; reference if the
  inference/principality proofs get hairy.

Per the literature, the recursive RHSs are canonically **lambdas** ("`let rec`
binds functions"). We do **not** bake that restriction into Core: the unfolding
dynamics (§3.1) is type-safe for any RHS (a non-function recursive binding simply
diverges), so the function-restriction, if wanted, is an optional surface lint.

### 2.4 Why `letRec` subsumes `letIn` (but we keep both anyway)

A singleton `letRec [e] body` where `e` doesn't reference `var 0` types the same as
`letIn none e body` (the unused mono binding is harmless, then generalised
identically). So `letRec` *could* replace `letIn` entirely — we keep `letIn`
because its metatheory is already proven and it's the cleaner path for the common
non-recursive case. Elaboration chooses (decision §0.3).

---

## 3. Dynamics + safety

### 3.1 The reduction rule (unconditional unfolding)

```
Step (.letRec bindings body)
     (body.substN 0 (bindings.map (fun e => Expr.letRec bindings e)))
```

I.e. substitute, for each group var `j` in `body`, the term `letRec bindings eⱼ`
("binding `j`, re-wrapped so its own group references stay resolved"). Each such
re-wrapped binding reduces by the same rule on demand; when `eⱼ` is a `λ`, one
unfold step exposes a lambda (productive). For `n = 1` this is precisely the `fix`
unfolding `fix f → f (fix f)`.

### 3.2 Consequences for safety

- **Progress is trivial for `letRec`**: it is *never a value* and *always steps*
  (the unfold rule always applies), so there is no new stuckness — even for a
  diverging binding like `letRec [var 0] (var 0)` (which loops, as it should). We
  lose normalisation (expected) but **not** type safety.
- **Preservation** is the real work: show
  `letRec bindings body : ρ ⟹ body.substN 0 (bindings.map (letRec bindings ·)) : ρ`.
  This is a `subst_lemma_many`-style argument (like `letIn`'s `letReduce`), but the
  substituted terms are themselves `letRec`s rather than values. Key fact to prove:
  each `letRec bindings eⱼ` has **scheme `Mⱼ`** (i.e. `HasScheme`), because
  `eⱼ : τⱼ` mono and `Mⱼ` generalises `τⱼ`. Then the existing scheme-substitution
  lemma discharges the body. ⚠️ **de Bruijn care**: the re-wrapped bindings are
  closed w.r.t. the group (the inner `letRec` re-binds it) and reference outer vars
  at the correct level; verify the `substN 0` shifting carefully — this is the most
  error-prone part of the dynamics.
- `letRec` is annotation-free ⇒ trivially `IsTyErased`, and `AllMatchesExhaustive`
  threads through its sub-terms (RHSs + body) like the other recursive nodes. Both
  closure lemmas (`Step.preserves_isTyErased`, `Step.preserves_exhaustive`) get a
  straightforward new case (the unfold result is a `substN` of erased/exhaustive
  pieces).

---

## 4. Inference (`Infer` / `inferCore`)

Mirrors `letIn` (which already uses `genScheme`) but with a monomorphic
pre-binding + a list-threader over the group (analogous to `InferBranches` for
match). Algorithm-W:

```
infer (letRec bindings body):
  βⱼ := fvar (Φ + j)         for j < n            -- n fresh monotype vars
  monoCtx := (β's as mkTrivial) ++ ctx
  -- thread inference over the group, unifying each RHS's type with its βⱼ:
  fold over bindings:  (Sⱼ, τⱼ) := infer eⱼ ; unify τⱼ with (current βⱼ)   -- like InferBranches
  S := composed group substitution
  Mⱼ := genScheme (S ctx).freeVars (S ctx).env (S βⱼ)                       -- generalise (as letIn)
  (S_body, ρ) := infer body in (Ms ++ S ctx)
  result := (S ++ S_body, S_body ρ)
```

So the inference side needs, in parallel to the match work:
- a new `Infer.letRec` constructor,
- an `InferRecGroup` list-threading inductive (the analogue of `InferBranches`) for
  the monomorphic group inference + per-binding unification,
- executable `inferCore`/`inferRecGroupCore` refiners,
- the lemma suite (`frontier_le`, `lc`, `belowFvars`, `sound`, `gap_avoid`,
  `complete`, `complete'`) + the `Infer.complete'` `letRec` case.

This is comparable in size to the `InferBranches` work in §1.

---

## 5. Should we design declarative + inference together?

**Design both now (this doc); implement declarative + safety first.**

- *Design together* because the declarative generalisation phrasing (§2.3 (b)) must
  be inference-friendly — it should line up with `genScheme` so the principality
  proof goes through, and the de Bruijn convention (§1) is shared. Designing the
  inference rule now is what *validates* the declarative choices (we already know
  §2.3 (b) ↔ `genScheme`, and the group-threading ↔ `InferRecGroup`).
- *Implement in stages* (the lock-then-thread pattern that worked for §1):
  1. `Expr.letRec` node + `TypeOfHM.letRec` + `rec_strong` case  → **green checkpoint.**
  2. Dynamics (unfold rule + `step`) + progress + preservation + the two `Step`
     closure lemmas + `erased_type_safety`  → **green + axiom-clean checkpoint, commit.**
  3. `Infer.letRec` + `InferRecGroup` + `inferCore`/`inferRecGroupCore` + soundness.
  4. Completeness/principality (`complete`, `complete'`, `inferCore_complete`) +
     an `AuditCapstone` witness (e.g. a recursive `length`-shaped program typechecks
     at its principal type)  → **final green + axiom-clean, commit.**

## 6. Risks / watch-items

- **(b) generalisation phrasing** — the one genuinely novel declarative premise;
  must be sound *and* completeness-provable. Cross-check with `genScheme`/`HasScheme`.
- **`substN 0` de Bruijn shifting** in the unfold rule (§3.1) — easy to get the
  group-vs-outer index levels wrong; write small `#eval`/lemma checks early.
- **`Forall₂` premises** ripple a per-binding IH through every `Expr`/`TypeOfHM`
  induction (`rec_strong`, progress, preservation, soundness, the `complete'`
  monster) — a `RecGroupMotive` helper (à la `BranchMotive`) will be needed.
- **Scope of v1**: annotation-free, monomorphic recursion only. Polymorphic
  (annotated) recursion and top-level `def` groups are deliberate follow-ups.
