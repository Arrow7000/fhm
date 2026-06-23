<!-- Handoff brief written after the "InferW soundness + completeness-foundation"
     session. Supersedes next-agent-brief-inferw-stage1.md (and the older
     next-agent-brief-inferw.md). Companion north-star: next-agent-brief-surface-lang.md. -->

# Handoff: finish InferW for scoped type variables (completeness → executable → typecheck)

## 0. North star and where this fits
The eventual goal is a verified **surface HM language** on top of the de Bruijn
`Core` (see `next-agent-brief-surface-lang.md`). The prerequisite is making the
**algorithm `Infer` (Algorithm-W) sound and complete for scoped type variables**
against the (already-committed) scoped-var `Core` spec, then exposing a public
`typecheck` API. **Soundness is done.** This brief is about the rest.

## 0a. Workflow the user wants (please follow, in order)
1. **Orient first.** Read this brief end-to-end. Then read (don't just grep)
   the relevant parts of `Experiments/FreshTypeSystem/InferW.lean` with the
   lean-lsp MCP — especially the now-green soundness layer (`Infer.sound`,
   `Infer.belowFvars`) and the partially-migrated completeness layer
   (`Infer.CompleteAt` and the `complete_*` helpers).
2. **Design soundness/completeness-critical moves with the user before a big
   push.** The two genuinely-subtle remaining pieces (the unification
   escape-dual in A1, and the skolem-unifier rework in A3) are worth a quick
   on-paper confirmation first. The *design is settled* (described below); if it
   needs to change, surface that before barrelling in.
3. **Be merciless about correctness, never cosmetic.** No `sorry`/`axiom`/
   `native_decide`; no weakening of headline statements to force green. Verify
   with `lean_verify` — axioms must be exactly `propext`/`Classical.choice`/
   `Quot.sound`. If something can't be proven honestly, say so and report the
   real obstacle. Decline/report beats a half-baked push.

## 0b. Environment gotchas
- **`Core.lean` is done + committed and should not need further edits.** All the
  Core machinery this work needs already exists (rename bridge, size measures,
  `Expr.tyFreeVars_openTyVars`, erasure). If you *do* edit Core, you must rebuild
  its olean and restart the LSP or InferW shows stale "fake green": shell
  `lake build Experiments.FreshTypeSystem.Core` (~35s), then MCP `lean_build`
  (it restarts the LSP; it will "fail" on the **unrelated pre-broken**
  `Experiments/Filterings.lean` — ignore that).
- **`lean_diagnostic_messages`: trust the `items` array, not whole-file
  `success`** (it reports false while *any* part of the 9.9k-line file is red).
  Scope queries with `start_line`/`end_line`. The mutual `Infer.*` theorems emit
  **enormous** `decreasing_by` dumps when a measure goal is unsolved — the real
  goal is the last line (e.g. `⊢ a.size < (a.pair b).size`).
- **`induction h` does NOT work on `Infer`/`InferBranches`** ("does not support
  mutually inductive"). Use `cases h` + the `termination_by e.size` pattern
  (below), or `Infer.rec`/`TypeOfHM.rec_strong` if you truly need IHs.

## 1. The single idea to internalize: scoped variables are RIGID, threaded as `K`
A scoped type variable becomes a free `fvar` "skolem" once its enclosing
`letInAnn` opens it (`rhs.openTyVars Ys`). It must stay **rigid** within its
scope. This shows up as a **rigid set `K`** threaded through the metatheory,
with two dual faces:

- **Soundness** (`Infer.sound`): the inferred substitution `S` **avoids** `K`
  (never binds a skolem). Signature:
  `Infer Φ ctx e Φ' S τ → CtxWF ctx → (K : List Nat) → (∀ k ∈ K, k < Φ) →
   (∀ y ∈ e.tyFreeVars, y ∈ K) → (∀ p ∈ S, p.1 ∉ K) → TypeOfHM (S.onCtx ctx) e τ`.
  Closed-program corollary `Infer.sound_closed` instantiates `K := []`.
- **Completeness** (`Infer.CompleteAt`): the given specialization `S₀`
  **fixes** `K`, and the residual `R` inherits it. Current (migrated) shape:
  `… CtxWF → CtxBelow Φ ctx → (∀ p ∈ S₀, p.2.IsLC) → (K : List Nat) →
   (∀ k ∈ K, k < Φ) → (∀ y ∈ e.tyFreeVars, y ∈ K) →
   (∀ k ∈ K, S₀.onTy (.fvar k) = .fvar k) → TypeOfHM (S₀.onCtx ctx) e τ₀ →
   ∃ Φ' S τ R, Infer … ∧ AgreesBelow Φ S₀ (S ++ R) ∧ τ₀ = R.onTy τ ∧
     (∀ p ∈ R, p.2.IsLC) ∧ (∀ k ∈ K, R.onTy (.fvar k) = .fvar k)`.

`K < Φ` and `e.tyFreeVars ⊆ K` together say "all in-scope skolems are old
(allocated below the frontier)". **Both disciplines are vacuous for a closed
top-level program** (`e.tyFreeVars = []`, `K := []`), so the public headlines
(`Infer.sound_closed`, `Infer.principal`) are unaffected — this is the standard
rigid-variable side condition, not a wart.

The **algorithm fix** that made soundness true: the unannotated `let` must not
generalize over an in-scope skolem. `genVars`/`genScheme` take a `rigid` list,
and `Infer.letIn` passes `rhs.tyFreeVars` (a no-op for ordinary HM programs).

## 2. DONE this session (committed; green + axiom-clean)
- **`Infer.sound` / `InferBranches.sound` / `Infer.sound_closed`** — the full
  soundness layer (commit `2314b04`).
- **`Infer.belowFvars` / `InferBranches.belowFvars`** — rebuilt with the
  "annotation vars `< Φ`" hypothesis (the below-frontier twin of `K`),
  `termination_by e.size`.
- **Completeness foundation** (commit `682f640`): `Infer.CompleteAt` re-based on
  the `K` discipline above, and these cases migrated + verified green:
  `complete_prim`, `complete_pair`, `complete_var`, `complete_ctor`, and the
  lambda trio — including the genuinely-new **`complete_lambda_ann_aux`** where
  the annotation `T` may carry scoped vars (`R.onTy (S.onTy T) = T` falls out of
  the agreement clause + `S₀` fixing `K`).
- **Helper lemmas hoisted** above their new first uses: `Ty.BelowFvars.of_freeVars_lt`,
  `Subst.onTy_eq_self_of_fixes`. New small Core/InferW lemmas added earlier:
  `Expr.tyFreeVars_openTyVars` (Core), `freshVars_ge`/`freshVars_lt`,
  `genVars_not_mem_rigid`.

## 3. The termination pattern (reuse verbatim)
Every mutual `Infer.*`/`InferBranches.*` metatheory theorem uses:
```
termination_by e.size                      -- (Expr.sizeBranches brs for the *Branches half)
decreasing_by
  all_goals (simp_wf; try subst_vars; try simp only [Expr.size, Expr.sizeBranches, Expr.size_openTyVars]; omega)
```
`Expr.size` ignores annotations so `(rhs.openTyVars Ys).size = rhs.size`
(`Expr.size_openTyVars`), which is what lets the opened-rhs recursion decrease.
Keep `decreasing_by` on ONE line (a newline before `try` inside the `(...)` is a
parse error).

## 4. WORK LEFT, in fresh stages

### Stage A — Finish completeness of the `Infer` relation (→ `Infer.principal`)
This is the bulk. The pattern for each helper: add `K` + the three input
conditions, `simp only [Expr.tyFreeVars, …] at` the `⊆ K` hyp to split it over
subterms, thread `K` to every recursive `CompleteAt` call and every
`Infer.belowFvars` call (which now needs `∀ y ∈ sub.tyFreeVars, y < Φ`, derived
as `fun y hy => hKΦ y (hKe y …)`), and produce the new "`R` fixes `K`" output.

- **A1 — unification cases: `complete_app(_aux)`, `complete_fst`, `complete_snd`,
  `complete_pair_unify_aux`, `complete_match(_aux)`.** These are the first cases
  whose residual comes out of *unification*, so "`R` fixes `K`" is NOT free from
  the agreement. It needs the **dual of soundness's escape**: *the MGU never
  binds a rigid variable that a witness unifier keeps fixed*. That is exactly
  `OUnify.skolem_escape` (the orientation kernel powering soundness). Plan:
  switch the MGU step from `UnifyRel.complete` to `OUnify.complete`, build the
  witness unifier `U` (you can show `U` fixes `K`: it fixes the fresh/`W` vars by
  construction and the residual-`R₂` part fixes `K` by induction), read off
  "`S` (the MGU) fixes `K`" from `OUnify.skolem_escape`, and combine with the
  factoring (`U = R ∘ S`) to get "`R` fixes `K`". Confirm this shape with the
  user before doing all four.
- **A2 — unannotated let: `complete_letIn_aux`.** `genScheme`/`genVars` now take
  the `rigid` list; the algorithm rule generalizes `genScheme rhs.tyFreeVars …`.
  Thread `K`; the generalization machinery (`closeOver`, `genScheme_hasSchemeVars`)
  is already adapted on the soundness side and should port over.
- **A3 — annotated let: `complete_letIn_ann_aux` + the skolem-unifier (old "D4").**
  The hard one. The OLD proof builds the rhs derivation *unopened* and allocates
  skolems `freshVars Φ₁ pc` *after* (so `τ₁` is disjoint from them, `σ` closed).
  The D2 algorithm allocates `Ys = freshVars Φ pc` *before* and infers
  `rhs.openTyVars Ys`, so **`τ₁` and `B = σ.openVars Ys` can both mention `Ys`,
  and `σ` can carry outer scoped vars**. Two sub-tasks:
  - Rework **`exists_skolem_unifier`**: today it assumes `Ys = freshVars Φ₁ pc`
    (interior block disjoint from `τ₁`) and `B.freeVars ⊆ Ys` (closed `σ`).
    Generalize to the `Ys ⊎ residue` partition (residue `< Φ`, the genuinely
    outer vars), tolerating skolems on both sides. The **block-swap conjugation**
    technique already in the proof (`blockList`/`blockListBack`, swap `Ys ↔ Ws`
    with `Ws` fresh, apply the declarative residual `R`, swap back) is the right
    tool and generalizes — only the hypotheses change.
  - Rework `complete_letIn_ann_aux` to the D2 order, and adapt the escape lemmas
    (`skolem_no_env_leak`, the `hesc2` second-opening trick) and
    `typeOfHM_at_block` to scoped `σ` / `Ys = freshVars Φ pc`.
- **A4 — the driver + headlines: `complete'`, `complete_letIn` dispatcher,
  `Infer.completeAt`, `Infer.complete`, `Infer.complete_instance`,
  `Infer.complete_id`, `Infer.principal`.** `complete'` threads `K` and dispatches
  to the migrated helpers (its `letInAnn` case opens the rhs at `Ys` and extends
  `K` by `Ys`, exactly mirroring `Infer.sound`'s `letInAnn`). The wrappers
  instantiate `K := []` (closed program) to recover the public statements.

### Stage B — The executable inferencer
`inferCore` / `inferBranchesCore` (the `Option`-returning function) and their
correctness bridges to the relation (`inferCore_complete`, soundness,
decidability). Currently red: a `sorry`-stub cascade plus the relation's
signature changes (the `LamSeed.some` `IsLC`, the 6-arg `letInAnn`, `genScheme`'s
rigid arg, and `Infer.sound` now taking `K`). Re-align with the new relation and
remove the `sorry`-dependent `#eval`s once it's green.

### Stage C — Type-safety + public `typecheck` API
`typecheck_progress` / `typecheck_preservation` currently call Core's
`progress`/`preservation` *without* the now-required `IsTyErased` argument.
Restate them over the **erased** program (model on Core's
`TypeOfHM.erased_type_safety` / `erased_type_safety_star`). **They cannot be
re-proven unchanged — subject reduction is false with annotations present**
("check with annotations, run erased"). Finish with the headline `typecheck` /
`infer_iff_typeable`.

After Stage C the file is fully green + axiom-clean; the surface language begins.

## 5. Reservations / sizing
- **A3 (skolem-unifier) is the riskiest single piece** — design with the user;
  expect iteration. **A1 (the escape-dual) is the second**; confirm the
  `OUnify.skolem_escape` shape on one case before replicating to all four.
- Honest sizing: A ≈ 1–2 focused sessions (A3 the unknown); B ≈ small–medium;
  C ≈ small. Stage it, validate each piece `lean_verify`-clean, report cleanly.
- The partially-migrated completeness section is a clean *partial* state: the
  Stage-1 soundness, `belowFvars`, and the six migrated `complete_*` helpers are
  green; everything from `complete_app` onward is uniformly red against the new
  `CompleteAt` signature (as expected). No green code is at risk.

## 6. Tools / verification
lean-lsp MCP: `lean_diagnostic_messages` (scope with line ranges; trust `items`),
`lean_goal`, `lean_multi_attempt`, `lean_hover_info`,
`lean_verify` (axiom check; fully-qualified names — expect exactly
`propext`/`Classical.choice`/`Quot.sound`). Avoid gratuitous whole-project
builds (they fail on `Filterings.lean`).
