<!-- Handoff brief written after the "completeness research + reformulation" session.
     Supersedes next-agent-brief-inferw-completeness.md (which describes the OLD,
     now-abandoned escape-check approach to the annotated-let completeness).
     Companion north-star: next-agent-brief-surface-lang.md. -->

# Handoff: finish InferW completeness via *rigidity-aware unification* (reformulation)

## 0. One-paragraph summary
Soundness of `Infer` (Algorithm-W) for scoped type variables is done + committed.
Completeness was stuck for several sessions on the **annotated `let`** case. Root
cause (confirmed against the literature): we represent the signature's rigid
skolems as ordinary unification variables (`Ty.fvar`) and enforce their rigidity
with **post-hoc escape checks** (`hesc1`/`hesc2`, `OUnify.skolem_escape`,
`exists_skolem_unifier`). That is the one approach the literature singles out as
*subtle to get complete* (Peyton Jones et al. 2007 / Leijen / FreezeML). The fix
is to make rigidity **structural in unification** — the D&K / levels lesson,
specialized to our rank-1 setting via the rigid set `K` we already thread. This
stays **entirely in InferW**: Core's `TypeOfHM` (the declarative spec) is the
ground truth and needs no levels/rigidity; **no Core edits, no new `Ty`
constructor**. The two genuinely-hard facts are already proven (see §2).

## 0a. Workflow the user wants (please follow)
1. Be merciless about correctness: no `sorry`/`axiom`/`native_decide`, no
   weakening of headline statements. Verify with `lean_verify` — axioms must be
   exactly `propext`/`Classical.choice`/`Quot.sound`. Decline/report beats a
   half-baked push.
2. Don't edit Core. If you think you must, stop and surface it first (we worked
   hard to keep Core green + sorry-free, and the design does not require it).
3. Validate each piece `lean_verify`-clean; commit checkpoints.

## 0b. Environment gotchas
- **`lean_diagnostic_messages`: trust the `items` array, not whole-file
  `success`** (false while *any* part of the 10k-line file is red). Scope with
  `start_line`/`end_line`.
- `induction h` does NOT work on `Infer`/`InferBranches` (mutual inductive). Use
  `cases h` + `termination_by e.size` with
  `decreasing_by all_goals (simp_wf; try subst_vars; try simp only [Expr.size, Expr.sizeBranches, Expr.size_openTyVars]; omega)`
  (keep `decreasing_by` on ONE line). For derivation induction over `TypeOfHM`
  use `TypeOfHM.rec_strong` (its `letIn` case gives the IH for the *opened* bound
  expr — this is how `weaken_scheme` was repaired).
- Don't run whole-project `lake build` (it fails on the unrelated pre-broken
  `Experiments/Filterings.lean`).

## 1. The reformulation, precisely
**Idea:** unification *knows* the rigid set `K` and refuses to bind a `k ∈ K`
(it binds the other side; it *fails* if a rigid var is forced to equal a
non-variable or a different rigid var). Consequences:
- the inferred substitution **avoids `K` by construction** → `hesc1` ("no skolem
  is bound") is structural, not a property to re-establish;
- over-general annotations are rejected because unification *fails* directly;
- completeness of unification becomes a clean induction (`complete_K`), replacing
  `OUnify.skolem_escape` + `exists_skolem_unifier` (both get **deleted**).

`Φ` is the `Infer` frontier (a freshness counter; NOT in `TypeOfHM`). It *mints*
the skolems (`Ys = freshVars Φ pc`) but does not mark rigidity — **`K` does**.

## 2. DONE this session (committed; green + axiom-clean)
- `2dd94ca`: `UnifyRel.greatest_K` (MGU residual preserves `K`) + the A1/A2
  completeness cases (`complete_app/fst/snd/pair_unify/match`,
  `InferBranches.complete`, `complete_letIn_aux`) + `TypeOfHM.weaken_scheme`
  reproved via `rec_strong`.
- `b6ec5ee`: **`UnifyRel.complete_K`** (≈ line 5180). The hesc1 kernel:
  `a.IsLC → b.IsLC → (∀p∈U, p.2.IsLC) → Unifies U a b → (∀k∈K, U.onTy (.fvar k) = .fvar k)
   → ∃ S, UnifyRel a b S ∧ (∀p∈S, p.1 ∉ K)`. **No** `b.freeVars ⊆ Ys` restriction
  (the thing that broke `OUnify.skolem_escape` under D2). Var-var oriented away
  from `K`; rigid-var-meets-nonvar is vacuous (U fixes it); recursion threads the
  witness via `greatest_K`.
- `9396e04`: **`skolem_no_env_leak_K`** (≈ line 7990). The hesc2 kernel:
  scoped-σ leak (no `NoFreeVars σ`); witness `U := R₁` directly (R₁ fixes `Ys`
  and `K`), so the block-swap `exists_skolem_unifier` is gone; the `Ys ∪ K`
  residue of `B = σ.openVars Ys` is discharged by "`Schk` avoids `K`" + "`Ys`
  above frontier"; two-opening (cofinite) contradiction core unchanged.

## 3. The one remaining design point (issue 2a) — decided
Both kernels need the rhs residual `R₁` to fix `Ys` (and `K`). The producer gets
that by inferring the *opened* rhs (`rhs.openTyVars Ys`) at rigid set `K ∪ Ys`,
which needs the input specialization `S₀` to leave `Ys` rigid. But completeness
residuals carry proof-fresh vars above the frontier, so `S₀` cannot be assumed to
avoid the *specific* block `freshVars Φ pc`. **Decision:** relax `Infer.letInAnn`
so `Ys` is an *abstract* sufficiently-fresh block (premises: `Ys.Nodup`,
`Ys.length = σ.paramCount`, `∀ y ∈ Ys, Φ ≤ y`, and a frontier `Φ'` with
`∀ y ∈ Ys, y < Φ'` for the rhs inference), letting completeness *choose*
`Ys ∉ dom S₀`. This is the literature-standard move (skolems are never pinned to
fixed names). Low risk: **`sound_letInAnn` is already stated abstractly over
`Ys`**, so soundness is mostly re-wiring; the executable `inferCore` picks
`freshVars` (a valid instance) in the Stage-B bridge.

## 4. Step plan (in order)
1. **Relax `Infer.letInAnn`** (the inductive, ≈ line 727 area) to an abstract
   fresh block `Ys` with the premises above. Re-prove `Infer.frontier_le`,
   `Infer.belowFvars`, `Infer.lc`, `Infer.sound` for the new rule (the letInAnn
   case feeds the premises to the already-abstract `sound_letInAnn`).
2. **Thread "S avoids K" through the completeness producer**: each unification
   case (`complete_app/fst/snd/pair_unify/match`) switches `UnifyRel.complete` →
   `UnifyRel.complete_K`, adding `(∀ p ∈ S, p.1 ∉ K)` to the `CompleteAt` output
   (alongside the existing "R fixes K" from `greatest_K`). Mechanical.
3. **`complete_letIn_ann_aux`** (≈ line 8089): choose `Ys` fresh w.r.t. `S₀`
   (via the relaxed rule); infer `rhs.openTyVars Ys` at `K ∪ Ys` → `S₁` avoids
   `Ys` (hesc1, from step 2) and residual `R₁` fixes `K ∪ Ys` (greatest_K);
   build `Schk` via `complete_K` (avoids `Ys`); `hesc2` via `skolem_no_env_leak_K`;
   assemble `letInAnn`. Delete `exists_skolem_unifier` + `OUnify.skolem_escape`
   once unused. Generalize `typeOfHM_at_block` to scoped σ if needed.
4. **A4 / Stage B / Stage C**: thread, then instantiate `K := []` at the headlines
   (`Infer.complete`, `Infer.principal`, etc.); re-align `inferCore`/
   `inferBranchesCore` to the abstract-`Ys` rule; finish `typecheck` over the
   *erased* program (subject reduction is false with annotations — model on Core's
   `TypeOfHM.erased_type_safety`). Verify headlines `lean_verify`-clean.

## 5. Sizing / reservations
- Steps 1–2 are mechanical-moderate; step 3 is the payoff (now de-risked); step 4
  is plumbing + the erasure restatement.
- This is *smaller* than the old escape grind: `exists_skolem_unifier`, the
  `OUnify` escape kernel, and the orientation gymnastics are deleted, not
  generalized.
- If a frontier-bookkeeping snag appears in step 1, the abstract-`Ys` premises
  may need adjusting (a `Φ'` frontier param); surface it but it should be local.

## 6. Tools
lean-lsp MCP: `lean_diagnostic_messages` (scope; trust `items`), `lean_goal`,
`lean_multi_attempt`, `lean_hover_info`, `lean_verify` (axiom check; fully
qualified names — expect exactly `propext`/`Classical.choice`/`Quot.sound`).
