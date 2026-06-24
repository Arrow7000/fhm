<!-- Handoff brief written mid "scoped type variables → InferW Stage 1" session.
     Supersedes next-agent-brief-inferw.md for the *current* state.
     Companion north-star: next-agent-brief-surface-lang.md. -->

# Handoff: finish Stage 1 (Infer.sound), then completeness, then typecheck

## 0. Workflow the user wants (please follow, in order)

1. **Orient first.** Read this brief end-to-end. Then look around with the lean-lsp MCP
   (read, don't just grep): the new machinery in `FHM/Core.lean`
   and the work-in-progress in `FHM/InferW.lean`. Both are
   **uncommitted** right now (see §0a).
2. **Design soundness-critical moves with the user before a big implementation push.**
   The remaining `Infer.sound` rewrite (§4) is the soundness crux. The *algorithm*
   design is settled and validated; the *proof architecture* (the ambient-skolem `K`
   threading) is described below and was agreed with the user — but if you discover it
   needs to change, surface that before barrelling in.
3. **Be merciless about correctness, never cosmetic.** No `sorry`/`axiom`/`native_decide`,
   no weakening of headline statements to force green. If something can't be proven
   honestly, say so and report the real obstacle. Verify with `lean_verify` (axioms must
   be exactly `propext`/`Classical.choice`/`Quot.sound`).

## 0a. Environment gotchas (these bit us)

- **Core is uncommitted+modified, and its `.olean` is freshly built to match.** Don't be
  confused that `git status` shows `Core.lean` dirty — it is green and axiom-clean, and
  the on-disk olean is current with it (I rebuilt it). InferW currently sees the new Core.
- **After ANY further Core edit, rebuild Core's olean and restart the LSP**, or InferW
  shows stale "fake green". The whole-project `lake build` / MCP `lean_build` **fails on an
  UNRELATED pre-existing-broken file `Experiments/Filterings.lean`** (nothing to do with
  us — do NOT try to fix it). So target Core directly:
  `lake build FHM.Core` (shell, ~35s), then MCP `lean_build`
  (restarts the LSP; it will still "fail" on Filterings — ignore that). Then verify the
  new Core symbols resolve from InferW.
- **Termination diagnostics are enormous** for the mutual `Infer`/`InferBranches`
  theorems (pages of `invImage`/`PSigma` dumps). When a `decreasing_by` goal is unsolved,
  the *actual* goal is the last line of the dump (e.g. `⊢ body.size < Expr.sizeBranches brs`).
- **`lean_diagnostic_messages`: trust the `items` array, not the whole-file `success`**
  (it reports false while *any* part of the file is red). Scope queries with line ranges.

## 1. Big picture
North star (the eventual destination, NOT this task): a verified **surface HM language**
on top of this de Bruijn core (see `next-agent-brief-surface-lang.md`). **Scoped type
variables** (referencing a signature's type variable inside its body, à la GHC
`ScopedTypeVariables`) are the prioritized prerequisite, and they are *already done at the
declarative + dynamic level in Core* (committed earlier). This task is making the
**algorithm `Infer` (Algorithm-W) accept and stay sound for** scoped type variables, in
three stages: **(1) soundness**, **(2) completeness/D4**, **(3) the `typecheck` API /
erasure**. The user wants ALL THREE finished (completeness included — "no Swiss cheese")
before the surface language.

## 2. DONE this session (uncommitted; all the items below are green + verified)

### Core.lean additions (axiom-clean: `propext`/`Classical.choice`/`Quot.sound`)
- **The rename bridge** — the key fact for scoped-var soundness: opening a term at one
  skolem block `Ys`, then renaming `Ys ↦ Xs`, equals opening directly at `Xs`.
  - `Expr.substTyFvars_zip_openTyVars` (top level) and `…_openTyVarsAux` (depth-general),
    `Ty.substFvars_zip_openVarsFrom` (type level), plus the `Expr.substTyFvars`
    structural-distribution lemmas (`_pair/_app/_fst/_snd/_lambda/_letIn/_match`) and the
    private `BranchList.substTyFvar_eq_map` / `BranchList.openTyVarsAux_eq_map` helpers.
- **A well-founded measure for derivation recursion**: `Expr.size` / `Expr.sizeBranches`
  (mutual; **ignores type annotations**) and `Expr.size_openTyVars` /`…_openTyVarsAux`
  (invariance under opening — proven where `BranchList.openTyVarsAux` is in scope).

### InferW.lean changes (the new rule + repaired invariants)
- **`LamSeed.some` relaxed** from `Ty.isClosed T` to `T.IsLC` (annotation must be
  locally closed but **may carry free scoped vars**). New helper `LamSeed.pt_isLC`;
  `LamSeed.ann_openVarsFrom` re-proven; **deleted** the now-false `LamSeed.ann_freeVars_nil`.
- **`Infer.letInAnn` reordered (D2)** — the headline algorithm change:
  ```
  | letInAnn {Φ ctx σ rhs body Φ₁ Φ₂ S₁ Schk S₂ τ₁ τ₂} :
      σ.WF →
      Infer (Φ + σ.paramCount) ctx (rhs.openTyVars (freshVars Φ σ.paramCount)) Φ₁ S₁ τ₁ →
      UnifyRel τ₁ (σ.openVars (freshVars Φ σ.paramCount)) Schk →
      (∀ y ∈ freshVars Φ σ.paramCount, y ∉ (S₁ ++ Schk).map Prod.fst) →
      (∀ y ∈ freshVars Φ σ.paramCount, y ∉ (Schk.onCtx (S₁.onCtx ctx)).env.freeVars) →
      Infer Φ₁ { (Schk.onCtx (S₁.onCtx ctx)) with
                 env := σ :: (Schk.onCtx (S₁.onCtx ctx)).env } body Φ₂ S₂ τ₂ →
      Infer Φ ctx (.letIn (some σ) rhs body) Φ₂ (S₁ ++ Schk ++ S₂) τ₂
  ```
  i.e.: skolems `Ys = freshVars Φ σ.paramCount` allocated **first**; the bound expression
  is inferred **already opened at `Ys`** (`rhs.openTyVars Ys`, matching the spec's
  `openBoundTyVars`); `σ.WF` only (**`NoFreeVars σ.body` dropped** — σ may mention outer
  scoped vars); the escape now covers the **whole** `S₁ ++ Schk` (not just `Schk`).
- **`Infer.frontier_le`/`InferBranches.frontier_le` and `Infer.lc`/`InferBranches.lc`
  re-proven** against the new rule. The reorder broke Lean's automatic term-size
  termination (the opened rhs `rhs.openTyVars Ys` is not a structural subterm), so these
  now use:
  ```
  termination_by e.size                       -- Infer.*  (Expr.sizeBranches brs for InferBranches.*)
  decreasing_by
    all_goals (simp_wf; try subst_vars;
      try simp only [Expr.size, Expr.sizeBranches, Expr.size_openTyVars]; omega)
  ```
  (`subst_vars` is needed because `cases h` leaves the measure var unsubstituted.)
- **Deleted** the obsolete closed-regime invariants `Infer.tyFreeVars_eq_nil`,
  `InferBranches.tyFreeVars_eq_nil`, and the `sorry`-gated `Infer.openTyVarsAux_eq_self` /
  `Infer.openTyVars_eq_self`. **The single `sorry` is gone.**

## 3. The design to internalize

- **Algorithm (D2):** check the bound expression opened at rigid skolems; keep skolems
  rigid via escape-checking the whole rhs+unify substitution. Outer scoped vars appear as
  free `fvar`s in inner annotations/signatures and must also stay rigid — but they're
  guarded by *their own* enclosing `let`'s escape (the discipline stays local).
- **Soundness via an ambient rigid-skolem set `K` (the crux, §4).** Because the bound
  expression is now inferred *opened*, accepted terms have non-empty annotation free vars
  (the in-scope skolems). The old "term has no free vars, so any subst fixes it" discharge
  is dead. Replace it by threading a set `K ⊇ e.tyFreeVars` with the invariant "the
  substitution `S` avoids `K`" (`∀ p ∈ S, p.1 ∉ K`). Sub-substitutions inherit "avoids
  `K`" (their domains ⊆ `S`'s), so `TypeOfHM.onSubst_fixed` discharges every node; each
  `letInAnn` extends `K` by its new `Ys` using the escape. The cofinite spec premise is
  recovered by renaming `Ys → Xs` via the Core **rename bridge**.
- **Runtime = erased.** Naive scoped annotations break subject reduction
  (`Core.preservation_is_unsound`); the fix is "check with annotations, run erased". Core
  already has `erased_type_safety`/`_star`, `eraseTyAnnots`, and `progress`/`preservation`
  carrying an `IsTyErased` premise. The *static* algorithm is unaffected by erasure.

## 4. NEXT (immediate): rewrite `Infer.sound` (Stage 1 finish)

Currently red (they reference deleted lemmas and the old rule shape): `Infer.sound`,
`InferBranches.sound`, and the helpers `Infer.sound_letInAnn`, `hasSchemeVars_of_fresh_opening`,
`Infer.sound_fst/_snd`, `Infer.sound_letIn`.

Plan:
1. **Restate the mutual `Infer.sound`/`InferBranches.sound`** to carry `K`, e.g.
   `Infer.sound : Infer Φ ctx e Φ' S τ → CtxWF ctx → (K : List Nat) →
     (∀ y ∈ e.tyFreeVars, y ∈ K) → (∀ p ∈ S, p.1 ∉ K) → TypeOfHM (S.onCtx ctx) e τ`,
   proven by `cases h` with `termination_by e.size` + the same `decreasing_by` as
   `frontier_le`/`lc`. Each non-letInAnn case: push the threaded subst through sub-results
   with `TypeOfHM.onSubst_fixed` + `Expr.substTyFvars_eq_self_of_not_mem_tyFreeVars`
   (sub-term's tyFreeVars ⊆ K; the relevant subst avoids K).
2. **`letInAnn` case:** `Ys = freshVars Φ σ.paramCount`. The rhs is inferred opened at
   `Ys`; its soundness gives `TypeOfHM … (rhs.openTyVars Ys) τ₁` for the rhs subtree under
   `K ∪ Ys` (escape ⇒ `S₁ ++ Schk` avoid `Ys`; parent gives avoid `K`). Push `Schk`
   through (it fixes `σ.openVars Ys` because it avoids `Ys`), unify to get
   `TypeOfHM … (rhs.openTyVars Ys) (σ.openVars Ys)`, then **rename `Ys → Xs`** for the
   cofinite premise via `Expr.substTyFvars_zip_openTyVars` (term) +
   `Ty.openWith_eq_substFvars_openVars` (type) + `TypeOfHM.typ_substs_preservation`.
3. **Generalize `hasSchemeVars_of_fresh_opening`**: its rename step used
   `Expr.substTyFvars_eq_self_of_tyFreeVars_nil` (closed rhs). Replace with the bridge so
   `(rhs.openTyVars Ys).substTyFvars [Ys↦Xs] = rhs.openTyVars Xs`.
4. **Drop the closed-σ assumptions**: `Subst.onPolyTy_eq_self_of_closed hσnfv` no longer
   applies (σ may have free outer scoped vars ⊆ K). Handle σ's free vars via the K
   invariant too.
5. **Top-level wrapper:** for a closed program (`e.tyFreeVars = []`), instantiate `K = []`
   to recover the plain `TypeOfHM (S.onCtx ctx) e τ`. NOTE: the headline `Infer.sound`
   signature changes (adds `K` + 2 hyps, or expose a closed-`e` corollary), so its callers
   (`Infer.principal`, `infer_sound`/typecheck) will need updating — but those are Stage 2/3
   and already red, so fix them there.
6. **Verify** `lean_verify` on `Infer.sound` → no `sorryAx`.

Concrete sanity programs to keep in mind: `let id : ∀a. a→a = λ(x:a).x in id 3` (accept,
`Int`); `let f : ∀a. a→a = λ(x:a).x+1 in …` (REJECT — body pins the skolem; escape catches
it); nested `let outer : ∀a. a→a = λ(x:a). (let inner : a→a = λ(y:a).y+1 in x) in …`
(REJECT — caught by `outer`'s escape on its whole rhs subst).

## 5. THEN: Stage 2 (completeness/D4) and Stage 3 (typecheck/erasure)

Currently red, in dependency order after soundness:
- **`Infer.belowFvars`/`InferBranches.belowFvars`** — same termination fix as
  `frontier_le`/`lc` (convert to `Expr.size` measure) + new-rule `letInAnn` pattern.
- **Completeness** (`Infer.complete'`, `complete_letIn_ann_aux`, `typeOfHM_at_block`,
  `Infer.complete`/`complete_instance`, `Infer.principal`): repair for the new Core spec
  (the `hMσ`/`hpeq` breakages came from the dropped-`NoFreeVars` `letIn` rule) and the new
  reordered `letInAnn`. **D4 = `exists_skolem_unifier`** is the riskiest single piece:
  today it assumes the rhs principal type is disjoint from the skolems; once the rhs can
  mention skolems that's false — rework it to split `τ₁.freeVars` into skolems ⊎ residue
  and build a skolem-fixing unifier tolerating skolems on both sides. **Design it on paper
  with the user before coding.**
- **Stage 3 — `typecheck_*`:** `typecheck_progress`/`typecheck_preservation` call Core's
  `progress`/`preservation` *without* the now-required `IsTyErased` argument. Restate them
  over the *erased* program (model on Core's `TypeOfHM.erased_type_safety`). These can NOT
  be "re-proven unchanged" — subject reduction is false with annotations present.

## 6. Reservations / concerns
- **The K-threading soundness proof is the soundness-risk zone.** Get the escape/`K`
  discipline wrong and `Infer.sound` becomes false or unprovable. The `letInAnn` case +
  `hasSchemeVars_of_fresh_opening` generalization are where to be careful.
- **D4 is the riskiest single piece** — expect to iterate; design before coding.
- **Honest sizing:** soundness ≈ 1 focused session; completeness/D4 ≈ 1–2 (D4 is the
  unknown); typecheck/erasure ≈ small. Stage it; validate each stage axiom-clean; report
  cleanly. Decline/report beats a half-baked push.
- **Mutual-inductive recursion**: `induction h` does NOT work on `Infer`/`InferBranches`
  ("does not support mutually inductive"). Use `cases h` + the `Expr.size` termination
  pattern (keeps existing proof bodies), or `induction h using Infer.rec (motive_2 := …)`
  if you need real IHs.

## 7. Tools / verification
lean-lsp MCP: `lean_diagnostic_messages` (scope with line ranges; trust `items`),
`lean_goal`, `lean_multi_attempt`, `lean_hover_info`, `lean_verify` (axiom check; fully
qualified names). For Core rebuilds use the targeted shell build + `lean_build` per §0a;
avoid gratuitous whole-project builds (they fail on `Filterings.lean`).
