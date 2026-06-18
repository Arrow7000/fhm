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

## 2b. Step-3 design, fully nailed down (do this next)
Reading Core + `sound_letInAnn` settled every open question for `complete_letIn_ann_aux`:
- **Core's `letIn` (Core.lean ~1761) allows scoped `σ`.** Premises: `M.WF`,
  `hann : ∀ σ, ann = some σ → M = σ` (scheme *is* the annotation; **no
  `NoFreeVars`** — free vars of `σ.body` are scoped vars ⊆ `K`), and the cofinite
  premise is over the **opened** rhs:
  `∀ Xs fresh, TypeOfHM ctx (Expr.openBoundTyVars ann Xs rhs) (M.openVars Xs)`,
  where `openBoundTyVars (some σ) Xs rhs = rhs.openTyVars Xs`. So the declarative
  input for the opened rhs is **free** — no `typeOfHM_at_block` rename. The
  current dispatcher's `obtain ⟨hMσ, hσnfv⟩ := hann σ rfl` is **stale** (hann is a
  single `M = σ`, not a pair) — fix it to `have hMσ := hann σ rfl; subst hMσ`.
- **`completeAt` → strong induction on `e.size`** (NOT `Expr.rec_strong`, NOT
  `TypeOfHM.rec_strong`). Pattern: prove `∀ n, ∀ e, e.size ≤ n → CompleteAt e` by
  `induction n`; each case derives its sub-`CompleteAt`s from the size-IH. This is
  the *only* place that changes; the standalone case lemmas keep taking
  `CompleteAt subterm`. (`TypeOfHM.rec_strong` would force restating the whole
  producer in derivation-motive form *and* fights `CompleteAt`'s `S₀`/`ctx`/`K`
  abstraction — rejected.) `Expr.size_openTyVars` (Core) gives
  `(rhs.openTyVars Ys).size = rhs.size`, so the size-IH reaches the opened rhs.
- **`complete_letIn_ann_aux` new signature**: `iha : ∀ Ys, CompleteAt (rhs.openTyVars Ys)`,
  `ihb : CompleteAt body`, hyps `hKrhs/hKbody/hKσ : … ⊆ K`, `hKfix`, `hσwf`,
  `hcofin : ∀ Xs fresh, TypeOfHM (S₀.onCtx ctx) (rhs.openTyVars Xs) (σ.openVars Xs)`,
  `hbody`. Output = the 6-conjunct `CompleteAt` shape.
- **Body of the proof** (use `sound_letInAnn`'s signature as the checklist of
  facts to produce):
  1. pick `N ≥ Φ` with `Ys := freshVars N pc` disjoint from `dom S₀` **and**
     `S₀`'s range (and `ctx`); `S₀` then fixes `K ∪ Ys`.
  2. `iha Ys (K∪Ys) … (hcofin Ys)` → `Drhs : Infer (N+pc) ctx (rhs.openTyVars Ys) Φ₁ S₁ τ₁`,
     residual `R₁` fixing `K∪Ys`, `htya : σ.openVars Ys = R₁.onTy τ₁`,
     and **`S₁` avoids `K∪Ys`** (step-2 conjunct ⇒ hesc1's `S₁` half).
  3. `U := R₁` unifies `τ₁` with `σ.openVars Ys` (R₁ fixes `K∪Ys` ⊇ both sides'
     fvars); `complete_K … U …` → `Schk` with **`Schk` avoids `K∪Ys`** (⇒ hesc1's
     `Schk` half + `hSchkK`).
  4. **hesc2 — direct argument (do NOT use `skolem_no_env_leak_K`).** That kernel
     assumes `Ys ≥ Φ₁` (skolems above the rhs *output* frontier — the OLD
     surface-rhs design). The relaxed rule infers the *opened* rhs, so `Ys` is
     allocated *before* it ⇒ `Ys < N+pc ≤ Φ₁`; the kernel is **unfit** and is
     deleted unused. Instead: let `V` be the `greatest_K` factor of `R₁` through
     `Schk` (`V∘Schk = R₁` below `Φ`, `V` fixes `K`). `V` also **fixes each
     `Y∈Ys`** (`Schk` fixes `Y` by hesc1 + `R₁` fixes `Y`). If `Y ∈
     (Schk.onCtx (S₁.onCtx ctx)).env.freeVars`, then `Y ∈ (V.onCtx …).env =
     (S₀.onCtx ctx).env` (the `hmain` identity), which avoids `Ys` because
     `ctx`'s fvars `< Φ ≤ N` and **`S₀`'s range avoids `Ys`** (freshness choice).
     Contradiction. ~15 lines, reusing the `V` needed for the body anyway. No
     second opening, no renaming.
  5. body: factor `R₁` through `Schk` via `greatest_K` → `V` (fixes `K`); recast
     `hbody` over `V.onCtx {σ :: Schk.onCtx (S₁.onCtx ctx)}` (σ fixed since
     `σ.body.freeVars ⊆ K`, `V`/`S₂` avoid `K`); `ihb K … hbodyV` → `Dbody`,`S₂`,`R₂`.
  6. assemble `Infer.letInAnn hσwf (Φ≤N) Drhs huni hesc1 hesc2 Dbody`; agreement +
     `τ₀ = R₂.onTy τ₂` mirror `complete_letIn_aux`; output `S = S₁++Schk++S₂`
     avoids `K` from S₁/Schk/S₂ avoidances.
- **Delete once unused**: `exists_skolem_unifier`, the `OUnify.skolem_escape`
  mutual, the old `skolem_no_env_leak`, **`skolem_no_env_leak_K`** (unfit — see
  point 4), `typeOfHM_at_block` (the red one).

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

## 7. STATUS (live) — what's green vs. what remains

**Axiom-clean + committed:** the whole completeness *producer* — `Infer.completeAt`
(via `completeAt` size-induction, the relaxed `letInAnn`, the rigidity-aware
`complete_K`, and `complete_letIn_ann_aux`) — plus the headlines `Infer.complete`
/`complete_instance`/`complete_id`/`iff_typeable`/`principal` (they carry `K`;
the closed/identity ones instantiate `K:=[]`). Soundness (`Infer.sound_closed`).
The executable `inferCore`/`infer`/`infer_sound` (annotated-let arm realigned to
the relaxed rule; lambda checks `Ty.bvarsBelow 0`; unannotated-let `genScheme` gets
the `rhs.tyFreeVars` rigid arg; `termination_by e.size`). `typeOfHM_at_block`
(fixed to the opened-rhs/scoped-σ cofinite shape).

**Still RED (the remaining work, in order):**

### 7a. `Infer.complete'` / `InferBranches.complete'` (mutual, ~6396–7594) — the big one
"Principality of a *given* derivation": `(h : Infer …) → typing → ∃ R, AgreesBelow ∧
τ₀=R.onTy τ ∧ R lc`. Atomic mutual (no partial commits). Needed by `output_unique`
→ `isPrincipal` → `infer_principal`, and by `inferCore_complete`. Cannot be derived
from `completeAt` (circular via `output_unique`). **Migration:**
- **Signature**: add `(K : List Nat)` + `(hKΦ : ∀ k∈K, k<Φ)` +
  `(hKe : ∀ y∈e.tyFreeVars, y∈K)` + `(hKfix : ∀ k∈K, S₀.onTy (.fvar k)=.fvar k)` to
  both `complete'` and `InferBranches.complete'` (mirror `CompleteAt`'s preconds).
- **`belowFvars` calls** (e.g. 6610/6622/6731/6801/6879/7064): now 3-arg — pass
  `htfv := fun y hy => hKΦ y (hKe y hy)` (split `hKe` per sub-expr first).
- **prim×5**: signature only (K unused).
- **var/ctor**: `Infer.complete_var K hwf hbelow hS₀ hKΦ hKe hKfix hty` (hKe vacuous,
  `(var i).tyFreeVars = []`); destructure the 6-tuple ignoring the last two
  (`R-fix-K`, `S-avoids-K`): `⟨_,_,_,R,hinf,hag,hfac,hRlc,_,_⟩`.
- **pair / letIn-none / app / fst / snd / match**: thread `K` through the recursive
  `complete'` calls (sub-expr `tyFreeVars ⊆ K` via the `hKe` split) + the
  `belowFvars` `htfv`. The `app`/`fst`/`snd`/`match` manual-`U` + `greatest_lc`
  factoring is UNCHANGED (these factor the *given* MGU `Duni`, no `complete_K`).
- **lambda-none** (~6479–6602): K-thread the conjugated-spec recursion; `K`-vars
  `< Φ` are untouched by the swap `Φ↔W` (W,Φ chosen ≥ everything). `hKfix` for the
  conjugated `S₀` follows since the swap fixes `<Φ` vars.
- **lambda-some** (~6445–6478): **REWORK** for scoped `T` (`LamSeed.some T (_:T.IsLC)`,
  `T.freeVars ⊆ K`). Mirror `complete_lambda_ann_aux`: `hself : S₀.onTy T = T` from
  `hKfix`+`hTK`; recurse `complete'` on body at `K`; no `NoFreeVars`.
- **letInAnn** (~6787–6865): **REWRITE** for the relaxed rule. New `cases` pattern
  `| letInAnn Drhs hΦN huni hesc1 hesc2 Dbody` (N abstract, no `hσnfv`). From Core's
  `letIn`, `hann σ rfl : M = σ`; `hcofin` is over the opened rhs. Get the typing at
  the derivation's own block `Ys = freshVars N pc` via the FIXED `typeOfHM_at_block`
  (no more `hσnfv`); recurse `complete'` on `Drhs` at `K ∪ Ys`; factor `R₁` through
  `Schk` (`greatest_lc` — `huni` is given). Reuse the producer's `V`/`hmain` shape
  for the body. Delete the old `exists_skolem_unifier` path here.
- **InferBranches.complete'** (nil/cons): thread `K` (mirror `InferBranches.complete`).

### 7b. After `complete'` is green
- `output_unique` (7599), `isPrincipal` (7617): pass `K:=[]` for closed `e` (add a
  closure hyp or carry `K`); `infer_principal` (≈9121) follows.
- `inferCore_complete` (≈9335+): migrate like `complete'` (it also uses the old
  escape lemmas at ≈9657/9668/9677/9682/9692) → off the escape lemmas.
- **Delete** now-dead lemmas: `exists_skolem_unifier`, the `OUnify.skolem_escape`
  mutual, `skolem_no_env_leak`, `skolem_no_env_leak_K`.
- Stage C: `typecheck` over the *erased* program + final headline; `lean_verify`.
