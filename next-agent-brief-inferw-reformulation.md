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

### 7c. UPDATE after the §7b attempt (subagent 2) — what's done + the real wall
- **DONE + committed (`a97fda4`):** removed unused `hrhs_lc` from `sound_letInAnn` (+ caller),
  deleted dead `skolem_no_env_leak_K`. `Infer.sound_closed` axiom-clean.
- **`inferCore_complete` annotated-let is the hard wall — it's the DUAL of issue 2a.**
  The producer solved 2a by letting completeness *choose* `Ys ∉ dom S₀`; but the executable
  `inferCore` **hard-codes `Ys = freshVars Φ pc` (N=Φ)** and can't choose, while the relation
  allows any `N ≥ Φ`. So the proof must bridge the executable's fixed block vs the relation's
  abstract `N`. The non-annotated cases (prim/var/ctor/lambda/pair/app/letIn-none) migrate
  mechanically (lambda seed → `Ty.bvarsBelow 0`; `genScheme` 3-arg `rhs.tyFreeVars`; thread
  `K`/`hSK`; a `Subst.fixes_fvar_of_avoids` helper). Two candidate unblocks, both real work:
  1. Add invariant `hS₀dom : ∀ p∈S₀, p.1 < Φ` to the executable-completeness predicate (then
     `Ys ≥ Φ ∉ dom S₀` automatically). Needs a NEW **residual-domain-bound** lemma (the `R`
     from `complete'`/`completeAt` has `dom R < Φ'`) so the invariant survives the
     second-subterm compositional cases — i.e. a new output conjunct threaded through
     `completeAt`/`complete'` (like the step-2 `S`-avoids-`K` threading).
  2. Rename the *given* derivation's block `N→Φ` (block-swap) + use `output_unique`/principality
     to reconcile the executable's deterministic re-inference. (More like what `complete'`'s
     `letInAnn` did.)
- **`OUnify.skolem_escape` is NOT dead** (the §7b "delete it" was WRONG): the executable `hesc1`
  needs the LEFT-LEANING `unifyCore` MGU to avoid `Ys`, which `complete_K` (existential,
  away-from-`K`) doesn't give. KEEP it; generalize its `b.freeVars ⊆ Ys` to `⊆ K∪Ys` and call
  at the rigid set `K∪Ys`. (`exists_skolem_unifier`/`skolem_no_env_leak` are still referenced by
  the red `inferCore_complete`; reassess after B.)
- **Big picture:** the RELATION metatheory is fully done + axiom-clean — soundness
  (`sound_closed`), completeness (`completeAt`), principality (`complete'`/`isPrincipal`/
  `output_unique`). Executable: soundness (`infer_sound`) done; the remaining red is the
  executable-refinement layer (`inferCore_complete` ← the wall above; then Stage C `typecheck`
  over erased programs, whose headline region is independently WIP: `genScheme` 3-arg,
  `IsTyErased` erasure on progress/preservation, an errored Stage-C theorem ~line 10760).

### 7d. UPDATE — the wall is CRACKED (locality lemma; block-swap is a dead-end)
- **Design decision (reasoned through with concrete examples):** the **block-swap** route
  (Approach A in §7c-style thinking) is a **DEAD END** for this wall. Cleaning `S`'s domain/range
  w.r.t. the executable block `Ys = freshVars Φ pc` via `Subst.conj (blockSwap …)` necessarily
  renames the env's occurrences of `Ys` — which, to keep a valid declarative typing, forces
  renaming the *subject*/*type*'s `Ys` too (to `freshVars W pc`). But the executable is **pinned**
  to `Ys = freshVars Φ pc`; the block cannot move. So §7c-path-1's `dom S₀ < Φ` also fails (the
  `completeAt` residuals are block-swap conjugates with huge domain `[W,W+pc)`). The viable route
  is **path 2-flavoured but realized via a structural locality lemma about the given derivation.**
- **DONE + committed (axiom-clean):**
  - `b98b39c` **`Infer.gap_avoid`** / `InferBranches.gap_avoid` (≈ line 9590): a derivation whose
    ctx env + annotation free vars avoid an interval `[lo,hi)` with `hi ≤ Φ` (gap *below* the input
    frontier) has output substitution **domain AND range** + result type all avoiding `[lo,hi)`.
    The `[lo,hi)` analogue of `belowFvars`, additionally bounding the substitution *domain*.
    Helpers: `Subst.onTy_avoidsItv`, `Subst.onCtx_avoidsItv`, `Ty.openWith_avoidsItv`,
    `UnifyRel.gap_avoid`/`UnifyRelList.gap_avoid`.
  - `bc41274` **`Infer.letInAnn_block_fresh`** (≈ line 10000): from a given `letInAnn` derivation,
    `(A) dom S avoids freshVars Φ pc` and `(B) (S.onCtx ctx).env avoids freshVars Φ pc`. Proof
    splits `freshVars Φ pc` at the derivation's own block start `N`: lower gap `[Φ,N)` → `gap_avoid`
    on rhs/Schk/body sub-derivations; upper part `[N,Φ+pc) ⊆ freshVars N pc` → `hesc1` (rhs/unify)
    + `gap_avoid` over the `hesc2`-cleaned body context. Also added `Subst.fixes_fvar_of_avoids`.
- **REMAINING (mechanical migration + assembly — the design is fully de-risked):**
  1. **`InferCoreComplete` predicate** (≈ line 10090): add `(K : List Nat)` + `(hKΦ : ∀ k∈K, k<Φ)`
     + `(hKe : ∀ y∈e.tyFreeVars, y∈K)` + `(hSK : ∀ p∈S, p.1∉K)` (mirror `CompleteAt`). Every case
     lemma then K-threads.
  2. **Mechanical cases** (prim/var/ctor: K unused; lambda/letIn-none/pair/app/fst/snd/match/
     branches): thread `K` to the `iha`/`ihb` recursive calls, to `Infer.sound h hwf K hKΦ hKe hSK`,
     to `Infer.belowFvars h hbelow (fun y hy => hKΦ y (hKe y …))` (now 3-arg), and switch
     `Infer.complete` → **`Infer.completeAt e K …`** (6-conjunct: it yields the "reconstructed S
     avoids K" needed to feed `ihb`). `Infer.complete'` calls take `K` + `hKΦ`/`hKe`/`hKfix`
     (`hKfix` from `Subst.fixes_fvar_of_avoids` on the per-subterm "S avoids K" split of `hSK`).
     The `complete'`/`completeAt` output is now a 5-/6-tuple — capture the extra `R`-fixes-`K` and
     `S`-avoids-`K` conjuncts.
  3. **`inferCore_complete` assembler** (≈ line 10580): restructure to **strong induction on
     `e.size`** (mirror `Infer.completeAt`, NOT `Expr.rec_strong`), so the annotated-`let` case gets
     `iha : ∀ Ys, InferCoreComplete (rhs.openTyVars Ys)` (via `Expr.size_openTyVars`). Make
     `inferCore_complete_letIn` take `(iha : InferCoreComplete rhs) (ihao : ∀ Ys, InferCoreComplete
     (rhs.openTyVars Ys)) (ihb : InferCoreComplete body)` (mirror `Infer.complete_letIn`).
  4. **Annotated-`let` assembly** (the only non-mechanical part, now de-risked): in
     `inferCore_complete_letIn`'s `letInAnn` case, with `Ys := freshVars Φ σ.paramCount`:
     - `happ := Infer.sound h hwf K hKΦ hKe hSK`; `cases happ` (Core `letIn`) → `hcofin` over the
       opened rhs; `hann σ rfl : M = σ`.
     - `⟨hAdom, hBenv⟩ := Infer.letInAnn_block_fresh h hbelow (htfv from hKΦ∘hKe)`.  ⇒ `S` fixes
       `K ∪ Ys` (K via `hSK`+`fixes_fvar_of_avoids`; Ys via `hAdom`).
     - `htyYs := typeOfHM_at_block (freshVars_length …) hcofin : TypeOfHM (S.onCtx ctx)
       (rhs.openTyVars Ys) (σ.openVars Ys)` — block-independent, free.
     - `Infer.completeAt (rhs.openTyVars Ys) (K ++ Ys) hwf hbelowN hSlc … htyYs` → `Drhs` +
       residual `R₁` (fixes `K∪Ys`, `σ.openVars Ys = R₁.onTy τ₁`) + **`S₁` avoids `K∪Ys`** (hesc1
       first half). Feed `Drhs` to `ihao Ys (K++Ys) …` ⇒ executable infers the opened rhs; use
       `Infer.output_unique` (needs `(rhs.openTyVars Ys).tyFreeVars = []`? NO — `output_unique`'s
       `hclosed` is too strong here; instead re-run `complete'`/`completeAt` directly on the
       executable's `hrhs'` at `K∪Ys`, OR thread the avoid-conjunct via `completeAt` and match by
       determinism using a `closed`-free principality variant — reconcile S₁'=S₁ etc.).
     - `unifyCore τ₁ (σ.openVars Ys)` succeeds with witness `U := R₁` (fixes `K∪Ys` ⊇ both fvars)
       via `unifyCore_complete_aux`; gives left-leaning `Schk'`.
     - `hesc1`: S₁' avoids `Ys` (from the `completeAt` avoid-conjunct) + `Schk'` avoids `Ys` via the
       **generalized `OUnify.skolem_escape`** (generalize its `b.freeVars ⊆ Ys` premise to `⊆ K∪Ys`;
       witness `U = R₁`).
     - `hesc2`: producer-style `V` argument (factor `R₁` through `Schk'` via `greatest_K`; `V` fixes
       `K∪Ys`; `V.onCtx (Schk'.onCtx (S₁'.onCtx ctx)) = S.onCtx ctx`); a leak would put `Y∈Ys` into
       `(S.onCtx ctx).env`, contradicting `hBenv`.
     - body: recast `hbodyD` over `V`, recurse `ihb K …` (via `completeAt` for the reconstructed body
       derivation + match), drive the executable arm (`dif_pos` for `hσwf`/`hesc1`/`hesc2`).
  5. **Headlines:** add `hclosed : e.tyFreeVars = []` to `infer_isPrincipal`/`principalType_*`/
     `infer_iff_typeable`/`typecheck_*` (closed programs ⇒ `K := []`, `output_unique`/`isPrincipal`
     already take `hclosed`). Then `lean_verify` the headlines axiom-clean.
  - Reassess deleting `exists_skolem_unifier`/`skolem_no_env_leak` only once `inferCore_complete` is
    off them (the assembly above no longer needs `exists_skolem_unifier`; `skolem_no_env_leak` is
    likely dead).

### 7f. RESOLVED — orientation wall closed by making the executable rigidity-aware
The §7e blocker had a clean, natural fix (the executable mirror of the relation's `complete_K`
reformulation), now implemented + committed + **validated by `#eval`**:
- `2be1cac` **`unifyCoreK`** (≈ line 9015): rigidity-aware decidable unifier — takes a rigid set `K`,
  orients away from it, carries `UnifyRel ∧ (S avoids K)`. With `K=[]` ≡ `unifyCore`.
- `23de728` **`inferCore`/`inferBranchesCore` thread `K`** and use `unifyCoreK K`; annotated-`let`
  infers the opened rhs at `K ++ freshVars Φ pc` (skolems rigid) and the body at `K`. `infer` runs at
  `K=[]`. `infer_sound` re-proved. **Validated:** the §7e counterexample now `#eval`s to
  `some (α→α)` (skolem kept rigid) instead of `none`.
- `f0ef0f8` **`inferCore`/`inferBranchesCore` carry `avoids K`** in their result subtype (free, like
  `unifyCoreK`) — so the annotated-`let` `hesc1` and sub-recursion rigidity are available directly.
- `3d2655d` **`unifyCoreK_complete`** (≈ line 9659): rigidity-aware unify completeness — a `K`-fixing
  LC unifier ⇒ `unifyCoreK K` succeeds (fuses `unifyCore_complete_aux`'s size induction with
  `complete_K_aux`'s orientation reasoning). Axiom-clean.
- **Net:** `inferCore_complete` is now a TRUE statement and all foundations are in place:
  `gap_avoid` + `letInAnn_block_fresh` (freshness), `unifyCoreK_complete` (rigidity-aware unify),
  carried `avoids K`.
- **`inferCore_complete` migration — IN PROGRESS (8/11 cases committed green):**
  - `InferCoreComplete` predicate is now `+K` (`(K : List Nat)` + `hKΦ`/`hKe`/`hSK`); executable call
    is `inferCore K Φ ctx e`; each result destructures the carried avoids `⟨(…), hInfer, hav⟩`.
  - DONE + committed: prim/var/ctor/lambda (lambda-some uses `hcl : IsLC` for WF, `hKΦ`/`hKe` for
    below, `dif_pos (Ty.bvarsBelow_iff …).mpr hcl`; reduce via `split` not `simp`),
    pair/app/fst/snd. `exists_app_unifier`/`exists_pair_unifier` extended with a `(∀k∈K, U fixes k)`
    output (hyps `hR₂K`/`hR₁K` + `hΦ₂K`/`hΦ₁K`); unify steps use `unifyCoreK_complete`.
    Pattern per compositional case: split `hKe`/`hSK`; `Infer.sound h hwf K …`; `Infer.complete' …
    K hKΦ hKe (fixes_fvar_of_avoids …)`; `Infer.belowFvars … (fun y hy => hKΦ y (hKe y hy))`;
    `Infer.completeAt` (NOT `complete`) to reconstruct the 2nd subterm + get its `S avoids K` for the
    sub-IH; unify via the K-fixing `exists_*_unifier` + `unifyCoreK_complete`.
  - REMAINING (mechanical, same pattern):
    1. **`inferBranchesCore_complete`** (predicate `InferBranchesCoreComplete` `+K`; `InferBranches.sound`
       already takes `K`/`hKΦ`/`hKbr`/`hSK`; `InferBranches.belowFvars` is 4-arg with a `htfv`;
       `InferBranches.complete` threads `K`; unify via `unifyCoreK_complete` — the branch-body unify
       `unifyCore τb (S₁.onTy ρ)`'s K-fixing unifier is `R_b` (the `greatest_lc`/`complete'` residual,
       which fixes `K`)).
    2. **`inferCore_complete_match`**: like app but with the doubled manual unifier `U` (the
       `freshVars … zip` block); extend its construction with a `U`-fixes-`K` fact (`R₁` fixes `K`,
       the `freshVars Φ₁ …`/`freshVars W₀ …` are `≥ Φ₁ > K`) and call `unifyCoreK_complete`.
    3. **`inferCore_complete_letIn`**: `iha`/`ihao`/`ihb` IHs (size induction in the assembler). none =
       like pair (3-arg `genScheme rhs.tyFreeVars`). ann = the assembly: `Ys := freshVars Φ pc`;
       `Infer.sound h` → cofinite; `typeOfHM_at_block` → `TypeOfHM (S.onCtx ctx) (rhs.openTyVars Ys)
       (σ.openVars Ys)`; `⟨hAdom,hBenv⟩ := Infer.letInAnn_block_fresh h hbelow (htfv from hKΦ∘hKe)`;
       reconstruct opened rhs via `Infer.completeAt … (K++Ys) … (S fixes K++Ys via hSK + hAdom)`; feed
       to `ihao Ys (K++Ys)`; `hesc1` from the carried avoids of the rhs result (`inferCore (K++Ys)` ⇒
       `S₁ avoids K++Ys ⇒ avoids Ys`) + the `unifyCoreK (K++Ys)` result's carried avoids (`Schk` avoids
       Ys); `hesc2` via the producer `V`/`greatest_K` argument + `hBenv`; recurse `ihb K`; drive the
       executable arm (the `if hσwf`/`if hesc1`/`if hesc2` all now provably pass).
    4. **assembler `inferCore_complete`**: strong induction on `e.size` (mirror `Infer.completeAt`),
       passing `inferCore_complete_letIn (iha) (fun Ys => …) (ihb)`.
    5. **headlines**: `infer_complete`/`infer_iff`/`infer_iff_typeable`/`principalType_*`/`typecheck_*`/
       `infer_isPrincipal` — add `hclosed : e.tyFreeVars = []` (closed top-level ⇒ `K:=[]`;
       `inferCore_complete e [] … (by simp)/(by simp[hclosed])/(by simp)`); `output_unique`/`isPrincipal`
       already take `hclosed`.
- NOTE: `OUnify.skolem_escape`, `exists_skolem_unifier`, `skolem_no_env_leak` are now superseded by
  `unifyCoreK` — delete once `inferCore_complete` no longer references them.

### 7e. (historical) `inferCore_complete` was FALSE for the pre-fix executable (ORIENTATION WALL)
While building the §7d.4 assembly, found (and **empirically confirmed via `#eval`**) a second,
*deeper* obstacle that the freshness lemmas do **not** fix and that **no proof can fix**: the
executable `inferCore` rejects a typeable program.

- **Counterexample (verified `#eval infer 0 ⟨[],[]⟩ … = none`):**
  `let f : ∀a.(a→a) = (λw. (λ(z:a).z) w) in f`
  i.e. `.letIn (some ⟨1, .arrow (.bvar 0) (.bvar 0)⟩)`
  `      (.lambda none (.app (.lambda (some (.bvar 0)) (.var 0)) (.var 0))) (.var 0)`.
  Control `let f : ∀a.(a→a) = (λ(z:a).z) in f` ⇒ `some (α→α)` (works — trivial scoped use).
- **Why.** D2 infers the *opened* rhs `rhs.openTyVars Ys` (`Ys = freshVars Φ pc` the skolems) with
  the skolems already present. Inside the rhs, the app `(λ(z:a).z) w` unifies the function domain
  `fvar Y` (skolem, on the LEFT) with the flexible arg var `fvar X` (`X > Y`). The executable's
  **left-leaning** `unifyCore (.fvar Y) (.fvar X)` always binds the LEFT var ⇒ `[(Y, fvar X)]`,
  i.e. it binds the skolem. So the rhs substitution `S₁` has `Y ∈ dom S₁`, the rule's own
  `hesc1` (`Ys ∉ (S₁++Schk).map fst`) fails, and `inferCore` returns `none`. The **relation**
  `Infer` accepts (its `UnifyRel (.fvar Y) (.fvar X)` may choose `fvarR ⇒ [(X, fvar Y)]`, keeping
  `Y` rigid; `Infer.completeAt` is proven, and the declarative `TypeOfHM` accepts). Hence
  relation-complete but executable-incomplete ⇒ `inferCore_complete` (relation ⇒ executable) is FALSE.
- **Scope.** Triggers whenever a scoped-typed value is *used* (applied/projected) against a flexible
  type inside the rhs — a broad class, not a corner case. `OUnify.skolem_escape` only saves the
  *final* `unifyCore τ₁ (σ.openVars Ys)` step (there `b = σ.openVars Ys` is all-skolems, so skolems
  sit on the RIGHT and `fvarR`/refl keep them rigid). It does NOT help the rhs's *internal*
  unifications, where skolems can be on the left.
- **The fix is a DESIGN change to the executable, not a proof.** `inferCore`'s rhs inference must use
  **rigidity-aware unification** that knows the skolem block `K ∪ Ys` and orients away from it
  (refuses to bind a rigid var; binds the other side; fails on rigid-vs-nonvar). I.e. give `inferCore`
  a rigid-set parameter and a `unifyCoreK`/decidable analogue of `UnifyRel.complete_K`, threaded
  through the opened-rhs inference (and re-prove `infer_sound`). This is the executable mirror of the
  reformulation that fixed the *relation*. Only AFTER that does `inferCore_complete` become true, and
  the §7d migration (predicate K-threading + the §7d.4 assembly using `gap_avoid`/`letInAnn_block_fresh`)
  applies.
- **Net status of this session.** Committed + axiom-clean: `Infer.gap_avoid` (locality) and
  `Infer.letInAnn_block_fresh` (the freshness bridge: given derivation's `S` leaves `freshVars Φ pc`
  rigid in domain + env-range). Block-swap ruled out as a dead end. These are necessary for the
  eventual executable-completeness proof but **not sufficient** — the orientation wall above must be
  closed first by making the executable rigidity-aware. The §7d.4 partial case-migration (K-threading
  of prim/var/ctor/lambda/pair/app/letIn-none) was drafted and green but reverted, since it targets a
  statement that is currently false; redo it once the executable is rigidity-aware (the recipe in §7d
  still applies, plus each unify step in app/fst/snd/match must use the rigidity-aware unifier).
