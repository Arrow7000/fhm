<!-- Written 2026-07-14: audit of work + models after commit 6522862.
     UPDATED 2026-07-14 ~11:40: incorporate f762950 (annotated/poly WT + demos). -->

# Report: work and models since `6522862`

**Scope:** everything after `6522862` (`briefs: surface-bridge follow-ups; fix stale SurfaceBridge header`, 2026-07-11 00:50) through `f762950` (2026-07-14 11:40).

**Sources:** `git log 6522862..HEAD`, briefs created/updated in that range, Cursor agent transcripts under `~/.cursor/projects/Users-aron-dev-fhm/agent-transcripts/`. Episodic-memory MCP was unavailable (Node ABI mismatch on `better-sqlite3`).

**Changelog of this report:** first draft covered through `74e4c2f` (12 commits). Updated after `f762950` closed Approach A / 1a’s remaining annotated/poly gap and added surface→eval demos.

---

## A) Model switch — is “Opus → Grok 4.5 for the last N commits” right?

### Short answer

**Partially.** There are now **13 commits** after `6522862`. The switch is real for **heavy Lean proving** on Jul 13–14 (SCC + SurfaceWT corollary), but it is **not** a clean “parent chat became Grok instead of Opus for everything.” The newest commit (`f762950`) was actually **Composer-only** for proofs — Grok was the stated fallback and was never needed.

What the transcripts support:

| Layer | Switched to Grok 4.5? | Confidence |
|-------|----------------------|------------|
| **Proof subagents** (meaty Lean) | **Mostly yes** Jul 13–14 (`cursor-grok-4.5-high` / `grok-4.5-xhigh`); **Composer** finished `f762950` | High |
| **Research / smaller proofs** | **No** — stayed on **Composer 2.5** (`composer-2.5-fast`) | High |
| **Adversarial review** | **No** — **GLM 5.2** (`glm-5.2-max`) once | High |
| **Parent / orchestrator chat** | **No positive evidence of Grok**; still looks like a separate supervisor (last explicit identity: Opus 4.8 just before / at the `6522862` boundary). This report’s own parent chat (`a4a729f2`) *was* Grok 4.5. | Medium–High |

### What the data can and cannot prove

- Parent JSONL transcripts **do not store** system prompts or parent model slugs (`role` is only `user` / `assistant` / `turn_ended`). So “parent = Opus” after `6522862` is **inferred**, not logged — except when the session itself is known (e.g. this audit chat).
- Subagent model choice **is** logged via `Task` `"model":"…"` fields.
- Last **explicit parent identity** in-repo before this audit: session [`5cab47ef`](5cab47ef-d51a-498c-ba81-65b56fa41746) (boundary / pre-`6522862`): user said *“you're back to being **opus 4.8**”*. No later user message says *“you're grok now”* / *“switched parent to grok”* for the implementer sessions.

### Established workflow (Jul 11–14)

User policy stated early in the post-`6522862` arc ([`1e9914ae`](1e9914ae-e3fc-4d0b-add8-07f2a446d29c)):

> meaty work → **grok 4.5 xhigh**; smaller → **composer 2.5**; parent owns high-level spec and gates.

Operational ladder that stuck:

1. Parent freezes theorem / Prop statements (often edits `SurfaceBridge` / briefs directly).
2. **Composer 2.5** first for research, scaffolding, smaller lemmas, lint cleanup.
3. Escalate to **Grok 4.5** when Composer stalls or the proof is meaty (reachability/Kahn, `compile_initMatrix_typeable`, SurfaceWT corollary headlines).
4. Prefer in-Cursor **`cursor-grok-4.5-high`** over third-party Grok when farming from Cursor (explicit Jul 13 request in [`7bd8f687`](7bd8f687-0b33-41b2-ab5a-10fccfc61069)).
5. Occasional **GLM 5.2** adversarial review; one brief Sonnet 5 farm attempt was rejected in favour of Grok.
6. **`f762950` exception that proves the rule:** parent said “composer, grok if composer fails”; all four proof farms succeeded on Composer — no Grok dispatch.

### Subagent model dispatch counts (parent Task.model)

| Session | Date | composer-2.5 | grok-4.5* | other |
|---------|------|--------------|----------|-------|
| [`1e9914ae`](1e9914ae-e3fc-4d0b-add8-07f2a446d29c) | Jul 11 eve | 3 | 0 | gpt-5.5×1, glm-5.2×1 |
| [`01391943`](01391943-07ac-4d71-95e6-6568c56d436b) | Jul 12–13 | 1 | **7** | — |
| [`8e194ef8`](8e194ef8-0565-458b-a59f-fa2d2e1741e4) | Jul 13 | 8 | 1 | — |
| [`400c6805`](400c6805-44f7-4fa4-8c73-7a5c572f81aa) | Jul 13 | explore only | 0 | — |
| [`7bd8f687`](7bd8f687-0b33-41b2-ab5a-10fccfc61069) | Jul 13–14 | 4 | **6** | sonnet-5×1 (then redirected to Grok) |
| [`9b2d98fc`](9b2d98fc-ad65-4eed-b2c3-ad04de798584) | Jul 14 10:04–11:40 | **4** (proof) + search | **0** | advisory then implementer |
| [`a4a729f2`](a4a729f2-fc9e-40a4-96f6-f63c6862fd9b) | Jul 14 | Composer search | — | **Grok 4.5 parent** (this report) |

\*Includes `grok-4.5-xhigh` and `cursor-grok-4.5-high`.

### Verdict sentence for (a)

**Yes on the proving workhorse for the hardest Jul 13–14 theorems; no on “everything / every chat became Grok.”** The arc used a **hybrid Opus/Claude-class parent + Composer research + Grok heavy-proof** setup that formed at `6522862`, tilted toward Grok for SCC + SurfaceWT headlines, then finished annotated/poly WT (`f762950`) with **Composer alone**.

---

## B) Commit inventory (exactly 13)

Baseline (not counted): `6522862` — follow-ups brief + SurfaceBridge header fix.

| # | Commit | Date | Summary |
|---|--------|------|---------|
| 1 | `ace4206` | Jul 11 22:28 | Surface `DataDecl` lowering, sound/complete `Lowers` bridge |
| 2 | `e5f1835` | Jul 11 23:22 | Prelude-aware `Program` pipeline + `program_type_safe` |
| 3 | `3fb2a3a` | Jul 11 23:34 | Explicit `Program.groups` → nested `letRecIn` via `desugarGroups` |
| 4 | `ebf20d5` | Jul 11 23:58 | `freeNames` / dep edges / naive `sccGroups` + `ValidBindingGroups` (proofs still sorry) |
| 5 | `6478be4` | Jul 11 23:58 | Handoff brief `next-agent-brief-surface-bridge-program-scc.md` |
| 6 | `9f59e10` | Jul 13 08:46 | Prove `sccGroups_sound` / `_complete` (axiom-clean) |
| 7 | `568853a` | Jul 13 09:47 | `Program.ofFlat` (flat binds → SCC groups) |
| 8 | `06bb46f` | Jul 13 09:47 | Update program/SCC + kickoff briefs |
| 9 | `7e9fc1f` | Jul 13 12:52 | Executable `checkExhaustive` + Bool→Prop soundness |
| 10 | `44669db` | Jul 13 23:57 | SurfaceWT corollary via strong inductive Approach A / **1a** |
| 11 | `e0d8f34` | Jul 13 23:57 | Point SCC brief at finished SurfaceWT; add `EvaluateUnsafe` root |
| 12 | `74e4c2f` | Jul 14 10:01 | Post-SurfaceWT front-end backlog brief; annotated WT before `letBlock` |
| 13 | `f762950` | Jul 14 11:40 | Finish annotated/poly `SurfaceWTExpr` ctors; surface→eval demos |

**Diff size (`6522862..HEAD`):** ~+8400 / −120 across ~11 files — overwhelmingly `FHM/SurfaceBridge.lean`, plus `EvaluateUnsafe`, `Examples` demos, small `SurfaceLang` / `InferW` / `Core` / `lakefile` / briefs.

`f762950` alone: +681 / −58 in `SurfaceBridge`, `Examples`, and two briefs.

---

## C) Technical arc (moderate detail)

### Phase 1 — Front-end product layer (Jul 11 evening)

Sessions: [`1e9914ae`](1e9914ae-e3fc-4d0b-add8-07f2a446d29c) (+ GLM review [`3448e5f7`](3448e5f7-ae63-412e-a36c-9be42556c107)).

After expression `surface_type_safe` was already unconditional at the baseline, work moved up the stack:

1. **`Surface.DataDecl` → Core `Decls` / `elabDecls`**
   - Ambient `preludeKindEnv` for lowering; closed-group API as `ke₀ = []`.
   - `LowersDataDeclsIn` / `lowerDataDeclsIn` sound + complete.
   - Closes original plan item 1.

2. **Whole-program slice**
   - `Surface.Program = decls + groups + body`.
   - Prelude merge: lower user decls under prelude KindEnv, then `elabDecls (preludeDecls ++ userCore)`.
   - `program_type_safe` talks about `p.term` (desugared), not raw `body`.
   - Completeness stays ∃ / `isSome` because match lowering is one-to-many.

3. **`desugarGroups`**
   - Hand-written SCCs fold into existing `letRecIn` (always `letRecIn` for nonempty groups, including size 1).
   - No Core metatheory growth.

4. **SCC scaffolding (C0/C1)**
   - `freeNames` / `bindingDepEdges`.
   - Spec `ValidBindingGroups` (Nodup, flatten-perm, mutual reachability, maximality, topo order matching `desugarGroups` foldr).
   - Executable `sccGroups`: mutual reachability partitions + Kahn on condensation.
   - Adequacy still sorry at end of Jul 11 night; handoff brief written.

**Models:** parent orchestrates + lots of direct edits; Composer for DataDecl/program proofs; GLM adversarial review (issues found, not blocking).

### Phase 2 — SCC adequacy + `ofFlat` (Jul 12–13)

Session: [`01391943`](01391943-07ac-4d71-95e6-6568c56d436b) (+ tactic archaeology [`6f0c2409`](6f0c2409-ea6b-4ffb-a4ed-7b2dcee12007)).

- Composer first-pass on SCC stalled on reachability / Kahn friction.
- Escalated to **Grok 4.5** per the ladder.
- Proved:
  - `sccGroups_sound : sccGroups = some groups → ValidBindingGroups`
  - `sccGroups_complete : ValidBindingGroups → (sccGroups _).isSome`
  - Completeness deliberately **not** `= some groups` (order freedom).
- Important truth fixes:
  - `sccOrderedIndexSets_flatPerm` needs **name-Nodup** (without it condensation can cycle / Kahn truncates).
  - Unbounded Kahn edge lemmas needed `edgesBounded` + edge Nodup.
- Parent added **`Program.ofFlat`**: `(sccGroups binds).map (groups ↦ ⟨decls, groups, body⟩)` with validity lemmas + `#guard`s.
- Briefs updated: SCC/ofFlat marked DONE; next pointers were checkExhaustive / SurfaceWT / letBlock.

### Phase 3 — Executable exhaustiveness (Jul 13 midday)

Session: [`8e194ef8`](8e194ef8-0565-458b-a59f-fa2d2e1741e4).

- Confirmed sequencing: checkExhaustive → SurfaceWT → letBlock.
- Implemented Bool mirrors of Prop coverage:
  - `dTreeExhaustiveB`, `checkExhaustive`, soundness into `SurfaceCovers` / related Prop forms.
- Drivers can now discharge coverage without hand-built Prop witnesses.
- Early SurfaceWT attempt (naive typecheck-transfer / invariant) **failed** at `match_` (witness vs canonical `lower`); planning pivoted to Approach A.

**Models:** Composer-heavy (research + implementation); one Grok attempt on the failed WT path.

### Phase 4 — `EvaluateUnsafe` (Jul 13 midday, orthogonal)

Session: [`400c6805`](400c6805-44f7-4fa4-8c73-7a5c572f81aa).

- Fuel-bounded evaluator discussion (why fuel vs Part/coinduction).
- New root `FHM/EvaluateUnsafe.lean`: `evaluate_sound` / `evaluate_complete`, `evaluateUnsafe`, `evaluateUnsafeTyped`.
- Registered in `lakefile.toml` (`e0d8f34`).
- Explicitly **not** part of the surface front-end backlog.

**Models:** parent did the implementation directly; no Grok proof farm.

### Phase 5 — SurfaceWT Approach A / 1a headlines (Jul 13 evening – Jul 14 morning)

Session: [`7bd8f687`](7bd8f687-0b33-41b2-ab5a-10fccfc61069).

**Problem:** weak WT (`∃ c, Lowers ∧ typecheck`) cannot feed open-branch `TypeOfHM_lowerMatch`.

**Chosen design (1a):** strong inductive

```lean
SurfaceWT ctors s := ∃ τ, SurfaceWTExpr ctors (kindEnvOfCtors ctors) [] [] [] s τ
```

At `match_` / `ife`, require open ingredient typings (scrutinee + branches under `patVars` / env extensions), not “some weird `emitInner` typechecks.” Weak WT kept as `SurfaceWT_weak` for NoMatch uniqueness only. Approaches B (pin `LowersExpr.match_`) and C (WT = `typecheck(lower)`) rejected.

**Lemma ladder shipped:**

| Rung | Status |
|------|--------|
| NoMatch uniqueness / weak transfer | DONE |
| `lowerExpr_match_decomp` | DONE |
| `patBindTys` / `EmitTyCtx` / `DTreeTypeable` | DONE |
| `TypeOfHM.weaken_env`, `emitLets_typeable`, `emit_DTreeTypeable`, `compile_initMatrix_typeable` | DONE |
| `TypeOfHM_lowerMatch` | DONE (hygiene + kinding) |
| `TypeOfHM_of_lowerExpr_of_SurfaceWTExpr` | DONE |
| `typecheck_of_lower_of_SurfaceWT` | DONE |
| `surface_type_safe_of_SurfaceWT` | DONE (axiom-clean; needs `arityConsistent` / `fieldsKinded`) |

**Coverage after this phase (still incomplete):**

- Unannotated mono `letIn` / `letRecIn`: strong ctors (nested matches OK).
- Annotated / poly lets: still `of_lowers` only — flagged as Priority 1 in the new backlog brief.

**Models:** parent proved some rungs directly (`weaken_env`, early emit helpers); Composer for mid-ladder; **Grok** for `compile_initMatrix_typeable` and finishing the strong corollary. One Sonnet farm attempt redirected to Grok on request.

### Phase 6 — Handoff briefs (Jul 14 morning)

Sessions: end of [`7bd8f687`](7bd8f687-0b33-41b2-ab5a-10fccfc61069), start of [`9b2d98fc`](9b2d98fc-ad65-4eed-b2c3-ad04de798584) (advisory), plus this audit [`a4a729f2`](a4a729f2-fc9e-40a4-96f6-f63c6862fd9b).

- Wrote `briefs/next-agent-brief-surface-wt-corollary.md` (Approach A record).
- Wrote `briefs/next-agent-brief-surface-front-end-backlog.md` (current takeover).
- Updated program/SCC brief to point at finished SurfaceWT + backlog order.
- Review endorsed: **finish annotated/poly strong WT before `letBlock`.**
- Wrote this models/work report (initially through `74e4c2f`).

### Phase 7 — Annotated/poly strong ctors + surface→eval demos (Jul 14 late morning)

Session: [`9b2d98fc`](9b2d98fc-ad65-4eed-b2c3-ad04de798584) (continued from advisory into implementation). Commit: **`f762950`**.

Closed the last Approach A / 1a gap:

1. **`SurfaceWTExpr.letInAnn` / `letRecInAnn`**
   - Annotated mono + poly `letIn` / `letRecIn` with recursive strong premises (nested matches OK).
   - Require **`tvs = []`** so `GeneralisesTo` transport can collapse `openBoundTyVars` via `tyBvarBounded` / `Expr.openTyVarsAux_eq_self_of_tyBvarBounded`. Honest under closed `SurfaceWT`; refuses only manually open judgments with nonempty ambient surface `tvs`.
   - `letRecInAnn` covers `RecSpec` mono/poly + `lowerAnnList`.

2. **Supporting infrastructure**
   - TyBvarBounded helper layer mirroring the existing tyFreeVars layer (`emit*`, `lowerMatch`, `lowerExpr`, …).
   - Ladder arms in `lowerExpr_isSome_of_SurfaceWTExpr` and `TypeOfHM_of_lowerExpr_of_SurfaceWTExpr`.
   - Corollary still axiom-clean (`lean_verify` on `surface_type_safe_of_SurfaceWT`).
   - `of_lowers` remains as escape hatch, no longer required for annotated/poly lets.

3. **`Examples.lean` — `SurfacePipelineDemo`**
   - Front-end pipeline demos: `Surface.Program` → `elaborateProgram` → `SmallStep.evaluate`.
   - Working cases: `ife`, user `Maybe` match (+ `checkExhaustive`), `Program.ofFlat` id app, annotated poly `∀a. a→a` id.
   - Conventions aligned with `Core.Demo` (`#eval showEval`, `#guard` on `.isSome` / printed results).
   - Documented gap: pattern-λ still lowers to `none` (`@TODO(pattern-λ)`).

4. **Briefs**
   - Backlog: annotated/poly **DONE**; **Priority 1 → `letBlock`**; pattern-λ → Priority 2.
   - WT corollary table updated for `letInAnn` / `letRecInAnn`.

**Models:** parent supervised + froze `tvs = []`; **four `composer-2.5-fast` proof subagents** (TyBvarBounded helpers, `letInAnn` ladder, `letRecInAnn` ladder); Grok fallback unused. Parent also wrote demos / brief updates / commit.

---

## D) Briefs created / modified since `6522862`

| Brief | Action | Role |
|-------|--------|------|
| `next-agent-brief-surface-bridge-program-scc.md` | **Added** (`6478be4`), updated through `74e4c2f` | Program / SCC / ofFlat status; points to WT + backlog |
| `next-agent-brief-surface-wt-corollary.md` | **Added** (`44669db`), updated `74e4c2f` + **`f762950`** | SurfaceWT Approach A / 1a record (now incl. annotated/poly) |
| `next-agent-brief-surface-front-end-backlog.md` | **Added** (`74e4c2f`), updated **`f762950`** | **Current takeover** — next is `letBlock` |
| `next-agent-brief-surface-bridge-kickoff.md` | **Touched** (`06bb46f`) | Historical PatComp kickoff tidy |
| `post-6522862-work-and-models-report.md` | **Added** (this file; may be untracked until committed) | Models + work audit |
| `next-agent-brief-surface-bridge-followups.md` | Unchanged in range (baseline) | Still authoritative for coverage / DTreeExhaustive lessons |
| `next-agent-brief-surface-bridge.md` | Unchanged in range | Original plan items 1–9 |

### Current backlog (from front-end brief, post-`f762950`)

| Priority | Item | Status |
|----------|------|--------|
| — | Expression `surface_type_safe`, PatComp, DataDecl, Program/SCC/ofFlat, `checkExhaustive`, SurfaceWT **including annotated/poly strong ctors** | **DONE** |
| **1** | `letBlock` public AST collapse (design settled) | **OPEN** |
| **2** | Pattern-λ desugar | OPEN |
| 3 | Strings / friendly errors / InferW dead-code prune | Optional |
| — | Plan item 9 (typeclasses, rows, …) | Deferred |
| — | `EvaluateUnsafe` | Orthogonal staging |

---

## E) Conversation ↔ work map

| Transcript | Approx date | Parent role | Subagents | Work |
|------------|-------------|-------------|-----------|------|
| [`5cab47ef`](5cab47ef-d51a-498c-ba81-65b56fa41746) | Jul 8–11 | Explicitly **Opus 4.8** | Grok / Composer / GLM | Boundary: O5 complete; `6522862` |
| [`1e9914ae`](1e9914ae-e3fc-4d0b-add8-07f2a446d29c) | Jul 11 eve | Orchestrator | Composer, GLM | DataDecl → Program → SCC scaffold + program-scc brief |
| [`3448e5f7`](3448e5f7-ae63-412e-a36c-9be42556c107) | Jul 11 23:09 | (review) | **glm-5.2-max** | Adversarial review of slice A |
| [`01391943`](01391943-07ac-4d71-95e6-6568c56d436b) | Jul 12–13 | Orchestrator (“you supervise”) | Composer → **Grok×7** | SCC proofs + ofFlat |
| [`6f0c2409`](6f0c2409-ea6b-4ffb-a4ed-7b2dcee12007) | Jul 12 | Search | — | Composer near-miss tactic archaeology |
| [`8e194ef8`](8e194ef8-0565-458b-a59f-fa2d2e1741e4) | Jul 13 | Orchestrator | Composer×8, Grok×1 | `checkExhaustive`; failed early SurfaceWT |
| [`400c6805`](400c6805-44f7-4fa4-8c73-7a5c572f81aa) | Jul 13 | Direct implementer | explore only | `EvaluateUnsafe` |
| [`2f1bd902`](2f1bd902-c7e0-48bf-a065-6e5f19dd70d6) | Jul 13 | Search | — | Fuel-eval history |
| [`7bd8f687`](7bd8f687-0b33-41b2-ab5a-10fccfc61069) | Jul 13–14 | Orchestrator + some proofs | Composer, **Grok×6**, Sonnet×1 | SurfaceWT 1a headlines + WT/backlog briefs (`74e4c2f`) |
| [`9b2d98fc`](9b2d98fc-ad65-4eed-b2c3-ad04de798584) | Jul 14 10:04–11:40 | Advisory → supervisor | **Composer×4** (Grok unused) | Backlog review → `letInAnn`/`letRecInAnn` + demos → **`f762950`** |
| [`a4a729f2`](a4a729f2-fc9e-40a4-96f6-f63c6862fd9b) | Jul 14 | **Grok 4.5** (this audit) | Composer search | Model + work report (updated after `f762950`) |

---

## F) Bottom line

1. **Commit count:** **13 commits** after `6522862` (was 12 when this report was first written; +`f762950`).
2. **Model story:** hybrid persisted. **Grok** carried the hardest Jul 13–14 proofs (SCC Kahn, SurfaceWT corollary ladder). **Composer** did research, `checkExhaustive`, DataDecl/program scaffolding, and — notably — **finished annotated/poly WT without needing Grok**. Parent stayed the orchestrator in implementer sessions; this audit chat itself is Grok 4.5.
3. **Substance:** built the surface **program front-end** (DataDecl → Program → SCC → ofFlat), **decidable coverage**, the **full strong SurfaceWT corollary including annotated/poly**, surface→eval **Examples demos**, an orthogonal **unsafe evaluator**, and a backlog whose next product item is now **`letBlock`** (pattern-λ after that).
4. **Caveat:** if you selected Grok as the *parent* model in the Cursor UI for some Jul 11–14 implementer sessions, transcripts cannot confirm or deny that — only subagent `Task.model` and user/orchestrator language are recoverable.
