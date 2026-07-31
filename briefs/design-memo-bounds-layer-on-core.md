# Design memo: bounds layer on Core (B′)

**Status:** dual-stack BL under `--bl` product-usable (J1–R2 Done; **R3 partial** — pack path wired, residual factory open). **Merged into `fhm`.** Next: **finish R3 residual mid-case** (§5 B handoff), then E2E gate, then editor/LSP + playground/CI.  
**Updated:** 2026-07-31  
**Repo:** `/Users/aron/dev/fhm` (optional `FHMBounds` package; default FHM stays pure).  
**This doc’s job:** living plan for work yet to do + locked design. History is compacted below; detail lives in git.

**BL sandbox history:** Jul 2026 bounds work was done in a temporary clone `/Users/aron/dev/blt`, then merged back here. Code/docs in `fhm` are current. For *chat* context (design debates, false starts), search Cursor/Grok conversations / agent transcripts from the **`blt` workspace** (`~/.cursor/projects/Users-aron-dev-blt/agent-transcripts/`), not only `fhm`. Prefer this memo + git for decisions; use blt chats when reconstructing “why.”

**Handoff (cold start):**
1. Read §§1–2 (hard nos), **§5 B + F** (R3 policy + mid-case examples), then `FHM/Bounds/Escape.lean` module header.  
2. Smoke: `lake build fhm FHMBounds` · `.lake/build/bin/fhm run --bl scratch/bl-stdlib.fhm` · `… bl-showcase.fhm` (expect `listId : ∀ n m. …`).  
3. **Next work = finish R3** — residual factory + mid-case reject (see §5 B “R3 handoff” below). Do not reopen D1–D2/D22.  
4. Key code: `FHM/Bounds/Escape.lean`, `Check.lean` (`packAtEscape`), `Commit.lean`, `Synth.lean` (app/inst); Live display in `Live.lean` / `Report.lean`.

**Related:** `design-memo-collapse-bl-axioms-to-z3.md` · `design-p1-bounds-kernel-api.md` · `next-agent-brief-type-holes.md` (orthogonal)

---

## 1. Vision & values

### What this is

FHM is a **verified Hindley–Milner** stack (Core, InferW, PatComp, …) — pedagogical HM *and* a testbed for original type-system ideas. The **BoundedList (BL) layer** is the first major refinement experiment: length intervals on lists, smarter matches, bound schemes — **without** rewriting Core or teaching Unify about counts.

### Dual-stack (non-negotiable)

| User sees | Implementation |
|-----------|----------------|
| One language; optional `BL` / `{n : Nat,…}` | B′ surface → **erase** → same HM spine |
| Bounds in types under `--bl` | Sidecar anns + `HasBounds` / `BoundCovers` + `ProgramReport` display |
| HM-only mode still works | D16 reject BL when `--bl` off; default lake target never pulls Bounds/Z3 |

**Hard no:** fuse `bl` into Core `Ty`; invent intervals from bare HM `List` (D22); uniqueness inside declarative `HasBounds` (Commit policy only).

### Priorities (how to choose work)

1. **Honest product UX** — one bounds-aware type line; errors that point at the right place; demos that mean what they say.  
2. **Principled dual-stack** — erase/check/report stay projections of one story; no print-time zips or “inject later from outside.”  
3. **Correctness holes before polish** — §2.3 residuals (ascription/`bctx`, Commit) before CI chrome.  
4. **Metatheory follows product** — progress composition / axiom collapse are post-E2E hygiene, not blockers.  
5. **Editor & shareability** — LSP-quality diagnostics and a hosted playground matter for *using* the language; schedule after BL correctness spine.  
6. **Proofs stay honest** — prefer bridging lemmas for recoverable pipelines over ad-hoc “best effort” that can’t be related to the verified path.

### Values for agents / collaborators

- Prefer elegant pipelines over clever edge patches.  
- Display and check must not drift (see `ProgramReport`).  
- When unsure, read §2 locked decisions and §5 backlog — don’t reopen D1–D2/D22.  
- Capture decisions in this memo; chat history is not the source of truth.

---

## 2. Locked decisions (summary)

| # | Decision |
|---|----------|
| D1–D2 | Dual-stack; Core/Infer unchanged for bounds |
| D3 | List as ADT (`Nil`/`Cons`); BL is surface/ann refinement |
| D4–D7 | One grammar; erase; no second bridge/PatComp/SCC |
| D8 | BoundCovers for List under `--bl`; else HM exhaustiveness |
| D9 | Uniqueness = Commit policy, not HasBounds |
| D10 | Z3 optional; axioms OK; collapse later |
| D11 | `FHM/Bounds/`; lake `FHMBounds`; default FHM pure |
| D12 | Sandbox `blt` → **merged into `fhm`** (Done) |
| D14–D15 | BoundsTy mirrors Ty; match join = min lo / max hi |
| D16 | HM mode: fail-fast on BL syntax |
| D17 | `{n : Nat, a}` — Nat + type foralls |
| D18 | Nested surface BoundCovers deferred; Core after lower |
| D20–D21 | Anns on erase package; gate ≠ erase |
| D22 | **Origin-only** intervals — never invent from bare `List` |
| D23 | Surface Count ↔ Kernel (ops + `inf` early) |
| D24 | Unascribed List λ: fresh `?lo`/`?hi` → constrain → generalise; mid-case → Commit `uniqueOnly` on escape |

**Origins of `lo`/`hi`:** Nil/Cons spine · surface ascription · `bctx` · app result · match join · scheme inst. **Not** “HM says List.”

**§2.3 ascription vs `bctx`:** solid anns push **ascribed** β (A+B Done). Residuals R1–R2 Done; R3 = multi-model at escape (§5 F).

---

## 3. Architecture today

```text
parse → [hmRequireNoBl if HM] → eraseProgram → lower → infer
  → assembleProgramReport          # display truth (ascription → synth → HM)
  → if --bl: ofLower + checkProgramAnns + checkProgramMatches
       enrich report from Check synth for unascribed binders
  → elaborate → evaluate
```

| Piece | Role |
|-------|------|
| `ErasedProgram` | HM spine + binder anns |
| `ProgramBoundsAnns.ofLower` | De Bruijn projection for Check |
| `ProgramReport` | Name-ordered display; Live/JSON/hover **only** pretty this |
| `Count.simplify` | Used by pretty (and Oracle normalize); **not** in Check `bctx` yet |

Display priority: erase ascription → Check synth β → HM `PolyTy`.

---

## 4. Done (compact)

| Area | Status |
|------|--------|
| Kernel / ExtNat / Oracle / Commit / BoundsTy / BoundCovers | Done |
| Surface BL + erase + Live `--bl` + diagnose | Done |
| Origin synth, hole pin, BoundCovers in Live | Done |
| `{n:Nat,…}` schemes, D24 fresh List λ, stdlib | Done |
| letRec id-sugar self-slot; hover pre-erase + count order | Done |
| `ProgramReport` + synth enrich + display Count fold | Done |
| Type-only schemes (`{a}`) package as `.scheme` → `∀ a. …` | Done |

**Exit demo:** `scratch/bl-stdlib.fhm` under `--bl` — schemes print with `∀`, `result` shows folded `BL` intervals, eval OK.

---

## 5. What’s next (ordered)

### Triage (park here; don’t reorder the spine for these)

Sticky notes from day-to-day use. Promote into §5 B/C only when tackling that tier; otherwise leave here so we don’t thrash the main order.

| ID | Item | Notes / likely home |
|----|------|---------------------|
| **T1** | **λ/head param hover shows HM `List`, not binder `BL`** | **Done** (with R2 + RHS `expectedβ`): colon-form `\xs` and head binders both show `BL …`. |
| **T2** | Match/coverage diagnostic spans often file-top | No binder name in message. **C** localized errors. |
| **T3** | Non-List **ctor apps** under bounds (`Some 1`, etc.) | Nullary `None` / ascribed check OK; saturated non-List ctor apps still `cannot infer bounds for ctor`. Blocks Option demos with `Some`. Synth/checkBounds ctor app path (Pair/Cons special-cased today). |
| **T4** | Hole ascription pretty keeps `_` on hover/report | **Partial:** binder/program pretty prefer synth when ann has holes; λ-domain hover may still peel holey ascription. |
| **T5** | Compound scheme **domains** (`BL (n+1) m`) don’t pin from concrete args | `head`/`tail` define but don’t call. **I1**. |

### A. Reintegrate `blt` → `fhm` ✅

**Done.** Bounds lives here as optional `FHMBounds`; default `lake build` FHM stays pure. See header **BL sandbox history** for where to find Jul 2026 chat transcripts.

### B. BL correctness residuals (**next product work**)

| ID | Item | Importance |
|----|------|------------|
| **J1** | Non-List multi-arm **result join** in origin synth (`if`/Bool/… → join arm βs) | **Done** — `synthJoinArms` / `synthJoinArmsAt`; unascribed `pick` → `BL 1 3`; see `scratch/bl-join-if.fhm` |
| **R1** | Hole anns → push **pinned** template into `bctx` | **Done** — pin-meet then `pinHoles` into env (same interface as solid); `scratch/bl-r1-pin-env*.fhm` |
| **R2** | Head-binder `(xs : BL …)` fold into demand | **Done** — `foldHeadParamAnns` in erase; ofLower gets full arrow; `scratch/bl-r2-head-binder.fhm` |
| **R3** | Detect **non-vacuous multi-model** free counts at escape; **reject + ask for let-ascription** (uniqueOnly) | **Partial** — see **R3 handoff** below + §5 F |
| **R4** | Pair-match demand peel | Medium |
| **R5** | Declarative `HasBounds.letMono` align | Low |
| **R6** | Nested BoundCovers path-Δ | Medium |

#### R3 handoff (for the next agent)

**Done:**
- Policy locked in **§5 F** (what is / isn’t mid-case; reject + let-ascription).
- `FHM/Bounds/Commit.lean` — `uniqueOnly`, `gatherNarrowingEvidence`, `decideCommit` (+ witness lemmas).
- `FHM/Bounds/Escape.lean` — `EscapeVerdict`, `classifyEscape` / `classifyEscapeDefault`, theorems; **`packAtEscape`**; best-effort `subConstraints?` / `escapeResidualCons?`.
- `Check.checkBinderRhs` calls `packAtEscape` (unascribed: residual `[]`; hole pin: residual from pin-vs-synth when available).
- Vacuous path unchanged: free lengths still pack to `∀` (e.g. showcase `listId`).

**Not done (this is the work):**
1. **Residual factory for real mid-case** — non-empty `cons` when free outs sit under a non-vacuous band, especially:
   - Affine app / scheme inst: `f : {x} BL x (2*x) _ → BL x (2*x) _`, `e : BL 10 10 _`, result of `f e` mentions `?x` with `5 ≤ ?x ≤ 10` (§5 F example 1).
   - Exact-length inst + residual band on shared `?n` (§5 F example 2).
   - Pattern: BLSketch `subtypeProblem` / `forceSubtype` — dual-stack needs an equivalent that **accumulates or re-derives** residual constraints at app/ascription, not only pin-vs-synth at binder pack.
2. **Thread residual into `packAtEscape`** at those sites (API already takes `residualCons`; Check often passes `[]` today → always vacuous → never multi-reject).
3. **Surface demo** that **fails** uniqueOnly for the right reason; keep green: stdlib, showcase, `listId` ∀, join `BL 1 3`.
4. Optional: apply `uniqueCommit σ` to ground β (today unique still packs); expand `EscapeClassifies` beyond vacuous constructors.

**Call sites today:**
| Location | Behaviour |
|----------|-----------|
| `Check` hole-pin pack | `escapeResidualCons? βPinned β1` then `packAtEscape` |
| `Check` unascribed pack | `packAtEscape Δ β1 []` |
| App / scheme-inst result export | **no residual yet** — main gap |

**Smoke:**
```bash
lake build fhm FHMBounds
.lake/build/bin/fhm run --bl scratch/bl-stdlib.fhm
.lake/build/bin/fhm run --bl scratch/bl-showcase.fhm   # listId : ∀ n m. …
.lake/build/bin/fhm run --bl scratch/bl-r1-pin-env.fhm
.lake/build/bin/fhm run --bl scratch/bl-r1-pin-env-fail.fhm  # expect bounds error
```

**Done when:**
- [ ] Mid-case residual non-empty for §5 F example (1) or (2) at escape
- [ ] `uniqueOnly` rejects with clear “non-unique…; add a let ascription…” message
- [ ] Vacuous `listId` / stdlib / showcase still green
- [ ] Memo §5 B R3 marked Done; §7 R3 checkbox ticked

**Then:** **Slice 9 — E2E gate suite** over `scratch/bl-*` (CI smoke; locks the fixed surface). Not an adversarial research suite.

### C. Editor / LSP quality (after B spine)

Happy-path diagnose exists (`blt diagnose`, VS Code + `editors/web`). Desired:

| Theme | Notes |
|-------|--------|
| **Localized errors** | Squiggles on the **failing span**, not file-top / whole program |
| **Recoverable pipeline** | Error in one binder/scope stays contained; unused broken `let x = …` shouldn’t kill the body if `x` unused; ideally recover at **lex / parse / typecheck / bounds** stages |
| **Cost & proofs** | More than happy-path; expect duplication or a parallel “partial” driver. Prefer **bridging lemmas**: recoverable success ⇒ same as verified pipeline on the OK fragment |
| **IDE niceties (wishlist)** | Go to definition · find references · rename · hover already partially there · workspace symbols · maybe signature help |

No full design yet — spike after R1–R3 / E2E, or a thin “error span” pass sooner if cheap.

### D. CI + hosted playground

- **CI:** `.github/workflows/lean_action_ci.yml` exists (lean-action). Extend to `lake build blt FHMBounds` + bl-stdlib/`--bl` smoke.  
- **Local playground:** `editors/web` (Monaco → `blt diagnose` / `--json`).  
- **Host:** start on **render.com free tier**.  
- **Sharing model (decision needed):**
  - *Live query URL* (Lean playground style) — every edit in the URL; breaks in chat/email when long.  
  - *Snapshot share* — Share button writes source to SQLite (or similar), returns short id URL; **immutable snapshot** preferred (less surprise than editable shared docs).  
  Default leaning: **immutable snapshot URLs** + optional “fork to edit.”

### E. Later / design (don’t steal focus)

| Topic | Note |
|-------|------|
| **Pretty-printer spine duplication** | Display sugar/prec (`→`, `(a,b)`, `BL …`) is implemented separately on `Ty`, `Surface.Ty`, `BoundsAnnTy`, and `BoundsTy` (`FHM/Pretty.lean`, `FHM/Bounds/Ann.lean`, `FHM/Bounds/Typing.lean`); Synth still has a debug-only `prettyβ` without prec/Pair sugar. Parallel ASTs explain some of it; `BoundsAnnTy`/`BoundsTy` are nearly copy-paste. Low priority: unify via shared spine (count-slot + var-name params) or a single display IR — not blocking product work. |
| **Count folding in Check/Synth** | Display folds via `Count.simplify`. Open: fold once post-synth into `bctx`? at each op? only pre-Oracle? Don’t change solver inputs casually. |
| Axiom collapse to Z3 | Collapse memo; post-E2E |
| Progress under HasBounds+BoundCovers | Post-E2E |
| Surface nested BoundCovers | D18 |
| HM type holes / head-binder packing | Separate brief |
| README “Bounds experimental” | Hygiene |

### F. Multi-model / uniqueness (locked 2026-07-31)

Original gist §4.5 + BLSketch: uniqueness is elaborator policy, not declarative typing. Below is the dual-stack product reading.

**Not multi-model (do not treat as R3):**

| Situation | Why OK |
|-----------|--------|
| Join → `BL 1 3` | Unique **range type** (endpoints determined) |
| Free `BL ?lo ?hi` into demand `BL 3 5` | Principal product is usually hull `BL 3 5` |
| Vacuous free → `∀ n m. …` | Any Nat; generalise |

**Two concrete mid-cases** (result type depends on which model you commit):

```text
-- (1) Affine demand + free in result  (canonical; DemandOK-legal)
e  : BL 10 10 α                    -- concrete length 10
f  : {x} BL x (2*x) α → BL x (2*x) β   -- e.g. map-shaped; demand is Sub not exact-eq
f e
-- instantiate x ↦ ?x; need BL 10 10 <: BL ?x (2*?x)
-- ⇒ 5 ≤ ?x ≤ 10  (many models)
-- result type is BL ?x (2*?x) β  →  BL 5 10 vs BL 10 20 vs …  all sound, mutually exclusive prints
```

```text
-- (2) Exact-length scheme inst + residual band on shared ?n
idExact : {n} BL n n α → BL n n α   -- instantiate n ↦ ?n  (lo and hi share ?n)
-- after use, residual only e.g. 1 ≤ ?n ≤ 5  (band, not a single n)
-- export mono BL ?n ?n  → models {1,2,3,4,5}; bare ∀ n would drop the band (unsound)
-- (How ?n appears: scheme inst, not a user rigid ∀ being "solved".)
```

**Policy (product):** on mid-case at output-visible escape → **reject + ask for let-ascription** (no expr-level `(e : τ)` AST). Do not silent-pick. Vacuous free still generalises. Unique range types still OK.

**DemandOK:** bans multi-inferable-in-one-count on *demands* (`?a*?b`); does not remove mid-case (1).

**R3 = implement that policy on Live Check escape** (detect non-vacuous multi-model free outs → uniqueOnly-style error + let-ascription hatch).

**Today (R3 partial):** classifier + `packAtEscape` are on the binder pack path, but residual `cons` is usually empty → still **vacuous generalise**. Mid-case is not yet *rejected*; it is still mostly *invisible*. Full R3 = residual factory + reject (above).

---

## 6. Risks (short)

| Risk | Mitigation |
|------|------------|
| Scope into Unify / Core Ty | D1–D2 hard no |
| Inventing List intervals | D22 |
| Ascription vs env leak | §2.3 A+B; finish R1 |
| Z3 in default build | Thin Ann/Report; Check only on `--bl` |
| Display/check desync | `ProgramReport` assemble + enrich only |
| Merge dual editor binary lookup | Drop on `fhm` merge |

---

## 7. Success criteria (rolling)

- [x] Dual-stack BL under `--bl` with schemes + stdlib + unified display  
- [x] Core/Infer free of bound feature work  
- [x] Merged into `fhm` as optional Bounds  
- [x] J1 non-List multi-arm result join (unascribed `if` → join)  
- [x] R1 hole anns → pinned template in `bctx`  
- [x] R2 head-binder BL fold into demand  
- [x] R3 Escape API + `packAtEscape` on Check pack path (vacuous path)  
- [ ] R3 residual mid-case factory + uniqueOnly reject demo (or explicitly waived)  
- [ ] Slice 9 E2E gate in CI  
- [ ] Localized diagnostic spans (MVP)  
- [ ] Hosted playground + share story decided and shipped  
- [ ] Default `lake build` FHM pure documented  

---

## 8. One-liner

> **B′:** erase BL to List; origin HasBounds + BoundCovers; schemes; `ProgramReport` display — **next finish R3 residual mid-case → E2E → LSP/playground.**

---

## 9. New-agent checklist

1. Read §§1–2 (hard nos), **§5 B + F** (R3 policy + examples), **§5 B “R3 handoff”**, `FHM/Bounds/Escape.lean` header.  
2. Smoke: `lake build fhm FHMBounds` · `.lake/build/bin/fhm run --bl scratch/bl-stdlib.fhm` · `… bl-showcase.fhm`.  
3. Work **R3 residual factory** next (not R4+ until R3 Done or waived).  
4. Do not invent List intervals (D22). Do not fuse bounds into Core Ty. Bounds defs stay **total** (no `partial` under `FHM/Bounds/`).  
5. Update **§5** / §7 when closing an item.

---

## Appendix A — Historical slice map (compact)

| # | Delivered |
|---|-----------|
| 0–2 | Docs honesty; `Count.inf`; binder spine / ofLower |
| 3–6 | Surface Count; origin synth; hole pin; BoundCovers in Live |
| 7–8 | Schemes + D24; stdlib map/filter/append/flatMap/… |
| 9 | E2E gate — **queued** after R1–R3 |
| + | Display report; synth enrich; pretty fold; type-only `∀ a.` |

P0–P6 / old P4 tables: superseded by the above; see git history if needed.

## Appendix B — Module map

`Kernel` · `Oracle` · `Commit` · `Ann` · `Report` · `Typing` · `Synth` · `Erase` · `Pipeline` · `Check` · `Examples` — plus Live / EditorSupport / `editors/web` / `editors/vscode`.
