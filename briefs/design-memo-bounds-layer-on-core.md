# Design memo: bounds layer on Core (B′ plan)

**Status:** living plan — P1–P3 / P3.5b–c / P4a–P4b done; **P4c Live `--bl` through ann-visible + v1 Z3 ascription check** (`defaultBounds` synth)  
**Updated:** 2026-07-29  
**Repo:** `/Users/aron/dev/blt` (sandbox; merge back into `fhm` later as optional package)  
**Canonical doc for this integration** (plus satellite briefs below)

**Related briefs (not replaced):**

| Doc | Role |
|-----|------|
| `design-memo-collapse-bl-axioms-to-z3.md` | Oracle TCB / prove BL axioms from Z3 |
| `design-p1-bounds-kernel-api.md` | P1 conceptual (API now in Lean) |
| `next-agent-brief-remove-unique-from-typeof.md` | BLSketch uniqueness exit (done) |
| `next-agent-brief-type-holes.md` | HM type holes / head-binder packing (**orthogonal**) |

---

## 1. Goal

Add a **BoundedList refinement layer** on top of the existing FHM Hindley–Milner stack **without** rewriting Core, InferW, TypeOf*, PatComp, or vanilla exhaustiveness metatheory.

| User sees | Implementation |
|-----------|----------------|
| One language (optional BL syntax) | **B′:** bounds-aware surface + erase + bound passes |
| Smarter List matches, bound schemes, intervals in types | Sidecar `BoundsAnnTy` + `HasBounds` / `BoundCovers` |
| REPL toggle BL on/off | Pipeline flag; HM spine identical after erase |
| Pure HM product still exists | Default lake target never imports Bounds/Z3 axioms |

**Non-goals (v1):** fuse `bl` into Core `Ty`; teach Unify/Infer about intervals; principal bounds; inferred count gen; type-passing counts; full dual surface frontend; finish BLSketch axiom collapse before the layer exists.

---

## 2. Locked decisions

| # | Decision |
|---|----------|
| D1 | **Dual-stack:** HM equality typing unchanged; bounds are a separate judgment/pass |
| D2 | **Core `Ty` / `Expr` / InferW / TypeOf\***: **no** bound constructors, no Infer changes for v1 |
| D3 | **List as ADT:** refinements of `customTy "List" [α]` + `Nil`/`Cons`, not Core primitive `BL` |
| D4 | **Surface: B′ (same AST)** — extend `Surface.Ty` (etc.) with bounds; **one** grammar |
| D5 | **`eraseBounds`** rewrites `BL lo hi t` → surface `List t`; **bound holes `_` only in BoundsAnnTy** |
| D6 | **`DoesntContainBounds`** on erased programs; SurfaceBridge absurd `.bl` arms only |
| D7 | **No second SurfaceBridge / PatComp / SCC** |
| D8 | **Coverage:** `AllMatchesExhaustive` for non-List; **`BoundCovers`** for List under bounds (Core flat patterns) |
| D9 | **Uniqueness:** not a premise of declarative `HasBounds`; Commit policy only |
| D10 | **Oracles:** Z3 optional target; BL axioms OK initially; collapse later |
| D11 | **Containment:** `FHM/Bounds/`; lake `FHMBounds`; default `FHM` pure |
| D12 | **Work in `blt` for now**; merge to `fhm` later |
| D13 | **BLSketch:** reference/demos; kernel extracted into Bounds |
| D14 | **BoundsTy mirrors Core `Ty`** (prim/arrow/bvar/fvar/list/custom); intervals only on `list` |
| D15 | **Match join bounds:** min lo / max hi (not equality) |
| D16 | **HM mode:** reject BL syntax at frontend (not silent erase); Core never sees BL either way |
| D17 | **Count ∀ syntax (direction):** `{n m : Nat, a b}` — only `: Nat` + bare type vars lower in v1 |
| D18 | **Surface nested BoundCovers:** **not** for v1 — check **after lower** on Core `BoundCovers` |
| D19 | **File budget:** prefer few large modules (current: Kernel, Oracle, Commit, Typing, Erase, Pipeline) |
| D20 | **Erase packages anns with binders** (`ErasedTy` / `ErasedBinding`); not a free-floating map beside an unrelated program |
| D21 | **Gate ≠ erase:** `hmRequireNoBl` is D16 only; `eraseProgram` always erases; Live composes them |

**D16 clarified:** “reject” is **UX fail-fast** when BL mode is off (`--bl` absent): clear error after parse, not silent erase. It is *not* about Core `TypeOf*` — Core `Ty` has no `.bl`, so HM typing never sees bounds. Without erase, `lowerTy .bl = none` already fails; D16 is the intentional HM-mode message.

---

## 3. Architecture

```text
.fhm source
    │
    ▼
Parse (bounds-aware Surface)          [SurfaceLang + Parse]
    │
    ├─ .hm: hmRequireNoBl (D16)       [Bounds/Pipeline — Live]
    │
    ▼
eraseProgram                          [Bounds/Erase]
    │
    ├──────────────────► ErasedBinding.ann / BoundsAnnTy
    ▼
erased.toProgram  (DoesntContainBounds)
    │
    ▼
lower / SCC / PatComp                 [SurfaceBridge — absurd .bl only]
    │
    ▼
Core.Expr
    │
    ▼
Infer / elaborate                     [InferW — UNCHANGED]
    │  τ_HM   (pretty still shows List, not BL — expected until bounds report)
    ▼
ofLower (binderEnv)                   [Bounds/Pipeline — next]
    │  ProgramBoundsAnns
    ▼
HasBounds + BoundProgramOK            [Bounds/Typing — not wired to Live yet]
    │  β
    ▼
BoundCovers (List β)                  [same file]
  vs AllMatchesExhaustive (non-List / HM mode / current --bl)
    │
    ▼
evaluate                              [UNCHANGED]
```

### Live today (2026-07-29)

```text
parse → [hmRequireNoBl if not --bl] → eraseProgram → lower/infer/exh/elab/eval
```

Anns are produced but **not consumed**. Exhaustiveness is still the HM checker under `--bl`. REPL types print as `List Int` after erase — correct for this slice.

### Outer safety (BL mode) — target theorem

```text
TypeOfElabHM Γ e τ
∧ HasBounds … e τ β
∧ (BoundCovers … β branches  ∨  non-List exhaustiveness)
⇒  never stuck
∧  (optional later) closed values satisfy length intervals
```

`TypeOfElabHM.progress` unchanged; composite lemmas later.

---

## 4. Current codebase (as of 2026-07-29)

```text
FHM/Bounds/
  Kernel.lean    # Count, constraints, DemandOK, Interval, path helpers
  Oracle.lean    # checkValid / solve / unique + axioms + Z3 bridge
  Commit.lean    # NarrowingEvidence, PolicyKind, decideCommit
  Typing.lean    # BoundsTy, Agrees, Sub, HasBounds, CheckBounds, BoundCovers
                 # + BoundsAnnTy / Elab* / MatchSafe / BoundProgramOK
  Erase.lean     # ErasedTy / ErasedBinding / ErasedProgram (anns with erase)
  Pipeline.lean  # BoundsMode, hmRequireNoBl, ofLower, Bool detectors
  Examples.lean  # Core-only HasBounds / BoundCovers / MatchSafe demos

Live / CLI:
  --bl flag; D16 gate; erase before lower; scratch/bl-live.fhm
  watch-live.sh --bl

Surface:
  Count lit/hole; Ty.bl; DoesntContainBounds (Ty/Expr/Program);
  Parse BL / _; Pretty; lowerTy .bl → none
```

| Area | Status |
|------|--------|
| P1 kernel + BLSketch rewire | **Done** |
| P2 BoundsTy ≅ Core Ty + HasBounds (List rules) | **Done** |
| P3 BoundCovers (Core flat patterns) | **Done** |
| P3.5b BoundsAnnTy contract | **Done** |
| P3.5c Core demos | **Done** |
| P4a Surface AST + Pretty + bridge stubs | **Done** |
| P4a-parse `BL` / `_` | **Done** |
| P4a-count-ops (Surface.Count add/mul/…) | **Deferred** — see §6 |
| P4b erase / ErasedBinding | **Done** (`Erase.lean`; `noBl` proof still `sorry`) |
| P4c shapes + Live `--bl` + D16 + erase-run | **Done enough to run** — anns unused; HasBounds unwired |
| P4c-follow (see §6 next) | **Next** |
| Bound schemes / stdlib | **Not started** (P5) |
| `Count.inf` (kernel) | **TODO only** (P3.5a) |
| Axiom collapse to Z3 | **Partial** |

---

## 5. Does the reshuffle cover everything?

### 5.1 Original plan → reshuffle mapping

| Original | Reshuffle | Status |
|----------|-----------|--------|
| P0 design freeze | P0 | Done (this memo) |
| P1 kernel extract | P1 | Done |
| P2 HasBounds on Core | P2 | Done (stronger: full BoundsTy mirror) |
| P3 BoundCovers + **progress composition** | P3 covers **done**; **progress still open** | Partial |
| P4 Surface B′ + erase + CLI | P4 | **Parse/erase/CLI gate done**; bounds check pass open |
| P5 schemes + stdlib | P5 | Pending |
| P6 polish / merge / axiom collapse / apply-σ / toggle | P6 | Pending |

### 5.2 Emergent work folded into reshuffle

| Emergent item | Where it sits now |
|---------------|-------------------|
| BoundsTy must track **composites** (not list/arrow-only POC) | **Done** in P2 (`custom` + `Agrees`) |
| `Count.inf` + default list `hi = inf` | **P3.5a** |
| `HasBounds.weaken_Δ` unprovable (`checkValid` not mono) | **On-demand** |
| BoundsAnnTy keying (post-Infer / bindings) | **P3.5b** shapes; **P4b** producers; **ofLower** still demo-spine |
| HM mode = frontend fail-fast | **Done** in Live (`hmRequireNoBl` / `--bl`) |
| `{n : Nat, a}` scheme syntax | **P5** |
| Core BoundCovers only; surface nested later | **D18** |
| **Live imports Bounds → Oracle → Z3 just to erase** | **P4c-thin** (emergent; see §6) |
| Diagnose path does not erase (BL buffers fail hover) | **P4c-diagnose** |
| REPL prints `List` not `BL` after erase | **Expected** until bounds report / pretty (P4c-ann-visible or P6) |
| Editor dual `blt`/`fhm` binary lookup | Sandbox artifact; `@TODO(merge-to-fhm)` in editors |

### 5.3 Worth noting: **not** fully covered / still external

| Item | Notes |
|------|-------|
| **Head-binder packing / HM type holes** | Orthogonal; type-holes brief |
| **Surface nested BoundCovers** | D18 deferred |
| **Semantic length safety** | P6 or later |
| **README / Headlines “Bounds experimental”** | Still open |
| **Playground/editor hover for bounds anns** | After anns are visible in pipeline |
| **CI job for FHMBounds** | Not specified |
| **Proving `checkValid_sound` from Z3** | Collapse memo / P6 |

---

## 6. Reshuffled residual plan

### Done

- **P0** — Dual-stack / B′ locks (living memo)  
- **P1** — `Kernel` / `Oracle` / `Commit`; BLSketch rewire  
- **P2** — `Typing`: BoundsTy, Agrees, Sub, HasBounds, CheckBounds  
- **P3** — `BoundCovers` + branch detectors (Core only)  
- **P3.5b** — BoundsAnnTy / Elab* / MatchSafe / BoundProgramOK shapes  
- **P3.5c** — `FHM/Bounds/Examples.lean`  
- **P4a** / **P4a-parse** — surface `BL` + parse  
- **P4b** — erase packages (`ErasedTy` / `ErasedBinding` / `ErasedProgram`)  
- **P4c (partial)** — `hmRequireNoBl`, Live `--bl`, erase-then-run end-to-end  

### Next (ordered; pressure from Live wire)

These four are the immediate follow-ons from wiring `--bl`. They sit under **P4c residual** / early **P6 hygiene**, not a new top-level phase:

| Slice | Fits as | Content |
|-------|---------|---------|
| **P4c-thin** | P4c / D11 hygiene | Thin Erase so `blt` does not pull Typing→Oracle→Z3 just to strip `BL`→`List`. Biggest structural smell from the Live wire. |
| **P4c-diagnose** | P4c / editor | Diagnose always erases (like Live under `--bl`) so BL buffers get hover/symbols (still as `List …` until ann report). |
| **P4c-ann-visible** | P4c | Carry `ErasedProgram` through check; first real `ofLower` (honest binder spine) + something visible (print/JSON anns). Forces binder-spine honesty without full HasBounds. |
| **P4c-hasbounds** | P4c exit / progress | Live bounds check pass: Core `e`+`τ`+`ProgramBoundsAnns` → HasBounds / ascriptions / MatchSafe; BoundCovers for List under `--bl`. |

Recommended order: **thin → diagnose → ann-visible → hasbounds**.

#### P3.5a — `Count.inf` (when defaults / pretty matter)

- Kernel `Count.inf`; eval / DemandOK / Z3 encode / `defaultBounds` list hi = inf  

#### P4 — Surface B′ (slice table)

| Slice | Content | Status |
|-------|---------|--------|
| **P4a** | Surface AST / Pretty / bridge stubs | **Done** |
| **P4a-parse** | Parse `BL` / `_` | **Done** |
| **P4a-count-ops** | Count `add`/`mul`/… | **Deferred** ≤ P5 |
| **P4b** | Erase packages | **Done** (prove `noBl` later) |
| **P4c** | Gate + Live `--bl` + erase-run | **Done** (run works) |
| **P4c-thin** | Erase without Oracle/Z3 (`Ann.lean`) | **Done** |
| **P4c-diagnose** | Diagnose erase | **Done** |
| **P4c-ann-visible** | ofLower + print/JSON `BL …` anns | **Done** (demo binder spine) |
| **P4c-hasbounds** | Bound pass in Live | **Done (v1)** — `Check.checkProgramAnns` via Z3 `checkValid`; synth β = `defaultBounds` until HasBounds synthesis |

**Exit (full P4):** `.fhm` with `BL 0 5 Int` → List + bound check + smarter List matches.

#### P5 — Bound schemes + stdlib

- `{n m : Nat, a b}` erase → BoundsAnnTy schemes  
- Re-add `Surface.Count.var` + parse/pretty/erase wiring  
- Pack/instantiate with Sub/solve + Commit  
- Demos: map, filter, append, …  
- **Must include P4a-count-ops if not done earlier**

#### P6 — Polish / hygiene / merge

- Axiom collapse (encoding lemmas; delete BL triple axioms)  
- Apply-σ / normalise BoundsTy for pretty  
- Default commit policy product choice  
- Composite progress + optional semantic length lemmas  
- Playground toggle; README/Headlines note  
- Merge `FHM/Bounds` into `fhm`; retire `blt` when ready  
- Drop editor dual `blt`/`fhm` binary lookup (`@TODO(merge-to-fhm)`)  
- Optional: head-binder packing; Surface nested BoundCovers; Pair HasBounds intros; restated `weaken_Δ`  

---

## 7. Pipeline / REPL toggle

| Mode | Front | Coverage | Bound pass |
|------|-------|----------|------------|
| **HM (default)** | Parse; **`hmRequireNoBl`** (D16) | `checkExhaustive` | skip (erase still runs; anns unused) |
| **BL (`--bl`)** | Parse BL; erase; lower | still HM exh today → **BoundCovers** at P4c-hasbounds | HasBounds at P4c-hasbounds |

Shared: Infer, elaborate, evaluate.

---

## 8. Explicitly deferred (still)

| Item | Why |
|------|-----|
| Core `Ty.bl` | Dual-stack |
| InferW bound completeness / principal bounds | False / research |
| Unique in HasBounds | Policy only |
| Full axiom collapse before Surface | Hygiene |
| HM structural type holes | Separate brief |
| Second surface language | B′ |
| Deep BLSketch polish | Extract done |
| Surface nested BoundCovers mutual with SurfaceCovers | After-lower Core check first |
| `HasBounds.weaken_Δ` as originally stated | False for oracle equality |
| Surface.Count arithmetic (until P4a-count-ops) | Parse v1 = lit/hole; ops have an owned slice |
| Surface.Count.var | Returns with P5 Nat binders |

---

## 9. Risk register (updated)

| Risk | Mitigation |
|------|------------|
| BoundsAnnTy paths break under lower/elab | Binding-level + post-Infer; **ann-visible** forces spine |
| Default `[0,0]` misleads | P3.5a `Count.inf` |
| SurfaceBridge touch radius | Absurd-bl only |
| Z3 in default / CLI proof cone | **P4c-thin**; keep `FHMBounds` optional for Typing |
| Scope creep into unify | Hard no |
| BoundCovers vs AllMatchesExhaustive | P4c-hasbounds pipeline contract |
| `checkValid` non-monotonicity | Don’t state weaken_Δ; use Valid if mono needed |
| Surface count ops forgotten | **P4a-count-ops** owned; deadline ≤ P5 |
| Editor looks for wrong CLI binary | Relink + dual lookup; revert on merge |

---

## 10. Success criteria

- [x] Optional Bounds build: kernel + Typing (HasBounds, BoundCovers)  
- [x] Core/InferW free of bound feature work  
- [ ] Default `lake build` FHM pure; Headlines guard (document Bounds as optional)  
- [x] `BL _ 5 t` / lit erases to List (hole in BoundsAnnTy on erase path)  
- [ ] Nil-only match under proved empty upper bound (Core demo and/or surface)  
- [x] REPL/CLI HM vs BL mode (fail-fast vs erase+run) — **partial:** run works; bound pass open  
- [ ] Composite never-stuck under HasBounds + BoundCovers (or documented partial)  

---

## 11. One-liner

> **B′ dual-stack:** BoundsTy mirrors Core Ty with intervals on List; surface `BL` parses and erases under Live `--bl`; next is consume anns (ofLower → HasBounds) without dragging Z3 into erase — never put intervals in Core or InferW.

---

## 12. Next action

1. **HasBounds synthesis** (replace `defaultBounds` in Live check) + real post-lower binder spine.  
2. BoundCovers / MatchSafe under `--bl` for List matches (still HM exh today).  
3. Pull **P3.5a** / **P4a-count-ops** when demos demand.  

Thin erase (`Ann.lean`) stays Z3-free for diagnose/hover; Live `--bl` check path uses Z3 via `FHM.Bounds.Check`.
