# Design memo: bounds layer on Core (B′ plan)

**Status:** living plan — P1–P3 done; reshuffled residual work  
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
| Smarter List matches, bound schemes, intervals in types | Sidecar `BoundAnn` + `HasBounds` / `BoundCovers` |
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
| D5 | **`eraseBounds`** rewrites `BL lo hi t` → surface `List t`; **bound holes `_` only in BoundAnn** |
| D6 | **`DoesntContainBounds`** on erased programs; SurfaceBridge absurd `.bl` arms only |
| D7 | **No second SurfaceBridge / PatComp / SCC** |
| D8 | **Coverage:** `AllMatchesExhaustive` for non-List; **`BoundCovers`** for List under bounds (Core flat patterns) |
| D9 | **Uniqueness:** not a premise of declarative `HasBounds`; Commit policy only |
| D10 | **Oracles:** Z3 optional target; BL axioms OK initially; collapse later |
| D11 | **Containment:** `FHM/Bounds/`; lake `FHMBounds`; default `FHM` pure |
| D12 | **Work in `blt` for now**; merge to `fhm` later |
| D13 | **BLSketch:** reference/demos; kernel extracted into Bounds |
| D14 | **BoundInfo mirrors Core `Ty`** (prim/arrow/bvar/fvar/list/custom); intervals only on `list` |
| D15 | **Match join bounds:** min lo / max hi (not equality) |
| D16 | **HM mode:** reject BL syntax at frontend (not silent erase); Core never sees BL either way |
| D17 | **Count ∀ syntax (direction):** `{n m : Nat, a b}` — only `: Nat` + bare type vars lower in v1 |
| D18 | **Surface nested BoundCovers:** **not** for v1 — check **after lower** on Core `BoundCovers` |
| D19 | **File budget:** prefer few large modules (current: Kernel, Oracle, Commit, Typing) |

---

## 3. Architecture

```text
.fhm source
    │
    ▼
Parse (bounds-aware Surface)          [SurfaceLang + Parse — B]
    │
    ▼
eraseBounds                           [FHM/Bounds — future Erase]
    │
    ├──────────────────► BoundAnn
    ▼
{ program // DoesntContainBounds }    // BL → List t
    │
    ▼
lower / SCC / PatComp                 [SurfaceBridge — absurd .bl only]
    │
    ▼
Core.Expr
    │
    ▼
Infer / elaborate                     [InferW — UNCHANGED]
    │  τ_HM
    ▼
HasBounds                             [FHM/Bounds/Typing.lean]
    │  β
    ▼
BoundCovers (List β)                  [same file]
  vs AllMatchesExhaustive (non-List / HM mode)
    │
    ▼
evaluate                              [UNCHANGED]
```

### Outer safety (BL mode) — target theorem

```text
TypeOfElabHM Γ e τ
∧ HasBounds … e τ β
∧ (BoundCovers … β branches  ∨  non-List exhaustiveness)
⇒  never stuck
∧  (optional later) closed values satisfy length intervals
```

`TypeOfElabHM.progress` unchanged; composite lemmas in Bounds/Pipeline.

---

## 4. Current codebase (as of 2026-07-29)

```text
FHM/Bounds/
  Kernel.lean    # Count, constraints, DemandOK, Interval, path helpers
  Oracle.lean    # checkValid / solve / unique + axioms + Z3 bridge
  Commit.lean    # NarrowingEvidence, PolicyKind, decideCommit
  Typing.lean    # BoundInfo, Agrees, Sub, HasBounds, CheckBounds, BoundCovers
```

| Area | Status |
|------|--------|
| P1 kernel + BLSketch rewire | **Done** |
| P2 BoundInfo ≅ Core Ty + HasBounds (List rules) | **Done** |
| P3 BoundCovers (Core flat patterns) | **Done** |
| Surface / erase / BoundAnn / CLI | **Not started** |
| Pipeline glue + composite progress | **Not started** |
| Bound schemes / stdlib | **Not started** |
| `Count.inf` | **TODO only** |
| Axiom collapse to Z3 | **Partial** (definitional oracles; axioms remain) |

---

## 5. Does the reshuffle cover everything?

### 5.1 Original plan → reshuffle mapping

| Original | Reshuffle | Status |
|----------|-----------|--------|
| P0 design freeze | P0 | Done (this memo) |
| P1 kernel extract | P1 | Done |
| P2 HasBounds on Core | P2 | Done (stronger: full BoundInfo mirror) |
| P3 BoundCovers + **progress composition** | P3 covers **done**; **progress split to P3.5/P4c** | Partial |
| P4 Surface B′ + erase + CLI | P4 | Pending |
| P5 schemes + stdlib | P5 | Pending |
| P6 polish / merge / axiom collapse / apply-σ / toggle | P6 | Pending |

### 5.2 Emergent work folded into reshuffle

| Emergent item | Where it sits now |
|---------------|-------------------|
| BoundInfo must track **composites** (not list/arrow-only POC) | **Done** in P2 (`custom` + `Agrees`) |
| `Count.inf` + default list `hi = inf` | **P3.5a** (before/with honest defaults; before polished UX) |
| `HasBounds.weaken_Δ` unprovable (`checkValid` not mono) | **On-demand** — drop until induction needs it; then semantic `Valid` or mono hyp |
| BoundAnn keying (post-Infer / bindings) | **P3.5b design lock** before P4 erase |
| HM mode = frontend reject | **P4 / Live** |
| `{n : Nat, a}` scheme syntax | **P4 surface + P5** |
| Core BoundCovers only; surface nested later | **D18** — after-lower check for v1 |
| Pair/`custom` **intro rules** for HasBounds | **When first composite demo needs them** (shape already exists) |
| Sub/join proof tweaks (`joinMin`, `ListShapeOK`, …) | **Locked** as implemented unless reopened |
| unique out of TypeOf / Commit policy / honest uniqueZ3 | **Done** (BLSketch + Bounds.Commit) |
| Definitional oracles | **Done**; full axiom collapse → **P6** |

### 5.3 Worth noting: **not** fully covered / still external

| Item | Notes |
|------|-------|
| **Head-binder packing / HM type holes** (`next-agent-brief-type-holes.md`) | Orthogonal HM UX; not required for bound `_`; not in reshuffle critical path |
| **Surface nested BoundCovers ⟷ SurfaceCovers mutual** | Explicitly deferred (D18); only if pre-lower diagnostics needed |
| **Semantic length safety** (`length(v) ∈ [lo,hi]`) | Named in outer safety; no phase owns implementation yet → **P6 or P3.5c optional** |
| **README / Headlines “Bounds experimental”** | Original P0 checkbox still open |
| **BLSketch retirement / Core-only demos** | Implied by D13; no explicit “delete BLSketch TypeOf” milestone |
| **libz3 FFI vs subprocess** | Never in plan; stays out |
| **zip/take/drop, value-Nat in types** | BLSketch non-goals; still out |
| **Inferred count generalisation / principal bounds** | Still non-goals |
| **ConstraintTypeSystem.lean revival** | Still out |
| **Playground/editor hover for bounds** | Only under P6 “toggle/polish”; thin |
| **CI job for FHMBounds** | Not specified |
| **Proving `checkValid_sound` from Z3** | In collapse memo / P6, not blocking Surface |

If something must not fall through cracks: add explicit owners for **semantic length lemmas** and **README pointer** (below).

---

## 6. Reshuffled residual plan

### Done

- **P0** — Dual-stack / B′ locks (living memo)  
- **P1** — `Kernel` / `Oracle` / `Commit`; BLSketch rewire  
- **P2** — `Typing`: BoundInfo, Agrees, Sub, HasBounds, CheckBounds  
- **P3** — `BoundCovers` + branch detectors (Core only)

### Next (reshuffled)

#### P3.5a — `Count.inf` (small, recommended before polished defaults)

- Add `Count.inf`; eval / DemandOK / Z3 encode / `defaultBounds` list hi = inf  
- Unblocks honest “unknown length” without lying with `[0,0]`

#### P3.5b — BoundAnn + pipeline contract

- **Shapes in** `FHM/Bounds/Typing.lean` (awaiting sign-off): `AnnoCount`, `BoundAnn`,
  `ElabCount`/`ElabAnn`, `ProgramBoundAnns`, `MeetsAscription`, `MatchSafe`, `BoundProgramOK`
- Binding-level ascriptions / post-Infer check (avoid path reindexing hell)
- List `β` → `BoundCovers`; non-List → abstract `hmExh` (AllMatchesExhaustive)
#### P3.5c — Core-only vertical demos (before Surface)

- **Done:** `FHM/Bounds/Examples.lean` — HasBounds Nil/Cons, BoundCovers full/wild,
  nil-only/cons-only under `checkValid` hyp, MatchSafe  
- Optional later: composite progress lemma; full `WellBound` with List `CtorEnv`  

#### P4 — Surface B′

1. `Surface.Ty` + Parse + Pretty (`bl`, bound holes, optional Nat binders in schemes)  
2. `eraseBounds` + `DoesntContainBounds` + absurd-`.bl` in SurfaceBridge/Pretty  
3. HM mode reject BL syntax; BL mode flag (`--bl` candidate)  
4. Wire HasBounds + BoundCovers after Infer  

**Exit:** `.fhm` with `BL 0 5 Int` → List + bound check + smarter List matches.

#### P5 — Bound schemes + stdlib

- `{n m : Nat, a b}` erase → BoundAnn schemes  
- Pack/instantiate with Sub/solve + Commit  
- Demos: map, filter, append, …

#### P6 — Polish / hygiene / merge

- Axiom collapse (encoding lemmas; delete BL triple axioms) — see collapse memo  
- Apply-σ / normalise BoundInfo for pretty  
- Default commit policy product choice  
- Composite progress + optional semantic length lemmas  
- Playground toggle; README/Headlines note  
- Merge `FHM/Bounds` into `fhm`; retire `blt` when ready  
- Optional: head-binder packing (type-holes brief)  
- Optional: Surface nested BoundCovers if pre-lower UX demands it  
- Optional: HasBounds rules for Pair.Mk etc. when demos need them  
- Optional: restated `weaken_Δ` if proofs demand it  

---

## 7. Pipeline / REPL toggle

| Mode | Front | Coverage | Bound pass |
|------|-------|----------|------------|
| **HM (default)** | Parse; **reject** BL syntax | `checkExhaustive` / AllMatchesExhaustive | skip |
| **BL** | Parse BL; erase; lower | `BoundCovers` for List β; ctor exhaustiveness for non-List | HasBounds |

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

---

## 9. Risk register (updated)

| Risk | Mitigation |
|------|------------|
| BoundAnn paths break under lower/elab | Binding-level + post-Infer (P3.5b) |
| Default `[0,0]` misleads | P3.5a `Count.inf` |
| SurfaceBridge touch radius | Absurd-bl only |
| Z3 in default proof cone | Optional `FHMBounds` |
| Scope creep into unify | Hard no |
| BoundCovers vs AllMatchesExhaustive | Pipeline contract P3.5b |
| `checkValid` non-monotonicity | Don’t state weaken_Δ; use Valid if mono needed |

---

## 10. Success criteria

- [x] Optional Bounds build: kernel + Typing (HasBounds, BoundCovers)  
- [x] Core/InferW free of bound feature work  
- [ ] Default `lake build` FHM pure; Headlines guard (still true; document Bounds as optional)  
- [ ] `BL _ 5 t` erases to List; hole in BoundAnn  
- [ ] Nil-only match under proved empty upper bound (Core demo and/or surface)  
- [ ] REPL/CLI HM vs BL mode  
- [ ] Composite never-stuck under HasBounds + BoundCovers (or documented partial)  

---

## 11. One-liner

> **B′ dual-stack:** BoundInfo mirrors Core Ty with intervals on List; HasBounds + BoundCovers on Core are in; next is inf defaults, BoundAnn contract, Core demos, then Surface erase + pipeline — never put intervals in Core or InferW.

---

## 12. Next action

1. **P3.5b** quick BoundAnn/pipeline lock (or skip if jumping straight to Surface with binding-level BoundAnn only)  
2. **P3.5a** `Count.inf` if defaults matter before UX  
3. **P3.5c** Core demos  
4. **P4** Surface + erase + `--bl`  

Recommend: **P3.5b (short) → P3.5c demos → P4**, with **P3.5a** either before P4 pretty or immediately when printing bounds.
