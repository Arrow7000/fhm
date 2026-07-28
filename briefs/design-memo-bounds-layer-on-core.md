# Design memo: bounds layer on Core (B′ plan)

**Status:** agreed direction — implement in phases  
**Date:** 2026-07-28  
**Repo:** `/Users/aron/dev/blt` (sandbox; merge back into `fhm` later as optional package)  
**Supersedes / builds on:** dual-stack investigation; uniqueness-out-of-TypeOf; axiom-collapse (partial); type-holes research (orthogonal)

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
| D5 | **`eraseBounds`** rewrites `BL lo hi t` → surface `List t` (or equivalent sugar that lowers to List); **bound holes `_` only in BoundAnn** — HM side always knows “list of `t`” |
| D6 | **`DoesntContainBounds`** on erased programs; SurfaceBridge (and other exhaustive `Surface.Ty` matches) get **absurd `.bl` arms** via that proof — **no** bound semantics in the bridge |
| D7 | **No second SurfaceBridge / PatComp / SCC** — existing lower runs on bounds-free surface |
| D8 | **Coverage:** keep `AllMatchesExhaustive` / `checkExhaustive`; add **`BoundCovers`** in Bounds package; compose at pipeline |
| D9 | **Uniqueness:** not a premise of declarative `HasBounds`; algo/commit policy only (port BLSketch `CommitHandler` ideas) |
| D10 | **Oracles:** Z3 behind optional target; BL-level axioms OK initially; collapse-to-Z3 later |
| D11 | **Containment:** all new logic under `FHM/Bounds/` (or equivalent); lake lib e.g. `FHMBounds`; default `FHM` roots stay pure |
| D12 | **Work here in `blt` for now**; no merge-back/dir housekeeping required yet |
| D13 | **BLSketch toy Expr/TypeOf:** reference + demos; do not deepen; extract mechanisms into Bounds |

---

## 3. Architecture

```text
.fhm source
    │
    ▼
Parse (bounds-aware Surface)          [SurfaceLang + Parse — B]
    │
    ▼
eraseBounds                           [FHM/Bounds/Erase.lean]
    │
    ├──────────────────► BoundAnn     (intervals, holes, count schemes, paths)
    ▼
{ program // DoesntContainBounds }    // BL → List t; no bl left in tree
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
boundCheck / HasBounds                [FHM/Bounds — parasitic on τ_HM]
    │
    ▼
BoundCovers  (BL mode)                [FHM/Bounds/Covers.lean]
  vs checkExhaustive (HM mode / non-List)
    │
    ▼
evaluate                              [UNCHANGED]
```

### Parasitic bound judgment

```text
HasBounds Δ Γ e τ β
```

- `e` : Core `Expr`
- `τ` : HM type **already known** (Infer / TypeOfElabHM)
- `β` : bound info at that shape (payload on List leaves; structural on arrows)
- **No** `TypeOfHM` premise inside each ctor; outer theorems conjoin HM typing

### Outer safety (BL mode)

```text
TypeOfElabHM Γ e τ
∧ HasBounds … e τ β
∧ BoundCovers …
⇒  never stuck
∧  (optional later) closed values satisfy length intervals
```

`TypeOfElabHM.progress` stays as-is; composite lemmas live in Bounds/Pipeline.

---

## 4. Surface & erase (detail)

### Surface extensions (minimal v1)

- `Surface.Ty`: `bl (lo hi : BoundCount) (elem : Ty)` (names flexible)
- `BoundCount`: lit / var / ops / **hole** (`_`)
- Schemes: optional **count binders** then type binders (story A at surface); erase strips counts into BoundAnn, leaves type-only `PolyTy` for HM
- Parse/Pretty/editor: BL syntax + holes in **bound** slots only for v1

### `eraseBounds`

| Input | HM-facing output | BoundAnn |
|-------|------------------|----------|
| `BL lo hi t` | `List t` (surface form that lowers to List) | record `lo`, `hi` at path |
| `BL _ hi t` | `List t` | `lo = hole`, `hi = …` |
| Arrow / pair / custom | recurse | recurse |
| No BL | identity | empty / none |

**Invariant:** `DoesntContainBounds (erase p).1`

### SurfaceBridge edits

- Thread bounds-free programs (subtype or proof argument), **or** match on `Surface.Ty` with:

  ```lean
  | .bl .. => nomatch hFree   -- absurd
  ```

- **Do not** implement Sub, Z3, or BoundAnn filling in the bridge
- Prefer a single shared `Ty` recursor helper that packages absurd-bl for Pretty/Bridge/WT

---

## 5. Bounds package layout (target)

```text
FHM/Bounds/
  Count.lean          # Count, Constraint, Forall/Exists problems (from BLSketch)
  Oracle.lean         # checkValid / solve / unique defs + axioms (or re-export Z3)
  Commit.lean         # PolicyKind, CommitHandler (from BLSketch PR3a)
  BoundInfo.lean      # β structure over Core.Ty shapes
  Sub.lean            # Sub Δ on BoundInfo / List intervals
  Erase.lean          # eraseBounds, DoesntContainBounds
  HasBounds.lean      # parasitic judgment + Check dual
  Covers.lean         # BoundCovers (List nil-only / cons-only / full)
  Synth.lean          # algorithmic bound pass (optional early)
  Pipeline.lean       # glue: Infer + boundCheck + covers
  Pretty.lean         # bounds display
```

Extract from `FHM/BLSketch.lean` rather than rewrite arithmetic/oracle from scratch where possible.

Lake (later / when convenient):

```toml
[[lean_lib]]
name = "FHMBounds"
# not in defaultTargets
roots = ["FHM.Bounds..."]
```

Default `FHM` roots: **no** Bounds (or only Bounds-free modules if we temporarily put Erase proofs that depend on Surface without Z3 — prefer Bounds imports Surface, not the reverse for Z3).

**Import rule:** `FHM.Core` / `InferW` never import Bounds. Bounds imports Core/InferW/Surface as needed.

---

## 6. Phased plan

### Phase 0 — Spec freeze (this memo)

- [x] Dual-stack, B′, erase, DoesntContainBounds, BoundCovers, package shape  
- [ ] Optional: one-page README pointer / Headlines note “Bounds experimental”

**Exit:** implementers treat D1–D13 as locked unless reopened.

---

### Phase 1 — Kernel extract (no Core Expr yet)

**Deliverable:** `FHM/Bounds/{Count,Oracle,Commit,Sub}` (or single file initially) ported from BLSketch; builds under optional target; demos/oracles still work.

- Port Count / constraints / problems / Sub on intervals  
- Port definitional oracles + soundness axioms  
- Port Commit policy types (default `uniqueOnly`)  
- Leave toy `TypeOf` in BLSketch as-is or thin-wrap  

**Exit:** `lake build FHMBounds` (or `FHMZ3` roots extended); no Surface changes yet.

**Estimate:** small–medium (mostly move/split + fix imports).

---

### Phase 2 — BoundInfo + HasBounds on Core fragment

**Deliverable:** parasitic judgment for **List-heavy fragment** on hand-built Core terms.

- `BoundInfo` / β for `List α` intervals; structural arrows  
- Rules: Nil, Cons, var mono, app (Sub/force), lambda, let mono, match Nil/Cons with Δ refine  
- Algorithmic check optional; declarative first  
- Theorems: local soundness relative to oracles (synth ⇒ HasBounds) if algo exists  

**Exit:** `#eval` / demos: `Cons x (Cons y Nil)` @ `List Int` ⇒ `BL 2 2`; simple Sub.

**Estimate:** medium (new judgment, not 20k InferW).

---

### Phase 3 — BoundCovers + progress composition

**Deliverable:** nil-only / cons-only / full List match coverage under Δ + Z3 `checkValid`.

- `BoundCovers` independent of `AllMatchesExhaustive`  
- Pipeline lemma: HM typed + BoundCovers (+ HasBounds) ⇒ never stuck for fragment  
- Do **not** edit Core.progress  

**Exit:** killer UX feature formal + runnable on Core terms.

**Estimate:** medium; highest user-visible dual-stack win.

---

### Phase 4 — Surface B′ (erase + absurd-bl)

**Deliverable:** users can write BL types; existing lower stack accepts erased programs.

1. Extend `Surface.Ty` (+ Parse, Pretty)  
2. `eraseBounds` + `DoesntContainBounds` + lemmas (subterms inherit)  
3. SurfaceBridge / Pretty / WT: absurd `.bl` (or subtype signatures)  
4. Wire BoundAnn paths through lower **reindexing** if paths are surface-based — prefer **post-Infer** ascriptions keyed by binding identity where possible to avoid path hell  
5. Live/CLI: `--bl` / mode flag  

**Binding / path strategy (prefer):**

- BoundAnn primarily on **binding ascriptions** and explicit type annotations (stable names/indices after lower), not every intermediate expr path  
- After Infer, check elaborated Core at known τ against those ascriptions  

**Exit:** `.fhm` with `BL 0 5 Int` lowers, infers as `List Int`, bound-checks.

**Estimate:** medium–large (Surface + bridge exhaustiveness + path/ascription design).

---

### Phase 5 — Bound schemes + stdlib

**Deliverable:** length-polymorphic APIs with explicit surface binders / `@` or ann packs.

- erase strips count telescope into BoundAnn scheme  
- HasBounds pack/instantiate with Sub/solve + commit policy  
- Demos: map, filter, append, etc.  

**Exit:** annotated stdlib demos through full pipeline.

---

### Phase 6 — Product polish (optional, parallelisable)

- Axiom collapse Phases C–D (encoding lemmas; delete BL triple axioms)  
- Apply-σ into BoundInfo for pretty  
- Default commit policy product choice  
- Playground toggle  
- Head-binder packing (HM-only; orthogonal brief)  
- Merge Bounds into `fhm` as optional lib; retire `blt` when ready  

---

## 7. Pipeline / REPL toggle

| Mode | Front | Coverage | Bound pass |
|------|-------|----------|------------|
| **HM (default)** | Parse; reject or ignore BL syntax | `checkExhaustive` | skip |
| **BL** | Parse BL; erase; lower | `BoundCovers` (+ ctor coverage for non-List as needed) | HasBounds / boundCheck |

Shared: Infer, elaborate, evaluate.

---

## 8. Explicitly deferred

| Item | Why |
|------|-----|
| Core `Ty.bl` | Destroys dual-stack value |
| InferW completeness for bounds | False / research |
| Unique in HasBounds | Wrong (policy only) |
| Full axiom collapse before Phase 1–3 | Hygiene, not blocker |
| Structural HM type holes (`Int → _ → Int`) | Separate brief; not required for bound `_` |
| Second full surface language | B′ rejects this |
| Deep BLSketch refactors (semantic NarrowingEvidence, etc.) | Extract what we need; don’t polish the toy |

---

## 9. Risk register

| Risk | Mitigation |
|------|------------|
| Path-keyed BoundAnn breaks under lower/elab | Prefer binding-level ascriptions; check post-Infer |
| `DoesntContainBounds` boilerplate | Shared recursor; erase lemmas once |
| SurfaceBridge 13k LOC touch radius | Only absurd-bl / signature; no logic |
| Z3 in default proof cone | Optional lake target; Live may link binary with flag |
| Scope creep into unify | Hard no in review |
| BoundCovers vs AllMatchesExhaustive confusion | Docs + separate names; compose only in Pipeline |

---

## 10. Success criteria (program-level)

- [ ] Default `lake build` (FHM): still pure HM; Headlines axiom guard green  
- [ ] Optional Bounds build: HasBounds + BoundCovers demos green (z3 on PATH)  
- [ ] Core/InferW: no bound-related feature work (diff review)  
- [ ] `BL _ 5 t` erases to List; hole only in BoundAnn  
- [ ] Nil-only match accepted under proved empty upper bound  
- [ ] REPL/CLI can run same file path in HM vs BL mode without Core fork  

---

## 11. Suggested first implementation PR sequence

| PR | Content | Depends |
|----|---------|---------|
| **P0** | This memo landed; optional README one-liner | — |
| **P1** | Create `FHM/Bounds/` skeleton; move Count/Oracle/Commit from BLSketch | P0 |
| **P2** | BoundInfo + HasBounds Nil/Cons/app fragment + demos | P1 |
| **P3** | BoundCovers + composite safety for fragment | P2 |
| **P4a** | Surface `bl` + Parse + Pretty | P1 |
| **P4b** | eraseBounds + DoesntContainBounds + absurd-bl in bridge | P4a |
| **P4c** | Pipeline + CLI `--bl` | P2, P4b |
| **P5** | Schemes / stdlib | P4c |

P4a can overlap P2 once Surface deps are clear.

---

## 12. Open / resolved product points

1. **Surface syntax for count ∀ (resolved direction):** extend `{a b}` schemes to  
   `{n m : Nat, a b}` — `n`/`m` are Nat (bound) binders; `a`/`b` remain type vars.  
   Parser may accept other annotations on forall binders later; **lowering only** for  
   `: Nat` (and bare type vars as today). No lowering for other kinds in v1.

2. **BoundAnn keying:** de Bruijn after lower vs surface names vs post-elab only — still open when Phase 4 lands.

3. **HM mode vs BL mode (clarified):**  
   Core/`TypeOf*HM` never see `BL` either way — bounds are erased before Core.  
   The mode choice is **frontend policy** only:  
   - **HM mode:** if source uses BL syntax (`BL …`, Nat scheme binders, …), **reject at parse/validate** (“enable BL mode”) instead of erase-and-forget.  
   - **BL mode:** erase → lower → Infer → boundCheck + BoundCovers.  
   “Silent erase without bound-check” = accept `BL 0 5 Int`, drop the interval, succeed as `List Int` under pure HM — looks fine, never checked bounds. Not a Core typing issue; a product/UX footgun.
4. **Join of match branch bounds (resolved):** **min lo / max hi** (as in BLSketch `Interval.join` / `joinBranchTy`). Requiring equal bounds is too strict.

5. **Lake / CLI names:** `FHMBounds` target; CLI flag name still open (`--bl` candidate).

6. **Bounds package file budget:** start with **≤3–4 files** (P1 uses exactly three: Kernel, Oracle, Commit). Split later only when stable.
---

## 13. One-liner

> **B′ dual-stack:** one bounds-aware surface; erase `BL … t` to `List t` + BoundAnn; prove `DoesntContainBounds` so the existing lower stack only needs absurd `.bl` cases; run unchanged Infer on Core; check bounds and BoundCovers in `FHM/Bounds/`; never put intervals in Core or InferW.

---

## 14. Next action

Start **P1** (Bounds skeleton + extract from BLSketch) unless a syntax bikeshed on P4a is preferred first for demos — **recommend P1 → P2** so Core-attached judgments exist before Surface noise.
