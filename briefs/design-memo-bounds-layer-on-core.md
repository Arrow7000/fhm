# Design memo: bounds layer on Core (B′ plan)

**Status:** living plan — slices **0–7 Done** (pack/inst + D24 fresh List λ); **next = slice 8 stdlib demos**  
**Updated:** 2026-07-29 (session handoff)  
**Repo:** `/Users/aron/dev/blt` (sandbox; merge back into `fhm` later as optional package)  
**Canonical doc for this integration** (plus satellite briefs below)

**Related briefs (not replaced):**

| Doc | Role |
|-----|------|
| `design-memo-collapse-bl-axioms-to-z3.md` | Oracle TCB / prove BL axioms from Z3 |
| `design-p1-bounds-kernel-api.md` | P1 conceptual (API now in Lean) |
| `next-agent-brief-remove-unique-from-typeof.md` | BLSketch uniqueness exit (done) |
| `next-agent-brief-type-holes.md` | HM type holes / head-binder packing (**orthogonal**) |

**Handoff tip:** start at §6 linear table + §12–13; scratch demos under `scratch/bl-*.fhm`; build `lake build FHMBounds blt`.

---

## 1. Goal

Add a **BoundedList refinement layer** on top of the existing FHM Hindley–Milner stack **without** rewriting Core, InferW, TypeOf*, PatComp, or vanilla exhaustiveness metatheory.

| User sees | Implementation |
|-----------|----------------|
| One language (optional BL syntax) | **B′:** bounds-aware surface + erase + bound passes |
| Smarter List matches, bound schemes, intervals in types | Sidecar `BoundsAnnTy` + `HasBounds` / `BoundCovers` |
| REPL toggle BL on/off | Pipeline flag; HM spine identical after erase |
| Pure HM product still exists | Default lake target never imports Bounds/Z3 axioms |

**Non-goals (v1):** fuse `bl` into Core `Ty`; teach Unify/Infer about intervals; principal bounds / full inferred count gen; type-passing counts; full dual surface frontend; finish BLSketch axiom collapse before the layer exists.

**Origin lock (D22):** list intervals are **never invented from bare `List` / HM `Ty` alone**. Every `β = .list lo hi _` comes from an origin (see §2.1). `agreesTemplate` (ex-`defaultBounds`) / erase `defaultListAnn` remain **scaffold debt** for nested List-as-elem shapes — not Live ascription synth. `Count.inf` is vocabulary for “unbounded as a *result* of analysis or an explicit surface count,” not a stamp on every unascribed `List`.

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
| D19 | **File budget:** prefer few large modules (Kernel, Oracle, Commit, Ann, Typing, Erase, Pipeline, Check) |
| D20 | **Erase packages anns with binders** (`ErasedTy` / `ErasedBinding`); not a free-floating map beside an unrelated program |
| D21 | **Gate ≠ erase:** `hmRequireNoBl` is D16 only; `eraseProgram` always erases; Live composes them |
| D22 | **Origin-based bounds:** intervals flow from constructors / ascriptions / env / apps / joins — never from `agreesTemplate τ` as Live synth |
| D23 | **Surface Count ↔ Kernel Count:** ground ops + `inf` early; `Count.var` with schemes — do not forget ops by bundling them with schemes |
| D24 | **Unascribed List params:** fresh `?lo`/`?hi`; constrain by uses; else generalise (scheme-quantify); mid-case → Commit on **output-visible** outs (`uniqueOnly` = annotate-or-fail; swappable) |

**D16 clarified:** “reject” is **UX fail-fast** when BL mode is off (`--bl` absent): clear error after parse, not silent erase. It is *not* about Core `TypeOf*` — Core `Ty` has no `.bl`, so HM typing never sees bounds. Without erase, `lowerTy .bl = none` already fails; D16 is the intentional HM-mode message.

### 2.1 Where list bounds come from (end model)

| Origin | How `lo`/`hi` arise |
|--------|---------------------|
| Concrete Nil / Cons spine | HasBounds `nil` / `cons` (`[0,0]`, then `+1`) |
| Surface ascription `BL …` | Erase → `BoundsAnnTy`; check synth ⊆ / meets ascription (`MeetsAscription`) |
| Bound variable | Lookup in `bctx` — **solid ann:** ascribed β (§2.3 A+B); else origin-synth |
| Application | Function arrow’s result `βr`; arg must `Sub` into domain `βa` |
| Match branches | `joinBoundsTy` — min lo / max hi (D15) |
| Scheme / Nat binder | Slice 7: instantiate `{n : Nat,…}`; counts mention `n` |

**Not an origin:** “this HM type is `List α`, so invent `[0,0]` or `[0,inf]`.”

### 2.2 Unascribed `List` λ-params / binders (D24)

When `ErasedBinding.ann = none` (bare `List` or no ascription):

1. **Allocate** fresh inferable counts `?lo`, `?hi` for that parameter (not a concrete default interval).
2. **Constrain** them by every use (args passed to functions whose domains demand intervals; match refinements; etc.).
3. **If unconstrained** (e.g. ignored `l`): **generalise** — quantify the function’s bound scheme over those count vars (polymorphic in `lo`/`hi`). Same family as slice 7 Nat binders; v1 may only fully shine once schemes exist.
4. **Mid-case** — constraints sat but not unique on some outs:
   - Ambiguity is a **product problem only when those outs are output-visible** (escape into the exported/return bounds). Internal witnesses that all agree on the observable type are harmless (classic: factorizations of `12` when only `BL 12 12` is exported).
   - Then **Commit**: product default **`uniqueOnly`** — accept only a unique solution on those outs; otherwise **reject** (annotate-or-fail / just fail until the user ascribes). **`anyWitness`** (pick any model) stays available and swappable via `PolicyKind` / `CommitHandler` — not hard-wired into `HasBounds`.

This is D9 applied at λ-params: uniqueness ∉ declarative typing; elaborator policy only. Still **never** invent `[0,inf]` from `Ty`.

### 2.3 Ascription vs `bctx` (important follow-up)

**Was (slices 4–6):** Meet used origin ⊆ ascription, but `bctx` stored the **tighter origin**. Same surface `BL 0 5` matched differently depending on RHS — leaky BL abstraction.

**Now (A+B, solid anns):** when `BoundsAnnTy.toBoundsTy?` succeeds, Live pushes the **ascribed** `β` into `bctx` (`checkLetSpine` / `checkProgramMatchesSpine`) and walks the RHS under demand (`checkAgainst` / matches peel). List λ-params take domain bounds from the binder ascription; Infer’s singleton `letRec` wrapper is peeled the same way. Holes / missing anns still synth-then-pin and push origin (D24 for unascribed List λs).

**Still open:** hole-bearing anns pin-to-synth then push origin (not the pinned ascription template); head-binder `(xs : BL …)` params are not yet folded into binder demand (colon `BL → …` works); declarative `HasBounds.letMono` optional later align.

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
    │  τ_HM   (pretty: List; under --bl also print/JSON bounds: BL …)
    ▼
ofLower (binderEnv)                   [Bounds/Pipeline — demo spine today]
    │  ProgramBoundsAnns
    ▼
HasBounds synth + MeetsAscription     [Synth/Check — slices 4–5]
    │  origin β; meet ⊆ ann; `_` pin-to-synth
    │  **bctx ← ascribed β when solid** (§2.3 A+B); else origin
    ▼
BoundCovers / MatchSafe               [Check.checkProgramMatches — slice 6]
  vs checkExhaustive (HM mode / non-List under bl via coreCtorCoverage)
    │
    ▼
evaluate                              [UNCHANGED]
```

### Live today (2026-07-29)

```text
parse → [hmRequireNoBl if not --bl] → eraseProgram → lower/infer
  → if --bl:
       ofLower + checkProgramAnns (synth + pin holes + Sub)
       checkProgramMatches (BoundCovers / ctor coverage)   # NOT surface checkExhaustive
  → else: checkExhaustive (surface)
  → elab → eval
```

**Slices 4–7 in Live.** Open: §2.3 residuals (holes / head-binder params); `@TODO(bounds-path-Δ)` nested refine; fuller Commit on escape (rank-1 `checkSubInst` today); hover still prints HM `List`.

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
  Ann.lean       # AnnoCount, BoundsAnnTy, ProgramBoundsAnns (Z3-free)
  Typing.lean    # BoundsTy, Agrees, Sub, HasBounds, CheckBounds, BoundCovers
                 # + Elab* / MatchSafe / BoundProgramOK (imports Ann)
  Synth.lean     # checkBounds / inferBounds / synthBounds / pinHoles (executable)
  Erase.lean     # ErasedTy / ErasedBinding / ErasedProgram (anns with erase)
  Pipeline.lean  # BoundsMode, hmRequireNoBl, ofLower, Bool detectors
  Check.lean     # checkProgramAnns + checkProgramMatches (Live --bl; Z3)
  Examples.lean  # Core-only HasBounds / BoundCovers / MatchSafe demos

Live / CLI / editor:
  --bl: D16 gate; erase; ofLower; checkProgramAnns; checkProgramMatches
  scratch/bl-*.fhm demos; watch-live.sh --bl; diagnose erases to List
  editors try `blt` then `fhm`

Surface:
  Count: lit | inf | add/mul/pred/min/max  (slice 3); var → slice 7
  CountSlot = hole | solid Count; Ty.bl; Parse BL / ∞ / _; Pretty
```

| Area | Status |
|------|--------|
| P1–P3.5c kernel / BoundsTy / BoundCovers / Ann / demos | **Done** |
| P4a–P4c Surface BL + erase + Live `--bl` + diagnose | **Done** |
| Slice 1 `Count.inf` + ExtNat | **Done** |
| Slice 2 binder spine / ofLower | **Done** |
| Slice 3 surface ground Count | **Done** |
| Slice 4 origin HasBounds synth | **Done** |
| Slice 5 hole pin-to-synth | **Done** |
| Slice 6 BoundCovers in Live | **Done** |
| Slice 7 bound schemes / D24 | **Done** (pack/inst + fresh `?lo`/`?hi`; rank-1 `checkSubInst`) |
| Slice 8–9 stdlib + E2E suite | **Next** / not started |
| §2.3 ascription wins in `bctx` | **Done** for solid anns (A+B); holes/head-binders still open |
| Axiom collapse to Z3 | **Partial** / post-E2E |

---

## 5. Does the reshuffle cover everything?

### 5.1 Original plan → reshuffle mapping

| Original | Reshuffle | Status |
|----------|-----------|--------|
| P0 design freeze | P0 | Done (this memo) |
| P1 kernel extract | P1 | Done |
| P2 HasBounds on Core | P2 | Done (stronger: full BoundsTy mirror) |
| P3 BoundCovers + **progress composition** | P3 covers **done**; **progress still open** | Partial |
| P4 Surface B′ + erase + CLI | P4 + slices 3–6 | **Done** through BoundCovers in Live |
| P5 schemes + stdlib | P5 → slices **7–8** | **Next** |
| P6 polish / merge / axiom collapse / apply-σ / toggle | P6 | Pending (post-E2E OK) |

### 5.2 Emergent work folded into reshuffle

| Emergent item | Where it sits now |
|---------------|-------------------|
| BoundsTy must track **composites** (not list/arrow-only POC) | **Done** in P2 (`custom` + `Agrees`) |
| `Count.inf` as Kernel vocabulary (not List default) | **Done** (slice 1) |
| `HasBounds.weaken_Δ` unprovable (`checkValid` not mono) | **On-demand** |
| BoundsAnnTy keying (post-Infer / bindings) | **P3.5b** shapes; **P4b** producers; **ofLower** spine OK for Live |
| HM mode = frontend fail-fast | **Done** in Live (`hmRequireNoBl` / `--bl`) |
| `{n : Nat, a}` scheme syntax | **Slice 7** |
| Core BoundCovers only; surface nested later | **D18**; BoundCovers **wired in Live** (slice 6) |
| **Live imports Bounds → Oracle → Z3 just to erase** | **Fixed** by **P4c-thin** (`Ann.lean`); Check still pulls Z3 |
| Diagnose path does not erase (BL buffers fail hover) | **Fixed** by **P4c-diagnose** |
| REPL prints `List` not `BL` after erase | HM types stay `List`; under `--bl`, **bounds:** lines show `BL …` |
| Editor dual `blt`/`fhm` binary lookup | Sandbox artifact; `@TODO(merge-to-fhm)` in editors |
| **`defaultBounds` / erase `defaultListAnn` invent intervals** | Live synth **done**; residual `agreesTemplate` / `defaultListAnn` = nested-elem debt |
| **Ascription vs `bctx` (origin vs ann)** | **§2.3** — solid Done (A+B); holes / head-binder params still open |

### 5.3 Worth noting: **not** fully covered / still external

| Item | Notes |
|------|-------|
| **Head-binder packing / HM type holes** | Orthogonal; type-holes brief |
| **Surface nested BoundCovers** | D18 deferred |
| **Semantic length safety** | P6 or later |
| **README / Headlines “Bounds experimental”** | Still open |
| **Playground/editor hover for bounds anns** | Still HM `List` under `--bl` — prefer synth/erase `BL` later |
| **CI job for FHMBounds** | Not specified |
| **Ascription-in-`bctx` (§2.3)** | Solid Done (A+B); residual: holes, head-binder params |
| **Proving `checkValid_sound` from Z3** | Collapse memo / P6 |

---

## 6. Residual plan — linear path to E2E BL experience

**E2E means runtime product:** `.fhm` with `BL`, full ground Count language, origin-based HasBounds check, smarter List matches, schemes for map/filter/append. Metatheory (progress composition, axiom collapse, erase `noBl` proofs) is **post-E2E hygiene**, not a blocker.

### Done through slice 6

- **P0–P3.5c** — Dual-stack; Kernel/Oracle/Commit; BoundsTy/HasBounds/BoundCovers; Ann; Examples  
- **P4a–P4c** — Surface `BL` + erase + Live `--bl` + thin Ann + diagnose  
- **Slices 1–2** — `Count.inf` / ExtNat; honest binder spine / ofLower  
- **Slice 3** — Surface ground Count (`inf`/`∞`, ops, `CountSlot`)  
- **Slice 4** — Origin `synthBounds` in Live (no `defaultBounds` on ascription path)  
- **Slice 5** — Hole pin-to-synth + Sub  
- **Slice 6** — `checkProgramMatches` / BoundCovers under `--bl`

### Linear slices (do in order)

| # | Slice | Delivers | Exit |
|---|--------|----------|------|
| **0** | Docs / status honesty | Memo + Pipeline/Live headers match reality; D22–D23 locked | No “HasBounds wired” claims |
| **1** | `Count.inf` + `ExtNat` + NoInf→Z3 | Kernel ℕ∪{∞}; normalize; total `countToExpr` under `NoInf` | **Done** |
| **2** | Honest binder spine | `groups.reverse.flatMap` (0=innermost); `ofLower` after infer | **Done** |
| **3** | Surface ground Count | ops + `inf`/`∞`; parse / pretty / erase → Kernel | **Done** |
| **4** | HasBounds synth | Executable Core→`β` from origins (D22); kill Live `defaultBounds` | **Done** |
| **5** | Elab holes + solve | Pin `_` to synth Counts, then `Sub` | **Done** |
| **6** | BoundCovers in Live | List matches → BoundCovers/MatchSafe; else HM exh | Nil-only when `hi=0`; Cons-only when `lo≥1` | **Done** |
| **7** | Bound schemes | `{n m : Nat, a b}` + pack/inst; D24 fresh `?lo`/`?hi` + generalise | `bl-scheme-id`, `bl-unascribed-list-lam` | **Done** |
| **8** | Stdlib demos | map / filter / append with bound schemes | Scratch demos under `--bl` |
| **9** | E2E gate suite | Fixed demos checklist | BL experience green |

### 6.1 Slice 3 — Surface ground Count (D23) ✅

**Goal:** surface bound slots speak the same ground arithmetic as Kernel (minus `var` → slice 7).

**AST** (`SurfaceLang`):

```text
Count     ::= lit Nat | inf
            | add Count Count | mul Count Count | pred Count
            | min Count Count | max Count Count
CountSlot ::= hole | solid Count     -- BL lo/hi only; mirrors AnnoCount
```

- **`inf` keyword + `∞` punct** — both parse; pretty prints **`∞`**.
- **Exclude `var`** — still P5 / slice 7 with `{n : Nat,…}`.
- Hygienic: holes cannot nest under ops (not inhabitable in `Count`).

**Parse** (`Surface.Parse.count`; prec: `+` < `*` < FP app < atom):

| Form | Notes |
|------|--------|
| `0`, `5`, `_` | `_` only as whole lo/hi atom |
| `inf` / `∞` | both; `inf` reserved keyword |
| `pred c`, `min c d`, `max c d` | FP-style; atom args (parens on compounds) |
| `c + c`, `c * c` | infix (`*` is `Punct.star`, not expr binop) |

Reject bare idents (`n`) until slice 7. Reject nested holes (`BL (_ + 1) 5 t`).

**Pretty** — `Surface.Count.prettyAux` with prec (left-assoc `+`/`*`; FP apps take atom prec).

**Erase** (`eraseCount : Surface.CountSlot → AnnoCount`): `hole` → `.hole`; else `.solid` (Kernel `Count`).

**DoesntContainBounds / detectors:** unchanged (BL is still the bounds marker; count ops live only inside `Ty.bl`).

### 6.2 Slice 4 — Origin HasBounds synth (D22) ✅

**Goal:** Live `--bl` synthesizes `β` from Core origins (Nil/Cons/var/app/let), not `defaultBounds τ`.

**Delivered:**
- [`FHM/Bounds/Synth.lean`](FHM/Bounds/Synth.lean) — `checkBounds` / `inferBounds` / `synthBounds`
- [`FHM/Bounds/Check.lean`](FHM/Bounds/Check.lean) — `checkLetSpine` over Infer `letRec`/`letIn`; MeetsAscription via Z3 `Sub`
- Live passes `eOut` + `τ`; no `defaultBounds` on this path

**Exit demos:** `scratch/bl-synth-ok.fhm` (`BL 2 2` ← `[1,2]` OK); `scratch/bl-synth-fail.fhm` (`BL 0 0` ← `[1,2]` fail).

**Deferred:** D24 fresh `?lo`/`?hi` for unascribed List λs (slice 7); nested-Nil `agreesTemplate` List-elem debt; path-Δ refine threading (`@TODO(bounds-path-Δ)`).

**Editor follow-up (not blocking):** under `--bl`, hover/diagnose still show HM `List` — should prefer erase/synth `BL …` when bounds mode is on.

### 6.3 Slice 5 — Hole elab pin-to-synth ✅

**Policy:** each ascription `_` copies the Count from the matching slot of origin-synth `β`, then `checkSub β β_pinned`. Not Z3 `anyWitness` / `uniqueOnly`.

**Delivered:** `pinHoles` / `checkMeetsAscriptionPinned` in Synth; Live binder/body anns use pinned meet.

**Exit demos:** `scratch/bl-hole-ok.fhm` (`BL _ 5` ← `[1,2]`); `scratch/bl-hole-fail.fhm` (`BL _ 0` ← `[1,2]` fail).

### 6.4 Slice 6 — BoundCovers in Live ✅

**Goal:** under `--bl`, List matches use BoundCovers (not surface `checkExhaustive`).

**Delivered:**
- `checkBoundCovers` / `coreCtorCoverage` / `checkProgramMatches` in [`Check.lean`](FHM/Bounds/Check.lean)
- Live `--bl` replaces surface exhaustiveness with Core walk
- Nil-only when `hi=0`; Cons-only when `lo≥1`

**Exit demos:** `scratch/bl-nil-only.fhm`, `bl-cons-only.fhm`, `bl-nil-only-fail.fhm` (fail on `BL 2 2`).

**Deferred:** nested `nilRefine`/`consRefine` path-Δ stacking (`@TODO(bounds-path-Δ)`); §2.3 residuals (holes / head-binder params).

### Post-E2E hygiene (do not block product)

- Prove erase `noBl` / Pipeline Bool↔Prop sorries  
- Axiom collapse; apply-σ / pretty normalise; commit policy product choice  
- Composite progress + optional semantic length lemmas  
- README/Headlines; merge `FHM/Bounds` → `fhm`; drop editor dual lookup  
- Optional: head-binder packing; surface nested BoundCovers; Pair HasBounds; restated `weaken_Δ`  
- Remove remaining `defaultListAnn` / `defaultBounds` List invention from Erase/Typing if still present  

### Old P4 slice table (historical)

| Slice | Status |
|-------|--------|
| P4a / P4a-parse | **Done** |
| P4a-count-ops | → **slice 3** (elevated; not deferred to P5) |
| P4b / P4c / thin / diagnose / ann-visible | **Done** |
| P4c-hasbounds “v1” | **Scaffold only** → replaced by slices **4–6** |

## 7. Pipeline / REPL toggle

| Mode | Front | Coverage | Bound pass |
|------|-------|----------|------------|
| **HM (default)** | Parse; **`hmRequireNoBl`** (D16) | `checkExhaustive` | skip (erase still runs; anns not reported) |
| **BL (`--bl`)** | Parse BL; erase; lower | **BoundCovers** on Core (slice 6) | origin synth + pin holes + match coverage (slices 4–6) |

Shared: Infer, elaborate, evaluate. Diagnose always erases (hover as `List`).

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
| Inventing `[0,inf]` / `[0,0]` for bare `List` as end model | **Rejected (D22)** — scaffold only |
| Surface.Count.var | Slice 7 with Nat binders (ops are slice 3) |
| Ascription wins in `bctx` | **§2.3** — solid Done (A+B); holes / head-binder params open |
| Nested BoundCovers path-Δ | `@TODO(bounds-path-Δ)` in Check/Typing |
| `--bl` hover shows `BL` | Editor/diagnose still print HM `List` |

---

## 9. Risk register (updated)

| Risk | Mitigation |
|------|------------|
| BoundsAnnTy paths break under lower/elab | Binding-level + post-Infer; spine slice 2 |
| Scaffold `defaultBounds` mistaken for product | D22; Live path uses origin synth |
| Ascription meet ≠ env (`bctx` origin-tight) | **§2.3** — solid anns push ascription (A+B); holes still origin |
| SurfaceBridge touch radius | Absurd-bl only |
| Z3 in default / CLI proof cone | **P4c-thin**; Check may pull Z3 |
| Scope creep into unify | Hard no |
| BoundCovers vs AllMatchesExhaustive | Slice 6; HM exh otherwise |
| `checkValid` non-monotonicity | Don’t state weaken_Δ; use Valid if mono needed |
| Surface count ops forgotten | **D23 / slice 3** — before schemes |
| Unascribed List λ-param policy undecided | **Locked D24** |
| Synth hardness (oracle + join + Commit) | Approve executable API in Lean before proving |
| `outs` list too wide/narrow for uniqueness | Soft spot C — prefer output-visible / escape bounds |
| Editor looks for wrong CLI binary | Relink + dual lookup; revert on merge |

---

## 10. Success criteria

- [x] Optional Bounds build: kernel + Typing (HasBounds, BoundCovers)  
- [x] Core/InferW free of bound feature work  
- [ ] Default `lake build` FHM pure; Headlines guard (document Bounds as optional)  
- [x] `BL _ 5 t` / lit erases to List (hole in BoundsAnnTy on erase path)  
- [x] Surface ground Count ops erase into Kernel `Count` (slice 3)  
- [x] Origin-based HasBounds synth in Live (no List-inventing defaults) (slice 4)  
- [x] `BL _ 5` pin-to-synth meets under `--bl` (slice 5)  
- [x] Nil-only match under proved empty upper bound (surface under `--bl`) (slice 6)  
- [x] REPL/CLI HM vs BL: fail-fast vs erase + origin check + BoundCovers (slice 6)  
- [ ] Scheme demos (map/filter/append) under `--bl`  
- [ ] Composite never-stuck under HasBounds + BoundCovers (or documented partial — post-E2E OK)  

---

## 11. One-liner

> **B′ dual-stack:** surface `BL` erases under `--bl`; origins + hole pin; BoundCovers; solid ascriptions win in `bctx`; `{n:Nat}` schemes pack/inst; D24 fresh List λ; **next = slice 8 map/filter/append**.

---

## 12. Next action

1. **Slice 8 — Stdlib demos:** honest `map` / `filter` / `append` under `--bl` with bound schemes.  
2. Then **9** E2E suite.  
3. **Whenever convenient:** §2.3 residuals — hole anns push pinned template; head-binder `(xs : BL …)` fold into demand; fuller Commit `uniqueOnly` (Live uses rank-1 `checkSubInst` today).

Thin erase (`Ann.lean`) stays Z3-free for diagnose/hover; Live `--bl` check path uses Z3 via `FHM.Bounds.Check`.

---

## 13. New-agent checklist

1. Read this memo §§1–2 (esp. D22–D24, **§2.3**), §3 Live today, §6 table + 6.1–6.4.  
2. Build: `lake build FHMBounds blt` (or project’s usual target).  
3. Smoke: `scratch/bl-synth-ok.fhm`, `bl-hole-ok.fhm`, `bl-nil-only.fhm`, `bl-ascribed-list-lam.fhm`, `bl-scheme-id.fhm`, `bl-unascribed-list-lam.fhm` under `--bl`.  
4. Implement **slice 8** — map/filter/append demos; keep pack/inst honest (no List-interval invention).  
5. Key files: `SurfaceLang` / Parse / Pretty / Erase; `Bounds/{Synth,Check,Typing,Ann,Kernel}`; `Live.lean`.  
6. Do not invent List intervals from bare HM `List` (D22). Do not fuse bounds into Core Ty.
