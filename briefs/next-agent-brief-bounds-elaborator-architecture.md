<!-- Written 2026-08-03: handoff from a long diagnostics/LSP + BL authoring session.
   Revised after an independent code/runtime audit.
   Superseded for product direction 2026-08-04. -->

# Next-agent brief: Bounds elaborator architecture (one semantic authority, staged migration)

> **Superseded (product architecture):** 2026-08-04 by
> [`design-memo-bounds-preserving-elaboration.md`](design-memo-bounds-preserving-elaboration.md).
>
> **Keep for history:** failure taxonomy (Class A split authority vs B count
> discharge vs C legitimate rejects vs D diagnostics), concrete Infer Core
> exhibits (`λ` + List-let match encoding), and why one-off patches failed.
>
> **Do not** start the V1/V2 staged migration or further Matches case-patches as
> the main line. New work follows the bounds-preserving double-elaboration plan.
> Coverage still must not be a second environment-rebuilding interpreter — that
> diagnosis stands; the packaging fix is “BL on Core through Infer,” not
> ofLower+record-on-Anns alone.

**Status:** Historical investigation (complete). Product redesign documented elsewhere.  
**Related (current):** `briefs/design-memo-bounds-preserving-elaboration.md`  
**Related (product rules):** `briefs/design-memo-bounds-layer-on-core.md`  
**Related (historical next step that is also superseded):** `briefs/design-memo-bounds-elaborator.md`

**User stance (2026-08-03, context only):**
- Reluctant to divert from **main BL integration** (still incomplete).
- Concerned about **size / blast radius** and **forever-refactor**.
- Wants findings written for **fresh eyes**; interested in principled fix **if** derisked.
- Preference: right architecture over more one-off patches — but **not** at the cost of stalling BL product indefinitely.

**(2026-08-04 update):** Principled packaging agreed; see superseding memo. Implementation starts at Core `Ty.list` + preserve-BL lower, not Matches migration.

---

## 1. Executive verdict

| Question | Answer |
|----------|--------|
| Are awkward per-program errors a sign of wrong architecture? | **Some are.** Repeated λ/list-let/match failures come from two semantic authorities rebuilding bounds environments differently. Other failures are independent HM, Sub, or count-discharge limitations. |
| Is dual-stack BL-on-Core itself wrong? | **No.** Keep erase → HM → bounds sidecar. |
| What is wrong? | `checkProgramAnns` computes authoritative bindings, but `checkProgramMatches` discards them and independently interprets Infer Core using stubs and fallbacks. The system lacks one owner of `(Δ, bctx, demand?, τ, residual)`. |
| Is “one giant elaborator” the answer? | **No.** The target is one **semantic authority**, not necessarily one giant function or one pass. Synthesis may emit coverage obligations that a separate checker discharges, provided that checker never reconstructs bindings. |
| Does this depart from the original memo? | **No locked decision changes.** D1–D2, D18, D22, D24, and R3 remain constraints on the migration. The descriptive two-walk implementation in memo §3 is not itself a locked design. |
| What should happen first? | P0 contract + frozen acceptance matrix, then one λ → Infer list-let → match vertical slice that deletes the stub/fallback path. Do not begin with a file-scale rewrite. |
| How do we derisk? | Preserve old behavior at the public entry point, migrate one Core shape at a time, count deleted semantic fallbacks, and stop if a slice cannot replace code or unlock its named acceptance case. |

---

## 2. What the user hit (exhibits)

These are **symptoms**, not the root design.

### 2.1 Editor diagnostics (mostly fixed)

- HM failures collapsed to `(1,1)` / `"typechecking failed"`.
- Parse soft-fail pointed at `let` / `:` instead of string / `*` / count vars.
- Bounds squiggles one column (wrong extension install once; then name-only spans).

**Shipped (high level):** real parse end spans; commit after `:` / top-level `let`/`type`; expected vs got on ascription HM failure; bounds RHS spans; structured binder tags.

### 2.2 Showcase authoring (architecture)

| Program shape | Failure mode | Real cause |
|---------------|--------------|------------|
| `let x : σ = map` | typechecking failed | Bare `map` is `(a→b)→List→List`, not `List→List` (HM correct) |
| `map id` + product scheme ascription | “argument … function domain …” | Bounds Sub: synth `BL ?n ?m → …` ≰ demand `BL (n*m) (n*m) → …` — **not** DemandOK, **not** HM |
| Unascribed `\xs -> match … \| [] -> []` | `Nil needs an expected List type` | `synthMatch` pure-inferred Nil, ignoring scrutinee `List α` from HM |
| Same after Nil fix | `match not exhaustive for scrutinee type` | Infer emits `λy. let z : List a = y in match z`; Matches walk pushed `?β` stub for bare λ; List-let `checkBounds` returned stub |
| `\| h :: [] -> …` under `BL 0 1` | `Nil-only match but upper bound not proved empty` | Pattern desugars to **nested** Nil-only on **tail**; refine/`pred`/oracle path doesn’t discharge “tail empty” |

**Lesson:** one character of surface difference → different layer (HM / Sub / coverage / nested refine). Some are split-authority bugs; some are local rule or diagnostic gaps. Classify the failing judgment before prescribing the fix.

### 2.3 Current L81-ish exhibit (as of handoff)

```fhm
let firstOrEmpty : BL 0 1 Int -> BL _ _ Int =
  \xs ->
    match xs with
    | [] -> []
    | h :: [] -> [h]
```

Infer Core (approx.):

```text
λy. let z : List Int = y in
  match z with
  | Nil => []
  | Cons u v => match v with | Nil => [u]
```

Outer match: Nil+Cons. Inner: Nil-only on tail after Cons from length≤1. Error talks about Nil-only / empty upper bound — user never wrote an inner match.

**Also try:** `| h :: t -> [h]` under same ascription — often a **different** ascription Sub failure (`BL ?n ?m → BL 0 1` vs pinned domain `BL 0 1`). Same family of fragility.

### 2.4 Root-cause taxonomy (do not make one refactor own all failures)

| Class | Examples | Root action |
|-------|----------|-------------|
| **A. Split semantic authority** | λ `.fvar 0` stub; Infer List-let D24 fallback; Anns green / Matches red; demand lost across elaborated Core | Unify env/type/demand ownership; delete reconstruction |
| **B. Local refinement/discharge gap** | Nested `h :: []`; proving `pred 1 = 0`; Cons-tail empty/nonempty facts | Improve `consRefine` / solid count discharge independently |
| **C. Legitimate typing or meet failure** | Bare `map` has the wrong HM shape; genuinely ambiguous R3 escape; invalid coverage | Preserve rejection; improve structured explanation |
| **D. Diagnostic transport** | `Option` from Infer; `Except String`; string-based span archaeology | Structured errors, independently shippable |

The recurring **Class A** failures justify architectural work. A single semantic authority is necessary to make that class converge. It is **not sufficient** for Classes B–D, and success must not be claimed merely because those concerns have been moved into the same function.

---

## 3. Architecture on the ground

### 3.1 Intended pipeline (sound)

```text
Surface  --erase BL→List-->  Surface'  --lower-->  Core
                                    --InferW-->  eOut + τ
                         --bl: origin synth / ascription meet / BoundCovers
                         --pack / uniqueOnly (R3)
```

Design memo: `briefs/design-memo-bounds-layer-on-core.md`.

### 3.2 Actual executable shape (the root authority bug)

Two **separate** reconstructions of binder environments on the same `eOut`:

| Walk | File | Role |
|------|------|------|
| **Anns / origin** | `FHM/Bounds/Check.lean` `checkProgramAnns` + `Synth.inferBoundsΦ` / `checkBoundsΦ` | Binder ascriptions, pack, R3 |
| **Matches** | `Check.checkProgramMatches` / `checkProgramMatchesGo` | Nested match BoundCovers / exhaustiveness |

They do **not** share one `(Δ, bctx, demand?, τ, residual)` invariant. In particular, the successful `bctx` produced by Anns is used for report enrichment but is not passed to Matches. Matches re-pushes:

- bare `.fvar 0` for unannotated λ (when Infer left `paramAnn = none`)
- List-let β via `checkBounds` of RHS, but **var lookup ignores expected τ** (`checkBoundsΦ` on `.var` returns env β only)

Infer elaborates freely (`let z : List a = y`, unannotated `λ`, let-rec wrappers). Bounds answers with **special cases**. Each new elaboration pattern can therefore require a patch in a pass that should not be an independent semantic authority.

Two traversals are not inherently wrong. The defect is that both traversals decide what a binder means. A future coverage pass may remain separate if it consumes obligations or an authoritative elaboration trace and never recreates `bctx`.

### 3.3 Type information underused

- HM already has `List a`, arrow shapes, match result types.
- Bounds often re-discovers via optional Core anns or pure infer.
- Pure infer of `Nil` hard-fails without expected List type — even when match scrutinee already fixed `α`.

**Partial fix landed:** `synthMatch` checks arms at `listTy α` (not pure-infer Nil). Still not a full type-directed elaborator.

**Important implementation caveat:** “HM knows the type” does not imply that a complete per-node typed derivation is currently retained. P0 must inventory which child `τ`s can be propagated from the program `τ`, Core scheme annotations, constructor signatures, and demands. If a gap remains, prefer a small bounds-side typed trace/replay over changes to InferW. Do not casually assume V3 is only plumbing.

### 3.4 Diagnostics pipeline (improved, still shallow)

| Layer | Error info |
|-------|------------|
| Infer | `Option` — no unify site |
| Bounds | `Except String` — string archaeology (`for name`) |
| Diagnose | Progressive probe + strip-ascription expected/got (HM ascription only) |

Spans/messages got better; **semantic robustness** did not fully follow.

### 3.5 Size of ground zero (approx. LOC)

| File | ~LOC | Role |
|------|------|------|
| `FHM/Bounds/Synth.lean` | 930 | infer/check bounds |
| `FHM/Bounds/Check.lean` | 590 | Anns + Matches walks |
| `FHM/Bounds/Typing.lean` | 1400 | declarative + helpers |
| `FHM/Bounds/Escape.lean` | 370 | R3 pack |
| `FHM/Live.lean` / `EditorSupport.lean` | call sites | |
| `FHM/InferW.lean` | **21k** | **Do not open for this MVP** |

---

## 4. Fair assessment of recent fixes

| Fix | Kind |
|-----|------|
| Parse commit-after-`:`, string/`*` sites, binder tags | Structural for **diag UX** |
| HM ascription expected vs got (strip ann, re-infer) | Smart **diag patch** |
| meetForApp wording (synth vs demand) | Presentation |
| `synthMatch` check Nil at `List α` | Small **structural** local |
| Matches D24 fallback when List-let meets λ-stub | **Classic patch** (papers over dual walk) |
| L81 nested `h :: []` | **Not fixed** — independent nested-refinement/discharge gap exposed by the same authoring session |

**Verdict:** Not pure cargo-cult, but the **volume** of one-offs is a real signal. Further case patches on Matches/Anns without the P0 contract and a V1 authority slice will not converge.

---

## 5. Revised principled target

### 5.1 Preserve these boundaries

- Keep erase → unchanged HM/Infer → optional bounds sidecar (D1–D2).
- Keep nested coverage on lowered Core for this project (D18).
- Keep origin-only intervals: HM `List` gives an element/type shape, never a fabricated interval (D22).
- Keep D24 fresh interval variables only at its sanctioned origin; do not turn “type-directed” into default bounds invention.
- Keep R3 residual collection and `packAtEscape` / `uniqueOnly` policy.
- Keep Bounds optional; no Bounds/Z3 dependency in the default FHM target.
- Avoid InferW proof or elaboration changes unless P0 demonstrates that no bounds-side typed trace can supply a required `τ`.

### 5.2 The target invariant

There must be exactly one semantic authority for each expression/binder transition:

```text
input:   Core expression + HM type information
state:   Δ + bctx + optional bounds demand + residual constraints
output:  synthesized/checked β + residual + coverage obligations
```

This is a **judgmental contract**, not a mandate for one enormous recursive function.

A suitable end state is:

```text
elaborate bounds once
  ├─ decide binder β / scheme / escape exactly once
  ├─ propagate τ and demand through λ / let / app / match
  ├─ synthesize/check result β and residual
  └─ emit coverage obligations carrying authoritative Δ + scrutinee β + branch env

discharge coverage obligations
  └─ may traverse obligation trees, but must not reconstruct binders
```

Inline coverage is also acceptable. What is forbidden is a second pass independently answering “what β is in this slot?”

### 5.3 Concrete goals

1. **Binder transition rulebook** covering surface spine and Infer-introduced λ / let / letRec shapes.
2. **One authoritative environment** shared by synthesis, escape, report enrichment, and coverage.
3. **Type-directed propagation** with no blind `.fvar 0` when `τ` or a sanctioned D24 origin is available.
4. **Coverage obligations or trace** so coverage can stay modular without becoming a second interpreter.
5. **Independent nested-refinement repair** for `pred`/literal and Cons-tail empty/nonempty facts.
6. **Structured `BoundsError`** (site + kind + expected/got where meaningful).

### 5.4 Acceptance matrix (freeze semantics before implementation)

Create small dedicated files; do not use a dirty showcase as the only oracle.

| Case | Expected | Why |
|------|----------|-----|
| Unascribed List λ + Nil/Cons match | **green** | D24 origin; no λ stub |
| `BL 0 1` + `[]` / `h :: t` returning lists | **green** | Demand must reach λ and branches |
| `BL 0 1` + `[]` / `h :: []` returning lists | **green** | Same plus nested tail-empty discharge |
| Cons-only match on `BL 0 1` | **red** | Input may be empty |
| Nil-only match on `BL 1 1` | **red** | Input is nonempty |
| Product-count scheme checked against `map id` | **green**, if HM shape agrees | Scheme instantiation/checking, not arbitrary model choice |
| Bare `map` as `List → List` | **red at HM** | Legitimate arity/type mismatch |
| R3 vacuous/generalised canary | **green** | Preserve packing |
| R3 non-vacuous multi-model escape | **red** | Preserve `uniqueOnly` |
| Bare HM `List` with no BL origin | **no invented concrete interval** | D22 |

P0 must turn each row into exact source plus expected stage/error kind. If product semantics disagree with a row, change the table explicitly **before** code.

### 5.5 Migration phases (revised)

| Phase | Deliverable | Estimate | Required deletion / proof of value |
|-------|-------------|----------|------------------------------------|
| **P0** | Binder/type-flow table; Core-shape inventory; acceptance matrix; D22/D24/R3 invariants | 1–2d | No code |
| **G0** | Freeze existing e2e + dedicated green/red acceptance files | 0.5–1d | Reproducible baseline |
| **V1** | λ → Infer List-let → match vertical slice uses one binder transition; remove λ stub and List-let D24 fallback for that path | 2–4d | Named fallback lines deleted; first acceptance pair green |
| **V2** | Authoritative elaboration result/trace carries nested let/letRec env and coverage obligations; coverage stops rebuilding those slots | 4–7d | Duplicated env reconstruction materially deleted |
| **V3** | Complete τ/demand propagation for Nil/Cons/app/match gaps found by P0 | 2–4d | Type-directed acceptance cases green; no D22 regression |
| **N1** | Nested Cons refine + solid `mustBeEmpty`/`mustBeNonempty` discharge | 2–4d | `h :: []` acceptance green |
| **E1** | `BoundsError` → Live/editor diagnostics | 2–4d | String archaeology reduced; red semantics unchanged |
| **C1** | Delete compatibility path, goldens, update product-fragment memo | 1–2d | No second semantic authority remains |

These are estimates, not commitments. Expected focused calendar remains roughly **2–4 weeks**, but V1 must produce evidence within days. N1 and E1 can be scheduled independently because they do not validate or invalidate the authority migration.

### 5.6 Blast radius and explicit risks

**Ground zero:** `FHM/Bounds/Check.lean`, `FHM/Bounds/Synth.lean`.  
**Likely call sites:** `FHM/Live.lean`, `FHM/EditorSupport.lean`, report enrichment.  
**Independent refinement work:** `Typing.lean` / Kernel/Oracle helpers as demonstrated by P0.  
**Preserve carefully:** `Escape.lean` and the `ResM` → `packAtEscape` path.  
**Avoid by default:** `InferW.lean`.

Highest risks:

1. Accidentally using HM `List` shape as a bounds origin (D22 violation).
2. Losing D24 generalisation by replacing fresh sanctioned bounds with a concrete template.
3. Dropping or splitting R3 residual state across compatibility paths.
4. Breaking letRec/de Bruijn alignment while “sharing” binder logic.
5. Retaining two authorities behind a new abstraction and declaring victory.
6. Assuming per-node HM types exist without proving how each `τ` is obtained.

---

## 6. Recent commits (context for git archaeology)

On `main` (not exhaustive):

- `411382e` — editor diagnostic spans (parse/HM/bounds locations)
- `7c3a173` — list-match Nil at `List α` + Matches List-let D24 fallback + meetForApp wording
- `8ad22d9` — diagnose expected/got + parse reject sites

Local unstaged often includes `scratch/bl-showcase.fhm` experiments — **do not treat as product truth**.

E2E: `./scripts/bl-e2e-smoke.sh` (green + intentional red demos). Use as gate for any bounds change. At revision time, the locally edited `bl-showcase.fhm` can make this 20/21; separate the new acceptance cases from that mutable showcase before freezing G0.

---

## 7. Derisking the refactor (how not to forever-refactor)

User concern is valid. Concrete controls:

### 7.1 Do not start V1 until

1. **P0 contract exists** and records every binder transition V1 will touch.
2. **G0 is frozen** with exact expected stage/outcome for §5.4.
3. The V1 diff has a named deletion target: λ `.fvar 0` and the corresponding Infer List-let fallback, not merely a new abstraction.
4. **Time-box:** V1 gets at most four focused days. If it cannot delete its old semantic path and keep the frozen matrix stable, stop and revise the contract.

### 7.2 Vertical slices, not file or layer rewrites

Each PR must ship **one** of:

- One Core-shape route moved to the authoritative transition **and its old route deleted**; or
- One coverage-obligation route that no longer reconstructs its env; or
- One independent refinement acceptance case, clearly labelled N1 rather than evidence for V1/V2; or
- Structured error transport with no semantic change.

**Stop rule:** reject a PR that only renames/moves code, adds a third env representation, or leaves old and new paths both semantically live without a next-PR deletion already prepared.

### 7.3 Coexistence policy

- **Forbidden:** “Anns old path + Matches new path” as an indefinite architecture.
- **Allowed:** compatibility at the public entry point while one Core shape at a time moves behind it.
- **Required:** old behavior remains callable only long enough to compare a slice; delete that branch in the same PR stack.
- Do not use two full-program runs and compare only final pretty output: that can miss env, residual, and error-stage drift.

### 7.4 Keep product BL work unblocked

| Continue now (main line) | Defer |
|--------------------------|--------|
| G0 / Slice 9 E2E hardening | Any file-scale elaborator rewrite |
| R-series / memo backlog that doesn’t need free authoring | Infer structured errors |
| Display (T6 count pretty), kernel totalization | Surface-aware BoundCovers rewrite |
| Small diag UX if critical | More Matches special cases for showcase |

V1 is now a legitimate scheduled root-fix project once P0/G0 exist; it need not masquerade as incidental diagnostics work. N1 may be pulled forward if `h :: []` blocks authoring, but it must not grow into V2 implicitly.

### 7.5 Metrics of success (so “small portions of one phase” is visible)

After each PR, report:

1. Which component was the semantic authority before and after.
2. Stub/fallback/duplicated env lines deleted.
3. Acceptance rows newly green and intentional reds unchanged.
4. Frozen e2e result, including failure stage/kind where relevant.
5. D22/D24/R3 canary result.
6. Time spent versus slice estimate.

If authority is still split or deletion is flat for two PRs, **stop**. A growing facade around both old walks is a failed migration.

### 7.6 Fresh-agent anti-patterns

- Do **not** open InferW for this.  
- Do **not** equate “one authority” with “one giant function.”  
- Do **not** claim nested `pred` discharge proves the env architecture.  
- Do **not** call `agreesTemplate` on a bare List as an easy type-directed default (D22).  
- Do **not** add another `freshParamBounds` fallback for a new Infer shape without updating the **binder table** in the plan.  
- Do **not** commit without user say-so; no `Co-Authored-By`.

---

## 8. Sequencing recommendation (product vs architecture)

```text
Now:               P0 contract + G0 acceptance/e2e freeze
                   (useful product hardening even if migration stops)

Then, if approved: V1 λ → Infer List-let → match
                   hard stop unless stub/fallback code is deleted

After V1 evidence: V2 authoritative trace/coverage obligations
                   then V3 remaining type flow

Independent lane:  N1 nested count discharge; E1 structured errors

Alongside:          BL product items that do not touch these semantics
```

This intentionally changes the old recommendation to leave P0 parked indefinitely. The recurring patch pattern is now sufficiently evidenced to justify specifying and testing the root boundary. It does **not** justify starting V2 before V1 demonstrates deletion and stable semantics.

---

## 9. Suggested first tasks for a fresh agent

**Read only (half day):**

1. This brief.  
2. `briefs/design-memo-bounds-layer-on-core.md` §§1–2, §5 B/F, backlog table.  
3. `FHM/Bounds/Check.lean`: `checkProgramAnns`, `checkProgramMatchesGo` (λ / letIn / match).  
4. `FHM/Bounds/Synth.lean`: `inferBoundsΦ` Nil, `checkBoundsΦ` var (τ ignored), `synthMatch`, `consBoundEnv`.  
5. Reproduce exhibits:

```bash
./scripts/bl-e2e-smoke.sh
# then minimal files for firstOrEmpty with h :: t vs h :: [] under BL 0 1
```

**Write (if user asks for plan only):**

- Expand P0 into `briefs/design-memo-bounds-elaborator.md`.
- Include the exact binder/type-flow table, authority boundary, Core-shape examples, acceptance files, PR DAG, rollback points, and D22/D24/R3 preservation checks.
- Decide whether coverage obligations or an authoritative trace is the smaller V2 mechanism; do not decide by naming preference.

**Implement (only with explicit go):**

- G0 first.
- V1 only, preferably isolated, with e2e at each semantic deletion.
- Return for review before V2.

---

## 10. Open questions for the user / next agent

1. Confirm §5.4 product semantics, especially that both `h :: t` and `h :: []` under `BL 0 1` are must-green.
2. Choose V2 representation after P0: emitted coverage obligations versus a reusable elaboration trace.
3. Confirm one short compatibility PR stack is acceptable; recommendation: **yes**, with same-stack deletion.
4. Keep structured Infer errors outside this MVP? Recommendation: **yes**.
5. Is executable↔declarative proof correspondence required per slice, or are frozen e2e + existing props acceptable for this MVP? Recommendation: state the gap explicitly and defer a broad proof project.

---

## 11. One-paragraph summary for context packing

The dual-stack BL-on-Core design remains right. The root recurring architecture defect is narrower: Anns computes authoritative bounds bindings, then Matches discards them and independently reconstructs env/type/demand through Infer Core using λ stubs and shape-specific fallbacks. Fix that with one semantic authority over `(Δ, bctx, demand?, τ, residual)`; coverage may remain a separate obligation checker but must not decide binders again. Do not bundle independent nested-count discharge or structured errors into proof that this migration worked. Preserve D18/D22/D24 and R3. Start with P0 + frozen acceptance semantics, then a four-day λ → List-let → match V1 that must delete the old stub/fallback; proceed to an authoritative trace/obligation V2 only if V1 produces stable behavior and real deletion. Expected full effort remains roughly 2–4 weeks, but there is a hard evidence gate after days, not weeks.

---

## 12. File index

| Path | Why |
|------|-----|
| `FHM/Bounds/Check.lean` | Anns + Matches dual walk |
| `FHM/Bounds/Synth.lean` | Origin infer/check, synthMatch, meetForApp |
| `FHM/Bounds/Typing.lean` | `consBoundEnv`, `agreesTemplate`, BoundCovers props |
| `FHM/Bounds/Escape.lean` | R3 packAtEscape |
| `FHM/Live.lean` | `--bl` pipeline |
| `FHM/EditorSupport.lean` | diagnose ≡ Live `--bl` + spans |
| `scripts/bl-e2e-smoke.sh` | Local gate |
| `scratch/bl-*.fhm` | Demos (showcase may be dirty locally) |
