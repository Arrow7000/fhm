# Findings: poly-rec stress suite + suspect-feature survey (recruiter snapshot & branch work)

**Status:** tests landed on `main` (8/8 green); 2 confirmed bugs + several smaller findings open
**Date:** 2026-09-03 (revised 2026-09-07: findings consolidated; shortlist moved to `briefs/`)
**Motivation:** assess pushed `main` for sharing with recruiters; demote 84 WIP commits to a named branch; smoke-test annotated polymorphic recursion end-to-end; survey remaining suspect features
**Related:** [`stress-test-shortlist.md`](stress-test-shortlist.md) (ranked survey, both bugs in detail); `scratch/POLYREC-README.md` (suite docs); `scratch/PolyRecTest.lean` (driver)

---

## One-liner

> Pushed `main` (`62b20aa`) was a clean milestone worth sharing (sorry-free default build, green CI, Path R + poly-rec complete); the 84-commit CEK/erasure/completeness WIP now lives on `erasure-migration`. The new poly-rec `.fhm` suite is 8/8 green including the hard inner-polymorphic case, and the survey confirmed two real bugs: **`checkExhaustive` false-negatives on nested ADTs** and a **data-decl parser bug that silently swallows a bare body as a phantom ctor field** — plus the `Bounds.Typing` build break that hides the CLI from CI.

---

## 1. Repo-state verdict (why the branch surgery was done)

- **Pushed commit `62b20aa`** (Aug 16, "Prove the SurfaceBridge headline…") closed the last sorries in the verified stack. It sits **after** Path R completion (`b36ca3d`, Aug 14) and **after** the poly-rec tiers (`InferRecGroup.complete` etc.). README's claims (incl. fully polymorphic recursion, mixed groups) are true *at that commit*. CI green on exactly that commit. Verdict: safe to share.
- **Local `main` was 84 commits ahead** (Aug 18–27), all WIP-era. Campaign map:
  1. **CEK machine Stage 1** (Aug 18–19, ~20 commits) — type-erasing CEK, full preservation/progress/determinism… then abandoned (`03c6531` "drop CEK; keep substitution semantics").
  2. **Erasure migration Steps 1–6** (Aug 19–24, ~50 commits) — `Expr.erase`, `Infer.sound` coherence, type-safety tower on erased terms, deleted `TypeOfElabHM`/`var.tyArgs`/`eOut`. Dominant campaign → **branch name `erasure-migration`**.
  3. **Completeness + principality restoration** (Aug 25–27, ~12 commits) — spine pivot, 8/12 tiers closed; branch HEAD mid-campaign ("5 polish errors left").
- **Git state:** `main` = `origin/main`; all WIP + uncommitted `Completeness.lean` polish committed on `erasure-migration`; both pushed. (Note: branch CI fails — expected, WIP sorries.)

## 2. What landed on `main` (purely additive)

- `4dd9064` — poly-rec stress suite: 8 `.fhm` files + `scratch/PolyRecTest.lean` (runs parse → erase → lower → infer → report → exhaustiveness → elaborate → **evaluate**, dumping per-binder inferred/ascribed schemes and group-internal anns) + `scratch/POLYREC-README.md`. **8/8 behaved as designed.**
- `aaed47f` — survey report, now at [`stress-test-shortlist.md`](stress-test-shortlist.md).

### The poly-rec suite in one table

| file | pins down | status |
|---|---|---|
| `polyrec-nested.fhm` | Mycroft's `Nested` (recursion at `Nested (List a)`), 3 outer instantiations | ✓ evals 7 |
| `polyrec-inner-poly-calls.fhm` | **Hard case**: two inner call sites of annotated `f` at `Int` and `List Int`, mutual w/ unannotated `g` | ✓ evals (4,4) |
| `polyrec-mixed-group.fhm` | mono member keeps free pool var; generalises `∀ b. Int → b → Int` at exit | ✓ evals (1,2) |
| `polyrec-groups-nested.fhm` | 3 top-level groups, cross-group calls | ✓ evals 7 |
| `polyrec-skolem-leak-must-fail.fhm` | rigid-var pass to mono sibling — untypeable **by design** | ✓ rejected |
| `polyrec-unannotated-must-fail.fhm` | unannotated polyrec → infinite type | ✓ rejected |
| `polyrec-inner-poly-unannotated-must-fail.fhm` | inner 2-site case w/o annotation → occurs-check | ✓ rejected |
| `polyrec-mixed-conflict-must-fail.fhm` | mono member's own recursion conflicts with pin | ✓ rejected |

### Semantics discoveries (documented in `scratch/POLYREC-README.md`)

1. **Skolem-leak boundary is real and intentional**: `RecSpecs.PolyTyped` nests poly skolems `Ys` *inside* the pool opening `Xs`, excluding each other — so an unannotated member's shared monotype can never mention an annotated sibling's skolem (machine-checked: `SpikeLetRecMixed.skolemLeak_untypeable`). Workaround: annotate the sibling, or pass only skolem-free values.
2. A mono member that keeps free pool vars generalises over **its own** leftovers at exit (DM cut), never over a sibling's skolems.
3. Surface-syntax quirks: sibling-continuation groups are `let…in`-only (top level → SCC via `Program.ofFlat`); **one infix operator per expression** (`a + (b + c)`).
4. `BL 0 0 a` display for plain `List a` params in HM-mode reports — the erase package's default List bounds leaking into display (see survey item 3); `inferred:` line is the HM truth.

## 3. Bug log (consolidated; full evidence in the survey)

| # | Bug / issue | Where | Severity | Evidence |
|---|---|---|---|---|
| B1 | `checkExhaustive` false negatives on fully-covered **nested ADT** matches (`Just (Just x)`, nested `List`) — sound but not complete; `tyArgsGuess` `.unit` placeholders fail closed | `SurfaceBridge.lean` `checkExhaustive`/`matchExhaustiveB`/`tyArgsGuess` | high (correct programs unrunnable) | subagent probes on fresh `main` build (throwaway clone) |
| B2 | **Data-decl parser greediness**: after a `type` decl, a body starting with an identifier is absorbed as a phantom ctor field (`type Color = Red | Green | Blue` + body `Red` → field counts `[0,0,1]`, body silently `()` → misleading `[lower]` error); any leading `let` masks it | `Surface/Parse.lean` `dataCtor`/`ctorField`/`tyAtom` | high (silent wrong-program acceptance, zero theorem coverage on this layer) | `#eval` probe: field counts `[0,0,1]`, body `primLit unit` |
| B3 | `lake build fhm` fails on `main`: `FHM/Bounds/Typing.lean` non-exhaustive `Ty.bl` matches ("prove after shape" debt) — invisible to CI (default target excludes CLI) | `Bounds/Typing.lean` | medium (tooling blind spot) | local build log |
| B4 | HM-mode display shows `BL 0 0` for bare `List` + tyvar misalignment in `erasePolyTy` (`filter` displays `∀ b. (b → Bool) → BL 0 0 b → BL 0 0 b`) | `Bounds/Erase.lean` + `Bounds/Report.lean` pretty | medium (user-facing misdisplay) | visible on existing `scratch/live.fhm` |
| B5 | Scoped-tyvar asymmetry vs README claim: λ-param anns see outer schemes; **let-RHS anns don't** (README overclaims); inner `{a}` rebind silently fresh | `SurfaceBridge.lean` `finalizeAnn`/`letAnnTyPrefix`/`lowerPolyAnn` | medium (doc drift) | probes; survey item 4 |
| B6 | Head-binder packing fallback broken: `let f (x : Int) y : Int = …` fails at typecheck (type-holes brief PR1 predicted it) | `SurfaceBridge.lean` `finalizeAnn` fallback | medium | probes; survey item 5 |
| B7 | Every top-level binding desugars to `letRec` — surface `letIn` unreachable; report order reversed per group (`zipBindingTypes`) | `SurfaceLang.lean` `desugarGroups` | low (design choice, but pins generalisation timing) | probes; survey item 7 |
| B8 | `Nat` apparently unnameable in `.fhm` source (Core has primitive `Nat`; surface `KindEnv` never declares it) | `SurfaceBridge.lean` lower/KindEnv | low, **unverified** | subagent probe only — re-check before acting |

## 4. Open questions / next steps

- Fix B3 (one `match` completion, 4 cases) to unbreak the CLI; CI can then cover it.
- Work the survey top-down: B1 and B2 are genuine bug territory; B4/B5/B6 are user-visible papercuts; B7/B8 document or decide.
- The n² letRec elaboratum question (survey item 7) is **not settled** — needs a scale probe with timing before/after any promotion refactor.
- Double-check the survey's claim that `agreesTemplate`'s `Ty.bl` case is "fixed on `erasure-migration`" before relying on it.

## 5. Artifact map

| artifact | location |
|---|---|
| poly-rec suite (8 `.fhm`) + driver + docs | `scratch/polyrec-*.fhm`, `scratch/PolyRecTest.lean`, `scratch/POLYREC-README.md` |
| ranked suspect-feature survey | [`stress-test-shortlist.md`](stress-test-shortlist.md) |
| this consolidated findings brief | `briefs/findings-polyrec-stress-and-survey.md` |
| WIP workstream (85 commits) | branch `erasure-migration` (pushed) |
