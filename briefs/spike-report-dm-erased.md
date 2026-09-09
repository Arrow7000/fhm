# Spike report: A (blind tax), B (pins), C (mining) — results and superseded follow-ups

**Status:** A–C complete 2026-09-08; R1 and the B6 implementation recommendation superseded/deferred after later experiments and decision review
**Date:** 2026-09-08; corrected 2026-09-09
**Related:** [`design-memo-dm-erased-shadow.md`](design-memo-dm-erased-shadow.md) (D1–D10)

---

## 2026-09-09 decision-review correction (current authority)

The measurements and historical observations in Spikes A–C remain useful. Two recommendations drawn from them do not:

- **R1 is deferred and off the critical path.** A later implementation experiment found that the required `substN`/`openTyVars` commutation is false without extra freshness hypotheses. The branch's existing erased safety tower remains the proved boundary; `.found`, LSP, and BL do not depend on deleting it.
- **The B6 declared-mono implementation is parked.** Opening a declared scheme once can support scoped type variables in an annotated RHS, but it cannot make genuine in-SCC multi-instantiation legal under D2. In particular, `polyrec-nested`, `polyrec-groups-nested`, `polyrec-inner-poly-calls`, and `polyrec-mixed-group` remain expected rejections. The later claim that those four should flip to passing was a semantic error, not the DM target. The former `polyrec-skolem-leak-must-fail` is the converse: it uses one fixed recursive instantiation, is valid DM, and is now the passing `polyrec-mixed-fixed-instantiation` fixture.

The current implementation sequence is therefore: repair the decision/executable-spec record; specify `.found` including final substitutions, binder schemes, and source provenance; land a thin `.found` → internal hover → BL vertical slice; revisit matches/recursive groups afterward. R1 and surface head-binder support require separate bounded spikes if they return to scope.

## Spike A — where the blind tax actually lives (measured on `erasure-migration` tip)

| file | lines | `AgreesHM` occurrences |
|---|---|---|
| `FHM/Completeness.lean` | 6,668 | **226** |
| `FHM/InferW.lean` | 13,963 | **79** |
| `FHM/Core.lean` | — | 1 (the definition) |

The blind economy is concentrated in **the completeness spine and the Infer-side transport**, not the dynamics. `Infer.sound` on the branch (InferW:9964) is stated at the erase level (`TypeOfHM (S.onCtx ctx).eraseBounds e.erase …`) — i.e. blindness is baked into the *statement*, which is why it saturates everything downstream of it. **Verdict:** D5's "smaller surface" claim is confirmed *conditionally* — the tax is a consequence of stating soundness at the erase level, not of `.bl` itself. Which motivates R1 below.

## Spike B — pin sites

`Option.Pins` is **structural equality** (Core:3280), used at lambda (3457) and letIn (3471) pins. The branch's blind equality lives in `AgreesHM` / `Ty.eraseBounds` (Core:94, 4889) and is applied in the *transport* layer, not the declarative rules. Under one-pipeline BL, the minimal change is exactly what the memo predicted: pins become blind (`Ty.eraseBounds ann = Ty.eraseBounds inferred`, the existing `AgreesHM` notion) at the two pin sites, and unify gains the same tolerance when a user ascription meets list sugar. One notion, two application sites. The cofinite machinery is untouched (it quantifies over fresh *names*, not type equality).

## Spike C — mining inventory at `be9cc14f` (the old type-erased era)

- **`Infer : Nat → Ctx → Expr → Nat → Subst → Ty`** — pure inference, **no elaborated output** (confirms typed `.found` output is genuinely new work; also confirms the old `infer : … → Option (Nat × Subst × Ty)`, no eOut).
- **`InferRecGroup : … → List Expr → List Ty → …`** — plain DM: per-member shared monotypes `β`, unify-and-thread; **no `RecSpec`, no anns, no ceiling**. D2's target rule exists in finished form.
- **One `TypeOfHM`** (+ match-branch helper). No `TypeOfElabHM`. No `Expr.erase`. No erase-commutes family.
- Old-era `Step` runs **on the source terms with annotations as inert payload** (rules pattern-match `.lambda ann body` and carry `ann` through untouched).

## R1 — Historical proposal: dynamics on source terms; delete the erase function

> **SUPERSEDED 2026-09-09:** this was a recommendation from Spikes A–C, not a completed or ratified deletion. The subsequent failed commutation spike exposed missing freshness conditions. R1 is now deferred/off-path; see the correction above and D6 in the design memo.

The erasure branch chose to *re-point* the declarative side at erased terms (`TypeOfHM` on `e.erase`) — that choice is what forces `Infer.sound` to be an erase-transport theorem, which is what saturates the spine with `AgreesHM` (Spike A). The old era shows the simpler shape: **`TypeOfHM` on source terms, decoration-blind** (typing never inspects ann payloads *except* at pins), **`Step` on the same source terms** (anns inert), no erase anywhere.

Consequences:
1. `Infer.sound` restates as `Infer … → TypeOfHM …` **directly** — no `eraseBounds` in the statement. The 226+79 blind occurrences should collapse to the pin/unify sites (Spike B's two sites).
2. `Expr.erase`, `eraseBounds`, erase-commutes, residual bridges: **deleted** (they existed to bridge source-typing to erased-typing — a split R1 abolishes).
3. The branch's erased-dynamics **tower** (progress/preservation/safety) was proved for erased terms under erased-typing; under R1 it restates over source-term decoration-blind typing with anns inert. The proofs port in structure, but this is the one place R1 costs real work (subst lemma must handle ann payloads as inert — mechanical, but it's a re-plumb, not a free port). Honest estimate: medium, bounded, and it *replaces* the erase-transport plumbing rather than adding to it.
4. BL annotations ride in the term as inert payload exactly as D5 wants — and now with zero erase machinery to commute them through.

**Net:** R1 *reduces* total machinery below both the current branch and the memo's D6 picture, and is directly inspired by the mined old-era design (D10 paying off immediately).

## Historical recommended next steps (superseded where marked)

1. Cut `dm-erased` from `c64bb14` ("erasure migration complete" — before spine WIP entanglement), per D9.
2. Fix B3 (`Bounds.Typing`'s four `Ty.bl` cases) — CLI sanity tooling first.
3. D2 deletion: replace fused `InferRecGroup`/`RecSpec`/ceiling with the old-era DM rule (Spike C shows the target shape); delete `PolyTyped`, `RecSpec.poly`, ceiling, `letRecElabNest`, promotion leftovers. Net-negative LOC, suite re-run (4 tests flip to must-fail by design). **This semantic boundary remains current.**
4. ~~R1 re-pointing: `TypeOfHM` to source terms (decoration-blind), `Step` to source terms (anns inert), delete erase machinery, restate the dynamics tower.~~ **Deferred after the failed freshness/commutation spike.**
5. ~~Shadow elaboration (`ElabExpr` + `elaborate`, Infer builds it)~~ `.found : Ty → Expr → Expr` in the existing `Expr`, with coherence, final-substitution, binder-scheme, and provenance contracts; then LSP walk and deletion of `zipBindingTypes`/`collectTopSchemes`. `ElabExpr` was the agent's unratified alternative.
6. BL pass per D8; delete Path R residue.
7. Port the completeness spine tiers onto the settled shape (last, per D9).

---

## Addendum (2026-09-08, implementation start): B6 root cause + historical scope proposal

> **STATUS CORRECTION 2026-09-09:** the root-cause evidence below remains valid: annotated head-binder syntax can leave RHS-bound type variables unopened. The proposed repair is **not** the next implementation task and is parked. More importantly, its original test expectations confused "open one declared monotype so the RHS can refer to its scoped variables" with "instantiate a recursive scheme at multiple types inside its SCC." Only the first is compatible with D2.

**Correction to "small fix" assessment.** The head-binder failures are *introduced by this branch's DM cut*, not pre-existing: `RecSpec.init` emits all-mono specs and the executable dropped the scheme-opening path (annotated spec ⇒ `none`), so tyvar annotations inside annotated members' RHSs (generated by head-binder sugar, e.g. `λy : a. y`'s `: a` = the scheme's own bvar 0) dangle untypeable. Main's fused rule opened schemes (`consPoly`) and worked.

**Scope correction:** the fix is the D2 deletion pass proper, not a patch — `InferRecGroup`/`consPoly`/`RecSpec` machinery, the `letRec` rule, the declarative `RecSpecs.*` mirror, and the spine's letRec tiers all rest on the fused design.

**Historical target sketch (D2-consistent only if it enforces one fixed SCC instantiation):**
- Unannotated member: fresh β, unify, generalise at exit (branch already does this).
- Annotated member: scheme σ opened ONCE at rigid skolems Ys ⇒ declared monotype `σ.openVars Ys`; RHS checked against it (opened at the same Ys, escape-premises as in old `consPoly`); siblings see that monotype only (ONE fixed instantiation — in-block polymorphism stays dead); body sees σ (body-side polymorphism intact).
- Ceiling machinery (`ceilingOK`/`ceilingSchemes`) becomes unnecessary: deletable.

**Probe evidence chain (scratch/B6Probe.lean):** parse ✓ / finalizeAnn ✓ / lowerPoly ✓ / eraseProgram ✓ / lowerProgram ✓ → lowered term is *correct* (`let rec (x : ∀ a. a → a) = λy : a. y in x 5`) → **Infer fails**. At the time, the four annotated-polyrec fixtures also reached this earlier head-binder failure; that observation did **not** establish that they should pass after the syntax issue was removed. Full-scheme-ascribed programs passed. The old skolem-leak fixture's positive result was semantically correct for D2 because all recursive uses share one fixed instantiation; the repaired executable spec renames it `polyrec-mixed-fixed-instantiation`.

## Historical fix sketch (parked; requires a fresh spec/review before implementation)

**Insight:** the all-mono init is *almost* right — the only missing piece is that annotated members' RHSs must be **opened at their scheme's binders** (that's what makes internal tyvar anns like `λy : a. y`'s `: a` resolve) while staying **monomorphic for siblings**.

1. `RecSpec.init`: for `some σ` at frontier Φ emit `.mono (σ.openVars (freshVars Φ σ.paramCount))` instead of a bare `.mono (fvar Φ)` — every member still presents a MONOTYPE to siblings (DM-pure, no re-instantiation), but the annotated member's monotype is its *declared instance*.
2. `InferRecGroup.consMono` branches on the member's ann (positional, available in the rule):
   - `none`: unchanged (infer bare, unify vs spec mono).
   - `some σ`: Ys = the same `freshVars` init used (deterministic); infer `e.openTyVars Ys` with rigid set K ∪ Ys (unifyCoreK keeps Ys unbound — declared-type rigidity, cf. old consPoly's escape premises); unify vs spec mono unchanged.
3. Executable `inferRecGroupCore`: mirror the same two branches.
4. Ceiling machinery **unchanged** (ceilingSchemes already exposes σ to the body; ceilingOK becomes near-trivial for annotated members — simplify later).
5. Declarative side (`Core.RecSpecs`): `MonoTyped` restated to "every member types at its spec monotype, annotated members opened at their Ys"; `PolyTyped` **deleted**; `WF` drops `poly_wf`-specific bits.
6. Proof updates: `Infer.sound` letRec case + `eOut_avoid`/`eliminates`/`frontier_le` letRec cases adjust to the opening (bounded); spine letRec tiers re-farm later per D9 (spine stays on `erasure-migration`).

**Superseded sequencing note:** rule + executable + declarative mirror + proof families would still need to move as one coherent checkpoint if this work is resumed. It is no longer the next session's task. Before implementation, replace the stale polyrec driver with a matrix separating (a) scoped head-binder syntax at one fixed recursive monotype, (b) post-group polymorphic use, and (c) genuine in-SCC multi-instantiation, which must remain rejected. The historical analytic work above was committed at `4f683b1`.
