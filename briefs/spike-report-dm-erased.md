# Spike report: A (blind tax), B (pins), C (mining) — results and one design revision

**Status:** spikes complete 2026-09-08; one material design revision (R1) discovered
**Date:** 2026-09-08
**Related:** [`design-memo-dm-erased-shadow.md`](design-memo-dm-erased-shadow.md) (D1–D10)

---

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

- **`Infer : Nat → Ctx → Expr → Nat → Subst → Ty`** — pure inference, **no elaborated output** (confirms the shadow is genuinely new work; also confirms the old `infer : … → Option (Nat × Subst × Ty)`, no eOut).
- **`InferRecGroup : … → List Expr → List Ty → …`** — plain DM: per-member shared monotypes `β`, unify-and-thread; **no `RecSpec`, no anns, no ceiling**. D2's target rule exists in finished form.
- **One `TypeOfHM`** (+ match-branch helper). No `TypeOfElabHM`. No `Expr.erase`. No erase-commutes family.
- Old-era `Step` runs **on the source terms with annotations as inert payload** (rules pattern-match `.lambda ann body` and carry `ann` through untouched).

## R1 — Design revision (strengthens D1/D6): dynamics on source terms; the erase function is deleted entirely

The erasure branch chose to *re-point* the declarative side at erased terms (`TypeOfHM` on `e.erase`) — that choice is what forces `Infer.sound` to be an erase-transport theorem, which is what saturates the spine with `AgreesHM` (Spike A). The old era shows the simpler shape: **`TypeOfHM` on source terms, decoration-blind** (typing never inspects ann payloads *except* at pins), **`Step` on the same source terms** (anns inert), no erase anywhere.

Consequences:
1. `Infer.sound` restates as `Infer … → TypeOfHM …` **directly** — no `eraseBounds` in the statement. The 226+79 blind occurrences should collapse to the pin/unify sites (Spike B's two sites).
2. `Expr.erase`, `eraseBounds`, erase-commutes, residual bridges: **deleted** (they existed to bridge source-typing to erased-typing — a split R1 abolishes).
3. The branch's erased-dynamics **tower** (progress/preservation/safety) was proved for erased terms under erased-typing; under R1 it restates over source-term decoration-blind typing with anns inert. The proofs port in structure, but this is the one place R1 costs real work (subst lemma must handle ann payloads as inert — mechanical, but it's a re-plumb, not a free port). Honest estimate: medium, bounded, and it *replaces* the erase-transport plumbing rather than adding to it.
4. BL annotations ride in the term as inert payload exactly as D5 wants — and now with zero erase machinery to commute them through.

**Net:** R1 *reduces* total machinery below both the current branch and the memo's D6 picture, and is directly inspired by the mined old-era design (D10 paying off immediately).

## Recommended next steps (in order)

1. Cut `dm-erased` from `c64bb14` ("erasure migration complete" — before spine WIP entanglement), per D9.
2. Fix B3 (`Bounds.Typing`'s four `Ty.bl` cases) — CLI sanity tooling first.
3. D2 deletion: replace fused `InferRecGroup`/`RecSpec`/ceiling with the old-era DM rule (Spike C shows the target shape); delete `PolyTyped`, `RecSpec.poly`, ceiling, `letRecElabNest`, promotion leftovers. Net-negative LOC, suite re-run (4 tests flip to must-fail by design).
4. R1 re-pointing: `TypeOfHM` to source terms (decoration-blind), `Step` to source terms (anns inert), delete erase machinery, restate the dynamics tower.
5. Shadow elaboration (`ElabExpr` + `elaborate`, Infer builds it), coherence theorem, LSP walk; delete `zipBindingTypes`/`collectTopSchemes`.
6. BL pass per D8; delete Path R residue.
7. Port the completeness spine tiers onto the settled shape (last, per D9).
