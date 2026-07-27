# Next-agent brief: remove uniqueness from declarative `TypeOf` / `Check`

**Status:** done (PR1 `2426eb1`; PR2 docs in follow-up)  
**Date:** 2026-07-27  
**Spine:** `FHM/BLSketch.lean`  
**Related:** [`design-memo-collapse-bl-axioms-to-z3.md`](design-memo-collapse-bl-axioms-to-z3.md) (unique is not a free Z3 corollary; axiom kept for algo policy)

---

## Goal (achieved)

Uniqueness of solutions for escaping bounds is **not** a premise of well-typedness.

- **Declarative** `TypeOf` / `Check`: dropped every `unique ψ outs = .unique` premise.
- Kept **existence** of a solve witness (`solve ψ = .witness σ`) on the `*Infer` rules.
- Did **not** merge `*Infer` into plain `Sub` (`Sub` is ∀ via `checkValid`; Infer is ∃ via `solve`).
- Algorithmic `forceSubtype` **keeps** the uniqueness gate (elaborator policy).
- **`unique_sound` kept** (not deleted) — reserved for algorithmic uniqueness policy / future proofs.

Non-goals (still open): axiom collapse, Core/InferW wiring, semantic `ψ.Sat`, chooser / commit-a-model (PR3-shaped).

---

## Why

A non-unique model is not “ill-typed.” It means “several assignments work; which bounds we *commit* is ambiguous.” That is elaborator / UX policy, not declarative soundness.

| Algo filter | Effect |
|-------------|--------|
| Soundness (algo ⇒ TypeOf) | **Preserved** if algo is stricter (unique required) |
| Completeness (TypeOf ⇒ algo) | **Already not claimed** for bounds; unique only widens the gap |

---

## What landed (PR1)

| Item | Result |
|------|--------|
| 6 TypeOf `*Infer` + 2 Check (`ofInfer`, `nilInfer`) | unique premise removed |
| `TypeOf.weakenCtx` / `synth_sound` / `check_sound` | arity fixed; ignore unique from `forceSubtype_sub` |
| `forceSubtype` unique gate | **unchanged** |
| `opaque unique` + `unique_sound` | **kept** |
| `UniqueOutputs` / `sameOutputs` | kept (used by axiom) |
| Module contract + Examples ambiguity prose | unique = elaborator policy |
| `lake build FHM.BLSketch` | green |

---

## Remaining (optional)

### PR3 — Algo alignment (product decision; not started)

- Drop unique gate, or accept any witness, or `List Solution → Option Solution` chooser.
- Retune demos that expected “ambiguous ⇒ fail.”
- Only then consider deleting `opaque unique` / `unique_sound`.

### PR4 — Out of scope here

- Axiom collapse to Z3-only (`design-memo-collapse-bl-axioms-to-z3.md`)
- Semantic `∃ σ, ψ.SolvedBy σ` instead of `solve = .witness`

---

## Success criteria (PR1)

- [x] No `unique … = .unique` in TypeOf or Check constructors
- [x] `synth_sound` / `check_sound` still prove
- [x] `unique_sound` retained for algo policy (amended from original brief)
- [x] Module contract documents: unique is elaborator policy, not well-typedness
- [x] `forceSubtype` policy left as-is
