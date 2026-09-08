# Next-agent brief: land the declared-mono opening for annotated letRec members (D2 completion / B6 fix)

**Status:** spec complete, implementation NOT started
**Date:** 2026-09-08
**Branch:** `dm-erased` (green at `c5fad74`; CLI builds; 9 sorries, all in `FHM/Bounds/*`; do not touch `Bounds/`)
**Read first:** [`spike-report-dm-erased.md`](spike-report-dm-erased.md) (root cause + full fix spec + probe evidence), [`design-memo-dm-erased-shadow.md`](design-memo-dm-erased-shadow.md) (D1–D10 context)

---

## One-liner

> Annotated `letRec` members currently fail to typecheck because the DM cut checks their RHS at a bare fresh monotype without opening their scheme; fix = **declared-mono opening** (open σ once at rigid skolems, RHS checked against it, siblings see one fixed instantiation, body sees σ), applied to the relation, executable, declarative mirror, and the four affected proof families — one coherent green-at-the-end editing session.

## The spec (from spike report §Fix spec — authoritative)

1. **`RecSpec.init`** (`FHM/InferW.lean:1356`): for `some σ` at frontier Φ emit `.mono (σ.openVars (freshVars Φ σ.paramCount))` — NOT a bare `.mono (.fvar Φ)`. Every member still presents a monotype to siblings (DM-pure), but the annotated member's monotype is its declared instance. NOTE: `init` currently ignores the ann entirely (see `RecSpec.map_ann_init`); you will need to thread the ann, and decide how `freshVars` interact with the frontier (`Φ` consumption as in `consPoly`: the init for an annotated member should consume `σ.paramCount` fresh names — make `init` take/return the advanced frontier consistently, mirroring `letRec`'s `Φ + bindings.length` premise which may need to become a summed frontier).
2. **`InferRecGroup.consMono`** (`FHM/InferW.lean:1886`): branch on the member's ann:
   - `none`: unchanged.
   - `some σ`: Ys are exactly the freshVars already baked into the spec monotype (deterministic, no extra choice); infer `e.openTyVars Ys`; the rigid set K gains Ys (use `unifyCoreK` discipline so Ys stay unbound — mirror old `consPoly`'s escape premises: Ys not bound by S₁, not leaking into the threaded ctx).
3. **Executable `inferRecGroupCore`** (`FHM/InferW.lean:13183`): mirror the same two branches; keep the K-avoidance witnesses.
4. **`Infer.letRec` rule** (`FHM/InferW.lean:1812`): the premise frontier `Φ + bindings.length` becomes `Φ + Σ paramCounts of annotated members` (consistent with init); ceiling machinery (`RecSpecs.ceilingOK` / `RecSpecs.ceilingSchemes`, `FHM/InferW.lean:1710–1725`) stays initially (body side already exposes σ) and can be simplified afterward — `ceilingOK` should become near-trivial for annotated members.
5. **Declarative mirror** (`FHM/Core.lean`, `RecSpecs` ~2900–3120): `MonoTyped` restated so annotated members are typed at their *opened* scheme's monotype (Ys nested inside the pool opening, excluding it); **`PolyTyped` deleted**; `WF`'s `poly_wf` adjusts. The mirror must match the algorithmic rule shape-for-shape.
6. **Proof families to update together** (all in `FHM/InferW.lean`): `Infer.sound`'s letRec case (~L4547 area), `Infer.eOut_avoid`, `Infer.eliminates`, `Infer.frontier_le` — the letRec cases adjust to the opening (bounded, mechanical-ish; the opening mirrors what `consPoly` already did on main, and `git show 62b20aa:FHM/InferW.lean` has the fused rule's opening idioms to crib from). `RecSpec.map_ann_init` and friends get restated.

## Workflow invariants (D9)

- Branch stays green: `lake build` (default FHM target) must pass at every commit; run `lake env lean scratch/B6Probe.lean`-style checks and the `.fhm` suite via the CLI (`lake build fhm` then `.lake/build/bin/fhm run --json scratch/polyrec-*.fhm`).
- Suite expectations after the fix: `polyrec-nested`, `polyrec-groups-nested`, `polyrec-inner-poly-calls`, `polyrec-mixed-group` **flip to passing** (head-binder shape works again); `polyrec-skolem-leak-must-fail` **stays passing-positive** (it is now legal DM: rename file/expectations in `scratch/PolyRecTest.lean` accordingly — it should TYPECHECK and eval `[5,5,5]`); `polyrec-unannotated-must-fail`, `polyrec-inner-poly-unannotated-must-fail`, `polyrec-mixed-conflict-must-fail` **must stay rejected**.
- `update Fixture`/`#guard`s referencing `RecSpec.init` shapes get updated alongside.
- Use lean-lsp MCP tools (`lean_diagnostic_messages`, `lean_goal`, `lean_multi_attempt`) during editing; avoid full `lake build` loops where file-level diagnostics suffice.
- Small commits per component (init+rule / executable / declarative / proofs), each green or explicitly noted.

## Out of scope (do NOT start)

Ceiling deletion, `Expr.erase` removal (R1 re-pointing), shadow tree, BL pass, spine port. Those are the NEXT briefs in sequence (design memo §2).

## Report format

Per commit: what changed, `lake build` status, sorry count, suite line. Final: overall diffstat, remaining risks, and whether `Infer.sound`'s letRec case stayed axiom-clean (`lean_verify` on it if feasible).
