# Archived next-agent brief: declared-mono opening for annotated letRec members (B6)

**Status:** **SUPERSEDED / PARKED 2026-09-09** — retain as B6 analysis, do not execute as the next task
**Date:** 2026-09-08; corrected 2026-09-09
**Branch:** `dm-erased` (green at `c5fad74`; CLI builds; 9 sorries, all in `FHM/Bounds/*`; do not touch `Bounds/`)
**Read first:** [`spike-report-dm-erased.md`](spike-report-dm-erased.md) (root cause, historical fix sketch, and correction), [`design-memo-dm-erased-shadow.md`](design-memo-dm-erased-shadow.md) (current D1–D10 decisions)

---

## Current disposition

Do **not** start this implementation from this brief. Head-binder support is parked while the `.found`/LSP/BL vertical slice is specified and built. If B6 returns to scope, write a fresh brief after rechecking the current rule and executable.

The useful distinction this brief originally missed is:

| case | D2 expectation |
|---|---|
| Complete surface head-binder/scoped-type-variable syntax in an annotated RHS | Desirable surface support; compatible with DM in principle; currently parked |
| A recursive member is used at multiple instantiations, or recursively at a type different from its one SCC monotype | Reject; genuine polymorphic recursion |
| Mutually recursive members use one fixed in-SCC instantiation, even when it contains a rigid variable introduced by an annotation | Accept, provided that variable does not escape its scope |
| The member's scheme is instantiated after the SCC exits | Accept; ordinary post-generalisation polymorphism |

Accordingly, `polyrec-nested`, `polyrec-groups-nested`, `polyrec-inner-poly-calls`, and `polyrec-mixed-group` must **not** flip to passing under a D2/head-binder repair. They exercise genuine in-SCC polymorphic recursion. The old expectation below was erroneous.

## One-liner

> **Historical proposal:** annotated `letRec` members currently fail to typecheck because the DM cut checks their RHS at a bare fresh monotype without opening their scheme; a possible fix is **declared-mono opening** (open σ once at rigid skolems, RHS checked against it, siblings see one fixed instantiation, body sees σ). This remains a design sketch, not an authorized implementation task.

## Historical implementation sketch (not authoritative)

1. **`RecSpec.init`** (`FHM/InferW.lean:1356`): for `some σ` at frontier Φ emit `.mono (σ.openVars (freshVars Φ σ.paramCount))` — NOT a bare `.mono (.fvar Φ)`. Every member still presents a monotype to siblings (DM-pure), but the annotated member's monotype is its declared instance. NOTE: `init` currently ignores the ann entirely (see `RecSpec.map_ann_init`); you will need to thread the ann, and decide how `freshVars` interact with the frontier (`Φ` consumption as in `consPoly`: the init for an annotated member should consume `σ.paramCount` fresh names — make `init` take/return the advanced frontier consistently, mirroring `letRec`'s `Φ + bindings.length` premise which may need to become a summed frontier).
2. **`InferRecGroup.consMono`** (`FHM/InferW.lean:1886`): branch on the member's ann:
   - `none`: unchanged.
   - `some σ`: Ys are exactly the freshVars already baked into the spec monotype (deterministic, no extra choice); infer `e.openTyVars Ys`; the rigid set K gains Ys (use `unifyCoreK` discipline so Ys stay unbound — mirror old `consPoly`'s escape premises: Ys not bound by S₁, not leaking into the threaded ctx).
3. **Executable `inferRecGroupCore`** (`FHM/InferW.lean:13183`): mirror the same two branches; keep the K-avoidance witnesses.
4. **`Infer.letRec` rule** (`FHM/InferW.lean:1812`): the premise frontier `Φ + bindings.length` becomes `Φ + Σ paramCounts of annotated members` (consistent with init); ceiling machinery (`RecSpecs.ceilingOK` / `RecSpecs.ceilingSchemes`, `FHM/InferW.lean:1710–1725`) stays initially (body side already exposes σ) and can be simplified afterward — `ceilingOK` should become near-trivial for annotated members.
5. **Declarative mirror** (`FHM/Core.lean`, `RecSpecs` around lines 3329–3365 at archival time): `MonoTyped` restated so annotated members are typed at their *opened* scheme's monotype (Ys nested inside the pool opening, excluding it); **`PolyTyped` deleted**; `WF`'s `poly_wf` adjusts. The mirror must match the algorithmic rule shape-for-shape.
6. **Proof families to update together** (all in `FHM/InferW.lean`): `Infer.sound`'s letRec case (around line 10685 at archival time), `Infer.eOut_avoid`, `Infer.eliminates`, `Infer.frontier_le` — the letRec cases adjust to the opening (bounded, mechanical-ish; the opening mirrors what `consPoly` already did on main, and `git show 62b20aa:FHM/InferW.lean` has the fused rule's opening idioms to crib from). `RecSpec.map_ann_init` and friends get restated.

## Historical workflow notes (D9 policy corrected)

- Work as one coherent checkpoint: intermediate commits may be temporarily red when the rule, executable, declarative mirror, and proofs must move together; the checkpoint must end green or record its rollback/recovery point and timebox. Run focused diagnostics during editing and `lake build` plus the semantic `.fhm` matrix at the checkpoint.
- Correct suite expectations under D2:
  - `polyrec-nested`, `polyrec-groups-nested`, `polyrec-inner-poly-calls`, and `polyrec-mixed-group`: **reject** (genuine in-SCC multi-instantiation).
  - `polyrec-unannotated-must-fail`, `polyrec-inner-poly-unannotated-must-fail`, and `polyrec-mixed-conflict-must-fail`: **reject** as before.
  - Historical `polyrec-skolem-leak-must-fail`: its calls use one fixed recursive instantiation, so it is legal DM and has been renamed `polyrec-mixed-fixed-instantiation`; **accept** with result `[5, 5, 5]`.
  - `polyrec-head-binder-scoped-must-fail`: **reject at Infer** to record the separately parked complete head-binder/scoped-type-variable form. This is an implementation limitation, not an extra semantic restriction of DM.
- `update Fixture`/`#guard`s referencing `RecSpec.init` shapes get updated alongside.
- Use lean-lsp MCP tools (`lean_diagnostic_messages`, `lean_goal`, `lean_multi_attempt`) during editing; avoid full `lake build` loops where file-level diagnostics suffice.
- Small commits per component are useful only where the repository remains coherent; green-at-every-commit is not a requirement.

## Scope if this work is deliberately resumed

Keep ceiling deletion, `Expr.erase` removal (R1 re-pointing), `.found`, BL, and the spine port out of the B6 checkpoint. R1 is independently deferred; `.found`/LSP/BL is the current architectural path and should not be bundled into this parked repair.

## Historical report format (if reactivated by a new brief)

Per commit: what changed, `lake build` status, sorry count, suite line. Final: overall diffstat, remaining risks, and whether `Infer.sound`'s letRec case stayed axiom-clean (`lean_verify` on it if feasible).
