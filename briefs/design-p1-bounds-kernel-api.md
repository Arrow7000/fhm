# P1 design: Bounds kernel (conceptual)

**Status:** API in Lean for sign-off — see `FHM/Bounds/*.lean`  
**Date:** 2026-07-28  

Policy: review **inductives / props / theorem statements in the Lean files**, not in this memo. This doc is orientation only.

---

## Intent

Extract the **Ty-free** bound kernel from BLSketch into three modules under `FHM/Bounds/`, optional lake target `FHMBounds`. Default `FHM` build stays pure HM.

After sign-off: commit → subagents fill `sorry`s, rewire BLSketch to import Bounds (single `Count`), green demos.

---

## Three files (max)

| File | Role |
|------|------|
| `FHM/Bounds/Kernel.lean` | Counts, constraints, problems, DemandOK, intervals, match-Δ helpers |
| `FHM/Bounds/Oracle.lean` | Z3 bridge, `checkValid` / `solve` / `unique`, soundness axioms |
| `FHM/Bounds/Commit.lean` | Narrowing evidence, policies, `decideCommit`, `ForceOk` |

No fourth file for now (no barrel module).

**Out of P1:** toy `Ty`/`Expr`/`TypeOf`/`Sub`/`forceSubtype` on types (stay in BLSketch until Core `BoundInfo`).

---

## Import graph

```text
FHM.Z3.*  ←  Bounds.Oracle  ←  Bounds.Commit
                ↑
           Bounds.Kernel
```

BLSketch will import Bounds after rewire; Core/InferW/Surface never import Bounds.

---

## TCB

- Irreducible: `opaque z3Run` + Z3 `decide_*_sound` axioms  
- Bounds layer: three problem-language axioms on positive oracle answers (collapse later)  
- Uniqueness not part of declarative typing (Commit policy only)

---

## Acceptance (after implementation)

- `lake build FHMBounds` green (sorry-free)  
- BLSketch rewired; no duplicate `Count`  
- Default `lake build` unchanged / pure  
- Scratch Z3 demos still work  

---

## Sign-off

Review the three Lean files. Confirm or amend shapes there; this memo stays conceptual.
