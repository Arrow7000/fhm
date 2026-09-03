# Polymorphic-recursion smoke tests (`scratch/polyrec-*`)

Dedicated `.fhm` stress tests for annotated polymorphic recursion, driven by
`PolyRecTest.lean` (run with `lake env lean --run scratch/PolyRecTest.lean`).
Each file runs the real pipeline: parse → erase → lower → infer → report →
exhaustiveness → elaborate → **evaluate** (type-passing evaluator: polymorphic
recursion must also *execute* correctly, not just typecheck).

> **Note.** The driver mirrors the HM path of `FHM.Live.checkPipeline` without
> importing `FHM.Live`, because `Live → Bounds.Check → Bounds.Synth →
> Bounds.Typing` and `Bounds.Typing` currently fails to build on `main`
> (pre-existing: non-exhaustive `Ty.bl` match, flagged "prove after shape" —
> this is why `lake build fhm` fails while CI's default target stays green).

## The files

| file | what it pins down | status |
|---|---|---|
| `polyrec-nested.fhm` | Mycroft's `Nested`: recursion at `Nested (List a)` (one inner instantiation site), three distinct outer instantiations, mixed ADTs at one call site | ✓ passes, evals to 7 |
| `polyrec-inner-poly-calls.fhm` | **THE hard case**: two inner call sites of the annotated `f` at *different* types (`a` and `List Int`) inside the letRec block, mutual with unannotated `g`. Catches: ascription ignored, monomorphic recursion, one shared instance var across sites | ✓ passes, evals to (4, 4) |
| `polyrec-mixed-group.fhm` | Mixed group where the unannotated `g` keeps a FREE pool var: generalises to `∀ b. Int -> b -> Int` at group exit and is used at two types outside | ✓ passes, evals to (1, 2) |
| `polyrec-groups-nested.fhm` | Three top-level groups (three nested letRec blocks), cross-group calls, `stats` calling `size` mid-group-checking | ✓ passes, evals to 7 |
| `polyrec-skolem-leak-must-fail.fhm` | Expressiveness boundary: `f` passing its RIGID scoped var to unannotated `g` is **untypeable by design** (`RecSpecs.PolyTyped` nests poly skolems inside the pool opening; `SpikeLetRecMixed.skolemLeak_untypeable`) | ✓ correctly rejected |
| `polyrec-unannotated-must-fail.fhm` | Plain polymorphic recursion without annotation → infinite type | ✓ correctly rejected |
| `polyrec-inner-poly-unannotated-must-fail.fhm` | Inner two-instantiation case with no annotation → occurs-check failure (decidability boundary) | ✓ correctly rejected |
| `polyrec-mixed-conflict-must-fail.fhm` | Mixed group where the mono member's own recursion conflicts with the pin | ✓ correctly rejected |

`8/8 behaved as expected` — including correct per-binder scheme reports
(inferred *and* ascribed) and the internal `letIn (some σ)` annotations of the
elaborated term (group members' runtime schemes).

## Semantics notes discovered while testing (worth knowing before extending)

1. **Sibling syntax is `let…in`-only.** Top-level lets are always standalone;
   mutual groups at top level are formed by SCC (`Program.ofFlat`). A same-column
   sibling after a top-level let is parsed as the program body.
2. **One infix operator per expression.** `a + b + c` must be written
   `a + (b + c)` (deliberate parser decision, `Surface/Parse.lean`).
3. **Skolem-leak boundary (by design, documented in `RecGroup.rigidVars`
   and machine-checked in `SpikeLetRecMixed.skolemLeak_untypeable`):**
   an unannotated group member's shared monotype can never mention an annotated
   sibling's scoped type variables. Concretely: if annotated `f` passes its
   rigid `x : a` to unannotated `g`, the program is rejected. Workaround:
   pass only skolem-free values to `g`, or annotate `g` too.
4. Consequently, an unannotated member that *does* keep free type variables
   generalises over its own leftover shared-pool vars at group exit (DM cut),
   but never over an annotated sibling's skolems.
5. The `BL 0 0` display in some reports is the erase package's default List
   bounds rendering, not an error; the `inferred:` line is the HM truth.

## Known pre-existing issue on this commit (not touched here)

`lake build fhm` (the CLI) fails: `FHM/Bounds/Typing.lean` has non-exhaustive
matches over `Ty.bl` (flagged "prove after shape ✅" in-file). CI only builds
the default `FHM` target, so this is invisible on GitHub. Fixing it is one
`match` completion away (four `Ty.bl` cases), tracked in the report.
