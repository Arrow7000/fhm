<!-- Written 2026-07-17: handoff after TypeOf + synth + Z3 subprocess oracle land. -->

# Next-agent brief: BoundedList sketch (`BLSketch`) × Z3

**Branch:** `bl-problem-taxonomy`
**Spine:** `FHM/BLSketch.lean`
**Oracle:** `FHM/Z3/` (Percissus subprocess port; optional lake target `FHMZ3`)

---

## Bigger picture

FHM’s usual story is Hindley–Milner with a principality / InferW pipeline. **Bounded lists are a different axis:** lengths as *refinement bounds* on a single list type `BL lo hi`, sitting **on top of ordinary HM**, not a System‑F redesign.

The hard work is **subtyping + arithmetic obligations** (DML / Liquid / HM(X) territory): compare, join, meet inhabitability, solve for annotation holes, demand that outputs are unique when ambiguity would escape. Principality of *bounds* is not free; the sketch accepts that and uses Z3 as a **best‑effort trusted oracle**.

What we built is a **didactic end‑to‑end spine**, not production FHM:

1. Count language + constraint problems (`ForallProblem` / `ExistsProblem`)
2. Toy terms/types with `TypeOf Δ Γ e τ` (declarative center of gravity)
3. Algorithmic `synth` / `check` with `AnnoTy` holes and freshness frontier `Φ`
4. Real Z3 behind `checkValid` / `solve` / `unique` via `@[implemented_by]`

You can now **run** the oracles and hold concrete answers (valid / invalid / witnesses / unique / multiple). The remaining Lean work is mostly **proving the algorithmic layer matches the declarative one**, then optionally wiring into real FHM.

---

## What landed (commits on this branch)

Rough chronology (newest first among BL work):

| Commit | What |
| --- | --- |
| `c478e9b` | Percissus Z3 → `FHM/Z3/`; wire oracles; smoke files |
| `55b74af` | Algorithmic `synth`/`check` + `AnnoTy` holes |
| `e47e4c1` … `d0a338f` | Match refine; WF schemes; firm TypeOf / Δ threading |
| `1c3308e` | Rename `BLChallenges` → `BLSketch` |

**Earlier taxonomy era** (`BLChallenges` challenge lemmas) is superseded as the *deliverable*; intuitions (compare / join / meet / solve) survive in the module contract at the top of `BLSketch.lean`.

### Files that matter

- `FHM/BLSketch.lean` — everything didactic; start with the module docstring contract
- `FHM/Z3/{Oracle,Encode,Parse,Process,Query,Syntax}.lean` + `FHM/Z3.lean`
- `lakefile.toml` — optional `[[lean_lib]] name = "FHMZ3"` (not in default `FHM` build)
- Smoke / demos:
  - `scratch/z3_smoke.lean` — raw Z3 ping
  - `scratch/blsketch_z3_smoke.lean` — thin BLSketch oracle call
  - `scratch/blsketch_z3_demos.lean` — **validity + witnesses + uniqueness** (run this)

```bash
lake build FHMZ3          # if needed
lake env lean scratch/blsketch_z3_demos.lean   # needs `z3` on PATH
```

Verified demo output (2026-07-17): pinFive → `i_0=5`; sumSeven → `7+0`; productTwelve → `2×6`; unsat; unique vs multiple on product factors vs product value.

---

## Design decisions (locked — don’t reopen unless asked)

| Area | Decision |
| --- | --- |
| Architecture | Bounds **layer on HM**; only list form is `BL`; unbounded ≈ `BL 0 ∞` |
| Nonlinear | Keep `mul` including var×var (`flatMap`); undecidable in theory, Z3 in practice |
| Oracles | **Three** 3‑valued APIs: `checkValid`, `solve`, `unique`; `unknown` never proves |
| Trust / TCB | Only `.valid` / `.witness` / `.unique` are axiomatized as sound; Encode/Parse/Process unverified; don’t axiomatize `.invalid`/`.unsat`/`.multiple` |
| Ambiguity | When uniqueness fails on **escaping** outputs → **no derivation** (fail / require annotation). No commit‑a‑model in the core relation |
| Demand | Negative bounds: ≤1 inferable, affine over rigid (`DemandOK`, syntactic). Positive may use products |
| Join / meet | Join = free `min`/`max`; meet inhabitability = `checkValid` side condition, not a `TypeOf` constructor |
| Schemes | Bound‑∀ only (`BScheme`); **story A** — flat binders `0..n-1` + `WF`; no nested scheme LN |
| Annotations | Structure annotated on λ/let; bound holes via `AnnoTy` (`Option Count`) |
| Match | Refine `Δ`; nil: `lo ≤ 0` (**do not force `hi = 0`**); cons‑only when `1 ≤ lo`; nil‑only when `hi ≤ 0` |
| Freshness | Thread `Φ : Nat` (InferW‑style), not `StateM` |
| Z3 plumbing | Subprocess `z3` on PATH; **no** libz3 C shim yet |
| Deliverable shape | Catalog‑first abandoned; **`TypeOf` is the didactic center** |

---

## Explicitly deferred / out of scope

Leave these alone unless the user reopens them:

- `zip` / `take` / `drop` / `splitAt` (and length‑splitting without annotations)
- Value‑`Nat` appearing in types; indexing APIs that “eval looks at type”
- Opsem, preservation, progress
- Scheme binder LN / nested hygiene (stay on story A)
- Semantic / normalized `DemandOK` (syntactic is enough for the sketch)
- Commit‑a‑model when non‑unique (sketch fails instead)
- Type‑level `∀`; inferred let‑generalisation + production commit policy
- `unknown` UX / solver timeouts as product features
- Wiring bounds into real FHM Core / phase‑2 InferW
- Replacing subprocess with libz3 FFI

---

## Outstanding / good next work

### High value (natural next sessions)

1. **`synth_sound`** — theorem stated around line ~908 in `BLSketch.lean`, currently `sorry`. Prove algorithmic `synth`/`check` imply declarative `TypeOf` for the covered fragment. This is the main “close the loop” proof goal.
2. **Richer live demos** — small `TypeOf` / `synth` examples that *call* the live oracle (matchNil/matchCons refine; `annoInfer` solving holes; a tiny `flatMap`‑style mul). Demos in `scratch/` are fine; keep the spine file from becoming a novel.
3. **Soft spots in the sketch** (fix or document, don’t redesign):
   - Flat scheme hygiene vs real LN
   - How algorithmic subst / `ψ` relates to declarative `annoInfer` existential witnesses
   - Whether `forceSubtype`’s fail‑on‑non‑unique matches the intended observable‑escape policy everywhere

### Later / product

- InferW / FHM phase‑2 integration of bounds
- Inferred generalisation + explicit commit‑vs‑annotate policy for production
- Optional C FFI for Z3
- Completeness of `synth` (non‑goal for the toy; don’t chase unless asked)

---

## How to work in this repo (BL slice)

- Prefer **lean-lsp-mcp** diagnostics / goals over `lake build` for routine proving (`FHM/BLSketch.lean` is large).
- Build `FHMZ3` when touching Z3 modules or after fresh checkout; default `FHM` target may omit it.
- Don’t expand the toy into full HM inference — holes only on **bound slots** (`AnnoTy`).
- Keep the TCB narrow: positive oracle answers only.
- Unrelated dirty tree noise often present: `scratch/live.fhm`, `scripts/watch-live.sh`, `FHM/PatCompDemo.lean` — leave alone unless asked.

---

## Suggested first moves for the next agent

1. Skim module contract + §5 Z3 bridge + §9 `synth` in `BLSketch.lean`.
2. Run `scratch/blsketch_z3_demos.lean` once to confirm the environment (`z3` on PATH).
3. Either start **`synth_sound`**, or add **one** end‑to‑end `synth` demo that prints a solved assignment for an annotated hole — whichever the user wants.
4. Don’t reopen DemandOK semantics, scheme LN, opsem, or FHM merge without an explicit ask.

---

## One‑liner for orientation

> We have a toy BoundedList type system with a real Z3 backend: declarative `TypeOf`, algorithmic `synth`/`check`, and demos that return concrete witnesses. Next is prove `synth_sound` and optionally deepen demos / FHM wiring — not reinvent the arithmetic layer.
