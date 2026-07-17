<!-- Written 2026-07-17; updated 2026-07-18 after synth_sound / Check land. -->

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
2. Toy terms/types with `TypeOf Δ Γ e τ` (declarative **synthesis** center — syntax-directed)
3. Separate `Check Δ Γ e τ` for checking (synth type + `Sub` / solve+unique) — **not** general subsumption inside `TypeOf`
4. Algorithmic `synth` / `check` with `AnnoTy` holes and freshness frontier `Φ`
5. Real Z3 behind `checkValid` / `solve` / `unique` via `@[implemented_by]`
6. **Proved:** `synth_sound` (`synth` ⇒ `TypeOf`) and `check_sound` (`check` ⇒ `Check`)

---

## What landed (commits on this branch)

Rough chronology (newest first among BL work):

| Commit | What |
| --- | --- |
| `17c4c16` | Prove `synth_sound` + `check_sound`; `Check` judgment; `Sub.bl_refl` |
| `d5616b3` | Align TypeOf/synth (HM narrowing at app/letScheme; matchBL join; total synth) |
| `609029c` | Z3 witness demos + handoff brief |
| `c478e9b` | Percissus Z3 → `FHM/Z3/`; wire oracles; smoke files |
| `55b74af` | Algorithmic `synth`/`check` + `AnnoTy` holes |
| `e47e4c1` … `d0a338f` | Match refine; WF schemes; firm TypeOf / Δ threading |
| `1c3308e` | Rename `BLChallenges` → `BLSketch` |

**Earlier taxonomy era** (`BLChallenges` challenge lemmas) is superseded as the *deliverable*; intuitions (compare / join / meet / solve) survive in the module contract at the top of `BLSketch.lean`.

### Files that matter

- `FHM/BLSketch.lean` — everything didactic; start with the module docstring contract
- `FHM/Z3/{Oracle,Encode,Parse,Process,Query,Atom}.lean` + `FHM/Z3.lean`
- `lakefile.toml` — optional `[[lean_lib]] name = "FHMZ3"` (not in default `FHM` build)
- Smoke / demos:
  - `scratch/z3_smoke.lean` — raw Z3 ping
  - `scratch/blsketch_z3_smoke.lean` — thin BLSketch oracle call
  - `scratch/blsketch_z3_demos.lean` — validity + witnesses + uniqueness
  - `scratch/blsketch_synth_demos.lean` — **`synth` / `check` / holes / match / app** (run this)

```bash
lake build FHMZ3          # if needed
lake env lean scratch/blsketch_z3_demos.lean
lake env lean scratch/blsketch_synth_demos.lean   # needs `z3` on PATH
```

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
| Match | Refine `Δ`; nil: `lo ≤ 0` (**do not force `hi = 0`**); cons‑only when `1 ≤ lo`; nil‑only when `hi ≤ 0`; **both-`BL` branches join**; non-`BL` branches must be equal |
| Freshness | Thread `Φ : Nat` (InferW‑style), not `StateM` |
| Narrowing sites | HM-style solve+unique at **app / anno / letScheme** (`*Infer` rules) and algorithmic `check`; plain `Sub` at those sites too |
| Checking vs synth | **`TypeOf` stays syntax-directed** (no general subsumption). Algorithmic `check` is justified by separate **`Check`** (`ofSub` / `ofInfer`) |
| `Sub` refl | `Sub.bl_refl` — equal BL intervals without opaque `checkValid` (no completeness axiom) |
| Z3 plumbing | Subprocess `z3` on PATH; **no** libz3 C shim yet |
| Deliverable shape | Catalog‑first abandoned; **`TypeOf` is the didactic synth center**; `Check` is the checking dual |

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
- Completeness of `synth` (non-goal)
- General `TypeOf` subsumption (rejected — use `Check` instead)

---

## Outstanding / good next work

### High value (natural next sessions)

1. ~~**`synth_sound` / `check_sound`**~~ — **done** (`17c4c16`).
2. **Richer live demos** — `scratch/blsketch_synth_demos.lean` (extend as needed; keep spine file lean).
3. **Soft spots** (document or lightly tighten — see below; **no redesign required** unless user asks):
   - Flat scheme hygiene vs real LN
   - Algo does not substitute witnesses into returned types; declarative existentially picks `σ`
   - Escape / `unique` on `obsBounds` — confirm policy is what we want at every `forceSubtype` site

### Later / product

- InferW / FHM phase‑2 integration of bounds
- Inferred generalisation + explicit commit‑vs‑annotate policy for production
- Optional C FFI for Z3

---

## Soft spots — what they actually are (for humans)

These are **not blockers**. They are “know the sketch’s corners.”

### A. Flat scheme hygiene vs LN
**What:** Scheme bodies use rigid indices `0 .. binders-1` only (`story A`). No locally-nameless / nested binder hygiene.
**Risk:** Fine for top-level library schemes in the toy; would break if we nested schemes or mixed binder kinds casually.
**Decision needed?** Only if you want nested schemes or production FHM schemes soon → then reopen LN. Otherwise leave locked.

### B. Witnesses vs returned types
**What:** Algorithmic `forceSubtype` / `solve` finds a witness `σ` but **does not rewrite** the type — `synth` of an ascription with holes can still return a type mentioning `i₀`, `i₁`, while the derivation’s Infer rule existentially holds `σ`. Declarative `TypeOf` never returns a substitution either.
**Risk:** Confusing when printing types in demos; not a soundness bug (`synth_sound` / `check_sound` already match).
**Decision needed?** Only if you want “normalize types under `σ` before returning” as UX/product. Optional polish, not a foundation fork.

### C. Escape / uniqueness policy
**What:** `unique` is checked on the **source** type’s `obsBounds`. Fail ⇒ no derivation. Same helper (`forceSubtype`) at app, anno, letScheme, and `check`.
**Risk:** Whether “observable escape” is the right output list at every site (e.g. should app uniqueness look at the *codomain* somehow?). Current policy is uniform and locked in the Infer rules.
**Decision needed?** Only if you notice a concrete weird example where you’d want different outs. Otherwise leave it.

---

## How to work in this repo (BL slice)

- Prefer **lean-lsp-mcp** diagnostics / goals over `lake build` for routine proving (`FHM/BLSketch.lean` is large).
- Build `FHMZ3` when touching Z3 modules or after fresh checkout; default `FHM` target may omit it.
- Don’t expand the toy into full HM inference — holes only on **bound slots** (`AnnoTy`).
- Keep the TCB narrow: positive oracle answers only.
- Keep `TypeOf` syntax-directed; checking goes through `Check`.
- Unrelated dirty tree noise often present: `scratch/live.fhm`, `scripts/watch-live.sh`, `FHM/PatCompDemo.lean` — leave alone unless asked.

---

## Suggested first moves for the next agent

1. Skim module contract + `Check` + §9 `synth` in `BLSketch.lean`.
2. Run `scratch/blsketch_synth_demos.lean` (and optionally `blsketch_z3_demos.lean`) to confirm `z3` on PATH.
3. Extend demos or start FHM/InferW wiring — **only if the user asks**. Soft spots are documentation-grade unless reopened.
4. Don’t reopen DemandOK semantics, scheme LN, opsem, general `TypeOf` subsumption, or FHM merge without an explicit ask.

---

## One‑liner for orientation

> Toy BoundedList layer with live Z3: syntax-directed `TypeOf`, separate `Check`, total `synth`/`check`, and proved `synth_sound` / `check_sound`. Next is demos / optional FHM wiring — not reinventing arithmetic or adding free subsumption.
