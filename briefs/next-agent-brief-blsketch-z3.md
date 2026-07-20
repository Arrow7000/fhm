<!-- Written 2026-07-17; updated 2026-07-18 after synth_sound / Check land;
     updated 2026-07-20 after elem types + mixed Nat/Type schemes. -->

# Next-agent brief: BoundedList sketch (`BLSketch`) × Z3

**Branch:** `main` (elem-poly landed here)
**Spine:** `FHM/BLSketch.lean`
**Oracle:** `FHM/Z3/` (Percissus subprocess port; optional lake target `FHMZ3`)
**Elem / type-∀ session:** [`next-agent-brief-blsketch-elem-poly.md`](next-agent-brief-blsketch-elem-poly.md) · plan/spec under `docs/superpowers/`

---

## Bigger picture

FHM’s usual story is Hindley–Milner with a principality / InferW pipeline. **Bounded lists are a different axis:** lengths as *refinement bounds* on list type `BL lo hi α`, sitting **on top of ordinary HM**, not a System‑F redesign.

The hard work is **subtyping + arithmetic obligations** (DML / Liquid / HM(X) territory): compare, join, meet inhabitability, solve for annotation holes, demand that outputs are unique when ambiguity would escape. Principality of *bounds* is not free; the sketch accepts that and uses Z3 as a **best‑effort trusted oracle**.

What we built is a **didactic end‑to‑end spine**, not production FHM:

1. Count language + constraint problems (`ForallProblem` / `ExistsProblem`)
2. Toy terms/types with `TypeOf Δ Γ e τ` (declarative **synthesis** center — syntax-directed)
3. Separate `Check Δ Γ e τ` for checking (synth type + `Sub` / solve+unique) — **not** general subsumption inside `TypeOf`
4. Algorithmic `synth` / `check` with `AnnoTy` holes and freshness frontier `Φ`
5. Real Z3 behind `checkValid` / `solve` / `unique` via `@[implemented_by]`
6. **Proved:** `synth_sound` (`synth` ⇒ `TypeOf`) and `check_sound` (`check` ⇒ `Check`)
7. **Element types + prenex type schemes:** `BL lo hi α`, `Ty.tbind`, mixed count/type binders with explicit `@`, `nil` as a scheme, `Bool` + `true`/`false`

---

## What landed (commits on this branch)

Rough chronology (newest first among BL work):

| Commit | What |
| --- | --- |
| `5d5bc6e` | Typed nil/cons/match; Bool; stdlib schemes (`nil @α`, mismatch demos) |
| `ca1dc54` | `@[simp]` on DemandOK / SchemeWF mirrors |
| `6153a0e` | Mixed Nat/Type scheme binders with kinded `@` |
| `81c6d6a` … `779732c` | `BL lo hi` carries element type (Unit-hardwired, then soundness) |
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
- `FHM/BLSketch/Pretty.lean` — counts, types, schemes (`∀ {a b : Nat, α}. …`), `@` spines
- `FHM/Z3/{Oracle,Encode,Parse,Process,Query,Atom}.lean` + `FHM/Z3.lean`
- `lakefile.toml` — optional `[[lean_lib]] name = "FHMZ3"` (not in default `FHM` build)
- Smoke / demos:
  - `scratch/z3_smoke.lean` — raw Z3 ping
  - `scratch/blsketch_z3_smoke.lean` — thin BLSketch oracle call
  - `scratch/blsketch_z3_demos.lean` — validity + witnesses + uniqueness
  - `scratch/blsketch_synth_demos.lean` — **`synth` / `check` / holes / match / app / stdlib / mismatch** (run this)

```bash
lake build FHMZ3          # if needed
lake env lean scratch/blsketch_z3_demos.lean
lake env lean scratch/blsketch_synth_demos.lean   # needs `z3` on PATH
```

---

## Design decisions (locked — don’t reopen unless asked)

| Area | Decision |
| --- | --- |
| Architecture | Bounds **layer on HM**; only list form is `BL lo hi α`; unbounded ≈ `BL 0 ∞ α` |
| Element type | `Ty.bl lo hi elem`; `AnnoTy` holes **only on bound slots** (elem always concrete `Ty`) |
| Nonlinear | Keep `mul` including var×var (`flatMap`); undecidable in theory, Z3 in practice |
| Oracles | **Three** 3‑valued APIs: `checkValid`, `solve`, `unique`; `unknown` never proves |
| Trust / TCB | Only `.valid` / `.witness` / `.unique` are axiomatized as sound; Encode/Parse/Process unverified; don’t axiomatize `.invalid`/`.unsat`/`.multiple` |
| Ambiguity | When uniqueness fails on **escaping** outputs → **no derivation** (fail / require annotation). No commit‑a‑model in the core relation |
| Demand | Negative bounds: ≤1 inferable, affine over rigid (`DemandOK`, syntactic). Positive may use products |
| Join / meet | Join = free `min`/`max` when elems equal; meet inhabitability = `checkValid` side condition, not a `TypeOf` constructor |
| Schemes | Prenex **count then type** binders (`SchemeBinder` / `SchemeArg`); **story A** — flat indices + `SchemeWF`; no nested scheme LN; explicit `@` spine (no inference) |
| `nil` | `nilScheme : ∀ {α}. BL 0 0 α`; bare `Expr.nil` kept for `[]` pretty but **does not synth** |
| Bases | `Unit`, `Bool` (`Expr.true` / `Expr.false`) |
| `Sub` on elem | **Definitional `elem = elem'` only** (no recursive elem subtyping yet) |
| Annotations | Structure annotated on λ/let; bound holes via `AnnoTy` (`Option Count`) |
| Match | Refine `Δ`; nil: `lo ≤ 0` (**do not force `hi = 0`**); cons‑only when `1 ≤ lo`; nil‑only when `hi ≤ 0`; **both-`BL` branches join** (same elem); non-`BL` branches must be equal; `consCtx` binds head:`elem`, tail:`BL (pred lo) (pred hi) elem` |
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
- **Elem subtyping** (recursive `Sub` on element types) — v1 is equality only
- Bare-`nil` under expected type (special `Check` rule) — use `nil @α`
- Inferred let‑generalisation + production commit policy; type-`@` inference
- `letRec` / recursive map/filter/flatMap bodies
- `unknown` UX / solver timeouts as product features
- Wiring bounds into real FHM Core / phase‑2 InferW
- Replacing subprocess with libz3 FFI
- Completeness of `synth` (non-goal)
- General `TypeOf` subsumption (rejected — use `Check` instead)

---

## Outstanding / good next work

### High value (natural next sessions)

1. ~~**`synth_sound` / `check_sound`**~~ — **done** (`17c4c16`; kept through elem-poly).
2. ~~**Element types + mixed Nat/Type schemes**~~ — **done** (see elem-poly brief).
3. **Soft spots** (document or lightly tighten — see below; **no redesign required** unless user asks):
   - Flat scheme hygiene vs real LN (now with mixed binder kinds — still prenex only)
   - Algo does not substitute witnesses into returned types; declarative existentially picks `σ`
   - Escape / `unique` on `obsBounds` — confirm policy is what we want at every `forceSubtype` site
   - Standalone `tail` synth prints `pred(·+1)` until packed under `letScheme`+`Sub`

### Later / product

- Elem subtyping / sub-checking
- InferW / FHM phase‑2 integration of bounds
- Inferred generalisation + explicit commit‑vs‑annotate policy for production
- Optional C FFI for Z3

---

## Soft spots — what they actually are (for humans)

These are **not blockers**. They are “know the sketch’s corners.”

### A. Flat scheme hygiene vs LN
**What:** Scheme bodies use flat count/type indices under story A (`SchemeWF`). No locally-nameless / nested binder hygiene. Telescope is counts-then-types.
**Risk:** Fine for top-level library schemes in the toy; would break if we nested schemes.
**Decision needed?** Only if you want nested schemes or production FHM schemes soon → then reopen LN. Otherwise leave locked.

### B. Witnesses vs returned types
**What:** Algorithmic `forceSubtype` / `solve` finds a witness `σ` but **does not rewrite** the type — `synth` of an ascription with holes can still return a type mentioning `i₀`, `i₁`, while the derivation’s Infer rule existentially holds `σ`. Declarative `TypeOf` never returns a substitution either.
**Risk:** Confusing when printing types in demos; not a soundness bug (`synth_sound` / `check_sound` already match).
**Decision needed?** Only if you want “normalize types under `σ` before returning” as UX/product. Optional polish, not a foundation fork.

### C. Escape / uniqueness policy
**What:** `unique` is checked on the **source** type’s `obsBounds`. Fail ⇒ no derivation. Same helper (`forceSubtype`) at app, anno, letScheme, and `check`.
**Risk:** Whether “observable escape” is the right output list at every site (e.g. should app uniqueness look at the *codomain* somehow?). Current policy is uniform and locked in the Infer rules.
**Decision needed?** Only if you notice a concrete weird example where you’d want different outs. Otherwise leave it.

### D. Elem equality vs subtyping
**What:** `Sub` / join / `subConstraints` require `elem = elem'` only.
**Risk:** Incomplete as a subtype story (e.g. no `BL _ _ α <: BL _ _ β` via `α <: β`).
**Decision needed?** Reopen only for a dedicated elem-subtyping session.

---

## How to work in this repo (BL slice)

- Prefer **lean-lsp-mcp** diagnostics / goals over `lake build` for routine proving (`FHM/BLSketch.lean` is large). Targeted `lake build FHM.BLSketch` is fine when oleans are stale.
- Build `FHMZ3` when touching Z3 modules or after fresh checkout; default `FHM` target may omit it.
- Don’t expand the toy into full HM inference — holes only on **bound slots** (`AnnoTy`); scheme instantiation stays explicit `@`.
- Keep the TCB narrow: positive oracle answers only.
- Keep `TypeOf` syntax-directed; checking goes through `Check`.
- Unrelated dirty tree noise often present: `scratch/live.fhm`, `scripts/watch-live.sh`, `FHM/PatCompDemo.lean` — leave alone unless asked.

---

## Suggested first moves for the next agent

1. Skim module contract + `Check` + §9 `synth` in `BLSketch.lean`.
2. Run `scratch/blsketch_synth_demos.lean` (and optionally `blsketch_z3_demos.lean`) to confirm `z3` on PATH.
3. Soft spots / FHM wiring / elem-subtyping — **only if the user asks**.
4. Don’t reopen DemandOK semantics, scheme LN, opsem, general `TypeOf` subsumption, or FHM merge without an explicit ask.

---

## One‑liner for orientation

> Toy BoundedList layer with live Z3: `BL lo hi α`, prenex count/type schemes with explicit `@`, syntax-directed `TypeOf`, separate `Check`, and proved `synth_sound` / `check_sound`. Bounds oracle unchanged; next is optional FHM wiring or elem-subtyping — not reinventing arithmetic or free subsumption.
