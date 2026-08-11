# Design memo: bounds-preserving double elaboration

**Status:** Agreed direction (2026-08-04). **Authoritative** product architecture for
bounds packaging.  
**Supersedes (packaging only):** erase → name-sidecar → `ofLower` → dual Bounds
walk (`design-memo-bounds-elaborator.md`, elaborator architecture brief).  
**Does not** reopen dual-stack *meaning* (HM owns shape; bounds owns list lengths).  
**Does** change *how* length ascriptions and elaborated types are carried on Core.

**Related:**

- `design-memo-bounds-layer-on-core.md` — product rules still in force (D22/D24/R3, …)
- `design-memo-bounds-elaborator.md` — **historical**; coverage-authority diagnosis only
- `next-agent-brief-bounds-elaborator-architecture.md` — **historical** failure taxonomy
- **`next-agent-brief-path-r-dual-stack.md`** — **active (2026-08-11):** Path R formalization,
  residual Infer soundness/completeness statements, proof order, session handoff

**This doc’s job:** pipeline, Core/Infer blast radius, what to scrap vs keep,
theorem targets, work phases.

### Glossary (plain language)

| Term | Meaning |
|------|---------|
| **BL / bounded list** | List type with length interval `lo…hi` (surface `BL lo hi t`, Core `Ty.list lo hi t`) |
| **Bare List** | List shape with **no** user length demand (Infer-filled or user wrote `List`) |
| **HM pass** | InferW: ordinary Hindley–Milner; treats every list as the same shape regardless of lengths |
| **Bounds pass** | Second elaboration: assign/check length intervals; rewrite bare List to concrete BL where synth succeeds |
| **Semi-elaborated Core** | After HM only: structure fixed; user BL still on binders; bare Lists not yet filled with lengths |
| **Fully bounds-elaborated Core** | After bounds pass: list types carry intervals where known; ready for length-aware match coverage |
| **Demand** | Expected bounds type when checking a term (from ascription or function domain) |
| **Demand peel** | If checking a λ against `domain → codomain`, bind the param at `domain` and check the body at `codomain` |
| **Binder discipline** | Ascribed binder → check RHS meets ann, env gets the **ann**; unascribed → synth RHS, env gets that result |
| **Bounds-blind unify** | Unification ignores `lo`/`hi`; two BLs unify like two Lists; HM never picks lengths |
| **BoundAwareCovers** | Match exhaustiveness that uses length intervals (and ordinary ADT ctors); under `--bl` this replaces HM-only exhaustiveness |

### Phase status (updated 2026-08-11)

| Phase | Content | Status |
|-------|---------|--------|
| **0** | Agree design; supersede old memos; deprecate old packaging entry points; list acceptance cases | **Mostly done** (design agreed; banners + deprecations) |
| **1** | `Ty.bl` in Core; lower preserves BL | **Largely done** (committed) |
| **2** | Infer bounds-blind + ann preservation + **Path R residual metatheory** | **In progress** — statements mostly Path R; proofs fenced; see path-r brief |
| **3** | Bounds elab driver → rewrite AST | Pending (product; after metatheory checkpoint) |
| **4** | BoundAwareCovers; delete Matches dual walk | Pending |
| **5** | Remove erase/ofLower product path (Live) | Pending — **Live may stay broken** until metatheory lands |
| **6** | Theorems: residual soundness → completeness → ann preserve → bounds ascription | **Soundness next** after §6 checklist in path-r brief |

**Phase 0 exit (enough to start Phase 1):** this memo stable; old architecture docs
bannered; key packaging symbols marked deprecated in code comments. A full green
new-world e2e gate is **not** a Phase 0 blocker (nothing implements the new path
yet); keep a short written acceptance list and grow programs as Phase 1–3 land.

---

## 1. Problem with the current packaging

Intended story was always:

```text
HM is pure and complete first; bounds is a parasitic second judgment.
```

Executable packaging broke that for nested user demands:

1. **Destructive erase** turns every `BL` into `List` before lower/Infer.
2. Only **top-level** binder BL ascriptions are kept (name-keyed sidecar + `ofLower`).
3. **Nested** `: BL …` ascriptions are dropped at `eraseExpr`.
4. Bounds then walks Core with a partial ascription table and a **second** Matches
   interpreter that rebuilds environments with stubs — Class A failures.

Nested *terms* were still analyzed; nested *BL ascriptions* were not preserved.
That is incomplete and unprincipled for “check what the user wrote,” not proof
that parasitic bounds is impossible.

---

## 2. Agreed architecture

### 2.1 Pipeline

```text
Surface (may contain BL)
  │
  │  lower — keep BL on Core types / binder annotations
  │  (park head-binder sugar until `_` holes work properly)
  ▼
Core after lower
  │  user ascriptions may still say BL …; other lists are bare List shape
  │
  │  InferW (HM only)
  │  • unify ignores lengths (BL same shape as List)
  │  • HM never chooses lo/hi
  │  • empty annotations filled with bare List / HM schemes only
  │  • never overwrite a user BL annotation with List
  │  • when rebuilding let/λ/letRec, copy annotations through
  ▼
Semi-elaborated Core   (HM done; lengths not solved)
  │
  │  Bounds elaboration
  │  • user BL annotation → demand; check; keep that interface on the binder
  │  • bare List → synth lengths from the term; write BL back
  │  • pack / multi-model escape policy (R3) at binders
  │  • under arrow demand, enter λ by binding the domain (demand peel)
  ▼
Fully bounds-elaborated Core   (list types carry intervals where known)
  │
  │  BoundAwareCovers  (under --bl: only length-aware + ADT coverage)
  ▼
accept / reject
  │
  ▼
evaluate  (runtime ignores length intervals)
```

Under `--bl`, do **not** mix HM-only exhaustiveness with a shallow list-only
coverage pass. One coverage story owns Core matches.

HM-only mode: reject surface BL (D16); skip bounds pass; use existing HM
exhaustiveness.

### 2.2 One annotation slot (no dual hm/bl fields)

Binder anns remain a single `Option` type slot (Core as today).

| How the slot is filled | Content after Infer | Bounds meaning |
|------------------------|---------------------|----------------|
| User wrote `BL …` / `BL _ …` | **Preserved** BL | Demand / interface |
| User wrote bare `List` | `List` | No length demand |
| User wrote nothing; Infer filled | HM-only `List` / scheme | No length demand |

Discrimination: **presence of `BL` in the ann** ⇒ bounds ascription; else origin
synth only. No parallel sidecar spine to desync.

`erase` / bounds-erasure is a **function** used by Infer when comparing/unifying
types — **not** a pipeline step that mutates the AST to strip BL.

### 2.3 What `List t` means after HM (non-ascription)

Infer-produced or bare `List t` is **not** “user hole ascription,” and is **not**
“recover the two BLs that unified” (we keep no unify provenance).

```text
List t  ⇒  type shape only
           synth lo/hi from the term + env + demands
           then write BL lo hi t back onto the elaborated AST
```

Unifying two BLs under HM yields a List-spine *solution type*; intervals are
recovered by synthesizing the **term** that connected them (e.g. `if`/`match`
join), not by replaying the unifier.

User `BL _ _` ascriptions are a different mechanism (pin + push interface) and
are irrelevant to the pure-`List` case because those anns were never turned into
`List`.

### 2.4 Binder discipline

At each binder during bounds elab:

**Ascribed (`BL` present)**

1. Synth/check RHS under current bounds env.  
2. Meet ascription (solid Sub or pin holes).  
3. Push **ascribed / pinned interface** β into env (may be wider than witness).  
4. Write that interface onto the binder ann in `Core_BL`.  
5. Pack / R3 residuals as today at escape.

**Not ascribed (`List` / empty filled by Infer)**

1. Synth RHS from origins (Nil/Cons/app/var/join/…).  
2. Pack/generalise free interval vars if needed.  
3. Push **synth/packed** β.  
4. Write resulting `BL` over the `List` placeholder on the AST.

### 2.5 Demand peel

Bidirectional checking under an expected bounds type (demand):

```text
check (λ xs. e)  against  (βd → βc)
  ⇒  env, xs ↦ βd
  ⇒  check e against βc
```

App is the dual: synth function as arrow, check argument against domain (Sub /
meet), result is codomain. Same skeleton as HM bidirectional rules; intervals
add Sub, not a second unifier.

### 2.6 Coverage

After (or as the closing phase of) bounds elaboration, every match scrutinee has
a β (or the program already failed). Run **BoundAwareCovers**:

- List: wildcard / Nil+Cons / Nil-only if empty / Cons-only if nonempty  
- Non-list ADTs: ctor exhaustiveness + arity (subsumes HM coverage under `--bl`)

Prefer recording obligations during the synth walk and discharging once, rather
than a second interpreter that rebuilds `bctx` (see elaborator deletion memo).

---

## 3. Blast radius

### 3.1 Core — moderate, localized

Today `Ty` has no intervals (`prim | arrow | bvar | fvar | customTy`). Lists are
`customTy "List" [α]`.

**Required:** represent bounded lists in Core types, e.g.

```text
Ty.list (lo hi : Count) (elem : Ty)   -- or equivalent
```

plus surface/Core agreement on bare `List` vs `BL`. Count may live in Core or be
imported from a small shared kernel module (avoid pulling Z3 into Core).

Touches (mechanical, wide fan-out of `match` on `Ty`):

- `Ty` freeVars / subst / open / close / LC / pretty  
- anything that assumes “only five Ty ctors”

Does **not** require changing evaluator semantics (runtime ignores counts).

**Expr:** keep single ann slots; no second field. Elaboration hygiene is on
Infer rewrites, not a new Expr shape.

**Estimate:** small definitional change, **large mechanical** `Ty` case-split
updates; proof surface in Core grows with each new ctor.

### 3.2 InferW — small *policy*, non-trivial *hygiene*

InferW stays HM-only. Expected changes:

| Change | Nature |
|--------|--------|
| Unify / equality: `BL` ~ `List` ~ `BL` on spine; result List-spine for solutions | Local clauses + subst |
| Do not solve or invent `lo`/`hi` | Policy |
| Fill empty anns with HM-only types | Policy (likely already List-shaped) |
| **Never** rewrite user `BL` ann to `List` | Invariant on elab rebuilds |
| Copy anns through every `let`/`λ`/`letRec` reconstruction | Hygiene audit |

What InferW must **not** gain: Sub on intervals, join/meet of bounds, Z3,
BoundCovers, residual pack.

**Estimate:** not a rewrite of TypeOfElabHM. Worst cost is finding every place
that rebuilds binders or normalizes annotations. No need for Path correspondence
if hygiene holds.

### 3.3 Lowering / surface

- Lower must **preserve** BL into Core types/anns (stop destructive erase-before-lower).  
- **Park head-binder sugar** until `_` holes are first-class in annotations
  (agreed temporary simplification).  
- D16: HM mode still rejects BL at the surface/program gate.

### 3.4 Bounds layer — scrap packaging, keep kernel judgments

#### Scrap or replace (pipeline packaging)

| Piece | Action |
|-------|--------|
| Destructive `eraseProgram` as the product path | Remove from Live/`--bl` path |
| Name-keyed sidecar / `ErasedProgram` binder ann map | Remove as authority |
| `ProgramBoundsAnns.ofLower` | Remove |
| Dual walk `checkProgramAnns` + `checkProgramMatches` as two authorities | Replace with one bounds elab + coverage discharge |
| λ `.fvar 0` coverage stub / List-let D24 coverage-only fallback | Delete with Matches authority |
| Report paths that zip erase names vs Core by hope | Rebuild from bounds-elaborated anns |

#### Keep / rehome (semantics)

| Piece | Action |
|-------|--------|
| `Count`, constraints, `DemandOK`, oracle bridge | Keep (Kernel/Oracle) |
| `Sub`, `HasBounds`, `CheckBounds`, `BoundCovers` (Props) | Keep; retarget to Core-with-BL |
| Synth rules (Nil/Cons/app/λ/let/match join, D24, R3 pack) | Rewrite drivers for new AST; reuse ideas |
| Escape / Commit uniqueOnly | Keep policy |
| Z3 collapse work | Orthogonal |

**Verdict:** yes — scrap the **erase/repack/ofLower/dual-walk** machinery as the
product architecture. Do **not** scrap the arithmetic kernel or the declarative
bounds judgments wholesale; rewire them to bounds-preserving Core.

Rough size today: Erase+Pipeline+large parts of Check/Report are packaging;
Synth/Typing/Kernel/Escape are the reusable center (with edits).

### 3.5 Live / EditorSupport / demos

- Pipeline order: lower → infer → bounds elab → BoundAwareCovers → eval.  
- Hover/report: prefer types on the fully bounds-elaborated Core term.  
- E2E: grow acceptance programs (including nested `: BL`) as Phases 1–3 land.

### Acceptance cases to track (thin G0 list)

Write dedicated small programs over time (not only the dirty showcase):

| # | Intent | Notes |
|---|--------|--------|
| A1 | Nested `let ys : BL … =` inside λ | **New** — fails packaging today |
| A2 | Top-level solid BL ascription | Regression |
| A3 | Infer-filled bare List gets lengths from term | Write-back story |
| A4 | Nil-only / Cons-only under exact empty/nonempty | Coverage |
| A5 | D22: bare List does not invent intervals without origin | |
| A6 | D24: unascribed list λ generalises | |
| A7 | R3 unique / multi-model canaries | Existing scratch files |

---

## 4. Theorem targets (faithfulness of double elaboration)

Goal: say something precise about surface → semi-elaborated Core → fully
bounds-elaborated Core without boiling the ocean. Prefer a **tower of projections**.

### 4.1 Projections

```text
eraseBounds : Ty → Ty          -- drop intervals; BL lo hi α ↦ List α
eraseExpr   : Expr → Expr      -- map binder anns + tyArgs through eraseBounds
eraseCtx    : Ctx → Ctx        -- erase env schemes
```

Implemented on Core as `Ty.eraseBounds` / `Expr.eraseBounds` / `Ctx.eraseBounds`.
**Pipeline must not run erase as packaging.** Residual theorems only.

### 4.1.1 Path R formalization (locked 2026-08-11)

**Path R (chosen):** pure declarative `TypeOf*` stays **structural HM** (structural
`Option.Pins`; no BL ≡ List inside TypeOf). Infer is bounds-blind and may keep BL
on the elaboratum. Soundness/completeness bridges are **residual**:

```text
Infer … eOut, τ
  ⇒  TypeOfElabHM (S·ctx).eraseBounds  (eOut[S]).eraseBounds  (erase τ)

CompleteAt / complete': hyp is TypeOfHM (S₀·ctx).eraseBounds e.eraseBounds τ₀
```

**Path B (rejected for TypeOf):** make TypeOf itself bounds-blind (weak Pins).
Simpler Infer↔TypeOf slogans; contaminates the golden HM judgment with BL-world.

**Ann preservation ≠ residual TypeOf.** Separate relation (`UserAnnsCopied` /
`Infer.preservesAnns`) on the real elaboratum. Note: Infer `letRec` elaboratum is
`Expr.letRecElab` (Λ-outside nest), not bare `.letRec`.

**Quotients:** use `AgreesHM` / erase predicates (moral quotient). No Lean `Quot Ty`.

Details, proof order, greps: `next-agent-brief-path-r-dual-stack.md`.

### 4.2 HM faithfulness (first elaboration)

**Prop (Path R residual soundness)** — primary Infer faithfulness theorem:

```text
Infer Φ ctx e ↝ eOut, S, τ
  ⇒  TypeOfElabHM (S.onCtx ctx).eraseBounds
        (eOut.substTyFvars S).eraseBounds
        (Ty.eraseBounds τ)
```

**Prop: User BL not destroyed** (ann preservation; independent of TypeOf residual):

```text
Infer … e ↝ eOut
  ⇒  UserAnnsCopied e eOut
  -- λ / annotated let: same ascription option; letRec: same anns inside letRecElab;
  -- unannotated let may gain genScheme; let RHS may be closeTyVars∘subst
```

**Prop (sketch): Erased elaboratum relates to pure-HM Infer of erased program**

```text
Infer (with BL) e = eOut
  →  Infer (HM) (erase e) related to erase eOut
```

Connects dual-stack to the pure HM path (recovery of today’s erase-then-infer).
Optional after residual soundness.

### 4.3 Bounds faithfulness (second elaboration)

**Prop (sketch): Ascription soundness**

```text
BoundsElab e_semi = some e_full
  →  for each binder with user BL ann β_ann in e_full,
       CheckBounds / Sub holds for the RHS against β_ann
```

**Prop (sketch): Agrees**

```text
anns on e_full satisfy Agrees β (eraseBounds β)   -- shape matches HM List spine
```

**Prop (sketch): Origin discipline (D22)**

```text
no bare List position is given a concrete interval except via
  Nil/Cons/app/join/env/D24 param origin/user BL
```

Hard to state fully; start with: “bounds elab never invents intervals at
Infer-filled List without a synth derivation.”

### 4.4 Coverage

```text
BoundsElab e_semi = some e_full
  →  BoundAwareCovers e_full
  →  (semantic) every value inhabiting scrutinee β matches some branch
```

Oracle side conditions use `ForallProblem.Valid` (meaning), with `checkValid`
soundness as bridge — prefer Valid in Props over raw Z3 enums (existing cleanup
desire).

### 4.5 Surface relation (longer horizon)

Full “surface bounds syntax ≡ Core_BL” needs lower correctness + double elab:

```text
SurfaceWT / surface bounds intent
  →  lower preserves BL anns
  →  Infer preserves them
  →  BoundsElab checks them
  →  Core_BL anns are the checked interfaces
```

MVP theorems: **§4.2 preservation + erased HM simulation**, then **§4.3
ascription soundness**, then coverage. Full observational equivalence with
surface is post-MVP.

### 4.6 What not to claim early

- Completeness of bounds synth (principal intervals everywhere).  
- Full executable ↔ declarative HasBounds correspondence in one PR.  
- Path-based surface↔Core bijection (explicitly rejected in favour of
  preservation-through-elab).

---

## 5. Explicit non-solutions (locked for this design)

- Path ↔ Path reattachment calculus for all of lower/Infer (unless preservation
  proves impossible).  
- Join/meet/Sub inside InferW unify.  
- Unify provenance (“List remembers two source BLs”).  
- Treating bare `List` as user `BL _ _` ascription (different packing/interface).  
- Dual `hm` + `bl?` fields that must stay in sync.  
- Destructive erase-before-lower as product path.  
- Under `--bl`, HM exhaustiveness + shallow BoundCovers sandwich.  
- Head-binder sugar as a dependency of this project (park it).

---

## 6. Suggested work order

```text
P0  Spec freeze (this memo) + G0 acceptance list including nested BL let
P1  Core.Ty (+ Count placement) + mechanical Ty API; lower preserves BL
P2  InferW: bounds-blind unify; ann preservation audit; fill-empty = HM only
P3  Bounds elab driver on Core_HM → Core_BL (reuse Kernel/Sub/synth ideas)
P4  BoundAwareCovers on Core_BL; delete Matches dual authority
P5  Live/Editor/Report/e2e; remove Erase/ofLower product path
P6  Theorems: ann preservation; erased HM simulation; ascription soundness
```

P3–P4 absorb the spirit of `design-memo-bounds-elaborator.md` (one authority)
without rebuilding ofLower.

**No implementation without explicit user request** (repo convention).

---

## 7. One-paragraph handoff

Keep dual-stack *meaning*: Infer is bounds-blind HM; bounds is a second
elaboration that solves intervals and coverage. Change *packaging*: stop
erasing BL before lower; carry BL only in real Core anns; Infer unifies List
spines and must preserve user BL while filling empty slots with List; bounds
elaboration rewrites `List` placeholders to synthesized `BL` and checks user
ascriptions as demands; then BoundAwareCovers runs on that fully
bounds-elaborated term. Scrap erase/sidecar/ofLower/dual-walk packaging; keep
Count/Sub/HasBounds/oracle ideas. Theorems start from ann preservation and
“erased Infer simulates pure HM,” then ascription soundness and coverage.
Park head binders until holes are real.

---

## 8. Locked representation choices (not open)

These follow from the architecture above; they are not menu options.

1. **`Ty.bl lo hi elem`** — intervals live **in** `Ty`, same as surface `BL`.
   No parallel count payload beside `customTy "List"`. Bare HM list stays
   `customTy "List" [α]` (no length demand) until bounds elab writes a `bl`.

2. **`Count` without Z3 on the Core import path** — Core may depend on count
   syntax/eval, never on Oracle/Z3. Split or thin the kernel if needed so
   `import FHM.Core` stays Z3-free.

3. **Scheme shape** — surface `PolyTy` carries **two** telescopes: type foralls
   (HM) and bounds/Nat foralls (bounds only). Lower/Infer thread the structure;
   InferW **ignores** bounds/Nat binders entirely (does not open, unify, or
   generalise them). Bounds elaboration owns Nat telescopes, inst, and pack.
   Same dual-stack rule as mono: one AST, two consumers.

4. **Bounds elab rewrites the AST** — like Infer, produce a fully
   bounds-elaborated Core term with BL written onto annotations/types. No
   parallel side map as the product truth (temps during a walk are fine).
