# Design memo: bounds-preserving double elaboration

**Status:** Agreed direction (2026-08-04). Supersedes the erase → name-sidecar →
`ofLower` → dual Bounds walk packaging for product architecture.  
**Does not** reopen dual-stack *semantics* (HM owns shape; bounds owns intervals).  
**Does** change *how* bounds ascriptions and elaborated types are carried.

**Related (historical / still useful pieces):**

- `design-memo-bounds-layer-on-core.md` — locked product rules (D22/D24/R3, dual stack intent)
- `design-memo-bounds-elaborator.md` — deletion-first coverage (one authority); still relevant *after* reattachment is fixed
- `next-agent-brief-bounds-elaborator-architecture.md` — diagnosis of dual Matches walk

**This doc’s job:** record the agreed pipeline, Core/Infer blast radius, what to
scrap vs keep in Bounds, and theorem targets for double elaboration.

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
  │  lower — preserve BL in Core types / binder anns
  │  (temporarily: no head-binder sugar until holes are first-class)
  ▼
Core₀  (BL may appear only in user ascriptions; else bare / open)
  │
  │  InferW — HM only
  │  • unify / equality ignore intervals (BL ~ List on spine)
  │  • HM solutions are List-spine (no lo/hi choice)
  │  • empty ann slots filled with HM-only types (List / schemes)
  │  • user BL ascriptions never overwritten with List
  │  • every rebuild of let / λ / letRec copies anns through
  ▼
Core_HM  (“semi-elaborated”: HM-complete, bounds not solved)
  │
  │  Bounds elaboration (synth + check)
  │  • user BL ann → demand; check Sub / pin holes; keep interface
  │  • bare List / Infer-filled List → no length demand;
  │      synth β from term + bctx + outer demands; write BL back
  │  • binder pack / R3 at escape
  │  • demand peel on λ under arrow demand
  ▼
Core_BL  (“fully elaborated” for types: lists carry intervals where known)
  │
  │  BoundAwareCovers (bounds-aware exhaustiveness only under --bl)
  ▼
accept / reject
  │
  ▼
eval on HM spine (intervals ignored at runtime)
```

Under `--bl`, **do not** sandwich HM exhaustiveness with a partial BoundCovers.
One coverage story owns Core matches (list intervals + ordinary ADT ctors).

HM-only mode: reject surface BL (D16); no bounds elab; existing HM exhaustiveness.

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
| Report paths that zip erase names vs Core by hope | Rebuild from `Core_BL` anns |

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
- Hover/report: prefer anns on `Core_BL`.  
- E2E gate: freeze G0-style cases including nested `: BL` ascriptions once supported.

---

## 4. Theorem targets (faithfulness of double elaboration)

Goal: say something precise about surface → Core_HM → Core_BL without boiling the
ocean. Prefer a **tower of projections**.

### 4.1 Projections

```text
eraseBounds : Ty → Ty          -- drop intervals; BL lo hi α ↦ List α
eraseExpr   : Expr → Expr      -- map anns through eraseBounds (optional)
```

### 4.2 HM faithfulness (first elaboration)

**Prop (sketch): Infer sees only erased shape**

```text
TypeOfElabHM Γ e τ
  →  (user anns in e may contain BL)
  →  the judgment only depends on eraseBounds of those anns
```

More operationally: if `e₀` and `e₁` agree after `eraseBounds` on all anns and
term structure, Infer accepts one iff the other (for HM), with erased results.

**Prop (sketch): User BL not destroyed**

```text
Infer Γ e = some eOut
  →  every user BL ascription site in e has a corresponding site in eOut
     with the same bounds ann (up to type-var subst Infer already applies
     to the *type* spine, not inventing lo/hi)
```

This is the formal content of “ann preservation hygiene.”

**Prop (sketch): Erased elaboratum is an HM elaboratum of the erased program**

```text
Infer (with BL) e = eOut
  →  Infer (HM) (erase e) related to erase eOut
```

Connects dual-stack to the pure HM path (recovery of today’s erase-then-infer).

### 4.3 Bounds faithfulness (second elaboration)

**Prop (sketch): Ascription soundness**

```text
BoundsElab e_HM = some e_BL
  →  for each binder with user BL ann β_ann in e_BL,
       CheckBounds / Sub holds for the RHS against β_ann
```

**Prop (sketch): Agrees**

```text
anns/βs on e_BL satisfy Agrees β (eraseBounds β)   -- shape match HM
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
BoundsElab e_HM = some e_BL
  →  BoundAwareCovers e_BL
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

1. **`Ty.list lo hi elem`** — intervals live **in** `Ty`, same as surface `BL`.
   No parallel count payload beside `customTy "List"`. That would reintroduce
   dual representation and desync. Bare HM list shape is `list` with no solid
   interval obligation after Infer (or a dedicated “unbounded/erased” form only
   if we need a constructor for “List with no counts yet”; prefer one ctor and
   treat Infer-filled list anns as shape-only until bounds elab writes lo/hi).

2. **`Count` without Z3 on the Core import path** — Core may depend on count
   syntax/eval, never on Oracle/Z3. Split or thin the kernel if needed so
   `import FHM.Core` stays Z3-free.

3. **Scheme shape** — surface `PolyTy` carries **two** telescopes: type foralls
   (HM) and bounds/Nat foralls (bounds only). Lower/Infer thread the structure;
   InferW **ignores** bounds/Nat binders entirely (does not open, unify, or
   generalise them). Bounds elaboration owns Nat telescopes, inst, and pack.
   Same dual-stack rule as mono: one AST, two consumers.

4. **Bounds elab rewrites the AST** — like Infer, produce `Core_BL` with BL
   written onto anns/types. No parallel β-map as the product truth (internal
   temps OK during a walk).
