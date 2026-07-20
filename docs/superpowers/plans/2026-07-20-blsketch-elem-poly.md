# BLSketch element types + type polymorphism Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Give bounded lists an element type (`BL lo hi α`) and prenex schemes that bind both count variables (`Nat`) and type variables (`Type`), with explicit `@`-instantiation for both — enough for a real `nil` scheme and element-accurate `cons`/`head`/`tail`.

**Architecture:** Keep today’s bounds/Z3 layer unchanged. Extend `Ty` with type variables and `BL … elem`; replace count-only `BScheme` with a mixed binder telescope; instantiate via one `List SchemeArg` spine on `Expr.var`. No type inference, no elem-subtyping, no `letRec` in this plan.

**Tech Stack:** Lean 4 (`v4.26.0`), existing `FHMZ3` / `FHM.BLSketch` / `FHM.BLSketch.Pretty`, Z3 oracles as-is, demos in `scratch/blsketch_synth_demos.lean`.

## Global Constraints

- Lean toolchain stays `leanprover/lean4:v4.26.0`.
- Do not reopen locked BLSketch decisions in `briefs/next-agent-brief-blsketch-z3.md` except where this plan explicitly extends schemes / `BL`.
- **No type inference / generalization** in v1 — every type scheme use is explicit `@`.
- **No element subtyping** — `Sub` on `BL` requires definitional equality of elements.
- **No `letRec`** — recursion stays a separate follow-up.
- Z3 / `Count` / `DemandOK` / match-`Δ` refinement stay as today; type structure does not enter the oracle.
- Prefer LSP diagnostics during edits; `lake build FHMZ3` + `lake env lean scratch/blsketch_synth_demos.lean` at task boundaries (needs `z3` on `PATH`).
- Follow existing proof style in `FHM/BLSketch.lean`; no new opaque axioms beyond the existing oracle soundness axioms.
- Pretty scheme binders use braces to distinguish from term λ: `∀ {a b : Nat, α β : Type}. …`.

---

## File structure

| File | Responsibility |
|------|----------------|
| `FHM/BLSketch.lean` | `Ty` / `AnnoTy` / `BScheme` / `TypeOf` / `synth` / `Check` / examples |
| `FHM/BLSketch/Pretty.lean` | Print `BL lo hi α`, mixed `∀ {…}`, `@` spine for counts and types |
| `scratch/blsketch_synth_demos.lean` | Migrate demos; expand `Demo.Stdlib` with typed nil/cons/head/tail |
| `briefs/next-agent-brief-blsketch-z3.md` | One-paragraph pointer to this plan + new locked decisions (end of work) |
| `docs/superpowers/specs/2026-07-20-blsketch-elem-poly-design.md` | Short design memo (written with this plan) |

**Testing style:** Inline `#guard` / `example` / `#eval` in modules and demos (same as rest of FHM). No separate test target.

---

## Design locks (from session)

1. **`Ty.bl lo hi elem`** with `elem : Ty` (allows nested `BL` later; v1 demos use base `Unit`).
2. **Type variables:** rigid de Bruijn in scheme bodies, parallel to count binders — `Ty.tbind i` (name TBD in Task 1; must be distinct from `Count.var`).
3. **Mixed schemes:**
   ```lean
   inductive SchemeBinder where
     | count  -- sorts as Nat in pretty
     | type   -- sorts as Type in pretty
   structure BScheme where
     binders : List SchemeBinder
     body : Ty
   ```
   WF: count indices / type indices separately in scope (`0 .. countBinders-1`, `0 .. typeBinders-1`), or a single indexed telescope — pick one in Task 1 and stick to it. Prefer **separate index spaces** (counts `a,b,…` / types `α,β,…`) matching Pretty letters already used.
4. **Instantiation args:**
   ```lean
   inductive SchemeArg where
     | count : Count → SchemeArg
     | ty : Ty → SchemeArg
   ```
   `Expr.var idx (args : List SchemeArg)`. Length and binder-kind must match the scheme telescope.
5. **Pretty:** `∀ {a b : Nat, α β : Type}. body`; apps `f @2 @Unit @3` (one `@` per binder, kind-directed).
6. **`nil`:** library scheme `∀ {α : Type}. BL 0 0 α`, not a synthesizing nullary ctor. Keep `Expr.nil` only if check/list-sugar still needs it; otherwise migrate demos to `nil @α` and treat `.nil` as sugar or delete from `TypeOf`/`synth`.
7. **`Sub` for `BL`:** same bound goals as today + `elem = elem'` (no subtype on elements).

---

### Task 1: Grammar — `Ty.bl` gains `elem`, add type binders

**Files:**
- Modify: `FHM/BLSketch.lean` (`Ty`, `AnnoTy`, `Ty.size` / `obsBounds` / `inferVars` / `Ground` / `DemandOK` / `BinderRigid`, module docstring)
- Modify: `FHM/BLSketch/Pretty.lean` (print `BL lo hi τ`)
- Create: `docs/superpowers/specs/2026-07-20-blsketch-elem-poly-design.md` (if not already present)

**Interfaces:**
- Consumes: current `Ty.bl lo hi`
- Produces: `Ty.bl lo hi elem`, `Ty.tbind (i : Nat)`, `AnnoTy.bl lo hi elemAnn`, updated Pretty

- [ ] **Step 1: Record the design memo**

Ensure `docs/superpowers/specs/2026-07-20-blsketch-elem-poly-design.md` exists and matches the locks above (short; no implementation).

- [ ] **Step 2: Extend `Ty` / `AnnoTy`**

```lean
inductive Ty where
  | unit
  | tbind (i : Nat)   -- rigid type scheme binder
  | arrow (dom cod : Ty)
  | bl (lo hi : Count) (elem : Ty)
```

Thread `elem` through `AnnoTy`, `ofTy`, `fillHoles`, `Ground`/`fold` (fold only counts; elem structure preserved), `DemandOK`, `BinderRigid` (counts + type binds), `obsBounds` (still only counts).

- [ ] **Step 3: Fix the mechanical fallout**

Update every `Ty.bl` pattern in `BLSketch.lean` so the file elaborates. Temporarily hardwire `elem := .unit` at former BL sites (nil/cons/match/examples) so behaviour matches today. Do **not** change `BScheme` yet.

- [ ] **Step 4: Pretty + sanity**

`BL 0 5 Unit`, `BL a b α`. Rebuild:

```bash
lake build FHMZ3
lake env lean scratch/blsketch_synth_demos.lean
```

Expected: demos still pass with implicit `Unit` elements.

- [ ] **Step 5: Commit**

```bash
git add FHM/BLSketch.lean FHM/BLSketch/Pretty.lean docs/superpowers/specs/2026-07-20-blsketch-elem-poly-design.md
git commit -m "feat(bl): BL lo hi carries element type (Unit-hardwired)"
```

---

### Task 2: Mixed `BScheme` + `SchemeArg` instantiation

**Files:**
- Modify: `FHM/BLSketch.lean` (`BScheme`, `Subst`, `InstantiatesTo`, `instantiate?`, `Expr.var`, `TypeOf.varScheme`, `synth` var case, examples)
- Modify: `FHM/BLSketch/Pretty.lean` (scheme telescope + `@` spine)

**Interfaces:**
- Consumes: Task 1 `Ty`
- Produces: `SchemeBinder`, `SchemeArg`, `BScheme.binders : List SchemeBinder`, kind-correct `InstantiatesTo` / `instantiate?`

- [ ] **Step 1: Replace count-only schemes**

```lean
inductive SchemeBinder where
  | count | type
  deriving DecidableEq, Repr

inductive SchemeArg where
  | count : Count → SchemeArg
  | ty : Ty → SchemeArg
  deriving DecidableEq, Repr

structure BScheme where
  binders : List SchemeBinder
  body : Ty
```

Define `BScheme.countBinders` / `typeBinders` as counts of each kind. WF: body only mentions count rigids `< countBinders` and `tbind i` with `i < typeBinders`.

- [ ] **Step 2: Dual substitution**

Extend / replace `Ty.Subst` so instantiation walks the binder list: each `.count` arg substitutes the next count binder; each `.ty` arg substitutes the next type binder. Reject kind mismatches in `instantiate?`.

- [ ] **Step 3: Wire `Expr.var`**

```lean
| var (idx : Nat) (args : List SchemeArg)
```

Update Pretty: `x @2 @Unit @6`. Scheme pretty:

`∀ {a b : Nat, α : Type}. …`

(group binders by kind in braces as decided).

- [ ] **Step 4: Migrate existing schemes**

`idScheme`, `flatMapScheme`, demo schemes → `binders := [.count, …]` only. All call sites use `.count (.lit n)` wrappers.

- [ ] **Step 5: Build + demos + commit**

```bash
lake build FHMZ3
lake env lean scratch/blsketch_synth_demos.lean
git add FHM/BLSketch.lean FHM/BLSketch/Pretty.lean scratch/blsketch_synth_demos.lean
git commit -m "feat(bl): mixed Nat/Type scheme binders with kinded @"
```

---

### Task 3: Element-accurate `cons` / match; `nil` as a scheme

**Files:**
- Modify: `FHM/BLSketch.lean` (`TypeOf.nil`/`cons`/`match*`, `consCtx`, `synth`/`check`, library examples)
- Modify: `scratch/blsketch_synth_demos.lean` (`Demo.Stdlib`)

**Interfaces:**
- Consumes: Task 2 schemes
- Produces: `nilScheme`, `consScheme` with type binders; match head typed as `elem`

- [ ] **Step 1: Fix `cons` / `consCtx`**

```lean
-- cons: head : elem, tail : BL lo hi elem ⊢ cons : BL (lo+1) (hi+1) elem
-- consCtx: mono elem :: mono (BL (pred lo) (pred hi) elem) :: ctx
```

`Sub.bl` requires `elem = elem'`.

- [ ] **Step 2: `nil` scheme; stop synthesizing bare `.nil`**

```lean
def nilScheme : BScheme where
  binders := [.type]
  body := .bl (.lit 0) (.lit 0) (.tbind 0)
```

Remove or gate `TypeOf.nil` / `synth .nil` so empty lists are `nil @Unit` (or check against a known `BL 0 0 α`). Update list-building demos.

- [ ] **Step 3: Stdlib bodies**

In `Demo.Stdlib`, redefine:

- `singleton : ∀ {α}. α → BL 1 1 α`
- `cons : ∀ {a b : Nat, α}. α → BL a b α → BL (a+1) (b+1) α`
- `head : ∀ {a b : Nat, α}. BL (a+1) b α → α`
- `tail : ∀ {a b : Nat, α}. BL (a+1) (b+1) α → BL a b α`

Show a **negative** demo: consing `Unit` into a `BL _ _` demand that expects a different element fails (once a second base type exists — see Task 4 — or use `tbind` mismatch via annotation).

- [ ] **Step 4: Prove / repair `synth_sound` for touched rules**

Fix broken cases only; don’t expand proof scope.

- [ ] **Step 5: Build + demos + commit**

```bash
lake build FHMZ3
lake env lean scratch/blsketch_synth_demos.lean
git commit -m "feat(bl): element-accurate cons/match; nil as type scheme"
```

---

### Task 4: Second base type + negative demos (optional but recommended)

**Files:**
- Modify: `FHM/BLSketch.lean` (add `Ty.bool` or `Ty.int` — pick one)
- Modify: demos / Pretty

**Interfaces:**
- Consumes: Task 3
- Produces: one extra nullary base type; demo that `cons` rejects element mismatch

- [ ] **Step 1: Add `Ty.bool` (or `int`) + `Expr` intro if needed**

Minimal: `Ty.bool` + `Expr.tt` / `Expr.ff` (or a single `Expr.boolLit`). Enough to write `nil @Bool` and fail `cons unit (nil @Bool)`.

- [ ] **Step 2: Demos**

Positive: `cons @0 @0 @Bool tt (nil @Bool)`.  
Negative: `showCheck` / `showSynth` failure for `cons unit (nil @Bool)`.

- [ ] **Step 3: Commit**

```bash
git commit -m "feat(bl): Bool base type for element-mismatch demos"
```

---

### Task 5: Docs handoff

**Files:**
- Modify: `briefs/next-agent-brief-blsketch-z3.md` (locked decisions + pointer)
- Modify: design memo if anything drifted during implementation

- [ ] **Step 1: Update brief**

Add locked rows: element type on `BL`; mixed schemes; explicit `@` for Nat/Type; no elem-subtyping; no type inference; `nil` is a scheme.

- [ ] **Step 2: Final verification**

```bash
lake build FHMZ3
lake env lean scratch/blsketch_synth_demos.lean
lake env lean scratch/blsketch_z3_demos.lean
```

- [ ] **Step 3: Commit**

```bash
git commit -m "docs(bl): lock elem/type-poly decisions in BLSketch brief"
```

---

## Out of scope (explicit follow-ups)

| Item | Why deferred |
|------|----------------|
| Type inference / let-generalization | Mycroft + HM engineering; v1 is explicit `@` |
| Element subtyping | Not needed for mismatch errors |
| `letRec` / recursive map/filter/flatMap bodies | Separate plan |
| Surface parser / FHM Core integration | BLSketch stays a didactic spine |
| Nested scheme LN / impredicative types | Stay prenex story A |

---

## Self-review

1. **Spec coverage:** Element on `BL`, mixed schemes, pretty braces, kinded `@`, nil scheme, cons/match elem accuracy, demos, brief update — all have tasks. Recursion explicitly out of scope.
2. **Placeholders:** None intentional; Task 1 allows naming `tbind` vs `tvar` at implement time.
3. **Type consistency:** `SchemeArg` / `SchemeBinder` / `BScheme.binders : List SchemeBinder` used uniformly from Task 2 onward.
