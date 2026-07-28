# Next-agent brief: type holes (`_`) and partial annotations in FHM

**Status:** research complete; not implemented  
**Date:** 2026-07-27 (revised 2026-07-28: return-pin encoding; `{a}`/structural-`_` clarified)  
**Motivation:** head-binder UX (`let f (a : Int) b = …`) and desire for blanks in signatures (`Int → _ → Int`); eventual UX parity with bound holes `BL _ _ t`  
**Related:** [`next-agent-brief-remove-unique-from-typeof.md`](next-agent-brief-remove-unique-from-typeof.md) (orthogonal; lives in blt, not yet copied); BLSketch `AnnoTy` already has count holes

---

## One-liner

> Binder-level partiality already exists (`Option Ty` on λ / nested head-binder λs). Missing return with incomplete domains can be kept via an **inner annotated let** pin — not by dropping `: ret`. Structural holes inside a monotype/scheme (`Int → _ → Int`, `List _`) and **named `{a}` without a full scheme** are **not** freebies from Infer’s Φ — they need a real scheme binder / AnnoTy.Elab story. Ship the strained head-binder lowering first; treat written `_` as a deliberate follow-on.

---

## Verdict on “fairly straightforward”

| Claim | Reality |
|-------|---------|
| We already synthesize missing types | **True** |
| Partial ann already drives synthesis | **True for binder-level `Option` / nested λ** |
| Head binders need Core type holes | **Mostly false** for mono params + return (see return-pin encoding) |
| `{a}` without full residual is the same | **False** — needs a scheme binder; incomplete body ⇒ type-level hole |
| Adding `_` in signatures is a local InferW tweak | **False** if Core `Pins` + rigid `K` stay as-is |
| BL bound holes need HM holes first | **False** — independent |

“Straightforward” is right for **surface/head-binder UX that lowers to existing Core binder `Option`s (+ return pin)**.  
It is **wrong** for **structural holes in Core schemes with green `Infer.principal` / `sourceSound`**, and for **`{a}` used in anns without a finalized `∀a.…` scheme**.

**Design tension:** head binders without full type holes are a half-feature. Elm avoids this by putting annotations on their own line (all-or-nothing). Partial head binders + return are Core-expressible; tying them to named typarams or written holey schemes is not, without PR3.

---

## Current model (what you already have)

### Core (`FHM/Core.lean`)

| Form | Annotation | `none` means |
|------|------------|--------------|
| `lambda` | `Option Ty` | invent param monotype |
| `letIn` | `Option PolyTy` | genScheme on RHS type |
| `letRec` | `List (Option PolyTy)` | mono-rec vs poly-rec mix |

`Core.Ty` has **no hole ctor** (`prim | arrow | bvar | fvar | customTy`).  
**No term-level ascription** — only binder anns.

### `Option.Pins` (`Core.lean` ~2428)

```lean
def Option.Pins (ann : Option α) (x : α) : Prop :=
  ∀ a, ann = some a → x = a
```

- `none` → vacuous (infer invents freely).  
- `some a` → invented choice **equals `a` exactly** — no partial structure.

Used by `TypeOfHM` / `TypeOfElabHM` for λ and let.

### Infer (`InferW.lean`)

```lean
inductive LamSeed (Φ : Nat) : Option Ty → Ty → Nat → Prop
  | none : LamSeed Φ none (.fvar Φ) (Φ + 1)
  | some (T : Ty) : T.IsLC → LamSeed Φ (some T) T Φ
```

- Unannotated → **flexible** fvar at Φ.  
- Annotated → monotype fixed; free fvars of `T` treated as **rigid** (must live in ambient `K` for `sourceSound` / completeness).  
- Same Φ mechanism, **opposite policy** for free fvars in annotations (scoped tyvars ≠ holes).

### Head binders already partially work

Surface (`SurfaceLang.lean`):

```lean
params : List (ValName × Option Ty)
ann    : Option PolyTy
```

Parse accepts bare params and `(name : ty)`.

Lowering (`SurfaceBridge.lean` ~3488–3538):

- `finalizeAnn` packs params+return into a Core scheme when residual is fully known.  
- `paramsToArrows`: **any** `none` param domain → `none` (cannot pack).  
- `wrapCoreParams`: nested Core `λ` with per-param `Option Ty`.  
- `letAnnTyPrefix`: tyParams enter RHS scope **only** when `finalizeAnn` yields a scheme.

**Works today:**

```text
let f (x : Int) = …     -- no return scheme
→ letIn none (lambda (some Int) …)
```

Unannotated params are already **binder-level holes**. Return is inferred + generalized (classic HM let), not monomorphic-only.

**Broken / incomplete today:**

| Program | Problem |
|---------|---------|
| `let f (x : Int) y : Int = …` | `paramsToArrows` fails on bare `y`; fallback leaves scheme = bare `Int` — **wrong packing** |
| `let f {a} (x : a) = …` without `: a` | tyParams not scoped when no finalized scheme |
| `let f : Int → _ → Int = …` | `_` not in type syntax at all |
| Docs `@TODO(partial-head-ann)` | Overstates: mono partial params work; packing fallback is the real bug |

---

## What “type holes” would mean

Two different features — do not conflate:

| Kind | Example | Core encoding today |
|------|---------|---------------------|
| **Binder-level partiality** | `(a : Int) b` / no return ann | `Option Ty` / `Option PolyTy` = `none` |
| **Structural holes** | `Int → _ → Int` inside one type | **Not supported** |

### Binder spine vs type tree (why head binders ≠ written `_`)

Head binders give a **binder spine** whose annotation slots are already `Option`:

```text
f (x : Int) y : Int = body
     │         │    │
     │         │    └─ return pin (inner let) — see below
     │         └─ λ none
     └─ λ (some Int)
```

A written type is a **single tree** with a missing subtree. There is no binder to hang `Option` on:

| Written | Desugar to binder Options? |
|---------|----------------------------|
| `(x : Int) y : Int` | **Yes** — λ / λ / inner let |
| `: Int → _ → Int` on a let whose RHS is already `λλ…` | Maybe (fragile special-case) |
| `List _ → Int`, `Maybe _`, `(_ → Int) → Bool` | **No** — hole inside type structure |

So: head-binder partiality → strained but 100% Core-expressible. Arbitrary `_` in type syntax → no lowering target without AnnoTy/Elab (or restricting `_` to desugarable binder positions = head-binder sugar again).

Structural holes need either:

1. Surface sugar that desugars to binder-level / unannotated let (only when holes line up with binder slots), or  
2. A real hole representation + filling story that does not treat hole fvars as rigid scoped tyvars.

---

## Strained lowering: keep all provided mono anns (no InferW)

**Do not** fix incomplete packing by dropping `: ret`. That loses surface type info.

### Encoding

```text
let f (x : Int) y : Int = body
  ↝  letIn none
       (λ(some Int). λ none.
          letIn (some Int) body (var 0))
```

| Piece | Role |
|-------|------|
| Outer `letIn none` | Classic HM `genScheme` → `∀α. Int → α → Int` |
| `λ(some Int)` | Pins `x` (`LamSeed.some` / `Pins`) |
| `λ none` | Invents flexible fvar for `y` |
| Inner `letIn (some Int)` | Pins/checks return (`letInAnn` + unify) |
| `var 0` | Identity; β-reduces away; param indices in `body` unchanged |

Core has no term ascription; the inner annotated let **is** the ascription encoding. InferW / `Pins` / `sourceSound` / `principal` already cover these forms — **no Core/InferW edits**.

### What this covers

| Surface | Lowering |
|---------|----------|
| Partial/missing param domains | `wrapCoreParams` `Option`s |
| Provided return + incomplete domains | outer `none` + inner return-pin let |
| Provided return + all domains known | keep today’s `finalizeAnn` full pack (unchanged) |
| No return + partial params | outer `none` + wrap only (already works) |

### Hard limit: type-wide skolems `{a}`

Surface `{a}` is a **named scheme binder**. Core only introduces those via

```text
letIn (some ⟨1, body⟩)   -- RHS opened at skolem for a
```

With `letIn none`, Infer generalises from the *inferred* type after the fact. It does **not** put named `a` in scope while checking annotations. Free fvars that already appear in annotations are **rigid** (ambient `K`) — they are *not* generalised. Inventing an fvar for `a`, sticking it in `(x : a)`, and leaving the outer let unannotated makes `a` look like an **escaping skolem**, not `∀a.…`.

The return-pin / nested-`Option`-λ encoding never creates scheme binders. It only fills **value-binder** annotation slots. So:

| Piece | Expressible without holey schemes? |
|-------|--------------------------------------|
| Param domain `Int` / missing | **Yes** — `λ (some Int)` / `λ none` |
| Return `Int` | **Yes** — inner `letIn (some Int)` |
| Typaram `{a}` used in anns | **Only if** a real `∀a.…` scheme exists to open |

Incomplete scheme body that still mentions `a` (`∀a. a → _`, `∀a. a → _ → a`) ⇒ structural hole (PR3), not binder `none`.

Full pack with `{a}` is fine today: `let f {a} (x : a) : a = x` → `∀a. a → a`.

`letAnnTyPrefix` (`SurfaceBridge` ~3546–3551) already encodes this: tyParams extend RHS scope iff `finalizeAnn` yields a scheme.

---

## Why structural holes hit metatheory hard

### Rigid vs flexible fvars

| Role of free fvar in annotation | Policy today |
|---------------------------------|--------------|
| Scoped tyvar from outer `{a}` / scheme | **Rigid** — in `K`; `S` must not bind; `S.onTy T = T` |
| Hole to be filled by inference | **Flexible** — invent at Φ; unify may bind |

Putting holes into Core `some T` as ordinary `fvar`s **without** splitting these roles breaks:

- `Infer.sourceSound` (source free vars ⊆ rigid `K`)  
- `Infer.principal` / `iff_typeable` (closed-world source TypeOfHM)  
- `complete_lambda_ann_aux` (`S₀.onTy T = T`)  
- letInAnn escape / skolem story for partial schemes  

### `Pins` is the wrong declarative notion for holey anns

After inference, the true type is a **filling** of the annotation, not the holey annotation itself.

- Elab path can survive if `eOut.substTyFvars S` fills anns (`Infer.sound`).  
- Source path (`TypeOfHM` of original term) needs something like BLSketch’s `AnnoTy.Elab ann τ` (∃ fill), not `Pins (some holey) τ`.

### `Infer.sound` vs `sourceSound`

| Property | Structural holes as flexible fvars in Core anns |
|----------|--------------------------------------------------|
| `Infer.sound` (elab) | Likely salvageable |
| `Infer.sourceSound` | **Breaks** without redesign |
| `principal` / `iff_typeable` | **Breaks** |

---

## Blast radius

| Scope | Modules | Effort | Metatheory |
|-------|---------|--------|------------|
| **PR1: packing fix + return-pin lowering** | `SurfaceBridge`, tests, docs | **~200–500 LOC** | Lowers/SurfaceWT only; **no InferW** |
| **PR2: surface `_` as sugar** for missing binder pieces | Parse, SurfaceLang, lower | **+50–150** | none if desugars to binder `none` / return pin |
| **PR3: true structural holes + green principal** | Core Pins/AnnoTy, InferW mutuals, Surface | **~1–3k+ proof LOC**, multi-week | **Very large** |
| **PR3-lite: holes → fvars, leave sourceSound broken** | smaller code | weeks of debt | **unacceptable** vs project standards |

Easy: parse `_`, pretty, binder `Option` paths (already there), return-pin let.  
Hard: rigid/flexible split, Pins→Elab, principal for holey source, `{a}` with incomplete residual.

Cross-module if PR3: `Core.lean`, `InferW.lean` (~30k combined hard proofs), `SurfaceBridge`, Pretty/Editor, Headlines.  
If PR1 only: almost all in `SurfaceBridge.lean`.

**SurfaceWT note:** strong `letInAnn` rules want a packed scheme + fully annotated params (`LowerLetParams`). Partial-param programs go through `of_lowers` today; PR1 should keep that path green rather than force structural WT rules to accept holey packs.

---

## Recommended implementation path

### Step 0 — Mental model (no code)

- Treat existing `Option` as **binder-level holes**.  
- Reserve “type holes” for **structure inside a monotype/scheme**.  
- Return with incomplete domains → **inner let pin**, not dropped ann, not holey outer scheme.  
- Do **not** open InferW Pins rewrite for head binders alone.  
- `{a}` without full residual is PR3/PR4, not PR1.

### PR1 — Head-binder packing + return-pin (do this first)

**Goal:** keep every provided **mono** annotation; never emit a wrong-arity scheme.

1. When `paramsToArrows` fails, **never** fall back to bare `ret` as the let scheme (`finalizeAnn` ~3514–3524). Set `finalizeAnn = none`.  
2. Still `wrapCoreParams` for per-param `Option`s.  
3. If surface had a **mono** return ann and packing was incomplete, wrap the raw RHS as  
   `letIn (some ret) body (var 0)` **inside** the λ nest (return pin). Poly return / tyParams in that residual → reject or defer (needs scheme / PR3).  
4. Clarify `@TODO(partial-head-ann)` docs: partial mono params already lower; bug is packing fallback; `{a}` without scheme is a separate skolem-scope limit.  
5. Tests:  
   - `let f (x : Int) y = …`  
   - `let f (x : Int) y : Int = …` → outer `none`, λ(some Int), λ none, **inner letIn (some Int)** — not `letIn (some Int)`  
   - body that violates `: Int` fails under Infer  
   - existing full-residual packing still works  

**Modules:** `FHM/SurfaceBridge.lean`, packing tests (`Headlines` / Parse guards / Examples).  
**Out of scope:** InferW, Core `Ty`, structural `_`, `{a}` without full pack.

### PR2 — Surface `_` sugar (limited)

1. Parser: `_` in type position (today underscore is value binder only).  
2. `(x : _)` ≡ bare `x` (`none`).  
3. Bare return `_` / missing return → no return pin.  
4. Reject or defer `Int → _ → Int` as a **written scheme residual** until PR3 — or only accept it when holes line up with head-binder slots and desugar like PR1 (does **not** cover `List _` / arbitrary positions).

### PR3 — True structural holes (only if still wanted)

**Do not** overload Core `fvar` rigidity.

Copy BLSketch pattern:

1. `AnnoTy` / `AnnoPoly` with holes (Surface and/or Core annotations).  
2. Declarative `AnnoTy.Elab ann τ` instead of `Pins` for holey anns.  
3. Algo: `fillHoles Φ ann → (Φ', τ)` then existing unify/skolem on solid `τ`.  
4. Elaborated terms store **filled** monotypes/schemes.  
5. Re-prove `sourceSound` against filled source or Elab-aware TypeOf.

Alternative: holes **Surface-only**, fully expanded before Core — Core theorems untouched; limited to desugarable positions (≈ PR1 spine).

### PR4 (optional) — `{a}` without full residual

Needs either implicit `∀a. _` (holes / PR3) or tyParam scope independent of finalized scheme (`letAnnTyPrefix` redesign + story for generalising those names). Not solved by return-pin lowering.

---

## BL holes (orthogonal note)

`FHM/BLSketch.lean` already has:

- `AnnoTy` with `Option Count` holes on **bound slots only**  
- `AnnoTy.Elab` / `fillHoles` at Φ  
- Used in `synth` for λ / ascriptions  

**HM type holes are not a prerequisite** for `BL _ _ t`.  
Bound-layer UX can proceed on the dual-stack track independently.  
If HM later adopts AnnoTy/Elab, it can mirror the BLSketch pattern (and the uniqueness-as-policy lesson).

---

## Concrete anchors

| Topic | Location |
|-------|----------|
| Pins | `FHM/Core.lean` ~2428–2432 |
| TypeOf λ/let | `Core.lean` ~2582–2617, ~2748–2768 |
| Expr (no term ascription) | `Core.lean` ~249–265 |
| LamSeed / Infer λ / letInAnn | `FHM/InferW.lean` ~842–844, ~1638–1696 |
| sourceSound rigidity | `InferW.lean` ~9917–9919, ~9979–9986 |
| finalizeAnn / wrapCoreParams / letAnnTyPrefix / TODO | `FHM/SurfaceBridge.lean` ~3488–3551, ~5059–5067 |
| Surface Binding params | `FHM/SurfaceLang.lean` ~97–118 |
| BL AnnoTy / fillHoles | `FHM/BLSketch.lean` ~367–400, ~1215–1230 |

---

## Success criteria (by PR)

### PR1

- [ ] No packing fallback that sets scheme body to bare return when domains incomplete  
- [ ] `let f (x : Int) y : Int = …` keeps Int on `x` **and** return (inner pin); outer scheme not bare `Int`  
- [ ] Docs match reality (incl. `{a}` skolem limit)  
- [ ] `lake build` green; no InferW edits  

### PR2

- [ ] `(x : _)` parses and ≡ unannotated param  
- [ ] No silent wrong schemes  

### PR3 (if ever)

- [ ] `#print axioms` on `Infer.principal` / `sourceSound` still clean  
- [ ] Hole filling documented as Elab, not Pins equality  
- [ ] Rigid scoped tyvars still distinct from flexible holes  

---

## Implementing-agent prompt (copy-paste)

> Read `briefs/next-agent-brief-type-holes.md`. Implement **PR1 only** unless the user expands scope: fix `finalizeAnn` so incomplete head-binder domains never produce a bare-return scheme (`none` instead); `wrapCoreParams` as today; when a mono return ann was present but packing failed, wrap the RHS as `letIn (some ret) body (var 0)` inside the λ nest so return info is kept. Add tests. Do not drop return anns silently. Do not touch InferW/Core Pins. Do not implement structural `_` or `{a}`-without-scheme unless asked (PR2+).
