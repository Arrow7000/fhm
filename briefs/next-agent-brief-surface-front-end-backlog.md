<!-- Written 2026-07-14: handoff after SurfaceWT Approach A / 1a closed.
     UPDATED 2026-07-14: annotated/poly strong ctors (`letInAnn`/`letRecInAnn`) DONE.
     Read these FIRST, in order:
       1. briefs/next-agent-brief-surface-bridge.md — original plan items 1–9.
       2. briefs/next-agent-brief-surface-bridge-followups.md — expression headline
          lessons (DTreeExhaustive; still authoritative).
       3. briefs/next-agent-brief-surface-bridge-program-scc.md — Program/SCC/ofFlat
          (DONE); letBlock design locks.
       4. briefs/next-agent-brief-surface-wt-corollary.md — SurfaceWT Approach A / 1a
          (DONE, including annotated/poly strong ctors).
     THIS brief is the CURRENT takeover. -->

# Brief: surface front-end backlog (post–SurfaceWT)

## TL;DR — where we are (2026-07-14)

Expression + program + coverage + declarative WT **headlines** are axiom-clean.
`SurfaceWT` Approach A / 1a is finished including annotated / poly strong ctors
(`letInAnn` / `letRecInAnn`, `tvs = []`). Next product feature: `letBlock`.

| Layer | Status |
|-------|--------|
| Expression `surface_type_safe` | **DONE** |
| Pattern compilation (`PatComp`) | **DONE** |
| Surface DataDecl lowering + `elabDecls` | **DONE** |
| Program / SCC / `Program.ofFlat` / `program_type_safe` | **DONE** |
| Executable `checkExhaustive` → `SurfaceCovers` | **DONE** (`7e9fc1f`) |
| `SurfaceWT` corollary headlines (Approach A / **1a**) | **DONE** (`44669db`) |
| **Annotated / poly strong `SurfaceWTExpr` constructors** | **DONE** (`letInAnn` / `letRecInAnn`) |
| `letBlock` public AST collapse | **OPEN — Priority 1** |
| Pattern-λ desugar | **OPEN — Priority 2** |
| Surface string literals | **OPEN** (optional) |
| Friendly errors (`Except Error`) | **OPEN** (optional / UX) |
| Far-horizon item 9 (typeclasses, rows, floats, …) | **DEFERRED** |

`EvaluateUnsafe` (`e0d8f34`) is orthogonal staging — not this backlog.

---

## What “done” means for SurfaceWT headlines (don’t redo)

- **Strong** `SurfaceWT` := `∃ τ, SurfaceWTExpr … [] [] [] s τ`.
- At `match_`/`ife`: open ingredient typings (not weird `emitInner`).
- Unannotated mono `letIn`/`letRecIn`: strong ctors; nested matches OK.
- Annotated / poly `letIn`/`letRecIn`: `letInAnn` / `letRecInAnn` (require
  `tvs = []`, natural under `SurfaceWT`); nested matches OK.
- Corollary: `surface_type_safe_of_SurfaceWT` (+ `arityConsistent` /
  `fieldsKinded`) axiom-clean.
- Weak WT kept as `SurfaceWT_weak` for the NoMatch uniqueness lemma only.
- **Do not** pin `LowersExpr.match_` (B) or redefine WT as `typecheck(lower)` (C)
  without Aron.
- Details: `briefs/next-agent-brief-surface-wt-corollary.md`.

---

## Priority 1 — `letBlock` (design settled)

**Goal:** Collapse surface `letIn` / `letRecIn` in the *public* AST into one
`letBlock`; run freeNames → SCC → nested Core `let`/`letRec` in **lowering**
(same machinery as `Program.ofFlat` / `desugarGroups`).

**Settled shape (program-SCC brief):**
- One surface binding form (`letBlock`).
- Lowering partitions via `freeNames` / `sccGroups` / `ValidBindingGroups`.
- Internal desugar to today’s `letRecIn` is fine as a stepping stone.
- **Do not** confuse with `Program.ofFlat` (already done).
- **Do not** add a second IR layer or grow Core metatheory.

**Likely work:** AST + freeNames / covers / Lowers / lower / `SurfaceWTExpr` /
examples; prefer desugar-early to limit proof churn in ~9k-line `SurfaceBridge`.
Strong WT already has `letIn`/`letInAnn`/`letRecIn`/`letRecInAnn` — desugar
`letBlock` into those forms early so the inductive need not grow a fifth binder.

Gate: `lake build` + `lean_verify` on `surface_type_safe` /
`surface_type_safe_of_SurfaceWT` / `program_type_safe`.

---

## Priority 2 — Pattern-λ desugaring (original plan item 4 leftover)

Today `lower` returns `none` for a λ whose parameter is a **non-trivial pattern**
(only `lambda_name` / `lambda_wild` in `Lowers`). Surface AST already has
`lambda (param : Pattern) …`.

Desugar `λ(p). body` → `λx. match x with p => body` (fresh `x`); wire
`Lowers` / `lower` / `SurfaceWTExpr` / coverage. **Confirm exhaustiveness policy
with Aron** before locking (catch-all vs irrefutable-only vs fail-default +
`SurfaceCovers`).

---

## Priority 3 — Small product gaps (opportunistic)

1. **Surface string literals** — `Surface.PrimLitExpr` has no `str`; original
   brief wanted `str → List Char` sugar.
2. **Friendly errors (plan item 8)** — total `… → Except Error _`; blame is
   heuristic. Do last.
3. **InferW dead-code prune** — unused `AllMatchesExhaustive.eraseVarTyArgs*`
   (~InferW); stale doc refs.

---

## Original plan checklist (items 1–9)

| # | Item | Status |
|---|------|--------|
| 1 | Surface DataDecl → `elabDecls` | **DONE** |
| 2 | `Surface.Ty` lowering + kind-check | **DONE** |
| 3 | Core expr lowering (names, app, λ, let) | **DONE** |
| 4 | Sugar (`ife`, pair, list, bool, **pattern-λ**) | **DONE** except pattern-λ |
| 5 | Pattern compilation | **DONE** |
| 6 | Exhaustiveness checker (executable) | **DONE** |
| 7 | Top-level bindings / SCC / Program | **DONE** (+ `ofFlat`) |
| — | `SurfaceWT` declarative corollary | **DONE** (incl. annotated/poly strong ctors) |
| 8 | Friendly errors | **OPEN** (optional) |
| 9 | Typeclasses / rows / floats / `ord`/`chr` / nat→Peano / Core split | **DEFERRED** |

Extra (not in original 1–9): `letBlock` — **OPEN**, Priority 1.

---

## Non-negotiables

- Headlines stay `sorryAx`-free; gate with `lake build` / `lean_verify` after
  dependency edits (LSP oleans go stale).
- **Core stays minimal** — front-end in `SurfaceBridge` / `Decls` / `SurfaceLang`.
- Don’t weaken frozen headlines; strengthen helper premises with comments OK.
- No new `.lean` roots without strong justification.
- Don’t reopen Core metatheory, `ValidBindingGroups` design, Approach B/C, or
  `checkExhaustive` / `DTreeExhaustive` shape without Aron.
- Farm proofs with frozen statements; prefer `cursor-grok-4.5-high` for Lean in
  Cursor (economical); composer OK for smaller lemmas.

---

## File map (quick)

| Path | Role |
|------|------|
| `FHM/SurfaceLang.lean` | Surface AST (`lambda` Pattern param; `letIn`/`letRecIn`) |
| `FHM/SurfaceBridge.lean` | `SurfaceWTExpr` (~5214+), lower / Lowers / covers / Program / SCC |
| `FHM/Decls.lean` | `preludeDecls`, `elabDecls` |
| `FHM/PatComp.lean` | compile / emit / `lowerMatch` |
| `briefs/next-agent-brief-surface-wt-corollary.md` | Strong WT record (1a complete) |
| `briefs/next-agent-brief-surface-bridge-program-scc.md` | SCC / ofFlat / letBlock design notes |
| `briefs/next-agent-brief-surface-bridge-followups.md` | Coverage lessons |
