<!-- Written 2026-07-14: handoff after SurfaceWT Approach A / 1a closed.
     Read these FIRST, in order:
       1. briefs/next-agent-brief-surface-bridge.md — original plan items 1–9.
       2. briefs/next-agent-brief-surface-bridge-followups.md — expression headline
          lessons (DTreeExhaustive; still authoritative).
       3. briefs/next-agent-brief-surface-bridge-program-scc.md — Program/SCC/ofFlat
          (DONE); letBlock design locks.
       4. briefs/next-agent-brief-surface-wt-corollary.md — SurfaceWT Approach A / 1a
          (DONE for headlines; strong inductive still incomplete for annotated/poly).
     THIS brief is the CURRENT takeover. -->

# Brief: surface front-end backlog (post–SurfaceWT)

## TL;DR — where we are (2026-07-14)

Expression + program + coverage + declarative WT **headlines** are axiom-clean.
`SurfaceWT` Approach A / 1a shipped, but the strong inductive is **not finished**:
annotated / poly `letIn` / `letRecIn` still fall back to `of_lowers` (match-free
only). Close that gap **before** jumping to the next product feature (`letBlock`).

| Layer | Status |
|-------|--------|
| Expression `surface_type_safe` | **DONE** |
| Pattern compilation (`PatComp`) | **DONE** |
| Surface DataDecl lowering + `elabDecls` | **DONE** |
| Program / SCC / `Program.ofFlat` / `program_type_safe` | **DONE** |
| Executable `checkExhaustive` → `SurfaceCovers` | **DONE** (`7e9fc1f`) |
| `SurfaceWT` corollary headlines (Approach A / **1a**) | **DONE** (`44669db`) |
| **Annotated / poly strong `SurfaceWTExpr` constructors** | **OPEN — Priority 1** (finish 1a) |
| `letBlock` public AST collapse | **OPEN — Priority 2** |
| Pattern-λ desugar | **OPEN — Priority 3** |
| Surface string literals | **OPEN** (optional) |
| Friendly errors (`Except Error`) | **OPEN** (optional / UX) |
| Far-horizon item 9 (typeclasses, rows, floats, …) | **DEFERRED** |

`EvaluateUnsafe` (`e0d8f34`) is orthogonal staging — not this backlog.

---

## What “done” means for SurfaceWT headlines (don’t redo)

- **Strong** `SurfaceWT` := `∃ τ, SurfaceWTExpr … [] [] [] s τ`.
- At `match_`/`ife`: open ingredient typings (not weird `emitInner`).
- Unannotated mono `letIn`/`letRecIn`: strong ctors; nested matches OK.
- Corollary: `surface_type_safe_of_SurfaceWT` (+ `arityConsistent` /
  `fieldsKinded`) axiom-clean.
- Weak WT kept as `SurfaceWT_weak` for the NoMatch uniqueness lemma only.
- **Do not** pin `LowersExpr.match_` (B) or redefine WT as `typecheck(lower)` (C)
  without Aron.
- Details: `briefs/next-agent-brief-surface-wt-corollary.md`.

---

## Priority 1 — Finish strong `SurfaceWTExpr` (annotated / poly lets)

**Why first:** This is the unfinished slice of Approach A / 1a, not a separate
product feature. Closing it means nested `match_` under annotated / poly
`letIn`/`letRecIn` can inhabit strong `SurfaceWT` without forcing the whole
subterm into `SurfaceExprNoMatch`.

| Form | Today | Gap |
|------|-------|-----|
| Unannotated mono `letIn` | strong ctor | — |
| Annotated / poly `letIn` | `of_lowers` only | Nested match cannot form strong WT |
| Unannotated mono `letRecIn` | strong ctor (empty gen pool) | — |
| Annotated / poly `letRecIn` | `of_lowers` only | Same; needs `RecSpec.poly` / nonempty gen |

**Known obstruction (doc on `SurfaceWTExpr.letIn`):**
`GeneralisesTo` for `some σ` needs `openBoundTyVars` / arity-0 `openTyVars []`
transport that is not yet wired into the strong inductive. Expect work in
`SurfaceBridge` around `SurfaceWTExpr` + the `TypeOfHM_of_lowerExpr_of_SurfaceWTExpr`
ladder; possibly small helpers near existing `openTyVars` /
`AllMatchesExhaustive.openTyVars` uses.

**Done when:**
- Strong ctors (or equivalent) cover annotated mono + poly `letIn` and annotated /
  poly `letRecIn`, with recursive `SurfaceWTExpr` premises on RHS/body (matches OK).
- Ladder / corollary still axiom-clean; gate with `lean_verify` on
  `surface_type_safe_of_SurfaceWT`.
- Doc comments on `of_lowers` / let constructors updated to match reality.

**Do not** weaken headlines or reopen B/C to dodge the transport.

---

## Priority 2 — `letBlock` (design settled)

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

Gate: `lake build` + `lean_verify` on `surface_type_safe` /
`surface_type_safe_of_SurfaceWT` / `program_type_safe`.

---

## Priority 3 — Pattern-λ desugaring (original plan item 4 leftover)

Today `lower` returns `none` for a λ whose parameter is a **non-trivial pattern**
(only `lambda_name` / `lambda_wild` in `Lowers`). Surface AST already has
`lambda (param : Pattern) …`.

Desugar `λ(p). body` → `λx. match x with p => body` (fresh `x`); wire
`Lowers` / `lower` / `SurfaceWTExpr` / coverage. **Confirm exhaustiveness policy
with Aron** before locking (catch-all vs irrefutable-only vs fail-default +
`SurfaceCovers`).

---

## Priority 4 — Small product gaps (opportunistic)

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
| — | `SurfaceWT` declarative corollary | **DONE** headlines; **annotated/poly strong ctors OPEN** |
| 8 | Friendly errors | **OPEN** (optional) |
| 9 | Typeclasses / rows / floats / `ord`/`chr` / nat→Peano / Core split | **DEFERRED** |

Extra (not in original 1–9): `letBlock` — **OPEN**, Priority 2 after finishing
strong WT.

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
| `briefs/next-agent-brief-surface-wt-corollary.md` | Strong WT record + known poly obstruction |
| `briefs/next-agent-brief-surface-bridge-program-scc.md` | SCC / ofFlat / letBlock design notes |
| `briefs/next-agent-brief-surface-bridge-followups.md` | Coverage lessons |
