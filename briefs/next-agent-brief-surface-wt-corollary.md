<!-- Written 2026-07-13 evening (scaffold); UPDATED 2026-07-13 night after
     Approach A / 1a closed. Supersedes the “IN PROGRESS emit-typing” story.
     Read these FIRST, in order:
       1. briefs/next-agent-brief-surface-bridge.md — original plan items 1–9.
       2. briefs/next-agent-brief-surface-bridge-followups.md — coverage redesign
          (still authoritative for why DTreeExhaustive).
       3. briefs/next-agent-brief-surface-bridge-program-scc.md — Program/SCC/ofFlat
          (DONE).
     This brief is the SurfaceWT Approach A record + what comes next. -->

# Brief: SurfaceWT corollary — Approach A (DONE / 1a)

## TL;DR — where we are (2026-07-13 night)

| Item | Status |
|------|--------|
| `checkExhaustive` / Bool→`SurfaceCovers` | **DONE** (`7e9fc1f`) |
| Match-free weak transfer | **DONE** (`SurfaceWT_weak` + NoMatch) |
| Full `SurfaceWT` corollary (Approach A / **1a**) | **DONE**, axiom-clean |
| `letBlock` | Still deferred |

**Headline:** `surface_type_safe_of_SurfaceWT` — strong `SurfaceWT` + `SurfaceCovers` +
ctor-env hygiene (`arityConsistent` / `fieldsKinded`) ⇒ elaborated Core is
type-safe and never stuck. Reuses `surface_type_safe` after proving
`typecheck(lower s)`.

---

## What `SurfaceWT` means now (1a)

**Old (weak):** `∃ c, Lowers s c ∧ typecheck c` — at `match_`, only types some
behavioural `emitInner`. Kept as `SurfaceWT_weak` for the NoMatch lemma.

**New (strong):**
```lean
SurfaceWT ctors s :=
  ∃ τ, SurfaceWTExpr ctors (kindEnvOfCtors ctors) [] [] [] s τ
```
`SurfaceWTExpr` is an **inductive** open carrier. At `match_`, it requires open
typings of scrutinee + each branch body under `patVars` / `branchBodyEnv` /
`patBindTys`, plus `PatternWF`, `MatchExhaustive`, and kinding — **not** “some
weird `emitInner` typechecks”.

Why: weak WT cannot feed `TypeOfHM_lowerMatch` (needs open branch bodies).
Option 1a accepts the stronger declarative story rather than pinning `Lowers`
(B) or making WT executable (C).

---

## Lemma ladder (final)

| Rung | Name | Status |
|------|------|--------|
| 0 | NoMatch uniqueness / weak transfer | **DONE** |
| 1 | `lowerExpr_match_decomp` | **DONE** |
| 2a | `patBindTys` / `EmitTyCtx` / `DTreeTypeable` | **DONE** |
| 2b–d | `weaken_env`, `emitLets_typeable`, `emit_DTreeTypeable`, `compile_initMatrix_typeable` | **DONE** |
| 2e | `TypeOfHM_lowerMatch` | **DONE** (needs hygiene + kinding) |
| 3 | `TypeOfHM_of_lowerExpr_of_SurfaceWTExpr` | **DONE** |
| 4 | `typecheck_of_lower_of_SurfaceWT` | **DONE** |
| 5 | `surface_type_safe_of_SurfaceWT` | **DONE** |

Hygiene premises on the corollary (true of `elabDecls` envs):
`CtorEnv.arityConsistent`, `CtorEnv.fieldsKinded`.

---

## `SurfaceWTExpr` coverage notes

| Form | Strong constructor? | Notes |
|------|---------------------|--------|
| Unannotated mono `letIn` | **yes** | Nested matches OK |
| Annotated / poly `letIn` | **yes** (`letInAnn`) | Requires `tvs = []` |
| Unannotated mono `letRecIn` | **yes** | Empty gen pool; nested matches OK |
| Annotated / poly `letRecIn` | **yes** (`letRecInAnn`) | Requires `tvs = []`; `RecSpec` mono/poly |
| `match_` / `ife` / app / pair / … | **yes** | Recursive |

`of_lowers` = `SurfaceExprNoMatch` + `LowersExpr` + `TypeOfHM` (unique fragment;
still available as escape hatch, no longer required for annotated/poly lets).

---

## A / B / C (historical)

| | Outcome |
|---|---------|
| **A / 1a** | **Shipped** — strong inductive WT + lowerMatch typing |
| **B** | Not used (do not pin `LowersExpr.match_` without Aron) |
| **C** | Not used |

---

## What is NOT this brief

- **`letBlock`** — next product item (Priority 1 in the backlog brief).
- Core / SCC / `ValidBindingGroups` / Approach B/C — do not reopen.

---

## Key file map

| Path | What |
|------|------|
| `FHM/SurfaceBridge.lean` | `SurfaceWTExpr`, ladder, corollary |
| `FHM/InferW.lean` | `TypeOfHM.weaken_env` |
| `FHM/PatComp.lean` | `emit` / `compile` / `lowerMatch` |
| `briefs/next-agent-brief-surface-bridge-followups.md` | Why `DTreeExhaustive` |
| `briefs/next-agent-brief-surface-front-end-backlog.md` | Current takeover |
