<!-- Written 2026-07-11 (DataDecl → Program → freeNames → naive SCC scaffold).
     UPDATED 2026-07-13: SCC adequacy proved + Program.ofFlat landed.
     UPDATED 2026-07-13 evening: checkExhaustive DONE.
     UPDATED 2026-07-13 night: SurfaceWT Approach A / 1a DONE —
       see briefs/next-agent-brief-surface-wt-corollary.md.
     Read these FIRST, in order:
       1. briefs/next-agent-brief-surface-bridge.md — THE ORIGINAL PLAN (items 1–9).
       2. briefs/next-agent-brief-surface-bridge-followups.md — status when the
          expression headline `surface_type_safe` landed (still accurate for the
          Core/expr story; this brief UPDATES the program/SCC / front-end backlog).
       3. briefs/next-agent-brief-surface-bridge-kickoff.md — PatComp interface
          (historical; pattern compilation is done).
       4. briefs/next-agent-brief-surface-wt-corollary.md — SurfaceWT Approach A
          (DONE / 1a); next deferred item is `letBlock`.
     This brief does NOT duplicate the plan. It gives FRESH status after SCC
     proofs + ofFlat + checkExhaustive, and points at the SurfaceWT brief. -->

# Brief: surface Program pipeline + SCC — handoff (updated)

## TL;DR — where we are (2026-07-13 evening)

The **expression** north star is complete and axiom-clean:

```
surface_type_safe : lower + typecheck + SurfaceCovers
  → elaborate yields typed, exhaustive, non-stuck Core
```

The **program / top-level** layer is complete through automatic SCC grouping.
**Executable coverage** (`checkExhaustive`) is also done.

| Layer | Status |
|-------|--------|
| Surface `DataDecl` → `Decls` / `elabDecls` | **DONE**, axiom-clean |
| `Program` = decls + groups + body; prelude merge | **DONE**, axiom-clean |
| `desugarGroups` → nested `letRecIn`; `program_type_safe` | **DONE**, axiom-clean |
| `freeNames` / `bindingDepEdges` (C0) | **DONE**, `#guard`-tested |
| `ValidBindingGroups` + `sccGroups` (C1) | **DONE** executable + `#guard`s |
| Adequacy `sccGroups_sound` / `_complete` (C2) | **DONE**, axiom-clean |
| `Program.ofFlat` (flat binds → SCC groups) | **DONE**, axiom-clean |
| `checkExhaustive` / `dTreeExhaustiveB` → `SurfaceCovers` | **DONE** (`7e9fc1f`) |
| `SurfaceWT` corollary (Approach A / 1a) | **DONE** — see surface-wt brief |
| `letBlock` | **OPEN** (next) |

`lake build` green through SurfaceWT Approach A / 1a. See
`briefs/next-agent-brief-surface-wt-corollary.md` for the strong `SurfaceWT`
definition and axiom-clean corollary.

Recent commits on this arc:
- `ace4206` — surface DataDecl lowering
- `e5f1835` — prelude-aware `Program` + `program_type_safe`
- `3fb2a3a` — explicit `groups` → `letRecIn` desugar
- `ebf20d5` — `freeNames` + naive `sccGroups` + `ValidBindingGroups`
- `9f59e10` — prove `sccGroups_sound` / `_complete`
- `568853a` — `Program.ofFlat`
- `7e9fc1f` — `checkExhaustive` + Bool→Prop soundness
- *(this arc)* — SurfaceWT Approach A / 1a corollary

---

## Larger picture (roadmap)

Project: verified ML-family language. Prior steps (arithmetic, decls, comparisons,
fused `letRec`, PatComp, surface→Core **expression** bridge) are done.

**Step 5 follow-through** is turning “one expression + handed `CtorEnv`” into a
**real front-end**: declare types, declare top-level vals, don’t ask the author
to pre-partition mutual recursion.

North-star *product* end state (SCC+ofFlat+checkExhaustive done; SurfaceWT
corollary + public AST still open):

> A surface program (decls + flat bindings + body) elaborates to safe Core,
> with SCC inferred automatically, coverage checkable (and decidable), no Core
> metatheory growth.

---

## What landed (concrete) — all COMPLETE through ofFlat

### 1. Surface `DataDecl` (plan item 1)

- AST: `Surface.DataDecl` in `FHM/SurfaceLang.lean`
- Spec/impl: `LowersDataDeclsIn` / `lowerDataDeclsIn` (ambient `ke₀`, typically
  `preludeKindEnv`); closed-group API recovered as `ke₀ = []`
- Payoff: `toWF`, `toCombinedWF`, elaborates via `elabDecls`
- File: `FHM/SurfaceBridge.lean` §2b

### 2. Whole-program slice A

- `Surface.Program`: `decls`, `groups : List (List Binding)`, `body`
- Prelude: `lowerDataDeclsIn preludeKindEnv` then
  `elabDecls (preludeDecls ++ userCore)`
- `Program.term = desugarGroups groups body` — nonempty groups always
  `letRecIn` (incl. size 1); empty groups skipped
- `LowersProgram` / `lowerProgram` / `elaborateProgram` / `program_type_safe`
  all talk about **`p.term`**, not raw `p.body`
- **`lowerProgram_complete` is ∃-style** (`∃ c', lowerProgram = some (ctors, c')`)
  because `LowersExpr.match_` is one-to-many (same reason expression
  `lower_complete` only concludes `.isSome`). Do **not** strengthen back to
  `= some c` without pinning `match_`.

### 3. Binding groups desugar (explicit SCCs)

Authors *can* write `groups` by hand. Desugar reuses existing `letRecIn` /
`lower` — **no Core edits**, no second letRec metatheory.

### 4. C0 free-name analysis

In `SurfaceBridge` (after `patVars`):

- `freeNames` / `freeNamesD` — bound-scope free value names
- `Binding.refersTo`, `bindingDepEdges`
- `#guard`s for shadowing, let/letRec/match, dependency edges

**Infer does not do SCC** — surface already had `letRecIn`. Nothing to reuse
from Infer for this.

### 5. C1/C2 naive SCC + adequacy

- **Spec** `ValidBindingGroups binds groups`:
  - names `Nodup`
  - `groups.flatten` permutes `binds`
  - nonempty groups
  - mutual `DepReach` within each group
  - maximality (mutual ⇒ same group)
  - **topo**: direct cross-group edge `b1 → b2` ⇒ `b2`’s group index `<` `b1`’s
    (callee outer — matches `desugarGroups` foldr)
- **Executable** `sccGroups`: pairwise `canReach` → mutual partitions → Kahn on
  condensation → bindings
- **Proved:**
  ```
  theorem sccGroups_sound : sccGroups binds = some groups → ValidBindingGroups binds groups
  theorem sccGroups_complete : ValidBindingGroups binds groups → (sccGroups binds).isSome
  ```
  Completeness is deliberately **not** `= some groups` (order freedom).

Proof stack highlights (do not reopen casually):
- Bool `canReach` ↔ Prop `DepReach` (fuel / simple paths / Nodup name↔index)
- Partition separation + Kahn on DAG condensation
- `sccOrderedIndexSets_flatPerm` needs **name-Nodup** (without it condensation
  can cycle and Kahn truncates — unconstrained form was false)
- Unbounded `kahnTopo_edge_before` was also false (OOB targets get indeg 0);
  private form requires `edgesBounded` + edge `Nodup`

### 6. `Program.ofFlat` (Priority 2)

```
def Program.ofFlat decls binds body : Option Surface.Program :=
  (sccGroups binds).map fun groups => ⟨decls, groups, body⟩
```

- `ofFlat_groups_valid` / `ofFlat_decls_body`
- `#guard`s: f/g chain elaborates; dup names → `none`
- `desugarGroups` remains the sole consumer of `List (List Binding)`
- Authors may still hand-write `groups`; ofFlat is the flat-bindings path

---

## Immediate next work (recommended)

### Priority 1 — `SurfaceWT` corollary (Approach A) — ACTIVE

**Takeover doc:** `briefs/next-agent-brief-surface-wt-corollary.md`.

Push declarative headline via `SurfaceWT` + `SurfaceCovers` → safety.
Hard part is `match_` / `lowerMatch` typing (not weird-emit transfer).
Next concrete proofs: `TypeOfHM.weaken_env`, `emitLets_typeable`, then clear
`emit_DTreeTypeable` / `compile_initMatrix_typeable`.

Fallbacks B (pin Lowers emit) / C (executable SurfaceWT) only with Aron.

### Priority 2 — `letBlock` collapse (design settled, not scheduled)

Remove surface `letIn`/`letRecIn` from the *public* AST; one `letBlock`; run
the **same** freeNames→SCC→nested Core `let`/`letRec` in **lowering** (not a
second IR layer). Internal desugar to today’s `letRecIn` / `desugarGroups` is
fine as a stepping stone. **Do not** confuse with `Program.ofFlat` (already
done — that only SCC-fills `Program.groups`).

### Optional / deferred

Pattern-λ desugar, errors, strings.

---

## Design decisions (settled — don’t reopen casually)

1. **Core stays minimal** — SCC/desugar live in `SurfaceBridge` / `SurfaceLang`.
2. **Always `letRecIn` for nonempty groups** (incl. size 1). Tagged
   `nonrec`/`rec` groups deferred (better HM generalization later).
3. **`ValidBindingGroups` is intentionally non-deterministic** on intra-group
   order and order of incomparable SCCs — like `Lowers` at `match`.
4. **Naive mutual-reachability SCC**, not Kosaraju, not `Lean.Util.SCC`
   (`partial` / meta — unfit for FHM proofs).
5. **AbstractWalk** (`lean-experiments`) = directed reachability library only;
   **not** imported.
6. **Workflow**: parent freezes Prop/theorem *statements*; subagent proves or
   returns obstruction; parent edits specs if false. Prefer respectful prompts
   (no “workhorse” framing). Gate with fresh-olean `lake build`, not LSP alone
   after dependency edits. Prove agents: `composer-2.5-fast` first; bump to
   `cursor-grok-4.5-high` when reachability/Kahn get nasty.

---

## Hard-won lessons (carry forward)

- `#eval`/`#guard` adversarial inputs before big proofs (prelude clash, ctor
  clash, shadowing in `freeNames`, SCC order).
- Expression `lower_complete` / program `lowerProgram_complete` are **∃ /
  isSome** because match lowering is one-to-many.
- `toCombinedWF` is declarative-side; `lowerProgram_sound` uses
  `elabDecls_sound` for the same WF fact — both fine.
- Stale LSP oleans after `SurfaceLang` edits → trust `lake build` /
  `lean_build`.
- SCC: name-Nodup is load-bearing for Kahn completeness; private Kahn lemmas
  need bounded edges.

---

## Non-negotiables

- Headlines stay `sorry`/`admit`/`axiom`-free and axiom-clean when claimed done
- No new `.lean` roots without strong justification (still 9 roots)
- Don’t weaken frozen statements; add helper hypotheses instead
- Granular commits per slice

---

## Suggested first message for the next agent

> Read `briefs/next-agent-brief-surface-wt-corollary.md` (primary) and
> `briefs/next-agent-brief-surface-bridge-program-scc.md` (Program/SCC context).
> `checkExhaustive` is done (`7e9fc1f`). Continue **SurfaceWT Approach A** emit
> typing (`emit_DTreeTypeable` / `compile_initMatrix_typeable` and deps). Do not
> reopen Core, `ValidBindingGroups`, or switch to B/C without Aron. Gate with
> `lake build` + axiom checks; farm composer one lemma at a time.

---

## File map (quick)

| Path | Role |
|------|------|
| `FHM/SurfaceLang.lean` | `DataDecl`, `Binding`, `Program`, `desugarGroups`, `Program.term` |
| `FHM/SurfaceBridge.lean` §2b | DataDecl lowering |
| `FHM/SurfaceBridge.lean` (after `patVars`) | `freeNames`, `sccGroups`, `ValidBindingGroups`, `Program.ofFlat` |
| `FHM/SurfaceBridge.lean` §5b | `dTreeExhaustiveB`, `checkExhaustive` → `SurfaceCovers` |
| `FHM/SurfaceBridge.lean` §7 + ladder ~5165–5410 | `SurfaceWT`, Approach A emit-typing stubs |
| `FHM/SurfaceBridge.lean` §9b | `LowersProgram`, `lowerProgram`, `program_type_safe` |
| `FHM/Decls.lean` | `preludeDecls`, `elabDecls` |
| `briefs/next-agent-brief-surface-wt-corollary.md` | **CURRENT** SurfaceWT Approach A handoff |
| `briefs/next-agent-brief-surface-bridge-followups.md` | Post-expression-headline backlog (coverage lessons; program/SCC superseded by **this** brief; SurfaceWT superseded by surface-wt brief) |
