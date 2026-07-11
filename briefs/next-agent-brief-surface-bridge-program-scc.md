<!-- Written 2026-07-11, end of the post-headline front-end session
     (DataDecl → Program → freeNames → naive SCC). Read these FIRST, in order:
       1. briefs/next-agent-brief-surface-bridge.md — THE ORIGINAL PLAN (items 1–9).
       2. briefs/next-agent-brief-surface-bridge-followups.md — status when the
          expression headline `surface_type_safe` landed (still accurate for the
          Core/expr story; this brief UPDATES the program/SCC backlog).
       3. briefs/next-agent-brief-surface-bridge-kickoff.md — PatComp interface
          (historical; pattern compilation is done).
     This brief does NOT duplicate the plan. It gives the FRESH status after
     program-pipeline + SCC scaffolding landed, what’s proved vs sorry, and
     where the next agent should start. -->

# Brief: surface Program pipeline + SCC scaffolding — handoff

## TL;DR — where we are

The **expression** north star is still complete and axiom-clean:

```
surface_type_safe : lower + typecheck + SurfaceCovers
  → elaborate yields typed, exhaustive, non-stuck Core
```

This session built the **program / top-level** layer on top of that, and paved
the road to automatic mutual-recursion grouping:

| Layer | Status |
|-------|--------|
| Surface `DataDecl` → `Decls` / `elabDecls` | **DONE**, axiom-clean |
| `Program` = decls + groups + body; prelude merge | **DONE**, axiom-clean |
| `desugarGroups` → nested `letRecIn`; `program_type_safe` | **DONE**, axiom-clean |
| `freeNames` / `bindingDepEdges` (C0) | **DONE**, `#guard`-tested |
| `ValidBindingGroups` + `sccGroups` (C1 executable) | **DONE** executable + `#guard`s; **`sccGroups_sound` / `_complete` still `sorry`** |
| Adequacy of SCC vs dependency graph (C2) | **OPEN** (those sorries + polish) |
| `checkExhaustive`, `SurfaceWT` corollary, `letBlock` collapse | **OPEN** (later) |

`lake build` green. `#print axioms` on `program_type_safe` /
`lowerProgram_sound` / `toCombinedWF` / DataDecl headlines =
`{propext, Classical.choice?, Quot.sound}` (no `sorryAx` on those). The **only**
intentional `sorry`s in the new SCC slice are `sccGroups_sound` and
`sccGroups_complete`.

Recent commits on this arc:
- `ace4206` — surface DataDecl lowering
- `e5f1835` — prelude-aware `Program` + `program_type_safe`
- `3fb2a3a` — explicit `groups` → `letRecIn` desugar
- (HEAD) — `freeNames` + naive `sccGroups` + `ValidBindingGroups`

---

## Larger picture (roadmap)

Project: verified ML-family language. Prior steps (arithmetic, decls, comparisons,
fused `letRec`, PatComp, surface→Core **expression** bridge) are done.

**Step 5 follow-through** is turning “one expression + handed `CtorEnv`” into a
**real front-end**: declare types, declare top-level vals, don’t ask the author
to pre-partition mutual recursion.

North-star *product* end state (not all done):

> A surface program (decls + flat bindings + body) elaborates to safe Core,
> with SCC inferred automatically, coverage checkable, no Core metatheory growth.

---

## What this session delivered (concrete)

### 1. Surface `DataDecl` (plan item 1) — COMPLETE

- AST: `Surface.DataDecl` in `FHM/SurfaceLang.lean`
- Spec/impl: `LowersDataDeclsIn` / `lowerDataDeclsIn` (ambient `ke₀`, typically
  `preludeKindEnv`); closed-group API recovered as `ke₀ = []`
- Payoff: `toWF`, `toCombinedWF`, elaborates via `elabDecls`
- File: `FHM/SurfaceBridge.lean` §2b

### 2. Whole-program slice A — COMPLETE

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

### 3. Binding groups desugar (explicit SCCs) — COMPLETE

Authors *can* write `groups` by hand. Desugar reuses existing `letRecIn` /
`lower` — **no Core edits**, no second letRec metatheory.

### 4. C0 free-name analysis — COMPLETE

In `SurfaceBridge` (after `patVars`):

- `freeNames` / `freeNamesD` — bound-scope free value names
- `Binding.refersTo`, `bindingDepEdges`
- `#guard`s for shadowing, let/letRec/match, dependency edges

**Infer does not do SCC** — surface already had `letRecIn`. Nothing to reuse
from Infer for this.

### 5. C1 naive SCC — EXECUTABLE DONE; PROOFS OPEN

- **Spec** `ValidBindingGroups binds groups`:
  - names `Nodup`
  - `groups.flatten` permutes `binds`
  - nonempty groups
  - mutual `DepReach` within each group
  - maximality (mutual ⇒ same group)
  - **topo**: direct cross-group edge `b1 → b2` ⇒ `b2`’s group index `<` `b1`’s
    (callee outer — matches `desugarGroups` foldr)
- **Reachability** `DepEdge` / `DepReach` / `DepMutual` (Prop)
- **Executable** `sccGroups`:
  1. reject dup names
  2. pairwise `canReach` on index graph → mutual-reachability partitions
  3. Kahn topo on condensation (`sccBeforeEdges`: dependency before dependent)
  4. map indices back to `List (List Binding)`
- `#guard`s: `f`/`g` chain, mutual `h`/`k`, independents, dups, empty,
  SCC→desugar→`elaborateProgram`
- **Frozen, still `sorry`:**
  ```
  theorem sccGroups_sound : sccGroups binds = some groups → ValidBindingGroups binds groups
  theorem sccGroups_complete : ValidBindingGroups binds groups → (sccGroups binds).isSome
  ```
  Completeness is deliberately **not** `= some groups` (order freedom).

---

## Immediate next work (recommended)

### Priority 1 — discharge `sccGroups_sound` / `sccGroups_complete`

Parent-owned freeze is already in-tree. Hand off proofs only; **do not**
weaken `ValidBindingGroups` without Aron agreeing.

Hints:
- Bridge Bool `canReach` ↔ `DepReach` (fuel ≥ n, simple paths)
- Partition ↔ sameScc + maxScc
- Kahn ↔ topo
- `flatPerm` from reconstructing bindings via indices
- Completeness: Nodup ⇒ executable doesn’t `guard`-fail; algorithm always
  returns *some* partition (existence, not uniqueness)

Model: try **composer-2.5** first; bump to **grok-4.5-xhigh** if
reachability↔Prop or Kahn proofs get nasty.

Gate: `lake build` + no `sorry` on those two + `#print axioms` clean.

### Priority 2 — wire flat bindings into `Program` (optional small slice)

Today `Program.groups` is still author-supplied (or filled via
`(sccGroups binds).getD []` in tests). Natural glue:

- helper `Program.ofFlat decls binds body` using `sccGroups`, or
- change `Program` to carry a flat list and compute groups in `Program.term`

Keep desugarer as the single consumer of `List (List Binding)`.

### Priority 3 — later backlog (from followups; don’t mix into SCC proofs)

1. **`checkExhaustive` / `dTreeExhaustiveB`** — decide `SurfaceCovers`
2. **`SurfaceWT` corollary** — declarative headline (needs typeability
   invariant across match lowerings)
3. **`letBlock` collapse** (design settled, not scheduled): remove surface
   `letIn`/`letRecIn` from the *public* AST; one `letBlock`; run the **same**
   freeNames→SCC→nested Core `let`/`letRec` in **lowering** (not a second IR
   layer). Internal desugar to today’s `letRecIn` is fine as a stepping stone.
4. Pattern-λ desugar, errors, strings — still deferred / optional

---

## Design decisions (settled this session — don’t reopen casually)

1. **Core stays minimal** — SCC/desugar live in `SurfaceBridge` / `SurfaceLang`.
2. **Always `letRecIn` for nonempty groups** (incl. size 1). Tagged
   `nonrec`/`rec` groups deferred (better HM generalization later).
3. **`ValidBindingGroups` is intentionally non-deterministic** on intra-group
   order and order of incomparable SCCs — like `Lowers` at `match`.
4. **Naive mutual-reachability SCC**, not Kosaraju, not `Lean.Util.SCC`
   (`partial` / meta — unfit for FHM proofs).
5. **AbstractWalk** (`lean-experiments`) = directed reachability library only;
   **not** imported; patterns optional for `DepReach` proofs, insufficient for
   SCC+topo alone.
6. **Workflow**: parent freezes Prop/theorem *statements*; subagent proves or
   returns obstruction; parent edits specs if false. Prefer respectful prompts
   (no “workhorse” framing). Gate with fresh-olean `lake build`, not LSP alone
   after dependency edits.

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

---

## Non-negotiables

- Headlines stay `sorry`/`admit`/`axiom`-free and axiom-clean when claimed done
- No new `.lean` roots without strong justification (still 9 roots)
- Don’t weaken frozen statements; add helper hypotheses instead
- Granular commits per slice

---

## Suggested first message for the next agent

> Read `briefs/next-agent-brief-surface-bridge-program-scc.md`. Discharge
> `sccGroups_sound` and `sccGroups_complete` in `FHM/SurfaceBridge.lean` without
> changing `ValidBindingGroups` or `sccGroups`’ meaning. If a statement is
> unprovable/false, stop and explain with a minimal obstruction. Gate with
> `lake build` + axiom check. Then optionally wire `Program.ofFlat` /
> flat-bindings path.

---

## File map (quick)

| Path | Role |
|------|------|
| `FHM/SurfaceLang.lean` | `DataDecl`, `Binding`, `Program`, `desugarGroups`, `Program.term` |
| `FHM/SurfaceBridge.lean` §2b | DataDecl lowering |
| `FHM/SurfaceBridge.lean` (after `patVars`) | `freeNames`, `sccGroups`, `ValidBindingGroups` |
| `FHM/SurfaceBridge.lean` §9b | `LowersProgram`, `lowerProgram`, `program_type_safe` |
| `FHM/Decls.lean` | `preludeDecls`, `elabDecls` |
| `briefs/next-agent-brief-surface-bridge-followups.md` | Post-expression-headline backlog (partially superseded for program/SCC by **this** brief) |
