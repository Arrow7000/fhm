# Design memo: deletion-first bounds elaborator

> **Superseded (product architecture):** 2026-08-04 by
> [`design-memo-bounds-preserving-elaboration.md`](design-memo-bounds-preserving-elaboration.md).
> That memo is the agreed direction: keep BL on Core through Infer; bounds is a
> second elaboration that rewrites types; then bounds-aware exhaustiveness.
>
> **Still useful:** diagnosis that coverage must not be a second Core interpreter
> with stub environments; one semantic authority for match coverage; G0-style
> acceptance discipline. Those ideas fold into Phases 3–4 of the new plan after
> ascriptions are preserved on the term.
>
> Do **not** implement this memo’s erase/sidecar/`ofLower` + “record coverage on
> current Anns walk” stack as the product path without re-reading the superseding
> memo.

**Status:** Historical / partial (coverage-authority ideas only).  
**Date:** 2026-08-03 (superseded 2026-08-04).  
**Scope (original):** Bounds-side executable architecture only.  
**Superseded for packaging by:** `design-memo-bounds-preserving-elaboration.md`.  
**Originally superseded:** V1/V2 migration plan in
`next-agent-brief-bounds-elaborator-architecture.md` (that brief is also historical).

**Related:**

- `briefs/design-memo-bounds-preserving-elaboration.md` — **current** architecture.
- `briefs/design-memo-bounds-layer-on-core.md` — locked BL product rules (D22/D24/R3).
- `briefs/next-agent-brief-bounds-elaborator-architecture.md` — investigation history.
- `scripts/bl-e2e-smoke.sh` — legacy local product gate (old packaging).

---

## 1. Executive decision

Do **not** migrate or generalize `checkProgramMatches`.

The authoritative Bounds Synth traversal already visits every relevant Core
match while carrying the real `Δ`, `bctx`, HM type information, bounds demand,
freshness, and R3 residual state. The second Matches traversal exists to apply
list `BoundCovers` and non-List constructor exhaustiveness, but independently
reconstructs binder environments using λ stubs, templates, and Infer-shape
fallbacks.

The revised plan is:

```text
freeze product semantics
  → make authoritative Synth record coverage requirements at each match
  → discharge those requirements after bounds elaboration
  → delete the entire Matches interpreter and its second pipeline call
  → reassess what architecture work remains
```

This is a deletion project, not a new general elaborator framework.

### Expected reduction

| Plan | Root-authority work | Main risk |
|------|---------------------|-----------|
| Previous V1+V2 migration | ~10–17 focused days before cleanup | Building a trace/facade while both semantic authorities remain |
| Revised deletion-first plan | ~6–12 focused days including gates | Correctly preserving coverage through every Synth runner |

Independent nested-count discharge and structured diagnostics remain separate.
Including those, the broader project is estimated at roughly **2.5–5 focused
weeks**, not the earlier 5–9 week conservative forecast.

---

## 2. Locked architecture constraints

This plan changes no locked BL design decision.

1. **D1–D2:** BL remains an optional sidecar after erase and ordinary HM
   inference.
2. **InferW is off limits.** Bounds may consume `eOut` and `τ`; it must not add
   bounds logic, annotations, constraints, or output requirements to InferW.
3. **D18:** bounds-aware nested match coverage remains on lowered Core.
4. **D22:** HM `List α` supplies only type shape. It never creates a concrete or
   default interval.
5. **D24:** fresh `?lo` / `?hi` are introduced only at sanctioned unascribed
   List-parameter origins.
6. **R3:** residual collection, `packAtEscape`, and `uniqueOnly` policy remain
   unchanged.
7. Default FHM remains free of Bounds/Z3 dependencies.
8. No surface syntax, Core `Ty`, PatComp, SCC, evaluator, or letRec elaboration
   changes are part of this work.

If implementation appears to require an InferW, Core, lowering, or general
solver redesign, stop and write a separately estimated proposal. Do not absorb
it into this project.

---

## 3. Current executable shape

Live and EditorSupport currently perform two independent Bounds traversals:

```text
eOut + τ + bounds anns
  │
  ├─ checkProgramAnns
  │    • origin synthesis
  │    • ascription checking / hole pinning
  │    • binder β / scheme decisions
  │    • R3 residual and pack-at-escape
  │    • result: authoritative bctx + body β
  │
  └─ checkProgramMatches
       • starts again from empty bctx
       • reconstructs every binder
       • checks List BoundCovers / ctor exhaustiveness
       • recursively reconstructs nested branch environments
```

`checkProgramAnns`’s `bctx` is used for report enrichment but is not passed to
Matches. Matches therefore became a second bounds interpreter.

### 3.1 Patch-producing paths in Matches

The second walk currently contains:

- An unannotated λ `.fvar 0` slot solely for de Bruijn alignment.
- A List-let D24 fallback when lookup returns that stub.
- Pair and general ADT template fallbacks.
- A separate letRec group inference path.
- Separate surface-spine binder/index arithmetic.
- Optional demand propagation independent of Synth check mode.
- Separate branch-environment reconstruction.

Each path answers a semantic question that the authoritative Synth traversal
has already answered or can answer at the original match site.

### 3.2 What Synth already does

`inferBoundsΦ`, `checkBoundsΦ`, and `checkAgainstΦ` all recurse through matches.
At a match site they already have:

- `Δ`;
- authoritative `bctx`;
- scrutinee HM type `τs`;
- scrutinee bounds `βs`;
- branch patterns and bodies;
- refined Nil/Cons environments;
- expected result `τ` / demanded `β` when checking;
- R3’s current residual state.

`synthMatch` already handles:

- Nil+Cons in either order;
- Nil-only under `mustBeEmpty`;
- Cons-only under `mustBeNonempty`;
- Nil/Cons branch refinement;
- result checking/joining under `List α`.

`synthJoinArms` / `synthJoinArmsAt` already recurse through non-List branch
bodies and join result bounds.

What Synth does **not** yet own is:

- wildcard parity for List matches;
- an explicit full `checkBoundCovers` check;
- non-List `coreCtorCoverage`;
- transport of coverage results through all top-level runners.

Those are substantially smaller than retaining and repairing a second Core
interpreter.

---

## 4. Target architecture

### 4.1 One semantic traversal

```text
check program bounds
  │
  ├─ authoritative Synth traversal
  │    ├─ decide each binder exactly once
  │    ├─ synthesize/check each β exactly once
  │    ├─ preserve current residual semantics
  │    ├─ recurse through every branch under the real refined environment
  │    └─ record coverage requirements at match sites
  │
  ├─ discharge recorded coverage requirements with CtorEnv
  │
  └─ return bctx + body β for report / hover / execution
```

Coverage remains a distinct judgment, but not a distinct interpreter.

### 4.2 Coverage information

At each match, Synth must preserve enough information to later decide:

- List coverage under the match’s exact `Δ` and scrutinee `β`; or
- non-List constructor exhaustiveness under scrutinee `τ` and the constructor
  environment.

The requirement should also retain a semantic site suitable for later
structured diagnostics.

It must **not** contain a reconstructed binder environment. Branch bodies have
already been traversed under the authoritative environment; coverage discharge
only decides whether the observed branch set covers the scrutinee.

### 4.3 Recommended transport

Extend the existing Synth result state conceptually from:

```text
R3 residual constraints
```

to:

```text
R3 residual constraints + coverage requirements
```

Do not finalize a new Lean structure or inductive in this memo. Per project
workflow, add the proposed definition in Lean during A1, then stop for user
review before plumbing it through the traversal.

Why prefer recorded requirements over threading `CtorEnv` through Synth:

- Keeps constructor lookup out of every recursive Synth signature.
- Preserves the separation between bounds synthesis and coverage validation.
- Gives structured diagnostics a natural future site.
- Avoids an import cycle between `Check` and `Synth`.
- Allows exact comparison against the old Matches result during migration.

### 4.4 Public entry point

End state: Live and EditorSupport call one program-level Bounds checker. It:

1. Runs authoritative annotation/origin checking.
2. Collects coverage requirements from every binder RHS and the body.
3. Discharges them with `CtorEnv`.
4. Returns the same authoritative `bctx` and body `β` used for reporting.

There must be no second full-program Core traversal for bounds coverage.

---

## 5. Critical state-flow caveat

This is the main hidden implementation complexity.

`ResM` currently carries R3 residual constraints. Some public wrappers expose
them, while others intentionally discard them. In particular, demanded scheme
checking goes through `checkAgainst`, which runs `checkAgainstΦ` and returns
`Unit`.

Coverage requirements cannot be lost at those runner boundaries.

The implementation must inventory and update:

- `runRes`;
- `inferBoundsWithRes`;
- `checkBoundsWithRes`;
- `checkBounds`;
- `checkAgainst`;
- `checkBinderRhs`;
- `checkLetSpine`;
- top-level body checking;
- letRec member checking.

### R3 non-regression rule

Adding coverage transport must not silently change which residual constraints
are retained or discarded today.

Coverage and residuals may share an implementation state, but their wrapper
policies remain explicit:

- preserve existing R3 behavior first;
- make coverage survive every successful traversal;
- do not “clean up” residual semantics in the same PR.

R3 canaries must run after each state-plumbing change.

---

## 6. Coverage parity required before deletion

### 6.1 List matches

The authoritative path must preserve all current accepted/rejected shapes:

| Shape | Expected |
|-------|----------|
| wildcard | accepted |
| Nil + Cons, either order | accepted |
| Nil-only with `hi = 0` proved | accepted |
| Nil-only when emptiness is not proved | rejected |
| Cons-only with `lo ≥ 1` proved | accepted |
| Cons-only when nonemptiness is not proved | rejected |
| malformed/duplicate/incomplete unsupported branch set | rejected |

Current gap: `checkBoundCovers` accepts wildcard; `synthMatch` currently rejects
it as an unsupported shape. Wildcard result synthesis/checking must be defined
before Matches is removed.

### 6.2 Non-List matches

Move or extract `coreCtorCoverage` so the final coverage discharger can check:

- wildcard;
- all constructors for the scrutinee ADT;
- constructor arity agreement;
- Pair/Bool/Option/custom ADTs represented in current demos.

No Bounds interval is invented for ordinary ADT fields.

### 6.3 Nested branch traversal

Deleting Matches is safe only because Synth has already traversed branch bodies.
G0 must include nested matches under:

- a demanded List λ;
- an Infer-introduced List let;
- Nil and Cons branches;
- Pair fields carrying List bounds;
- a non-List unary/binary ADT where supported;
- recursive binder RHSs.

If a nested branch currently relies on Matches’ richer field reconstruction,
improve the authoritative Synth arm environment rather than retaining Matches.

---

## 7. Acceptance matrix (G0)

Use dedicated files with exact expected stage/outcome. Do not use the mutable
`bl-showcase.fhm` as the sole oracle.

### Must remain green

1. Existing committed BL stdlib/product gate.
2. Unascribed List λ + Nil/Cons match (D24).
3. `BL 0 1` with `[]` / `h :: t` returning lists.
4. `BL 0 1` with `[]` / `h :: []` returning lists after independent N1 work;
   before N1, freeze its current expected failure explicitly.
5. Wildcard List match.
6. Nil-only under exact empty bounds.
7. Cons-only under exact nonempty bounds.
8. Bool/non-List exhaustive match.
9. Pair match with nested List match.
10. R3 vacuous/generalised canary.
11. R3 unique-commit canary.
12. letRec stdlib functions (`map`, `filter`, `append`, etc.).

### Must remain red

1. Cons-only on `BL 0 1` (input may be empty).
2. Nil-only on `BL 1 1` (input is nonempty).
3. Non-List missing-constructor match.
4. Constructor arity mismatch.
5. R3 non-vacuous multi-model escape.
6. Hole/ascription failures already covered by the smoke gate.
7. Bare `map` under an HM-incompatible function ascription (HM-stage failure).

### Invariant canaries

- D22: bare HM `List` never yields an invented concrete interval.
- D24: unconstrained List λ parameters still generalise.
- R3: residual-based ambiguity behavior is unchanged.
- Failure stage does not drift without an explicit approved reason.

---

## 8. Execution plan

### P0 — contract and inventory

**Estimate:** 1 day.  
**Blast radius:** none.

Write the exact inventory of:

- all match cases in `inferBoundsΦ`, `checkBoundsΦ`, and `checkAgainstΦ`;
- every `runRes` boundary;
- existing residual-preservation policy;
- current list/non-List coverage behavior;
- current Matches-only branch-environment behavior;
- expected G0 source files and stages.

**Exit:** no unknown path remains where a successful match traversal could fail
to report coverage.

### G0 — freeze acceptance semantics

**Estimate:** 1–2 days.  
**Blast radius:** tests/scratch gate only.

Create dedicated green/red programs and make the local gate independent of the
dirty showcase.

Record exact:

- command;
- expected success/failure;
- expected stage;
- expected semantic error kind/message fragment.

**Exit:** reproducible baseline including D22/D24/R3 and nested match cases.

### A1 — coverage definition and module boundary

**Estimate:** 0.5–1 day.  
**Blast radius:** low; definition/module imports only.

1. Move pure coverage predicates out of the Matches interpreter into a location
   that authoritative Synth and the final discharger can depend on without a
   cycle.
2. Add the proposed coverage-information definition in Lean.
3. Stop for user review of the definition before plumbing.

No behavior change.

**Exit:** coverage can be represented and checked without importing the old
walker.

### A2 — parity in authoritative match rules

**Estimate:** 1–2 days.  
**Blast radius:** medium within Synth match rules.

1. Add wildcard List match handling.
2. Ensure every List shape has the same coverage decision as
   `checkBoundCovers`.
3. Ensure non-List matches record enough type/branch information for
   `coreCtorCoverage`.
4. Audit authoritative branch environments for Pair and supported ADTs.

Keep the old Matches pass running as a comparison oracle.

**Exit:** new and old coverage decisions agree on G0.

### A3 — transport coverage through Synth runners

**Estimate:** 2–4 days.  
**Blast radius:** medium–high in `Synth.lean` / `Check.lean`.

Record coverage in:

- infer-mode match;
- check-mode match;
- demand/check-against match.

Preserve it through:

- binder RHS checks;
- scheme/mono/ascription paths;
- top-level let spine;
- letRec members;
- program body.

Keep residual behavior unchanged.

**Exit:** one authoritative program traversal produces complete coverage
information for every G0 match, and R3 canaries are unchanged.

### A4 — single program checker and wholesale deletion

**Estimate:** 1–2 days.  
**Blast radius:** high but narrow: `Check.lean`, Live, EditorSupport.

1. Discharge recorded requirements with `CtorEnv`.
2. Make Live and EditorSupport call the single program-level Bounds checker.
3. Delete:
   - `checkProgramMatches`;
   - `checkProgramMatchesSpine`;
   - `checkProgramMatchesGo`;
   - `checkProgramMatchesBranches`;
   - Matches-only branch reconstruction;
   - λ `.fvar 0` coverage stub;
   - List-let D24 coverage fallback;
   - obsolete comments/imports/call sites.

Do not leave a feature flag or dormant second authority after this PR stack.

**Exit:** repository search finds no `checkProgramMatches`; Live/editor run one
Bounds semantic traversal; G0 is unchanged.

### A5 — authoritative arm environment cleanup

**Estimate:** 1–2 days, only if G0 exposes a gap.  
**Blast radius:** medium within non-List branch synthesis.

Unify/enrich the authoritative arm-environment helper only where required for
nested matches in ADT fields.

Do not call `agreesTemplate` on a bare List as a convenient interval origin.

**Exit:** supported nested ADT cases work without stubs that affect bounds
semantics.

### C0 — cleanup and documentation

**Estimate:** 0.5–1 day.  
**Blast radius:** low.

- Update module comments and both architecture briefs.
- Record deleted LOC and removed fallback inventory.
- Update e2e/golden diagnostics where approved.
- Re-estimate N1 and E1 from the smaller post-deletion codebase.

---

## 9. Independent follow-up lanes

These are not evidence that the authority project succeeded.

### N1 — nested small-count discharge

**Estimate:** 3–6 days.  
**Scope:** `pred`/literal simplification, Cons-tail refinement,
`mustBeEmpty`/`mustBeNonempty`, Oracle boundary.

Target: `h :: []` under `BL 0 1` becomes routine.

Stop and split a solver project if this requires general symbolic-count
normalization rather than the named solid/refinement cases.

### E1 — structured Bounds errors

**Estimate:** 3–6 days.  
**Scope:** Bounds + Live + EditorSupport.

Use coverage information’s semantic site, but do not combine this with A3/A4
unless required to avoid losing existing diagnostics.

### Proof correspondence

Broad executable↔declarative correspondence is not part of this MVP. Existing
props remain the north star; frozen e2e is the migration gate.

Any new Prop or theorem statement follows the repository workflow: formulate it
in Lean, stop for user review, and estimate proof work separately.

---

## 10. letRec policy

Do not simplify Surface/Core/Infer letRec for this project.

Lowering already produces canonical Core `letRec`. The elaborate outer
`letIn`/inner `letRec` shape is InferW’s load-bearing representation for
recursive mono/poly generalisation. Changing it would touch the InferW proof
stack while solving only a localized Bounds tax.

Deletion-first coverage removes the main duplication:

```text
before: Synth handles letRec + Matches handles letRec again
after:  Synth handles letRec once + coverage consumes recorded facts
```

Keep the existing authoritative Synth mechanisms:

- provisional recursive slots;
- group synthesis;
- singleton wrapper handling needed for honest self-application.

A bounds-side `BinderSpine` helper may be considered **after A4** only if
substantial duplicate wrapper/index logic remains. Do not pre-build another
representation that Matches deletion may make unnecessary.

---

## 11. Explicit non-solutions

Do not:

- pass only the final Anns `bctx` into Matches;
- share a binder fold while retaining two semantic walks;
- make variable lookup manufacture bounds from expected HM `List`;
- introduce fresh D24 variables outside sanctioned parameter origins;
- normalize or rewrite `eOut`;
- change PatComp or surface coverage;
- simplify `letRecElab`;
- thread Bounds requirements into InferW;
- unify infer/check into a mega-function without a demonstrated need;
- refactor R3 residual policy while adding coverage transport;
- keep old and new coverage authorities alive “temporarily” beyond the A2–A4
  comparison stack.

---

## 12. Success metrics

The project succeeds only if all are true:

1. `checkProgramMatches*` has been deleted.
2. Live and EditorSupport perform one program-level Bounds semantic traversal.
3. Coverage decisions use state captured at authoritative match sites.
4. No λ `.fvar 0` exists solely for coverage alignment.
5. No List-let D24 fallback exists solely for coverage.
6. D22/D24/R3 canaries are unchanged.
7. All G0 intentional greens and reds retain their approved outcomes/stages.
8. Nested match support no longer depends on Infer-generated wrapper guesses.
9. Net semantic LOC decreases; a new facade around old paths does not count.

Report after each implementation PR:

- old authority removed;
- fallback/stub LOC deleted;
- G0 result;
- D22/D24/R3 result;
- changed failure stages;
- time spent versus estimate.

---

## 13. Stop rules

Stop and reassess if:

1. P0 cannot identify all successful match traversal paths.
2. A1’s coverage information starts carrying reconstructed binder environments.
3. A2 cannot match current coverage semantics without changing product policy.
4. A3 changes R3 residual behavior.
5. Two consecutive sessions add plumbing but do not move toward deleting
   Matches.
6. InferW, Core typing, lowering, PatComp, or general solver work enters scope.
7. A4 cannot delete the second walk immediately after switching callers.
8. G0 failure-stage drift cannot be explained by an approved correction.

If A3 has not produced complete coverage information within four focused days,
stop before building further compatibility infrastructure.

---

## 14. PR / work-stack shape

```text
PR 0  P0 + G0
      contract and dedicated acceptance gate

PR 1  A1
      pure coverage extraction + in-Lean definition review

PR 2  A2 + first half of A3
      parity + record coverage; old pass remains comparison oracle

PR 3  finish A3 + A4
      single public checker; delete Matches and both call sites

PR 4  A5/C0 only if required
      authoritative arm-env parity + cleanup/docs
```

PR 2 and PR 3 form one short stack. Do not merge PR 2 and leave both authorities
as the new steady state.

No commits or PRs without explicit user request.

---

## 15. Revised forecast

### Root-authority project

| Outcome | Focused days |
|---------|--------------|
| Best credible | 5–7 |
| Likely | 6–12 |
| Stop/reassess threshold | 12 without wholesale deletion |

### Including independent N1 and E1

| Outcome | Focused time |
|---------|--------------|
| Best credible | 2–3 weeks |
| Likely | 2.5–5 weeks |
| Expanded solver/proof scope | separate project; do not roll into estimate |

The first decisive evidence should appear within one week: complete coverage
information from authoritative Synth and named Matches fallback deletion in
reach. If it does not, invoke the stop rules rather than extending the schedule.

---

## 16. One-paragraph handoff

The BL-on-Core architecture remains unchanged and InferW is off limits. The
root executable problem is not that bounds synthesis is missing; it is that a
second Matches interpreter independently rebuilds bounds environments merely
to check coverage. Authoritative Synth already traverses infer/check/demanded
matches with the real `Δ`, `bctx`, types, refinements, and residual state.
Freeze exact semantics, record coverage requirements at those match sites,
preserve them through every runner (especially `checkAgainst` and binder
checking), discharge them with `CtorEnv`, then delete `checkProgramMatches*`,
its λ stub/List-let fallback, and the second Live/editor call. Preserve
D18/D22/D24/R3, do not touch letRec elaboration, and stop if the work starts
creating compatibility architecture instead of deleting the second authority.
