<!-- Written 2026-07-03, HEAD d2aee37. Adversarial review of the mixed-recursion
     campaign (2026-07-02/03): Core node fusion + premise packaging (2 waves) +
     InferW port (phases A–D) + showcase examples. Modeled on
     next-agent-brief-phase6-adversarial-review.md, which reviewed the previous
     campaign. Design/status reference: next-agent-brief-primitives-typedecls-surface.md. -->

# Brief: adversarial review of the mixed-recursion fusion

## Your mission

A full, hostile review of everything landed in commits `c23fb92..d2aee37`:
(a) the Core fusion (`Expr.letRecAnn` deleted; fused `Expr.letRec` with
`anns : List (Option PolyTy)`; fused typing rule over `RecSpec` internals),
(b) the two premise-packaging waves (`RecSpecs.*`, `GeneralisesTo`,
`Option.Pins`, `Ty.AreLC`, `PolyTy.InstantiatesTo`, `BranchCtorSpec`),
(c) the InferW port (fused `Infer.letRec`, `InferRecGroup` consMono/consPoly,
mixed Λ-nest elaboration, soundness + completeness re-proofs),
(d) the new Examples witnesses. The goal: confirm the headline theorems are
**tight, non-vacuous, and no weaker than what the pre-campaign pair of rules
jointly provided** — and that nothing was silently smuggled in via the ~9
statement adjustments the port's executing agent logged.

You are reviewing work done rapidly by agents (including statement adjustments
made mid-proof). Assume nothing; **read the statements yourself**. Do NOT trust
the status log's claims — reproduce them.

## Method

- Ground truth: fresh-olean `lake build`, then `#print axioms` /
  `lean_verify` per headline theorem. The stale-olean trap has bitten twice.
- The pre-campaign baseline is `git show c23fb92~1:FHM/Core.lean` and
  `…:FHM/InferW.lean`. Diff STATEMENTS (not proofs) against it liberally.
- Use `rg` scans + cheap handyman subagents for mechanical sweeps ("list every
  hypothesis of every `complete*` lemma", "find conclusions that are `True`",
  "find premises discharged by `nofun`/`False.elim`/`by simp` at every site").
- The Status log in `next-agent-brief-primitives-typedecls-surface.md` lists
  every claimed statement adjustment — that list is your audit checklist, but
  verify it is COMPLETE by diffing, not just auditing what it admits to.

## Specific attacks (highest value first)

1. **Fused-rule premise necessity (Core `TypeOfElabHM.letRec` / `TypeOfHM.letRec`).**
   For each premise — `RecSpecs.WF`'s five fields, `MonoTyped`, `PolyTyped`, the
   `bodyCtx` equation — argue (or find) why deleting it breaks soundness or
   completeness. Confirm neither cofinite premise is vacuously satisfiable for a
   genuinely mixed group (e.g. `PolyTyped` must NOT be dischargeable by `nofun`
   when annotated members exist). Check `L`'s role: is the nested exclusion
   `L ++ Xs` in `PolyTyped` load-bearing (it should be — the skolem-leak
   rejection depends on it; find where a proof would go through with plain `L`
   and confirm none does).
2. **Degeneracy adequacy.** The all-`none` and all-`some` instances of the fused
   rule must be inter-derivable with the OLD `letRec`/`letRecAnn` rules (the
   spike proved this against the spike's `MixedRule`; nobody has re-proven it
   against the LANDED rule). Either re-derive the two old rules as corollaries
   (throwaway or committed, your call) or verify equivalence by careful
   statement comparison against the baseline. This is the single best guard
   against silent weakening.
3. **The logged statement adjustments** (Phase B: 6, Phase C: 3). For each:
   fetch the old statement(s) from the baseline, write down the fused statement,
   and confirm the fused one implies the conjunction of the old pair when
   specialised to all-none / all-some. Pay special attention to:
   - `RecGroup.rigidVars` (the Phase-B pool-widening "bug fix") — confirm the
     bug was real (what unsound generalisation did the Phase-A pool permit?) and
     that a REGRESSION WITNESS exists in Examples; if none, add one (a scoped
     scheme variable that must NOT be generalised).
   - `block_fresh`/`InferRecGroupCoreComplete`'s new `hspecs_env`/`hKsch`
     premises — confirm they're discharged non-trivially at every call site and
     do NOT propagate into any headline statement.
4. **Headline statements are hypothesis-clean.** `Infer.sound`, `sourceSound`,
   `iff_typeable`, `completeAt`, `principal`, `principalType_*`, `typecheck_*`,
   `TypeOfElabHM.{type_safety_star, preservation, progress, faithful}`: diff
   each against the baseline — the ONLY permitted drift is the node/packaging
   change itself. No new hypotheses, no weakened conclusions, no vacuous
   premises. Then `#print axioms` each against fresh oleans.
5. **Packaging defeq honesty.** For each packaged premise
   (`GeneralisesTo`, `Option.Pins`, `Ty.AreLC`, `PolyTy.InstantiatesTo`,
   `BranchCtorSpec`, `RecSpecs.MonoTyped/PolyTyped/WF/rhsCtx/bodyCtx`): unfold
   and compare against the baseline's inline form — character-level equivalent
   modulo naming? (`Ty.AreLC` reorders length/LC into a conjunction — confirm no
   site silently uses only half where the old rule required both.)
6. **The mixed Λ-nest.** Poly wrappers use `Ty.bvarRange σ.paramCount` as the
   projection's tyArgs — verify arity (`= paramCount`) and that the letIn
   opener resolves them to the wrapper's skolems. Confirm `letRecElab_sound`'s
   statement covers BOTH wrapper shapes, and — vacuity check — that actual
   `typecheck` runs on the mixed Examples produce nests containing genuinely
   mixed inner nodes (instrument with `#eval` pretty-prints if needed).
7. **Escape-check reality in `InferRecGroup.consPoly`.** The two escape premises
   must not be trivially satisfiable; verify the executable `inferRecGroupCore`
   actually CHECKS them (decidably) rather than assuming, and that the
   skolem-leak `#guard` in Examples fails through THIS check (trace it).
8. **The relations still differ only in `var`.** Re-verify constructor-by-
   constructor post-fusion (the shared parametric premises make this mostly
   syntactic now — confirm the two `letRec` rules are the same modulo the
   relation parameter, and `faithful` covers every rule).
9. **Eliminator honesty.** `TypeOfElabHM.rec_strong` (extended with the fused
   group IHs) and the derived `TypeOfHM.rec_strong`: no `partial`/`unsafe`,
   motives genuinely universal, the `BranchMotive` `Or`-encoding still faithful
   to `TypeOfElabMatchBranch` inversion.
10. **Dead code + doc drift sweep.** The port claimed `genGroupSchemes` is still
    used — verify, else delete. Find any `RecSpec`/`RecGroup` helpers with zero
    uses, stale docstrings still describing two nodes, and the known stale
    `SpikeLetRecMixed` citations (cleanup-backlog item — fix the cheap ones).
11. **Examples `#guard` polarity audit.** Every `#guard`'s expected boolean
    matches its comment's claim (a pass with inverted polarity is a silent lie).

## Deliverable

A verdict (tight / issues found), the issue list with severities, fixes applied
for anything cheap (docstrings, dead code, missing regression witness), and
stop-and-report for anything structural. Re-run the full gate (fresh `lake
build` + axiom audit) after any fix. Append a review entry to the Status log in
`next-agent-brief-primitives-typedecls-surface.md`.

## Gotchas (inherited; still true)

- MCP `success` is a whole-file flag — trust per-range `items`; retry on
  `timed_out`. Re-grep line numbers after every edit.
- `lean_verify` per-file is an approximation; the fresh-olean `#print axioms`
  is the audit of record.
- Commit trail of the campaign: `c23fb92` (Core fusion + packaging) →
  `3633bae` (InferW A+B) → `caac62d` (C) → `220c2a1` (D) → `d867d2d`
  (showcases) → `29792fc`/`1d2f611` (briefs) → `d2aee37` (lint). Commit your
  review fixes granularly.
