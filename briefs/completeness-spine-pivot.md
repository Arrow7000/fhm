# Spine pivot brief — finish the D2 campaign (start here)

**State @ `ee2cc99`+doc:** step-4 skeleton GREEN (`FHM/Completeness.lean`).
Proved: 8 trivial Infer ctors, COMPLETE-VAR/CTOR/LAMBDA, APP minus one inner
step. Remaining 9 sorries all share ONE blocker ⇒ do the pivot below FIRST,
then they close quickly. Supersedes §3–5 ordering in
`briefs/completeness-restoration.md` (steps 1–3 there are DONE & committed).

## The pivot (mechanical, do as one checkpoint)

Restate the three `Principal` premises from
`TypeOfHM (S₀.onCtx ctx) e τe` to `TypeOfHM (S₀.onCtx ctx).eraseBounds e τe`
(original ANNOTATED term — Pins stay live for lambda/letInAnn/letRec
ceilings; ERASED context — enables IH re-entry at residual-transformed
contexts via kept `TypeOfHM.onSubst_eraseBounds'` + `Subst.onCtx_congr_hm`;
rationale: design memo §4.1.2, APP post-mortem in commit `ee2cc99`).

- Defs + 8 trivial cases: mechanical (they never touch ctx content).
- VAR/CTOR: rework against erased schemes. Net SIMPLER: drop the
  conj-renaming dance on the scheme; inversion yields erased-scheme σE =
  eraseBounds(S₀.onPolyTy polyTy); pinning via NEW helper
  "InstantiatesTo respects AgreesHM-of-schemes" (∃-transfer through
  instantiation; prove once by Ty.rec on InstantiatesBy using
  `Ty.eraseBounds_onTy_erase`/`AgreesHM` congruences), then zip-residual as
  before with freshness vs τe.
- LAMBDA: body-context construction referenced raw ctx — rebuild via
  erase-context equality (`onCtx_congr_hm`) + `onSubst_eraseBounds'` for both
  seed cases; `.some` stays easy (Pins live), `.none` keeps the swap dodge.
- APP: keep everything; discharge inner `COMPLETE-APP-RESIDUAL` by
  ih-re-entry at `(R_f.onCtx …).eraseBounds` — direct under the pivot.
- LETIN/LETINANN/MATCH(branches)/LETREC(group): farm one-per-subagent after
  pivot lands; premises now transport, so each is a standard inversion +
  sub-IH chain. LETREC needs MonoTyped-cofinite lift (old
  `genGroup_generalizes_renameG` ideas; PolyTyped vacuous post-cut).

## Invariants (do not relitigate)
- AgreesHM pinning (§1 of restoration brief) ✓ decided.
- Given-derivation architecture (h : Infer as hypothesis) ✓ decided;
  construct-style is unavailable under erasure.
- Zero errors = green; commit only then. One case per subagent
  (deepseek-flash, background), assigned-marker discipline, no lake build.
- Audit `#print axioms` on newly proved thms each checkpoint
  ([propext, Classical.choice, Quot.sound] only).

## Capstones after spine (step 5)
complete_instance / principal / iff_typeable / typecheck_iff /
principalType_principal — thin projections of `principals_mut` components,
then docs (README proven-theorems section, memo §5.3 addendum).
