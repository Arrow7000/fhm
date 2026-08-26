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

## Addendum (2026-08-26, pivot checkpoint): premises are erased-context AND erased-term

Supersedes the "original ANNOTATED term" clause above. The pivot premise is

    TypeOfHM (S₀.onCtx ctx).eraseBounds e.eraseBounds τe   (+ erased branches/bindings
    in InferBranches.Principal / InferRecGroup.Principal)

Why the annotated-term clause is unsatisfiable: every sub-IH re-entry must SUPPLY
its premise at the residual-transformed context. An annotated-term premise cannot
be manufactured there — a *specific-type* coercion into erased contexts dies on
decorated lambda pins (Option.Pins is structural equality), and an ∃-type coercion
dies on letIn-cofinite / match-result-uniformity / letRec-MonoTyped specificity.
Dual-premise hedges just move the impossibility into the call sites.

Why this is still principled: Expr.eraseBounds MAPS annotations (ann.map), so Pins
survive at erase level (λ(x : BL 3 5 Int) still pins the declarative binder to
List Int) — which is all AgreesHM-level conclusions consume. This is memo §4.1.2's
"pure HM on shapes" applied symmetrically to hypotheses; conclusions were already
erase-level. Every IH premise is now manufacturable from existing lemmas:
TypeOfHM.eraseBounds_of, TypeOfHM.onSubst_eraseBounds_fixed, Subst.onCtx_congr_hm
(the last gives COMPLETE-APP-RESIDUAL by context identity: (S₀.onCtx ctx).eraseBounds
= ((S₁ ++ R_f).onCtx ctx).eraseBounds via hagf, types untouched).

New lemmas added in FHM/Completeness.lean §4 preamble:
- Ty.eraseBounds_rename: erasure commutes with α-renaming (block-swap dance works
  verbatim at erased contexts).
- InstantiatesBy.erase_agrees (+ private forall2 helper): backward ∃-transfer —
  InstantiatesBy ts (erase B) τ lifts to InstantiatesBy ts B τ₂ with AgreesHM τ τ₂.
  NOTE: result is AgreesHM-related, NOT equal (a decorated witness can instantiate
  the erased .bvar verbatim where the raw body yields a bare-List shape).
- AgreesHM.arrow / AgreesHM.customTy / AgreesHM.customTy_singleton_bl congruences.

Assembly notes for the case proofs:
- VAR/CTOR keep the block-swap architecture; inversion of the erased premise yields
  σE = PolyTy.eraseBounds scheme directly (Env.eraseBounds_getElem? /
  CtorEnv.eraseBounds_get?); apply erase_agrees, then zip-residual as before; final
  agreement goes through erase-commutation on the fvar-valued back-list.
- LAMBDA keeps the swap dodge; body premise = TypeOfHM.onSubst_eraseBounds_fixed
  (swapSubst) (eraseBounds_of hbodyD); context twin proved entrywise; feed
  τe := rename sw (erase bodyTy) and normalize htyb via herase_swap.
- Seed-.some: paramTyD = erase paramTy from the mapped pin; body premise =
  eraseBounds_of hbodyD directly (context matches (S₀.onCtx Γ'').eraseBounds by
  K-fixing of the pinned scheme + erasure idempotence).
