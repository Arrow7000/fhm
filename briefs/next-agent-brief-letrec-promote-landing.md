# Landed — the letRec promotion (Stage 1)

**Status: LANDED.** `Expr.letRecElabOut` is wired, sound, and axiom-clean; `lake build` is green
(831 jobs) with `FHM.InferW`, `FHM.SurfaceBridge`, and `FHM.Headlines` all sorry-free. Committed as
`f252fab` ("Land letRec promotion (Stage 1)").

Companion doc: `briefs/complexity-budget.md` (the §Status section is the authoritative plan).

## What landed

- `FHM/LetRecPromote.lean` (new, in lakefile roots, imports `FHM.Core`, imported by `FHM.InferW`).
  The promotion + transport metatheory, axiom-clean: `promoteScheme`/`promoteSpecs`/`promoteAnns`,
  `retargetVars`/`retargetStored`/`bodyExtend`, `retarget_transport`/`retarget_untransport`,
  `monoTyped_to_polyTyped`/`polyTyped_to_monoTyped`, `bodyScheme_weaken`, `retargetStored_openTyVars`,
  plus the Path-R commutes.
- `FHM/InferW.lean`: `Expr.letRecElabOut` + `allNone`, wired into `Infer.letRec` and `inferCore`.
  All-`none` group → promoted `.letRec` node; mixed group → `Expr.letRecElab` (unchanged). The
  `...Out` mirrors (`mem_tyFreeVars`, `tyBvarBounded`, `eraseBounds`, `substTyFvars`,
  `UserAnnsCopied`) are proved; `Infer.eOut_avoid`/`eOut_tyBvarBounded`/`Infer.sound` are wired;
  `Expr.letRecElabOut_sound` is proved in **both** branches.
- `FHM/SurfaceBridge.lean` (NOT in the original plan, but required for a green `lake build`): the
  `Infer.letRec` rewire had left `infer_preserves_AllMatchesExhaustive`'s letRec case calling the old
  `letRecElab_AllMatchesExhaustive`. Fixed by adding `letRecElabOut_AllMatchesExhaustive` (a
  `by_cases allNone anns` mirror) + `AllMatchesExhaustive.retargetStored`/`.bodyExtend` preservation
  lemmas, and rewiring the one call site.

## THE correction to the previous plan (important for anyone reading old notes)

The prior plan proved the all-mono branch of `Expr.letRecElabOut_sound` via
`monoTyped_to_polyTyped` + `TypeOfElabHM.onSubst_fixed` + `openTyVars_closeTyVars_self`, and flagged
an "open design question" about adding `hG_bs : ∀ g ∈ G, ∀ e ∈ bs, g ∉ e.tyFreeVars`. **That plan
was wrong, and `hG_bs` is false**: the gen pool genuinely occurs in the solved bindings —
`let f = id in f` elaborates `f`'s binding to `.var id [fvar a]` with `a ∈ G`. So `G` does *not*
avoid the bindings.

The correct proof:

- The empty-pool → pool-`G` bridge **renames the term** (`TypeOfElabHM.onSubst`, NOT `onSubst_fixed`),
  so `bs[k].substTyFvars (G.zip (Ys.map fvar))` is typed at `renameG G Ys τ`.
- `hpoly'` is built **directly via `retarget_transport`**, not `monoTyped_to_polyTyped` (whose
  `MonoTyped` premise fixes the term and so is the wrong abstraction here).
- The close/reopen round-trip uses `openTyVars_closeTyVars_rename_of_fresh` (the *rename*), not
  `openTyVars_closeTyVars_self` (the identity).

Net effect: no signature change to `letRecElabOut_sound`, no `Infer.sound` call-site change, no
`hG_bs` anywhere.

## Remaining (future work, NOT part of this landing)

**Part 3** — the faithfulness corollary `Decorates e e' → TypeOfElabHM ctx e' τ → TypeOfHM ctx e τ`
replacing `Infer.sourceSound`'s structural cases (all-mono letRec via `polyTyped_to_monoTyped`; the
mixed case keeps `TypeOfHM.letRec_of_emptyPool`). This is what converts elaboration-shape-preservation
into the §2.2 payoff (sourceSound as a corollary, not a second induction). Not started.

Note the honest scope: Stage 1 makes the elaboratum shape-preserving for **all-mono** groups only;
mixed groups still use the Λ-outside `letRecElab`, so `Infer.sourceSound` is still a full second
induction and `letRecElab` is not deleted. The near term is net-additive (~4.9k lines). The deletion
and the sourceSound collapse remain contingent on Part 3, and on the Option-B mixed-group promotion
(`complexity-budget.md` §Status) which is open research.

## Verification notes (how we know it's sound, not just green)

- `lake build` green: 831 jobs.
- `Expr.letRecElabOut_sound` and `SurfaceBridge.infer_preserves_AllMatchesExhaustive` are both
  `#print axioms`-clean (`propext`, `Classical.choice`, `Quot.sound` — no `sorryAx`).
- The all-mono sound core was first spiked in a scratch file (`import FHM.LetRecPromote` + `FHM.InferW`)
  and verified axiom-clean before porting.
