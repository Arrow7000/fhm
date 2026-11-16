import EPL2.Spec.Unify
import EPL2.Spec.Store
import EPL2.Spec.Declarative

/-!
# Inference of an explicit let

The one case of `inferAt_spec` with real content. It is split in two:

* `RhsChecked` — what checking the right-hand side against the annotation
  establishes (`rhsChecked`): the same sound/principal pair as `InferPost`,
  for the *completed annotation* `completed`, plus that the store stays
  anchored.
* What the level check on `completed` then decides: if every metavariable of
  `completed` is at or below the outer depth, the completion is `Determined`
  (`RhsChecked.determined`) and the bound scheme realizes as the completed
  scheme (`RhsChecked.realize_scheme`); otherwise no completion is
  (`RhsChecked.undetermined`).

Throughout: `k` is the let's depth, `store` the store before the let,
`store'` the store after unifying the right-hand side's type with the
allocated annotation, `completed` the annotation resolved through `store'`.
-/

namespace EPL2

/-- The outcome of checking an explicit let's right-hand side against its
annotation. -/
structure RhsChecked (sig : Signature) (k : Nat) (ctx : Ctx Nat) (ann : PolyAnn Template)
    (rhs : Source) (store : MStore) (rhsElab : Expr InfTy) (completed : InfTy)
    (store' : MStore) : Prop where
  safe : store'.Safe
  grows : store.length ≤ store'.length
  levels : ∀ id < store.length, store'.levelOf id ≤ store.levelOf id
  completedWF : completed.WF (k + ann.arity)
  completedAllocated : completed.Allocated store'
  completedLevels : completed.LevelBounded store' (k + ann.arity)
  completedUnsolved : ∀ id ∈ completed.vars, store'.lookup id = none
  elabAllocated : ∀ a ∈ rhsElab.anns, a.Allocated store'
  anchored : ∀ start level, level < k → start ≤ store.length →
    store.Anchored start level → store'.Anchored start level
  /-- With at least one binder, everything the right-hand side allocated
  started above `k`. -/
  anchoredSelf : 0 < ann.arity → store'.Anchored store.length k
  sound : ∀ valuation, store'.Models valuation →
    store.Models valuation ∧ ann.body.Matches (completed.realize valuation) ∧
      Elaborates sig (k + ann.arity) (ctx.realize valuation) rhs (rhsElab.realize valuation)
        (completed.realize valuation)
  principal : ∀ valuation, store.Models valuation →
    ∀ elaboration ty, ann.body.Matches ty → ty.WF (k + ann.arity) →
      Typing sig (k + ann.arity) (ctx.realize valuation) rhs elaboration ty →
      ∃ extended, store'.Models extended ∧ Agree store.length valuation extended ∧
        rhsElab.realize extended = elaboration ∧ completed.realize extended = ty

/-- **Proof guidance.** Write `inner := k + ann.arity`,
`(annTy, store₁) := store.allocate inner ann.body`.
* invariants: `MStore.allocate_wf`, `MStore.append_unsolved_*`, the fields of
  `rhsPost`, `MStore.unify_safe`/`unify_length`/`unify_levelOf_le`,
  `MStore.apply_wf`/`apply_allocated`/`apply_vars_unsolved`.
* `anchored`: `Anchored.append_unsolved` (the new metavariables are at
  `inner > level`), `rhsPost.anchored`, `MStore.unify_anchored`.
  `anchoredSelf`: the same, starting from `Anchored.of_length`.
* `sound`: `MStore.unify_sound`, `rhsPost.sound`,
  `MStore.models_append_unsolved`, `Models.realize_apply`,
  `MStore.allocate_sound`.
* `principal`: `MStore.allocate_principal`, `Ctx.realize_congr` (the context
  does not see the new metavariables), `rhsPost.principal`,
  `Ty.realize_congr` (neither does `annTy` see the right-hand side's), then
  `MStore.unify_complete`, whose result is `store'` by `unified`. -/
theorem rhsChecked {sig : Signature} {ann : PolyAnn Template} {rhsResult : Inferred}
    (pre : InferPre k ctx store) (annWF : ann.body.WF (k + ann.arity))
    (rhsPost : InferPost sig (k + ann.arity) ctx rhs
      (store.allocate (k + ann.arity) ann.body).2 rhsResult)
    (unified : rhsResult.store.unify rhsResult.ty
      (store.allocate (k + ann.arity) ann.body).1 = some store') :
    RhsChecked sig k ctx ann rhs store rhsResult.elaboration
      (store'.apply (store.allocate (k + ann.arity) ann.body).1) store' := by
  sorry

namespace RhsChecked

/-- The completed annotation, closed, completes the annotation; reopening it
gives the completed annotation back. Proof: the realization is well-formed at
`k + ann.arity` (`Ty.realize_wf`, `Models.image_wf`, `completedLevels`); then
`Scheme.closeRigids_wf`, `Scheme.skolemize_closeRigids`. -/
theorem completes {sig : Signature} {ann : PolyAnn Template}
    (checked : RhsChecked sig k ctx ann rhs store rhsElab completed store')
    (models : store'.Models valuation) :
    ann.Completes k ⟨ann.arity, (completed.realize valuation).closeRigids k ann.arity⟩ ∧
      (⟨ann.arity, (completed.realize valuation).closeRigids k ann.arity⟩ : Scheme Empty).skolemize k =
        completed.realize valuation := by
  sorry

/-- When the completed annotation's metavariables are all outer, the scheme
bound in the body realizes as the completed scheme
(`Scheme.realize_closeRigids`). -/
theorem realize_scheme {sig : Signature} {ann : PolyAnn Template}
    (checked : RhsChecked sig k ctx ann rhs store rhsElab completed store')
    (outer : completed.LevelBounded store' k) (models : store'.Models valuation) :
    (⟨ann.arity, completed.closeRigids k ann.arity⟩ : Scheme Nat).realize valuation =
      ⟨ann.arity, (completed.realize valuation).closeRigids k ann.arity⟩ := by
  sorry

/-- When the completed annotation's metavariables are all outer, the
completion is determined.

Proof: if `ann.arity = 0`, the left disjunct. Otherwise take another
completion `other` whose generic instance types the right-hand side.
`checked.principal` (from `valuation`, a model of `store` by
`checked.sound`) gives a model `extended` of `store'` that agrees with
`valuation` before `store.length` and realizes `completed` as
`other.skolemize k`. By `checked.anchoredSelf` and `MStore.Anchored.agree`
the two models agree on every metavariable at or below `k`, hence on those
of `completed` (`outer`, `Ty.bind_congr`). So `other.skolemize k =
completed.realize valuation`, and `Scheme.closeRigids_skolemize` recovers
`other`. -/
theorem determined {sig : Signature} {ann : PolyAnn Template}
    (checked : RhsChecked sig k ctx ann rhs store rhsElab completed store')
    (outer : completed.LevelBounded store' k) (models : store'.Models valuation) :
    Determined sig k (ctx.realize valuation) ann rhs
      ⟨ann.arity, (completed.realize valuation).closeRigids k ann.arity⟩ := by
  sorry

/-- When some metavariable `?m` of the completed annotation is still above
the outer depth, no completion is determined: it could equally be a binder.

Proof: `scheme.arity = ann.arity`. If it is 0, `completedLevels` contradicts
`inner`. Otherwise `checked.principal` gives a model `extended` of `store'`
realizing `completed` as `scheme.skolemize k`;
`MStore.Models.exists_different` gives a model `updated` that differs at
`?m` (unsolved by `completedUnsolved`) and nowhere else among the unsolved
metavariables, so by `MStore.Models.agree_below` the two agree on every
metavariable at or below `k`, and realize the context alike
(`Ctx.realize_congr_levels`; the context is at or below `k` in `store'` by
`pre.ctxLevels`, `pre.ctxAllocated` and `checked.levels`). `checked.sound`
for `updated` and `completes` give a completion that types the right-hand
side (`Elaborates.typing`), so by the `Determined` hypothesis it is `scheme`;
then `completed.realize updated = completed.realize extended`, and
`Ty.realize_eq_vars` contradicts the difference at `?m`. -/
theorem undetermined {sig : Signature} {ann : PolyAnn Template}
    (pre : InferPre k ctx store)
    (checked : RhsChecked sig k ctx ann rhs store rhsElab completed store')
    (inner : ¬ completed.LevelBounded store' k) (models : store.Models valuation)
    (completes : ann.Completes k scheme)
    (typing : Typing sig (k + scheme.arity) (ctx.realize valuation) rhs rhsElab'
      (scheme.skolemize k)) :
    ¬ Determined sig k (ctx.realize valuation) ann rhs scheme := by
  sorry

end RhsChecked

/-- The explicit-let case of `inferAt_spec`.

**Proof guidance.** First state and prove (by `rfl` or `simp [inferAt]`) an
equation that unfolds `inferAt` on `.letIn (some ann) rhs body` into nested
`if`/`match`/`Option.bind`, and split along it:
* annotation out of scope: no completion exists (`Template.Matches.wf` with
  `Scheme.skolemize_wf` and `Completes.arity_eq`);
* right-hand side fails: `rhsSpec` at `pre.deeper` extended by
  `MStore.append_unsolved_safe`, with a model from `MStore.allocate_principal`;
* unification fails: `rhsPost.principal` and `MStore.unify_complete`;
* level check fails: `RhsChecked.undetermined`;
* body fails or succeeds: `bodySpec` at the context extended by the closed
  scheme (`Scheme.closeRigids_wf`, `Ty.vars_closeRigids`, the level check),
  using `RhsChecked.realize_scheme`, `completes`, `determined` for soundness
  and `checked.principal` for principality. -/
theorem inferAt_spec_letPoly {sig : Signature} {ann : PolyAnn Template} {rhs body : Source}
    (rhsSpec : ∀ k ctx store, InferPre k ctx store → InferSpec sig k ctx rhs store)
    (bodySpec : ∀ k ctx store, InferPre k ctx store → InferSpec sig k ctx body store)
    (pre : InferPre k ctx store) :
    InferSpec sig k ctx (.letIn (some ann) rhs body) store := by
  sorry

end EPL2
