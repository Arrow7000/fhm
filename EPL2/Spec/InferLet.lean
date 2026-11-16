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

/-- Contexts are realized by their metavariables only. -/
theorem Ctx.realize_congr_vars {ctx : Ctx Nat} {first second : Valuation}
    (agree : ∀ scheme ∈ ctx, ∀ id ∈ scheme.body.vars, first id = second id) :
    ctx.realize first = ctx.realize second := by
  induction ctx with
  | nil => rfl
  | cons scheme rest ih =>
      simp only [Ctx.realize, List.map_cons]
      congr 1
      · simp only [Scheme.realize, Scheme.bind]
        congr 1
        exact Ty.bind_congr (fun id hid => agree scheme (by simp) id hid)
      · exact ih (fun scheme hscheme => agree scheme (by simp [hscheme]))

/-- The level check of `inferAt` is `Ty.LevelBounded`. -/
theorem levelCheck_iff {store : MStore} {ty : InfTy} {k : Nat} :
    (ty.vars.all (store.levelOf · ≤ k) = true) ↔ ty.LevelBounded store k := by
  rw [List.all_eq_true]
  constructor
  · intro h id hid
    have := h id hid
    simpa using this
  · intro h id hid
    simpa using h id hid

/-- A run one explicit let deeper sees the context after allocating the
annotation. -/
theorem InferPre.allocate_deeper (pre : InferPre k ctx store) (ann : PolyAnn Template) :
    InferPre (k + ann.arity) ctx (store.allocate (k + ann.arity) ann.body).2 := by
  have hdeep : InferPre (k + ann.arity) ctx store := pre.deeper (by omega)
  refine hdeep.extend ?_ ?_ ?_
  · rw [MStore.allocate_snd]
    exact MStore.append_unsolved_safe pre.safe
  · rw [MStore.allocate_snd]
    simp
  · intro id hid
    rw [MStore.allocate_snd, MStore.append_unsolved_levelOf, if_pos hid]

/-- Unfolding of `inferAt` on an explicit let. -/
theorem inferAt_letPoly (sig : Signature) (k : Nat) (ctx : Ctx Nat)
    (ann : PolyAnn Template) (rhs body : Source) (store : MStore) :
    inferAt sig k ctx (.letIn (some ann) rhs body) store = (do
      let inner := k + ann.arity
      if ¬ ann.body.WF inner then none
      let (annTy, store) := store.allocate inner ann.body
      let rhsResult ← inferAt sig inner ctx rhs store
      let store ← rhsResult.store.unify rhsResult.ty annTy
      let completed := store.apply annTy
      if ¬ completed.vars.all (store.levelOf · ≤ k) then none
      let scheme : Scheme Nat := ⟨ann.arity, completed.closeRigids k ann.arity⟩
      let bodyResult ← inferAt sig k (scheme :: ctx) body store
      some ⟨bodyResult.ty,
        .letIn (some ⟨ann.arity, completed⟩) rhsResult.elaboration bodyResult.elaboration,
        bodyResult.store⟩) := by
  rfl

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

/-- The context of the body: the completed annotation's closed scheme, above
the original context. -/
theorem RhsChecked.bodyPre {sig : Signature} {ann : PolyAnn Template}
    (pre : InferPre k ctx store)
    (checked : RhsChecked sig k ctx ann rhs store rhsElab completed store')
    (outer : completed.LevelBounded store' k) :
    InferPre k (⟨ann.arity, completed.closeRigids k ann.arity⟩ :: ctx) store' := by
  have hschemeWF : (⟨ann.arity, completed.closeRigids k ann.arity⟩ : Scheme Nat).WF k :=
    Scheme.closeRigids_wf checked.completedWF
  have hschemeAlloc :
      (⟨ann.arity, completed.closeRigids k ann.arity⟩ : Scheme Nat).body.Allocated store' := by
    intro id hid
    rw [Ty.vars_closeRigids] at hid
    exact checked.completedAllocated id hid
  have hschemeLevels :
      (⟨ann.arity, completed.closeRigids k ann.arity⟩ : Scheme Nat).body.LevelBounded store' k := by
    intro id hid
    rw [Ty.vars_closeRigids] at hid
    exact outer id hid
  have hpre : InferPre k ctx store' := pre.extend checked.safe checked.grows checked.levels
  refine ⟨checked.safe, ?_, ?_, ?_⟩
  · intro sch hsch
    rcases List.mem_cons.mp hsch with rfl | hsch
    · exact hschemeWF
    · exact hpre.ctxWF sch hsch
  · intro sch hsch
    rcases List.mem_cons.mp hsch with rfl | hsch
    · exact hschemeAlloc
    · exact hpre.ctxAllocated sch hsch
  · intro sch hsch
    rcases List.mem_cons.mp hsch with rfl | hsch
    · exact hschemeLevels
    · exact hpre.ctxLevels sch hsch

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
  have store₁Safe : (store.allocate (k + ann.arity) ann.body).2.Safe := by
    rw [MStore.allocate_snd]
    exact MStore.append_unsolved_safe pre.safe
  obtain ⟨annTyWF, annTyAlloc₁, annTyFresh⟩ :=
    MStore.allocate_wf (store := store) (template := ann.body) annWF
  have hlen₁ : (store.allocate (k + ann.arity) ann.body).2.length =
      store.length + ann.body.vars.dedup.length := by
    rw [MStore.allocate_snd]
    simp
  have grow₁ : store.length ≤ (store.allocate (k + ann.arity) ann.body).2.length := by
    omega
  have annTyAllocRhs :
      (store.allocate (k + ann.arity) ann.body).1.Allocated rhsResult.store := by
    intro id hid
    have h := annTyAlloc₁ id hid
    have := rhsPost.grows
    omega
  have annTyAlloc' : (store.allocate (k + ann.arity) ann.body).1.Allocated store' := by
    intro id hid
    have h := annTyAlloc₁ id hid
    have hlen : store'.length = rhsResult.store.length := MStore.unify_length unified
    have := rhsPost.grows
    omega
  have annTyLevels' :
      (store.allocate (k + ann.arity) ann.body).1.LevelBounded store' (k + ann.arity) := by
    intro id hid
    have hfresh := annTyFresh id hid
    have hid₁ : id < (store.allocate (k + ann.arity) ann.body).2.length :=
      annTyAlloc₁ id hid
    have hlev₁ : (store.allocate (k + ann.arity) ann.body).2.levelOf id = (k + ann.arity) := by
      have hidCount : id < store.length + ann.body.vars.dedup.length := by
        have h := hid₁
        rw [hlen₁] at h
        exact h
      rw [MStore.allocate_snd, MStore.append_unsolved_levelOf]
      rw [if_neg (by omega : ¬ id < store.length), if_pos hidCount]
    calc store'.levelOf id ≤ rhsResult.store.levelOf id := MStore.unify_levelOf_le unified id
      _ ≤ (store.allocate (k + ann.arity) ann.body).2.levelOf id := rhsPost.levels id hid₁
      _ = (k + ann.arity) := hlev₁
  have store'Safe : store'.Safe :=
    MStore.unify_safe rhsPost.safe rhsPost.tyAllocated annTyAllocRhs unified
  have completedWF :
      (store'.apply (store.allocate (k + ann.arity) ann.body).1).WF (k + ann.arity) :=
    (MStore.apply_wf store'Safe annTyWF annTyLevels').1
  have completedLevels :
      (store'.apply (store.allocate (k + ann.arity) ann.body).1).LevelBounded store'
        (k + ann.arity) :=
    (MStore.apply_wf store'Safe annTyWF annTyLevels').2
  refine ⟨store'Safe, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- grows
    have hlen : store'.length = rhsResult.store.length := MStore.unify_length unified
    have h₂ : (store.allocate (k + ann.arity) ann.body).2.length ≤
        rhsResult.store.length := rhsPost.grows
    rw [hlen₁] at h₂
    omega
  · -- levels
    intro id hid
    have hle : store'.levelOf id ≤ rhsResult.store.levelOf id :=
      MStore.unify_levelOf_le unified id
    have hid₁ : id < (store.allocate (k + ann.arity) ann.body).2.length := by
      rw [hlen₁]
      omega
    have hrhs : rhsResult.store.levelOf id ≤
        (store.allocate (k + ann.arity) ann.body).2.levelOf id := rhsPost.levels id hid₁
    have hsame : (store.allocate (k + ann.arity) ann.body).2.levelOf id = store.levelOf id := by
      rw [MStore.allocate_snd, MStore.append_unsolved_levelOf, if_pos hid]
    omega
  · -- completedWF
    exact completedWF
  · -- completedAllocated
    exact MStore.apply_allocated store'Safe annTyAlloc'
  · -- completedLevels
    exact completedLevels
  · -- completedUnsolved
    exact MStore.apply_vars_unsolved store'Safe
  · -- elabAllocated
    intro a ha
    have h := rhsPost.elabAllocated a ha
    have hlen : store'.length = rhsResult.store.length := MStore.unify_length unified
    intro id hid
    have := h id hid
    omega
  · -- anchored
    intro start level hlevel hstart hanch
    have hinner : level < (k + ann.arity) := by omega
    have h₁ : (store.allocate (k + ann.arity) ann.body).2.Anchored start level := by
      rw [MStore.allocate_snd]
      exact MStore.Anchored.append_unsolved hanch hinner
    have h₂ : rhsResult.store.Anchored start level :=
      rhsPost.anchored start level hinner (by omega) h₁
    exact MStore.unify_anchored h₂ unified
  · -- anchoredSelf
    intro harity
    have hinner : k < (k + ann.arity) := by omega
    have h₁ : (store.allocate (k + ann.arity) ann.body).2.Anchored store.length k := by
      rw [MStore.allocate_snd]
      exact MStore.Anchored.append_unsolved (MStore.Anchored.of_length store k) hinner
    have h₂ : rhsResult.store.Anchored store.length k :=
      rhsPost.anchored store.length k hinner (by omega) h₁
    exact MStore.unify_anchored h₂ unified
  · -- sound
    intro valuation hmodels
    have hunifySound := MStore.unify_sound unified hmodels
    have hrhsModels : rhsResult.store.Models valuation := hunifySound.1
    have htyEq : rhsResult.ty.realize valuation =
        (store.allocate (k + ann.arity) ann.body).1.realize valuation := hunifySound.2
    have hrhsSound := rhsPost.sound valuation hrhsModels
    have hstore₁Models :
        (store.allocate (k + ann.arity) ann.body).2.Models valuation := hrhsSound.1
    have helab : Elaborates sig (k + ann.arity) (ctx.realize valuation) rhs
        (rhsResult.elaboration.realize valuation) (rhsResult.ty.realize valuation) := hrhsSound.2
    have hstoreModels : store.Models valuation := by
      rw [MStore.allocate_snd] at hstore₁Models
      exact (MStore.models_append_unsolved.mp hstore₁Models).1
    have hmatch : ann.body.Matches
        ((store'.apply (store.allocate (k + ann.arity) ann.body).1).realize valuation) := by
      rw [MStore.Models.realize_apply hmodels]
      exact MStore.allocate_sound store (k + ann.arity) ann.body valuation
    refine ⟨hstoreModels, hmatch, ?_⟩
    rw [MStore.Models.realize_apply hmodels, ← htyEq]
    exact helab
  · -- principal
    intro valuation hmodels elaboration ty hfits htyWF htyping
    obtain ⟨extended₀, h₀Models, h₀Agree, h₀AnnTy⟩ :=
      MStore.allocate_principal pre.safe hmodels hfits htyWF
    have hctxEq : ctx.realize valuation = ctx.realize extended₀ :=
      Ctx.realize_congr pre.ctxAllocated h₀Agree
    have htyping₀ : Typing sig (k + ann.arity) (ctx.realize extended₀) rhs elaboration ty := by
      rw [← hctxEq]
      exact htyping
    obtain ⟨extended, hExtModels, hExtAgree, hElab, hTy⟩ :=
      rhsPost.principal extended₀ h₀Models elaboration ty htyping₀
    have hAnnTyExt : (store.allocate (k + ann.arity) ann.body).1.realize extended = ty := by
      have hcongr : (store.allocate (k + ann.arity) ann.body).1.realize extended₀ =
          (store.allocate (k + ann.arity) ann.body).1.realize extended :=
        Ty.realize_congr annTyAlloc₁ hExtAgree
      rw [← hcongr, h₀AnnTy]
    have htyUnify : rhsResult.ty.realize extended =
        (store.allocate (k + ann.arity) ann.body).1.realize extended := by
      rw [hTy, hAnnTyExt]
    obtain ⟨result, hresult, hresultModels⟩ :=
      MStore.unify_complete rhsPost.safe rhsPost.tyAllocated annTyAllocRhs hExtModels htyUnify
    have hstore'Models : store'.Models extended := by
      rw [unified] at hresult
      have hEq : store' = result := Option.some.inj hresult
      rw [hEq]
      exact hresultModels
    have hAgree : Agree store.length valuation extended := by
      intro id hid
      rw [h₀Agree id hid]
      exact hExtAgree id (by omega)
    have hCompleted :
        (store'.apply (store.allocate (k + ann.arity) ann.body).1).realize extended = ty := by
      rw [MStore.Models.realize_apply hstore'Models, hAnnTyExt]
    exact ⟨extended, hstore'Models, hAgree, hElab, hCompleted⟩

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
  have images : ∀ id ∈ completed.vars, (valuation id).WF (k + ann.arity) := by
    intro id hid
    have hwf : (valuation id).WF (store'.levelOf id) :=
      MStore.Models.image_wf models (checked.completedAllocated id hid)
    exact Ty.Scoped.mono hwf (checked.completedLevels id hid) (Nat.zero_le 0)
  have tyWF : (completed.realize valuation).WF (k + ann.arity) :=
    Ty.realize_wf checked.completedWF images
  have hskel :
      (⟨ann.arity, (completed.realize valuation).closeRigids k ann.arity⟩ : Scheme Empty).skolemize k =
        completed.realize valuation :=
    Scheme.skolemize_closeRigids tyWF
  refine ⟨⟨rfl, ?_, ?_⟩, hskel⟩
  · exact Scheme.closeRigids_wf tyWF
  · rw [hskel]
    exact (checked.sound valuation models).2.1

/-- When the completed annotation's metavariables are all outer, the scheme
bound in the body realizes as the completed scheme
(`Scheme.realize_closeRigids`). -/
theorem realize_scheme {sig : Signature} {ann : PolyAnn Template}
    (checked : RhsChecked sig k ctx ann rhs store rhsElab completed store')
    (outer : completed.LevelBounded store' k) (models : store'.Models valuation) :
    (⟨ann.arity, completed.closeRigids k ann.arity⟩ : Scheme Nat).realize valuation =
      ⟨ann.arity, (completed.realize valuation).closeRigids k ann.arity⟩ := by
  have images : ∀ id ∈ completed.vars, (valuation id).WF k := by
    intro id hid
    have hwf : (valuation id).WF (store'.levelOf id) :=
      MStore.Models.image_wf models (checked.completedAllocated id hid)
    exact Ty.Scoped.mono hwf (outer id hid) (Nat.zero_le 0)
  simp only [Scheme.realize, Scheme.bind, Ty.realize]
  congr 1
  exact Ty.closeRigids_bind images

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
  unfold Determined
  by_cases harity : ann.arity = 0
  · left
    simp [harity]
  · right
    intro other otherElab completes typing
    have hsound := checked.sound valuation models
    have hstoreModels : store.Models valuation := hsound.1
    have hskelWF : (other.skolemize k).WF (k + ann.arity) := by
      rw [← completes.arity_eq]
      exact Scheme.skolemize_wf completes.wf
    have typing' : Typing sig (k + ann.arity) (ctx.realize valuation) rhs otherElab
        (other.skolemize k) := by
      rw [← completes.arity_eq]
      exact typing
    obtain ⟨extended, extModels, agree, _hrhs, hcompleted⟩ :=
      checked.principal valuation hstoreModels otherElab (other.skolemize k)
        completes.body_matches hskelWF typing'
    have hanch : store'.Anchored store.length k :=
      checked.anchoredSelf (by omega)
    have hagree := MStore.Anchored.agree checked.safe hanch models extModels agree
    have hval : ∀ id ∈ completed.vars, valuation id = extended id :=
      fun id hid => hagree id (checked.completedAllocated id hid) (outer id hid)
    have hreal : completed.realize valuation = completed.realize extended :=
      Ty.bind_congr hval
    have hreal' : completed.realize valuation = other.skolemize k := by
      rw [hreal, hcompleted]
    have hbodyEq : other.body = (completed.realize valuation).closeRigids k ann.arity := by
      rw [← Scheme.closeRigids_skolemize completes.wf]
      rw [← hreal', completes.arity_eq]
    cases other with
    | mk oa ob =>
      simp only [Scheme.mk.injEq]
      exact ⟨completes.arity_eq, hbodyEq⟩

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
  intro hdet
  have hbad : ∃ id, id ∈ completed.vars ∧ ¬ store'.levelOf id ≤ k := by
    by_contra h
    apply inner
    intro id hid
    by_contra hle
    exact h ⟨id, hid, hle⟩
  obtain ⟨id, hid, hlev⟩ := hbad
  have hunsolved : store'.lookup id = none := checked.completedUnsolved id hid
  have hallocated : id < store'.length := checked.completedAllocated id hid
  have htyping' : Typing sig (k + ann.arity) (ctx.realize valuation) rhs rhsElab'
      (scheme.skolemize k) := by
    rw [← completes.arity_eq]
    exact typing
  have hskelWF : (scheme.skolemize k).WF (k + ann.arity) := by
    rw [← completes.arity_eq]
    exact Scheme.skolemize_wf completes.wf
  obtain ⟨extended, extModels, agree, _hrhs, hcompleted⟩ :=
    checked.principal valuation models rhsElab' (scheme.skolemize k)
      completes.body_matches hskelWF htyping'
  obtain ⟨updated, updModels, hdiff, hsame⟩ :=
    MStore.Models.exists_different checked.safe extModels hallocated hunsolved
  have hbel : ∀ m, store'.levelOf m ≤ k → extended m = updated m := by
    apply MStore.Models.agree_below checked.safe extModels updModels
    intro m hmunsolved hmlevel
    have hmne : m ≠ id := by
      intro hmi
      subst hmi
      exact hlev hmlevel
    exact (hsame m hmunsolved hmne).symm
  have hctxEq : ctx.realize updated = ctx.realize valuation := by
    apply Ctx.realize_congr_vars
    intro sch hsch var hvar
    have hvarAlloc : var < store.length := pre.ctxAllocated sch hsch var hvar
    have hvarLevel : store.levelOf var ≤ k := pre.ctxLevels sch hsch var hvar
    have hvarLevel' : store'.levelOf var ≤ k := by
      have := checked.levels var hvarAlloc
      omega
    have e1 : updated var = extended var := (hbel var hvarLevel').symm
    have e2 : valuation var = extended var := agree var hvarAlloc
    rw [e1, e2]
  let other1 : Scheme Empty := ⟨ann.arity, (completed.realize updated).closeRigids k ann.arity⟩
  have hcomplUpd := RhsChecked.completes checked updModels
  have hsoundUpd := checked.sound updated updModels
  have htypingUpd : Typing sig (k + other1.arity) (ctx.realize valuation) rhs
      (rhsElab.realize updated) (other1.skolemize k) := by
    rw [hcomplUpd.2]
    have h := Elaborates.typing hsoundUpd.2.2
    rw [hctxEq] at h
    exact h
  have harity_ne : ann.arity ≠ 0 := by
    intro h0
    apply inner
    intro m hm
    have := checked.completedLevels m hm
    omega
  have hother : other1 = scheme := by
    unfold Determined at hdet
    rcases hdet with h0 | hforall
    · exfalso
      apply harity_ne
      rw [← completes.arity_eq]
      exact h0
    · exact hforall other1 (rhsElab.realize updated) hcomplUpd.1 htypingUpd
  have hupdEqExt : completed.realize updated = completed.realize extended := by
    calc completed.realize updated = other1.skolemize k := hcomplUpd.2.symm
      _ = scheme.skolemize k := by rw [hother]
      _ = completed.realize extended := hcompleted.symm
  exact hdiff (Ty.realize_eq_vars (ty := completed) (first := updated) (second := extended)
    hupdEqExt id hid)

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
  by_cases hann : ann.body.WF (k + ann.arity)
  · -- annotation is in scope
    cases hrhs : inferAt sig (k + ann.arity) ctx rhs
        (store.allocate (k + ann.arity) ann.body).2 with
    | none =>
        have hval : inferAt sig k ctx (.letIn (some ann) rhs body) store = none := by
          rw [inferAt_letPoly]
          simp [hann, hrhs]
        unfold InferSpec
        rw [hval]
        intro valuation hmodels elaboration ty helab
        cases helab with
        | letPoly completes rhsTyping det bodyTyping =>
          rename_i rhsElab scheme bodyElab
          have hskelWF : (scheme.skolemize k).WF (k + ann.arity) := by
            rw [← completes.arity_eq]
            exact Scheme.skolemize_wf completes.wf
          have hpre₁ : InferPre (k + ann.arity) ctx
              (store.allocate (k + ann.arity) ann.body).2 :=
            InferPre.allocate_deeper pre ann
          have spec := rhsSpec (k + ann.arity) ctx _ hpre₁
          unfold InferSpec at spec
          rw [hrhs] at spec
          obtain ⟨extended, extModels, agree, _⟩ :=
            MStore.allocate_principal pre.safe hmodels completes.body_matches hskelWF
          have hrhsElab : Elaborates sig (k + ann.arity) (ctx.realize extended) rhs rhsElab
              (scheme.skolemize k) := by
            have hctx : ctx.realize valuation = ctx.realize extended :=
              Ctx.realize_congr pre.ctxAllocated agree
            rw [← hctx, ← completes.arity_eq]
            exact rhsTyping
          exact spec extended extModels rhsElab (scheme.skolemize k) hrhsElab
    | some rhsResult =>
        cases hunify : rhsResult.store.unify rhsResult.ty
            (store.allocate (k + ann.arity) ann.body).1 with
        | none =>
            have hval : inferAt sig k ctx (.letIn (some ann) rhs body) store = none := by
              rw [inferAt_letPoly]
              simp [hann, hrhs, hunify]
            unfold InferSpec
            rw [hval]
            intro valuation hmodels elaboration ty helab
            cases helab with
            | letPoly completes rhsTyping det bodyTyping =>
              rename_i rhsElab scheme bodyElab
              have hskelWF : (scheme.skolemize k).WF (k + ann.arity) := by
                rw [← completes.arity_eq]
                exact Scheme.skolemize_wf completes.wf
              have hpre₁ : InferPre (k + ann.arity) ctx
                  (store.allocate (k + ann.arity) ann.body).2 :=
                InferPre.allocate_deeper pre ann
              have spec := rhsSpec (k + ann.arity) ctx _ hpre₁
              unfold InferSpec at spec
              rw [hrhs] at spec
              obtain ⟨extended₀, extModels₀, agree₀, hannTy₀⟩ :=
                MStore.allocate_principal pre.safe hmodels completes.body_matches hskelWF
              have htyping₀ : Typing sig (k + ann.arity) (ctx.realize extended₀) rhs rhsElab
                  (scheme.skolemize k) := by
                have hctx : ctx.realize valuation = ctx.realize extended₀ :=
                  Ctx.realize_congr pre.ctxAllocated agree₀
                rw [← hctx, ← completes.arity_eq]
                exact Elaborates.typing rhsTyping
              obtain ⟨extended, extModels, agree, _hElabEq, hTyEq⟩ :=
                spec.principal extended₀ extModels₀ rhsElab (scheme.skolemize k) htyping₀
              obtain ⟨-, annTyAlloc₁, -⟩ :=
                MStore.allocate_wf (store := store) (template := ann.body) hann
              have hannTy : (store.allocate (k + ann.arity) ann.body).1.realize extended =
                  scheme.skolemize k := by
                have hcongr :
                    (store.allocate (k + ann.arity) ann.body).1.realize extended₀ =
                      (store.allocate (k + ann.arity) ann.body).1.realize extended :=
                  Ty.realize_congr annTyAlloc₁ agree
                rw [← hcongr, hannTy₀]
              have annAllocRhs :
                  (store.allocate (k + ann.arity) ann.body).1.Allocated rhsResult.store := by
                intro id hid
                have := annTyAlloc₁ id hid
                have := spec.grows
                omega
              have hUnify : rhsResult.ty.realize extended =
                  (store.allocate (k + ann.arity) ann.body).1.realize extended := by
                rw [hTyEq, hannTy]
              obtain ⟨result, hresult, -⟩ :=
                MStore.unify_complete spec.safe spec.tyAllocated annAllocRhs extModels hUnify
              rw [hunify] at hresult
              cases hresult
        | some store' =>
            by_cases hlevel :
                (store'.apply (store.allocate (k + ann.arity) ann.body).1).LevelBounded store' k
            · -- level check passes, run the body
              cases hbody : inferAt sig k
                  (⟨ann.arity,
                    (store'.apply (store.allocate (k + ann.arity) ann.body).1).closeRigids
                      k ann.arity⟩ :: ctx) body store' with
              | none =>
                  have hval : inferAt sig k ctx (.letIn (some ann) rhs body) store = none := by
                    have hnot : ¬ ∃ x, x ∈
                        (store'.apply (store.allocate (k + ann.arity) ann.body).1).vars ∧
                        k < store'.levelOf x := by
                      rintro ⟨x, hx, hlt⟩
                      exact absurd (hlevel x hx) (by omega)
                    rw [inferAt_letPoly]
                    simp [hann, hrhs, hunify, hnot, hbody]
                  unfold InferSpec
                  rw [hval]
                  intro valuation hmodels elaboration ty helab
                  cases helab with
                  | letPoly completes rhsTyping det bodyTyping =>
                    rename_i rhsElab scheme bodyElab
                    have hpre₁ : InferPre (k + ann.arity) ctx
                        (store.allocate (k + ann.arity) ann.body).2 :=
                      InferPre.allocate_deeper pre ann
                    have spec := rhsSpec (k + ann.arity) ctx _ hpre₁
                    unfold InferSpec at spec
                    rw [hrhs] at spec
                    have rhsPost : InferPost sig (k + ann.arity) ctx rhs
                        (store.allocate (k + ann.arity) ann.body).2 rhsResult := spec
                    have hchecked : RhsChecked sig k ctx ann rhs store rhsResult.elaboration
                        (store'.apply (store.allocate (k + ann.arity) ann.body).1) store' :=
                      rhsChecked pre hann rhsPost hunify
                    obtain ⟨extended, extModels, agree, _hrhs, hcompleted⟩ :=
                      hchecked.principal valuation hmodels rhsElab (scheme.skolemize k)
                        completes.body_matches (by
                          rw [← completes.arity_eq]
                          exact Scheme.skolemize_wf completes.wf) (by
                          rw [← completes.arity_eq]
                          exact Elaborates.typing rhsTyping)
                    have bspec := bodySpec k
                      (⟨ann.arity,
                        (store'.apply (store.allocate (k + ann.arity) ann.body).1).closeRigids
                          k ann.arity⟩ :: ctx) store'
                      (RhsChecked.bodyPre pre hchecked hlevel)
                    unfold InferSpec at bspec
                    rw [hbody] at bspec
                    have hschemeExt :
                        (⟨ann.arity,
                          (store'.apply (store.allocate (k + ann.arity) ann.body).1).closeRigids
                            k ann.arity⟩ : Scheme Nat).realize extended = scheme := by
                      have h := RhsChecked.realize_scheme hchecked hlevel extModels
                      rw [h, hcompleted]
                      have hbodyEq :
                          (scheme.skolemize k).closeRigids k ann.arity = scheme.body := by
                        rw [← completes.arity_eq]
                        exact Scheme.closeRigids_skolemize completes.wf
                      cases scheme with
                      | mk sa sb =>
                        simp only [Scheme.mk.injEq]
                        exact ⟨completes.arity_eq.symm, hbodyEq⟩
                    have hctxExt : ctx.realize extended = ctx.realize valuation :=
                      (Ctx.realize_congr pre.ctxAllocated agree).symm
                    have bodyTyping' : Elaborates sig k
                        (Ctx.realize ((⟨ann.arity,
                          (store'.apply (store.allocate (k + ann.arity) ann.body).1).closeRigids
                            k ann.arity⟩ : Scheme Nat) :: ctx) extended) body bodyElab ty := by
                      rw [Ctx.realize_cons, hschemeExt, hctxExt]
                      exact bodyTyping
                    exact bspec extended extModels bodyElab ty bodyTyping'
              | some bodyResult =>
                  have hval : inferAt sig k ctx (.letIn (some ann) rhs body) store =
                      some ⟨bodyResult.ty,
                        .letIn (some ⟨ann.arity,
                          store'.apply (store.allocate (k + ann.arity) ann.body).1⟩)
                          rhsResult.elaboration bodyResult.elaboration,
                        bodyResult.store⟩ := by
                    have hnot : ¬ ∃ x, x ∈
                        (store'.apply (store.allocate (k + ann.arity) ann.body).1).vars ∧
                        k < store'.levelOf x := by
                      rintro ⟨x, hx, hlt⟩
                      exact absurd (hlevel x hx) (by omega)
                    rw [inferAt_letPoly]
                    simp [hann, hrhs, hunify, hnot, hbody]
                  have hpre₁ : InferPre (k + ann.arity) ctx
                      (store.allocate (k + ann.arity) ann.body).2 :=
                    InferPre.allocate_deeper pre ann
                  have spec := rhsSpec (k + ann.arity) ctx _ hpre₁
                  unfold InferSpec at spec
                  rw [hrhs] at spec
                  have rhsPost : InferPost sig (k + ann.arity) ctx rhs
                      (store.allocate (k + ann.arity) ann.body).2 rhsResult := spec
                  have hchecked : RhsChecked sig k ctx ann rhs store rhsResult.elaboration
                      (store'.apply (store.allocate (k + ann.arity) ann.body).1) store' :=
                    rhsChecked pre hann rhsPost hunify
                  have bodyPre := RhsChecked.bodyPre pre hchecked hlevel
                  have bodySpec' := bodySpec k
                    (⟨ann.arity,
                      (store'.apply (store.allocate (k + ann.arity) ann.body).1).closeRigids
                        k ann.arity⟩ :: ctx) store' bodyPre
                  unfold InferSpec at bodySpec'
                  rw [hbody] at bodySpec'
                  have bodyPost : InferPost sig k
                      (⟨ann.arity,
                        (store'.apply (store.allocate (k + ann.arity) ann.body).1).closeRigids
                          k ann.arity⟩ :: ctx) body store' bodyResult := bodySpec'
                  unfold InferSpec
                  rw [hval]
                  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
                  · -- safe
                    exact bodyPost.safe
                  · -- grows
                    show store.length ≤ bodyResult.store.length
                    have h₁ : store.length ≤
                        (store.allocate (k + ann.arity) ann.body).2.length := by
                      rw [MStore.allocate_snd]
                      simp
                    have h₂ : (store.allocate (k + ann.arity) ann.body).2.length ≤
                        rhsResult.store.length := rhsPost.grows
                    have h₃ : store'.length = rhsResult.store.length :=
                      MStore.unify_length hunify
                    have h₄ : store'.length ≤ bodyResult.store.length := bodyPost.grows
                    omega
                  · -- levels
                    intro id hid
                    show bodyResult.store.levelOf id ≤ store.levelOf id
                    have hle : store'.levelOf id ≤ store.levelOf id := hchecked.levels id hid
                    have hid' : id < store'.length := by
                      have := hchecked.grows
                      omega
                    have hbl := bodyPost.levels id hid'
                    omega
                  · -- tyWF
                    exact bodyPost.tyWF
                  · -- tyAllocated
                    exact bodyPost.tyAllocated
                  · -- tyLevels
                    exact bodyPost.tyLevels
                  · -- elabAllocated
                    intro a ha
                    change a ∈ (store'.apply (store.allocate (k + ann.arity) ann.body).1 ::
                      (rhsResult.elaboration.anns ++ bodyResult.elaboration.anns)) at ha
                    rcases List.mem_cons.mp ha with rfl | ha
                    · intro id hid
                      change id < bodyResult.store.length
                      have h := hchecked.completedAllocated id hid
                      have := bodyPost.grows
                      omega
                    · rcases List.mem_append.mp ha with ha | ha
                      · intro id hid
                        change id < bodyResult.store.length
                        have h := hchecked.elabAllocated a ha id hid
                        have := bodyPost.grows
                        omega
                      · exact bodyPost.elabAllocated a ha
                  · -- anchored
                    intro start level hlevelk hstart hanch
                    change bodyResult.store.Anchored start level
                    have hstore' : store'.Anchored start level :=
                      hchecked.anchored start level hlevelk hstart hanch
                    exact bodyPost.anchored start level hlevelk (by
                      have := hchecked.grows
                      omega) hstore'
                  · -- sound
                    intro valuation hmodels
                    have hbodySound := bodyPost.sound valuation hmodels
                    have hstore'Models : store'.Models valuation := hbodySound.1
                    have hbodyElab : Elaborates sig k
                        (Ctx.realize ((⟨ann.arity,
                          (store'.apply (store.allocate (k + ann.arity) ann.body).1).closeRigids
                            k ann.arity⟩ : Scheme Nat) :: ctx) valuation) body
                        (bodyResult.elaboration.realize valuation)
                        (bodyResult.ty.realize valuation) := hbodySound.2
                    have hcheckedSound := hchecked.sound valuation hstore'Models
                    have hstoreModels : store.Models valuation := hcheckedSound.1
                    have hrhsElab : Elaborates sig (k + ann.arity) (ctx.realize valuation) rhs
                        (rhsResult.elaboration.realize valuation)
                        ((store'.apply (store.allocate (k + ann.arity) ann.body).1).realize
                          valuation) := hcheckedSound.2.2
                    obtain ⟨hcompl, hskel⟩ := RhsChecked.completes hchecked hstore'Models
                    have hschemeRealize :
                        (⟨ann.arity,
                          (store'.apply (store.allocate (k + ann.arity) ann.body).1).closeRigids
                            k ann.arity⟩ : Scheme Nat).realize valuation =
                        (⟨ann.arity,
                          ((store'.apply (store.allocate (k + ann.arity) ann.body).1).realize
                            valuation).closeRigids k ann.arity⟩ : Scheme Empty) :=
                      RhsChecked.realize_scheme hchecked hlevel hstore'Models
                    have hrhsTyping : Elaborates sig
                        (k + (⟨ann.arity,
                          ((store'.apply (store.allocate (k + ann.arity) ann.body).1).realize
                            valuation).closeRigids k ann.arity⟩ : Scheme Empty).arity)
                        (ctx.realize valuation) rhs (rhsResult.elaboration.realize valuation)
                        ((⟨ann.arity,
                          ((store'.apply (store.allocate (k + ann.arity) ann.body).1).realize
                            valuation).closeRigids k ann.arity⟩ : Scheme Empty).skolemize k) := by
                      rw [hskel]
                      exact hrhsElab
                    have hbodyTyping : Elaborates sig k
                        ((⟨ann.arity,
                          ((store'.apply (store.allocate (k + ann.arity) ann.body).1).realize
                            valuation).closeRigids k ann.arity⟩ : Scheme Empty) ::
                          ctx.realize valuation) body
                        (bodyResult.elaboration.realize valuation)
                        (bodyResult.ty.realize valuation) := by
                      have hctxEq :
                          (Ctx.realize ((⟨ann.arity,
                            (store'.apply (store.allocate (k + ann.arity) ann.body).1).closeRigids
                              k ann.arity⟩ : Scheme Nat) :: ctx) valuation) =
                          (⟨ann.arity,
                            ((store'.apply (store.allocate (k + ann.arity) ann.body).1).realize
                              valuation).closeRigids k ann.arity⟩ : Scheme Empty) ::
                            ctx.realize valuation := by
                        rw [Ctx.realize_cons, hschemeRealize]
                      rw [← hctxEq]
                      exact hbodyElab
                    refine ⟨hstoreModels, ?_⟩
                    have hlet := TypingWith.letPoly hcompl hrhsTyping
                      (RhsChecked.determined hchecked hlevel hstore'Models) hbodyTyping
                    rw [hskel] at hlet
                    rw [show
                      (Expr.letIn (some ⟨ann.arity,
                          store'.apply (store.allocate (k + ann.arity) ann.body).1⟩)
                          rhsResult.elaboration bodyResult.elaboration).realize valuation =
                        Expr.letIn (some ⟨ann.arity,
                            (store'.apply (store.allocate (k + ann.arity) ann.body).1).realize
                              valuation⟩)
                          (rhsResult.elaboration.realize valuation)
                          (bodyResult.elaboration.realize valuation) from by
                      simp [Expr.realize, Expr.mapAnn, PolyAnn.map]]
                    exact hlet
                  · -- principal
                    intro valuation hmodels elaboration ty htyping
                    cases htyping with
                    | letPoly completes rhsTyping det bodyTyping =>
                      rename_i rhsElab0 scheme bodyElab0
                      have hskelWF : (scheme.skolemize k).WF (k + ann.arity) := by
                        rw [← completes.arity_eq]
                        exact Scheme.skolemize_wf completes.wf
                      have htyping' : Typing sig (k + ann.arity) (ctx.realize valuation) rhs
                          rhsElab0 (scheme.skolemize k) := by
                        rw [← completes.arity_eq]
                        exact rhsTyping
                      obtain ⟨extended₁, extModels₁, agree₁, _hrhsElab, hcompleted₁⟩ :=
                        hchecked.principal valuation hmodels rhsElab0 (scheme.skolemize k)
                          completes.body_matches hskelWF htyping'
                      have hschemeExt₁ :
                          (⟨ann.arity,
                            (store'.apply (store.allocate (k + ann.arity) ann.body).1).closeRigids
                              k ann.arity⟩ : Scheme Nat).realize extended₁ = scheme := by
                        have h := RhsChecked.realize_scheme hchecked hlevel extModels₁
                        rw [h, hcompleted₁]
                        have hbodyEq :
                            (scheme.skolemize k).closeRigids k ann.arity = scheme.body := by
                          rw [← completes.arity_eq]
                          exact Scheme.closeRigids_skolemize completes.wf
                        cases scheme with
                        | mk sa sb =>
                          simp only [Scheme.mk.injEq]
                          exact ⟨completes.arity_eq.symm, hbodyEq⟩
                      have hctx₁ : ctx.realize extended₁ = ctx.realize valuation :=
                        (Ctx.realize_congr pre.ctxAllocated agree₁).symm
                      have hbodyTyping₁ : Typing sig k
                          (Ctx.realize ((⟨ann.arity,
                            (store'.apply (store.allocate (k + ann.arity) ann.body).1).closeRigids
                              k ann.arity⟩ : Scheme Nat) :: ctx) extended₁) body bodyElab0 ty := by
                        rw [Ctx.realize_cons, hschemeExt₁, hctx₁]
                        exact bodyTyping
                      obtain ⟨extended, extModels, agreeBody, hbodyElab, hty⟩ :=
                        bodyPost.principal extended₁ extModels₁ bodyElab0 ty hbodyTyping₁
                      have hAgree : Agree store.length valuation extended := by
                        intro id hid
                        rw [agree₁ id hid]
                        exact agreeBody id (by
                          have := hchecked.grows
                          omega)
                      have hcr :
                          (store'.apply (store.allocate (k + ann.arity) ann.body).1).realize
                              extended₁ =
                            (store'.apply (store.allocate (k + ann.arity) ann.body).1).realize
                              extended :=
                        Ty.realize_congr hchecked.completedAllocated agreeBody
                      have hrr :
                          rhsResult.elaboration.realize extended₁ =
                            rhsResult.elaboration.realize extended :=
                        Expr.realize_congr hchecked.elabAllocated agreeBody
                      have hElabInf :
                          (Expr.letIn (some ⟨ann.arity,
                              store'.apply (store.allocate (k + ann.arity) ann.body).1⟩)
                              rhsResult.elaboration bodyResult.elaboration).realize extended =
                            Expr.letIn (some ⟨scheme.arity, scheme.skolemize k⟩)
                              rhsElab0 bodyElab0 := by
                        rw [show
                          (Expr.letIn (some ⟨ann.arity,
                              store'.apply (store.allocate (k + ann.arity) ann.body).1⟩)
                              rhsResult.elaboration bodyResult.elaboration).realize extended =
                            Expr.letIn (some ⟨ann.arity,
                                (store'.apply (store.allocate (k + ann.arity) ann.body).1).realize
                                  extended⟩)
                              (rhsResult.elaboration.realize extended)
                              (bodyResult.elaboration.realize extended) from by
                          simp [Expr.realize, Expr.mapAnn, PolyAnn.map]]
                        rw [← hcr, hcompleted₁, ← hrr, _hrhsElab, hbodyElab,
                          completes.arity_eq]
                      exact ⟨extended, extModels, hAgree, hElabInf, hty⟩
            · -- level check fails
              have hbad : ∃ x, x ∈
                  (store'.apply (store.allocate (k + ann.arity) ann.body).1).vars ∧
                  k < store'.levelOf x := by
                by_contra h
                apply hlevel
                intro x hx
                by_contra hle
                exact h ⟨x, hx, by omega⟩
              have hval : inferAt sig k ctx (.letIn (some ann) rhs body) store = none := by
                rw [inferAt_letPoly]
                simp [hann, hrhs, hunify, hbad]
              unfold InferSpec
              rw [hval]
              intro valuation hmodels elaboration ty helab
              cases helab with
              | letPoly completes rhsTyping det bodyTyping =>
                rename_i rhsElab scheme bodyElab
                have hpre₁ : InferPre (k + ann.arity) ctx
                    (store.allocate (k + ann.arity) ann.body).2 :=
                  InferPre.allocate_deeper pre ann
                have spec := rhsSpec (k + ann.arity) ctx _ hpre₁
                unfold InferSpec at spec
                rw [hrhs] at spec
                have rhsPost : InferPost sig (k + ann.arity) ctx rhs
                    (store.allocate (k + ann.arity) ann.body).2 rhsResult := spec
                have hchecked : RhsChecked sig k ctx ann rhs store rhsResult.elaboration
                    (store'.apply (store.allocate (k + ann.arity) ann.body).1) store' :=
                  rhsChecked pre hann rhsPost hunify
                exact (RhsChecked.undetermined pre hchecked hlevel hmodels completes
                  (Elaborates.typing rhsTyping)) det
  · -- annotation is out of scope
    have hval : inferAt sig k ctx (.letIn (some ann) rhs body) store = none := by
      rw [inferAt_letPoly]
      simp [hann]
    unfold InferSpec
    rw [hval]
    intro valuation hmodels elaboration ty helab
    cases helab with
    | letPoly completes rhsTyping det bodyTyping =>
      rename_i rhsElab scheme bodyElab
      exfalso
      apply hann
      have h := Template.Matches.wf completes.body_matches (Scheme.skolemize_wf completes.wf)
      rwa [completes.arity_eq] at h

end EPL2
