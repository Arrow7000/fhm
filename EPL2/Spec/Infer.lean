import EPL2.Spec.Unify
import EPL2.Spec.Declarative
import EPL2.Infer

/-!
# Inference is sound and complete

The whole correctness argument is **one induction**, `inferAt_spec`, on the
source program. Its cases are short compositions of the specifications of the
store operations below (`fresh`, `freshMany`, `allocate`, `paramTy`, and
`unify` from `EPL2.Spec.Unify`), each of which says how the operation changes
the set of models:

* *sound*: every model of the new store is a model of the old one, with some
  property of the returned type;
* *principal*: every model of the old store and every choice the declarative
  rule could make extends to a model of the new store that agrees on the old
  metavariables and realizes the returned type as that choice.

The public theorems (`infer_eq_some_iff` and friends) are corollaries.
-/

namespace EPL2

/-! ## Store operations -/

/-- Structural facts about appending unsolved metavariables. -/
theorem MStore.append_unsolved_safe {store : MStore} (safe : store.Safe) :
    (store ++ List.replicate count (⟨level, none⟩ : MEntry)).Safe := by
  sorry

theorem MStore.append_unsolved_levelOf (store : MStore) (id : Nat) :
    (store ++ List.replicate count (⟨level, none⟩ : MEntry)).levelOf id =
      if id < store.length then store.levelOf id
      else if id < store.length + count then level else 0 := by
  sorry

theorem MStore.append_unsolved_lookup (store : MStore) (id : Nat) :
    (store ++ List.replicate count (⟨level, none⟩ : MEntry)).lookup id =
      if id < store.length then store.lookup id else none := by
  sorry

theorem MStore.freshMany_fst (store : MStore) (level count : Nat) :
    (store.freshMany level count).1 = (List.range count).map fun i => .var (store.length + i) :=
  rfl

theorem MStore.freshMany_snd (store : MStore) (level count : Nat) :
    (store.freshMany level count).2 = store ++ List.replicate count ⟨level, none⟩ :=
  rfl

theorem MStore.fresh_eq (store : MStore) (level : Nat) :
    store.fresh level = (.var store.length, store ++ List.replicate 1 ⟨level, none⟩) :=
  rfl

/-- Any arguments well-formed at the level can be chosen for fresh
metavariables. -/
theorem MStore.freshMany_principal {store : MStore} {valuation : Valuation} (safe : store.Safe)
    (models : store.Models valuation) (length : args.length = count)
    (argsWF : ∀ arg ∈ args, arg.WF level) :
    ∃ extended, (store.freshMany level count).2.Models extended ∧
      Agree store.length valuation extended ∧
      (store.freshMany level count).1.map (·.realize extended) = args := by
  sorry

theorem MStore.allocate_snd (store : MStore) (level : Nat) (template : Template) :
    (store.allocate level template).2 =
      store ++ List.replicate template.vars.dedup.length ⟨level, none⟩ :=
  rfl

/-- The allocated type is the template with holes replaced by fresh
metavariables. -/
theorem MStore.allocate_wf {store : MStore} {template : Template} (wf : template.WF level) :
    (store.allocate level template).1.WF level ∧
      (store.allocate level template).1.Allocated (store.allocate level template).2 ∧
      ∀ id ∈ (store.allocate level template).1.vars, store.length ≤ id := by
  sorry

/-- Every realization of an allocated template matches the template. -/
theorem MStore.allocate_sound (store : MStore) (level : Nat) (template : Template)
    (valuation : Valuation) :
    template.Matches ((store.allocate level template).1.realize valuation) := by
  sorry

/-- Every type the template matches, well-formed at the level, is a
realization of the allocated template. -/
theorem MStore.allocate_principal {store : MStore} {valuation : Valuation} {template : Template}
    {ty : SemTy} (safe : store.Safe) (models : store.Models valuation)
    (fits : template.Matches ty) (wf : ty.WF level) :
    ∃ extended, (store.allocate level template).2.Models extended ∧
      Agree store.length valuation extended ∧
      (store.allocate level template).1.realize extended = ty := by
  sorry

/-- The parameter type of a lambda: a fresh metavariable or an allocated
annotation. Fails exactly on an annotation with an out-of-scope variable. -/
theorem paramTy_spec {store : MStore} (safe : store.Safe) :
    match paramTy k store param with
    | some (ty, store') =>
        store' = store ++ List.replicate (store'.length - store.length) ⟨k, none⟩ ∧
        ty.WF k ∧ ty.Allocated store' ∧ (∀ id ∈ ty.vars, store.length ≤ id) ∧
        (∀ valuation, Template.MatchesOpt param (ty.realize valuation)) ∧
        ∀ valuation paramSem, store.Models valuation → Template.MatchesOpt param paramSem →
          paramSem.WF k →
          ∃ extended, store'.Models extended ∧ Agree store.length valuation extended ∧
            ty.realize extended = paramSem
    | none => ∀ paramSem : SemTy, Template.MatchesOpt param paramSem → ¬ paramSem.WF k := by
  sorry

/-! ## Contexts and schemes -/

theorem Ctx.realize_congr {ctx : Ctx Nat} {first second : Valuation} {frontier : Nat}
    (allocated : ∀ scheme ∈ ctx, ∀ id ∈ scheme.body.vars, id < frontier)
    (agree : Agree frontier first second) : ctx.realize first = ctx.realize second := by
  sorry

/-- Valuations that agree on the metavariables at or below `level` realize a
context whose metavariables are all at or below `level` alike. -/
theorem Ctx.realize_congr_levels {ctx : Ctx Nat} {store : MStore} {first second : Valuation}
    (levels : ∀ scheme ∈ ctx, scheme.body.LevelBounded store level)
    (agree : ∀ id, store.levelOf id ≤ level → first id = second id) :
    ctx.realize first = ctx.realize second := by
  sorry

theorem Ctx.realize_wf {ctx : Ctx Nat} {store : MStore} {valuation : Valuation}
    (models : store.Models valuation) (wf : ∀ scheme ∈ ctx, scheme.WF k)
    (allocated : ∀ scheme ∈ ctx, scheme.body.Allocated store)
    (levels : ∀ scheme ∈ ctx, scheme.body.LevelBounded store k) :
    (ctx.realize valuation).WF k := by
  sorry

/-- The scheme an explicit let binds: the completed generic type, closed. Its
realization is the closed realization, when the completed type's
metavariables are outer (images well-formed at the outer depth `k`). -/
theorem Scheme.realize_closeRigids {ty : InfTy} {valuation : Valuation}
    (images : ∀ id ∈ ty.vars, (valuation id).WF k) :
    (⟨n, ty.closeRigids k n⟩ : Scheme Nat).realize valuation =
      ⟨n, (ty.realize valuation).closeRigids k n⟩ := by
  sorry

/-! ## The inference invariant -/

/-- What a run at depth `k` assumes of its context and store. -/
structure InferPre (k : Nat) (ctx : Ctx Nat) (store : MStore) : Prop where
  safe : store.Safe
  ctxWF : ∀ scheme ∈ ctx, scheme.WF k
  ctxAllocated : ∀ scheme ∈ ctx, scheme.body.Allocated store
  ctxLevels : ∀ scheme ∈ ctx, scheme.body.LevelBounded store k

/-- `InferPre` survives any extension of the store that lowers no level. -/
theorem InferPre.extend {store store' : MStore} (pre : InferPre k ctx store) (safe : store'.Safe)
    (grows : store.length ≤ store'.length)
    (levels : ∀ id < store.length, store'.levelOf id ≤ store.levelOf id) :
    InferPre k ctx store' := by
  sorry

/-- What a successful run at depth `k` guarantees. -/
structure InferPost (sig : Signature) (k : Nat) (ctx : Ctx Nat) (src : Source)
    (store : MStore) (result : Inferred) : Prop where
  safe : result.store.Safe
  grows : store.length ≤ result.store.length
  levels : ∀ id < store.length, result.store.levelOf id ≤ store.levelOf id
  tyWF : result.ty.WF k
  tyAllocated : result.ty.Allocated result.store
  tyLevels : result.ty.LevelBounded result.store k
  /-- Runs deeper than `level` keep the store anchored at `level`. -/
  anchored : ∀ start level, level < k → start ≤ store.length →
    store.Anchored start level → result.store.Anchored start level
  /-- Every model of the result is a model of the input under which the
  program elaborates as inferred. -/
  sound : ∀ valuation, result.store.Models valuation →
    store.Models valuation ∧
      Elaborates sig k (ctx.realize valuation) src (result.elaboration.realize valuation)
        (result.ty.realize valuation)
  /-- Every typing, under any model of the input, is a realization of the
  result. -/
  principal : ∀ valuation, store.Models valuation →
    ∀ elaboration ty, Typing sig k (ctx.realize valuation) src elaboration ty →
      ∃ extended, result.store.Models extended ∧ Agree store.length valuation extended ∧
        result.elaboration.realize extended = elaboration ∧ result.ty.realize extended = ty

/-- **The** inference theorem. A run either succeeds with `InferPost`, or the
program elaborates under no model of the input store.

**Proof guidance.** Induction on `src`, generalizing `k`, `ctx`, `store`.
Every case is a chain of the specifications above; no case should unfold
`MStore.unify`. Sketch of the interesting cases:

* `app`: IH on the function, then on the argument (with `InferPre.extend`),
  then `fresh` and `unify_sound`/`unify_complete`. Principal: chain the two
  principal results (`Ctx.realize_congr` shows the argument sees the same
  context), extend by the result type (`MStore.models_append_unsolved` +
  `Models.congr`), then `unify_complete`. Failure of the unification
  contradicts that chain.
* `letIn (some ann)`, with `start := store.length`, `inner := k + ann.arity`,
  `completed := store₃.apply annTy`:
  - The right-hand side runs at `inner` against the store after `allocate`
    (`allocate_principal`/`allocate_sound`).
  - *Sound*, the `Determined` premise: given another completion with a
    typing of the right-hand side, chain `allocate_principal`, the IH's
    principality and `unify_complete` to a second model of `store₃` agreeing
    with the first before `start`. The store is anchored at `k` from `start`
    (vacuous after `allocate`, then the IH's `anchored` and
    `unify_anchored`), and the level check puts every metavariable of
    `completed` at or below `k`, so `Anchored.agree` + `Ty.realize_congr`
    show both models realize `completed` alike; `Scheme.skolemize_injective`
    concludes.
  - *Failure of the level check*: some `?m` in `completed` is unsolved at
    a level above `k`. From a hypothetical elaboration, principality gives a
    model of `store₃`; `Models.exists_different` changes `?m`. Both models
    realize the context alike (`Ctx.realize_congr_levels`: the context is at
    or below `k`), so soundness of the right-hand side gives two different
    completions (`Ty.realize_eq_vars`) that both check, contradicting
    `Determined`. (When `ann.arity = 0` there is no such `?m`: everything
    is at or below `inner = k`.)
  - The body's context entry realizes to the completed scheme by
    `Scheme.realize_closeRigids` and `Scheme.skolemize_closeRigids`.
* `var`, `const`: `freshMany_principal` with the declarative instance's
  arguments; `Scheme.inst_bind`. -/
theorem inferAt_spec {sig : Signature} {k : Nat} {ctx : Ctx Nat} {src : Source} {store : MStore}
    (pre : InferPre k ctx store) :
    match inferAt sig k ctx src store with
    | some result => InferPost sig k ctx src store result
    | none => ∀ valuation, store.Models valuation →
        ∀ elaboration ty, ¬ Elaborates sig k (ctx.realize valuation) src elaboration ty := by
  sorry

/-! ## The public entry point -/

theorem infer_sound {sig : Signature} {src : Source} {result : InferenceResult}
    (accepted : infer sig src = some result) :
    Elaborates sig 0 [] src result.elaboration result.ty := by
  sorry

/-- An accepted program has exactly one typing: its elaboration and type are
the inferred ones. -/
theorem infer_unique {sig : Signature} {src : Source} {result : InferenceResult}
    (accepted : infer sig src = some result)
    (typing : Typing sig 0 [] src elaboration ty) :
    elaboration = result.elaboration ∧ ty = result.ty := by
  sorry

/-- **Soundness and completeness.** `infer` accepts exactly the programs with
a unique elaboration, and returns it. Proof of `←`: `inferAt_spec` cannot
fail (its failure case contradicts the elaboration); if the result's type or
elaboration kept an unsolved metavariable, `Models.exists_different` and
soundness would give a second elaboration. -/
theorem infer_eq_some_iff {sig : Signature} {src : Source} {result : InferenceResult} :
    infer sig src = some result ↔
      Elaborates sig 0 [] src result.elaboration result.ty ∧
        ∀ elaboration ty, Elaborates sig 0 [] src elaboration ty →
          elaboration = result.elaboration ∧ ty = result.ty := by
  sorry

theorem infer_eq_none_iff {sig : Signature} {src : Source} :
    infer sig src = none ↔
      ¬ ∃ elaboration ty, Elaborates sig 0 [] src elaboration ty ∧
        ∀ elaboration' ty', Elaborates sig 0 [] src elaboration' ty' →
          elaboration' = elaboration ∧ ty' = ty := by
  sorry

/-! ## Accepted programs run safely -/

theorem infer_runtimeTyping {sig : Signature} {src : Source} {result : InferenceResult}
    (accepted : infer sig src = some result) :
    RuntimeTyping sig 0 [] src.erase result.ty := by
  sorry

theorem infer_steps_typed {sig : Signature} {src : Source} {result : InferenceResult}
    (accepted : infer sig src = some result) (steps : Eval.Steps sig src.erase expr) :
    RuntimeTyping sig 0 [] expr result.ty := by
  sorry

/-- Type safety: an accepted program never gets stuck. -/
theorem infer_type_safety {sig : Signature} {src : Source} {result : InferenceResult}
    (accepted : infer sig src = some result) (steps : Eval.Steps sig src.erase expr) :
    Eval.Value sig expr ∨ ∃ next, Eval.Step sig expr next := by
  sorry

/-- When the evaluator stops before its fuel runs out, it stops at a value. -/
theorem infer_run_value {sig : Signature} {src : Source} {result : InferenceResult}
    (accepted : infer sig src = some result)
    (stopped : Eval.step? sig (Eval.run sig fuel src.erase) = none) :
    Eval.Value sig (Eval.run sig fuel src.erase) := by
  sorry

end EPL2
