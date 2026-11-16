import EPL2.Spec.Models
import EPL2.Infer

/-!
# Store operations and the inference invariant

Each store operation of inference (`fresh`, `freshMany`, `allocate`,
`paramTy`; `unify` is in `EPL2.Spec.Unify`) is specified by how it changes
the set of models:

* *sound*: every model of the new store is a model of the old one, with some
  property of the returned type;
* *principal*: every model of the old store and every choice the declarative
  rule could make extends to a model of the new store that agrees on the old
  metavariables and realizes the returned type as that choice.

`InferPre`/`InferPost`/`InferSpec` state the same for a whole run of
`inferAt`.
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

/-! ## Anchoring -/

/-- Nothing is allocated from the frontier on. -/
theorem MStore.Anchored.of_length (store : MStore) (level : Nat) :
    store.Anchored store.length level := by
  sorry

/-- Metavariables appended above `level` are not `Anchored`'s concern. -/
theorem MStore.Anchored.append_unsolved {store : MStore} (anchored : store.Anchored start level)
    (above : level < level') :
    (store ++ List.replicate count (⟨level', none⟩ : MEntry)).Anchored start level := by
  sorry

/-! ## Contexts and schemes -/

theorem Ctx.realize_cons (scheme : Scheme Nat) (ctx : Ctx Nat) (valuation : Valuation) :
    Ctx.realize (scheme :: ctx) valuation = scheme.realize valuation :: ctx.realize valuation :=
  rfl

theorem Scheme.realize_mono (ty : InfTy) (valuation : Valuation) :
    (Scheme.mono ty).realize valuation = .mono (ty.realize valuation) :=
  rfl

theorem Ctx.realize_getElem? (ctx : Ctx Nat) (valuation : Valuation) (index : Nat) :
    (ctx.realize valuation)[index]? = (ctx[index]?).map (·.realize valuation) := by
  sorry

/-- A signature's scheme has no metavariables. -/
theorem Scheme.realize_lift (scheme : Scheme Empty) (valuation : Valuation) :
    (scheme.lift : Scheme Nat).realize valuation = scheme := by
  sorry

/-- Realizing an instance: realize the scheme and the arguments. The scheme's
metavariables must have `bvar`-free images, as they do under any model. -/
theorem Scheme.realize_inst (scheme : Scheme Nat) (args : List InfTy) {valuation : Valuation}
    (closed : ∀ id ∈ scheme.body.vars, (valuation id).WF k) :
    (scheme.inst args).realize valuation =
      (scheme.realize valuation).inst (args.map (·.realize valuation)) := by
  sorry

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

/-- A run one explicit let deeper sees the same context. -/
theorem InferPre.deeper (pre : InferPre k ctx store) (le : k ≤ k') : InferPre k' ctx store := by
  sorry

/-- A context entry for a type of the run's own depth. -/
theorem InferPre.cons_mono (pre : InferPre k ctx store) (wf : ty.WF k)
    (allocated : ty.Allocated store) (levels : ty.LevelBounded store k) :
    InferPre k (.mono ty :: ctx) store := by
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
  elabAllocated : ∀ ann ∈ result.elaboration.anns, ann.Allocated result.store
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

/-- The specification of one run: it either succeeds with `InferPost`, or the
program elaborates under no model of the input store. -/
def InferSpec (sig : Signature) (k : Nat) (ctx : Ctx Nat) (src : Source) (store : MStore) : Prop :=
  match inferAt sig k ctx src store with
  | some result => InferPost sig k ctx src store result
  | none => ∀ valuation, store.Models valuation →
      ∀ elaboration ty, ¬ Elaborates sig k (ctx.realize valuation) src elaboration ty

end EPL2
