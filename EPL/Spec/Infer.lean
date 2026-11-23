import EPL.Spec.InferLet

/-!
# Inference is sound and complete

The whole correctness argument is **one induction**, `inferAt_spec`, on the
source program, with one lemma per constructor. Each is a short composition
of the specifications of the store operations (`EPL.Spec.Store`,
`EPL.Spec.Unify`); none unfolds `MStore.unify`. The explicit let is in
`EPL.Spec.InferLet`.

The public theorems (`infer_eq_ok_iff` and friends, in `EPL.Theorems`) are
corollaries.

**Outline of the cases.** Each lemma unfolds `inferAt` on its constructor
into nested `match`/`Option.bind` and splits along it.

* leaves: `MStore.freshMany_principal` with the declarative instance's
  arguments; `Scheme.realize_inst`, `Scheme.realize_lift`,
  `Ctx.realize_getElem?`, `PrimOp.ty_bind`.
* `lambda`, `fix`: `paramTy_spec` / `MStore.allocate_*`, `InferPre.cons_mono`
  and `InferPre.extend`.
* `app`: the function, then the argument (`InferPre.extend`), then `fresh`
  and `unify_sound`/`unify_complete`. Principal: chain the two principal
  results (`Ctx.realize_congr` shows the argument sees the same context,
  `Ty.realize_congr`/`Expr.realize_congr` that later extensions do not change
  earlier results), extend by the result type
  (`MStore.models_append_unsolved` + `Models.congr`), then `unify_complete`.
  Failure of the unification contradicts that chain.
* In every failure case, the hypothetical `Elaborates` derivation of the
  earlier subterms is turned into a model of the store the failing step ran
  against by `Elaborates.typing` and the earlier steps' `principal`.
-/

namespace EPL

/-- `Except.mapError` on a success reduces definitionally. -/
private theorem mapError_ok {ε ε' α : Type} (f : ε → ε') (a : α) :
    (Except.ok a : Except ε α).mapError f = .ok a := rfl

/-- `Except.mapError` on a failure reduces definitionally. -/
private theorem mapError_error {ε ε' α : Type} (f : ε → ε') (e : ε) :
    (Except.error e : Except ε α).mapError f = .error (f e) := rfl

/-! ## Small helpers -/

private theorem Ty.allocated_mono {store store' : MStore} {ty : InfTy}
    (grows : store.length ≤ store'.length) (allocated : ty.Allocated store) :
    ty.Allocated store' :=
  fun id h => lt_of_lt_of_le (allocated id h) grows

private theorem Ty.levelBounded_mono {store store' : MStore} {level : Nat} {ty : InfTy}
    (allocated : ty.Allocated store) (bounded : ty.LevelBounded store level)
    (levels : ∀ id < store.length, store'.levelOf id ≤ store.levelOf id) :
    ty.LevelBounded store' level :=
  fun id h => le_trans (levels id (allocated id h)) (bounded id h)

private theorem Ty.allocated_arrow {store : MStore} {d c : InfTy}
    (hd : d.Allocated store) (hc : c.Allocated store) :
    (Ty.arrow d c).Allocated store := by
  intro id hmem
  simp only [Ty.vars, List.mem_append] at hmem
  exact hmem.elim (hd id) (hc id)

private theorem Ty.levelBounded_arrow {store : MStore} {level : Nat} {d c : InfTy}
    (hd : d.LevelBounded store level) (hc : c.LevelBounded store level) :
    (Ty.arrow d c).LevelBounded store level := by
  intro id hmem
  simp only [Ty.vars, List.mem_append] at hmem
  exact hmem.elim (hd id) (hc id)

private theorem Ty.wf_arrow {k : Nat} {d c : InfTy} (hd : d.WF k) (hc : c.WF k) :
    (Ty.arrow d c).WF k := ⟨hd, hc⟩

private theorem Ty.realize_agree {ty : InfTy} {store : MStore} {first second : Valuation}
    (allocated : ty.Allocated store) (agree : Agree store.length first second) :
    ty.realize first = ty.realize second :=
  Ty.realize_congr allocated agree

private theorem Scheme.realize_agree {scheme : Scheme Nat} {store : MStore}
    {first second : Valuation} (allocated : scheme.body.Allocated store)
    (agree : Agree store.length first second) :
    scheme.realize first = scheme.realize second := by
  have h : scheme.body.bind first = scheme.body.bind second :=
    Ty.bind_congr (fun id hid => agree id (allocated id hid))
  cases scheme with
  | mk ar body => simpa [Scheme.realize, Scheme.bind] using congrArg (Scheme.mk ar) h

private theorem Expr.realize_agree {expr : Expr InfTy} {store : MStore}
    {first second : Valuation} (allocated : ∀ ann ∈ expr.anns, ann.Allocated store)
    (agree : Agree store.length first second) :
    expr.realize first = expr.realize second :=
  Expr.realize_congr (fun ann hann id hid => allocated ann hann id hid) agree

/-- Two valuations agreeing on the input store realize the context alike. -/
private theorem ctx_realize_congr_of_agree {k : Nat} {ctx : Ctx Nat} {store : MStore}
    {valuation extended : Valuation} (pre : InferPre k ctx store)
    (agree : Agree store.length valuation extended) :
    ctx.realize extended = ctx.realize valuation :=
  Ctx.realize_congr (fun scheme hmem id hid => pre.ctxAllocated scheme hmem id hid)
    (fun id hi => (agree id hi).symm)

/-- The context extended by the realized type of a subterm. -/
private theorem ctx_realize_cons_eq {k : Nat} {ctx : Ctx Nat} {store : MStore}
    {valuation extended : Valuation} (pre : InferPre k ctx store)
    (agree : Agree store.length valuation extended) {ty : InfTy} {sem : SemTy}
    (real : ty.realize extended = sem) :
    Ctx.realize (.mono ty :: ctx) extended = .mono sem :: ctx.realize valuation := by
  simp only [Ctx.realize_cons, Scheme.realize_mono]
  rw [real, ctx_realize_congr_of_agree pre agree]

private theorem ctx_image_wf {pre : InferPre k ctx store} {valuation : Valuation}
    (models : store.Models valuation) {scheme : Scheme Nat} (hmem : scheme ∈ ctx) {id : Nat}
    (hid : id ∈ scheme.body.vars) : (valuation id).WF k :=
  Ty.Scoped.mono (MStore.Models.image_wf models (pre.ctxAllocated scheme hmem id hid))
    (pre.ctxLevels scheme hmem id hid) (le_refl 0)

private theorem Ty.realize_wf_of_models {store : MStore} {valuation : Valuation}
    (models : store.Models valuation) {ty : InfTy} {k : Nat} (wf : ty.WF k)
    (allocated : ty.Allocated store) (levels : ty.LevelBounded store k) :
    (ty.realize valuation).WF k :=
  Ty.realize_wf wf (fun id hid =>
    Ty.Scoped.mono (MStore.Models.image_wf models (allocated id hid)) (levels id hid) (le_refl 0))

private theorem PrimLit.ty_vars (literal : PrimLit) : (literal.ty : Ty V).vars = [] := by
  cases literal <;> simp [PrimLit.ty, Ty.vars]

private theorem PrimOp.ty_vars {op : PrimOp} {ty : Ty V} {sig : Signature}
    (typed : op.ty sig = some ty) : ty.vars = [] := by
  cases op with
  | intAdd | intSub =>
      simp only [PrimOp.ty, Option.some.injEq] at typed
      subst typed; simp [Ty.vars]
  | intLt | charLt =>
      by_cases hb : sig.HasBool
      · simp only [PrimOp.ty, hb, if_true, Option.some.injEq] at typed
        subst typed; simp [Ty.bool, Ty.vars]
      · simp [PrimOp.ty, hb] at typed

private theorem Ty.levelBounded_append {store : MStore} {count level : Nat} {ty : InfTy}
    (allocated : ty.Allocated (store ++ List.replicate count ⟨level, none⟩))
    (outer : ∀ id ∈ ty.vars, store.length ≤ id) :
    ty.LevelBounded (store ++ List.replicate count ⟨level, none⟩) level := by
  intro id hmem
  have hlt := allocated id hmem
  have hge := outer id hmem
  rw [MStore.append_unsolved_levelOf, if_neg (by omega : ¬ id < store.length)]
  have hlt' : id < store.length + count := by simpa using hlt
  rw [if_pos hlt']

/-- A variable occurring in a defaulted list lookup occurs in some entry. -/
private theorem getD_vars_mem (args : List InfTy) (default : InfTy) (hdef : default.vars = []) :
    ∀ (j : Nat) {id : Nat}, id ∈ (args.getD j default).vars → ∃ arg ∈ args, id ∈ arg.vars := by
  induction args with
  | nil =>
      intro j id hid
      simp [List.getD, hdef] at hid
  | cons a as ih =>
      intro j id hid
      cases j with
      | zero => exact ⟨a, by simp, by simpa [List.getD] using hid⟩
      | succ j =>
          obtain ⟨arg, harg, hmem⟩ := ih (j := j) (by simpa [List.getD] using hid)
          exact ⟨arg, by simp [harg], hmem⟩

/-- Instantiation only reads the flexible variables of the type and of the
arguments. -/
private theorem Ty.vars_instantiate : ∀ (ty : InfTy) (args : List InfTy),
    ∀ id ∈ (ty.instantiate args).vars, id ∈ ty.vars ∨ ∃ arg ∈ args, id ∈ arg.vars
  | .prim _, _ => by intro id hid; simp [Ty.instantiate, Ty.subst, Ty.vars] at hid
  | .con _, _ => by intro id hid; simp [Ty.instantiate, Ty.subst, Ty.vars] at hid
  | .rigid _, _ => by intro id hid; simp [Ty.instantiate, Ty.subst, Ty.vars] at hid
  | .var _, _ => by
      intro id hid
      simp only [Ty.instantiate, Ty.subst, Ty.vars] at hid
      exact Or.inl hid
  | .bvar i, args => by
      intro id hid
      simp only [Ty.instantiate, Ty.subst] at hid
      exact Or.inr (getD_vars_mem args (.bvar i) (by simp [Ty.vars]) i hid)
  | .arrow d c, args => by
      intro id hid
      simp only [Ty.instantiate, Ty.subst, Ty.vars, List.mem_append] at hid
      rcases hid with hid | hid
      · rcases Ty.vars_instantiate d args id hid with h | ⟨arg, harg, hmem⟩
        · exact Or.inl (List.mem_append_left _ h)
        · exact Or.inr ⟨arg, harg, hmem⟩
      · rcases Ty.vars_instantiate c args id hid with h | ⟨arg, harg, hmem⟩
        · exact Or.inl (List.mem_append_right _ h)
        · exact Or.inr ⟨arg, harg, hmem⟩
  | .app d c, args => by
      intro id hid
      simp only [Ty.instantiate, Ty.subst, Ty.vars, List.mem_append] at hid
      rcases hid with hid | hid
      · rcases Ty.vars_instantiate d args id hid with h | ⟨arg, harg, hmem⟩
        · exact Or.inl (List.mem_append_left _ h)
        · exact Or.inr ⟨arg, harg, hmem⟩
      · rcases Ty.vars_instantiate c args id hid with h | ⟨arg, harg, hmem⟩
        · exact Or.inl (List.mem_append_right _ h)
        · exact Or.inr ⟨arg, harg, hmem⟩

private theorem Ty.allocated_instantiate (ty : InfTy) (args : List InfTy) (store : MStore)
    (allocated : ty.Allocated store) (argsAllocated : ∀ arg ∈ args, arg.Allocated store) :
    (ty.instantiate args).Allocated store :=
  fun id hid =>
    (Ty.vars_instantiate ty args id hid).elim (allocated id)
      (fun ⟨arg, harg, hmem⟩ => argsAllocated arg harg id hmem)

private theorem Ty.levelBounded_instantiate (ty : InfTy) (args : List InfTy) (store : MStore)
    (level : Nat) (bounded : ty.LevelBounded store level)
    (argsBounded : ∀ arg ∈ args, arg.LevelBounded store level) :
    (ty.instantiate args).LevelBounded store level :=
  fun id hid =>
    (Ty.vars_instantiate ty args id hid).elim (bounded id)
      (fun ⟨arg, harg, hmem⟩ => argsBounded arg harg id hmem)

private theorem freshMany_fst_length (store : MStore) (k count : Nat) :
    (store.freshMany k count).1.length = count := by
  rw [MStore.freshMany_fst]
  simp

private theorem freshMany_args_wf {store : MStore} {k count : Nat} :
    ∀ arg ∈ (store.freshMany k count).1, arg.WF k := by
  intro arg h
  rw [MStore.freshMany_fst] at h
  simp only [List.mem_map, List.mem_range] at h
  obtain ⟨i, hi, rfl⟩ := h
  trivial

private theorem freshMany_args_allocated {store : MStore} {k count : Nat} :
    ∀ arg ∈ (store.freshMany k count).1,
      arg.Allocated (store ++ List.replicate count ⟨k, none⟩) := by
  intro arg h
  rw [MStore.freshMany_fst] at h
  simp only [List.mem_map, List.mem_range] at h
  obtain ⟨i, hi, rfl⟩ := h
  intro id hid
  simp only [Ty.vars, List.mem_singleton] at hid
  subst hid
  show store.length + i < (store ++ List.replicate count (⟨k, none⟩ : MEntry)).length
  simp
  omega

private theorem freshMany_args_levelBounded {store : MStore} {k count : Nat} :
    ∀ arg ∈ (store.freshMany k count).1,
      arg.LevelBounded (store ++ List.replicate count ⟨k, none⟩) k := by
  intro arg h
  rw [MStore.freshMany_fst] at h
  simp only [List.mem_map, List.mem_range] at h
  obtain ⟨i, hi, rfl⟩ := h
  intro id hid
  simp only [Ty.vars, List.mem_singleton] at hid
  subst hid
  show (store ++ List.replicate count (⟨k, none⟩ : MEntry)).levelOf (store.length + i) ≤ k
  rw [MStore.append_unsolved_levelOf, if_neg (by omega : ¬ store.length + i < store.length)]
  rw [if_pos (by omega : store.length + i < store.length + count)]

private theorem freshMany_args_realize_wf {store : MStore} {k count : Nat}
    {valuation : Valuation}
    (models : (store ++ List.replicate count (⟨k, none⟩ : MEntry)).Models valuation) :
    ∀ arg ∈ (store.freshMany k count).1, (arg.realize valuation).WF k := by
  intro arg h
  rw [MStore.freshMany_fst] at h
  simp only [List.mem_map, List.mem_range] at h
  obtain ⟨i, hi, rfl⟩ := h
  have hfresh := ((MStore.models_append_unsolved (store := store) (count := count)
    (level := k)).1 models).2 i hi
  simpa [Ty.realize, Ty.bind, Ty.subst] using hfresh

/-- The arguments produced by one `freshMany` call: well-formed, of the right
length, allocated and level-bounded in the extended store. -/
private theorem freshMany_facts (store : MStore) (k count : Nat) :
    (∀ arg ∈ (store.freshMany k count).1, arg.WF k) ∧
      (store.freshMany k count).1.length = count ∧
      (∀ arg ∈ (store.freshMany k count).1,
        arg.Allocated (store ++ List.replicate count ⟨k, none⟩)) ∧
      (∀ arg ∈ (store.freshMany k count).1,
        arg.LevelBounded (store ++ List.replicate count ⟨k, none⟩) k) :=
  ⟨freshMany_args_wf, freshMany_fst_length store k count,
    freshMany_args_allocated, freshMany_args_levelBounded⟩

private theorem freshMany_map_length {store : MStore} {k count : Nat} (valuation : Valuation) :
    ((store.freshMany k count).1.map (·.realize valuation)).length = count := by
  rw [List.length_map, freshMany_fst_length]

private theorem freshMany_map_wf {store : MStore} {k count : Nat} {valuation : Valuation}
    (models : (store.freshMany k count).2.Models valuation) :
    ∀ arg ∈ (store.freshMany k count).1.map (·.realize valuation), arg.WF k := by
  intro arg harg
  rw [List.mem_map] at harg
  obtain ⟨orig, horig, rfl⟩ := harg
  exact freshMany_args_realize_wf models orig horig

private theorem fresh_allocated {store : MStore} {k : Nat} :
    (store.fresh k).1.Allocated (store.fresh k).2 := by
  rw [MStore.fresh_eq]
  intro id hid
  simp only [Ty.vars, List.mem_singleton] at hid
  subst hid
  simp

private theorem fresh_levelBounded {store : MStore} {k : Nat} :
    (store.fresh k).1.LevelBounded (store.fresh k).2 k := by
  rw [MStore.fresh_eq]
  intro id hid
  simp only [Ty.vars, List.mem_singleton] at hid
  subst hid
  rw [MStore.append_unsolved_levelOf, if_neg (by omega), if_pos (by omega)]

/-- Realization distributes over a type-application spine. -/
private theorem Ty.realize_apps (head : InfTy) (args : List InfTy) (valuation : Valuation) :
    (Ty.apps head args).realize valuation =
      Ty.apps (head.realize valuation) (args.map (·.realize valuation)) := by
  induction args generalizing head with
  | nil => rfl
  | cons arg rest ih =>
      change (Ty.apps (Ty.app head arg) rest).realize valuation =
        Ty.apps (head.realize valuation) ((arg :: rest).map (·.realize valuation))
      rw [ih]
      rfl

/-- Realizing an instantiated lifted field: the arguments are realized first. -/
private theorem Ty.realize_instantiate_lift (field : SemTy) (args : List InfTy)
    (valuation : Valuation) :
    ((field.lift : InfTy).instantiate args).realize valuation =
      field.instantiate (args.map (·.realize valuation)) := by
  rw [Ty.realize, Ty.instantiate_bind (rigids := 0) (ty := (field.lift : InfTy))
    (f := valuation) (args := args) ?_, Ty.lift_bind, Ty.lift_self]
  · simp only [Ty.realize]
  · intro v hv
    rw [Ty.vars_lift] at hv
    simp at hv

/-- Realization leaves the fresh rigid levels of a `rigidBlock` alone. -/
private theorem Ty.realize_rigidBlock (k n : Nat) (valuation : Valuation) :
    ((rigidBlock k n : List InfTy)).map (·.realize valuation) = rigidBlock k n := by
  unfold rigidBlock
  rw [List.map_map]
  rfl

/-- The realization of a branch's field context: the constructor's own
variables are instantiated at fresh rigid levels, which realization keeps as
they are. -/
private theorem Ctx.realize_fieldCtx (ctor : CtorDecl) (args : List InfTy) (k : Nat)
    (valuation : Valuation) :
    Ctx.realize ((ctor.fields.map fun field =>
        field.lift.instantiate (args ++ rigidBlock k ctor.existentials)).map Scheme.mono).reverse
        valuation =
      ctor.fieldCtx (args.map (·.realize valuation)) (rigidBlock k ctor.existentials) := by
  unfold Ctx.realize CtorDecl.fieldCtx
  simp only [List.map_reverse, List.map_map]
  congr 1
  apply List.map_congr_left
  intro field _
  simp only [Function.comp_apply, Scheme.realize_mono]
  rw [Ty.realize_instantiate_lift, List.map_append, Ty.realize_rigidBlock]

/-- Realization distributes over appending contexts. -/
private theorem Ctx.realize_append (first second : Ctx Nat) (valuation : Valuation) :
    Ctx.realize (first ++ second) valuation =
      Ctx.realize first valuation ++ Ctx.realize second valuation :=
  List.map_append

/-- Realization of the context a branch body is inferred in. -/
private theorem Ctx.realize_fieldCtx_append (ctor : CtorDecl) (args : List InfTy) (k : Nat)
    (ctx : Ctx Nat) (valuation : Valuation) :
    Ctx.realize (((ctor.fields.map fun field =>
        field.lift.instantiate (args ++ rigidBlock k ctor.existentials)).map Scheme.mono).reverse ++
        ctx) valuation =
      ctor.fieldCtx (args.map (·.realize valuation)) (rigidBlock k ctor.existentials) ++
        ctx.realize valuation := by
  rw [Ctx.realize_append, Ctx.realize_fieldCtx]

/-- The fresh rigid levels of a `rigidBlock` allocate in any store. -/
private theorem rigidBlock_allocated {store : MStore} {k n : Nat} :
    ∀ arg ∈ (rigidBlock k n : List InfTy), arg.Allocated store := by
  intro arg harg id hid
  unfold rigidBlock at harg
  simp only [List.mem_map, List.mem_range] at harg
  obtain ⟨i, _, rfl⟩ := harg
  simp [Ty.vars] at hid

/-- The length of a rigid block. -/
private theorem rigidBlock_length' (k n : Nat) : (rigidBlock k n : List InfTy).length = n := by
  simp [rigidBlock]

/-- Every member of a rigid block is well formed one block deeper. -/
private theorem rigidBlock_wf' {k n : Nat} {arg : InfTy} (harg : arg ∈ rigidBlock k n) :
    arg.WF (k + n) := by
  unfold rigidBlock at harg
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp harg
  simp only [List.mem_range] at hi
  show k + i < k + n
  omega

/-- The members of a rigid block are level-bounded everywhere. -/
private theorem rigidBlock_levelBounded {store : MStore} {k n level : Nat} :
    ∀ arg ∈ (rigidBlock k n : List InfTy), arg.LevelBounded store level := by
  intro arg harg id hid
  unfold rigidBlock at harg
  obtain ⟨i, _, rfl⟩ := List.mem_map.mp harg
  simp [Ty.vars] at hid

/-- A branch's field, instantiated at the scrutinee's arguments and the
constructor's fresh rigid levels, is well formed one block deeper. -/
private theorem field_wf {decl : DataDecl} {ctor : CtorDecl} {field : SemTy} {args : List InfTy}
    {k : Nat} (wf : decl.WF) (ctorMem : ctor ∈ decl.ctors) (fieldMem : field ∈ ctor.fields)
    (arity : args.length = decl.params) (argsWF : ∀ arg ∈ args, arg.WF k) :
    ((field.lift : InfTy).instantiate (args ++ rigidBlock k ctor.existentials)).WF
      (k + ctor.existentials) := by
  have hscheme : (⟨decl.params + ctor.existentials, (field.lift : InfTy)⟩ : Scheme Nat).WF 0 :=
    (Ty.scoped_lift).2 (wf ctor ctorMem field fieldMem)
  refine Scheme.inst_wf (scheme := ⟨decl.params + ctor.existentials, (field.lift : InfTy)⟩)
    (args := args ++ rigidBlock k ctor.existentials) (k := 0)
    (k' := k + ctor.existentials) hscheme (Nat.zero_le _) ?_ ?_
  · rw [List.length_append, arity, rigidBlock_length']
  · intro arg harg
    rcases List.mem_append.mp harg with h | h
    · exact Ty.Scoped.mono (argsWF arg h) (Nat.le_add_right k _) (le_refl 0)
    · exact rigidBlock_wf' h

/-- A branch's instantiated field mentions only allocated metavariables. -/
private theorem field_allocated {store : MStore} {ctor : CtorDecl} {field : SemTy}
    {args : List InfTy} {k : Nat} (argsAllocated : ∀ arg ∈ args, arg.Allocated store) :
    ((field.lift : InfTy).instantiate (args ++ rigidBlock k ctor.existentials)).Allocated store :=
  Ty.allocated_instantiate (field.lift) (args ++ rigidBlock k ctor.existentials) store
    (fun id hid => by rw [Ty.vars_lift] at hid; simp at hid)
    (fun arg harg => by
      rcases List.mem_append.mp harg with h | h
      · exact argsAllocated arg h
      · exact rigidBlock_allocated arg h)

/-- A branch's instantiated field is level-bounded one block deeper. -/
private theorem field_levelBounded {store : MStore} {ctor : CtorDecl} {field : SemTy}
    {args : List InfTy} {k : Nat}
    (argsLevels : ∀ arg ∈ args, arg.LevelBounded store k) :
    ((field.lift : InfTy).instantiate (args ++ rigidBlock k ctor.existentials)).LevelBounded
      store (k + ctor.existentials) :=
  Ty.levelBounded_instantiate (field.lift) (args ++ rigidBlock k ctor.existentials) store
    (k + ctor.existentials)
    (fun id hid => by rw [Ty.vars_lift] at hid; simp at hid)
    (fun arg harg => by
      rcases List.mem_append.mp harg with h | h
      · exact fun id hid => le_trans (argsLevels arg h id hid) (Nat.le_add_right k _)
      · exact rigidBlock_levelBounded arg h)

/-- The entries of a branch's field context are the constructor's fields. -/
private theorem mem_fieldCtx {ctor : CtorDecl} {args : List InfTy} {k : Nat} {scheme : Scheme Nat}
    (hmem : scheme ∈ ((ctor.fields.map fun field =>
      field.lift.instantiate (args ++ rigidBlock k ctor.existentials)).map Scheme.mono).reverse) :
    ∃ field ∈ ctor.fields,
      scheme = Scheme.mono (field.lift.instantiate (args ++ rigidBlock k ctor.existentials)) := by
  rw [List.mem_reverse, List.mem_map] at hmem
  obtain ⟨wrapped, hwrapped, rfl⟩ := hmem
  obtain ⟨field, hfield, rfl⟩ := List.mem_map.mp hwrapped
  exact ⟨field, hfield, rfl⟩

/-- Allocation of a type-application spine. -/
private theorem Ty.allocated_apps {store : MStore} (head : InfTy) (args : List InfTy)
    (headAllocated : head.Allocated store)
    (argsAllocated : ∀ arg ∈ args, arg.Allocated store) :
    (Ty.apps head args).Allocated store := by
  induction args generalizing head with
  | nil => exact headAllocated
  | cons arg rest ih =>
      change (Ty.apps (Ty.app head arg) rest).Allocated store
      refine ih (Ty.app head arg) ?_ fun other hmem => argsAllocated other (by simp [hmem])
      intro id hid
      simp only [Ty.vars, List.mem_append] at hid
      exact hid.elim (headAllocated id) (argsAllocated arg (by simp) id)

/-- The parts of a well-formed application spine are well formed. -/
private theorem Ty.wf_apps_parts {k : Nat} {head : Ty V} {args : List (Ty V)}
    (wf : (Ty.apps head args).WF k) : head.WF k ∧ ∀ arg ∈ args, arg.WF k := by
  induction args generalizing head with
  | nil => exact ⟨wf, by simp⟩
  | cons arg rest ih =>
      have h := ih (head := Ty.app head arg) (by simpa using wf)
      exact ⟨h.1.1, fun other hmem => by
        rcases List.mem_cons.mp hmem with rfl | hmem
        · exact h.1.2
        · exact h.2 other hmem⟩

/-- Branch-body annotations of a branch list are allocated when each body's
are. -/
private theorem annsBranches_allocated {branches : List (Pattern × Expr InfTy)} {store : MStore}
    (allocated : ∀ branch ∈ branches, ∀ ann ∈ branch.2.anns, ann.Allocated store) :
    ∀ ann ∈ Expr.annsBranches branches, ann.Allocated store := by
  induction branches with
  | nil => intro ann hmem; simp at hmem
  | cons branch rest ih =>
      intro ann hmem
      rw [Expr.annsBranches_eq, List.flatMap_cons] at hmem
      rcases List.mem_append.mp hmem with hmem | hmem
      · exact allocated branch (by simp) ann hmem
      · exact ih (fun other hother ann hann =>
          allocated other (by simp [hother]) ann hann) ann (by rwa [Expr.annsBranches_eq])

/-- A model of a store extended by unsolved metavariables restricts to the
original store. -/
private theorem MStore.Models.of_append_unsolved {store : MStore} {count level : Nat}
    {valuation : Valuation}
    (models : (store ++ List.replicate count (⟨level, none⟩ : MEntry)).Models valuation) :
    store.Models valuation :=
  ((MStore.models_append_unsolved (store := store) (count := count) (level := level)).1 models).1

/-! ## Inverting a typing derivation -/

private theorem TypingWith.primOp_type {sig : Signature} {Det : LetCondition} {k : Nat} {ctx : Ctx Empty}
    {op : PrimOp} {elaboration : Elab} {ty : SemTy}
    (typing : TypingWith sig Det k ctx (.primOp op) elaboration ty) : op.ty sig = some ty := by
  cases typing with
  | primOp h => exact h

private theorem TypingWith.var_inv {sig : Signature} {Det : LetCondition} {k : Nat} {ctx : Ctx Empty}
    {index : Nat} {elaboration : Elab} {ty : SemTy}
    (typing : TypingWith sig Det k ctx (.var index) elaboration ty) :
    elaboration = .var index ∧
      ∃ scheme : Scheme Empty, ∃ args : List SemTy,
        ctx[index]? = some scheme ∧ args.length = scheme.arity ∧
          (∀ arg ∈ args, arg.WF k) ∧ ty = scheme.inst args := by
  cases typing with
  | var h inst =>
      obtain ⟨args, hlen, hwf, hinst⟩ := inst
      exact ⟨rfl, _, args, h, hlen, hwf, hinst.symm⟩

private theorem TypingWith.lambda_inv {sig : Signature} {Det : LetCondition} {k : Nat} {ctx : Ctx Empty}
    {param : Option Template} {body : Source} {elaboration : Elab} {ty : SemTy}
    (typing : TypingWith sig Det k ctx (.lambda param body) elaboration ty) :
    ∃ sem : SemTy, ∃ bodyElab : Elab, ∃ bodyTy : SemTy,
      elaboration = .lambda (some sem) bodyElab ∧ ty = .arrow sem bodyTy ∧
        sem.WF k ∧ Template.MatchesOpt param sem ∧
          TypingWith sig Det k (.mono sem :: ctx) body bodyElab bodyTy := by
  cases typing with
  | lambda hwf hmatches hbody => exact ⟨_, _, _, rfl, rfl, hwf, hmatches, hbody⟩

private theorem TypingWith.app_inv {sig : Signature} {Det : LetCondition} {k : Nat} {ctx : Ctx Empty}
    {function argument : Source} {elaboration : Elab} {ty : SemTy}
    (typing : TypingWith sig Det k ctx (.app function argument) elaboration ty) :
    ∃ functionElab : Elab, ∃ argumentElab : Elab, ∃ argumentTy : SemTy, ∃ resultTy : SemTy,
      elaboration = .app functionElab argumentElab ∧ ty = resultTy ∧
        TypingWith sig Det k ctx function functionElab (.arrow argumentTy resultTy) ∧
          TypingWith sig Det k ctx argument argumentElab argumentTy := by
  cases typing with
  | app hfun harg => exact ⟨_, _, _, _, rfl, rfl, hfun, harg⟩

private theorem TypingWith.letMono_inv {sig : Signature} {Det : LetCondition} {k : Nat} {ctx : Ctx Empty}
    {rhs body : Source} {elaboration : Elab} {ty : SemTy}
    (typing : TypingWith sig Det k ctx (.letIn none rhs body) elaboration ty) :
    ∃ rhsElab : Elab, ∃ rhsTy : SemTy, ∃ bodyElab : Elab, ∃ bodyTy : SemTy,
      elaboration = .letIn none rhsElab bodyElab ∧ ty = bodyTy ∧
        TypingWith sig Det k ctx rhs rhsElab rhsTy ∧
          TypingWith sig Det k (.mono rhsTy :: ctx) body bodyElab bodyTy := by
  cases typing with
  | letMono hrhs hbody => exact ⟨_, _, _, _, rfl, rfl, hrhs, hbody⟩

private theorem TypingWith.fix_inv {sig : Signature} {Det : LetCondition} {k : Nat} {ctx : Ctx Empty}
    {self : Option Template} {body : Source} {elaboration : Elab} {ty : SemTy}
    (typing : TypingWith sig Det k ctx (.fix self body) elaboration ty) :
    ∃ sem : SemTy, ∃ bodyElab : Elab,
      elaboration = .fix (some sem) bodyElab ∧ ty = sem ∧ sem.WF k ∧
        Template.MatchesOpt self sem ∧
          TypingWith sig Det k (.mono sem :: ctx) body bodyElab sem := by
  cases typing with
  | fix hwf hmatches hbody => exact ⟨_, _, rfl, rfl, hwf, hmatches, hbody⟩

/-- Inverting a `match` typing. -/
private theorem TypingWith.match_inv {sig : Signature} {Det : LetCondition} {k : Nat}
    {ctx : Ctx Empty} {scrutinee : Source} {branches : List (Pattern × Source)}
    {elaboration : Elab} {ty : SemTy}
    (typing : TypingWith sig Det k ctx (.match scrutinee branches) elaboration ty) :
    ∃ (type : Nat) (decl : DataDecl) (args : List SemTy) (scrutineeElab : Elab)
      (branchesElab : List (Pattern × Elab)),
      sig.decl? type = some decl ∧ args.length = decl.params ∧ branches ≠ [] ∧
        (∀ pattern ∈ branches.map (·.1), pattern.ctor.type = type ∧
          pattern.ctor.index < decl.ctors.length) ∧
        (∀ pattern ∈ branches.map (·.1), ∀ ctor, decl.ctors[pattern.ctor.index]? = some ctor →
          pattern.binders = ctor.fields.length) ∧
        branchesElab.map (·.1) = branches.map (·.1) ∧
        TypingWith sig Det k ctx scrutinee scrutineeElab (Ty.apps (.con type) args) ∧
        (∀ (i : Nat) pattern body bodyElab ctor,
          branches[i]? = some (pattern, body) →
          branchesElab[i]? = some (pattern, bodyElab) →
          decl.ctors[pattern.ctor.index]? = some ctor →
          TypingWith sig Det (k + ctor.existentials)
            (ctor.fieldCtx args (rigidBlock k ctor.existentials) ++ ctx) body bodyElab ty) ∧
        ty.WF k ∧
        elaboration = .match scrutineeElab branchesElab := by
  cases typing with
  | «match» hscrut hdecl harity hne hpatterns hbinders hmap hall hwf =>
      exact ⟨_, _, _, _, _, hdecl, harity, hne, hpatterns, hbinders, hmap, hscrut, hall, hwf,
        rfl⟩

/-- A run that succeeds without touching the store on a closed, annotation-free
type: only `sound` and `principal` remain to be proved. -/
private theorem closed_post {sig : Signature} {k : Nat} {ctx : Ctx Nat} {store : MStore}
    {src : Source} {ty : InfTy} {elaboration : Expr InfTy} (pre : InferPre k ctx store)
    (tyWF : ty.WF k) (noVars : ty.vars = []) (noAnns : elaboration.anns = [])
    (sound : ∀ valuation, store.Models valuation →
      store.Models valuation ∧
        Elaborates sig k (ctx.realize valuation) src
          (elaboration.realize valuation) (ty.realize valuation))
    (principal : ∀ valuation, store.Models valuation → ∀ elaboration' ty',
      Typing sig k (ctx.realize valuation) src elaboration' ty' →
      ∃ extended, store.Models extended ∧ Agree store.length valuation extended ∧
        elaboration.realize extended = elaboration' ∧ ty.realize extended = ty') :
    InferPost sig k ctx src store ⟨ty, elaboration, store, .node ty []⟩ :=
  { safe := pre.safe
    grows := le_rfl
    levels := fun _ _ => le_rfl
    tyWF := tyWF
    tyAllocated := fun id hid => by rw [noVars] at hid; simp at hid
    tyLevels := fun id hid => by rw [noVars] at hid; simp at hid
    elabAllocated := fun ann hmem => by rw [noAnns] at hmem; simp at hmem
    anchored := fun _ _ _ _ hanch => hanch
    sound := sound
    principal := principal }

theorem inferAt_spec_lit {sig : Signature} (pre : InferPre k ctx store) :
    InferSpec sig k ctx (.lit literal) store := by
  have h : inferAt sig k ctx (.lit literal) store =
      .ok ⟨literal.ty, .lit literal, store, .node literal.ty []⟩ := rfl
  simp only [InferSpec, h]
  refine closed_post (elaboration := .lit literal) pre (PrimLit.ty_wf literal)
    (PrimLit.ty_vars literal) (by simp [Expr.anns]) ?_ ?_
  · intro valuation models
    refine ⟨models, ?_⟩
    have hty : (literal.ty : InfTy).realize valuation = (literal.ty : SemTy) :=
      PrimLit.ty_bind literal valuation
    simp only [Expr.realize, Expr.mapAnn, hty]
    exact TypingWith.lit
  · intro valuation models elaboration ty typing
    cases typing with
    | lit =>
      exact ⟨valuation, models, fun _ _ => rfl, rfl, PrimLit.ty_bind literal valuation⟩

theorem inferAt_spec_primOp {sig : Signature} (pre : InferPre k ctx store) :
    InferSpec sig k ctx (.primOp op) store := by
  have hbind : inferAt sig k ctx (.primOp op) store =
      (op.ty sig).getDM (throw (.here .noBool)) >>= (fun ty =>
        (pure ⟨ty, .primOp op, store, .node ty []⟩ : Except InferError Inferred)) := rfl
  cases hop : op.ty sig with
  | none =>
      have h : inferAt sig k ctx (.primOp op) store = .error (.here .noBool) := by
        rw [hbind, hop]; rfl
      simp only [InferSpec, h]
      intro valuation models elaboration ty typing
      cases typing with
      | primOp hty =>
          have hlift := PrimOp.ty_lift (op := op) (ty := ty) (V := Nat) hty
          rw [hop] at hlift
          cases hlift
  | some ty =>
      have h : inferAt sig k ctx (.primOp op) store =
          .ok ⟨ty, .primOp op, store, .node ty []⟩ := by
        rw [hbind, hop]; rfl
      simp only [InferSpec, h]
      have htyvars : ty.vars = [] := PrimOp.ty_vars hop
      refine closed_post (elaboration := .primOp op) pre (PrimOp.ty_wf hop) htyvars
        (by simp [Expr.anns]) ?_ ?_
      · intro valuation models
        refine ⟨models, ?_⟩
        simp only [Expr.realize, Expr.mapAnn]
        exact TypingWith.primOp (PrimOp.ty_bind hop valuation)
      · intro valuation models elaboration target typing
        cases typing with
        | primOp hty =>
            refine ⟨valuation, models, fun _ _ => rfl, rfl, ?_⟩
            rw [PrimOp.ty_bind hop valuation] at hty
            exact Option.some.inj hty

theorem inferAt_spec_ctor {sig : Signature} (pre : InferPre k ctx store) :
    InferSpec sig k ctx (.ctor ref) store := by
  have hbind : inferAt sig k ctx (.ctor ref) store =
      (sig.ctorScheme ref).getDM (throw (.here .unknownCtor)) >>= (fun scheme =>
        (pure ⟨scheme.lift.inst (store.freshMany k scheme.arity).1, .ctor ref,
          (store.freshMany k scheme.arity).2,
          .node (scheme.lift.inst (store.freshMany k scheme.arity).1) []⟩ :
            Except InferError Inferred)) := rfl
  cases hsch : sig.ctorScheme ref with
  | none =>
      have h : inferAt sig k ctx (.ctor ref) store = .error (.here .unknownCtor) := by
        rw [hbind, hsch]; rfl
      simp only [InferSpec, h]
      intro valuation models elaboration ty typing
      cases typing with
      | ctor htyping _ =>
          rw [hsch] at htyping
          cases htyping
  | some scheme =>
      have h : inferAt sig k ctx (.ctor ref) store =
          .ok ⟨(scheme.lift : Scheme Nat).inst (store.freshMany k scheme.arity).1,
            .ctor ref, (store.freshMany k scheme.arity).2,
            .node ((scheme.lift : Scheme Nat).inst (store.freshMany k scheme.arity).1) []⟩ := by
        rw [hbind, hsch]; rfl
      simp only [InferSpec, h]
      obtain ⟨hargsWF, hlen, hargsAlloc, hargsLB⟩ :=
        freshMany_facts store k scheme.arity
      have hschemeWF0 : scheme.WF 0 := Signature.ctorScheme_wf hsch
      have hschemeWFk : scheme.body.Scoped k scheme.arity :=
        Ty.Scoped.mono hschemeWF0 (by omega) le_rfl
      have hliftWF : (scheme.lift : Scheme Nat).WF k := by
        simpa [Scheme.lift] using (Ty.scoped_lift).2 hschemeWFk
      have hbodyAlloc : (scheme.lift : Scheme Nat).body.Allocated
          (store ++ List.replicate scheme.arity ⟨k, none⟩) := by
        intro id hid
        simp [Scheme.lift, Ty.vars_lift] at hid
      have hbodyLB : (scheme.lift : Scheme Nat).body.LevelBounded
          (store ++ List.replicate scheme.arity ⟨k, none⟩) k := by
        intro id hid
        simp [Scheme.lift, Ty.vars_lift] at hid
      refine
        { safe := MStore.append_unsolved_safe pre.safe
          grows := by rw [MStore.freshMany_snd]; simp
          levels := ?_
          tyWF := Scheme.inst_wf hliftWF (le_refl k) hlen hargsWF
          tyAllocated := ?_
          tyLevels := ?_
          elabAllocated := ?_
          anchored := ?_
          sound := ?_
          principal := ?_ }
      · intro id hi
        show (store.freshMany k scheme.arity).2.levelOf id ≤ store.levelOf id
        rw [MStore.freshMany_snd, MStore.append_unsolved_levelOf, if_pos hi]
      · simpa [Scheme.inst] using
          (Ty.allocated_instantiate (scheme.lift : Scheme Nat).body
            (store.freshMany k scheme.arity).1
            (store ++ List.replicate scheme.arity ⟨k, none⟩) hbodyAlloc hargsAlloc)
      · simpa [Scheme.inst] using
          (Ty.levelBounded_instantiate (scheme.lift : Scheme Nat).body
            (store.freshMany k scheme.arity).1
            (store ++ List.replicate scheme.arity ⟨k, none⟩) k hbodyLB hargsLB)
      · intro ann hmem
        simp [Expr.anns] at hmem
      · intro start level hlt hstart hanch
        exact MStore.Anchored.append_unsolved (count := scheme.arity) (level' := k) hanch hlt
      · intro valuation models
        have hmodelsStore : store.Models valuation :=
          MStore.Models.of_append_unsolved models
        refine ⟨hmodelsStore, ?_⟩
        simp only [Expr.realize, Expr.mapAnn]
        have hclosed : ∀ id ∈ (scheme.lift : Scheme Nat).body.vars, (valuation id).WF k := by
          intro id hid
          simp [Scheme.lift, Ty.vars_lift] at hid
        have hreal := Scheme.realize_inst (scheme := (scheme.lift : Scheme Nat))
          (args := (store.freshMany k scheme.arity).1) (valuation := valuation) hclosed
        rw [Scheme.realize_lift] at hreal
        refine TypingWith.ctor hsch ?_
        exact ⟨(store.freshMany k scheme.arity).1.map (·.realize valuation),
          freshMany_map_length valuation, freshMany_map_wf models, hreal.symm⟩
      · intro valuation models elaboration target typing
        cases typing with
        | ctor htyping hinst =>
            have hschemeEq := Option.some.inj (hsch.symm.trans htyping)
            obtain ⟨args', hlen', hwf', hinstEq⟩ := hinst
            rw [← hschemeEq] at hlen' hinstEq
            obtain ⟨extended, hmodels', hagree', hmap⟩ :=
              MStore.freshMany_principal (store := store) (level := k)
                (count := scheme.arity) (valuation := valuation) pre.safe models hlen' hwf'
            refine ⟨extended, hmodels', hagree', ?_, ?_⟩
            · simp only [Expr.realize, Expr.mapAnn]
            · have hclosed : ∀ id ∈ (scheme.lift : Scheme Nat).body.vars,
                  (extended id).WF k := by
                intro id hid
                simp [Scheme.lift, Ty.vars_lift] at hid
              have hreal := Scheme.realize_inst (scheme := (scheme.lift : Scheme Nat))
                (args := (store.freshMany k scheme.arity).1) (valuation := extended) hclosed
              rw [Scheme.realize_lift, hmap] at hreal
              rw [← hinstEq]
              exact hreal

/-! ## Match

`inferBranches` threads the store through the branches, so its specification
is `InferSpec` lifted to a list: each branch body is checked, one rigid level
deeper per existential of its constructor and with its fields
`fields[args ++ fresh levels]` in the context (`CtorDecl.fieldCtx`), against
`resultTy`. -/

/-- What a successful `inferBranches` run guarantees, given the scrutinee's
type arguments `args` and the shared `resultTy`. -/
structure BranchesPost (sig : Signature) (k : Nat) (ctx : Ctx Nat) (decl : DataDecl)
    (args : List InfTy) (resultTy : InfTy) (branches : List (Pattern × Source))
    (store : MStore) (result : List (Pattern × Expr InfTy) × MStore) : Prop where
  safe : result.2.Safe
  grows : store.length ≤ result.2.length
  levels : ∀ id < store.length, result.2.levelOf id ≤ store.levelOf id
  patterns : result.1.map (·.1) = branches.map (·.1)
  elabAllocated : ∀ branch ∈ result.1, ∀ ann ∈ branch.2.anns, ann.Allocated result.2
  anchored : ∀ start level, level < k → start ≤ store.length →
    store.Anchored start level → result.2.Anchored start level
  /-- Every model of the result is a model of the input under which each
  branch elaborates as inferred, at its expected type. -/
  sound : ∀ valuation, result.2.Models valuation →
    store.Models valuation ∧
      ∀ (i : Nat) pattern body bodyElab ctor,
        branches[i]? = some (pattern, body) →
        result.1[i]? = some (pattern, bodyElab) →
        decl.ctors[pattern.ctor.index]? = some ctor →
        Elaborates sig (k + ctor.existentials)
          (ctor.fieldCtx (args.map (·.realize valuation)) (rigidBlock k ctor.existentials) ++
            ctx.realize valuation)
          body (bodyElab.realize valuation) (resultTy.realize valuation)
  /-- Every typing of all the branches, under any model of the input, is a
  realization of the result. -/
  principal : ∀ valuation, store.Models valuation →
    ∀ branchesElab : List (Pattern × Elab),
      branchesElab.map (·.1) = branches.map (·.1) →
      (∀ (i : Nat) pattern body bodyElab ctor,
        branches[i]? = some (pattern, body) →
        branchesElab[i]? = some (pattern, bodyElab) →
        decl.ctors[pattern.ctor.index]? = some ctor →
        Typing sig (k + ctor.existentials)
          (ctor.fieldCtx (args.map (·.realize valuation)) (rigidBlock k ctor.existentials) ++
            ctx.realize valuation)
          body bodyElab (resultTy.realize valuation)) →
      ∃ extended, result.2.Models extended ∧ Agree store.length valuation extended ∧
        result.1.map (fun branch => (branch.1, branch.2.realize extended)) = branchesElab

/-- The specification of `inferBranches`: success with `BranchesPost`, or (on
any error) no model of the input store lets every branch elaborate at its expected type. -/
def BranchesSpec (sig : Signature) (k : Nat) (ctx : Ctx Nat) (decl : DataDecl)
    (args : List InfTy) (resultTy : InfTy) (branches : List (Pattern × Source))
    (store : MStore) : Prop :=
  match inferBranches sig k ctx decl args resultTy branches store with
  | .ok result => BranchesPost sig k ctx decl args resultTy branches store result.1
  | .error _ => ∀ valuation, store.Models valuation →
      ∀ branchesElab : List (Pattern × Elab),
        branchesElab.map (·.1) = branches.map (·.1) →
        ¬ ∀ (i : Nat) pattern body bodyElab ctor,
          branches[i]? = some (pattern, body) →
          branchesElab[i]? = some (pattern, bodyElab) →
          decl.ctors[pattern.ctor.index]? = some ctor →
          Elaborates sig (k + ctor.existentials)
            (ctor.fieldCtx (args.map (·.realize valuation)) (rigidBlock k ctor.existentials) ++
              ctx.realize valuation)
            body bodyElab (resultTy.realize valuation)

/-- Proof: induction on `branches`, each body by its `InferSpec` and the
unification by the unifier's specification, as in `inferAt_spec_app`. -/
theorem inferBranches_spec {sig : Signature} {decl : DataDecl} {args : List InfTy}
    {resultTy : InfTy} {branches : List (Pattern × Source)}
    (bodies : ∀ branch ∈ branches, ∀ k ctx store, InferPre k ctx store →
      InferSpec sig k ctx branch.2 store)
    (wf : decl.WF) (arity : args.length = decl.params)
    (indices : ∀ pattern ∈ branches.map (·.1), pattern.ctor.index < decl.ctors.length)
    (pre : InferPre k ctx store)
    (argsWF : ∀ arg ∈ args, arg.WF k) (argsAllocated : ∀ arg ∈ args, arg.Allocated store)
    (argsLevels : ∀ arg ∈ args, arg.LevelBounded store k)
    (resultWF : resultTy.WF k) (resultAllocated : resultTy.Allocated store)
    (resultLevels : resultTy.LevelBounded store k) :
    BranchesSpec sig k ctx decl args resultTy branches store := by
  -- `wf`, `arity` and `resultWF` are part of the statement but not needed below.
  have _declWF : decl.WF := wf
  have _arity : args.length = decl.params := arity
  have _resultWF : resultTy.WF k := resultWF
  revert store bodies indices pre argsAllocated argsLevels argsWF resultAllocated resultLevels
  induction branches with
  | nil =>
      intro store bodies indices pre argsWF argsAllocated argsLevels resultAllocated resultLevels
      have h : inferBranches sig k ctx decl args resultTy [] store = .ok (([], store), []) :=
        rfl
      simp only [BranchesSpec, h]
      refine
        { safe := pre.safe
          grows := le_rfl
          levels := fun _ _ => le_rfl
          patterns := rfl
          elabAllocated := by intro branch hmem; simp at hmem
          anchored := fun start level hlt hstart hanch => hanch
          sound := ?_
          principal := ?_ }
      · intro valuation models
        refine ⟨models, ?_⟩
        intro i pattern body bodyElab ctor hbr hbrE hfields
        simp at hbr
      · intro valuation models branchesElab hmap _hall
        have hnil : branchesElab = [] := List.map_eq_nil_iff.mp hmap
        subst hnil
        exact ⟨valuation, models, fun _ _ => rfl, rfl⟩
  | cons head rest ih =>
      obtain ⟨pattern, body⟩ := head
      intro store bodies indices pre argsWF argsAllocated argsLevels resultAllocated resultLevels
      have hbind : inferBranches sig k ctx decl args resultTy ((pattern, body) :: rest) store = (do
          let ctor ← decl.ctors[pattern.ctor.index]?.getDM
            (throw ⟨[.matchBranch 0], .foreignPattern⟩)
          let fieldTys := ctor.fields.map fun field =>
            field.lift.instantiate (args ++ rigidBlock k ctor.existentials)
          let bodyResult ← (inferAt sig (k + ctor.existentials)
            ((fieldTys.map .mono).reverse ++ ctx) body store).mapError (.under (.matchBranch 0))
          let store ← bodyResult.store.unifyAt [.matchBranch 0] bodyResult.ty resultTy
          let ((restElab, store), restTypes) ←
            (inferBranches sig k ctx decl args resultTy rest store).mapError InferError.nextBranch
          pure (((pattern, bodyResult.elaboration) :: restElab, store),
            .node resultTy (fieldTys.map (.node · []) ++ [bodyResult.types]) :: restTypes)) := rfl
      have hmem : pattern ∈ ((pattern, body) :: rest).map (·.1) := by simp
      cases hfields : decl.ctors[pattern.ctor.index]? with
      | none =>
          have h : inferBranches sig k ctx decl args resultTy ((pattern, body) :: rest) store =
              .error ⟨[.matchBranch 0], .foreignPattern⟩ := by
            simp only [hbind, hfields, Option.getDM, Bind.bind, Except.bind]
          simp only [BranchesSpec, h]
          intro valuation models branchesElab hmap hall
          have hidx := indices pattern hmem
          rw [List.getElem?_eq_none_iff] at hfields
          omega
      | some ctor =>
          have hctorMem : ctor ∈ decl.ctors := List.mem_of_getElem? hfields
          have hpreInner : InferPre (k + ctor.existentials)
              (((ctor.fields.map fun field =>
                field.lift.instantiate (args ++ rigidBlock k ctor.existentials)).map
                Scheme.mono).reverse ++ ctx) store := by
            refine ⟨pre.safe, ?_, ?_, ?_⟩
            · intro scheme hmem
              rcases List.mem_append.mp hmem with hmem | hmem
              · obtain ⟨field, hfield, rfl⟩ := mem_fieldCtx hmem
                exact field_wf wf hctorMem hfield arity argsWF
              · exact Ty.Scoped.mono (pre.ctxWF scheme hmem) (Nat.le_add_right k _) le_rfl
            · intro scheme hmem id hid
              rcases List.mem_append.mp hmem with hmem | hmem
              · obtain ⟨field, _, rfl⟩ := mem_fieldCtx hmem
                exact field_allocated argsAllocated id hid
              · exact pre.ctxAllocated scheme hmem id hid
            · intro scheme hmem id hid
              rcases List.mem_append.mp hmem with hmem | hmem
              · obtain ⟨field, _, rfl⟩ := mem_fieldCtx hmem
                exact field_levelBounded argsLevels id hid
              · exact le_trans (pre.ctxLevels scheme hmem id hid) (Nat.le_add_right k _)
          cases hb : inferAt sig (k + ctor.existentials)
              (((ctor.fields.map fun field =>
                field.lift.instantiate (args ++ rigidBlock k ctor.existentials)).map
                Scheme.mono).reverse ++ ctx) body store with
          | error bodyError =>
              have h : inferBranches sig k ctx decl args resultTy ((pattern, body) :: rest) store =
                  .error (.under (.matchBranch 0) bodyError) := by
                simp only [hbind, hfields, hb, Option.getDM, Bind.bind, Except.bind,
                  Pure.pure, Except.pure, mapError_error]
              simp only [BranchesSpec, h]
              intro valuation models branchesElab hmap hall
              obtain ⟨headElab, tailElab, rfl, hheadElab, _⟩ := List.map_eq_cons_iff.mp hmap
              obtain ⟨patternElab, bodyElab⟩ := headElab
              simp only at hheadElab
              subst patternElab
              have hbodyNone := bodies (pattern, body) (by simp) (k + ctor.existentials) _ store
                hpreInner
              unfold InferSpec at hbodyNone
              rw [hb] at hbodyNone
              refine hbodyNone valuation models bodyElab (resultTy.realize valuation) ?_
              rw [Ctx.realize_fieldCtx_append]
              exact hall 0 pattern body bodyElab ctor (by simp) (by simp) hfields
          | ok bodyResult =>
              have hbodyPost : InferPost sig (k + ctor.existentials)
                  (((ctor.fields.map fun field =>
                    field.lift.instantiate (args ++ rigidBlock k ctor.existentials)).map
                    Scheme.mono).reverse ++ ctx) body store bodyResult := by
                have hspec := bodies (pattern, body) (by simp) (k + ctor.existentials) _ store
                  hpreInner
                unfold InferSpec at hspec
                rw [hb] at hspec
                simpa only using hspec
              have hgrow₁ : store.length ≤ bodyResult.store.length := hbodyPost.grows
              have hresultAlloc₁ : resultTy.Allocated bodyResult.store :=
                Ty.allocated_mono hgrow₁ resultAllocated
              cases hu : bodyResult.store.unify bodyResult.ty resultTy with
              | error cause =>
                  have h : inferBranches sig k ctx decl args resultTy
                      ((pattern, body) :: rest) store =
                      .error ⟨[.matchBranch 0], .mismatch
                        (bodyResult.store.apply resultTy)
                        (bodyResult.store.apply bodyResult.ty) cause⟩ := by
                    simp only [hbind, hfields, hb, MStore.unifyAt, Option.getDM,
                      Bind.bind, Except.bind, Pure.pure, Except.pure, mapError_ok, mapError_error, hu]
                  simp only [BranchesSpec, h]
                  intro valuation models branchesElab hmap hall
                  obtain ⟨headElab, tailElab, rfl, hheadElab, _⟩ := List.map_eq_cons_iff.mp hmap
                  obtain ⟨patternElab, bodyElab⟩ := headElab
                  simp only at hheadElab
                  subst patternElab
                  have htyping : Typing sig (k + ctor.existentials)
                      (Ctx.realize (((ctor.fields.map fun field =>
                        field.lift.instantiate (args ++ rigidBlock k ctor.existentials)).map
                        Scheme.mono).reverse ++ ctx) valuation)
                      body bodyElab (resultTy.realize valuation) := by
                    rw [Ctx.realize_fieldCtx_append]
                    exact Elaborates.typing
                      (hall 0 pattern body bodyElab ctor (by simp) (by simp) hfields)
                  obtain ⟨extended, hmodels, hagree, _, hty⟩ :=
                    hbodyPost.principal valuation models bodyElab _ htyping
                  have hresultExt : resultTy.realize extended = resultTy.realize valuation :=
                    Ty.realize_congr resultAllocated (fun id hi => (hagree id hi).symm)
                  have hunifies : bodyResult.ty.realize extended = resultTy.realize extended :=
                    hty.trans hresultExt.symm
                  obtain ⟨result, hresult, _⟩ :=
                    MStore.unify_complete hbodyPost.safe hbodyPost.tyAllocated hresultAlloc₁
                      hmodels hunifies
                  rw [hu] at hresult
                  cases hresult
              | ok store' =>
                  have hgrow₂ : bodyResult.store.length ≤ store'.length :=
                    le_of_eq (MStore.unify_length hu).symm
                  have hgrowAll : store.length ≤ store'.length := le_trans hgrow₁ hgrow₂
                  have hlevels' : ∀ id < store.length, store'.levelOf id ≤ store.levelOf id :=
                    fun id hi => le_trans (MStore.unify_levelOf_le hu id) (hbodyPost.levels id hi)
                  have hpre' : InferPre k ctx store' :=
                    pre.extend (MStore.unify_safe hbodyPost.safe hbodyPost.tyAllocated
                      hresultAlloc₁ hu) hgrowAll hlevels'
                  have hargsAllocated' : ∀ arg ∈ args, arg.Allocated store' :=
                    fun arg harg => Ty.allocated_mono hgrowAll (argsAllocated arg harg)
                  have hargsLevels' : ∀ arg ∈ args, arg.LevelBounded store' k :=
                    fun arg harg =>
                      Ty.levelBounded_mono (argsAllocated arg harg) (argsLevels arg harg) hlevels'
                  have hresultAllocated' : resultTy.Allocated store' :=
                    Ty.allocated_mono hgrowAll resultAllocated
                  have hresultLevels' : resultTy.LevelBounded store' k :=
                    Ty.levelBounded_mono resultAllocated resultLevels hlevels'
                  have hindices' : ∀ pat ∈ rest.map (·.1),
                      pat.ctor.index < decl.ctors.length :=
                    fun pat hpat => indices pat (by simp [hpat])
                  have hrestBodies : ∀ branch ∈ rest, ∀ k ctx store, InferPre k ctx store →
                      InferSpec sig k ctx branch.2 store :=
                    fun branch hbranch => bodies branch (by simp [hbranch])
                  have hrestSpec := ih hrestBodies hindices' hpre' argsWF hargsAllocated'
                    hargsLevels' hresultAllocated' hresultLevels'
                  cases hr : inferBranches sig k ctx decl args resultTy rest store' with
                  | error restError =>
                      have h : inferBranches sig k ctx decl args resultTy
                          ((pattern, body) :: rest) store =
                          .error (InferError.nextBranch restError) := by
                        simp only [hbind, hfields, hb, MStore.unifyAt, Option.getDM,
                          Bind.bind, Except.bind, Pure.pure, Except.pure,
                          mapError_ok, mapError_error, hu, hr]
                      simp only [BranchesSpec, h]
                      intro valuation models branchesElab hmap hall
                      obtain ⟨headElab, tailElab, rfl, hheadElab, htailElab⟩ :=
                        List.map_eq_cons_iff.mp hmap
                      obtain ⟨patternElab, bodyElab⟩ := headElab
                      simp only at hheadElab
                      subst patternElab
                      have htyping : Typing sig (k + ctor.existentials)
                          (Ctx.realize (((ctor.fields.map fun field =>
                            field.lift.instantiate (args ++ rigidBlock k ctor.existentials)).map
                            Scheme.mono).reverse ++ ctx) valuation)
                          body bodyElab (resultTy.realize valuation) := by
                        rw [Ctx.realize_fieldCtx_append]
                        exact Elaborates.typing
                          (hall 0 pattern body bodyElab ctor (by simp) (by simp) hfields)
                      obtain ⟨extended, hmodels, hagree, _, hty⟩ :=
                        hbodyPost.principal valuation models bodyElab _ htyping
                      have hargsExt : args.map (·.realize extended) =
                          args.map (·.realize valuation) :=
                        List.map_congr_left fun arg harg =>
                          Ty.realize_congr (argsAllocated arg harg) (fun id hi => (hagree id hi).symm)
                      have hresultExt : resultTy.realize extended = resultTy.realize valuation :=
                        Ty.realize_congr resultAllocated (fun id hi => (hagree id hi).symm)
                      have hunifies : bodyResult.ty.realize extended = resultTy.realize extended :=
                        hty.trans hresultExt.symm
                      obtain ⟨result, hresult, hmodels'⟩ :=
                        MStore.unify_complete hbodyPost.safe hbodyPost.tyAllocated hresultAlloc₁
                          hmodels hunifies
                      rw [hu] at hresult
                      have hresultEq : result = store' := (Except.ok.inj hresult).symm
                      subst hresultEq
                      have hrestNone := hrestSpec
                      unfold BranchesSpec at hrestNone
                      rw [hr] at hrestNone
                      refine hrestNone extended hmodels' tailElab htailElab ?_
                      intro i pat srcElab bodyElab' ctor' hbr hbrElab hfields'
                      have htyping' := hall (i + 1) pat srcElab bodyElab' ctor'
                        (by simpa using hbr) (by simpa using hbrElab) hfields'
                      rw [ctx_realize_congr_of_agree pre hagree, hargsExt, hresultExt]
                      exact htyping'
                  | ok restFull =>
                      obtain ⟨restResult, restTypes⟩ := restFull
                      have h : inferBranches sig k ctx decl args resultTy
                          ((pattern, body) :: rest) store =
                          .ok (((pattern, bodyResult.elaboration) :: restResult.1, restResult.2),
                            .node resultTy ((ctor.fields.map fun field =>
                              field.lift.instantiate (args ++ rigidBlock k ctor.existentials)).map
                              (.node · []) ++ [bodyResult.types]) :: restTypes) := by
                        simp only [hbind, hfields, hb, MStore.unifyAt, Option.getDM,
                          Bind.bind, Except.bind, Pure.pure, Except.pure, mapError_ok, hu, hr]
                      have hrestPost : BranchesPost sig k ctx decl args resultTy rest store'
                          restResult := by
                        have hspec := hrestSpec
                        unfold BranchesSpec at hspec
                        rw [hr] at hspec
                        simpa only using hspec
                      simp only [BranchesSpec, h]
                      have hgrowRest : store'.length ≤ restResult.2.length := hrestPost.grows
                      have hgrowFinal : bodyResult.store.length ≤ restResult.2.length :=
                        le_trans hgrow₂ hgrowRest
                      refine
                        { safe := hrestPost.safe
                          grows := le_trans hgrowAll hgrowRest
                          levels := ?_
                          patterns := by simp [hrestPost.patterns]
                          elabAllocated := ?_
                          anchored := ?_
                          sound := ?_
                          principal := ?_ }
                      · intro id hi
                        refine le_trans (hrestPost.levels id (lt_of_lt_of_le hi hgrowAll)) ?_
                        exact le_trans (MStore.unify_levelOf_le hu id) (hbodyPost.levels id hi)
                      · intro branch hbranch ann hann
                        rcases List.mem_cons.mp hbranch with rfl | hbranch
                        · exact Ty.allocated_mono hgrowFinal (hbodyPost.elabAllocated ann hann)
                        · exact hrestPost.elabAllocated branch hbranch ann hann
                      · intro start level hlt hstart hanch
                        have h₁ := hbodyPost.anchored start level (by omega) hstart hanch
                        have h₂ : store'.Anchored start level := MStore.unify_anchored h₁ hu
                        exact hrestPost.anchored start level hlt
                          (le_trans hstart hgrowAll) h₂
                      · -- sound
                        intro valuation models
                        obtain ⟨hmodelsStore', hbranchesRest⟩ := hrestPost.sound valuation models
                        obtain ⟨hmodelsBody, htyEq⟩ := MStore.unify_sound hu hmodelsStore'
                        obtain ⟨hmodelsStore, hbodyElab⟩ :=
                          hbodyPost.sound valuation hmodelsBody
                        refine ⟨hmodelsStore, ?_⟩
                        intro i pat srcElab bodyElab' ctor' hbr hbrElab hfields'
                        cases i with
                        | zero =>
                            simp only [List.getElem?_cons_zero, Option.some.injEq,
                              Prod.mk.injEq] at hbr hbrElab
                            obtain ⟨rfl, rfl⟩ := hbr
                            obtain ⟨-, rfl⟩ := hbrElab
                            have hfieldsEq : ctor = ctor' := by
                              rw [hfields] at hfields'
                              exact Option.some.inj hfields'
                            subst hfieldsEq
                            rw [← Ctx.realize_fieldCtx_append, ← htyEq]
                            exact hbodyElab
                        | succ i =>
                            exact hbranchesRest i pat srcElab bodyElab' ctor'
                              (by simpa using hbr) (by simpa using hbrElab) hfields'
                      · -- principal
                        intro valuation models branchesElab hmap hall
                        obtain ⟨headElab, tailElab, rfl, hheadElab, htailElab⟩ :=
                          List.map_eq_cons_iff.mp hmap
                        obtain ⟨patternElab, bodyElab⟩ := headElab
                        simp only at hheadElab
                        subst patternElab
                        have htyping : Typing sig (k + ctor.existentials)
                            (Ctx.realize (((ctor.fields.map fun field =>
                              field.lift.instantiate (args ++ rigidBlock k ctor.existentials)).map
                              Scheme.mono).reverse ++ ctx) valuation)
                            body bodyElab (resultTy.realize valuation) := by
                          rw [Ctx.realize_fieldCtx_append]
                          exact hall 0 pattern body bodyElab ctor (by simp) (by simp) hfields
                        obtain ⟨extended₁, hmodels₁, hagree₁, helab₁, hty₁⟩ :=
                          hbodyPost.principal valuation models bodyElab _ htyping
                        have hargs₁ : args.map (·.realize extended₁) =
                            args.map (·.realize valuation) :=
                          List.map_congr_left fun arg harg =>
                            Ty.realize_congr (argsAllocated arg harg) (fun id hi => (hagree₁ id hi).symm)
                        have hresult₁ : resultTy.realize extended₁ = resultTy.realize valuation :=
                          Ty.realize_congr resultAllocated (fun id hi => (hagree₁ id hi).symm)
                        have hunifies : bodyResult.ty.realize extended₁ =
                            resultTy.realize extended₁ :=
                          hty₁.trans hresult₁.symm
                        obtain ⟨result, hresult, hmodels₂⟩ :=
                          MStore.unify_complete hbodyPost.safe hbodyPost.tyAllocated hresultAlloc₁
                            hmodels₁ hunifies
                        rw [hu] at hresult
                        have hresultEq : result = store' := (Except.ok.inj hresult).symm
                        subst hresultEq
                        have htypingRest : ∀ (i : Nat) pat srcElab bodyElab' ctor',
                            rest[i]? = some (pat, srcElab) →
                            tailElab[i]? = some (pat, bodyElab') →
                            decl.ctors[pat.ctor.index]? = some ctor' →
                            Typing sig (k + ctor'.existentials)
                              (ctor'.fieldCtx (args.map (·.realize extended₁))
                                (rigidBlock k ctor'.existentials) ++ ctx.realize extended₁)
                              srcElab bodyElab' (resultTy.realize extended₁) := by
                          intro i pat srcElab bodyElab' ctor' hbr hbrElab hfields'
                          have htyping' := hall (i + 1) pat srcElab bodyElab' ctor'
                            (by simpa using hbr) (by simpa using hbrElab) hfields'
                          rw [ctx_realize_congr_of_agree pre hagree₁, hargs₁, hresult₁]
                          exact htyping'
                        obtain ⟨extended, hmodelsExt, hagreeExt, hmapExt⟩ :=
                          hrestPost.principal extended₁ hmodels₂ tailElab htailElab htypingRest
                        refine ⟨extended, hmodelsExt, ?_, ?_⟩
                        · intro id hi
                          exact (hagree₁ id hi).trans (hagreeExt id (lt_of_lt_of_le hi hgrowAll))
                        · have hagreeExt₁ : Agree bodyResult.store.length extended₁ extended :=
                            fun id hi => hagreeExt id (lt_of_lt_of_le hi hgrow₂)
                          rw [List.map_cons, hmapExt]
                          simp only [List.cons.injEq, Prod.mk.injEq, and_true, true_and]
                          rw [← Expr.realize_agree (store := bodyResult.store)
                            hbodyPost.elabAllocated hagreeExt₁]
                          exact helab₁

/-- A successful declaration lookup gives a well-formed declaration. -/
private theorem Signature.decl?_wf {sig : Signature} {type : Nat} {decl : DataDecl}
    (found : sig.decl? type = some decl) : decl.WF := by
  cases h : sig[type]? with
  | none => simp [Signature.decl?, h] at found
  | some other =>
      by_cases hwf : other.WF
      · simp only [Signature.decl?, h, Option.bind_eq_bind, Option.bind_some] at found
        simp only [hwf, if_true, Option.some.injEq] at found
        subst found
        exact hwf
      · simp only [Signature.decl?, h, Option.bind_eq_bind, Option.bind_some] at found
        simp only [hwf, if_false] at found
        cases found

/-- The facts a successful branch check records about the patterns. -/
private theorem branches_all_facts {branches : List (Pattern × Source)} {first : Pattern}
    {decl : DataDecl}
    (all : branches.all (fun branch => (branch.1.ctor.type == first.ctor.type) &&
      decide (branch.1.ctor.index < decl.ctors.length)) = true) :
    ∀ pattern ∈ branches.map (·.1), pattern.ctor.type = first.ctor.type ∧
      pattern.ctor.index < decl.ctors.length := by
  rw [List.all_eq_true] at all
  intro pattern hpattern
  obtain ⟨branch, hbranch, hpatternEq⟩ := List.mem_map.mp hpattern
  subst hpatternEq
  have h := all branch hbranch
  simpa only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] using h

/-- Every pattern of a match that typing accepts passes the check. -/
private theorem branches_all_of_facts {branches : List (Pattern × Source)} {first : Pattern}
    {decl : DataDecl}
    (patterns : ∀ pattern ∈ branches.map (·.1), pattern.ctor.type = first.ctor.type ∧
      pattern.ctor.index < decl.ctors.length) :
    branches.all (fun branch => (branch.1.ctor.type == first.ctor.type) &&
      decide (branch.1.ctor.index < decl.ctors.length)) = true := by
  rw [List.all_eq_true]
  intro branch hbranch
  obtain ⟨hpattern, hind⟩ := patterns branch.1 (List.mem_map.mpr ⟨branch, hbranch, rfl⟩)
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq]
  exact ⟨hpattern, hind⟩

/-- The binder-count check records that every pattern binds its constructor's
fields. -/
private theorem branches_arity_facts {branches : List (Pattern × Source)} {decl : DataDecl}
    (all : branches.all (fun branch => decl.ctors[branch.1.ctor.index]?.all fun ctor =>
      branch.1.binders == ctor.fields.length) = true) :
    ∀ pattern ∈ branches.map (·.1), ∀ ctor, decl.ctors[pattern.ctor.index]? = some ctor →
      pattern.binders = ctor.fields.length := by
  rw [List.all_eq_true] at all
  intro pattern hpattern ctor hctor
  obtain ⟨branch, hbranch, hpatternEq⟩ := List.mem_map.mp hpattern
  subst hpatternEq
  have h := all branch hbranch
  rw [Option.all_eq_true] at h
  simpa using h ctor hctor

/-- Every pattern of a match that typing accepts passes the binder-count check. -/
private theorem branches_arity_of_facts {branches : List (Pattern × Source)} {decl : DataDecl}
    (facts : ∀ pattern ∈ branches.map (·.1), ∀ ctor,
      decl.ctors[pattern.ctor.index]? = some ctor → pattern.binders = ctor.fields.length) :
    branches.all (fun branch => decl.ctors[branch.1.ctor.index]?.all fun ctor =>
      branch.1.binders == ctor.fields.length) = true := by
  rw [List.all_eq_true]
  intro branch hbranch
  rw [Option.all_eq_true]
  intro ctor hctor
  have := facts branch.1 (List.mem_map.mpr ⟨branch, hbranch, rfl⟩) ctor hctor
  simpa using this

theorem inferAt_spec_match {sig : Signature} {scrutinee : Source}
    {branches : List (Pattern × Source)}
    (scrutineeSpec : ∀ k ctx store, InferPre k ctx store → InferSpec sig k ctx scrutinee store)
    (bodies : ∀ branch ∈ branches, ∀ k ctx store, InferPre k ctx store →
      InferSpec sig k ctx branch.2 store)
    (pre : InferPre k ctx store) :
    InferSpec sig k ctx (.match scrutinee branches) store := by
  have hbind : inferAt sig k ctx (.match scrutinee branches) store = (do
      let (first, _) ← branches.head?.getDM (throw (.here .emptyMatch))
      let decl ← (sig.decl? first.ctor.type).getDM (throw ⟨[.matchBranch 0], .unknownType⟩)
      if ¬ branches.all (fun branch =>
          branch.1.ctor.type == first.ctor.type && decide (branch.1.ctor.index < decl.ctors.length)) then
        throw ⟨[.matchBranch (branches.findIdx fun branch =>
          !(branch.1.ctor.type == first.ctor.type && decide (branch.1.ctor.index < decl.ctors.length)))],
          .foreignPattern⟩
      if ¬ branches.all (fun branch => decl.ctors[branch.1.ctor.index]?.all fun ctor =>
          branch.1.binders == ctor.fields.length) then
        throw ⟨[.matchBranch (branches.findIdx fun branch =>
          !(decl.ctors[branch.1.ctor.index]?.all fun ctor =>
            branch.1.binders == ctor.fields.length))],
          .patternArity⟩
      let scrutineeResult ← (inferAt sig k ctx scrutinee store).mapError
        (.under .matchScrutinee)
      let (args, store) := scrutineeResult.store.freshMany k decl.params
      let store ← store.unifyAt [.matchScrutinee] scrutineeResult.ty
        (Ty.apps (.con first.ctor.type) args)
      let (resultTy, store) := store.fresh k
      let ((branchesElab, store), branchTypes) ←
        inferBranches sig k ctx decl args resultTy branches store
      pure ⟨resultTy, .match scrutineeResult.elaboration branchesElab, store,
        .node resultTy (scrutineeResult.types :: branchTypes)⟩) := rfl
  cases hhead : branches.head? with
  | none =>
      have hbranches : branches = [] := List.head?_eq_none_iff.mp hhead
      subst hbranches
      have h : inferAt sig k ctx (.match scrutinee []) store =
          .error (.here .emptyMatch) := by
        simp only [hbind, hhead, Option.getDM, Bind.bind, Except.bind]
      simp only [InferSpec, h]
      intro valuation models elaboration ty typing
      obtain ⟨type, decl, args, scrutineeElab, branchesElab, hdecl, harity, hne,
        hpatterns, _, hmap, hscrut, hall, _, helab⟩ := TypingWith.match_inv typing
      exact hne rfl
  | some headPair =>
      obtain ⟨first, second⟩ := headPair
      obtain ⟨restBranches, rfl⟩ := List.head?_eq_some_iff.mp hhead
      have hmemHead : first ∈ ((first, second) :: restBranches).map (·.1) := by simp
      cases hdecl : sig.decl? first.ctor.type with
      | none =>
          have h : inferAt sig k ctx
              (.match scrutinee ((first, second) :: restBranches)) store =
              .error ⟨[.matchBranch 0], .unknownType⟩ := by
            simp only [hbind, hhead, hdecl, Option.getDM, Bind.bind, Except.bind,
              Pure.pure, Except.pure]
          simp only [InferSpec, h]
          intro valuation models elaboration ty typing
          obtain ⟨type, declTy, args, scrutineeElab, branchesElab, hdeclTy, harity,
            hne, hpatterns, _, hmap, hscrut, hall, _, helab⟩ := TypingWith.match_inv typing
          have htype : first.ctor.type = type := (hpatterns first hmemHead).1
          rw [← htype] at hdeclTy
          rw [hdecl] at hdeclTy
          cases hdeclTy
      | some decl =>
          by_cases hallCheck : ((first, second) :: restBranches).all (fun branch =>
              branch.1.ctor.type == first.ctor.type && decide (branch.1.ctor.index < decl.ctors.length)) = true
          · by_cases hallArity : ((first, second) :: restBranches).all (fun branch =>
                decl.ctors[branch.1.ctor.index]?.all fun ctor =>
                  branch.1.binders == ctor.fields.length) = true
            · cases hs : inferAt sig k ctx scrutinee store with
              | error scrutineeError =>
                  have h : inferAt sig k ctx
                      (.match scrutinee ((first, second) :: restBranches)) store =
                      .error (.under .matchScrutinee scrutineeError) := by
                    simp only [hbind, hhead, hdecl, hallCheck, hallArity, hs, not_true, ite_false, Option.getDM,
                      Bind.bind, Except.bind, Pure.pure, Except.pure, mapError_error]
                  simp only [InferSpec, h]
                  intro valuation models elaboration ty typing
                  obtain ⟨type, declTy, args, scrutineeElab, branchesElab, hdeclTy,
                    harity, hne, hpatterns, _, hmap, hscrut, hall, _, helab⟩ := TypingWith.match_inv typing
                  have hscrutNone := scrutineeSpec k ctx store pre
                  unfold InferSpec at hscrutNone
                  rw [hs] at hscrutNone
                  exact hscrutNone valuation models _ _ hscrut
              | ok scrutineeResult =>
                  have hscrutPost : InferPost sig k ctx scrutinee store scrutineeResult := by
                    have hspec := scrutineeSpec k ctx store pre
                    unfold InferSpec at hspec
                    rw [hs] at hspec
                    simpa only using hspec
                  have hsafeA : (scrutineeResult.store.freshMany k decl.params).2.Safe := by
                    rw [MStore.freshMany_snd]
                    exact MStore.append_unsolved_safe hscrutPost.safe
                  have hgrowA : scrutineeResult.store.length ≤
                      (scrutineeResult.store.freshMany k decl.params).2.length := by
                    rw [MStore.freshMany_snd]; simp
                  have hlenA : (scrutineeResult.store.freshMany k decl.params).2.length =
                      scrutineeResult.store.length + decl.params := by
                    rw [MStore.freshMany_snd]; simp
                  have hleftAllocA : scrutineeResult.ty.Allocated
                      (scrutineeResult.store.freshMany k decl.params).2 :=
                    Ty.allocated_mono hgrowA hscrutPost.tyAllocated
                  have hrightAlloc : (Ty.apps (.con first.ctor.type)
                      (scrutineeResult.store.freshMany k decl.params).1).Allocated
                      (scrutineeResult.store.freshMany k decl.params).2 := by
                    refine Ty.allocated_apps (.con first.ctor.type) _ ?_ ?_
                    · intro id hid; simp [Ty.vars] at hid
                    · exact freshMany_args_allocated
                  cases hu : (scrutineeResult.store.freshMany k decl.params).2.unify
                      scrutineeResult.ty
                      (Ty.apps (.con first.ctor.type)
                        (scrutineeResult.store.freshMany k decl.params).1) with
                  | error cause =>
                      have h : inferAt sig k ctx
                          (.match scrutinee ((first, second) :: restBranches)) store =
                          .error ⟨[.matchScrutinee], .mismatch
                            ((scrutineeResult.store.freshMany k decl.params).2.apply
                              (Ty.apps (.con first.ctor.type)
                                (scrutineeResult.store.freshMany k decl.params).1))
                            ((scrutineeResult.store.freshMany k decl.params).2.apply
                              scrutineeResult.ty) cause⟩ := by
                        simp only [hbind, hhead, hdecl, hallCheck, hallArity, hs, not_true, ite_false, MStore.unifyAt,
                          Option.getDM, Bind.bind, Except.bind, Pure.pure, Except.pure,
                          mapError_ok, mapError_error, hu]
                      simp only [InferSpec, h]
                      intro valuation models elaboration ty typing
                      obtain ⟨type, declTy, argsSem, scrutineeElab, branchesElab, hdeclTy,
                        haritySem, hne, hpatterns, _, hmap, hscrut, hall, _, helab⟩ :=
                        TypingWith.match_inv typing
                      have htype : first.ctor.type = type := (hpatterns first hmemHead).1
                      rw [← htype] at hdeclTy
                      rw [hdecl] at hdeclTy
                      cases hdeclTy
                      have hctxWF : (ctx.realize valuation).WF k :=
                        Ctx.realize_wf models pre.ctxWF pre.ctxAllocated pre.ctxLevels
                      have hargsSemWF : ∀ arg ∈ argsSem, arg.WF k :=
                        (Ty.wf_apps_parts
                          (TypingWith.regular hctxWF (Elaborates.typing hscrut))).2
                      obtain ⟨ext₁, hmodels₁, hagree₁, _, hty₁⟩ :=
                        hscrutPost.principal valuation models scrutineeElab _
                          (Elaborates.typing hscrut)
                      obtain ⟨ext₂, hmodels₂, hagree₂, hargs₂⟩ :=
                        MStore.freshMany_principal hscrutPost.safe hmodels₁ haritySem hargsSemWF
                      have hscrut₂ : scrutineeResult.ty.realize ext₂ =
                          Ty.apps (.con type) argsSem := by
                        rw [← Ty.realize_congr hscrutPost.tyAllocated hagree₂]
                        exact hty₁
                      have hunifies : scrutineeResult.ty.realize ext₂ =
                          (Ty.apps (.con first.ctor.type)
                            (scrutineeResult.store.freshMany k decl.params).1).realize ext₂ := by
                        rw [Ty.realize_apps, hargs₂, htype]
                        exact hscrut₂
                      obtain ⟨result, hresult, _⟩ :=
                        MStore.unify_complete (store :=
                          (scrutineeResult.store.freshMany k decl.params).2) hsafeA hleftAllocA
                          hrightAlloc hmodels₂ hunifies
                      rw [hu] at hresult
                      cases hresult
                  | ok storeU =>
                      have hdeclWF : decl.WF := Signature.decl?_wf hdecl
                      have hargsLength : (scrutineeResult.store.freshMany k decl.params).1.length
                          = decl.params := freshMany_fst_length _ _ _
                      have hindices : ∀ pattern ∈ ((first, second) :: restBranches).map (·.1),
                          pattern.ctor.index < decl.ctors.length :=
                        fun pattern hmem => (branches_all_facts hallCheck pattern hmem).2
                      have hgrowU : (scrutineeResult.store.freshMany k decl.params).2.length ≤
                          storeU.length := le_of_eq (MStore.unify_length hu).symm
                      have hgrowB : store.length ≤
                          (scrutineeResult.store.freshMany k decl.params).2.length :=
                        le_trans hscrutPost.grows hgrowA
                      have hgrowStoreR : store.length ≤ (storeU.fresh k).2.length := by
                        rw [MStore.fresh_eq]
                        simp only [List.length_append, List.length_replicate]
                        omega
                      have hgrowU2 : store.length ≤ storeU.length := by omega
                      have hgrowAR : (scrutineeResult.store.freshMany k decl.params).2.length ≤
                          (storeU.fresh k).2.length := by
                        rw [MStore.fresh_eq]
                        simp only [List.length_append, List.length_replicate]
                        omega
                      have hsafeU : storeU.Safe :=
                        MStore.unify_safe (store :=
                          (scrutineeResult.store.freshMany k decl.params).2) hsafeA hleftAllocA
                          hrightAlloc hu
                      have hlevelsAU : ∀ id < (scrutineeResult.store.freshMany k
                          decl.params).2.length,
                          (storeU.fresh k).2.levelOf id ≤
                            (scrutineeResult.store.freshMany k decl.params).2.levelOf id := by
                        intro id hi
                        have hidU : id < storeU.length := by
                          rw [MStore.unify_length hu]; exact hi
                        rw [MStore.fresh_eq, MStore.append_unsolved_levelOf, if_pos hidU]
                        exact MStore.unify_levelOf_le hu id
                      have hlevelsU : ∀ id < store.length, (storeU.fresh k).2.levelOf id ≤
                          store.levelOf id := by
                        intro id hi
                        refine le_trans (hlevelsAU id (lt_of_lt_of_le hi ?_)) ?_
                        · rw [MStore.freshMany_snd]
                          simp only [List.length_append, List.length_replicate]
                          have := hgrowB
                          have := hlenA
                          omega
                        · rw [MStore.freshMany_snd, MStore.append_unsolved_levelOf,
                            if_pos (lt_of_lt_of_le hi hscrutPost.grows)]
                          exact hscrutPost.levels id hi
                      have hsafeR : (storeU.fresh k).2.Safe := by
                        rw [MStore.fresh_eq]
                        exact MStore.append_unsolved_safe hsafeU
                      have hpreR : InferPre k ctx (storeU.fresh k).2 :=
                        pre.extend hsafeR hgrowStoreR hlevelsU
                      have hargsAllocR : ∀ arg ∈ (scrutineeResult.store.freshMany k
                          decl.params).1, arg.Allocated (storeU.fresh k).2 :=
                        fun arg harg => Ty.allocated_mono hgrowAR
                          (freshMany_args_allocated arg harg)
                      have hargsLevR : ∀ arg ∈ (scrutineeResult.store.freshMany k
                          decl.params).1, arg.LevelBounded (storeU.fresh k).2 k :=
                        fun arg harg => Ty.levelBounded_mono (freshMany_args_allocated arg harg)
                          (freshMany_args_levelBounded arg harg) hlevelsAU
                      have hbranchesSpec : BranchesSpec sig k ctx decl
                          (scrutineeResult.store.freshMany k decl.params).1 (storeU.fresh k).1
                          ((first, second) :: restBranches) (storeU.fresh k).2 :=
                        inferBranches_spec bodies hdeclWF hargsLength hindices hpreR
                          freshMany_args_wf hargsAllocR hargsLevR trivial fresh_allocated
                          fresh_levelBounded
                      cases hbr : inferBranches sig k ctx decl
                          (scrutineeResult.store.freshMany k decl.params).1 (storeU.fresh k).1
                          ((first, second) :: restBranches) (storeU.fresh k).2 with
                      | error restError =>
                          have h : inferAt sig k ctx
                              (.match scrutinee ((first, second) :: restBranches)) store =
                              .error restError := by
                            simp only [hbind, hhead, hdecl, hallCheck, hallArity, hs, not_true, ite_false, MStore.unifyAt,
                              Option.getDM, Bind.bind, Except.bind, Pure.pure, Except.pure,
                              mapError_ok, hu, hbr]
                          simp only [InferSpec, h]
                          intro valuation models elaboration ty typing
                          obtain ⟨type, declTy, argsSem, scrutineeElab, branchesElab, hdeclTy,
                            haritySem, hne, hpatterns, _, hmap, hscrut, hall, _, helab⟩ :=
                            TypingWith.match_inv typing
                          have htype : first.ctor.type = type := (hpatterns first hmemHead).1
                          rw [← htype] at hdeclTy
                          rw [hdecl] at hdeclTy
                          cases hdeclTy
                          have hctxWF : (ctx.realize valuation).WF k :=
                            Ctx.realize_wf models pre.ctxWF pre.ctxAllocated pre.ctxLevels
                          have hargsSemWF : ∀ arg ∈ argsSem, arg.WF k :=
                            (Ty.wf_apps_parts
                              (TypingWith.regular hctxWF (Elaborates.typing hscrut))).2
                          obtain ⟨ext₁, hmodels₁, hagree₁, _, hty₁⟩ :=
                            hscrutPost.principal valuation models scrutineeElab _
                              (Elaborates.typing hscrut)
                          obtain ⟨ext₂, hmodels₂, hagree₂, hargs₂⟩ :=
                            MStore.freshMany_principal hscrutPost.safe hmodels₁ haritySem
                              hargsSemWF
                          have hscrut₂ : scrutineeResult.ty.realize ext₂ =
                              Ty.apps (.con type) argsSem := by
                            rw [← Ty.realize_congr hscrutPost.tyAllocated hagree₂]
                            exact hty₁
                          have hunifies : scrutineeResult.ty.realize ext₂ =
                              (Ty.apps (.con first.ctor.type)
                                (scrutineeResult.store.freshMany k decl.params).1).realize
                                ext₂ := by
                            rw [Ty.realize_apps, hargs₂, htype]
                            exact hscrut₂
                          obtain ⟨storeUnified, hresult, hmodelsU⟩ :=
                            MStore.unify_complete (store :=
                              (scrutineeResult.store.freshMany k decl.params).2) hsafeA
                              hleftAllocA hrightAlloc hmodels₂ hunifies
                          rw [hu] at hresult
                          have hresultEq : storeUnified = storeU :=
                            (Except.ok.inj hresult).symm
                          subst storeUnified
                          have hresultWF : ty.WF k :=
                            TypingWith.regular hctxWF typing
                          let ext₃ : Valuation := Function.update ext₂ storeU.length ty
                          have hagreeU : Agree storeU.length ext₂ ext₃ := by
                            intro id hi
                            have hne : id ≠ storeU.length := by omega
                            simp only [ext₃, Function.update]
                            rw [dif_neg hne]
                          have hmodelsR : (storeU.fresh k).2.Models ext₃ := by
                            rw [MStore.fresh_eq, MStore.models_append_unsolved]
                            refine ⟨?_, ?_⟩
                            · exact MStore.Models.congr hsafeU hmodelsU hagreeU
                            · intro i hi
                              have hi0 : i = 0 := by omega
                              subst hi0
                              simpa [ext₃, Function.update] using hresultWF
                          have hargs₃ : (scrutineeResult.store.freshMany k decl.params).1.map
                              (·.realize ext₃) =
                              (scrutineeResult.store.freshMany k decl.params).1.map
                                (·.realize ext₂) := by
                            apply List.map_congr_left
                            intro arg harg
                            rw [MStore.freshMany_fst] at harg
                            simp only [List.mem_map, List.mem_range] at harg
                            obtain ⟨i, hi, rfl⟩ := harg
                            show ext₃ (scrutineeResult.store.length + i) =
                              ext₂ (scrutineeResult.store.length + i)
                            have hne : scrutineeResult.store.length + i ≠ storeU.length := by
                              rw [MStore.unify_length hu, MStore.freshMany_snd]
                              simp only [List.length_append, List.length_replicate]
                              omega
                            simp only [ext₃, Function.update]
                            rw [dif_neg hne]
                          have hagree₁₃ : Agree scrutineeResult.store.length ext₁ ext₃ := by
                            intro id hi
                            exact (hagree₂ id hi).trans (hagreeU id
                              (lt_of_lt_of_le hi (le_trans hgrowA hgrowU)))
                          have hagreeVal₃ : Agree store.length valuation ext₃ := by
                            intro id hi
                            exact (hagree₁ id hi).trans
                              (hagree₁₃ id (lt_of_lt_of_le hi hscrutPost.grows))
                          have hresult₃ : ((storeU.fresh k).1).realize ext₃ = ty := by
                            show ext₃ storeU.length = ty
                            simp only [ext₃, Function.update]
                            simp
                          have hallR : ∀ (i : Nat) pattern body bodyElab ctor,
                              ((first, second) :: restBranches)[i]? = some (pattern, body) →
                              branchesElab[i]? = some (pattern, bodyElab) →
                              decl.ctors[pattern.ctor.index]? = some ctor →
                              Elaborates sig (k + ctor.existentials)
                                (ctor.fieldCtx
                                  ((scrutineeResult.store.freshMany k decl.params).1.map
                                    (·.realize ext₃))
                                  (rigidBlock k ctor.existentials) ++ ctx.realize ext₃)
                                body bodyElab (((storeU.fresh k).1).realize ext₃) := by
                            intro i pattern body bodyElab ctor hbr' hbrElab hfields'
                            have h := hall i pattern body bodyElab ctor hbr' hbrElab hfields'
                            rw [ctx_realize_congr_of_agree pre hagreeVal₃, hargs₃.trans hargs₂,
                              hresult₃]
                            exact h
                          have hbranchesNone := hbranchesSpec
                          unfold BranchesSpec at hbranchesNone
                          rw [hbr] at hbranchesNone
                          exact hbranchesNone ext₃ hmodelsR branchesElab hmap hallR
                      | ok branchFull =>
                          obtain ⟨branchResult, branchTypes⟩ := branchFull
                          have h : inferAt sig k ctx
                              (.match scrutinee ((first, second) :: restBranches)) store =
                              .ok ⟨(storeU.fresh k).1,
                                .match scrutineeResult.elaboration branchResult.1,
                                branchResult.2,
                                .node (storeU.fresh k).1 (scrutineeResult.types :: branchTypes)⟩ := by
                            simp only [hbind, hhead, hdecl, hallCheck, hallArity, hs, not_true, ite_false, MStore.unifyAt,
                              Option.getDM, Bind.bind, Except.bind, Pure.pure, Except.pure,
                              mapError_ok, hu, hbr]
                          have hbrPost : BranchesPost sig k ctx decl
                              (scrutineeResult.store.freshMany k decl.params).1 (storeU.fresh k).1
                              ((first, second) :: restBranches) (storeU.fresh k).2
                              branchResult := by
                            have hspec := hbranchesSpec
                            unfold BranchesSpec at hspec
                            rw [hbr] at hspec
                            simpa only using hspec
                          simp only [InferSpec, h]
                          have hgrowBranches : (storeU.fresh k).2.length ≤ branchResult.2.length :=
                            hbrPost.grows
                          have hgrowFinal : store.length ≤ branchResult.2.length :=
                            le_trans hgrowStoreR hgrowBranches
                          have hgrowScrut : scrutineeResult.store.length ≤
                              branchResult.2.length :=
                            le_trans hgrowA (le_trans hgrowAR hgrowBranches)
                          have hgrowUFinal : storeU.length ≤ branchResult.2.length := by
                            have h1 : storeU.length ≤ (storeU.fresh k).2.length := by
                              rw [MStore.fresh_eq]; simp
                            omega
                          refine
                            { safe := hbrPost.safe
                              grows := hgrowFinal
                              levels := ?_
                              tyWF := trivial
                              tyAllocated := Ty.allocated_mono hgrowBranches fresh_allocated
                              tyLevels := Ty.levelBounded_mono fresh_allocated fresh_levelBounded
                                hbrPost.levels
                              elabAllocated := ?_
                              anchored := ?_
                              sound := ?_
                              principal := ?_ }
                          · -- levels
                            intro id hi
                            have hidR : id < (storeU.fresh k).2.length :=
                              lt_of_lt_of_le hi hgrowStoreR
                            have hidU : id < storeU.length := lt_of_lt_of_le hi hgrowU2
                            have h1 : branchResult.2.levelOf id ≤ (storeU.fresh k).2.levelOf id :=
                              hbrPost.levels id hidR
                            have h2 : (storeU.fresh k).2.levelOf id = storeU.levelOf id := by
                              rw [MStore.fresh_eq, MStore.append_unsolved_levelOf, if_pos hidU]
                            have h3 : storeU.levelOf id ≤
                                (scrutineeResult.store.freshMany k decl.params).2.levelOf id :=
                              MStore.unify_levelOf_le hu id
                            have h4 : (scrutineeResult.store.freshMany k decl.params).2.levelOf id =
                                scrutineeResult.store.levelOf id := by
                              rw [MStore.freshMany_snd, MStore.append_unsolved_levelOf,
                                if_pos (lt_of_lt_of_le hi hscrutPost.grows)]
                            have h5 : scrutineeResult.store.levelOf id ≤ store.levelOf id :=
                              hscrutPost.levels id hi
                            calc branchResult.2.levelOf id ≤ (storeU.fresh k).2.levelOf id := h1
                              _ = storeU.levelOf id := h2
                              _ ≤ (scrutineeResult.store.freshMany k decl.params).2.levelOf id := h3
                              _ = scrutineeResult.store.levelOf id := h4
                              _ ≤ store.levelOf id := h5
                          · -- elabAllocated
                            intro ann hann
                            simp only [Expr.anns, List.mem_append] at hann
                            rcases hann with hann | hann
                            · exact Ty.allocated_mono hgrowScrut (hscrutPost.elabAllocated ann hann)
                            · exact annsBranches_allocated hbrPost.elabAllocated ann hann
                          · -- anchored
                            intro start level hlt hstart hanch
                            have h₁ := hscrutPost.anchored start level hlt hstart hanch
                            have h₂ : (scrutineeResult.store.freshMany k decl.params).2.Anchored
                                start level := by
                              rw [MStore.freshMany_snd]
                              exact MStore.Anchored.append_unsolved h₁ hlt
                            have h₃ : storeU.Anchored start level := MStore.unify_anchored h₂ hu
                            have h₄ : (storeU.fresh k).2.Anchored start level := by
                              rw [MStore.fresh_eq]
                              exact MStore.Anchored.append_unsolved h₃ hlt
                            exact hbrPost.anchored start level hlt (le_trans hstart hgrowStoreR) h₄
                          · -- sound
                            intro valuation models
                            obtain ⟨hmodelsR, hbranchesElab⟩ := hbrPost.sound valuation models
                            have hmodelsU : storeU.Models valuation :=
                              MStore.Models.of_append_unsolved (store := storeU) (count := 1)
                                (level := k) hmodelsR
                            obtain ⟨hmodelsA, htyEq⟩ := MStore.unify_sound hu hmodelsU
                            have hmodelsScrut : scrutineeResult.store.Models valuation :=
                              MStore.Models.of_append_unsolved
                                (store := scrutineeResult.store) (count := decl.params)
                                (level := k) hmodelsA
                            obtain ⟨hmodelsStore, hscrutElab⟩ :=
                              hscrutPost.sound valuation hmodelsScrut
                            refine ⟨hmodelsStore, ?_⟩
                            have hreal : Ty.apps (.con first.ctor.type)
                                ((scrutineeResult.store.freshMany k decl.params).1.map
                                  (·.realize valuation)) =
                                (Ty.apps (.con first.ctor.type)
                                  (scrutineeResult.store.freshMany k decl.params).1).realize
                                  valuation := by
                              rw [Ty.realize_apps]
                              rfl
                            have hscrutGoal : Elaborates sig k (ctx.realize valuation) scrutinee
                                (scrutineeResult.elaboration.realize valuation)
                                (Ty.apps (.con first.ctor.type)
                                  ((scrutineeResult.store.freshMany k decl.params).1.map
                                    (·.realize valuation))) := by
                              rw [hreal, ← htyEq]
                              exact hscrutElab
                            have hbranchesGoal : ∀ (i : Nat) pattern body bodyElab ctor,
                                ((first, second) :: restBranches)[i]? = some (pattern, body) →
                                (branchResult.1.map
                                  (fun branch => (branch.1, branch.2.realize valuation)))[i]? =
                                  some (pattern, bodyElab) →
                                decl.ctors[pattern.ctor.index]? = some ctor →
                                Elaborates sig (k + ctor.existentials)
                                  (ctor.fieldCtx
                                    ((scrutineeResult.store.freshMany k decl.params).1.map
                                      (·.realize valuation))
                                    (rigidBlock k ctor.existentials) ++ ctx.realize valuation)
                                  body bodyElab (((storeU.fresh k).1).realize valuation) := by
                              intro i pattern body bodyElab ctor hbr' hbrElab hfields'
                              rw [List.getElem?_map] at hbrElab
                              cases hlookup : branchResult.1[i]? with
                              | none => simp [hlookup] at hbrElab
                              | some branch =>
                                  rw [hlookup] at hbrElab
                                  obtain ⟨hpat, hbody⟩ :=
                                    Prod.mk.inj (Option.some.inj hbrElab)
                                  subst hpat
                                  rw [← hbody]
                                  exact hbranchesElab i branch.1 body branch.2 ctor hbr'
                                    hlookup hfields'
                            have hfreshWF : (((storeU.fresh k).1).realize valuation).WF k := by
                              have hwf := ((MStore.models_append_unsolved (store := storeU)
                                (count := 1) (level := k)).1 hmodelsR).2 0 (by simp)
                              simpa [MStore.fresh_eq, Ty.realize, Ty.bind, Ty.subst] using hwf
                            simp only [Expr.realize, Expr.mapAnn, Expr.mapAnnBranches_eq]
                            exact TypingWith.«match» hscrutGoal hdecl
                              (by rw [List.length_map, hargsLength]) (by simp)
                              (fun pattern hmem => branches_all_facts hallCheck pattern hmem)
                              (fun pattern hmem ctor hctor =>
                                branches_arity_facts hallArity pattern hmem ctor hctor)
                              (by rw [List.map_map]; exact hbrPost.patterns)
                              hbranchesGoal hfreshWF
                          · -- principal
                            intro valuation models elaboration ty typing
                            have htyWF : ty.WF k := by
                              have hctxWF : (ctx.realize valuation).WF k :=
                                Ctx.realize_wf models pre.ctxWF pre.ctxAllocated pre.ctxLevels
                              exact TypingWith.regular hctxWF typing
                            obtain ⟨type, declTy, argsSem, scrutineeElab, branchesElab, hdeclTy,
                              haritySem, hne, hpatterns, _, hmap, hscrut, hall, _, helab⟩ :=
                              TypingWith.match_inv typing
                            subst helab
                            have htype : first.ctor.type = type := (hpatterns first hmemHead).1
                            rw [← htype] at hdeclTy
                            rw [hdecl] at hdeclTy
                            cases hdeclTy
                            have hctxWF : (ctx.realize valuation).WF k :=
                              Ctx.realize_wf models pre.ctxWF pre.ctxAllocated pre.ctxLevels
                            have hargsSemWF : ∀ arg ∈ argsSem, arg.WF k :=
                              (Ty.wf_apps_parts (TypingWith.regular hctxWF hscrut)).2
                            obtain ⟨ext₁, hmodels₁, hagree₁, helab₁, hty₁⟩ :=
                              hscrutPost.principal valuation models scrutineeElab _ hscrut
                            obtain ⟨ext₂, hmodels₂, hagree₂, hargs₂⟩ :=
                              MStore.freshMany_principal hscrutPost.safe hmodels₁ haritySem
                                hargsSemWF
                            have hscrut₂ : scrutineeResult.ty.realize ext₂ =
                                Ty.apps (.con type) argsSem := by
                              rw [← Ty.realize_congr hscrutPost.tyAllocated hagree₂]
                              exact hty₁
                            have hunifies : scrutineeResult.ty.realize ext₂ =
                                (Ty.apps (.con first.ctor.type)
                                  (scrutineeResult.store.freshMany k decl.params).1).realize
                                  ext₂ := by
                              rw [Ty.realize_apps, hargs₂, htype]
                              exact hscrut₂
                            obtain ⟨storeUnified, hresult, hmodelsU⟩ :=
                              MStore.unify_complete (store :=
                                (scrutineeResult.store.freshMany k decl.params).2) hsafeA
                                hleftAllocA hrightAlloc hmodels₂ hunifies
                            rw [hu] at hresult
                            have hresultEq : storeUnified = storeU :=
                              (Except.ok.inj hresult).symm
                            subst storeUnified
                            let ext₃ : Valuation := Function.update ext₂ storeU.length ty
                            have hagreeU : Agree storeU.length ext₂ ext₃ := by
                              intro id hi
                              have hne : id ≠ storeU.length := by omega
                              simp only [ext₃, Function.update]
                              rw [dif_neg hne]
                            have hmodelsR : (storeU.fresh k).2.Models ext₃ := by
                              rw [MStore.fresh_eq, MStore.models_append_unsolved]
                              refine ⟨?_, ?_⟩
                              · exact MStore.Models.congr hsafeU hmodelsU hagreeU
                              · intro i hi
                                have hi0 : i = 0 := by omega
                                subst hi0
                                simpa [ext₃, Function.update] using htyWF
                            have hargs₃ : (scrutineeResult.store.freshMany k decl.params).1.map
                                (·.realize ext₃) =
                                (scrutineeResult.store.freshMany k decl.params).1.map
                                  (·.realize ext₂) := by
                              apply List.map_congr_left
                              intro arg harg
                              rw [MStore.freshMany_fst] at harg
                              simp only [List.mem_map, List.mem_range] at harg
                              obtain ⟨i, hi, rfl⟩ := harg
                              show ext₃ (scrutineeResult.store.length + i) =
                                ext₂ (scrutineeResult.store.length + i)
                              have hne : scrutineeResult.store.length + i ≠ storeU.length := by
                                rw [MStore.unify_length hu, MStore.freshMany_snd]
                                simp only [List.length_append, List.length_replicate]
                                omega
                              simp only [ext₃, Function.update]
                              rw [dif_neg hne]
                            have hagree₁₃ : Agree scrutineeResult.store.length ext₁ ext₃ := by
                              intro id hi
                              exact (hagree₂ id hi).trans (hagreeU id
                                (lt_of_lt_of_le hi (le_trans hgrowA hgrowU)))
                            have hagreeVal₃ : Agree store.length valuation ext₃ := by
                              intro id hi
                              exact (hagree₁ id hi).trans
                                (hagree₁₃ id (lt_of_lt_of_le hi hscrutPost.grows))
                            have hresult₃ : ((storeU.fresh k).1).realize ext₃ = ty := by
                              show ext₃ storeU.length = ty
                              simp only [ext₃, Function.update]
                              simp
                            have hallR : ∀ (i : Nat) pattern body bodyElab ctor,
                                ((first, second) :: restBranches)[i]? = some (pattern, body) →
                                branchesElab[i]? = some (pattern, bodyElab) →
                                decl.ctors[pattern.ctor.index]? = some ctor →
                                Typing sig (k + ctor.existentials)
                                  (ctor.fieldCtx
                                    ((scrutineeResult.store.freshMany k decl.params).1.map
                                      (·.realize ext₃))
                                    (rigidBlock k ctor.existentials) ++ ctx.realize ext₃)
                                  body bodyElab (((storeU.fresh k).1).realize ext₃) := by
                              intro i pattern body bodyElab ctor hbr' hbrElab hfields'
                              have h := hall i pattern body bodyElab ctor hbr' hbrElab hfields'
                              rw [ctx_realize_congr_of_agree pre hagreeVal₃, hargs₃.trans hargs₂,
                                hresult₃]
                              exact h
                            obtain ⟨extended, hmodelsExt, hagreeExt, hmapExt⟩ :=
                              hbrPost.principal ext₃ hmodelsR branchesElab hmap hallR
                            refine ⟨extended, hmodelsExt, ?_, ?_, ?_⟩
                            · intro id hi
                              exact (hagreeVal₃ id hi).trans
                                (hagreeExt id (lt_of_lt_of_le hi hgrowStoreR))
                            · have hagree₁ext : Agree scrutineeResult.store.length ext₁ extended := by
                                intro id hi
                                exact (hagree₁₃ id hi).trans
                                  (hagreeExt id (lt_of_lt_of_le hi (le_trans hgrowA hgrowAR)))
                              simp only [Expr.realize, Expr.mapAnn, Expr.mapAnnBranches_eq,
                                Expr.match.injEq]
                              refine ⟨?_, hmapExt⟩
                              show scrutineeResult.elaboration.realize extended = scrutineeElab
                              rw [← Expr.realize_agree (store := scrutineeResult.store)
                                hscrutPost.elabAllocated hagree₁ext]
                              exact helab₁
                            · rw [← Ty.realize_congr fresh_allocated hagreeExt, hresult₃]
            · have hnotA : (¬ (((first, second) :: restBranches).all (fun branch =>
                  decl.ctors[branch.1.ctor.index]?.all fun ctor =>
                    branch.1.binders == ctor.fields.length) = true)) = True := eq_true hallArity
              have h : inferAt sig k ctx
                  (.match scrutinee ((first, second) :: restBranches)) store =
                  .error ⟨[.matchBranch (((first, second) :: restBranches).findIdx
                    fun branch => !(decl.ctors[branch.1.ctor.index]?.all fun ctor =>
                      branch.1.binders == ctor.fields.length))],
                    .patternArity⟩ := by
                simp only [hbind, hhead, hdecl, hallCheck, hnotA, not_true, ite_true,
                  ite_false, Option.getDM, Bind.bind, Except.bind, Pure.pure, Except.pure]
              simp only [InferSpec, h]
              intro valuation models elaboration ty typing
              obtain ⟨type, declTy, args, scrutineeElab, branchesElab, hdeclTy,
                harity, hne, hpatterns, hbinders, hmap, hscrut, hall, _, helab⟩ :=
                TypingWith.match_inv typing
              have htype : first.ctor.type = type := (hpatterns first hmemHead).1
              rw [← htype] at hdeclTy
              rw [hdecl] at hdeclTy
              cases hdeclTy
              exact hallArity (branches_arity_of_facts hbinders)
          · have hnot : (¬ (((first, second) :: restBranches).all (fun branch =>
                branch.1.ctor.type == first.ctor.type &&
                  decide (branch.1.ctor.index < decl.ctors.length)) = true)) = True :=
              eq_true hallCheck
            have h : inferAt sig k ctx
                (.match scrutinee ((first, second) :: restBranches)) store =
                .error ⟨[.matchBranch (((first, second) :: restBranches).findIdx
                  fun branch => !(branch.1.ctor.type == first.ctor.type &&
                    decide (branch.1.ctor.index < decl.ctors.length)))],
                  .foreignPattern⟩ := by
              simp only [hbind, hhead, hdecl, hnot, ite_true, Option.getDM, Bind.bind,
                Except.bind, Pure.pure, Except.pure]
            simp only [InferSpec, h]
            intro valuation models elaboration ty typing
            obtain ⟨type, declTy, args, scrutineeElab, branchesElab, hdeclTy, harity,
              hne, hpatterns, _, hmap, hscrut, hall, _, helab⟩ := TypingWith.match_inv typing
            have htype : first.ctor.type = type := (hpatterns first hmemHead).1
            rw [← htype] at hdeclTy
            rw [hdecl] at hdeclTy
            cases hdeclTy
            exact hallCheck (branches_all_of_facts fun pattern hpat =>
              ⟨(hpatterns pattern hpat).1.trans htype.symm, (hpatterns pattern hpat).2⟩)

theorem inferAt_spec_var {sig : Signature} (pre : InferPre k ctx store) :
    InferSpec sig k ctx (.var index) store := by
  have hbind : inferAt sig k ctx (.var index) store =
      (ctx[index]?).getDM (throw (.here .unboundVar)) >>= (fun scheme =>
        (pure ⟨scheme.inst (store.freshMany k scheme.arity).1, .var index,
          (store.freshMany k scheme.arity).2,
          .node (scheme.inst (store.freshMany k scheme.arity).1) []⟩ :
            Except InferError Inferred)) := rfl
  cases hget : ctx[index]? with
  | none =>
      have h : inferAt sig k ctx (.var index) store = .error (.here .unboundVar) := by
        rw [hbind, hget]; rfl
      simp only [InferSpec, h]
      intro valuation models elaboration ty typing
      cases typing with
      | var htyping _ =>
          rw [Ctx.realize_getElem?, hget] at htyping
          simp at htyping
  | some scheme =>
      have h : inferAt sig k ctx (.var index) store =
          .ok ⟨scheme.inst (store.freshMany k scheme.arity).1, .var index,
            (store.freshMany k scheme.arity).2,
            .node (scheme.inst (store.freshMany k scheme.arity).1) []⟩ := by
        rw [hbind, hget]; rfl
      simp only [InferSpec, h]
      have hmem : scheme ∈ ctx := List.mem_of_getElem? hget
      obtain ⟨hargsWF, hlen, hargsAlloc, hargsLB⟩ :=
        freshMany_facts store k scheme.arity
      refine
        { safe := MStore.append_unsolved_safe pre.safe
          grows := by rw [MStore.freshMany_snd]; simp
          levels := ?_
          tyWF := Scheme.inst_wf (pre.ctxWF scheme hmem) (le_refl k) hlen hargsWF
          tyAllocated := ?_
          tyLevels := ?_
          elabAllocated := ?_
          anchored := ?_
          sound := ?_
          principal := ?_ }
      · intro id hi
        show (store.freshMany k scheme.arity).2.levelOf id ≤ store.levelOf id
        rw [MStore.freshMany_snd, MStore.append_unsolved_levelOf, if_pos hi]
      · have hctxAlloc : scheme.body.Allocated
            (store ++ List.replicate scheme.arity ⟨k, none⟩) :=
          Ty.allocated_mono (by simp) (pre.ctxAllocated scheme hmem)
        simpa [Scheme.inst] using
          (Ty.allocated_instantiate scheme.body
            (store.freshMany k scheme.arity).1
            (store ++ List.replicate scheme.arity ⟨k, none⟩)
            hctxAlloc hargsAlloc)
      · have hctxLevels : scheme.body.LevelBounded
            (store ++ List.replicate scheme.arity ⟨k, none⟩) k :=
          Ty.levelBounded_mono (pre.ctxAllocated scheme hmem) (pre.ctxLevels scheme hmem)
            (fun id hi => by
              rw [MStore.append_unsolved_levelOf, if_pos hi])
        simpa [Scheme.inst] using
          (Ty.levelBounded_instantiate scheme.body
            (store.freshMany k scheme.arity).1
            (store ++ List.replicate scheme.arity ⟨k, none⟩) k
            hctxLevels hargsLB)
      · intro ann hmem
        simp [Expr.anns] at hmem
      · intro start level hlt hstart hanch
        exact MStore.Anchored.append_unsolved (count := scheme.arity) (level' := k) hanch hlt
      · intro valuation models
        have hmodelsStore : store.Models valuation :=
          MStore.Models.of_append_unsolved models
        refine ⟨hmodelsStore, ?_⟩
        simp only [Expr.realize, Expr.mapAnn]
        have hctxget : (ctx.realize valuation)[index]? = some (scheme.realize valuation) := by
          rw [Ctx.realize_getElem?, hget]; rfl
        have hclosed : ∀ id ∈ scheme.body.vars, (valuation id).WF k :=
          fun id hid => ctx_image_wf (pre := pre) hmodelsStore hmem hid
        have hreal := Scheme.realize_inst (scheme := scheme)
          (args := (store.freshMany k scheme.arity).1) (valuation := valuation) hclosed
        refine TypingWith.var hctxget ?_
        rw [hreal]
        exact ⟨(store.freshMany k scheme.arity).1.map (·.realize valuation),
          freshMany_map_length valuation, freshMany_map_wf models, rfl⟩
      · intro valuation models elaboration target typing
        cases typing with
        | var htyping hinst =>
            have hrealget : (ctx.realize valuation)[index]? = some (scheme.realize valuation) := by
              rw [Ctx.realize_getElem?, hget]; rfl
            have hschemeEq := Option.some.inj (hrealget.symm.trans htyping)
            obtain ⟨args', hlen', hwf', hinstEq⟩ := hinst
            rw [← hschemeEq] at hlen' hinstEq
            obtain ⟨extended, hmodels', hagree', hmap⟩ :=
              MStore.freshMany_principal (store := store) (level := k)
                (count := scheme.arity) (valuation := valuation) pre.safe models hlen' hwf'
            have hmodelsStore : store.Models extended :=
              MStore.Models.of_append_unsolved hmodels'
            refine ⟨extended, hmodels', hagree', ?_, ?_⟩
            · simp only [Expr.realize, Expr.mapAnn]
            · have hclosed : ∀ id ∈ scheme.body.vars, (extended id).WF k :=
                fun id hid => ctx_image_wf (pre := pre) hmodelsStore hmem hid
              have hschemeReal : scheme.realize extended = scheme.realize valuation :=
                Scheme.realize_agree (pre.ctxAllocated scheme hmem)
                  (fun id hi => (hagree' id hi).symm)
              have hreal := Scheme.realize_inst (scheme := scheme)
                (args := (store.freshMany k scheme.arity).1) (valuation := extended) hclosed
              calc ((scheme.inst (store.freshMany k scheme.arity).1).realize extended)
                  = (scheme.realize extended).inst
                      ((store.freshMany k scheme.arity).1.map (·.realize extended)) := hreal
                _ = (scheme.realize valuation).inst args' := by rw [hschemeReal, hmap]
                _ = target := hinstEq

theorem inferAt_spec_lambda {sig : Signature} {body : Source}
    (bodySpec : ∀ k ctx store, InferPre k ctx store → InferSpec sig k ctx body store)
    (pre : InferPre k ctx store) :
    InferSpec sig k ctx (.lambda param body) store := by
  have hbind : inferAt sig k ctx (.lambda param body) store =
      (paramTy k store param).getDM (throw (.here .illScopedAnnotation)) >>= (fun pair =>
        (inferAt sig k (.mono pair.1 :: ctx) body pair.2).mapError (.under .lambdaBody) >>=
          (fun bodyResult =>
          (pure ⟨.arrow pair.1 bodyResult.ty, .lambda (some pair.1) bodyResult.elaboration,
            bodyResult.store, .node (.arrow pair.1 bodyResult.ty) [bodyResult.types]⟩ :
              Except InferError Inferred))) := rfl
  cases hp : paramTy k store param with
  | none =>
      have h : inferAt sig k ctx (.lambda param body) store =
          .error (.here .illScopedAnnotation) := by
        rw [hbind, hp]; rfl
      simp only [InferSpec, h]
      have hspec := paramTy_spec (k := k) (store := store) (param := param) pre.safe
      rw [hp] at hspec
      intro valuation models elaboration ty typing
      obtain ⟨sem, bodyElab, bodyTy, _, _, hsemwf, hsemmatches, _⟩ :=
        TypingWith.lambda_inv typing
      exact hspec sem hsemmatches hsemwf
  | some pair =>
      obtain ⟨pty, store'⟩ := pair
      have h : inferAt sig k ctx (.lambda param body) store =
          (inferAt sig k (.mono pty :: ctx) body store').mapError (.under .lambdaBody) >>=
            (fun bodyResult =>
            (pure ⟨.arrow pty bodyResult.ty, .lambda (some pty) bodyResult.elaboration,
              bodyResult.store, .node (.arrow pty bodyResult.ty) [bodyResult.types]⟩ :
                Except InferError Inferred)) := by
        rw [hbind, hp]; rfl
      have hspec := paramTy_spec (k := k) (store := store) (param := param) pre.safe
      rw [hp] at hspec
      obtain ⟨hstore', htywf, htyalloc, htyouter, hmatches, hprincipal⟩ := hspec
      have hsafe' : store'.Safe := by
        rw [hstore']; exact MStore.append_unsolved_safe pre.safe
      have hgrow' : store.length ≤ store'.length := by
        rw [hstore']; simp
      have hlev' : ∀ id < store.length, store'.levelOf id ≤ store.levelOf id := by
        intro id hi
        rw [hstore', MStore.append_unsolved_levelOf, if_pos hi]
      have htyalloc' : pty.Allocated
          (store ++ List.replicate (store'.length - store.length) ⟨k, none⟩) := by
        rw [← hstore']; exact htyalloc
      have htylev : pty.LevelBounded store' k := by
        rw [hstore']
        exact Ty.levelBounded_append htyalloc' htyouter
      have hpre' : InferPre k (.mono pty :: ctx) store' :=
        InferPre.cons_mono (pre.extend hsafe' hgrow' hlev') htywf htyalloc htylev
      cases hb : inferAt sig k (.mono pty :: ctx) body store' with
      | error bodyError =>
          have hnone : inferAt sig k ctx (.lambda param body) store =
              .error (.under .lambdaBody bodyError) := by
            rw [h, hb]
            simp only [mapError_error, Bind.bind, Except.bind]
          simp only [InferSpec, hnone]
          have hbodyNone := bodySpec k (.mono pty :: ctx) store' hpre'
          unfold InferSpec at hbodyNone
          rw [hb] at hbodyNone
          intro valuation models elaboration ty typing
          obtain ⟨sem, bodyElab, bodyTy, _, _, hsemwf, hsemmatches, hbody⟩ :=
            TypingWith.lambda_inv typing
          obtain ⟨ext', hmodels', hagree', hreal'⟩ :=
            hprincipal valuation sem models hsemmatches hsemwf
          have hctxeq := ctx_realize_cons_eq pre hagree' hreal'
          rw [← hctxeq] at hbody
          exact hbodyNone ext' hmodels' bodyElab bodyTy hbody
      | ok bodyResult =>
          have hsucc : inferAt sig k ctx (.lambda param body) store =
              .ok ⟨.arrow pty bodyResult.ty, .lambda (some pty) bodyResult.elaboration,
                bodyResult.store, .node (.arrow pty bodyResult.ty) [bodyResult.types]⟩ := by
            rw [h, hb]
            simp only [mapError_ok, Bind.bind, Except.bind, Pure.pure, Except.pure]
          simp only [InferSpec, hsucc]
          have hbodyPost := bodySpec k (.mono pty :: ctx) store' hpre'
          unfold InferSpec at hbodyPost
          rw [hb] at hbodyPost
          simp only at hbodyPost
          refine
            { safe := hbodyPost.safe
              grows := le_trans hgrow' hbodyPost.grows
              levels := ?_
              tyWF := Ty.wf_arrow htywf hbodyPost.tyWF
              tyAllocated := Ty.allocated_arrow (Ty.allocated_mono hbodyPost.grows htyalloc)
                hbodyPost.tyAllocated
              tyLevels := Ty.levelBounded_arrow
                (Ty.levelBounded_mono htyalloc htylev hbodyPost.levels) hbodyPost.tyLevels
              elabAllocated := ?_
              anchored := ?_
              sound := ?_
              principal := ?_ }
          · intro id hi
            exact le_trans (hbodyPost.levels id (lt_of_lt_of_le hi hgrow')) (hlev' id hi)
          · intro ann hann
            simp only [Expr.anns, List.mem_cons] at hann
            rcases hann with rfl | hann
            · exact Ty.allocated_mono hbodyPost.grows htyalloc
            · exact hbodyPost.elabAllocated ann hann
          · intro start level hlt hstart hanch
            have hstoreAnch : store'.Anchored start level := by
              rw [hstore']
              exact MStore.Anchored.append_unsolved
                (count := store'.length - store.length) (level' := k) hanch hlt
            exact hbodyPost.anchored start level hlt (le_trans hstart hgrow') hstoreAnch
          · intro valuation models
            obtain ⟨hmodels', hbodyElab⟩ := hbodyPost.sound valuation models
            refine ⟨?_, ?_⟩
            · rw [hstore'] at hmodels'
              exact MStore.Models.of_append_unsolved hmodels'
            · simp only [Expr.realize, Expr.mapAnn]
              exact TypingWith.lambda
                (Ty.realize_wf_of_models hmodels' htywf htyalloc htylev)
                (hmatches valuation) hbodyElab
          · intro valuation models elaboration target typing
            obtain ⟨sem, bodyElab, bodyTy, helab, htarget, hsemwf, hsemmatches, hbody⟩ :=
              TypingWith.lambda_inv typing
            obtain ⟨ext', hmodels', hagree', hreal'⟩ :=
              hprincipal valuation sem models hsemmatches hsemwf
            have hctxeq := ctx_realize_cons_eq pre hagree' hreal'
            rw [← hctxeq] at hbody
            obtain ⟨extended, hmodelsExt, hagreeExt, hbodyElabReal, hbodyTyReal⟩ :=
              hbodyPost.principal ext' hmodels' bodyElab bodyTy hbody
            have hpty : pty.realize extended = sem := by
              rw [Ty.realize_agree htyalloc (fun id hi => (hagreeExt id hi).symm), hreal']
            refine ⟨extended, hmodelsExt, ?_, ?_, ?_⟩
            · intro id hi
              exact (hagree' id hi).trans (hagreeExt id (lt_of_lt_of_le hi hgrow'))
            · change (Expr.lambda (some pty) bodyResult.elaboration).realize extended = elaboration
              rw [helab]
              show Expr.lambda (some (pty.realize extended))
                  (Expr.mapAnn (fun x => Ty.realize x extended) bodyResult.elaboration) =
                Expr.lambda (some sem) bodyElab
              have hbodyMap : Expr.mapAnn (fun x => Ty.realize x extended)
                  bodyResult.elaboration = bodyElab := hbodyElabReal
              rw [hpty, hbodyMap]
            · change (Ty.arrow pty bodyResult.ty).realize extended = target
              rw [htarget]
              show (Ty.arrow (pty.realize extended) (bodyResult.ty.realize extended)) =
                Ty.arrow sem bodyTy
              rw [hpty, hbodyTyReal]

/-- A model of the function's store extends through the argument and the fresh
metavariable to one satisfying the unification constraint. -/
private theorem app_extend {sig : Signature} {k : Nat} {ctx : Ctx Nat} {store : MStore}
    {function argument : Source} {functionResult argumentResult : Inferred}
    (pre : InferPre k ctx store)
    (hfunPost : InferPost sig k ctx function store functionResult)
    (hargPost : InferPost sig k ctx argument functionResult.store argumentResult)
    {valuation : Valuation} (models : store.Models valuation)
    {fElab aElab : Elab} {argTy resTy : SemTy}
    (hfun : Typing sig k (ctx.realize valuation) function fElab (.arrow argTy resTy))
    (harg : Typing sig k (ctx.realize valuation) argument aElab argTy)
    (resWF : resTy.WF k) :
    ∃ ext1 : Valuation, (argumentResult.store.fresh k).2.Models ext1 ∧
      Agree store.length valuation ext1 ∧
      functionResult.elaboration.realize ext1 = fElab ∧
      argumentResult.elaboration.realize ext1 = aElab ∧
      ((argumentResult.store.fresh k).1).realize ext1 = resTy ∧
      functionResult.ty.realize ext1 =
        (Ty.arrow argumentResult.ty (argumentResult.store.fresh k).1).realize ext1 := by
  have hgrowFresh : argumentResult.store.length ≤
      (argumentResult.store.fresh k).2.length := by
    rw [MStore.fresh_eq]; simp
  have hsafeFresh : (argumentResult.store.fresh k).2.Safe := by
    rw [MStore.fresh_eq]
    exact MStore.append_unsolved_safe hargPost.safe
  have hleftAllocFresh : functionResult.ty.Allocated
      (argumentResult.store.fresh k).2 :=
    Ty.allocated_mono (le_trans hargPost.grows hgrowFresh) hfunPost.tyAllocated
  have hrightAllocFresh :
      (Ty.arrow argumentResult.ty (argumentResult.store.fresh k).1).Allocated
        (argumentResult.store.fresh k).2 :=
    Ty.allocated_arrow (Ty.allocated_mono hgrowFresh hargPost.tyAllocated) fresh_allocated
  obtain ⟨extF, hmodelsF, hagreeF, hfunElabReal, hfunTyReal⟩ :=
    hfunPost.principal valuation models fElab (.arrow argTy resTy) hfun
  have hctxF := ctx_realize_congr_of_agree pre hagreeF
  rw [← hctxF] at harg
  obtain ⟨extA, hmodelsA, hagreeFA, hargElabReal, hargTyReal⟩ :=
    hargPost.principal extF hmodelsF aElab argTy harg
  let ext1 : Valuation := Function.update extA argumentResult.store.length resTy
  have hagreeA1 : Agree argumentResult.store.length extA ext1 := by
    intro id hi
    have hne : id ≠ argumentResult.store.length := by omega
    simp [ext1, hne]
  have hmodelsFresh : (argumentResult.store.fresh k).2.Models ext1 := by
    rw [MStore.fresh_eq, MStore.models_append_unsolved]
    refine ⟨?_, ?_⟩
    · exact MStore.Models.congr hargPost.safe hmodelsA hagreeA1
    · intro i hi
      have hi0 : i = 0 := by omega
      subst hi0
      simpa [ext1, Function.update] using resWF
  have hfunAllocA : functionResult.ty.Allocated argumentResult.store :=
    Ty.allocated_mono hargPost.grows hfunPost.tyAllocated
  have hfunAtA : functionResult.ty.realize extA = .arrow argTy resTy := by
    rw [← Ty.realize_agree hfunPost.tyAllocated hagreeFA, hfunTyReal]
  have hfunAt1 : functionResult.ty.realize ext1 = .arrow argTy resTy := by
    rw [← Ty.realize_agree hfunAllocA hagreeA1]
    exact hfunAtA
  have hargAt1 : argumentResult.ty.realize ext1 = argTy := by
    rw [← Ty.realize_agree hargPost.tyAllocated hagreeA1, hargTyReal]
  have hfreshAt1 : ((argumentResult.store.fresh k).1).realize ext1 = resTy := by
    show ext1 argumentResult.store.length = resTy
    simp [ext1]
  have hunifies : functionResult.ty.realize ext1 =
      (Ty.arrow argumentResult.ty (argumentResult.store.fresh k).1).realize ext1 := by
    rw [hfunAt1]
    show (Ty.arrow argTy resTy) =
      (Ty.arrow (argumentResult.ty.realize ext1)
        (((argumentResult.store.fresh k).1).realize ext1))
    rw [hargAt1, hfreshAt1]
  have hfunElab1 : functionResult.elaboration.realize ext1 = fElab := by
    rw [← Expr.realize_agree (store := argumentResult.store)
      (fun ann hann => Ty.allocated_mono hargPost.grows (hfunPost.elabAllocated ann hann))
      hagreeA1]
    rw [← Expr.realize_agree (store := functionResult.store)
      hfunPost.elabAllocated hagreeFA]
    exact hfunElabReal
  have hargElab1 : argumentResult.elaboration.realize ext1 = aElab := by
    rw [← Expr.realize_agree (store := argumentResult.store) hargPost.elabAllocated hagreeA1]
    exact hargElabReal
  have hagree1 : Agree store.length valuation ext1 := by
    intro id hi
    exact (hagreeF id hi).trans
      ((hagreeFA id (lt_of_lt_of_le hi hfunPost.grows)).trans
        (hagreeA1 id (lt_of_lt_of_le hi (le_trans hfunPost.grows hargPost.grows))))
  exact ⟨ext1, hmodelsFresh, hagree1, hfunElab1, hargElab1, hfreshAt1, hunifies⟩

theorem inferAt_spec_app {sig : Signature} {function argument : Source}
    (functionSpec : ∀ k ctx store, InferPre k ctx store → InferSpec sig k ctx function store)
    (argumentSpec : ∀ k ctx store, InferPre k ctx store → InferSpec sig k ctx argument store)
    (pre : InferPre k ctx store) :
    InferSpec sig k ctx (.app function argument) store := by
  have hbind : inferAt sig k ctx (.app function argument) store =
      (inferAt sig k ctx function store).mapError (.under .appFunction) >>= (fun functionResult =>
        (inferAt sig k ctx argument functionResult.store).mapError (.under .appArgument) >>=
          (fun argumentResult =>
          (fun (resultTy : InfTy) (store : MStore) =>
            store.unifyAt [] functionResult.ty (.arrow argumentResult.ty resultTy) >>=
              (fun store =>
                (pure ⟨resultTy,
                  .app functionResult.elaboration argumentResult.elaboration,
                  store, .node resultTy [functionResult.types, argumentResult.types]⟩ :
                    Except InferError Inferred)))
            (argumentResult.store.fresh k).1 (argumentResult.store.fresh k).2)) := rfl
  cases hf : inferAt sig k ctx function store with
  | error functionError =>
      have h : inferAt sig k ctx (.app function argument) store =
          .error (.under .appFunction functionError) := by
        rw [hbind, hf]; rfl
      simp only [InferSpec, h]
      have hfunNone := functionSpec k ctx store pre
      unfold InferSpec at hfunNone
      rw [hf] at hfunNone
      intro valuation models elaboration target typing
      obtain ⟨fElab, aElab, argTy, resTy, _, _, hfun, _⟩ := TypingWith.app_inv typing
      exact hfunNone valuation models fElab (.arrow argTy resTy) hfun
  | ok functionResult =>
      have hfunPost := functionSpec k ctx store pre
      unfold InferSpec at hfunPost
      rw [hf] at hfunPost
      simp only at hfunPost
      have hpreArg : InferPre k ctx functionResult.store :=
        pre.extend hfunPost.safe hfunPost.grows hfunPost.levels
      cases ha : inferAt sig k ctx argument functionResult.store with
      | error argumentError =>
          have h : inferAt sig k ctx (.app function argument) store =
              .error (.under .appArgument argumentError) := by
            simp only [hbind, hf, ha, Bind.bind, Except.bind, mapError_ok, mapError_error]
          simp only [InferSpec, h]
          have hargNone := argumentSpec k ctx functionResult.store hpreArg
          unfold InferSpec at hargNone
          rw [ha] at hargNone
          intro valuation models elaboration target typing
          obtain ⟨fElab, aElab, argTy, resTy, _, _, hfun, harg⟩ := TypingWith.app_inv typing
          have hfunTyping := Elaborates.typing hfun
          obtain ⟨extF, hmodelsF, hagreeF, _, _⟩ :=
            hfunPost.principal valuation models fElab (.arrow argTy resTy) hfunTyping
          have hctxF := ctx_realize_congr_of_agree pre hagreeF
          rw [← hctxF] at harg
          exact hargNone extF hmodelsF aElab argTy harg
      | ok argumentResult =>
          have hargPost := argumentSpec k ctx functionResult.store hpreArg
          unfold InferSpec at hargPost
          rw [ha] at hargPost
          simp only at hargPost
          have hgrowFresh : argumentResult.store.length ≤
              (argumentResult.store.fresh k).2.length := by
            rw [MStore.fresh_eq]; simp
          have hsafeFresh : (argumentResult.store.fresh k).2.Safe := by
            rw [MStore.fresh_eq]
            exact MStore.append_unsolved_safe hargPost.safe
          have hleftAllocFresh : functionResult.ty.Allocated
              (argumentResult.store.fresh k).2 :=
            Ty.allocated_mono (le_trans hargPost.grows hgrowFresh) hfunPost.tyAllocated
          have hrightAllocFresh :
              (Ty.arrow argumentResult.ty (argumentResult.store.fresh k).1).Allocated
                (argumentResult.store.fresh k).2 := by
            apply Ty.allocated_arrow
            · exact Ty.allocated_mono hgrowFresh hargPost.tyAllocated
            · exact fresh_allocated
          cases hu : (argumentResult.store.fresh k).2.unify functionResult.ty
              (.arrow argumentResult.ty (argumentResult.store.fresh k).1) with
          | error cause =>
              have h : inferAt sig k ctx (.app function argument) store =
                  .error ⟨[], .mismatch
                    ((argumentResult.store.fresh k).2.apply
                      (.arrow argumentResult.ty (argumentResult.store.fresh k).1))
                    ((argumentResult.store.fresh k).2.apply functionResult.ty) cause⟩ := by
                simp only [hbind, hf, ha, MStore.unifyAt, Bind.bind, Except.bind,
                  mapError_ok, mapError_error, hu]
              simp only [InferSpec, h]
              intro valuation models elaboration target typing
              obtain ⟨fElab, aElab, argTy, resTy, _, htarget, hfun, harg⟩ :=
                TypingWith.app_inv typing
              have hctxWF : (ctx.realize valuation).WF k :=
                Ctx.realize_wf models pre.ctxWF pre.ctxAllocated pre.ctxLevels
              have hresWF : resTy.WF k := by
                have := TypingWith.regular hctxWF typing
                rwa [htarget] at this
              obtain ⟨ext1, hmodelsFresh, _, _, _, _, hunifies⟩ :=
                app_extend pre hfunPost hargPost models (Elaborates.typing hfun)
                  (Elaborates.typing harg) hresWF
              obtain ⟨result, hresult, _⟩ :=
                MStore.unify_complete hsafeFresh hleftAllocFresh hrightAllocFresh
                  hmodelsFresh hunifies
              rw [hu] at hresult
              cases hresult
          | ok store2 =>
              have hsucc : inferAt sig k ctx (.app function argument) store =
                  .ok ⟨(argumentResult.store.fresh k).1,
                    .app functionResult.elaboration argumentResult.elaboration, store2,
                    .node (argumentResult.store.fresh k).1
                      [functionResult.types, argumentResult.types]⟩ := by
                simp only [hbind, hf, ha, MStore.unifyAt, Bind.bind, Except.bind,
                  Pure.pure, Except.pure, mapError_ok, hu]
              simp only [InferSpec, hsucc]
              have hgrowArg1 : argumentResult.store.length ≤ store2.length :=
                le_trans hgrowFresh (le_of_eq (MStore.unify_length hu).symm)
              have hgrowFun2 : functionResult.store.length ≤ store2.length :=
                le_trans hargPost.grows hgrowArg1
              have hgrowStore2 : store.length ≤ store2.length :=
                le_trans hfunPost.grows hgrowFun2
              refine
                { safe := MStore.unify_safe hsafeFresh hleftAllocFresh hrightAllocFresh hu
                  grows := hgrowStore2
                  levels := ?_
                  tyWF := trivial
                  tyAllocated := ?_
                  tyLevels := ?_
                  elabAllocated := ?_
                  anchored := ?_
                  sound := ?_
                  principal := ?_ }
              · intro id hi
                have hidArg : id < argumentResult.store.length :=
                  lt_of_lt_of_le hi (le_trans hfunPost.grows hargPost.grows)
                have hstore1 : (argumentResult.store.fresh k).2.levelOf id =
                    argumentResult.store.levelOf id := by
                  rw [MStore.fresh_eq, MStore.append_unsolved_levelOf, if_pos hidArg]
                refine le_trans (MStore.unify_levelOf_le hu id) ?_
                rw [hstore1]
                exact le_trans (hargPost.levels id (lt_of_lt_of_le hi hfunPost.grows))
                  (hfunPost.levels id hi)
              · exact Ty.allocated_mono (le_of_eq (MStore.unify_length hu).symm) fresh_allocated
              · exact Ty.levelBounded_mono fresh_allocated fresh_levelBounded
                  (fun id _ => MStore.unify_levelOf_le hu id)
              · intro ann hann
                simp only [Expr.anns, List.mem_append] at hann
                rcases hann with hann | hann
                · exact Ty.allocated_mono hgrowFun2 (hfunPost.elabAllocated ann hann)
                · exact Ty.allocated_mono hgrowArg1 (hargPost.elabAllocated ann hann)
              · intro start level hlt hstart hanch
                have hfunAnch := hfunPost.anchored start level hlt hstart hanch
                have h1 := hargPost.anchored start level hlt
                  (le_trans hstart hfunPost.grows) hfunAnch
                have h2 : (argumentResult.store.fresh k).2.Anchored start level := by
                  rw [MStore.fresh_eq]
                  exact MStore.Anchored.append_unsolved (count := 1) (level' := k) h1 hlt
                exact MStore.unify_anchored h2 hu
              · intro valuation models2
                obtain ⟨hmodelsFresh, hunifyEq⟩ := MStore.unify_sound hu models2
                have hmodelsArg : argumentResult.store.Models valuation := by
                  rw [MStore.fresh_eq] at hmodelsFresh
                  exact MStore.Models.of_append_unsolved hmodelsFresh
                obtain ⟨hmodelsFunction, hargElab⟩ := hargPost.sound valuation hmodelsArg
                obtain ⟨hmodelsStore, hfunElab⟩ := hfunPost.sound valuation hmodelsFunction
                refine ⟨hmodelsStore, ?_⟩
                simp only [Expr.realize, Expr.mapAnn]
                rw [hunifyEq] at hfunElab
                exact TypingWith.app hfunElab hargElab
              · intro valuation models elaboration target typing
                obtain ⟨fElab, aElab, argTy, resTy, helab, htarget, hfun, harg⟩ :=
                  TypingWith.app_inv typing
                have hctxWF : (ctx.realize valuation).WF k :=
                  Ctx.realize_wf models pre.ctxWF pre.ctxAllocated pre.ctxLevels
                have hresWF : resTy.WF k := by
                  have := TypingWith.regular hctxWF typing
                  rwa [htarget] at this
                obtain ⟨ext1, hmodelsFresh, hagree1, hfunElab1, hargElab1, hfreshAt1, hunifies⟩ :=
                  app_extend pre hfunPost hargPost models hfun harg hresWF
                obtain ⟨result, hresult, hmodelsResult⟩ :=
                  MStore.unify_complete hsafeFresh hleftAllocFresh hrightAllocFresh
                    hmodelsFresh hunifies
                have hresultEq : result = store2 := by
                  rw [hu] at hresult
                  exact (Except.ok.inj hresult).symm
                subst hresultEq
                refine ⟨ext1, hmodelsResult, hagree1, ?_, ?_⟩
                · change (Expr.app functionResult.elaboration
                      argumentResult.elaboration).realize ext1 = elaboration
                  rw [helab]
                  change Expr.app (functionResult.elaboration.realize ext1)
                      (argumentResult.elaboration.realize ext1) = Expr.app fElab aElab
                  rw [hfunElab1, hargElab1]
                · change ((argumentResult.store.fresh k).1).realize ext1 = target
                  rw [htarget]
                  exact hfreshAt1

theorem inferAt_spec_letMono {sig : Signature} {rhs body : Source}
    (rhsSpec : ∀ k ctx store, InferPre k ctx store → InferSpec sig k ctx rhs store)
    (bodySpec : ∀ k ctx store, InferPre k ctx store → InferSpec sig k ctx body store)
    (pre : InferPre k ctx store) :
    InferSpec sig k ctx (.letIn none rhs body) store := by
  have hbind : inferAt sig k ctx (.letIn none rhs body) store =
      (inferAt sig k ctx rhs store).mapError (.under .letRhs) >>= (fun rhsResult =>
        (inferAt sig k (.mono rhsResult.ty :: ctx) body rhsResult.store).mapError
          (.under .letBody) >>= (fun bodyResult =>
          (pure ⟨bodyResult.ty,
            .letIn none rhsResult.elaboration bodyResult.elaboration,
            bodyResult.store, .node bodyResult.ty [rhsResult.types, bodyResult.types]⟩ :
              Except InferError Inferred))) := rfl
  cases hr : inferAt sig k ctx rhs store with
  | error rhsError =>
      have h : inferAt sig k ctx (.letIn none rhs body) store =
          .error (.under .letRhs rhsError) := by
        rw [hbind, hr]; rfl
      simp only [InferSpec, h]
      have hrhsNone := rhsSpec k ctx store pre
      unfold InferSpec at hrhsNone
      rw [hr] at hrhsNone
      intro valuation models elaboration ty typing
      obtain ⟨rhsElab, rhsTy, bodyElab, bodyTy, _, _, hrhs, _⟩ :=
        TypingWith.letMono_inv typing
      exact hrhsNone valuation models rhsElab rhsTy hrhs
  | ok rhsResult =>
      have h : inferAt sig k ctx (.letIn none rhs body) store =
          (inferAt sig k (.mono rhsResult.ty :: ctx) body rhsResult.store).mapError
            (.under .letBody) >>= (fun bodyResult =>
            (pure ⟨bodyResult.ty,
              .letIn none rhsResult.elaboration bodyResult.elaboration,
              bodyResult.store, .node bodyResult.ty [rhsResult.types, bodyResult.types]⟩ :
                Except InferError Inferred)) := by
        rw [hbind, hr]; rfl
      have hrhsPost := rhsSpec k ctx store pre
      unfold InferSpec at hrhsPost
      rw [hr] at hrhsPost
      simp only at hrhsPost
      have hpre' : InferPre k (.mono rhsResult.ty :: ctx) rhsResult.store :=
        InferPre.cons_mono (pre.extend hrhsPost.safe hrhsPost.grows hrhsPost.levels)
          hrhsPost.tyWF hrhsPost.tyAllocated hrhsPost.tyLevels
      cases hb : inferAt sig k (.mono rhsResult.ty :: ctx) body rhsResult.store with
      | error bodyError =>
          have hnone : inferAt sig k ctx (.letIn none rhs body) store =
              .error (.under .letBody bodyError) := by
            rw [h, hb]; rfl
          simp only [InferSpec, hnone]
          have hbodyNone := bodySpec k (.mono rhsResult.ty :: ctx) rhsResult.store hpre'
          unfold InferSpec at hbodyNone
          rw [hb] at hbodyNone
          intro valuation models elaboration ty typing
          obtain ⟨rhsElab, rhsTy, bodyElab, bodyTy, _, _, hrhs, hbody⟩ :=
            TypingWith.letMono_inv typing
          have hrhsTyping := Elaborates.typing hrhs
          obtain ⟨ext, hmodelsExt, hagreeExt, _, hrhsTyReal⟩ :=
            hrhsPost.principal valuation models rhsElab rhsTy hrhsTyping
          have hctxeq := ctx_realize_cons_eq pre hagreeExt hrhsTyReal
          rw [← hctxeq] at hbody
          exact hbodyNone ext hmodelsExt bodyElab bodyTy hbody
      | ok bodyResult =>
          have hsucc : inferAt sig k ctx (.letIn none rhs body) store =
              .ok ⟨bodyResult.ty,
                .letIn none rhsResult.elaboration bodyResult.elaboration,
                bodyResult.store, .node bodyResult.ty [rhsResult.types, bodyResult.types]⟩ := by
            rw [h, hb]; rfl
          simp only [InferSpec, hsucc]
          have hbodyPost := bodySpec k (.mono rhsResult.ty :: ctx) rhsResult.store hpre'
          unfold InferSpec at hbodyPost
          rw [hb] at hbodyPost
          simp only at hbodyPost
          refine
            { safe := hbodyPost.safe
              grows := le_trans hrhsPost.grows hbodyPost.grows
              levels := ?_
              tyWF := hbodyPost.tyWF
              tyAllocated := hbodyPost.tyAllocated
              tyLevels := hbodyPost.tyLevels
              elabAllocated := ?_
              anchored := ?_
              sound := ?_
              principal := ?_ }
          · intro id hi
            exact le_trans (hbodyPost.levels id (lt_of_lt_of_le hi hrhsPost.grows))
              (hrhsPost.levels id hi)
          · intro ann hann
            simp only [Expr.anns, List.mem_append] at hann
            rcases hann with hann | hann
            · exact Ty.allocated_mono hbodyPost.grows (hrhsPost.elabAllocated ann hann)
            · exact hbodyPost.elabAllocated ann hann
          · intro start level hlt hstart hanch
            exact hbodyPost.anchored start level hlt
              (le_trans hstart hrhsPost.grows)
              (hrhsPost.anchored start level hlt hstart hanch)
          · intro valuation models
            obtain ⟨hmodelsRhs, hbodyElab⟩ := hbodyPost.sound valuation models
            obtain ⟨hmodelsStore, hrhsElab⟩ := hrhsPost.sound valuation hmodelsRhs
            refine ⟨hmodelsStore, ?_⟩
            simp only [Expr.realize, Expr.mapAnn]
            exact TypingWith.letMono hrhsElab hbodyElab
          · intro valuation models elaboration target typing
            obtain ⟨rhsElab, rhsTy, bodyElab, bodyTy, helab, htarget, hrhs, hbody⟩ :=
              TypingWith.letMono_inv typing
            obtain ⟨ext, hmodelsExt, hagreeExt, hrhsElabReal, hrhsTyReal⟩ :=
              hrhsPost.principal valuation models rhsElab rhsTy hrhs
            have hctxeq := ctx_realize_cons_eq pre hagreeExt hrhsTyReal
            rw [← hctxeq] at hbody
            obtain ⟨extended, hmodelsExt', hagreeExt', hbodyElabReal, hbodyTyReal⟩ :=
              hbodyPost.principal ext hmodelsExt bodyElab bodyTy hbody
            refine ⟨extended, hmodelsExt', ?_, ?_, ?_⟩
            · intro id hi
              exact (hagreeExt id hi).trans
                (hagreeExt' id (lt_of_lt_of_le hi hrhsPost.grows))
            · change (Expr.letIn none rhsResult.elaboration
                  bodyResult.elaboration).realize extended = elaboration
              rw [helab]
              show Expr.letIn none
                  (Expr.mapAnn (fun x => Ty.realize x extended) rhsResult.elaboration)
                  (Expr.mapAnn (fun x => Ty.realize x extended) bodyResult.elaboration) =
                Expr.letIn none rhsElab bodyElab
              have hrhsMap : Expr.mapAnn (fun x => Ty.realize x extended)
                  rhsResult.elaboration = rhsElab := by
                change rhsResult.elaboration.realize extended = rhsElab
                rw [← Expr.realize_agree (store := rhsResult.store)
                  hrhsPost.elabAllocated hagreeExt']
                exact hrhsElabReal
              rw [hrhsMap, show Expr.mapAnn (fun x => Ty.realize x extended)
                bodyResult.elaboration = bodyElab from hbodyElabReal]
            · rw [htarget]
              exact hbodyTyReal

/-- The `fix` case of inference: the binder type comes from `paramTy`, exactly
as a lambda's parameter, and the body is then unified with it. -/
theorem inferAt_spec_fix {sig : Signature} {self : Option Template} {body : Source}
    (bodySpec : ∀ k ctx store, InferPre k ctx store → InferSpec sig k ctx body store)
    (pre : InferPre k ctx store) :
    InferSpec sig k ctx (.fix self body) store := by
  have hbind : inferAt sig k ctx (.fix self body) store =
      (paramTy k store self).getDM (throw (.here .illScopedAnnotation)) >>= (fun pair =>
        (inferAt sig k (.mono pair.1 :: ctx) body pair.2).mapError (.under .fixBody) >>=
          (fun bodyResult =>
          bodyResult.store.unifyAt [] bodyResult.ty pair.1 >>= (fun store =>
            (pure ⟨pair.1, .fix (some pair.1) bodyResult.elaboration, store,
              .node pair.1 [bodyResult.types]⟩ : Except InferError Inferred)))) := rfl
  cases hp : paramTy k store self with
  | none =>
      have h : inferAt sig k ctx (.fix self body) store =
          .error (.here .illScopedAnnotation) := by
        rw [hbind, hp]; rfl
      simp only [InferSpec, h]
      have hspec := paramTy_spec (k := k) (store := store) (param := self) pre.safe
      rw [hp] at hspec
      intro valuation models elaboration ty typing
      obtain ⟨sem, bodyElab, _, _, hsemwf, hsm, _⟩ := TypingWith.fix_inv typing
      exact hspec sem hsm hsemwf
  | some pair =>
      obtain ⟨selfTy, store'⟩ := pair
      have h : inferAt sig k ctx (.fix self body) store =
          (inferAt sig k (.mono selfTy :: ctx) body store').mapError (.under .fixBody) >>=
            (fun bodyResult =>
            bodyResult.store.unifyAt [] bodyResult.ty selfTy >>= (fun store =>
              (pure ⟨selfTy, .fix (some selfTy) bodyResult.elaboration, store,
                .node selfTy [bodyResult.types]⟩ : Except InferError Inferred))) := by
        rw [hbind, hp]; rfl
      have hspec := paramTy_spec (k := k) (store := store) (param := self) pre.safe
      rw [hp] at hspec
      obtain ⟨hstore', htywf, htyalloc, htyouter, hmatches, hprincipal⟩ := hspec
      have hsafe' : store'.Safe := by
        rw [hstore']; exact MStore.append_unsolved_safe pre.safe
      have hgrow' : store.length ≤ store'.length := by
        rw [hstore']; simp
      have hlev' : ∀ id < store.length, store'.levelOf id ≤ store.levelOf id := by
        intro id hi
        rw [hstore', MStore.append_unsolved_levelOf, if_pos hi]
      have htyalloc' : selfTy.Allocated
          (store ++ List.replicate (store'.length - store.length) ⟨k, none⟩) := by
        rw [← hstore']; exact htyalloc
      have htylev : selfTy.LevelBounded store' k := by
        rw [hstore']
        exact Ty.levelBounded_append htyalloc' htyouter
      have hpre' : InferPre k (.mono selfTy :: ctx) store' :=
        InferPre.cons_mono (pre.extend hsafe' hgrow' hlev') htywf htyalloc htylev
      cases hb : inferAt sig k (.mono selfTy :: ctx) body store' with
      | error bodyError =>
          have hnone : inferAt sig k ctx (.fix self body) store =
              .error (.under .fixBody bodyError) := by
            rw [h, hb]; rfl
          simp only [InferSpec, hnone]
          have hbodyNone := bodySpec k (.mono selfTy :: ctx) store' hpre'
          unfold InferSpec at hbodyNone
          rw [hb] at hbodyNone
          intro valuation models elaboration ty typing
          obtain ⟨sem, bodyElab, _, _, hsemwf, hsm, hbody⟩ := TypingWith.fix_inv typing
          obtain ⟨ext', hmodels', hagree', hreal'⟩ :=
            hprincipal valuation sem models hsm hsemwf
          have hctxeq := ctx_realize_cons_eq pre hagree' hreal'
          rw [← hctxeq] at hbody
          exact hbodyNone ext' hmodels' bodyElab sem hbody
      | ok bodyResult =>
          have hsucc : inferAt sig k ctx (.fix self body) store =
              bodyResult.store.unifyAt [] bodyResult.ty selfTy >>= (fun store =>
                (pure ⟨selfTy, .fix (some selfTy) bodyResult.elaboration, store,
                  .node selfTy [bodyResult.types]⟩ : Except InferError Inferred)) := by
            rw [h, hb]; rfl
          have hbodyPost := bodySpec k (.mono selfTy :: ctx) store' hpre'
          unfold InferSpec at hbodyPost
          rw [hb] at hbodyPost
          simp only at hbodyPost
          cases hu : bodyResult.store.unify bodyResult.ty selfTy with
          | error cause =>
              have hnone : inferAt sig k ctx (.fix self body) store =
                  .error ⟨[], .mismatch (bodyResult.store.apply selfTy)
                    (bodyResult.store.apply bodyResult.ty) cause⟩ := by
                simp only [hsucc, MStore.unifyAt, Bind.bind, Except.bind,
                  mapError_error, hu]
              simp only [InferSpec, hnone]
              intro valuation models elaboration ty typing
              obtain ⟨sem, bodyElab, _, _, hsemwf, hsm, hbody⟩ := TypingWith.fix_inv typing
              have hbodyTyping := Elaborates.typing hbody
              obtain ⟨ext, hmodelsExt, hagreeExt, hreal⟩ :=
                hprincipal valuation sem models hsm hsemwf
              have hctxeq := ctx_realize_cons_eq pre hagreeExt hreal
              rw [← hctxeq] at hbody
              rw [← hctxeq] at hbodyTyping
              obtain ⟨extended, hmodelsExt', hagreeExt', _, hbodyTyReal⟩ :=
                hbodyPost.principal ext hmodelsExt bodyElab sem hbodyTyping
              have hself : selfTy.realize extended = sem := by
                rw [Ty.realize_agree htyalloc
                  (fun id hi => (hagreeExt' id hi).symm), hreal]
              have hunifies : bodyResult.ty.realize extended = selfTy.realize extended := by
                rw [hbodyTyReal, hself]
              obtain ⟨result, hresult, _⟩ :=
                MStore.unify_complete (store := bodyResult.store)
                  (left := bodyResult.ty) (right := selfTy)
                  hbodyPost.safe hbodyPost.tyAllocated
                  (Ty.allocated_mono hbodyPost.grows htyalloc) hmodelsExt' hunifies
              rw [hu] at hresult
              cases hresult
          | ok store2 =>
              have hsucc' : inferAt sig k ctx (.fix self body) store =
                  .ok ⟨selfTy, .fix (some selfTy) bodyResult.elaboration, store2,
                    .node selfTy [bodyResult.types]⟩ := by
                simp only [hsucc, MStore.unifyAt, Bind.bind, Except.bind, Pure.pure,
                  Except.pure, mapError_ok, hu]
              simp only [InferSpec, hsucc']
              have hgrowBody2 : bodyResult.store.length ≤ store2.length :=
                le_of_eq (MStore.unify_length hu).symm
              have hgrow12 : store'.length ≤ store2.length :=
                le_trans hbodyPost.grows hgrowBody2
              have hselfLevBody : selfTy.LevelBounded bodyResult.store k :=
                Ty.levelBounded_mono htyalloc htylev hbodyPost.levels
              refine
                { safe := MStore.unify_safe hbodyPost.safe hbodyPost.tyAllocated
                    (Ty.allocated_mono hbodyPost.grows htyalloc) hu
                  grows := by
                    show store.length ≤ store2.length
                    exact le_trans (le_trans hgrow' hbodyPost.grows) hgrowBody2
                  levels := ?_
                  tyWF := htywf
                  tyAllocated := Ty.allocated_mono hgrow12 htyalloc
                  tyLevels := Ty.levelBounded_mono (Ty.allocated_mono hbodyPost.grows htyalloc)
                    hselfLevBody (fun id _ => MStore.unify_levelOf_le hu id)
                  elabAllocated := ?_
                  anchored := ?_
                  sound := ?_
                  principal := ?_ }
              · intro id hi
                exact le_trans (MStore.unify_levelOf_le hu id)
                  (le_trans (hbodyPost.levels id (lt_of_lt_of_le hi hgrow')) (hlev' id hi))
              · intro ann hann
                simp only [Expr.anns, List.mem_cons] at hann
                rcases hann with rfl | hann
                · exact Ty.allocated_mono hgrow12 htyalloc
                · exact Ty.allocated_mono hgrowBody2 (hbodyPost.elabAllocated ann hann)
              · intro start level hlt hstart hanch
                have hstoreAnch : store'.Anchored start level := by
                  rw [hstore']
                  exact MStore.Anchored.append_unsolved
                    (count := store'.length - store.length) (level' := k) hanch hlt
                exact MStore.unify_anchored
                  (hbodyPost.anchored start level hlt (le_trans hstart hgrow') hstoreAnch) hu
              · intro valuation models
                obtain ⟨hmodelsBody, hunifyEq⟩ := MStore.unify_sound hu models
                obtain ⟨hmodels1, hbodyElab⟩ := hbodyPost.sound valuation hmodelsBody
                refine ⟨?_, ?_⟩
                · rw [hstore'] at hmodels1
                  exact MStore.Models.of_append_unsolved hmodels1
                · simp only [Expr.realize, Expr.mapAnn]
                  have hselfRealWF : (selfTy.realize valuation).WF k :=
                    Ty.realize_wf_of_models hmodels1 htywf htyalloc htylev
                  rw [hunifyEq] at hbodyElab
                  exact TypingWith.fix hselfRealWF (hmatches valuation) hbodyElab
              · intro valuation models elaboration target typing
                obtain ⟨sem, bodyElab, helab, htarget, hsemwf, hsm, hbody⟩ :=
                  TypingWith.fix_inv typing
                obtain ⟨ext, hmodelsExt, hagreeExt, hreal⟩ :=
                  hprincipal valuation sem models hsm hsemwf
                have hctxeq := ctx_realize_cons_eq pre hagreeExt hreal
                rw [← hctxeq] at hbody
                obtain ⟨extended, hmodelsExt', hagreeExt', hbodyElabReal, hbodyTyReal⟩ :=
                  hbodyPost.principal ext hmodelsExt bodyElab sem hbody
                have hself : selfTy.realize extended = sem := by
                  rw [Ty.realize_agree htyalloc
                    (fun id hi => (hagreeExt' id hi).symm), hreal]
                have hunifies : bodyResult.ty.realize extended = selfTy.realize extended := by
                  rw [hbodyTyReal, hself]
                obtain ⟨result, hresult, hmodelsResult⟩ :=
                  MStore.unify_complete (store := bodyResult.store)
                    (left := bodyResult.ty) (right := selfTy)
                    hbodyPost.safe hbodyPost.tyAllocated
                    (Ty.allocated_mono hbodyPost.grows htyalloc) hmodelsExt' hunifies
                have hresultEq : result = store2 := by
                  rw [hu] at hresult
                  exact (Except.ok.inj hresult).symm
                subst hresultEq
                refine ⟨extended, hmodelsResult, ?_, ?_, ?_⟩
                · intro id hi
                  exact (hagreeExt id hi).trans
                    (hagreeExt' id (lt_of_lt_of_le hi hgrow'))
                · change (Expr.fix (some selfTy) bodyResult.elaboration).realize extended = elaboration
                  rw [helab]
                  show Expr.fix (some (selfTy.realize extended))
                      (Expr.mapAnn (fun x => Ty.realize x extended) bodyResult.elaboration) =
                    Expr.fix (some sem) bodyElab
                  have hbodyMap : Expr.mapAnn (fun x => Ty.realize x extended)
                      bodyResult.elaboration = bodyElab := hbodyElabReal
                  rw [hself, hbodyMap]
                · rw [htarget]
                  exact hself

/-- **The** inference theorem: induction on `src` with the lemmas above. -/
theorem inferAt_spec {sig : Signature} {k : Nat} {ctx : Ctx Nat} {src : Source} {store : MStore}
    (pre : InferPre k ctx store) : InferSpec sig k ctx src store := by
  induction src using Expr.induction generalizing k ctx store with
  | lit literal => exact inferAt_spec_lit pre
  | primOp op => exact inferAt_spec_primOp pre
  | ctor ref => exact inferAt_spec_ctor pre
  | var index => exact inferAt_spec_var pre
  | lambda param body ih =>
      exact inferAt_spec_lambda
        (fun k ctx store pre' => ih (k := k) (ctx := ctx) (store := store) pre') pre
  | app function argument ihFunction ihArgument =>
      exact inferAt_spec_app
        (fun k ctx store pre' => ihFunction (k := k) (ctx := ctx) (store := store) pre')
        (fun k ctx store pre' => ihArgument (k := k) (ctx := ctx) (store := store) pre') pre
  | letIn ann rhs body ihRhs ihBody =>
      cases ann with
      | none =>
          exact inferAt_spec_letMono
            (fun k ctx store pre' => ihRhs (k := k) (ctx := ctx) (store := store) pre')
            (fun k ctx store pre' => ihBody (k := k) (ctx := ctx) (store := store) pre') pre
      | some ann =>
          exact inferAt_spec_letPoly
            (fun k ctx store pre' => ihRhs (k := k) (ctx := ctx) (store := store) pre')
            (fun k ctx store pre' => ihBody (k := k) (ctx := ctx) (store := store) pre') pre
  | fix self body ih =>
      exact inferAt_spec_fix
        (fun k ctx store pre' => ih (k := k) (ctx := ctx) (store := store) pre') pre
  | «match» scrutinee branches ihScrutinee ihBranches =>
      exact inferAt_spec_match
        (fun k ctx store pre' => ihScrutinee (k := k) (ctx := ctx) (store := store) pre')
        (fun branch mem k ctx store pre' =>
          ihBranches branch mem (k := k) (ctx := ctx) (store := store) pre') pre

end EPL
