import EPL2.Spec.InferLet

/-!
# Inference is sound and complete

The whole correctness argument is **one induction**, `inferAt_spec`, on the
source program, with one lemma per constructor. Each is a short composition
of the specifications of the store operations (`EPL2.Spec.Store`,
`EPL2.Spec.Unify`); none unfolds `MStore.unify`. The explicit let is in
`EPL2.Spec.InferLet`.

The public theorems (`infer_eq_some_iff` and friends, in `EPL2.Theorems`) are
corollaries.

**Proof guidance for the cases.** For each constructor, first state and prove
(by `rfl` or `simp [inferAt]`) an equation unfolding `inferAt` on it into
nested `match`/`Option.bind`, then split along it.

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

namespace EPL2

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
  | intAdd =>
      simp only [PrimOp.ty, Option.some.injEq] at typed
      subst typed; simp [Ty.vars]
  | intSub =>
      simp only [PrimOp.ty, Option.some.injEq] at typed
      subst typed; simp [Ty.vars]
  | intLt =>
      by_cases hb : sig.HasBool
      · simp only [PrimOp.ty, hb, if_true, Option.some.injEq] at typed
        subst typed; simp [Ty.bool, Ty.vars]
      · simp [PrimOp.ty, hb] at typed
  | charLt =>
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

private theorem Ty.allocated_getD (args : List InfTy) (i : Nat) (default : InfTy)
    (store : MStore) (defaultVars : default.vars = [])
    (argsAlloc : ∀ arg ∈ args, arg.Allocated store) :
    (args.getD i default).Allocated store := by
  induction args generalizing i with
  | nil =>
      intro id hid
      simp [List.getD] at hid
      rw [defaultVars] at hid
      simp at hid
  | cons a as ih =>
    cases i with
    | zero => simpa using argsAlloc a (by simp)
    | succ i =>
      have hstep := ih (i := i) (fun arg ha => argsAlloc arg (by simp [ha]))
      simpa [List.getD] using hstep

private theorem Ty.levelBounded_getD (args : List InfTy) (i level : Nat)
    (default : InfTy) (store : MStore) (defaultVars : default.vars = [])
    (argsLB : ∀ arg ∈ args, arg.LevelBounded store level) :
    (args.getD i default).LevelBounded store level := by
  induction args generalizing i with
  | nil =>
      intro id hid
      simp [List.getD] at hid
      rw [defaultVars] at hid
      simp at hid
  | cons a as ih =>
    cases i with
    | zero => simpa using argsLB a (by simp)
    | succ i =>
      have hstep := ih (i := i) (fun arg ha => argsLB arg (by simp [ha]))
      simpa [List.getD] using hstep

private theorem Ty.allocated_instantiate : ∀ (ty : InfTy) (args : List InfTy) (store : MStore),
    ty.Allocated store → (∀ arg ∈ args, arg.Allocated store) →
    (ty.instantiate args).Allocated store
  | .prim _, _, _, _, _ => by simp [Ty.instantiate, Ty.subst, Ty.vars, Ty.Allocated]
  | .con _, _, _, _, _ => by simp [Ty.instantiate, Ty.subst, Ty.vars, Ty.Allocated]
  | .rigid _, _, _, _, _ => by simp [Ty.instantiate, Ty.subst, Ty.vars, Ty.Allocated]
  | .var _, _, _, h, _ => by
      simpa [Ty.instantiate, Ty.subst, Ty.vars, Ty.Allocated] using h _ (by simp [Ty.vars])
  | .bvar i, args, store, _, ha => by
      simpa [Ty.instantiate, Ty.subst] using
        Ty.allocated_getD args i (.bvar i) store rfl ha
  | .arrow d c, args, store, h, ha => by
      have hd := Ty.allocated_instantiate d args store (fun id hi => h id (by simp [Ty.vars, hi])) ha
      have hc := Ty.allocated_instantiate c args store (fun id hi => h id (by simp [Ty.vars, hi])) ha
      intro id hmem
      simp only [Ty.instantiate, Ty.subst, Ty.vars, List.mem_append] at hmem
      exact hmem.elim (hd id) (hc id)
  | .app d c, args, store, h, ha => by
      have hd := Ty.allocated_instantiate d args store (fun id hi => h id (by simp [Ty.vars, hi])) ha
      have hc := Ty.allocated_instantiate c args store (fun id hi => h id (by simp [Ty.vars, hi])) ha
      intro id hmem
      simp only [Ty.instantiate, Ty.subst, Ty.vars, List.mem_append] at hmem
      exact hmem.elim (hd id) (hc id)

private theorem Ty.levelBounded_instantiate : ∀ (ty : InfTy) (args : List InfTy) (store : MStore)
    (level : Nat), ty.LevelBounded store level →
    (∀ arg ∈ args, arg.LevelBounded store level) →
    (ty.instantiate args).LevelBounded store level
  | .prim _, _, _, _, _, _ => by simp [Ty.instantiate, Ty.subst, Ty.vars, Ty.LevelBounded]
  | .con _, _, _, _, _, _ => by simp [Ty.instantiate, Ty.subst, Ty.vars, Ty.LevelBounded]
  | .rigid _, _, _, _, _, _ => by simp [Ty.instantiate, Ty.subst, Ty.vars, Ty.LevelBounded]
  | .var _, _, _, _, h, _ => by
      simpa [Ty.instantiate, Ty.subst, Ty.vars, Ty.LevelBounded] using h _ (by simp [Ty.vars])
  | .bvar i, args, store, level, _, ha => by
      simpa [Ty.instantiate, Ty.subst] using
        Ty.levelBounded_getD args i level (.bvar i) store rfl ha
  | .arrow d c, args, store, level, h, ha => by
      have hd := Ty.levelBounded_instantiate d args store level
        (fun id hi => h id (by simp [Ty.vars, hi])) ha
      have hc := Ty.levelBounded_instantiate c args store level
        (fun id hi => h id (by simp [Ty.vars, hi])) ha
      intro id hmem
      simp only [Ty.instantiate, Ty.subst, Ty.vars, List.mem_append] at hmem
      exact hmem.elim (hd id) (hc id)
  | .app d c, args, store, level, h, ha => by
      have hd := Ty.levelBounded_instantiate d args store level
        (fun id hi => h id (by simp [Ty.vars, hi])) ha
      have hc := Ty.levelBounded_instantiate c args store level
        (fun id hi => h id (by simp [Ty.vars, hi])) ha
      intro id hmem
      simp only [Ty.instantiate, Ty.subst, Ty.vars, List.mem_append] at hmem
      exact hmem.elim (hd id) (hc id)

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

/-! ## Inverting a typing derivation -/

private theorem TypingWith.primOp_type {sig : Signature} {Det : LetCondition} {k : Nat} {ctx : Ctx Empty}
    {op : PrimOp} {elaboration : Elab} {ty : SemTy}
    (typing : TypingWith sig Det k ctx (.primOp op) elaboration ty) : op.ty sig = some ty := by
  cases typing with
  | primOp h => exact h

private theorem TypingWith.const_inv {sig : Signature} {Det : LetCondition} {k : Nat} {ctx : Ctx Empty}
    {c : DataConst} {elaboration : Elab} {ty : SemTy}
    (typing : TypingWith sig Det k ctx (.const c) elaboration ty) :
    elaboration = .const c ∧
      ∃ scheme : Scheme Empty, ∃ args : List SemTy,
        sig.schemeOf c = some scheme ∧ args.length = scheme.arity ∧
          (∀ arg ∈ args, arg.WF k) ∧ ty = scheme.inst args := by
  cases typing with
  | const h inst =>
      obtain ⟨args, hlen, hwf, hinst⟩ := inst
      exact ⟨rfl, _, args, h, hlen, hwf, hinst.symm⟩

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
    {self : Template} {body : Source} {elaboration : Elab} {ty : SemTy}
    (typing : TypingWith sig Det k ctx (.fix self body) elaboration ty) :
    ∃ sem : SemTy, ∃ bodyElab : Elab,
      elaboration = .fix sem bodyElab ∧ ty = sem ∧ sem.WF k ∧
        self.Matches sem ∧ TypingWith sig Det k (.mono sem :: ctx) body bodyElab sem := by
  cases typing with
  | fix hwf hmatches hbody => exact ⟨_, _, rfl, rfl, hwf, hmatches, hbody⟩

theorem inferAt_spec_lit {sig : Signature} (pre : InferPre k ctx store) :
    InferSpec sig k ctx (.lit literal) store := by
  have h : inferAt sig k ctx (.lit literal) store =
      some ⟨literal.ty, .lit literal, store⟩ := rfl
  simp only [InferSpec, h]
  refine
    { safe := pre.safe
      grows := le_rfl
      levels := ?_
      tyWF := PrimLit.ty_wf literal
      tyAllocated := ?_
      tyLevels := ?_
      elabAllocated := ?_
      anchored := ?_
      sound := ?_
      principal := ?_ }
  · intro id _
    exact le_rfl
  · intro id hmem
    rw [PrimLit.ty_vars] at hmem
    simp at hmem
  · intro id hmem
    rw [PrimLit.ty_vars] at hmem
    simp at hmem
  · intro ann hmem
    simp [Expr.anns] at hmem
  · intro start level _ _ hanch
    exact hanch
  · intro valuation models
    refine ⟨models, ?_⟩
    have hty : (literal.ty : InfTy).realize valuation = (literal.ty : SemTy) :=
      PrimLit.ty_bind literal valuation
    simp only [Expr.realize, Expr.mapAnn, hty]
    exact TypingWith.lit
  · intro valuation models elaboration ty typing
    cases typing with
    | lit =>
      refine ⟨valuation, models, ?_, ?_, ?_⟩
      · intro id _; rfl
      · rfl
      · exact PrimLit.ty_bind literal valuation

theorem inferAt_spec_primOp {sig : Signature} (pre : InferPre k ctx store) :
    InferSpec sig k ctx (.primOp op) store := by
  have hbind : inferAt sig k ctx (.primOp op) store =
      (op.ty sig).bind (fun ty => some ⟨ty, .primOp op, store⟩) := rfl
  cases hop : op.ty sig with
  | none =>
      have h : inferAt sig k ctx (.primOp op) store = none := by
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
          some ⟨ty, .primOp op, store⟩ := by
        rw [hbind, hop]; rfl
      simp only [InferSpec, h]
      have htyvars : ty.vars = [] := PrimOp.ty_vars hop
      refine
        { safe := pre.safe
          grows := le_rfl
          levels := ?_
          tyWF := PrimOp.ty_wf hop
          tyAllocated := ?_
          tyLevels := ?_
          elabAllocated := ?_
          anchored := ?_
          sound := ?_
          principal := ?_ }
      · intro id _
        exact le_rfl
      · intro id hmem
        rw [htyvars] at hmem
        simp at hmem
      · intro id hmem
        rw [htyvars] at hmem
        simp at hmem
      · intro ann hmem
        simp [Expr.anns] at hmem
      · intro start level _ _ hanch
        exact hanch
      · intro valuation models
        refine ⟨models, ?_⟩
        simp only [Expr.realize, Expr.mapAnn]
        exact TypingWith.primOp (PrimOp.ty_bind hop valuation)
      · intro valuation models elaboration target typing
        cases typing with
        | primOp hty =>
            refine ⟨valuation, models, ?_, ?_, ?_⟩
            · intro id _; rfl
            · rfl
            · have hsame : (ty.bind valuation : SemTy) = target := by
                have h1 := PrimOp.ty_bind hop valuation
                rw [h1] at hty
                exact Option.some.inj hty
              exact hsame

theorem inferAt_spec_const {sig : Signature} (pre : InferPre k ctx store) :
    InferSpec sig k ctx (.const c) store := by
  have hbind : inferAt sig k ctx (.const c) store =
      (sig.schemeOf c).bind (fun scheme =>
        (fun (args : List InfTy) (store : MStore) =>
          some ⟨scheme.lift.inst args, .const c, store⟩)
          (store.freshMany k scheme.arity).1 (store.freshMany k scheme.arity).2) := rfl
  cases hsch : sig.schemeOf c with
  | none =>
      have h : inferAt sig k ctx (.const c) store = none := by
        rw [hbind, hsch]; rfl
      simp only [InferSpec, h]
      intro valuation models elaboration ty typing
      cases typing with
      | const htyping _ =>
          rw [hsch] at htyping
          cases htyping
  | some scheme =>
      have h : inferAt sig k ctx (.const c) store =
          some ⟨(scheme.lift : Scheme Nat).inst (store.freshMany k scheme.arity).1,
            .const c, (store.freshMany k scheme.arity).2⟩ := by
        rw [hbind, hsch]; rfl
      simp only [InferSpec, h]
      have hargsWF : ∀ arg ∈ (store.freshMany k scheme.arity).1, arg.WF k :=
        freshMany_args_wf
      have hlen : (store.freshMany k scheme.arity).1.length = scheme.arity :=
        freshMany_fst_length store k scheme.arity
      have hargsAlloc : ∀ arg ∈ (store.freshMany k scheme.arity).1,
          arg.Allocated (store ++ List.replicate scheme.arity ⟨k, none⟩) :=
        freshMany_args_allocated
      have hargsLB : ∀ arg ∈ (store.freshMany k scheme.arity).1,
          arg.LevelBounded (store ++ List.replicate scheme.arity ⟨k, none⟩) k :=
        freshMany_args_levelBounded
      have hschemeWF0 : scheme.WF 0 := Signature.schemeOf_wf hsch
      have hschemeWFk : scheme.body.Scoped k scheme.arity :=
        Ty.Scoped.mono hschemeWF0 (by omega) le_rfl
      have hliftWF : (scheme.lift : Scheme Nat).WF k := by
        simpa [Scheme.lift] using (Ty.scoped_lift).2 hschemeWFk
      have hbodyAlloc : (scheme.lift : Scheme Nat).body.Allocated
          (store ++ List.replicate scheme.arity ⟨k, none⟩) := by
        intro id hid
        rw [Scheme.lift] at hid
        rw [Ty.vars_lift] at hid
        simp at hid
      have hbodyLB : (scheme.lift : Scheme Nat).body.LevelBounded
          (store ++ List.replicate scheme.arity ⟨k, none⟩) k := by
        intro id hid
        rw [Scheme.lift] at hid
        rw [Ty.vars_lift] at hid
        simp at hid
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
        obtain ⟨hmodelsStore, _⟩ :=
          (MStore.models_append_unsolved (store := store) (count := scheme.arity)
            (level := k)).1 models
        refine ⟨hmodelsStore, ?_⟩
        simp only [Expr.realize, Expr.mapAnn]
        have hargsRealWF : ∀ arg ∈ (store.freshMany k scheme.arity).1,
            (arg.realize valuation).WF k := freshMany_args_realize_wf models
        have hclosed : ∀ id ∈ (scheme.lift : Scheme Nat).body.vars, (valuation id).WF k := by
          intro id hid
          rw [Scheme.lift] at hid
          rw [Ty.vars_lift] at hid
          simp at hid
        have hreal := Scheme.realize_inst (scheme := (scheme.lift : Scheme Nat))
          (args := (store.freshMany k scheme.arity).1) (valuation := valuation) hclosed
        rw [Scheme.realize_lift] at hreal
        refine TypingWith.const hsch ?_
        refine ⟨(store.freshMany k scheme.arity).1.map (·.realize valuation), ?_, ?_, ?_⟩
        · rw [List.length_map, hlen]
        · intro arg harg
          rw [List.mem_map] at harg
          obtain ⟨orig, horig, rfl⟩ := harg
          exact hargsRealWF orig horig
        · exact hreal.symm
      · intro valuation models elaboration target typing
        cases typing with
        | const htyping hinst =>
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
                rw [Scheme.lift] at hid
                rw [Ty.vars_lift] at hid
                simp at hid
              have hreal := Scheme.realize_inst (scheme := (scheme.lift : Scheme Nat))
                (args := (store.freshMany k scheme.arity).1) (valuation := extended) hclosed
              rw [Scheme.realize_lift, hmap] at hreal
              rw [← hinstEq]
              exact hreal

theorem inferAt_spec_var {sig : Signature} (pre : InferPre k ctx store) :
    InferSpec sig k ctx (.var index) store := by
  have hbind : inferAt sig k ctx (.var index) store =
      (ctx[index]?).bind (fun scheme =>
        (fun (args : List InfTy) (store : MStore) =>
          some ⟨scheme.inst args, .var index, store⟩)
          (store.freshMany k scheme.arity).1 (store.freshMany k scheme.arity).2) := rfl
  cases hget : ctx[index]? with
  | none =>
      have h : inferAt sig k ctx (.var index) store = none := by
        rw [hbind, hget]; rfl
      simp only [InferSpec, h]
      intro valuation models elaboration ty typing
      cases typing with
      | var htyping _ =>
          rw [Ctx.realize_getElem?, hget] at htyping
          simp at htyping
  | some scheme =>
      have h : inferAt sig k ctx (.var index) store =
          some ⟨scheme.inst (store.freshMany k scheme.arity).1, .var index,
            (store.freshMany k scheme.arity).2⟩ := by
        rw [hbind, hget]; rfl
      simp only [InferSpec, h]
      have hmem : scheme ∈ ctx := List.mem_of_getElem? hget
      have hargsWF : ∀ arg ∈ (store.freshMany k scheme.arity).1, arg.WF k :=
        freshMany_args_wf
      have hlen : (store.freshMany k scheme.arity).1.length = scheme.arity :=
        freshMany_fst_length store k scheme.arity
      have hargsAlloc : ∀ arg ∈ (store.freshMany k scheme.arity).1,
          arg.Allocated (store ++ List.replicate scheme.arity ⟨k, none⟩) :=
        freshMany_args_allocated
      have hargsLB : ∀ arg ∈ (store.freshMany k scheme.arity).1,
          arg.LevelBounded (store ++ List.replicate scheme.arity ⟨k, none⟩) k :=
        freshMany_args_levelBounded
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
        obtain ⟨hmodelsStore, _⟩ :=
          (MStore.models_append_unsolved (store := store) (count := scheme.arity)
            (level := k)).1 models
        refine ⟨hmodelsStore, ?_⟩
        simp only [Expr.realize, Expr.mapAnn]
        have hctxget : (ctx.realize valuation)[index]? = some (scheme.realize valuation) := by
          rw [Ctx.realize_getElem?, hget]; rfl
        have hargsRealWF : ∀ arg ∈ (store.freshMany k scheme.arity).1,
            (arg.realize valuation).WF k := freshMany_args_realize_wf models
        have hclosed : ∀ id ∈ scheme.body.vars, (valuation id).WF k :=
          fun id hid => ctx_image_wf (pre := pre) hmodelsStore hmem hid
        have hreal := Scheme.realize_inst (scheme := scheme)
          (args := (store.freshMany k scheme.arity).1) (valuation := valuation) hclosed
        refine TypingWith.var hctxget ?_
        rw [hreal]
        refine ⟨(store.freshMany k scheme.arity).1.map (·.realize valuation), ?_, ?_, rfl⟩
        · rw [List.length_map, hlen]
          rfl
        · intro arg harg
          rw [List.mem_map] at harg
          obtain ⟨orig, horig, rfl⟩ := harg
          exact hargsRealWF orig horig
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
              ((MStore.models_append_unsolved (store := store) (count := scheme.arity)
                (level := k)).1 hmodels').1
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
      (paramTy k store param).bind (fun pair =>
        (inferAt sig k (.mono pair.1 :: ctx) body pair.2).bind (fun bodyResult =>
          some ⟨.arrow pair.1 bodyResult.ty, .lambda (some pair.1) bodyResult.elaboration,
            bodyResult.store⟩)) := rfl
  cases hp : paramTy k store param with
  | none =>
      have h : inferAt sig k ctx (.lambda param body) store = none := by
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
          (inferAt sig k (.mono pty :: ctx) body store').bind (fun bodyResult =>
            some ⟨.arrow pty bodyResult.ty, .lambda (some pty) bodyResult.elaboration,
              bodyResult.store⟩) := by
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
      have hpreExt : InferPre k ctx store' := pre.extend hsafe' hgrow' hlev'
      have hpre' : InferPre k (.mono pty :: ctx) store' :=
        InferPre.cons_mono hpreExt htywf htyalloc htylev
      cases hb : inferAt sig k (.mono pty :: ctx) body store' with
      | none =>
          have hnone : inferAt sig k ctx (.lambda param body) store = none := by
            simp only [h, hb, Option.bind]
          simp only [InferSpec, hnone]
          have hbodyNone := bodySpec k (.mono pty :: ctx) store' hpre'
          unfold InferSpec at hbodyNone
          rw [hb] at hbodyNone
          intro valuation models elaboration ty typing
          obtain ⟨sem, bodyElab, bodyTy, _, _, hsemwf, hsemmatches, hbody⟩ :=
            TypingWith.lambda_inv typing
          obtain ⟨ext', hmodels', hagree', hreal'⟩ :=
            hprincipal valuation sem models hsemmatches hsemwf
          have hctxeq : Ctx.realize (.mono pty :: ctx) ext' =
              .mono sem :: ctx.realize valuation := by
            simp only [Ctx.realize_cons, Scheme.realize_mono]
            rw [hreal']
            congr 1
            exact Ctx.realize_congr
              (fun scheme hmem id hid => pre.ctxAllocated scheme hmem id hid)
              (fun id hi => (hagree' id hi).symm)
          rw [← hctxeq] at hbody
          exact hbodyNone ext' hmodels' bodyElab bodyTy hbody
      | some bodyResult =>
          have hsucc : inferAt sig k ctx (.lambda param body) store =
              some ⟨.arrow pty bodyResult.ty, .lambda (some pty) bodyResult.elaboration,
                bodyResult.store⟩ := by
            simp only [h, hb, Option.bind]
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
              exact ((MStore.models_append_unsolved (store := store)
                (count := store'.length - store.length) (level := k)).1 hmodels').1
            · simp only [Expr.realize, Expr.mapAnn]
              exact TypingWith.lambda
                (Ty.realize_wf_of_models hmodels' htywf htyalloc htylev)
                (hmatches valuation) hbodyElab
          · intro valuation models elaboration target typing
            obtain ⟨sem, bodyElab, bodyTy, helab, htarget, hsemwf, hsemmatches, hbody⟩ :=
              TypingWith.lambda_inv typing
            obtain ⟨ext', hmodels', hagree', hreal'⟩ :=
              hprincipal valuation sem models hsemmatches hsemwf
            have hctxeq : Ctx.realize (.mono pty :: ctx) ext' =
                .mono sem :: ctx.realize valuation := by
              simp only [Ctx.realize_cons, Scheme.realize_mono]
              rw [hreal']
              congr 1
              exact Ctx.realize_congr
                (fun scheme hmem id hid => pre.ctxAllocated scheme hmem id hid)
                (fun id hi => (hagree' id hi).symm)
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

theorem inferAt_spec_app {sig : Signature} {function argument : Source}
    (functionSpec : ∀ k ctx store, InferPre k ctx store → InferSpec sig k ctx function store)
    (argumentSpec : ∀ k ctx store, InferPre k ctx store → InferSpec sig k ctx argument store)
    (pre : InferPre k ctx store) :
    InferSpec sig k ctx (.app function argument) store := by
  have hbind : inferAt sig k ctx (.app function argument) store =
      (inferAt sig k ctx function store).bind (fun functionResult =>
        (inferAt sig k ctx argument functionResult.store).bind (fun argumentResult =>
          (fun (resultTy : InfTy) (store : MStore) =>
            (store.unify functionResult.ty (.arrow argumentResult.ty resultTy)).bind
              (fun store =>
                some ⟨resultTy, .app functionResult.elaboration argumentResult.elaboration,
                  store⟩))
            (argumentResult.store.fresh k).1 (argumentResult.store.fresh k).2)) := rfl
  cases hf : inferAt sig k ctx function store with
  | none =>
      have h : inferAt sig k ctx (.app function argument) store = none := by
        rw [hbind, hf]; rfl
      simp only [InferSpec, h]
      have hfunNone := functionSpec k ctx store pre
      unfold InferSpec at hfunNone
      rw [hf] at hfunNone
      intro valuation models elaboration target typing
      obtain ⟨fElab, aElab, argTy, resTy, _, _, hfun, _⟩ := TypingWith.app_inv typing
      exact hfunNone valuation models fElab (.arrow argTy resTy) hfun
  | some functionResult =>
      have hfunPost := functionSpec k ctx store pre
      unfold InferSpec at hfunPost
      rw [hf] at hfunPost
      simp only at hfunPost
      have hpreArg : InferPre k ctx functionResult.store :=
        pre.extend hfunPost.safe hfunPost.grows hfunPost.levels
      cases ha : inferAt sig k ctx argument functionResult.store with
      | none =>
          have h : inferAt sig k ctx (.app function argument) store = none := by
            simp only [hbind, hf, ha, Option.bind]
          simp only [InferSpec, h]
          have hargNone := argumentSpec k ctx functionResult.store hpreArg
          unfold InferSpec at hargNone
          rw [ha] at hargNone
          intro valuation models elaboration target typing
          obtain ⟨fElab, aElab, argTy, resTy, _, _, hfun, harg⟩ := TypingWith.app_inv typing
          have hfunTyping := Elaborates.typing hfun
          obtain ⟨extF, hmodelsF, hagreeF, _, _⟩ :=
            hfunPost.principal valuation models fElab (.arrow argTy resTy) hfunTyping
          have hctxF : ctx.realize extF = ctx.realize valuation :=
            Ctx.realize_congr
              (fun scheme hmem id hid => pre.ctxAllocated scheme hmem id hid)
              (fun id hi => (hagreeF id hi).symm)
          rw [← hctxF] at harg
          exact hargNone extF hmodelsF aElab argTy harg
      | some argumentResult =>
          have hargPost := argumentSpec k ctx functionResult.store hpreArg
          unfold InferSpec at hargPost
          rw [ha] at hargPost
          simp only at hargPost
          have hfreshSnd : (argumentResult.store.fresh k).2 =
              argumentResult.store ++ List.replicate 1 (⟨k, none⟩ : MEntry) := rfl
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
            · rw [MStore.fresh_eq]
              intro id hid
              simp only [Ty.vars, List.mem_singleton] at hid
              subst hid
              simp
          cases hu : (argumentResult.store.fresh k).2.unify functionResult.ty
              (.arrow argumentResult.ty (argumentResult.store.fresh k).1) with
          | none =>
              have h : inferAt sig k ctx (.app function argument) store = none := by
                simp only [hbind, hf, ha, hu, Option.bind]
              simp only [InferSpec, h]
              intro valuation models elaboration target typing
              obtain ⟨fElab, aElab, argTy, resTy, _, htarget, hfun, harg⟩ :=
                TypingWith.app_inv typing
              have hfunTyping := Elaborates.typing hfun
              have hargTyping := Elaborates.typing harg
              have hctxWF : (ctx.realize valuation).WF k :=
                Ctx.realize_wf models pre.ctxWF pre.ctxAllocated pre.ctxLevels
              have hresWF : resTy.WF k := by
                have := TypingWith.regular hctxWF typing
                rwa [htarget] at this
              obtain ⟨extF, hmodelsF, hagreeF, _, hfunTyReal⟩ :=
                hfunPost.principal valuation models fElab (.arrow argTy resTy) hfunTyping
              have hctxF : ctx.realize extF = ctx.realize valuation :=
                Ctx.realize_congr
                  (fun scheme hmem id hid => pre.ctxAllocated scheme hmem id hid)
                  (fun id hi => (hagreeF id hi).symm)
              rw [← hctxF] at harg
              rw [← hctxF] at hargTyping
              obtain ⟨extA, hmodelsA, hagreeFA, _, hargTyReal⟩ :=
                hargPost.principal extF hmodelsF aElab argTy hargTyping
              let ext1 : Valuation :=
                Function.update extA argumentResult.store.length resTy
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
                  simpa [ext1, Function.update] using hresWF
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
              obtain ⟨result, hresult, _⟩ :=
                MStore.unify_complete hsafeFresh hleftAllocFresh hrightAllocFresh
                  hmodelsFresh hunifies
              rw [hu] at hresult
              cases hresult
          | some store2 =>
              have hsucc : inferAt sig k ctx (.app function argument) store =
                  some ⟨(argumentResult.store.fresh k).1,
                    .app functionResult.elaboration argumentResult.elaboration, store2⟩ := by
                simp only [hbind, hf, ha, hu, Option.bind]
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
              · show ((argumentResult.store.fresh k).1).Allocated store2
                have halloc : ((argumentResult.store.fresh k).1).Allocated
                    (argumentResult.store.fresh k).2 := by
                  rw [MStore.fresh_eq]
                  intro id hid
                  simp only [Ty.vars, List.mem_singleton] at hid
                  subst hid
                  simp
                exact Ty.allocated_mono (le_of_eq (MStore.unify_length hu).symm) halloc
              · show ((argumentResult.store.fresh k).1).LevelBounded store2 k
                have halloc : ((argumentResult.store.fresh k).1).Allocated
                    (argumentResult.store.fresh k).2 := by
                  rw [MStore.fresh_eq]
                  intro id hid
                  simp only [Ty.vars, List.mem_singleton] at hid
                  subst hid
                  simp
                have hbounded : ((argumentResult.store.fresh k).1).LevelBounded
                    (argumentResult.store.fresh k).2 k := by
                  rw [MStore.fresh_eq]
                  intro id hid
                  simp only [Ty.vars, List.mem_singleton] at hid
                  subst hid
                  rw [MStore.append_unsolved_levelOf, if_neg (by omega), if_pos (by omega)]
                exact Ty.levelBounded_mono halloc hbounded
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
                exact MStore.unify_anchored hsafeFresh h2 hu
              · intro valuation models2
                obtain ⟨hmodelsFresh, hunifyEq⟩ := MStore.unify_sound hu models2
                have hmodelsArg : argumentResult.store.Models valuation :=
                  ((MStore.models_append_unsolved (store := argumentResult.store)
                    (count := 1) (level := k)).1 hmodelsFresh).1
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
                obtain ⟨extF, hmodelsF, hagreeF, hfunElabReal, hfunTyReal⟩ :=
                  hfunPost.principal valuation models fElab (.arrow argTy resTy) hfun
                have hctxF : ctx.realize extF = ctx.realize valuation :=
                  Ctx.realize_congr
                    (fun scheme hmem id hid => pre.ctxAllocated scheme hmem id hid)
                    (fun id hi => (hagreeF id hi).symm)
                rw [← hctxF] at harg
                obtain ⟨extA, hmodelsA, hagreeFA, hargElabReal, hargTyReal⟩ :=
                  hargPost.principal extF hmodelsF aElab argTy harg
                let ext1 : Valuation :=
                  Function.update extA argumentResult.store.length resTy
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
                    simpa [ext1, Function.update] using hresWF
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
                obtain ⟨result, hresult, hmodelsResult⟩ :=
                  MStore.unify_complete hsafeFresh hleftAllocFresh hrightAllocFresh
                    hmodelsFresh hunifies
                have hfunElab1 : functionResult.elaboration.realize ext1 = fElab := by
                  rw [← Expr.realize_agree (store := argumentResult.store)
                    (fun ann hann =>
                      Ty.allocated_mono hargPost.grows (hfunPost.elabAllocated ann hann))
                    hagreeA1]
                  rw [← Expr.realize_agree (store := functionResult.store)
                    hfunPost.elabAllocated hagreeFA]
                  exact hfunElabReal
                have hargElab1 : argumentResult.elaboration.realize ext1 = aElab := by
                  rw [← Expr.realize_agree (store := argumentResult.store)
                    hargPost.elabAllocated hagreeA1]
                  exact hargElabReal
                have hresultEq : result = store2 := by
                  rw [hu] at hresult
                  exact (Option.some.inj hresult).symm
                subst hresultEq
                refine ⟨ext1, hmodelsResult, ?_, ?_, ?_⟩
                · intro id hi
                  exact (hagreeF id hi).trans
                    ((hagreeFA id (lt_of_lt_of_le hi hfunPost.grows)).trans
                      (hagreeA1 id (lt_of_lt_of_le hi (le_trans hfunPost.grows hargPost.grows))))
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
      (inferAt sig k ctx rhs store).bind (fun rhsResult =>
        (inferAt sig k (.mono rhsResult.ty :: ctx) body rhsResult.store).bind (fun bodyResult =>
          some ⟨bodyResult.ty,
            .letIn none rhsResult.elaboration bodyResult.elaboration,
            bodyResult.store⟩)) := rfl
  cases hr : inferAt sig k ctx rhs store with
  | none =>
      have h : inferAt sig k ctx (.letIn none rhs body) store = none := by
        rw [hbind, hr]; rfl
      simp only [InferSpec, h]
      have hrhsNone := rhsSpec k ctx store pre
      unfold InferSpec at hrhsNone
      rw [hr] at hrhsNone
      intro valuation models elaboration ty typing
      obtain ⟨rhsElab, rhsTy, bodyElab, bodyTy, _, _, hrhs, _⟩ :=
        TypingWith.letMono_inv typing
      exact hrhsNone valuation models rhsElab rhsTy hrhs
  | some rhsResult =>
      have h : inferAt sig k ctx (.letIn none rhs body) store =
          (inferAt sig k (.mono rhsResult.ty :: ctx) body rhsResult.store).bind
            (fun bodyResult =>
              some ⟨bodyResult.ty,
                .letIn none rhsResult.elaboration bodyResult.elaboration,
                bodyResult.store⟩) := by
        rw [hbind, hr]; rfl
      have hrhsPost := rhsSpec k ctx store pre
      unfold InferSpec at hrhsPost
      rw [hr] at hrhsPost
      simp only at hrhsPost
      have hpreExt : InferPre k ctx rhsResult.store :=
        pre.extend hrhsPost.safe hrhsPost.grows hrhsPost.levels
      have hpre' : InferPre k (.mono rhsResult.ty :: ctx) rhsResult.store :=
        InferPre.cons_mono hpreExt hrhsPost.tyWF hrhsPost.tyAllocated hrhsPost.tyLevels
      cases hb : inferAt sig k (.mono rhsResult.ty :: ctx) body rhsResult.store with
      | none =>
          have hnone : inferAt sig k ctx (.letIn none rhs body) store = none := by
            simp only [h, hb, Option.bind]
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
          have hctxeq : Ctx.realize (.mono rhsResult.ty :: ctx) ext =
              .mono rhsTy :: ctx.realize valuation := by
            simp only [Ctx.realize_cons, Scheme.realize_mono]
            rw [hrhsTyReal]
            congr 1
            exact Ctx.realize_congr
              (fun scheme hmem id hid => pre.ctxAllocated scheme hmem id hid)
              (fun id hi => (hagreeExt id hi).symm)
          rw [← hctxeq] at hbody
          exact hbodyNone ext hmodelsExt bodyElab bodyTy hbody
      | some bodyResult =>
          have hsucc : inferAt sig k ctx (.letIn none rhs body) store =
              some ⟨bodyResult.ty,
                .letIn none rhsResult.elaboration bodyResult.elaboration,
                bodyResult.store⟩ := by
            simp only [h, hb, Option.bind]
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
            have hctxeq : Ctx.realize (.mono rhsResult.ty :: ctx) ext =
                .mono rhsTy :: ctx.realize valuation := by
              simp only [Ctx.realize_cons, Scheme.realize_mono]
              rw [hrhsTyReal]
              congr 1
              exact Ctx.realize_congr
                (fun scheme hmem id hid => pre.ctxAllocated scheme hmem id hid)
                (fun id hi => (hagreeExt id hi).symm)
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
              have hrhsElab1 : rhsResult.elaboration.realize extended = rhsElab := by
                rw [← Expr.realize_agree (store := rhsResult.store)
                  hrhsPost.elabAllocated hagreeExt']
                exact hrhsElabReal
              have hrhsMap : Expr.mapAnn (fun x => Ty.realize x extended)
                  rhsResult.elaboration = rhsElab := hrhsElab1
              have hbodyMap : Expr.mapAnn (fun x => Ty.realize x extended)
                  bodyResult.elaboration = bodyElab := hbodyElabReal
              rw [hrhsMap, hbodyMap]
            · rw [htarget]
              exact hbodyTyReal

theorem inferAt_spec_fix {sig : Signature} {self : Template} {body : Source}
    (bodySpec : ∀ k ctx store, InferPre k ctx store → InferSpec sig k ctx body store)
    (pre : InferPre k ctx store) :
    InferSpec sig k ctx (.fix self body) store := by
  have hbind : inferAt sig k ctx (.fix self body) store =
      (if ¬ self.WF k then none else
        (fun (selfTy : InfTy) (store : MStore) =>
          (inferAt sig k (.mono selfTy :: ctx) body store).bind (fun bodyResult =>
            (bodyResult.store.unify bodyResult.ty selfTy).bind (fun store =>
              some ⟨selfTy, .fix selfTy bodyResult.elaboration, store⟩)))
          (store.allocate k self).1 (store.allocate k self).2) := rfl
  by_cases hwf : self.WF k
  · have hbase : inferAt sig k ctx (.fix self body) store =
        (fun (selfTy : InfTy) (store : MStore) =>
          (inferAt sig k (.mono selfTy :: ctx) body store).bind (fun bodyResult =>
            (bodyResult.store.unify bodyResult.ty selfTy).bind (fun store =>
              some ⟨selfTy, .fix selfTy bodyResult.elaboration, store⟩)))
          (store.allocate k self).1 (store.allocate k self).2 := by
      rw [hbind]; simp [hwf]
    obtain ⟨hselfWF, hselfAlloc, hselfOuter⟩ :=
      MStore.allocate_wf (store := store) (level := k) (template := self) hwf
    have hsafe1 : (store.allocate k self).2.Safe := by
      rw [MStore.allocate_snd]
      exact MStore.append_unsolved_safe pre.safe
    have hgrow1 : store.length ≤ (store.allocate k self).2.length := by
      rw [MStore.allocate_snd]; simp
    have hlev1 : ∀ id < store.length, (store.allocate k self).2.levelOf id ≤ store.levelOf id := by
      intro id hi
      rw [MStore.allocate_snd, MStore.append_unsolved_levelOf, if_pos hi]
    have hselfLev : (store.allocate k self).1.LevelBounded (store.allocate k self).2 k := by
      rw [MStore.allocate_snd]
      exact Ty.levelBounded_append hselfAlloc hselfOuter
    have hpreExt : InferPre k ctx (store.allocate k self).2 :=
      pre.extend hsafe1 hgrow1 hlev1
    have hpre1 : InferPre k (.mono (store.allocate k self).1 :: ctx) (store.allocate k self).2 :=
      InferPre.cons_mono hpreExt hselfWF hselfAlloc hselfLev
    cases hb : inferAt sig k (.mono (store.allocate k self).1 :: ctx) body
        (store.allocate k self).2 with
    | none =>
        have hnone : inferAt sig k ctx (.fix self body) store = none := by
          simp only [hbase, hb, Option.bind]
        simp only [InferSpec, hnone]
        have hbodyNone := bodySpec k (.mono (store.allocate k self).1 :: ctx)
          (store.allocate k self).2 hpre1
        unfold InferSpec at hbodyNone
        rw [hb] at hbodyNone
        intro valuation models elaboration ty typing
        obtain ⟨sem, bodyElab, _, _, hsemwf, hsm, hbody⟩ := TypingWith.fix_inv typing
        have hbodyTyping := Elaborates.typing hbody
        obtain ⟨ext, hmodelsExt, hagreeExt, hreal⟩ :=
          MStore.allocate_principal (store := store) (level := k) (template := self)
            (ty := sem) pre.safe models hsm hsemwf
        have hctxeq : Ctx.realize (.mono (store.allocate k self).1 :: ctx) ext =
            .mono sem :: ctx.realize valuation := by
          simp only [Ctx.realize_cons, Scheme.realize_mono]
          rw [hreal]
          congr 1
          exact Ctx.realize_congr
            (fun scheme hmem id hid => pre.ctxAllocated scheme hmem id hid)
            (fun id hi => (hagreeExt id hi).symm)
        rw [← hctxeq] at hbody
        exact hbodyNone ext hmodelsExt bodyElab sem hbody
    | some bodyResult =>
        have h : inferAt sig k ctx (.fix self body) store =
            (bodyResult.store.unify bodyResult.ty (store.allocate k self).1).bind
              (fun storeFinal =>
                some ⟨(store.allocate k self).1,
                  .fix (store.allocate k self).1 bodyResult.elaboration, storeFinal⟩) := by
          simp only [hbase, hb, Option.bind]
        have hbodyPost := bodySpec k (.mono (store.allocate k self).1 :: ctx)
          (store.allocate k self).2 hpre1
        unfold InferSpec at hbodyPost
        rw [hb] at hbodyPost
        simp only at hbodyPost
        cases hu : bodyResult.store.unify bodyResult.ty (store.allocate k self).1 with
        | none =>
            have hnone : inferAt sig k ctx (.fix self body) store = none := by
              rw [h, hu]; rfl
            simp only [InferSpec, hnone]
            intro valuation models elaboration ty typing
            obtain ⟨sem, bodyElab, _, _, hsemwf, hsm, hbody⟩ := TypingWith.fix_inv typing
            have hbodyTyping := Elaborates.typing hbody
            obtain ⟨ext, hmodelsExt, hagreeExt, hreal⟩ :=
              MStore.allocate_principal (store := store) (level := k) (template := self)
                (ty := sem) pre.safe models hsm hsemwf
            have hctxeq : Ctx.realize (.mono (store.allocate k self).1 :: ctx) ext =
                .mono sem :: ctx.realize valuation := by
              simp only [Ctx.realize_cons, Scheme.realize_mono]
              rw [hreal]
              congr 1
              exact Ctx.realize_congr
                (fun scheme hmem id hid => pre.ctxAllocated scheme hmem id hid)
                (fun id hi => (hagreeExt id hi).symm)
            rw [← hctxeq] at hbody
            rw [← hctxeq] at hbodyTyping
            obtain ⟨extended, hmodelsExt', hagreeExt', _, hbodyTyReal⟩ :=
              hbodyPost.principal ext hmodelsExt bodyElab sem hbodyTyping
            have hself : (store.allocate k self).1.realize extended = sem := by
              rw [Ty.realize_agree hselfAlloc
                (fun id hi => (hagreeExt' id hi).symm), hreal]
            have hunifies : bodyResult.ty.realize extended =
                (store.allocate k self).1.realize extended := by
              rw [hbodyTyReal, hself]
            obtain ⟨result, hresult, _⟩ :=
              MStore.unify_complete (store := bodyResult.store)
                (left := bodyResult.ty) (right := (store.allocate k self).1)
                hbodyPost.safe hbodyPost.tyAllocated
                (Ty.allocated_mono hbodyPost.grows hselfAlloc) hmodelsExt' hunifies
            rw [hu] at hresult
            cases hresult
        | some store2 =>
            have hsucc : inferAt sig k ctx (.fix self body) store =
                some ⟨(store.allocate k self).1,
                  .fix (store.allocate k self).1 bodyResult.elaboration, store2⟩ := by
              simp only [h, hu, Option.bind]
            simp only [InferSpec, hsucc]
            have hgrowBody : (store.allocate k self).2.length ≤ bodyResult.store.length :=
              hbodyPost.grows
            have hgrow12 : (store.allocate k self).2.length ≤ store2.length :=
              le_trans hbodyPost.grows (le_of_eq (MStore.unify_length hu).symm)
            have hgrowBody2 : bodyResult.store.length ≤ store2.length :=
              le_of_eq (MStore.unify_length hu).symm
            have hselfLevBody : (store.allocate k self).1.LevelBounded bodyResult.store k :=
              Ty.levelBounded_mono hselfAlloc hselfLev hbodyPost.levels
            refine
              { safe := MStore.unify_safe hbodyPost.safe hbodyPost.tyAllocated
                  (Ty.allocated_mono hbodyPost.grows hselfAlloc) hu
                grows := by
                  show store.length ≤ store2.length
                  exact le_trans (le_trans hgrow1 hbodyPost.grows) hgrowBody2
                levels := ?_
                tyWF := hselfWF
                tyAllocated := Ty.allocated_mono hgrow12 hselfAlloc
                tyLevels := Ty.levelBounded_mono (Ty.allocated_mono hbodyPost.grows hselfAlloc)
                  hselfLevBody (fun id _ => MStore.unify_levelOf_le hu id)
                elabAllocated := ?_
                anchored := ?_
                sound := ?_
                principal := ?_ }
            · intro id hi
              exact le_trans (MStore.unify_levelOf_le hu id)
                (le_trans (hbodyPost.levels id (lt_of_lt_of_le hi hgrow1)) (hlev1 id hi))
            · intro ann hann
              simp only [Expr.anns, List.mem_cons] at hann
              rcases hann with rfl | hann
              · exact Ty.allocated_mono hgrow12 hselfAlloc
              · exact Ty.allocated_mono hgrowBody2 (hbodyPost.elabAllocated ann hann)
            · intro start level hlt hstart hanch
              have hstoreAnch : (store.allocate k self).2.Anchored start level := by
                rw [MStore.allocate_snd]
                exact MStore.Anchored.append_unsolved
                  (count := self.vars.dedup.length) (level' := k) hanch hlt
              exact MStore.unify_anchored hbodyPost.safe
                (hbodyPost.anchored start level hlt (le_trans hstart hgrow1) hstoreAnch) hu
            · intro valuation models
              obtain ⟨hmodelsBody, hunifyEq⟩ := MStore.unify_sound hu models
              obtain ⟨hmodels1, hbodyElab⟩ := hbodyPost.sound valuation hmodelsBody
              refine ⟨?_, ?_⟩
              · rw [MStore.allocate_snd] at hmodels1
                exact ((MStore.models_append_unsolved (store := store)
                  (count := self.vars.dedup.length) (level := k)).1 hmodels1).1
              · simp only [Expr.realize, Expr.mapAnn]
                have hselfRealWF : ((store.allocate k self).1.realize valuation).WF k :=
                  Ty.realize_wf_of_models hmodels1 hselfWF hselfAlloc hselfLev
                rw [hunifyEq] at hbodyElab
                exact TypingWith.fix hselfRealWF
                  (MStore.allocate_sound store k self valuation) hbodyElab
            · intro valuation models elaboration target typing
              obtain ⟨sem, bodyElab, helab, htarget, hsemwf, hsm, hbody⟩ :=
                TypingWith.fix_inv typing
              obtain ⟨ext, hmodelsExt, hagreeExt, hreal⟩ :=
                MStore.allocate_principal (store := store) (level := k) (template := self)
                  (ty := sem) pre.safe models hsm hsemwf
              have hctxeq : Ctx.realize (.mono (store.allocate k self).1 :: ctx) ext =
                  .mono sem :: ctx.realize valuation := by
                simp only [Ctx.realize_cons, Scheme.realize_mono]
                rw [hreal]
                congr 1
                exact Ctx.realize_congr
                  (fun scheme hmem id hid => pre.ctxAllocated scheme hmem id hid)
                  (fun id hi => (hagreeExt id hi).symm)
              rw [← hctxeq] at hbody
              obtain ⟨extended, hmodelsExt', hagreeExt', hbodyElabReal, hbodyTyReal⟩ :=
                hbodyPost.principal ext hmodelsExt bodyElab sem hbody
              have hself : (store.allocate k self).1.realize extended = sem := by
                rw [Ty.realize_agree hselfAlloc
                  (fun id hi => (hagreeExt' id hi).symm), hreal]
              have hunifies : bodyResult.ty.realize extended =
                  (store.allocate k self).1.realize extended := by
                rw [hbodyTyReal, hself]
              obtain ⟨result, hresult, hmodelsResult⟩ :=
                MStore.unify_complete (store := bodyResult.store)
                  (left := bodyResult.ty) (right := (store.allocate k self).1)
                  hbodyPost.safe hbodyPost.tyAllocated
                  (Ty.allocated_mono hbodyPost.grows hselfAlloc) hmodelsExt' hunifies
              have hresultEq : result = store2 := by
                rw [hu] at hresult
                exact (Option.some.inj hresult).symm
              subst hresultEq
              refine ⟨extended, hmodelsResult, ?_, ?_, ?_⟩
              · intro id hi
                exact (hagreeExt id hi).trans
                  (hagreeExt' id (lt_of_lt_of_le hi hgrow1))
              · change (Expr.fix (store.allocate k self).1
                    bodyResult.elaboration).realize extended = elaboration
                rw [helab]
                show Expr.fix ((store.allocate k self).1.realize extended)
                    (Expr.mapAnn (fun x => Ty.realize x extended) bodyResult.elaboration) =
                  Expr.fix sem bodyElab
                have hbodyMap : Expr.mapAnn (fun x => Ty.realize x extended)
                    bodyResult.elaboration = bodyElab := hbodyElabReal
                rw [hself, hbodyMap]
              · rw [htarget]
                exact hself
  · have h : inferAt sig k ctx (.fix self body) store = none := by
      rw [hbind]
      simp [hwf]
    simp only [InferSpec, h]
    intro valuation models elaboration ty typing
    obtain ⟨sem, bodyElab, _, _, hsemwf, hsm, _⟩ := TypingWith.fix_inv typing
    exact hwf (Template.Matches.wf hsm hsemwf)

/-- **The** inference theorem: induction on `src` with the lemmas above. -/
theorem inferAt_spec {sig : Signature} {k : Nat} {ctx : Ctx Nat} {src : Source} {store : MStore}
    (pre : InferPre k ctx store) : InferSpec sig k ctx src store := by
  induction src generalizing k ctx store with
  | lit literal => exact inferAt_spec_lit pre
  | primOp op => exact inferAt_spec_primOp pre
  | const c => exact inferAt_spec_const pre
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

end EPL2
