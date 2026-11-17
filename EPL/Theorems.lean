import EPL.Spec.Infer
import EPL.Spec.Eval

/-!
# EPL: the headline theorems

* `infer_eq_some_iff` / `infer_eq_none_iff`: inference accepts exactly the
  programs that elaborate and have no other typing, and returns that typing.
* `infer_unique`: an accepted program has exactly one typing.
* `infer_type_safety`, `infer_run_value`: accepted programs do not get stuck.
* `evaluate`: infer, erase and run, returning a typed value or a typed term
  that can still step.

**Proof outline.** Everything about inference follows from `inferAt_spec`
at the empty store (`InferPre` holds by `MStore.safe_nil`), unfolding
`InferSpec` and `infer`:
* a model of the result exists (`MStore.has_model`), and a type or
  elaboration that `Ty.ground`/`Expr.traverseAnn Ty.ground` accepts realizes
  the same under every valuation (`Ty.ground_eq_some`,
  `Expr.traverseAnn_ground_eq_some`, `Ty.realize_lift`,
  `Models.realize_apply`);
* if the resolved type or an annotation of the resolved elaboration still
  has a metavariable, it is unsolved (`MStore.apply_vars_unsolved`), so
  `MStore.Models.exists_different` and `InferPost.sound` give two different
  elaborations (`Ty.realize_eq_vars`, `Expr.realize_eq_vars`).
The runtime theorems follow from `TypingWith.erase`,
`RuntimeTyping.preservation`/`progress` and `Eval.step?_complete`.
-/

namespace EPL

/-! ## Mapping the annotations of an expression -/

private theorem Expr.mapAnn_mapAnn {A B C : Type} (f : A → B) (g : B → C) (expr : Expr A) :
    (expr.mapAnn f).mapAnn g = expr.mapAnn fun a => g (f a) := by
  induction expr with
  | lit _ | primOp _ | const _ | var _ => rfl
  | lambda param body ih =>
      simp only [Expr.mapAnn, ih]
      cases param <;> rfl
  | app function argument ihFunction ihArgument =>
      simp only [Expr.mapAnn, ihFunction, ihArgument]
  | letIn ann rhs body ihRhs ihBody =>
      simp only [Expr.mapAnn, ihRhs, ihBody]
      cases ann with
      | none => rfl
      | some ann => cases ann; rfl
  | fix self body ih =>
      cases self <;> simp [Expr.mapAnn, ih]

private theorem Expr.mapAnn_id {A : Type} (expr : Expr A) : expr.mapAnn (fun a => a) = expr := by
  induction expr with
  | lit _ | primOp _ | const _ | var _ => rfl
  | lambda param body ih =>
      simp only [Expr.mapAnn, ih]
      cases param <;> rfl
  | app function argument ihFunction ihArgument =>
      simp only [Expr.mapAnn, ihFunction, ihArgument]
  | letIn ann rhs body ihRhs ihBody =>
      simp only [Expr.mapAnn, ihRhs, ihBody]
      cases ann with
      | none => rfl
      | some ann => cases ann; rfl
  | fix self body ih =>
      cases self <;> simp [Expr.mapAnn, ih]

/-- Resolving an elaboration's annotations does not change its realization. -/
private theorem Expr.realize_applyElab {store : MStore} {valuation : Valuation}
    (models : store.Models valuation) (expr : Expr InfTy) :
    (store.applyElab expr).realize valuation = expr.realize valuation := by
  unfold MStore.applyElab Expr.realize
  rw [Expr.mapAnn_mapAnn]
  exact Expr.mapAnn_congr fun ann _ => MStore.Models.realize_apply models ann

/-- A ground type realizes to its ground value under every model. -/
private theorem Ty.realize_of_ground {store : MStore} {valuation : Valuation} {ty : InfTy} {sem : SemTy}
    (models : store.Models valuation) (ground : (store.apply ty).ground = some sem) :
    ty.realize valuation = sem := by
  have h : store.apply ty = sem.lift := Ty.ground_eq_some.mp ground
  calc ty.realize valuation = (store.apply ty).realize valuation :=
        (MStore.Models.realize_apply models ty).symm
    _ = (sem.lift : InfTy).realize valuation := by rw [h]
    _ = sem := Ty.realize_lift sem valuation

/-- A ground elaboration realizes to its ground value under every model. -/
private theorem Expr.realize_of_traverseAnn_ground {store : MStore} {valuation : Valuation}
    {expr : Expr InfTy} {elaboration : Elab}
    (models : store.Models valuation)
    (ground : (store.applyElab expr).traverseAnn Ty.ground = some elaboration) :
    expr.realize valuation = elaboration := by
  have h : store.applyElab expr = elaboration.mapAnn Ty.lift :=
    Expr.traverseAnn_ground_eq_some.mp ground
  have hself : (elaboration.mapAnn Ty.lift).realize valuation = elaboration := by
    unfold Expr.realize
    rw [Expr.mapAnn_mapAnn]
    simp only [Ty.realize_lift, Expr.mapAnn_id]
  calc expr.realize valuation = (store.applyElab expr).realize valuation :=
        (Expr.realize_applyElab models expr).symm
    _ = (elaboration.mapAnn Ty.lift).realize valuation := by rw [h]
    _ = elaboration := hself

/-- A ground result realizes to itself under any model. -/
private theorem realize_ground {internal : Inferred} {ty : SemTy} {elaboration : Elab}
    {valuation : Valuation} (models : internal.store.Models valuation)
    (ground : (internal.store.apply internal.ty).ground = some ty)
    (traverse : (internal.store.applyElab internal.elaboration).traverseAnn Ty.ground =
      some elaboration) :
    internal.ty.realize valuation = ty ∧
      internal.elaboration.realize valuation = elaboration :=
  ⟨Ty.realize_of_ground models ground, Expr.realize_of_traverseAnn_ground models traverse⟩

/-! ## Unfolding `infer` -/

/-- The public entry point, unfolded. -/
private theorem infer_unfold {sig : Signature} {src : Source} {result : InferenceResult} :
    infer sig src = some result ↔
      ∃ internal : Inferred,
        inferAt sig 0 [] src [] = some internal ∧
          (internal.store.apply internal.ty).ground = some result.ty ∧
          (internal.store.applyElab internal.elaboration).traverseAnn Ty.ground =
            some result.elaboration := by
  unfold infer
  cases h : inferAt sig 0 [] src [] with
  | none => simp
  | some internal =>
      simp only [Bind.bind, Option.bind]
      cases hty : (internal.store.apply internal.ty).ground with
      | none => simp [hty]
      | some ty =>
          cases helab : (internal.store.applyElab internal.elaboration).traverseAnn Ty.ground with
          | none => simp [helab]
          | some elaboration =>
              simp only [Option.some.injEq]
              constructor
              · rintro rfl
                refine ⟨internal, rfl, ?_, ?_⟩
                · rw [hty]
                · rw [helab]
              · rintro ⟨internal', hinternal, htyEq, helabEq⟩
                subst hinternal
                have tyEq : ty = result.ty := Option.some.inj (hty.symm.trans htyEq)
                have elaborationEq : elaboration = result.elaboration :=
                  Option.some.inj (helab.symm.trans helabEq)
                rw [tyEq, elaborationEq]

/-! ## The empty starting invariants -/

private theorem inferPre_nil : InferPre 0 ([] : Ctx Nat) ([] : MStore) where
  safe := MStore.safe_nil
  ctxWF := by simp
  ctxAllocated := by simp
  ctxLevels := by simp

/-- The invariant guaranteed by a successful run of `inferAt`. -/
private theorem inferPost_of_run {sig : Signature} {k : Nat} {ctx : Ctx Nat} {src : Source}
    {store : MStore} {result : Inferred} (pre : InferPre k ctx store)
    (run : inferAt sig k ctx src store = some result) :
    InferPost sig k ctx src store result := by
  have h := inferAt_spec (sig := sig) (src := src) pre
  simpa only [InferSpec, run] using h

/-! ## Failure of the final resolution -/

/-- An unsolved metavariable of a resolved annotation yields two models that
disagree on it, together with their elaborations. -/
private theorem models_of_unsolved {sig : Signature} {src : Source} {internal : Inferred}
    (post : InferPost sig 0 ([] : Ctx Nat) src ([] : MStore) internal)
    {ty : InfTy} {id : Nat} (hid : id ∈ (internal.store.apply ty).vars) :
    ∃ first second : Valuation,
      internal.store.Models first ∧ internal.store.Models second ∧ second id ≠ first id ∧
      Elaborates sig 0 [] src (internal.elaboration.realize first)
        (internal.ty.realize first) ∧
      Elaborates sig 0 [] src (internal.elaboration.realize second)
        (internal.ty.realize second) := by
  have hunsolved : internal.store.lookup id = none :=
    MStore.apply_vars_unsolved post.safe id hid
  obtain ⟨first, firstModels⟩ := MStore.has_model post.safe
  obtain ⟨second, secondModels, different, _⟩ :=
    MStore.Models.exists_different post.safe firstModels hunsolved
  exact ⟨first, second, firstModels, secondModels, different,
    (post.sound first firstModels).2, (post.sound second secondModels).2⟩

/-- If the resolved type still has a metavariable, acceptance contradicts
uniqueness. -/
private theorem false_of_ty_ground_none {sig : Signature} {src : Source} {internal : Inferred}
    {elaboration : Elab} {ty : SemTy}
    (post : InferPost sig 0 ([] : Ctx Nat) src ([] : MStore) internal)
    (bad : (internal.store.apply internal.ty).ground = none)
    (unique : ∀ elaboration' ty', Elaborates sig 0 [] src elaboration' ty' →
      elaboration' = elaboration ∧ ty' = ty) : False := by
  obtain ⟨id, hid⟩ := List.exists_mem_of_ne_nil _ (Ty.ground_eq_none.mp bad)
  obtain ⟨first, second, firstModels, secondModels, different, firstElaborates,
    secondElaborates⟩ := models_of_unsolved post hid
  have realizeEq : (internal.store.apply internal.ty).realize first =
      (internal.store.apply internal.ty).realize second := by
    rw [MStore.Models.realize_apply firstModels, MStore.Models.realize_apply secondModels,
      (unique _ _ firstElaborates).2, (unique _ _ secondElaborates).2]
  exact different ((Ty.realize_eq_vars realizeEq) id hid).symm

/-- If a resolved annotation still has a metavariable, acceptance contradicts
uniqueness. -/
private theorem false_of_elab_ground_none {sig : Signature} {src : Source} {internal : Inferred}
    {elaboration : Elab} {ty : SemTy}
    (post : InferPost sig 0 ([] : Ctx Nat) src ([] : MStore) internal)
    (bad : (internal.store.applyElab internal.elaboration).traverseAnn Ty.ground = none)
    (unique : ∀ elaboration' ty', Elaborates sig 0 [] src elaboration' ty' →
      elaboration' = elaboration ∧ ty' = ty) : False := by
  obtain ⟨annotation, hannotation, hne⟩ := Expr.traverseAnn_ground_eq_none.mp bad
  obtain ⟨original, horiginal, rfl⟩ : ∃ original ∈ internal.elaboration.anns,
      internal.store.apply original = annotation := by
    rw [MStore.applyElab, Expr.anns_mapAnn] at hannotation
    exact List.mem_map.mp hannotation
  obtain ⟨id, hid⟩ := List.exists_mem_of_ne_nil _ hne
  obtain ⟨first, second, firstModels, secondModels, different, firstElaborates,
    secondElaborates⟩ := models_of_unsolved post hid
  have realizeEq : (internal.store.applyElab internal.elaboration).realize first =
      (internal.store.applyElab internal.elaboration).realize second := by
    rw [Expr.realize_applyElab firstModels, Expr.realize_applyElab secondModels,
      (unique _ _ firstElaborates).1, (unique _ _ secondElaborates).1]
  exact different
    ((Expr.realize_eq_vars realizeEq) (internal.store.apply original) hannotation id hid).symm

/-! ## The public entry point -/

theorem infer_sound {sig : Signature} {src : Source} {result : InferenceResult}
    (accepted : infer sig src = some result) :
    Elaborates sig 0 [] src result.elaboration result.ty := by
  obtain ⟨internal, run, ground, traverse⟩ := infer_unfold.mp accepted
  have post := inferPost_of_run inferPre_nil run
  obtain ⟨valuation, models⟩ := MStore.has_model post.safe
  obtain ⟨-, elaborates⟩ := post.sound valuation models
  obtain ⟨hty, helaboration⟩ := realize_ground models ground traverse
  simpa only [Ctx.realize, List.map_nil, hty, helaboration] using elaborates

/-- An accepted program is typed at the inferred elaboration and type. -/
theorem infer_typing {sig : Signature} {src : Source} {result : InferenceResult}
    (accepted : infer sig src = some result) :
    Typing sig 0 [] src result.elaboration result.ty :=
  (infer_sound accepted).typing

/-- The empty context is well formed at any depth. -/
private theorem ctxWF_nil {k : Nat} : Ctx.WF k ([] : Ctx Empty) := by
  intro scheme hmem
  simp at hmem

/-- The inferred type is closed. -/
theorem infer_ty_wf {sig : Signature} {src : Source} {result : InferenceResult}
    (accepted : infer sig src = some result) : result.ty.WF 0 :=
  TypingWith.regular ctxWF_nil (infer_sound accepted)

/-- An accepted program has exactly one typing: its elaboration and type are
the inferred ones. -/
theorem infer_unique {sig : Signature} {src : Source} {result : InferenceResult}
    (accepted : infer sig src = some result)
    (typing : Typing sig 0 [] src elaboration ty) :
    elaboration = result.elaboration ∧ ty = result.ty := by
  obtain ⟨internal, run, ground, traverse⟩ := infer_unfold.mp accepted
  have post := inferPost_of_run inferPre_nil run
  obtain ⟨valuation, models⟩ := MStore.has_model MStore.safe_nil
  obtain ⟨extended, extendedModels, -, helaboration, hty⟩ :=
    post.principal valuation models elaboration ty typing
  obtain ⟨hground, hgroundElab⟩ := realize_ground extendedModels ground traverse
  exact ⟨helaboration.symm.trans hgroundElab, hty.symm.trans hground⟩

/-- **Soundness and completeness.** `infer` accepts exactly the programs that
elaborate and have no other typing, and returns that typing. (Uniqueness among
elaborations alone is equivalent, by this theorem.) Proof of `←`:
`inferAt_spec` cannot fail (its failure case contradicts the elaboration); if
the result's type or elaboration kept an unsolved metavariable,
`Models.exists_different` and soundness would give a second elaboration. -/
theorem infer_eq_some_iff {sig : Signature} {src : Source} {result : InferenceResult} :
    infer sig src = some result ↔
      Elaborates sig 0 [] src result.elaboration result.ty ∧
        ∀ elaboration ty, Typing sig 0 [] src elaboration ty →
          elaboration = result.elaboration ∧ ty = result.ty := by
  constructor
  · intro accepted
    exact ⟨infer_sound accepted, fun _ _ typing => infer_unique accepted typing⟩
  · rintro ⟨sound, uniqueTyping⟩
    have unique : ∀ elaboration ty, Elaborates sig 0 [] src elaboration ty →
        elaboration = result.elaboration ∧ ty = result.ty :=
      fun elaboration ty elaborates => uniqueTyping elaboration ty elaborates.typing
    cases run : inferAt sig 0 [] src [] with
    | none =>
        have hspec := inferAt_spec (sig := sig) (src := src) inferPre_nil
        have hnone : ∀ valuation, MStore.Models ([] : MStore) valuation →
            ∀ elaboration ty, ¬ Elaborates sig 0 [] src elaboration ty := by
          simpa only [InferSpec, run, Ctx.realize, List.map_nil] using hspec
        obtain ⟨valuation, models⟩ := MStore.has_model MStore.safe_nil
        exact absurd sound (hnone valuation models result.elaboration result.ty)
    | some internal =>
        have post := inferPost_of_run inferPre_nil run
        cases ground : (internal.store.apply internal.ty).ground with
        | none =>
            exact (false_of_ty_ground_none post ground unique).elim
        | some ty =>
            cases traverse : (internal.store.applyElab internal.elaboration).traverseAnn
                Ty.ground with
            | none =>
                exact (false_of_elab_ground_none post traverse unique).elim
            | some elaboration =>
                have accepted : infer sig src = some ⟨elaboration, ty⟩ :=
                  infer_unfold.mpr ⟨internal, run, ground, traverse⟩
                obtain ⟨valuation, models⟩ := MStore.has_model MStore.safe_nil
                obtain ⟨extended, extendedModels, -, helaboration, hty⟩ :=
                  post.principal valuation models result.elaboration result.ty
                    (Elaborates.typing sound)
                obtain ⟨hground, hgroundElab⟩ := realize_ground extendedModels ground traverse
                have tyEq : ty = result.ty := hground.symm.trans hty
                have elaborationEq : elaboration = result.elaboration :=
                  hgroundElab.symm.trans helaboration
                simpa [tyEq, elaborationEq] using accepted

theorem infer_eq_none_iff {sig : Signature} {src : Source} :
    infer sig src = none ↔
      ¬ ∃ elaboration ty, Elaborates sig 0 [] src elaboration ty ∧
        ∀ elaboration' ty', Typing sig 0 [] src elaboration' ty' →
          elaboration' = elaboration ∧ ty' = ty := by
  constructor
  · rintro noneRun ⟨elaboration, ty, elaborates, unique⟩
    have accepted : infer sig src = some ⟨elaboration, ty⟩ :=
      infer_eq_some_iff.mpr ⟨elaborates, unique⟩
    rw [accepted] at noneRun
    exact Option.noConfusion noneRun
  · intro notExists
    cases run : infer sig src with
    | none => rfl
    | some result =>
        have data := infer_eq_some_iff.mp run
        exact absurd ⟨result.elaboration, result.ty, data.1, data.2⟩ notExists

/-! ## Accepted programs run safely -/

theorem infer_runtimeTyping {sig : Signature} {src : Source} {result : InferenceResult}
    (accepted : infer sig src = some result) :
    RuntimeTyping sig 0 [] src.erase result.ty :=
  TypingWith.erase ctxWF_nil (infer_sound accepted)

theorem infer_steps_typed {sig : Signature} {src : Source} {result : InferenceResult}
    (accepted : infer sig src = some result) (steps : Eval.Steps sig src.erase expr) :
    RuntimeTyping sig 0 [] expr result.ty := by
  induction steps with
  | refl => exact infer_runtimeTyping accepted
  | tail _ step ih => exact RuntimeTyping.preservation ih step

/-- Type safety: an accepted program never gets stuck. -/
theorem infer_type_safety {sig : Signature} {src : Source} {result : InferenceResult}
    (accepted : infer sig src = some result) (steps : Eval.Steps sig src.erase expr) :
    Eval.Value sig expr ∨ ∃ next, Eval.Step sig expr next :=
  RuntimeTyping.progress (infer_steps_typed accepted steps)

/-- Running an accepted program, for any fuel, yields a term of the inferred
type. -/
theorem infer_run_typed {sig : Signature} {src : Source} {result : InferenceResult}
    (accepted : infer sig src = some result) (fuel : Nat) :
    RuntimeTyping sig 0 [] (Eval.run sig fuel src.erase) result.ty :=
  infer_steps_typed accepted (Eval.run_steps fuel src.erase)

/-- When the evaluator stops before its fuel runs out, it stops at a value. -/
theorem infer_run_value {sig : Signature} {src : Source} {result : InferenceResult}
    (accepted : infer sig src = some result)
    (stopped : Eval.step? sig (Eval.run sig fuel src.erase) = none) :
    Eval.Value sig (Eval.run sig fuel src.erase) := by
  rcases RuntimeTyping.progress (infer_run_typed accepted fuel) with value | ⟨next, step⟩
  · exact value
  · rw [Eval.step?_complete step] at stopped
    exact Option.noConfusion stopped

/-! ## A proof-carrying pipeline -/

/-- The result of running a closed program of type `ty` from `start` with
bounded fuel, carrying its own evidence. -/
inductive Eval.Outcome (sig : Signature) (start : RuntimeExpr) (ty : SemTy) : Type
  /-- Evaluation finished at a value. -/
  | value (result : RuntimeExpr)
      (steps : Eval.Steps sig start result)
      (isValue : Eval.Value sig result)
      (typed : RuntimeTyping sig 0 [] result ty)
  /-- Fuel ran out at a typed term that can still step. -/
  | running (current next : RuntimeExpr)
      (steps : Eval.Steps sig start current)
      (typed : RuntimeTyping sig 0 [] current ty)
      (step : Eval.Step sig current next)

/-- The final value, or `none` if fuel ran out. -/
def Eval.Outcome.value? : Eval.Outcome sig start ty → Option RuntimeExpr
  | .value result .. => some result
  | .running .. => none

/-- Infer `src`, then run its erasure for at most `fuel` steps. Rejected
programs yield `none`; accepted programs cannot get stuck, by construction of
`Eval.Outcome`. -/
def evaluate (sig : Signature) (src : Source) (fuel : Nat) :
    Option ((result : InferenceResult) × Eval.Outcome sig src.erase result.ty) :=
  match accepted : infer sig src with
  | none => none
  | some result =>
      some ⟨result,
        match stepped : Eval.step? sig (Eval.run sig fuel src.erase) with
        | some next =>
            .running _ next (Eval.run_steps fuel _) (infer_run_typed accepted fuel)
              (Eval.step?_sound stepped)
        | none =>
            .value _ (Eval.run_steps fuel _) (infer_run_value accepted stepped)
              (infer_run_typed accepted fuel)⟩

/-! ## Axioms

The build fails if a headline theorem comes to depend on anything but Lean's
three standard axioms. -/

/-- info: 'EPL.infer_eq_some_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms infer_eq_some_iff

/-- info: 'EPL.infer_eq_none_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms infer_eq_none_iff

/-- info: 'EPL.infer_unique' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms infer_unique

/-- info: 'EPL.infer_type_safety' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms infer_type_safety

/-- info: 'EPL.evaluate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms evaluate

end EPL
