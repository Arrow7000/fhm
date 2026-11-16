import EPL2.Spec.Infer
import EPL2.Spec.Eval

/-!
# EPL2: the headline theorems

* `infer_eq_some_iff` / `infer_eq_none_iff`: inference accepts exactly the
  programs with a unique elaboration, and returns it.
* `infer_unique`: an accepted program has exactly one typing.
* `infer_type_safety`, `infer_run_value`: accepted programs do not get stuck.

**Proof guidance.** Everything about inference follows from `inferAt_spec`
at the empty store (`InferPre` holds by `MStore.safe_nil`), unfolding
`InferSpec` and `infer`:
* a model of the result exists (`MStore.has_model`), and a type or
  elaboration that `Ty.ground`/`Expr.traverseAnn Ty.ground` accepts realizes
  the same under every valuation (`Ty.ground_eq_some`,
  `Expr.traverseAnn_ground_eq_some`, `Ty.realize_lift`,
  `Models.realize_apply`);
* if the resolved type or an annotation of the resolved elaboration still
  has a metavariable, it is unsolved and allocated (`MStore.apply_vars_unsolved`,
  `MStore.apply_allocated`, `InferPost.tyAllocated`/`elabAllocated`), so
  `MStore.Models.exists_different` and `InferPost.sound` give two different
  elaborations (`Ty.realize_eq_vars`, `Expr.realize_eq_vars`).
The runtime theorems follow from `TypingWith.erase`,
`RuntimeTyping.preservation`/`progress` and `Eval.step?_complete`.
-/

namespace EPL2

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
