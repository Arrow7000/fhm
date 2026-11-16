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

theorem inferAt_spec_lit {sig : Signature} (pre : InferPre k ctx store) :
    InferSpec sig k ctx (.lit literal) store := by
  sorry

theorem inferAt_spec_primOp {sig : Signature} (pre : InferPre k ctx store) :
    InferSpec sig k ctx (.primOp op) store := by
  sorry

theorem inferAt_spec_const {sig : Signature} (pre : InferPre k ctx store) :
    InferSpec sig k ctx (.const c) store := by
  sorry

theorem inferAt_spec_var {sig : Signature} (pre : InferPre k ctx store) :
    InferSpec sig k ctx (.var index) store := by
  sorry

theorem inferAt_spec_lambda {sig : Signature} {body : Source}
    (bodySpec : ∀ k ctx store, InferPre k ctx store → InferSpec sig k ctx body store)
    (pre : InferPre k ctx store) :
    InferSpec sig k ctx (.lambda param body) store := by
  sorry

theorem inferAt_spec_app {sig : Signature} {function argument : Source}
    (functionSpec : ∀ k ctx store, InferPre k ctx store → InferSpec sig k ctx function store)
    (argumentSpec : ∀ k ctx store, InferPre k ctx store → InferSpec sig k ctx argument store)
    (pre : InferPre k ctx store) :
    InferSpec sig k ctx (.app function argument) store := by
  sorry

theorem inferAt_spec_letMono {sig : Signature} {rhs body : Source}
    (rhsSpec : ∀ k ctx store, InferPre k ctx store → InferSpec sig k ctx rhs store)
    (bodySpec : ∀ k ctx store, InferPre k ctx store → InferSpec sig k ctx body store)
    (pre : InferPre k ctx store) :
    InferSpec sig k ctx (.letIn none rhs body) store := by
  sorry

theorem inferAt_spec_fix {sig : Signature} {self : Template} {body : Source}
    (bodySpec : ∀ k ctx store, InferPre k ctx store → InferSpec sig k ctx body store)
    (pre : InferPre k ctx store) :
    InferSpec sig k ctx (.fix self body) store := by
  sorry

/-- **The** inference theorem: induction on `src` with the lemmas above. -/
theorem inferAt_spec {sig : Signature} {k : Nat} {ctx : Ctx Nat} {src : Source} {store : MStore}
    (pre : InferPre k ctx store) : InferSpec sig k ctx src store := by
  sorry

end EPL2
