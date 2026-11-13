import EPL2.Spec.Syntax
import EPL2.Runtime

/-!
# Runtime metatheory and the evaluator

Type safety rests on four lemmas about `RuntimeTyping`:

* `mono_depth`: more rigid levels in scope — trivial thanks to the Kripke
  `letIn` rule;
* `weaken` / `subst`: the term-level lemmas for `beta`, `letValue` and
  `fixUnfold`;
* `substRigids`: the one type-substitution lemma, used only by erasure.
-/

namespace EPL2
namespace RuntimeTyping

theorem regular (ctxWF : ctx.WF k) (typing : RuntimeTyping sig k ctx expr ty) : ty.WF k := by
  sorry

/-- Proof: induction; the `letIn` premise already quantifies over all larger
depths. -/
theorem mono_depth (typing : RuntimeTyping sig k ctx expr ty) (le : k ≤ k') :
    RuntimeTyping sig k' ctx expr ty := by
  sorry

/-- Term weakening: insert `extra` below the innermost `inner.length` binders. -/
theorem weaken (typing : RuntimeTyping sig k (inner ++ ctx) expr ty) (extra : Ctx Empty) :
    RuntimeTyping sig k (inner ++ extra ++ ctx) (expr.shift inner.length extra.length) ty := by
  sorry

/-- Substitute a value for the variable bound to `scheme`, given that the value
has every instance of the scheme at every larger depth (which is exactly what
the `letIn` rule provides, and what `mono_depth` provides for a monomorphic
binder). Proof: induction on `typing`, generalizing `inner` and `k`; the
variable case uses `weaken` with `inner := []`. -/
theorem subst (typing : RuntimeTyping sig k (inner ++ scheme :: ctx) expr ty)
    (value : ∀ k', k ≤ k' → ∀ ty', scheme.Instance k' ty' → RuntimeTyping sig k' ctx v ty') :
    RuntimeTyping sig k (inner ++ ctx) (expr.substAt inner.length v) ty := by
  sorry

/-- Type substitution: replace the rigid levels below `k` by types
well-formed at `k'`. Proof: induction on `typing`, generalizing `k'` and `f`.
In the `letIn` case, prove the premise at depth `k'' ≥ k'` for the instance
`(scheme.substRigids f).inst args` by applying the induction hypothesis to the
generic instance `scheme.skolemize k` (at depth `k + arity`) with the
substitution `fun l => if l < k then f l else args.getD (l - k) (.rigid l)`;
`ctxWF` makes it act on the context as `f` does. -/
theorem substRigids (ctxWF : ctx.WF k) (typing : RuntimeTyping sig k ctx expr ty)
    (f : Nat → SemTy) (images : ∀ l < k, (f l).WF k') :
    RuntimeTyping sig k' (ctx.map (Scheme.substRigids f)) expr (ty.substRigids f) := by
  sorry

/-- Proof: induction; canonical forms of values at arrow types (a lambda, a
primitive operator possibly applied to one literal, or a partial constant
spine) and at data types (a saturated constructor spine). -/
theorem progress (typing : RuntimeTyping sig k [] expr ty) :
    Eval.Value sig expr ∨ ∃ next, Eval.Step sig expr next := by
  sorry

/-- Proof: induction on the step. `beta`, `fixUnfold`: `subst` with
`inner := []` and `mono_depth`; `letValue`: `subst` with the `letIn` premise;
`const`: the eliminator's scheme types the chosen branch at the scrutinee's
field types (a lemma about typing `Expr.apps` spines helps). -/
theorem preservation (typing : RuntimeTyping sig k ctx expr ty)
    (step : Eval.Step sig expr next) :
    RuntimeTyping sig k ctx next ty := by
  sorry

end RuntimeTyping

namespace Eval

theorem isValue_iff : isValue sig expr = true ↔ Value sig expr := by
  sorry

theorem Value.irreducible (value : Value sig expr) : ¬ Step sig expr next := by
  sorry

theorem step?_sound (found : step? sig expr = some next) : Step sig expr next := by
  sorry

theorem step?_complete (step : Step sig expr next) : step? sig expr = some next := by
  sorry

theorem Step.deterministic (first : Step sig expr a) (second : Step sig expr b) : a = b := by
  sorry

theorem run_steps (fuel : Nat) (expr : RuntimeExpr) : Steps sig expr (run sig fuel expr) := by
  sorry

/-- Every terminating execution is found by `run` with enough fuel. -/
theorem run_complete (steps : Steps sig expr result) (value : Value sig result) :
    ∃ fuel, run sig fuel expr = result := by
  sorry

end Eval
end EPL2
