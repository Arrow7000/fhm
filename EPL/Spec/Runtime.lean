import EPL.Spec.Syntax
import EPL.Runtime

/-!
# Runtime metatheory

Type safety rests on four lemmas about `RuntimeTyping`:

* `mono_depth`: more rigid levels in scope — trivial thanks to the Kripke
  `letIn` rule;
* `weaken` / `subst`: the term-level lemmas for `beta`, `letValue` and
  `fixUnfold`;
* `substRigids`: the one type-substitution lemma, used only by erasure.
-/

namespace EPL

theorem DataDecl.WF.ctorScheme_wf {decl : DataDecl} (wf : decl.WF) {fields : List SemTy}
    (mem : fields ∈ decl.ctors) (type : Nat) : (decl.ctorScheme type fields).WF 0 := by
  sorry

/-- Every constructor scheme a signature assigns is closed. -/
theorem Signature.ctorScheme_wf {sig : Signature} {ref : CtorRef} {scheme : Scheme Empty}
    (found : sig.ctorScheme ref = some scheme) : scheme.WF 0 := by
  sorry

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
primitive operator possibly applied to one literal, or a constructor spine
short of its fields) and at data types (a constructor spine with all its
fields, whose constructor the exhaustive match has a branch for). -/
theorem progress (typing : RuntimeTyping sig k [] expr ty) (exhaustive : Exhaustive sig expr) :
    Eval.Value expr ∨ ∃ next, Eval.Step expr next := by
  sorry

/-- Proof: induction on the step. `beta`, `fixUnfold`: `subst` with
`inner := []` and `mono_depth`; `letValue`: `subst` with the `letIn` premise;
`matchCtor`: the scrutinee's constructor scheme gives its fields the types
the branch expects (a lemma about typing `Expr.apps` spines helps). -/
theorem preservation (typing : RuntimeTyping sig k ctx expr ty)
    (step : Eval.Step expr next) :
    RuntimeTyping sig k ctx next ty := by
  sorry

end RuntimeTyping

end EPL
