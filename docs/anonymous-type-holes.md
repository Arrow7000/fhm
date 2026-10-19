# Anonymous type holes

The target is anonymous `_` holes throughout expression annotations in the normal
parser, editor, and execution pipeline. Named holes remain a later feature.
Core `Ty` and `TypeOfHM` describe completed types and expressions.

## Architecture

`Elaboration.Input` records annotation syntax before inference. Its templates
contain fixed types, independent anonymous holes, arrows, and datatype
applications. Let annotations distinguish absent, complete, monomorphic partial,
and explicitly quantified partial signatures.

The canonical judgment is
`Infer K frontier ctx input next subst completedExpr ty`. `InferW` exports its
worker and public API. `inferWithTypes` produces the completed Core expression,
type, substitution, and editor maps in one inference traversal. A complete
subtree can delegate to `CoreBackend`; there is no second public inference path.
The separate files under `Elaboration/` organize this judgment and its proofs.

An ordinary substitution does not express the entire completion. For example,
`let id = \(x : _) -> x` needs its hole generalized into a scheme binder and its
RHS annotation closed under that binder. Inference therefore returns the
completed expression explicitly. Soundness types this output with `TypeOfHM`;
erasure proves that completion preserves the runtime term exactly.

Each inference visit allocates its own anonymous variables. Pattern compilation
preserves templates through the shared `PatComp` emitter, including copied arms.
It neither infers types nor assigns global identities to holes. Source spans
locate hovers and have no role in variable allocation or sharing.

The production frontend lowers into `Input`, then uses canonical inference.
Runtime execution receives `completedExpr.erase`. Editor types and schemes come
from the same inference result; original input annotation modes are retained to
distinguish authored declarations from synthesized schemes. Hole hovers join
annotation tokens to their owners and existing inferred artifacts.

## Proof contracts

Lambda, application, ordinary let, and named/wildcard match inference have
checked proofs of:

- completed Core typing (`Infer.sourceSound`), runtime erasure (`Infer.erase`),
  and annotation fidelity (`Infer.completes`);
- independent partial-input typing (`Infer.inputSound`);
- residual result/context principality against independently quantified protected
  sets (`Infer.principal`);
- executable completeness and exact closed-input acceptance
  (`inferCore_complete`, `inferCore_empty_accepts_iff`).

Eligible unsolved hole variables generalize. Variables reachable through the
context and written rigid variables do not. A whole `_` has the same independent
typing meaning as an omitted lambda or ordinary-let annotation.

These principal-type results concern the result type and flexible context.
They do not claim a universal most-general filling for every unused annotation.

## Completion checklist

- [x] Canonical elaborating judgment and worker, internal complete-Core backend.
- [x] Annotation lowering through shared pattern emission, with erasure proofs.
- [x] Parser spans, completed-expression runtime handoff, basic hole hovers.
- [x] Match inference and its complete soundness/principality/completeness stack.
- [ ] Explicit signatures with partial RHSs or continuations; partial `forall`.
- [ ] Recursive groups with partial syntax and signatures. Partial signatures
  must constrain the entire monomorphic SCC before export and must not grant
  polymorphic recursive calls. Complete signatures retain existing polyrec.
- [ ] Full source-level regressions, normal builds, CLI/editor and web tests,
  verified-boundary and axiom audits.

`FHM.Elaboration.Examples` exercises the proved expression and match rules. Editor canaries live
in `FHM.Unverified.EditorSupportTests`; `scripts/hm-editor-smoke.mjs` includes
end-to-end acceptance targets for the remaining constructs. Some targets remain
intentionally red during this WIP extension; this checklist is the feature's
completion criterion.
