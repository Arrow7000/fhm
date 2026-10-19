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

Lambda, application, ordinary let, nonrecursive explicit signatures (including
partial `forall` and complete signatures with partial RHSs or continuations),
and named/wildcard match inference have checked proofs of:

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

Completed partial signatures preserve the authored forall prefix in its exact
order, including unused binders, and append newly generalized hole variables.
Editor definition hovers, hole hovers, and runtime binding reports preserve
these names.

These principal-type results concern the result type and flexible context.
They do not claim a universal most-general filling for every unused annotation.

## Completion checklist

- [x] Canonical elaborating judgment and worker, internal complete-Core backend.
- [x] Annotation lowering through shared pattern emission, with erasure proofs.
- [x] Parser spans, completed-expression runtime handoff, basic hole hovers.
- [x] Match inference and its complete soundness/principality/completeness stack.
- [x] Nonrecursive explicit signatures with partial RHSs or continuations;
  partial `forall`, including soundness, principality, and completeness.
- [ ] Recursive groups with partial syntax and signatures. Partial signatures
  must constrain the entire monomorphic SCC before export and must not grant
  polymorphic recursive calls. Complete signatures retain existing polyrec.
- [ ] Full source-level regressions, normal builds, CLI/editor and web tests,
  verified-boundary and axiom audits.

## Remaining recursive work

The reviewed recursive design gives partial explicit-forall slots provisional
monotypes while solving the whole SCC. Their fixed structure constrains every
member before export; each member then retains its own written prefix and
appends inferred binders. Shared or permuted roots must not be treated as
independent rigid skolems or identified merely by ordinal position. Complete
signatures continue to permit polymorphic recursive calls; partial signatures
do not.

The proposed recursive extension carries `F`, the current type images of live
provisional slots, alongside frozen `K`. These images participate in scope and
are excluded from nested generalization, while unification may refine them.
Nested signature escape checks must protect both the outer environment and
outer `F`, including roots absent from the environment or annotation type.
This extension is work in progress; the committed canonical judgment above
still has no `F` index.

## Regression coverage and completion

`FHM.Elaboration.Examples` exercises the proved expression, match, and signed-let
rules. `FHM.Unverified.EditorSupportTests` checks source lowering, provenance,
and available inferred artifacts. `scripts/hm-editor-smoke.mjs` keeps independent
runtime/editor targets for the remaining recursive cases, including:

- shared and permuted member prefixes, authored definition/parameter/hole names,
  unused written binders, and extra inferred binders;
- SCC-wide structural constraints and complete-versus-partial polymorphic calls;
- nested signature escape and ordinary-let generalization under a vacuous outer
  forall, each paired with a nearby accepted program;
- complete annotations referring to outer provisional slots, which require
  structural inference when backend delegation is ineligible;
- completed annotation depths versus metadata's explicit-only binder depths.

Recursive lowering guards already check the intended input shapes; pending
runtime positives remain intentionally red until the canonical worker supports
them. A rejection without its accepted control does not establish correctness.
The feature is complete only when all supported annotation syntax, including
recursive groups, has the full proof stack above and the retained source,
CLI/editor, web, normal-build, verified-boundary, and axiom checks pass.
