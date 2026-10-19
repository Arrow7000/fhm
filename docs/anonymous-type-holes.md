# Anonymous type holes

Anonymous `_` holes are supported throughout expression annotations in the normal
parser, editor, and execution pipeline. Named holes remain a later feature.
The canonical worker has checked soundness, annotation-fidelity, principality,
and producer-completeness proofs, including recursive groups with partial signatures.
Core `Ty` and `TypeOfHM` describe completed types and expressions.

## Try it

Run [the commented playground](../scratch/anonymous-type-holes.fhm) with
`.lake/build/bin/fhm run scratch/anonymous-type-holes.fhm`, or open it in the
editor and hover its annotation holes. It covers structured and datatype holes,
patterns, matches, partial forall signatures, and terminating mutual recursion.
[The deliberately rejected example](../scratch/anonymous-type-holes-errors.fhm)
shows that a hole still enforces the fixed parts of its annotation; change its
`True` argument to `41` to make it succeed.

## Architecture

`Elaboration.Input` records annotation syntax before inference. Its templates
contain fixed types, independent anonymous holes, arrows, and datatype
applications. Let annotations distinguish absent, complete, monomorphic partial,
and explicitly quantified partial signatures.

The canonical judgment is
`Infer K F frontier ctx input next subst completedExpr ty`. `K` contains frozen
variables. `F` is a list of the current type images of provisional written-forall
slots: these images remain unifiable but cannot generalize in nested bindings.
Authored free variables are scoped by `K ++ softVars F`. Sequential inference
transforms both the source annotations and `F` with the substitutions it produces.

`InferW` exports the worker and public API. `inferWithTypes` produces the completed
Core expression, type, substitution, and editor maps in one inference traversal.
A complete subtree can delegate to `CoreBackend` only when its authored free
variables lie in `K` and avoid `softVars F`; successful `toCore` conversion alone
is insufficient. Other subtrees use structural elaboration. There is no second
public inference path. The separate files under `Elaboration/` organize this
judgment and its proofs.

An ordinary substitution does not express the entire completion. For example,
`let id = \(x : _) -> x` needs its hole generalized into a scheme binder and its
RHS annotation closed under that binder. Inference therefore returns the
completed expression explicitly. Soundness types this output with `TypeOfHM`;
erasure proves that completion preserves the runtime term exactly.

Each inference visit allocates its own anonymous variables. Pattern compilation
preserves templates through the shared `PatComp` emitter, including copied arms.
It neither infers types nor assigns global identities to holes. Source spans
locate hovers and have no role in variable allocation or sharing.

`Headlines.elaborateSafe` is a separate complete-Core safe-lowering demonstration
using `SurfaceBridge.lowerProgram` and `CoreBackend.typecheck`. It has no production
caller and rejects holeful Core lowering. The CLI/editor use the `Input` path
above; the verified Core bridge and its safety proofs remain intact.

The production frontend lowers into `Input`, then uses canonical inference.
Runtime execution receives `completedExpr.erase`. Editor types and schemes come
from the same inference result; original input annotation modes are retained to
distinguish authored declarations from synthesized schemes. Hole hovers join
annotation tokens to their owners and existing inferred artifacts.

## Proof contracts

All canonical inference constructors, including recursive groups with partial
signatures, have checked proofs of completed Core typing (`Infer.sourceSound`),
independent partial-input typing (`Infer.inputSound`), annotation fidelity
(`Infer.completes`), and exact runtime erasure (`Infer.erase`). The `_source`
variants retain arbitrary provisional `F` and compare the transformed input.
The executable `inferWithTypes_source_sound`, `inferWithTypes_input_sound`, and
`inferWithTypes_erase` wrappers apply directly to the returned result.

The global canonical `Infer.principal` and `Infer.complete` contracts include
recursive groups. Principality protects an independent candidate scope and
factors arbitrary valid result types through an LC residual substitution.
`inferWithTypesCore_sourceComplete` covers internal transformed-source visits;
`inferCore_complete` specializes this result to the public empty provisional
context. `inferCore_accepts_iff` characterizes acceptance under admissible context
specialization, and `inferCore_empty_accepts_iff` characterizes closed inputs.
The artifact API has the corresponding `inferWithTypes_complete`,
`inferWithTypes_accepts_iff`, and `inferWithTypes_principal` guarantees.

Eligible unsolved hole variables generalize. Variables reachable through the
context, frozen variables, and live provisional slot images do not. A whole `_`
has the same independent typing meaning as an omitted lambda or ordinary-let
annotation.

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
- [x] Recursive worker with partial syntax and signatures, including SCC-wide
  constraints and complete-signature polymorphic recursion.
- [x] Recursive completed-output/input typing, annotation fidelity, and erasure.
- [x] Global recursive residual principality and producer completeness.
- [x] Full source-level regressions, normal builds, CLI/editor and web tests,
  verified-boundary and axiom audits.

## Recursive semantics

The recursive worker gives partial explicit-forall slots provisional monotypes
while solving the whole SCC. Their fixed structure constrains every
member before export; each member then retains its own written prefix and
appends inferred binders. Shared or permuted roots must not be treated as
independent rigid skolems or identified merely by ordinal position. Complete
signatures continue to permit polymorphic recursive calls; partial signatures
do not.

The canonical judgment already carries `F` alongside frozen `K`. Nested signature
escape checks protect both the outer environment and outer `F`, including roots
absent from the environment or annotation type. Checked source/output typing
and fidelity preserve these invariants through shape constraints, provisional
slot refinement, and completed exports. The principal and producer proofs
retain independent candidate scope, arbitrary candidate types and contexts,
and exact authored-prefix/output-binder distinctions. The worker follows the
canonical dependency schedule; independent typing permits arbitrary valid
residual groupings, including shared or permuted roots across stages.

## Regression coverage and completion

`FHM.Elaboration.Examples` exercises expression, match, and signed-let rules.
`FHM.Unverified.EditorSupportTests` checks source lowering, provenance, and
inferred artifacts. `scripts/hm-editor-smoke.mjs` exercises the actual canonical
recursive worker with independent runtime/editor groups, including:

- shared and permuted member prefixes, authored definition/parameter/hole names,
  unused written binders, and extra inferred binders;
- SCC-wide structural constraints and complete-versus-partial polymorphic calls;
- cross-component prefix sharing and specialization of a completed export within
  one original source cycle cut by a complete contract;
- nested signature escape and ordinary-let generalization under a vacuous outer
  forall, each paired with a nearby accepted program;
- complete annotations referring to outer provisional slots, which require
  structural inference when backend delegation is ineligible;
- completed annotation depths versus metadata's explicit-only binder depths.

Recursive lowering guards check true recursive input shapes and partial-forall
counts. Runtime tests pair rejection cases with nearby accepted controls; a
rejection alone does not establish correctness. Passing these tests complements
the full proof stack above. Final verification passed:

- `lake build`: 745 jobs, including the recursive proof examples.
- `lake build FHMEditorTests fhm`: 1,663 jobs.
- `node scripts/hm-editor-smoke.mjs`: 64/64 CLI/editor semantic checks.
- `npm --prefix editors/web test`: 31/31 tests.
- `scripts/check-unverified-boundary.sh`: passed; `Core.lean` and
  `RuntimeTyping.lean` are unchanged by this feature.
- An actual-import audit of 21 public capstones checked their API contracts and
  found only `propext`, `Classical.choice`, and `Quot.sound`, with no residual
  producer callbacks, `sorryAx`, or native-decision axioms. `FHM.Headlines`
  retains the public API and axiom guards in the default build.
