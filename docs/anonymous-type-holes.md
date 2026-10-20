# Anonymous type holes

Anonymous `_` holes are supported throughout expression annotations in the normal
parser, editor, and execution pipeline. Named holes remain a later feature.
The canonical worker has checked soundness, annotation-fidelity, principality,
and producer-completeness proofs, including recursive groups with partial signatures.
Core `Ty` and `TypeOfHM` describe completed types and expressions.

## Try it

Run [the commented playground](../scratch/anonymous-type-holes.fhm) with
`.lake/build/bin/fhm run scratch/anonymous-type-holes.fhm`, or open it in the
editor and hover its parameters and annotation holes. Its six sections mix
function heads with explicit lambdas, structured and datatype holes, patterns,
matches, partial forall signatures, and terminating mutual recursion.
[The deliberately rejected example](../scratch/anonymous-type-holes-errors.fhm)
shows that a hole still enforces the fixed parts of its annotation; change its
`True` argument to `41` to make it succeed.

## Function heads

Head parameters may be unannotated, concretely annotated, or contain holes:

```text
let add (x : Int) y : Int = x + y
let pair left right = (left, right)
let apply (fn : _ -> _) value = fn value
let keep {element} (value : element) ignored : element = value
```

A type after the parameters is the **return** type, so `add` has two `Int`
parameters and an `Int` result. Missing parameter and result annotations are
inferred. Named forall variables remain in scope through the RHS, including
nested headed bindings; unused authored binders are retained. Heads without
annotations use ordinary HM inference. Explicit lambda RHSs remain supported.

## Architecture

`InferInput` records annotation syntax before inference. Its templates
contain fixed types, independent anonymous holes, arrows, and datatype
applications. Let annotations distinguish absent, complete, monomorphic partial,
and explicitly quantified partial signatures.

The production path expands function heads with `finalizeInputAnn`
before existing input lowering. It combines parameter domains with the return
annotation and supplies holes for omitted types when a forall or return
annotation needs a full signature. Unannotated heads retain ordinary HM inference.
The legacy `SurfaceBridge.finalizeAnn` and complete-Core lowering bridge remain
for the conservative proof/demo path; their partial-head restrictions do not
specify the production frontend's head policy.

The canonical judgment is
`Infer K F frontier ctx input next subst completedExpr ty`. `K` contains frozen
variables. `F` is a list of the current type images of provisional written-forall
slots: these images remain unifiable but cannot generalize in nested bindings.
Authored free variables are scoped by `K ++ softVars F`. Sequential inference
transforms both the source annotations and `F` with the substitutions it produces.

`InferW.lean` contains the sole inference judgment and executable worker.
`inferWithTypes` returns completed Core, its type, a substitution, and editor maps
in one traversal. Completed Core uses the same engine through `InferInput.ofCore`;
there is no backend delegation or alternate inference relation.

The theory is organized in four top-level modules: `InferenceSupport.lean` for
shared substitution/unification, generalization, dependency scheduling, and Core
typing lemmas, `InferInput.lean` for
`TyTemplate`, `BindingAnn`, `InferInput`, independent `InputTyping`, and
`AnnotationCompletion`, `InferW.lean` for inference and its soundness/fidelity
proofs, and `Completeness.lean` for principality and producer completeness.
Surface normalization and lowering live in `SurfaceBridge.lean`.

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
using `SurfaceBridge.lowerProgram` followed by the same canonical inference
engine through `InferInput.ofCore`. This complete-Core lowering path has no
production caller and rejects holeful Core lowering. The CLI/editor preserve
partial annotations directly; the verified Core bridge retains its original
source-typing and safety contracts.

The production frontend lowers into `InferInput`, then uses canonical inference.
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

- [x] A single canonical elaborating judgment and worker for partial and complete inputs.
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

`FHM.Examples` exercises Core adapters, partial annotations, matches, signed lets,
and recursive elaboration.
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
  structural inference under mutable provisional annotations;
- completed annotation depths versus metadata's explicit-only binder depths.

Recursive lowering guards check true recursive input shapes and partial-forall
counts. Runtime tests pair rejection cases with nearby accepted controls; a
rejection alone does not establish correctness. Passing these tests complements
the full proof stack above. Fresh validation after inference consolidation passed:

- `lake build`: 729 jobs, including the recursive proof examples.
- `lake build FHMEditorTests fhm`: 1,639 jobs.
- `node scripts/hm-editor-smoke.mjs`: 74/74 CLI/editor semantic checks.
- `node editors/vscode/test/anonymous-holes-integration.cjs`: 11 provider
  scenarios passed using the real CLI backend and a simulated VS Code host API;
  this checks the extension's providers, not an LSP protocol or a live editor UI.
  The existing provider lifecycle test also passed.
- `node scripts/scratch-hm-audit.mjs`: 14 files, 11 accepted and three
  expected type errors; `lake env lean --run scratch/PolyRecTest.lean`: 11/11.
- The expanded playground ran to its six expected result sections; all 20
  authored hole tokens had precise, distinct source hovers, alongside checked
  headed-parameter hovers and the deliberately rejected Int/Bool example.
- `npm --prefix editors/web test`: 31/31 tests.
- `scripts/check-unverified-boundary.sh`: passed; `Core.lean` and
  `RuntimeTyping.lean` are unchanged by this feature.
- An actual-import audit of 32 inference, source/safety, and concrete-example
  capstones checked their API contracts and
  found only `propext`, `Classical.choice`, and `Quot.sound`, with no residual
  producer callbacks, `sorryAx`, or native-decision axioms. `FHM.Headlines`
  retains the public API and axiom guards in the default build.
