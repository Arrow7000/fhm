# Plan: return FHM to an erased Hindley--Milner language

**Status:** implemented, 2026-09-29

**Branch:** `hm-reset-investigation`

**Historical reference:** `b016fcf` (last source-complete pre-type-passing HM checkpoint),
plus the intended cleanup at `be9cc14`

**Implementation base:** current `dm-erased` descendant, not `be9cc14`

## Decision

Keep the current repository history and subtract the bounds language from the current
erased Damas--Milner stack. Do **not** reset the implementation to `be9cc14`.

`b016fcf`/`be9cc14` are the right semantic and architectural reference for the
intended core:

- one erased operational semantics;
- one declarative HM typing relation;
- Algorithm W with soundness, completeness, and principality;
- scoped type variables in ordinary annotations;
- mutually recursive groups checked at shared monotypes;
- group members generalized only for the body, so later uses may be polymorphic;
- no term-level type passing and no executable elaboratum.

It is not the right repository base. Reverting to it would throw away valuable later
work that is independent of bounds: the real surface parser and lowering relation,
datatype declarations, verified SCC analysis, verified pattern compilation and
coverage, primitive operations, the CLI/editor pipeline, source provenance,
expression-level type hover, and the later erased progress/preservation/completeness
tower.

The current tree already implements the desired recursive-language boundary. Its
problem is not its runtime or its live recursive inference policy; its problem is that
the bounds experiment is embedded in the shared type grammar and therefore infects
the statements and proofs of otherwise ordinary HM results.

## Language contract after the reset

1. Types are ordinary rank-1 HM types: variables, arrows, primitive types, and
   applications of nominal datatype constructors. There is no `BL`, count kind,
   count binder, interval, subtyping, join/meet, or bounds-specific equality.
2. Ordinary non-recursive `let` generalizes in the standard way.
3. For each recursive SCC, allocate one monotype per member; check every RHS with all
   members available only at those monotypes; solve the group; then generalize the
   solved member types for the body and for subsequent SCCs.
4. A type annotation checks or constrains the one monotype assigned to a recursive
   member. It does not allow the member to be instantiated at different types inside
   its own SCC.
5. Scoped type variables in supported explicit annotations remain a language feature.
   Surface head-binder annotation sugar is excluded until partial annotation holes
   have a representation and checking story.
6. All type information is compile-time-only. Evaluation runs `Expr.erase` output (or
   an equivalent annotation-free term) using the existing substitution semantics.
   There is no type-passing operational semantics and no type-directed runtime step.
7. Expression-level hover remains a product requirement, but inferred expression
   types live in an inference-result table keyed by `CorePath`, not in the Core
   expression grammar. Lowering provenance joins `SourceId`/spans to those paths;
   generalized binder schemes remain a separate result. Runtime terms contain none
   of this metadata.

The semantic slogan is: **monomorphic inside an SCC; generalized after the SCC;
erased at runtime**.

## Historical findings

### The useful old checkpoint

`be9cc14` is the intended final cleanup before `1eaf41e` began the type-passing
migration. However, that exact commit deletes `FHM/HasItem.lean` while leaving
`import FHM.HasItem` in `FHM/Core.lean`, so it is not a clean-source build target.
Its parent `b016fcf` retains the unused module and is the closest source-complete
checkpoint with the same language semantics. A fresh build was started in an isolated
worktree but stopped while Mathlib dependencies were still compiling, so this report
does not claim a completed clean-build verification of the historical tree. Together
the two commits contain the cleanest complete version of the intended core:

- `FHM/Core.lean`: shared-monotype `TypeOfHM.letRec`, `eraseTyAnnots`, small-step
  semantics, and erased type safety;
- `FHM/InferW.lean`: recursive-group Algorithm W plus soundness, completeness,
  executable completeness, and principality;
- no `letRec` annotations and therefore no in-block polymorphic recursion;
- no term-level type arguments on variables.

Some prose at and after this point used “polymorphic mutual recursion” loosely. The
rules are authoritative: recursive occurrences are monomorphic; only uses after the
group is generalized are polymorphic.

### Why type passing appeared

The costly migration was not required by mutual recursion or scoped annotations by
themselves. It was motivated by the stronger goal of annotation-directed polymorphic
recursion inside an SCC, especially nested recursive annotations that referred to an
enclosing scoped type variable. The FHM formalization chose to preserve explicit
instantiations through substitution using elaboration and term-level type passing.

That choice was not a semantic necessity. OCaml, F#, and Haskell accept explicitly
annotated polymorphic recursion while erasing ordinary parametric type arguments
before runtime. A different FHM metatheory could also check such programs and then
erase them. What the reset rejects is the static and proof complexity of doing so,
not erasure compatibility in principle. There is no clean pre-type-passing repository
checkpoint containing the full feature, and it is outside the reset contract above.

### External recursion precedent

Standard ML is the closest established precedent for the chosen rule: recursive uses
within the declaration share a monotype even in the presence of explicit scoped type
variables. OCaml without an explicitly universal annotation behaves similarly, but
`'a.` annotations enable polymorphic recursion. F#, Haskell/GHC, and explicitly
universal OCaml are more permissive than this reset.

Elm is a notable middle ground and does **not** implement the uniform per-SCC rule:
an annotated function's direct self-reference is monomorphic, but other members of
the same genuine recursive cycle may instantiate that annotated function at different
types. That matches the tempting “one type in `g`, another in `h`” intuition, but is
not the simpler all-members-monomorphic SCC policy selected here.

### The pre-reset Path R state

The pre-reset implementation was already type-erased and Damas--Milner at runtime and
at recursive SCCs:

- `RecSpec.init` gives every recursive member a monotype;
- `Infer.letRec`, the executable inferer, and `TypeOfHM.letRec` all enforce a single
  in-SCC instance;
- annotations act as export ceilings/checks rather than enabling in-SCC scheme use;
- body and later-SCC environments contain generalized schemes;
- `Expr.erase` removes annotations; `Step` never inspects a type. Before Gate C,
  `.found` was also removed here, but inferred node types now live outside syntax.

The recursive smoke matrix confirms this boundary: ordinary mutual recursion,
post-SCC polymorphism, and fixed-instantiation annotated groups pass; annotated and
unannotated in-SCC multi-instantiation fail.

Surface head-binder annotation sugar remains deliberately unsupported. It cannot be
fully lowered into the present Core annotation shapes until partial annotation holes
such as `Int -> _ -> (_, Bool) -> Int` have a defined representation and checking
story. It is not part of this reset.

Baseline verification on 2026-09-29:

- `lake build`: 726 jobs, success (warnings only);
- `lake env lean --run scratch/PolyRecTest.lean`: 11/11 cases matched the DM contract;
- `node scripts/scratch-hm-audit.mjs`: 37/37 fixtures behaved as expected;
- `node scripts/hm-editor-smoke.mjs`: 10/10 checks passed.

Final Gate C verification on the same date additionally covered the metadata-specific
`NodeTypeMapTest` and provenance suites, the 1,643-job CLI/editor/grammar build, both
safe exhaustive hover sweeps, the VS Code lifecycle regression, the browser
playground, and the verified/unverified boundary check.

## Expression type metadata after BL

Before Gate C, the `.found Ty Expr` node was chiefly the internal carrier for per-expression
monotypes. It powered arbitrary-expression hover, lambda/pattern binder fallback
types, and the BL walkers. It did **not** own generalized binder schemes: inference
already emitted those in a separate `BinderSchemeMap`. The editor also did not
consume the decorated tree directly. `inferWithProvenance` first joined its payloads
into source/path type tables, and `HMDisplay` read those tables.

Gate C kept that observable behavior while removing `.found` from `Expr`:

- `inferWithTypes` returns an `InferenceResult` containing
  `NodeTypeMap := List (CorePath × Ty)`, the root type, and `BinderSchemeMap`;
- recursive inference rebases child maps under path components and applies final
  substitutions/skolem closing to their types;
- lowering continues to own `SourceId → CorePath` provenance;
- hover joins the two maps once per check;
- evaluation consumes the unchanged source Core term after ordinary annotation
  erasure.

This is the smallest conventional design for this repository. A separate typed AST
would also be clean, but would duplicate the Core tree and require another family of
shape/erasure traversals. Re-inferring only the hovered subexpression is unattractive:
it must reconstruct its lexical environment, scoped variables, expected type, and
recursive-group constraints. The metadata-table migration remained separate from BL
deletion so hover parity could be tested independently. `TypedLowered.nodeTypesTotal`
now checks exact one-to-one coverage of the logical Core paths before editor
artifacts are exposed.

## Why not revert to `be9cc14`

The checkpoint has only the early Core/InferW/Examples/Pretty/SurfaceLang skeleton.
Compared with the present repository it lacks, among other things:

- the lexer/parser and full surface-to-Core bridge;
- user datatype declaration elaboration;
- dependency SCC computation and its verification;
- verified pattern compilation, exhaustiveness, and surface safety bridges;
- the production CLI/evaluator/editor support;
- source spans, provenance, stable Core paths, and rich hover support;
- later primitives and language examples;
- the current headline theorem packaging and the restored completeness spine.

Rebuilding or replaying those features onto the old tree would be a second migration,
with no semantic benefit. The old tree should instead be consulted when a bounds-era
abstraction obscures the simpler HM statement or proof.

## Why stripping the current tree is still non-trivial

Bounds is not an isolated directory. `FHM/Core.lean` imports the bounds kernel and
adds `Ty.bl`; the surface grammar includes counts, count slots, `BL`, and Nat binders;
lowering carries those forms into Core; inference uses `AgreesHM`, `FactorsHM`, and
bounds-blind unification; soundness and completeness are stated through
`eraseBounds`; and the CLI/editor import bounds reporting/checking directly.
The visible scale is large: `FHM/Bounds/` currently contains 149 Lean modules and
about 52,600 lines, while the shared Core/InferW/Completeness files contain thousands
of additional bounds-projection references and proof cases.

Consequently, deleting `FHM/Bounds/` alone cannot produce a plain HM repository.
The reset needs to remove the product layer first, then simplify the shared grammar
and metatheory together.

## Implementation sequence

The original investigation split the work into seven phases (0--6), each targeting a
fully green tree. That is too much process for this deletion campaign. In particular,
`Core`, `InferW`, and `Completeness` form one tightly coupled Path-R proof cluster;
separating direct-HM restoration from recursive-rule cleanup would repair many of the
same proofs twice. Conversely, `.found` has an independent, observable hover-parity
requirement and should not disappear in the middle of the bounds proof rewrite.

Use three meaningful integration gates. Focused modules may be red inside a campaign;
the whole repository need only be green at the gate.

### Gate A -- user-facing HM-only language and product (complete)

This folds the old contract-freeze, bounds-product, and surface-language phases into
one deletion campaign.

- Freeze an explicit HM fixture manifest instead of letting the audit discover every
  `.fhm` file in `scratch/`.
- Preserve the recursion boundary suite, including ordinary scoped annotations and
  every negative in-SCC multi-instantiation case. Keep head-binder sugar explicitly
  unsupported for reasons independent of recursion.
- Remove `--bl`/`--auto`, bounds result fields, bounds reports and diagnostics, bounds
  hover assembly, and bounds editor configuration.
- Delete surface counts, count slots/holes, `BL` syntax, Nat binders, their parser and
  lowering paths, and count-driven binding classification.
- Remove bounds-only build targets, tests, scripts, examples, experiments, and proof
  modules as their last importers disappear.
- It is acceptable for unreachable internal bounds compatibility definitions to
  remain briefly inside the Core proof cluster until Gate B. Do not invent new
  compatibility modules merely to manufacture a smaller checkpoint.

Gate A is complete when no user program or tool mode can request or construct bounds,
and the verified target, CLI, editor, grammar generator, HM fixture suite, recursion
matrix, hover sweep, and verified/unverified boundary check are all green.

### Gate B -- direct HM Core, Algorithm W, and recursive rule (complete)

This is one bounded red-to-green proof campaign, combining the old Core-purification
and recursive-rule phases.

- Remove `Ty.bl` and the final Core import of the bounds kernel.
- Delete all `eraseBounds` operations and bounds-projection statements on types,
  schemes, expressions, environments, constructors, and contexts.
- Replace `AgreesHM`/`FactorsHM` and bounds-blind unification with ordinary structural
  equality, `Unifies`, and standard MGU factorization.
- Restate soundness, completeness, principality, progress, preservation, and surface
  safety directly over the inferred context, term, and type.
- Delete `RecSpecs.PolyTyped`, `InferRecGroup.consPoly`, and the old source path that
  made annotations available as schemes inside an SCC. Retain annotations only as
  checks/ceilings on the single solved monotype for each SCC member. `RecSpec.poly`
  remains the declarative descriptor for an annotated member's post-group export
  scheme; `RecSpec.init`, the source inferer, produces only `.mono` witnesses for
  recursive RHS checking.
- Mine `b016fcf`/`be9cc14` for direct-HM proof shapes without replacing the mature
  surface/compiler stack.

Keeping these edits together avoids temporarily adapting the enormous Path-R proof
family to a bounds-free but still two-regime recursive representation that is deleted
immediately afterward.

Gate B requires direct, axiom-clean HM soundness, completeness, principality, and
runtime/surface safety, plus the unchanged recursion polarity matrix.

### Gate C -- expression metadata and final audit (complete)

Keep the `.found` migration separate because it changes observable editor metadata
and needs a precise hover-parity gate.

- Define `NodeTypeMap := List (CorePath × Ty)` with final-substitution types.
- Return it and `BinderSchemeMap` alongside the root inference result without
  constructing a second expression.
- Join source provenance directly to the node map and preserve expression, parameter,
  pattern-binder, and declaration hover behavior.
- Remove `.found`, `FoundFree`, `stripFound`, found-type opening/closing/substitution
  helpers, and their cases from semantic inductions.
- Finish repository cleanup here: remove stale bounds prose/settings/fixtures,
  correct obsolete polymorphic-recursion claims, and run the forbidden-symbol audit.

Gate C requires hover parity, one inference pass, unchanged root types and binder
schemes, no `.found` in semantic Core, and no bounds symbols or imports outside the
explicitly preserved historical design notes.

## Verification gates

At minimum, preserve or adapt these existing checks:

```sh
lake build
node scripts/scratch-hm-audit.mjs
lake env lean --run scratch/PolyRecTest.lean
node scripts/hm-editor-smoke.mjs
node editors/web/scripts/hover-sweep.mjs editors/web/fixtures/hover-rich.fhm
bash scripts/check-unverified-boundary.sh
```

Add focused checks for:

- ordinary `let` polymorphism;
- self and mutual recursion at one monotype;
- generalization after SCC exit, including two different body instantiations;
- rejection of annotated and unannotated in-SCC multi-instantiation;
- scoped variables in supported lambda, let, and nested explicit annotations;
- deliberate rejection of unsupported head-binder annotation sugar;
- annotation erasure and evaluation independence;
- full soundness/completeness/principality theorem signatures with no residual
  bounds relation.

## Expected end state

The repository now keeps its mature language front end and verified compiler/tooling
pipeline, but its trusted static core again says exactly what the language is:
ordinary erased rank-1 Hindley--Milner with monomorphic recursive SCCs and
generalization at group exit. Bounds survives only in git history and in the preserved
design-review commit on the old line of development.
