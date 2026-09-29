# Plan: return FHM to an erased Hindley--Milner language

**Status:** investigation and recommendation, 2026-09-29

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

### The present Path R state

The current implementation is already type-erased and Damas--Milner at runtime and at
recursive SCCs:

- `RecSpec.init` gives every recursive member a monotype;
- `Infer.letRec`, the executable inferer, and `TypeOfHM.letRec` all enforce a single
  in-SCC instance;
- annotations act as export ceilings/checks rather than enabling in-SCC scheme use;
- body and later-SCC environments contain generalized schemes;
- `Expr.erase` removes annotations and `.found`; `Step` never inspects a type.

The current recursive smoke matrix confirms this boundary: ordinary mutual recursion,
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

## Expression type metadata after BL

The current `.found Ty Expr` node is chiefly the internal carrier for per-expression
monotypes. It powers arbitrary-expression hover, lambda/pattern binder fallback types,
and the BL walkers. It does **not** own generalized binder schemes: inference already
emits those in a separate `BinderSchemeMap`. The editor also does not consume the
decorated tree directly. `inferWithProvenance` first joins its payloads into
source/path type tables, and `HMDisplay` reads those tables.

Once BL is gone, keep that observable behavior but remove `.found` from `Expr`:

- inference returns `NodeTypeMap := List (CorePath × Ty)` alongside its root type and
  `BinderSchemeMap`;
- recursive inference rebases child maps under path components and applies final
  substitutions/skolem closing to their types, exactly as it currently transforms
  `.found` payloads;
- lowering continues to own `SourceId → CorePath` provenance;
- hover joins the two maps once per check;
- evaluation consumes the unchanged source Core term after ordinary annotation
  erasure.

This is the smallest conventional design for this repository. A separate typed AST
would also be clean, but would duplicate the Core tree and require another family of
shape/erasure traversals. Re-inferring only the hovered subexpression is unattractive:
it must reconstruct its lexical environment, scoped variables, expected type, and
recursive-group constraints. The metadata-table migration should remain separate
from BL deletion so hover parity can be tested independently.

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

Each phase ends with a green build and the HM semantic matrix. Avoid mixing the
recursive-policy change with the bounds removal until ordinary HM has a direct,
bounds-free statement again.

### Phase 0 -- freeze the HM contract

- Turn the existing recursion fixtures into the permanent language-boundary suite.
- Add a positive fixture for scoped type variables in an ordinary annotation.
- Preserve negative fixtures for every form of in-SCC multi-instantiation.
- Keep head-binder annotation sugar explicitly unsupported; do not use its current
  negative fixture as evidence about the recursive typing boundary.
- Record current theorem signatures/axioms and current CLI/editor outputs.

Gate: current `lake build`, HM audit, recursion matrix, and editor smoke all remain
green before structural deletion begins.

### Phase 1 -- remove the bounds product and proof forest

- Remove `FHM/Bounds/**`, bounds-only tests, `FHM/BLSketch.lean`, quantitative/count
  experiments, and bounds-only scratch programs.
- Remove the bounds and Z3 targets/dependencies from `lakefile.toml` when no remaining
  HM component imports them.
- Remove `--bl`/`--auto` modes, bounds reports, bounds diagnostics, and bounds hover
  assembly from the CLI/editor/web surfaces.
- Remove or rewrite bounds-only documentation; retain this plan and the git history as
  the archaeology record.

Transitional rule: it is acceptable for the shared Core type to retain unreachable
`Ty.bl`/`eraseBounds` compatibility code during this phase if that is needed to keep
the verified HM target green. Do not add new compatibility abstractions.

### Phase 2 -- make the surface language plain HM

- Delete surface `Count`, `CountSlot`, `Ty.bl`, count holes, Nat binders, and their
  lexer/parser/finalization/lowering paths.
- Simplify binding classification so count binders can no longer force an otherwise
  non-recursive local binding through `letRec`.
- Remove BL pretty-printing and syntax highlighting.
- Retain ordinary explicit schemes and scoped type-variable syntax.

Gate: no parsed/lowered program can construct a bounds-bearing Core type; all HM
surface, declaration, SCC, coverage, provenance, and editor tests pass.

### Phase 3 -- purify Core and Algorithm W

This is the main proof checkpoint and should be treated as one bounded campaign.

- Remove `Ty.bl` and the Core import of `FHM.Bounds.Kernel`.
- Delete every `eraseBounds` operation on types, schemes, expressions, environments,
  constructors, and contexts.
- Replace `AgreesHM`/`FactorsHM` and BL/List special unification with ordinary
  structural equality, `Unifies`, and standard MGU factorization.
- Restate `Infer.sound`, completeness, principality, and the surface headlines
  directly over the inferred context, term, and type, with no bounds projection.
- Simplify the proof families by mining the corresponding statements/proof shapes at
  `b016fcf`/`be9cc14`; do not copy the old product architecture wholesale.
- Remove now-dead residual transport and erase-commutation lemmas.

Gate: direct (not “up to bounds erasure”) soundness, completeness, principality,
progress, preservation, and surface safety; no project-specific axioms.

### Phase 4 -- move inferred expression types out of Core

- Define a final-substitution `NodeTypeMap` keyed by the existing `.found`-transparent
  `CorePath` vocabulary.
- Make the inference worker return that map and `BinderSchemeMap` beside the root
  type, without constructing a second expression.
- Join source provenance directly against the type map; preserve arbitrary-expression,
  parameter, pattern-binder, and declaration hover behavior.
- Remove `.found`, `FoundFree`, `stripFound`, found-type substitution/closing helpers,
  and their cases from Core, inference, completeness, lowering, paths, pretty-printing,
  and pattern compilation.
- State and prove the required map domain/final-substitution coherence contracts rather
  than making editor metadata part of the term induction principles.

Gate: identical successful-program hover results, one inference pass, unchanged root
type/scheme results, and no `.found` constructor anywhere in the semantic Core.

### Phase 5 -- collapse recursive typing to its actual DM rule

Do this after Phase 4 so failures cannot be confused with bounds blindness or the
expression-metadata migration.

- Delete stale `RecSpec.poly`, `RecSpecs.PolyTyped`, `InferRecGroup.consPoly`, and
  related comments/helpers that describe the abandoned in-block-polymorphic regime.
- Keep per-member annotations only as compile-time checks/ceilings.
- State one obvious recursive-group rule: all RHS environments contain only the
  group's monotypes; the body environment contains the generalized/validated schemes.
- Preserve the already-separated expression-type and binder-scheme metadata.

Gate: the full recursion matrix still has the same polarity, and the declarative,
relational, and executable rules visibly implement the same policy.

### Phase 6 -- repository cleanup and final audit

- Delete dead bounds briefs, scripts, editor settings, fixtures, and generated grammar
  entries; remove empty dependencies and targets.
- Correct stale claims that the language supports polymorphic recursion.
- Run a repository-wide forbidden-symbol audit for `BL`, bounds/count constructs,
  `eraseBounds`, `AgreesHM`, `FactorsHM`, and bounds/Z3 imports (allowing only this
  historical plan if desired).
- Re-run fresh builds, theorem axiom audits, CLI/editor tests, parser/lowering tests,
  recursion tests, and pattern/declaration tests.

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

The repository keeps its mature language front end and verified compiler/tooling
pipeline, but its trusted static core again says exactly what the language is:
ordinary erased rank-1 Hindley--Milner with monomorphic recursive SCCs and
generalization at group exit. Bounds survives only in git history and in the preserved
design-review commit on the old line of development.
