# Canonical partial Core and annotation-local named holes

There is one `Expr T` inductive family and one `Scheme T` wrapper. Parameters
store `Option T`; ordinary and recursive bindings store `Option (Scheme T)`.
Canonical source is `InferInput := Expr TyTemplate`, and `PolyTy := Scheme Ty`.
`PartialCore.Source` names that same source instance; it is not another AST.
There is one universe of types, contexts, schemes and constructors.

A source binding stores only an optional written binder count and template.
`Option.annotationView` derives the checking cases (`CheckAnn`) from that
content: absent, partial monotype, partial written forall, or hole-free scheme.
No complete/partial tag is stored in the source. Every hole-free annotation
follows the parser's existing complete-signature policy, including polymorphic
recursive use. This also normalizes hand-built Core nodes whose old tags
previously disagreed with their hole-free contents.

`InputTyping` is the main declarative source judgment. It has structural rules
for every source form, including ordinary and signed lets and recursive groups.
It directly judges partial annotations. There is no constructor admitting a
completed subtree. Inference proves `InputTyping` directly, and
`InputTyping.erase` proves runtime typing.

## Dependency boundary

The syntax is below inference and has no solver state:

```text
Core                       Ty, Scheme T, Expr T, Ctx, partial type syntax
  → RuntimeTyping
  → InferenceSupport       neutral substitution, unification and runtime facts
    → AnnotationMatching   pure matching, local assignments and completions
      → AnnotationAllocation
      → SourceAnnotations  written schemes, checking views, transport
      → InferInput         source operations and scoped proof refinement
        → SourceTyping     InputTyping, direct erasure, refinement equivalence
          → InferW
            → Completeness
```

Historical complete-Core support is an optional branch of this graph:

```text
Core → Compatibility/Typing
RuntimeTyping + Compatibility/Typing → Compatibility/Erasure
InferenceSupport + Compatibility/Erasure → Compatibility/Metatheory
SourceTyping + Compatibility/Metatheory → SourceCompatibility
  → SurfaceBridge/CompleteCore → Headlines/CompleteCore
                              → Examples/CompleteCore
```

The default roots, CLI and canonical `Examples` do not import that branch.
`AnnotationAllocation` imports only `AnnotationMatching`; it does not depend on
expression inference, generalization or SCC scheduling. There is one universe
of types, schemes, contexts and constructors.

## Declarative annotations

`Template.Fits holes template ty` is a pure relation:

- `_` matches any type independently at each occurrence.
- `?name` looks up one type in `holes`, a finite `List (String × Ty)`.
- Fixed leaves and type constructors retain their ordinary meaning.

`Template.Matches` existentially hides a unique-key local assignment.
`Completion n template ty` additionally packages scoped assignment values and
a scoped result. `Fits.covers` establishes that all occurring names have
assignments. `Fits.named_equality` forces repeated occurrences to agree.
Neither typing contexts nor source expressions carry a global hole table.

`Fits.completion` restricts a match to its used keys, discarding unused or
duplicate irrelevant entries. There is no uniqueness or principality claim for
unused hole solutions. Expression-type principality remains the public claim.

`Completion.onSubst`, `Completion.open`, and `Completion.close` transport the
type and the same local assignment together. Matching regularity, bound-variable
scope, authored-variable avoidance, and opening compatibility are proved in
`AnnotationMatching`. Source substitution, weakening and environment agreement
transport these witnesses. `InputTyping : Ctx → InferInput → Ty → Prop` has no
protected-variable index. Fresh scheme openings are abstract type parameters;
inference's protected metavariables belong to `InferRequest`.

`ScopedTyping` retains the old scope-indexed induction machinery as an internal
proof refinement. `ScopedTyping.source`, `InputTyping.scoped`, and
`scopedTyping_iff` prove its equivalence with source typing whenever the index
covers authored free variables. Public executable soundness, completeness and
principality now quantify over the unindexed `InputTyping`.

## Scope and quantifier order

Every written annotation has its own assignment. Repeated `?a` in
`(?a, ?a)` shares; `?a` in another annotation is unrelated. Different names and
anonymous occurrences are independent. This remains true for separate
parameter and result annotations in one function head.

Head desugaring can combine independently written annotations into one full
signature. Lowering qualifies named keys by their parameter/result origin
before that combination, so desugaring cannot accidentally extend their scope.
The qualification separator is not a source identifier character. Original
token names and annotation spans remain available to the editor.

Ordinary lets require `MonoMatches` of the derived checking view; signed lets
require `SignatureMatches`; recursive groups store `RecAnnotationsMatch` for each
monomorphic member. These contain one closed `SchemeMatches` witness before
any cofinite RHS or recursive-pool-opening premise. Thus the order is:

```text
∃ completedScheme, ∃ localCompletion,
  matches annotation completedScheme localCompletion ∧
  ∀ fresh openings, source RHS has completedScheme.openVars
```

Solutions may contain the scheme's bound variables. Every opening transports
that one solution consistently; the rule never selects a new completion at
each opening. `InputTyping.template_completion`,
`InputTyping.partialSignature_completion` and recursive inversion preserve
this order explicitly. `SignatureMatches.ofCofinite` and
`RecMatches.ofCofinite` close one sufficiently fresh checked opening.

`AllowsExtraBinders written inferred := written ≤ inferred` isolates the
existing policy that partial signatures may infer extra binders. Authored fixed
leaves must be scoped by the written prefix, while hole solutions may refer to
the entire completed scheme. Implicit let-polymorphism, dependency cuts,
recursive SCC order, staged contexts and generalization policy are unchanged.
Complete written signatures alone permit polymorphic recursive calls.

## Algorithm and artifacts

The production allocator uses one fresh metavariable per distinct local name
and a separate metavariable for each `_`. It starts a new named table at every
annotation. `Template.Fits.allocate_override_source` proves that a declarative
match factors through this allocation while preserving older ambient
substitution images and the reported named lookups. Targets may themselves
mention allocated variables; no hidden global freshness assumption is needed.
`allocate_bounds`, `allocate_lc_source`, and `allocate_avoid` establish the
frontier, local-closure and avoidance invariants used by production inference
and its completeness proof.

The shared checked allocator returns the substitution and a certified
completion. Production public results retain inferred type, frontier,
substitution, node types and binder schemes. Existing editor artifacts project
hole solutions from these inferred types and source provenance. Named keys
are `(annotation span, local name)`; anonymous identities are token positions.
Each token has its own precise hover, and holes have no declaration target.
The lexer uses a dedicated `?name` token, with the existing Unicode identifier
rules and UTF-16 editor coordinates.
Application diagnostics identify repeated local names in directly annotated
parameters. Signed and recursive failures retain the existing binding-level
fallback where the diagnostic probe cannot locate a more precise explanation.

`InferCert.inputSound_source` constructs source typing by induction on
inference; it does not assume typing of a completed expression.
`InferCert.inputSound` preserves authored annotations when there are no live
provisional slots. `Infer.sound` now follows directly from source soundness
and `InputTyping.erase`. Runtime terms have no named-hole representation or
effect.

## Retained compatibility

The `Expr Ty` instance also represents erased runtime terms. Historical
`TypeOfHM` lives in `Compatibility/Typing`, alongside `TypeOfMatchBranch`,
`Option.Pins` and complete-annotation `GeneralisesTo`. None of these declarations
is present in the default verified environment. They support complete-Core
clients and the opt-in `FHMCompatibility` façade. `InputTyping`
has its own explicit primitive rules. Comparison rules require source typings
for `True` and `False` at `Bool`, just as the historical rules did. Recursive
rules use `SourceRec.MonoTyped` and `SourceRec.PolyTyped` to expose the existing
staged policy without expanding it inside the main rule. Matching remains
separate from that policy.

Complete and partial annotations use instances of the same syntax family.
`ScopedTyping.ofComplete` and `ScopedTyping.toCore` live in the optional
`SourceCompatibility` module. Production completeness no longer imports it:
primitive, variable and constructor cases use direct leaf inversions. These
compatibility theorems are neither typing constructors nor soundness premises.

The internal `ScopedTyping` refinement now uses `RuntimeTyping.RunWT` for its
primitive leaf facts, substitution and weakening. Public source soundness,
completeness, principality and erasure have no transitive proof dependency on
`TypeOfHM` or `TypeOfMatchBranch`. The import-boundary script rejects historical
compatibility imports in every default root and canonical examples. Run
`lake env lean scripts/check-source-proof-boundary.lean` to check that the old
declarations are absent from the default environment, inspect actual public
proof dependencies, and check the standard-axiom boundary.

Default `Headlines` inversions and `Examples` use `InputTyping`; typed pattern
adequacy uses `RuntimeTyping.RunWT` directly. Runtime closure and finite-execution
safety are proved under `RunWT`, independently of either source relation.
Complete-Core inversion witnesses and demonstrations moved to optional modules.
About 1,200 lines of unused historical substitution, generalization, closure,
canonical-form and safety proofs were deleted rather than moved. Only the
induction and term-weakening proofs used by the remaining historical clients
survive in `Compatibility/Metatheory`; regularity is a runtime-erasure corollary.
The old erasure bridge lives in
`Compatibility/Erasure`, outside `RuntimeTyping`.

Public `InferenceResult` contains type, substitution/frontier, node types and
binder schemes, with no completed expression. The editor reads binding schemes
from metadata or complete written declarations. The CLI and example runners
evaluate the original source's erasure. Hole hovers continue to project the
solution of each source occurrence from type/scheme facts and provenance.

`InferResult` now contains only `frontier`, `subst` and `ty`, and
`InferenceResult` extends it with editor facts. Neither the worker nor
`InferCert` constructs or retains a completed annotated expression. Branch
results retain no branch ASTs; recursive state stores schemes, metadata and a
checked flag per member. Completeness proves those flags are set before scheme
collection. `inferWithTypes_infer` relates the exact public semantic result to
`InferCert` without a hidden expression witness.

The completed-output typing, AST-fidelity and erasure-comparison proof paths
have been deleted. Local annotation fidelity still follows from direct source
typing and its closed matching witnesses. `AnnotationCompletion`, its recursive
AST relations and their transport/generalization proofs have also been deleted.
The separate named-source prototype and its worker have been removed. So have
the completed-subtree typing constructor, annotation-only embeddings into a
second template syntax, the old anonymous-only allocation factoring proof,
and matching-only transport through arbitrary completed ASTs.

## Result-contract audit and remaining retirement boundary

The audit on 2026-11-02 distinguishes successful execution from correctness of
the returned data. `inferWithTypes_typing_iff` characterizes every valid source
type as an admissible substitution instance of the actual returned type.
`principalType_eq_inferWithTypes` and `typecheck_eq_inferWithTypes` preserve the
actual values across the public projection APIs. `typecheck_sound` proves that
every fresh opening of its returned scheme types the original source.

That last contract exposed an overgeneralization in the scheme-only wrapper:
it previously generalized authored fixed free variables. It now excludes
`input.rigidVars`, just as inference does. This affects hand-built open Core
annotations; parsed programs have no authored free type variables. Ordinary
let generalization and recursive SCC policy are unchanged.

`DataDecls.ElaboratesTo` independently specifies declaration output. Its
constructor-signature equality preserves names, parent types, parameter counts,
field types and declaration order, excluding missing or extra entries.
`elabDecls_eq_some_iff` proves the exact result graph. Program-lowering relations
now use this declarative contract in place of an equality to the elaborator.
`DeclsTests` proves that erased, missing, added or altered entries violate it.

Other reviewed uses of `.isSome` are paired with value-level contracts:
unification returns a certified most-general unifier; annotation and recursive
helpers return indexed certificates; pattern compilation preserves the exact
selected branch and captures; SCC soundness specifies the returned partition
and ordering. Their completeness or totality corollaries legitimately mention
only successful execution. None of those corollaries alone certifies an output.

The semantic source migration is implemented, but complete retirement of the
historical architecture and verification of every editor artifact are not done.
The remaining deletion boundary is:

| Region | Retirement condition |
| --- | --- |
| `SourceCompatibility`, `SurfaceBridge/CompleteCore`, `Headlines/CompleteCore`, `Examples/CompleteCore` | Migrate or retire the opt-in complete-Core API and its demonstrations. |
| `Compatibility/Typing` | Remove the remaining complete-Core clients of `TypeOfHM`, `TypeOfMatchBranch`, complete-annotation `GeneralisesTo` and `Option.Pins`. |
| `Compatibility/Metatheory` | Retire the historical surface bridge's regularity and term-weakening uses; the other old metatheory has been deleted. |
| `Compatibility/Erasure` | Retire the historical clients of `TypeOfHM.erase_preserves_typing`. |
| Complete-source projections and annotation operations | Check compatibility, examples and diagnostic probes before deletion. |

Keep `Expr Ty` for erased terms, `RuntimeTyping.RunWT` and its operational
metatheory, and neutral `Ty`/scheme/context/unification/recursive-policy lemmas.
Deleting entire support modules would also delete foundations the canonical
path still uses. The unused complete-Core annotation-boundedness proof formerly
in `InferInput` has been removed; the opt-in compatibility proof remains.

## Verification

The default build includes `DeclsTests`, `NamedHoleTests`, `AnnotationAllocationTests`,
`LetMatchingTests`, `SignatureMatchingTests`, and `RecMatchingTests`.
They cover independent anonymous/named holes, repeated-name conflicts,
separate scopes, mixed holes, bound-variable solutions across openings,
ordinary/signed/recursive inference, closed witness extraction, substitution,
pool renaming, authored-scope rejection, allocation factorization, noisy
assignment restriction, authored-rigid preservation in returned schemes,
declaration-output fidelity, and unchanged erased evaluation.

Parser/editor guards, CLI smoke tests, accepted/rejected scratch fixtures and
hover snapshots cover surface syntax, annotation provenance, function heads,
Unicode token ranges and runtime regression. Generated TextMate syntax includes
the dedicated named-hole token.

Required final gates are `lake build`, the CLI/editor/compatibility/example and
grammar targets, `scripts/scratch-hm-audit.mjs`, `scripts/hm-editor-smoke.mjs`,
the web tests, `scripts/check-unverified-boundary.sh`, and
`lake env lean scripts/check-source-proof-boundary.lean`.

Latest full verification on 2026-11-02:

- `lake build`: passed.
- `lake build fhm FHMEditorTests FHMCompatibility FHMExamples FHMHistorical fhm_grammar`:
  passed.
- `node scripts/scratch-hm-audit.mjs`: 17 files; 13 accepted, four expected
  rejections, no failures. The existing anonymous-hole playground is included.
- `node scripts/hm-editor-smoke.mjs`: 84/84 passed, including all 75 prior checks.
- `node --test editors/web/tests/*.test.mjs`: 35/35 passed, no skips, including
  three hover snapshots and the grammar/token-export tests.
- `bash scripts/check-unverified-boundary.sh` and `git diff --check`: passed.
- `lake env lean scripts/check-source-proof-boundary.lean`: historical typing
  declarations are absent from the default environment; all seventeen checked
  public proofs have no historical source-typing dependencies and use standard
  axioms only.

The modified modules in the trusted production import closure contain no
`sorry`, `admit`, `axiom` declarations or `native_decide` proof escapes.
The public production soundness, runtime erasure, completeness and principality
theorems, together with assignment matching, substitution, opening, closing and
allocation fidelity, were checked explicitly. They use only `propext`,
`Classical.choice` and `Quot.sound`; repeated-name equality needs none.
The optional `FHM.Examples.CompleteCore` module retains its pre-existing native
concrete demo canaries. Canonical `FHMExamples` uses source derivations and
executable guards without native proof escapes. No production proof depends on
the historical canaries.

The parser, diagnostic wording and editor provenance joins remain unverified,
as before. Their operational regressions are covered by the executable tests.
`InferCert` certifies the semantic inference result. Local matching and allocation
fidelity are proved, but there is no array-wide theorem certifying every returned
node/binder metadata entry or its projection into an editor hover.
The remaining compatibility artifacts are described above. The shared
`Expr T`/`Scheme T` migration removes the separate `InferInput` inductive and its
two annotation parameters. Implicit polymorphism and recursive SCC/generalization
policy remain unchanged; annotation matching stays separate from that policy.
