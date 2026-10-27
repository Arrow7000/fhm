# Canonical partial Core and annotation-local named holes

The production source language is `InferInput`, declared in `Core.lean`, with
`TyTemplate` and `BindingAnn` as aliases for the shared `PartialCore.Template`
and `PartialCore.Ann` types. `PartialCore.Source` is an alias for that same
source type. The namespace name is historical; there is no separate prototype
source language or prototype inference worker.

`InputTyping` is the main declarative source judgment. It has structural rules
for every source form, including ordinary and signed lets and recursive groups.
It directly judges partial annotations. There is no constructor admitting a
completed subtree. Inference proves `InputTyping` directly, and
`InputTyping.erase` proves runtime typing.

## Dependency boundary

The syntax is below inference and has no solver state:

```text
Core                       Ty, PolyTy, Ctx, source/annotation/runtime syntax
  → RuntimeTyping
  → InferenceSupport       neutral substitution, unification and runtime facts
    → AnnotationMatching   pure matching, local assignments and completions
      → AnnotationAllocation
      → InferInput         source operations, InputTyping, direct erasure
        → SourceCompatibility
        → InferW
          → Completeness
```

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
`AnnotationMatching`. Source substitution, weakening, scope restriction, and
environment agreement transport these witnesses in `InferInput`.

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

Ordinary lets store `Ann.MonoMatches`; signed lets store
`Ann.SignatureMatches`; recursive groups store `RecAnnotationsMatch` for each
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
`Infer.inputSound` preserves authored annotations when there are no live
provisional slots. `Infer.sound` now follows directly from source soundness
and `InputTyping.erase`. Runtime terms have no named-hole representation or
effect.

## Retained compatibility

The historical `Expr` and `TypeOfHM` support completed-Core clients, neutral
runtime/typing facts, and the opt-in `FHMCompatibility` façade. They are not a
second production source language. `InputTyping.ofComplete` in
`SourceCompatibility` derives structural source typing for complete syntax;
it is not a typing constructor or soundness premise.

`InferResult.completedExpr`, `Infer.sourceSound`, and `AnnotationCompletion`
remain verified compatibility/editor artifacts. Removing these would require
migrating their existing consumers and certificate indices, independently of
source acceptance. Direct source/runtime soundness does not go through them.
The separate named-source prototype and its worker have been removed. So have
the completed-subtree typing constructor, annotation-only embeddings into a
second template syntax, the old anonymous-only allocation factoring proof,
and matching-only transport through arbitrary completed ASTs.

## Verification

The default build includes `NamedHoleTests`, `AnnotationAllocationTests`,
`LetMatchingTests`, `SignatureMatchingTests`, and `RecMatchingTests`.
They cover independent anonymous/named holes, repeated-name conflicts,
separate scopes, mixed holes, bound-variable solutions across openings,
ordinary/signed/recursive inference, closed witness extraction, substitution,
pool renaming, authored-scope rejection, allocation factorization, noisy
assignment restriction, and unchanged erased evaluation.

Parser/editor guards, CLI smoke tests, accepted/rejected scratch fixtures and
hover snapshots cover surface syntax, annotation provenance, function heads,
Unicode token ranges and runtime regression. Generated TextMate syntax includes
the dedicated named-hole token.

Required final gates are `lake build`, the CLI/editor/compatibility/example and
grammar targets, `scripts/scratch-hm-audit.mjs`, `scripts/hm-editor-smoke.mjs`,
the web tests and `scripts/check-unverified-boundary.sh`.

Final results in the main worktree on 2026-10-27:

- `lake build`: passed (736 jobs).
- `lake build fhm FHMEditorTests FHMCompatibility FHMExamples fhm_grammar`:
  passed (1653 jobs).
- `node scripts/scratch-hm-audit.mjs`: 17 files; 13 accepted, four expected
  rejections, no failures. The existing anonymous-hole playground is included.
- `node scripts/hm-editor-smoke.mjs`: 84/84 passed, including all 75 prior checks.
- `node --test editors/web/tests/*.test.mjs`: 35/35 passed, no skips, including
  three hover snapshots and the grammar/token-export tests.
- `bash scripts/check-unverified-boundary.sh` and `git diff --check`: passed.

The 19 changed modules in the default trusted import closure contain no
`sorry`, `admit`, `axiom` declarations or `native_decide` proof escapes.
The public production soundness, runtime erasure, completeness and principality
theorems, together with assignment matching, substitution, opening, closing and
allocation fidelity, were checked explicitly. They use only `propext`,
`Classical.choice` and `Quot.sound`; repeated-name equality needs none.
The optional `FHMExamples` library retains its pre-existing native concrete
demo canaries; its only edits are annotation-namespace references. No new
production proof depends on those canaries.

The parser, diagnostic wording and editor provenance joins remain unverified,
as before. Their operational regressions are covered by the executable tests.
The remaining compatibility artifacts are described above; there is no
unfinished production-source migration or change to implicit polymorphism.
