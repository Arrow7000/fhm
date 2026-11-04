# Editor error recovery

Open [`scratch/error-recovery.fhm`](../scratch/error-recovery.fhm) to see five
independent errors together: an argument mismatch, an annotation mismatch, an
unbound value, a type arity error and an infinite type. The two uses of `id`
retain their separate `Int → Int` and `Bool → Bool` hovers. Dependent bindings
show `type unknown (error in badArgument)` without additional cascade errors.

```sh
lake build fhm FHMEditorTests
.lake/build/bin/fhm diagnose scratch/error-recovery.fhm
node scripts/hm-recovery-smoke.mjs
```

The diagnose command returns failure status while supplying all recovered
diagnostics and hover symbols. Both editor clients already consume arrays of
diagnostics and ranged symbols. Execution still rejects the file.

## Recovery between groups

Fully checked programs use the existing whole-program inference and artifact
path. When that path rejects a source expression, the editor runs a recovery
pass over the parser's dependency-ordered top-level groups and then the final
expression. Declaration groups recover independently. When strict parsing fails, top-level
resynchronisation first recovers parseable source fragments.

Each group is lowered with provenance and checked by the same native contextual
inference worker. A successful group exports its actual group-exit schemes,
including validated complete signatures. Exports must be closed before they
enter the environment for later groups. Polymorphic instantiation, recursive
group checking, annotation checking and generalisation stay in the canonical
checker. The recovery pass checks each whole group once before descending into
rejected regions; it does not replay growing prefix programs or remove annotations.

A failed implementation contributes its native diagnostic. A complete valid
annotation can independently provide a declared editor interface. Recovery cuts
dependency edges at those interfaces and checks the remaining components using
the native worker. This includes unsigned members of an originally recursive
SCC: they can acquire actual inferred schemes conditional on a signed member's
declared contract.

A binding without a usable interface remains unavailable. Its transitive
dependants preserve the original failure cause, avoiding unbound-name cascades;
independent children still check. Annotations containing `_` or named holes,
invalid annotations, unavailable datatype dependencies and parser-quarantined
names never provide declared interfaces. Ordinary native success can still
resolve a partial annotation in an otherwise checkable residual component.

Healthy source slices keep inferred definition/use types, holes, documentation,
source locations and definition navigation. Unavailable slices retain lexical
binders and occurrences with a human-readable `type unknown (error in …)` label.
This label is editor presentation metadata; it supplies no type to inference.
Retaining lexical identity also prevents a failed local parameter from borrowing
the hover or definition target of a same-named outer binding.

The final expression is checked in the environment of successful groups if its
dependencies are available. Its type is omitted when it fails or is blocked.
Recovered diagnostics are displayed in source order.

## Scope and guarantees

Recovery lives under `FHM/Unverified/EditorRecovery.lean`. Its result contains
editor slices and diagnostics, not a checked executable whole program. `fhm run`,
`elaborateSafe` and the verified typing, completeness and safety interfaces retain
the strict acceptance path. Successful recovered slices call the native checker. Their environments may
contain declared interface assumptions, recorded separately from validated
implementations. Recovery adds no execution acceptance rules or guessed schemes.

Declaration recovery groups datatype dependencies and shared-name conflicts.
Each successful component is lowered and elaborated by the native workers;
failed components export no kinds or constructor signatures. Their dependent
declarations and values retain the original declaration cause without cascading
unknown-name errors. All definitions involved in a duplicate type/constructor
conflict are withheld. Valid forward and mutually recursive datatype references
continue checking. The prelude remains the validated initial environment.

[`scratch/error-recovery-declarations.fhm`](../scratch/error-recovery-declarations.fhm)
demonstrates independent declaration and value errors together. Unavailable
type and constructor references preserve separate namespaces for navigation.

Top-level parser recovery uses native item parsing and resumes at a later
`let` or `type` token on a new line at the failed header's indentation or less.
It retains original token positions; strings and comments cannot introduce fake
resynchronisation boundaries. Complete surviving token fragments are parsed by
the original grammar. Rejected headers withhold their known names, and duplicate
binding definitions are all quarantined. Malformed trailing syntax also
quarantines a softly parsed item prefix, so a broken declaration cannot export
an incomplete constructor signature. Failed final expressions have no synthetic
`Unit` program type. Documentation and namespace-specific navigation survive.

[`scratch/error-recovery-parser.fhm`](../scratch/error-recovery-parser.fhm)
demonstrates syntax, declaration and value errors together. Unparsed identifiers
mask outer hover/navigation fallbacks until their lexical identity is known.
The strict parser and runner still reject the original file.

Lexical recovery uses checkpoints from the original lexer. It keeps emitted
prefix tokens and resumes after closed malformed literals, invalid characters,
or recoverable layout errors. Code owning a lexical gap is quarantined even
when deleting the bad token would make it parse and typecheck. Multiple lexical
failures retain their original positions and dependency causes. Invalid comment
regions do not change the meaning of checked code outside them.

Unfinished strings consume their remaining tail; unfinished block comments keep
the prefix but do not promote comment text into declarations. Editor-only opaque
token markers keep literal/comment text out of identifier hover and navigation
fallbacks. These markers never enter the parser or inference.
[`scratch/error-recovery-lexical.fhm`](../scratch/error-recovery-lexical.fhm)
demonstrates lexical and ordinary type errors together, including healthy code
on both sides of closed bad tokens and before an unfinished comment.

## Recovery inside expressions and recursive groups

[`scratch/error-recovery-nested.fhm`](../scratch/error-recovery-nested.fhm)
shows seven errors together inside local bindings, match arms, mutually recursive
functions and a scoped `forall`. Healthy local definitions, parameters, pattern
captures and later polymorphic uses retain types and navigation. Fixing those
errors returns the entire program to the strict artifact and execution path.

`ExpressionRecovery` descends through rejected applications, pairs, lists,
conditionals, lambdas, matches and local lets. Every checked fragment is lowered
with its original annotations and checked in its actual lexical context by the
native worker. A failed expression yields no result type, even if its children
were checked. Independent errors still appear when another child refers to an
unavailable binding. For example, `1 unavailable` is certainly applying an `Int`
as a function; recovery reports that without inventing an argument type.

Successful local bindings export only their native schemes into the local
continuation. Captured outer parameters remain monomorphic, while ordinary local
let polymorphism still generalises under the real surrounding environment.
Successful substitutions constrain subsequent siblings and update earlier checked
hover artifacts. Substitutions from failed checks are discarded. Lexical scope
restoration preserves successful constraints, including when a shadowed outer
name shares a type variable with another visible binding.

Lambda parameters and patterns are checked separately when their bodies fail.
Match captures receive native types only when the scrutinee itself has a checked
type. An unavailable scrutinee keeps captures unavailable, while independent arm
bodies can still check. Rejected datatype dependencies suppress constructor and
pattern cascades. Administrative wrappers are marked separately from their
authored children, preserving real RHS occurrences without displaying synthetic
`Unit` result types or synthetic coverage errors.

Authored annotations supply expected constraints without becoming exported
binding schemes. Explicit type variables stay rigid and retain their authored
names. Every accepted contextual substitution is checked against saved outer
environments, preventing a local rigid variable from escaping. Safe constraints
on captured monotypes still survive a rejected local `forall`.

Whole recursive SCCs still use the original native check first. After rejection,
complete interfaces cut the cycle; unsigned residual SCCs retain native recursive
checking and generalisation. Complete members' implementations are checked against
their actual annotations using the recovered environment. Incomplete signatures
never grant polymorphic recursive calls through recovery assumptions.

[`scratch/error-recovery-interfaces.fhm`](../scratch/error-recovery-interfaces.fhm)
shows a broken signed recursive member, an inferred unsigned member, a caller
argument error and a polymorphic declared interface together. Signature hovers
say that the implementation is not fully validated. Caller hovers say which
unvalidated interfaces their types assume. Documentation and definition targets
remain attached to the original lexical definition.

The additive v3 JSON fields `typeStatus: "declared" | "conditional"` and
`typeAssumptions` preserve that distinction. Each assumption includes its binding
name and definition position, distinguishing shadowed names. A conditional final
expression also carries `programTypeAssumptions`. Successful constraints on shared
outer monotypes propagate interface provenance to affected artifacts. Unrelated
closed definitions keep their ordinary status. Fully valid programs use the
strict path and omit these recovery fields.

## Deliberate conservative boundaries

Recovery produces useful checked regions, rather than a repaired executable or
a type for every source node. Constraints that require a failed child's result
or a recursive member without a usable interface remain deferred. Recovery
does not invent provisional member schemes to enumerate every possible conflict
inside a rejected unsigned SCC. A rejected enclosing expression still has no
inferred result merely because independent nested definitions have interfaces.
Partial signatures and their holes can remain unavailable even when a healthy
parameter or nested binding has a type.
Native checks remain authoritative when the source is repaired.

The [shared partial parser](partial-parser.md) retains expression holes at known
grammar and delimiter boundaries, including arbitrary parenthesised expressions.
Malformed headers, annotations, patterns and ambiguous/unclosed syntax can still
quarantine their containing item and resume at a safe top-level header. No missing
token is inserted. Unfinished literals consume their tail.

Regression coverage is in the editor, declaration, expression, parser and lexer recovery
Lean test modules and `scripts/hm-recovery-smoke.mjs`, alongside the existing
HM/editor suites. It covers
multiple precise diagnostics, source-order/SCC reordering, closed polymorphic
exports, native residual recursion, dependency suppression, lexical shadowing,
unknown hovers, documentation/navigation, local polymorphism, shared monomorphic
constraints, scoped variables and escape prevention, multiple recursive-member
failures, fixing errors, and strict execution.

## Validation

The completed recovery work is checked with:

```sh
lake build FHM FHMUnverified FHMEditorTests FHMExamples fhm fhm_parser_audit
lake env lean scripts/check-source-proof-boundary.lean
bash scripts/check-unverified-boundary.sh
node scripts/hm-editor-smoke.mjs
node scripts/hm-recovery-smoke.mjs
node scripts/hm-interface-recovery-smoke.mjs
node scripts/parser-properties.mjs
node scripts/parser-recovery-properties.mjs
bash recursion-language-comparison/check.sh fhm
(cd editors/web && npm test)
```
