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

## The first recovery boundary

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
checker. The recovery pass checks each group once; it does not replay growing
prefix programs or remove annotations.

A failed group contributes its native diagnostic and exports nothing. Every
member of its syntactic SCC becomes unavailable, including members with complete
signatures. A later group that refers to an unavailable name is skipped. The
pass tracks the original failed groups through transitive dependencies so the
editor can explain the cause without producing unbound-name or type-error
cascades. Local parameters, patterns and nested bindings still shadow names
when dependencies are computed. Independent groups continue checking.

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
the strict acceptance path. Successful recovered slices call the native checker;
recovery does not add language acceptance rules or placeholder schemes.

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

Recovery within a recursive value group and nested expressions remains future
work. Lexer failures also remain strict at this stage: an unfinished string or
comment can contain apparent declaration keywords that must not become code.
An entire value SCC is withheld when a member fails, even when finer recovery
may be possible.

Regression coverage is in `FHM/Unverified/EditorRecoveryTests.lean` and
`scripts/hm-recovery-smoke.mjs`, alongside the existing HM/editor suites. It covers
multiple precise diagnostics, source-order/SCC reordering, closed polymorphic
exports, recursive-group atomicity, dependency suppression, lexical shadowing,
unknown hovers, documentation/navigation, fixing errors, and strict execution.
