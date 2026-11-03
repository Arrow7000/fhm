# Typed errors

The first native typed-error worker is the rigidity-aware unifier in
`FHM/InferenceFoundations.lean`:

```lean
unifyResultK (K : List Nat) (a b : Ty) :
  Except UnifyError { S : Subst // UnifyRel a b S ∧ (∀ p ∈ S, p.1 ∉ K) }
```

`unifyListResultK` handles type-argument lists with the corresponding list
derivation. `unifyResult` exposes the empty-rigid-set operation without its
proof payload. These are the only executable unification workers. Existing
`unifyCoreK`, `unifyListCoreK`, `unifyCore`, and `unify` callers use projections
of the same implementation that discard failure data.

`UnifyError` retains structured operands at the failing step:

| Constructor | Meaning |
| --- | --- |
| `mismatch left right` | Incompatible type shapes or names, or unopened bound variables |
| `rigidVariable varId other` | Solving the constraint would require assigning a protected variable |
| `occursCheck varId within` | A flexible variable occurs in the type it would have to equal |
| `arityMismatch leftRemaining rightRemaining` | One type-argument list ended before the other |

Earlier substitutions have already been applied to these operands. List-length
errors retain the unmatched suffixes, rather than claiming their lengths are
the original constructor arities. The first failure is propagated unchanged;
there is no source span or human-facing message in the worker's error type.

Successful results retain the existing proof of unification and preservation of
rigid variables. `unifyResultK_complete` proves success whenever locally closed
inputs admit a locally closed, rigid-preserving unifier.
`unifyResultK_error_not_unifies` gives the corresponding rejection guarantee.
The existing inference soundness/completeness API continues to use `Option`.

Application diagnostics now use native failure reasons instead of probing
rejected expressions. For example, `\(f : ?a -> ?a) -> f f` reports an infinite
type even though `f` already has an arrow type. Errors in recursive RHSs and
under unrelated recursive wrappers retain their precise application spans.

Annotation checking in `FHM/InferW.lean` now follows the same arrangement:
`seedResult`, `checkLetResult` and `checkSignatureResult` are the native workers;
`seed`, `checkLet` and `checkSignature` project their results to `Option` for
existing inference callers. Successful results still carry `Seed`, `LetCheck`
and `SignatureCheck` certificates. Their `...Result_complete_source` theorems in
`FHM/Completeness.lean` expose native success under the existing source
completeness premises.

`AnnotationError` distinguishes:

| Constructor | Meaning |
| --- | --- |
| `invalidBoundVariables body binderCount` | The checked type has bound variables outside the permitted binder depth |
| `outOfScopeVariables varIds` | These authored free type variables are outside the permitted scope |
| `unification error` | The original `UnifyError`, preserved with its substituted operands |
| `expectedMonotype` | A signature was passed to the monotype annotation worker |
| `expectedSignature` | A monotype annotation was passed to the signature worker |

The error type lives in `FHM/AnnotationAllocation.lean`, where recursive setup
can also use it without importing inference. Standalone `allocateResult` and
`checkAnnotationResult` preserve native failures there too; their older APIs are
`Option` projections.

The last two cases describe use of the wrong internal worker. They do not add
language restrictions. Validation order and hole allocation remain the same,
including the whole-annotation `_` shortcut, annotation-local named sharing,
flexible outer variables and rigid written forall variables. Escaping abstract
variables are checked by the surrounding inference workers and now have native
failure reasons there.

Expression inference and its mutually recursive branch, component, strata and
signed-member workers now return `Except InferError`. `InferError` separates a
logical `CorePath` from `InferErrorReason`. Reasons retain application operands
and annotation-local names, annotation/unification failures, constructor and
pattern failures, invalid request boundaries, escaping type variables, and
recursive-state failures. Recursive helper results retain the affected member
or shape index. `InferError.below` adds an enclosing expression edge while
preserving the failure data.

The public native APIs are `inferWithTypesResult`, `principalTypeResult`,
`typecheckResult`, and the bundled-request result APIs. Existing `Option` APIs
project the same workers. `TypedResult` projection laws and the explicit
`typed_result_projection` simp set let the existing completeness arguments
reason about that exact projection. The typing rules and successful inference
certificates remain unchanged.

Native public inference has source soundness, completeness, principality and
the full source-typing characterization. `inferWithTypesResult_error_not_typing`
proves that a native rejection rules out every declarative source type. These
theorems are included in the proof-dependency audit.

The editor and runner call `inferWithProvenanceResult`. Application presentation
reads its native failure directly; the old application probe has been removed.
Other diagnostic presentation still has binding-level fallbacks to migrate.

The next migration steps are:

1. Give declaration and expression lowering their own failure data and source
   identity, so lowering failures do not need a diagnostic reconstruction.
2. Finish migrating operational provenance failures and the remaining
   declaration, lowering and type-error presentation fallbacks to native failure
   data. Preserve useful annotation mismatch wording without rechecking source.

Error recovery remains a separate follow-up:

1. Make the editor collect failures at binding/SCC boundaries and continue
   checking independent groups. Define how dependent failures suppress cascades
   before adding placeholder types. The safe elaboration path continues to
   require a fully checked program.

Typed failures are the prerequisite for recovery; this slice still stops at the
first failure. Regression coverage lives in `FHM/UnificationTests.lean`,
`FHM/AnnotationErrorTests.lean`, `FHM/InferenceErrorTests.lean`, the editor tests,
and `scripts/hm-editor-smoke.mjs`.
