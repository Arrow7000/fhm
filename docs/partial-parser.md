# Partial expression parsing

Open [the scratch showcase](../scratch/error-recovery-partial-parser.fhm) for
five syntax errors and an independent type error in one file. Local bindings,
parameters, match captures, documentation and later polymorphic uses survive.
Fixing the errors restores strict checking and execution.

## One handwritten grammar

`Surface/Parse.lean` keeps the existing productions and explicit combinators.
The internal expression/program productions take a `RecoveryMode`; the public
strict production names keep their original interfaces. There is no parser
generator or second grammar implementation.

Recovery is attached to expression boundaries. Parentheses delimit arbitrary
expressions, including lambdas, local lets, conditionals and matches. Each
production supplies its follow tokens: commas and matching closing delimiters,
`then`, `else`, `with`, `in`, or a match-arm separator. Synchronisation tracks
nested parentheses, brackets and braces. Delimiter-looking text in strings or
comments is already opaque to the lexer and cannot introduce a restart point.

Normal continuation tokens are distinct from caller-owned fences. For an `if`
condition, `then` is expected, while `else` is a fence: `if 6 else 7` must report
the missing separator at `else`, rather than consume it while searching for
`then`. Nested expression modes retain their callers' boundaries. Match scrutinees
similarly stop at an arm separator when `with` is missing. The owning production
still requires its separator; treating a token as a fence does not insert one.

A failed expression records its original error and token interval. Its owning
production consumes the boundary token; a zero-length missing operand therefore
cannot make a repetition loop without advancing. Mismatched delimiters and
unclosed regions fall back to the existing top-level recovery when their
ownership cannot be established. Top-level headers also stop an unmatched
opener from swallowing later declarations.

Diagnostics travel in the same Writer results as binders and source spans.
Backtracking discards the entire tentative result, including its diagnostics.
The parser retains its original alternative ordering and error-selection rules.
A soft datatype prefix is still quarantined if damaged trailing syntax belongs
to it; recovery cannot publish an incomplete constructor signature.

Explicit binding-structure rejections, such as duplicate pattern captures or
recursive pattern bindings, carry an internal error tag and bypass expression
hole recovery. Their containing item is quarantined with its primary diagnostic.
Otherwise a hole could stop at that local binding's `in`, strand the separator,
and replace the useful header error with a later generic syntax error. The tag
uses the existing parser error tree and does not appear in public messages or
change strict alternative selection.

## Partial trees and typing

`PartialExpr` and `PartialProgram` pair a Surface-shaped skeleton with explicit
`ExprHole` leaves. Each hole carries its diagnostic, original span and token
interval. Its skeleton identity uses a reserved name that source identifiers
cannot spell. This keeps the existing grammar's construction logic shared;
the wrapper is an editor result, not an accepted Surface program.

Hole identities become unavailable dependencies before semantic recovery.
Only hole-free fragments reach native lowering/inference. Structural guards at
both inference entry points reject any accidental hole-bearing input. No hole
receives a placeholder type or a synthetic `Unit` value. A complete annotation
on a definition whose own body has a syntax hole does not publish an interface.
`PartialProgram.toStrict` rejects both recorded holes and orphaned hole leaves.

Rejected token regions mask hover/navigation fallback for identifiers whose
lexical role is unknown. Parsed parameters and bindings retain their real
identities, so healthy inner uses do not borrow same-named outer definitions.
Independent fragments use the existing contextual recovery and constraint
threading described in [editor recovery](error-recovery.md).

## Verification

The verification executable is opt-in:

```sh
lake build fhm fhm_parser_audit FHMEditorTests
node scripts/parser-properties.mjs
node scripts/parser-recovery-properties.mjs
```

For the complete editor and recovery regression suite, including these checks,
run `bash scripts/check-editor-recovery.sh`. CI runs the same command.

Verification combines several independent checks:

- Before changing the parser, commit `464546a` recorded 3,384 strict results in
  `scripts/fixtures/parser-before-partial.json`. Their fingerprints cover full
  structural ASTs, binders, spans, exact error messages and error locations.
  The corpus includes seeded trees, comments, deletions, damaged programs,
  declarations, annotations, patterns, layout, recursion and Unicode.
- A separate JavaScript AST generator/printer checks 2,640 expression parses
  against independently constructed expected ASTs. It covers application,
  infix desugaring, cons, pairs, lists, lambdas, local bindings, conditionals and
  matches. It does not use the parser's pretty-printer as an oracle.
- Across 5,624 inputs, strict success must give the identical editor AST and
  metadata with no holes. An editor success on strict-invalid input must retain
  errors and fail strict projection. Hole identities and ranges are audited.
  Complete retained source islands are reparsed with the strict grammar using
  their original token intervals and compared structurally. Known desugared
  internal nodes are audited through their actual source children instead.
- Token fuzzing and seeded mutations exercise malformed boundaries and parser
  termination under a batch timeout. Failures print the deterministic case ID
  and original source for reproduction.
- 120 generated damage/repair programs exercise the actual diagnose and editor
  resolver APIs. They verify lexical shadowing, healthy types, documentation,
  navigation, absence of internal/lowering cascades, strict execution rejection,
  and full recovery after repair. Another 96 deletion cases check missing
  `then`/`with` boundaries across nesting, wrappers and layout, including the
  exact scratch-file edit that originally skipped past `else`. Additional cases
  cover unmatched/mismatched delimiters, later top-level headers and UTF-16 positions.
  A further 36 damage/repair cases check primary binding-structure errors across
  expression wrappers, dependent withholding and healthy later declarations.
- `parseExprPartial_of_strict` and `parseProgramTokensPartial_of_strict` prove
  exact preservation of every successful strict result at the API boundary,
  including sidecars. This follows from the strict-success fast path, without
  formalising the parser combinators or introducing a grammar specification.

The frozen baseline is intentionally not regenerated during normal tests.
`--record-baseline` is an explicit maintenance operation; a grammar change that
updates it requires reviewing the changed expectations. The file also records
the SHA-256 of the original parser source.

These tests are bounded regression checks, not a proof of the full grammar.
They complement the exact compatibility theorems and the existing build,
semantic, editor, recursion and proof-boundary suites.

## Current boundaries

Recovery constructs holes for expressions. Malformed type annotations, patterns,
binding headers and datatype syntax retain the existing conservative item
quarantine; they do not acquire guessed binders, types or constructor fields.
Unfinished lexical literals still consume their tail. Ambiguous or unmatched
syntax may quarantine a larger region, and recovery does not promise to retain
every parseable substring. No missing delimiter is inserted and no recovered
program can bypass strict execution checks.
