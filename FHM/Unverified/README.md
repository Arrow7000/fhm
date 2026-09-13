# Operational, unverified code

This directory contains the production code outside the verified language
metatheory: parsing and lexing, editor/provenance plumbing, CLI entry points,
the unbounded evaluator, Z3 output parsing, and the experimental BL pretty-printer.
Some supporting modules here are total; they live alongside the operational
pipeline whose behavior is not established by the headline HM theorems.

In particular, Lean `partial def` permits executable recursion without a
termination proof. It is not a transparent logical definition on which the
verified progress, preservation, completeness, or principality proofs depend.
Moving code here makes that boundary explicit; it does not prove the parser,
editor pipeline, solver subprocess protocol, or unbounded evaluator correct.

The total token vocabulary, character classes, spelling tables, and token/span
lookup helpers live in `FHM/Surface/Token.lean`. They retain the `Surface.Lex`
namespace, while the operational lexer/parser retain `Surface.Lex` and
`Surface.Parse`. Total source-span data lives in `FHM/Surface/Span.lean` and
imports only the token module, not the partial lexer.

The default `lake build` target remains the verified `FHM` library and does not
import these modules. Operational builds remain available through
`lake build FHMUnverified`, `lake build FHMEditorTests`, `lake build fhm`, and
`lake build fhm_grammar`. The optional Bounds and Z3 targets include operational
plumbing; their existing behavior and proof statements are unchanged.

Run `bash scripts/check-unverified-boundary.sh` to check that all production
partial declarations remain here and that the default library's local import
closure stays outside this directory. Historical design briefs retain their
original paths; active imports and commands use the new paths.
