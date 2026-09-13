# Scratch HM audit (non-`polyrec` corpus)

Run on 2026-09-13 using `.lake/build/bin/fhm`.

## HM / editor payload

`fhm diagnose` returned a nonempty program type and **no diagnostics** for every
non-`polyrec` `scratch/*.fhm` after rewriting `scratch/live.fhm`. Before that
rewrite, `live.fhm` alone reported:

```
typechecking failed in `listLength` (ascribed Int; RHS also fails without ascription)
```

The cause was the unsupported head-binder surface form. It now uses explicit
schemes plus ordinary lambdas and both `diagnose` and ordinary `run` succeed
(`17`). The deliberately named `*-fail.fhm` files do not produce HM editor
errors: `diagnose` is HM-only and intentionally erases/ignores BL constraints.

The editor payload does emit nested `expr` symbols. For example in `live.fhm`
the final call has spans/types `78:3–16 : Int → Int → Int`, `78:6–16 : Int →
Int`, `78:11–16 : Int`, and the inner application `78:11–14 : Int → Int`.
Hover is therefore available on an expression's *source span*, not arbitrary
whitespace outside it; nested spans choose the smallest containing symbol.

## `run --bl` cross-check

These complete successfully: `bl-ascribed-list-lam`, `bl-cons-only`,
`bl-hole-ok`, `bl-live`, `bl-nil-only`, `bl-r1-pin-env`,
`bl-r2-head-binder`, `bl-r4-pair-peel`, `bl-scheme-id`, and `bl-synth-ok`.
Notably, the current BL runner accepts the head-binder canary `bl-r2-head-binder`.

Expected intentional bounds rejections: `bl-hole-fail`, `bl-nil-only-fail`,
`bl-r1-pin-env-fail`, and `bl-synth-fail`.

The following are documented as success/demo cases but currently fail only in
the Bounds layer (not an HM parse/lower/type diagnostic):

| File | Current Bounds-only result |
| --- | --- |
| `bl-join-if` | `letRec member needs scheme ascription from Infer` |
| `bl-r3-canary` | same |
| `bl-r3-mid-fail` | same, rather than its intended non-unique-escape canary |
| `bl-showcase` | same |
| `bl-small-showcase` | same |
| `bl-t5-head-tail` | same |
| `bl-stdlib` | `flatMap` ascription mismatch |
| `bl-t3-option` | `someList` ascription: `unbound var 3` |
| `bl-unascribed-list-lam` | exhaustiveness error for an apparently exhaustive List match |

Those are not evidence of a regression in the HM-only editor path, but they do
mean the corresponding BL examples are not executable evidence of their claims
today. No Bounds/metatheory code was changed by this audit.

## Hover rendering defect observed before the display repair

Definition hovers correctly preserve their explicit schemes, e.g.
`listLength : ∀ a. List a → Int`, but body/use-site hover symbols in the same
annotated definitions render inference metas such as `List ?j`, `?t64 → ?t63`,
and `?t89`. This was an editor presentation defect, not an HM type error.

The parent repair adds `FHM/Unverified/HMDisplay.lean`: source signature names
are retained in declarations and genuine scoped/skolem payloads, while
synthesized variables receive compact, consistent alpha names within their RHS.
A bijective variable-name correspondence also preserves signature names in a
recursive RHS when its synthesized type has the corresponding shape. It does
not invent composite signature domains or conflate independently synthesized
variables for a less-general annotation ceiling.

## Reproduce the completed HM audit

```sh
lake build FHMEditorTests fhm
node scripts/scratch-hm-audit.mjs
node scripts/hm-editor-smoke.mjs
node editors/web/scripts/hover-sweep.mjs --all --safe
```

The original 35-file corpus has 27 HM successes and eight expected D2/scoped
syntax rejections. With the new `scratch/hm-hover.fhm` playground, the repeatable
audit covers 36 files: 28 successes, eight expected rejections, zero unexpected
diagnostics or debug metavariable names in successful hover payloads.

For expression hover, use a successfully checked file and hover **inside** its
half-open expression span: the space in `keep [1, 2]`, or the space after the
list comma, works. Exact token/binder spans win; otherwise the smallest authored
expression containing the position supplies the type. Whitespace between
statements or outside the expression is not a target. Failed programs currently
return diagnostics without partial hover recovery. After rebuilding the binary,
reload the editor window or edit the buffer so its cached diagnose result refreshes.

The VS Code extension's refresh lifecycle was also repaired: disabling diagnostic
markers no longer disables hover inference, obsolete worker responses cannot
replace newer snapshots, and edit-invalidated spans are not served while a new
diagnose request is pending. Reproduce its mocked integration checks with
`node editors/vscode/test/lifecycle-regression.cjs`.

“Head binders unsupported” is shorthand for the **scoped type-variable** case;
concrete monomorphic head parameters already work (for example the HM-clean
`bl-r2-head-binder.fhm`). The live demo now uses ordinary lambdas throughout so
it does not rely on that distinction.
