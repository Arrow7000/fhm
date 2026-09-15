# FHM editor extension (Cursor / VS Code)

## What you get (no Core / InferW / SurfaceLang changes)

- **Syntax highlighting** for `.fhm` via a TextMate grammar generated from `Surface.Lex`
- **Language config** — `--` / `{- -}` comments, brackets, auto-close
- **Parse, lowering, HM and canonical Bounds diagnostics on edit** (debounced) via `fhm diagnose`.
- **Type-on-hover** (v3) from actual inferred artifacts and a separate source/Core provenance map. Definitions show validated declarations or inferred schemes; occurrences show independently instantiated monotypes. Lambda/pattern binders and authored compound expressions are covered. Exact spans win before name/scope fallback.
- **Checker modes:** `auto` (the default) runs canonical Bounds checking when the parsed program contains `BL`; `hm` retains Path-R bounds blindness and displays `BL` as `List`; `bl` always requests the canonical checker. Scoped head-type-variable sugar is still unsupported; prefer explicit schemes and ordinary lambdas.

## Install via symlink (Cursor)

From the repo root:

```bash
scripts/gen-fhm-tmgrammar.sh          # once / when Lex keyword tables change
lake build fhm               # for parse squiggles + hover types
scripts/install-fhm-extension.sh      # ln -s into ~/.cursor/extensions
```

Then **Developer: Reload Window**.

The symlink target is `~/.cursor/extensions/fhm.fhm-0.0.1` → `editors/vscode/`. Grammar / `extension.js` edits apply after reload (no reinstall). Bump `version` in `package.json` if you change the folder name contract.

## Diagnose JSON (v3)

```json
{
  "version": 3,
  "diagnostics": [],
  "symbols": [
    {
      "name": "xs",
      "kind": "param",
      "type": "…",
      "startLine": 1,
      "startCol": 10,
      "endLine": 1,
      "endCol": 12,
      "scopeStartLine": 1,
      "scopeStartCol": 13,
      "scopeEndLine": 1,
      "scopeEndCol": 20
    }
  ],
  "programTy": "…"
}
```

Line/col are **1-based UTF-16**, half-open `[start, end)` (same as the lexer/editor). Missing `scope*` fields fall back to the def span (v2 compat).

## Tests

```bash
lake build FHMEditorTests   # #guard canaries in FHM/Unverified/EditorSupportTests.lean
lake build fhm
.lake/build/bin/fhm diagnose editors/web/fixtures/hover-rich.fhm
.lake/build/bin/fhm diagnose --bl scratch/bl-live.fhm
node scripts/hm-editor-smoke.mjs
node scripts/scratch-hm-audit.mjs
node editors/vscode/test/lifecycle-regression.cjs
```

## Regenerate grammar

```bash
scripts/gen-fhm-tmgrammar.sh
```

Keywords / ops / punct come from `keywordEntries`, `binOpSurfaces`, `punctSurfaces` in the total `FHM/Surface/Token.lean` module. Ident / comment / string patterns are TextMate approximations of the operational lexer in `FHM/Unverified/Surface/Lex.lean`.

## Settings

| Setting | Default | Meaning |
|---------|---------|---------|
| `fhm.diagnostics.enable` | `true` | Show diagnostics; hover inference still runs when disabled |
| `fhm.diagnostics.debounceMs` | `300` | Debounce for `didChange` |
| `fhm.diagnosePath` | `""` | Override path to `fhm` binary. Empty = search workspace `.lake/build/bin/fhm`. |
| `fhm.boundsMode` | `"auto"` | `auto`, bounds-blind `hm`, or canonical `bl` checking and hover. |
