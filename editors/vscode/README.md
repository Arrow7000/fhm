# FHM editor extension (Cursor / VS Code)

## What you get (no Core / InferW / SurfaceLang changes)

- **Syntax highlighting** for `.fhm` via a TextMate grammar generated from `Surface.Lex`
- **Language config** — `--` / `/- -/` comments, brackets, auto-close
- **Parse, lowering, and HM diagnostics on edit** (debounced) via `fhm diagnose`.
- **Type-on-hover** (v3) from actual inferred artifacts and a separate source/Core provenance map. Definitions show validated declarations or inferred schemes; occurrences show independently instantiated monotypes. Lambda/pattern binders and authored compound expressions are covered. Exact spans win before name/scope fallback. Comments and indentation have no hover; keywords and punctuation show the expression they belong to.
- **Doc comments** (`--- …` lines or `/-- … -/`) before a `let`, `type` or constructor appear under the signature when hovering the definition or any use of it.
- **Go to definition** for values, parameters, pattern variables, types, constructors and type variables (not for built-ins, which have no source location).

Scoped head-type-variable sugar is still unsupported; prefer explicit schemes and ordinary lambdas.

## Install via symlink (Cursor or VS Code)

From the repo root:

```bash
scripts/gen-fhm-tmgrammar.sh          # once / when Lex keyword tables change
lake build fhm               # for parse squiggles + hover types
scripts/install-cursor-extension.sh   # or scripts/install-vscode-extension.sh
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
