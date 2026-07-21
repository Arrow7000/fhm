# FHM editor extension (Cursor / VS Code)

## What you get (no Core / InferW / SurfaceLang changes)

- **Syntax highlighting** for `.fhm` via a TextMate grammar generated from `Surface.Lex`
- **Language config** — `--` / `{- -}` comments, brackets, auto-close
- **Parse diagnostics on `didChange`** (debounced) via `fhm_diagnose` — line/col from the existing parser
- **Type-on-hover** via **span + scope** (v3): binder def spans from the parse sidecar, lexical `scope` for use sites, inferred types (vals, λ params, pattern binds, lets in match/if arms). Def-site span hit first; else name + innermost scope. Type/ctor use-site deferred. Empty types show no hover — **no name-map fallback**. Tyvar params show `type variable (of T)`.

## Install via symlink (Cursor)

From the repo root:

```bash
scripts/gen-fhm-tmgrammar.sh          # once / when Lex keyword tables change
lake build fhm_diagnose               # for parse squiggles + hover types
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

Line/col are **1-based**, half-open `[start, end)` (same as the lexer). Missing `scope*` fields fall back to the def span (v2 compat).

## Tests

```bash
lake build FHMEditorTests   # #guard canaries in FHM/EditorSupportTests.lean
lake build fhm_diagnose
.lake/build/bin/fhm_diagnose scratch/live.fhm
```

## Regenerate grammar

```bash
scripts/gen-fhm-tmgrammar.sh
```

Keywords / ops / punct come from `keywordEntries`, `binOpSurfaces`, `punctSurfaces` in `FHM/Surface/Lex.lean`. Ident / comment / string patterns are TextMate approximations of the lexer.

## Settings

| Setting | Default | Meaning |
|---------|---------|---------|
| `fhm.diagnostics.enable` | `true` | Parse check on edit |
| `fhm.diagnostics.debounceMs` | `300` | Debounce for `didChange` |
| `fhm.diagnosePath` | `""` | Override path to `fhm_diagnose` |
