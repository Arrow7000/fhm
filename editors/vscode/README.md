# FHM editor extension (Cursor / VS Code)

## What you get (no Core / InferW / SurfaceLang changes)

- **Syntax highlighting** for `.fhm` via a TextMate grammar generated from `Surface.Lex`
- **Language config** — `--` / `{- -}` comments, brackets, auto-close
- **Parse diagnostics on `didChange`** (debounced) via `fhm diagnose` — line/col from the existing parser
- **Type-on-hover** via **span + scope** (v3): one structural walk emits complete symbols (def span + type + lexical scope together) in parse/source order; top schemes are a name map from inference (SCC reorder cannot desync). Lit/op tokens (incl. unit `()`), type/ctor uses, type-decl tyvar uses (decl-hull scope), and scheme-ann `{a}` tyvar uses included. Def-site / token span hit first; else name + innermost scope. Empty types show no hover — **no name-map fallback**. Tyvar params show `type variable (of T)` / `type variable (scheme binder)`.

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

Line/col are **1-based**, half-open `[start, end)` (same as the lexer). Missing `scope*` fields fall back to the def span (v2 compat).

## Tests

```bash
lake build FHMEditorTests   # #guard canaries in FHM/EditorSupportTests.lean
lake build fhm
.lake/build/bin/fhm diagnose scratch/live.fhm
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
| `fhm.diagnosePath` | `""` | Override path to `fhm` binary. Empty = search workspace `.lake/build/bin/fhm`. |
