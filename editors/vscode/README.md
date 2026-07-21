# FHM editor extension (Cursor / VS Code)

## What you get (no Core / InferW / SurfaceLang changes)

- **Syntax highlighting** for `.fhm` via a TextMate grammar generated from `Surface.Lex`
- **Language config** — `--` / `{- -}` comments, brackets, auto-close
- **Parse diagnostics on `didChange`** (debounced) via `fhm_diagnose` — line/col from the existing parser
- **Type-on-hover** via **span containment** (v2): binder locations from the parse sidecar + inferred types (vals, λ params via expected-type peel / `.app` domain, pattern binds via `patBindTys`). Shadowed names resolve to the innermost binder under the cursor. Empty types show no hover — **no name-map fallback**.

## Install via symlink (Cursor)

From the repo root:

```bash
scripts/gen-fhm-tmgrammar.sh          # once / when Lex keyword tables change
lake build fhm_diagnose               # for parse squiggles + hover types
scripts/install-fhm-extension.sh      # ln -s into ~/.cursor/extensions
```

Then **Developer: Reload Window**.

The symlink target is `~/.cursor/extensions/fhm.fhm-0.0.1` → `editors/vscode/`. Grammar / `extension.js` edits apply after reload (no reinstall). Bump `version` in `package.json` if you change the folder name contract.

## Diagnose JSON (v2)

```json
{
  "version": 2,
  "diagnostics": [],
  "symbols": [
    {"name":"xs","kind":"param","type":"…","startLine":1,"startCol":10,"endLine":1,"endCol":12},
    {"name":"xs","kind":"val","type":"Int","startLine":2,"startCol":5,"endLine":2,"endCol":7}
  ],
  "programTy": "…"
}
```

Line/col are **1-based**, half-open `[start, end)` (same as the lexer).

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
