# FHM editor extension (Cursor / VS Code)

## What you get (no Core / InferW / SurfaceLang changes)

- **Syntax highlighting** for `.fhm` via a TextMate grammar generated from `Surface.Lex`
- **Language config** — `--` / `{- -}` comments, brackets, auto-close
- **Parse diagnostics on `didChange`** (debounced) via `fhm_diagnose` — line/col from the existing parser
- **Type-on-hover** for value bindings (top-level and nested `let`/`let rec`) and type/ctor names — from the same `fhm_diagnose` JSON (`symbols` map). Hover the *name*, not arbitrary expressions.

## Install via symlink (Cursor)

From the repo root:

```bash
scripts/gen-fhm-tmgrammar.sh          # once / when Lex keyword tables change
lake build fhm_diagnose               # for parse squiggles + hover types
scripts/install-fhm-extension.sh      # ln -s into ~/.cursor/extensions
```

Then **Developer: Reload Window**.

The symlink target is `~/.cursor/extensions/fhm.fhm-0.0.1` → `editors/vscode/`. Grammar / `extension.js` edits apply after reload (no reinstall). Bump `version` in `package.json` if you change the folder name contract.

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
