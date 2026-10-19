# FHM editor extension (Cursor / VS Code)

## What you get

- **Syntax highlighting** for `.fhm` via a TextMate grammar generated from `Surface.Lex`
- **Language config** — `--` / `/- -/` comments, brackets, auto-close
- **Parse, lowering, and HM diagnostics on edit** (debounced) via `fhm diagnose`.
- **Type-on-hover** (v3) from actual inferred artifacts and a separate source/Core provenance map. Definitions show validated declarations or inferred schemes; occurrences show independently instantiated monotypes. Lambda/pattern binders and authored compound expressions are covered. Exact spans win before name/scope fallback. Comments and indentation have no hover; keywords and punctuation show the expression they belong to.
- **Doc comments** (`--- …` lines or `/-- … -/`) before a `let`, `type` or constructor appear under the signature when hovering the definition or any use of it.
- **Go to definition** for values, parameters, pattern variables, types, constructors and type variables (not for built-ins, which have no source location).

The extension registers VS Code hover, definition, and diagnostic providers directly. It sends the current buffer to `fhm diagnose` and uses the returned type artifacts and source spans. There is no separate LSP server or JSON-RPC transport.

Anonymous type holes work through this path, including structured annotations, partial `forall` signatures, patterns, and recursive definitions. Hover directly on an annotation's `_` to see its inferred type:

```fhm
let id = \(x : _) -> x
(id 1, id True)
```

Here `_` hovers as `a`; it has no declaration target. Fixed annotation structure still constrains the program: `let f : Int -> _ = \x -> x` followed by `f True` reports a type mismatch. Pattern wildcards are separate from type holes.

Let heads also support scoped type binders and typed or untyped parameters:

```fhm
let keep {item unused} (x : item) y : _ = (x,y)
keep 1 True
```

Here the result hole hovers as `(item, a)`, and parameter uses resolve to their head definitions. The annotation after the parameters is the return type. Missing annotations are inferred without creating source hole tokens. Authored forall names retain their order, including unused binders. A fully written signature permits polymorphic recursive calls; an omitted or holeful part keeps calls within its recursive component monomorphic.

## Install via symlink (Cursor or VS Code)

From the repo root:

```bash
scripts/gen-fhm-tmgrammar.sh          # once / when Lex keyword tables change
lake build fhm                       # for diagnostics + hover types
scripts/install-cursor-extension.sh   # or scripts/install-vscode-extension.sh
```

Then **Developer: Reload Window**.

The symlink target is `~/.cursor/extensions/fhm.fhm-0.0.1` → `editors/vscode/`. Grammar / `extension.js` edits apply after reload (no reinstall). Bump `version` in `package.json` if you change the folder name contract.

Rebuild `fhm` after compiler changes. By default the extension uses the open workspace's `.lake/build/bin/fhm`; for another workspace, set `fhm.diagnosePath` to the rebuilt binary's absolute path.

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
node editors/vscode/test/anonymous-holes-integration.cjs
```

The lifecycle regression mocks the backend to test races. The anonymous-hole integration test uses the actual extension providers and real `fhm diagnose` processes, with only the VS Code host API simulated. It checks precise hole hovers, edits, diagnostics, definition lookup, recursive holes, copied match fallbacks, top-level pattern annotations, and scoped head parameters. It does not launch an editor window or test an LSP protocol.

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
