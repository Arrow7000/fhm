#!/usr/bin/env bash
# Regenerate editors/vscode/syntaxes/fhm.tmLanguage.json from Surface.Lex.
set -euo pipefail
ROOT="$(cd "$(dirname "$0")/.." && pwd)"
cd "$ROOT"
OUT="$ROOT/editors/vscode/syntaxes/fhm.tmLanguage.json"
mkdir -p "$(dirname "$OUT")"
echo "building fhm_grammar…"
lake build fhm_grammar
echo "writing $OUT"
.lake/build/bin/fhm_grammar > "$OUT"
echo "done."
