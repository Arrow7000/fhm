#!/usr/bin/env bash
# Regenerate editors/vscode/syntaxes/fhm.tmLanguage.json from Surface.Lex, and
# derive epl.tmLanguage.json from it (EPL has FHM's tokens, plus the `\0`
# escape).
set -euo pipefail
ROOT="$(cd "$(dirname "$0")/.." && pwd)"
cd "$ROOT"
OUT="$ROOT/editors/vscode/syntaxes/fhm.tmLanguage.json"
mkdir -p "$(dirname "$OUT")"
echo "building fhm_grammar…"
lake build fhm_grammar
echo "writing $OUT"
.lake/build/bin/fhm_grammar > "$OUT"
EPL_OUT="$ROOT/editors/vscode/syntaxes/epl.tmLanguage.json"
echo "writing $EPL_OUT"
python3 - "$OUT" "$EPL_OUT" <<'PY'
import json, sys
text = open(sys.argv[1], encoding="utf-8").read()
grammar = json.loads(text.replace('.fhm"', '.epl"').replace("source.fhm", "source.epl"))
grammar["name"] = "EPL"
repo = grammar["repository"]
repo["strings"]["patterns"][0]["match"] = repo["strings"]["patterns"][0]["match"].replace("[ntr", "[ntr0")
repo["chars"]["match"] = repo["chars"]["match"].replace("[ntr", "[ntr0")
with open(sys.argv[2], "w", encoding="utf-8") as out:
    json.dump(grammar, out, indent=1, ensure_ascii=False)
PY
echo "done."
