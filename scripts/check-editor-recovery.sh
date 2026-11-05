#!/usr/bin/env bash
set -euo pipefail

cd "$(dirname "$0")/.."

# Keep the operational editor checks opt-in locally, and run the same suite in CI.
# Node's built-in test runner needs no npm install or browser downloads.
lake build FHMUnverified FHMEditorTests fhm fhm_parser_audit fhm_grammar
node scripts/parser-properties.mjs
node scripts/parser-recovery-properties.mjs
node scripts/hm-editor-smoke.mjs
node scripts/hm-recovery-smoke.mjs
node scripts/hm-interface-recovery-smoke.mjs
bash recursion-language-comparison/check.sh fhm
(cd editors/web && npm test)
