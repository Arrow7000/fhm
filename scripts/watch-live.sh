#!/usr/bin/env bash
# Watch a .fhm file and re-run the full FHM pipeline on each save.
#
# Usage:
#   scripts/watch-live.sh                  # watches scratch/live.fhm
#   scripts/watch-live.sh path/to/foo.fhm
#
# Rebuilds fhm_live when the binary is missing or older than Lean sources
# under FHM/ / lakefile. After that, only the .fhm file is re-read on save.

set -euo pipefail

ROOT="$(cd "$(dirname "$0")/.." && pwd)"
cd "$ROOT"

# Cursor/CI often export NO_COLOR; prefer colour when this watch is on a real TTY.
if [[ -t 1 ]]; then
  export FORCE_COLOR=1
fi

FILE="${1:-scratch/live.fhm}"
BIN=".lake/build/bin/fhm_live"

if [[ ! -f "$FILE" ]]; then
  echo "error: file not found: $FILE" >&2
  exit 1
fi

needs_rebuild() {
  if [[ ! -x "$BIN" ]]; then
    return 0
  fi
  # Any newer Lean source / lakefile → rebuild so Pretty/Live edits take effect.
  local newest
  newest="$(find FHM lakefile.lean lake-manifest.json -type f \( -name '*.lean' -o -name 'lakefile.lean' -o -name 'lake-manifest.json' \) -newer "$BIN" 2>/dev/null | head -1)"
  [[ -n "$newest" ]]
}

if needs_rebuild; then
  echo "building fhm_live…"
  lake build fhm_live
fi

run_once() {
  if needs_rebuild; then
    echo "building fhm_live…"
    lake build fhm_live
  fi
  clear 2>/dev/null || true
  echo "═══ $FILE ═══ $(date '+%H:%M:%S')"
  echo
  # Don't abort the watch loop on pipeline failure (exit 1).
  set +e
  "$BIN" "$FILE"
  local code=$?
  set -e
  echo
  if [[ $code -eq 0 ]]; then
    echo "(ok)"
  else
    echo "(failed, exit $code)"
  fi
}

echo "watching $FILE — save to re-run (Ctrl-C to stop)"
run_once

if command -v entr >/dev/null 2>&1; then
  # Watch the .fhm file *and* Lean sources so Pretty/Live edits trigger a rebuild+rerun.
  {
    printf '%s\n' "$FILE"
    find FHM -name '*.lean' -type f 2>/dev/null
    printf '%s\n' lakefile.lean
  } | entr -c bash -c "
    cd '$ROOT'
    if [[ ! -x '$BIN' ]] || find FHM lakefile.lean -type f -name '*.lean' -newer '$BIN' 2>/dev/null | grep -q .; then
      echo 'building fhm_live…'
      lake build fhm_live
    fi
    '$BIN' '$FILE'
    echo
    echo \"(exit \$?)\"
  "
elif command -v fswatch >/dev/null 2>&1; then
  fswatch -o "$FILE" FHM | while read -r _; do
    run_once
  done
else
  echo "note: install 'entr' (preferred) or 'fswatch' for event-based watching;" >&2
  echo "      falling back to 0.5s mtime poll." >&2
  last=""
  while true; do
    now="$(stat -f '%m' "$FILE" 2>/dev/null || stat -c '%Y' "$FILE")"
    if [[ "$now" != "$last" ]] || needs_rebuild; then
      last="$now"
      run_once
    fi
    sleep 0.5
  done
fi
