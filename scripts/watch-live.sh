#!/usr/bin/env bash
# Watch a .fhm file and re-run the full FHM pipeline on each save.
#
# Usage:
#   scripts/watch-live.sh                  # watches scratch/live.fhm
#   scripts/watch-live.sh path/to/foo.fhm
#
# Rebuilds fhm at startup (and when a pipeline Lean source changes) if
# the binary is missing or stale. Saving the .fhm file only re-runs the exe —
# it does not scan unrelated FHM/*.lean scratch files.

set -euo pipefail

ROOT="$(cd "$(dirname "$0")/.." && pwd)"
cd "$ROOT"

# Cursor/CI often export NO_COLOR; prefer colour when this watch is on a real TTY.
if [[ -t 1 ]]; then
  export FORCE_COLOR=1
fi

FILE="${1:-scratch/live.fhm}"
BIN=".lake/build/bin/fhm"

# Lean sources that actually feed `fhm` (not scratch modules under FHM/).
PIPELINE_SRCS=(
  FHM/PipelineShared.lean
  FHM/Cli.lean
  FHM/Live.lean
  FHM/Diagnose.lean
  FHM/Pretty.lean
  FHM/EvaluateUnsafe.lean
  FHM/SurfaceBridge.lean
  FHM/InferW.lean
  FHM/Core.lean
  FHM/SurfaceLang.lean
  FHM/Surface
  lakefile.lean
)

if [[ ! -f "$FILE" ]]; then
  echo "error: file not found: $FILE" >&2
  exit 1
fi

needs_rebuild() {
  if [[ ! -x "$BIN" ]]; then
    return 0
  fi
  local newest
  newest="$(find "${PIPELINE_SRCS[@]}" -type f -name '*.lean' -newer "$BIN" 2>/dev/null | head -1)"
  [[ -n "$newest" ]]
}

ensure_built() {
  if needs_rebuild; then
    echo "building fhm…"
    lake build fhm
  fi
}

run_once() {
  ensure_built
  clear 2>/dev/null || true
  echo "═══ $FILE ═══ $(date '+%H:%M:%S')"
  echo
  # Don't abort the watch loop on pipeline failure (exit 1).
  set +e
  "$BIN" "$FILE"
  local code=$?
  set -e
  # echo
  if [[ $code -eq 0 ]]; then
    # echo "(ok)"
  :
  else
    echo "(failed, exit $code)"
  fi
}

echo "watching $FILE — save to re-run (Ctrl-C to stop)"
run_once

if command -v entr >/dev/null 2>&1; then
  # Watch the .fhm file and pipeline Lean sources only (not all of FHM/).
  {
    printf '%s\n' "$FILE"
    find "${PIPELINE_SRCS[@]}" -type f -name '*.lean' 2>/dev/null
  } | entr -c bash -c "
    cd '$ROOT'
    BIN='$BIN'
    FILE='$FILE'
    needs_rebuild() {
      if [[ ! -x \"\$BIN\" ]]; then return 0; fi
      local newest
      newest=\"\$(find ${PIPELINE_SRCS[*]} -type f -name '*.lean' -newer \"\$BIN\" 2>/dev/null | head -1)\"
      [[ -n \"\$newest\" ]]
    }
    if needs_rebuild; then
      echo 'building fhm…'
      lake build fhm
    fi
    \"\$BIN\" \"\$FILE\"
    echo
    echo \"(exit \$?)\"
  "
elif command -v fswatch >/dev/null 2>&1; then
  fswatch -o "$FILE" "${PIPELINE_SRCS[@]}" | while read -r _; do
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
