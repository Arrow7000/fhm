#!/usr/bin/env bash
# Local E2E gate for bounds demos under --bl.
# Usage: from repo root:  ./scripts/bl-e2e-smoke.sh
# Expects: lake build fhm  (uses .lake/build/bin/fhm)

set -euo pipefail
ROOT="$(cd "$(dirname "$0")/.." && pwd)"
cd "$ROOT"
FHM="${FHM:-.lake/build/bin/fhm}"

if [[ ! -x "$FHM" ]]; then
  echo "missing $FHM — run: lake build fhm" >&2
  exit 1
fi

pass=0
fail=0

run_ok() {
  local f="$1"
  if out="$("$FHM" run --bl "$f" 2>&1)"; then
    echo "  OK  $f"
    pass=$((pass + 1))
  else
    echo "  FAIL (expected green) $f"
    echo "$out" | tail -5
    fail=$((fail + 1))
  fi
}

run_err() {
  local f="$1"
  local needle="${2:-}"
  if out="$("$FHM" run --bl "$f" 2>&1)"; then
    echo "  FAIL (expected error) $f"
    echo "$out" | tail -3
    fail=$((fail + 1))
  else
    if [[ -n "$needle" ]] && ! grep -q "$needle" <<<"$out"; then
      echo "  FAIL (wrong error, want /$needle/) $f"
      echo "$out" | tail -5
      fail=$((fail + 1))
    else
      echo "  OK  $f (red as expected)"
      pass=$((pass + 1))
    fi
  fi
}

echo "== green =="
for f in \
  scratch/bl-stdlib.fhm \
  scratch/bl-showcase.fhm \
  scratch/bl-r3-canary.fhm \
  scratch/bl-t5-head-tail.fhm \
  scratch/bl-t3-option.fhm \
  scratch/bl-r4-pair-peel.fhm \
  scratch/bl-join-if.fhm \
  scratch/bl-r1-pin-env.fhm \
  scratch/bl-r2-head-binder.fhm \
  scratch/bl-scheme-id.fhm \
  scratch/bl-hole-ok.fhm \
  scratch/bl-synth-ok.fhm \
  scratch/bl-cons-only.fhm \
  scratch/bl-nil-only.fhm \
  scratch/bl-ascribed-list-lam.fhm \
  scratch/bl-live.fhm
do
  [[ -f "$f" ]] || { echo "  SKIP missing $f"; continue; }
  run_ok "$f"
done

echo "== red =="
run_err scratch/bl-r3-mid-fail.fhm "non-unique"
run_err scratch/bl-r1-pin-env-fail.fhm "does not meet"
run_err scratch/bl-hole-fail.fhm "ascription"
run_err scratch/bl-synth-fail.fhm "ascription"
run_err scratch/bl-nil-only-fail.fhm "empty\|Nil-only\|cover"

echo "== summary: $pass passed, $fail failed =="
[[ "$fail" -eq 0 ]]
