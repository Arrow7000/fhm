#!/usr/bin/env bash
# Build the size/RSS-optimized fhm binary: normal `lake build fhm`, then
# relink with the lean_initialize shim (see lean_init_shim.c for why/safety).
# Output: .lake/build/bin/fhm-small
set -euo pipefail

ROOT="$(cd "$(dirname "$0")/.." && pwd)"
cd "$ROOT"

lake build fhm

SYSROOT="$(lake env lean --print-prefix)"
RSP=.lake/build/bin/fhm.rsp
[[ -f "$RSP" ]] || { echo "error: $RSP not found (lake version too old?)" >&2; exit 1; }

SHIM_O=.lake/build/lean_init_shim.o
"$SYSROOT/bin/clang" -c -O2 -o "$SHIM_O" scripts/lean_init_shim.c \
  --sysroot "$SYSROOT" -nostdinc -isystem "$SYSROOT/include/clang"

{ echo "$SHIM_O"; cat "$RSP"; } > .lake/build/fhm-small.rsp
MACOSX_DEPLOYMENT_TARGET=99.0 "$SYSROOT/bin/clang" \
  -o .lake/build/bin/fhm-small @.lake/build/fhm-small.rsp

ls -la .lake/build/bin/fhm .lake/build/bin/fhm-small \
  | awk '{printf "%8.2f MB  %s\n", $5/1048576, $NF}'
