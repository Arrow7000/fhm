#!/usr/bin/env bash
set -euo pipefail

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$repo_root"
export ELAN_HOME="$repo_root/.elan"
export PATH="$ELAN_HOME/bin:$PATH"
export MATHLIB_NO_CACHE_ON_UPDATE=1

if ! command -v elan >/dev/null 2>&1; then
  curl --retry 3 -sSf https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh | sh -s -- -y --default-toolchain none
fi

# Fetch only the mathlib modules used by FHM and their transitive dependencies.
mapfile -t mathlib_modules < <(git grep -h '^import Mathlib' -- FHM | awk '{print $2}' | sort -u)
lake exe cache get "${mathlib_modules[@]}"
lake build fhm
.lake/build/bin/fhm --help

npm --prefix editors/web ci --include=dev
npm --prefix editors/web test
npm --prefix editors/web run build
