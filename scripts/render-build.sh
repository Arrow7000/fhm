#!/usr/bin/env bash
set -euo pipefail

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$repo_root"
export ELAN_HOME="$repo_root/.elan"
export PATH="$ELAN_HOME/bin:$PATH"
export MATHLIB_NO_CACHE_ON_UPDATE=1

# Render preserves XDG_CACHE_HOME between builds, but not the source checkout.
# Key native artifacts by platform, toolchain, and dependency configuration;
# Lake's own traces then rebuild any changed FHM modules within that cache.
cache_dir=""
if [[ -n "${XDG_CACHE_HOME:-}" ]]; then
  cache_dir="$XDG_CACHE_HOME/fhm-build"
  cache_key="$(cat lean-toolchain lake-manifest.json lakefile.toml; uname -sm)"
  cache_key="$(printf '%s' "$cache_key" | sha256sum | cut -d ' ' -f 1)"
  mkdir -p "$cache_dir"
  if [[ -f "$cache_dir/$cache_key.tar.gz" ]]; then
    echo "==> Restoring cached Lean toolchain and native Lake artifacts"
    tar -xzf "$cache_dir/$cache_key.tar.gz" -C "$repo_root"
  else
    echo "==> No native Lake cache yet for this toolchain and dependency set"
  fi
fi

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

if [[ -n "$cache_dir" ]]; then
  # UI-only deploys restore the same executable. Keep that archive instead of
  # spending minutes recompressing an unchanged toolchain and native build.
  if [[ ! -f "$cache_dir/$cache_key.tar.gz" || ".lake/build/bin/fhm" -nt "$cache_dir/$cache_key.tar.gz" ]]; then
    echo "==> Saving Lean toolchain and native Lake artifacts for future deploys"
    tar -czf "$cache_dir/$cache_key.tar.gz.tmp" .elan .lake
    mv "$cache_dir/$cache_key.tar.gz.tmp" "$cache_dir/$cache_key.tar.gz"
  else
    echo "==> Native executable unchanged; retaining the existing Lake cache"
  fi
fi
