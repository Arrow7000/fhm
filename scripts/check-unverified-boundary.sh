#!/usr/bin/env bash
set -euo pipefail

cd "$(dirname "$0")/.."

# Check declarations, not prose mentioning partial definitions.
if rg -n --glob '*.lean' --glob '!FHM/Unverified/**' \
    '^[[:space:]]*((private|protected|noncomputable)[[:space:]]+)*partial[[:space:]]+(def|instance|abbrev)\b' FHM; then
  echo 'error: production partial declarations must live under FHM/Unverified/' >&2
  exit 1
fi

# Bash-3-compatible visited set: each module occupies a complete line.
visited=$'\n'
check_module() {
  local module="$1"
  case "$visited" in
    *$'\n'"$module"$'\n'*) return ;;
  esac
  visited+="$module"$'\n'
  case "$module" in
    FHM.Unverified.*)
      echo "error: default verified library imports $module" >&2
      exit 1
      ;;
  esac
  local module_file="${module//.//}.lean"
  [[ -f "$module_file" ]] || return
  local import_line dependency
  local dependencies=()
  while IFS= read -r import_line; do
    read -r -a dependencies <<< "${import_line#import }"
    for dependency in "${dependencies[@]}"; do
      case "$dependency" in
        FHM.*) check_module "$dependency" ;;
      esac
    done
  done < <(rg '^import ' "$module_file" || true)
}

roots=()
while IFS= read -r module; do
  roots+=("$module")
done < <(awk '
  /^name = "FHM"$/ { library = 1 }
  library && /^roots = \[/ { in_roots = 1; next }
  in_roots && /^\]/ { exit }
  in_roots && match($0, /"FHM[^" ]*"/) {
    print substr($0, RSTART + 1, RLENGTH - 2)
  }
' lakefile.toml)
[[ ${#roots[@]} -gt 0 ]] || { echo 'error: no default FHM roots found' >&2; exit 1; }
for module in "${roots[@]}"; do
  check_module "$module"
done

echo 'Unverified boundary checks passed.'
