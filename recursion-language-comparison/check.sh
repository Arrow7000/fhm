#!/usr/bin/env bash
# Run every case listed in expected.tsv and compare the actual outcome with the
# expected one.
#
#   bash recursion-language-comparison/check.sh            # all languages
#   bash recursion-language-comparison/check.sh fhm elm    # a subset
#   VERBOSE=1 bash recursion-language-comparison/check.sh  # also print diagnostics
#
# The external compilers come from shell.nix; the script re-enters itself inside
# nix-shell when they are not already on PATH. FHM uses the repository's built
# binary (override with FHM=/path/to/fhm); it is not rebuilt here.
set -u

root="$(cd "$(dirname "$0")" && pwd)"
manifest="$root/expected.tsv"
fhm="${FHM:-$(cd "$root/.." && pwd)/.lake/build/bin/fhm}"
languages=("$@")
[ "${#languages[@]}" -eq 0 ] && languages=(haskell ocaml fsharp elm sml fhm)

wanted() {
  local lang
  for lang in "${languages[@]}"; do [ "$lang" = "$1" ] && return 0; done
  return 1
}

needs_nix=0
for lang in "${languages[@]}"; do [ "$lang" != fhm ] && needs_nix=1; done
if [ "$needs_nix" -eq 1 ] && [ -z "${RECURSION_COMPARISON_IN_NIX:-}" ]; then
  for tool in ghc ocaml dotnet elm poly; do
    if ! command -v "$tool" >/dev/null 2>&1; then
      exec nix-shell "$root/shell.nix" --run \
        "RECURSION_COMPARISON_IN_NIX=1 bash '$root/check.sh' ${languages[*]}"
    fi
  done
fi

export DOTNET_CLI_TELEMETRY_OPTOUT=1 DOTNET_NOLOGO=1 DOTNET_SKIP_FIRST_TIME_EXPERIENCE=1

tmp="$(mktemp -d "${TMPDIR:-/tmp}/fhm-recursion-comparison.XXXXXX")"
trap 'rm -rf "$tmp"' EXIT

printf '%s\n' 'Versions'
wanted haskell && printf '  %-7s %s\n' GHC "$(ghc --numeric-version 2>&1 | head -n 1)"
wanted ocaml   && printf '  %-7s %s\n' OCaml "$(ocamlc -version 2>&1 | head -n 1)"
wanted fsharp  && printf '  %-7s %s\n' 'F#' "$(dotnet fsi --version 2>&1 | head -n 1)"
wanted elm     && printf '  %-7s %s\n' Elm "$(elm --version 2>&1 | head -n 1)"
wanted sml     && printf '  %-7s %s\n' PolyML "$(poly -v </dev/null 2>&1 | head -n 1)"
wanted fhm     && printf '  %-7s %s\n' FHM "$fhm"
printf '\n'

if wanted elm; then
  cp -R "$root/elm" "$tmp/elm"
fi

# run_case LANG FILE LOG: exit status 0 means the program was accepted.
# For FHM the evaluated value is written to $tmp/value.
run_case() {
  local lang="$1" file="$2" log="$3"
  case "$lang" in
    haskell)
      mkdir -p "$tmp/ghc/$file"
      ghc -v0 -fno-code -fforce-recomp -outputdir "$tmp/ghc/$file" \
        "$root/haskell/$file" >"$log" 2>&1 ;;
    ocaml)
      ocamlc -i "$root/ocaml/$file" >"$log" 2>&1 ;;
    fsharp)
      dotnet fsi --nologo --exec "$root/fsharp/$file" >"$log" 2>&1 ;;
    elm)
      (cd "$tmp/elm" && elm make "src/$file" --output=/dev/null) >"$log" 2>&1 ;;
    sml)
      poly --error-exit --script "$root/sml/$file" >"$log" 2>&1 ;;
    fhm)
      if [ ! -x "$fhm" ]; then
        printf 'FHM binary not found at %s (run lake build in the repo root)\n' "$fhm" >"$log"
        return 2
      fi
      "$fhm" run "$root/fhm/$file" >"$log" 2>&1
      local status=$?
      sed -n 's/^⟹  //p' "$log" >"$tmp/value"
      if [ "$status" -ne 0 ]; then
        "$fhm" diagnose "$root/fhm/$file" 2>/dev/null \
          | sed -n 's/.*"message": "\(.*\)",$/  \1/p' >>"$log"
      fi
      return "$status" ;;
    *)
      printf 'unknown language %s\n' "$lang" >"$log"
      return 2 ;;
  esac
}

failures=0
total=0
printf '%-7s %-58s %-8s %-8s %s\n' LANG CASE EXPECTED ACTUAL RESULT
while IFS=$'\t' read -r lang file expected value; do
  case "$lang" in ''|'#'*) continue ;; esac
  wanted "$lang" || continue
  total=$((total + 1))
  log="$tmp/$lang-$file.log"
  : >"$tmp/value"
  if run_case "$lang" "$file" "$log" </dev/null; then actual=accept; else actual=reject; fi

  verdict=ok
  detail=''
  if [ "$actual" != "$expected" ]; then
    verdict=MISMATCH
  elif [ "$lang" = fhm ] && [ "$actual" = accept ]; then
    got="$(cat "$tmp/value")"
    detail="= $got"
    if [ "$value" != - ] && [ "$got" != "$value" ]; then
      verdict=MISMATCH
      detail="= $got (expected $value)"
    fi
  fi

  printf '%-7s %-58s %-8s %-8s %s %s\n' "$lang" "$file" "$expected" "$actual" "$verdict" "$detail"
  if [ "$verdict" != ok ]; then
    failures=$((failures + 1))
    sed -n '1,40p' "$log" | sed 's/^/        /'
  elif [ -n "${VERBOSE:-}" ] && [ "$actual" = reject ]; then
    sed -n '1,40p' "$log" | sed 's/^/        /'
  fi
done <"$manifest"

printf '\n'
if [ "$failures" -eq 0 ]; then
  printf 'All %d cases matched expected.tsv.\n' "$total"
  exit 0
fi
printf '%d of %d cases disagreed with expected.tsv.\n' "$failures" "$total"
exit 1
