#!/usr/bin/env bash
set -u

root="$(cd "$(dirname "$0")" && pwd)"
tmp="$(mktemp -d "${TMPDIR:-/tmp}/fhm-recursion-comparison.XXXXXX")"
trap 'find "$tmp" -depth -delete' EXIT

failures=0

version_line() {
  local name="$1"
  shift
  printf '%-8s %s\n' "$name" "$($@ 2>&1 | head -n 1)"
}

expect_pass() {
  local name="$1"
  shift
  local log="$tmp/${name//[^a-zA-Z0-9]/_}.log"
  if "$@" >"$log" 2>&1; then
    printf 'PASS  %s\n' "$name"
  else
    printf 'FAIL  %s (unexpected rejection)\n' "$name"
    sed -n '1,100p' "$log"
    failures=$((failures + 1))
  fi
}

expect_fail() {
  local name="$1"
  shift
  local log="$tmp/${name//[^a-zA-Z0-9]/_}.log"
  if "$@" >"$log" 2>&1; then
    printf 'FAIL  %s (unexpected acceptance)\n' "$name"
    failures=$((failures + 1))
  else
    printf 'PASS  %s (rejected as expected)\n' "$name"
    sed -n '1,100p' "$log" | sed 's/^/      /'
  fi
}

printf '%s\n' 'Compiler versions'
version_line OCaml ocamlc -version
version_line GHC ghc --numeric-version
version_line FSharp dotnet fsi --version
version_line Elm elm --version
version_line PolyML poly --version
printf '\n'

expect_pass 'OCaml explicit forall permits recursive polymorphic uses' \
  ocamlc -i "$root/ocaml/positive_explicit_forall.ml"
expect_fail 'OCaml ordinary annotation remains monomorphic recursively' \
  ocamlc -i "$root/ocaml/negative_ordinary_annotation.ml"

mkdir -p "$tmp/ghc-positive" "$tmp/ghc-negative"
expect_pass 'Haskell signature permits recursive polymorphic uses' \
  ghc -v0 -fno-code -fforce-recomp -outputdir "$tmp/ghc-positive" \
    "$root/haskell/PositiveSignature.hs"
expect_fail 'Haskell missing signature makes recursive uses monomorphic' \
  ghc -v0 -fno-code -fforce-recomp -outputdir "$tmp/ghc-negative" \
    "$root/haskell/NegativeNoSignature.hs"

expect_pass 'FSharp explicit type parameter permits recursive polymorphic uses' \
  dotnet fsi --exec "$root/fsharp/positive_explicit_type_parameter.fsx"
expect_fail 'FSharp ordinary annotation is constrained by recursive uses' \
  dotnet fsi --exec "$root/fsharp/negative_ordinary_annotation.fsx"

cp -R "$root/elm" "$tmp/elm"
expect_pass 'Elm annotated sibling uses may instantiate differently' \
  bash -c "cd '$tmp/elm' && elm make src/PositiveMutual.elm --output=/dev/null"
expect_fail 'Elm annotated direct self-use remains monomorphic' \
  bash -c "cd '$tmp/elm' && elm make src/NegativeSelf.elm --output=/dev/null"
expect_fail 'Elm unannotated mutual uses remain monomorphic' \
  bash -c "cd '$tmp/elm' && elm make src/NegativeMutualUnannotated.elm --output=/dev/null"

expect_pass 'Standard ML generalizes after recursive declaration exits' \
  poly --error-exit --script "$root/sml/positive_after_group.sml"
expect_fail 'Standard ML recursive uses share the declaration monotype' \
  poly --error-exit --script "$root/sml/negative_in_group.sml"

printf '\n'
if [ "$failures" -eq 0 ]; then
  printf '%s\n' 'All comparison cases matched their expected boundary.'
  exit 0
fi

printf '%s\n' "$failures comparison case(s) disagreed with the expected boundary."
exit 1
