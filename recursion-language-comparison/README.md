# Recursive polymorphism comparison

"Language X supports polymorphic recursion" is ambiguous. This suite pins down how
GHC, OCaml, F#, Elm, Standard ML (Poly/ML) and FHM actually typecheck polymorphism
inside recursive binding groups. It uses the same small programs with the same
dependency structure in every language. The deciding question is T5: does a complete
signature cut dependency edges, so that the unsigned members of a group can be
generalised before the rest of the group?

## Running

```sh
bash recursion-language-comparison/check.sh             # everything
bash recursion-language-comparison/check.sh fhm elm     # a subset
VERBOSE=1 bash recursion-language-comparison/check.sh   # also print the expected rejections' diagnostics
```

`check.sh` re-enters itself through `nix-shell shell.nix` when the external compilers
are missing, so they need not be installed globally. FHM uses the already-built
`.lake/build/bin/fhm` (override with `FHM=...`). The script runs every case listed in
[`expected.tsv`](expected.tsv) and compares accepted/rejected against the expectation.
For FHM it also compares the evaluated value. It exits non-zero on any mismatch.

## Layout

One directory per language: `haskell/`, `ocaml/`, `fsharp/`, `elm/src/`, `sml/`
and `fhm/`. File names give the test id and the topic, for example
`t5_signature_cuts_dependency.ml` or `T5SignatureCutsDependency.hs`. Haskell and Elm
files use CamelCase because their module names must match. Expected outcomes live only
in `expected.tsv`, not in file names.

Each language's most idiomatic complete, rigid signature is used: a Haskell top-level
signature, OCaml `'a.`, F# `<'a>`, an Elm top-level annotation, SML `(x : 'a)` inside
`fun ... and ...`, and FHM `{a}`. Languages with explicit recursive groups (OCaml, F#
and SML) put all mutually dependent members in one `let rec ... and ...` /
`fun ... and ...`. Haskell, Elm and FHM use top-level definitions and their own
dependency analysis. Dead branches (`if True then x else ...`) create dependencies
without non-termination.

## Tests

| Id | Shape |
|---|---|
| T1 | `wrapN : ∀a. Int → a → Int` calls itself at `[a]` |
| T2 | T1 with no signature |
| T3 | signed `f : ∀a. a → a` and unsigned `useF _ = (f 1, f True)` in one SCC |
| T4 | signed `consumer : Int → (Int, Bool)` uses unsigned sibling `helper` at Int and Bool |
| T5 | signed `f`; unsigned `g n = (h 1, h True)` and `h` (which reaches the cycle only through `f`); order f, g, h |
| T5b | T5 with the order f, h, g |
| T6 | `depth : ∀a. Nested a → Int` over `data Nested a = Flat a \| Nest (Nested [a])` |
| T7 | signed `ping`/`pong` call each other at `[a]` and `(b, b)` |

## Results

A = accepted, R = rejected. The table matches `expected.tsv`, which `check.sh`
verifies.

| Test | GHC 9.6 | OCaml 5.2 | F# 6 | Elm 0.19.1 | Poly/ML 5.9 | FHM |
|---|---|---|---|---|---|---|
| T1 annotated self polyrec | A | A | A | R | R | A `3` |
| T2 unannotated self polyrec | R | R | R | R | R | R |
| T3 unsigned uses signed at 2 types | A | A | A | A | R | A `(1, True)` |
| T4 signed uses unsigned at 2 types | A | R | R (A if helper is defined first) | A | R | A `(5, True)` |
| **T5** signature cuts dependency | **A** | R | R | R | R | R |
| T5b T5, order f, h, g | A | R | A | R | R | R |
| T6 nested datatype | A | A | A | R | R | A `2` |
| T7 signed mutual polyrec | A | A | A | A | R | A `(4, 4)` |

Only GHC implements full Haskell-style dependency analysis, where a signature removes
the incoming edges and the remainder is re-split into SCCs. FHM, like Elm, treats
annotated members as polymorphic contracts but checks all unannotated members of an
SCC as one monomorphic HM block. FHM differs from Elm by also allowing direct
polymorphic self-recursion (T1 and T6).

The `t0_*` / `T0*` files are the older per-language boundary probes. Each uses a
recursive `f` at Int and Bool from inside its own group, once with the language's
polymorphic annotation and once without it. They also cover Elm's
annotated-sibling/unannotated-sibling pair, and SML's "generalised only after the
group" behaviour.

## Caveats

- **OCaml needs `'a.`.** A plain `'a` annotation is an ordinary unification variable,
  so `let rec wrapN : int -> 'a -> int` fails T1. Unannotated members of a `let rec`
  stay monomorphic throughout the group, regardless of order.
- **F# is order-sensitive.** Unannotated members are generalised in source order, so
  T5 fails but T5b passes, and T4 passes once `helper` precedes `consumer`. Without
  `<'a>`, T1 produces `warning FS0064` ("less generic than indicated by the type
  annotations") followed by an error. However, a member annotated as `(x: 'a) : 'a`
  is still generalised early enough for T5b (`t5c_*`).
- **Elm is asymmetric.** An annotated function is polymorphic to the other members
  of its group (T3, T4, T7, `T0SiblingsTwoUses`) but monomorphic in its own body
  (T1, T6, `T0SelfTwoUses`). All unannotated members of an SCC are checked together,
  so T5 fails in either order.
- **SML's explicit type variables are bound at the group.** `'a` in
  `fun f (x : 'a) ...` scopes over the whole `fun ... and ...` declaration and is rigid
  there, so even T3 fails with "Cannot unify with explicit type variable". There is
  no polymorphic recursion; functions are generalised only after the group.
