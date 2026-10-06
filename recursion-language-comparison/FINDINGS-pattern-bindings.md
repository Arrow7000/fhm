# Pattern bindings: generalisation and recursion

Observed with GHC 9.6.6, OCaml 5.2.0, F# 6, Elm 0.19.1 and Poly/ML 5.9.1,
using the `P*`/`p*` files, which `check.sh` verifies against `expected.tsv`.
Entries marked "from docs, not run" were not run.

## Summary

| | local generalised? | top-level generalised? | signature gives polymorphism? | recursive allowed? | refutable pattern |
|---|---|---|---|---|---|
| GHC (default) | yes, even open | yes (minus MR-constrained tyvars) | only if the binding would generalise anyway | **yes**: self, mutual with functions, local and top-level | accepted; `-Wincomplete-uni-patterns` warning |
| GHC `MonoLocalBinds`/`GADTs` | closed only | yes | closed yes; open **no** | yes | warning |
| OCaml | syntactic value; else covariant tyvars only | same | no syntax | **no** | warning 8 |
| F# | generalisable RHS; else nothing | same | no (FS0721) | **no** (FS0873) | warning FS0025 |
| SML | non-expansive; else nothing | same | no | **no** | warning |
| Elm | yes, even open | top-level destructuring is a syntax error | no syntax | **no** | **rejected** |

## Haskell

- Accepted: P1 (local), P1b (top-level), P1c (top-level signatures), P3 (open
  binding generalises `f` per component), P2 (closed, MonoLocalBinds), P2d
  (signature, open, default), P2e (signature, closed, MonoLocalBinds), P4b
  (NoMonomorphismRestriction).
- P2b (MonoLocalBinds, open) and P3b (GADTs): `[GHC-83865] Couldn't match
  expected type ‘Bool’ with actual type ‘Int’ • In the expression: f True`.
- P2c (MonoLocalBinds, open, `f :: a -> a`): `[GHC-83865] Couldn't match
  expected type: p0 -> p0 with actual type: forall a. a -> a • In the pattern:
  (f, k)`. A signature on a pattern-bound name only checks a generalised type;
  it does not cause generalisation.
- P4 (MR, `(n, m) = (1, 2)` at Int and Double): `Couldn't match expected type
  ‘Double’ with actual type ‘Int’`. P4c (adds `n :: Num a => a`): `[GHC-16675]
  Overloaded signature conflicts with monomorphism restriction` (report §4.5.5
  Rule 1: a tuple pattern is never a simple pattern binding).
- Recursion is accepted everywhere: P5 (top-level knot), P5b (local knot,
  evaluates to `[0,2,4,6,8]`), P5c (function plus pattern in one group), P5e
  (recursive pattern binding generalised after its group), P5d (bang-pattern
  knot compiles and runs).
- P6: `[GHC-62161] [-Wincomplete-uni-patterns] Pattern match(es) are
  non-exhaustive In a pattern binding: Patterns of type ‘Maybe Int’ not
  matched: Nothing`. No warning when the RHS is literally `Just 1`.
- Lazy: let patterns are implicitly `~` (report §3.12).

## OCaml

- p1/p1b accepted (`val f : 'a -> 'a`). p2 (expansive): `This expression has
  type "bool" but an expression was expected of type "int"`.
- p3 accepted: in `let (f, xs) = ((fun x -> x), List.rev [])`, `xs` is used at
  int list and bool list (relaxed value restriction). p3b: `f` used at two
  types is rejected. Generalisation is partial, per type variable.
- p4 `let ((f : 'a. 'a -> 'a), g) = …`: `Syntax error: ")" expected`.
- p5/p5b: `Only variables are allowed as left-hand side of "let rec"`.
- p6: `Warning 8 [partial-match]: this pattern-matching is not exhaustive …
  None`. Strict; a failed match raises `Match_failure`.

## F#

- p1/p1b accepted. p2: `FS0001 … expected to have type 'int' but here has type
  'bool'`. p3 is rejected (no relaxed value restriction): `FS0001: Type
  mismatch. Expecting a 'bool list' but given a 'int list'`.
- p4 `let (f<'a> : 'a -> 'a), g`: `FS0721: Type arguments cannot be specified
  here`.
- p5/p5b: `FS0873: Only simple variable patterns can be bound in 'let rec'
  constructs`. The parenthesised form gives an unhelpful FS3521.
- p6: `FS0025: Incomplete pattern matches on this expression. For example, the
  value 'None' …`.

## SML (Poly/ML)

- p1/p1b accepted. p2: `Function: f : int -> int Argument: true : bool`. p3
  rejected (strict value restriction, nothing generalised). p4: `Type ('a ->
  'a) * ('b -> 'b) includes a free type variable`.
- p5/p5b: ``Recursive declaration is not of the form `fn match'``
  (Definition §2.9).
- p6: `warning: Pattern is not exhaustive. Found near val SOME x = m`. A failed
  match raises `Bind`.

## Elm

- P1 and P3 accepted (generalises even open destructuring). P1b: `UNEXPECTED
  SYMBOL … this line starts with the ( symbol`.
- P5/P5b: `CYCLIC VALUE — I do not allow cyclic values in let expressions …
  isEven → isOdd`, even with every reference under a lambda and even mutual
  with a function.
- P6: `UNSAFE PATTERN … You can use let to deconstruct values only if there is
  ONE possibility.`

## From docs, not run

- Rust: no let-generalisation; a refutable `let` is a hard error (E0005)
  unless written `let … else`.
- Scala 3: refutable `val` patterns warn unless marked `@unchecked` (Scala 3
  reference, "pattern-bindings").
- Lean 4: `let (a, b) := e` elaborates to `match`; a non-exhaustive pattern
  needs `| alt`; `let rec` takes only identifiers.
- Vytiniotis, Peyton Jones and Schrijvers, "Let should not be generalised"
  (TLDI 2010): the rationale for MonoLocalBinds.

## Implications for FHM

- **Non-recursive:** strongly precedented. Every strict language rejects
  recursive pattern bindings; only lazy Haskell allows them. FHM is
  call-by-value (`FHM/Core.lean`). Elm's error, which names the cycle, is the
  model to copy.
- **Monomorphic:** principled (a one-arm `match` gives exactly this) and
  forward-compatible, since generalising later only accepts more programs. It
  is stricter than all five languages for value right-hand sides such as
  `let (f, g) = (\x -> x, \y -> y)`. The workaround for users: bind the tuple
  to a variable (which is generalised) and project.
- **Top level:** monomorphic top-level pattern bindings have no precedent.
  Decide how type variables left unsolved at the top level are handled (F#
  FS0030, OCaml weak variables, Haskell's MR defaulting), or follow Elm and
  allow pattern lets only locally.
- **Signatures:** don't copy Haskell's escape hatch. GHC itself rejects P2c and
  P4c, and honouring a polymorphic signature would mean generalising. A
  monomorphic annotation inside the pattern is fine.
- **Refutable patterns:** reuse `match`'s exhaustiveness check and reject, as
  Elm and Rust do.
