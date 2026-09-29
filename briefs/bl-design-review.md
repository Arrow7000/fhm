# BL language design review corpus

This document collects proposed BL programs and edge cases. Several examples
intentionally use syntax or features that do not exist yet; they are design
specimens rather than executable tests.

## Contents

- [A. Lists are bounds-first-class everywhere](#a-lists-are-bounds-first-class-everywhere)
- [B. Bounds-polymorphic datatype declarations](#b-bounds-polymorphic-datatype-declarations)
- [C. Uniform indices versus GADT-like indices](#c-uniform-indices-versus-gadt-like-indices)
- [D. Nominal invariance, subtyping, joins and meets](#d-nominal-invariance-subtyping-joins-and-meets)
- [E. Transparent type aliases](#e-transparent-type-aliases)
- [F. Constructor inference](#f-constructor-inference)
- [G. Function application and bidirectionality](#g-function-application-and-bidirectionality)
- [H. Pattern matching and index recovery](#h-pattern-matching-and-index-recovery)
- [I. Recursion](#i-recursion)
- [J. Erasure and runtime meaning](#j-erasure-and-runtime-meaning)
- [K. Database-motivated examples](#k-database-motivated-examples)
- [L. Scoping, equality and diagnostics](#l-scoping-equality-and-diagnostics)
- [M. Features deliberately outside the first complete language](#m-features-deliberately-outside-the-first-complete-language)
- [Review checklist](#review-checklist)

## Status vocabulary

| Status          | Meaning                                                    |
| --------------- | ---------------------------------------------------------- |
| **Accept**      | The proposed language should accept this.                  |
| **Reject**      | The proposed language should reject this deliberately.     |
| **Future**      | Coherent feature, but outside the first implementation.    |
| **Question**    | A design choice on which user input would be useful.       |
| **Current gap** | Desired behaviour differs from the current implementation. |

## Provisional contract

- In `--bl` mode, `List a` means and displays as `BL 0 inf a`.
- Bounds are retained through functions, nested scopes and type arguments.
- Datatypes have separate count parameters and type parameters.
- Constructor fields may use arbitrary count expressions over declared count
  parameters, including `n + 1`, multiplication, `min`, and `max`.
- Datatype result indices are initially uniform: every constructor of
  `T {counts} types` constructs that same `T {counts} types`.
- Nominal parameters are invariant unless a future feature explicitly declares
  or derives variance.
- Transparent aliases expand before subtyping, joining and meeting.
- Bounds inference succeeds only when it finds a unique semantic solution.
- Full result-to-argument bidirectional inference is deferred.
- Accepted closed programs receive a runtime bounds-soundness theorem.

## A. LISTS ARE BOUNDS-FIRST-CLASS EVERYWHERE

### A01 — Bare List is only surface sugar.

**Status:** ACCEPT.
**Hover:** `xs : BL 0 inf Int`, never `List Int` in --bl mode.

```fhm
let xs : List Int = [1, 2, 3]
xs
```

ok so actually maybe here we should interpret the `List Int` as more like `BL _ _ Int`, i.e. as a BL with inferable bounds slots. like, if we had a `\(xs : List Int) -> ...` then sure, there is nothing to infer, and we should just interpret that as a list as loosely boundaried as possible. but when the `List` is an annotation on a concrete, already existent, list whose bounds can be inferred, i think we should do that instead.

### A02 — The sugar applies recursively, not only at the outermost type.

**Status:** ACCEPT.
**Hover:** `xss : BL 0 inf (BL 0 inf Int)`.

```fhm
let xss : List (List Int) = [[1], [2, 3]]
xss
```

yes but same comment applies as at A01

### A03 — Explicit intervals remain visible through arrows.

**Status:** ACCEPT.
**Hover:** `f : BL 2 5 Int -> BL 2 5 Int`.

```fhm
let f : BL 2 5 Int -> BL 2 5 Int = \xs -> xs
f
```

### A04 — Bounds nested in ordinary type arguments must not be discarded.

**Status:** ACCEPT.

```fhm
type Box a = Box a
let b : Box (BL 2 4 Int) = Box [1, 2]
match b with
| Box xs -> xs
```

**Expected result:** `BL 2 4 Int`.
**Current gap:** static argument substitution mostly supports this, but generic
nominal runtime safety is not yet proved.

### A05 — Bounds remain nested at more than one nominal layer.

**Status:** ACCEPT.

```fhm
type Box a = Box a
type Maybe a = Some a | None
let x : Maybe (Box (BL 1 3 Int)) = Some (Box [1])
x
```

**Expected hover:** `Maybe (Box (BL 1 3 Int))`.

## B. BOUNDS-POLYMORPHIC DATATYPE DECLARATIONS

Proposed syntax uses braces for count parameters and ordinary names for type
parameters. The precise punctuation is still open; the semantic distinction
is the important part.

### B01 — A count parameter may appear unchanged in a field.

**Status:** ACCEPT.

```fhm
type Chunk {n : Nat} a =
  Chunk (BL n n a)
```

Runtime meaning: every value of `Chunk n a` contains exactly n `a`s.

### B02 — Count expressions in fields may contain `n + 1`, multiplication, or other expressions

**Status:** ACCEPT.

```fhm
type Window {n : Nat} a =
  Window (BL n (n + 1) a)
```

### B03 — Several count parameters can describe a proper interval.

**Status:** ACCEPT, subject to the declaration requiring/proving lo <= hi when
used. We need to decide whether this is a declaration premise or merely a
constructor-use premise.

```fhm
type BoundedBuffer {lo hi : Nat} a =
  BoundedBuffer (BL lo hi a)
```

**Question B03:** should the datatype carry an explicit declaration constraint
such as `{lo hi : Nat | lo <= hi}`, or is inhabitation simply impossible at
call sites where the interval is inconsistent?

hmm yeah im not sure how we could require this... or rather, how we could satisfy this requirement. or perhaps rather, how this requirement travels up. should it be fully implicit everywhere? i feel like that's a recipe for surprising behaviour. where sometimes the checker can carry a proof of ≤ through and sometimes not, and if we can't thread those requirements through explicitly or assert those requirements explicitly in the places where we require them, would result in confusing and seemingly inconsistent behaviour with no obvious way for the user to fix things.

### B04 — Arbitrary supported arithmetic may occur in fields.

**Status:** ACCEPT.

```fhm
type MatrixStorage {rows cols : Nat} a =
  MatrixStorage (BL (rows * cols) (rows * cols) a)
```

### B05 — A parameter may relate several fields.

**Status:** ACCEPT.

```fhm
type SameLengthPair {n : Nat} a b =
  SameLengthPair (BL n n a) (BL n n b)
```

Runtime meaning: both lists have exactly the same length n.

### B06 — Different expressions over the same parameters can relate fields.

**Status:** ACCEPT.

```fhm
type Split {left right : Nat} a =
  Split (BL left left a)
        (BL right right a)
        (BL (left + right) (left + right) a)
```

### B07 — Concrete bounds require no count parameters.

**Status:** ACCEPT.

```fhm
type IPv4 =
  IPv4 (BL 4 4 Nat)
```

### B08 — Infinity may appear in a field declaration.

**Status:** ACCEPT.

```fhm
type NonEmptyBag a =
  NonEmptyBag (BL 1 inf a)
```

### B09 — Count parameters can be phantom.

**Status:** QUESTION.

```fhm
type PhantomSize {n : Nat} a =
  PhantomSize a
```

**Recommendation:** allow this. It remains a real refinement index even though
the runtime representation does not determine it. Construction must still
choose a unique n from context or annotation; otherwise inference rejects it.

mm yeah good question. yeah i think it makes sense to allow it. and in that case actually the existence of a bound variable comes without any ≤ obligations/proofs attached, either implicit or explicit. so i think assigining one `PhantomSize` to another only works if the `n`s match up exactly under all circumstances. which i think makes sense.

### B10 — A count parameter may occur only under another nominal type.

**Status:** ACCEPT.

```fhm
type Box a = Box a
type NestedChunk {n : Nat} a =
  NestedChunk (Box (BL n n a))
```

sorry not sure what this means? does it mean we couldn't have something like

```
type Bla {n : Nat} a = Bla (BL n n a)
```

? and if so, why not?

### B11 — Recursive uniform datatype with bounded payloads.

**Status:** ACCEPT.

```fhm
type ChunkTree {n : Nat} a =
  Leaf (BL n n a)
  | Branch (ChunkTree n a) (ChunkTree n a)
```

This is recursive, but every recursive occurrence keeps the same n.

### B12 — Recursive type with bounded branching factor.

**Status:** ACCEPT.

```fhm
type Rose {lo hi : Nat} a =
  Rose a (BL lo hi (Rose lo hi a))
```

This is an important generic-runtime case: ValueAt must recurse through the
fields at a smaller observation budget.

### B13 — Count parameters and type parameters occupy distinct namespaces.

**Status:** ACCEPT.

```fhm
type Example {n : Nat} n = Example (BL n n n)
```

The spelling is intentionally provocative: it should either be legal with
unambiguous namespaces, or rejected for readability. Semantically there is
no need to confuse the count n with the type n.
**Question B13:** allow shadowing across kinds, or require globally distinct
parameter names within a declaration? Recommendation: require distinct names.

hm yeah. technically we could probably support this but yeah probably nicer to not allow this at the user-facing level. but either way, internally we shouldn't rely on bounds vars and type vars being distinct.

### B14 — An undeclared count in a field is rejected.

**Status:** REJECT.

```fhm
type Bad a = Bad (BL n n a)
```

**Why:** datatype declarations are closed schemas; n has no binder.

### B15 — A type argument cannot be supplied where a count is expected.

**Status:** REJECT.

```fhm
type Chunk {n : Nat} a = Chunk (BL n n a)
let x : Chunk Int Char = ...
```

**Why:** count and type parameters are separately kinded.

## C. UNIFORM INDICES VERSUS GADT-LIKE INDICES

### C01 — Uniform means the constructor returns the datatype's own parameters.

**Status:** ACCEPT.

```fhm
type Window {n : Nat} a =
  Small (BL n n a)
  | Large (BL n (n + 1) a)
```

Both constructors still return `Window n a`; field expressions may differ.

### C02 — Constructor-specific result indices are a different feature.

**Status:** REJECT FOR NOW.

```fhm
type Vec {n : Nat} a where
  Nil  : Vec 0 a
  Cons : a -> Vec n a -> Vec (n + 1) a
```

**Why rejected:** matching refines n, Cons introduces an existential predecessor,
coverage interacts with impossible indices, and constructor result types are
no longer uniform. This is dependent/GADT-style pattern matching.

yeah i don't think we should ever need to support this. not in scope.

### C03 — Existentially hiding a count index is also deferred.

**Status:** REJECT FOR NOW.

```fhm
type SomeChunk a where
  Pack : {n : Nat} Chunk n a -> SomeChunk a
```

**Why rejected:** opening Pack introduces a fresh existential count and requires
escape checks. This is useful, but materially beyond rank-1 count schemas.

yup, out of scope.

### C04 — Constructor equations refining an existing index are deferred.

**Status:** REJECT FOR NOW.

```fhm
type Parity {n : Nat} =
  Even : {k : Nat} Parity (k * 2)
  | Odd : {k : Nat} Parity (k * 2 + 1)
```

**Why rejected:** branch typing needs local arithmetic equalities and existential
constructor variables. Ordinary uniform declarations do not need either.

indeed, out of scope.

## D. NOMINAL INVARIANCE, SUBTYPING, JOINS AND MEETS

Default rule: all parameters of an abstract nominal datatype are invariant.
Equality should be semantic under current constraints, not raw syntax.

### D01 — Equal nominal arguments join successfully.

**Status:** ACCEPT.

```fhm
type Chunk {n : Nat} a = Chunk (BL n n a)
if condition then chunk3 else chunk3Again
```

**Result:** `Chunk 3 Int`.

### D02 — Semantically equal count expressions count as equal.

**Status:** ACCEPT.

```fhm
-- one branch: Chunk (n + 0) Int
-- other:     Chunk n Int
```

**Result:** `Chunk n Int`, provided the solver proves n + 0 = n.

### D03 — Different nominal count indices do not widen automatically.

**Status:** REJECT.

```fhm
if condition then chunk3 else chunk4
```

There is no inferred `Chunk ? Int`. The datatype has not declared what
widening its index means.

### D04 — Bounds hidden in a nominal type argument are also invariant.

**Status:** REJECT.

```fhm
type Box a = Box a
-- branch 1: Box (BL 1 1 Int)
-- branch 2: Box (BL 3 3 Int)
```

We do not infer `Box (BL 1 3 Int)` merely because Box happens to store a.

hmm. ok actually i disagree with this one. i don't see why we couldn't join/meet things here? this is better than if `Box` itself were to expose bounds vars, because `a` being instantiated as a BL means we can see the bounds directly, so we should always be able to treat bounds covariantly or contravariantly as appropriate. i think. no?

### D05 — Unwrap first, and naked BL joining works normally.

**Status:** ACCEPT.

```fhm
type Box a = Box a
let unpack = \b -> match b with | Box x -> x
if condition then unpack box1 else unpack box3
```

**Result:** `BL 1 3 Int`.

### D06 — Invariance is necessary for negative occurrences.

**Status:** ACCEPT AS A DECLARATION; PARAMETER REMAINS INVARIANT.

```fhm
type Consumer a =
  Consumer (a -> Int)
```

Treating arbitrary custom parameters covariantly would be unsound here.
**Current gap:** current custom SemanticSub and join recurse covariantly through
custom arguments. This must change before generic nominal runtime safety.

yes, but... is it possible to actually remember whether a given typevar is in covariant or contravariant position, which therefore allows us to treat BLs with correct variance? idk if this would break other stuff tho.

### D07 — Mixed positive and negative occurrence remains invariant.

**Status:** ACCEPT AS A DECLARATION.

```fhm
type Cell a =
  Cell a (a -> Unit)
```

### D08 — Explicit variance declarations are future work.

**Status:** FUTURE.

```fhm
type covariant Box a = Box a
```

**Why deferred:** variance must be checked against every field occurrence and
then threaded through semantic subtyping, join/meet and runtime transport.
Invariance is a complete sound baseline.

uhhh yeah not sure if we ever want this. either way not relevant for now.

### D09 — Count indices require exact equality even when a larger interval would contain both

**Status:** REJECT.

```fhm
type RangeTag {lo hi : Nat} = RangeTag
-- RangeTag 1 4 and RangeTag 0 5 do not subtype either way.
```

The nominal index is an identity/refinement, not automatically an interval.

### D10 — Explicit user code may repack into a different nominal index.

**Status:** ACCEPT when its implementation proves the field obligation.

```fhm
type Chunk {n : Nat} a = Chunk (BL n n a)
let forgetExact : {n : Nat, a} Chunk n a -> Box (BL n n a) =
  \c -> match c with | Chunk xs -> Box xs
```

Nominal invariance does not prevent explicit, checked conversions.

yes

## E. TRANSPARENT TYPE ALIASES

### E01 — A simple bounds alias expands transparently.

**Status:** ACCEPT.

```fhm
type alias NonEmpty a = BL 1 inf a
let head : {a} NonEmpty a -> a = ...
```

HOVER QUESTION: recommendation is to display the alias when helpful but also
expose its expansion, e.g. `NonEmpty Int (= BL 1 inf Int)`.

i think just expose the expansion for now. otherwise it's not clear that/whether for the given type wrapper bounds are to be treated `*`variantly or not.

### E02 — Alias count parameters may occur in arbitrary expressions.

**Status:** ACCEPT.

```fhm
type alias SizedPlusOne {n : Nat} a =
  BL (n + 1) (n + 1) a
```

### E03 — Aliases inside constructor fields are expanded before checking.

**Status:** ACCEPT.

```fhm
type alias SizedPlusOne {n : Nat} a = BL (n + 1) (n + 1) a
type Wrapped {n : Nat} a = Wrapped (SizedPlusOne n a)
```

This is equivalent to declaring the BL field directly.

### E04 — Aliases do not block intelligent BL joining.

**Status:** ACCEPT.

```fhm
type alias Sized {n : Nat} a = BL n n a
-- join (Sized 2 Int) (Sized 5 Int)
```

RESULT AFTER EXPANSION: `BL 2 5 Int`, not failure from alias invariance.

### E05 — Alias chains expand transitively.

**Status:** ACCEPT.

```fhm
type alias NonEmpty a = BL 1 inf a
type alias NonEmptyInts = NonEmpty Int
```

### E06 — Recursive alias cycles are rejected.

**Status:** REJECT.

```fhm
type alias A = B
type alias B = A
```

**Why:** transparent expansion would not terminate.

### E07 — Partially applied aliases are rejected initially.

**Status:** REJECT FOR NOW.

```fhm
type alias PairWith a = Pair a
-- use PairWith as a higher-kinded value
```

**Why:** the language has first-order types, not higher-kinded type functions.

### E08 — Explicitly parameterized function aliases remain rank-1.

**Status:** ACCEPT.

```fhm
type alias BoundedEndo {x : Nat} a =
  BL x (x * 2) a -> BL x (x * 2) a
```

```fhm
let f : {x : Nat, a} BoundedEndo x a = \xs -> xs
```

### E09 — An alias that hides its own forall is deferred.

**Status:** REJECT FOR NOW.

```fhm
type alias PolyEndo =
  {x : Nat, a} BL x (x * 2) a -> BL x (x * 2) a
```

**Why rejected:** this is an alias for a polymorphic scheme, not a monotype
abbreviation. Allowing it in fields or arrows raises higher-rank questions.

### E10 — Storing a polymorphic function in a datatype is likewise deferred.

**Status:** REJECT FOR NOW.

```fhm
type PolyMapper =
  PolyMapper ({lo hi : Nat, a b}
    (a -> b) -> BL lo hi a -> BL lo hi b)
```

**Why rejected:** the field itself has a forall. Current HM is rank-1.

yes exactly

## F. CONSTRUCTOR INFERENCE

### F01 — A constructor argument uniquely determines its count index.

**Status:** ACCEPT.

```fhm
type Chunk {n : Nat} a = Chunk (BL n n a)
Chunk [1, 2, 3]
```

**Result:** `Chunk 3 Int`.

### F02 — Several fields jointly determine parameters.

**Status:** ACCEPT.

```fhm
type SameLengthPair {n : Nat} a b =
  SameLengthPair (BL n n a) (BL n n b)
```

```fhm
SameLengthPair [1, 2] ['a', 'b']
```

**Result:** `SameLengthPair 2 Int Char`.

### F03 — Conflicting fields reject construction.

**Status:** REJECT.

```fhm
SameLengthPair [1] ['a', 'b']
```

No n satisfies both exact field demands.

### F04 — An interval field may underdetermine a parameter.

**Status:** REJECT WHEN AMBIGUOUS.

```fhm
type Window {n : Nat} a = Window (BL n (n + 1) a)
Window [1, 2, 3, 4, 5]
```

Both n=4 and n=5 may satisfy the argument inclusion, depending on the exact
constructor rule. With unique-solution inference, synthesis must reject.

### F05 — An explicit expected nominal type resolves constructor ambiguity.

**Status:** ACCEPT, even without general bidirectional application inference.

```fhm
let w : Window 4 Int = Window [1, 2, 3, 4, 5]
```

The constructor is checked against a known result index.

### F06 — Phantom indices require an expected type.

**Status:** REJECT without one; ACCEPT with one.

```fhm
type PhantomSize {n : Nat} a = PhantomSize a
PhantomSize 42                    -- reject: n is unknowable
let x : PhantomSize 7 Int = PhantomSize 42  -- accept
```

### F07 — Semantically unique, not merely syntactically unique.

**Status:** ACCEPT.

```fhm
type Double {n : Nat} a = Double (BL (n * 2) (n * 2) a)
Double [1, 2, 3, 4, 5, 6]
```

**Result:** `Double 3 Int`, if the uniqueness oracle proves it.

### F08 — No natural-number solution rejects construction.

**Status:** REJECT.

```fhm
Double [1, 2, 3, 4, 5]
```

ye exactly.

## G. FUNCTION APPLICATION AND BIDIRECTIONALITY

### G01 — Unique application inference succeeds.

**Status:** ACCEPT.

```fhm
let exact : {n : Nat, a} BL n n a -> BL n n a = \xs -> xs
exact [1, 2, 3]
```

**Result:** `BL 3 3 Int`.

### G02 — Ambiguous application inference is rejected.

**Status:** REJECT.

```fhm
let f : {x : Nat, a}
    BL x (x * 2) a -> BL x (x * 2) a = \xs -> xs
let xs : BL 5 5 Int = [1, 2, 3, 4, 5]
f xs
```

Multiple x values can admit the argument, and each produces a different
result type. Picking one arbitrarily would make inference unstable.

### G03 — An outside expected result could determine the ambiguous argument.

**Status:** FUTURE BIDIRECTIONAL FEATURE.

```fhm
(f xs : BL 6 12 Int)
```

Desired future behaviour: use the result demand to choose x=6, then verify
the argument and result constraints together.
**Current behaviour:** ordinary application synthesis does not propagate its
expected result backwards through the function application.

### G04 — A context may determine the result indirectly.

**Status:** FUTURE BIDIRECTIONAL FEATURE.

```fhm
let consume : BL 6 12 Int -> Unit = \ys -> ()
consume (f xs)
```

Full checking mode could push `BL 6 12 Int` into `f xs`; synthesis need not.

### G05 — A smallest or largest solution is insufficient without an explicit defaulting policy

**Status:** REJECT.

```fhm
f xs
```

**Recommendation:** do not silently choose minimal x, maximal x, or the tightest
inferred result. Require semantic uniqueness or outside guidance.

### G06 — Higher-order monomorphic use is ordinary rank-1 HM.

**Status:** ACCEPT.

```fhm
let apply = \g x -> g x
apply (\xs -> xs) [1, 2]
```

### G07 — Passing a generalized bounds-polymorphic function may require rank-2 polymorphism

**Status:** REJECT FOR NOW.

```fhm
let usePoly = \g -> (g [1], g [1, 2])
usePoly exact
```

**Why:** g must itself be polymorphic inside usePoly. Ordinary rank-1 let
polymorphism does not quantify lambda parameters.

## H. PATTERN MATCHING AND INDEX RECOVERY

### H01 — Matching recovers the declared bounds-rich field type.

**Status:** ACCEPT.

```fhm
type Window {n : Nat} a = Window (BL n (n + 1) a)
let contents : {n : Nat, a} Window n a -> BL n (n + 1) a =
  \w -> match w with | Window xs -> xs
```

### H02 — Matching through an alias recovers its expansion.

**Status:** ACCEPT.

```fhm
type alias Sized {n : Nat} a = BL n n a
type Chunk {n : Nat} a = Chunk (Sized n a)
match chunk with | Chunk xs -> xs
```

**Branch type:** `BL n n a`.

### H03 — Exhaustiveness remains declaration-indexed.

**Status:** ACCEPT.

```fhm
type Maybe a = Some a | None
match m with
| Some x -> ...
| None -> ...
```

### H04 — Constructors from another datatype are rejected even when their arity matches

**Status:** REJECT.

### H05 — Branches returning the same nominal indices join.

**Status:** ACCEPT.

```fhm
if b then chunk3 else anotherChunk3
```

**Result:** `Chunk 3 Int`.

### H06 — Branches returning different nominal indices fail to join.

**Status:** REJECT.

```fhm
if b then chunk3 else chunk4
```

### H07 — Branches returning their naked fields can join as BL.

**Status:** ACCEPT.

```fhm
if b then
  match chunk3 with | Chunk xs -> xs
else
  match chunk4 with | Chunk xs -> xs
```

**Result:** `BL 3 4 Int`.

### H08 — Impossible branches based on constructor-specific indices are deferred

**Status:** REJECT FOR NOW.

A future Vec 0 match could know Cons is impossible, but uniform indexed ADTs
do not introduce such equations.

## I. RECURSION

### I01 — Bounds-polymorphic recursion with a user-supplied invariant.

**Status:** ACCEPT.

```fhm
let map : {lo hi : Nat, a b}
    (a -> b) -> BL lo hi a -> BL lo hi b =
  \f xs ->
    match xs with
    | [] -> []
    | h :: t -> f h :: map f t
```

The recursive group checks the supplied invariant; it does not invent one.

### I02 — Recursive invariant inference from base cases.

**Status:** FUTURE NICE-TO-HAVE.

```fhm
let map = \f xs -> ...
```

**Why deferred:** synthesizing recursive invariants requires solving a fixed-point
inference problem. Current policy requires annotations when recursion entails
nontrivial polymorphic bounds.

### I03 — Monomorphic recursive bounds may be inferred from a stable unique interface

**Status:** ACCEPT where the existing stable-interface check succeeds.

### I04 — Mutually recursive functions each receive explicit invariants.

**Status:** ACCEPT.

```fhm
let rec
  even : {n : Nat} BL n n Int -> Bool = ...
  odd  : {n : Nat} BL n n Int -> Bool = ...
in ...
```

### I05 — In-group polymorphic recursion is deliberately excluded.

**Status:** REJECT.

A recursive member cannot call itself at two different instantiations inside
the same SCC merely because it has a forall annotation. It becomes available
polymorphically only after the group has been checked and exited.
**Why:** genuine polymorphic recursion destroys ordinary HM inference and greatly
complicates the recursive semantic invariant.

### I06 — Recursive custom datatypes are not recursive functions.

**Status:** ACCEPT.

```fhm
type ChunkTree {n : Nat} a =
  Leaf (BL n n a)
  | Branch (ChunkTree n a) (ChunkTree n a)
```

Generic runtime ValueAt handles the recursive value structure by decreasing
the observation budget. This does not require termination checking.

## J. ERASURE AND RUNTIME MEANING

### J01 — Count indices erase from custom types.

**Status:** ACCEPT.

```fhm
erase (Chunk 3 Int) = Chunk Int
erase (Chunk 9 Int) = Chunk Int
```

Runtime constructors do not carry a hidden count tag unless their ordinary
payload already contains relevant data.

### J02 — BL fields erase to ordinary List fields.

**Status:** ACCEPT.

```fhm
erase (Window n a) = Window a
erase field (BL n (n + 1) a) = List a
```

### J03 — The bounds runtime theorem distinguishes refinements that HM erases.

**Status:** ACCEPT.

HM sees both Chunk 3 Int and Chunk 9 Int as Chunk Int. BL safety separately
proves that their fields have lengths 3 and 9 respectively.

### J04 — Bounds do not affect operational reduction.

**Status:** ACCEPT.

No evaluator branch inspects n, lo or hi. Bounds constrain which source
programs are accepted and what values are semantically permitted.

### J05 — General recursion means partial correctness, not termination.

**Status:** ACCEPT.

If an accepted expression terminates with a value, the value obeys its bound.
A diverging recursive expression does not falsify `BL lo hi a`.

### J06 — Primitive specifications need verified or explicitly trusted contracts

**Status:** QUESTION / TRUST-BOUNDARY DECISION.

Example: declaring a database primitive as returning `BL 5 5 Row` when it
can return three rows. We must identify whether such primitive contracts are
axioms, verified implementations, or checked against an external semantics.

## K. DATABASE-MOTIVATED EXAMPLES

The operation names below are illustrative rather than current primitives.

### K01 — Map/projection preserves cardinality.

**Status:** ACCEPT.

```fhm
map : {lo hi : Nat, a b}
  (a -> b) -> BL lo hi a -> BL lo hi b
```

### K02 — Filter/select preserves only the upper bound in general.

**Status:** ACCEPT.

```fhm
filter : {lo hi : Nat, a}
  (a -> Bool) -> BL lo hi a -> BL 0 hi a
```

### K03 — Append/union-all adds cardinality intervals.

**Status:** ACCEPT.

```fhm
append : {a b c d : Nat, row}
  BL a b row -> BL c d row -> BL (a + c) (b + d) row
```

### K04 — Cartesian product multiplies cardinalities.

**Status:** ACCEPT.

```fhm
product : {a b c d : Nat, x y}
  BL a b x -> BL c d y -> BL (a * c) (b * d) (x, y)
```

### K05 — Inner join usually has no positive lower bound without key or foreign-key facts

**Status:** ACCEPT.

```fhm
innerJoin : {a b c d : Nat, x y}
  (x -> y -> Bool) -> BL a b x -> BL c d y -> BL 0 (b * d) (x, y)
```

### K06 — A limit operation can express min arithmetic.

**Status:** ACCEPT, subject to the precise lower-bound semantics.

```fhm
limit : {n lo hi : Nat, a}
  BL lo hi a -> BL (min n lo) (min n hi) a
```

### K07 — A nonempty query result justifies total head.

**Status:** ACCEPT.

```fhm
head : {lo hi : Nat, a} BL (lo + 1) hi a -> a
```

### K08 — A table schema can wrap a cardinality-indexed collection.

**Status:** ACCEPT.

```fhm
type Table {lo hi : Nat} row =
  Table (BL lo hi row)
```

Nominal invariance means Table 10 20 Row is not silently widened to
Table 0 100 Row. An explicit query/operator contract performs that conversion.

### K09 — A result page relates metadata to payload length.

**Status:** ACCEPT.

```fhm
type Page {n : Nat} row =
  Page Nat (BL 0 n row)
```

The Nat field might be a page number; n constrains only the payload.

### K10 — Relating a runtime `Nat` field to a type index is outside this design

**Status:** REJECT FOR NOW.

```fhm
type Page row =
  Page (size : Nat) (rows : BL size size row)
```

**Why rejected:** size is a runtime value bound by the constructor, not a static
count parameter. Supporting this requires dependent pairs/existentials and
pattern-bound count values.

### K11 — Schema facts require a refinement vocabulary beyond cardinalities

**Status:** FUTURE.

A foreign-key join might preserve the left cardinality, but only if uniqueness
and referential-integrity facts are represented and trusted/proved.

## L. SCOPING, EQUALITY AND DIAGNOSTICS

### L01 — Count parameters obey lexical scoping.

**Status:** ACCEPT.

```fhm
type Chunk {n : Nat} a = Chunk (BL n n a)
```

n is available throughout every constructor field and nowhere outside the
declaration/application unless rebound.

### L02 — Duplicate count parameters reject the declaration.

**Status:** REJECT.

```fhm
type Bad {n : Nat, n : Nat} a = Bad a
```

### L03 — Duplicate names across count/type kinds should probably reject too.

**Status:** QUESTION; RECOMMEND REJECT for readable diagnostics.

```fhm
type Confusing {a : Nat} a = Confusing a
```

### L04 — Semantic equality should recognize arithmetic identities.

**Status:** ACCEPT where the oracle proves them.

`Chunk (n + 0) a` and `Chunk n a` are the same indexed nominal type.

### L05 — Semantic equality must not depend on accidental solver search choices.

**Status:** ACCEPT AS A META-REQUIREMENT.

Equality evidence is a proposition/certificate. Failure to find a certificate
may reject a program conservatively; success must always be sound.

### L06 — Error messages should identify the nominal invariance boundary.

**Status:** ACCEPT AS A TOOLING REQUIREMENT.

Bad: "type mismatch"
Good: "cannot join Chunk 3 Int and Chunk 4 Int: nominal count parameter n

```fhm
     is invariant; unwrap/repack explicitly or provide a common expected type"
```

### L07 — Hovers must preserve all bounds structure.

**Status:** ACCEPT AS A TOOLING REQUIREMENT.

```fhm
Window n (Box (List Int))
```

displays in --bl mode as:

```fhm
Window n (Box (BL 0 inf Int))
```

### L08 — Internal metavariable names must not leak into stable hover output

**Status:** ACCEPT AS A TOOLING REQUIREMENT.

## M. FEATURES DELIBERATELY OUTSIDE THE FIRST COMPLETE LANGUAGE

### M01 — GADT-like constructor result indices.

REJECTED FOR NOW: requires index equations, existentials and impossible-arm
reasoning during pattern matching.

### M02 — Hidden existential count packages.

REJECTED FOR NOW: requires fresh count witnesses and escape discipline.

### M03 — Hidden-forall type aliases or polymorphic datatype fields.

REJECTED FOR NOW: requires higher-rank/impredicative polymorphism.

### M04 — Automatic variance inference for nominal parameters.

REJECTED FOR NOW: invariance is sound and complete enough for a first system.

### M05 — Full bidirectional count inference.

DEFERRED: useful, but unique synthesis plus annotations gives a principled
initial language. Add checking-mode feedback deliberately later.

### M06 — Inventing recursive bounds invariants from base cases.

DEFERRED: useful ergonomics, but user-provided invariants keep recursive
checking decidable and predictable.

### M07 — Termination checking.

REJECTED AS A REQUIREMENT FOR THIS LANGUAGE: runtime bounds safety is partial
correctness, and recursive functions remain valuable demonstrations.

### M08 — Runtime values reflected automatically into count indices.

REJECTED FOR NOW: this is dependent typing over terms, not merely symbolic
cardinality refinement.

### M09 — Arbitrary-world/open-certificate semantic modularity.

DEFERRED AS A HEADLINE REQUIREMENT: potentially useful for separate
compilation and proof-reusing optimizers, but closed-program safety is the
product-critical theorem.

## Review checklist

1. Do count-polymorphic nominal declarations such as Window and Chunk feel
   useful enough to justify the representation extension?
2. Is invariant-by-default nominal behaviour acceptable, especially the
   rejection of joins like Chunk 3 a with Chunk 4 a?
3. Should semantically equal expressions (n and n+0) count as the same index?
4. Should phantom count parameters be allowed when an annotation/context
   supplies them?
5. Should datatype declarations carry explicit arithmetic premises such as
   lo <= hi, or should inconsistent instantiations merely be uninhabited?
6. Is the uniform-index restriction acceptable for the first complete
   language, with Vec/GADT-like declarations clearly deferred?
7. Should aliases always expand in hovers, preserve their surface names, or
   show both alias and expansion?
8. Is rejecting hidden-forall scheme aliases acceptable if explicitly
   parameterized aliases cover ordinary use cases?
9. Is unique-only synthesis the right policy until proper bidirectional
   bounds checking is designed?
10. Which database primitives belong inside the verified semantics, and which
    should be an explicit trusted-contract boundary?
11. Does the closed-program runtime theorem described above match the desired
    definition of a complete bounds metatheory?
12. Which accepted example here is least valuable, and which rejected/future
    example is actually essential to the intended database language?
