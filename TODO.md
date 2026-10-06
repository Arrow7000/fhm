# TODO

Known bugs and smaller tasks. The bigger picture lives in the
[README roadmap](./README.md#roadmap).

## Suggested order

Bugs and cleanup can be picked up at any time. The larger items build
on each other:

1. **Errors as data**: the foundation for everything below.
2. **Better error messages**, with locations, built on (1).
3. **Error recovery**, so one error doesn't take down the rest of the file.
   Needs (1) to collect errors and carry on.
4. **Richer hovers**: most useful once (3) keeps them working in files with
   errors.

Separately, the annotation features go in this order:

5. **Type holes**, then **named holes**.
6. **Head-binder syntax**, which needs (5) for anything not fully annotated.

And patterns in bindings:

7. **Nested-match exhaustiveness** (under Bugs), which otherwise rejects
   tuple patterns such as `\((a, b), c) -> …` straight away.
8. **Patterns in lambda parameters**, then **pattern lets**.

## Bugs

- [ ] **`fhm run --json` reports type errors at 1:1.** When typechecking fails,
  the run JSON's `line`/`col` are the `PipelineErr` defaults rather than the
  failing expression's span; `fhm diagnose` reports the right location. The
  playground only shows positions from `diagnose`, so this affects other
  `--json` consumers.

- [ ] **Exhaustiveness checker rejects complete nested matches.**
  `checkExhaustive` is sound (it never accepts an incomplete match) but not
  complete: some matches whose patterns go more than one constructor deep are
  rejected with `match not exhaustive` even though they cover every case.
  The simplest case is a nested tuple, which has only one case to cover:

  ```
  let f = \p ->
    match p with
    | ((a, b), c) -> a

  f ((1, 2), 3)
  ```

  `(a, (b, c))` fails the same way. With constructors:

  ```
  type Maybe a = Just a | Nothing

  let g = \m ->
    match m with
    | Just (Just x) -> x
    | Just Nothing -> 0
    | Nothing -> 0

  g (Just (Just 3))
  ```

  The same happens with nested lists:

  ```
  let h = \xs ->
    match xs with
    | [] -> 0
    | [] :: _ -> 1
    | (y :: _) :: _ -> y

  h [[5]]
  ```

  Suspected cause: when the checker guesses a nested scrutinee's type
  arguments (`tyArgsGuess` in `FHM/SurfaceBridge.lean`), it uses placeholders
  that fail closed.

- [x] **Self-referential constructor fields only parsed last.** In a type
  without parameters, `type T = Leaf | Node T Int T` was read as
  `Node (T Int T)`, and parentheses didn't help. Fixed in 897be46: constructor
  fields are now type atoms, as in Haskell and Elm. Worth a look at what else
  the field parser accepts too eagerly (see the next entry).

- [ ] **Parser swallows a bare program body after a `type` declaration.** If
  a `type` declaration is followed directly by the program's final
  expression, the parser reads that expression as an extra constructor field
  of the declaration's last constructor:

  ```
  type Color = Red | Green | Blue

  Red
  ```

  This fails with `[lower] lowering failed`, because `Blue` now appears to
  take a `Red` argument. `(Red)` fails the same way. Any `let` between the
  declaration and the body hides the problem. The constructor-field parser
  (`dataCtor` / `ctorField` in `FHM/Unverified/Surface/Parse.lean`) should
  stop at the end of the declaration's layout block.

- [ ] **Value recursion overflows the evaluator's stack.** A recursive
  definition that isn't a function crashes `fhm run` with `Stack overflow
  detected. Aborting.`, even with `--fuel`, so the step budget doesn't count
  this kind of recursion. Ordinary infinite recursion (`let loop = \n -> loop
  (n + 1)`) does stop at the budget.

  ```
  let x = x + 1

  x
  ```

  Local `let`s are recursive too, so `let x = x + 1 in x` inside a function
  does the same. Either the evaluator should spend fuel here, or definitions
  like this should be rejected, as OCaml rejects `let rec x = x + 1` ("This
  kind of expression is not allowed as right-hand side of let rec").

- [ ] **A type and a constructor with the same name are confused by hover and
  go to definition.** With `type Box a = Box a`, the `Box` in an annotation
  such as `Box a -> a` is resolved by name to the constructor, so hover shows
  `∀ a. a → Box a` and go to definition jumps to the constructor. The editor
  only knows the name and scope. The parser should record type-name and
  constructor references with their kind, as it does for binders. The
  `hover-syntax` snapshot (`editors/web/fixtures/`) pins the current
  behaviour.

## Errors and diagnostics

- [ ] **Errors as data.** Replace the stringly typed errors throughout the
  pipeline with an error ADT, so errors can be collected, computed over, and
  presented differently depending on context (terminal, JSON, editor). The
  verified functions currently return `Option`; moving them to `Except` means
  restating their theorems in terms of `.ok` rather than `some`, which is
  mechanical but touches a lot of code.
- [ ] **Better error messages.** `fhm run` reports only
  `[typecheck] typechecking failed`, and `fhm diagnose` adds just the name of
  the failing definition; neither gives a location or a reason. Lowering
  errors are a single generic message: `lowering failed (unbound name, bad
  decl, or rejected sugar)`.
- [ ] **Error recovery.** A single lowering or typechecking error currently
  kills hover information for the whole file. Type checking already proceeds
  one recursive group at a time, so a failed group's members could get a
  placeholder type and checking could continue; only code that depends on the
  failure would lose information. Lowering can recover per binding in the
  same way, and the parser (unverified) can resynchronise at top-level
  declarations. Recovery is for the editor path only: `elaborateSafe` and the
  theorems keep applying to programs that check completely.

## Editor tooling

- [ ] **Richer hovers.** Hovers show a highlighted signature but little else.
  Look at what Elm's and other high-quality language servers show on hover,
  and how they format it. Ideas:
  - Show a constructor's full declaration, not just its type.
  - For annotated bindings, show the inferred type when it differs from the
    annotation.
  - With error recovery, show something like "type unknown (error in `g`)"
    instead of nothing.

- [ ] **Missing-case witnesses.** When a match isn't exhaustive, name the
  missing patterns (`missing: Just Nothing`) instead of only saying so, in
  `fhm diagnose` and the editors. The playground shows `diagnose` output, so
  it gets this for free. Once patterns are allowed in lambdas and lets, the
  same witnesses explain why a refutable one is rejected. Also wants errors
  as data.

- [ ] **Formatter**: an elm-format equivalent. One canonical layout for FHM
  source, as `fhm format`, with format-on-save in the editors. Hovers would
  reuse its printer for declarations and long signatures. Today a type's hover
  uses a fixed one-constructor-per-line layout (so constructor docs fit), and
  long signatures stay on one line. The printer has to keep comments where
  they were, so the parser needs to keep them with their positions; the lexer
  already emits them as tokens.

## Playground

- [ ] **Embeds and "Open in playground" links.** Let the README, the language
  guide and other docs link each code block into the playground (a share
  link built at docs-build time), and maybe an embeddable read-only/runnable
  view for iframes.

## Language features

- [ ] **Type holes** in annotations, e.g. `Int -> (_, Bool) -> _ -> Int`.
  Each `_` is an unknown type to be inferred.
- [ ] **Named holes** `_a`: like `_`, but every `_a` in the same annotation
  stands for the same unknown type. They are inferred, not fixed.
- [ ] **Head-binder syntax**: `let f (x : a) y (z : c) : Int = ...`. The point
  of the syntax is that each parameter and the return type can be annotated or
  not, independently. A fully annotated head can already be lowered, but
  anything less is a partial annotation, so this needs type holes.

- [ ] **Patterns in lambda parameters**, e.g. `\(a, b) -> a`. The AST
  already allows a pattern, and lowering has a `@TODO(pattern-λ)` hook
  (`FHM/SurfaceBridge.lean`). Desugar `\p -> b` to `\x -> match x with
  p -> b`, reusing `lowerMatch` as `if` does. Touches the parser (only names
  and `_` parse today), `lowerExpr` and `LowersExpr`, the soundness,
  completeness and uniqueness proofs (a pattern lambda counts as a match),
  `SurfaceCovers`/`checkExhaustive`, and hover spans for the pattern's
  binders. A refutable pattern (`\(Just x) -> x`) is rejected by the
  exhaustiveness check, as an incomplete `match` is. Needs the nested-match
  exhaustiveness fix first.
- [ ] **Pattern lets**, e.g. `let (q, r) = divMod n 10`, locally and at the
  top level.
  - **Generalised, name by name.** Desugar `let p = e in b` to
    `let t = e in let x₁ = match t with p -> x₁ in … in b`, one `let` per
    name `xᵢ` that `p` binds, with `t` a hidden name that source can't
    write. This is the Haskell Report's translation (§4.4.3.2), made
    strict: `e` is evaluated once, and each `match` re-reads `t`, which
    can't fail since `p` is exhaustive. Each `xᵢ` is an ordinary `let`, so
    it's generalised as usual: `let (f, n) = (\x -> x, 1)` gives
    `f : ∀ a. a → a` and `n : Int`. No new typing rules. Generalising is
    safe because FHM is pure; OCaml, F# and SML restrict it only because of
    mutable references (the value restriction).
  - **Not recursive.** `e` can't mention the names `p` binds, and a pattern
    binding can't join a recursive group with other definitions; that's an
    error naming the cycle, like Elm's.
  - **Refutable patterns are rejected** by the exhaustiveness check, as for
    pattern lambdas.
  - **Top level:** the same translation, with `t` and each `xᵢ` as
    top-level bindings.

  [`recursion-language-comparison/FINDINGS-pattern-bindings.md`](./recursion-language-comparison/FINDINGS-pattern-bindings.md)
  compares GHC, OCaml, F#, SML and Elm. Every strict language rejects
  recursive pattern bindings. Generalising matches Haskell and Elm, the
  pure ones; Elm doesn't allow pattern bindings at the top level at all.

**Design decisions for partial annotations:**

- **Recursion.** A partial annotation (one with holes, or a head binder with
  unannotated parts) is not a complete type, so the binding is inferred like
  an unannotated one: it doesn't cut dependency edges and can't be used
  polymorphically inside its own recursive group.
- **Type variables.** A plain type variable such as `a` in a partial
  annotation refers to a type variable already in scope (from an enclosing
  annotation). If none is in scope, that's an unknown-type-variable error,
  as it is for complete annotations. Unknown types to be inferred are written
  `_` or `_a`.
- **New type variables on heads.** A head binder introduces new type variables
  with `{a}`, as in `let f {a} (x : a) y : a = ...`.

## Cleanup

- [ ] `FHM/AnnotatedPolyRecErasure.lean` and `FHM/AnnotatedPolyRecHybrid.lean`
  are prototype proofs from the annotated polymorphic recursion work, still in
  the default build. Move them somewhere clearly archival, or drop them from
  the build.
- [ ] Recursive grouping currently happens in two places: SCC analysis during
  lowering, and a second split of the unannotated members during inference.
  A single SCC pass per scope, ignoring edges into annotated definitions,
  would give the same results with one algorithm.

## Ideas

### `fails`: code that must not typecheck

- [ ] Sometimes you want code in the codebase that shows an expression does
  *not* typecheck: documenting where the type system draws a line, or pinning
  down that a mistake is caught. Today that code has to be commented out or
  kept in a file outside the build. Instead, a top-level declaration like

  ```
  fails (1 + True)
  ```

  would build only if its contents have a **type error**, and would itself be
  an error if they typecheck.

  Prior art: Idris 2's `failing "expected message"` blocks are almost exactly
  this. Also TypeScript's `// @ts-expect-error`, Rust's `compile_fail`
  doctests, and Haskell's `should-not-typecheck` (built on deferred type
  errors).

  Design notes:

  - **A declaration, not an expression or function.** Whether something
    typechecks is a property of an expression in its context, not of any
    value, so no function type could describe `fails`; giving it a type like
    `()` would misrepresent it. Like Idris's `failing`, it is a static
    assertion, in the same family as a type annotation (or Lean's `example`,
    or Rust's `const _: () = assert!(...)`). It has no runtime meaning, so
    purity is untouched.
  - **Only type errors count.** Parse errors inside the block are ordinary
    parse errors, and scope errors (unbound names, unknown type variables)
    should be too; otherwise `fails (lenght xs)` would pass because of a
    typo. Type mismatches are the valuable case.
  - **Expected errors.** Idris-style, a block could also state *which* error
    it expects, so it can't pass for the wrong reason. With errors as data
    (see above) that could name an error kind (`fails TypeMismatch (...)`)
    rather than match a message string. Worth considering once errors are
    data; type mismatch alone covers the main use.
  - **Checked after inference.** Each block is recorded with its context
    during inference and checked once the whole program has been inferred,
    under the final substitution. Nothing flows back into inference, so this
    can be a separate pass (a side condition on the program) rather than
    part of the verified `Infer` relation. Blocks are dropped before Core and
    don't affect evaluation or the safety theorems.
  - **Leftover type variables are flexible.** Some types never become
    concrete, because the code really is polymorphic. Matching apartness
    (below), such variables are flexible: the block holds only if no choice
    of them makes its contents typecheck. Type variables bound by enclosing
    annotations stay fixed.
  - **Failures are real.** Inference is proved complete
    (`typecheck_accepts_iff`), so rejection means no typing exists at all,
    not that the algorithm gave up.
  - **Start at the top level.** Top-level `fails` declarations, where every
    name has its final type, avoid most of the questions about surrounding
    local variables. Nested blocks can come later, using the rules above.

### Type apartness via `fails`

- [ ] Assert that two expressions *cannot* have the same type: the opposite
  of the usual "these have the same type" check, and often just as useful to
  document. The meaning wanted is **apartness**, as in GHC: the two types
  can't be unified however their type variables are chosen. Types that can
  be reconciled (`a -> a` and `b -> Int`, say) are not apart.

  No new type-system machinery is needed:

  ```
  let asTypeOf : {a} a -> a -> a = \x y -> x

  fails (asTypeOf e1 e2)   -- e1 and e2 are apart
  ```

  `asTypeOf e1 e2` typechecks exactly when the two types unify, so the `fails`
  block holds exactly when they're apart.

  This can't be wrapped in a user-defined function: inside
  `let apart = \a b -> fails (asTypeOf a b)`, the parameters `a` and `b` are
  just flexible type variables, so `asTypeOf a b` typechecks and the
  definition is itself an error. A nicer spelling (such as `e1 <!=> e2`) would
  have to be notation that expands to the `fails` idiom. (Comparing the
  *values* isn't part of this: in HM, comparing values of different types is
  already a type error.)

  Building disequality into inference as a constraint instead (like Prolog's
  `dif/2`) would be much harder, and a type such as "`x`'s type differs from
  `y`'s" in `\x y -> x <!=> y` can't be expressed as a plain HM type.

### Row types

- [ ] Investigate row types (extensible records, maybe variants) before
  building anything: what changes in `Ty`, unification (Rémy's rows or
  Leijen's scoped labels), the inference algorithm and above all its
  completeness proof (`typecheck_accepts_iff`), and whether pattern
  compilation has to know about records. Write it up as a brief with an
  estimate. Worth doing after errors as data.
