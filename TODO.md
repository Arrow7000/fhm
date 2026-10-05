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

## Bugs

- [ ] **Exhaustiveness checker rejects complete nested matches.**
  `checkExhaustive` is sound (it never accepts an incomplete match) but not
  complete: some matches whose patterns go more than one constructor deep are
  rejected with `match not exhaustive` even though they cover every case.

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
  - Show doc comments (needs a doc-comment syntax).
  - For annotated bindings, show the inferred type when it differs from the
    annotation.
  - With error recovery, show something like "type unknown (error in `g`)"
    instead of nothing.

## Language features

- [ ] **Type holes** in annotations, e.g. `Int -> (_, Bool) -> _ -> Int`.
  Each `_` is an unknown type to be inferred.
- [ ] **Named holes** `_a`: like `_`, but every `_a` in the same annotation
  stands for the same unknown type. They are inferred, not fixed.
- [ ] **Head-binder syntax**: `let f (x : a) y (z : c) : Int = ...`. The point
  of the syntax is that each parameter and the return type can be annotated or
  not, independently. A fully annotated head can already be lowered, but
  anything less is a partial annotation, so this needs type holes.

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
  kept in a file outside the build. Instead, something like

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

  - **Only type errors count.** Parse errors inside the block are ordinary
    parse errors, and scope errors (unbound names, unknown type variables)
    should be too; otherwise `fails (lenght xs)` would pass because of a
    typo. Type mismatches are the valuable case.
  - **Expected errors.** Idris-style, a block could also state *which* error
    it expects, so it can't pass for the wrong reason. With errors as data
    (see above) that could name an error kind (`fails TypeMismatch (...)`)
    rather than match a message string. Worth considering once errors are
    data; type mismatch alone covers the main use.
  - **Check once, after inference.** The block is checked in its surrounding
    context but feeds nothing back into inference, and is dropped before Core,
    so it doesn't affect evaluation or the safety theorems.
  - **Failures are real.** Inference is proved complete
    (`typecheck_accepts_iff`), so rejection means no typing exists at all,
    not that the algorithm gave up.
  - **Open question: blocks inside functions.** What does the block assume
    about surrounding variables whose types aren't settled yet? Matching
    apartness (below) means treating them as flexible ("could these ever
    unify?"), while type variables from enclosing annotations stay fixed.
    The simplest start is to allow `fails` only at the top level, where every
    name has its final type.

### Type apartness, as a library function over `fails`

- [ ] Assert that two expressions *cannot* have the same type: the opposite
  of the usual "these have the same type" check, and often just as useful to
  document. The meaning wanted is **apartness**, as in GHC: the two types
  can't be unified however their type variables are chosen. Types that can
  be reconciled (`a -> a` and `b -> Int`, say) are not apart.

  This needs no special operator:

  ```
  let asTypeOf : {a} a -> a -> a = \x y -> x

  fails (asTypeOf e1 e2)   -- e1 and e2 are apart
  ```

  `asTypeOf e1 e2` typechecks exactly when the two types unify, so the `fails`
  block holds exactly when they're apart. A wrapper with a nicer name (or an
  operator such as `<!=>`) can be defined once `fails` exists. (Comparing the
  *values* isn't part of this: in HM, comparing values of different types is
  already a type error.)

  Building disequality into inference as a constraint instead (like Prolog's
  `dif/2`) would be much harder, and a type such as "`x`'s type differs from
  `y`'s" in `\x y -> x <!=> y` can't be expressed as a plain HM type.
