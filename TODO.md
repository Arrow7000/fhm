# TODO

Known bugs and smaller tasks. The bigger picture lives in the
[README roadmap](./README.md#roadmap).

## Bugs

### Exhaustiveness checker rejects complete nested matches

`checkExhaustive` is sound (it never accepts an incomplete match) but not
complete: some matches whose patterns go more than one constructor deep are
rejected with `match not exhaustive` even though they cover every case.

```fsharp
type Maybe a = Just a | Nothing

let g = \m ->
  match m with
  | Just (Just x) -> x
  | Just Nothing -> 0
  | Nothing -> 0

g (Just (Just 3))
```

The same happens with nested lists:

```fsharp
let h = \xs ->
  match xs with
  | [] -> 0
  | [] :: _ -> 1
  | (y :: _) :: _ -> y

h [[5]]
```

Suspected cause: when the checker guesses a nested scrutinee's type arguments
(`tyArgsGuess` in `FHM/SurfaceBridge.lean`), it uses placeholders that fail
closed.

### Parser swallows a bare program body after a `type` declaration

If a `type` declaration is followed directly by the program's final
expression, the parser reads that expression as an extra constructor field of
the declaration's last constructor:

```fsharp
type Color = Red | Green | Blue

Red
```

This fails with `[lower] lowering failed`, because `Blue` now appears to take
a `Red` argument. `(Red)` fails the same way. Any `let` between the
declaration and the body hides the problem:

```fsharp
type Color = Red | Green | Blue

let c = Red

c
```

The constructor-field parser (`dataCtor` / `ctorField` in
`FHM/Unverified/Surface/Parse.lean`) should stop at the end of the
declaration's layout block.

## Error messages

- `fhm run` reports only `[typecheck] typechecking failed`. `fhm diagnose`
  names the failing definition, but neither gives a location or a reason.
- Lowering errors are a single generic message: `lowering failed (unbound
  name, bad decl, or rejected sugar)`.

## Cleanup

- `FHM/AnnotatedPolyRecErasure.lean` and `FHM/AnnotatedPolyRecHybrid.lean`
  are prototype proofs from the annotated polymorphic recursion work, still in
  the default build. Move them somewhere clearly archival, or drop them from
  the build.
- Recursive grouping currently happens in two places: SCC analysis during
  lowering, and a second split of the unannotated members during inference.
  A single SCC pass per scope, ignoring edges into annotated definitions,
  would give the same results with one algorithm.
