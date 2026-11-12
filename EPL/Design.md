# EPL kernel contract

EPL is a cleanroom, explicitly polymorphic research language. It does not
import the FHM language or inference stack.

## Initial language

- Contexts contain rank-1 type schemes.
- Variable uses instantiate schemes implicitly.
- An unannotated `let` is monomorphic.
- A polymorphic `let` must write its exact `forall` prefix.
- Written schemes never acquire additional inferred binders.
- Lambda parameter annotations are optional. An omitted annotation introduces
  a local inference metavariable; a successful public result may not contain
  unresolved metavariables.
- `_` and `?name` are Core-native partial annotations. Named holes share only
  within their enclosing annotation.
- Recursive binding groups do not exist. A separately typed `fix` binder will
  provide monomorphic general recursion.
- Inference should be sound and complete: it accepts exactly the typable
  programs whose implicit types (omitted lambda parameter types and
  annotation holes) are uniquely determined. Unknowns introduced only to
  instantiate a scheme need not be determined.

## Variable classes

`Ty` deliberately distinguishes:

- `bvar`: bound by a `Scheme`;
- `rigid`: an authored variable or skolem used while checking a written
  scheme;
- `mvar`: a flexible inference metavariable.

Declarative well-formedness excludes `mvar`. Algorithmic scoping admits it,
but only unification metavariables may be solved.

## Declarative contract

The public judgment is `Typing rigidCount ctx expr ty`.

- `Typing.var` opens a context scheme with arbitrary well-formed semantic
  types.
- `Typing.lambda` chooses a well-formed parameter type constrained by the
  optional partial annotation.
- `Typing.letMono` binds the inferred RHS monomorphically.
- `Typing.letPoly` checks an explicitly written scheme at one fresh block of
  rigid levels and binds exactly that scheme in the body. Its unopened RHS
  annotations must be scoped under the outer rigid boundary and the written
  binders, and its ambient context must be well-formed at the outer boundary;
  neither source syntax nor a context entry can smuggle a rigid into the fresh
  skolem block.
- `Typing.fix` binds its annotated self type monomorphically.

The rigid-level count makes fresh skolem allocation deterministic. Checking a
scheme with `n` binders uses rigid levels `k, ..., k+n-1`; no protected-variable
set or cofinite fresh-name quantifier is needed.

## Intended theorem boundary

The kernel should establish, without custom axioms:

1. annotation-local names are coherent;
2. opening preserves scope and meta-freedom;
3. declarative typing produces a well-formed semantic type;
4. rigid-scope weakening;
5. runtime term weakening and substitution;
6. generic rigid-block checking supports arbitrary well-formed scheme
   instantiations at every larger rigid boundary;
7. erasure preserves typing;
8. progress and preservation for the erased runtime;
9. executable checking/inference is sound;
10. successful public results contain no unresolved metavariables.

Both claims are now established: `inferFuel_sound_model` connects every
successful internal run to declarative typing under every semantic model of
its result state, and `infer_sound` specializes that result to the closed type
returned by the public entry point.

The kernel deliberately makes no claim of
implicit generalisation or polymorphic recursion. Completeness is in progress.

## Algorithmic boundary

Annotation allocation reserves one metavariable per distinct local `?name`,
then one per anonymous `_` occurrence. Separate calls rebuild the name table;
the inference caller must thread `Allocation.next` between calls so distinct
annotations receive disjoint metavariable ranges.

The public inference entry point validates `Expr.TypeScoped` before allocating
anything. In particular, authored fixed annotations cannot contain inference
metavariables or out-of-scope bound/rigid variables and therefore cannot forge
or capture an allocator-generated ID.

Inference returns, besides the type, an elaboration of the program: the same
expression with every lambda parameter type, `fix` type and explicit scheme
filled in (`Elaborates` is the declarative counterpart). A program is accepted
exactly when its type and its elaboration are fully determined. Unknowns that
only instantiate a scheme are not part of the elaboration, so they need not
be determined (a valid use of `forall a. Int` is accepted).

Inference state is a dense table `MStore := List MEntry`: entry `i` holds
`?i`'s level and, once solved, its solution; solutions mention only unsolved
metavariables. Resolving a type is one lookup per metavariable. Unification
is Robinson's algorithm with this table as its solved form: binding
`?i := ty` writes entry `i`, eliminates `?i` from every other entry and from
the pending constraints, and lowers levels (below). It recurses structurally
(so `decide` evaluates it) with fuel that is proved sufficient, and it is
proved sound and complete: its result's models are exactly the input's
models that equate the two types. A model gives each metavariable a type
well-formed at that metavariable's level.

Checking an explicit scheme opens its binders as a fresh block of rigid
levels. Metavariables carry Rémy-style *levels* (as in OCaml): a metavariable
at level `L` may only be solved to a type whose rigid variables are below
`L`, and binding it lowers the metavariables of its solution to `L`. Holes in
the written scheme, and unknowns created while checking its right-hand side,
start at the inner level and are lowered as soon as they become part of an
outer unknown's solution. This is the whole rigid-escape check.

Partial signatures are completed from their definition and its context,
never from later uses: after checking, every metavariable left in the
completed scheme must be at the outer level. A hole still at the inner level
could equally have been one of the scheme's own binders, so the signature is
ambiguous (`let f : forall a. _ -> a -> a = fun z y => y in f true true` is
rejected). Other unknowns are simply kept: an unannotated parameter inside
the definition may be determined by later code (`fun x => let f : forall a.
a -> a = (let _ = (fun z => x z) in fun y => y) in x 1 + 1`).
