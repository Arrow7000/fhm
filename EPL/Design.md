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
- Completeness and principality are not initial goals. Sound inference and
  runtime type safety are.

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

The first kernel deliberately makes no claim of inference completeness,
principal types, implicit generalisation, or polymorphic recursion.

## Algorithmic boundary

`Unification` distinguishes its public empty-substitution entry point from its
internal accumulator. Successful public runs are proved sound and scoped.
Reachable substitutions are stable under reapplication and are extended only
with forward bindings. Arbitrary preloaded association lists are deliberately
outside the soundness contract; inference composes public solver results
instead of passing hostile initial substitutions to the worker.

Annotation allocation reserves one metavariable per distinct local `?name`,
then one per anonymous `_` occurrence. Separate calls rebuild the name table;
the inference caller must thread `Allocation.next` between calls so distinct
annotations receive disjoint metavariable ranges.

The public inference entry point validates `Expr.TypeScoped` before allocating
anything. In particular, authored fixed annotations cannot contain inference
metavariables or out-of-scope bound/rigid variables and therefore cannot forge
or capture an allocator-generated ID.

Inference distinguishes ordinary fresh metavariables from obligations. Fresh
variables used to instantiate a scheme may remain irrelevant when a binder is
phantom. Holes in authored annotations and omitted lambda parameter types are
obligations and must have semantic solutions before a successful boundary is
crossed. This rejects ambiguous lambdas even when hidden in a dead `let`
without rejecting a valid use of a scheme such as `forall a. Int`.

Checking an explicit scheme uses a lexical metavariable region. The completed
scheme and all local obligations must be semantic before leaving the region;
the retained outer solution-table prefix is checked for local rigid or
metavariable escape. The local frontier is then restored, so its discarded IDs
can be reused safely. The public `InferenceResult` exposes only its closed,
well-scoped type, not this internal allocation state.

Inference state uses a dense canonical solution table rather than carrying the
unifier's ordered association list between syntax nodes. Entry `i` is the
current normalized meaning of metavariable `i`, with an unsolved entry equal
to `mvar i`. A successful constraint maps its short-lived solver substitution
over the whole table. This makes allocation, semantic lookup, and lexical
projection ordinary list append, indexing, and prefix operations; ordering and
duplicate-target concerns remain confined to the separately verified unifier.
