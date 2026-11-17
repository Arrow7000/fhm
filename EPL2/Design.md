# EPL2 kernel contract

EPL2 is a cleanroom, explicitly polymorphic research language. It does not
import the FHM language or inference stack. `lake build EPL2` checks every
definition, proof and test; nothing is assumed beyond Lean's three standard
axioms, which the build verifies for the headline theorems.

## The language

- Contexts contain rank-1 type schemes; variable uses instantiate them
  implicitly.
- An unannotated `let` is monomorphic.
- A polymorphic `let` writes its exact `forall` prefix. Written schemes never
  acquire inferred binders.
- Lambda parameter annotations are optional, and any annotation may be
  partial: it may contain named holes. Holes with the same name within one
  annotation stand for the same type. The surface `_` is a hole with a fresh
  name.
- `fix` binds an annotated self type monomorphically. There are no recursive
  binding groups, no implicit generalisation and no polymorphic recursion.
- Inference accepts exactly the programs with a unique elaboration: every
  omitted parameter type and every hole is determined. Unknowns introduced
  only to instantiate a scheme are not part of the elaboration and need not
  be determined (a use of `forall a. Int` is accepted).

## Types

There is one type syntax, `Ty V`, parametric in what its flexible variables
are:

| Type | Flexible variables | Used for |
|---|---|---|
| `SemTy = Ty Empty` | none | declarative types |
| `InfTy = Ty Nat` | metavariables `?id` | inference |
| `Template = Ty String` | named holes | source annotations |

Two further kinds of variable are natural numbers at every `V`:

- `bvar i` is bound by the enclosing `Scheme` (de Bruijn index). It occurs
  only in scheme bodies: in contexts and in data declarations.
- `rigid l` is a type variable in scope, named by *level*: the binders of
  the written schemes enclosing a source position are levels `0, 1, ...`,
  outermost first.

Source annotations name type variables by level, so no source term is ever
re-indexed, and checking a scheme with `n` binders at depth `k` uses the
levels `k, ..., k + n - 1` with no freshness side conditions.

Every operation that replaces variables (`bind`, `lift`, `instantiate`,
`substRigids`, `closeRigids`) is an instance of one traversal, `Ty.subst`.
It is not capture-avoiding; the lemmas that commute a substitution with
`instantiate` ask for images without bound variables.

## Data types

A program is a `Signature` (a list of `DataDecl`s) and an expression; the
signature is a parameter of every judgment and of evaluation. Declaration
`i` is the type constructor `Ty.con i`. Types are applied with binary
`Ty.app`, and kinds are not checked: an ill-kinded type such as `Bool Int`
is a type without values. A declaration lists, per constructor, its field
types over the declaration's parameters (`bvar`s) and any declared types,
so recursive and mutually recursive types are allowed.

Each declaration contributes constants with closed schemes:

- constructor `C_i : forall params. fields_i -> T params`;
- eliminator `elim_T : forall params r. T params -> branch_1 -> ... ->
  branch_k -> r`, where `branch_i = Unit -> fields_i -> r`.

Surface `match` is an application of the eliminator to one branch function
per constructor, in declaration order; `if` is a match on `Bool`, which by
convention is declaration 0. Each branch first receives `()`, so
call-by-value evaluation does not run the branches a match does not take.
Typing and inference treat constants exactly like variables with closed
schemes. A constant's arity is read from the signature: a constant applied
to fewer arguments than it consumes is a value, and a saturated eliminator
meeting a saturated constructor reduces to the chosen branch applied to
`()` and the fields.

## Declarative typing

`TypingWith sig Det k ctx src elab ty`: at rigid depth `k`, in `ctx`, source
`src` has type `ty`, and `elab` is `src` with every implicit type filled in.
The relation takes a side condition `Det` on explicit lets, which gives two
judgments from one set of rules:

- `Typing` imposes no condition.
- `Elaborates` imposes `Determined`: no other completion of a polymorphic
  signature's holes lets its right-hand side check. Later uses could not
  tell apart completions that mention the scheme's own binders, so
  `let f : forall a. _ -> a -> a = fun z y => y in f True True` is typable
  but does not elaborate. A signature without binders is an ordinary partial
  annotation, which later uses may determine.

An explicit let checks its right-hand side once, generically, at the fresh
levels, and binds exactly the completed scheme in its body. There are no
scoping premises on source annotations: an annotation with an out-of-scope
variable matches no well-formed type.

`RuntimeTyping` types erased programs. Its single `let` rule asks the
right-hand side to have every instance of the bound scheme at every deeper
rigid depth, so weakening and value substitution need no type-level
reasoning. Erasure turns the generic check of an explicit let into that
form with one type-substitution lemma.

## Inference

Inference state is a dense table `MStore = List MEntry`: entry `i` holds
`?i`'s level and, once solved, its solution. Solutions mention only
unsolved metavariables, so resolving a type is one lookup per metavariable.
The table's length is the allocation frontier.

Metavariables carry Rémy-style levels (as in OCaml): a metavariable at
level `L` may only be solved to a type whose rigid variables are below `L`,
and binding it lowers the metavariables of its solution to `L`. This is the
whole rigid-escape check.

Unification is Robinson's algorithm with the table as its solved form. It
recurses structurally on fuel that is internal and proved sufficient, so
`decide` evaluates it and `MStore.unify` takes no fuel argument.

`inferAt` recurses structurally on the source. For an explicit let with `n`
binders at depth `k` it allocates the annotation's holes at level `k + n`,
infers the right-hand side at depth `k + n`, unifies, and then requires
every metavariable left in the completed scheme to be at level `k` or
below. A hole still at an inner level could equally have been one of the
scheme's own binders, so the signature is ambiguous. Other unknowns created
inside the right-hand side are kept and may be determined by later code.

`infer` runs `inferAt` on a closed program and accepts it when the resolved
type and every annotation of the resolved elaboration are ground.

## Theorems

| Theorem | Statement |
|---|---|
| `infer_eq_some_iff` | `infer` returns a result exactly when it is the program's unique elaboration |
| `infer_eq_none_iff` | `infer` rejects exactly the programs without a unique elaboration |
| `infer_unique` | an accepted program has exactly one `Typing` |
| `infer_type_safety` | an accepted program never gets stuck |
| `evaluate` | infer, erase and run; returns a typed value or a typed term that can still step |
| `inferAt_spec` | a successful run is sound and principal; a failed run means no model elaborates |
| `MStore.unify_sound`, `MStore.unify_complete` | the result's models are exactly the input's models that equate the two types |
| `TypingWith.erase` | erasure preserves typing |
| `RuntimeTyping.progress`, `RuntimeTyping.preservation` | type safety of the erased runtime |
| `Eval.step?_sound`, `Eval.step?_complete`, `Eval.Step.deterministic` | the executable evaluator is the step relation |

## How the proofs are organised

A *valuation* gives every metavariable a semantic type. It *models* a store
when it gives each allocated metavariable a type well-formed at that
metavariable's level and satisfies every solution. Each store operation is
specified by how it changes the set of models, and `inferAt_spec` is one
induction on the source proving `InferSpec`:

- on success, `InferPost`: the store stays safe and only grows, levels only
  decrease, every model of the result is a model of the input under which
  the program elaborates as inferred (soundness), and every typing under a
  model of the input is the inferred one under some extension of that model
  (principality);
- on failure, the program elaborates under no model of the input.

| File | Contents |
|---|---|
| `Syntax.lean` | types, schemes, templates, declarations, expressions |
| `Typing.lean` | `TypingWith`, `Typing`, `Elaborates`, `RuntimeTyping` |
| `Runtime.lean` | values, the step relation, the executable evaluator |
| `Unify.lean` | the metavariable store and unification |
| `Infer.lean` | `inferAt` and `infer` |
| `Spec/Syntax.lean` | laws of `Ty.subst` and its instances |
| `Spec/Eval.lean` | the evaluator agrees with the step relation |
| `Spec/Runtime.lean` | weakening, substitution, progress, preservation |
| `Spec/Declarative.lean` | regularity and erasure |
| `Spec/Models.lean` | valuations, models and store invariants |
| `Spec/Unify.lean` | unification is sound, complete, safe and anchored |
| `Spec/Store.lean` | allocation, and the `InferPre`/`InferPost`/`InferSpec` contract |
| `Spec/InferLet.lean` | the explicit-let case of inference |
| `Spec/Infer.lean` | `inferAt_spec` |
| `Theorems.lean` | the headline theorems and `evaluate` |
| `Tests.lean` | executable checks of inference, unification and evaluation |
