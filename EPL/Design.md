# EPL kernel contract

EPL is a cleanroom, explicitly polymorphic research language. It does not
import the FHM language or inference stack. `lake build EPL` checks every
definition, proof and test; nothing is assumed beyond Lean's three standard
axioms, which the build verifies for the headline theorems.

## The language

- Contexts contain rank-1 type schemes; variable uses instantiate them
  implicitly.
- An unannotated `let` is monomorphic.
- A polymorphic `let` writes its exact `forall` prefix. Written schemes never
  acquire inferred binders.
- `fix` binds its recursive binder monomorphically. There are no recursive
  binding groups, no implicit generalisation and no polymorphic recursion.
- Annotations on lambda parameters and `fix` binders are optional, and any
  annotation may be partial: it may contain named holes. Holes with the same
  name within one annotation stand for the same type. The surface `_` is a
  hole with a fresh name.
- Inference accepts exactly the programs that elaborate and have no other
  typing: every omitted binder type and every hole is determined. Unknowns
  introduced only to instantiate a scheme are not part of the elaboration and
  need not be determined (a use of `forall a. Int` is accepted).

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
so recursive and mutually recursive types are allowed. A declaration is well
formed (`DataDecl.WF`) when every field type mentions only its parameters;
the constants of an ill-formed declaration have no type.

Constructors are named by `CtorRef ⟨type, index⟩`; names are resolved
before the core, so a constructor always says which type it belongs to. A
constructor `C_i : forall params. fields_i -> T params` is an expression
(`Expr.ctor`) applied to its fields by ordinary application, like `Ty.con` is
applied by `Ty.app`. It is first class, and typing treats it like a variable
with a closed scheme.

`match scrutinee [(pattern, body), ...]` lists branches with explicit
constructor patterns. A branch body is a function of its constructor's
fields, so patterns bind nothing themselves. Typing requires at least one
branch, every pattern a constructor of the scrutinee's type `T args`, and
each body of type `fields_i[args] -> r`. Matches may be partial and may
repeat a pattern; the first matching branch is taken. A match with no
branches is not typable: its type would be unconstrained.

Exhaustiveness is separate from typing, as in FHM: `Exhaustive sig e` says
every match in `e` covers every constructor of the type its patterns name.
Progress assumes both typing and exhaustiveness.

Evaluation does not consult the signature. A constructor applied to values
is a value, and a match whose scrutinee is a constructor value steps to the
first branch for that constructor applied to the fields.

## Declarative typing

`TypingWith sig Det k ctx src elab ty`: at rigid depth `k`, in `ctx`, source
`src` has type `ty`, and `elab` is `src` with every implicit type filled in.
Expressions are parametric in their annotations: `Source = Expr Template`,
`Elab = Expr SemTy` (every annotation present) and `RuntimeExpr = Expr
Empty` (every annotation erased).
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

Inference stops at the first error. An `InferError` is a reason and the path
from the program's root to the expression it concerns; reasons carry only
what the source does not show, such as the two types of a mismatch and the
`UnifyError` (clash, occurs check or escape) inside them. Error values are not
part of the specification: the theorems say only when inference fails, and
which error it reports is unconstrained.

## Theorems

| Theorem | Statement |
|---|---|
| `infer_eq_ok_iff` | `infer` returns a result exactly when it elaborates the program and is its only typing |
| `infer_eq_error_iff` | `infer` reports an error exactly for the programs without such a typing |
| `infer_unique` | an accepted program has exactly one `Typing` |
| `infer_type_safety` | an accepted, exhaustive program never gets stuck |
| `evaluate` | infer, check exhaustiveness, erase and run; returns a typed value or a typed term that can still step, or why it did not run |
| `inferAt_spec` | a successful run is sound and principal; a failed run means no model elaborates |
| `MStore.unify_sound`, `MStore.unify_complete` | the result's models are exactly the input's models that equate the two types |
| `TypingWith.erase` | erasure preserves typing |
| `RuntimeTyping.progress`, `RuntimeTyping.preservation` | type safety of the erased runtime (progress assumes `Exhaustive`) |
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
| `Spec/Exhaustive.lean` | the exhaustiveness check, and preservation of exhaustiveness |
| `Spec/Runtime.lean` | weakening, substitution, progress, preservation |
| `Spec/Declarative.lean` | regularity and erasure |
| `Spec/Models.lean` | valuations, models and store invariants |
| `Spec/Unify.lean` | unification is sound, complete, safe and anchored |
| `Spec/Store.lean` | allocation, and the `InferPre`/`InferPost`/`InferSpec` contract |
| `Spec/InferLet.lean` | the explicit-let case of inference |
| `Spec/Infer.lean` | `inferAt_spec` |
| `Theorems.lean` | the headline theorems and `evaluate` |
| `Tests.lean` | executable checks of inference, unification and evaluation |

## Surface language

`EPL/Surface/` is an unverified front end (`lake build EPLSurface`) with
FHM's syntax: `type` declarations, top-level `let`s and a final expression,
function heads `let f {a} (x : a) y : R = ...`, `_` and `?a` holes, `\x -> e`,
`if`, `+ - < ::`, pairs, lists, strings (`List Char`) and `match` with nested
patterns. It stops at the first error, reported as a typed error with a
source span. `runToString` runs a program end to end through `evaluate`.

Lowering (`Lower.lean`) produces the core term and signature:

- The prelude declares `Bool` (declaration 0), `List` and `Pair`; the sugar
  denotes their constructors.
- The bindings of a block may come in any order and are sorted by use. A
  binding that mentions itself becomes a `fix`; mutual recursion is rejected.
- A binding with any annotation becomes an explicit `let` whose signature is
  its head (missing parts are fresh holes); one without is a monomorphic `let`.
- Matches compile to nested core matches on one constructor at a time.
  Constructor patterns are checked against their arity, and unreachable arms
  are rejected. A case no arm covers is left out of the core match, so
  `evaluate` rejects the program as not exhaustive; the lowering records the
  constructor and where it is missed, for the error message.
- An `Origin` tree of the core term's shape records each node's source span,
  so an `InferError`'s path leads to the source. A mismatch at an application
  is reported at its argument (parameter type against argument type), or at
  its function if that is not a function.
- Each `Origin` node also records what the core node is in the source: the
  value of a surface expression, a use of a name or an infix operator, or the
  binder of a variable. Lowering lists every name the source defines with the
  binder it stands for, and the type names, type variables, pattern
  constructors and pattern `::`s it mentions.

Types for editors come from inference itself: `inferWithTypes` also returns a
`TypeTree`, the type of every core node in the term's shape
(`inferWithTypes_fst`: it accepts and rejects exactly as `infer` does). A
node's type is the one at the same path in the `TypeTree` as its `Origin`, so
`Lowering.symbols` gives each defined name its binder's type, and each use and
expression its own. Spans stay out of the core term. Types and constructors
show their declaration, and type variables what binds them.

Doc comments (`--- text` or `/-- text -/`) are FHM's: a run of them documents
the `let`, type or constructor it comes before, and one before anything else
is an error. The lexer keeps comments aside, and `frontEnd` attaches each doc
comment to the names it documents, for hover at the definition and its uses.

The `epl` executable (`lake build epl`) runs a file (`epl [run] [--fuel N]
file.epl`, printing each top-level binding's type and the program's, then its
value, as `fhm run` does), checks it (`epl check`), or prints editor JSON
(`epl diagnose`, the shape `fhm diagnose` prints: the first error, symbols
with types and docs, and tokens). The editor extension in `editors/vscode`
highlights `.epl` files, shows their first error, shows types and docs on
hover, goes to definitions, and runs files (`EPL: Run File`).
`EPL/examples/playground.epl` is a tour.

| File | Contents |
|---|---|
| `Surface/Syntax.lean` | the surface AST, with spans |
| `Surface/Lex.lean` | the lexer, and comments with their doc text |
| `Surface/Parse.lean` | the parser (recursive descent, FHM's layout rules) |
| `Surface/Lower.lean` | name resolution, binding order, pattern compilation, origins |
| `Surface/Run.lean` | the pipeline, symbols for editors, printing of types, values and errors |
| `Surface/Main.lean` | the `epl` executable |
| `Surface/Tests.lean` | whole-program tests, including one per error kind |
