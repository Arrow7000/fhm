# FHM: Formalised Hindley–Milner

FHM is a small, Elm-flavoured functional language with Hindley–Milner type
inference, formalised in Lean 4, with a command-line tool, watch mode, and browser
playground. Its canonical frontend elaborates anonymous and annotation-local named type holes, with proved
soundness, annotation fidelity, principality, and completeness, including recursive
groups and partial signatures. The completed-Core type system also has proved
type safety. See the [feature details](./docs/anonymous-type-holes.md).

The [partial Core architecture](./docs/partial-core.md) judges source annotations
directly. Inference proves that judgment, and runtime soundness follows by
erasure. Ordinary, signed, and recursive annotations retain one local completion
before fresh scheme openings. The editor uses inferred node types, binder
schemes and source provenance; inference returns no completed expression.

## A taste of the language

```
type Maybe a = Just a | Nothing

type Tree a =
  | Leaf
  | Node a (Tree a) (Tree a)

-- No annotation needed: the most general type is inferred.
let map = \f xs ->
  match xs with
  | [] -> []
  | x :: rest -> f x :: map f rest

let head = \xs ->
  match xs with
  | [] -> Nothing
  | x :: _ -> Just x

-- Annotations are optional, and checked when given.
let insert : Int -> Tree Int -> Tree Int = \n t ->
  match t with
  | Leaf -> Node n Leaf Leaf
  | Node m l r ->
    if n < m then Node m (insert n l) r
    else Node m l (insert n r)

-- The last expression is the program's result.
(map (\n -> n + 1) [1, 2, 3], (head [True, False], insert 2 (insert 3 Leaf)))
```

Running it with `fhm run` prints the inferred types, then the result:

```text
  insert  :  Int → Tree Int → Tree Int
  head  :  ∀ a. List a → Maybe a
  map  :  ∀ a b. (a → b) → List a → List b
  <program>  :  (List Int, (Maybe Bool, Tree Int))

⟹  ([2, 3, 4], (Just True, Node 3 (Node 2 Leaf Leaf) Leaf))
```

Ill-typed programs and non-exhaustive matches are rejected before anything runs.

## Language features

- **Hindley–Milner type inference** with let-polymorphism. No annotations are
  required.
- **Optional type annotations** on `let` bindings (`let id : {a} a -> a = …`)
  and lambda parameters (`\(n : Int) -> …`). Annotations are checked, not
  trusted. The type variables an annotation introduces are in scope throughout
  the definition's body, so inner annotations can refer to them.
  Function heads can mix typed and untyped parameters: `let add (x : Int) y : Int = x + y`.
  A type after head parameters describes the return value; omitted types are
  inferred. `let keep {a} (x : a) ignored : a = x` scopes `a` through the body.
- **Anonymous type holes** in expression annotations: `\(x : _) -> x` or
  `let f : {a} a -> _ = …`. Each `_` is inferred independently; eligible
  variables generalise, and authored forall names retain their order.
- **Annotation-local named holes:** `\(p : (?item, ?item)) -> p` requires both
  components to have the same type. Different names are independent. The same
  spelling in a separate annotation is unrelated, including separate parameter
  and result annotations in a function head. Hover a `?name` to see its solution.
- **Algebraic data types**, including parameterised and recursive ones.
- **Nested pattern matching** with wildcards. Matches must be exhaustive.
  Lambda parameters accept exhaustive patterns too: `\(x, y) -> x` or
  `\((x, y), z) -> y`. Applied constructors need parentheses (`\(Box x) -> x`);
  refutable parameters such as `\(Just x) -> x` are rejected with missing cases.
  Whole patterns can be annotated: `\((x, y) : (Int, Bool)) -> x`.
- **Pattern lets**, locally and at top level: `let (f, n) = (\x -> x, 1)`.
  Each name is generalised independently; `f` can be used at both `Int` and
  `Bool`. Patterns must be exhaustive and cannot participate in recursion.
  Like ordinary lets, evaluation is call-by-name: unused RHSs are skipped,
  and multiple uses may repeat work. Shared call-by-need evaluation is deferred.
- **Recursion and mutual recursion** between definitions written in any order.
  Unannotated recursive definitions follow standard HM. A complete written
  polymorphic signature permits polymorphic recursive calls, including in its
  own body. Partial signatures constrain the whole monomorphic SCC before
  export and do not permit polymorphic recursive calls.
- Built-in `Int`, `Bool`, pairs, and lists, with `+`, `-`, `<`, `::`, list
  literals, `if`/`then`/`else`, and `let … in` blocks.

[`scratch/anonymous-type-holes.fhm`](./scratch/anonymous-type-holes.fhm) is a
runnable playground with scattered function-head annotations and anonymous holes:
try the examples and hover their parameters and `_` tokens.
[`scratch/named-type-holes.fhm`](./scratch/named-type-holes.fhm) demonstrates
named holes, mixed holes, and annotation-local scope.
[`scratch/language-guide.fhm`](./scratch/language-guide.fhm) walks through
annotations and recursion with runnable examples, and
[`recursion-language-comparison/`](./recursion-language-comparison/) compares
FHM's recursion rules with GHC, OCaml, F#, Elm and Standard ML.

## What is proved

All of the following are machine-checked, with no `sorry` and only Lean's
standard axioms. [`FHM/Headlines.lean`](./FHM/Headlines.lean) gathers the
canonical production theorems. The opt-in
[`FHM/Headlines/CompleteCore.lean`](./FHM/Headlines/CompleteCore.lean) preserves
the earlier complete-Core surface-safety façade and demonstration.

| Claim                                                                                                                                              | Main theorems                                                             |
| -------------------------------------------------------------------------------------------------------------------------------------------------- | ------------------------------------------------------------------------- |
| **Runtime type safety:** a closed, well-typed, erased term with exhaustive matches is a value or can step; steps preserve its type. | `RuntimeTyping.RunWT.progress`, `RuntimeTyping.RunWT.preservation`, `InputTyping.erase` |
| **Complete-Core surface safety:** a well-typed, exhaustive surface program accepted by the Core lowering bridge never gets stuck.                  | `program_type_safe`, `surface_type_safe`                                  |
| **Surface lowering preserves partial annotations:** the structural lowering relation and executable lowerer agree on canonical `InferInput`, including holes, heads, patterns, and recursive groups. | `lower_sound`/`lower_complete`, `lowerProgram_sound`/`lowerProgram_complete` |
| **Canonical inference is sound:** successful inference directly proves partial-source typing; erasure of the original source gives runtime typing. | `InferCert.inputSound_source`, `InferCert.inputSound`, `InputTyping.erase`, `inferWithTypes_runtime_sound` |
| **Canonical inference is complete and principal:** inference accepts exactly independently well-typed partial inputs, and every valid result type factors through the inferred type. | `Infer.principal`, `Infer.complete`, `inferCore_accepts_iff`, `inferWithTypes_accepts_iff` |
| **Complete Core uses the same inference engine:** `Expr.ofCore` preserves source typing, acceptance, and residual principality. | `SurfaceBridge.coreTypecheck_accepts_iff`, `SurfaceBridge.inferOfCore_source_sound`, `SurfaceBridge.inferOfCore_principal` |
| **Pattern compilation is correct:** nested matches compile to decision trees that select the same branch with the same bindings.                   | `PatComp.compile_correct_surface`, `PatComp.lowerMatch_adequate_of_typed` |
| **Exhaustiveness checking is sound:** if the checker accepts a match, the match is exhaustive.                                                     | `checkExhaustive_sound`                                                   |
| **Recursive grouping is correct:** dependency analysis splits definitions into exactly their strongly connected components.                        | `sccGroups_sound`, `sccGroups_complete`, `kosaraju_sound`                 |
| **Data declarations elaborate faithfully:** the returned environment contains exactly the written constructors, with their names, parameter counts, parent types, fields and declaration order. | `DataDecls.ElaboratesTo`, `elabDecls_eq_some_iff`, `lowerProgram_sound`/`_complete` |

**What is not verified:** the lexer, parser, CLI, editor tooling, and the
unbounded evaluator used by `fhm run`. These live under
[`FHM/Unverified/`](./FHM/Unverified/README.md) and are kept out of the
verified build. Verified lowering starts at the surface syntax tree and returns
canonical `InferInput := Expr TyTemplate`; inference returns type and editor
facts. Successful production provenance lowering is proved to return that same input term. Its
source-span tables and editor joins remain operational code. The
verified evaluator (`runSafe` in `Headlines.lean`) is fuel-bounded, because the
language allows non-terminating programs.

## Getting started

You need [`elan`](https://github.com/leanprover/elan); the pinned Lean version
is in [`lean-toolchain`](./lean-toolchain).

```bash
lake exe cache get   # download prebuilt Mathlib (avoids compiling it locally)
lake build           # check the production verified library
lake build FHMCompatibility FHMExamples FHMHistorical  # opt-in compatibility, examples, artifacts
lake build fhm       # build the fhm executable
```

### Running programs

```bash
.lake/build/bin/fhm run path/to/program.fhm          # infer types, then evaluate
.lake/build/bin/fhm --json path/to/program.fhm       # the same, as JSON
.lake/build/bin/fhm run --fuel 100000 program.fhm    # stop after 100000 evaluation steps
.lake/build/bin/fhm diagnose path/to/program.fhm     # diagnostics and hover info for editors
```

The CLI and playground stop evaluation when the erased expression exceeds depth
512, reporting `eval.depthLimit` at the program entry expression with the completed
step count. This conservative guard prevents the known deep-recursion stack crash;
it is separate from `--fuel`, which limits reduction steps. It may reject deep
computations (including values) that a future evaluator with an explicit
continuation stack could handle. It covers evaluation, not parsing/typechecking,
and does not change the verified `runSafe` or its theorems.

For a REPL-like loop that re-runs the program every time you save:

```bash
scripts/watch-live.sh                     # watches scratch/live.fhm
scripts/watch-live.sh path/to/program.fhm
```

This uses `entr` or `fswatch` if available and falls back to polling.

### Browser playground

A Monaco editor that type-checks and evaluates the program as you type, with
inline errors and hover types. The URL always encodes the current program, so it
doubles as a share link:

```bash
lake build fhm
cd editors/web
npm install
npm run dev          # http://localhost:5173
```

### VS Code / Cursor

[`editors/vscode/`](./editors/vscode/) provides syntax highlighting,
diagnostics, and hover types:

```bash
scripts/install-vscode-extension.sh   # VS Code
scripts/install-cursor-extension.sh   # Cursor
```

## How it works

```text
source text
  → parse                   (unverified)
  → surface syntax tree
  → lower to Core source    name resolution, desugaring,
                             shared pattern compilation, recursive grouping
  → infer                   direct source typing, type and editor artifacts
  → check exhaustiveness
  → erase annotations
  → evaluate                small-step semantics
```

The surface language has names, nested patterns, and syntactic sugar. Core is
a smaller language with de Bruijn indices and only flat, one-constructor-deep
matches. `Expr T` is the single Core syntax family. `InferInput := Expr TyTemplate`
is its canonical source instance, including partial annotations; bindings use
`Option (Scheme T)`. `InputTyping` judges it directly. The CLI executes an
erasure of that original source; editor types and schemes come from metadata.
Neither results nor the worker/certificate retain a completed expression.
Recursive state stores schemes, metadata and checked flags.
The structural lowering proof covers the term produced by production provenance
lowering. It does not verify the parser, source-span metadata, editor joins, or
the unbounded CLI evaluator.

`SurfaceBridge` contains the shared structural traversal and its production
specialization, which preserves partial annotations in `InferInput`.
`FHM.SurfaceBridge.CompleteCore` is an explicit opt-in compatibility module for
the older complete-Core specialization and its source-typing and safety theory.

The design choices that matter most:

- **Evaluation is type-free.** Annotations are used only for type checking and
  are erased before the program runs. No type information exists at runtime.
- **Declarative and algorithmic typing are kept separate.** `InputTyping`
  specifies canonical partial source using pure annotation matching. Named-hole
  assignments are existential and local to each annotation. Only inference
  allocates metavariables. `TypeOfHM` and `Expr.ofCore` support historical
  complete-Core clients; they use the same inference worker.
- **Type variables use a locally nameless representation** with cofinite
  quantification, following
  [Charguéraud's formalisation of mini-ML](https://github.com/charguer/formalmetacoq).
- **Pattern compilation** uses a [Maranget](https://dl.acm.org/doi/10.1145/1411204.1411211)-style
  pattern matrix. Recursive groups are found with a verified Kosaraju SCC
  algorithm.

### Repository map

| Module                                           | Contents                                                                         |
| ------------------------------------------------ | -------------------------------------------------------------------------------- |
| [`Core.lean`](./FHM/Core.lean)                   | Types, Scheme T, Expr T, partial annotations and runtime semantics |
| [`InferenceSupport.lean`](./FHM/InferenceSupport.lean) | Shared unification, generalization, scheduling, and Core typing lemmas       |
| [`AnnotationMatching.lean`](./FHM/AnnotationMatching.lean) | Pure local hole assignments, matching, closed completions, substitution and opening |
| [`AnnotationAllocation.lean`](./FHM/AnnotationAllocation.lean) | Shared certified hole allocation/checking, independent of generalization policy |
| [`SourceAnnotations.lean`](./FHM/SourceAnnotations.lean) | Written schemes, derived checking views, substitution and opening |
| [`InferInput.lean`](./FHM/InferInput.lean)       | Source operations, scoped inference proof refinement, optional complete projection |
| [`SourceTyping.lean`](./FHM/SourceTyping.lean)   | Main source judgment `InputTyping`, direct erasure and scope refinement equivalence |
| [`SourceCompatibility.lean`](./FHM/SourceCompatibility.lean) | Derived complete-Core conversion, outside the source soundness path |
| [`InferW.lean`](./FHM/InferW.lean)               | The sole inference judgment and worker, bounds, soundness, and fidelity         |
| [`Completeness.lean`](./FHM/Completeness.lean)   | Principality and executable completeness for that same worker                   |
| [`RuntimeTyping.lean`](./FHM/RuntimeTyping.lean) | Typing for erased runtime terms, used to prove progress and preservation         |
| [`SurfaceLang.lean`](./FHM/SurfaceLang.lean)     | Surface syntax tree                                                              |
| [`SurfaceBridge.lean`](./FHM/SurfaceBridge.lean) | Head normalization, annotation-preserving `InferInput` lowering, SCCs, and coverage |
| [`SurfaceBridge/CompleteCore.lean`](./FHM/SurfaceBridge/CompleteCore.lean) | Opt-in complete-Core lowering, structural surface typing, and safety theory |
| [`PatComp.lean`](./FHM/PatComp.lean)             | Pattern-match compiler and its correctness proofs                                |
| [`Scc/Kosaraju.lean`](./FHM/Scc/Kosaraju.lean)   | Verified strongly connected components                                           |
| [`Decls.lean`](./FHM/Decls.lean)                 | Data declaration checking                                                        |
| [`Headlines.lean`](./FHM/Headlines.lean)         | Canonical production theorems and the proof-carrying erased-term runner |
| [`Headlines/CompleteCore.lean`](./FHM/Headlines/CompleteCore.lean) | Opt-in structural witnesses and complete-Core `elaborateSafe` demo |
| [`Examples.lean`](./FHM/Examples.lean)           | Worked examples of programs that typecheck and programs that are rejected        |
| [`Unverified/`](./FHM/Unverified/README.md)      | Lexer, parser, CLI, editor support, unbounded evaluator                          |

## Roadmap

Known bugs and smaller tasks are tracked in [`TODO.md`](./TODO.md).

Near term:

- **Better error messages.** Application errors explain mismatches at the
  offending expression; extend these diagnostics to recursive groups, matches
  and the rest of the pipeline.
- **Signatures on function heads** (`let f (x : Int) (y : a) : a = …`).
- **String literals**.

Further out:

- **Row types** and records.
- **Type system experiments** of my own, built on this foundation.

## My motivation

I've been interested in type systems for a long time, and I really enjoy working in ML-style pure languages like e.g. Elm. At the same time I've been frustrated by Elm's limitations and wanted to create my own implementation of an Elm-like language that I could steer according to my own instincts and desired features.

I've also had some ideas for novel type system features, some of which I haven't seen mentioned in the literature. I'd like to explore what is involved in implementing those and to see if I could make them work. So this project really serves two purposes: both a pedagogical project for my own learning about well-trodden PLT grounds, and also to serve as a testbed for exploring my own type system ideas, once the stable HM (and perhaps row types) foundations are in place.

For this I've leaned quite a bit on LLMs. Mainly in two ways:

- As tutor: to bounce ideas off of, to get feedback on my designs, but also to help me explore – and understand – relevant papers when I can't figure out how to solve a problem. I've spent quite a bit of time talking to claude (mostly opus 4.8) getting it to explain certain concepts to me, in different ways, using different examples. I would propose my own simpler solutions and it would give me a counterexample to illustrate why that idea won't work. This has proven massively useful to me and I certainly would not have the understanding I have now had I not done this work.
- Proof workhorse: I've used LLMs to do most of the proving grunt-work. Although there have been quite a few moments when in the midst of trying to amend a broken theorem after adding a new feature, it realised that the original theorem was now false as stated. At that point it would surface the issue to me, I'd interrogate it, making sure I had a clear grasp of the issue. It would propose some solutions, I'd usually need to push it to make sure we were actually coming up with the most principled solution, rather than an ad hoc one. Once I decided on a solution, I'd prompt it to execute the amended brief.

This workflow has been very fruitful, both in getting this formalisation to the mature point it is now, and also in advancing my own learning. I learn best by building, and this has been an incredibly successful way for me to learn and absorb the relevant material.

## References

- J. Roger Hindley. _The principal type-scheme of an object in combinatory logic._ Transactions of the American Mathematical Society 146:29–60, 1969. <https://doi.org/10.1090/S0002-9947-1969-0253905-6>
- Robin Milner. _A theory of type polymorphism in programming._ Journal of Computer and System Sciences 17(3):348–375, 1978. <https://doi.org/10.1016/0022-0000(78)90014-4>
- Luis Damas and Robin Milner. _Principal type-schemes for functional programs._ POPL 1982, 207–212. <https://doi.org/10.1145/582153.582176>
- Alan Mycroft. _Polymorphic type schemes and recursive definitions._ International Symposium on Programming, LNCS 167, 217–228, 1984. <https://doi.org/10.1007/3-540-12925-1_41>
- Fritz Henglein. _Type inference with polymorphic recursion._ ACM TOPLAS 15(2):253–289, 1993. <https://doi.org/10.1145/169701.169692>
- A. J. Kfoury, J. Tiuryn, and P. Urzyczyn. _Type reconstruction in the presence of polymorphic recursion._ ACM TOPLAS 15(2):290–311, 1993. <https://doi.org/10.1145/169701.169687>
- Simon Peyton Jones and Mark Shields. _Lexically scoped type variables._ Microsoft Research, 2002. <https://www.microsoft.com/en-us/research/publication/lexically-scoped-type-variables/>
- Luc Maranget. _Compiling pattern matching to good decision trees._ ML Workshop 2008. <https://dl.acm.org/doi/10.1145/1411204.1411211>
- François Pottier and Didier Rémy. _The essence of ML type inference._ In B. C. Pierce (ed.), Advanced Topics in Types and Programming Languages, ch. 10, 389–489. MIT Press, 2005. <https://pauillac.inria.fr/~fpottier/publis/emlti-final.pdf>
- Brian Aydemir, Arthur Charguéraud, Benjamin C. Pierce, Randy Pollack, and Stephanie Weirich. _Engineering formal metatheory._ POPL 2008, 3–15. <https://doi.org/10.1145/1328438.1328443>
- Arthur Charguéraud. _The locally nameless representation._ Journal of Automated Reasoning 49(3):363–408, 2012. <https://doi.org/10.1007/s10817-011-9225-2>. Coq sources: <https://github.com/charguer/formalmetacoq> (the `ln/ML_*` files).
