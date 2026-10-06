# FHM: Formalised Hindley–Milner

FHM is a small, Elm-flavoured functional language with Hindley–Milner type
inference, formalised in Lean 4. The type system is proved sound, inference is
proved complete and to compute principal types, and the same verified pipeline
runs real programs through a command-line tool, a watch mode, and a browser
playground.

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
- **Algebraic data types**, including parameterised and recursive ones.
- **Nested pattern matching** with wildcards. Matches must be exhaustive.
- **Recursion and mutual recursion** between definitions written in any order.
  Unannotated recursive definitions follow standard HM. A definition with a
  type annotation can be used at different types anywhere in its recursive
  group, including in its own body (polymorphic recursion), following the
  same rules as Haskell.
- Built-in `Int`, `Bool`, pairs, and lists, with `+`, `-`, `<`, `::`, list
  literals, `if`/`then`/`else`, and `let … in` blocks.

[`scratch/language-guide.fhm`](./scratch/language-guide.fhm) walks through
annotations and recursion with runnable examples, and
[`recursion-language-comparison/`](./recursion-language-comparison/) compares
FHM's recursion rules with GHC, OCaml, F#, Elm and Standard ML.

## What is proved

All of the following are machine-checked, with no `sorry` and only Lean's
standard axioms. [`FHM/Headlines.lean`](./FHM/Headlines.lean) gathers the main
theorems in one place, each with a plain-English explanation, and is the best
starting point for reading the proofs.

| Claim | Main theorems |
|---|---|
| **Type safety:** a well-typed program never gets stuck. It is either a value or can take another step, and its type is preserved. | `TypeOfHM.progress`, `TypeOfHM.preservation`, `TypeOfHM.type_safety_star` |
| **End-to-end safety:** a well-typed, exhaustive *surface* program lowers to Core that never gets stuck. | `program_type_safe`, `surface_type_safe` |
| **Inference is sound:** any type Algorithm W infers is a valid type for the program. | `Infer.sound`, `Infer.sourceSound` |
| **Inference is complete and principal:** if a program has *any* type, inference succeeds, and every valid type is an instance of the inferred one. | `typecheck_accepts_iff`, `typecheck_principal`, `Infer.complete` |
| **Pattern compilation is correct:** nested matches compile to decision trees that select the same branch with the same bindings. | `PatComp.compile_correct_surface`, `PatComp.lowerMatch_adequate_of_typed` |
| **Exhaustiveness checking is sound:** if the checker accepts a match, the match is exhaustive. | `checkExhaustive_sound` |
| **Recursive grouping is correct:** dependency analysis splits definitions into exactly their strongly connected components. | `sccGroups_sound`, `sccGroups_complete`, `kosaraju_sound` |
| **Data declarations elaborate correctly**, matching their declarative spec. | `lowerDataDecls_sound`/`_complete`, `elabDecls_sound`/`_complete` |

**What is not verified:** the lexer, parser, CLI, editor tooling, and the
unbounded evaluator used by `fhm run`. These live under
[`FHM/Unverified/`](./FHM/Unverified/README.md) and are kept out of the
verified build. The verified story starts at the parsed syntax tree. The
verified evaluator (`runSafe` in `Headlines.lean`) is fuel-bounded, because the
language allows non-terminating programs.

## Getting started

You need [`elan`](https://github.com/leanprover/elan); the pinned Lean version
is in [`lean-toolchain`](./lean-toolchain).

```bash
lake exe cache get   # download prebuilt Mathlib (avoids compiling it locally)
lake build           # check all the proofs
lake build fhm       # build the fhm executable
```

### Running programs

```bash
.lake/build/bin/fhm run path/to/program.fhm          # infer types, then evaluate
.lake/build/bin/fhm --json path/to/program.fhm       # the same, as JSON
.lake/build/bin/fhm run --fuel 100000 program.fhm    # stop after 100000 evaluation steps
.lake/build/bin/fhm diagnose path/to/program.fhm     # diagnostics and hover info for editors
```

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
  → lower to Core           name resolution, desugaring,
                             pattern compilation, recursive grouping
  → infer types             Algorithm W
  → check exhaustiveness
  → erase type annotations
  → evaluate                small-step semantics
```

The surface language has names, nested patterns, and syntactic sugar. Core is
a smaller language with de Bruijn indices and only flat, one-constructor-deep
matches. Every step after parsing is covered by the theorems above. The
exception is the unbounded evaluator that `fhm run` uses for convenience.

The design choices that matter most:

- **Evaluation is type-free.** Annotations are used only for type checking and
  are erased before the program runs. No type information exists at runtime.
- **Declarative and algorithmic typing are kept separate.** `TypeOfHM` defines
  which programs are well-typed. Algorithm W (`Infer`, implemented by
  `typecheck`) computes types and is proved sound and complete with respect to
  `TypeOfHM`.
- **Type variables use a locally nameless representation** with cofinite
  quantification, following
  [Charguéraud's formalisation of mini-ML](https://github.com/charguer/formalmetacoq).
- **Pattern compilation** uses a [Maranget](https://dl.acm.org/doi/10.1145/1411204.1411211)-style
  pattern matrix. Recursive groups are found with a verified Kosaraju SCC
  algorithm.

### Repository map

| Module | Contents |
|---|---|
| [`Core.lean`](./FHM/Core.lean) | Types, Core terms, the typing relation `TypeOfHM`, small-step semantics |
| [`InferW.lean`](./FHM/InferW.lean) | Unification, Algorithm W, inference soundness, progress and preservation |
| [`Completeness.lean`](./FHM/Completeness.lean) | Completeness and principality of inference |
| [`RuntimeTyping.lean`](./FHM/RuntimeTyping.lean) | Typing for erased runtime terms, used to prove progress and preservation |
| [`SurfaceLang.lean`](./FHM/SurfaceLang.lean) | Surface syntax tree |
| [`SurfaceBridge.lean`](./FHM/SurfaceBridge.lean) | Lowering surface to Core, exhaustiveness checking, end-to-end safety |
| [`PatComp.lean`](./FHM/PatComp.lean) | Pattern-match compiler and its correctness proofs |
| [`Scc/Kosaraju.lean`](./FHM/Scc/Kosaraju.lean) | Verified strongly connected components |
| [`Decls.lean`](./FHM/Decls.lean) | Data declaration checking |
| [`Headlines.lean`](./FHM/Headlines.lean) | Main theorems in one place, plus the verified `elaborateSafe`/`runSafe` pipeline |
| [`Examples.lean`](./FHM/Examples.lean) | Worked examples of programs that typecheck and programs that are rejected |
| [`Unverified/`](./FHM/Unverified/README.md) | Lexer, parser, CLI, editor support, unbounded evaluator |

## Roadmap

Known bugs and smaller tasks are tracked in [`TODO.md`](./TODO.md).

Near term:

- **Better error messages.** Type errors are currently reported without a
  location or explanation.
- **Signatures on function heads** (`let f (x : Int) (y : a) : a = …`) and
  **partial annotations** with holes (`Int -> _ -> Bool`).
- **Pattern lambdas** (`\(x, y) -> …`) and **string literals**.

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
