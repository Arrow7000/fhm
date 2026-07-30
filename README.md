# FHM: Formalised Hindley-Milner

A formalisation of a language with a Hindley-Milner type system, plus a concrete frontend that can actually run programs. Includes some additional features, like:

- type annotations on let bindings and lambda variables (not part of core HM)
- annotations can reference [type variables quantified in outer scopes](https://www.microsoft.com/en-us/research/publication/lexically-scoped-type-variables/)
- nested pattern matching (with wildcards)
- mutually recursive let bindings with optional type annotations on each (unannotated bindings are assumed to be monomorphic and generalised after typechecking the recursive block); dependency grouping uses a verified Kosaraju SCC pass plus Kahn ordering on the condensation
- when recursive bindings have annotations they may be polymorphic – which enables fully polymorphic recursion, including _mixed_ groups where some members are annotated and others aren't
- algebraic data declarations (`type Maybe a = Just a | Nothing`, …)
- primitive arithmetic and comparison ops (`+`, `-`, `<`), as ordinary curried functions – a partial application is a value; a saturated one δ-reduces on literals

There's a full lexer and parser for an Elm-flavoured concrete syntax, and a live watch driver that re-runs the whole pipeline whenever you save a `.fhm` file.

## Architecture

A high-level overview of the pipeline:

```text
.fhm text
→ lex
→ parse
→ Surface AST
→ lower
    · desugar / name-resolve
    · compile nested matches → flat Core matches
    · group recursive bindings (Kosaraju SCCs + condensation topo)
→ Infer / elaborate → fully-annotated Core
  + check exhaustiveness   (separate check; both needed)
→ evaluate
```

In a bit more detail:

- A surface language (`Surface.Expr` / `Surface.Program`) – named AST, data decls, sugar for pairs/lists/`if`; what the parser builds
- A core language (`Core.lean`'s `Expr`) that surface is lowered into – de Bruijn indices for terms and types, flat matches, explicit constructors
- The Hindley-Milner typing relation (`TypeOfHM`), defined on the pre-elaboration core language
- An elaboration (`Infer`) from desugared core to a core language suitable for execution – adds type annotations on all let bindings and applied type parameters on vars (for System F style type-passing semantics)
  - This doubles as the algorithm-oriented spec for typechecking (as opposed to the `TypeOf*` relations which are non-algorithmic, _declarative_ typing relations)
- The HM typing relation defined on the _post_-elaboration core language (`TypeOfElabHM`)
- A small-step, type-passing, operational semantics (`SmallStep.Step`) defined on an elaborated core-language program

Elaboration actually does two things at once: it infers a type for every term, and it writes those types into the program as it goes. The two are inseparable – you can't annotate the bindings and variables without inferring their types first, and there's no point inferring types unless you're also getting the program closer to something runnable. The reason this is needed is that our operational semantics only accepts fully-annotated programs; but because the type system stays within HM (rank-1 prenex polymorphism), inference is still 100% decidable without any annotations. So the source stays annotation-optional, and elaboration is the phase that turns it into the fully-annotated form the evaluator needs.

Representation choices:

- terms use de Bruijn indices for their bound variables
- type variables use a locally-nameless representation with cofinite quantification, following [Charguéraud's formalisation of mini-ML](https://github.com/charguer/formalmetacoq/blob/master/ln/ML_Definitions.v)
- types split into monotypes and `∀`-quantified schemes
- typing contexts are indexed by de Bruijn position

### [`Core.lean`](./FHM/Core.lean)

This is where the language lives and where we say, abstractly, what it means for a program to be well-typed. It doesn't compute anything; it just lays down the rules.

- `Expr`: the term language – applications, lambdas, lets (including mutually recursive ones, optionally annotated), constructors, matches, primitives.
- `TypeOfHM`: the declarative typing relation for the pre-elaboration reading. This is textbook HM, where a polymorphic variable may be used at any instance of its scheme.
- `TypeOfElabHM`: the same relation for the post-elaboration reading, where every polymorphic use carries the exact type arguments it was instantiated at. The two relations are identical apart from that one rule.
- `SmallStep.Step`: a small-step semantics that runs the elaborated program directly, carrying types at runtime rather than erasing them.

### [`InferW.lean`](./FHM/InferW.lean)

This is where we actually work out a program's type, instead of just declaring which types are valid. It's the algorithmic side, and it's where elaboration happens.

- `Infer`: a relation specifying inference and elaboration together. From a source program it produces a substitution, an inferred type, and the elaborated program.
- `infer` and `inferCore`: the executable versions of that relation.
- `typecheck`: the whole-program entry point. It runs from the empty context and generalises the result into a closed scheme.

### [`SurfaceLang.lean`](./FHM/SurfaceLang.lean), [`Surface/Lex.lean`](./FHM/Surface/Lex.lean), [`Surface/Parse.lean`](./FHM/Surface/Parse.lean)

This is what the language looks like to a user: real string names, data declarations, and syntactic sugar for pairs, lists, `if`, and so on. Lex and Parse turn source text into that AST – Elm-flavoured concrete syntax, with F#-style `match` and `{a b} τ` schemes for polymorphism. Infix like `+`/`-`/`<`/`::` and multi-arg lambdas are desugared during parsing. Lexer/parser _correctness_ is deliberately not proven; the verified story starts at the Surface AST.

### [`SurfaceBridge.lean`](./FHM/SurfaceBridge.lean)

The front end proper: lowers Surface into Core, groups flat bindings into SCCs, checks exhaustiveness, and proves the end-to-end claim – a well-typed, exhaustive surface program elaborates to Core that is type-safe and never gets stuck.

- `Lowers` / `lower`: declarative vs executable lowering. At match there isn't a unique correct Core term – different decision trees can implement the same surface match equivalently – so the relation allows any of them, and the function picks one.
- `SurfaceWT` / `SurfaceWTExpr`: a declarative surface typing relation – at match it requires the branches themselves to be well-typed under the binders the patterns introduce, rather than just “whatever Core the lowerer emitted typechecks.”
- `checkExhaustive`: executable coverage checker, proved sound against the declarative coverage predicate that type safety needs.
- `program_type_safe` / `surface_type_safe`: the “doesn't go wrong” theorems at program and expression level.

### [`Scc/Kosaraju.lean`](./FHM/Scc/Kosaraju.lean)

Verified Kosaraju strongly-connected-components on abstract finite digraphs (`Digraph α` with `succ : α → Finset α`).

- Declarative spec: `Reach`, `Mutual`, `ValidSccPartition` (partition + same-SCC + maximal-SCC properties).
- Executable `kosaraju` (fuelled DFS on the graph and its transpose).
- Main adequacy theorems: `kosaraju_sound` and `ValidSccPartition.eqv_mutual` (any two valid partitions agree up to reordering).
- Wired into `SurfaceBridge.sccGroups` for letrec dependency grouping (`bindDigraph` on binding indices, then Kahn topo on the condensation). `sccGroups_sound` / `_complete` prove the pipeline matches the declarative `ValidBindingGroups` spec.

### [`PatComp.lean`](./FHM/PatComp.lean)

Verified pattern-match compilation. Surface has nested patterns; Core only has flat single-constructor switches.

- Compiles via a [Maranget](https://dl.acm.org/doi/10.1145/1411204.1411211)-style pattern matrix (specialisation / default), leftmost column, no heuristics.
- Builds a decision tree, then emits nested Core matches.
- Proved against a trusted first-match surface semantics: same branch, same captures.
- Adequacy: the emitted Core actually reduces to that branch with the right bindings.
- Exhaustiveness is checked separately – typechecking alone never gives you coverage.

### [`Decls.lean`](./FHM/Decls.lean)

Data-declaration elaboration: surface `type` decls become the Core constructor environment, with soundness and completeness against the declarative specs.

### [`Headlines.lean`](./FHM/Headlines.lean)

A single entry point that re-exports the main theorems with plain-English glosses, plus the safe pipeline helpers `elaborateSafe` / `runSafe`. Also keeps a living `#print axioms` guard. Worth reading first if you're new to the project.

### [`EvaluateUnsafe.lean`](./FHM/EvaluateUnsafe.lean), [`Live.lean`](./FHM/Live.lean), [`Diagnose.lean`](./FHM/Diagnose.lean)

The formal evaluator is fuelled. For actually running programs – including naive recursion that blows past any fixed fuel – there's an unbounded evaluator. The unified `fhm` CLI (see `FHM/Cli.lean`) exposes:

- `fhm` / `fhm run` — parse, lower, infer (print binding and body types), exhaustiveness, elaborate, evaluate (`Live.lean`; `--json` for machine output)
- `fhm diagnose` — parse + hover symbols as JSON for editors (`Diagnose.lean` / `EditorSupport.lean`)

Pair `fhm run` with `scripts/watch-live.sh` and a `.fhm` file (see `scratch/live.fhm`) for a save-triggered, REPL-like loop. The Monaco playground under `editors/web/` talks to the same binary over HTTP.

### [`Pretty.lean`](./FHM/Pretty.lean), [`Examples.lean`](./FHM/Examples.lean)

`Pretty.lean` prints Core and Surface terms readably, and `Examples.lean` collects runnable `#eval` demos – let-polymorphism, mixed polymorphic recursion, surface→eval walks, and various ill-typed programs that should be rejected.

### [`ConstraintTypeSystem.lean`](./FHM/ConstraintTypeSystem.lean) 🚧

A work-in-progress experiment in a different approach. Instead of Algorithm W, it tries the constraint-based style (Wand; Pottier and Rémy), where inference generates a constraint and then solves it, using guarded constraint schemes `∀ᾱ[C].τ`. It's currently out of date against `Core`, excluded from the default build, and may be getting discarded.

### [`Bounds/`](./FHM/Bounds/) + [`BLSketch.lean`](./FHM/BLSketch.lean) + [`Z3/`](./FHM/Z3/) (optional)

Separate lake targets (`FHMBounds`, `FHMZ3`; not in the default build): bounded-list types with count/index schemes, Z3-backed bound oracles, and a Core-attached typing layer (`BoundInfo`, `BoundCovers`, erase/synth/check). `fhm run --bl` enables BL surface syntax and runs the bounds pipeline alongside HM inference. `BLSketch.lean` retains the original standalone sketch and soundness proofs.

### Proven theorems

All of these are fully proved. The theorems only use the standard axioms and are completely free of `sorry`s. `Headlines.lean` gathers them in one place if you want a single entry point.

**Inference and principality** (`InferW.lean`):

- `Infer.sound`: if inference succeeds, the elaborated program it returns really is well-typed under the post-elaboration relation.
- `Infer.sourceSound`: and the original source program is well-typed under plain HM.
- `Infer.iff_typeable`: inference succeeds exactly when the program is typeable at all.
- `Infer.principal`: the type it finds is the [most general](https://doi.org/10.1145/582153.582176) one, and every other valid type is an instance of it.
- `typecheck_sound`, `typecheck_iff`, `typecheck_principal`: the same three guarantees, packaged up for a whole program.

**Unification** (`InferW.lean`):

- `unify_sound`, `unify_complete`: the unifier returns a most general unifier when one exists, and only when one exists.

**Recursive bindings** (`InferW.lean`):

- `InferRecGroup.sound`, `InferRecGroup.complete`: inference is sound and complete for mutually recursive groups – unannotated members are checked monomorphically and then generalised, annotated members are checked at their declared schemes (polymorphic recursion), and one group may mix both kinds.

**Pattern compilation** (`PatComp.lean`):

- `PatComp.compile_correct_surface`: on any scrutinee value, the compiled decision tree selects exactly the branch (and captures) that first-match surface semantics would.
- `PatComp.lowerMatch_adequate_of_typed`: under typing hypotheses, the emitted Core reduces to that branch body with the right substitution.

**Exhaustiveness** (`SurfaceBridge.lean`):

- `checkExhaustive_sound`: if the executable coverage checker says yes, the declarative coverage predicate that type safety needs holds.
- Exhaustiveness is preserved through lowering and elaboration.

**Surface / program safety** (`SurfaceBridge.lean`):

- `surface_type_safe` / `program_type_safe`: a well-typed, exhaustive surface expression / program elaborates to Core that never gets stuck.
- `surface_type_safe_of_SurfaceWT`: the same claim, starting from the declarative surface typing relation rather than the executable lower/typecheck pipeline. (The converse – that executable acceptance implies a declarative surface typing – is still open.)

**Data declarations & binding groups**:

- `lowerDataDecls_sound` / `_complete`, `elabDecls_sound` / `_complete`: surface data decls elaborate exactly as the declarative specs allow.
- `sccGroups_sound` / `_complete`: the SCC grouping of a flat binding list matches the declarative validity predicate for binding groups.

**Kosaraju SCC** (`Scc/Kosaraju.lean`):

- `kosaraju_sound`: the executable Kosaraju partition satisfies `ValidSccPartition`.
- `ValidSccPartition.eqv_mutual`: any two valid SCC partitions of the same graph agree (components are mutual-reachability classes, up to reordering).

**Runtime safety** (`Core.lean`):

- `TypeOfElabHM.progress`: a well-typed elaborated program is either a finished value or it can take another step.
- `TypeOfElabHM.preservation`: taking a step never changes a program's type.
- `TypeOfElabHM.type_safety` / `type_safety_star`: putting those together, a well-typed program never gets stuck – including under iterated stepping.

**The elaboration bridge** (`Core.lean`):

- `TypeOfElabHM.faithful`: anything well-typed after elaboration was already well-typed in plain HM, so elaboration never invents new typings.

**Safe pipeline** (`Headlines.lean`):

- `elaborateSafe`: if a surface program typechecks and is exhaustive, returns the elaborated Core term together with proofs of both.
- `runSafe`: given those proofs, evaluates under fuel. The only thing that can go "wrong" is nontermination – unavoidable in a Turing-complete language.

## Why type-passing semantics for a Hindley-Milner language

I first implemented a simple language without type annotations at all. Then I wanted to support type annotations that could mention type variables (skolems) from a higher enclosing scope. That caused a problem because when a let binding reduces, those skolems can end up orphaned, pointing at a scope that no longer exists. This would break type preservation, as stepping would result in an invalid, ill-scoped type variable reference. I decided to tackle this by erasing all type annotations before running a program, and defining all theorems related to evaluation against type-erased programs. That makes sure there are no skolems left to dangle during evaluation.

Then I wanted to support mutually recursive let bindings. This is manageable as long as you stick to unannotated bindings or keep them all monomorphic.

But then I also wanted _polymorphic_ mutual recursion. This was hard, because inferring it in general is [undecidable](https://doi.org/10.1145/169701.169692), but it becomes decidable once each binding carries a type annotation. The catch is that those annotations can no longer be erased: erase them and inference has to fall back to the monomorphic case, which would leave the typed language strictly weaker than the annotated one. What used to be two separate valid instantiations of a single polymorphic binding has now become two incompatible applications of a _monomorphic_ binding. So erasing types is no longer an option.

That's what forced the current evaluation model. Instead of erasing types, the program keeps them and runs under a [type-passing](https://doi.org/10.1017/S0956796801004282) semantics, and inference elaborates each program into fully-annotated form. To show that this is merely an evaluation semantics and type annotations are not required for inference, we maintain two different declarative typing relations as stated above: one for the program _before_ elaboration and one for after, with `TypeOfElabHM.faithful` tying them together.

## Building

Requires the Lean toolchain pinned in `lean-toolchain` (`leanprover/lean4:v4.26.0`,
managed by `elan`). On a fresh clone:

```bash
lake exe cache get   # download prebuilt Mathlib oleans (don't recompile Mathlib!)
lake build
```

### Live watch (terminal)

Save a `.fhm` file and re-run the full pipeline (types, then eval) on each save:

```bash
lake build fhm                         # builds .lake/build/bin/fhm
scripts/watch-live.sh                  # watches scratch/live.fhm by default
scripts/watch-live.sh path/to/foo.fhm  # or point it at another file
```

Needs `entr` (preferred) or `fswatch`; otherwise it falls back to polling. The script only rebuilds `fhm` when pipeline Lean sources change (not every file under `FHM/`).

Manual one-shots without the watcher:

```bash
.lake/build/bin/fhm scratch/live.fhm           # human Ansi output
.lake/build/bin/fhm --json scratch/live.fhm    # JSON (same as the web /api/run)
.lake/build/bin/fhm diagnose scratch/live.fhm  # editor diagnostics / hover JSON
```

### Web playground

Local Monaco editor + output pane; debounced `fhm diagnose` on edit, Run for `fhm --json`.

```bash
lake build fhm
cd editors/web
npm install
npm run dev          # http://localhost:5173
```

If the editor pane stays blank or imports look stale after changing `editors/shared/`, use `npm run dev:clean` (clears Vite’s optimize-deps cache) and hard-refresh the browser.

Optional checks: `npm run hover-sweep`, `npm run verify-playground` (Playwright).

The Cursor/VS Code extension under `editors/vscode/` also talks to `fhm diagnose` (see `scripts/install-fhm-extension.sh`). Syntax highlighting is generated from the live lexer tables via `fhm_grammar` (`scripts/gen-fhm-tmgrammar.sh`).

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
- Karl Crary, Stephanie Weirich, and Greg Morrisett. _Intensional polymorphism in type-erasure semantics._ Journal of Functional Programming 12(6):567–600, 2002 (ICFP 1998). <https://doi.org/10.1017/S0956796801004282>
- Luc Maranget. _Compiling pattern matching to good decision trees._ ML Workshop 2008. <https://dl.acm.org/doi/10.1145/1411204.1411211>
- François Pottier and Didier Rémy. _The essence of ML type inference._ In B. C. Pierce (ed.), Advanced Topics in Types and Programming Languages, ch. 10, 389–489. MIT Press, 2005. <https://pauillac.inria.fr/~fpottier/publis/emlti-final.pdf>
- Brian Aydemir, Arthur Charguéraud, Benjamin C. Pierce, Randy Pollack, and Stephanie Weirich. _Engineering formal metatheory._ POPL 2008, 3–15. <https://doi.org/10.1145/1328438.1328443>
- Arthur Charguéraud. _The locally nameless representation._ Journal of Automated Reasoning 49(3):363–408, 2012. <https://doi.org/10.1007/s10817-011-9225-2>. Coq sources: <https://github.com/charguer/formalmetacoq> (the `ln/ML_*` files).
