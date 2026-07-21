# FHM: Formalised Hindley-Milner

A formalisation of a language with a Hindley-Milner type system — plus a concrete frontend that can actually run programs. Includes some additional features, like:

- type annotations on let bindings and lambda variables (not part of core HM)
- annotations can reference [type variables quantified in outer scopes](https://www.microsoft.com/en-us/research/publication/lexically-scoped-type-variables/)
- pattern matching (with nested patterns and wildcards), compiled down to Core's flat single-level matches
- mutually recursive let bindings with optional type annotations on each (unannotated bindings are assumed to be monomorphic and generalised after typechecking the recursive block)
- when recursive bindings have annotations they may be polymorphic – which enables fully polymorphic recursion, including _mixed_ groups where some members are annotated and others aren't
- algebraic data declarations (`type Maybe a = Just a | Nothing`, …)
- primitive arithmetic and comparison ops (`+`, `-`, `<` on the surface; `intAdd` / `intSub` / `intLt` in Core), as ordinary curried functions — a partial application is a value; a saturated one δ-reduces on literals

There's a full lexer and parser for an Elm-flavoured concrete syntax, and a live watch driver that re-runs the whole pipeline on save. So this isn't just a Lean formalisation sitting in a vacuum — you can write `.fhm` files and watch them typecheck and evaluate.

## Architecture

A high-level overview of the pipeline:

```text
.fhm text → lex → parse → Surface AST
  → lower (desugar, name-resolve, compile matches, SCC binding groups)
  → Infer / elaborate → fully-annotated Core
  → small-step / evaluate
```

In a bit more detail:

- A surface language (`Surface.Expr` / `Surface.Program`) – named AST, data decls, sugar for pairs/lists/`if`, the thing the parser builds
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

- `Expr`: the term language (including `primBinOp` for the built-in arithmetic/comparison ops, and a single fused `letRec` that carries per-binding optional scheme annotations — so mono and poly recursion live in one node).
- `TypeOfHM`: the declarative typing relation for the pre-elaboration reading. This is textbook HM, where a polymorphic variable may be used at any instance of its scheme.
- `TypeOfElabHM`: the same relation for the post-elaboration reading, where every polymorphic use carries the exact type arguments it was instantiated at. The two relations are identical apart from that one rule.
- `SmallStep.Step`: a small-step semantics that runs the elaborated program directly, carrying types at runtime rather than erasing them. Saturated primops δ-reduce à la Plotkin.

### [`InferW.lean`](./FHM/InferW.lean)

This is where we actually work out a program's type, instead of just declaring which types are valid. It's the algorithmic side, and it's where elaboration happens.

- `Infer`: a relation specifying inference and elaboration together. From a source program it produces a substitution, an inferred type, and the elaborated program.
- `infer` and `inferCore`: the executable versions of that relation.
- `typecheck`: the whole-program entry point. It runs from the empty context and generalises the result into a closed scheme.

### [`SurfaceLang.lean`](./FHM/SurfaceLang.lean), [`Surface/Lex.lean`](./FHM/Surface/Lex.lean), [`Surface/Parse.lean`](./FHM/Surface/Parse.lean)

`SurfaceLang` is the named AST: real string names, data declarations, sugar for pairs and lists, layout-shaped `let`/`if`/`match`. `Lex` and `Parse` turn source text into that AST — Elm-flavoured concrete syntax, with F#-style `match` and Lean-ish `{a b} τ` schemes for polymorphism. Infix desugars during parse (`+`/`-`/`<`/`::`, multi-arg lambdas). Lexer/parser _correctness_ is deliberately not proved; the verified story starts at the Surface AST.

### [`SurfaceBridge.lean`](./FHM/SurfaceBridge.lean)

The front end proper: lowers Surface into Core, groups flat bindings into SCCs, checks exhaustiveness, and states the campaign's headline payoff — a well-typed, exhaustive surface program elaborates to a Core program that is type-safe and never gets stuck.

- `Lowers` / `lower`: declarative vs executable lowering (one-to-many at `match`, because many behaviourally-equivalent Core renderings of one surface match are fine).
- `SurfaceWTExpr` / `SurfaceWT`: a strong declarative surface typing relation (open branch typings at match, not "whatever `lower` happened to emit typechecks").
- `checkExhaustive`: executable coverage checker, with a Bool→Prop soundness theorem against the declarative `SurfaceCovers` predicate that type safety actually needs.
- `program_type_safe` / `surface_type_safe`: the end-to-end "doesn't go wrong" theorems at program and expression level.

### [`PatComp.lean`](./FHM/PatComp.lean)

Verified pattern-match compilation. Surface has nested patterns; Core only has flat single-constructor switches. The compiler turns a surface `match` into a [Maranget](https://dl.acm.org/doi/10.1145/1411204.1411211)-style pattern matrix (`S(c,M)` / `D(M)`), using a naive leftmost-column strategy (no heuristics), builds a decision-tree IR (`DTree`), and emits nested Core `match_`es.

The hard part — and the part we actually proved — is that this isn't just a compiler that "looks right." There's a trusted surface-side spec (`firstMatch` / `matchPat`: first-matching branch + captures), a denotational interpreter for the decision tree, and theorems that `compile` preserves that semantics and that the emitted Core actually reduces to the selected branch with the right bindings. Exhaustiveness is a separate, load-bearing conjunct: typechecking alone never gives you coverage, so the pipeline insists on it independently.

### [`Decls.lean`](./FHM/Decls.lean)

Data-declaration elaboration: surface `type` decls → Core constructor environment, with soundness and completeness against the declarative specs.

### [`Headlines.lean`](./FHM/Headlines.lean)

A façade for newcomers (and for me, six months from now). Re-exports the campaign's headline theorems with plain-English glosses, witnesses that the relations are genuinely inhabited, and a proof-carrying safe pipeline (`elaborateSafe` / `runSafe`) that only accepts programs that typecheck _and_ are exhaustive — and then can't get stuck. Also keeps a living `#print axioms` budget guard. If you want one Lean file to read first, start here.

### [`EvaluateUnsafe.lean`](./FHM/EvaluateUnsafe.lean), [`Live.lean`](./FHM/Live.lean)

The formal evaluator is fuelled (`evaluate`). For actually running programs — including naive `fib` that blows past any fixed fuel — there's an unbounded `evaluateUnsafe`. `Live.lean` wires the whole stack into an executable (`fhm_live`):

`parse → lower → infer (print binding + body types) → exhaustiveness → elaborate → evaluateUnsafe`

Pair that with `scripts/watch-live.sh` and a `.fhm` file (see `scratch/live.fhm`) and you get a save-triggered, REPL-like loop.

### [`Pretty.lean`](./FHM/Pretty.lean), [`Examples.lean`](./FHM/Examples.lean)

`Pretty.lean` prints Core and Surface terms readably (including list/pair sugar for live output). `Examples.lean` collects runnable `#eval` demos: let-polymorphism, mixed polymorphic recursion, surface→eval walks, and various ill-typed programs that should be rejected.

### [`ConstraintTypeSystem.lean`](./FHM/ConstraintTypeSystem.lean) 🚧

A work-in-progress experiment in a different approach. Instead of Algorithm W, it tries the constraint-based style (Wand; Pottier and Rémy), where inference generates a constraint and then solves it, using guarded constraint schemes `∀ᾱ[C].τ`. It's currently out of date against `Core`, excluded from the default build, and may be getting discarded.

### Proven theorems

All of these are fully proved. The theorems only use the standard axioms and are completely free of `sorry`s. `Headlines.lean` is the living inventory; the list below is the tour.

**Inference and principality** (`InferW.lean`):

- `Infer.sound`: if inference succeeds, the elaborated program it returns really is well-typed under the post-elaboration relation.
- `Infer.sourceSound`: and the original source program is well-typed under plain HM.
- `Infer.iff_typeable`: inference succeeds exactly when the program is typeable at all.
- `Infer.principal`: the type it finds is the [most general](https://doi.org/10.1145/582153.582176) one, and every other valid type is an instance of it.
- `typecheck_sound`, `typecheck_iff`, `typecheck_principal`: the same three guarantees, packaged up for a whole program.

**Unification** (`InferW.lean`):

- `unify_sound`, `unify_complete`: the unifier returns a most general unifier when one exists, and only when one exists.

**Recursive bindings** (`InferW.lean`):

- `InferRecGroup.sound`, `InferRecGroup.complete`: inference is sound and complete for mutually recursive groups — unannotated members are checked monomorphically and then generalised, annotated members are checked at their declared schemes (polymorphic recursion), and one group may mix both kinds.

**Pattern compilation** (`PatComp.lean`):

- `PatComp.compile_correct_surface`: on any scrutinee value, the compiled decision tree selects exactly the branch (and captures) that the trusted `firstMatch` reference semantics would select.
- `PatComp.lowerMatch_adequate_of_typed`: the operational form the bridge consumes — under typing + value hypotheses, the emitted Core reduces to the selected branch body with the right substitution.

**Exhaustiveness** (`SurfaceBridge.lean`):

- `checkExhaustive_sound`: the executable coverage checker implies the declarative `SurfaceCovers` predicate that type safety needs.
- Exhaustiveness is preserved through lowering and elaboration (so a surface-exhaustive program stays Core-exhaustive after compile + infer).

**Surface / program safety** (`SurfaceBridge.lean`):

- `surface_type_safe` / `program_type_safe`: a well-typed, exhaustive surface expression / program elaborates to Core that never gets stuck.
- `surface_type_safe_of_SurfaceWT`: the declarative mirror — start from `SurfaceWT` rather than the executable `lower`/`typecheck` pipeline, and you get the same payoff. (The converse — "`typecheck (lower s)` implies `SurfaceWT`" — is still open; see below.)

**Data declarations & binding groups**:

- `lowerDataDecls_sound` / `_complete`, `elabDecls_sound` / `_complete`: surface data decls elaborate to exactly the `CtorEnv` the declarative specs allow.
- `sccGroups_sound` / `_complete`: the SCC grouping of a flat binding list is sound and complete against `ValidBindingGroups`.

**Runtime safety** (`Core.lean`):

- `TypeOfElabHM.progress`: a well-typed elaborated program is either a finished value or it can take another step.
- `TypeOfElabHM.preservation`: taking a step never changes a program's type.
- `TypeOfElabHM.type_safety` / `type_safety_star`: putting those together, a well-typed program never gets stuck — including under iterated stepping.

**The elaboration bridge** (`Core.lean`):

- `TypeOfElabHM.faithful`: anything well-typed after elaboration was already well-typed in plain HM, so elaboration never invents new typings.

**Proof-carrying pipeline** (`Headlines.lean`):

- `elaborateSafe` / `runSafe`: compose typechecking + exhaustiveness into a value that can only be obtained for safe programs, then run it under fuel without ever getting stuck.

## Why type-passing semantics for a Hindley-Milner language

I first implemented a simple language without type annotations at all. Then I wanted to support type annotations that could mention type variables (skolems) from a higher enclosing scope. That caused a problem because when a let binding reduces, those skolems can end up orphaned, pointing at a scope that no longer exists. This would break type preservation, as stepping would result in an invalid, ill-scoped type variable reference. I decided to tackle this by erasing all type annotations before running a program, and defining all theorems related to evaluation against type-erased programs. That makes sure there are no skolems left to dangle during evaluation.

Then I wanted to support mutually recursive let bindings. This is manageable as long as you stick to unannotated bindings or keep them all monomorphic.

But then I also wanted _polymorphic_ mutual recursion, and that's where it got difficult. Inferring it in general is [undecidable](https://doi.org/10.1145/169701.169692), but it becomes decidable once each binding carries a type annotation. The catch is that those annotations can no longer be erased: erase them and inference has to fall back to the monomorphic case, which would leave the typed language strictly weaker than the annotated one. What used to be two separate valid instantiations of a single polymorphic binding has now become two incompatible applications of a _monomorphic_ binding. So erasing types is no longer an option.

That's what forced the current evaluation model. Instead of erasing types, the program keeps them and runs under a [type-passing](https://doi.org/10.1017/S0956796801004282) semantics, and inference elaborates each program into fully-annotated form. To show that this is merely an evaluation semantics and type annotations are not required for inference, we maintain two different declarative typing relations as stated above: one for the program _before_ elaboration and one for after, with `TypeOfElabHM.faithful` tying them together.

## Building

Requires the Lean toolchain pinned in `lean-toolchain` (`leanprover/lean4:v4.26.0`,
managed by `elan`). On a fresh clone:

```bash
lake exe cache get   # download prebuilt Mathlib oleans (don't recompile Mathlib!)
lake build
```

That builds the verified stack (Core, InferW, Surface, PatComp, SurfaceBridge, Headlines, …). For the live driver:

```bash
lake build fhm_live
scripts/watch-live.sh                  # watches scratch/live.fhm by default
scripts/watch-live.sh path/to/foo.fhm  # or point it at another file
```

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
