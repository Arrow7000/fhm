# FHM: Formalised Hindley-Milner

A formalisation of a language with a Hindley-Milner type system. Includes some additional features, like:

- type annotations on let bindings and lambda variables (not part of core HM)
- annotations can reference [type variables quantified in outer scopes](https://www.microsoft.com/en-us/research/publication/lexically-scoped-type-variables/)
- pattern matching (with wildcard patterns)
- mutually recursive let bindings (unannotated, internally monomorphic)
- in progress: mutually recursive let bindings with _polymorphic_ type annotations

## Architecture

Term bindings use de Bruijn indices. The formalisation splits things into `Core.lean` and `InferW.lean`.

`Core.lean` contains the language itself (`Expr`), the declarative typing relation (`TypeOfHM`), operational semantics in the form of a small step evaluator (`SmallStep.Step`), as well as various lemmas and theorems. E.g. substitution, and progress and preservation lemmas.

`InferW.lean` contains an algorithmically-oriented relation `Infer` as well as its actual implementation `infer` – or `typecheck` for a complete program. It contains soundness and completeness lemmas between the `Infer` relation and the `infer` function, as well as bridging lemmas between `Infer` and `TypeOfHM`. Taken together, we prove that for any HM-typeable expression `infer` finds a type, and that any type found by `infer` is HM-typeable.

We also prove that `infer` finds [principal types](https://doi.org/10.1145/582153.582176) (the most general type allowable by the declarative typing relation).

The declarative typing relation `TypeOfHM` uses cofinite let-generalisation, taken from [Charguéraud's formalisation of mini-ML](https://github.com/charguer/formalmetacoq/blob/master/ln/ML_Definitions.v).

There is also a surface language that contains syntax for constructing booleans, tuples, lists, patterns for destructuring them in let bindings and match expressions. This surface language is not yet wired up to the rest of the project. This will come when the desired core functionality is fully implemented and proven.

Beyond `Core.lean` and `InferW.lean`, the rest of `FHM/` is:

- `SurfaceLang.lean`, `Pretty.lean` — the surface language and pretty-printers for Core and Surface terms.
- `Examples.lean` — `#eval` demos: infer-then-pretty-print, let-polymorphism, polymorphic recursion, and adversarial reject cases.
- `ConstraintTypeSystem.lean` — an alternative constraint-based presentation of HM, with soundness back to `TypeOfHM`. Currently stale against `Core` and excluded from the default build; kept for reference.
- `SpikeC.lean`, `SpikeLetRecAnn.lean` — exploratory spikes for the in-progress annotated-polymorphic-recursion / type-passing work.
- `HasItem.lean` — a small indexed list-membership relation used for context lookups.

## Where things stand

This is the part I'm proud of: the core HM metatheory is done and machine-checked. `infer` is proven sound and complete against the declarative system, it finds principal types, and the dynamics are type-safe (progress + preservation). All of it is axiom-clean.

We recently supported referencing in-scope type variables (skolems) by type annotations on values inside a forall-quantified let binding. This forced a move to type-erased evaluation, since otherwise let reduction would leave orphan skolems (i.e. not scoped inside of a forall quantifier) inside inner type annotations. So our preservation theorem was written to be about a type-erased expression. There were no evaluation semantics for non-type-erased expressions.

We also now support mutually recursive let bindings. This can be done as long as you keep the let bindings monomorphic (during typechecking) and generalise them afterwards.

However I also wanted to support polymorphic mutually recursive let bindings. Polymorphic recursive inference is [undecidable](https://doi.org/10.1145/169701.169692) in general, but is decidable when the bindings have polymorphic type annotations. However, this makes these type annotations un-erasable: upon erasing them, we'd have to fall back to monomorphic type inference, so erasing types would make our language strictly less capable than the typed version. That isn't compatible with type erasure.

In order to keep type annotations while preventing orphan skolems on let reduction, we need to move to a [type-passing](https://doi.org/10.1017/S0956796801004282) semantics, where our core language explicitly carries the instantiated types that a variable pointing to a polymorphic type has been applied to. However, since our language still adheres to the HM restrictions (only prenex polymorphism), it is still fully decidable with inference alone. Thus the types that our polymorphic vars are "applied" to do not actually need to be made explicit in the source program, but can be fully determined by inference.

To express this, we split the original HM declarative relation in two: one defined on the original program that does not contain vars' applied types, and one that operates on an "elaborated" program that _does_ contain applied types. This is effectively an elaboration stage. We therefore repurposed our `Infer` relation to not only infer the type of a given expression, but also return a new expression that takes the types it infers and applies them to polymorphic vars. Thus effectively acting as an elaborator from a non-type-passing source language to a System F style language that contains applied types in the term itself.

This migration (from type erasure to type passing, and from only supporting monomorphic unannotated mutually recursive let bindings to also supporting annotated polymorphic ones) is why `InferW.lean` is currently in a temporarily broken state.

## Building

Requires the Lean toolchain pinned in `lean-toolchain` (`leanprover/lean4:v4.26.0`,
managed by `elan`). On a fresh clone:

```bash
lake exe cache get   # download prebuilt Mathlib oleans (don't recompile Mathlib!)
lake build
```

## Purpose, workflow & LLM usage

This project contains a lot of LLM-written code, primarily Claude Opus 4.x. This formalisation has proven very labour-intensive and requires a lot of legwork. It's therefore a prime candidate for using LLMs to get much of the gruntwork done. At the same time, there have been many points at which the LLM would have gone off the rails had I not taken the time to understand exactly what is going on, get it to explain its choices to me, form a mental picture, and to use my own judgment to guide it to the right path. So this project is simultaneously 1. a testbed for assessing the performance of the latest frontier LLMs, 2. a learn-by-doing project for learning PLT and type theory with all its gnarly complexities, and 3. a tangible source to enlist LLMs to supercharge my own self-learning through detailed back and forth interrogation of the workhorse LLM at points where my intuitions are lacking or where I am presented with a new idea or technique.

Contrary to my initial expectations, it has actually taken a huge amount of human effort to get this project to the state that it is, not just LLM-hours. It has therefore proven quite successful in its goal as a pedagogical project for me.

## References

- J. Roger Hindley. _The principal type-scheme of an object in combinatory logic._ Transactions of the American Mathematical Society 146:29–60, 1969. <https://doi.org/10.1090/S0002-9947-1969-0253905-6>
- Robin Milner. _A theory of type polymorphism in programming._ Journal of Computer and System Sciences 17(3):348–375, 1978. <https://doi.org/10.1016/0022-0000(78)90014-4>
- Luis Damas and Robin Milner. _Principal type-schemes for functional programs._ POPL 1982, 207–212. <https://doi.org/10.1145/582153.582176>
- Alan Mycroft. _Polymorphic type schemes and recursive definitions._ International Symposium on Programming, LNCS 167, 217–228, 1984. <https://doi.org/10.1007/3-540-12925-1_41>
- Fritz Henglein. _Type inference with polymorphic recursion._ ACM TOPLAS 15(2):253–289, 1993. <https://doi.org/10.1145/169701.169692>
- A. J. Kfoury, J. Tiuryn, and P. Urzyczyn. _Type reconstruction in the presence of polymorphic recursion._ ACM TOPLAS 15(2):290–311, 1993. <https://doi.org/10.1145/169701.169687>
- Simon Peyton Jones and Mark Shields. _Lexically scoped type variables._ Microsoft Research, 2002. <https://www.microsoft.com/en-us/research/publication/lexically-scoped-type-variables/>
- Karl Crary, Stephanie Weirich, and Greg Morrisett. _Intensional polymorphism in type-erasure semantics._ Journal of Functional Programming 12(6):567–600, 2002 (ICFP 1998). <https://doi.org/10.1017/S0956796801004282>
- François Pottier and Didier Rémy. _The essence of ML type inference._ In B. C. Pierce (ed.), Advanced Topics in Types and Programming Languages, ch. 10, 389–489. MIT Press, 2005. <https://pauillac.inria.fr/~fpottier/publis/emlti-final.pdf>
- Brian Aydemir, Arthur Charguéraud, Benjamin C. Pierce, Randy Pollack, and Stephanie Weirich. _Engineering formal metatheory._ POPL 2008, 3–15. <https://doi.org/10.1145/1328438.1328443>
- Arthur Charguéraud. _The locally nameless representation._ Journal of Automated Reasoning 49(3):363–408, 2012. <https://doi.org/10.1007/s10817-011-9225-2> — Coq sources: <https://github.com/charguer/formalmetacoq> (the `ln/ML_*` files).
