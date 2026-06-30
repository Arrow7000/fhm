<!-- @format -->

# FHM: Formalised Hindley–Milner

A formalisation of a language with a Hindley-Milner type system. Includes some additional features, like:

- type annotations on let bindings and lambda variables (not part of core HM)
- annotations can reference type variables quantified in outer scopes
- pattern matching (with wildcard patterns)
- mutually recursive let bindings (unannotated, internally monomorphic)
- in progress: mutually recursive let bindings with _polymorphic_ type annotations

Term bindings use de Bruijn indices.

This formalisation splits things into Core.lean and InferW.lean.

Core.lean contains the language itself (`Expr`), the declarative typing relation (`TypeOfHM`), operational semantics in the form of a small step evaluator (`SmallStep.Step`), as well as various lemmas and theorems. E.g. substitution, and progress and preservation lemmas.

InferW.lean contains an algorithmically-oriented relation `Infer` as well as its actual implementation `infer` – or `typecheck` for a complete program. It contains soundness and completeness lemmas between the `Infer` relation and the `infer` function, as well as bridging lemmas between `Infer` and `TypeOfHM`. Taken together, we prove that for any HM-typeable expression `infer` finds a type, and that any type found by `infer` is HM-typeable.

We also prove that `infer` finds principal types (the most general type allowable by the declarative typing relation).

The declarative typing relation `TypeOfHM` uses cofinite let-generalisation, taken from Chargeraud's formalisation of mini-ML.

There is also a surface language that contains syntax for constructing booleans, tuples, lists, patterns for destructuring them in let bindings and match expressions. This surface language is not yet wired up to the rest of the project. This will come when the desired core functionality is fully implemented and proven.

## Recent changes

We recently supported referencing in-scope type variables (skolems) by type annotations on values inside a forall-quantified let binding. This forced a move to type-erased evaluation, since otherwise let reduction would leave orphan skolems (i.e. not scoped inside of a forall quantifier) inside inner type annotations. So our preservation theorem was written to be about a type-erased expression. There were no evaluation semantics for non-type-erased expressions.

We also now support mutually recursive let bindings. This can be done as long as you keep the let bindings monomorphic (during typechecking) and generalise them afterwards.

However I also wanted to support polymorphic mutually recursive let bindings. Polymorphic recursive inference is undecidable [source](source) but is decidable when the bindings have polymorphic type annotations. However, this makes these type annotations un-erasable. Since upon erasing these type annotations, we'd have to fall back to monomorphic type inference. Thus erasing types would make our language strictly less capable than the typed version. This is thus not compatible with type erasure. In order to keep type annotations while preventing orphan skolems on let reduction, we need to move to a type-passing semantics, where our core language explicitly carries the instantiated types that a variable pointing to a polymorphic type has been applied to. However, since our language still adheres to the HM restrictions (only prenex polymorphism), it is still fully decidable with inference-only. Thus, the types that our polymorphic vars are "applied" to do not actually need to be made explicit in the source program, but can be fully determined by inference alone. To express this, we split the original HM declarative relation in two: one that is defined on the original program that does not contain vars' applied types, and one that operates on an "elaborated" program that _does_ contain applied types. This is effectively an elaboration stage. We therefore repurposed our `Infer` relation to not only infer the type of a given expression, but also returns a new expression, that takes the types it infers and applies it to polymorphic vars. Thus effectively acting as an elaborator from a non-type-passing source language to a System F style language that contains applied types in the term itself.

This above migration (from type erasure to type passing, from only supporting monomorphic unannotated mutually recursive let bindings to also supporting annotated polymorphic ones) is why Infer.lean is currently in a temporarily broken state.

## Purpose, workflow & LLM usage

This project contains a lot of LLM-written code, primarily Claude Opus 4.x. This formalisation has proven very labour-intensive and requires a lot of legwork. It's therefore a prime candidate for using LLMs to getting much of the gruntwork done. At the same time, there have been many points at which the LLM would have gone off the rails had I not taken the time to understand exactly what is going on, get it to explain its choices to me, form a mental picture, and to use my own judgment to guide it to the right path. So this project is simultaneously 1. a testbed for assessing the performance of the latest frontier LLMs, 2. a learn-by-doing project for learning PLT and type theory with all its gnarly complexities, and 3. a tangible source to enlist LLMs to supercharge my own self-learning through detailed back and forth interrogation of the workhorse LLM at points where my intuitions are lacking or where I am presented with a new idea or technique.

Contrary to my initial expectations, it has actually taken a huge amount of human effort to get this project to the state that it is, not just LLM-hours. It has therefore proven quite successful in its goal as a pedagogical project for me.

---

A from-scratch formalisation of **Hindley–Milner type inference in Lean 4**, with
machine-checked **soundness** and **completeness (principality)** for Algorithm W —
plus a deliberately opinionated set of extensions that go a bit past textbook HM.

This started life inside a monorepo of Lean experiments and was extracted (with its
full history) into its own home. The name is an abbreviation of _formalised HM_; read
nothing further into it.

## What's in here

The core development lives under `FHM/`:

- **`Core.lean`** — the declarative type system: types, schemes, contexts (de Bruijn),
  the `TypeOfHM` typing relation, type-erasure dynamics, and the metatheory
  (progress / preservation, i.e. type safety).
- **`InferW.lean`** — the executable **Algorithm W**: a verified unifier and inferencer,
  with `unify` / `infer` proven **sound** and **complete**, culminating in
  **principality** of inferred types. Axiom-clean.
- **`ConstraintTypeSystem.lean`** — an alternative constraint-based presentation of HM
  (guarded constraint schemes) with soundness back to `TypeOfHM`. ⚠️ Currently **stale**
  against `Core` (predates the `fst`/`snd` refactor), so it's kept for reference/history
  but excluded from the default build.
- **`SurfaceLang.lean` / `Pretty.lean`** — an Elm-flavoured surface language and
  readable pretty-printers for Core and Surface terms.
- **`Examples.lean`** — end-to-end `#eval` demos: infer-then-pretty-print, let-polymorphism,
  polymorphic recursion, adversarial reject cases.
- **`SpikeC.lean` / `SpikeLetRecAnn.lean`** — exploratory spikes for in-progress work
  (annotated polymorphic recursion / type-passing). `SpikeLetRecAnn` compiles;
  `SpikeC` is a forward draft referencing a `letRecAnn` constructor not yet in `Core`,
  so it's excluded from the default build.
- **`HasItem.lean`** — a small indexed list-membership relation used for
  context lookups.

### The opinionated extras

Beyond vanilla HM, this development covers:

- **Scoped type variables** — rigidity-aware unification that respects user-written,
  scope-bound type annotations (Haskell-ish `ScopedTypeVariables`).
- **Annotated `let`** — skolemising-and-unifying inference for annotated bindings.
- **`letRec`** — recursive binding groups under a shared-monotype rule, with **mutual**
  polymorphic recursion supported soundly under type erasure.
- **Pattern matching** — typing, dynamics, and inference for `match`.
- **Type-erasure semantics** — the dynamics run on erased terms, and safety is proven
  against them.

## Building

Requires the Lean toolchain pinned in `lean-toolchain` (`leanprover/lean4:v4.26.0`,
managed by `elan`). On a fresh clone:

```bash
lake exe cache get   # download prebuilt Mathlib oleans (don't recompile Mathlib!)
lake build
```

## Working notes (`briefs/`)

The `briefs/` directory holds the running **next-agent handoff briefs** — candid,
chronological design notes (state of play, dead-ends, proofs of impossibility, open
questions). They cross-reference each other, so they read as a trail. If you (human or
agent) are picking the project back up, start from the most recent relevant brief and
follow its "successor context" links backwards. The most recent frontier as of writing
is `briefs/next-agent-brief-letrec-typepassing.md`.

## Status

Research / experimental. The HM core (inference soundness + completeness, safety) is
proven and axiom-clean; the `letRec` and annotated-polymorphic-recursion work is an
active frontier (see `briefs/`). The door is deliberately left open to growing beyond
HM.
