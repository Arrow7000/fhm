<!-- @format -->

# `fhm` — Formalised Hindley–Milner

A from-scratch formalisation of **Hindley–Milner type inference in Lean 4**, with
machine-checked **soundness** and **completeness (principality)** for Algorithm W —
plus a deliberately opinionated set of extensions that go a bit past textbook HM.

This started life inside a monorepo of Lean experiments and was extracted (with its
full history) into its own home. The name is an abbreviation of *formalised HM*; read
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
