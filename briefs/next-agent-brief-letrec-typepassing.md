<!-- Conversation summary + state-of-play for annotated polymorphic recursion
     (`letRec` Stage 3). Successor context to next-agent-brief-letrec-annotated.md
     and next-agent-brief-letrec-annotated-stage1.md. Written 2026-06-23. -->

# `letRecAnn` — state of play & the type-passing decision

Summary of a long working session on **annotated polymorphic recursion** (Stage 3
of `letRec`). We shipped the Core declarative layer, then discovered that the one
genuinely hard sub-feature ("C", below) is **fundamentally incompatible with the
type-erasure safety architecture** and needs **type-passing**. No final decision
was taken on whether/how to pursue type-passing; this doc captures the reasoning so
it isn't lost.

## TL;DR

- **Stage 1 (Core: node + declarative rule + dynamics + full safety) is DONE, green,
  axiom-clean.** It supports **Feature A** — own-`∀` polymorphic recursion, **self
  and mutual** — soundly under erasure.
- The hard case is **C**: a recursion scheme that references a type variable bound by
  an **enclosing** scope (i.e. `ScopedTypeVariables` on a nested poly-recursive
  helper). We **proved** this cannot work under type-erasure.
- The principled fix for C is **type-passing** (explicit type application + type-beta
  reduction). It keeps HM inference fully intact and, as a bonus, **dissolves the
  type-erasure premises** that currently clutter the preservation theorems.
- **Open question for when we return:** do real programs genuinely need C, or does
  Feature A (mutual poly-recursion, done) + lambda-lifting (the opaque cases) cover
  the actual use cases? The Elm evidence leans toward "Feature A is enough," but it's
  unresolved.

## The feature taxonomy (the key mental model)

A recursion scheme `σ` on a binding can mention type variables in three ways:

- **A — own `∀`-bound variables** (`f : ∀a. …`, the `a` is `σ`'s own quantifier).
  This includes both **self** poly-recursion (`f` calls itself at a different type)
  and **mutual** poly-recursion (independent per-binding schemes, cross-instantiated).
  These vars are `bvar < paramCount`, bound by the scheme itself, so they're
  genuinely polymorphic and **erasure-safe**. **DONE in Stage 1.**
- **B — a top-level free `fvar`** (a rigid scoped constant, like `openId`'s `fvar 5`).
  Declaratively + safety: fine (free `fvar`s never dangle). *Inference* would need the
  `rigid` set threaded — but that's the **same machinery the existing `letIn`
  scoped-variable inference already uses**, not novel. Deferred work, not a mystery.
- **C — a variable bound by an ENCLOSING scope** (a nested helper whose annotation
  mentions the enclosing function's `∀a`; Haskell `ScopedTypeVariables`). **This is the
  hard one. Not doable under type-erasure (proven).**

C is **orthogonal to mutual recursion.** Mutual recursion uses independent schemes
(Feature A) and is fully supported; C is specifically about cross-*scope* variable
sharing.

## Why C is impossible under type-erasure (proven)

The collision of three facts:
1. C's scheme is **load-bearing** (it's what makes the recursion polymorphic), so
   erasure can't delete it without losing typeability.
2. The variable `a` is bound by an enclosing binder that gets **consumed** by
   reduction.
3. Under **type-erasure** the reduction is untyped, so consuming that binder
   **substitutes nothing** — `a` is never replaced by a concrete type.

Two "rescue" ideas were tried and shown to fail:
- **Freeze-and-re-generalise** (erase the enclosing `∀a`, freeze `a` to a fresh free
  `fvar Z`, let the now-unannotated binder re-generalise `Z`). **Fails:**
  `SpikeC.cTerm_rigid` proves a kept scheme carrying a free `fvar Z` is **rigid** in
  `Z` (`InstantiatesBy.fvar` only maps an `fvar` to itself), so the term is *not*
  polymorphic in `Z` and the enclosing binder **cannot re-generalise it**.
- **Gradual / lazy erasure** (erase node-by-node as you Step, not upfront). **Fails:**
  the issue isn't the *timing* of erasure; it's that the load-bearing scheme can never
  be deleted and the consuming step carries no type to substitute. "Resolving" the
  scoped variable must mean **substituting** it (= type-passing), not **deleting** it
  (= erasure). Push the gradual idea until it works and it *becomes* type-passing.

Root cause in one line: **type-erasure makes reduction untyped, but C needs a type
substituted at the consuming step.**

## Type-passing — the fix (and why it's not as scary as it sounds)

Concretely:
- `Expr.var` gains a `tyArgs : List Ty` field (explicit type application: `f [Int]`).
- Generalising binders carry a type abstraction `Λ` over the generalised vars.
- Reduction gains **type-beta**: `(Λa. e) [T] → e[a := T]`, which substitutes `a`
  **through the kept scheme** at each use → no dangling, and different uses get
  different (correct) instantiations.

Crucial clarifications established in the session:
- **Inference is NOT lost.** Inference (static) and type-passing-vs-erasure (dynamic)
  are independent axes. GHC = full HM inference + System-FC type-passing Core. Rank-1
  / prenex stays exactly as inferable.
- **"Elaboration" here is just decoration, not a surface→Core translation.** Inference
  already computes the instantiation at each `var` use — `Infer.var` opens the scheme
  at `freshVars Φ polyTy.paramCount` and unification constrains them. Type-passing
  simply **keeps** that (apply the final substitution `S` to record concrete `tyArgs`
  in the term) instead of discarding it. `tyArgs` may still contain generalised type
  vars after `S`; those become bound by the enclosing `Λ`.
- **Bonus: it removes the type-erasure scaffolding.** Type-beta also substitutes the
  scoped `bvar` in the original `probeV` counterexample (`Core.lean` ~4794) that
  *motivated erasure in the first place*. So `eraseTyAnnots` / `erase_preserves_typing`
  / the `IsTyErased`-gated safety theorems could be **deleted**, not added to. (User
  wants these gone anyway.)
- **The hard preservation step reuses what we have:** type-beta's substitution is the
  existing `Ty.substFvar` / `PolyTy.openVars` machinery, and its subject-reduction case
  is essentially `typ_subst_preservation` (already proven).

**Cost:** `Expr.var` carrying `tyArgs` ripples through the term functions + the `var`
typing rule; the dynamics + `progress`/`preservation` get redone on the type-passing
reduction. The **inference half (`InferW`) is largely preserved** (it becomes the
elaborator that emits `tyArgs`). Substantial but standard (GHC-Core-style), not a
research gamble.

## Cheaper partial alternative: lambda-lifting

A local helper that uses the enclosing variable **opaquely** (just passes `a`-values
around, never doing `a`-specific operations linked to the enclosing function) can be
**lambda-lifted** to a top-level binding with `a` as its **own** `∀`-parameter —
converting C into Feature A (erasure-safe, already supported).

- **Handles:** opaque-`a` local helpers (the common shape).
- **Cannot handle:** non-opaque-`a` (the body genuinely uses the enclosing function's
  `a`-specific operations), or a helper that is mutually recursive *with its host*.

The **opaque / non-opaque** split is the real fault line for "is type-passing
needed." A rejected refinement ("typecheck the helper as its own `∀b`, then post-check
that every use instantiated `b := a`") recovers the *use-site* restriction but fails
on the *body* — an `a`-using body can't typecheck as `∀b`, so it reduces to
lambda-lifting and doesn't extend coverage to genuine C.

## The Elm investigation (`elm-letrec-test/FINDINGS.md`)

A separate agent tested Elm 0.19.1. Findings + our reading:
- Elm allows **mutual** polymorphic recursion via annotated siblings (= **Feature A**,
  independent schemes) but **not self** polymorphic recursion (self-references are
  monomorphic). Every passing example there is Feature A — **none is C.**
- That self-recursion restriction is an Elm *inference choice*, **not** a soundness
  law: we **support self poly-recursion soundly** (`SpikeC`/`SpikeLetRecAnn`
  witnesses), i.e. we're strictly more permissive than Elm here. Restricting it would
  help us with nothing (it's orthogonal to C).
- **Unresolved:** whether Elm (or real programs) actually use C — a nested helper's
  annotation referencing the enclosing function's type variable, especially inside a
  mutual block. A *prior* agent reportedly found inner helpers *do* reference scoped
  type vars; this agent's findings don't exhibit C. The two test **different axes** and
  may both be true. A plausible hypothesis (worth a targeted test): Elm's implicit
  quantification is **best-effort** — reference the scoped var when it can, quietly
  re-quantify fresh otherwise (which would dodge C). **Re-verify carefully before
  treating C as a real-world requirement.**

## What's on disk

- **`Experiments/FreshTypeSystem/Core.lean`** — Stage 1 landed: `Expr.letRecAnn` node,
  `TypeOfHM.letRecAnn` rule, `Step.letRecAnnUnfold`, full safety chain (incl.
  `recAnn_binding_hasScheme`), all structural/erasure cases. Axiom-clean
  (`propext`/`Classical.choice`/`Quot.sound`); independently re-verified. Also: lint
  cleanup (dead `decreasing_by` branch removed; redundant premises dropped from
  `rewrap_at_opening`/`rewrap_hasScheme`).
- **`Experiments/FreshTypeSystem/SpikeLetRecAnn.lean`** — standalone Stage-1 design
  spike (the `TypeOfLetRecAnn` predicate, a genuine poly-rec witness, the
  monomorphic-reading-fails `#eval`, and proven `weaken_env`/`typ_subst` templates).
- **`Experiments/FreshTypeSystem/SpikeC.lean`** — the C investigation:
  `cTerm_typeable` (Feature B types), **`cTerm_rigid`** (the obstruction — kept scheme
  rigid in `Z`), `mutual_typeable` (mutual poly-rec = Feature A, works). Axiom-clean.
- **`next-agent-brief-letrec-annotated-stage1.md`** — the Stage-1 implementation brief.
- **`elm-letrec-test/FINDINGS.md`** — the Elm empirical study (separate agent).

## Suggested next steps (when fresh)

1. **Resolve "is C real."** Targeted Elm (and/or GHC) tests for the exact case: a
   nested helper, inside a mutual block, whose annotation references the enclosing
   function's type variable *non-opaquely*. Classify the programs you actually care
   about as Feature A (done), opaque-`a` (lambda-liftable), or genuine non-opaque C.
2. **If C is needed → scoping spike for type-passing.** A minimal typed-Core fragment
   (`var i tyArgs`, `Λ` binders, type-beta `Step`) and a subject-reduction proof for
   the C witness, reusing `typ_subst_preservation`, to (a) confirm it closes and
   (b) size the rebuild honestly. Weigh full type-passing (cleanest; deletes the
   erasure scaffolding) vs a hybrid (type-passing only for the annotated fragment).
3. **If C is not needed →** Feature A is done; finish Feature B inference (rigid
   threading, mirrors existing `letIn` scoped-var inference) and Stage 2/3 inference
   for `letRecAnn` (the locked `Infer.letRecAnn` / `InferRecGroupAnn` shape from the
   session — escape conditions per-binding, threaded; soundness via `sound_letInAnn`
   renaming; completeness is the heavy lift).

## Relevant literature (gathered this session)

- **Decidability:** Mycroft 1984; Henglein 1993 (annotated poly-rec decidable;
  unannotated = semi-unification = undecidable).
- **Declarative rule:** Pottier, MPRI 2-4-2 (`LetRecPoly`).
- **Type-passing is the standard for load-bearing types:** Rémy MPRI (poly-rec
  compilation needs the type-passing recursive closure); Pottier (monomorphization
  impossible under poly-rec); Crary–Weirich–Morrisett, *Intensional Polymorphism in
  Type-Erasure Semantics*.
- **Erasure soundness needs annotations to be non-computational:** Mishra-Linger &
  Sheard (EPTS); Tejiščák (Idris erasure) — "erasure commutes with substitution."
- **Scoped type variables:** GHC users-guide (scoped vars are *rigid*, no inference);
  Pierce/Shields/Peyton Jones, *Lexically scoped type variables*; GHC Core (System FC)
  is explicitly typed = type-passing.
- **Style:** Chargueraud, *Engineering Formal Metatheory* (locally-nameless +
  cofinite — what `Core.lean` uses).
