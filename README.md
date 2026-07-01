# FHM: Formalised Hindley-Milner

A formalisation of a language with a Hindley-Milner type system. Includes some additional features, like:

- type annotations on let bindings and lambda variables (not part of core HM)
- annotations can reference [type variables quantified in outer scopes](https://www.microsoft.com/en-us/research/publication/lexically-scoped-type-variables/)
- pattern matching (with wildcard patterns)
- mutually recursive let bindings (unannotated, internally monomorphic)
- mutually recursive let bindings with _polymorphic_ type annotations

## Architecture

A few representational choices shape everything else. Terms use de Bruijn indices for their bound variables; type variables use a locally-nameless representation with cofinite quantification, in the style of [Charguéraud's formalisation of mini-ML](https://github.com/charguer/formalmetacoq/blob/master/ln/ML_Definitions.v). Types come in two layers — monotypes and `∀`-quantified schemes — and typing contexts are de-Bruijn-indexed (with a small `HasItem` membership relation for lookups). Terms also come in two forms: plain source expressions, and _elaborated_ ones that additionally carry the type arguments each polymorphic variable is instantiated at (see the elaboration split below).

The formalisation splits into `Core.lean` and `InferW.lean`.

`Core.lean` is the language and its theory. It defines the term language (`Expr`), two declarative typing relations — `TypeOfHM` on source programs and `TypeOfElabHM` on elaborated ones (they differ in exactly one rule) — a type-passing small-step semantics (`SmallStep.Step`), and the metatheory: substitution lemmas, type safety, and the faithfulness bridge between the two typing relations.

`InferW.lean` is the algorithm. The `Infer` relation specifies inference and elaboration together — from a source expression it produces a substitution, an inferred type, and an elaborated term — and `infer` / `typecheck` are its executable counterparts (`typecheck` runs a whole program from the empty context and generalises the result). Its soundness, completeness, and principality results, and how they bridge to the declarative relations, are covered in the next section.

There is also a surface language that contains syntax for constructing booleans, tuples, lists, patterns for destructuring them in let bindings and match expressions. This surface language is not yet wired up to the rest of the project. This will come when the desired core functionality is fully implemented and proven.

Beyond `Core.lean` and `InferW.lean`, the rest of `FHM/` is:

- `SurfaceLang.lean`, `Pretty.lean` — the surface language and pretty-printers for Core and Surface terms.
- `Examples.lean` — `#eval` demos: infer-then-pretty-print, let-polymorphism, polymorphic recursion, and adversarial reject cases.
- `ConstraintTypeSystem.lean` — an alternative constraint-based presentation of HM, with soundness back to `TypeOfElabHM`. Currently stale against `Core` and excluded from the default build; kept for reference.
- `SpikeC.lean`, `SpikeLetRecAnn.lean` — exploratory spikes used while working out the annotated-polymorphic-recursion / type-passing design.
- `HasItem.lean` — a small indexed list-membership relation used for context lookups.

## Where things stand

The pipeline now works end to end: programs are inferred, elaborated, and evaluated under a type-passing semantics, and the metatheory is machine-checked and axiom-clean.

**The elaboration split.** Supporting polymorphic recursion made type annotations load-bearing, so the declarative system comes in two halves: `TypeOfHM`, the classic decoration-blind HM relation on source programs, and `TypeOfElabHM`, the same system on _elaborated_ programs, where every use of a polymorphic variable carries the type arguments it is instantiated at. The two differ in exactly one rule (`var`). Three bridges tie the algorithm to both: `Infer.sound` (the elaborated output is well-typed in `TypeOfElabHM`), `TypeOfElabHM.faithful` (elaboration is faithful to source-level HM, `TypeOfElabHM ⟹ TypeOfHM`), and `Infer.sourceSound` (the algorithm is sound directly against `TypeOfHM`).

**What's proven.**

- Inference is sound, complete, and finds [principal types](https://doi.org/10.1145/582153.582176) — `Infer.sound`, `Infer.iff_typeable`, `Infer.principal` — with whole-program counterparts `typecheck_sound`, `typecheck_iff`, `typecheck_principal`.
- The unifier is sound and complete: `unify_sound`, `unify_complete`.
- The type-passing dynamics are safe: `TypeOfElabHM.progress` and `TypeOfElabHM.preservation`, bundled as `TypeOfElabHM.type_safety`.
- Mutually recursive bindings are covered both unannotated (`InferRecGroup.sound` / `.complete`) and annotated-and-polymorphic (`InferRecGroupAnn.sound` / `.complete`).

**How we got here.** The core HM system came first — inference proven sound, complete, and principal, over a safe dynamics. Then I wanted type annotations that could reference type variables bound in outer scopes, which initially pushed the evaluator toward type erasure (to avoid leaving orphan skolems behind on let-reduction). Mutual recursion came next — monomorphic during checking, generalised afterwards. The turning point was wanting _polymorphic_ mutual recursion: inference for it is [undecidable](https://doi.org/10.1145/169701.169692) in general but decidable once the bindings carry annotations — and those annotations can't be erased without collapsing back to monomorphic inference, i.e. erasure would make the typed language strictly weaker. So type erasure had to go, replaced by the [type-passing](https://doi.org/10.1017/S0956796801004282) semantics and the elaboration split above.

## Building

Requires the Lean toolchain pinned in `lean-toolchain` (`leanprover/lean4:v4.26.0`,
managed by `elan`). On a fresh clone:

```bash
lake exe cache get   # download prebuilt Mathlib oleans (don't recompile Mathlib!)
lake build
```

## Why this exists

Most of the code and proofs here were written by an LLM — mostly Claude Opus 4.x. I'm not going to pretend otherwise: formalisation is a slog, and much of it is exactly the legwork these models are now good at. But I designed the language and its type system — the features it supports, what the relations and theorems should say, what counts as correct — and I stay the guardian of anything we actually claim to have proved. That part isn't optional: left alone the model will quietly weaken a theorem or prove something adjacent to what I asked, so I stay in the loop wherever it matters, and I've pushed for the principled route wherever it stays decidable, however much harder that makes the proof.

It's also been the best way I've found to actually learn this material. Driving the project — and interrogating the model at the points where my own intuition gives out — has taught me more PLT and type theory than any amount of reading.

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
