import Experiments.FreshTypeSystem.Core
import Experiments.FreshTypeSystem.InferW

/-! # `Experiments.FreshTypeSystem` — entrypoint module.

A Hindley–Milner type system for a small expression language, developed in
two parts (split across the `FreshTypeSystem/` folder):

* **`Experiments.FreshTypeSystem.Core`** — the declarative side: the syntax
  (`Ty`/`Expr`/`PolyTy`/`Ctx`), call-by-value small-step semantics, the
  locally-nameless + cofinite declarative typing relation `TypeOfHM`, and its
  metatheory (substitution lemmas, weakening, canonical forms, progress,
  preservation).

* **`Experiments.FreshTypeSystem.InferW`** — the algorithmic side: the
  unification substitution algebra, the MGU relation `UnifyRel`, Algorithm W
  as a relation (`Infer`) and as an executable function (`infer`/`unify`),
  their soundness and principality (Damas–Milner completeness), and the
  whole-program `typecheck` API.

Importing `Experiments.FreshTypeSystem` re-exports both. (The alternative
constraint-based development lives in `Experiments.FreshTypeSystem.ConstraintTypeSystem`.)
-/
