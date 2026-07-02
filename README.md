# FHM: Formalised Hindley-Milner

A formalisation of a language with a Hindley-Milner type system. Includes some additional features, like:

- type annotations on let bindings and lambda variables (not part of core HM)
- annotations can reference [type variables quantified in outer scopes](https://www.microsoft.com/en-us/research/publication/lexically-scoped-type-variables/)
- pattern matching (with wildcard patterns)
- mutually recursive let bindings (unannotated members are internally monomorphic, generalised for the body)
- _polymorphic_ type annotations on recursive bindings (enabling polymorphic recursion) — annotations are per binding, so a single group can mix annotated and unannotated members

## Architecture

Type inference here does two jobs at once: it works out the types, and it elaborates the program while doing so. The two can't really be pulled apart, because the whole point of the polymorphic annotations is that inference has to record how each polymorphic variable gets instantiated. So there are two ways to read a program: before elaboration, where those instantiations are left implicit, and after, where they have been written in. Each reading gets its own declarative typing relation.

Here's how the pieces are represented:

- terms use de Bruijn indices for their bound variables
- type variables use a locally-nameless representation with cofinite quantification, following [Charguéraud's formalisation of mini-ML](https://github.com/charguer/formalmetacoq/blob/master/ln/ML_Definitions.v)
- types split into monotypes and `∀`-quantified schemes
- typing contexts are indexed by de Bruijn position

### Core.lean

This is where the language lives and where we say, abstractly, what it means for a program to be well-typed. It doesn't compute anything; it just lays down the rules.

- `Expr`: the term language.
- `TypeOfHM`: the declarative typing relation for the pre-elaboration reading. This is textbook HM, where a polymorphic variable may be used at any instance of its scheme.
- `TypeOfElabHM`: the same relation for the post-elaboration reading, where every polymorphic use carries the exact type arguments it was instantiated at. The two relations are identical apart from that one rule.
- `SmallStep.Step`: a small-step semantics that runs the elaborated program directly, carrying types at runtime rather than erasing them.

### InferW.lean

This is where we actually work out a program's type, instead of just declaring which types are valid. It's the algorithmic side, and it's where elaboration happens.

- `Infer`: a relation specifying inference and elaboration together. From a source program it produces a substitution, an inferred type, and the elaborated program.
- `infer` and `inferCore`: the executable versions of that relation.
- `typecheck`: the whole-program entry point. It runs from the empty context and generalises the result into a closed scheme.

### SurfaceLang.lean 🏗️

This is what the language is meant to look like to a user: real string names, and syntactic sugar for building and taking apart pairs and lists. The plan is to desugar and name-resolve it down into the constructor-based, de-Bruijn-indexed Core language, but that bridging step isn't written yet. Worth a look if you want a fuller picture of the user-facing language.

### ConstraintTypeSystem.lean 🚧

A work-in-progress experiment in a different approach. Instead of Algorithm W, it tries the constraint-based style (Wand; Pottier and Rémy), where inference generates a constraint and then solves it, using guarded constraint schemes `∀ᾱ[C].τ`. It's currently out of date against `Core`, so unlike the surface language it isn't really worth reading yet.

Rounding things out, `Pretty.lean` prints Core and Surface terms readably, and `Examples.lean` collects runnable `#eval` demos, including let-polymorphism, polymorphic recursion, and programs that should be rejected.

### What we've proved

All of these are fully proved. The theorems only use the standard axioms and are completely free of `sorry`s.

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

**Runtime safety** (`Core.lean`):

- `TypeOfElabHM.progress`: a well-typed elaborated program is either a finished value or it can take another step.
- `TypeOfElabHM.preservation`: taking a step never changes a program's type.
- `TypeOfElabHM.type_safety`: putting those together, a well-typed program never gets stuck.

**The elaboration bridge** (`Core.lean`):

- `TypeOfElabHM.faithful`: anything well-typed after elaboration was already well-typed in plain HM, so elaboration never invents new typings.

## How it got here

The core HM system came first: inference proven sound, complete, and principal, over a small-step semantics that was proven safe.

Then I wanted type annotations that could mention type variables bound further out, in an enclosing scope. That caused a problem. When a let binding reduces, those variables can end up orphaned, pointing at a scope that no longer exists. The fix at the time was to erase types before running a program, so there was nothing left to dangle.

Mutual recursion came next. That one stayed manageable as long as I checked the bindings monomorphically and only generalised them afterwards.

The next thing I wanted was polymorphic mutual recursion, and that's where it got hard. Inferring it in general is [undecidable](https://doi.org/10.1145/169701.169692), but it becomes decidable once each binding carries a type annotation. The catch is that those annotations can no longer be erased: erase them and inference has to fall back to the monomorphic case, which would leave the typed language strictly weaker than the annotated one. So erasing types stopped being an option.

That's what forced the current model. Instead of erasing types, the program keeps them and runs under a [type-passing](https://doi.org/10.1017/S0956796801004282) semantics, and inference elaborates each program into that form. To keep everything honest, the declarative typing was split into the two relations above, one for the program before elaboration and one for after, with `TypeOfElabHM.faithful` tying them together. The main piece still missing is the translation from the surface language down into Core.

## Building

Requires the Lean toolchain pinned in `lean-toolchain` (`leanprover/lean4:v4.26.0`,
managed by `elan`). On a fresh clone:

```bash
lake exe cache get   # download prebuilt Mathlib oleans (don't recompile Mathlib!)
lake build
```

## Why this exists

I've been into type systems for a long time, and I have a soft spot for ML-style pure languages like Elm. This is my attempt to formalise a small language and type system in that spirit, and to learn some proper PLT by building one rather than just reading about it.

I've leaned on LLMs a lot along the way, in two ways. I've used them as a tutor, to explain things when I got stuck, and I've handed them most of the proving grunt-work, which is a genuine slog. But whenever that surfaced a broken assumption, the decision came back to me. I made sure I understood enough of the context to make the design call myself, and only then handed the reins back. I designed the language, chose which features it should support, and decided what the theorems needed to say.

Doing it this way has taught me far more than reading would have. I learn by building, and this has been the most rewarding way I've found to actually absorb this material.

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
- Arthur Charguéraud. _The locally nameless representation._ Journal of Automated Reasoning 49(3):363–408, 2012. <https://doi.org/10.1007/s10817-011-9225-2>. Coq sources: <https://github.com/charguer/formalmetacoq> (the `ln/ML_*` files).
