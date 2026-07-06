<!-- Written 2026-07-06 after the primops + type-declarations campaigns landed
     (roadmap steps 1–3 done; step 4 was already done). Successor to
     next-agent-brief-primops-typedecls.md (now fully completed). The
     DESIGN REFERENCE + status log is still next-agent-brief-primitives-typedecls-surface.md
     — read it first, don't duplicate it here. -->

# Brief: the surface language → Core bridge (roadmap step 5 — the north star)

## Where the repo stands (2026-07-06)

Everything below Core's north star is DONE, axiom-clean, `lake build` green:

- **Arithmetic primops** (step 1): `intAdd`, `intSub` — a single `Expr.primBinOp`
  leaf over a `PrimBinOp` enum, curried, applied via `app`; fixed monotype in
  both `TypeOf*`; Plotkin δ-rules in `SmallStep.Step`; **structural** (arity-free)
  value semantics (a partial application is a value, a saturated one δ-reduces).
  `intMul`/`intEq`/`neg`/`div` are userland — the irreducible int kernel is
  `{intAdd, intLt}`.
- **`str` → `char`**: the atomic-string primitive was replaced by a primitive
  `Char` (`PrimTy.char`, `PrimLitExpr.char`). Strings become `List Char`.
- **Comparison primops** (step 3): `intLt`, `charLt` (`… → … → Bool`). Env-DEPENDENT
  by design: their `TypeOf*` rule carries `TypeOf ctx (.ctor "True"/"False")
  (customTy "Bool" [])` premises (reusing the `ctor` typing judgment), so they're
  well-typed only relative to a Bool-providing env; `preservation` reads the
  δ-result's type straight off a premise. Inference decides Bool-in-scope via a
  decidable `Ctor.isBoolCtor` and bridges to the judgment in `sound`/`sourceSound`.
  `charEq`/`intEq` are userland (derivable from `<`).
- **Type declarations** (step 2) — `FHM/Decls.lean` (imports only Core; NO new Core
  metatheory, since the theorems are `∀ ctors`): the `DataDecl` AST, the
  `Ty.WellKinded` kind-check (arity of type applications + bvar-range + closedness,
  one inductive), `DataDecls.WF`, a decidable checker (`wellKindedB` + `_iff` ⟹
  `Decidable`), `elabDecls : List DataDecl → Option CtorEnv` with BOTH
  `elabDecls_sound` and `elabDecls_complete`, and a `preludeDecls` (Bool, List).
  `Examples.demoCtors` is now produced by `elabDecls` (the hand-built `mkCtor` is
  retired) — the whole declare → kind-check → elaborate → typecheck pipeline runs
  end-to-end.
- **Lakefile roots**: Core, Decls, SurfaceLang, Pretty, SpikeC, InferW, Examples.
  All 25 headline theorems axiom-clean (`{propext, Classical.choice, Quot.sound}`).

## Your mission: lower the surface language into Core

The surface AST already exists in `FHM/SurfaceLang.lean` (`namespace Surface`):
`Ty`/`PolyTy` with **named** tvars, `PrimLitExpr` (incl. `bool`/`str`), nested
`Pattern` (`pair`/`ctor`/`cons`/`list`/`name`/`wildcard`), and `Expr` (with
`pair`/`cons`/`list`/`ife` sugar, **pattern-lambdas** `lambda (param : Pattern)`,
named `letIn`/`var`). What's MISSING: a surface `DataDecl` (named params), and the
whole **lowering** to Core.

Settled framing (from the reference brief + recent session):

- **No surface *typing* relation, but a declarative *lowering* relation.** Surface
  typing/semantics are still given entirely by Core — do **not** build a
  `Surface.TypeOf`. But lowering itself gets the house-style treatment (as
  `TypeOf`/`Infer`/`unify` do): a declarative `Lowers` **relation** — the readable
  desugaring + name-resolution + kind-checking spec, the trusted artefact the
  theorems are stated against — plus an opaque executable `lower` **function**,
  bridged by **soundness** (`lower s = some c → Lowers … s c`) and **completeness**
  (a valid lowering exists ⟹ `lower` finds one). Surface well-typedness is then
  *defined* against the relation: `s` well-typed `:= ∃ c, Lowers … s c ∧ (typecheck
  env c).isSome`; the executable pipeline decides it with `lower` + `typecheck`.
  Applies to Expr **and** DataDecl lowering.
  - **Completeness nuance:** name-resolution and sugar are deterministic
    (`lower s = some c ↔ Lowers s c`), but **pattern compilation admits several
    valid Core renderings** of one surface match, so `Lowers` is *one-to-many*
    there and completeness reads "if some valid lowering exists, `lower` produces
    one" — not "`lower` produces this exact `c`." Decide up front whether to keep
    `Lowers` non-deterministic for matches (cleaner spec) or pin a compilation
    strategy into it (so `lower` = `Lowers` exactly). The `Lowers` rule for `match`
    is precisely where **pattern-compilation equivalence** (match order + binding +
    exhaustiveness preserved) is pinned down as a spec — so the `lower`-soundness
    obligation for that case *is* the compilation-correctness theorem.
- **Terminology (don't conflate):** *elaboration* = `Infer`'s `e → eOut` (the
  type-passing `tyArgs` decoration, Core-internal); *lowering* = surface → Core
  (name resolution + kind-checking + desugaring), the new work.
- **Pipeline / dependency order:** parse (out of scope / trust) → collect the
  `KindEnv` (+ ctor-name set) from decl headers → **in parallel** elaborate
  DataDecls (`elabDecls`) ∥ lower Exprs (both need only the `KindEnv`) → then
  **typecheck** the lowered Core against the finished `CtorEnv`. Expr *typechecking*
  waits for the `CtorEnv`; Expr *lowering* can overlap once the `KindEnv` exists.
  This is why the plan below is ordered as it is.

## The plan (in order; markers note optional/hard/deferred)

Each item is a committable slice; land them roughly top-to-bottom (the ordering
follows the pipeline dependencies above). Front-end concerns live OUTSIDE Core —
a new surface-bridge module (and `Decls.lean`), never Core's metatheory.

1. **Surface `DataDecl` + its lowering → `Decls.DataDecl` → `elabDecls`.**
   - Add a surface `DataDecl` (named type params + named/field ctors).
   - Lower: named params → `bvar` indices; resolve type references (exists? arity?)
     while producing the `Decls.DataDecl`; then reuse `Decls.elabDecls` → `CtorEnv`.
   - Add **`Pair`** to `Decls.preludeDecls` (needed for tuple sugar, item 4).

2. **`Surface.Ty → Core.Ty` lowering + annotation kind-checking** (against the `KindEnv`).
   - Named tvars → `Ty.bvar` (scoped-tyvar resolution); type applications
     arity-checked — reuse `Decls.Ty.WellKinded`.
   - Load-bearing: Core has **no type-name→arity env at all**, so a bad type name
     or wrong arity in an annotation is NOT caught by typechecking (it only surfaces
     indirectly via ctor arity on construct/match; a phantom on an unused binding
     sails through, still type-safe but nonsensical). This kind-check is a genuinely
     separate, mandatory front-end job.

3. **`Surface.Expr → Core.Expr` — the non-sugar, non-pattern core.**
   - Term name resolution: named `var` → de Bruijn `Expr.var` index [fallible: unbound].
   - `app`, var-lambda, `letIn` (carrying lowered annotations from item 2).

4. **Sugar expansion** [total — no failure of its own].
   - `ife c t f` → `match c with True => t | False => f`; `(a, b)` → a `Pair` ctor;
     `[…]`/`cons` → `Cons`/`Nil`; string literals → `List Char`; `bool` literals →
     `True`/`False`; pattern-lambdas → `lambda` + `match`.

5. **Pattern compilation** [HARD — its own sub-campaign; the known gnarly part].
   - Nested `Surface.Pattern` (ctor/pair/cons/list, arbitrarily deep) → Core's
     *flat, single-level* `match_` (one ctor + arity + wildcard).
   - The equivalence proof must preserve **match order, variable binding, and
     exhaustiveness** simultaneously. Well-studied (Maranget-style) but genuinely
     intricate to *verify* — budget accordingly and reach for the literature.

6. **Exhaustiveness checker.**
   - Core already has `AllMatchesExhaustive` and `progress` REQUIRES it, but there
     is NO executable checker. Add a decidable `checkExhaustive : CtorEnv → Expr →
     Bool` with soundness `= true → AllMatchesExhaustive`.
   - Pattern compilation (item 5) must emit exhaustive Core matches (or this rejects).

7. **Top-level bindings** [small].
   - SCC / dependency analysis → partition into mutually-recursive groups + topo
     order → desugar to nested `letRec`/`letIn` (reuse the fused mixed-recursion
     node — NO new Core metatheory).

8. **Friendly error messages** [optional / UX — do last or opportunistically].
   - Make the checker a *total* `… → Except Error Type`; totality gives "a message
     for every failure," and `iff_typeable` proves error-soundness (an `Error` ⟺
     genuinely ill-typed).
   - A structured `NonInfer`/diagnosis relation (provably-complete error
     *classification*) is a stretch goal — beware the **blame problem** (where to
     report is heuristic, not "the most helpful reason" formalizably).

9. **[DEFERRED — record, do NOT build now]**
   - **Typeclasses / Elm-style constrained vars** (`number`, `comparable`) — the
     real path to polymorphic `+`/`<` over several types; do around/after this push.
   - **Row types / extensible records** — far horizon.
   - **Floats** — not inductively generated, so they'd need a full arithmetic
     primop kernel (unlike int, which needs only `{add, lt}`).
   - **`ord`/`chr`** (Char↔Int) — the first *arity-1* ops; when they arrive, build
     the `primUnOp` node PARAMETRIC (single rule + a `PrimUnOp → Ty` function).
   - **`nat` → Peano data** (retire primitive `nat`) — fold into surface
     numeric-literal desugaring.
   - **Core naming/hygiene backlog + `Core.lean` file split** (see the reference brief).

## Non-negotiables (from the reference brief — restated because they bite)

- Headline theorems stay `sorry`/`admit`/`axiom`-free and axiom-clean; gate every
  increment with a fresh-olean `lake build` + `#print axioms` (the LSP alone is NOT
  the gate after a `Core` edit — the stale-olean trap is real).
- **Core stays minimal**: don't add to its metatheory unless genuinely forced.
- Don't weaken headline statements; add hypotheses to internal helpers instead.
- Delegate bulk proof-plumbing to subagents with precise per-error specs; keep
  design decisions and the build/axiom gate in the parent. Granular commits per slice.
- Append to the reference brief's status log as you land things; don't rewrite history.
