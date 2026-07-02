<!-- Planning doc written 2026-07-01 after the nested-letRecAnn feature landed.
     HEAD at writing: 4677731. Successor to next-agent-brief-phase6-adversarial-review.md
     and next-agent-brief-corev2-and-surface.md (whose §2–§3 this refines). -->

# Brief: primitives → type declarations + prelude → mixed recursion → surface language

This captures the roadmap and the **design decisions** agreed in discussion, so the
next agent doesn't have to re-derive them. The core HM metatheory (Core + InferW) is
done, axiom-clean, and now supports annotated polymorphic mutual recursion including
**nested `letRecAnn` schemes that reference an outer scoped type variable** (the
type-passing payoff). `FHM.InferW` and `FHM.Examples` are back in the lakefile build.

## The ordered roadmap

1. **Arithmetic primitive ops** (self-contained; the on-ramp — details below).
2. **Type declarations + prelude** (user `data` decls → `CtorEnv`; a fixed prelude env).
3. **Comparison / boolean primops** (`<`, `==`, … → `Bool`; needs the prelude).
4. **Mixed annotated/unannotated mutual recursion** (the hard one; completes the trifecta).
5. **Surface-language bridging** (desugar → resolve → elaborate + bridge lemmas + pattern
   compilation; includes the prelude). This is the north star (see README ~L90 and
   `next-agent-brief-corev2-and-surface.md` §3's staged 0→6 plan).

**Later, explicitly deferred (record, don't build yet):**
- **Typeclasses / overloading** (ad-hoc polymorphism, e.g. one `+` over `int` and `nat`).
  Genuinely needed to make the language *usable*; do it around/after the first surface
  bridging push. Not trivial (dictionary elaboration or similar).
- **Row types / extensible records** (Elm-style). Core-deep (row kind, row unification,
  re-prove principality). The far horizon; not critical to anything else.
- **Top-level mutually-recursive `def` groups** (same SCC/elaboration machinery as `let`
  blocks); small, fold into recursion or surface work whenever.
- **Brief consolidation / repo hygiene** whenever.

## Design decisions (agreed)

### Primitive ops
- **Representation:** a `PrimOp` enum + a single `Expr.primOp : PrimOp → Expr` node
  (mirrors the single `primLit` ctor — do NOT add one Expr constructor per operator).
  A `primOp` is a nullary node applied via ordinary `app`; it is a **monomorphic
  primitive function** (curried), e.g. `intAdd : int → int → int`.
- **Typing:** each `PrimOp` has a fixed type (a small total `PrimOp → Ty`). Trivial for
  inference — treat like a monomorphic `ctor` (fixed type, no `tyArgs`).
- **Dynamics = Plotkin-style δ-rules:** extend `SmallStep.Step` with one rewrite per
  *saturated* primop on literal args, e.g. `app (app (primOp intAdd) (int m)) (int n) ↝
  int (m + n)`. This is the operational counterpart to the op's type (β reduces lambdas;
  δ reduces built-ins).
- **Progress/preservation gotchas:** (a) a **partially-applied** primop (`intAdd (int 2)`)
  is a *value/stuck function*, NOT an error — progress must treat it as canonical;
  (b) canonical-forms: a value of type `int` is an `int` literal; (c) preservation for a
  δ-step is otherwise trivial (fixed types).
- **Cascade:** every structural function/lemma over `Expr` gets a new `primOp` case, but
  almost all are trivial (it's a leaf / a value / reduces by δ). Mostly mechanical.

### Bool, and the "op returns a ctor that may not be in the env" question
- **`Bool` is a DATA type in the prelude** (`True`/`False` ctors), NOT a primitive type.
  This keeps elimination uniform (`if` desugars to `match` on `True`/`False`) and avoids a
  second primitive eliminator.
- **Comparison primops return `Bool`**, so their δ-rule produces `.ctor "True"/"False"`.
  For type-safety this requires `Bool`/`True`/`False` in the ambient `CtorEnv` — *exactly
  the env-dependency `ctor` already has*. **Resolution:** the comparison primop's TYPING
  rule looks up `Bool` (+ `True`/`False`, right arity) in the env (like `ctor` does) and
  assigns result type `customTy "Bool" []`. Then "typechecks ⟹ Bool present ⟹ δ-result
  well-typed ⟹ preservation holds." Nothing is ever undefined; the op is simply only
  *sound relative to a Bool-providing env* — always true in practice (the prelude).
- **Staging consequence:** arithmetic ops (return primitive `int`) are unconditional and
  come FIRST; comparison/boolean ops come AFTER the prelude exists.

### Nats and ints
- **`int` stays primitive** with primitive literals + primitive arithmetic — unavoidable
  (opaque literals can't be computed on in userland).
- **`nat`: consider making it Peano data** (`Nat = Zero | Succ Nat`, already in
  `demoCtors`), with numeric literals desugaring to nested `Succ`/`Zero`. Then nat
  arithmetic is **userland** (recursive `add`/`mul` via `match`) — no primop needed. This
  could eventually retire the primitive `nat` type (a bool-style cleanup). Open choice;
  not required for step 1.

### Elm-style infix operators (a SURFACE feature)
- Core only ever has named primitive *functions*. The surface language provides infix
  operator **syntax + fixity** that **desugars to application** (`a + b ↝ intAdd a b`, or
  to a userland function). So Core needs no "binop handling"; the operator mechanism lives
  in the surface layer (à la Elm — the mechanism is part of the language even if specific
  ops are ordinary definitions).

### Type declarations — no new *Core* metatheory, but real validation
- Core's soundness/completeness/safety theorems are already `∀ ctors, …` and `ctor`/`match`
  just look up the env. So a `data` decl = well-formed entries added to the `CtorEnv`; the
  existing theorems already cover it. (Recursive and mutually-recursive data types already
  work — `demoCtors` has `Peano`, `Tree`/`Forest`.)
- The work is in the **`data`-decl → `CtorEnv` elaboration** (new code, not new
  metatheory): arity/kinding (type applications at correct arity; ctor result matches the
  declared type), well-formed ctor entries (contents `bvarsBelow paramCount` + closed —
  the existing `Ctor` structure demands this), name resolution, and uniqueness. All
  rejections happen here, not in the typing relation.
- **Recursive types are fine for soundness.** Uninhabitable/degenerate types (no base
  case) are a *usability lint*, not a safety issue — validate "at some point," not
  required for metatheory. (Elm's self-recursive-record restriction is about transparent
  *aliases*, which we don't have.)

### Mixed annotated/unannotated recursion (step 4 — the hard one)
- Fuse the two existing rules. `letRec` uses **one shared** opening `G ↦ Xs` for all
  (unannotated) bindings (shared-monotype linking); `letRecAnn` opens **each** binding at
  its **own** fresh `Ys` (scheme-relative). A mixed block needs both simultaneously: the
  per-binding annotated openings live *nested inside* the shared-`Xs` quantifier, since
  during checking every binding sees an env with annotated bindings at their full schemes
  `σⱼ` AND unannotated ones at their shared-pool monotypes `τₖ[G↦Xs]`.
- **Representation:** one node with per-binding `Option PolyTy` (mirroring `letIn`'s
  `ann`); `letRec` / `letRecAnn` become the all-`none` / all-`some` special cases, so a lot
  of existing proofs are reusable as the boundary cases.
- **Risk:** subject reduction is manageable; the **completeness/principality** proof for
  the fused rule (inference allocates fresh monotypes for unannotated bindings, keeps
  annotated ones polymorphic, infers mutually, unifies, generalises *only* the unannotated
  ones over the residual pool) is the real effort. Moderate — comparable to the
  nested-`letRecAnn` change, but with more genuinely-new proof content.
- **CORE MIGRATION LANDED (2026-07-02, same session as the spike):** the direct-replace
  route was taken. `Expr.letRecAnn` is GONE; `Expr.letRec` now carries
  `anns : List (Option PolyTy)` (mirroring `letIn`'s `ann`). One fused typing rule in
  `TypeOfElabHM`/`TypeOfHM` (constructor-implicit `specs : List RecSpec` with
  `mono τ | poly σ`, env projections `RecSpec.rhsEntry`/`bodyScheme`, premise
  `specs.map RecSpec.ann = anns`; TWO separate cofinite premises `hmono`/`hpoly` because
  the kernel rejects `∧` under binders in an inductive).
- **PREMISE PACKAGING (2026-07-02, follow-up in the same session):** the fused rule's
  premises are now NAMED, docstringed definitions (Core ~L2212–2290): the rule reads
  `RecSpecs.WF anns bindings specs G → RecSpecs.MonoTyped TypeOf ctx bindings specs G L
  → RecSpecs.PolyTyped TypeOf ctx bindings specs G L → bodyCtx = RecSpecs.bodyCtx ctx
  specs G → …`, with `RecSpecs.rhsCtx`/`bodyCtx` as the two context builders.
  `MonoTyped`/`PolyTyped` are parametric in the relation, so `TypeOfElabHM` and
  `TypeOfHM` share them verbatim. Everything is DEFINITIONALLY transparent (apply/intro
  work through the defs; auto-generated recursors provide IHs through them — verified);
  only syntactic `rw`/`simp` need `simp only [RecSpecs.rhsCtx]`-style unfolds.
  `RecSpecs.WF` is a structure (fields `anns_eq/length/nodup/mono_lc/poly_wf`).
  The InferW port MUST state its lemmas against this packaged shape. A fresh
  `lake build` of the restored stack (Core+SurfaceLang+Pretty+SpikeC) passed
  post-packaging, discharging the build gate for the Core layer.
- **PACKAGING WAVE 2 (2026-07-02, later same session):** the remaining noisy rule
  premises are also named now, shared between both relations: `letIn` uses
  `Option.Pins ann M` + `GeneralisesTo TypeOf ctx ann boundExpr M L` (the cofinite
  let-generalisation premise); `lambda` uses `paramTy.IsLC` + `Option.Pins`;
  `TypeOfElabHM.var` bundles arity+LC as `Ty.AreLC polyTy.paramCount tyArgs` (now 3
  premises — old `htyargs`/`hlen` are `hlc.2`/`hlc.1`); scheme instantiation goes
  through the wrapper `PolyTy.InstantiatesTo σ tyArgs τ` (defeq to
  `InstantiatesBy tyArgs σ.body τ`, which stays as the recursive engine — the
  match rule still uses the raw form on `ctor.contents`; the old `@TODO` above
  `InstantiatesBy` is resolved this way, deliberately WITHOUT an arity constraint
  since `TypeOfHM.var` is arity-lax by design); both branch `mk` rules shrink to 3
  premises via the shared `structure BranchCtorSpec` (fields
  `lookup/scrut_eq/arity/bind_count/fields`) with the `patternBindings` intermediate
  inlined; `BranchMotive`'s inl-disjunct now carries `BranchCtorSpec` (9-slot
  destructure `⟨ct, c, n, tyArgs, instContents, hpat, hspec, _, hbodyIH⟩`).
  Everything defeq-transparent as before. Fresh `lake build` passed (7747 jobs);
  headline theorems axiom-clean. One unified `RecGroup.*` helper
  suite over `List (Option PolyTy)` (`shieldDepths`/`instAnns`/`openAnns`/
  `instTyAux`/`openTyVarsAux` keyed by `RecAnn.params`); `Expr.TyBvarBounded.RecGroup`
  is now the shielded (anns-keyed) predicate. Preservation rewrap fused via
  `RecSpec.openAt` + `rec_rewrap_typed` (mono-group trick generalises: transported
  specs at the EMPTY pool make body env = RHS env), with `rewrap_hasScheme_mono`
  (generalised scheme) and `rewrap_hasScheme_poly` (declared scheme) per member kind.
  **Status: Core + SurfaceLang + Pretty + SpikeC are green and in the lakefile;
  progress/preservation/type_safety_star axiom-clean via lean-lsp verify.
  NOT yet ported: InferW (20k lines — fused `Infer` rule + threading relations +
  soundness/completeness/executable) and Examples; both OUT of the lakefile until
  ported. A fresh-olean `lake build` gate is still owed when the stack is restored.**
- **SPIKED (2026-07-02): `FHM/SpikeLetRecMixed.lean`** validates the fused declarative
  rule standalone (NOTE: now superseded by the landed Core rule and REMOVED from the
  lakefile — it references the pre-migration constructors; port its two witnesses into
  Examples at cleanup, then delete it). Machine-checked there: the nested-quantifier
  rule shape (per-binding `Ys` inside shared-pool `Xs`, inner exclusion `L ++ Xs`); both
  degeneracy directions (all-`none` ⟺ Core `letRec`, all-`some` ⟺ Core `letRecAnn` — the
  `Option PolyTy` representation claim); a genuinely mixed positive witness (poly-recursive
  annotated `f` + unannotated `g` cross-calling it at a pool var; neither shipped rule
  covers it); the **skolem-leak rejection** (annotated member forcing an unannotated
  sibling's monotype to mention its skolem is underivable — the quantifier nesting is
  load-bearing, proof is a short inversion + freshness pick); and `weaken_env` (zero
  friction) + `typ_subst` (= the shipped `letRec` + `letRecAnn` case machinery run
  simultaneously; the only new content is a pointwise-by-constructor env transport; every
  lemma needed already exists in Core). All axiom-clean. The spike's `RecSpec`
  (`mono τ | poly σ`) with `rhsEntry`/`bodyScheme` projections is a candidate shape for
  the Core rule's internals. NOT spiked (node-dependent): preservation rewrap, inference.

## Recursion status (so nobody re-opens closed doors)
- **Done:** `letRec` (monomorphic, generalise-after), `letRecAnn` (annotated polymorphic
  mutual recursion), scoped type variables in annotations, **nested `letRecAnn` schemes
  referencing outer scoped vars** (Feature C), and **inference of scoped-var threading in
  `letRecAnn`** (Feature B — demonstrated by the nested witness in `Examples.lean`:
  `let (g : ∀a. a→a) = (let rec (loop : a→a) = λy. loop y in loop) in g` infers `∀a. a→a`).
- **Open:** mixed blocks (step 4) and top-level `def` groups only.

## Cleanup-pass backlog (deferred; do as a dedicated hygiene session)

- **Naming debt in Core**: `Ty.renameG` (it's a parallel free-var rename of the pool
  — the "G" says nothing), `PolyTy.genGroup` (it's PER-BINDING generalisation over a
  shared pool, not a group op), `Expr.SubstArgsGe` (opaque), and the
  `ContainsBvarsUpTo`/`Ty.IsLC`/`bvarsBelow` family (same idea, three spellings).
  Renames ripple into briefs/README — batch them.
- **Move examples out of Core**: the `LetRecAnnSmokeTest` namespace + demo defs at the
  bottom of `Core.lean` belong in `Examples.lean`.
- **Stale docstring**: `HasSchemeVars` still claims to be "exactly the cofinite premise
  of `TypeOfElabHM.letIn`" — that role now belongs to `GeneralisesTo` (the ann-aware
  opener); `HasSchemeVars` is the `instTy`-based sibling.
- **Optional**: `Ctx.extend`-style builders for the remaining inline
  `{ ctx with env := … ++ ctx.env }` in lambda/match (marginal; short enough inline).
- **File split** of `Core.lean` (Syntax/Semantics/Typing/Metatheory/Safety) + a
  reader's-map ToC module doc — owner wants to think about the structure first.
- **Rejected on principle**: merging `TypeOfElabHM`/`TypeOfHM` behind an `elab : Bool`
  flag (dedupes one rule, pollutes every proof). The shared-premise-defs design is the
  stopping point.

## InferW port: settled design + phase plan (LIVE STATUS — executing agents update this)

InferW is OUT of the lakefile until ported. It imports only `FHM.Core` (fresh olean).
State lemmas against the packaged Core shapes (RecSpecs.WF/MonoTyped/PolyTyped,
rhsCtx/bodyCtx, Option.Pins, GeneralisesTo, Ty.AreLC, PolyTy.InstantiatesTo,
BranchCtorSpec; Core's `TypeOfElabHM.faithful` is the destructuring model).

### Settled design decisions

- **Fused `Infer.letRec`** (replaces `Infer.letRec` + `Infer.letRecAnn`): build
  `initSpecs : List RecSpec` positionally from `anns`: member `j` unannotated ↦
  `.mono (Ty.fvar (Φ+j))` (allocate a fresh var for EVERY member; annotated members
  simply don't use theirs — harmless, keeps indexing trivial); `some σ` ↦ `.poly σ`
  (after a decidable `σ.WF` check, as before). Group RHS env :=
  `initSpecs.map (RecSpec.rhsEntry [] [])` ++ ctx.env (note
  `RecSpec.rhsEntry [] [] = mono ↦ mkTrivial, poly ↦ id` definitionally, since
  `Ty.renameG [] _ = id`). Thread the fused `InferRecGroup` (below); afterwards
  `solvedSpecs := initSpecs.map (RecSpec.onSubst S₁)`, pool
  `G := genGroupVars (bindings.flatMap Expr.tyFreeVars) (S₁.onCtx ctx).env
  (monoTys solvedSpecs)` (define `RecSpec.monoTy? : RecSpec → Option Ty` and
  `monoTys := filterMap monoTy?` — poly members contribute NOTHING to the pool),
  body env := `solvedSpecs.map (RecSpec.bodyScheme G) ++ (S₁.onCtx ctx).env`
  (reuses Core's bodyScheme: genGroup for mono, σ for poly).
- **`RecSpec.onSubst (S : Subst) : RecSpec → RecSpec`** := mono τ ↦ mono (S.onTy τ);
  poly σ ↦ poly σ (schemes thread RIGID, exactly like old `InferRecGroupAnn`).
- **Fused threading `InferRecGroup : Nat → Ctx → List Expr → List RecSpec → Nat →
  Subst → List Expr → Prop`**: `nil`, plus TWO cons shapes:
  - `consMono` (old `InferRecGroup.cons`): infer the binding as stored, unify its type
    against `S₁.onTy β`, recurse with ctx and REMAINING SPECS threaded through
    `RecSpec.onSubst` of the accumulated substitution; output raw eOut.
  - `consPoly` (old `InferRecGroupAnn.cons`): `Φ ≤ N`, skolems
    `Ys = freshVars N σ.paramCount`, infer `e.openTyVars Ys`, unify against
    `σ.openVars Ys` (→ `Schk`), escape checks (`Ys ∉ (S₁++Schk).map Prod.fst`, `Ys ∉`
    threaded env freeVars — NOTE the env now contains the mono βs, so this check
    ALSO rejects skolem-into-pool leaks, which is exactly the declarative rejection),
    close-back `(eOut.substTyFvars (S₁++Schk)).closeTyVars Ys`, recurse with ctx AND
    remaining specs threaded through `S₁++Schk`.
- **Elaborated output — mixed Λ-nest** (rework `Expr.letRecElab`/`letRecElabNest`):
  wrap ALL n members (member 0 innermost; indices preserved), inner node is the fused
  `.letRec anns rawBindings' (.var i tyArgsᵢ)` with rawBindings' shifted past wrappers
  as today:
  - mono member i (solved τᵢ): wrapper `.letIn (some (PolyTy.genGroup G τᵢ))
    (Expr.closeTyVars (Ty.genFilter G τᵢ) (.letRec anns shifted (.var i [])))` — as
    today.
  - poly member i (σᵢ): wrapper `.letIn (some σᵢ)
    (.letRec anns shifted (.var i (Ty.bvarRange σᵢ.paramCount)))` — NO closeTyVars
    (annotated bindings are already closed back scheme-relatively by the threader;
    the projection's tyArgs are the wrapper scheme's own bvars, opened by the letIn
    rule's cofinite opener). Core-side soundness ammunition already exists:
    `TypeOfElabHM.rec_rewrap_typed`, `rewrap_hasScheme_mono`, `rewrap_hasScheme_poly`.
- **`NoRecAnn`**: attempt full RETIREMENT (the general freshness-keyed kernel
  `openTyVars_closeTyVars_rename_of_fresh` and the `RecGroupAnn.not_mem_*` general
  lemmas cover the letRecAnn cases); only if something resists, port it as
  `Expr.RecAnnsNone` ("every letRec node's anns all-`none`, recursively"). Do NOT let
  it block a phase.
- **Aux suites**: `RecGroupAnn.closeSchemes`/`closeTyVarsAux` →
  `RecGroup.closeAnns`/`closeTyVarsAux` over `List (Option PolyTy)`, keyed by
  `RecAnn.params`, mirroring Core's `instAnns`/`openAnns` (cons-none = depth d,
  cons-some σ = depth d + σ.paramCount; `_eq_zip` via `RecGroup.shieldDepths`).
- **Packaging fallout** applies file-wide: Core's `var` is 3 premises
  (`hlook`, `hlc : Ty.AreLC pc tyArgs` — old htyargs/hlen = `hlc.2`/`hlc.1` —,
  `hinst : InstantiatesTo`), branch `mk` is 3 (`hspec : BranchCtorSpec`, heq, hbody),
  `letIn`'s hann/hcofin are `Option.Pins`/`GeneralisesTo` (defeq-transparent).

### Phases (sequential; each ends with the file elaborating and the status updated HERE)

- [ ] **A — definitions + mechanical sweep**: fuse every definition/inductive/executable
  above (Infer, InferRecGroup, inferCore/inferRecGroupCore, letRecElab nest, close
  suites, NoRecAnn retirement attempt, eraseVarTyArgs, genGroupSchemes retirement in
  favor of bodyScheme-mapping); adapt all mechanical lemmas (lengths, frontier_le, lc,
  eq_zip, tyFreeVars/tyBvarBounded of the nest, …). `sorry`-stub the heavy families
  (sound/sourceSound/complete*/gap_avoid/block_fresh/inferCore_complete/capstones) and
  RECORD the exact stub inventory below. Exit: zero errors, stubs catalogued.
- [ ] **B — soundness**: fill `Infer.sound`, fused `InferRecGroup.sound`,
  mixed `letRecElab_sound`, `sourceSound` family, and the structural support
  (belowFvars, dom_below/dom_avoid, eOut_avoid, eliminates, eOut_tyBvarBounded, …).
- [ ] **C — completeness** (the risk pool): fused `InferRecGroup.complete`/`complete'`,
  `Infer.complete_letRec` (fused; supersedes complete_letRecAnn), `gap_avoid`,
  `block_fresh`, `inferRecGroupCore_complete`, `inferCore_complete`, then the
  capstones (`iff_typeable`, `principal`, `principalType_*`, `typecheck_*`).
- [ ] **D — cleanup + gate**: port `Examples.lean`; port `SpikeLetRecMixed`'s two
  witnesses (mixed positive + skolem-leak `#guard`/negative) into Examples; DELETE
  `FHM/SpikeLetRecMixed.lean`; restore `FHM.InferW` + `FHM.Examples` to lakefile
  roots; fresh-olean `lake build`; `#print axioms` on ALL headline theorems
  (type_safety_star, faithful, iff_typeable, principal, typecheck_*); update README
  if counts/names changed; add a status line here.

### Status log (append-only)

- 2026-07-02: design settled, phases defined. Port not started.
- 2026-07-02 (**Phase A DONE**): `FHM/InferW.lean` fully fused to the new Core and
  elaborates with **ZERO errors** (52 catalogued `sorry`s; `lean-lsp` full-file
  diagnostic clean; no `axiom`/`admit`). Continued the interrupted partial edit.

  **Fusions landed (definitions/inductives/executables — all real, non-stubbed):**
  - Small defs (near `genGroupVars`): `RecSpec.onSubst`/`monoTy?`/`RecSpecs.monoTys`/
    `RecSpec.init`(+`map_ann_init`/`init_length`/`init_getElem?`), plus
    `RecSpec.LC`/`RecSpec.BelowFvars`/`RecSpec.freeVars` (spec-level lifts used by the
    stubbed invariant/soundness/completeness statements).
  - Close/open aux suite keyed by `List (Option PolyTy)`: `RecGroup.closeAnns`/
    `closeTyVarsAux`(+`_eq_zip`/`_length`), `openClose_self`, `openAnns_closeAnns_self`,
    `openTyVarsAux_closeAnns`, `not_mem_close*`, `tyFreeVars_closeAnns_subset`/
    `_closeTyVarsAux_subset`; `Expr.closeTyVarsAux`/`annTyFreeVars` (→ `AnnList.*`);
    the `openTyVarsAux_closeTyVarsAux_self`/`not_mem_..._of_fresh`/`rename_of_fresh`
    kernel — all adapted.
  - Mixed Λ-nest: **`Expr.closeRecGroup` deleted** (unused); `Expr.letRecElabNest`/
    `letRecElab` reworked to `(G, anns, n, rawBindings) (List (Nat × RecSpec)) body`
    (mono wrapper = `letIn (some (genGroup G τ)) (closeTyVars (genFilter G τ) (.letRec
    anns shifted (.var i [])))`; poly wrapper = `letIn (some σ) (.letRec anns shifted
    (.var i (Ty.bvarRange σ.paramCount)))`, NO closeTyVars). `rawBindings :=
    bindingsOut.map (·.substTyFvars S₁)` (uniform — harmless on the already-closed poly
    members, since S₁ ⊆ S₁++Schk domain).
  - `Infer.letRec` (fused; `letRecAnn` rule GONE): WF-premise `∀ σ, some σ ∈ anns →
    σ.WF`, `InferRecGroup (Φ+n) rhsCtx bindings (RecSpec.init Φ anns) …`, body env
    `(init.map (onSubst S₁)).map (bodyScheme G) ++ …` with pool `G := genGroupVars …
    (monoTys (init.map (onSubst S₁)))`, output `letRecElab`.
  - `InferRecGroup` (fused; **`InferRecGroupAnn` GONE**): `nil`/`consMono`/`consPoly`,
    remaining specs threaded by `RecSpec.onSubst (S₁++S₂)` / `(S₁++Schk)`; consPoly
    keeps both escape checks + close-back over `Ys`.
  - Executables: `inferCore.letRec` fused (decidable per-ann `bvarsBelow` WF check,
    `RecSpec.init`, fused threader, bodyScheme-map body env, `letRecElab` output);
    `inferRecGroupCore` fused to case on the head `RecSpec` (**`inferRecGroupAnnCore`
    GONE**). Both compile (kernel-accepted derivations).
  - Mechanical lemmas ADAPTED (real proofs): `Infer/InferBranches/InferRecGroup.
    frontier_le`; `eraseVarTyArgs` (def + `_substTyFvars` + `_openTyVarsAux`, fused,
    with `RecGroup.eraseVarTyArgs_openTyVarsAux` now anns-keyed and `RecGroupAnn.*`
    deleted); `TypeOfElabHM.regular`/`TypeOfMatchBranch.regular` and `TypeOfHM.regular`/
    `TypeOfMatchBranch.regular` (packaging: `var` via `hlc.2`/`Ty.AreLC`, `mk` via
    `BranchCtorSpec`, fused `letRec`); `dom_notMem_substTyFvars` (fused, anns-part
    via `RecAnn.substFvars_none/some`); `mem_tyFreeVars_substTyFvars` +
    `AnnList.mem_tyFreeVars_substFvars`; `InferRecGroup.bindingsOut_length`/`length_eq`;
    `Expr.shiftFrom_tyFreeVars`; `Expr.tyFreeVars_closeTyVarsAux_subset`.

  **NoRecAnn outcome: FULLY RETIRED.** `Expr.NoRecAnn` and its entire preservation
  family (`closeTyVarsAux`/`closeTyVars`/`letRecElab(Nest)_noRecAnn`/
  `substTyFvar(s)_noRecAnn`/`substTyFvar_tyBvarBounded`/`shiftFrom`/`BranchList_iff`/
  `RecGroup_iff`/`not_mem_closeTyVarsAux_tyFreeVars`/`openTyVars_closeTyVars_rename`)
  are deleted; no consumer resisted (the general `..._rename_of_fresh` kernel covers
  the ex-`letRecAnn` case). Only comments mention `NoRecAnn` now.

  **Deletions (old `letRecAnn`-era support with no fused counterpart):**
  `Expr.closeRecGroup`; `RecGroupAnn.substTyFvars_tyBvarBounded`,
  `RecGroupAnn.closeSchemes_tyBvarBounded`, `Expr.TyBvarBounded.RecGroupAnn_closeSchemes`,
  `RecGroupAnn.closeTyVarsAux_tyBvarBounded`, `RecGroupAnn.substFvars_closeSchemes`,
  `RecGroupAnn.substTyFvars_closeTyVarsAux`, `RecGroupAnn.eraseVarTyArgs_openTyVarsAux`,
  `Expr.mem_tyFreeVars_schemeList`, `InferRecGroupAnn.*` (frontier_le/lc/belowFvars/
  dom_below/eOut_avoid/eliminates/eOut_tyBvarBounded/dom_avoid/sound/sourceSound/
  gap_avoid/complete/complete'/bindingsOut_length/length_eq/block_fresh),
  `inferRecGroupAnnCore`, `inferRecGroupAnnCore_complete`, `Infer.rec_strong` (the
  4-motive eliminator — unused once `sourceSound`/`complete` are stubbed; its
  `TypeOfHM.rec_strong` sibling is kept but stubbed), the standalone
  `complete_letRecAnn`/`inferCore_complete_letRecAnn` (folded into the fused
  `complete_letRec`/`inferCore_complete_letRec`). `genGroupSchemes` was **kept**
  (still referenced by a compiling completeness-support lemma; its retirement in
  favour of `bodyScheme`-mapping is deferred — the fused `Infer.letRec` already uses
  `bodyScheme`-mapping).

  **STUB INVENTORY (52 `sorry`s; all catalogued; statements honest/fused, never
  weakened as headlines).**
  Phase B (soundness + structural support):
  - `Expr.substTyFvars_tyBvarBounded`, `Expr.closeTyVarsAux_tyBvarBounded`,
    `Expr.shiftFrom_tyBvarBounded`, `Expr.substTyFvars_closeTyVarsAux`,
    `Expr.substTyFvars_shiftFrom` (fused `letRec` arm only; other arms real).
  - `Expr.letRecElabNest_tyBvarBounded`, `Expr.letRecElab_tyBvarBounded`,
    `Expr.mem_tyFreeVars_letRecElabNest`, `Expr.mem_tyFreeVars_letRecElab`,
    `Expr.substTyFvars_letRecElabNest`, `Expr.substTyFvars_letRecElab` (restated for
    the mixed nest; FLAGGED: poly-member scheme transform under `S`, and the anns
    disjunct in the nest free-var lemma).
  - `Infer.lc`/`belowFvars`/`dom_below`/`eOut_avoid`/`eliminates`/`eOut_tyBvarBounded`/
    `dom_avoid`/`sound` (fused `letRec` arm stub; other arms retained where they
    compiled) and their `InferRecGroup.*` (spec-keyed) siblings; `InferBranches.sound`;
    `Expr.letRecElab_sound` (FLAGGED packaging), `Infer.sourceSound`/
    `InferBranches.sourceSound`/`InferRecGroup.sourceSound` (FLAGGED mono/poly split).
  Phase C (completeness + capstones):
  - `TypeOfHM.rec_strong` (fused-`letRec` motive-arg; IH-through-`Mono/PolyTyped` TBD),
    `TypeOfHM.typ_subst_preservation_uniform`, `TypeOfHM.weaken_scheme`.
  - `InferBranches.complete`, `InferRecGroup.complete` (FLAGGED), `Infer.complete'`/
    `InferBranches.complete'`/`InferRecGroup.complete'` (FLAGGED), `Infer.complete_letIn`
    (GeneralisesTo packaging), `Infer.complete_letRec` (FLAGGED; fused mono+opened IHs),
    `Infer.completeAt`, `Infer.gap_avoid`/`InferBranches.gap_avoid`/
    `InferRecGroup.gap_avoid`.
  - `inferCore_complete_letIn`, `inferBranchesCore_complete`, `inferRecGroupCore_complete`
    (FLAGGED), `inferCore_complete_letRec` (FLAGGED), `inferCore_complete`.
  Phase D (witness port): `AuditCapstone.mutualRec_typeable` (all-`none` group under the
  fused `TypeOfHM.letRec`; verbose but routine — deferred with the `SpikeLetRecMixed`
  witnesses to the Examples port). `mutualRec` def updated to `[none, none]` anns.

  **Flagged guessed statements** (correct fused form uncertain, best-reading stubbed):
  `Expr.letRecElab_sound`, `substTyFvars_letRecElab(Nest)`, `mem_tyFreeVars_letRecElabNest`
  (anns disjunct), `InferRecGroup.sound`/`sourceSound`/`complete`/`complete'` (mono-half
  + poly-half packaging + `L`/pool choice), `InferRecGroup.dom_avoid`/`eOut_avoid`/
  `eliminates`/`belowFvars`/`dom_below`/`lc`/`gap_avoid` (spec `LC`/`BelowFvars`/`freeVars`
  hypotheses are my choice), `Infer.complete_letRec`/`inferCore_complete_letRec`/
  `inferRecGroupCore_complete` (separate mono-raw vs poly-opened `CompleteAt` hyps).
  Executable-relation result types match the fused relation (kernel-accepted).

- 2026-07-02 (**Phase B DONE**): every Phase-B stub filled; `FHM/InferW.lean`
  (16,516 lines) elaborates with **ZERO errors** (`lean-lsp` full-file diagnostic
  clean); 18 `sorry`s remain, all in the catalogued Phase-C list + the one Phase-D
  witness. No new `axiom`/`admit`; other files untouched.

  **Filled (structural):** `Expr.substTyFvars_tyBvarBounded`,
  `closeTyVarsAux_tyBvarBounded`, `shiftFrom_tyBvarBounded`,
  `substTyFvars_closeTyVarsAux`, `substTyFvars_shiftFrom` (fused `letRec` arms);
  `Expr.mem_tyFreeVars_letRecElab(Nest)`; `Expr.letRecElab(Nest)_tyBvarBounded`;
  `Expr.substTyFvars_letRecElab(Nest)`. New supporting lemmas:
  `RecGroup.closeAnns_tyBvarBounded`, `RecGroup.substFvars_closeAnns`,
  `Expr.TyBvarBounded.RecGroup_map_shiftFrom`/`_map_substTyFvars`/`.monotone`,
  `ContainsBvarsUpTo.bvarRange`, `RecSpec` transport block (`mem_init`,
  `poly_mem_init/_map_onSubst`, `LC/BelowFvars.onSubst`, `onSubst_append`,
  `rhsEntry_nil_*`, `bodyScheme_*`, `map_ann_onSubst`, `renameG_nil_pool`),
  `Ty/RecSpec.freeVars_onSubst_mem_onEnv`, `List.zip_map_left/right_eq'`.

  **Filled (invariants):** fused `letRec` arms + in-mutual fused `InferRecGroup.*`
  for `lc`/`belowFvars`/`dom_below`/`eOut_avoid`/`eliminates`/`eOut_tyBvarBounded`/
  `dom_avoid`.

  **Filled (soundness):** `Expr.letRecElab_sound` (via new `innerFusedLetRec_sound`
  — the empty-pool re-derivation of the fused rule — plus a fused
  `letRecElabNest_sound` handling both wrapper shapes; poly wrappers via
  `letRec_proj_openTyVars` + `InstantiatesBy.openVars`); the full
  `Infer.sound`/`InferBranches.sound`/`InferRecGroup.sound` mutual (non-`letRec`
  arms restored from git with `var`/branch-`mk` packaging fixes; fused `letRec` arm
  and fused two-halves group theorem new); `TypeOfHM.rec_strong` (via
  `TypeOfHM.rec`, motive extended with the fused rule's mono/poly IHs);
  `TypeOfHM.typ_subst_preservation_uniform` (port of Core's fused proof); the full
  `Infer.sourceSound`/`InferBranches.sourceSound`/`InferRecGroup.sourceSound`
  mutual (converted from the retired `Infer.rec_strong` style to a `cases` mutual;
  fused source `letRec` arm re-derives `TypeOfHM.letRec` with the pool renaming
  `G ↦ Xs` pushed through the solved-form group typings).

  **Soundness-forced statement adjustments (all ≥ the old `letRec`+`letRecAnn`
  strength; PROMINENT):**
  1. **Pool rigid set widened (design-relevant, rule + executable changed):**
     `Infer.letRec`/`inferCore` now pass `RecGroup.rigidVars anns bindings`
     (= ann scheme-body vars ++ binding ann vars) to `genGroupVars`, not just
     `bindings.flatMap Expr.tyFreeVars` — without it a stored scheme's scoped
     var could be generalised into the pool (soundness bug in the Phase-A guess).
  2. `InferRecGroup.sound`/`sourceSound`: both halves stated over `substTyFvars S`
     outputs (sound) / source bindings (sourceSound); two premises added —
     `hspecs_env` (spec free vars live in the threaded env; ties mono monotypes to
     the context so the poly skolem-escape check also covers sibling monotypes)
     and `hKsch` (stored scheme bodies are `K`-rigid). Both are discharged
     trivially at the `letRec` call site (rhs entries ARE env members; ann bodies
     are scoped vars). Jointly not weaker than the old split pair.
  3. `Expr.substTyFvars_letRecElab(Nest)`: added premise that `S` fixes the stored
     poly-scheme bodies (schemes are RIGID under `RecSpec.onSubst`); supplied from
     `K`-rigidity at the call site.
  4. `Expr.letRecElab_sound`: hypotheses in solved/identity form over the
     elaborated bindings (`specs.map (rhsEntry [] [])` env, skolems fresh for a
     caller-chosen `Lp`) rather than Core's pool-opened `RecSpecs.Mono/PolyTyped`;
     the pool-`G` premise re-emerges inside via the empty-pool inner rule. New
     premise `hG_specs` (pool avoids stored scheme bodies) — supplied by
     `RecGroup.rigidVars` (adjustment 1).
  5. `Expr.letRecElabNest_tyBvarBounded`: raw-bindings hypothesis strengthened from
     per-binding `TyBvarBounded 0` to the shielded `TyBvarBounded.RecGroup 0 anns`
     zip form (poly members are closed back over their own arity), matching
     `InferRecGroup.eOut_tyBvarBounded`'s new zip-form conclusion.
  6. `TypeOfHM.rec_strong`: `letRec` minor premise extended with the mono/poly
     cofinite IHs (mirroring Core's `TypeOfElabHM.rec_strong`) — needed by
     `typ_subst_preservation_uniform`; strictly more information for users.

  **Line-count note (requested):** Phase A shrank `InferW` 20.3k → 12.6k almost
  entirely by REPLACING the heavy proof families' bodies with catalogued stubs
  (the ~52 `sorry`s) plus the genuine deletions listed in the Phase-A entry
  (`NoRecAnn` family, `InferRecGroupAnn.*`, `SchemeList` suite, `closeRecGroup`,
  `Infer.rec_strong`, `inferRecGroupAnnCore`). Phase B re-added the fused proof
  bodies, growing the file back to 16.5k; the remaining ~3.8k gap vs the old file
  is (a) the still-stubbed Phase-C completeness bodies and (b) the intended
  consolidation above. Nothing substantial was removed beyond the Phase-A
  deletion list.

## Working discipline (non-negotiable, learned the hard way)
- The headline theorems must stay `sorry`/`admit`/`axiom`-free and **axiom-clean**
  (`propext`/`Classical.choice`/`Quot.sound`). Gate every increment with a full
  `lake build` against fresh oleans **and** `#print axioms` on the headline theorems —
  never trust "it compiles" from the LSP alone after a `Core` edit (stale-olean trap).
- Don't weaken headline theorem *statements*; add hypotheses to internal helpers instead
  and discharge them at the top from closedness/`CtxBelow`.
- Prefer the lean-lsp MCP for the tight edit loop; use `lake build` for ground-truth gates
  and anything downstream of a `Core` change.
- Delegating bulk proof-plumbing to subagents (with precise per-error specs + the
  lean-lsp MCP) worked very well this session; keep the design decisions and the
  build/axiom review gate in the parent.

## Suggested first task (step 1, concrete)
Add integer arithmetic primops end-to-end:
- `PrimOp` enum with `intAdd` (+ optionally `intSub`, `intMul`); a total `PrimOp → Ty`.
- `Expr.primOp : PrimOp → Expr`; thread the trivial new case through the structural
  functions/lemmas.
- Typing rule (fixed type) in `TypeOfElabHM` and `TypeOfHM`; inference case in `Infer` /
  `inferCore` (like a monomorphic `ctor`).
- δ-rules in `SmallStep.Step`; extend progress (partial-application-is-a-value +
  int canonical forms) and preservation.
- A witness `#eval` in `Examples.lean` (e.g. `(λx. intAdd x 1) 41 ⟹ 42`), and confirm the
  headline theorems remain axiom-clean.
