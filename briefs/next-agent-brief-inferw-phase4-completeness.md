<!-- Handoff: after Phase 3 (the elaboration relation + honest soundness) landed.
     Successor to next-agent-brief-inferw-typepassing.md (whose two 2026-06-26
     addenda are SUPERSEDED — see "Corrections to the prior brief" below).
     Written 2026-06-30 at commit 2531f5b. -->

# Brief: `InferW` — Phase 4 (`letRecAnn` inference) + Phase 5 (completeness), and beyond

## State of play (READ FIRST)

`FHM/Core.lean` is the **type-passing** declarative core with literal type safety
(committed + reviewed; axiom-clean). `FHM/InferW.lean` is being rebuilt into a
verified **Algorithm-W elaborator** for it. **Phase 3 is done:** the `Infer`
relation is now a type-directed *elaboration* relation, and honest **soundness is
machine-checked with zero `sorry`** (verified via `lake env lean FHM/InferW.lean`:
the soundness region — everything up to ~line 7575 — has no errors and no `sorry`;
all remaining red/`sorry` is the out-of-scope completeness/driver section from
~7576 onward). Current HEAD: `2531f5b`. `InferW` is still **excluded from the
lakefile build** (it won't fully compile until completeness lands).

### The architecture (three relations + one algorithm)

- **`TypeOfElabHM`** (Core): the type-passing declarative typing relation over
  *elaborated* terms (vars carry `tyArgs`; `var` checks `tyArgs.length =
  paramCount` + `InstantiatesBy`). The dynamics + progress/preservation/type_safety
  are about this. This is what **soundness** targets.
- **`TypeOfHM`** (Core, added Phase 2): **decoration-blind** classic Damas–Milner —
  the algorithm-independent HM spec. Differs from `TypeOfElabHM` in exactly the
  `var` rule (instantiates by an *existential* witness, ignores stored `tyArgs`,
  no length premise). This is what **completeness** is stated against.
- **`Infer Φ ctx eIn Φ' S eOut τ`** (InferW): the elaboration relation — skeleton
  `eIn` in, elaborated `eOut` out. The "runnable" term is `eOut.substTyFvars S`.
- **`inferCore`** (InferW): the executable; returns `(Φ', S, eOut, τ)` + the `Infer`
  derivation (so it is sound w.r.t. `Infer` by construction).

### The correctness triangle

- **Soundness** — DONE (Phase 3): `Infer … eOut τ → TypeOfElabHM (S.onCtx ctx)
  (eOut.substTyFvars S) τ`. Theorem `Infer.sound` (+ `InferBranches.sound`,
  `InferRecGroup.sound`, `Infer.sound_closed`, helpers `Infer.sound_letIn`,
  `Infer.sound_letInAnn`). Proved by induction on `Infer`, one arm per constructor.
- **Faithfulness** — DONE (Phase 2): `TypeOfElabHM.faithful : TypeOfElabHM e τ →
  TypeOfHM e τ` (the elaborated relation is the stricter one; elaboration doesn't
  invent typeability).
- **Completeness / principality** — Phase 5 (remaining): `TypeOfHM ctx e τ →`
  inference succeeds with a *principal* type (every `TypeOfHM` typing factors
  through it). Stated against the **declarative `TypeOfHM`**, NOT `TypeOfElabHM`.

Compose them: a source program is HM-typeable iff inference succeeds, and when it
does it yields a well-typed type-passing elaboration at the principal type.

## Phase 4 — `letRecAnn` inference (decidable check-and-elaborate)

The **typing rules** for annotated polymorphic (and mutual) recursion already
exist: `TypeOfElabHM.letRecAnn` (committed, reviewed) and `TypeOfHM.letRecAnn`
(declarative, Phase 2). What's missing is the **inference/elaboration side** —
Phase 3 deliberately stubbed it (`Infer` has no `letRecAnn` constructor; `inferCore`
returns `none` for `.letRecAnn`).

To add:
1. **`Infer.letRecAnn`** rule (with an `InferRecGroupAnn` threader — the annotated
   analogue of `InferRecGroup`). Because the schemes are **given** (annotations),
   this is **check-and-elaborate**, not infer-the-recursion-types — hence
   **decidable** (Henglein; unannotated poly-recursion would be undecidable).
   Mirror the `letInAnn` machinery (which Phase 3 built + proved sound): skolemise
   each declared scheme, infer/check each binding **opened at its skolems**
   (`p.openTyVars Ys`) against the scheme's opening, escape-check to keep the
   skolems rigid, and emit each elaborated binding **closed back** scheme-relatively.
2. **`inferCore`'s `letRecAnn` branch** (replace the `none` stub): build + return
   the elaborated group.
3. **The `letRecAnn` arm of `Infer.sound`** (the existing soundness mutual gains a
   case because the relation grew a constructor): `Infer.letRecAnn … →
   TypeOfElabHM.letRecAnn …`. Reuse `sound_letInAnn`'s close-back pattern.

⚠️ **Close-AFTER-substitution ordering** (this bug bit us twice in Phase 3 — see
Lessons). The `letRecAnn` `eOut` must close each binding over its scheme vars
*after* applying the binding/check MGU, not on the raw `eOut`
(`(rhsOut.substTyFvars (S₁ ++ Schk)).closeTyVars Ys`, as `letInAnn` now does), or a
`var`/`ctor`-rhs whose fresh tyArg unifies to a skolem leaves that skolem free and
soundness becomes false.

Phase 4 is a prerequisite for Phase 5 covering `letRecAnn` (completeness's `cases e`
needs a `letRecAnn` case, which needs the inference rule).

## Phase 5 — completeness / principality (the heavy lift)

Re-prove **principality of inference against the declarative `TypeOfHM`**: if
`TypeOfHM ctx e τ` then `inferCore` succeeds and the inferred type is principal.
Two layers (both currently red, from ~line 7576 on — ~95 errors + a handful of
`sorry`'d declarations):

- **Relation level** — `Infer.CompleteAt` / `Infer.complete'` / `Infer.complete`
  (+ the per-form `complete_*` case lemmas, `complete_lambda`, `complete_app`,
  `complete_letIn`, `complete_match`, `complete_letRec`, and a NEW `complete_letRecAnn`).
  Re-point these onto the **declarative `TypeOfHM`** (the old ones were against the
  pre-migration relation = essentially today's `TypeOfHM`).
- **Executable level** — `InferCoreComplete` / `inferCore_complete*` /
  `infer_complete`: the algorithm realises the relation-level guarantee.
- **Support invariants still on the old 6-ary `Infer`** (red, must be migrated to
  the 7-ary `Infer … eOut …`): `Infer.gap_avoid`, `Infer.letInAnn_block_fresh`.
- **Drivers** (red, fix last): `infer` (now returns a 4-tuple incl. `eOut`),
  `principalType`, `typecheck`, and the capstone `#eval`/example theorems.

This is the grindiest part (the prior completeness work — `greatest_K`, the
skolem-escape kernel, annotated-let completeness — is the template). Budget for
hard *proof engineering*, not fundamental walls. Reuse: `genScheme_generalizes`,
the locality lemmas, and the close-back kernel.

## Phase 6 — finalize

- Re-add `FHM.InferW` (+ `FHM.Examples`, `FHM.SpikeLetRecAnn`) to the lakefile
  `roots`; delete any remaining dead code.
- Refresh `README.md` (still describes the old type-erasure architecture).
- **Axiom audit**: `#print axioms Infer.sound` and the headline theorems —
  confirm `propext`/`Classical.choice`/`Quot.sound` only, no `sorryAx`. Independent
  `lake build` + audit against fresh oleans (the stale-olean trap is real).
- Consider relocating/removing the spike files (`SpikeC` `SpikeLetInElab`,
  `SpikeLetInElab` de-risk, etc.).

## Key machinery / landmarks (committed + green — REUSE; grep for current lines)

- **Close-back kernel** (the structural inverse of `Expr.openTyVars`):
  `Expr.closeTyVars`, `Expr.openTyVars_closeTyVars_self`/`_rename`,
  `Ty.closeOverFrom`/`openVarsFrom_closeOverFrom_rename`, `Expr.NoRecAnn`.
- **`Infer.eliminates`** (+ `InferBranches`/`InferRecGroup` siblings): composed
  substitution **idempotency** (`∀ p∈S, ∀ x, p.1 ∉ (S.onTy x).freeVars`, plus the
  result-reduced `p.1 ∉ τ.freeVars`). The keystone for the prefix-fix and the
  close-after-`S` ordering.
- **`Infer.eOut_substTyFvars_eq`** (prefix-fix): an earlier idempotent prefix `R`
  (dom `< Φ`, avoiding `K`) fixes a later `eOut` (`eOut.substTyFvars R = eOut`).
- **Locality**: `Infer.dom_below` (`∀ p∈S, p.1 < Φ'`), `Infer.eOut_avoid`,
  `Infer.dom_avoid`, `Infer.belowFvars`.
- **`letRecElab_sound`** (+ `innerMonoLetRec_sound`, `letRecElabNest_sound`): the
  **Λ-outside `letRec`** typing — a generalising `letRec` elaborates to a
  monomorphic inner `letRec` wrapped in annotated `letIn`(s) (NOT `letRecAnn`).
  See `Expr.letRecElab`/`letRecElabNest`.
- **`Infer.sound_letIn` / `Infer.sound_letInAnn`**: the let-soundness helpers
  (close/open rename); the templates for the `letRecAnn` soundness arm.
- **`substTyFvars`/`closeTyVars`/`openTyVars` commutation + preservation** helpers,
  `Expr.substTyFvars_append`, `Expr.substTyFvars_shiftFrom`, `Ty.genFilter_onTy`.
- **Generalisation**: `genScheme` / `genGroup` / `genVars` / `genFilter` /
  `Ty.renameG` (Core). `genScheme rhs.tyFreeVars …` uses the **skeleton** rhs's
  free vars (= annotation vars only) as the rigid set — this is why full
  let-polymorphism is sound.

## Corrections to the prior brief (`...-typepassing.md`)

Its two 2026-06-26 addenda are **wrong / superseded**:
- Addendum 1's "no second index, elaboration = `e.substTyFvars S`" is insufficient
  — generalising `let`/`letRec` change the term *shape* (annotate + close), so the
  relation carries an explicit output `Expr` (`eOut`), and the subject is the
  skeleton.
- Addendum 2's "keep generalised bindings monomorphic (post-`S₁` rigid set)" is
  unsound-as-HM (forfeits let-polymorphism). The correct design: elaborate
  unannotated generalising `let` → **annotated + closed** core `let` (the Λ via the
  existing annotated-`let` mechanism), and `letRec` → the **Λ-outside** encoding.

## Hard-won lessons / gotchas (DON'T relearn these the hard way)

1. **Close AFTER applying the binder's substitution, never on the raw `eOut`.** The
   gen-vars live in the *resolved* types but the raw `eOut` still holds *fresh holes*;
   `closeTyVars` on the raw term misses them and `S` reintroduces them free. Soundness
   becomes false. This bit `letIn` and `letInAnn`; apply the same care to
   `letRecAnn`. Soundness of the fix rests on `Infer.eliminates` (idempotency).
2. **`sorry` is fine as INTERMEDIATE scaffolding.** Write the full mutual, prove the
   ready cases, `sorry` the rest so it compiles, commit WIP, fill incrementally.
   Do NOT all-or-nothing-revert a partial mutual (that makes progress evaporate).
   The FINAL headline theorems must have ZERO `sorry`/`admit`/`axiom` (a soundness
   theorem proved by `sorry` is worthless) — verify with `lake env lean`.
3. **Reading `lean_diagnostic_messages`**: `success` is a WHOLE-FILE flag (false if
   the file has any error anywhere) — IGNORE it. Trust `items` PER-RANGE: empty
   `items` for a queried range = that range is clean. Re-grep line numbers after
   every edit (they shift a lot). Only distrust when `timed_out: true`.
4. **`InferW` is out of the build**: verify per-declaration via the lean-lsp MCP
   (it must be open in the IDE for the LSP to load it), or `lake env lean
   FHM/InferW.lean` (~40s) for definitive ground truth. After editing `Core.lean`,
   rebuild + restart the LSP (`lean_build`) or InferW shows stale errors.
5. **STOP and report if a proof seems to need a `Core` statement change** — Phase 3
   needed none, and the genuine soundness bugs we found were all InferW-side. (This
   discipline is how the `letInAnn` and `letIn` close-ordering bugs were caught.)

## Commit trail (Phase 3, most recent first)

`2531f5b` letRec arm complete · `a4df172` letInAnn arm · `45bb1a1` letInAnn
close-after-`S₁++Schk` fix · `01197a8`–`a3a3b2b` soundness mutual (incremental) ·
`bc18678`/`3775868`/`61d4ec9` letRecElab_sound + commutation + dom_avoid infra ·
`54a0a87`/`8769b11` idempotency + prefix-fix · `4c83996` 3a/3b/3d structural ·
`d5aaac4` declarative `TypeOfHM` · `c36699a` faithfulness · `ce01736` rename
`TypeOfHM → TypeOfElabHM`.
