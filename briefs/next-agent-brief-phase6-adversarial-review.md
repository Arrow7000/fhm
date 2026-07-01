<!-- Handoff after Phases 4 (letRecAnn inference+soundness) and 5 (completeness/
     principality re-pointed to the declarative TypeOfHM) landed, all axiom-clean.
     Successor to next-agent-brief-inferw-phase4-completeness.md.
     Written 2026-07-01. HEAD at handoff: e4de83c. -->

# Brief: adversarial review of the annotated-poly-recursion work, then Phase 6

## Your mission, in order

1. **FIRST: a full, thorough, adversarial review** of *everything* done for annotated
   polymorphic mutually-recursive `let` support. This spans (a) the type-passing
   migration (`TypeOfHM → TypeOfElabHM` rename + the type-passing `var` rule), (b) the
   split into two typing relations (`TypeOfElabHM` elaborated vs `TypeOfHM` declarative),
   (c) the `letRecAnn` inference/soundness/completeness, and (d) the Phase-5 `TypeOfHM`
   metatheory port + completeness re-point.
2. **THEN: Phase 6 cleanup** (lakefile, README, spikes, `bool`), gated on the review.

`FHM/Core.lean` (~8.8k lines) is the type-passing declarative core (committed, reviewed,
literal type safety). `FHM/InferW.lean` (~21k lines) is the verified Algorithm-W
elaborator. **`InferW` is still excluded from the lakefile build.** Verify per-declaration
via the lean-lsp MCP (file must be open in the IDE) or `lake env lean FHM/InferW.lean`
(~90–130s) for ground truth.

## State of play — what is proven (all axiom-clean: only propext/Classical.choice/Quot.sound)

Four relations: **`TypeOfElabHM`** (Core; type-passing, elaborated terms, `var` carries
`tyArgs` with `length = paramCount`), **`TypeOfHM`** (Core; decoration-blind Damas–Milner,
existential `var` witness, no length premise), **`Infer Φ ctx e Φ' S eOut τ`** (InferW;
elaboration relation, skeleton→elaborated), **`inferCore`/`typecheck`** (executable).

The bridging lemmas (**verify these are the headline theorems and that they're tight**):
- `Infer.sound` : `Infer … eOut τ → TypeOfElabHM (S.onCtx ctx) (eOut.substTyFvars S) τ` (Infer → elaborated).
- `TypeOfElabHM.faithful` : `TypeOfElabHM e τ → TypeOfHM e τ`.
- `Infer.sourceSound` : `Infer … e … τ → TypeOfHM (S.onCtx ctx) e τ` (Infer → **source** declarative).
- `Infer.iff_typeable` / `Infer.principal` / `Infer.IsPrincipal` : completeness+principality against **`TypeOfHM`**.
- Executable: `typecheck_iff`, `typecheck_principal`, `typecheck_sound`.

`letRecAnn` (annotated polymorphic **mutual** recursion) is complete across the stack:
`Infer.letRecAnn` + `InferRecGroupAnn` (+ `.sound`/`.complete`/`.complete'`/`.gap_avoid`/
`.block_fresh`/`.sourceSound`), `inferCore`/`inferRecGroupAnnCore` (+ `_complete`),
`Infer.complete_letRecAnn`. Custom eliminator `Infer.rec_strong` (mutual, `@[elab_as_elim]`)
underpins `sourceSound`.

Current state: `lake env lean FHM/InferW.lean` = **0 errors, 0 sorries**; source has no
`sorry`/`admit`/`axiom` tokens (only in docstring prose).

## PART A — the adversarial review (the priority)

Goal: confirm the headline theorems are **tight, compact, and rock-solid** — that they
prove what they purport, with no premise that makes them vacuous or pointless.

**Do NOT trust working memory over 29k lines.** Liberally use `rg`/grep/regex, the
lean-lsp MCP (`lean_diagnostic_messages`, `lean_goal`, `lean_hover_info`, `lean_verify`
for axiom+source scans), `lake env lean`, `#print axioms`, and dispatch fast "handyman"
subagents/models for mechanical scans (e.g. "list every hypothesis of every `complete_*`
lemma", "find all theorems whose conclusion is `True`/trivial", "grep every `letRecAnn`
case that's discharged by `False.elim`"). Prefer piping/grepping to re-reading.

**Specific things to attack (highest-value first):**
1. **Vacuity / trivial-premise checks.** For `CompleteAt`, `complete'`, `complete_*`,
   `sourceSound`, `IsPrincipal`, `iff_typeable`, `principal`: does any hypothesis make the
   statement trivially true or unsatisfiable? Confirm the top-level drivers instantiate the
   hypothesis bundle non-vacuously (`iff_typeable` uses `K = []`, closed `e`, `S₀ = []`).
2. **`iff_typeable`'s specialization existential.** It states "typeable under *some* LC
   specialization `S₀` of `ctx` ⟺ Infer succeeds." This is intentional (Infer may
   instantiate `ctx`'s free vars, rigid in the declarative system) and documented — but
   confirm it is the *intended* completeness and not a sneaky weakening.
3. **The newest / hardest lemmas** (least battle-tested): `InferRecGroupAnn.complete` /
   `.complete'` / `.block_fresh`, `Infer.complete_letRecAnn` (note its IH is the *opened*
   form `∀ Ys, CompleteAt (e.openTyVars Ys)` — confirm that's correct, not a weakening),
   `inferRecGroupAnnCore_complete`, `Infer.sourceSound`, `Infer.rec_strong`. Read the
   *statements*, not just the axiom lists.
4. **The two typing relations differ in exactly the `var` rule** — verify that claim by
   diffing `TypeOfElabHM` vs `TypeOfHM` constructor-by-constructor (Core). Faithfulness
   relies on it.
5. **`InferRecGroupAnn` / `Infer.letRecAnn` shape.** Confirm the group is genuinely in
   scope at the full `schemes` in every RHS + body (mutual), that the close-back is
   `closeTyVars` **after** `substTyFvars (S₁ ++ Schk)` per binding (the ordering that bit
   `letIn`/`letInAnn`), and that no escape/rigidity premise is trivially discharged.
6. **`Infer.sound` / `sourceSound` mutual recursion well-formedness** — `sound` uses
   `cases h` + self-call, `sourceSound` uses `Infer.rec_strong`; confirm both are honest
   (no `partial`, no `unsafe`, termination genuinely established).
7. **Freshness-kernel re-basing.** The `NoRecAnn` invariant was replaced by
   `Expr.recAnnSchemeFreeVars` + freshness for the close-then-open=rename kernel
   (`openTyVars_closeTyVars_rename_of_fresh`). Confirm the freshness side-conditions are
   actually discharged (not assumed) at every call site, and that `eOut_recAnnScheme_in_K`
   is real.
8. **`#print axioms` on the fresh oleans** (see Part B) for `Infer.sound`, `sourceSound`,
   `iff_typeable`, `principal`, `typecheck_iff`, `typecheck_principal`,
   `TypeOfElabHM.type_safety` — the stale-olean trap is real; the per-file `lean_verify`
   results must be reproduced against an independent build.

## PART B — Phase 6 cleanup (after the review)

- Re-add `FHM.InferW` (+ `FHM.Examples`, `FHM.SpikeLetRecAnn`) to the lakefile `roots`;
  do a full independent `lake build` against **fresh oleans**, then `#print axioms` the
  headline theorems (the definitive audit — the belt-and-suspenders the per-file checks
  approximated).
- Refresh `README.md` (still describes the old type-erasure architecture).
- Relocate/remove spike files; delete dead code.
- Finish removing the half-removed `bool` primitive (commented out across several
  relations / `inferCore` / `complete_prim`).

## A flagged limitation (decide, likely post-review) — nested `letRecAnn` schemes

A well-formed nested `letRecAnn` scheme **cannot reference an outer scoped type variable**:
`open`/`close`/`instTy` are **no-ops on `letRecAnn` scheme bodies** (the "self-contained"
comment in `Core.Expr.openTyVarsAux`), so an outer ref (a bvar past the scheme's own
binders) is forbidden by `PolyTy.WF`. **Notably, `letInAnn` does NOT have this limit** — its
`open`/`close` descend into `σ.body` at depth `d + σ.paramCount`. So the fix is to make
`letRecAnn`'s operations thread each `σⱼ.body` at `d + σⱼ.paramCount` (mirroring
`letInAnn`), plus a depth-aware `WF`. This is a **Core** change (rule #5): mechanical
depth-shifting (pattern already exists) but requires re-proving the `letRecAnn` case of the
open/close/instTy/substTyFvars/`TyBvarBounded`/`tyFreeVars` lemma family (currently trivial)
and **re-checking subject reduction** for `letRecAnn`. Moderate; do after the review.

## Hard-won lessons / gotchas (don't relearn these)

1. **`sorry` is fine as intermediate scaffolding** (compiles + WIP-commits), but the FINAL
   headline theorems must be `sorry`/`admit`/`axiom`-free — verify with `lake env lean` +
   `#print axioms`. A soundness/completeness theorem closed by `sorry` is worthless.
2. **MCP reading:** `success` is a whole-file flag — IGNORE it; trust per-range `items`
   (empty = clean). Distrust only on `timed_out: true` (wait/retry; the file is big).
   Re-grep line numbers after every edit — they shift a lot.
3. **Stale oleans:** after a `Core` edit, the LSP shows phantom downstream errors until
   `lean_build` (build + LSP restart). Never take a build/axiom claim on faith — re-audit
   against fresh oleans.
4. **`git add` only the intended file** — a broad `git add` once swept Elm build artifacts
   (`elm-letrec-test/elm-stuff/`) into a commit (now gitignored + untracked in `d6c729b`).
5. **Elaboration = type-*application* at var uses + type-*abstraction* at generalizing
   binders.** A generalizing `let`/`letRec` elaborates to an **annotated + closed** (or
   Λ-outside, for unannotated `letRec`) core term — the source and its elaboration are
   *different terms*, not the same term re-decorated. (This is why `toElab` — a
   same-skeleton `TypeOfHM → TypeOfElabHM` bridge — is **provably impossible**: a
   directly-returned ctx-polymorphic value like `let g = f in g`, `f : ∀a.a→a`, has no
   same-skeleton `TypeOfElabHM` typing.) Consequence: completeness against `TypeOfHM`
   required porting `TypeOfHM`'s own substitution/weakening/regularity metatheory
   (mirroring `TypeOfElabHM`'s; the `var` case is *simpler* — no length premise).
6. **`weaken_scheme` is friction under `TypeOfElabHM` (pinned `tyArgs`) but trivial under
   `TypeOfHM`** (existential witness adapts). Decoration-blindness makes the metatheory
   cleaner, not just "more correct."
7. **Recursive theorem, conclusion mentions the recursion subject ⇒ kernel-fragile.**
   `cases h` + self-call is kernel-rejected when the motive depends on the subject variable
   (`sourceSound` on `e`), though it works when it depends on the output (`sound` on
   `eOut`). Fix: the `@[elab_as_elim]` custom mutual eliminator `Infer.rec_strong`.
8. **`InstantiatesBy` is length-agnostic** (unused quantified vars need no witness), which
   is why `TypeOfHM.var`'s existential witness slots into the `var` completeness case.

## Commit trail & how to verify

HEAD `e4de83c`. Phase 4: `d51ba1d` (freshness kernel) → `0d080ae` (Infer.letRecAnn +
InferRecGroupAnn) → helper arms → `5c6c299` (inferCore branch) → `b69561c`/`73c8122`
(soundness arm). Phase 5: `ed01145` (mechanical) → `1e45eec`/`efa0aea` (TypeOfHM metatheory
port) → `5473a1f` (C1 re-point) → `2fa3f82` (rec_strong) → `06bae25` (sourceSound) →
`77131e9` (C3 drivers) → `e81856a` (complete_letRecAnn) → `e4de83c` (executable arm). See
`git log --oneline` for the full chain. Every checkpoint was re-verified against
`lake env lean` before building on it; the reports were consistently accurate, but this
review is the intended independent gate — read the statements yourself.
