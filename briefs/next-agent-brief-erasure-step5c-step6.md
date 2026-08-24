# Erasure-on-Step migration — handover: finish step 5(c) + step 6

**Status (2026-08-24): steps 1–4 DONE; step 5(a) + 5(b) DONE; step 5(c) NOT STARTED;
step 6 NOT STARTED. `lake build` green (830 jobs).**

This supersedes `next-agent-brief-erasure-step4.md` (that brief had steps 1–3 done
and step 4 next). The numbering below is the **migration** steps (1–6) from
`design-memo-erasure-migration.md` §5.3. Read that memo §0–§5 first.

## 0. Where we are (the migration steps)

1. (done) DM cut — `RecSpec.init` all-`.mono`, `Infer.letRec` ceiling premise.
2. (done) `Expr.erase` + `erase_openTyVarsAux` etc.
3. (done) `Infer.sound` / `InferBranches.sound` / `InferRecGroup.sound` (vs `TypeOfHM`).
4. (done, this session) The `TypeOfHM`/`Step` dynamics metatheory, in `InferW.lean`:
   `HasSchemeHM`, `TypeOfHM.subst_lemma_many`/`subst_lemma`, `rec_rewrap_typed`,
   `rewrap_hasSchemeHM_mono`, `canonical_*`, `ctor_chain_inversion`, `progress`,
   `preservation`, `preservation_star`, `type_safety`, `type_safety_star`,
   `Step.preserves_erased`, `AllMatchesExhaustive.erase`/`eraseCtorBounds`,
   `InstantiatesBy.eq_of_closed`, `HasSchemeHM.ofTypeOfHM`, `InstantiatesBy.build_match_vs`,
   `GeneralisesTo_inst(_ann)`, `Instantiates`, `Ty.substFvars_zip_openVars_eq`,
   `TypeOfHM.varsBelow`/`closed`, `Expr.openTyVarsAux_eq_self_of_erase_image`, `Expr.erase_idem`.
   All stated for **erased terms** (`h_erased : e.erase = e`), all axiom-clean
   (`propext`/`Classical.choice`/`Quot.sound` only).
5. (a done) Rewired the surface to `lower → Infer → erase → Step`:
   `Headlines.WellTyped`/`Safe`/`Running`/`runSafe`/`elaborateSafe`;
   `SurfaceBridge.surface_type_safe`/`program_type_safe`/`surface_type_safe_of_SurfaceWT`
   (glued by `Infer.sound` at `K = []`); `EvaluateUnsafe.evaluateUnsafeTyped`;
   `PatComp` adequacy re-pointed to `TypeOfHM`; deleted `SpikeC`/`SpikeLetRecPromote`/
   `PatCompDemo`; re-plumbed `Examples.evalProgram` + `Live.checkPipeline`.
   (b done) Dropped `eOut` from `Infer`/`InferBranches`/`InferRecGroup` and
   `inferCore`/`inferRecGroupCore`/`infer`/`principalType`/`typecheck`; deleted the
   elaborator (`elaborate`/`elaborateProgram`) + the `eOut`-exhaustiveness transport.
   (c) **NOT STARTED** — delete `TypeOfElabHM` + its metatheory + the now-`sorry`'d
   doomed lemmas. This brief covers (c) + step 6.

## 1. Step 5(c) — delete `TypeOfElabHM` + metatheory + doomed lemmas

The relation `TypeOfElabHM` is now used ONLY by its own metatheory and the doomed
lemmas (nothing live references it). Delete it. **Search by name, not line** —
line numbers shifted after the `eOut` drop deleted ~7.5k lines from `InferW`.

### 1a. `FHM/Core.lean` — the big one

Delete (all in/around the `TypeOfElabHM` metatheory region, ~lines 3300–10900):

- `inductive TypeOfElabHM` + `inductive TypeOfElabMatchBranch`.
- `faithful` (the `TypeOfElabHM`→`TypeOfHM` bridge) and any `TypeOfHM.toElab` helper.
- `HasScheme` / `HasSchemeVars` (type-passing "value types at scheme" predicates —
  the NEW dynamics uses `HasSchemeHM` instead).
- The `TypeOfElabHM.*` metatheory: `subst_lemma_many`, `subst_lemma`, `canonical_arrow`/
  `customTy`/`int`/`char`, `ctor_chain_has_customTy_form`, `ctor_chain_inversion`,
  `progress`, `preservation`, `preservation_star`, `type_safety`, `type_safety_star`,
  `closed`, `varsBelow`, `tyBvarBounded`, `regular` (the ElabHM one), `weaken_env`/
  `weaken_scheme(s)` (the ElabHM ones), `rec_rewrap_typed`, `rewrap_hasScheme_mono`/
  `_poly`, `substArgsGe`, `fromLetCofinite`, `ofTypeOfElabHM`, `fromHasSchemeVars`.
- `Expr.letRecElab` / `Expr.letRecElabNest` / `Expr.closeTyVars` / `Expr.closeTyVarsAux`
  and their lemmas (type-passing Λ-nest / skolem-closing — dead now).
- The residual `eraseBounds` bridge (~10117–10880): `TypeOfElabHM.residual_progress`/
  `residual_preservation`/`residual_preservation_star` and the `eraseBounds`-commutation
  lemmas that ONLY serve the decorated→eraseBounds lifting. **Careful**: `Expr.eraseBounds`
  itself and `Ty.eraseBounds`/`CtorEnv.eraseBounds`/`AllMatchesExhaustive.eraseBounds` are
  still LIVE (the `WellTyped` contract uses `CtorEnv.eraseBounds ctors`) — delete only the
  `TypeOfElabHM`-specific residual lemmas, not the `eraseBounds` defs.

**KEEP** (reusable, about `substN`/`Step`/`AllMatchesExhaustive`, NOT relation-specific):
`Expr.substN`/`subst1`, `SmallStep.Step`/`IsValue`/`IsCtorChain`/`CtorAppliedTo`/
`FirstMatchingBranch`, `AllMatchesExhaustive` + `AllMatchesExhaustive.substN`/`shiftFrom`/
`instTyAux`/`eraseBounds`, `Step.preserves_exhaustive`, `SmallStep.IsValue.substN`,
`InstantiatesBy.det_agree`, `InstantiatesBy.preserves_bvars`, `Ty.bvarRange*`,
`SmallStep.CtorAppliedTo.det`, `SmallStep.FirstMatchingBranch.mem`/`.ctor_eq`,
`BranchList.mem_substN`/`mem_substN_of_mem`, `Expr.substN_openTyVarsAux_comm`,
`exists_fresh_names`, and everything `TypeOfHM`/`Infer`/`Infer.sound` actually uses.
(When in doubt, keep it and see if the build complains about an unused-but-present
declaration — unused lemmas are harmless, missing ones break the build.)

### 1b. `FHM/InferW.lean`

Delete the now-`sorry`'d doomed lemmas (they were `sorry`'d during the `eOut` drop):
- `Infer.sourceSound` / `InferBranches.sourceSound` / `InferRecGroup.sourceSound`.
- The `Infer.complete*` completeness campaign (search `complete_`, `CompleteAt`,
  `iff_typeable`, `Infer.principal`, `inferCore_complete*`, `inferBranchesCore_complete`,
  `inferRecGroupCore_complete`) — these are `sorry`'d and reference the dropped `eOut`.
- `letRecFused_body_retype`, `letRecFused_residual_setup` (doomed, `sorry`'d).
- Any remaining `letRecElab*`/`closeTyVars`/`eOut_*`/`…Out` mirrors in `InferW`.

### 1c. `FHM/SurfaceBridge.lean`

Delete the `private` helpers that use `Expr.closeTyVarsAux`/`Expr.letRecElab` (search
`closeTyVarsAux_match_eq`, `closeTyVarsAux_letRec_eq`, `AllBranchBodiesExhaustive.closeTyVarsAux`,
`AllMatchesExhaustive.closeTyVars*`, `letRecElabNest_AllMatchesExhaustive`,
`letRecElab_AllMatchesExhaustive`) — they only served the deleted elaborator.

### 1d. `FHM/Headlines.lean`

Remove the now-dangling `#check @TypeOfElabHM.*` lines (search `#check @TypeOfElabHM`) and
the `#print axioms Infer.sourceSound` / `InferBranches.sourceSound` / `InferRecGroup.sourceSound`
lines, plus any doc-comment mentions of `TypeOfElabHM`/`sourceSound` (rewrite to the
`erase` + `TypeOfHM` + `Step` story; the module doc at the top still describes the old
Path-R residual — refresh it).

### 1e. `FHM/CekMachine.lean`

Its `TypeOfElabHM` mentions are comments only. **Leave it** (it's deleted wholesale in step 6).

### 1f. `ConstraintTypeSystem.lean`

Uses `TypeOfElabHM`, but it is **excluded from the lakefile build** (stale, kept for
reference). Leave it (or delete it in step 6 cleanup — your call).

**Green bar:** `lake build` **and** `lake build fhm` (the CLI pulls Bounds + Live).
The 7 `Bounds/*` `sorry`s (Pipeline ×6, Erase ×1) remain and still compile.

## 2. Step 6 — cleanup

After 5(c) is green:

1. Drop `var.tyArgs` from `Expr` and `TypeOfHM.var` (erased terms have `tyArgs = []`).
   This changes `Expr.var` and breaks `CekMachine.lean` (`Expr.IsErased.var`). **Delete
   `FHM/CekMachine.lean`** and remove `"FHM.CekMachine"` from the lakefile `roots`
   (its reusable lemmas already moved to Core/InferW in step 4). Also delete
   `FHM/ConstraintTypeSystem.lean` if you kept it.
2. Delete now-dead `Expr.instTy`/`instTyAux`/`shiftFrom` (type-beta helpers), and any
   dead `AllMatchesExhaustive.instTyAux`/`shiftFrom` lemmas — search for their only users.
3. Refresh docs: `README.md`, `briefs/complexity-budget.md`, `briefs/letrec-design.md`,
   and the `Headlines.lean` module doc (already partly done in 1d). Update the memo's
   §5.3 status blurb.

## 3. Key decisions & invariants (do NOT re-litigate — learned this session)

1. **`Infer.sound` / `InferBranches.sound` / `InferRecGroup.sound` MUST stay axiom-clean**
   (`[propext, Classical.choice, Quot.sound]`, no `sorryAx`). This is the whole point of
   the migration. The `eOut` drop initially broke it (a subagent `sorry`'d `Infer.eOut_avoid`
   instead of re-proving it); it was fixed by re-proving `Infer.eOut_avoid` /
   `InferBranches.eOut_avoid` / `InferRecGroup.eOut_avoid` as *locality* lemmas (a var below
   the frontier avoiding ctx+input is absent from `S`'s range and the result type). `git show
   750b7e4` has the pre-`eOut` proofs to port if ever needed. Verify with
   `#print axioms`/`lean_verify` after every step-5 change.
2. **`WellTyped` carries `eraseBounds`, `Safe` carries `e.erase = e`.** Per memo §5.1 the
   final form is `∃ τ, TypeOfHM ⟨[],ctors⟩ (erase e) τ`, but during the migration (bounds
   layer still present) the contract is:
   `WellTyped ctors e := ∃ τ, TypeOfHM ⟨[], CtorEnv.eraseBounds ctors⟩ (e.erase) τ`, and
   `Safe ctors := { e // e.erase = e ∧ WellTyped ctors e ∧ AllMatchesExhaustive ctors e }`,
   with `erase` happening in `elaborateSafe` (which returns `c.erase`). This was the
   owner-confirmed "option 1".
3. **`eOut` is fully gone from `Infer`.** `Infer : Nat → Ctx → Expr → Nat → Subst → Ty → Prop`
   (no elaborated-output index). `inferCore` returns `Option { r : Nat × Subst × Ty // … }`.
   The runnable term is always `c.erase` (the erased SOURCE), never an elaborated term.
4. **The live evaluator runs `Step` on erased terms.** `runSafe` steps `t.val` (= `c.erase`),
   `evaluateUnsafeTyped` steps `e` with `h_erased`. Everything is `erase`-on-the-source,
   never annotated terms (memo §7 load-bearing restriction).
5. **Do not re-prove or "clean up" the doomed lemmas** (`sourceSound`, `complete*`,
   `letRecElab*`, `closeTyVars`, `eOut_*`) — they are deleted in 1b. If a deletion unblocks
   a reference, the fix is the deletion (or the reference goes too), not re-proving.

## 4. Workflow (unchanged)

- Main agent: definitions + theorem statements + trivial proofs; hard proofs → `sorry`.
- Proof farming: `deepseek-flash` subagents (background), one lemma/small cluster per call,
  using the lean-lsp MCP. **Subagents must not edit outside their assigned `sorry` markers.**
- Edit `.lean` only via Read/Edit. No `admit`/`axiom`/`native_decide`/new axioms. No `sorry`
  left in anything marked done.
- Commit at green checkpoints (`lake build`). `#print axioms`/`lean_verify` is the audit.
- Subagent runs can fail with "Insufficient Balance" (DeepSeek) — an account thing, not a
  proof failure; relaunch (the file is untouched on such failures).
