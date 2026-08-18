# Resume state — landing the letRec promotion (Stage 1)

Handoff for resuming after an opencode restart. Companion doc: `briefs/complexity-budget.md`
(the §Status section is the authoritative plan; this file is the live "where things are" snapshot).

## Goal

Land `Expr.letRecElabOut` (all-mono promoted `.letRec` node) so `lake build FHM.InferW` and
`lake build FHM.Headlines` are clean. The promotion is the one in `complexity-budget.md` §3.4 /
correction #1: all-`none` group → promoted node; mixed group → keep `Expr.letRecElab`.

## File states (2026-08-17)

- `FHM/LetRecPromote.lean` — **DONE, axiom-clean, zero warnings.** (new, untracked, in lakefile
  roots, imports `FHM.Core` only, imported by `FHM.InferW`). Contains the transport
  (`retarget_transport`/`retarget_untransport`, `monoTyped_to_polyTyped`, `polyTyped_to_monoTyped`,
  `bodyScheme_weaken`, `retargetStored_openTyVars`) AND the Path R commutes:
  `retargetStored_eraseBounds/substTyFvars/tyFreeVars_subset/tyBvarBounded`,
  `bodyExtend_eraseBounds/substTyFvars/tyFreeVars_subset/tyBvarBounded`,
  `promoteScheme_eraseBounds/substFvars`. Do not re-derive any of these.
- `FHM/InferW.lean` — modified, uncommitted. `letRecElabOut` + `allNone` are defined and wired into
  both the `Infer.letRec` rule and `inferCore`. `Expr.UserAnnsCopied.letRec` constructor now targets
  `letRecElabOut` (this cleared the old `:11506` error). Contains 10 `sorry` lemmas (batch 3, see
  below) and 3 pre-existing errors to wire.
- `briefs/complexity-budget.md` — 4 doc fixes already applied (sourceSound-not-blocking, Part-3-is-future,
  Option B precision, §5.5 stale-after-correction-#1).

## Batch 3 — DONE (the 10 `sorry` lemmas in InferW are all proved)

The 6 promotion-stability facts and 4 `...Out` mirrors are all proved. The 3 pre-existing error
sites (`Infer.eOut_avoid`, `Infer.eOut_tyBvarBounded`, `Infer.sound` letRec case) are all wired.
`Infer.sound`'s letRec residual packing now calls `Expr.letRecElabOut_sound` (a NEW mirror of
`Expr.letRecElab_sound`, declared right after it ~line 8998). Its **mixed** branch is proved
(reduces to `Expr.letRecElab_sound`); its **all-mono** branch is the single remaining `sorry`,
with a detailed PLAN comment in the file.

## THE remaining work: the all-mono branch of `Expr.letRecElabOut_sound`

`lake build FHM.InferW` currently SUCCEEDS with exactly one `sorry` warning, at
`Expr.letRecElabOut_sound`'s all-mono branch (~line 8998). The full plan is written as a comment
in the file at that `sorry`. Summary:

- `simp [Expr.letRecElabOut, hallNone, ↓reduceIte]` → promoted `.letRec` node.
- Derive `hspecs_mono : ∀ s ∈ specs, ∃ τ, s = .mono τ` from `hallNone` + `hwf.anns_eq`.
- `refine TypeOfElabHM.letRec (specs := promoteSpecs G specs) (G := []) (L := Lp ++ G) ?hwf' ?hmono' ?hpoly' rfl ?hbody'`.
- `hwf'` (WF at empty pool): anns_eq by def, length, `[].Nodup`, mono_lc vacuous, poly_wf via
  `promoteScheme_wf` + `hwf.mono_lc`.
- `hmono'` (MonoTyped over promoteSpecs): vacuous via `promoteSpecs_all_poly`.
- `hpoly'` via `monoTyped_to_polyTyped (monos := monoTys specs) (G) (L := Lp)`:
  - `hmono` premise = **rename bridge**: empty-pool `hmono` → pool-`G` `MonoTyped` via
    `TypeOfElabHM.onSubst_fixed (S := G.zip (Xs.map Ty.fvar))`, mirroring
    `TypeOfHM.letRec_of_emptyPool` (InferW ~12600) but for `TypeOfElabHM`.
  - `hopen` premise = discharged by `retargetStored_openTyVars` + `openTyVars_closeTyVars_self`
    (bindings' = `bs.map (retargetStored (specsMono specs) G.length 0 0 (closeTyVars G ·))`).
- `hbody'` via `bodyScheme_weaken (monos := monoTys specs) (G) hwf.nodup hmonoLC hbody`.

**OPEN DESIGN QUESTION**: the rename bridge needs `p.1.substTyFvars (G.zip (Xs.map fvar)) = p.1`
(i.e. `G` avoids the bindings' free vars). `letRecElab_sound` has no such premise; if the bridge
can't be discharged without one, ADD `hG_bs : ∀ g ∈ G, ∀ e ∈ bs, g ∉ e.tyFreeVars` to
`letRecElabOut_sound` and supply it at the `Infer.sound` call site (provable from `hKe`/`genGroupVars`).

Do this proof BY HAND (deepseek-flash corrupts it), ideally first as a scratch-file spike
(`import FHM.LetRecPromote` + `FHM.InferW`), iterating on the ~4s `lake build FHM.LetRecPromote`.

Search by name (line numbers shift as proofs are added):

1. `promoteAnns_eraseBounds`
2. `promoteAnns_substFvars`
3. `specsMono_eraseBounds`
4. `specsMono_onSubst`
5. `monoTys_eraseBounds`
6. `monoTys_onSubst`
7. `Expr.mem_tyFreeVars_letRecElabOut`
8. `Expr.letRecElabOut_tyBvarBounded`
9. `Expr.eraseBounds_letRecElabOut`
10. `Expr.substTyFvars_letRecElabOut`

Each mirror is `by_cases allNone anns`: all-mono branch uses the LetRecPromote commutes (above) +
`Expr.eraseBounds_closeTyVars`/`Expr.substTyFvars_closeTyVars`/`Expr.closeTyVars_tyBvarBounded` +
`promoteScheme_wf`/`promoteAnns_all_some`; mixed branch reduces to the existing
`Expr.mem_tyFreeVars_letRecElab` / `Expr.letRecElab_tyBvarBounded` / `Expr.eraseBounds_letRecElab` /
`Expr.substTyFvars_letRecElab`.

**Resume check:** `grep -n sorry FHM/InferW.lean` (count remaining). Done state =
`lake build FHM.InferW` fails with EXACTLY 3 errors (`Infer.eOut_avoid`, `Infer.eOut_tyBvarBounded`,
`Infer.sound` letRec case — line numbers shift) and ZERO `declaration uses 'sorry'` warnings.
If the subagent was mid-edit, the file may have one half-written broken proof — fix it or re-farm
that single lemma; the rest on disk is verified.

## Remaining plan (after batch 3)

1. **Spike the all-mono sound core** in a scratch file (`import FHM.LetRecPromote`, fast ~4s loop):
   given `RecSpecs.MonoTyped` at the solved specs + body typed at `bodyScheme G` ctx, produce
   `TypeOfElabHM erasedCtx (promoted node erased) erasedTy` via `monoTyped_to_polyTyped` +
   `bodyScheme_weaken` + `TypeOfElabHM.letRec` instantiated at erased args. This validates the
   "structural collapse" (the one part `complexity-budget.md` calls untested) BEFORE integrating.
2. **Part 2 — by hand, NOT deepseek-flash** (flash has corrupted this 4× before):
   - Wire the 3 error sites: `Infer.eOut_avoid` → `Expr.mem_tyFreeVars_letRecElabOut`,
     `Infer.eOut_tyBvarBounded` → `Expr.letRecElabOut_tyBvarBounded`, `Infer.sound` →
     `Expr.eraseBounds_letRecElabOut` + `Expr.substTyFvars_letRecElabOut` + the all-mono branch.
   - `Infer.sound` letRec case: `by_cases hallNone : allNone anns`.
     - all-mono: structural `TypeOfElabHM.letRec` via `monoTyped_to_polyTyped` (discharge `hopen`
       with `retargetStored_openTyVars`) + `bodyScheme_weaken`, threaded through the erase/subst
       `…Out` lemmas. **Must rebuild a NEW** `RecSpecs.WF (promoteAnns G specs) bs' (promoteSpecs G specs) G`
       (the existing `hwfS` is for the source anns — not reusable).
     - mixed: keep `Expr.letRecElab_sound`, adapted to the goal now mentioning `letRecElabOut`.
   - Watch the erased/un-erased impedance: `Infer.sound` is stated at erased level; the transport
     lemmas are un-erased but generic over `ctx`/`bindings`/`monos`, so instantiate them at erased args.
3. **Part 3 (future, NOT part of landing):** faithfulness corollary `Decorates e e' → TypeOfElabHM ctx
   e' τ → TypeOfHM ctx e τ` replacing `Infer.sourceSound`'s structural cases (all-mono via
   `polyTyped_to_monoTyped`). Do not do this yet.

## Handles

- This conversation session: `ses_fef389c3ffeKI9QqyqTfyr1te`.
- batch 3 subagent (running at restart): `ses_feed661c9ffeDhXThU4xPIVoNK`. The internal `subagent`
  tool has no resume-by-ID; treat the ID as a label only. Resume = inspect the on-disk state above
  and re-launch a fresh subagent for whatever `sorry`s remain.

## Tooling discipline

- Edit `.lean` only via Read/Edit. Never Python/sed.
- Farm mechanical proofs to deepseek-flash via the `subagent` tool (background), WITH a hard
  verify-after-each rule (`lake build FHM.LetRecPromote` ~4s per theorem; for InferW use MCP
  diagnostics per theorem since a full build is 2min and fails on the 3 known errors).
- Do NOT run `lake build FHM.InferW` while a subagent is editing `FHM/LetRecPromote.lean` (races on
  the imported file).
- MCP tools: `lean_goal`, `lean_diagnostic_messages`, `lean_multi_attempt`; call `lean_build` (MCP)
  when the LSP stalls or reports "not known clean".
- lake builds sparingly. `lake build FHM.LetRecPromote` ~4s; `lake build FHM.InferW` ~2min.
