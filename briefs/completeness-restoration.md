# Brief: reinstating completeness + principality (post-erasure world)

**Mission:** restore the decidability/completeness headline theorems that were
deleted in step 5(c) of the erasure migration — this time against the *simple*
post-migration API (no `eOut`, no elaboratum, no `TypeOfElabHM`), so they can be
proved **sorry-free** and stay that way.

**Reference implementation:** commit **`ffc544f`** ("Restructure: move sources
into FHM/ library dir"). At that commit `FHM/InferW.lean` contained a fully
proved, effectively sorry-free completeness stack:

- `Infer.complete'` / `InferBranches.complete'` / `InferRecGroup.complete'`
  (~1,300 ln) — principality of a *given* derivation: every declarative typing
  factors through its output.
- `Infer.output_unique`, `Infer.isPrincipal`
- `Infer.complete_letIn_ann_aux`, `complete_letIn`, `complete_letRec`,
  `completeAt`, `complete`, `complete_instance`, `complete_id`
- `Infer.iff_typeable`, `Infer.principal`
- supporting infrastructure: `Ty.rename`/`swapNat`/`Subst.conj`/`swapSubst`
  (α-renaming dodges), `blockSwap`/`blockList(Back)` (skolem-block swaps),
  `exists_fresh_block`, `exists_var_residual`, `exists_app_unifier(_erase)`,
  `exists_residual_at_fresh`, `UnifyRel.greatest_lc_factors` (still present!),
  `UnifyRel.complete_aux`/`complete_K_aux` (unification completeness — deleted,
  must be rebuilt), `unifyCoreK_complete_aux/_complete` (executable-side),
  `gap_avoid` family (domain/range locality of `Infer` substitutions).

Extract per-file with e.g.
`git show ffc544f:FHM/InferW.lean` — the old proofs are the best available
templates; port them rather than re-deriving from scratch.

---

## 0. What already survives today (do NOT rebuild)

| piece | status |
|---|---|
| `unify_sound`, `unifyCoreK` executable | ✅ live |
| `Infer.sound` / `InferBranches.sound` / `InferRecGroup.sound` (erased-term coherence) | ✅ axiom-clean |
| `TypeOfHM.progress/preservation/type_safety(_star)` on erased terms | ✅ axiom-clean |
| `principalType_sound`, `typecheck_sound` | ✅ axiom-clean |
| `Infer.eliminates` (+ Branches/RecGroup), `Infer.lc`, `dom_avoid`, `frontier_le`, `CtxWF/CtxBelow` | ✅ live |
| `TypeOfHM.weaken_scheme(s)/weaken_env`, `GeneralisesTo_inst(_ann)` | ✅ live |
| `ceilingOk_sound*` (DM-cut ceiling machinery) | ✅ live |

Deleted-but-needed (rebuild list): `UnifyRel.complete_aux` /
`UnifyRelList.complete_aux` / `complete_K_aux`; `unifyCoreK_complete_aux`/
`unifyCoreK_complete`/`unify_complete`; the renaming/swap/block-swap kit;
`exists_*` unifier/residual lemmas; `gap_avoid` family;
`Infer.complete'*` + `CompleteAt` + assembled corollaries.

---

## 1. Target statements (modern API — sign these off before proving)

All over the CURRENT `Expr` (no `var.tyArgs`) and current `Infer` (no `eOut`).
`bl` types still exist (`Path R` bounds layer); `Infer` may still produce them,
so erasure-threading stays in the statements exactly as in `Infer.sound`.

```lean
-- D1. Unification completeness (rigidity-aware, matches unifyCoreK)
theorem UnifyRel.complete {a b : Ty} {U : Subst}
    (ha : a.IsLC) (hb : b.IsLC) (h : Unifies U a b)
    (hUlc : ∀ p ∈ U, p.2.IsLC) :
    ∃ S, UnifyRel a b S
-- and the rigidity-aware executable twin:
theorem unifyCoreK_complete {K : List Nat} {a b : Ty} {U : Subst}
    (ha : a.IsLC) (hb : b.IsLC) (hUlc : ∀ p ∈ U, p.2.IsLC)
    (h : Unifies U a b) (hK : ∀ k ∈ K, U.onTy (.fvar k) = .fvar k) :
    (unifyCoreK K a b).isSome

-- D2. Principality of a given inference ("complete'", the engine's spine):
--     every declarative typing factors through the inferred output UP TO ERASURE.
--     Modern form (no eOut; conclusion is eOut-free by construction):
theorem Infer.complete' {Φ ctx e Φ' S τ} (h : Infer Φ ctx e Φ' S τ)
    (hwf : CtxWF ctx) (hbelow : CtxBelow Φ ctx) {S₀ τ₀}
    (hS₀ : ∀ p ∈ S₀, p.2.IsLC) (K : List Nat)
    (hKΦ : ∀ k ∈ K, k < Φ) (hKe : ∀ y ∈ e.tyFreeVars, y ∈ K)
    (hKfix : ∀ k ∈ K, S₀.onTy (.fvar k) = .fvar k)
    (hty : TypeOfHM (S₀.onCtx ctx).eraseBounds e.erase (Ty.eraseBounds τ₀)) :
    ∃ R : Subst, (∀ p ∈ R, p.2.IsLC) ∧
      AgreesHM τ₀ (R.onTy τ) ∧ (∀ k ∈ K, R.onTy (.fvar k) = .fvar k)
-- plus InferBranches/InferRecGroup variants.

-- D3. Assembled capstones:
theorem Infer.complete_instance ... :   -- typing ⇒ inference succeeds
theorem Infer.principal ...             -- soundness + principality bundled:
                                        --   TypeOfHM .. e.erase .. τ₀ at the result
theorem infer_iff_typeable ...          -- (infer succeeds ↔ erased-typeable)

-- D4. Whole-program packaging (restore names users had):
theorem typecheck_iff / typecheck_principal / principalType_principal
```

**Design decision to make FIRST (owner sign-off):** the exact pinning relation
for D2/D3 — plain equality `τ₀ = R.onTy τ` is FALSE when `τ` carries `bl` heads
(`Subst.onTy_bl` never rewrites); the honest pin is `AgreesHM τ₀ (R.onTy τ)`
with an `hnorm : Ty.eraseBounds τ₀ = τ₀` side-condition for the equality-flavoured
corollaries, mirroring pre-deletion §"Path R residual completeness". Do not
relitigate at proof time.

---

## 2. Known obstructions (from the post-mortem of the old campaign)

1. **Decoration sensitivity:** `TypeOfHM.var` instantiates existentially, so
   derivations can carry `bl`-types even from erase-normal inputs → only
   up-to-erasure pinning is true. State `AgreesHM` versions; get equalities via
   `hnorm`.
2. **Fresh-binder obstruction** (the reason `complete_aux` alone wasn't enough):
   the residual substitution hits fresh skolems; dodge via α-renaming
   (`swapSubst`) and block-swaps (`blockList`). Port the kit wholesale from
   `ffc544f`; it is Type-level and should port nearly verbatim.
3. **Gap avoidance**: the executable `letInAnn` arm hard-codes
   `Ys = freshVars Φ pc` while the relation permits any `N ≥ Φ`. The old
   `gap_avoid` family (≈600 ln) bridges this; port + adapt (its statement
   survives unchanged — it quantifies over `Infer` derivations, which still
   exist in the same shape).
4. **letRec case**: needs the DM-cut-era fused rule. The old `letRecFused_*`
   helpers were deleted with the campaign; their modern replacements live in
   `TypeOfHM.rec_rewrap_typed` / `rewrap_hasSchemeHM_mono` (kept). Expect the
   mono-only world to be *simpler* than the old mixed `.mono/.poly` one —
   `PolyTyped` is vacuous now (no `.poly` specs are ever produced).
5. **`substN_openTyVarsAux_comm` is gone forever** (false after `tyArgs`
   drop). If some port reaches for it, the replacement fact is: substitution
   commutes with opening on values that are `varsBelow`-closed
   (`Expr.substN_of_closed` / `shiftFrom_of_closed`), which is what the erased
   world actually supplies (`e.erase` is always closed).

---

## 3. Suggested order (green checkpoints, farm-friendly)

1. **Kit port** (mechanical): renaming/swap/blockSwap infrastructure +
   `exists_fresh_block` + `Ty.substFvars_zip_fvar_eq'` dependents. Nearly
   verbatim from `ffc544f`. Checkpoint: compiles.
2. **Unification completeness**: `UnifyRel.complete_aux` induction +
   `greatest_lc_factors` wiring (factors lemma already kept) → `UnifyRel.complete`;
   then `unifyCoreK_complete_aux` → `unifyCoreK_complete` → `unify_complete`.
   Checkpoint: `unify_iff` restorable.
3. **Gap avoidance family** (port; statements unchanged).
4. **D2 spine** per-tier: `complete'_app`-style cases first (they need only 1–3),
   then `letInAnn` (needs 3), then `letRec` (needs 4 + rewrap lemmas).
   Farm ONE CASE PER SUBAGENT with the assigned-`sorry` discipline.
5. **Assembled capstones** (D3/D4) — thin, mechanical.
6. **Docs**: README proven-theorems section back to full strength; memo §5.3
   addendum.

Estimated shape: steps 1–3 ≈ 1.5–2k lines, mostly ports; step 4 is the real
campaign (historically ~1.7k ln for `complete'` alone, but mono-only `letRec`
and no-`eOut` conclusions should shrink it).

---

## 3b. Related cleanup to fold in (small, do alongside)

- **Delete the `EmptyVarTyArgs` tower properly.** It is currently vacuous
  (`var` case `True` after the `tyArgs` drop) but load-bearing for
  `TypeOfHM_tyBvarBounded_of_emptyVarTyArgs`. Replacing it requires a new
  transfer lemma:
  `TypeOfHM ctx e τ → e.TyBvarBounded 0` proved WITHOUT emptiness — the
  delicate case is `letRec`'s mono members, where the cofinite premise gives
  boundedness of every *opening* `(e.openTyVars Xs)` and one needs
  "bounded-at-all-fresh-openings ⟹ bounded" (contrapositive: a dangling
  annotation bvar survives every opening and blocks typability downstream via
  `IsLC` premises). Prove that once, delete the predicate + all
  `*_emptyVarTyArgs` lemmas, and restate the capstone as
  `TypeOfHM.tyBvarBounded_zero`. Alternatively keep the vacuous predicate —
  it is harmless — but it is exactly the kind of scaffolding this campaign
  should absorb.
- `scratch/live.fhm` uses the disabled `{a} (x : a)` head-binder sugar and no
  longer typechecks (pre-existing; owner has deliberately un-supported the
  sugar until partial annotations/type holes land). Either rewrite it in the
  supported scheme-ascription style or move it to an archive folder so the
  repo's own smoke file runs green again.
- **Editor binder hover types degraded** (post-`eOut` drop): the report layer
  read each binding's scheme off the elaborated Λ-spine (`collectTopSchemes`);
  with no elaboratum, `zipBindingTypes` finds no entries and binder `pretty`
  types render empty. Names/kinds/diagnostics unaffected. Marked as
  `@TODO(editor-report)` at the report-assembly site in
  `FHM/EditorSupport.lean`. Fix sketch there; pair with whichever session owns
  editor work (independent of this campaign's proofs).
