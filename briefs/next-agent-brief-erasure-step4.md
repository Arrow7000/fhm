# Erasure-on-Step migration — status & handover (steps 4–6)

**Status: steps 1–3 COMPLETE (2026-08-22, commit `a505638`, `lake build` green).**
This is the authoritative "where we are" doc for a new agent continuing the
erasure-on-`Step` migration described in `design-memo-erasure-migration.md` (§5.3
is the roadmap). Read that memo first, then this doc.

---

## 0. TL;DR of the whole migration

Remove type-passing/elaboration from FHM so the source checker `Infer` is coherent
with the erased machine relation `TypeOfHM` via **one theorem**:

```
Infer.sound : Infer Φ ctx e Φ' S eOut τ → … → TypeOfHM (S.onCtx ctx).eraseBounds (e.erase) (Ty.eraseBounds (S.onTy τ))
```

Steps 1–3 (the DM cut, `erase`, and `Infer.sound` itself) are **done and proven**.
Steps 4–6 (the `TypeOfHM`/`Step` dynamics metatheory, the surface rewire +
deletion of `TypeOfElabHM`, and cleanup) remain.

---

## 1. What is DONE (steps 1–3)

### Step 1 — the Damas–Milner monomorphic-recursion cut (commit `78cf9a1`, done before this doc)
`RecSpec.init` emits all-`.mono`; `Infer.letRec` carries a `RecSpecs.ceilingOK`
premise (annotations are *ceilings*) and a `ceilingSchemes` body env;
`inferCore`/`inferRecGroupCore` are mono-only with a decidable `ceilingOk` check.
`ceilingOk_sound`/`ceilingOKB_sound` are proved (sorry-free, axiom-clean).

### Step 2 — type erasure (`Expr.erase`), commit `9380ab0`
- `FHM/Core.lean`: `def Expr.erase` (near `Expr.openBoundTyVars`, ~line 2579) — drops
  all annotations: `lambda _ → none`, `letIn _ → none`, `letRec _ → all-none`,
  `var i _ → var i []`. Plus `@[simp]` lemmas `Expr.erase_lambda/app/letIn/var/match/letRec`.
- `Expr.erase_openTyVarsAux` (depth-generalised: `∀ e d, (e.openTyVarsAux d Xs).erase = e.erase`),
  with `BranchList`/`RecGroup` helpers, plus `Expr.erase_openTyVars`/`erase_openBoundTyVars`.
  All sorry-free, axiom-clean.

### Step 3 — the coherence theorem `Infer.sound`, commit `a505638`
The NEW sound family (vs declarative `TypeOfHM`) is **fully proven, sorry-free,
axiom-clean** (`propext`/`Classical.choice`/`Quot.sound` only):

- `Infer.sound` — `FHM/InferW.lean:16853`
- `InferBranches.sound` — `:18266`
- `InferRecGroup.sound` — `:18665`

These live in a `mutual` block (with `set_option maxRecDepth 10_000 in` before it),
relocated to sit **after** the `TypeOfHM` metatheory (`TypeOfHM.weaken_scheme` etc.)
they depend on. The old sound family was renamed `*_elab`:

- `Infer.sound_elab` (`:9688`), `InferBranches.sound_elab`, `InferRecGroup.sound_elab`
  — vs `TypeOfElabHM`, DOOMED (deleted in step 5), their `letRec` cases still `sorry`.
- `Infer.sound_closed` (`:11217`) kept its name (no collision); the `sourceSound`
  family (`Infer.sourceSound` etc., vs `TypeOfHM`) is self-contained and untouched.

The **REUSE invariant layer** re-proved for the new `Infer.letRec` rule (commits
`750b7e4`, `68f8113`, `0d05f73`): `Infer.lc/.belowFvars/.dom_below/.eOut_avoid/
.eliminates/.eOut_tyBvarBounded/.dom_avoid/.gap_avoid/.preservesAnns` plus their
`InferRecGroup.*` siblings (`eOut_avoid`, `dom_avoid`, `gap_avoid`; the others were
already proven since `InferRecGroup`'s shape didn't change).

### The one genuinely-new lemma (the crux of step 3)
`PolyTy.Generalizes.freeVars_subset` (`FHM/InferW.lean:3859`):

```lean
theorem PolyTy.Generalizes.freeVars_subset {M' M : PolyTy} (h : PolyTy.Generalizes M' M) :
    M'.body.freeVars ⊆ M.body.freeVars
```

This is **the** fact that closed the `letRec` body-lift (see §3 sharp edges below).
The brief said the body-lift needed "no new metatheory shape"; that was slightly
optimistic — this small lemma is the extra shape, and it is what makes the
S₂-threading gap close.

---

## 2. What is STILL `sorry` (all DOOMED — do NOT re-prove, they are deleted in step 5)

Exactly 8 `sorry`s remain in `FHM/InferW.lean`, all in the doomed bucket:

| line | theorem | fate |
|---|---|---|
| 10334 | `Infer.sound_elab` (old, vs `TypeOfElabHM`) — `letRec` case | delete in step 5 |
| 13071 | `Infer.sourceSound` — `letRec` case | delete in step 5 |
| 20079 | `letRecFused_body_retype` | delete in step 5 (see note) |
| 20139 | `letRecFused_residual_setup` | delete in step 5 (see note) |
| 22326 | `Infer.complete'` — `letRec` case | delete in step 5 |
| 23900 | `Infer.complete_letRec` | delete in step 5 |
| 27205 | `inferRecGroupCore_complete` | delete in step 5 |
| 27396 | `inferCore_complete_letRec` | delete in step 5 |

**Note on `letRecFused_*`:** the brief listed them as "REUSE (re-prove)"; in
practice they turned out to be **unreferenced completeness-direction scaffolding**
(they previously fed the now-doomed `Infer.complete_letRec`). The new `Infer.sound`
does **not** need them (confirmed — the proof went through without them). Leave
them `sorry`; delete with the rest in step 5.

(There are also 7 pre-existing `sorry`s in `Bounds/Pipeline.lean` ×6 and
`Bounds/Erase.lean` ×1 — unrelated to this migration; leave them alone.)

---

## 3. Key decisions & findings (learned the hard way; do NOT re-litigate)

1. **The `letRec` body-lift "S₂-threading" gap.** The `Infer.letRec` ceiling premise
   is checked at `S₁` (after group unification, *before* body inference), but the
   declarative `TypeOfHM.letRec` body context is at `S₁ ++ S₂` (the body's substitution
   `S₂` threaded). The bridge is that **`S₂` fixes the solved monotype**:
   - pool vars `G` are avoided by `S₂` (domain via `Infer.dom_avoid`, range via
     `Infer.eOut_avoid`, + `mem_genGroupVars` freshness), so
     `S₂.onPolyTy (genGroup G τ) = genGroup G (S₂.onTy τ)` (via
     `Ty.substFvars_closeOverFrom`, `:7785`) — unannotated members match with no weaken;
   - non-pool free vars of the solved mono are ⊆ the annotation's fvars (via
     `PolyTy.Generalizes.freeVars_subset` on the ceiling), hence ⊆ `K`, hence avoided
     by `S₂` via the sound premise `∀ p ∈ S, p.1 ∉ K` — annotated members weaken
     `σᵢ → genGroup G τᵢ` via `TypeOfHM.weaken_scheme(s)` along the ceiling `Generalizes`.
   A naive "`S₂` keys ≥ Φ₁" invariant is **false** (`UnifyRel` can bind a rigid env
   var); do NOT go down that path. The ceiling check itself is what makes the
   annotated-member case sound (a program like `let rec f : ∀a.a→a = λx. y in …` with
   a rigid outer `y` is *rejected* by the ceiling, because `genGroup (α→v)` cannot
   generalise `∀a.a→a`).

2. **`S.onTy τ = τ` at the top of `Infer.sound`.** The proof begins with
   `rw [show S.onTy τ = τ from Ty.substFvars_eq_self_of_no_key (… Infer.eliminates …)]`.
   This is the "Infer's output type is already post-substitution" invariant, discharged
   by `Infer.eliminates` (idempotency). The statement uses `S.onTy τ` (per the brief)
   but is propositionally `Ty.eraseBounds τ`.

3. **Naming.** The new family owns the canonical names `Infer.sound` /
   `InferBranches.sound` / `InferRecGroup.sound`; the old (doomed) family is `*_elab`.
   `Infer.sound_closed` kept its name (no collision); `sourceSound` untouched.

4. **Placement.** The new sound family must sit **after** the `TypeOfHM` metatheory
   (`rec_strong`, `typ_subst_preservation`, `onSubst*`, `weaken_scheme(s)`, `regular`)
   — it is now at `:16853`+; the metatheory is `:11468`–`:16770`-ish. `weaken_env`
   ends ~`:16770`.

5. **`InferRecGroup.consPoly` is dead-but-present.** It was *not* deleted by the DM
   cut (only made unreachable via all-`.mono` `RecSpec.init`). Its case-handlers still
   exist in the invariant lemmas. The new `InferRecGroup.sound` conclusion is
   mono-only; the `consPoly` case is dispatched vacuously (head spec is `.poly`, so the
   `p.2 = .mono τ` premise is false). Do not "clean it up" mid-migration.

6. **`Expr.erase` lets `letRec` anns = `bindings.map (fun _ => none)`** (all-none, length
   = bindings), which is what makes `erase ∘ openTyVarsAux = erase` hold depth-generally
   and what `TypeOfHM.letRec`'s `RecSpecs.WF.anns_eq` sees (`specs.map RecSpec.ann` =
   all-none for all-mono specs).

---

## 4. Step 4 (NEXT): `TypeOfHM` dynamics for `SmallStep.Step`

The old dynamics metatheory (`TypeOfElabHM.progress`/`preservation`/`type_safety`,
`Core.lean:8471`/`:9442`/`:10074`) is against the elaborated relation and is deleted
in step 5. So prove, for `TypeOfHM` on **erased** terms, the standard Mini-ML
substitution-semantics metatheory (`SmallStep.Step` lives in `Core.lean:1435` and is
NOT deleted — the live evaluator already runs it):

1. **Substitution lemma**: `substN` preserves `TypeOfHM`. The delicate parts are the
   cofinite `letIn`/`letRec` cases ("types at every opening survive substitution").
   Scaffolding that survives the deletion: `TypeOfHM.rec_strong` (`:11468`),
   `Expr.substN_openTyVarsAux_comm` (`Core.lean:7889`), `SmallStep.IsValue.substN`,
   `Step.preserves_exhaustive`, `AllMatchesExhaustive.substN`.
2. **Progress**: canonical forms for `TypeOfHM` (a value of arrow type is a λ, etc.).
3. **Preservation**: `Step` preserves `TypeOfHM`. The `letRecUnfold` case is the hard
   one: it substitutes `letRec anns bindings eⱼ` (a full copy of the group) for each
   member — needs a `TypeOfHM` port of `TypeOfElabHM.rewrap_hasScheme_mono`
   (`Core.lean:9247`) and `rec_rewrap_typed` (`Core.lean:9184`). Name it as a checkpoint.
   The `letReduce` case needs `GeneralisesTo_inst_ann` and (for the erased term)
   `openTyVars_eq_self_of_erased`.
4. `preservation_star` / `type_safety` / `type_safety_closed`.

**Dependency note:** `GeneralisesTo_inst_ann`, `GeneralisesTo_inst`,
`recclo_body_typed`, and `openTyVars_eq_self_of_erased` currently live in
`FHM/CekMachine.lean` (the proved-but-unused CEK machine leaf). **Move the reusable
ones into `Core`/`InferW`** (now that `erase` exists in `Core`) rather than importing
`CekMachine.lean` — the new `TypeOfHM`/`Step` metatheory must not cite the leaf.

---

## 5. Step 5: rewire the surface; drop `eOut`; delete `TypeOfElabHM`

- Rewire `SurfaceBridge` / `Headlines` / `EvaluateUnsafe` / `PatComp` / `Bounds/*` to
  `erase` + `SmallStep.Step` + `TypeOfHM` (Headlines `WellTyped := ∃ τ, TypeOfHM
  ⟨[],ctors⟩ (erase e) τ`; `runSafe` loops `Step`).
- **Drop `eOut`** from `Infer`/`InferBranches`/`InferRecGroup` and from
  `inferCore`/`principalType`/`typecheck`. (The `Infer.sound` proof already ignores
  `eOut`; this is now a mechanical sweep.)
- **Delete**: `TypeOfElabHM` + its metatheory (`Core.lean:3139`, `:5101–10917`),
  `faithful`, `Infer.sourceSound` family, the `*_elab` sound family, the 8 doomed
  sorries above, `eOut_*`/`...Out` mirrors, `letRecElab*`, `closeTyVars`, the residual
  `eraseBounds` bridge (`Core.lean:10117–10880`).
- Green: `lake build` **and** `lake build fhm` (CLI pulls the bounds pipeline).

## 6. Step 6: cleanup

Drop `var.tyArgs` from `Expr` + `TypeOfHM.var` (changes `Expr` and `Expr.IsErased.var`,
so it will break `CekMachine.lean` — if friction, delete that leaf; its reusable lemmas
will already have moved per §4). Delete now-dead `instTy`/`shiftFrom`/`AllMatchesExhaustive.*`
helpers. Refresh `README.md` / `complexity-budget.md` / `letrec-design.md`.

---

## 7. Workflow (unchanged from the memo §6 / cekmachine-design §6)

- Main agent: definitions + theorem statements + trivial proofs; hard proofs → `sorry`.
- Proof farming: `deepseek-flash` subagents (background), one lemma/small cluster per
  call, using the lean-lsp MCP (`lean_goal`, `lean_diagnostic_messages`,
  `lean_multi_attempt`, `lean_local_search`, `lean_hover_info`). **Subagents must not
  edit outside their assigned `sorry` markers** — this bit us twice (one run clobbered
  `sourceSound`/`sound_elab` with `sorry`; verify the file is green first, and treat
  any error outside the target range as the subagent's own doing).
- Edit `.lean` only via Read/Edit. No `admit`/`axiom`/`native_decide`/new axioms. No
  `sorry` left in anything marked done. Commit at green checkpoints.
- Subagent runs can fail with `Insufficient Balance` (DeepSeek) — that's an account
  thing, not a proof failure; just relaunch (the file is untouched on such failures).
