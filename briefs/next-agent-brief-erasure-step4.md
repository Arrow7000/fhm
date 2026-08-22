# Erasure-on-Step migration — status & handover (steps 4–6)

**Status: steps 1–3 COMPLETE (2026-08-22, commit `a505638`, `lake build` green).**
This is the authoritative "where we are" doc for a new agent continuing the
erasure-on-`Step` migration described in `design-memo-erasure-migration.md` (§5.3
is the roadmap). Read that memo first, then this doc.

**Numbering.** This brief's steps 1–6 are the *migration* steps (cut, erase,
`Infer.sound`, dynamics, rewire/delete, cleanup). The memo's §5.3 uses a
1–7 list that starts with "settled design" as step 1, so **this brief's step 4
= memo step 5**, brief step 5 = memo step 6, brief step 6 = memo step 7. The
memo's status blurb saying "steps 1–4 are DONE" is memo-numbering (design +
cut + erase + `Infer.sound`). Do not treat that as "dynamics is done".

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
They are **soundness, not iff**: isolated `ceilingOk` is strictly stronger than
semantic `Generalizes` (fresh `Ys`, `σ.body.freeVars` held rigid, `τ` LC,
`unifyCoreK` succeeds). The three traps from the memo are handled: (a) `σrigid`
is in the Bool; (b) unify runs on `eraseBounds`; (c) `ceilingOKB_sound` requires
equal lengths because zip truncates while `Forall₂` does not. At the `inferCore`
call site `σrigid` is automatic (`RecGroup.rigidVars` includes `AnnList.tyFreeVars`
= `σ.body.freeVars`) and `hLen` is discharged by `RecSpec.init_length`.

`ceilingOk_complete` (semantic `Generalizes` ⇒ Bool, under the call-site hyps
`inferCore` already has: `σ.WF`, equal lengths, `rigidVars`, fresh `Φ₁`) **is a
real theorem worth having**: it would make `inferCore`'s check match
`Infer.letRec`'s premise, so the algorithm isn't a silent conservative
approximation of the relation. It is **not** on the critical path of steps 4–6
(`Infer.sound` uses semantic `ceilingOK`; the remaining work is `TypeOfHM`/`Step`
then deletion). `unifyCoreK_complete_aux` (`InferW.lean:25016`) already exists,
so this is a bounded matching-completeness lemma, not another S₂-threading
gap. Do not block dynamics on it; park it as a follow-up completeness item
(alongside the doomed `Infer.complete*` family, which is a *different*
completeness — Infer vs `TypeOfHM` — and is deleted in step 5).

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
- `Infer.sound_closed` (`:11217`) kept its name (no collision) — it is a
  corollary of `sound_elab` (elaborated `TypeOfElabHM` / `eOut`), **not** of the
  new `Infer.sound`. For a closed `TypeOfHM` fact, instantiate `Infer.sound`
  with `K = []`. The `sourceSound` family (`Infer.sourceSound` etc., vs
  `TypeOfHM` of the *annotated* input) is self-contained and untouched
  (doomed; deleted in step 5).

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

7. **Do not strip annotation fvars out of `RecGroup.rigidVars`.** The comment at
   `InferW.lean:1533` is stale (it still talks about schemes sitting in `rhsCtx`;
   after the cut they don't). The *list* is still right: `G` is computed against
   the outer `(S₁.onCtx ctx).env`, not the ceiling body env, so rigidVars is
   what keeps a dangling annotation fvar out of the pool. Deleting that term
   is a soundness footgun, not a cleanup.

8. **`Expr.IsErased` ≠ image of `Expr.erase`.** `IsErased` (`CekMachine.lean:10`)
   is the old *selective* erase: λ-ascriptions and `var.tyArgs` dropped, but
   `letIn`/`letRec` annotations **kept** (provided `WF`). Uniform `Expr.erase`
   drops those too. `e.erase` is `IsErased`, but not conversely.
   `openTyVars_eq_self_of_erased` is stated on `IsErased` and relies on
   `σ.WF` to leave kept annotations unchanged; the fact you actually want for
   `Step` on `erase e` is "opening is a no-op on the *image* of `erase`"
   (which follows from `erase` producing `none`/all-none/`tyArgs = []`, or
   from `erase_openTyVarsAux` plus `erase` idempotence). Do not import
   `IsErased` into the new dynamics and call the job done.

9. **Adversarial review of steps 1–3 (2026-08-22) passed all five sections.**
   `Infer.sound` / `InferRecGroup.sound` / `freeVars_subset` / `erase_openTyVarsAux`
   / `ceilingOk_sound` are axiom-clean (`propext`/`Classical.choice`/`Quot.sound`).
   The 8 `sorry`s in §2 are the complete live set in `InferW.lean`.

---

## 4. Step 4 (NEXT): `TypeOfHM` dynamics for `SmallStep.Step`

The old dynamics metatheory (`TypeOfElabHM.progress`/`preservation`/`type_safety`,
`Core.lean:8633`/`:9604`/`:10236`) is against the elaborated relation and is deleted
in step 5. So prove, for `TypeOfHM` on **erased** terms, the standard Mini-ML
substitution-semantics metatheory (`SmallStep.Step` lives in `Core.lean:1435` and is
NOT deleted — the live evaluator already runs it).

**Load-bearing restriction (memo §7):** state progress/preservation/`type_safety`
for `erase e` (or terms in the image of `erase`), **never** for arbitrary annotated
terms. `Step` on an annotated `let f : ∀a. a→a = λ(x:a). x in f 3` orphans the
ascription; `TypeOfHM` of that closed rhs fails `paramTy.IsLC`. Do not try to
prove `Step` preservation for annotated terms — that brings type-passing back.

**Placement:** put the new metatheory in `InferW` (after `TypeOfHM.rec_strong` /
`weaken_scheme`), **not** in `Core`. `TypeOfHM` is defined in `Core`, but its
induction principle `TypeOfHM.rec_strong` (`InferW.lean:11468`) and the type-subst
family live in `InferW`; `Core` does not import `InferW`. A new file that imports
`InferW` is also fine. Do **not** import `CekMachine.lean`.

Templates (port, don't cite):

- `TypeOfElabHM.subst_lemma` / `subst_lemma_many` (`Core.lean:8420` / `:8195`)
- `TypeOfElabHM.canonical_*` (`:8476+`) then `progress` (`:8633`)
- `TypeOfElabHM.rec_rewrap_typed` (`:9346`) and `rewrap_hasScheme_mono` (`:9409`)
- `TypeOfElabHM.preservation` (`:9604`) — `beta` uses `subst_lemma`; `letReduce`
  uses `HasScheme.fromLetCofinite`; `letRecUnfold` uses the rewrap pair

Under the DM cut the rewrap is *simpler* than the ElabHM original: specs are
all-`.mono`, so the `PolyTyped` half is vacuous.

Green checkpoints, commit each:

1. **Move/restate the reusable CEK lemmas** into `Core`/`InferW`, restated for
   the image of `Expr.erase` rather than `IsErased` where it matters:
   - `Expr.openTyVars_eq_self_of_erased` (`CekMachine.lean:98`) — see §3 item 8
   - `GeneralisesTo_inst` (`:839`) and `GeneralisesTo_inst_ann` (`:787`)
   - `recclo_body_typed` (`:972`) is **not** a drop-in for `Step`. It is the
     CEK analogue of `rewrap_hasScheme_mono` (a rec-closure, not a substituted
     `letRec` copy). Use it as a proof *template* for the TypeOfHM rewrap
     port; do not try to apply it to `letRecUnfold`.
2. **Substitution lemma**: `substN` preserves `TypeOfHM`. Delicate: cofinite
   `letIn`/`letRec` ("types at every opening survive substitution"). Scaffolding
   that survives the later deletion: `TypeOfHM.rec_strong` (`:11468`),
   `Expr.substN_openTyVarsAux_comm` (`Core.lean:7889`), `SmallStep.IsValue.substN`,
   `Step.preserves_exhaustive`, `AllMatchesExhaustive.substN`. Name the rewrap
   port (`TypeOfHM.rec_rewrap_typed` / `rewrap_hasScheme_mono`) as a sub-checkpoint
   of this lemma — it *is* the letRec case, not a freebie.
3. **Progress**: canonical forms for `TypeOfHM` (a value of arrow type is a λ,
   etc.). Port `TypeOfElabHM.canonical_*`; they invert values, so they are
   almost copy-paste onto `TypeOfHM`.
4. **Preservation** (`Step` preserves `TypeOfHM`). `letRecUnfold` is the hard
   case (substitutes `letRec anns bindings eⱼ` — a full copy of the group —
   for each member; the copy must inhabit `genGroup G τ`). `letReduce` needs
   `GeneralisesTo_inst_ann` and opening-is-id on `erase e`.
5. `preservation_star` / `type_safety` / `type_safety_closed`.

---

## 5. Step 5: rewire the surface; drop `eOut`; delete `TypeOfElabHM`

Do **not** do this as one commit. Three sequenced green checkpoints:

**(a) Rewire call sites, TypeOfElabHM still present.** `SurfaceBridge` /
`Headlines` / `EvaluateUnsafe` / `PatComp` / `Bounds/*` to `erase` + `SmallStep.Step`
+ `TypeOfHM`. Today's `Headlines.WellTyped` (`:558`) is `TypeOfElabHM` of
`e.eraseBounds` — that is the Path R *bounds* erase, **not** `Expr.erase`. The
new definition is `∃ τ, TypeOfHM ⟨[], ctors⟩ (e.erase) τ` (memo §5.1).
`elaborateSafe` currently runs `elaborateProgram`; the new pipeline is
`lower → Infer → erase → Step` (no `eOut`). `runSafe` already loops `Step`.
`Infer.sound` with `K = []` is the closed-term glue; do not call
`Infer.sound_closed` (that is `sound_elab`).

**(b) Drop `eOut`** from `Infer`/`InferBranches`/`InferRecGroup` and from
`inferCore`/`principalType`/`typecheck`. The `Infer.sound` *proof* already ignores
`eOut`; the *type* still carries it. This is mechanical in idea and large in
blast radius (`eOut` occurs ~270 times in `InferW.lean`). The REUSE layer just
re-proved for step 3 (`eOut_avoid`, `eOut_tyBvarBounded`, `preservesAnns`) either
simplifies or disappears — that is expected, not a regression. Do not mix this
with (c).

**(c) Delete**: `TypeOfElabHM` + its metatheory (`Core.lean:3139`, roughly
`:5101–10917`), `faithful`, `Infer.sourceSound` family, the `*_elab` sound family,
the 8 doomed sorries above, `eOut_*`/`...Out` mirrors, `letRecElab*`, `closeTyVars`,
the residual `eraseBounds` bridge (`Core.lean:10117–10880`). **Keep** anything
about `substN`/`Step`/`AllMatchesExhaustive` that is not ElabHM-specific
(`Expr.substN_openTyVarsAux_comm`, `SmallStep.IsValue.substN`,
`Step.preserves_exhaustive`, `AllMatchesExhaustive.substN`) — those are step-4
scaffolding living next to doomed lemmas.

Green: `lake build` **and** `lake build fhm` (CLI pulls the bounds pipeline).
The 7 Bounds `sorry`s stay; they still compile.

## 6. Step 6: cleanup

Drop `var.tyArgs` from `Expr` + `TypeOfHM.var` (changes `Expr` and `Expr.IsErased.var`,
so it will break `CekMachine.lean`). **Expect to delete `FHM/CekMachine.lean` in
this step** — nothing imports it, reusable lemmas moved in §4, and keeping it
compiling through an `Expr` ctor change is wasted work. Delete now-dead
`instTy`/`shiftFrom`/`AllMatchesExhaustive.*` helpers. Refresh `README.md` /
`complexity-budget.md` / `letrec-design.md`. `Headlines.lean`'s module doc still
describes Path R residual `TypeOfElabHM` / `sourceSound`; rewrite it to the
`erase` + `TypeOfHM` + `Step` story.

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
