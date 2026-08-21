# Next-agent brief: CEK migration — Stage 2 (erase + `Infer.sound` + rewire)

**Status: handover brief.** Read this first, then the design spec, then the living
status log. This brief is the bridge between the settled design and the concrete repo.

## TL;DR (the vision and momentum)

- The CEK machine (Stage 1) is **done and proved**: `FHM/CekMachine.lean` — `progress`,
  `preservation`, `preservation_*`, `type_safety`, `type_safety_closed`,
  `stepM_deterministic` — sorry-free, axiom-clean.
- The goal of the whole migration: eliminate **type-passing + elaboration + the O(n²)
  letRec Λ-nest** by moving generalisation into the environment.
- The feature set is **settled** (after a long adversarial review): scoped tyvars
  everywhere (dropped + re-inferred), polymorphic recursion **outside** blocks only
  (Damas–Milner monomorphic recursion), no type-passing/elaboration/n².
- **The design is DONE. Do not iterate the brief, do not redesign the architecture.**
  The one remaining unproved thing is a single theorem:
  `Infer.sound : Infer e τ → TypeOfHM (erase e) τ`.

## What matters (the owner's priorities — make decisions against these)

The actual goals are two *language features*: **(1) scoped type variables, usable
everywhere**, and **(2) polymorphic recursion**. Whether the operational semantics is
type-erasing or type-passing is **incidental** — a means, not an end. The n² and
`TypeOfElabHM` are **costs** to remove, not features. If a decision is ambiguous,
optimise for the features, not the machinery.

## Where the design lives

- **`briefs/feature-support-analysis-response-6.md`** — THE settled design spec. Read
  this first; it's short and final. It states: `Infer` = source relation (DM
  monomorphic recursion + **ceiling** annotations), `TypeOfHM` = machine relation
  (erased terms, mono-only `letRec`), coherence = `Infer.sound`; the ceiling premise
  `PolyTy.Generalizes (genGroup G τ) σ_opened`; the full `Infer.letRec` rule; the
  `Infer.sound` proof-obligation table.
- **The review trail** (context only if needed — do not reopen any of it):
  `feature-support-analysis-response-1.md` (mixed-group sibling poly use found),
  `response-3.md` (ground-pinning + the architecture split), `response-5.md` (the
  ceiling premise).
- **`briefs/cekmachine-design.md`** — the overall migration plan (Stages 1–4) and the
  workflow protocol. ⚠️ Its **erasure section is superseded** (see the banner at its
  top); everything else (machine description, staging, risk map, workflow) is current.

## Current code state (Stage 1 = done)

- `FHM/CekMachine.lean` (3,394 lines): the machine, fully proved. The machine types
  **closed** terms via `TypeOfHM`; `ValTyped`/`EnvOK`/`KontTyped`/`StateOK`;
  `StepM` (18 cases); `IsErased`/`ErasedState`.
- `FHM/Core.lean`: `TypeOfHM` (~3309, the declarative relation the machine uses),
  `TypeOfElabHM` (~3139, the old elaborating relation — to be DELETED),
  `GeneralisesTo` (~3040), `RecSpec`/`RecSpecs` (`.mono`/`.poly`, `MonoTyped`/
  `PolyTyped`, `bodyScheme`, `rhsEntry` — ~2941–3110), `PolyTy.WF` (~2875), the old
  `SmallStep.Step` (~1435, substitution semantics — to be DELETED).
- `FHM/InferW.lean` (27,954 lines): `Infer` (with the `eOut` index — to be DROPPED),
  `Infer.sound` (~9274, currently against `TypeOfElabHM` with `eOut`), `Infer.sourceSound`
  (~12584, to be DELETED), `letRecElabNest` (~2487, the n² — to be DELETED).
- 7 `sorry`s remain, all in `Bounds/Pipeline.lean` (6) and `Bounds/Erase.lean` (1) —
  unrelated to this work.

## Stage 2 task list (concrete, with entry points)

Do these roughly in order; each is a green checkpoint. These are the *refined* Stage 2
(the original brief's "rewire Infer / drop eOut" plus the erase+coherence slice, which
are the same thing now).

1. **Change `Infer.letRec`** (the `letRec` constructor of `Infer`, ~3018 in
   `FHM/InferW.lean`) to the doc-6 rule:
   - `RecSpec.init` (~1600) emits `.mono` for **every** member, annotations included;
     delete the `.poly` mapping.
   - Delete the `InferRecGroup.consPoly` path (~3105) and all its usages; the group
     inference is pure `consMono`.
   - Add the ceiling premise: for each `some σ`, `PolyTy.Generalizes (genGroup G τ)
     σ_opened` (`PolyTy.Generalizes` at 17227; open `σ` under the enclosing scope the
     way `Infer.letInAnn` already does — ~2983 — not the stored dangling scheme).
   - Body env = the annotations (ceiling); `genGroup` for unannotated members.
   - Note: `RecGroup.rigidVars` (~1542) currently treats annotation fvars as rigid
     because they sat in `rhsCtx` as schemes; under the cut they no longer do — drop
     the stale justification, don't copy it.
2. **Define `erase : Expr → Expr`** in `FHM/Core.lean` (near `Expr.openTyVars`): drop all
   annotations — `lambda (some t) → lambda none`, `letIn (some σ) → letIn none`,
   `letRec anns → letRec (all none)`, `var i _ → var i []` (zero the tyArgs, don't just
   pass `[]` through). Prove `erase_openTyVars : erase (e.openTyVars Xs) = erase e`
   (this is what the `letIn` case of `Infer.sound` needs).
3. **Prove `Infer.sound : Infer Φ ctx e Φ' S τ → TypeOfHM (S.onCtx ctx) (erase e)
   (S.onTy τ)`** — replacing the current `Infer.sound` (~9274). The proof-obligation
   table is doc-6 §2; key glue: `erase_openTyVars`, `TypeOfHM.weaken_scheme` (17236)
   for the `letRec` body case (lift from the annotation env to the `genGroup` env),
   and cofinite reconstruction (one opening → all openings).
4. **Spec + implement Bounds opening** — Bounds walks stored dangling `bvar`s and must
   open in lockstep with Infer, or run on a pre-opened copy. `Bounds/Synth.lean`
   ~662–680 reads λ ascriptions and let anns; `letRecProvisional` ~430–433 feeds
   `σ.body` as stored.
5. **Lift `SurfaceBridge.lowerPoly`** (~3504) to allow outer scoped refs in scheme
   bodies (thread the ambient tyvar scope the way `bindingLowerTyScope` (~3756) /
   `letAnnTyPrefix` (~3597) already do for λ ascriptions).

Then continue the original Stage 2 (drop `eOut` wholesale from `Infer`/`InferBranches`/
`InferRecGroup`, delete `sourceSound`/`faithful`/`eOut_*`/`letRecElab*`/`closeTyVars`)
and Stage 3 (delete `TypeOfElabHM` + its metatheory, `SmallStep.Step` +
`substN`/`instTy`/`shiftFrom`, the residual bridge; rewire `Headlines`/`SurfaceBridge`/
`EvaluateUnsafe`/`PatComp`/`Bounds` walkers to the source term + `erase` + the machine).

## Workflow (established protocol — from `cekmachine-design.md` §6)

- **You** make the substantive changes: define the `inductive`s/`def`s/theorem
  *statements*, prove the trivial ones, leave the rest `sorry`.
- **Proof workhorse = `deepseek-flash` subagent**, one lemma/small cluster per call,
  instructed to prove and nothing else; use the lean-lsp MCP (`lean_goal`,
  `lean_diagnostic_messages`, `lean_multi_attempt`, `lean_local_search`) for fast
  iteration; call `lean_build` if the LSP stalls (>~120s); if a goal looks unprovable as
  stated, STOP and report (never weaken the statement, never `admit`/`axiom`/
  `native_decide`).
- Edit `.lean` only via Read/Edit (never `sed`/Python). Headline theorems stay
  **axiom-clean** (`propext`/`Classical.choice`/`Quot.sound` only); `#print axioms` is
  the audit of record. Commit at each green checkpoint.

## The one thing to protect

`Infer.sound : Infer e τ → TypeOfHM (erase e) τ` is the whole game. If it fails to
prove, the fix is a **rule tweak** (the `Generalizes` ceiling premise), **not** a
redesign. The architecture is settled — do not reintroduce selective erasure, a floor,
a fused `TypeOfHM`-on-source, or any of the refuted designs from the review trail.
