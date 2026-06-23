<!-- Handoff: Stage 2 of `letRec` — the InferW inference side.
     Companion to letrec-design.md (read §4). Core side is DONE (commit f074745). -->

# Handoff: `letRec` Stage 2 — InferW inference

## Status (READ FIRST)
- **Core `letRec` is DONE, green + axiom-clean, committed (`f074745`).** The node
  `Expr.letRec (bindings : List Expr) (body : Expr)`; the **cofinite** typing rule
  `TypeOfHM.letRec` (∀ fresh `Xs`, group bound monomorphically at `PolyTy.openGroup
  Ms Xs`, body sees schemes `Ms`); dynamics `Step.letRecUnfold` (unconditional
  unfold; `n=1` = `fix`); and full safety (`progress`/`preservation`/
  `erased_type_safety` axiom-clean) are all in `Core.lean`. `Pretty.lean` renders
  `letRec`. Helpers: `PolyTy.totalParams`, `PolyTy.openGroup`, plus the threading
  helpers the Stage-1 subagent added (`openGroup_length`, `*_substFvar`,
  `rewrap_at_opening`/`rewrap_hasScheme`, etc.).
- **`InferW.lean` and `Examples.lean` are RED** against the new `Expr.letRec` node
  (no inference rule yet). That is this stage.
- Design rationale: **`letrec-design.md` §4** sketches the inference algorithm.
- ⚠️ A stray `faebb71` commit changed the Surface lambda print style to `\x -> …`;
  confirm or revert if unintended (cosmetic only).

## The task: inference for `letRec` (mirror the §1 `match`/`InferBranches` work)
1. **`Infer.letRec`** constructor (mirror `Infer.letIn`, which uses `genScheme`, but
   for a group with a monomorphic pre-binding). Algorithm-W:
   allocate `n` fresh monotype vars `βⱼ`; bind the group monomorphically; infer each
   RHS threading substitutions and unify `τⱼ` with the running `βⱼ`; then
   **generalize** each `S βⱼ` over `S ctx` via `genScheme` → schemes `Mⱼ`; infer the
   body in `Ms ++ S ctx`.
2. **`InferRecGroup`** threader inductive — the analogue of `InferBranches` for the
   group (threads inference + per-binding unification over the list). Re-prove its
   lemmas (`frontier_le`/`lc`/`belowFvars`/`sound`/`gap_avoid`/`complete`/`complete'`).
3. **Executable** `inferCore` `letRec` case + `inferRecGroupCore` (refining the
   relations); this is what unblocks `InferW.lean` building.
4. **Soundness:** `Infer.letRec` ⟹ `TypeOfHM.letRec`. The soundness proof must
   PRODUCE the cofinite premise — i.e. show the inferred schemes `Ms = genScheme …`
   satisfy "∀ fresh `Xs`, group types at `openGroup Ms Xs`". Reuse the `genScheme`
   soundness lemmas + the `onSubst_fixed` machinery (as `Infer.letIn`/`match_` sound do).
5. **Completeness/principality:** `Infer.complete'` `letRec` case + the
   `inferCore_complete` `letRec` case — mirror `letIn` + `InferBranches.complete'`.
6. **Examples/capstone:** once inference works, add a recursive demo to `Examples.lean`
   (e.g. a `length`-shaped self-recursive program — note `map`/`length`/`fold` are
   `n=1`) and an `AuditCapstone` witness that a recursive program typechecks at its
   principal type.

## Workflow / guardrails (same as before)
- Lock-then-thread: the Core defs are frozen — do NOT change `TypeOfHM.letRec` or any
  Core statement. Design `Infer.letRec`/`InferRecGroup` (soundness-critical), get the
  executable inferer compiling, then thread proofs.
- NEVER `sorry`/`admit`/`axiom`/`native_decide` in the final; never weaken a headline
  statement; if a goal needs a statement change, STOP and report (that's how the
  existential-premise bug was caught in Stage 1).
- Targeted builds only: `lake build Experiments.FreshTypeSystem.InferW` (NOT
  whole-project — `Filterings.lean` is broken). After editing Core (you shouldn't),
  rebuild Core first. Use the `project-0-experiments-lean-lsp` MCP.
- Verify axiom-clean (`propext`/`Classical.choice`/`Quot.sound`) on the headline set
  (`typecheck_*`, `principalType_*`, `infer_*`, `Infer.complete'`/`isPrincipal`/
  `output_unique`, `inferCore_complete`, `AuditCapstone.*`) via `#print axioms` /
  `lean_verify` (cross-check — `lean_verify` can show stale `sorryAx`).
- Scope: v1 is annotation-free, monomorphic recursion. Polymorphic (annotated)
  recursion is a deliberate later extension.
