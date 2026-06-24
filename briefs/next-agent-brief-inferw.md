<!-- Handoff brief written at the end of the "scoped type variables → erasure → InferW" session.
     Companion to next-agent-brief-surface-lang.md (the longer-term north star). -->

# Handoff: continue scoped type variables into InferW (Algorithm-W)

## 0. Workflow the user wants from you (please follow, in order)

1. **Orient first.** Read this brief end-to-end. Then look around with the lean-lsp MCP (read, don't just grep): the new machinery in `FHM/Core.lean` (committed, green, axiom-clean) and the **work-in-progress** in `FHM/InferW.lean` (uncommitted, exactly one deliberately-gated `sorry`).
2. **Then think, then PRESENT — do NOT barrel into implementation.** After orienting, give the user your own read of where things stand and what you think the next step should be. The next move is soundness-critical, and the user strongly prefers to **brainstorm / confirm the algorithm design before it is implemented** (we did exactly this for the erasure fix below, and it paid off). Hold off on any big implementation push until you've presented and aligned.
3. **Be merciless about correctness, never cosmetic.** No weakening of headline statements to force a green build; no `sorry`/`axiom`/`native_decide` in any final state. If something can't be proven honestly, say so and report the real obstacle. That ethic has served this project well.

## 0a. ⚠️ Environment gotcha that bit us hard
Editing `Core.lean` does **not** auto-refresh the running lean-LSP for files that *import* it (`InferW.lean`). After any Core edit, InferW will show a **fake green** against the stale `Core.olean`. To get truthful InferW diagnostics you must rebuild Core's olean and restart the LSP (`lean_build`); verify by checking that e.g. `@Expr.substTyFvar` and `@TypeOfHM.rec_strong` resolve from inside InferW. (Right now `Core.olean` is current with committed `Core.lean`, so a fresh session is fine — just remember this the instant you touch Core.)

## 1. The big picture (north star)
The goal is a verified **surface HM language** (named vars + sugar → parse → desugar → resolve → infer) on top of this de Bruijn core. **Scoped type variables** (referencing a signature's type variable inside its body, à la GHC `ScopedTypeVariables` / Elm) are the prioritized prerequisite. The surface language itself (§5) lives in `next-agent-brief-surface-lang.md` — that's the eventual destination, *not* this task.

## 2. DONE and committed — Phase A (`Core.lean`, commit `20f7c9e`, axiom-clean)
Scoped type variables now work at the **declarative + dynamic** level:
- `TypeOfHM.lambda`/`letIn` dropped the `NoFreeVars` closedness restriction; the `letIn` cofinite premise opens the bound expression's scoped vars (`Expr.openBoundTyVars`) in lockstep with the scheme.
- New ops: `Expr.substTyFvar(s)`, `Ty.openVarsFrom`, `Expr.openTyVars`/`openBoundTyVars`; the strong eliminator `TypeOfHM.rec_strong` (single motive over the mutual `TypeOfHM`/`TypeOfMatchBranch` — use it for derivation induction).
- **Important discovery:** naive scoped-var annotations *break subject reduction*. `preservation_is_unsound` is a kernel-checked proof that `let f : ∀a.a→a = λ(x:a).x in f 3` steps to the untypeable `λ(x:a).x`. (See §3.)
- **Fix = type erasure:** `Expr.eraseTyAnnots`/`IsTyErased`, `erase_preserves_typing`, erased `progress`/`preservation`, and `erased_type_safety` (single-step) + `erased_type_safety_star` (multi-step, via `Relation.ReflTransGen`). All `lean_verify`-clean.

## 3. The key idea to internalize: "check with annotations, run erased"
A scoped variable `a` is meaningful only under its binder. After a `let` reduces away, the value `λ(x:a).x` is substituted raw and its `a` is orphaned — there is no term-level mechanism to resolve it to the use-instance (`Int`), and it can't be any fixed fvar either (that types at `W→W ≠ Int→Int`). The principled HM fix (rather than System-F-style type passing) is that **annotations are runtime-irrelevant**: typecheck *with* annotations, then run on the **type-erased** term. That's why the dynamic-soundness layer is phrased over `IsTyErased` terms. **Crucially: the static inference algorithm is unaffected by erasure — it must match the static `TypeOfHM` spec, which now has scoped vars.**

## 4. WIP — `InferW.lean` (uncommitted, one gated `sorry`)
Stage 1 (done): the *existing, closed-annotation* algorithm re-proven **sound** against the new Core.
- Added `TypeOfHM.onSubst_fixed` (recovers the fixed-term conclusion under "the threaded subst fixes the term's annotation fvars") + the closed-regime discharge `Infer.tyFreeVars_eq_nil`; threaded through all of `Infer.sound`/`InferBranches.sound` **without weakening** any headline. `sound_letInAnn` re-proved (axiom-clean). `LamSeed`/`Infer.lambda`/`belowFvars` ripples fixed.
- **One `sorry`** (search for "STAGE-2 / D2 GATE", ≈ line 914, `Infer.openTyVarsAux_eq_self` `match_` case): blocked only because Core's `BranchList.openTyVarsAux` is `private`. It's a *mechanization* gap, not unsoundness — the D2 re-order (§5) removes the need for this bridge entirely.
- **Not done:** the actual scoped-var algorithm, completeness (D4), and the erasure/`typecheck_*` adaptation (`progress`/`preservation` now carry an `IsTyErased` premise).

## 5. The crux ahead — the REAL scoped-variable algorithm (§4.2; soundness-critical)
Stage 1 stayed in the *closed-annotation regime*, so the algorithm still **rejects** scoped-var programs. The real feature is one coherent move:
- **Relax** `LamSeed.some` (`Ty.isClosed → IsLC` / `ContainsBvarsUpTo 0`) and `Infer.letInAnn` (drop `NoFreeVars σ.body`).
- **Re-order `letInAnn` (D2):** allocate the signature's skolems *before* inferring the rhs; infer the rhs already opened at those skolems (matching the spec's `openBoundTyVars`); keep the skolems **rigid**; escape-check the **whole** rhs substitution (today only the final unifier `Schk` is checked).
- This (a) **generalizes D1** from the trivial closed-regime invariant (`tyFreeVars_eq_nil`) to the real "the threaded subst fixes the rigid skolems, via escape" discharge — reuse `onSubst_fixed`; (b) **removes the lone `sorry`** (no more `openTyVars = id` bridge); (c) is **required for completeness**.
- **D4 (completeness kernel):** `exists_skolem_unifier` assumes the rhs principal type is disjoint from the skolems (`τ₁ ∩ Ys = ∅`); once the rhs can mention skolems that's false. Rework it to split `τ₁.freeVars` into (skolems `Ys`) ⊎ (residue `< Φ₁`) and build a `Ys`-fixing unifier that tolerates skolems on both sides. **(Riskiest single piece — design it before coding.)**
- Then re-prove the headlines unchanged: `Infer.sound`, `Infer.principal`, `infer_complete`, `infer_iff_typeable`, `typecheck_*`.

## 6. Reservations / concerns
- **This is the soundness-risk zone.** The rigid-skolem discipline (escape-checks keeping skolems un-unified) is exactly what makes scoped-var inference sound; get it wrong and `Infer.sound` becomes false (or unprovable). Design D2/D4 with the user first.
- **Completeness needs the relaxation** — don't attempt completeness against the unrelaxed (closed-only) algorithm; it's genuinely false there (the spec accepts `λ(x:a).x`, the closed algorithm rejects it).
- **Some Stage-1 work will be reworked** (`tyFreeVars_eq_nil` → skolem-fixing); the `onSubst_fixed` corollary + threading scaffold remain useful.
- **Honest sizing:** ~3–5 focused sessions for InferW. Stage it, validate each stage (`lean_verify` axiom-clean), report cleanly. Decline/report beats a half-baked push.
- **Don't modify `Core.lean`** unless genuinely necessary (verified + committed). If tempted to un-`private` `BranchList.openTyVarsAux`, prefer the D2 reorder instead; if you do touch Core, re-verify it and flag the user.

## Tools
lean-lsp MCP: `lean_diagnostic_messages` (scope with line ranges; its `success` is whole-file, so trust the `items` array), `lean_goal`, `lean_multi_attempt`, `lean_hover_info`, `lean_verify` (axiom check; use fully-qualified names). Avoid gratuitous `lake build` — but see §0a; you *will* need to refresh the LSP after Core edits.
