<!-- Handoff: Stage 3 of `letRec` — annotated (polymorphic) recursion.
     Companion to letrec-design.md (read the STATUS banner + §2.3′/§4) and
     next-agent-brief-letrec-inferw.md (Stage 2, now DONE). -->

# Brief: annotated polymorphic recursion for `letRec` (Stage 3)

## Status (READ FIRST)
- Monomorphic `letRec` (self + mutual, **annotation-free**) is DONE, green,
  axiom-clean, committed: Core rule + full safety (`a02089a`), InferW inference +
  soundness + completeness/principality (`778959b`), Examples + AuditCapstone
  (`50ed93d`).
- The shipped Core rule is the **shared-monotype** form — `letrec-design.md` §2.3′
  (NOT the §2.3 `openGroup` form, which was found unsound vs DM for `n > 1` and
  replaced). Source is ground truth.
- Key Core pieces to reuse: `TypeOfHM.letRec` (search `| letRec` in `Core.lean`),
  helpers `PolyTy.genGroup` / `Ty.renameG` / `Ty.genFilter`, and freshening lemmas
  `PolyTy.genGroup_renameG` / `genGroup_substFvar` / `Ty.closeOver_rename` /
  `openVars_closeOver_rename` / `closeOver_openVars_self`.
- Key InferW pieces: `Infer.letRec` + `InferRecGroup` threader, `genGroupSchemes`
  / `genGroupVars`, `inferRecGroupCore`, `Infer.sound` / `InferRecGroup.sound`,
  `Infer.complete'` / `InferRecGroup.complete'`, `inferCore_complete`.

## Goal
Add DECIDABLE **polymorphic recursion** via per-binding type annotations.
(Unannotated polymorphic recursion = Milner–Mycroft = undecidable; we never infer
it. Annotated is decidable because it is "**check, not infer**".) An annotated
recursive binding goes into scope at its FULL declared scheme `σⱼ` (polymorphic)
in BOTH the RHSs and the body; each RHS is checked against `σⱼ`'s skolemised
opening; recursive occurrences may instantiate `σⱼ` at DIFFERENT types — that is
exactly what makes the recursion polymorphic (`depth : ∀a. a perfect → Int`
calling itself at `(a×a) perfect`). This **sidesteps generalisation entirely**
(no `genGroup`, no shared-monotype opening — schemes are given, not generalised).

## THE design template: annotated `letIn` already exists — generalise it to a group
Study and mirror the *annotated* (`some σ`) path of `letIn`, which is precisely the
scoped-type-variable / skolem machinery you must lift to a group:
- `TypeOfHM.letIn`'s `(∀ σ, ann = some σ → M = σ)` premise (Core).
- `Infer.letInAnn` (InferW): allocates skolems `Ys = freshVars N σ.paramCount`,
  infers the rhs already-opened at `Ys`, unifies against `σ.openVars Ys`, with the
  TWO escape conditions (skolems not bound by `S₁ ++ Schk`; not leaked into the body
  context). **These escape conditions ARE the hard part** — generalising them to a
  group is the main metatheory risk. Also read `Infer.sound_letInAnn` and
  `Infer.complete_letIn_ann_aux`.

## Decisions to make FIRST (brainstorm before coding)
1. **Representation.** Either (a) extend `Expr.letRec` bindings to carry an
   `Option PolyTy` per binding, or (b) add a separate `Expr.letRecAnn` node.
   (a) ripples through EVERY structural function + proof in Core/InferW (large);
   (b) duplicates but isolates. `letIn` uses ONE node with `Option PolyTy`; that
   uniform style is attractive, but a recursive GROUP can MIX annotated +
   unannotated bindings, which (b)/(a) must both handle.
2. **Scope for v1 of this stage.** STRONGLY consider **all-annotated groups only**
   first (clean polymorphic recursion). Mixing the `genGroup` (infer-then-generalise)
   path with the skolem (check) path *within one group* is materially harder — defer.

## Workflow / guardrails (the discipline that worked for Stage 2)
- **LOCK-THEN-THREAD. SPIKE the declarative rule first**: state it standalone, prove a
  polymorphic-recursion example types (add a `perfect`-tree ADT for a `depth`-style
  witness, or hand-roll a simpler one), AND sanity-check `weaken_env`/`typ_subst` are
  tractable for the rule BEFORE touching frozen Core. (Stage 2 had a wrong first rule
  that only `weaken_env` exposed — and an even-earlier wrong redesign. Do the spike.)
- If a goal needs a Core statement change, STOP and report.
- NEVER `sorry`/`admit`/`axiom`/`native_decide`; never weaken a headline statement.
- Targeted builds only (`lake build FHM.InferW`; the
  whole project is broken — `Filterings.lean`). Use the
  `project-0-experiments-lean-lsp` MCP; verify axiom-clean via `lean_verify`
  (cross-check, not just the editor's cache — and re-verify subagent claims yourself).
- Stages: (1) rule + `rec_strong` + safety → green + axiom-clean, commit;
  (2) inference + soundness; (3) completeness/principality + an `AuditCapstone`
  witness that a polymorphic-recursive program typechecks at its principal scheme.

## Headline axiom-clean set to keep clean
`typecheck_*`, `principalType_*`, `infer_sound`/`infer_isPrincipal`/`infer_complete`,
`Infer.sound`/`Infer.complete'`/`Infer.isPrincipal`, `inferCore_complete`,
`progress`/`preservation`/`erased_type_safety`, `AuditCapstone.*` — all currently
`propext`/`Classical.choice`/`Quot.sound` only; keep them so.
