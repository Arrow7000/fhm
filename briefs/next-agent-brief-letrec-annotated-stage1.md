<!-- Handoff: Stage 3 / Step 1 of `letRec` — annotated polymorphic recursion, CORE.
     Parent brief: next-agent-brief-letrec-annotated.md. Spike (proven, axiom-clean):
     FHM/SpikeLetRecAnn.lean. -->

# Brief: `letRecAnn` Stage 1 — Core rule + dynamics + full safety

## Status / what is already done (READ FIRST)
- The **design is spiked and proven** in `FHM/SpikeLetRecAnn.lean`
  (standalone, no Core edits, axiom-clean). It contains:
  - `TypeOfLetRecAnn` — the declarative rule as a derived predicate (this is the
    EXACT shape to port into Core as the `TypeOfHM.letRecAnn` constructor);
  - `polyRec_typeable` — a genuine polymorphic-recursion witness types;
  - `#eval` showing the monomorphic reading is rejected (scheme is load-bearing);
  - `TypeOfLetRecAnn.weaken_env_front` and `TypeOfLetRecAnn.typ_subst` — the two
    metatheory-risk lemmas, PROVEN (their proof bodies are the templates for the
    real `weaken_env`/`typ_subst` cases);
  - `scopedRhs_typeable`/`scopedRec_typeable` — a scheme mentioning a free `fvar`
    is WF and types.
- **Monomorphic `letRec` is DONE, green, axiom-clean** (`Core.lean`, search
  `| letRec`). It is your **line-by-line template** for EVERY structural function,
  lemma, the `Step` rule, `rec_strong`, erasure, and the safety proofs. Mirror it.

## Goal of this step
Add the `letRecAnn` node + the **declarative** typing rule + dynamics + **full
safety** (`progress`/`preservation`/`erased_type_safety` axiom-clean) to
`Core.lean`. Inference (`InferW`) is a LATER step — do not touch it here.

## LOCKED design decisions (do not redesign; if one seems impossible, STOP + report)

### Representation — PARALLEL lists (maximises reuse of the `RecGroup.*` helpers)
```lean
| letRecAnn (schemes : List PolyTy) (bindings : List Expr) (body : Expr)
```
- `bindings : List Expr` is the SAME type as `letRec`'s, so **reuse the existing
  `RecGroup.*` helpers verbatim** for every term-level operation on the bindings
  (`RecGroup.shiftFrom`/`substN`/`substTyFvar`/`openTyVarsAux`/`eraseTyAnnots`/
  `tyFreeVars`/`sizeRecGroup` + their `_eq_map` lemmas).
- `schemes : List PolyTy` is the new parallel list. The length invariant
  (`bindings.length = schemes.length`) lives in the **rule** (mirroring how
  `letRec` keeps `τs.length = Ms.length` as a premise), NOT in the constructor.

### Structural function clauses (mirror `letRec`; schemes handled as noted)
- `shiftFrom` / `substN`: **schemes untouched** (these are term-var operations).
  `letRecAnn schemes (RecGroup.shiftFrom (threshold + bindings.length) n bindings)
  (body.shiftFrom (threshold + bindings.length) n)` — exactly `letRec`'s threshold.
- `substTyFvar Z U`: **schemes substituted** —
  `letRecAnn (schemes.map (PolyTy.substFvar Z U)) (RecGroup.substTyFvar Z U bindings)
  (body.substTyFvar Z U)`.
- `openTyVarsAux d Xs`: **schemes UNTOUCHED** (v1 schemes are closed, so opening is
  a no-op on them — this is the key simplification; do NOT try to open schemes).
  Recurse into bindings/body: `letRecAnn schemes (RecGroup.openTyVarsAux d Xs bindings)
  (body.openTyVarsAux d Xs)`.
- `eraseTyAnnots`: **KEEP schemes**, erase the rest —
  `letRecAnn schemes (RecGroup.eraseTyAnnots bindings) body.eraseTyAnnots`.
  (This is the whole point: the recursion schemes are load-bearing for typeability,
  so unlike `lambda`/`letIn` annotations they are NOT dropped. Being closed + WF,
  they are opening-invariant, so `Expr.eraseTyAnnots_openBoundTyVars` extends with a
  trivial `letRecAnn` case.)
- `tyFreeVars`: `(schemes.flatMap (·.body.freeVars)) ++ RecGroup.tyFreeVars bindings
  ++ body.tyFreeVars` (schemes contribute their free vars, like `letIn`'s `σ`).
- `Expr.size`/`sizeRecGroup`: mirror `letRec` (size over bindings + body; schemes
  add 0 or a constant — match whatever makes `decreasing_by` go through).

### Dynamics — mirror `Step.letRecUnfold` exactly, carrying schemes in the rewrap
```lean
| letRecAnnUnfold {schemes bindings body} :
    Step (.letRecAnn schemes bindings body)
      (body.substN 0 (bindings.map (fun e => Expr.letRecAnn schemes bindings e)))
```
Add the executable `step` arm and the `IsValue`/progress facts the same way
`letRec` does (never a value; always steps).

### Declarative rule — port `SpikeLetRecAnn.TypeOfLetRecAnn` to a `TypeOfHM` ctor
```lean
| letRecAnn {schemes : List PolyTy} {L : List Nat} :
    bindings.length = schemes.length →
    (∀ σ ∈ schemes, σ.WF) →
    (∀ Xs, FreshNames L (PolyTy.totalParams schemes) Xs →
        ∀ p ∈ bindings.zip (PolyTy.openGroup schemes Xs),
          TypeOfHM { ctx with env := schemes ++ ctx.env } p.1 p.2) →
    bodyCtx = { ctx with env := schemes ++ ctx.env } →
    TypeOfHM bodyCtx body ρ →
    TypeOfHM ctx (.letRecAnn schemes bindings body) ρ
```
Notes:
- The group is in scope at the FULL schemes in BOTH the RHSs and the body (this is
  the polymorphic recursion). There is **no generalisation step** — schemes are
  given. Use the existing `PolyTy.openGroup` / `PolyTy.totalParams` (already in
  Core; the disjoint-slice opening is CORRECT here — the §2.3 unsoundness was about
  generalisation, which we do not do).
- `rec_strong`: add the `letRecAnn` minor premise threading per-binding IHs over
  the cofinite `∀ Xs … ∀ p ∈ … zip …` shape (a per-pair IH — same trick as `letRec`,
  no bespoke motive needed).

### Other inductives — mirror `letRec`
- `IsTyErased.letRecAnn`: bindings erased + body erased, **schemes allowed** (kept).
- `WellScopedUnder.letRecAnn`, `AllMatchesExhaustive.letRecAnn`: mirror `letRec`
  over bindings + body (schemes impose nothing).

## Safety — the proofs to thread (mirror `letRec`; templates noted)
1. `typ_subst_preservation` `letRecAnn` case: **port `SpikeLetRecAnn.TypeOfLetRecAnn.typ_subst`.**
   It needs only `PolyTy.WF.substFvar`, `PolyTy.totalParams_map_substFvar`,
   `PolyTy.openGroup_map_substFvar` (all already in Core), and the IH. NO
   `genGroup_renameG` freshening (schemes are given) — strictly easier than `letRec`.
2. `weaken_env` `letRecAnn` case: **port `SpikeLetRecAnn.TypeOfLetRecAnn.weaken_env_front`.**
   Cofinite + ctx-free schemes ⇒ delegate each RHS/body to the IH; no `L` growth.
3. `subst_lemma(_many)`: mirror `letRec` (schemes carried unchanged; they mention no
   term vars).
4. Erasure: `erase_preserves_typing` `letRecAnn` case — re-apply `TypeOfHM.letRecAnn`
   with the SAME schemes, IHs for the cofinite RHSs + body. The cofinite openings are
   untouched by erasure (schemes kept; `RecGroup.eraseTyAnnots_eq_map` for the RHSs).
5. Preservation `letRecAnnUnfold` case (**the error-prone one — go carefully**):
   mirror `letRec`'s `letRecUnfold`. Key fact: each rewrapped
   `letRecAnn schemes bindings eⱼ` has scheme `σⱼ` (`HasScheme`) — re-apply the rule
   with body `eⱼ` typed at a fresh opening of `σⱼ` (this is DIRECT here: `eⱼ` already
   types at `σⱼ`'s opening by the cofinite premise — no generalisation needed, unlike
   `letRec`'s `rewrap_hasScheme`). Then `subst_lemma_many` discharges the body.
   Mind the `substN 0` de-Bruijn shifting (the rewrapped bindings re-bind the group).
6. `Step.preserves_isTyErased` / `preserves_exhaustive`: new `letRecAnn` case (the
   unfold result is a `substN` of erased/exhaustive pieces) — mirror `letRec`.

## v1 scope (do NOT exceed; these are deliberate deferrals)
- **All-annotated groups only.** No mixed annotated/unannotated groups (a genuine
  later Core rule; cannot be done by elaboration — out of scope here).
- **`rigid = []` / closed schemes.** No scoped type variables flowing into the
  group from enclosing scopes. This is what makes erasure keep schemes verbatim with
  no skolemisation. Do NOT add scoped-var opening for schemes.
- Do not touch `InferW.lean` (inference is the next step).

## Workflow / guardrails (the discipline that worked for the monomorphic `letRec`)
- **Lock-then-thread.** First add the node + all structural-function clauses + the
  `Step` rule + the `TypeOfHM.letRecAnn` rule + `rec_strong` and get the file
  ELABORATING (definitions compile). Port the spike's `polyRec`/`scoped` witnesses
  as a smoke test that the rule shape is right BEFORE threading the big safety proofs.
- **NEVER `sorry`/`admit`/`axiom`/`native_decide`.** Never weaken a headline
  statement. If a proof genuinely needs a Core *statement* change (e.g. an existing
  lemma's signature), **STOP and report** — that is how the §2.3 bug was caught.
- If the **preservation rewrap** or **`substN` shifting** (#5) does not yield after a
  real attempt, STOP and report with the exact stuck goal — do not hack around it.
- **Targeted builds only.** Use the `project-0-experiments-lean-lsp` MCP for
  diagnostics (`lean_diagnostic_messages`), goals (`lean_goal`), and **axiom checks
  (`lean_verify`)**. The whole project is broken (`Filterings.lean`); never
  whole-project build. Lints/diagnostics are sufficient — do not run `lake build`
  unless a new import demands it.
- **Axiom-clean check.** `progress`/`preservation`/`erased_type_safety` and any new
  headline `letRecAnn` safety theorems must be `propext`/`Classical.choice`/`Quot.sound`
  only — verify via `lean_verify` (cross-check; the editor cache can be stale).

## Deliverable
`Core.lean` extended with `letRecAnn` (node + rule + dynamics + full safety), green
and axiom-clean, with the spike's witnesses ported in (as a correctness smoke test).
Report: what landed, axiom audit output, and ANY place you had to stop.
