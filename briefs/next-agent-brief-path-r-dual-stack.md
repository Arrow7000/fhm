# Next-agent brief: Path R dual-stack metatheory

**Status:** Active (2026-08-11). Read this first when resuming FHM dual-stack / InferW work.  
**Authoritative product packaging:** `design-memo-bounds-preserving-elaboration.md`  
**This brief:** formalization *choice* Path R, WIP state, proof order, do-nots.

---

## 1. Product vision (unchanged)

Dual stack is real — not top-level-only sidecar:

1. **Lower** keeps BL on Core types / binder anns (including nested).
2. **InferW** is pure HM for *shape*: bounds-blind unify (`BL` ≡ bare `List` for unify only); never invents `lo`/`hi`; copies user BL anns through; empty slots → bare List.
3. **Bounds pass** (later product) synth/checks lengths; rewrites bare `List` → tight `BL`; user BL is demand.
4. **Pipeline never uses erase as packaging.** `eraseProgram` / `ofLower` are deprecated; Live may still run them — **do not** keep Live green at the expense of honest metatheory. Live can break.

Erase is a **function / theorem projection**, not a pipeline mutate step that destroys nested BL.

---

## 2. Path R vs Path B (locked: **Path R**)

| | **Path R (chosen)** | Path B (rejected for TypeOf) |
|--|---------------------|------------------------------|
| `TypeOf*` | Golden pure HM: **structural** pins, **no** BL ≡ List | TypeOf itself bounds-blind |
| Infer | Dirty: bounds-blind unify; keeps BL on elaboratum | Same executable story |
| Infer ⇒ TypeOf | **Residual bridge** after erase | More direct on same trees |

**Path R residual soundness (shape):**

```text
Infer … e ↝ eOut, τ
  ⇒  TypeOfElabHM
        (S.onCtx ctx).eraseBounds
        (eOut.substTyFvars S).eraseBounds
        (Ty.eraseBounds τ)
```

Source soundness:

```text
  ⇒  TypeOfHM (S.onCtx ctx).eraseBounds e.eraseBounds (Ty.eraseBounds τ)
```

**Why erase the term too:** structural Pins mean a binder ann `: BL …` forces the rule-internal type to be that BL tree. Pure TypeOf cannot treat “ann says BL, HM shape is List” the way Infer can. Residual TypeOf judges the **erase-projected** elaboratum/source.

**Ann preservation is separate** (product honesty), not residual TypeOf:

- Real semi-elaborated AST still carries BL for the bounds pass.
- Theorems: `Expr.UserAnnsCopied` / `Infer.preservesAnns`.

**Quotients:** moral quotient via `eraseBounds` / `AgreesHM` only. Do **not** introduce Lean `Quot Ty`.

**False under Option A / Path R (do not re-prove):**

- `Unifies` ⇒ structural tree equality  
- `FactorsHM.to_structural` (deleted)  
- Structural `UnifyRel.greatest` / `greatest_lc` / `greatest_K` as truth — use `*_factors` / `FactorsHM` only  

---

## 3. Code map (where things live)

| Piece | Location |
|-------|----------|
| `Ty.eraseBounds`, `PolyTy.eraseBounds`, `Expr.eraseBounds`, `Env`/`Ctx.eraseBounds` | `FHM/Core.lean` |
| Structural `Option.Pins` | `FHM/Core.lean` (Path R restored; not erase-equality) |
| `AgreesHM` / `Unifies` / `FactorsHM` / `UnifyRel` | `FHM/InferW.lean` |
| Residual `Infer.sound` / `sourceSound` / packing `*_erase` | `FHM/InferW.lean` (`sorry -- PathR`) |
| `UserAnnsCopied` / `Infer.preservesAnns` | `FHM/InferW.lean` |
| `CompleteAt` / `complete'` residual TypeOf hyps | `FHM/InferW.lean` (bodies fenced) |
| Surface residual headlines | `FHM/SurfaceBridge.lean` |
| `WellTyped` residual | `FHM/Headlines.lean` |
| Product architecture | `briefs/design-memo-bounds-preserving-elaboration.md` |

Grep: `sorry -- PathR`, `PathR completeness`, `Path R`.

---

## 4. Infer elaboratum shapes (ann / packing)

| Infer rule | elaboratum head |
|------------|-----------------|
| `lambda` | `.lambda ann bodyOut` (same `ann`) |
| `letIn` none | `.letIn (some genScheme) (closeTyVars (subst … rhsOut)) bodyOut` |
| `letInAnn` | `.letIn (some σ) (closeTyVars (subst … rhsOut)) bodyOut` |
| **`letRec`** | **`Expr.letRecElab G anns …`** = nest of outer `letIn` wrappers over an **inner** `.letRec anns …` — **not** bare `.letRec` as `eOut` |

Any ann-preservation or packing statement must respect `letRecElab` and closed let RHS.

---

## 5. Proof farm order (do not scramble)

### Ready *after* small statement polish (see §6)

**Soundness cluster (prove first):**

1. Core: `Expr.eraseBounds` termination (or solid measure)  
2. Expr-level erase commute lemmas (`substTyFvars`, `openTyVars`, `closeTyVars`, `letRecElab`)  
3. `TypeOfElabHM.eraseBounds_of` / `TypeOfHM.eraseBounds_of`  
4. `onSubst_eraseBounds*`  
5. `Infer.sound` / `InferBranches.sound` / `InferRecGroup.sound`  
6. `Infer.sourceSound` (real branch/rec sourceSound statements if needed)  
7. packing `sound_letIn_erase` / `sound_letInAnn_erase`  
8. `Infer.preservesAnns` (after `UserAnnsCopied` matches elaborata)

### Defer

**Completeness** — top-level *statements* are residual-shaped (`CompleteAt`, `complete'` take `TypeOfHM … e.eraseBounds`), but:

- Proofs are a separate, larger campaign.
- Aux still has structural residue (e.g. `letRecFused_residual_setup` Mono/PolyTyped on non-erased terms).
- Completeness needs residual transport / MGU factoring / case tower; soundness lemmas feed it.
- **Order:** soundness → then residualize remaining complete aux → then completeness proofs.

**Operational bridge** (`runSafe`, progress/preservation with residual `WellTyped` on decorated `e`) — **does not** block `Infer.sound`. Separate design: residual TypeOf vs `Step` on real elaboratum. Fenced in Headlines; not part of soundness farm.

**Product Live ofLower** — after metatheory stable.

---

## 6. Pre-soundness checklist (statement level)

From 2026-08-11 audit + follow-up:

- [x] Path R Pins structural; residual Infer.sound statements  
- [x] Completeness top-level residual hyps; bodies fenced  
- [x] False structural MGU recovery deleted/fenced  
- [x] **`UserAnnsCopied`**: `letRec` → `letRecElab`; let RHS not full zip (re-verify once when proving `preservesAnns`)  
- [x] **Expr erase commute statements** (Core + InferW; bodies `sorry -- PathR`):
  - Core: `eraseBounds_idem`, `eraseBounds_substTyFvar(s)`, `eraseBounds_openTyVars`,
    `eraseBounds_openBoundTyVars`, ctor unfolds  
  - InferW: `eraseBounds_closeTyVars`, `eraseBounds_letRecElab`  
- [x] **Branch/rec residual `sourceSound` statements** — real (mirror `.sound`; TypeOfHM /
  TypeOfMatchBranch on **source** after erase). No vacuous `True` stubs.  
- [x] **Deleted** `UserAnnsCopied.eraseBounds_ann_payloads` — vacuous; under
  `UserAnnsCopied`, shared anns are definitionally equal, so post-subst erase
  agreement is congruence. Product honesty is `Infer.preservesAnns` alone.  
- [x] **`Expr.eraseBounds` termination** — `sizeOf`; match uses `pe.2` under list mem  
- [x] **Expr erase commute proofs** — Core (`idem`/`subst`/`open*`/ctors) + InferW
  (`closeTyVars`/`letRecElab`); sequential farm (Core before InferW)
- [x] **`Ctx.eraseBounds` projects `CtorEnv` too** — earlier "ctors unchanged /
  prelude NoBL" made residual `TypeOf*.eraseBounds_of` **false** when a ctor
  field carries `BL` (structural `InstantiatesBy` cannot relate BL template to
  erased List). Now `Ctor.eraseBounds` / `CtorEnv.eraseBounds`; `WellTyped`
  uses erased ctors.  

- [x] **`TypeOfElabHM.eraseBounds_of` / `TypeOfHM.eraseBounds_of`** proved (after CtorEnv erase)
- [x] **`onSubst_eraseBounds*`** (Elab + HM, primed + fixed) proved
- [x] **Packing** `sound_letIn_erase` / `sound_letInAnn_erase` proved
- [x] **`Infer.preservesAnns`** proved (+ `InferBranches.preservesAnns`). `UserAnnsCopied.letRec`
  restated: group `anns` + body only (bindings not full zip after subst/close — same as let RHS)

- [x] **`Infer.sound` / `InferBranches.sound` / `InferRecGroup.sound`** residual mutual **proved**
  (prims…letInAnn, match/branches, RecGroup mono/poly, letRec packing via
  `letRecElab_sound` at erased ctx)

**Farm next** (InferW only; sequential): residual **`sourceSound` trio**
(`Infer` / `InferBranches` / `InferRecGroup`). Not completeness, not runSafe /
operational residual `WellTyped`.

---

## 6.1 Documentation policy (do not multiply)

**Read for new sessions (only these):**

1. **This brief** — Path R formalization + proof order + checklist  
2. **`design-memo-bounds-preserving-elaboration.md`** — product dual-stack packaging (pipeline, not every failed proof approach)

**Do not** require reading historical elaborator diagnosis briefs, old next-agent
briefs for superseded packaging, or QuantitativeExperiments notes unless the task
explicitly resurrects that product path.

Other files under `briefs/` are **archive / optional background**. Prefer updating
*this* brief’s checklist over creating `next-agent-brief-path-r-part-2.md`.
When Path R soundness lands, fold the resume paragraph into a short “done /
next” section here rather than a new memo.

---

## 7. Work style (project convention)

- Orchestrator writes **defs / inductives / theorem statements**; leave `sorry`.  
- **Proof workhorse subagents** discharge proofs (and termination).  
- If unprovable as stated → report; orchestrator restates.  
- Prefer **lean-lsp** diagnostics for edit loop; `lake build` when expecting a clean full target.  
- Do not fill main context with proof grit.

---

## 8. Session principles (user)

- Dual stack was betrayed by top-bindings-only packaging — never again.  
- Principled metatheory first; no superficial Live-preserving cheats.  
- TypeOf stays pure HM (Path R); Infer accounts for BL-world; residual bridge is honest tax.  

---

## 9. One-paragraph resume prompt

> Continue Path R dual-stack metatheory in FHM. Read `briefs/next-agent-brief-path-r-dual-stack.md`. Product dual-stack packaging: `design-memo-bounds-preserving-elaboration.md`. Do **not** farm completeness or runSafe yet. Finish §6 checklist (ann relation, erase commute statements, eraseBounds termination), then farm residual **soundness** proofs only (`Infer.sound`, `eraseBounds_of`, packing, `preservesAnns`). Structural Pins; residual TypeOf via `eraseBounds` on ctx/term/result; no `FactorsHM.to_structural`. Live ofLower out of scope.

---

## 10. Related greps

```bash
rg -n "sorry -- PathR|PathR completeness|UserAnnsCopied|letRecElab|CompleteAt|Infer.sound " FHM/
rg -n "FactorsHM.to_structural|greatest_factors|structural residual factoring" FHM/InferW.lean
```
