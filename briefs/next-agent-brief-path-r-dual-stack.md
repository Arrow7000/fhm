# Next-agent brief: Path R dual-stack metatheory

**Status:** Active (2026-08-12). Read this first when resuming FHM dual-stack / InferW work.  
**Authoritative product packaging:** `design-memo-bounds-preserving-elaboration.md`  
**This brief:** formalization *choice* Path R, WIP state, proof order, do-nots.

---

## 0. Where we are (2026-08-12) — start here

### Done (proved, no PathR sorry)

| Cluster | Status |
|---------|--------|
| `Expr.eraseBounds` termination (`sizeOf`) | ✅ |
| Expr erase commute (Core + InferW, incl. `closeTyVars` / `letRecElab`) | ✅ |
| `Ctor.eraseBounds` / `CtorEnv.eraseBounds`; `Ctx.eraseBounds` erases **env + ctors** | ✅ |
| `TypeOfElabHM.eraseBounds_of` / `TypeOfHM.eraseBounds_of` | ✅ |
| `onSubst_eraseBounds*` (Elab + HM) | ✅ |
| Packing `Infer.sound_letIn_erase` / `sound_letInAnn_erase` | ✅ |
| `Infer.preservesAnns` (+ `InferBranches.preservesAnns`) | ✅ |
| **`Infer.sound` / `InferBranches.sound` / `InferRecGroup.sound`** residual mutual | ✅ **fully closed** |
| **`InferBranches.sourceSound`** (cons + consWild) | ✅ |
| **`InferRecGroup.sourceSound`** (consMono + consPoly) | ✅ |
| Most of **`Infer.sourceSound`** (prims…match_) | ✅ |

### In progress — **one sorry left for residual soundness**

```text
Infer.sourceSound  | letRec   —  sorry -- PathR letRec
  FHM/InferW.lean  ~line 12966 (grep: "sorry -- PathR letRec")
```

All other residual **soundness** PathR work is done. Completeness / runSafe still fenced (out of scope).

### Next farm (in order)

1. **Finish `Infer.sourceSound` `letRec`** — only open residual soundness goal.  
   Mirror dual of `Infer.sound` letRec, but **`TypeOfHM.letRec` on source** (not elaboratum `letRecElab`):
   - Use `InferRecGroup.sourceSound` mono/poly halves on **source** bindings (already residual).
   - Body: `Infer.sourceSound` under residual bodyCtx / bodyScheme.
   - Pack with `TypeOfHM.letRec` + residual `RecSpecs.WF` / `MonoTyped` / `PolyTyped` on **erased source** bindings (renameG G↦Xs etc. as structural letRec needs).
   - Comment at sorry: “dual of Infer.sound's letRecElab residual packing.”
2. Optional: thin corollaries that say `via sourceSound` if still sorry after (1).
3. **Defer:** completeness (`sorry -- PathR completeness`), runSafe / residual `WellTyped` ops bridge (Headlines).

### Recent commits (git log)

```text
3bccd84 Close residual Infer.sound mutual (letRec packing).
a500f0b Prove residual InferRecGroup.sound (consMono/consPoly).
9185101 Prove residual InferBranches.sound and Infer.sound match_.
9e51bbf Advance residual Infer.sound; drop false structural MGU stubs.
7d0ebb7 Land Path R residual soundness infrastructure …
c021091 Restate dual-stack Infer metatheory as Path R residual bridge.
```

Plus any WIP commit of `sourceSound` after this brief update.

### Sequential-edit rule

**Do not edit Core and InferW in parallel** (InferW reloads after Core). Farm one file at a time. Core is currently stable for residual work.

### Do not re-prove (false under Path R)

- `Unifies` ⇒ structural tree equality  
- `FactorsHM.to_structural` (deleted)  
- Structural `UnifyRel.greatest` / `greatest_lc` — use `*_factors` / `FactorsHM` only  
- Intentionally unprovable `*_structural_FALSE` theorems were **deleted**; comments remain  

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

**Path R residual elaboratum soundness:**

```text
Infer … e ↝ eOut, τ
  ⇒  TypeOfElabHM
        (S.onCtx ctx).eraseBounds
        (eOut.substTyFvars S).eraseBounds
        (Ty.eraseBounds τ)
```

**Source soundness:**

```text
  ⇒  TypeOfHM (S.onCtx ctx).eraseBounds e.eraseBounds (Ty.eraseBounds τ)
```

**Why erase the term too:** structural Pins mean a binder ann `: BL …` forces the rule-internal type to be that BL tree. Pure TypeOf cannot treat “ann says BL, HM shape is List” the way Infer can. Residual TypeOf judges the **erase-projected** elaboratum/source.

**Why erase CtorEnv too:** structural `InstantiatesBy` has no BL→List rule. Residual `TypeOf*` needs erased ctor field templates. `Ctx.eraseBounds` projects env **and** ctors (`CtorEnv.eraseBounds`).

**Ann preservation is separate** (product honesty), not residual TypeOf:

- Real semi-elaborated AST still carries BL for the bounds pass.
- Theorems: `Expr.UserAnnsCopied` / `Infer.preservesAnns` (proved).
- `UserAnnsCopied.letRec`: group **anns** + body only (bindings not full zip after subst/close — same as let RHS).

**Quotients:** moral quotient via `eraseBounds` / `AgreesHM` only. Do **not** introduce Lean `Quot Ty`.

---

## 3. Code map

| Piece | Location | Status |
|-------|----------|--------|
| `Ty`/`PolyTy`/`Expr`/`Env`/`Ctor`/`CtorEnv`/`Ctx.eraseBounds` | `FHM/Core.lean` | ✅ |
| Structural `Option.Pins` | `FHM/Core.lean` | ✅ |
| `AgreesHM` / `Unifies` / `FactorsHM` / `UnifyRel.*_factors` | `FHM/InferW.lean` | ✅ |
| Residual `Infer.sound` mutual | `FHM/InferW.lean` ~9128+ | ✅ proved |
| Residual `sourceSound` mutual | `FHM/InferW.lean` ~12287+ | ⚠️ **letRec only open** |
| `UserAnnsCopied` / `Infer.preservesAnns` | `FHM/InferW.lean` | ✅ |
| Packing / eraseBounds_of / onSubst residual | `FHM/InferW.lean` | ✅ |
| Completeness residual hyps | `FHM/InferW.lean` | statements OK; bodies fenced |
| Residual `WellTyped` / runSafe | `FHM/Headlines.lean` | deferred (ops bridge) |
| Product architecture | `briefs/design-memo-bounds-preserving-elaboration.md` | — |

```bash
rg -n "sorry -- PathR letRec|sorry -- PathR$|PathR completeness" FHM/InferW.lean
rg -n "theorem Infer\.sourceSound|theorem Infer\.sound " FHM/InferW.lean
```

---

## 4. Infer elaboratum shapes (ann / packing)

| Infer rule | elaboratum head |
|------------|-----------------|
| `lambda` | `.lambda ann bodyOut` (same `ann`) |
| `letIn` none | `.letIn (some genScheme) (closeTyVars …) bodyOut` |
| `letInAnn` | `.letIn (some σ) (closeTyVars …) bodyOut` |
| **`letRec`** | **`Expr.letRecElab G anns …`** — **not** bare `.letRec` as `eOut` |

Source soundness types the **source** `.letRec` after erase, not the elaboratum nest.

---

## 5. Proof farm order

### Residual soundness (almost done)

1. ~~Core eraseBounds termination~~ ✅  
2. ~~Erase commute~~ ✅  
3. ~~`TypeOf*.eraseBounds_of` / onSubst / packing / preservesAnns~~ ✅  
4. ~~`Infer.sound` mutual~~ ✅  
5. **`Infer.sourceSound` letRec** ← **you are here**  
6. (Branches/RecGroup sourceSound already ✅)

### Defer

**Completeness** — residual-shaped statements; large separate campaign after soundness.

**Operational bridge** (`runSafe`, residual `WellTyped` vs `Step` on decorated terms) — Headlines; not part of Infer residual farm.

**Product Live ofLower** — after metatheory stable.

---

## 6. Strategy notes that worked (for the next agent)

- **Scaffolding** for residual proofs mirrors structural Infer.sound: K, frontier, LC, BelowFvars, `eOut_avoid`, `dom_avoid`, then residual TypeOf rebuild.
- **`UnifyRel.unifies`** only gives **erase-equality** (`AgreesHM`), never tree equality.
- **Match / branches (elaboratum):** residual `BranchCtorSpec` via `CtorEnv.eraseBounds_get?` + `InstantiatesBy.forall2_eraseBounds`.
- **letRec elaboratum sound:** residual mono/poly from `InferRecGroup.sound` → `Expr.letRecElab_sound` at **erased ctx** → `Expr.eraseBounds_letRecElab`.
- **sourceSound letRec (open):** dual packing but `TypeOfHM.letRec` on **source** erased bindings; use already-proved `InferRecGroup.sourceSound`.
- Farm **one case at a time** when context is large; commit checkpoints often.
- **No vacuous `True` theorem statements.**

---

## 6.1 Documentation policy (do not multiply)

**Read for new sessions (only these):**

1. **This brief** — Path R formalization + proof order + checklist  
2. **`design-memo-bounds-preserving-elaboration.md`** — product dual-stack packaging  

Prefer updating *this* brief over creating `next-agent-brief-path-r-part-2.md`.

---

## 7. Work style (project convention)

- Orchestrator writes **defs / inductives / theorem statements**; leave `sorry`.  
- Proof subagents discharge proofs (and termination).  
- If unprovable as stated → report; orchestrator restates.  
- Prefer **lean-lsp** diagnostics; `lake build` for full targets.  
- Do not fill main context with proof grit.  
- **Sequential Core then InferW** (no parallel edits).

---

## 8. Session principles (user)

- Dual stack was betrayed by top-bindings-only packaging — never again.  
- Principled metatheory first; no superficial Live-preserving cheats.  
- TypeOf stays pure HM (Path R); Infer accounts for BL-world; residual bridge is honest tax.  

---

## 9. One-paragraph resume prompt

> Continue Path R dual-stack metatheory in FHM. Read `briefs/next-agent-brief-path-r-dual-stack.md` §0 first. Residual **Infer.sound** mutual is fully proved. Residual **sourceSound** is almost done: only `Infer.sourceSound` **letRec** remains (`sorry -- PathR letRec` in `FHM/InferW.lean`). Close that via `TypeOfHM.letRec` on erased **source** (use `InferRecGroup.sourceSound` mono/poly + body IH). Do **not** farm completeness or runSafe yet. Structural Pins; residual TypeOf via `eraseBounds` on ctx (incl. CtorEnv)/term/result; no structural MGU recovery. Live ofLower out of scope.

---

## 10. Related greps

```bash
rg -n "sorry -- PathR letRec|sorry -- PathR$|PathR completeness" FHM/InferW.lean
rg -n "theorem Infer\.(sound|sourceSound) |theorem InferBranches\.(sound|sourceSound)|theorem InferRecGroup\.(sound|sourceSound)" FHM/InferW.lean
rg -n "FactorsHM.to_structural|structural residual factoring" FHM/InferW.lean
```
