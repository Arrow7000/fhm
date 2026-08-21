# Adversarial review of `design-memo-erasure-migration.md`

The thesis is right: **the n² is an elaboration artifact, erasure is what kills
it, and erasure does not require CEK.** Keeping `SmallStep.Step` on `erase e` is
a coherent product decision. The live pipeline already runs `Step`
(`Live.lean` 257, `evaluateUnsafe`); `CekMachine.lean` is an isolated leaf
(nothing imports it).

The memo oversells two things: (1) that the DM cut is what *causes* the n² to
die, and (2) that dropping CEK is cheap on the *proof* side. Stage 1 already
*is* `TypeOfHM` type-safety. Dropping it means re-proving Mini-ML preservation
for `TypeOfHM`/`Step`, including a `TypeOfHM` port of
`TypeOfElabHM.rewrap_hasScheme_mono` (`Core.lean` 9247) for `letRecUnfold`.
That is real work you are choosing instead of a surface rewire to `StepM`.

Do not reopen the feature design (response-6). This review is only the
dynamics-target claim.

---

## 1. Verdict on the central claims

| Claim | Verdict |
|---|---|
| n² is `letRecElabNest` (both arms copy the group) | **TRUE** (`InferW.lean` 2486–2498) |
| Nest exists because type-passing puts generalisation in the term | **TRUE** as *why Infer emits it* |
| Dropping elaboration (no `eOut` / no nest) kills that n² | **TRUE** |
| The DM cut is what kills the n² | **FALSE** as causation — see §2 |
| `Step` never inspects types; `substN`’s type-touch is `instTy` | **TRUE** (`Core.lean` 1435–1523, 1331–1334) |
| `instTy [] = id` | **TRUE** (`Expr.instTy_nil`, `Core.lean` 1309) |
| Therefore `Step` *reduces* erased terms with no type computation | **TRUE** operationally |
| Therefore `Step` is already a *safe* dynamics for `TypeOfHM` | **FALSE** — safety is still only proved for `TypeOfElabHM` (`progress` 8471, `preservation` 9442, `type_safety` 10074). Memo §5.2 admits this; §0/§3.3 blur it. |
| Types are erasable (no typecase, match on ctor names, primops by name) | **TRUE** |
| Uniform erase + DM cut is the response-6 design | **TRUE** (not re-litigated here) |
| `Infer.sound : Infer e τ → TypeOfHM (erase e) τ` is the same hard core as the CEK plan | **TRUE** |
| Dropping CEK costs only the Mini-ML `TypeOfHM`/`Step` metatheory, which is smaller than CEK | **NOT-ESTABLISHED** — CEK’s `TypeOfHM` safety is *already proved*. You are discarding it. |
| §2.2: the cut is exactly “the programs uniform erasure cannot support anyway” | **FALSE** for self-contained poly rec — see §3 |

---

## 2. The cascade is one valid path, not the only one

Memo §0/§3: cut → annotations inert → erase → no type-passing → no `tyArgs` →
no gen-in-the-term → no nest → no elaboration.

**The n² dies when Infer stops emitting `letRecElabNest`.** That happens as
soon as the runnable term is the source (or `erase e`) typed by `TypeOfHM`,
rather than an `eOut` typed by `TypeOfElabHM`. Existential `TypeOfHM.var`
(`Core.lean` 3373) does not need `tyArgs` in the term.

A milder erase (drop λ ascriptions + zero `tyArgs`, **keep** `WF` `letRec`
anns) plus `TypeOfHM` + `Step` would also kill the nest, and would *keep*
self-contained poly rec (Stage 1 `IsErased` already does that). The DM cut is
what makes *uniform* drop of `letRec` anns sound. It is not what makes the nest
disappear.

Write the chain as:

1. **Uniform erase of `letRec` anns** needs the DM cut (response-6). Owner
   signed that.
2. **Killing the nest** needs “don’t elaborate” (`TypeOfHM` of `erase e` is
   what you run).
3. (1) implies we *can* do (2) with a single `erase` and no leftover
   load-bearing anns. That is the chosen design, not a uniqueness proof.

§3.4’s parenthetical (“this step is a consequence of erasure, not of the
cut — the cut is what makes erasure coherent”) is the accurate sentence.
The TL;DR bullet that reads as cut → no n² is the sloppy one.

---

## 3. “Erasure cannot support these programs anyway” is too strong

§2.2 lists three Infer-rejected classes and says they are “the class of
programs that **uniform erasure cannot support anyway**.”

- (1) mixed-group sibling poly, (2) ground-pin + poly body: **uniform** drop
  of `letRec` anns cannot support them. **Selective** keep of `WF` anns can
  (current `IsErased.letRec`). That is the C6 point from the review trail.
  The cut is a policy, not a physics constraint.
- (3) I1 (dangling tyvar *and* in-group poly rec): actually impossible
  without type-passing. Fine.

Don’t justify the cut twice. Owner already signed textbook DM. Self-contained
poly rec is out because of uniform erase, not because `Step` cannot run it.

---

## 4. `Step` on erased terms: reduction vs safety

### 4.1 Reduction — the memo is right

Every `Step` constructor is subst/congruence/δ. None read `ann`/`tyArgs`/
schemes. The only type walk is

```
(vs[i - k]).instTy tyArgs          -- Core.lean:1333
```

On `erase e`, `tyArgs = []`, and `Expr.instTy_nil` is `e.instTy [] = e`.
`letReduce` / `beta` / `matchReduce` / `letRecUnfold` do not need
`instTyAux` depth-shielding. Orphan tyvars cannot exist if there are no type
`bvar`s in the term. §3.2–3.3 hold as *operational* claims.

Q1 (dynamics only on erased terms) is **load-bearing**, not cosmetic. `Step`
on an *annotated* `let f : ∀a. a→a = λ(x:a). x in f 3` substitutes the
dangling-ascription λ; `TypeOfHM` of that closed rhs fails `paramTy.IsLC`.
That is the orphan problem. Erase at the pipeline boundary, and keep
`type_safety` quantified over erased terms (`IsErased`-style). Do not try to
prove `Step` preservation for arbitrary annotated terms without bringing
type-passing back.

### 4.2 Safety — not free, and under-named

`TypeOfElabHM` preservation of `letRecUnfold` (`Core.lean` 1478–1480) uses
the rewrap lemmas:

- `TypeOfElabHM.rec_rewrap_typed` (`Core.lean` 9184)
- `TypeOfElabHM.rewrap_hasScheme_mono` (`Core.lean` 9247)

Unfold substitutes, for each member `j`, the term
`letRec anns bindings eⱼ` — a **full copy of the group** with body = that
RHS. Preservation needs that copy to inhabit the member’s **body scheme**
(`genGroup G τ` under the cut). That lemma does not exist for `TypeOfHM`.
`CekMachine.recclo_body_typed` is the environment-machine analogue; it does
not apply to `substN`.

`letReduce` preservation needs: body typed under scheme `M`, rhs satisfies
`GeneralisesTo` at `M`, conclude `TypeOfHM (body.substN 0 [rhs]) τ`. On
erased terms `openBoundTyVars none = id`. The occurrence-at-instance lemma
is `GeneralisesTo_inst_ann` (`CekMachine.lean` 787) — **in the leaf you are
not importing**. Move it (and friends) into `Core`/`InferW` rather than
depending on `CekMachine`.

Progress needs canonical forms for `TypeOfHM` (arrow value is a λ, …). Same
shape as `TypeOfElabHM.progress`; not already proved.

§5.2 should name **rewrap/HasScheme for `TypeOfHM`** as a checkpoint, not
bury it under “substitution lemma, cofinite letIn/letRec.” That *is* the
letRec case.

### 4.3 Operational copies ≠ elaboration n²

`letRecUnfold` is already

```
body.substN 0 (bindings.map (fun e => Expr.letRec anns bindings e))
```

n members × a full group per member **per step**. That is substitution
semantics of mutual rec (`fix`), not the Infer nest. Erasure does **not**
remove it. CEK’s `forceRecclo`/`bindGroup` shares one group in the
environment and does not copy it into the term.

The owner’s goal (3) was the **elaborator** blowup (typechecker/proof AST).
Killing that is enough to drop CEK *if that was the only reason CEK existed*.
Do not write “the n² is gone” without saying **compile-time nest**, or
someone will think `letRecUnfold` got cheaper.

If a large mutually-recursive group ever becomes a product concern, that is
the remaining argument *for* CEK. For FHM-scale groups it is irrelevant.

---

## 5. Cost of dropping CEK (the memo is backwards here)

§3.7: adopting CEK “adds a machine … for no benefit over keeping `Step`.”
§5.2: Mini-ML metatheory is “smaller than the CEK metatheory it replaces.”

**CEK Stage 1 is done.** `progress` / `preservation` / `type_safety` /
`stepM_deterministic` for `TypeOfHM` (on `IsErased` terms) are sorry-free.
Nothing in the tree uses them. The *live* evaluator is `Step`.

So the real trade:

| Keep `Step` | Adopt CEK |
|---|---|
| Live path (`Live` / `EvaluateUnsafe` / `Headlines.runSafe`) already matches | Rewire those to `StepM` (mechanical, D7 PatComp too) |
| Re-prove `TypeOfHM` subst / progress / preservation / rewrap | Already have them |
| Runtime unfold copies the rec group | Env sharing |
| One operational model in the product | Two models (proved CEK + still-present `Step` until deletion) |

**Product:** keep `Step`. Do not put an unused machine on the evaluator path.
**Proof budget:** you are *paying* Mini-ML `TypeOfHM`/`Step`, not saving it.
The saving is “don’t maintain CEK in the surface.” Say that. “Dropping CEK is
cheap because Infer.sound is the same” is true of **Stage 2** and false of
**Stage 3**.

Leaving `CekMachine.lean` as an isolated leaf is fine ( sunk cost, no import
cycle). Do not cite it as the typing oracle while proving `Step` lemmas — move
the reusable bits (`GeneralisesTo_inst_ann`, `openTyVars_eq_self_of_erased`
once `erase` lives in `Core`).

---

## 6. Plan / sharp edges

**§6.1 `eraseBounds` threading** — TRUE and must be in the theorem statement
from day one. `TypeOfHM` has no `bl` inhabitants.

**§6.2 `erase (openTyVarsAux d Xs e) = erase e` for all `d`** — TRUE, needed
for C4. `var i _ → []` is what makes the `var` case go.

**§6.3 group cofinite lift** — TRUE, new, long pole of Infer.sound. No current
`TypeOfElabHM` analogue (that relation is not cofinite in the same way on
`letRec`). Shared with the `MonoTyped` half of CEK; not copy-pasteable from
`recclo_body_typed`.

**§6.4 `RecGroup.rigidVars`** — still right: after the cut, ceiling schemes
are in the *body* env, so `genGroupVars`’s `env.freeVars` filter must keep
outer `C` rigid. Confirm with `∀a. a → C` before deleting the ann term from
`rigidVars`.

**§5.3 ordering** — Infer still has `eOut` today. Step 2 (“change `letRec`,
`Infer.sound` sorry”) vs step 6 (drop `eOut`) is ambiguous. Either:

- keep `eOut` through Infer.sound and ignore it in the conclusion
  (`TypeOfHM (erase e)` of the *input*), or
- drop `eOut` in step 2 with the `letRec` change.

Pick one. Proving soundness against `erase eIn` while Infer still builds
`eOut` is the smaller diff.

**§7 Q2 rename** — ignore.

**Live path today:** parse → infer → **elaborate** → `evaluateUnsafe`
(`Live.lean` 20, 257). The rewire is “elaborate → erase”, not a new reducer.
`Headlines.WellTyped` must become `TypeOfHM ⟨[],ctors⟩ (erase e) τ` as the
memo says. `PatComp` adequacy is currently against `Step` on *elaborated*
bodies (`PatComp.lean` 29–34); restating on erased bodies is the actual
delta, not “Step vs StepM.”

---

## 7. Things the memo got right

- Owner goals vs CEK-as-means. CEK was never the feature.
- Why type-passing existed (orphan bvars + poly rec under substitution).
- `letRecElabNest` is both arms, Θ(n²) AST, generalisation not `.poly`-only.
- `Step` does not branch on types; `instTy []` is identity.
- Uniform `erase` as specified (including `var` zeroing).
- Coherence = Infer.sound, same as response-6; CEK vs Step does not change it.
- Dynamics theorem restricted to erased terms (Q1).
- Cofinite subst is the delicate case; `substN_openTyVarsAux_comm` survives.
- Bounds walkers still on source, still must open (response-6).
- Sorrys in `Bounds/Pipeline` are unrelated.

---

## 8. What must change in the memo before implementation

1. **Split “no n²”:** compile-time nest (gone) vs `letRecUnfold` copies
   (still there). Cut does not kill the nest; dropping `eOut` does.
2. **§2.2:** drop “erasure cannot support anyway” for self-contained poly rec.
3. **§3.3 / §0:** “`Step` already runs erased terms” ≠ “`TypeOfHM`/`Step` is
   already type-safe.” Safety is §5.2.
4. **§5.2:** name `TypeOfHM.rewrap_hasScheme_mono` (port of `Core.lean` 9247)
   as the `letRecUnfold` obligation; move `GeneralisesTo_inst*` out of
   `CekMachine`.
5. **§3.7:** keep-Step because the **product already evaluates with `Step`**,
   not because it avoids proof. Stage 3 is extra Mini-ML work.
6. **§5.3:** when `eOut` dies relative to Infer.sound.

Feature design (response-6): ceiling `Generalizes (genGroup G τ) σ_opened`,
`RecSpec.init` all `.mono`, no `consPoly`, body env = annotations, pipeline
`lower → Infer+bounds → erase → run`. Unchanged. Do not spend another
revision on the cut.

---

## 9. Bottom line

Implement this, with the corrections above. The dynamics-target change is
justified by the *live* evaluator already being `Step` and the n² being
Infer’s nest. It is **not** justified as a proof-work reduction versus the
CEK you already have. Stage 2 (Infer.letRec + erase + Infer.sound) is still
the long pole and is identical either way — start there; the `TypeOfHM`/`Step`
metatheory is Stage 3 and has a template in `TypeOfElabHM` plus a rewrap
lemma you must port.
