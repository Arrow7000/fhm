# Design memo: erasure on `Step` (the settled migration, revised)

**Status: settled design + revised execution plan.** Supersedes the *CEK* framing of
`cekmachine-design.md` (its Stage 1 machine description remains as historical record)
and the Stage 2 handover in `next-agent-brief-cek-stage2.md`. The *feature* design is
unchanged — it is exactly `feature-support-analysis-response-6.md`. What changes here
is only the **operational-semantics target**: we keep the existing substitution
semantics (`SmallStep.Step`) and run it on **erased** terms, instead of adopting the
CEK machine.

This memo is written to be read **cold** by an adversarial reviewer: it records the
full motivating history, why each architectural step was taken, and how one decision
— *monomorphic recursion inside `letRec` blocks* — cascades into a chain of
simplifications. The goal is that the reviewer can check every causal claim against
the code, not just against our summaries.

---

## 0. TL;DR

- **What was actually wanted** (the owner's real goals, in priority order): (1)
  *scoped type variables* usable everywhere, (2) *polymorphic recursion*, (3) *no
  O(n²) `letRec` elaboration blowup*. The CEK machine was **never** a goal in itself —
  it was believed to be the *only* way to achieve (3).
- **Why type-passing existed at all**: combining (1) scoped tyvars with (2)
  polymorphic recursion under a *substitution* operational semantics is what forced
  types into the term (`var i [tyArgs]`, `instTy`), which forced *elaboration*
  (writing generalisation into the term as the Λ-nest, hence n²), which forced a
  second typing relation (`TypeOfElabHM`) and a second soundness induction
  (`Infer.sourceSound`).
- **The one decision**: accept **Damas–Milner monomorphic recursion inside `letRec`
  blocks** (members used at a monotype inside the block; generalised to schemes for
  the *body*). This is the cut the owner has now signed off on.
- **The cascade that follows**: with mono-internal recursion the annotations are
  runtime-inert, so we **erase them before evaluation** → erasure dissolves the
  "orphan scoped tyvar" problem at its root → no type-passing → no `var.tyArgs` /
  `instTy` → no generalisation-in-the-term → no Λ-nest → **no n²** → no elaboration
  → no `TypeOfElabHM` / `sourceSound` / `eOut` / `closeTyVars` / `letRecElab*`.
- **The realisation that ends the CEK detour**: erasure is the load-bearing idea, and
  it is **separable from the choice of machine**. Types are fully erasable here (no
  type-based dispatch, `match` is on constructors, primops are monomorphic by name).
  The existing `SmallStep.Step` already reduces erased terms with **zero** type
  computation (its reduction rules never inspect types, and `substN`'s one type-touch
  is the identity on erased terms). So we keep `Step` and do not adopt the CEK
  machine. `FHM/CekMachine.lean` is left in place (it is a proven, isolated leaf).
- **What still has to be proved** (unchanged hard core): `Infer.sound : Infer e τ →
  TypeOfHM (erase e) τ`, plus one new-but-standard piece — the *term*-substitution
  and `Step`-preservation metatheory for `TypeOfHM` (which today exists only for
  `TypeOfElabHM`).

---

## 1. The motivating history (why we got here)

### 1.1 The two features, and the constraint

The owner wanted two *language* features and one *cost* removed:

1. **Scoped type variables, usable everywhere** — `let f : ∀a. a → a = λ(x : a). x in
   f 3`, i.e. `a` is lexically scoped and appears in inner annotations. (Haskell
   `ScopedTypeVariables`.)
2. **Polymorphic recursion** — a `let rec` member may be *used* at more than one type,
   by itself or by a sibling (e.g. `f (Cons x Nil)` where `f : ∀a. a → a`).
3. **No O(n²) `letRec` elaboration blowup** — the Λ-outside nest (see §1.2) that
   makes `letRec` elaboration quadratic.

Feature (3) is a *cost* to remove, not a feature; features (1) and (2) are the point.

### 1.2 Why combining (1) and (2) forced type-passing, and thus elaboration

The original architecture runs a **substitution** operational semantics
(`SmallStep.Step`, `FHM/Core.lean:1435`) in which *the term is the machine state*.
Under that semantics:

- **Scoped tyvars** are stored in the term as *dangling type `bvar`s*: `λ(x : a). x`
  inside `let f : ∀a. a → a = …` records `a` as `bvar 1` referring to the scheme
  binder. After `letReduce` substitutes the rhs into the body, that binder is gone —
  the `bvar` is **orphaned** (points past its binding site).
- **Polymorphic recursion** needs each *use* of a polymorphic member to be at a
  concrete instantiation. Under "the term is the machine state", the only place to
  record that instantiation is in the term: `var i [tyArgs]`.

The original design's answer to both was **type-passing**: keep types in the term, and
make reduction do type substitution. `Expr.instTy`/`instTyAux` (`Core.lean:1125/1172`)
push instantiation types through the term, and `Expr.substN` (`Core.lean:1330`) applies
`instTy tyArgs` when substituting a value into a `var i tyArgs` use (`Core.lean:1333`).
The "depth-shielding" of `instTyAux`/`openTyVarsAux` is precisely the bookkeeping that
keeps the dangling scoped-tyvar `bvar`s in range through substitution.

**That choice is load-bearing for the n².** Once types live in the term, *generalisation*
must also be manufactured into the term: for a `letRec`, the body must see each member
at its generalised scheme, so each member is wrapped in a term-level Λ by
`Expr.letRecElabNest` (`FHM/InferW.lean:2486`) — and each wrapper contains a **full copy
of the whole binding group** (so the Λ can re-enter the mutually-recursive group to
project one member). n members × n bindings per wrapper = **Θ(n²)**. The `.mono` arm
(`InferW.lean:2489`) does the same full-copy wrap as the `.poly` arm (`:2494`); the cost
is in generalisation, not in which arm is used.

**That in turn forced elaboration.** The elaborated term has a different *shape* than the
source (Λ-nest, `var i [tyArgs]`, closed annotations), so the source typing relation no
longer types it directly. Hence a second, *elaborated* typing relation `TypeOfElabHM`
(`Core.lean:3139`) with its own metatheory (`Core.lean:5101–10917`, ~5,800 lines) and a
second soundness induction `Infer.sourceSound` (`InferW.lean:12584`), plus the whole
`Infer` elaboration index `eOut` (`InferW.lean:2908`), `closeTyVars`, `letRecElab*`, and
`faithful` (`Core.lean:5260`). This is the ~19k-line inference stack the migration exists
to remove.

### 1.3 The CEK proposal (and why it was believed necessary)

`cekmachine-design.md` proposed removing the premise "the term is the machine state" by
switching to a type-erasing **CEK machine**, where generalisation lives in the proof-level
type environment (`ValTyped.recclo.bodyScheme`) instead of the term. The erasure removes
the dangling-tyvar problem by dropping annotations before evaluation. Stage 1 of that plan
was executed and proved: `FHM/CekMachine.lean` (3,394 lines) with
`progress`/`preservation`/`type_safety`/`stepM_deterministic`, sorry-free and axiom-clean.

The CEK machine was requested by the owner **only because it was believed to be the way to
kill the n²** — not as an end in itself.

---

## 2. The one decision: monomorphic recursion inside `letRec` (the DM cut)

### 2.1 What the cut is

Inside a `letRec` block, every member (annotated or not) is used at a single monotype;
the group is unified monomorphically; then — and only then — the solved monotypes are
generalised over the group's gen-var pool `G` for the **body**. Polymorphic *uses* are
allowed in the body (and anywhere outside the block); polymorphic *self/sibling uses
inside* the block are rejected. This is textbook Damas–Milner monomorphic recursion
(`RecSpecs.MonoTyped`, `Core.lean:3093`; the `PolyTyped` half, `:3107`, becomes vacuous).

The concrete rule change is small and local to `Infer`:
- `RecSpec.init` (`InferW.lean:1600`) emits `.mono` for **every** member — annotations
  included — instead of `.poly σ` for annotated ones;
- `InferRecGroup.consPoly` (`InferW.lean:3105`) is deleted (group inference is pure
  `consMono`);
- the body environment is the **annotations** (the ceiling) for annotated members, and
  `genGroup G τᵢ` for unannotated ones;
- one new premise, the ceiling check: for each `some σ`, `PolyTy.Generalizes
  (genGroup G τᵢ) σᵢ` where `σᵢ` is the annotation *as opened by the enclosing scope*
  (exactly as `Infer.letInAnn` already opens, `InferW.lean:2980`).

The full rule, the ceiling premise, and the proof-obligation table are in
`feature-support-analysis-response-6.md` §1–2 and are **not** restated here; this memo
takes them as settled.

### 2.2 What the cut gives up (concretely — the reviewer should check these)

Under the cut, `Infer` rejects three classes of program that the *old* fused
`TypeOfHM`/`Infer` accepted:

1. **Mixed-group sibling poly use**: `let rec f : ∀a. a → a = λx. x and g = (f 3,
   f True) in g` — `g` uses sibling `f` at two types.
2. **One in-group ground instantiation + poly body use**: `let rec f : ∀a. a → a =
   λx. x and g = f 3 in (g, f True)` — `g = f 3` pins `f` to `int → int`, so the body's
   `f True` is rejected (this is DM ground-pinning; see `response-3.md` §1).
3. **Scoped tyvars inside a poly-rec annotation** (the "I1" program): `let rec f :
   ∀a. a → c = λx. f (Cons x Nil) in …` — the rec call at `List a ≠ a` is in-group poly
   use, and keeping the dangling annotation would genuinely require type-passing (the
   three-way bind). The cut rejects it; erasure then has nothing dangling to worry about.

These are exactly the programs the v1/v2 coherence lemmas failed on (see
`feature-support-analysis-response-1/2/3.md`). The cut is *not* a gratuitous
expressivity sacrifice; it is the class of programs that **uniform erasure cannot
support anyway** (see §3.4 below).

### 2.3 What the cut keeps

- Scoped type variables in λ ascriptions and `letIn`/`letRec` annotations — still
  checked, still usable **everywhere**.
- Generalisation for the body: `let rec f = λx. x in (f 3, f True)` still types, with
  `f` at `∀α. α → α` in the body.
- Polymorphic values flowing out of a block: `let rec length = … in (length ints,
  length bools)`.
- All self-recursive monomorphic uses and all non-recursive polymorphism.

---

## 3. The cascade of simplifications

Each step states a consequence and *why* it holds. The reviewer is invited to verify
each against the code anchors given.

### 3.1 Annotations become runtime-inert → erase them

The only thing a `letRec` annotation did *at runtime* was carry the member's scheme so
in-group uses could instantiate it (`.poly` in `rhsCtx`) — i.e. it carried **internal
polymorphism**. The cut removes exactly that use. What remains in an annotation (the
ceiling for the body, scoped-tyvar references) is pure *typing* information, never read
by reduction. So the annotations can be dropped before evaluation with no loss of
behaviour.

`erase : Expr → Expr` (to be defined in `FHM/Core.lean` near `Expr.openTyVars`, `:2554`):

```
lambda (some t) → lambda none
letIn (some σ)  → letIn none
letRec anns     → letRec (all none)
var i _         → var i []          -- zero the tyArgs; not "pass [] through"
match_, app, primLit, primBinOp, ctor → structural
```

### 3.2 Erasure dissolves the orphan-tyvar problem at its root

The orphan-tyvar problem (§1.2) is "a scoped tyvar appears in the term as a dangling
type `bvar` that outlives its binder under substitution". Erasure removes **all** type
occurrences from the term, so there are no type `bvar`s to orphan. There is no longer
any need for `instTyAux`/`openTyVarsAux` depth-shielding at runtime. (The CEK design
also used erasure for this; the point of this memo is that erasure does the work
*without* a CEK machine.)

### 3.3 No type-passing → no `var.tyArgs` / `instTy`

The term no longer carries instantiation types. `Expr.substN`'s one type-touch
(`Core.lean:1333`, `(vs[i-k]).instTy tyArgs`) always sees `tyArgs = []` on erased
terms, and `instTy [] = id`. `var.tyArgs` (`Expr.var` at `Core.lean:338`) can be
dropped in cleanup (Stage 4 of the original plan), and `instTy`/`shiftFrom` become dead.

**This is the claim the reviewer should check most carefully**, because the whole
"keep `Step`" decision rests on it: every `Step` rule (`Core.lean:1443–1523`) reduces by
`substN` of *values/rhs/args* and never inspects a type; `substN`'s type-touch is
identity on erased terms. Therefore `Step` is already a correct, fully type-erased
reduction on erased terms.

### 3.4 No generalisation-in-the-term → no Λ-nest → no n²

Under type-passing, generalisation had to be a term-level Λ (`letRecElabNest`,
`InferW.lean:2486`), one full group-copy per member — Θ(n²). On erased terms,
generalisation lives only in the typing *derivation* (`TypeOfHM.letIn`'s cofinite
`GeneralisesTo`, `TypeOfHM.letRec`'s `bodyScheme`), not in the term. Nothing is
manufactured; nothing is copied. The n² is gone. (Note: this step is a consequence of
**erasure**, not of the cut — the cut is what makes erasure *coherent*, §3.5.)

### 3.5 No elaboration → no `TypeOfElabHM` / `sourceSound` / `eOut` / `closeTyVars` / `letRecElab*`

The source term no longer needs to be rewritten into an elaborated, type-carrying form
to be run. The runnable term is `erase e`, typed by the *declarative* `TypeOfHM`
(`Core.lean:3309`), whose `var` rule instantiates existentially (`:3373`, ignores stored
`tyArgs`) and whose `letIn`/`letRec` are cofinite. Elaboration ceases to exist:

- `Infer`'s `eOut` index (`InferW.lean:2908`) is dropped;
- `TypeOfElabHM` + its metatheory (`Core.lean:3139`, `:5101–10917`), `faithful`
  (`:5260`) are deleted;
- `Infer.sourceSound` (`InferW.lean:12584`), `letRecElab`/`letRecElabNest` (`:2505`/
  `:2486`), `closeTyVars` (`:1966`), and the `eOut_*`/`...Out` mirrors are deleted.

One typing relation, one soundness theorem (next).

### 3.6 One relation, one theorem

```
Infer.sound : Infer Φ ctx e Φ' S τ → TypeOfHM (S.onCtx ctx) (erase e) (S.onTy τ)
```

(modulo the bounds-erasure threading and the freshness preconditions — see §6.1). This
is **the** coherence theorem: the source typechecker's result is the type of the erased
term the machine runs. It is also the *same* theorem the CEK plan needed — the CEK
machine never changed the hard core of Stage 2, which is why dropping CEK is cheap.

### 3.7 Erasure ≠ CEK: why we keep `Step`

The CEK proposal conflated two separable things: **erasure** (drop types from the term)
and **the environment machine** (CEK). Erasure is the load-bearing idea — it is what
removes type-passing, elaboration, and the n², and it works with *any* operational
semantics (substitution or environment). The CEK machine is merely one way to *run*
erased terms.

Given §3.3 — the existing `Step` already runs erased terms correctly — adopting the CEK
machine adds a machine (`Val`/`Kont`/`StepM`/`StateOK`/`KontTyped`, 3,394 lines) and a
re-wiring of every surface module to it, for no benefit over keeping `Step`. Decision:
**keep `SmallStep.Step`; do not adopt the CEK machine.** `FHM/CekMachine.lean` is left
in place (proven, isolated, imports `Core`+`InferW`, nothing imports it).

The *cost* of this decision is one new metatheory obligation (§5.2), not any change to
the erasure design.

---

## 4. The settled design (unchanged from `response-6.md`)

For completeness, the design is the one in `feature-support-analysis-response-6.md`,
unchanged by this memo:

- **`Infer`** = the source relation: annotated source; DM monomorphic recursion for
  `letRec`; annotations are **ceilings**.
- **`TypeOfHM`** = the machine relation: erased terms only; `letRec` mono-only
  (`PolyTyped` vacuous — no `.poly` specs exist).
- **Coherence** = `Infer.sound : Infer e τ → TypeOfHM (erase e) τ` (with `S.onCtx` /
  `S.onTy`). No separate coherence lemma; no `TypeOfHM` of annotated `letRec`.
- **The ceiling premise**: `PolyTy.Generalizes (genGroup G τᵢ) σᵢ` for each `some σᵢ`,
  checked after group unification, on the *opened* scheme (as `Infer.letInAnn` opens).
- **The pipeline**: `lower → Infer + bounds (source) → erase → run (Step)`.

---

## 5. The revised plan

### 5.1 What changes vs the CEK brief

Only the *dynamics target* of Stage 3. Stage 2 (the `Infer` rewire, `erase`, and
`Infer.sound`) is **identical**. Concretely, versus
`next-agent-brief-cek-stage2.md` + `cekmachine-design.md` §Stage 3:

- **Not adopted**: the CEK machine; `StepM`-targeted rewiring of `EvaluateUnsafe`/
  `Headlines` (fuel bridges), re-stating `PatComp` adequacy against `StepM` (D7).
- **Kept**: `SmallStep.Step`, `substN`, and (for now) `instTy`/`shiftFrom` (dead code
  on erased terms; removable in cleanup).
- **Deleted** (as before): `TypeOfElabHM` + metatheory, `faithful`, `Infer.sourceSound`,
  `eOut`/`...Out` mirrors, `letRecElab*`, `closeTyVars`, the residual `eraseBounds`
  bridge.
- **Re-wired to `Step` on erased terms** (rather than to `StepM`): `SurfaceBridge`
  (drop `elaborate`'s `eOut` threading), `Headlines` (`WellTyped := ∃ τ, TypeOfHM
  ⟨[],ctors⟩ (erase e) τ`; `runSafe` loops `Step`), `EvaluateUnsafe` (add `erase` before
  `Step`), `PatComp` adequacy (re-stated against `TypeOfHM`/`Step` instead of
  `TypeOfElabHM`), `Bounds/*` walkers (source term, as before).

### 5.2 The one new metatheory obligation

`TypeOfHM` today has **type**-substitution metatheory (`rec_strong` `InferW.lean:11693`,
`typ_subst_preservation` `:11888`/`:12389`, `onSubst` `:12158`, `regular` `:12411`,
`weaken_scheme` `:17236`) but **no term-substitution / `Step`-preservation**. The old
dynamics metatheory (`TypeOfElabHM.progress` `Core.lean:8471`, `preservation` `:9442`,
`type_safety` `:10074`) is entirely against the elaborated relation and is deleted with
it.

So the revised plan adds, for the `Step`-on-erased-terms dynamics:

1. **Substitution lemma**: `substN` preserves `TypeOfHM` — the cofinite `letIn`/`letRec`
   cases are the delicate part ("types at every opening" survives substitution). The
   scaffolding exists: `TypeOfHM.rec_strong`, `Expr.substN_openTyVarsAux_comm`
   (`Core.lean:7889`), `SmallStep.IsValue.substN`, `Step.preserves_exhaustive`,
   `AllMatchesExhaustive.substN` (all about `substN`/`Step`, not about `TypeOfElabHM`,
   so they survive the deletion).
2. **Progress** (canonical forms for `TypeOfHM`: a value of arrow type is a λ, etc.).
3. **Preservation** (`Step` preserves `TypeOfHM`), then `preservation_star` /
   `type_safety` / `type_safety_closed`.

This is the standard mini-ML substitution-semantics metatheory (the reference in
`cekmachine-design.md` §8 is exactly this). It is real proof work — the cofinite
substitution case is the same *kind* of delicacy as `Infer.sound`'s cofinite
reconstruction, and the two will share lemmas — but it is smaller than the CEK
metatheory it replaces, and it is the **only** thing the "drop CEK" decision costs.

### 5.3 Ordering (green checkpoints)

1. (Done) Settled design + this memo; `CekMachine.lean` left in place.
2. Change `Infer.letRec` per §2.1 (all-`.mono` init, no `consPoly`, ceiling premise,
   body env = annotations); get `inferCore`/`principalType`/`typecheck` compiling;
   `lake build` green. Leave `Infer.sound` `sorry`.
3. Define `erase` (§3.1); prove `erase_openTyVarsAux` (depth-generalised, §6.3).
4. Prove `Infer.sound` (§3.6) via the proof-farming workflow; isolate the
   group-level cofinite lift first (§6.4).
5. Prove the `TypeOfHM` dynamics metatheory (§5.2): substitution lemma → progress →
   preservation → type_safety.
6. Rewire `SurfaceBridge`/`Headlines`/`EvaluateUnsafe`/`PatComp`/`Bounds` to
   `erase` + `Step` + `TypeOfHM`; delete `TypeOfElabHM` + metatheory, `sourceSound`,
   `eOut` mirrors, `letRecElab*`, `closeTyVars`, residual bridge.
7. Cleanup: drop `var.tyArgs`, `instTy`/`shiftFrom`; refresh README / `complexity-budget.md`
   / `letrec-design.md`.

---

## 6. Risks and proof-obligation sharp edges

These are the places an adversarial reviewer should probe. Items 6.1–6.4 are inherited
from the erasure design (and already flagged in the review trail); 6.5 is the new
dynamics metatheory.

### 6.1 `Infer.sound` must thread bounds-erasure (`eraseBounds`)

`Infer` is "Path R": it produces `bl`-annotated types (`UnifyRel` has `bl` cases,
`InferW.lean:964–973`; `Subst.onTy_bl` `:1004`), and `TypeOfHM`'s rules never inhabit
`bl` types. The headline statement in §3.6 is therefore a *schematic*; the real
conclusion is

```
TypeOfHM (S.onCtx ctx).eraseBounds (erase e) (Ty.eraseBounds (S.onTy τ))
```

(`erase e` is already bounds-free, since it drops all annotations.) The preconditions
`CtxWF ctx`, `CtxBelow Φ ctx`, and the `K`-list escape conditions from the existing
`Infer.sound` (`InferW.lean:9274`) also carry over. State these up-front; do not
discover them mid-proof.

### 6.2 `erase_openTyVars` must be depth-generalised

`Expr.openTyVarsAux` (`Core.lean:2330`) descends `letIn (some σ)`'s rhs at
`d + σ.paramCount` and `letRec` bindings at `d + RecAnn.params aⱼ`. The proof needs
`∀ d Xs, erase (e.openTyVarsAux d Xs) = erase e` (plus the `RecGroup`/`BranchList`
counterparts), not just the depth-0 instance `erase (e.openTyVars Xs) = erase e`.

### 6.3 Cofinite reconstruction is the long pole of `Infer.sound`

There are three distinct cofinite lifts: `letInAnn` one-opening → `TypeOfHM.letIn`
∀-opening; `letIn none` genScheme maximality → arbitrary `M` (already exists via
`weaken_scheme`); and the **`letRec` group** lift (`consMono` unifies at one batch of
fresh fvars → `RecSpecs.MonoTyped`'s `∀ Xs, FreshNames …`). The group lift has no
current analogue (today's `letRec` soundness targets the non-cofinite `TypeOfElabHM`)
and is genuinely new: a fresh-name renaming lemma for whole recursive groups over a
shared gen-pool.

### 6.4 `RecGroup.rigidVars` after the cut

`RecGroup.rigidVars` (`InferW.lean:1542`) currently includes annotation fvars because
they sat in `rhsCtx` as schemes. Under the cut they no longer do; but they are still
*in the body environment* (the ceiling schemes), and `genGroupVars` (`:1524`) excludes
`env.freeVars` — so the ann fvars must remain non-generalisable **via the env
argument**, not via `rigidVars`. Confirm (ideally with a small test: an outer scoped var
`C` in `∀a. a → C` must not enter the gen-pool) before deleting the ann-fvar term from
`rigidVars`. The stale comment ("because they sat in rhsCtx as schemes") must not be
copied into the new rule.

### 6.5 The new `TypeOfHM` dynamics metatheory (§5.2)

The substitution lemma's cofinite cases are the risk. Mitigation: much of the
`substN`/`Step` structural machinery survives `TypeOfElabHM` deletion; the proof is the
standard mini-ML pattern and shares lemmas with `Infer.sound`.

### 6.6 Not a risk, but note

The 7 existing `sorry`s (`Bounds/Pipeline.lean` ×6, `Bounds/Erase.lean` ×1) are about
the HM/`--bl` gate and surface-erase correctness, not about this work; they remain open
and unrelated.

---

## 7. Open questions (for the owner; only when load-bearing)

1. Do we keep the erased-term restriction in the dynamics statement (`Step` only ever
   sees `erase e`), or state `Step`'s type safety for arbitrary (annotated) terms and
   rely on `erase` only at the pipeline boundary? Recommendation: keep the dynamics
   statement on erased terms (`IsErased`-style), so no type ever appears at runtime and
   the substitution lemma's cofinite cases don't have to handle dangling annotations.
2. `elaborateSafe` → rename to `typecheckSafe` (cosmetic; deferred, as in
   `cekmachine-design.md` §7).

---

## 8. References

- `feature-support-analysis-response-6.md` — the settled feature design (authoritative).
- `feature-support-analysis-response-1/2/3/4/5.md` — the review trail (the
  counterexamples that forced the cut; the ceiling; the "keep Step" reasoning's
  erasure half).
- `cekmachine-design.md` — the old CEK plan (historical; Stage 1 machine description
  remains as a record; the erasure material is superseded here and by response-6).
- `next-agent-brief-cek-stage2.md` — the old Stage 2 handover (superseded by this memo's
  §5).
- `FHM/CekMachine.lean` — the proved CEK machine (left in place; isolated leaf).
- Charguéraud — *The locally nameless representation* (the reference substitution/
  environment metatheory this memo's §5.2 follows).
