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
- **Two causal threads, kept separate** (they are easy to conflate, and the review
  caught exactly this):
  - *The cut enables uniform erasure.* With mono-internal recursion the annotations
    are runtime-inert, so uniformly erasing them dissolves the orphan-tyvar problem
    at its root and removes type-passing / `var.tyArgs` / `instTy` from the runtime.
    The cut is what makes **uniform** erasure *coherent* (`Infer.sound`); it is a
    feature-policy decision, **not** what kills the n².
  - *Dropping elaboration kills the n².* The n² is the Λ-nest `Infer` emits into
    `eOut`. It disappears as soon as the runnable term is the source (`erase e`)
    typed by `TypeOfHM`, with no `eOut` — a consequence of "don't elaborate", which
    holds for **any** type-erasing runtime (a milder erase that kept `WF` `letRec`
    anns would also kill the nest). The cut is what lets a *single* `erase` cover
    `letRec` anns with no leftover load-bearing annotation.
- **The realisation that ends the CEK detour**: erasure is the load-bearing idea, and
  it is **separable from the choice of machine**. Types are fully erasable here (no
  type-based dispatch, `match` is on constructors, primops are monomorphic by name),
  and the *live* evaluator already runs `SmallStep.Step` (`Live.lean`,
  `EvaluateUnsafe`). So we keep `Step` and do not adopt the CEK machine —
  **operationally** `Step` reduces erased terms with zero type computation (its rules
  never inspect types; `substN`'s one type-touch is the identity on `tyArgs = []`).
  This is a *product* decision (don't put an unused machine on the evaluator path),
  **not** a proof-budget win — see §3.7 and §5.
- **What still has to be proved** (unchanged hard core): `Infer.sound : Infer e τ →
  TypeOfHM (erase e) τ`, plus a genuinely new *term*-substitution and
  `Step`-preservation metatheory for `TypeOfHM` (which today exists only for
  `TypeOfElabHM`; the CEK machine's `TypeOfHM` safety is already proved but is being
  left unused).

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
`feature-support-analysis-response-1/2/3.md`). Two clarifications of scope, so the
cut is not over-justified:

- Items (1) and (2) are unsupported by **uniform** drop of `letRec` anns. A *selective*
  erase that kept well-formed (`WF`) binding annotations **would** support them — that
  is the C6 point of the review trail, and Stage 1's `Expr.IsErased.letRec` already
  does it. The cut is therefore a **policy** (owner has signed textbook DM), not a
  physics constraint. Only item (3) — a *dangling* tyvar **and** in-group poly use —
  is genuinely impossible without type-passing.
- The cut is not what kills the n² (§3.4); it is what makes **uniform** erasure
  coherent. Don't justify it twice.

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
**reduction** on erased terms. This is an *operational* claim only: it says nothing
about whether `TypeOfHM`/`Step` *type-safety* is already proved — it is not (§5.2).
The whole "keep `Step`" decision rests on the *reduction* fact, plus the product fact
that the live evaluator already runs `Step` (§3.7).

### 3.4 No generalisation-in-the-term → no compile-time Λ-nest → no n²

Under type-passing, generalisation had to be a term-level Λ (`letRecElabNest`,
`InferW.lean:2486`), one full group-copy per member — Θ(n²) in the **elaborated AST**
(the compile-time / proof-object blowup). On erased terms, generalisation lives only in
the typing *derivation* (`TypeOfHM.letIn`'s cofinite `GeneralisesTo`,
`TypeOfHM.letRec`'s `bodyScheme`), not in the term. Nothing is manufactured; nothing is
copied **by the elaborator**. (Note: this step is a consequence of **dropping `eOut` /
elaboration**, not of the cut — the cut is what makes *uniform* erasure coherent, §3.6.)

**Sharp edge the review flagged**: this is the *elaborator* n². `SmallStep.letRecUnfold`
(`Core.lean:1478`) still substitutes a full copy of the group per member **per step** —
that is ordinary substitution semantics of mutual recursion (`fix`), present in any
substitution machine, and **not** what goal (3) was about. It is not removed by
erasure; it is the one place a CEK machine (shared environment, no copy) would
genuinely differ. For FHM-scale groups this is irrelevant; if a large mutually-recursive
group ever becomes a product concern, that is the remaining argument *for* CEK.

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
machine never changed the hard core of Stage 2. ("Dropping CEK is cheap" is true **only
of Stage 2**; Stage 3 is where the cost is paid, §3.7/§5.)

### 3.7 Erasure ≠ CEK: why we keep `Step`

The CEK proposal conflated two separable things: **erasure** (drop types from the term)
and **the environment machine** (CEK). Erasure is the load-bearing idea — it is what
removes type-passing, elaboration, and the *compile-time* n², and it works with *any*
operational semantics (substitution or environment). The CEK machine is merely one way
to *run* erased terms.

The decision to keep `Step` is a **product** decision, not a proof-budget win:

- **The live evaluator already runs `Step`.** The pipeline is
  `parse → infer → elaborate → evaluateUnsafe` (`Live.lean:20,257`). Adopting CEK would
  put a second, unused machine on the evaluator path and rewire `Live`/
  `EvaluateUnsafe`/`Headlines`/`PatComp` to `StepM`. Keeping `Step` changes the pipeline
  to `parse → infer → erase → evaluateUnsafe` — a one-line rewire, no new reducer.
- **The proof side is a wash, arguably a small loss.** CEK Stage 1 *already proved*
  `TypeOfHM` type-safety (`progress`/`preservation`/`type_safety`/`deterministic`) on
  `IsErased` terms. Keeping `Step` means re-proving the Mini-ML `TypeOfHM`/`Step`
  metatheory (§5.2) — real work, not a saving. We accept that because the product
  should run one operational model, not two, and the CEK machine is not on any path.

Decision: **keep `SmallStep.Step`; do not adopt the CEK machine.** `FHM/CekMachine.lean`
is left in place (proven, isolated, imports `Core`+`InferW`, nothing imports it).

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
   `type_safety` / `type_safety_closed`. The `letRecUnfold` case is the one with real
   content: it substitutes, for each member `j`, the term `letRec anns bindings eⱼ` —
   a **full copy of the group** — and preservation needs that copy to inhabit the
   member's *body scheme* (`genGroup G τ` under the cut). This is a `TypeOfHM` port of
   `TypeOfElabHM.rec_rewrap_typed` (`Core.lean:9184`) and
   `TypeOfElabHM.rewrap_hasScheme_mono` (`Core.lean:9247`). Name it explicitly as a
   checkpoint; it is the letRec case of the substitution lemma, not a freebie. The
   `letReduce` case needs the "occurrence-at-instance" lemma
   (`GeneralisesTo_inst_ann`) and, for the erased term, `openTyVars_eq_self_of_erased`.

**Dependency note**: `GeneralisesTo_inst_ann` (`CekMachine.lean:787`),
`GeneralisesTo_inst`, `recclo_body_typed`, and `openTyVars_eq_self_of_erased` currently
live in the CEK leaf we are *not* importing. Move the reusable ones into `Core`/`InferW`
(once `erase` exists in `Core`) rather than depending on `CekMachine.lean` — the new
`TypeOfHM`/`Step` metatheory must not cite the leaf.

This is the standard mini-ML substitution-semantics metatheory (the reference in
`cekmachine-design.md` §8 is exactly this). It is real proof work — the cofinite
substitution case is the same *kind* of delicacy as `Infer.sound`'s cofinite
reconstruction, and the two will share lemmas. It is **not** a saving versus the CEK
machine: CEK's `TypeOfHM` safety is already proved; we are *paying* this Mini-ML
metatheory as the price of keeping the product on a single, already-live dynamics
(`Step`).

### 5.3 Ordering (green checkpoints)

> **Execution status (2026-08-22, commit `a505638`):** steps 1–4 are DONE and proven
> (steps 1–4 = "settled design", the DM cut, `erase`, and `Infer.sound` itself).
> Steps 5–7 (= "step 5–6" below) remain. See **`briefs/next-agent-brief-erasure-step4.md`**
> for the authoritative current state, the exact remaining `sorry`s (8, all doomed),
> and the detailed plan for the remaining work. One correction to §6.3 recorded
> there: the `letRec` body-lift did need one small *new* lemma
> (`PolyTy.Generalizes.freeVars_subset`), not "no new metatheory shape"; it is proven.

1. (Done) Settled design + this memo; `CekMachine.lean` left in place.
2. (Done) Change `Infer.letRec` per §2.1 (all-`.mono` init, no `consPoly`, ceiling premise,
   body env = annotations); get `inferCore`/`principalType`/`typecheck` compiling;
   `lake build` green. **Keep `eOut` for now** (see below) and leave `Infer.sound`
   `sorry`.
3. (Done) Define `erase` (§3.1); prove `erase_openTyVarsAux` (depth-generalised, §6.2).
4. (Done) Prove `Infer.sound` (§3.6) via the proof-farming workflow; isolate the
   group-level cofinite lift first (§6.3). **`eOut` ordering, decided**: prove
   `Infer.sound` against the *input* term — `TypeOfHM (erase eIn) …` — while `Infer`
   still threads `eOut`; ignore `eOut` in the conclusion. This is the smaller diff
   (`eOut` is built but unused by the theorem). `eOut` itself is dropped in step 6.
5. Prove the `TypeOfHM` dynamics metatheory (§5.2): substitution lemma → progress →
   preservation → type_safety.
6. Rewire `SurfaceBridge`/`Headlines`/`EvaluateUnsafe`/`PatComp`/`Bounds` to
   `erase` + `Step` + `TypeOfHM`; **drop `eOut` from `Infer`/`InferBranches`/
   `InferRecGroup` and `inferCore`/`principalType`/`typecheck`**; delete
   `TypeOfElabHM` + metatheory, `sourceSound`, `eOut`/`...Out` mirrors, `letRecElab*`,
   `closeTyVars`, residual bridge.
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

The substitution lemma's cofinite cases are the risk, and the `letRecUnfold` case in
particular — it needs the `TypeOfHM` port of `rewrap_hasScheme_mono`/`rec_rewrap_typed`
(§5.2), which does not yet exist for `TypeOfHM`. Mitigation: much of the `substN`/`Step`
structural machinery survives `TypeOfElabHM` deletion; the proof is the standard mini-ML
pattern, shares lemmas with `Infer.sound`, and has a template in the `TypeOfElabHM`
rewrap lemmas (`Core.lean:9184`/`:9247`). Do not treat "`Step` reduces erased terms"
(§3.3, operational) as having proved any of this.

### 6.6 Not a risk, but note

The 7 existing `sorry`s (`Bounds/Pipeline.lean` ×6, `Bounds/Erase.lean` ×1) are about
the HM/`--bl` gate and surface-erase correctness, not about this work; they remain open
and unrelated.

---

## 7. Open questions (for the owner; only when load-bearing)

1. (Decided, not open — recorded for completeness.) The dynamics is quantified over
   **erased** terms only: `type_safety` is stated for `erase e` (or `IsErased`-style),
   never for arbitrary annotated terms. This is **load-bearing**, not cosmetic: `Step`
   on an *annotated* `let f : ∀a. a→a = λ(x:a). x in f 3` substitutes the
   dangling-ascription λ and `TypeOfHM` of that closed rhs fails `paramTy.IsLC` — the
   orphan problem again. Erase at the pipeline boundary, and do **not** try to prove
   `Step` preservation for annotated terms without bringing type-passing back.

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

---

## 9. Response to the adversarial reviewer (`design-memo-erasure-migration-1.md`)

All corrections accepted and incorporated; there are **no substantive disagreements**.
Specifically:

- **Split the causal claims** (§0, §3.4): dropping `eOut`/elaboration kills the
  *compile-time* Λ-nest; the cut only makes **uniform** erasure coherent. Both threads
  are now stated separately, and §3.4 names `SmallStep.letRecUnfold`'s per-step group
  copy as a distinct, erasure-independent phenomenon (and the one remaining argument
  for CEK, should large groups ever matter).
- **§2.2** no longer claims "uniform erasure cannot support these programs anyway" for
  the self-contained poly-rec cases; it now says the cut is a *policy* (owner-signed
  DM), with only the dangling-tyvar-plus-in-group-poly case (I1) being impossible
  without type-passing.
- **Reduction vs safety** (§3.3, §0, §6.5): "`Step` reduces erased terms" is now
  explicitly an operational claim; type-safety is §5.2 and unproved.
- **§5.2** names the `TypeOfHM` rewrap obligation (port of
  `TypeOfElabHM.rewrap_hasScheme_mono`/`rec_rewrap_typed`, `Core.lean:9247`/`:9184`) as
  a checkpoint, and records that `GeneralisesTo_inst*`/`openTyVars_eq_self_of_erased`
  must move out of `CekMachine.lean` into `Core`/`InferW`.
- **§3.7** justifies keeping `Step` as a product decision (live evaluator already runs
  it; don't put an unused machine on the path), and states plainly that Stage 3 *pays*
  the Mini-ML metatheory rather than saving it. "Dropping CEK is cheap" is now scoped
  to Stage 2 only (§3.6).
- **§5.3** resolves the `eOut` ordering: prove `Infer.sound` against the *input* while
  `eOut` is still threaded, drop `eOut` in step 6.
- **§7** marks the erased-term restriction as decided/load-bearing and drops the rename
  question.

Two small notes for the reviewer (not disagreements):

1. **`CekMachine.lean` is not quite "free" to leave in place.** It imports `InferW`
   (for the `TypeOfHM` metatheory at `InferW.lean:11661+`), though it does **not**
   reference `Infer`/`eOut`/`TypeOfElabHM`. So Stages 2–3 edits to `InferW` should not
   break it, but the Stage-4 `var.tyArgs` removal will (it changes `Expr` and
   `Expr.IsErased.var`). If keeping it compiling ever becomes friction, the cheapest fix
   is to delete it — nothing imports it, and its reusable lemmas will already have moved
   to `Core`/`InferW` per §5.2.
2. **"One operational model in the product" is the honest framing, not "one machine".**
   Keeping `Step` on the evaluator path while `CekMachine.lean` sits unimported means
   the repo still contains a second (proved but unused) machine; the *product* runs one.
   That is the intended state, and it is worth keeping explicit so nobody later
   "finishes" the CEK wiring by accident.
