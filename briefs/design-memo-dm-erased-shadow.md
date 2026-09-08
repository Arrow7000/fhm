# Design memo: DM-erased regime, shadow elaboration, two-layer BL ("the labyrinth exit")

**Status:** design agreed 2026-09-08 (after the poly-rec stress campaign + suspect-feature survey); spikes pending — results to be appended
**Date:** 2026-09-08
**Motivation:** end the whiplash of four half-landed campaigns (CEK, erasure, completeness spine, letRec-promotion) with ONE architecture the owner can hold in their head; each decision below is motivated and states what it was chosen *against*
**Related:** [`findings-polyrec-stress-and-survey.md`](findings-polyrec-stress-and-survey.md) (bug log B1–B8, branch map); [`complexity-budget.md`](complexity-budget.md) (n² root-cause analysis, §3); `scratch/POLYREC-README.md` (suite); branch `erasure-migration` (proved erased metatheory); commit `be9cc14f` (end of the ORIGINAL type-erased era — mining reference)

---

## One-liner

> Erased dynamics (old-era style, types never inspected at runtime) + DM monomorphic recursion (in-block polymorphism consciously dropped) + elaboration output as a **shadow tree** (1:1 structural mirror carrying a full `Ty` — `.bl` included — at every node) + BL as a downstream synth/check pass over that tree, with user annotations carried **inside** the term Path-R-style. Deletions, not promises: `letRecElabNest` (the n²) ceases to exist rather than being mitigated.

---

## 0. Context: what forced this

The owner experienced four sequential/parallel remediation campaigns, each sound in isolation, each reshuffling the same 20k lines: CEK Stage 1 (abandoned), erasure migration (complete at `c64bb14`), completeness spine (mid-flight, 8/12 tiers), letRec promotion Stage 1 (landed on `letrec-promotion`, then abandoned when erasure swept the board). Costs that triggered the reset: `letRecElab`'s n² group-copying, 574-line `Infer.sound` letRec case, LSP extraction by positional zip+reverse (`zipBindingTypes` — the source of display bug B4), the sidecar BL failure (bounds analysis silently degrading to top-level-only because nothing attached bounds to internal scopes), and `.bl` inside `Core.Ty` generating the entire Path R blind-economy.

Key receipts that shaped the decision:
- n² root cause: **not** cofinite quantification, **not** orphan bvars — it is "a rule-invented generalisation has nowhere to live in the term, under a convention that annotation slots only hold user-authored schemes" (complexity-budget §3.2). Type-passing forced a Λ-binder to be *materialised*; the hoist was one (bad) answer to that storage problem.
- The original type-erased era existed: `be9cc14f` (2026-06-24) — `var` without `tyArgs`, `Step` doing plain substitution, DM `letRec` without anns, ONE typing relation. The type-passing migration started `1eaf41e` the next day. (The "we never had erasure" claim made earlier in conversation was wrong.)
- PatComp `emit` uses the "leaf-lets" design: lowering **creates** anonymous capture-binders (`emitLets`, plus the scrutinee let in `lowerMatch`). Therefore surface↔Core binder structure is NOT 1:1 at match sites, and any tooling that reconciles surface with a Core-mirroring artifact by structural walk needs real correspondence machinery.

## 1. The decisions

### D1 — Erased operational semantics (old-era style). Type-passing is OUT.
Types are never inspected at runtime; `Step` reduces by ordinary substitution (`be9cc14f` is the reference shape; the `erasure-migration` branch supplies the *proved* erased metatheory: progress/preservation/type-safety/determinism, which the old era never had).
*Against:* type-passing (runtime type reification, annotations-mean-something aesthetics). Cost accepted: no runtime type access. Decisive reasons: kills the Λ-storage problem at its root (no runtime type args ⇒ no need to materialise schemes in terms), deletes `TypeOfElabHM` (already deleted on the branch), and makes annotation carriage dynamics-inert (see D6).
*The owner's "decoupling" motivation for type-passing was diagnosed as inverted:* type-passing couples opsem to types (every binding must carry a scheme; evaluator does type-beta); erasure is the decoupled regime. Accepted 2026-09-08.

### D2 — DM monomorphic recursion. In-block polymorphic recursion is OUT.
Inside a recursive block all members are monomorphic (shared monotype); generalise at group exit; polymorphic freely in the body and to later groups.
*Sacrificed (consciously, after the death marches):* Pottier `LetRecPoly` — two call sites of one member at different types *inside* its own group. Mycroft `Nested` leaves the language. Of the 8-test poly-rec suite: 3 keep passing, 1 stays must-fail (unannotated polyrec), 4 flip to must-fail *by design* — the suite becomes the executable spec of the new boundary.
*Deleted by this:* `RecSpec.poly`, `RecSpecs.PolyTyped`, skolem-nesting + `skolemLeak_untypeable`, ceiling machinery, the mixed-group fused rule — the tier that caused the death marches. Re-addable later as an add-on, not a load-bearing wall.

### D3 — The n² blowup is deleted, not mitigated. `letRecElab`/`letRecElabNest` cease to exist.
Under D1+D2 the elaboratum no longer needs *any* shape change for `letRec`: no Λ to materialise, no promotion (the `letrec-promotion` branch is moot). There is no residual "sometimes still n²" case — the copying code is gone. This also deletes the 574-line `Infer.sound` case (letRec becomes ordinary structural induction) and the promotion campaign's remaining work.

### D4 — Elaboration's output is the **shadow tree**: a parallel artifact, not an Expr rewrite.
`ElabExpr`: inductive with exactly one child per structural child of the corresponding source/Core node; every node carries its full `Ty`; spans carried (parser already produces `SpannedExpr`). `elaborate : Expr → Option (ElabExpr × Ty)`; the Infer relation and executable infer both build it.
*Against `.found : Ty → Expr → Expr` in the core term:* pollutes every function/family over `Expr` (eval, LC, subst, typing) with a case; conflates synthed data with the runtime term; owner prefers annotation slots stay user-authored. (Note: under D1 the *existing* elaboratum already puts synthed schemes in user ann slots — that conflation dies with D3/D4.) 
*Against the sidecar map:* historical failure — name-keyed, top-level-only, no internal attachment points (the trauma that motivated Path R).
*Buys:* type-on-hover for **arbitrary expressions** (lambda params included — currently architecturally impossible: nothing carries synthed param types), a flattened `(name, span, type)` LSP map by a trivial walk, and the landing pad for BL (D5/D8). Cost: one coherence theorem family (shadow node types agree with sub-derivations) — ordinary induction, no shape-changing cases.

### D5 — BL annotations ride INSIDE the term (Path R carriage). No strip-at-lowering.
User BL annotations stay attached to their binders through lowering and inference — wherever lowering moves a binder (including PatComp's anonymous capture-lets), the annotation moves with it. 
*Against strip-at-lowering + surface reconciliation:* rejected by owner — it requires correspondence inductions over the lowering relation (fragile, cross-coupled: "fixing a bunch of unrelated proofs if lowering ever changes") and re-creates the sidecar's alignment problem by another name.
*Consequence:* `.bl` stays a `Ty` constructor; the HM layer's grammar contains bounds syntax but treats it as an ordinary type former; bounds-blind equality (`AgreesHM`-style: equality up to bounds) appears **only** where a user ascription can meet an inferred type — pin sites in the declarative rules and the corresponding unify step. (This is the narrowed Path R tax; see Spike B.)

### D6 — The erased dynamics never inspects annotations ⇒ the Path R tax collapses to unify + statement-blindness.
The old Path R misery (erase function, erase-commutes family, blind equality threaded toward the dynamics) was inflated by type-passing: the runtime *consumed* types, so annotations had to be erased and commutation lemmas proven. Under D1 the erased `Step` mechanically ignores annotation payloads — `.bl` in an ann is as inert as `Int`. **Delete:** the erase machinery's role in dynamics, erase-commutes lemmas, the erase-level residual bridges. **Keep:** blind equality at pin/unify sites only.

### D7 — LSP: one check per edit; hover = walk of the shadow. Zip-glue is deleted.
One `checkPipeline` run per keystroke (unchanged — already how `diagnosePayload` works); all hover queries are lookups into the shadow walk output: `(name, span, type)` triples for every binder at every scope, plus arbitrary-expr hover by span containment. `collectTopSchemes` + `zipBindingTypes` + chunk-reversal die. HM and BL modes get **full parity** — BL mode's hover is the same tree plus per-node bounds lines; no second artifact, no degraded mode (owner explicitly rejected shortcuts here).

### D8 — BL layer = downstream synth/check over (surface anns carried in term, shadow types). One theorem.
Walk the shadow: at every node whose carried `Ty` is `List α`, **synth** bounds from origins (literal sizes, cons-chain pins, `Nil` [0,0], open params); at every annotated node, **check** the user's annotation against synth via the cross-layer `Agrees : BoundsTy → Ty → Prop`; emit a keyed (span) report. Main theorem: *check passes ⇒ every user annotation agrees with the HM-inferred type*. No runtime interaction; failure mode is "wrong bounds reported", never unsound execution.
*The internal-invisibility failure mode is structurally impossible:* there is no external map to forget to populate — annotations and types live on nodes, and internal scopes are nodes.

### D9 — Branch & process discipline (the anti-whiplash rules).
- Work happens on `erasure-migration`; cut `dm-erased` from `c64bb14` ("erasure migration complete") **before** the completeness-spine WIP (tip) entangles; the spine tier structure ports later onto the settled shape.
- Single campaign; every step ends CI-green; sorry count may only decrease; deletion phases are net-negative LOC; no new lemma without a named consumer; timebox-and-stop (blow the box ⇒ reassess, don't absorb the next campaign); `.fhm` suite re-run as executable spec at every step.
- Fix B3 (`Bounds.Typing`'s four missing `Ty.bl` cases) first so `lake build fhm`/CLI works as the sanity tool throughout.

### D10 — Mine the original type-erased era (`be9cc14f`).
It is not a revert target (BL entanglement, and the old era predates all safety proofs), but it is a reference sketch: one typing relation, DM `letRec` (no anns), erased `Step`, pre-type-passing `Infer`. Combine: old era's *shapes* + erasure branch's *proved metatheory* + new shadow/BL work.

## 2. Spike plan (before any new theorem is written)

- **Spike A — blind-tax concentration (D5/D6):** on `erasure-migration`, quantify where `AgreesHM`/erase-blindness actually appears: per-file counts; the statement of `Infer.sound`; one completeness tier's statement; how much of the spine's restatement cost was blindness vs shape.
- **Spike B — pin sites (D5):** what equality the declarative `TypeOfHM` uses at `letIn`/`lambda`/`letRec` pins on the branch (structural `Pins` vs blind); what unify does when `BL 0 5 Int` meets list sugar; the minimal rule change for one-pipeline BL.
- **Spike C — mining inventory (D10):** at `be9cc14f`: `TypeOfHM` (one relation?), DM `letRec` rule shape, `Infer` signature (pure inference, no eOut?), `genScheme`/generalisation, `Step` — what ports vs what's new.

## 3. Open risks (pre-spike)

1. The completeness spine's statements may be the real blind-tax cost center (they quantify over annotations) — if Spike A shows blindness saturating the spine, D5's "smaller surface" claim weakens and the BL design must be revisited *before* the spine ports.
2. Blind `Pins` in the declarative rules weakens/strengthens which lemmas? (cofinite machinery is equality-sensitive — subst/weaken lemmas over blind equality need checking).
3. Shadow ↔ lowering correspondence at PatComp sites: the shadow mirrors Core; PatComp inserts capture-lets. Hover over *surface match subexpressions* must map through the decision tree — acceptable to scope v1 hover to binders + non-match subexprs if the general mapping proves hairy (owner sign-off required if so).
