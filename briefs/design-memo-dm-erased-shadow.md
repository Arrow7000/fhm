# Design memo: DM-erased regime, `.found` elaboration, two-layer BL ("the labyrinth exit")

**Status:** design agreed 2026-09-08; decision record corrected 2026-09-09 after review of the originating session and the later implementation spikes
**Date:** 2026-09-08; revised 2026-09-09
**Motivation:** end the whiplash of four half-landed campaigns (CEK, erasure, completeness spine, letRec-promotion) with ONE architecture the owner can hold in their head; each decision below is motivated and states what it was chosen *against*
**Related:** historical `findings-polyrec-stress-and-survey.md` at commit `ed332a6` (bug log B1–B8, branch map; file is not present on this branch); [`complexity-budget.md`](complexity-budget.md) (n² root-cause analysis, §3); `scratch/POLYREC-README.md` (suite); branch `erasure-migration` (proved erased metatheory); commit `be9cc14f` (end of the ORIGINAL type-erased era — mining reference)

---

## One-liner

> Erased dynamics (types never inspected at runtime) + DM monomorphic recursion (in-block polymorphism consciously dropped) + elaboration output as `.found : Ty → Expr → Expr` nodes in the existing `Expr` + BL as a downstream synth/check pass over that typed output, with user annotations carried **inside** the term Path-R-style. Deletions, not promises: removing the executable elaboratum (`eOut`) makes `letRecElabNest` (the compile-time n²) unnecessary; DM is a separate language-boundary decision.

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

**2026-09-09 clarification — annotations do not punch through the DM boundary.** Opening an annotated member's scheme once at rigid variables, so scoped type variables in its RHS can be understood, is compatible with DM. Re-instantiating that member at different types within the SCC is not. Therefore `polyrec-nested`, `polyrec-groups-nested`, `polyrec-inner-poly-calls`, and `polyrec-mixed-group` remain expected rejections under D2; a declared-mono/head-binder repair must not make them pass. Conversely, the former `polyrec-skolem-leak-must-fail` uses only one fixed recursive instantiation and is legal DM; the executable spec now records it as passing under `polyrec-mixed-fixed-instantiation`. Complete surface head-binder/scoped-type-variable support is explicitly **parked**, not part of the current critical path. This corrects the later B6 brief, which conflated scoped head-binder support with genuine polymorphic recursion.

### D3 — The n² blowup is deleted, not mitigated. `letRecElab`/`letRecElabNest` cease to exist.
The causal cut is D1 plus removal of the executable elaboration output (`eOut`): without runtime type application there is no Λ to materialise and no need for `letRecElabNest` to copy a recursive group once per member. The old compile-time quadratic representation is therefore gone rather than mitigated. D2 is independently motivated by the language/proof-complexity budget; erasure does **not** logically require monomorphic recursion, and an erased language could retain annotation-directed polymorphic recursion at the cost of its static `RecSpec`/skolem/mixed-group machinery. Ordinary runtime unfolding of recursive syntax is a separate cost and is not what this n² claim describes.

### D4 — Elaboration's output uses `.found : Ty → Expr → Expr` in the existing `Expr`.

> **CORRECTION (2026-09-09, post-session review):** the original text below attributed the agent's `ElabExpr` recommendation to the owner. That was wrong. The owner's intended mechanism was `.found : Ty → Expr → Expr` in the existing `Expr`; `ElabExpr` was proposed by the agent and was not agreed. This paragraph supersedes the original mechanism choice while retaining it below as history.

The executable and relational inference outputs wrap each corresponding Core expression node once with its final-substitution monotype. This is a **static output artifact** even though it reuses `Expr`; dynamics should consume the source/stripped term at the currently proved erasure boundary. Required contracts before implementation:

1. parser/lowering output is `.found`-free;
2. `stripFound elaborated = source`;
3. exactly one `.found` corresponds to each source Core node, and BL maps that payload rather than adding a second wrapper;
4. every stored type has the final inference substitution applied and agrees with the corresponding typing derivation.

The node monotype is not always the generalised `PolyTy` expected for a let-bound hover. Inferred binder schemes therefore need an explicit machine-produced home distinct from the user annotation slot (whether extra node metadata or a proved index is an implementation choice). Likewise, lowering is not surface-structural at matches: stable source IDs/spans must originate before lowering, survive into Core, and distinguish generated nodes. A positional zip is not an acceptable substitute.

*Historical alternative, not the decision:* a parallel `ElabExpr` inductive was proposed to avoid adding a `.found` case to functions over `Expr`. Its costs and benefits remain useful comparison material, but it was never the ratified mechanism.
*Against the sidecar map:* historical failure — name-keyed, top-level-only, no internal attachment points (the trauma that motivated Path R). A total, proved `NodeId → TypeInfo` index would be technically viable, but is not the selected default.
*Buys:* type-on-hover for arbitrary Core expressions, one observable artifact for LSP and BL, and no reconciliation between two parallel tree shapes.

### D5 — BL annotations ride INSIDE the term (Path R carriage). No strip-at-lowering.
User BL annotations stay attached to their binders through lowering and inference — wherever lowering moves a binder (including PatComp's anonymous capture-lets), the annotation moves with it. 
*Against strip-at-lowering + surface reconciliation:* rejected by owner — it requires correspondence inductions over the lowering relation (fragile, cross-coupled: "fixing a bunch of unrelated proofs if lowering ever changes") and re-creates the sidecar's alignment problem by another name.
*Consequence:* `.bl` stays a `Ty` constructor; the HM layer's grammar contains bounds syntax but treats it as an ordinary type former; bounds-blind equality (`AgreesHM`-style: equality up to bounds) appears **only** where a user ascription can meet an inferred type — pin sites in the declarative rules and the corresponding unify step. (This is the narrowed Path R tax; see Spike B.)

### D6 — The erased dynamics never inspects annotations; wholesale erase removal is deferred.
The old Path R misery (erase function, erase-commutes family, blind equality threaded toward the dynamics) was inflated by type-passing: the runtime consumed types, whereas `.bl` in an annotation is dynamics-inert under D1. The long-term expectation remains that bounds-blindness should concentrate at pin/unify sites.

**2026-09-09 revision:** do not make deletion of `Expr.erase` and the erased safety boundary a prerequisite for `.found`, LSP, or BL. The later R1 implementation spike found that the proposed `substN`/`openTyVars` commutation is false without additional freshness hypotheses. The current branch already has a proved erased progress/preservation/safety tower, so R1 is **deferred and off the critical path** until its proof benefit justifies the freshness plumbing. This supersedes the immediate-deletion language in the original D6 and in the spike report's R1 recommendation.

### D7 — LSP: one check per edit; hover = walk of the `.found` output. Zip-glue is deleted.
One `checkPipeline` run per keystroke (unchanged — already how `diagnosePayload` works); hover queries are lookups derived from the `.found` output and its source provenance: `(name, span, type)` triples for every binder at every scope, plus arbitrary-expression hover by span containment. `collectTopSchemes` + `zipBindingTypes` + chunk-reversal die. HM and BL modes get **full parity** — BL mode uses the same typed term plus per-node bounds lines; no degraded mode. Generated PatComp nodes must be marked, and surface IDs/spans propagated, so "walk" does not imply unreliable positional correspondence.

### D8 — BL layer = downstream synth/check over (surface anns carried in term, `.found` types).
Walk the typed term: at every node whose carried `Ty` is `List α`, **synth** bounds from origins (literal sizes, cons-chain pins, `Nil` [0,0], open params); at every annotated node, **check** the user's annotation against synth via the cross-layer `Agrees : BoundsTy → Ty → Prop`; emit a report keyed by stable source provenance. The product headline remains *check passes ⇒ every user annotation agrees with the HM-inferred type*, but the realistic proof surface includes separate facts for HM/`.found` coherence, synthesis, annotation checking, report provenance, and bounds-aware match coverage.
*The old internal-invisibility failure becomes structurally preventable, not automatic:* it is ruled out only when every user/generated binder has provenance and the BL walk is proved total. There is no name-keyed optional sidecar to forget to populate.

### D9 — Branch & process discipline (the anti-whiplash rules).
- Work happens on `erasure-migration`; cut `dm-erased` from `c64bb14` ("erasure migration complete") **before** the completeness-spine WIP (tip) entangles; the spine tier structure ports later onto the settled shape.
- Single campaign; work in coherent checkpoints and keep the branch recoverable. A checkpoint should be green and its temporary breakage/timebox recorded, but **every intermediate commit need not be green** when a rule, executable, declarative mirror, and proofs must move together. Timebox-and-stop remains binding (blow the box ⇒ reassess, don't absorb the next campaign); run the relevant `.fhm` matrix at semantic checkpoints. Track `sorry`s explicitly rather than imposing a monotonic count that prevents necessary restructuring.
- Fix B3 (`Bounds.Typing`'s four missing `Ty.bl` cases) first so `lake build fhm`/CLI works as the sanity tool throughout.

### D10 — Mine the original type-erased era (`be9cc14f`).
It is not a revert target (BL entanglement, and the old era predates all safety proofs), but it is a reference sketch: one typing relation, DM `letRec` (no anns), erased `Step`, pre-type-passing `Infer`. Combine: old era's *shapes* + erasure branch's *proved metatheory* + new `.found`/BL work.

## 2. Historical spike plan (completed; see the spike report and its 2026-09-09 correction)

- **Spike A — blind-tax concentration (D5/D6):** on `erasure-migration`, quantify where `AgreesHM`/erase-blindness actually appears: per-file counts; the statement of `Infer.sound`; one completeness tier's statement; how much of the spine's restatement cost was blindness vs shape.
- **Spike B — pin sites (D5):** what equality the declarative `TypeOfHM` uses at `letIn`/`lambda`/`letRec` pins on the branch (structural `Pins` vs blind); what unify does when `BL 0 5 Int` meets list sugar; the minimal rule change for one-pipeline BL.
- **Spike C — mining inventory (D10):** at `be9cc14f`: `TypeOfHM` (one relation?), DM `letRec` rule shape, `Infer` signature (pure inference, no eOut?), `genScheme`/generalisation, `Step` — what ports vs what's new.

## 3. Open risks (updated after review)

1. The completeness spine's statements may be the real blind-tax cost center (they quantify over annotations) — if Spike A shows blindness saturating the spine, D5's "smaller surface" claim weakens and the BL design must be revisited *before* the spine ports.
2. Blind `Pins` in the declarative rules weakens/strengthens which lemmas? (cofinite machinery is equality-sensitive — subst/weaken lemmas over blind equality need checking).
3. `.found` ↔ surface correspondence at PatComp sites: PatComp inserts capture-lets. Stable IDs/spans and generated-node provenance must map through the decision tree; positional correspondence is insufficient.
4. Decide the exact machine-owned representation for generalised binder schemes alongside per-node `.found` monotypes before committing the LSP API.
5. R1 may still reduce proof plumbing, but its required freshness conditions and payoff should be measured in a new bounded spike; it is not a dependency of the typed-output vertical slice.
