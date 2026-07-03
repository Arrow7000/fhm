<!-- Written 2026-07-03 after the mixed-recursion campaign landed (roadmap step 4).
     Successor to next-agent-brief-primitives-typedecls-surface.md, which stays alive
     as the DESIGN REFERENCE + status log — read it first, don't duplicate it here. -->

# Brief: arithmetic primops → type declarations + prelude → comparison ops

## Where the repo stands (2026-07-03)

Mixed annotated/unannotated mutual recursion is DONE end-to-end (roadmap step 4):
ONE `Expr.letRec (anns : List (Option PolyTy)) bindings body` node, one fused
declarative rule (both relations), one fused inference path, full correctness
triangle re-proven. Repo-wide: zero sorries, fresh `lake build` green, all 25
headline theorems axiom-clean ({propext, Classical.choice, Quot.sound}).
Roots: Core, SurfaceLang, Pretty, SpikeC, InferW, Examples — all green.

Read `briefs/next-agent-brief-primitives-typedecls-surface.md` IN FULL before
starting. It contains: the settled designs for YOUR mission (its §"Primitive ops",
§"Bool …", §"Nats and ints", §"Type declarations"), the packaged-premise
architecture your new rules must follow, the working discipline, the cleanup
backlog (not your job, don't drift into it), and the campaign status log.

## Your mission (roadmap steps 1–3, in order)

1. **Arithmetic primops** (`intAdd`, optionally `intSub`/`intMul`) — the design in
   the reference brief §"Primitive ops" is settled: a `PrimOp` enum + ONE
   `Expr.primOp : PrimOp → Expr` node, a total `PrimOp → Ty`, δ-rules in
   `SmallStep.Step` for saturated applications on literals, progress treats
   partially-applied primops as values (canonical-forms: `int`-typed values are
   int literals), preservation for δ is trivial. The suggested first task at the
   bottom of the reference brief is your concrete starting checklist.
2. **Type declarations + prelude** — §"Type declarations" is settled: NO new Core
   metatheory (theorems are `∀ ctors`); the work is a validated `data`-decl →
   `CtorEnv` elaborator (arity/kinding, result-type shape, `bound`/`closed`
   witnesses — see `Examples.lean`'s `mkCtor` for the decidable-discharge
   pattern), plus a fixed prelude env (`Bool` as DATA with `True`/`False`, etc.).
3. **Comparison/boolean primops** (`intLt`, `intEq`, …) — AFTER the prelude exists:
   their typing rule looks up `Bool` in the ambient `CtorEnv` (like `ctor` does)
   and their δ-rules produce `.ctor "True"/"False"` (reference brief §"Bool" has
   the soundness story: typechecks ⟹ Bool present ⟹ δ-result well-typed).

## What changed since those designs were written (adjust expectations)

- **The `Expr` cascade meets ONE recursion constructor**, not two: every structural
  function/lemma you extend with a `primOp` case has a single fused `letRec` arm
  (keyed by `RecAnn.params` shield depths where relevant). `primOp` is a leaf —
  every case is trivial (like `ctor` without the env lookup).
- **New typing rules follow the packaged-premise style**: named, docstringed
  premise defs/structures rather than inline quantifier nests (see Core
  ~L2250–2320 for the pattern; `Ty.AreLC`, `PolyTy.InstantiatesTo`,
  `BranchCtorSpec` are the house style). A primop's rule is small enough that
  this mostly means: give it a good docstring and use `Ty.IsLC`-style named preds.
- **Both typing relations must stay in lockstep** except `var` (share any
  relation-recursing premise via a `TypeOf`-parametric def, per the house style).
- **Inference**: `Infer`/`inferCore` gain a trivial `primOp` case (fixed type, no
  fresh vars, like a monomorphic `ctor`); soundness/completeness cases are
  one-liners by design. The heavy machinery (recursion, unification) is untouched.

## Non-negotiables (from the reference brief, restated because they bite)

- Headline theorems stay sorry/axiom-free and axiom-clean; gate every increment
  with a fresh-olean `lake build` + `#print axioms` — the LSP alone is NOT the
  gate after a `Core` edit (stale-olean trap is real; it bit twice this campaign).
- Don't weaken headline statements; add hypotheses to internal helpers instead.
- Witness every feature in `Examples.lean` with `#eval`/`#guard` (e.g.
  `(λx. intAdd x 1) 41 ⟹ 42` evaluates AND typechecks; a partially-applied
  primop is a value; an ill-typed application is rejected).
- Delegate bulk proof-plumbing to subagents with precise per-error specs; keep
  design decisions and the build/axiom gate in the parent. Granular commits at
  each phase boundary.
- Update the reference brief's status log as you land things; append, don't
  rewrite history.

## Deferred (recorded in the reference brief — do NOT build now)

Typeclasses/overloading; row types; top-level mutually-recursive `def` groups
(small — fold into surface work); the cleanup backlog (naming pass, Core file
split, examples relocation); surface-language bridging (step 5, the north star —
your steps 1–3 clear its runway).
