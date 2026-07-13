<!-- Written 2026-07-08. Handoff for STARTING the surface → Core bridge campaign.
     The pattern-compilation kernel (bridge item 5) is now COMPLETE and
     UNCONDITIONAL. Read these FIRST, in order:
       1. briefs/next-agent-brief-surface-bridge.md — THE PLAN (items 1-9, the
          north star). Still accurate EXCEPT item 5 (pattern compilation) is
          DONE; see status below.
       2. briefs/design-memo-verified-pattern-compilation.md — the pattern-
          compilation record + status log (read the LAST TWO entries: the (X)
          totality layer and the 2026-07-08 blocker-fix + discharge).
     This brief does NOT duplicate the plan; it gives the fresh status, the
     interface the bridge must produce, one hard-won lesson, and where to start. -->

# Brief: kick off the surface → Core bridge

## Where the repo stands (2026-07-08)

The verified pattern-compilation campaign is **complete**, and its headline is
now **unconditional** — the `CtorSwitches` path-condition has been discharged
from typing. `lake build` green; all headlines axiom-clean
`{propext, Classical.choice, Quot.sound}`; 9 `.lean` files.

- **`FHM/PatComp.lean`** — the whole kernel. The theorem the bridge consumes:

  ```
  theorem lowerMatch_adequate_of_typed
      (hty : TypeOfElabHM ⟨[], ctors⟩ root (.customTy T tyArgs))
      (hval : IsValue root)
      (ps : List Surface.Pattern) (bodies : Nat → Expr)
      (hwf : ∀ r ∈ initMatrix ps, GPatWFList ctors r.pats [.customTy T tyArgs])
      (hmatch : firstMatch root ps = some (i, ws)) :
      Relation.ReflTransGen Step (lowerMatch root ps bodies) ((bodies i).substN 0 ws)
  ```

  For a scrutinee typed at an ADT `customTy` and patterns well-formed, the
  compiled-and-emitted Core match reduces under Core's real `Step` to the
  surface-selected branch body with exactly the right captures. No residual
  hypotheses beyond typing + well-formedness.

- **The bridge interface you must produce**: `GPatWF ctors : GPat → Ty → Prop`
  (with its pointwise `GPatWFList`), in `PatComp.lean`. A `gctor c` test is
  well-formed only at its ctor's `customTy`, with sub-patterns fitting the
  ctor's _instantiated_ field types. The `Lowers` `match` case must establish
  `∀ r ∈ initMatrix ps, GPatWFList ctors r.pats [.customTy T tyArgs]` for the
  scrutinee's type — then `lowerMatch_adequate_of_typed` fires and the match
  case's soundness obligation is discharged. Recommended: define a surface-level
  `PatternWF ctors : Surface.Pattern → Ty → Prop` and prove
  `PatternWF … p τ → GPatWF ctors (norm p) τ`, so the bridge speaks in surface
  terms and the `norm` bridge is a one-off lemma.

- **Already in place for you**: `FHM/Decls.lean` (the Core-side `DataDecl`,
  `Ty.WellKinded`, `elabDecls : List DataDecl → Option CtorEnv` sound+complete,
  `preludeDecls`); `FHM/SurfaceLang.lean` (the surface AST: `Ty`/`PolyTy`,
  `PrimLitExpr`, nested `Pattern`, `Expr` with sugar). NOT in place: any
  surface `DataDecl`, any `Surface.Ty/Expr → Core` lowering, any `Lowers`
  relation (grep confirms none exists yet).

## Your mission

Build the bridge per `next-agent-brief-surface-bridge.md` — items 1–4 and 6–8
(item 5, pattern compilation, is done). The end product is a **verified
front-end**:

1. A declarative **`Lowers`** relation (surface → Core: name resolution +
   kind-checking + desugaring), the trusted spec, plus an executable **`lower`**,
   bridged by **soundness** (`lower s = some c → Lowers … s c`) and
   **completeness** (a valid lowering exists ⟹ `lower` finds one; one-to-many at
   matches — see the plan's completeness nuance).
2. Surface well-typedness **defined** via the relation
   (`s` well-typed `:= ∃ c, Lowers … s c ∧ (typecheck ctors c).isSome`); no
   `Surface.TypeOf`.
3. An executable **exhaustiveness checker** (`checkExhaustive`, item 6) with
   `= true → AllMatchesExhaustive`.
4. Top-level binding/SCC handling (item 7).
5. **The headline payoff**: compose `Lowers` soundness with Core's existing
   `type_safety`/`progress` into _"a well-typed surface program lowers to a
   type-safe Core program that does not get stuck."_

Note on "semantics preserved": there is no separate surface operational
semantics — surface meaning _is_ Core meaning by the lowering. So for
names/sugar/types, soundness of `lower` wrt `Lowers` is the whole story.
**Pattern matching is the one construct with genuine behavioural content**, and
that behavioural theorem is already done (`lowerMatch_adequate_of_typed`); the
bridge just wires it into the `Lowers` match case.

## Recommended starting point

Items 1–2 first (surface `DataDecl` + its lowering → `elabDecls`; `Surface.Ty →
Core.Ty` + annotation kind-checking) — they're house-style, low-risk, need only
the `KindEnv`, and warm you up on the `Lowers`-relation-+-`lower`-function-+-
soundness/completeness pattern before the `Expr` case. Add `Pair` to
`preludeDecls` (needed for tuple sugar). Then the `Expr` `Lowers` skeleton
(name resolution, `app`/λ/`letIn`), then sugar, then wire the `match` case to
`lowerMatch_adequate_of_typed`, then exhaustiveness, then top-level SCC.

## The one hard-won lesson (heed this)

**A predicate or theorem can be subtly FALSE or vacuous even when it "looks
right" and everything around it type-checks.** Today's blocker: the
`CtorSwitches` side-condition had been stated to recurse into _every_ case
branch of the decision tree; that made it _unsatisfiable_ for well-typed
scrutinees whose actual constructor differs from a branch's assumption. The
theorem carrying it stayed **sound** but **vacuous** for those inputs, and the
planned discharge was impossible. Crucially, it was **not** caught by staring at
proofs (the proofs of everything around it went through, and the test suite
passed) — it was caught by **constructing a concrete instance and `#eval`-ing
it** (`root = A 5` against patterns testing `B`'s field).

So, before investing in a big proof of any new predicate / relation:

- **`#eval` the executable side on adversarial inputs** — especially
  mismatched, non-matching, wrong-shape, empty, and out-of-range ones.
- **Check your hypotheses are actually satisfiable** — construct a witness so
  you're not about to prove something vacuously true.
- This applies _double_ to `Lowers` **completeness** and to `checkExhaustive`:
  it is easy to state a checker or a completeness lemma that is trivially true.

## Non-negotiables (from the house rules)

- Headline theorems stay `sorry`/`admit`/`axiom`-free and axiom-clean
  `{propext, Classical.choice, Quot.sound}`; gate every increment with a
  fresh-olean `lake build` + `#print axioms` (the LSP alone is NOT the gate
  after a `Core` edit — the stale-olean trap is real).
- **Core stays minimal**: front-end concerns live outside Core's metatheory
  (a new bridge module and `Decls.lean`), never in Core.
- **File discipline**: no new `.lean` files without strong justification (the
  project runs on 9).
- Don't weaken headline statements; add hypotheses to internal helpers instead.
- Delegate bulk proof-plumbing to subagents with precise per-error specs; keep
  design decisions (relation shapes, statement wording) and the build/axiom
  gate in the parent. Granular commits per slice.
- Append to the design memo's / a status log as you land things; don't rewrite
  history.
