<!-- Written 2026-07-06 as a THINKING/DESIGN brief, spun off from
     next-agent-brief-surface-bridge.md (item 5) during the fork-1 discussion.
     This is the "Option B" escalation: behaviourally-verified pattern-match
     compilation. It is NOT scheduled work — the surface bridge ships with
     Option A (type-preservation only). Read the surface-bridge brief and its
     DESIGN REFERENCE (next-agent-brief-primitives-typedecls-surface.md) first. -->

# Brief: behaviourally-verified pattern-match compilation ("Option B")

## 0. What this is, and what it is NOT

The surface→Core bridge lowers nested surface patterns into Core's **flat,
single-level** `match_`. There are two possible correctness bars for that
lowering:

- **Option A (the shipping plan):** prove the compiled Core `match_` is
  well-typed and exhaustive. This gives full *type safety* of the surface
  program end-to-end (Core's `type_safety_star` applies to the lowered term),
  but says **nothing** about whether the compiled code computes the *answer* a
  human reading the nested patterns expects. Branch order and variable binding
  are runtime properties, and typing is blind to them — e.g. `match (a,b) with
  (x,y) => x` and a buggy compilation that returns `b` are *both* well-typed
  (same type). Under A, behavioural correctness is *trusted* (review + `#eval`
  / `#guard` tests).

- **Option B (this brief):** give the surface language its own semantics for
  matching, and *prove* the lowering preserves behaviour — the compiled Core
  term selects the same branch and binds the same values as the surface match,
  for every (well-typed) scrutinee. This is the gold-standard "verified
  pattern-match compilation" result.

**Your job is to THINK and DESIGN, not to land the whole thing.** Produce: (1) a
concrete architecture decision (the IR/denotational pivot below), (2) the exact
statement of the top-level theorem and the enumerated hard lemmas, (3) an
honest risk/effort assessment, and ideally (4) a **minimal end-to-end spike**
(one tiny matrix, proven equivalent) that de-risks the approach before anyone
commits to the full campaign. Nothing here touches Core's metatheory: the
surface semantics is a *new leaf module*, and Core's `Step` is reused unchanged
as the target. Do NOT add to Core.

## 1. The target semantics (Core) — already built, reuse verbatim

Everything you compile *to* already exists and is proven. Ground your source
semantics against these so the two sides line up by construction.

- **Patterns are flat** (`FHM/Core.lean` ~L193): `MatchPattern.named (ctor)
  (contents : Nat)` (tests one ctor at arity `contents`, binds `contents`
  fields) or `MatchPattern.wildcard`. `bindCount`/`matchesCtor` alongside.
- **Match reduction** (`Step`, ~L1129):
  ```
  matchReduce : IsValue scrut → CtorAppliedTo scrut name args →
                FirstMatchingBranch name args.length branches pat body →
                Step (.match_ scrut branches) (body.substN 0 (args.take pat.bindCount))
  ```
  So the **first** applicable branch (`FirstMatchingBranch`, ~L1095 — the
  declarative twin of the executable `findMatchingBranch`, ~L1227) fires, and
  its body is opened by substituting the ctor's args **positionally** at de
  Bruijn 0.. (`substN 0 (args.take bindCount)`; args are in
  constructor-application order, see `getCtorArgs` ~L1220).
- **Non-ctor scrutinees** (`matchWildReduce`, ~L1139): a value that is not a
  ctor chain (an `Int`, a function, …) can only be consumed by a **leading**
  `wildcard` branch. `isValue`/`isCtorChain` (~L1202) are the decidable value
  checks.
- **Exhaustiveness is orthogonal to typing** (`AllMatchesExhaustive`, ~L1752):
  it is a premise of `progress` ONLY — not of `TypeOfHM`, not of
  `preservation`. So a refutable / non-exhaustive match is perfectly
  well-typed; it just may get stuck. (This is why Option A can ship without the
  behavioural proof.)

Key consequence for you: Core's match is *already* essentially a one-level
decision node (multi-way switch on the scrutinee's ctor tag + a wildcard
default), and nesting `match_` inside branch bodies gives you exactly a
**decision tree**. You are not inventing the target IR — Core's nested `match_`
*is* one.

## 2. The source semantics you must build (keep it minimal)

You need just enough surface dynamics to *state* "which branch fires, with what
bindings." Two decisions that shrink the work dramatically — take both:

- **Reuse Core values as surface values.** The surface has no independent
  runtime; "running a surface program" = lower then run Core. So a surface
  value *is* a Core value. Define matching over Core value-`Expr`s (with
  `IsValue`), NOT a parallel `Surface.Value` algebra. This deletes an entire
  value-correspondence relation.
- **Represent bindings as an ordered list of captured sub-values**, in
  left-to-right *occurrence* order — NOT a name→value map. Core binds
  positionally via `substN`, so an ordered list is what actually has to line up.
  Name→de-Bruijn resolution is a *static* concern handled during lowering (item
  3 of the main brief); keep it out of the dynamic statement.

Then the source side is two small definitions:

```
-- `none` = this pattern REFUTES this value (⇒ try the next branch).
-- `some vs` = it matches, capturing sub-values `vs` in occurrence order.
matchPat  : Expr → Surface.Pattern → Option (List Expr)
firstMatch : Expr → List (Surface.Pattern × β) → Option (Nat × List Expr × β)
```

`matchPat` recurses structurally (ctor tag-test + recurse into sub-patterns,
concatenating captures; a sub-`none` makes the whole thing `none`; `name`/`wildcard`
are irrefutable, `name` captures the whole value, `wildcard` captures nothing;
`pair`/`cons`/`list` are ctor-tests in disguise — `Pair`/`Cons`/`Nil`).
`firstMatch` walks branches top-to-bottom returning the first `some`. **This
little pair is where first-match order and binding live** — and thus exactly
what the compilation must preserve.

Worked intuition:
```
matchPat (Just 5)              (ctor "Just" [name x])                   = some [5]
matchPat Nothing               (ctor "Just" [name x])                   = none
matchPat v                     wildcard                                 = some []
matchPat (Pair (Just 3) 7)     (pair (ctor "Just" [name x]) (name y))   = some [3, 7]
```

## 3. THE central design idea: a decision-tree IR pivot (compare denotations, not syntax)

The naive Option-B theorem — "relate the surface match AST directly to the
nested Core `match_` Expr" — forces you to juggle two concrete syntaxes with
different binding structures ("shuffling Exprs"). Avoid it. Introduce a shared
semantic pivot so the final equivalence is **extensional equality of functions
on values**, which needs zero syntactic manipulation.

Proposed architecture (this is the thing to evaluate and, if sound, spike):

1. **A decision-tree IR `DTree`** with an occurrence-indexed interpreter
   `evalDTree : DTree → Expr(value) → Option (Nat × List Expr)` (returns the
   selected leaf id + captured values). `DTree` leaves carry an explicit
   **occurrence vector** (the paths into the scrutinee that were bound, in
   order) — this vector is the *single source of truth* for both the surface
   name→index resolution and the Core `substN` order, which is precisely how
   binding-preservation becomes checkable rather than hand-waved.
2. **`compile : Matrix → DTree`** — the pattern-compilation algorithm
   (see §5 for which one; recommend the naive leftmost-column scheme).
3. **`emit : DTree → Core.Expr`** — render the tree as nested `match_`.
4. **`readback : Core.Expr → Option DTree`** — recover the tree from a Core
   match (structural; total on the shape `emit` produces).

Then behavioural correctness factors into independently-statable pieces, and
the headline is a *function equality*:

- **(H1) Algorithm correctness (the irreducible core):**
  `∀ v, evalDTree (compile M) v = matrixSemantics M v`
  where `matrixSemantics` is the `firstMatch`/`matchPat` first-match spec of §2.
  This is the real theorem (Maranget's specialization/default lemmas live here —
  see §4). **The IR does NOT make this easier; it just gives it a clean
  statement.** Everything else is bridging.
- **(H2) Core adequacy:** `evalDTree (readback c)` predicts Core's actual
  reduction — i.e. if `evalDTree (readback c) v = some (i, vs)` then
  `match_ v c` multi-steps (via `matchReduce`/`matchScrut`/`matchWildReduce`)
  to leaf `i`'s body opened by `vs` at the right de Bruijn indices; and the
  refutation/`none` case corresponds to stuck-ness. Proven ONCE, generic over
  the tree. This is the only place Core `Step` re-enters.
- **(H3) Emission round-trip:** `evalDTree (readback (emit t)) = evalDTree t`
  (structural; ideally `readback (emit t) = some t`).
- **Top-level:** compose H1–H3 into
  `∀ v, coreBehaviour (lower (match M)) v = surfaceBehaviour (match M) v`,
  stated as equality of `Value → Option (branch × bindings)` functions. No Expr
  shuffling anywhere in the *statement*; the syntactic reality is quarantined in
  H2/H3.

Why this is "not behaviourally different in a clean way": the surface matrix and
the compiled Core term are each given a **denotation** (a function from values
to outcomes), and you prove the denotations *equal*. The decision tree is simply
the concrete carrier of the Core-side denotation, and — conveniently — Core's
own nested `match_` already *is* a decision tree, so `readback` is cheap.

Evaluate alternatives to this exact shape too: (a) skip `DTree`, give surface
and Core matches *direct* denotations `Value → Outcome` and prove those equal
(even lighter, but you lose the occurrence-vector scaffolding that makes binding
checkable — probably a false economy); (b) a small-step *bisimulation* between a
surface match-machine and Core `Step` (heavier, only worth it if you later give
the whole surface an operational semantics). Recommend the `DTree` denotational
pivot unless you find a concrete reason it breaks.

## 4. The hard problems, enumerated honestly

The IR relocates difficulty into clean statements; it does not remove it. In
rough order of nastiness:

- **(HARD, irreducible) H1 = the specialization/default lemmas.** Maranget's
  compiler works by picking a column, then forming the **specialized matrix**
  `S(c, M)` (rows that can match ctor `c`, with `c`'s sub-patterns spliced into
  that column) and the **default matrix** `D(M)` (rows with a wildcard there).
  Correctness rests on proving, over *every* pattern form and threaded through
  the recursion, the key equations:
  `matrixSem M (c(w₁..wₐ) :: vs) = matrixSem (S(c,M)) (w₁..wₐ ++ vs)` and the
  wildcard/default analogue. The value and pattern *vectors get reshaped*
  (arity spliced in and out) at every recursive step, so this is voluminous
  index/arity bookkeeping — not conceptually deep, but exactly the kind of
  thing that is a slog to machine-check and easy to get subtly wrong. This is
  the "research-grade" heart, and it is the same whether or not you use a
  `DTree`.
- **(MEDIUM–HARD) H4 = occurrence ↔ de-Bruijn binding alignment.** Core opens a
  branch body with `body.substN 0 (args.take bindCount)`; nested matches add
  binders, so a variable bound at an *outer* test ends up at a shifted index
  deep inside. Proving the right captured value reaches the right `.var i`
  through all the nesting/shifting is where most machine-checked tedium
  concentrates. The `DTree` occurrence vector is your weapon: make it the
  canonical order and prove `emit` places bindings at exactly those indices and
  the surface resolver reads names against the same order.
- **(MEDIUM) H2 = Core adequacy.** Connect `evalDTree`/`readback` to real
  `matchReduce`/`matchScrut`/`matchWildReduce` multi-step reduction, including
  the leading-wildcard rule for non-ctor scrutinees. Localized but must handle
  the reduction-order congruence (`matchScrut` reduces the scrutinee first).
- **(AVOIDABLE) H0 = column-order independence.** Maranget's *heuristics* choose
  which column to test to make trees small; a correct compiler must give the
  same first-match result regardless of column choice, which is its own theorem.
  **Dodge it entirely by fixing a deterministic column order (always leftmost).**
  Tree size is irrelevant to a verified reference compiler.
- **(SHRINKABLE) value scope.** State H1/the top-level over **well-typed
  scrutinee values only** (using Core typing to know the scrutinee inhabits the
  matched ADT). This prunes impossible-ctor cases and lets exhaustiveness carry
  its weight. Decide between full *bisimulation* (both directions) and
  *refinement* ("surface produces a value ⇒ Core produces the same value";
  surface stuck ⇒ Core may be stuck) — refinement is usually the right, lighter
  target for a pure language.

## 5. Algorithm choice — pick the easiest to VERIFY, not the best codegen

- **Recommended: the naive leftmost-column ("Wadler"-style) matrix algorithm.**
  Same `S(c,M)`/`D(M)` machinery as Maranget, minus the heuristic column choice —
  which *kills H0 outright*. Produces possibly-larger trees; for a verified
  reference lowering nobody cares.
- **Maranget "good decision trees" (ML Workshop 2008):** the deployed, small-tree
  algorithm (OCaml lineage). He gives a real *solution* + correctness argument,
  not just a problem statement — but the column heuristics buy you H0 for no
  correctness benefit. Only pursue if small trees are a goal (they aren't here).
- **Backtracking automaton (Maranget's other scheme):** closer to the naive
  first-match semantics, sometimes argued easier to relate to the spec, but
  emits code with backtracking that maps less directly onto Core's `match_`.
  Consider only if the decision-tree adequacy (H2) proves unexpectedly painful.
- **Exhaustiveness / usefulness** is Maranget's *"Warnings for pattern
  matching" (JFP 2007)* algorithm — the same theory behind the surface bridge's
  item-6 checker. If Option B is pursued, unify with that checker so
  "compiled tree exhaustive ⇔ surface matrix exhaustive" is one story feeding
  Core's `progress` premise.

Prior art to lean on (this HAS been done, it is a known quantity, not a research
dead-end): CakeML's verified pattern-match compiler; assorted Coq/Isabelle
verified-match-compilation developments. Calibration: a verified-compiler-pass-
sized effort (weeks–months), self-contained, on top of the shipped Option-A
bridge.

## 6. Suggested path

1. **Design memo** (no code): commit to the §3 architecture (or a justified
   variant), write the exact `DTree`, `evalDTree`, and the top-level theorem
   statement, and enumerate H1–H4 as precise Lean signatures (`sorry`-stubbed).
2. **Minimal spike** to validate the shape before the slog: restrict to a
   two-column matrix over `Bool`/`Pair` (finite, no recursion), implement
   `compile`/`emit`/`readback`/`evalDTree`, and prove H1+H2+H3 for that
   fragment end-to-end, axiom-clean. If the occurrence↔de-Bruijn alignment (H4)
   goes through cleanly on `Pair` (which introduces nested binders), the
   approach is sound; if it fights you here, it will fight you everywhere —
   report back before scaling.
3. **Generalise** `matchPat`/`S`/`D` to arbitrary ctors + `Cons`/`Nil`/`list`,
   fill H1 across all pattern forms, then the recursive/ADT cases.
4. **Wire to the bridge:** replace (or wrap) Option A's `lower`-for-match with
   the verified `compile ∘ emit`, and connect exhaustiveness to `progress`.

## 7. Non-negotiables (inherited from the campaign)

- Headline theorems stay `sorry`/`admit`/`axiom`-free and axiom-clean
  (`{propext, Classical.choice, Quot.sound}`); gate real milestones with a
  fresh-olean `lake build` + `#print axioms`, not the LSP alone.
- **No Core metatheory changes.** The surface semantics + `DTree` live in a new
  front-end module importing `FHM.Core` (and the surface-bridge module); Core's
  `Step`/`match_`/`AllMatchesExhaustive` are consumed as-is.
- Don't weaken headline statements; add hypotheses (typedness of the scrutinee,
  exhaustiveness) to the *internal* lemmas and discharge them at the top.
- This is exploratory: if the spike says the effort is disproportionate,
  Option A remains a perfectly respectable shipping state — say so plainly.

## 8. Open questions to resolve in the design memo

- Bisimulation vs refinement (which direction(s) do we actually want)?
- Do we ever need the surface's *whole-expression* opsem, or does matching-only
  (values already produced by Core evaluation) suffice? (Almost certainly the
  latter — the scrutinee is a Core value by the time a match fires.)
- Is `readback` worth it, or state H2 directly on `emit t` (skip the round-trip
  H3)? Round-trip is cleaner; direct is fewer moving parts.
- How does the occurrence vector interact with the `name`/`wildcard`/nested-`ctor`
  capture order so it agrees with the surface term's name-resolution pass
  (shared source of truth, or two passes proven equal)?
