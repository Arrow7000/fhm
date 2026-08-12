# Where FHM's complexity budget goes

**Status:** Analysis, 2026-08-12. Written to answer "why is Core 10k and InferW 20k, and can we
make this simpler before the next big proof campaign?"

Companion to `next-agent-brief-path-r-dual-stack.md` (active work) — this brief is about
*design*, not the current farm.

---

## 0. Bottom line

`letRec` is the biggest single line item, but it is a **symptom**. Three design choices
compound, and `letRec` is where all three meet:

1. Algorithm W with explicitly threaded, `++`-composed substitutions and an explicit `Φ`
   freshness counter.
2. Elaboration fused into inference, with two typing relations and two soundness theorems.
3. `letRec`'s **shape-changing elaboratum** (`Expr.letRecElab`) — which is what makes (2)
   cost a second full induction instead of a corollary.

Fixing (3) is the highest-leverage move and — per §3.4 — does **not require changing `Expr`**.

**Status (2026-08-13):** spiked over three rounds in `FHM/SpikeLetRecPromote.lean`. The gate —
the general transport `MonoTyped → PolyTyped` at the promoted schemes — is **proved and
axiom-clean** (§3.6). What remains is bookkeeping-shaped, not existential: the stored-form
retarget traversal, rewiring `Infer.letRec`, preservation, and the Path R erase-commutes. The
effort estimate remains the weak part of this brief; the *viability* question is settled.

---

## 1. Measured distribution

### `Infer.sound` — 1,223 lines, by case

| case | lines | share |
|---|---:|---:|
| `letRec` | 574 | **47%** |
| `letInAnn` | 240 | 20% |
| `letIn` | 161 | 13% |
| `app` | 101 | 8% |
| `match_` | 56 | 5% |
| `lambda` | 44 | 4% |
| prims / `var` / `ctor` | 38 | 3% |

Binding forms are 80%. Everything that is not a binder — application, matching,
constructors, literals — is 20%.

### File-wide

| | Core.lean | InferW.lean |
|---|---:|---:|
| total | 10,975 | 19,302 |
| decls named for letRec machinery | 74 (911 ln) | 120 (**4,113 ln, 21%**) |
| freshness/scope invariants of the algorithm | — | ~3,900 ln (**20%**) |
| erase/PathR residual | ~540 ln | ~1,700 ln |

The freshness family — `Infer.lc`, `dom_below`, `dom_avoid`, `gap_avoid`, `eOut_avoid`,
`belowFvars`, `eliminates`, `block_fresh` — proves nothing about *types*. It exists only to
state "the algorithm does not clobber variables it should not," and it exists in that volume
because freshness is an explicit `Φ : Nat` threaded through the relation.

---

## 2. The three multipliers

### 2.1 Substitution-threading Algorithm W

`Infer Φ ctx e Φ' S eOut τ` composes substitutions with `++` and pre-applies them to
contexts. `InferBranches.cons` carries `S₂.onCtx (S₁.onCtx (S₀.onCtx ctx))`. Every soundness
case must push a composed substitution through a context, a term and a type, and show the
pushes commute. The `Φ` counter then requires the ~3,900-line invariant family above.

Largest single cost. Structural, not incidental. See §4 for whether constraints fix it.

### 2.2 Fused elaboration, two relations, two soundness theorems

`Infer` emits `eOut` alongside `S` and `τ`. So:

- `Infer.sound` (1,223 ln) — about `eOut`
- `Infer.sourceSound` (656 ln, still carrying the open `sorry`) — about `e`

`TypeOfElabHM.faithful` (`Core.lean:5260`) is ~30 lines and trivial: the two relations
differ only at `var`. It cannot bridge `sound` → `sourceSound`, because `eOut` and `e` are
different *trees*. So the induction runs twice.

Elaboration is shape-preserving for **every form except `letRec`** — elsewhere it only fills
`Option` slots and `tyArgs`. `letRec` alone changes the tree.

### 2.3 `letRec`'s shape-changing elaboratum

See §3.

---

## 3. `letRec` in a nutshell

### 3.1 What the source node means

```lean
Expr.letRec (anns : List (Option PolyTy)) (bindings : List Expr) (body : Expr)
```

All `n` bindings *and* the body share one binder scope (member `j` at de Bruijn index `j`).
Per member:

- **annotated** (`some σ`) — in scope at its full scheme inside the RHSs, so recursive uses
  may instantiate `σ` at different types. Polymorphic recursion; decidable because annotated.
- **unannotated** (`none`) — typed at a shared monotype *inside* the group (this is what
  keeps mutual recursion's types linked), generalised over the shared pool `G` only for the
  **body**. Damas–Milner monomorphic recursion.

`TypeOfElabHM.letRec` (`Core.lean:3258`) expresses exactly this: `RecSpecs.rhsCtx` binds
monos at their opened monotypes and polys at their schemes; `RecSpecs.bodyCtx` binds monos at
`∀(G ∩ ftv τ). τ`.

### 3.2 Why elaboration cannot leave it alone

FHM does not erase types. A polymorphic use at runtime is `var j [T₁ … Tₖ]`, and
`Expr.substN` (`Core.lean:1333`) discharges it by type-beta: `(vs[i-k]).instTy tyArgs`. So a
polymorphic binding needs a **Λ-binder for its type arguments to instantiate**.

An annotated member has one: its stored `σ`. An unannotated member does not — its
generalisation is invented by the typing rule (`bodyScheme G`), not stored in the term.

So `Infer.letRec` hoists the Λ **outside** the node. `Expr.letRecElab` /
`letRecElabNest` (`InferW.lean:2479`) emit, for each member `i`:

```lean
.letIn (some (PolyTy.genGroup G τᵢ))
  (closeTyVars (Ty.genFilter G τᵢ)
    (.letRec anns (bindings.map (·.shiftFrom n (n-1-i))) (.var i [])))
  ⟨next member⟩
```

That is: **a `let` whose RHS is a whole copy of the group, projected at member `i`.** The
`let`'s scheme is the Λ-binder. `n` members ⇒ `n` copies of an `n`-binding group, plus de
Bruijn `shiftFrom` renumbering. O(n²).

### 3.3 Why it is expensive out of proportion

- The elaborated tree has a **different shape** from the source, so `Infer.sound`'s letRec
  case cannot be a structural application of `TypeOfElabHM.letRec` — hence 574 lines and the
  dedicated support cast (`letRecElabNest_sound`, `letRec_body_retype`,
  `letRecFused_body_retype`, `letRecFused_residual_setup`, `RecGroup.shiftFrom`, …).
- Shape divergence is also what blocks §2.2: with it, `sourceSound` cannot be a corollary.
- Path R doubles the bill, since the residual `sourceSound` mirror inherits the same shape
  problem. The one remaining soundness `sorry` in the tree is exactly this case.

### 3.4 The fix, and whether it touches `Expr`

**It appears not to.** Put the Λ *inside* the node by using the `anns` slot that is already
there — promote every unannotated member to an annotated one at its generalised scheme:

> Elaborate a mono member with `anns[j] := some (∀G. τⱼ)` — generalising over the **full
> pool `G`**, not `Ty.genFilter G τⱼ` — store its RHS closed over `G`, and retarget
> group-internal references from `var j []` to `var j (bvarRange |G|)`.

Why the full pool rather than the filter: with full `G`, every promoted member has
`paramCount = |G|` and identical binder positions, so a sibling reference
`var j (bvarRange |G|)` means "instantiate sibling `j` at *my* pool binders" uniformly across
the group. That is precisely what reconstitutes the shared-monotype link that `MonoTyped`'s
"same `Xs` for the whole group" is enforcing.

**This is legal because `PolyTy.WF` is an upper bound, not a usage requirement:**
`PolyTy.WF M := ContainsBvarsUpTo M.paramCount M.body` (`Core.lean:2875`). A scheme with
vacuous binders is well-formed. Under `genFilter` the arities differ per member and the bvar
indices would not line up; under the full pool they do.

Note this means *not* reusing `PolyTy.genGroup`, which is defined over the filter
(`Core.lean:2918`): the promoted scheme is `⟨G.length, Ty.closeOver G τ⟩`. That needs its own
renaming-lemma set — but it should come out **shorter**, not longer. Roughly half of
`TypeOfElabHM.rewrap_hasScheme_mono`'s 79 lines is `genFilter` round-trip bookkeeping
(`Ty.renameG_eq_genFilter`, `PolyTy.genGroup_renameG`, `hYlen`, `hGFnodup`, `hGF_disj`,
`Ty.mem_of_mem_genFilter`). With a full pool, `(∀G.τ).openVars Ws` is just `Ty.renameG G Ws τ`
and all of that vanishes.

Consequences if it holds:

- The elaboratum is a plain `.letRec` with filled-in `anns`. **`Expr` unchanged** — this is
  ordinary slot-filling, the same kind elaboration already does for `letIn`.
- `letRecElab`, `letRecElabNest`, `letRecElabNest_sound`, `letRec_body_retype`,
  `letRecFused_body_retype`, `letRecFused_residual_setup`, `shiftFrom` plumbing: gone.
- With all members poly, `rhsCtx` no longer depends on the pool opening `Xs`, so
  `RecSpecs.PolyTyped`'s outer `Xs` quantifier goes vacuous and `MonoTyped` disappears. The
  `RecSpec` mono/poly split — and the `consMono`/`consPoly` case split in every group lemma —
  collapses to one uniform form.
- Elaboration becomes shape-preserving **everywhere**, which unlocks §2.2: replace
  `Infer.sourceSound` with a strengthened faithfulness lemma
  `Decorates e e' → TypeOfElabHM ctx e' τ → TypeOfHM ctx e τ`, proved **once** by structural
  induction on `TypeOfElabHM` and stable against future changes to `Infer`.
  `Infer.preservesAnns` is already most of the other half.
- Operationally this is the *existing annotated path* (`Step.letRecUnfold` +
  `RecGroup.shieldDepths`/`instTyAux`), now uniform in depth instead of mixed.

### 3.5 Known costs and open risks

Honest accounting — this is a sketch, not a verified plan.

1. **New term rewrite.** Group-internal references inside mono RHSs are currently `var j []`,
   valid because `rhsEntry` binds siblings at `mkTrivial` (paramCount 0). After promotion the
   sibling has paramCount `|G|`, so `Ty.AreLC polyTy.paramCount tyArgs` forces
   `var j (bvarRange |G|)`. That needs a depth-tracking `RecGroup`-level map plus its commute
   lemmas with `substTyFvars` / `eraseBounds`. Estimate 200–400 lines. It is shape-preserving,
   so it does not cost the §2.2 win.
2. **Soundness transport.** `Infer.sound`'s letRec case must derive `PolyTyped` for promoted
   members: rename `G ↦ Ys` through W's mono derivation, then reconstitute each sibling use as
   `var j` instantiated at `Ys`. The ammunition exists —
   `TypeOfElabHM.typ_subst_preservation_uniform` for the renaming, and the whole
   `renameG`/`closeOver`/`openVars` transport kit exercised by
   `rewrap_hasScheme_mono` (`Core.lean:9247`). Not yet checked end to end.
3. **Preservation.** Expected *easier*, and there is direct evidence.
   `TypeOfElabHM.rewrap_hasScheme_mono` / `_poly` (`Core.lean:9247`, `9326`) already prove the
   load-bearing semantic fact — a member of the re-wrapped group
   `.letRec anns bindings eⱼ` **has its body scheme, at arbitrary instantiation `Vs`**. That
   is exactly what `letRecElab` is encoding syntactically, which is good evidence the
   promotion is semantically right rather than a reshuffle. And `rewrap_hasScheme_poly`'s key
   step — `instTy Vs` is a no-op on the inner group because every member is `TyBvarBounded`
   at its own annotation's arity — carries over directly: promoted mono members are closed
   over `G`, hence bounded at `|G|`, hence the same argument applies with *uniform* depth
   instead of the current mixed `shieldDepths`.
4. **Completeness is unaffected** — it is stated against `TypeOfHM` on the *source* term,
   whose `anns` are still `none`.

### 3.6 Spike results — three rounds (`FHM/SpikeLetRecPromote.lean`, 2026-08-12/13)

Round 1 validated shape, round 2 the discriminating configurations, round 3 the transport.
Rounds 1–2 below; round 3 (the gate) and the honest remaining scope are at the end.

#### Round 1 (2026-08-12) — partial green

`FHM/SpikeLetRecPromote.lean` (not in `defaultTargets`). All goals proved, no `sorry`, no
added axioms, statements unweakened.

**Confirmed:**

- `promoteScheme_wf` — `Ty.closeOver_preserves_bvars hτ`, one term. Vacuous binders are fine,
  as §3.4 requires.
- `promoteScheme_openVars` — `Ty.openVars_closeOver_rename hτ hG hlen hdisj`, one term, no
  filter round-trip. This is direct support for "full pool is cheaper than `genFilter`":
  compare the ~40 lines of filter bookkeeping inside `rewrap_hasScheme_mono`.
- `S1_mono` / `S1_promoted` / `S2_mono` / `S2_promoted` all typecheck. The promoted node is a
  plain `.letRec` with the slot filled — `Expr` untouched, as claimed.

**What round 1 did NOT test:** `n = 1` (no siblings, so the mechanism the full pool exists for
was untouched) and `τ` mentioning all of `G` (so `genFilter G τ = G` and the full-pool choice
was indistinguishable). `sσ` was also literally `LetRecAnnSmokeTest.selfSig`, so `S2_promoted`
partly re-trod the already-working *annotated* path.

### Round 2 — the discriminating tests (`D1`/`D2`). Green.

Both on pool `G₂ = [0,1]`, both proved, no `sorry`, statements unweakened.

- **`D1`** — genuinely *mutual* pair, both at `τA = fvar 0 → fvar 0`. Neither mentions pool
  var 1, so each promoted scheme carries a **vacuous** binder (arity 2, where `genFilter`
  would give 1). Both directions of the mutual call type against the same uniform
  `tyArgs = [.bvar 0, .bvar 1]`.
- **`D2`** — members at `τA` and `τB = fvar 1 → fvar 1`, promoting to `⟨2, bvar 0 → bvar 0⟩`
  and `⟨2, bvar 1 → bvar 1⟩`: same arity, **vacuous in opposite slots**. One uniform retarget
  serves both — `σA`'s instantiation reads index 0, `σB`'s reads index 1.
- A machine-checked confirmation that the tests actually discriminate:
  `PolyTy.genGroup G₂ τA = PolyTy.genGroup G₂ τB = ⟨1, arrow (bvar 0) (bvar 0)⟩` — `genFilter`
  really does collapse the two distinct schemes to the same arity-1 scheme, losing `σB`'s
  binder position.

Vacuous binders caused no trouble anywhere: `poly_wf` falls to `promoteScheme_wf` (upper
bound), and in `InstantiatesBy` an unused slot's `tyArgs` entry must be *present* for the
arity check but is never consulted.

### Two findings from round 2 to carry into the design

1. **The retarget covers the body, not just the bindings.** The mono body sees
   `PolyTy.genGroup G τ` at *filtered* arity; the promoted body sees the full-pool scheme. So
   the body's `var` `tyArgs` arity changes too. Slightly widens the traversal in §3.4.
2. **Promotion removes a `renameG` hazard.** `Ty.renameG` is a *sequential* `substFvars` over
   `G.zip Xs`, so with `|G| ≥ 2` it can self-capture unless `Xs` is disjoint from `G` — which
   `RecSpecs.MonoTyped` only guarantees when its `L` includes `G`. Existing Core callers do
   pass `G` into the avoid set (see `rewrap_hasScheme_mono`), so this is a latent sharp edge
   rather than a bug, and it is a usability wart rather than a soundness hole. **The promoted
   regime has no analogue**: `promoteScheme`'s body is pre-closed and opened by direct bvar
   index lookup, never by sequential fvar substitution. An unanticipated point in favour.

### Round 3 — the transport (`T1`/`T2`). Green, axiom-clean.

The gate identified above. Both proved; `#print axioms` guard in the file reports
`[propext, Classical.choice, Quot.sound]` for `T1`, `T2`, `P1`, `P2`, `S2'`, `D1'`, `D2'` —
no `sorryAx`. Independently verified: single additive diff hunk (nothing above the T section
touched), statements byte-identical to as authored, `retargetVars`' window condition intact
(an identity retarget would have made `T1` vacuous).

- **`T1_retarget_transport`** — the mathematical core. The `TypeOfElabHM` analogue of
  `TypeOfHM.weaken_schemes`, *with the term rewrite that the type-passing `var` rule forces*.
  Swapping an env prefix of `PolyTy.mkTrivial μₖ` (arity 0) for schemes `Mₖ` with
  `Mₖ.InstantiatesTo Vs μₖ` preserves typing, provided uses in the window are retargeted to
  `Vs`. Proved by `TypeOfElabHM.rec_strong` on the `weaken_schemes` template, with the `ep`
  accumulator and invariant `b = ep.length`.
- **`T2_monoTyped_to_polyTyped`** — the letRec corollary: `MonoTyped` at shared monotypes
  yields `PolyTyped` at the full-pool promoted schemes. The pool quantifier forces `Xs = []`,
  confirming in the proof that `rhsCtx` stops depending on the pool opening once every member
  is `poly`.

Cost datum: the whole T section is **565 lines**, including `retargetVars`/`Branches`/`Group`,
their commute lemmas with `openTyVars`/`openBoundTyVars`, and length/membership plumbing.

### Status: gate passed, refactor not done

`§3.4`'s core claim is established — no structural obstruction, and the transport is real
rather than a repackaging (nothing in the codebase did this before, because `letRecElab`
exists precisely to avoid needing it). Remaining, in rough order:

1. **The stored retarget and its commute — `T2`'s `hopen` is still a hypothesis.** The spike
   works on *opened* terms, where `Vs` are concrete `fvar`s and depth-independent.
   `retargetVars_openTyVars` commutes that with `openTyVars` at the *same* `Vs` — it is **not**
   the stored-vs-opened fact. The stored form puts `Ty.bvarRangeFrom d |G|` in the term, so it
   needs type-binder depth tracking, and `hopen` needs
   `(storedRetarget e).openTyVars Ys = retargetVars n (Ys.map Ty.fvar) b (e.openTyVars Ys)`.
   This is the "depth-tracking traversal" §3.4 estimated at 200–400 lines; still unwritten.
2. **Rewire `Infer.letRec`** to emit the promoted node, and rewrite `Infer.sound`'s letRec case
   (574 lines) against it. The claimed collapse is untested.
3. **Preservation for the promoted node** — still untested. Argued easier (uniform depth `|G|`,
   and promotion removes the `renameG` sequential-substitution hazard), not checked.
4. **Path R erase-commute lemmas** for the new traversal — a real cost not yet estimated;
   InferW's existing erase-commute block is 577 lines for the operations it already has.
5. **Completeness interaction** — unknown, and per the Path R brief the completeness
   statements need repair before anything is farmed against them.

---

## 4. Constraint-based inference (HM(X) / Pottier–Rémy)

Conceptual estimate only — there is no implementation beyond the 238-line stub at
`FHM/ConstraintTypeSystem.lean`, whose `CScheme.WF` is `cs.vars = [] ∧ cs.body.IsLC` with a
`@TODO`: it proves the guard-free *monomorphic* fragment and never enters the hard case.

**Verdict: ≈1.1× the current size of the inference stack (band 0.9–1.4×). Do not do it.**
That is the *steady state*; the transition cost is roughly another 100% of InferW's 19.3k
lines, and would strand Path R one `sorry` from closing.

### The pivot

Constraint-based inference is a technique for computing **types**. FHM must compute a
**term**. Every published win — substitution-free rules, principality by construction, clean
`let` — is a win about types, and FHM pays the elaboration tax either way. This is the same
multiplier as §2.2, seen from the other side.

Concretely, constraint generation is type-agnostic by design and therefore cannot emit the
`letIn` elaboratum, whose binder structure is *solution-dependent*:

```lean
.letIn (some (genScheme …)) ((rhsOut.substTyFvars S₁).closeTyVars (genVars …)) bodyOut
```

`closeTyVars genV` is not hole-filling — it is a Λ-abstraction whose arity is unknown until
solving. Same for `letRecElab`'s nest shape. The options are a second `Elab` pass proved
sound separately (**+2,500–4,000**, and it reinstates the letRec elaboration case nearly
verbatim), or elaboration-carrying constraints à la Pottier's `inferno` (**+2,000–3,000**,
and much heavier in Lean than in OCaml).

Note the corollary: **if type-passing were dropped, the estimate falls to ~0.65×.** But the
README already litigated erasure and rejected it for a real reason (annotated polymorphic
recursion is strictly stronger than its erasure). That requirement is load-bearing.

### Arithmetic

| | lines |
|---|---:|
| Frontier/counter freshness | −1,800 |
| Completeness / principality | −1,700 |
| Rec-group + branch threading | −800 |
| Pre-substituted context towers | −400 |
| **savings** | **−4,700** |
| Constraint language + binder theory + `Sat` | +1,200 |
| Solver metatheory beyond plain unification | +1,500 |
| Elaboration bridge | +2,500 |
| `sourceSound` re-port, Path R rethreading | +400 |
| **costs** | **+5,600** |

This is a model, not a measurement — treat the band, not the point estimate.

### Notable sub-findings

- **The freshness win is real but obtainable without constraints.** Of the ~4,000 freshness
  lines, `dom_below`/`belowFvars`/`gap_avoid`/`block_fresh` (~2,200) exist purely because
  freshness is an explicit `Nat`. `eliminates` (707) and `eOut_avoid`/`dom_avoid` (~1,100) do
  **not** die — they say the solution doesn't touch variables later generalisation depends
  on, which relocates into the solver's locality proof. See middle path 2 in §5.
- **Principality is the strongest genuine argument** (~3,300 → ~1,600): generation is
  syntax-directed, so completeness collapses to one `Gen`/`Sat` equivalence with principality
  falling out of the already-proved `UnifyRel.isMGU`. Discounted because `Sat`'s
  existential-witness style must still be reconciled with `TypeOfElabHM`'s cofinite `∀ Xs ∉ L`
  at every binder.
- **The binder-representation matrix is orthogonal and gets *worse*.** Constraints add a
  fourth binder-carrying class (`∃α.C`, `∀ᾱ[C].τ`) on top of `Ty`/`PolyTy`/`Expr`.
- **Rémy levels are a formalisation loss.** `genVars` is two lines and *is* the spec; levels
  need a preserved invariant plus an equivalence back to it. +600–1,000 for no proof benefit.
  Good for implementations, bad here.
- **Skolem escape is a wash**, possibly a small loss — the same two-sided obligation, moved
  from a local rule premise to a global solver invariant.
- **Path R is roughly neutral** (−200–400): bounds-blind unification is solver-level, but the
  residual statement is about erased *terms and contexts*, not just unification.
- **Blast radius is small**: SurfaceBridge touches the inference stack in ~42 places, all via
  `typecheck` / `inferCore` / `Infer.sound` / `Infer.sourceSound`. Core is untouched. The one
  leak is `infer_of_typecheck` (`SurfaceBridge.lean:12134`), which destructures the
  `(Φ', S, eOut, τ)` tuple.

### Prior art

Line counts below are **estimates, not verified figures**. Naraschewski–Nipkow (JAR 1999,
Isabelle) and Dubois–Ménissier-Morain (JAR 1999, Coq) are textbook HM only — no ADTs, no
matching, no recursive groups, no elaboration — so they bound the *floor*, and confirm that
FHM's 19k is explained by features, not by the choice of algorithm. Urban–Nipkow's nominal
Algorithm W is evidence that binder representation dominates cost. The closest comparable is
**Garrigue, *A Certified Implementation of ML with Structural Polymorphism*** (APLAS 2010 /
MSCS 2015): Coq, built on the same Charguéraud locally-nameless ML framework FHM follows,
more features than textbook HM — and **W-style, not constraint-based**.

Two absences worth weighting: Pottier–Rémy's constraint framework appears **never to have
been fully mechanised**, and there is **no known mechanised constraint-based HM(X)
development that also produces an elaborated term**. FHM would be doing the uncharted case
without a map.

---

## 5. Other candidates, ranked

**Middle path 1 — stop pre-substituting contexts in non-generalising rules** (Algorithm J
style). Replace `Infer Φ₁ (S₁.onCtx ctx) arg …` with `Infer Φ₁ ctx arg …`, applying the
composed substitution only in the *statement* of soundness, and keeping pre-substitution at
`letIn`/`letRec` where `genVars` genuinely reads the solved env. Kills the
`S₂.onCtx (S₁.onCtx (S₀.onCtx ctx))` towers (171 occurrences of `onCtx (S`) and much of the
`Subst.onCtx_*` congruence surface. **Save 800–1,500.** Caveat: the claim that `eliminates`
already supplies the needed composed idempotence is plausible but unverified, and dropping
pre-substitution perturbs the **completeness** argument, not only soundness. Spike before
committing.

**Middle path 2 — cofinite freshness instead of the `Φ : Nat` counter in the relation.** Keep
Algorithm W; replace counter indices with "the chosen variables avoid a finite `L`", exactly
as `TypeOfElabHM`/`GeneralisesTo` already do. The executable `infer` keeps its counter and is
proved to refine the relation once. The relational/executable split this needs already exists
(`Infer` vs `inferCore`, bridged by `infer_sound`/`infer_complete`).

**Corrected estimate: 500–1,500, wide uncertainty. Do not trust this number without a spike.**
An earlier draft of this brief said 1,200–1,800 on the strength of the observation that
`Core.lean` has **zero** counter-interval lines against InferW's ~4,000. That comparison is
real but **confounded**: `TypeOfElabHM` is a declarative relation that merely *quantifies*
over fresh names, whereas `Infer` must be refinable by an executable function that *produces*
them. Core never pays the production cost, so it cannot bound what InferW would pay.

The honest mechanism is narrower than "the invariants disappear":

- **What dies:** the `Φ`-interval arithmetic *threaded through every theorem and every rule
  case*. `Φ` appears in the statement of every `Infer` theorem today, so `sound`, `complete`,
  `principal` and every helper re-establish interval facts per case — that is where most of
  the file's 612 `omega` calls live. Downstream (and `SurfaceBridge`) would stop seeing
  freshness at all.
- **What survives, relocated:** proving the executable counter's choices are actually fresh
  needs "`Φ` exceeds the free variables of ctx / τ / e / S" — which is precisely what
  `dom_below` and `belowFvars` say today. That content moves into the refinement proof rather
  than vanishing. `eliminates` / `eOut_avoid` / `dom_avoid` (~1,800) are untouched either way:
  they are about the *solution substitution* not clobbering generalisation-relevant variables,
  which is a real obligation under any freshness scheme.

So the win is a change in **distribution** — one obligation at one boundary instead of an
invariant threaded through a 10-rule mutual induction — not an elimination. That is still
worth having, but it is a different and smaller claim than the one first stated here.

**Middle path 3 — local constraint collection for `match` branches only.** Branch elaboration
does not depend on generalisation, so collecting branch equalities and solving once has no
elaboration hazard. **Save 300–500**, and it is an honest empirical probe of the constraint
idea for anyone who would rather have evidence than an estimate.

**Worth doing, cheap:** collapse `RecSpec = mono Ty | poly PolyTy` to one uniform form. Note
this falls out of §3.4 for free; it is only worth doing separately if §3.4 stalls.

**Do not adopt Rémy levels** (+600–1,000, no proof benefit). **Ordered algorithmic contexts**
(Dunfield–Krishnaswami style) make skolem escape cheaper — "the marker is still in the
context" beats FHM's two-sided check — but are a larger rewrite than constraints and answer
the elaboration question no better.

**Flagged, not recommended now:** Path R's ~1,700 lines come from putting `bl` *inside* `Ty`,
forcing settled HM metatheory to be restated modulo `eraseBounds`. This was locked
deliberately and should not be reopened mid-farm. But if the tax is still being paid after
§3.4 lands, the version of Path R that does not duplicate theorem statements is to
**parameterise `Ty` over its list annotation** — `Ty Unit` for pure HM, `eraseBounds` as a
map — so the declarative relations are stated once, on `Ty Unit`.

**Not recommended:** wholesale constraint rewrite — see §4.

---

## 6. Suggested order

1. ~~Spike §3.4 standalone.~~ **Done** — three rounds, gate passed (§3.6).
2. Do not stall the active Path R farm on this. Per the Path R brief the next items there are
   the `*_untypeable` demos and repairing the false completeness statements; that repair
   should land before anything is farmed against completeness either way.
3. Write the **stored-form retarget** (type-binder depth `d`, emitting `Ty.bvarRangeFrom d |G|`)
   and its commute with `openTyVars` — this discharges `T2`'s `hopen` and is the last piece
   before the refactor is mechanical.
4. Land the promotion: rewire `Infer.letRec`, rewrite `Infer.sound`'s letRec case, delete
   `letRecElab` and its cast, check preservation.
5. Then replace `Infer.sourceSound` with the strengthened faithfulness lemma
   (`Decorates e e' → TypeOfElabHM ctx e' τ → TypeOfHM ctx e τ`) — the §2.2 payoff, which only
   becomes available once elaboration is shape-preserving everywhere.
6. Then middle path 2 (cofinite freshness), then middle path 1 (drop eager context
   substitution) — in that order, since 2 is lower-risk and larger. Spike 2's cost first; §5's
   estimate for it is explicitly untrustworthy.
7. Revisit the `Ty`-parameterisation (§5) only after all of the above.

**Note the independence:** §4 finds that `letRecElab` and its support (~800 lines) would
survive *verbatim* under a constraint architecture, because it is pure elaboration. So §3.4 is
a win under **either** architecture, and is unconditionally the right first move.
