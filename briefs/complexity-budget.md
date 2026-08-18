# Where FHM's complexity budget goes

This document explains why the type-inference stack is the size it is (`Core.lean` ~11k lines,
`InferW.lean` ~19k), identifies the single highest-leverage simplification — the `letRec`
promotion described in §3 — and lays out the work to land it. It is written for whoever carries
out that refactor.

Companion reference: `FHM/SpikeLetRecPromote.lean`, which proves the encoding is viable.

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

The viability of (3) is settled: the general transport `MonoTyped → PolyTyped` at the promoted
schemes is proved and axiom-clean in `FHM/SpikeLetRecPromote.lean` (see §3.5). What remains is
bookkeeping-shaped, not existential: the stored-form retarget traversal, rewiring `Infer.letRec`,
preservation, and the Path R erase-commutes (§3.6). The effort estimate is the weak part of this
document; the *viability* is not in question.

---

## Status (2026-08-17): landing in progress

The promotion is **partially landed**. This section records where things stand so the work can be
resumed without re-derivation; it supersedes §5.5/§3.6 estimates where they conflict.

### Two corrections to §3, learned while landing

1. **Mixed groups are out of scope for the promotion (option A).** §3.4's "uniform arity `|G|`"
   only works when *every* member is promoted to arity `|G|` — i.e. all-mono groups. A user-annotated
   poly member has its own arbitrary arity `σ.paramCount` and cannot supply `|G|` type args when
   referencing a promoted mono sibling (the pool has no per-member binder in a mixed group). So:
   **all-`none` group → promoted `.letRec` node**; **mixed group (any `some`) → keep `Expr.letRecElab`**.
   Consequence: `letRecElab` is *not* deleted, and `sourceSound` keeps a mixed-group case.

2. **The body transport is a SPREAD, not an append.** `genGroup G μ` binds the *filtered* pool
   (a subsequence of `G`); `promoteScheme G μ` binds the *full* pool. Filtered→full inserts the
   vacuous `unit` fillers at the **gap positions** of `G`, not at the end. (`G=[0,1,2], μ=fvar 2`
   is a counterexample to appending: `closeOver [2] (fvar 2)=bvar 0` but `closeOver [0,1,2] (fvar 2)=bvar 2`.)

### Done

- **`FHM/LetRecPromote.lean`** (new, untracked; imports `FHM.Core`; imported by `FHM.InferW`; in
  `lakefile.toml` roots). Axiom-clean. Holds the promotion + transport machinery, generalized to
  target-aware `mono : Nat → Bool`:
  - `promoteScheme`/`promoteSpecs`/`promoteAnns`/`promoteSpec`/`RecSpec.isMono`/`specsMono`,
    `promoteScheme_wf`/`openVars`/`instantiatesTo`.
  - `retargetVars`/`retargetBranches`/`retargetGroup` (opened) and `retargetStored`/`...Branches`/`...Group`
    (stored), all `mono : Nat → Bool`.
  - `retarget_transport`/`retarget_untransport` (**mixed** prefixes, `specs : List RecSpec` + `G Xs`).
  - `monoTyped_to_polyTyped`/`polyTyped_to_monoTyped` (**homogeneous**, all-mono):
    `monoTyped_to_polyTyped (hGnodup) (hmonoLC : ∀ μ ∈ monos, μ.IsLC) (hlen : bindings.length = monos.length)
      (hmono : RecSpecs.MonoTyped TypeOfElabHM ctx bindings (monos.map RecSpec.mono) G L)
      (hopen : ∀ Ys, FreshNames (L++G) G.length Ys → ∀ p ∈ bindings.zip bindings',
         p.2.openTyVars Ys = retargetVars (specsMono (monos.map RecSpec.mono)) (Ys.map Ty.fvar) 0 p.1)
      : RecSpecs.PolyTyped … bindings' (monos.map (fun μ => RecSpec.poly (promoteScheme G μ))) [] (L++G)`.
  - `spreadTyArgs`/`bodyExtend`/`bodyScheme_weaken` (the body transport):
    `bodyScheme_weaken (hGnodup) (hmonoLC) (h : TypeOfElabHM ⟨monos.map (PolyTy.genGroup G) ++ env, ctors⟩ e τ)
      : TypeOfElabHM ⟨monos.map (promoteScheme G) ++ env, ctors⟩ (bodyExtend monos G 0 e) τ`.
  - `retargetStored_openTyVars` + the structural/commute lemmas.
- **`FHM/InferW.lean`** (modified, uncommitted): `Infer.letRec` and `inferCore` now emit
  `Expr.letRecElabOut G anns (bindingsOut.map (·.substTyFvars S₁)) solvedSpecs bodyOut`, where
  `solvedSpecs = (RecSpec.init Φ anns).map (RecSpec.onSubst S₁)`, `G = genGroupVars …`, and
  `allNone anns := anns.all (·.isNone)`; `letRecElabOut` branches all-mono → promoted node
  (`.letRec (promoteAnns G specs) (bindings retargetStored∘closeTyVars G) (bodyExtend (monoTys specs) G 0 body)`)
  else → `Expr.letRecElab`.

### Remaining (the downstream repair in `InferW.lean` — the subtle part)

`lake build FHM.LetRecPromote` is green; `lake build FHM.InferW` has **4 errors**: `:5968`
(`eOut_avoid`/`dom_avoid` calls `mem_tyFreeVars_letRecElab`), `:7332` (`eOut_tyBvarBounded` calls
`letRecElab_tyBvarBounded`), `:10286` (`Infer.sound` letRec case), `:11506` (`preservesAnns` calls
`UserAnnsCopied.letRec`). `Infer.sourceSound` (now ~12606) does **not** need touching to land the
promotion: it types the *source* node via `TypeOfHM.letRec_of_emptyPool` and never mentions the
elaboratum, and it sits in a `mutual` block separate from `preservesAnns`. Its all-mono letRec case
only collapses in the Part-3 faithfulness refactor — future work, not a build blocker.

Repair: (Part 1) add `letRecElabOut` mirrors of the `letRecElab` lemmas (`mem_tyFreeVars`,
`tyBvarBounded`, `eraseBounds`, `substTyFvars`, `UserAnnsCopied`), each `by_cases allNone anns`; the
all-mono branches need small facts that `promoteScheme`/`closeOver`/`retargetStored`/`bodyExtend`/
`closeTyVars` don't leak free vars/bvars (`promoteScheme G τ`'s free vars = `τ.freeVars` minus `G`).
(Part 2) `Infer.sound`'s letRec case: `by_cases hallNone : allNone anns`; all-mono → structural
`TypeOfElabHM.letRec` via `monoTyped_to_polyTyped` (discharge `hopen` via `retargetStored_openTyVars`)
+ `bodyScheme_weaken` + `eraseBounds`/`substTyFvars` threading; mixed → keep `Expr.letRecElab_sound`.
(Part 3, future — **not** required for a green build) swap in the `...Out` lemmas and add the
`UserAnnsCopied` fact for the promoted node; replace `sourceSound`'s structural cases with the
faithfulness corollary (all-mono letRec via `polyTyped_to_monoTyped`; the mixed letRec case keeps
`TypeOfHM.letRec_of_emptyPool`). Goal for **landing**: `lake build FHM.InferW`/`FHM.Headlines` clean
from Parts 1–2 alone. (2 pre-existing
`termination_by` warnings at `:7421`/`:11392` — leave them.)

### Tooling discipline (learned the hard way)

Edit `.lean` only via Read/Edit (never Python/`sed`). The lean-lsp MCP tools are `lean_goal`,
`lean_diagnostic_messages`, `lean_multi_attempt`, `lean_build`, `lean_local_search`, …; after editing,
the LSP goes stale ("diagnostics_unavailable / not known clean", or hangs) — on that signal (or
>~120s) call **`lean_build`** (runs `lake build` + restarts LSP) then re-query. `lake build
FHM.LetRecPromote` ~4s; `lake build FHM.InferW` ~2min. deepseek-v4-flash is fine for the mechanical
`LetRecPromote` lemmas but has corrupted the `InferW` sound-case repair 4× — do Part 2 by hand (or a
stronger model).

### Option B (future, not started)

Can typeable mixed groups hit the arity mismatch? The claim to pin down is *sharper than the original
§3.4 wording*. The pool `G` is **group-wide** (the union of every mono member's solved-type free
vars), so "referenced members have `|G| = 0`" is false on its face: `f : ∀a. a→a = fun x → g x`,
`g = fun x → x`, `h = fun x y → y` is typeable with `G = {β,γ}` (from `h`) while `f` references `g`.

What is conjectured instead: an annotated member referencing a mono member pins that mono's *filtered*
pool empty — `genFilter G τ = []` — because annotated members' variables are **rigid skolems** (they
cannot unify with a compound type), so the reference forces the mono's type to equal the skolems
exactly. The encoding would then be "promote the mono members with **nonempty** filtered pool (not
referenced by any poly member, so the uniform full-pool retarget is safe); leave pinned monos mono
(their `bodyScheme` is already monomorphic — no Λ needed)". Both halves need proof: the rigidity
pinning lemma, and a mixed-group `monoTyped_to_polyTyped` split. If both hold, option A's mixed branch
is replaced by the promotion and `letRecElab` fully deleted; otherwise option A stands as the boundary.

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

**It does not.** Put the Λ *inside* the node by using the `anns` slot that is already
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

Consequences:

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

### 3.5 What the reference proof establishes

`FHM/SpikeLetRecPromote.lean` proves the encoding works. It is a standalone reference, not part
of the built library, with derivations stated declaratively (`TypeOfElabHM`, no `Infer`). The
headline results, by role:

**The encoding.**

- `promoteScheme_wf` — the promoted scheme is well-formed even with vacuous binders (one line,
  via `Ty.closeOver_preserves_bvars`). This is the fact the whole design rests on.
- `promoteScheme_openVars` — opening the promoted scheme at fresh `Ys` recovers exactly
  `Ty.renameG G Ys τ` (one line, via `Ty.openVars_closeOver_rename`), with no
  filter-nodup / filter-disjointness round-trip. Direct support for "full pool is cheaper than
  `genFilter`": compare the ~40 lines of filter bookkeeping inside `rewrap_hasScheme_mono`.
- Concrete derivations (`smoke_*_noref`, `smoke_*_selfref`, `mutual_*`, `mutual_mixed_*`)
  typecheck the promoted node as a plain `.letRec` with the slot filled, covering no
  self-reference, self-reference, mutual recursion with a vacuous binder, and index alignment
  across members using different pool slots. A shape check also records that `PolyTy.genGroup`
  collapses the two distinct schemes of the index-alignment case to the same arity-1 scheme, so
  the full-pool choice is what keeps that case distinguishable.

**The transport.**

- `retarget_transport` — the core lemma: a `TypeOfElabHM` derivation over a monomorphic env
  prefix carries to one over the promoted schemes, with group-variable uses retargeted to `Vs`.
  The `TypeOfElabHM` analogue of `TypeOfHM.weaken_schemes`, *with the term rewrite the
  type-passing `var` rule forces* (swapping a `PolyTy.mkTrivial μₖ` entry for a scheme `Mₖ`
  with `Mₖ.InstantiatesTo Vs μₖ` preserves typing, provided in-window uses are retargeted to
  `Vs`). Proved by `TypeOfElabHM.rec_strong` on the `weaken_schemes` template, with an `ep`
  accumulator and the invariant `b = ep.length`.
- `retarget_untransport` — the reverse ("forgetting") direction.
- `monoTyped_to_polyTyped` — the letRec corollary, mono → poly: a mono group's `MonoTyped`
  premise yields the promoted group's `PolyTyped` premise at the full-pool schemes. The pool
  quantifier forces `Xs = []`, confirming that `rhsCtx` stops depending on the pool opening
  once every member is `poly`.
- `polyTyped_to_monoTyped` — the converse, poly → mono, which is what lets `Infer.sourceSound`
  become a decoration-forgetting corollary.

  The converse is true but not automatic. It needs two hypotheses that are easy to miss, and
  that the file documents:

  - a length relation `bindings'.length = bindings.length`, needed to index the poly derivation
    at member `k`;
  - the condition that retargeting to `[]` is the identity on the source bindings, needed
    because `retargetVars` *overwrites* `tyArgs` — the retarget alone does not constrain the
    source's group-use `tyArgs` (a source `.var 1 [int]` retargets to the same term as
    `.var 1 []`, but only the latter can be `MonoTyped`).

  A tempting objection is that an arbitrary poly derivation could instantiate a sibling at
  *different* types at different sites, which `MonoTyped` cannot express. It cannot happen:
  `TypeOfElabHM` reads `tyArgs` from the *term*, and the retarget assigns every in-window use
  the *same* `Vs`, so the term itself pins one shared instance per sibling — exactly what
  `MonoTyped` requires. Type-passing, the feature responsible for much of the complexity
  elsewhere, is what makes the converse hold.

**Preservation.** `promoted_preservation` shows that preservation for a promoted group is a
one-line application of the already-proved general `TypeOfElabHM.preservation`
(`Core.lean:9442`): the promotion changes neither `Expr`, `SmallStep.Step`, nor `TypeOfElabHM`,
so a promoted `letRec` is an ordinary well-typed term. `progress` and `type_safety` follow the
same way.

**The stored-form retarget.** `retargetStored` is the *stored*-form traversal the real
elaborator emits (with `Ty.bvarRangeFrom d |G|` at type-binder depth `d`), and
`retargetStored_openTyVars` is its commute with `openTyVars`, discharging the `hopen` hypothesis
the transport corollaries leave open. Two points to carry into the implementation:

- The stored retarget must be **`anns`-aware**: `Expr.openTyVarsAux` opens each group binding at
  `d + RecAnn.params aⱼ` (annotated bindings are scheme-shielded), so retargeting at uniform
  `d` is wrong — the pool `bvar`s would stay unopened. In the promoted design this shielding is
  uniform, since every member is annotated at arity `|G|`.
- The retarget covers the **body** as well as the bindings: the mono body sees
  `PolyTy.genGroup G τ` at filtered arity, the promoted body the full-pool scheme, so the body's
  `var` `tyArgs` arity changes too.

A further point in favour: **promotion removes a `renameG` hazard.** `Ty.renameG` is a
*sequential* `substFvars` over `G.zip Xs`, so with `|G| ≥ 2` it can self-capture unless `Xs` is
disjoint from `G` — which `RecSpecs.MonoTyped` only guarantees when its `L` includes `G`
(existing Core callers pass `G` into the avoid set; see `rewrap_hasScheme_mono`). The promoted
regime has no analogue: `promoteScheme`'s body is pre-closed and opened by direct bvar index
lookup, never by sequential fvar substitution.

Every headline result is axiom-clean (`propext`, `Classical.choice`, `Quot.sound` — no
`sorryAx`), recorded by a `#print axioms` guard in the file.

### 3.6 Remaining work and estimated costs

The reference proof is a proof of viability, not an implementation; the refactor has not been
landed. Remaining, in rough order:

1. **Rewire `Infer.letRec`** to emit the promoted node, and rewrite `Infer.sound`'s letRec case
   (574 lines) against it. The claimed collapse — a structural application of
   `TypeOfElabHM.letRec` instead of the dedicated support cast — is untested.
2. **Delete `letRecElab` and its support** (`letRecElab`, `letRecElabNest`,
   `letRecElabNest_sound`, `letRec_body_retype`, `letRecFused_body_retype`,
   `letRecFused_residual_setup`, the `shiftFrom` plumbing) — ~1,045 lines, 15 decls.
3. **Port the transport machinery** from the reference proof into `InferW` — ~1,450 lines
   measured, including `retargetVars`/`retargetBranches`/`retargetGroup` and their commute
   lemmas with `openTyVars`/`openBoundTyVars`.
4. **Strengthen the faithfulness lemma.** Replace `Infer.sourceSound` (~656 lines) with
   `Decorates e e' → TypeOfElabHM ctx e' τ → TypeOfHM ctx e τ`, proved once by structural
   induction and stable against future changes to `Infer`. Its letRec prerequisite —
   `polyTyped_to_monoTyped` — is already proved; `Infer.preservesAnns` is most of the other
   half. Residual caveat: `Decorates` must be tight at `letRec` (uniform `tyArgs` on
   group-member uses, which is what `Infer` emits).
5. **Path R erase-commute lemmas** for the two new traversals (`retargetVars`/
   `retargetStored`) — unmeasured; the existing erase-commute block is 577 lines for the
   operations it already has.
6. **Completeness interaction** — completeness is stated against `TypeOfHM` on the *source*
   term (whose `anns` are still `none`), so the promotion itself does not affect it; but per
   the Path R brief the completeness statements need repair before anything is farmed against
   them.

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

## 5.5 Expected payoff, by dimension

"Measured" means counted in the tree; "estimated" means judgement, and is where the bands are
widest.

### A. Net line count — **≈ break-even, ±500** — ⚠️ *stale after correction #1*

**Do not do this for the line count.**

⚠️ This table predates the "mixed groups out of scope" correction. As landed, `letRecElab` is
**kept** (mixed branch), the `RecSpec` mono/poly split survives, and `sourceSound`'s mixed case
stays — so the −1,045 / −656 deletions below are **not** realised by Option A alone; the near term
is net-additive (~2.9k lines of `LetRecPromote` + the `...Out` mirrors + the all-mono sound branch).
The deletion and the §2.2 shape-preservation payoff are contingent on Option B (below), which is
future research.

| | lines | basis |
|---|---:|---|
| `letRecElab` family, deleted outright | −1,045 | measured (15 decls) |
| `Infer.sourceSound`, replaced by a faithfulness corollary | −656 | measured deletion, replacement estimated |
| `Infer.sound`'s letRec case, collapsing to a structural application | −350 ± 200 | estimated — largest open number |
| Transport machinery moving from the reference proof into InferW | +1,450 | measured (`retarget_transport` + `retarget_untransport` + the two corollaries + `retargetStored`, excluding the concrete tests) |
| Faithfulness lemma (`Decorates` + the induction) | +300 ± 150 | estimated; not attempted |
| Path R erase-commutes for the two new traversals | +250 ± 150 | unmeasured — the existing erase-commute block is 577 lines for the operations it already has |

Note: "4,113 lines of letRec machinery" is **not** the deletion opportunity — most of
`RecSpec`/`RecSpecs` in Core is the *declarative spec* and survives; the mono/poly collapse
trims it rather than deleting it.

### B. Future-refactor cost — large reduction.

The real case for the change. Elaboration becomes shape-preserving everywhere, so
`Infer.sourceSound` stops being a second full induction that must be re-run whenever `Infer`
changes, and becomes a corollary proved once. Path R is the worked example of the cost: its
residual campaign had to mirror `sourceSound` precisely because of the shape divergence. The
letRec correspondence holds in *both* directions (`monoTyped_to_polyTyped` and
`polyTyped_to_monoTyped`), which is exactly what the corollary needs. The residual caveat is
that `Decorates` must be tight at `letRec` — a term-level, structurally checkable condition,
and what `Infer` emits.

### C. Refactor effort — a handful of focused sessions.

The transport — the hardest identified piece — is already proved; the stored-form retarget came
in at 170 lines against a 200–400 estimate; preservation turned out free. The remaining wildcard
is `Infer.sound`'s letRec case, and the tedium risk is Path R erase-commutes, historically where
this codebase's grind lives.

### D. Showstopper risk — low.

Every predicted obstruction has been probed and either discharged (transport in both
directions, preservation) or shown to be a statement bug rather than a design flaw (the two
hypotheses the converse needs, the stored retarget's missing `anns` shielding). `Expr`, `Step`
and `TypeOfElabHM` are untouched throughout, which is what keeps the blast radius small.

### Still unmeasured

`Infer.sound`'s letRec collapse; the faithfulness lemma itself (only its letRec prerequisite,
`polyTyped_to_monoTyped`, is done); Path R erase-commutes for
`retargetVars`/`retargetStored`.

---

## 6. Suggested order

**Do not interleave this with Path R.** Pausing one refactor mid-flight to start another in the
same 30k-line development is how you get an unrecoverable mess. Rework exposure is currently
**zero** — of 2,218 lines added by the concurrent completeness campaign, exactly **one**
mentions `letRec`/`RecSpec`/`RecGroup` — and it stays zero until that campaign reaches the
letRec completeness case *specifically*. That is a natural decision point which arrives on its
own; it is not a reason to pause. Finish Path R.

1. Finish Path R. Per that brief: the `*_untypeable` demos, then repairing the false
   completeness statements — which must land before anything is farmed against completeness
   regardless of what happens here.
2. Land the promotion: rewire `Infer.letRec`, rewrite `Infer.sound`'s letRec case, delete
   `letRecElab` and its cast, port the transport machinery from the reference proof.
3. Then replace `Infer.sourceSound` with the strengthened faithfulness lemma
   (`Decorates e e' → TypeOfElabHM ctx e' τ → TypeOfHM ctx e τ`) — the §2.2 payoff, which only
   becomes available once elaboration is shape-preserving everywhere.
4. Then middle path 2 (cofinite freshness), then middle path 1 (drop eager context
   substitution) — in that order, since 2 is lower-risk and larger. Spike 2's cost first; §5's
   estimate for it is explicitly untrustworthy.
5. Revisit the `Ty`-parameterisation (§5) only after all of the above.

**Note the independence:** §4 finds that `letRecElab` and its support (~800 lines) would
survive *verbatim* under a constraint architecture, because it is pure elaboration. So §3.4 is
a win under **either** architecture, and is unconditionally the right first move.
