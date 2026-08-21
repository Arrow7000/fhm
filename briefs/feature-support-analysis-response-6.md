# Feature-support analysis — revision 4 (final; design stable, ready to implement)

**Status: revision 4 — final.** Supersedes `feature-support-analysis-response-4.md`
(v3) and incorporates `feature-support-analysis-response-5.md`. The second review
declares **convergence**: v3 was the first internally-consistent design; the only
remaining gap was that the ceiling check was under-specified. This revision adds that
one premise, names the Infer deltas, and closes the design. **No further architecture
passes; the next step is Stage 2 implementation.**

## 0. Convergence

| Version | What it was | What broke |
|---|---|---|
| v1 | Uniform erase + unrestricted `TypeOfHM e τ → TypeOfHM (erase e) τ` | mixed-group sibling poly use; lemma false |
| v2 | Same lemma + use-site side condition; "floor"; `TypeOfHM` on annotated source | ground-pinning counterexample; floor-vs-ceiling; `anns_eq` forces `.poly` |
| v3 | Split relations; DM cut; **ceiling**; soundness = `Infer.sound` | ceiling check not stated at solved group schemes (one premise) |
| v4 | v3 + the `Generalizes` ceiling premise + explicit Infer deltas | — (nothing new) |

The settled architecture (unchanged from v3):

- **`Infer` = the source relation.** Annotated source; Damas–Milner monomorphic
  recursion for `letRec`; annotations are **ceilings**.
- **`TypeOfHM` = the machine relation.** Erased terms only; `letRec` mono-only
  (`PolyTyped` vacuous — no `.poly` specs exist).
- **Coherence = `Infer.sound`**: `Infer e τ → TypeOfHM (erase e) τ` (with `S.onCtx` /
  `S.onTy` threading). No separate coherence lemma; no `TypeOfHM` of annotated `letRec`.

## 1. The one missing premise: the ceiling check

The ceiling check is **not** "the RHS types at (an instance of) `σ`". A pin from a
*sibling* (`g = f 3`) is invisible to `f`'s RHS in isolation. The correct check runs
**after group unification**, for each annotated member, on the *solved* scheme:

> **`PolyTy.Generalizes (genGroup G τᵢ) σᵢ_opened`**
> (`M'` at least as general as `M`: every instance of `M` is an instance of `M'`.)

- **Over-claim** (`σ = ∀a. a→a` while a sibling pins `genGroup = int→int`) → the check
  **fails**, Infer rejects. This is what actually rejects
  `let rec f : ∀a. a→a = λx. x and g = f 3 in (g, f True)` — the annotation over-claims
  the pinned scheme, *before* the body is typed.
- **Under-claim** (`σ = int→int`, `genGroup = ∀a. a→a`) → the check **passes**; the body
  sees `f : int→int` (ceiling), so `f True` is rejected at the body.

With this, the `Infer.letRec` rule (post-cut) is, in full:

1. `RecSpec.init` emits `.mono` for **every** member — annotations included;
   `InferRecGroup.consPoly` is unused/deleted.
2. Unify the group at the fresh monotypes (ordinary DM monomorphic recursion).
3. Compute the gen-var pool `G` and `genGroup G τᵢ`.
4. For each `some σ`: check `PolyTy.Generalizes (genGroup G τᵢ) σᵢ_opened`
   (`σᵢ` opened under the enclosing scope, exactly as `Infer.letInAnn` already opens —
   not the stored `{1, a→bvar1}`).
5. Body env = the **annotations** (`genGroup G τᵢ` for unannotated members).

The erased term's body env is `genGroup G τᵢ` (more general); the `Infer.sound` proof
lifts the body derivation from the annotation env to the `genGroup` env via the existing
`TypeOfHM.weaken_scheme` (`InferW.lean` 17237), which is exactly the `Generalizes`
relation. No new metatheory shape is needed.

## 2. The Infer.sound proof obligations (what Stage 2 actually proves)

Induction on `Infer` (after the rule change). The non-trivial cases:

| Infer case | Erased `TypeOfHM` | Glue |
|---|---|---|
| `lambda` + `LamSeed.some T` | `lambda none`, choose `paramTy = S.onTy T` | `T.IsLC` already held |
| `letInAnn` | `letIn none`, choose `M = σ` | `erase ∘ openTyVars = erase`; cofinite lift from the single opening Infer used |
| `letIn` none | `letIn none`, choose `M = genScheme …` | ordinary W-soundness |
| `letRec` all-`.mono` + ceiling | `letRec` all-`none`, `specs = .mono τᵢ`, same `G` | `MonoTyped` cofinite lift; body: IH under the annotation env, then `weaken_scheme` along `Generalizes (genGroup G τ) σ` |
| `var` | `var i []` | `TypeOfHM.var` already ignores tyArgs |

There is **no** "convert `.poly` specs to `.mono`" case — that was the v1/v2 lemma, now
gone. The new work is: (i) the rule change, (ii) cofinite reconstruction
(one-opening-to-all-openings, the usual W-vs-declarative gap), (iii) the
`erase ∘ openTyVars = erase` commutation in the opened-RHS cases.

**Caveat on "already proved":** today's `Infer` is the fused *elaborating* one — it still
has `eOut`, `consPoly`, `RecSpec.init → .poly`, `σ.WF` on stored anns, and `sourceSound`
against `TypeOfElabHM`. `Infer e τ → TypeOfHM (erase e) τ` is the theorem *after* the
rule change, not the current `Infer.sound`. Do not cite today's tree as already
implementing it.

## 3. Corrections to v3

1. **I1's "source typechecker accepts it" is wrong.** Under v3 `Infer` (DM cut), the I1
   program is **rejected by the cut** (the recursive call `f (Cons x Nil)` at `List a ≠ a`
   is in-group poly use). The sentence was about the *old fused* `TypeOfHM` / `consPoly`,
   which is being deleted. What remains true: (i) the old declarative `TypeOfHM` types
   I1 via the outer `GeneralisesTo`; (ii) the machine cannot keep that dangling
   annotation without type-passing (the three-way bind); (iii) therefore
   selective-keeping of *dangling* poly-rec annotations is still impossible — and
   self-contained poly-rec annotations are a different knob, removed by the cut, not I1.
2. **Bounds opening** is implementation work, still to be specified: either open in
   lockstep with Infer's openings, or run Bounds on a pre-opened copy. Not implied by
   "annotations present".
3. **`RecSpec.init → .mono` is the enforcement of the cut**, not a comment. Delete
   `consPoly`; drop the now-stale `rigidVars` justification (annotation fvars are no
   longer in `rhsCtx` as schemes).

## 4. What to implement (Stage 2, in order)

1. Change `Infer.letRec` per §1 (all-`.mono` init, no `consPoly`, the `Generalizes`
   ceiling premise, body env = annotations).
2. Prove `Infer.sound : Infer e τ → TypeOfHM (erase e) τ` (§2).
3. Spec and implement Bounds opening (§3.2).
4. Lift `lowerPoly` (surface scoped refs in scheme bodies).

The feature set is settled and unchanged from v3's summary: **scoped tyvars everywhere**
(dropped + re-inferred), **polymorphic recursion outside blocks only** (the DM cut, with
the ground-pinning consequence), **no type-passing / no elaboration / no n²** (the CEK
machine); and the two incompatibilities — **the cut** (in-group poly use, by design) and
**I1** (scoped tyvars inside a poly-rec `letRec` annotation, genuinely needing
type-passing). This document is the last design iteration; the remaining risk is the
unproved `Infer.sound` theorem, not the design.
