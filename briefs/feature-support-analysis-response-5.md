# Adversarial review of `feature-support-analysis-response-4.md`

**Handover note (read this first).** v3 is a single design. Do **not** start
another architecture pass. Do **not** treat “ground-pinning” as a new language
cut, a product question, or something wider than v1’s “textbook Damas–Milner
`let rec`.” That *is* DM: in-group uses unify the member’s monotype, and
*that* monotype is what is generalised for the body. A use at `int` *inside*
the block means the body does not get `∀a`. A use at a type variable inside,
or any use *after* the block, still generalises. Scoped tyvars in λ / `let` /
`let rec` annotations remain a must-have (C3–C5); this does not touch them.

The `g = f 3 in (g, f True)` program shows up below only because (i) v2’s
*writeup* of the cut (“every in-group use at one monotype”) did not match DM,
so the lemma was false, and (ii) v3’s ceiling slogan still doesn’t match DM
unless Infer checks `PolyTy.Generalizes (genGroup G τ) σ_opened` after the
group is solved. Fold that premise into the Infer.letRec rule, fix the I1
“source typechecker accepts this” sentence, spec Bounds opening, then
**implement Stage 2**. Stop iterating the brief.

---

v3 (the file; titled “revision 3”) is the first version that is **internally a
single design**. The v1/v2 lemma, the two cuts, the floor/ceiling fight, and
“`TypeOfHM` of the annotated source” are actually resolved, not renamed.

The remaining failure is smaller and local: **the ceiling check is
under-specified**, and one reading of §3 makes `Infer.sound` false on the same
program the cut claims to reject. That is a missing Infer premise, not a
reason to flip the architecture again.

**Convergence.** Yes. This is no longer “three relations pretending to be one.”
It is Infer-as-DM-plus-ceiling on the source, `TypeOfHM` on `erase e`, and
soundness as the bridge. If `Infer.sound` fails it should be a rule tweak
(the `Generalizes` premise below), not a fourth redesign.

---

## 1. What v3 got right (and should not reopen)

- **The cut is the rule**, not a use-site condition. That rule *is* textbook
  DM (v1’s stated new world), including that an in-group `f 3` pins `f` to
  `int→int` for the body. That is not a second sacrifice on top of “mono
  inside.” It is what “mono inside, then generalise that monotype” means.
- **Two relations.** `TypeOfHM` only on erased terms; Infer on the annotated
  source; no `TypeOfHM` of annotated `letRec` (impossible under `anns_eq`).
- **Coherence = `Infer e τ → TypeOfHM (erase e) τ`** (with `S.onCtx` / `S.onTy`).
  No side condition on derivations. v1/v2’s false lemmas are gone because their
  *hypothesis* is gone.
- **Ceiling**, aligned with `letIn` and with ML/Haskell. Floor is dead.
- **`IsErased`:** uniformly erased terms already inhabit the current predicate;
  re-cut is hygiene. Correct.
- **`erase ∘ openTyVars = erase`** still holds of §4 (including `var i _ → []`).
- C1–C4, C6, I1-as-machine-wall, the two-term pipeline order, lifting
  `lowerPoly`, “Bounds must open” as *work* rather than a freebie.

Do not go back to fused-`TypeOfHM`-plus-a-side-condition. That direction is
refuted.

---

## 2. The remaining hole: ceiling vs `genGroup` (can still break `Infer.sound`)

§3 says two things:

1. “The RHS must type at (an instance of) the annotation.”
2. “The binding is visible at the annotation in the body — no more.”

§2 says the same program is **rejected** because DM **pins**:

```
let rec f : ∀a. a → a = λx. x
    and g             = f 3
in (g, f True)
```

Those three sentences do not automatically agree.

### What DM actually computes

In-group, `f 3` pins `f`’s monotype to `int→int`. After the group,
`genGroup G τf = int→int` (trivial scheme). The **annotation** is still
`∀a. a→a`.

### If ceiling is implemented as §3 literally

- `f`’s RHS is `λx. x`. It *does* type at every opening of `∀a. a→a`
  (does not use `g` or the pin).
- Body env carries `f : ∀a. a→a` (“visible at the annotation”).
- Then `f True` typechecks at Infer.
- After erase, `TypeOfHM` has only `genGroup = int→int`. `f True` fails.

**`Infer e τ` holds and `TypeOfHM (erase e) τ` does not.** That is a
counterexample to the lemma v3 just named as the whole game.

Checking the RHS against `σ` does **not** see a pin that lives in a *sibling*.
The pin is a fact about the solved group, not about `f`’s RHS in isolation.

### What makes the lemma true (and also matches “DM rejects it”)

After group unification, for every annotated member:

```
PolyTy.Generalizes (genGroup G τ) σ_opened
```

(`InferW.lean` 17227: `M'` is at least as general as `M` — every instance of
`M` is an instance of `M'`.) Then:

- Over-claim (`σ = ∀a. a→a`, `genGroup = int→int`) **fails the check**.
  Infer rejects. The §2 story is saved, but the reason is “annotation
  over-claims the pinned scheme,” not “`f True` failed against `int→int`”
  unless you *also* put `genGroup` in the body, which would violate ceiling.
- Under-claim (`σ = int→int`, `genGroup = ∀a. a→a`) **passes**. Body env is
  `σ` (ceiling: `f True` rejected). Erased env is `genGroup`. 
  `TypeOfHM.weaken_scheme` (`InferW.lean` 17237) lifts the body derivation.
  That is the Infer.sound case for C5-style restriction.

So the Infer.letRec rule that can actually be sound is:

1. `RecSpec.init` emits `.mono` for **every** member (`some σ` included).
   `InferRecGroup.consPoly` unused.
2. Unify the group (ordinary `consMono`).
3. Compute `G` / `genGroup G τᵢ`.
4. **For each `some σ`:** `PolyTy.Generalizes (genGroup G τ) σ_opened`
   (`σ` opened in the same sense as `Infer.letInAnn`, not the stored
   `{1, a→bvar1}`).
5. Body env = the **annotations** (trivial scheme if unannotated:
   `genGroup`).

Omit (4) and the lemma is false. Put `genGroup` in the body instead of `σ`
and `let rec f : int→int = λx. x in f True` is accepted — ceiling is a lie.

§3 must state (4) in those words. “RHS types at an instance of the
annotation” is the wrong check.

### The §2 rejection paragraph is slightly mis-explained

Under (4), that program dies at the ceiling check on `f` (`int→int` does not
generalize `∀a. a→a`), **before** the body is typed. The body-level “`f True`
fails because of the pin” explanation is what you get if the body sees
`genGroup`, i.e. if there is **no** annotation or the annotation *is*
`int→int`. For a too-polymorphic annotation, write “Infer rejects because
the solved scheme is less general than the signature.” Same user-visible
illegal program, different premise. Proofs care.

Unannotated `let rec f = λx. x and g = f 3 in (g, f True)` is the pure-DM
rejection (`f True` against `int→int`). Keep that example too; it is the
cut without ceiling.

---

## 3. Claim-by-claim

### Architecture / coherence statement — **TRUE as a spec shape**

`Infer e τ → TypeOfHM (erase e) τ` is the right theorem. It is **not**
“ordinary Stage 2 Infer.sound plus erase” in the current tree:

- Today Infer still has `eOut`, `consPoly`, `RecSpec.init → .poly`, and
  `sourceSound` against `TypeOfElabHM`.
- Today `Infer.letRec` requires `∀ σ, some σ ∈ anns → σ.WF` and puts
  annotated members in `rhsCtx` at `σ` (`InferW.lean` 3018–3024, 1600–1603).

The theorem is Stage 2 **after** those rules change, plus `erase`. Calling it
“not a new kind of metatheory” is fair *once the Infer rule is the one in
§2*. Until `init`/`consPoly` change, there is no object-level Infer that the
lemma could be about.

Cofinite reconstruction (Infer checks one opening / one batch of fresh
monotypes; `TypeOfHM` demands all openings) is the usual W-vs-declarative
gap. Erase does not make it worse if `erase ∘ openTyVars = erase`. Don’t
pretend it is already proved.

### Cut (§2) — **TRUE** as DM; enforcement is `init → .mono`, not a comment

`RecSpec.init` mapping `some σ` to `.poly` **is** in-group polymorphic lookup
(`rhsEntry (.poly σ) = σ`). The cut is that function returning `.mono` for
every arm, plus deleting the `consPoly` path. State that as the rule change.
`RecGroup.rigidVars` (`InferW.lean` 1533–1543) currently treats annotation
fvars as rigid *because they sit in `rhsCtx` as schemes*. Under the cut they
don’t. Outer names like `C` are already env-rigid after opening (`w : C`).
Stale justification; likely harmless. Don’t copy the old comment into the
new rule.

The “common case `length xs` does not pin” remark is right.

### Ceiling (§3) — **NOT-ESTABLISHED** until §2 of this review is in the rule

The ML slogan is right. The operational check is not written. See above.

Scoped-tyvar anns checked after opening: right, and `Infer.letInAnn` already
does the outer open (`InferW.lean` 2983). The letRec ceiling must run on
**that** `σ`, on the Infer of the opened RHS, not on stored dangling `bvar`s.

`LamSeed.some` already ceilings λ ascriptions (`paramTy = T`, `T.IsLC`,
`InferW.lean` 1840–1842). C3 is consistent with ceiling at the λ. After
erase, `TypeOfHM` reuses that `paramTy`. Fine.

### C1 — **TRUE**

Same as last round. Residual nit: “independent of the mono/poly split” is
still a slogan about *why a Λ exists for `.mono`*, not a description of the
current `.poly` nest arm. Not load-bearing.

### C2 — **TRUE** as the post-cut rule

`forceRecclo` / `recclo_body_typed` still type RHSs in `bodyCtx`. “Mono
inside” is Infer. Machine `hpoly` is vacuous on erased terms. Fine.

### C3 — **TRUE**

### C4 — **TRUE** (ceiling, reuse `M = σ`)

Do not mix with letRec’s `genGroup`. Annotated `letIn` already pins
(`Infer.letInAnn`). Erased `TypeOfHM.letIn` reuses that `M`. Proof obligation
is `erase (openTyVars Xs rhs) = erase rhs` plus the usual cofinite lift.

### C5 — **TRUE for the worked example; general case depends on §2**

No in-group uses; `w : C` pins `α→C`; `G = [α]`; opened ceiling `∀a. a→C`
equals `genGroup`. Body uses at `C` are inside the ceiling. Erased group is
the same `genGroup`. This example does not exercise `Generalizes` vs a pin.

### C6 — **TRUE**

### I1 — **TRUE as a machine wall; FALSE as “the source typechecker handles it”**

Under v3 Infer, I1 is **rejected by the cut** (`f (Cons x Nil)` at `List a ≠ a`).
The “source typechecker opens `c → C` and everything lines up” sentence is
about **old fused** `TypeOfHM` / `consPoly`, which you are deleting. Don’t
tell the reader the user-facing checker accepts I1. What remains true:

- Old declarative `TypeOfHM` (fused) types I1 via outer `GeneralisesTo`.
- The machine cannot keep that annotation without type-passing.
- Therefore selective-keeping of *dangling* poly-rec anns is still
  impossible; self-contained poly-rec anns are a different knob (cut, not I1).

### I2 — **TRUE** (non-claim)

### Pipeline — **TRUE as order; Bounds opening still unspecified**

Q3 is the right open question. `Bounds.Synth` uses `σ.body` as stored
(`letRecProvisional`, `checkBoundsΦ rhs σ.body`). That is wrong for C4/C5
until something opens. This is implementation work, not a design fork.

### Q4 (`erase ∘ openTyVars`) — **TRUE** of §4

### Q2 (`IsErased`) — **TRUE** (no new preservation proof if the machine only
sees erased terms)

---

## 4. Infer.sound: what the proof actually has to do

Induction on Infer, after the rule change. The interesting cases:

| Infer case | Erased `TypeOfHM` | Extra glue |
|---|---|---|
| `lambda` + `LamSeed.some T` | `lambda none`, choose `paramTy = S.onTy T` | `T.IsLC` already |
| `letInAnn` | `letIn none`, choose `M = σ` | `erase ∘ openTyVars = erase`; cofinite lift from the one `Ys` Infer used |
| `letIn` none | `letIn none`, choose `M = genScheme …` | existing W-soundness |
| `letRec` all-`.mono` + ceiling | `letRec` all-none, `specs = .mono τᵢ`, `G` as Infer | `MonoTyped` cofinite lift; body: IH under env `σ`, then `weaken_scheme` along `Generalizes (genGroup G τ) σ` |
| `var` | `var i []` | `TypeOfHM.var` already ignores tyArgs |

If `Generalizes (genGroup G τ) σ` is an Infer premise, the letRec body case is
exactly `weaken_scheme`. That lemma already exists. The new work is (i) the
Infer rule, (ii) cofinite reconstruction, (iii) erase commutation in the
opened-RHS cases.

There is **no** remaining “convert `.poly` specs to `.mono`” case. That was
the v1/v2 lemma. It is gone. Good.

---

## 5. Things that must change in the next revision (small)

1. **Write the ceiling premise as `PolyTy.Generalizes (genGroup G τ) σ_opened`**,
   after group unification, not as “RHS types at `σ`.” Give the
   over-claiming pinned program as rejected *by that premise*.
2. **Name the Infer deltas:** `RecSpec.init` all `.mono`; `consPoly` unused;
   body env = ceiling schemes; `σ.WF` on the term Infer actually sees (opened
   under enclosing `letInAnn`).
3. **Fix I1’s source-typechecker sentence** so it does not claim Infer
   accepts I1.
4. **Bounds opening:** still needs a spec (lockstep with Infer’s openings, or
   a pre-opened copy). Don’t start Stage 2 pretending this is implied by
   “annotations present.”
5. Don’t claim Infer.sound is already the shape of today’s `Infer.sound`;
   today’s Infer is the fused elaborating one.

---

## 6. Convergence

**Yes.** The sequence is actually monotonic now:

| Version | What it was | What broke |
|---|---|---|
| v1 | Uniform erase + unrestricted `TypeOfHM → TypeOfHM ∘ erase` | Mixed-group sibling poly; lemma false |
| v2 | Same lemma + use-site side condition; floor; “`TypeOfHM` on source” | Ground-pinning counterexample; floor vs ceiling; `anns_eq` |
| v3 | Split relations; DM cut; ceiling; soundness = Infer.sound | Ceiling check not stated at group-solved schemes (this review) |

v3 does not reopen v1/v2. The leftover is one predicate on Infer.letRec that
the rest of the document already *wants* (solved `genGroup` vs signature).
Put it in the rule and the architecture is stable enough to implement:
change Infer, prove `Infer.sound` against `erase e`, open Bounds, lift
`lowerPoly`. The DM cut was the v1 new world; it is not an open product
question. Stop redesigning and do Stage 2.
