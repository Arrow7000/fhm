# Adversarial review of `feature-support-analysis-response-2.md`

v2 correctly absorbed the v1 findings (mixed-group counterexample, C5’s
restriction-only claim, C6 ↛ I1, two-term pipeline, `var` zeroing, nest on both
arms, fused rule). Those are no longer the problem.

The load-bearing failure is new, and it is again the coherence lemma. v2 states
two “equivalent” formulations of the §2 cut that are **not equivalent**. The
weaker one is the side condition on the lemma; the stronger one is what Infer-as-DM
actually enforces. Under the weaker reading the restricted lemma is still **false**.
Under the stronger reading the lemma’s *subject* (`TypeOfHM` of the annotated
source) is not a theorem, because `RecSpecs.WF.anns_eq` forces `.poly` specs
whenever annotations are present.

A second, independent contradiction: §2 says letRec annotations are a **floor**
(do not restrict); C5 says they are a **restriction/check**. Those cannot both
be the language.

---

## 1. Headline: the restricted coherence lemma is still false

**Lemma (§3).** If `TypeOfHM e τ` and every in-group use of every `letRec`
member (self or sibling) is at one monotype, then `TypeOfHM (erase e) τ`.

**Verdict: FALSE** under the side condition as written.

v1’s counterexample used *two* in-group instantiations (`f 3` and `f True`).
The remaining hole is **one** in-group instantiation at a ground type, plus a
polymorphic use in the **body** (explicitly allowed: “poly *outside*”).

### Counterexample (mixed group, one in-group monotype)

```
let rec f : ∀a. a → a = λx. x
    and g             = f 3
in (g, f True)
```

**Source `TypeOfHM` holds**, at `int × bool`:

- `specs = [.poly ⟨1, a→a⟩, .mono int]`, `G = []`.
- `f`’s RHS: `PolyTyped`, `λx. x` at `Y→Y`. No rec uses.
- `g`’s RHS: `MonoTyped`; `rhsEntry (.poly σ) = σ`, so `f` is a scheme;
  `TypeOfHM.var` instantiates at `int`. One in-group use, one monotype.
- Body: `bodyScheme (.poly σ) = σ = ∀a. a→a`, so `f True : bool`. `g : int`.

**§2 side condition holds** as written: the only in-group use of `f` is `f 3`;
`g` is unused in-group; `f True` is *outside* the group.

**After erase, `TypeOfHM (erase e) (int × bool)` fails.** `anns_eq` forces both
specs `.mono`. Two candidate witness choices, both die:

| Choice | `MonoTyped` | Body `(g, f True)` |
|---|---|---|
| `τf = α→α`, `G = [α]` | `g`’s RHS is `f 3`. Under opening `Y`, `f : Y→Y`, so `Y = int`. Must hold for **every** fresh `Y`. Fails cofinitely. | would work (`genGroup = ∀α. α→α`) |
| `τf = int→int`, `G = []` | holds (`f 3` pins the unique monotype) | `bodyScheme = int→int`; `f True` fails |

Failing premises: `RecSpecs.MonoTyped` on `g`, or the body `TypeOfHM.var` on
`f True`. There is no third choice of `G`/`τf`.

This is the fused rule biting: under `.poly`, an in-group use at `int` does
**not** pin `f`’s body scheme; under `.mono`, it does. “Uses at one monotype”
does not restore the independence that `.poly` in `rhsCtx` was giving you.

`TypeOfHM.weaken_scheme` (`InferW.lean` 17227–17240) is the right lemma for
“more-general **body** scheme still types the body.” It does not help
`MonoTyped`. The failure is in `rhsCtx`, not `bodyCtx`.

### Single-member variant (poly rec at a ground type)

```
let rec f : ∀a. a → int = λx. f 3
in f True
```

In-group use of `f` at `int` only (one monotype). `PolyTyped`: for every skolem
`Y`, `λx. f 3 : Y→int` because `f` in `rhsCtx` is `∀a. a→int` and `f 3 : int`.
Body `f True : int`. After erase, the same two-table failure (`α→int` not
cofinite vs `int→int` killing `f True`).

Whether you classify `f 3` as “poly rec” (`int ≠ a`) is exactly the ambiguity
in the next section. As written (“one monotype”), the side condition passes.

---

## 2. The cut’s two formulations are not equivalent

§2 states as **equivalent**:

1. **Weak (use-site).** Every in-group use of every member is at one monotype.
2. **Strong (rule).** “The `hpoly` half of the fused rule is removed; `letRec`
   is pure Damas–Milner.” Infer binds every member at a fresh monotype and
   unifies; `InferRecGroup.consPoly` (`InferW.lean` 3105–3114) is gone;
   `RecSpec.init` no longer maps `some σ` to `.poly`.

They are not equivalent.

- (1) holds of the counterexample in §1; (2) **rejects** it: `g = f 3` pins
  `α = int`, then body `f True` fails unification. That program is *not* “two
  in-group types” (the v1 mixed-group case). It is DM pinning from a single
  in-group ground use.
- (2) is also what “enforcement is automatic via unification” describes. The
  `int = bool` illustration in §2 is only the two-type case; it does not
  mention the one-type-inside / poly-outside case.
- (1) is the side condition on the coherence lemma. So the lemma is conditioned
  on something Infer-as-DM does not actually implement, and under which the
  lemma is false.

**The language cut you will actually ship is (2), and it is strictly larger
than advertised.** Programs like

```
let rec f : ∀a. a → a = λx. x
    and g             = f 3
in (g, f True)
```

are well-typed in current `TypeOfHM`, in OCaml with an explicit polymorphic
signature, and under (1). They become illegal under (2). That is a real
expressivity cut, not “no in-group poly use.” Write it down.

Under (2) the *intended* lemma is not the one in §3. It is closer to

> `Infer_DM e τ → TypeOfHM (erase e) τ`

i.e. Infer.sound against the *erased* term. `TypeOfHM e τ` of the annotated
source is the wrong hypothesis (next section).

---

## 3. `TypeOfHM` of the annotated source cannot be “pure DM”

Pipeline §6 step 2: “Infer (`TypeOfHM` on the source) — enforces the §2 cut.”

Strong cut: all specs `.mono`. Current `TypeOfHM.letRec` (`Core.lean` 3394–3400)
plus `RecSpecs.WF.anns_eq` (`Core.lean` 3081):

```
RecSpec.ann (.mono _) = none
RecSpec.ann (.poly σ) = some σ
anns_eq : specs.map RecSpec.ann = anns
```

If the source still carries `some σ` (it does: Infer/bounds run *before*
erase), `anns_eq` **forbids** all-`.mono` specs. There is no `TypeOfHM`
derivation of an annotated `letRec` that is pure DM.

So one of the following has to give. v2 picks all of them at once:

| Choice | Consequence |
|---|---|
| A. Change `TypeOfHM.letRec` so stored anns are decoration-blind (like `var` tyArgs) | Then `TypeOfHM e τ` already ignores letRec anns; the letRec case of coherence is trivial; floor/ceiling is a *separate* check, not part of `TypeOfHM`. |
| B. Apply `TypeOfHM` only to `erase e` | Then there is no “`TypeOfHM` on the source.” Infer.sound **is** the coherence lemma. Completeness is against Infer, not against current `TypeOfHM`. |
| C. Keep current `TypeOfHM` (fused, `anns_eq`) | Then Infer-as-DM is **incomplete** (rejects §1) and, with floor semantics, **unsound** (next section). The §3 lemma is false. |

§6 step 2 as written is C plus “enforces the cut,” which is impossible.

`Infer.letRec` today (`InferW.lean` 3018–3040) still requires
`∀ σ, some σ ∈ anns → σ.WF` and `RecSpec.init` still emits `.poly σ`
(`InferW.lean` 1600–1603). That acceptance is acknowledged; the *replacement*
rule is not specified as a change to `TypeOfHM`.

---

## 4. Floor vs restriction: the doc contradicts itself

**§2 (how annotations participate):**

> the annotation does **not restrict** — `f : int→int` on a member whose RHS
> infers `∀a. a→a` leaves `f` at `∀a. a→a`, not `int→int`. That is the sound
> direction … not a bug.

**C5 (corrected argument):**

> every in-group use is monomorphic, so the annotation is only ever a
> **restriction/check**, and dropping it loses nothing that the group’s typing
> needs.

A floor and a ceiling are opposite. Pick one.

### If floor (as §2, as §5 bullet “dropping never restricts”)

User-visible semantics, not an implementation detail of erase. Infer runs on
the source, *before* erase; whatever Infer does with the annotation is what
the user gets.

```
let rec f : int → int = λx. x
in f True
```

- Current `TypeOfHM`: `f` is `.poly (int→int)`; body `f True` fails. **Illegal.**
- Floor Infer: RHS infers `α→α`, `genGroup = ∀a. a→a`, which `Generalizes`
  `int→int` (`PolyTy.Generalizes`, `InferW.lean` 17227–17229: `M'` at least as
  general as `M`). Floor passes. Body sees `∀a. a→a`. **Legal.**

So floor Infer is **unsound** against current `TypeOfHM`. It is also the
opposite of ML/Haskell signature semantics (a signature is a ceiling). Calling
it “the sound direction of drop-and-re-infer” mixes up two relations:

- Machine `TypeOfHM` of `erase e` always sees `genGroup` (more general). True.
- Infer of the *source* currently pins (`InferRecGroup.consPoly`,
  `bodyScheme (.poly σ) = σ`). If Infer keeps pinning, `f True` is rejected
  *before* erase and the user never observes the machine’s extra generality.
  Floor is a deliberate **language change**, not a consequence of erase.

`letIn` remains a ceiling (`Infer.letInAnn` pins `σ`; C4 reuses the same `M`).
So under §2, `let rec f : int→int = λx. x in f True` would type and
`let f : int→int = λx. x in f True` would not. That split needs to be a
bullet, not an accident.

### If ceiling (as C5, as current `TypeOfHM`)

Then §2’s `f : int→int` example is **wrong**: `f` stays at `int→int` in the
source typing; after erase the *machine* derivation may pick `∀a. a→a` and
instantiate back (coherence, not user-visible extra uses). Dropping does not
“leave `f` at `∀a. a→a`” in any program Infer accepted.

C5’s worked example is compatible with a ceiling: `∀a. a→c` equals the
inferred `∀α. α→C` after opening. No extra uses appear.

### Floor check with dangling outer tyvars

“Check `genGroup G τ` against the annotation” on C5’s inner `∀a. a→c` only
makes sense **after** the outer `openTyVars`. Compare unopened
`{1, a→bvar1}` to `∀α. α→C` and `Generalizes` fails. Infer.letInAnn already
opens the RHS first (`InferW.lean` 2983); the floor check must run on that
opened scheme, not on the stored one. Not specified.

---

## 5. Claim-by-claim (v2)

### Language cut — **NOT-ESTABLISHED** (internally inconsistent)

The cut as (2) is a coherent design. The cut as (1), the claim that (1)⇔(2),
and “enforcement is automatic / no decidability question” referring to (2)
while the lemma is conditioned on (1), are not. See §§1–2.

“There is no decidability question” is true of (2) (HM is decidable) and
irrelevant to I2 (unannotated poly rec). Fine as a parenthetical.

### C1 — **TRUE**

v2’s corrections are right: nest is both arms (`InferW.lean` 2486–2498);
deletion of `TypeOfElabHM`/`sourceSound` is Stages 2–3; CEK manufactures no
term-level Λ. Residual nit, not load-bearing: all-`.poly` groups still nest
*today* even though their schemes already exist, so “n² is purely type-passing
+ let polymorphism” is the right slogan for *why a Λ is needed for `.mono`*,
not a description of the current `.poly` arm.

### C2 — **TRUE** as the intended post-cut rule; do not cite `recclo` as already being that

v2 now says the machine “also has the `PolyTyped` half; the §2 cut removes
it.” Good. After the cut, `ValTyped.recclo` still *takes* `hpoly`; it becomes
vacuous because there are no `.poly` specs. That is fine. Runtime
`forceRecclo` still types RHSs in `bodyCtx` (`recclo_body_typed`,
`CekMachine.lean` 969–981, 2908–2915) — “mono inside” remains a source
constraint.

### C3 — **TRUE**

Unchanged. `ann.Pins` becomes vacuous; reuse `paramTy`.

### C4 — **TRUE** (argument now matches the proof)

Reuse the same `M`; `erase (rhs.openTyVars Xs) = erase rhs` under §5 including
`var i _ → var i []`. Nested λ ascriptions must go (caveat now present).
`GeneralisesTo none` types the closed erased term; after uniform drop there
are no type `bvar`s left in `Expr` (only `lambda`/`letIn`/`letRec`/`var tyArgs`
carried types, all dropped). Q3 and Q4 hold for this case.

Do **not** upgrade C4 to floor semantics; the proof is a ceiling proof (same `M`).

### C5 — **example TRUE; general claim NOT-ESTABLISHED**

The worked example still types after erase (`specs = [.mono (α→C), .mono (α→C)]`,
`G = [α]`, `C ∉ G` forced by cofiniteness). No in-group uses, so it is in both
(1) and (2).

The general claim is “supported by dropping, provided the §2 cut.” Under
reading (1) that is false (§1). Under reading (2) it is a claim about
`Infer_DM`, not about `TypeOfHM` of the annotated source (§3). The C5
paragraph still argues from “annotation is a restriction/check,” which §2
retracted.

### C6 — **TRUE**

v2’s split is right: self-contained poly-rec anns are Stage 1 / `IsErased`
today; I1 is the dangling sub-case; uniform erase drops both by policy. If
you ever want the self-contained case back, keep `WF` anns; that is still
out of scope.

### I1 — **TRUE**

Three closed-machine branches still fail, for the same reasons as v1.
“Source typechecker has a fourth move” is true of `TypeOfHM` and of
`Infer.letInAnn` (opens then descends); false of Surface (`lowerPoly` still
self-contained) and of `TypeOfElabHM` on the skeleton (`AreLC` vs `[]`).
v2 is more careful that I1 is a sub-case of the cut *and* an independent
machine wall under selective keeping. Keep both.

`f[t]` remains documentation of existential `instArgs`, not syntax. The rec
call is `f (Cons x Nil)`.

### I2 — **TRUE** (non-claim)

### Pipeline / §6 — **TRUE as order; FALSE as “Infer = TypeOfHM on the source”**

Order `lower → Infer + bounds (source) → erase → machine` is the right
response to `Bounds.Synth` throwing on `lambda none` (`Synth.lean` 662–665)
and reading `letIn`/`letRec` anns (669–680). D4 reversal is correctly
flagged. BL-erase ≠ CEK erase: good.

“Infer (`TypeOfHM` on the source)” is the contradiction in §3. Write Infer.sound
as `Infer e τ → TypeOfHM (erase e) τ` or change `TypeOfHM.letRec`.

**Bounds still does not open.** `inferBoundsΦ` / `checkBoundsΦ` walk the term
*as stored*. C5’s inner `∀a. a→c` is `{1, arrow (bvar 0) (bvar 1)}` on the
source; `letRecProvisional` feeds `σ.body` with a dangling `bvar 1` into the
group env (`Synth.lean` 430–433). Infer/TypeOfHM get those bvars opened by
outer `GeneralisesTo` / `letInAnn`; Bounds does not. “Bounds on source” is
necessary and **not sufficient** for C4/C5. Either Bounds must open in
lockstep with Infer, or it must run on an opened copy. Not in v2.

`checkBoundsΦ rhs σ.body` on the outer annotated let similarly checks the
unopened RHS against a scheme *body* (bvars, not an opening). Pre-existing
for scoped λ ascriptions; lifting `lowerPoly` makes scheme bodies the same
shape.

### `erase` §5 — **TRUE** as a function spec

Uniform drop; `var i _ → var i []`; `erase e ≠ e` for `λ(x:int)`. Q4
(`erase ∘ openTyVars = erase`) holds by induction on `Expr`: the only
type-carrying constructors are `lambda` / `letIn` / `letRec` / `var`, all
stripped to something `openTyVarsAux` cannot change. Match patterns carry
no types. This commutation is no longer a risk if the definition stays as
written.

### Q2 (`IsErased` recut) — less scary than v2 says

Uniformly erased terms **already satisfy** current `IsErased`
(`CekMachine.lean` 10–24): `lambda none`, `var []`, and
`∀ σ, some σ ∈ anns → σ.WF` is vacuous for `anns = [none,…]`.
`openTyVars_eq_self_of_erased` and `GeneralisesTo_inst_ann` therefore already
apply. The `some σ` branches become dead, not false. Re-cutting the predicate
is hygiene; it is not a new preservation proof if the machine only ever sees
erased terms. The mono half of `recclo_body_typed` is exactly what force
needs.

You *do* still need to stop constructing `ValTyped.recclo` with `.poly` specs
for source-annotated groups — but that is because those terms are erased
before the machine, not because `IsErased` rejects them.

### Well-posedness of `TypeOfHM` on closed annotated programs — **TRUE**

Unchanged from v1. Outer `openTyVars` rewrites inner scheme bodies
(`RecGroup.openAnns` at `d + paramCount`). The inner `poly_wf` check sees
`∀a. a→C`.

---

## 6. What a true lemma would look like

Pick a spec, then the lemma is almost Infer.sound.

**Recommended (matches the strong cut, the pipeline, and the machine):**

1. `TypeOfHM` is the machine spec, used on **erased** terms. `letRec` is
   `MonoTyped` only (`hpoly` vacuous). Annotations are not in the term.
2. Infer on the source: all members `.mono` (`RecSpec.init` maps everything
   to `.mono`; delete / never take `consPoly`). Body env is
   `specs.map (bodyScheme G)` = `genGroup`s. Then, optionally:
   - **Ceiling:** check that each stored (opened) `σ` is `Generalizes`d *by*
     the annotation from the inferred scheme? Wait — ceiling is the other
     direction: body typed against `σ`, i.e. `σ.Generalizes (genGroup G τ)`
     is wrong; you want to type the body in an env of `σ`s, or require
     `genGroup G τ` instantiates to what `σ` says in the *restricting*
     direction (`σ` less general). Simplest ceiling: Pins, as today, but then
     you cannot also drop-and-re-infer extra body uses. Coherence-from-source
     `TypeOfHM` is the v1 lemma and is false.
   - **Floor:** `PolyTy.Generalizes (genGroup G τ) σ_opened`. Rejects
     over-claiming (`f : ∀a. a→a = λx. 3`). Does not restrict uses. Then
     Infer accepts strictly more than current `TypeOfHM`. Do not claim
     Infer.sound against current `TypeOfHM`.
3. Infer.sound: `Infer e τ → TypeOfHM (erase e) τ`. That **is** coherence.
   There is no `TypeOfHM e τ → TypeOfHM (erase e) τ` obligation for
   annotated `letRec`, because `TypeOfHM` is not applied to those terms.
4. C3/C4 remain a real `TypeOfHM`-to-`TypeOfHM` fact on the erased term’s
   cousins (drop λ / `letIn` anns, reuse `paramTy` / `M`). They can stay
   packaged as one “erase preserves `TypeOfHM`” lemma **provided** the
   `letRec` case of the induction uses only `.mono` specs — i.e. the
   induction is on Infer, or on `TypeOfHM` of a term whose `letRec` anns are
   already `none`.

If you insist on `TypeOfHM` of the annotated source as the hypothesis, you
must first change `TypeOfHM.letRec` so `anns` are ignored (option A). Then
the letRec case of coherence is `erase` only dropping something the rule
does not read, and the side condition is unnecessary because there is no
`.poly` in `rhsCtx` to lose.

Do not keep current fused `TypeOfHM`, the weak use-site condition, *and*
Infer-as-DM. That is v2.

---

## 7. Things v2 got right

- v1 coherence was false; the mixed-group sibling example is correctly
  recorded.
- C5’s “restriction-only” claim was false for mixed groups; the worked
  example still checks.
- C6 is a language cut, not an I1 corollary; Stage 1 already keeps `WF`
  poly-rec anns.
- Two-term pipeline; `Bounds.Synth` throws on `lambda none`; BL-erase ≠
  CEK erase.
- `var i _ → var i []`; `erase e ≠ e` for `λ(x:int)`; C1 nest on both arms;
  C2 is the DM half of a fused rule.
- I1’s three closed-machine branches; source opening vs machine `force`.
- Q4 commutation is the right C4 obligation, and the §5 definition discharges
  it.
- Existing `IsErased` already holds of uniformly erased terms (vacuous `WF`).

---

## 8. Things that must change before this is safe to implement

1. **Split the cut.** (1) use-site “one monotype” ≠ (2) “no `hpoly` / Infer
   binds monotypes.” The lemma is false under (1). The implementation is (2).
   (2) additionally rejects in-group *ground* instantiations that pin the
   body (`g = f 3 in (g, f True)`). Say so.
2. **Pick Infer’s spec.** `TypeOfHM` of annotated source (fused, `anns_eq`)
   cannot be what Infer-as-DM produces. Either decoration-blind letRec anns,
   or `TypeOfHM` only on `erase e` with Infer.sound = coherence.
3. **Pick floor or ceiling**, once, and align C5 / §2 / §5 / `letIn`. Floor
   is unsound against current `TypeOfHM` and unlike ML. Ceiling makes §2’s
   `f : int→int` example false. Floor checks must run on *opened* schemes.
4. **Bounds must open** (or run on an opened term). Walking stored dangling
   `bvar`s in inner scheme bodies is not “bounds on source, annotations
   present.”
5. Specify the Infer change as a rule: `RecSpec.init` emits `.mono` for
   annotated members too; `consPoly` unused; floor/ceiling as a sidecar.
   `Infer.letRec`’s `σ.WF` premise is on the term Infer actually sees (opened
   under enclosing `letInAnn`), not on stored dangling inner anns of a
   closed fragment.
6. Do not re-prove preservation against a new `IsErased` unless the machine
   will see non-erased terms. Uniformly erased terms already inhabit the
   current predicate.

Until (1)–(3) are one design rather than three, C3–C5 “stand or fall with
coherence” is still the right warning, and the lemma on the page is still
the thing to refuse to prove.
