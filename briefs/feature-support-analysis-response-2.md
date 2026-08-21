# Feature-support analysis — revision 2 (post adversarial review)

**Status: revision 2.** This supersedes `feature-support-analysis.md` (v1) and
incorporates the findings of `feature-support-analysis-response-1.md`. The load-bearing
change: the v1 coherence lemma was **false**, and the fix is a **language cut** — "no
in-group polymorphic use" — which is exactly the "`f` and `g` are typed monomorphically
inside the rec block" position we had already settled on, but now stated as a *source
restriction enforced in inference*, not as a consequence of erasing.

## Revision notes (what changed from v1)

1. **The coherence lemma (§3) was FALSE as stated.** Counterexample:
   ```
   let rec f : ∀a. a → a = λx. x
       and g             = (f 3, f True)
   in g
   ```
   `f`'s self-contained annotation puts `f` at its full scheme inside the group
   (`RecSpec.rhsEntry (.poly σ) = σ`), so `g`'s RHS uses `f` at `int` and `bool`.
   Uniform erase turns `f` into a `.mono` member and `g`'s RHS can no longer type. The
   fix (§2 cut, §3 lemma): the design now enforces **no in-group polymorphic use** —
   every in-group use of every member (self *or* sibling) is at one monotype.
2. **C5's "annotations are restriction-only" was wrong** for mixed groups: an annotation
   switches `rhsEntry` from a monotype to a scheme, which is load-bearing for *sibling*
   uses, not just the member's own recursion. (C5's worked example was still correct.)
3. **C6's "cannot be recovered without type-passing" was wrong.** Self-contained poly-rec
   annotations are already supported by Stage 1 (`IsErased.letRec` keeps `WF` binding
   annotations; `PolyTyped` types them). What drops them is the **uniform erase** — a
   deliberate cut, not a corollary of I1. I1 is about the *specific* sub-case of
   poly-rec + an outer scoped tyvar.
4. **The pipeline is two-term.** `Bounds.Synth` reads lambda ascriptions and let
   annotations and throws on `lambda none`; the erase must run *after* Infer/bounds, on
   a separate term: `lower → Infer + bounds (source) → erase → machine`.
5. **Minor:** `erase` zeroes `var` tyArgs (`var i _ → var i []`); `erase e ≠ e` for
   programs with concrete lambda ascriptions (`λ(x : int)`); C1's nest is both `.mono`
   and `.poly` arms; C2's "exactly DM" should be "the fused DM + poly rule, restricted
   to the DM half by the cut".

---

## 0. History and motivation (why these moves, and what actually matters)

The project went **erasure → type-passing → erasing CEK**. Each move is explained
below, but first, the frame that matters:

**What matters vs. what doesn't.** The actual goals are two *language features*:
**(1) scoped type variables**, usable everywhere, and **(2) polymorphic recursion**
(recursive bindings usable at different types). Whether the operational semantics is
type-erasing or type-passing is **incidental** — a means, not an end. The O(n²)
elaboration blowup and the second typing relation (`TypeOfElabHM`) are **costs** to be
removed, not features. The machine work is only worth doing insofar as it serves (1)
and (2); agents reading this document should treat "erased vs type-passing" and "which
machine" as implementation choices, never as requirements.

- **Erasure era** (`e374bc9`, ~06-16): substitution `Step`, an `IsTyErased` premise on
  the safety theorems.
- **Type-passing migration** (`e7639f7`/`e4c5129`, ~06-25): done *precisely* to support
  the combination of scoped tyvars and polymorphic-recursive bindings, which the
  erasure era could not:
  - **Polymorphic recursion** needs load-bearing per-binding annotations (the
    annotation is what puts a member at its full scheme inside its own group). Erasure
    cannot drop those annotations without falling back to monomorphic recursion — a
    loss of expressivity/power. So erasure had to go.
  - **Scoped type variables** leave dangling orphan `bvar`s in annotations
    (`λ(x : a). x` references the enclosing `∀a`, which is not a term binder). The only
    way to resolve those orphans without dropping the annotations is to *instantiate
    the `bvar`s across let-reduction* — exactly what type-passing does
    (`var [tyArgs]`, `instTy`, type-beta). So type-passing was the mechanism that made
    the two features coexist.
  This forced `TypeOfElabHM`, the elaboration relation, `Infer.sourceSound`, and the
  O(n²) Λ-outside nest for letRec generalisation.
- **CEK migration** (current, `0c0aa32`): the *sole* motivation was the belief that an
  *environment* semantics — which a CEK machine provides and the substitution `Step`
  did not — would (a) avoid the letRec O(n²) elaboration Λ-nest blowup, and (b) either
  keep elaboration structurally similar or eliminate the need for elaboration (the
  second typing relation and its `sourceSound` induction) altogether. Stage 1 (the
  machine + metatheory) is proved, sorry-free, axiom-clean.

The question this doc answers: given all that, **what feature set can we actually
support?** — and the honest answer (now sharpened by review) is that scoped tyvars
survive (dropped and re-inferred), polymorphic recursion *outside* blocks
(generalisation) survives, and polymorphic recursion *inside* blocks is **removed by a
language cut**, not by any fundamental machine incompatibility.

---

## 1. The machine (recap, so the rest has a fixed reference)

`CekMachine.lean` defines `Val`/`VEnv`/`Kont`/`State`/`StepM` and the typing
invariant `ValTyped`/`EnvOK`/`KontTyped`/`StateOK`, with headline theorems
`progress`/`preservation`/`preservation_*`/`type_safety`/`type_safety_closed`/
`stepM_deterministic`, all proved.

Three facts about it are load-bearing for everything below:

- **The machine types *closed* terms.** `StateOK (.eval E e k)` requires
  `TypeOfHM ⟨Γ⟩ e τ` on `e` *as it is* — no opening. `TypeOfHM` rejects dangling
  `bvar`s (`λ(x : bvar0). x` fails `paramTy.IsLC`; a scheme `∀b. b→a` with outer `a`
  fails `PolyTy.WF = ContainsBvarsUpTo paramCount body`).
- **The machine's typing is *existential*.** The witnesses in the typing rules are
  proof-level: `TypeOfHM.var` instantiates via `∃ instArgs`;
  `ValTyped.recclo` chooses `specs` and the gen-var pool `G`; `TypeOfHM.letIn`
  chooses the scheme `M` (when unannotated). This existential freedom is what makes
  "drop the annotation and re-infer" sound — see §3.
- **The `letRec` rule is *fused*.** `TypeOfHM.letRec` and `ValTyped.recclo` take *both*
  `hmono` **and** `hpoly` premises (`Core.lean` 3394–3400, `CekMachine.lean` 296–303):
  unannotated members are at shared monotypes inside the group (Damas–Milner), and
  annotated members are at their **full schemes** inside the group (polymorphic
  recursion *and* cross-boundary polymorphic use). §2's language cut removes the
  `hpoly` half; it is not something the machine "already" lacks.

---

## 2. Claims: what we believe we can support

### The language cut (this is the thing everything else hangs off)

**Cut.** Inside a `letRec` group, every in-group use of every member — a member's own
recursive uses **and** a sibling's uses of it — is at **one monotype**. Equivalently:
the `hpoly` half of the fused rule is removed; `letRec` is pure Damas–Milner
monomorphic recursion.

**Why it exists.** It is what makes the uniform erase sound (§3). Without it, a
self-contained poly annotation on `f` is load-bearing for a *sibling* `g` that uses `f`
at two types inside the group (revision-note counterexample), and dropping it breaks
`g`'s typing.

**What it removes.** Self-poly-recursion (`f` used at two types inside `f`) and
sibling-poly-use (`g` uses `f` at two types inside `g`) — i.e. all polymorphic use
*inside* the block. It does **not** remove polymorphic use *outside* the block
(generalisation, §C2).

**How it is enforced.** This is a *source-language* restriction, enforced in inference
(`Infer` rejects a `letRec` whose in-group uses are polymorphic), not a property of the
erased term or of the machine. The current `Infer.letRec` accepts in-group poly use
(it maps annotated members to `.poly` specs); that acceptance must be removed. Note
the enforcement is *automatic*, not a separate check: monomorphic-recursion inference
binds each member at a fresh monotype and unifies, so a poly use simply fails
unification (see the revision-note counterexample, where `f 3` then `f True` forces
`int = bool`). There is no decidability question here.

**How annotations participate (under the cut).** An annotated member's scheme is a
*body-scheme declaration*, not an in-group constraint. Infer the member at a fresh
monotype (monomorphic recursion), generalise the monotype for the body, then check the
annotation against the generalised scheme as a **floor**: the generalised scheme must be
*at least as general as* the annotation. Consequence: the annotation does **not
restrict** — `f : int→int` on a member whose RHS infers `∀a. a→a` leaves `f` at
`∀a. a→a`, not `int→int`. That is the sound direction, and it is a deliberate
consequence of "drop the annotation and re-infer", not a bug.

### C1. CEK eliminates type-passing, elaboration, and the O(n²) Λ-nest

**Argument.** The O(n²) blowup is a *type-passing* artifact, not a letRec artifact.
In type-passing, "generalised value" must be a term-level Λ, because `var j [tyArgs]`
does type-beta against it. For a `letRec` group, the *body* uses each member at its
generalised scheme (`bodyScheme`), so the elaborator re-materialises each member as a
`letIn (some scheme)` Λ wrapped around a **full copy of the group** (`InferW.lean`
`letRecElabNest` ~2486–2498 — *both* the `.mono` and `.poly` arms do this) — n members
× n bindings = O(n²). The CEK machine puts generalisation in the environment
(`ValTyped.recclo` types each rec-clo at its `bodyScheme`), so no Λ is manufactured,
the term keeps its shape, and there is nothing for a second typing relation
(`TypeOfElabHM`) or a second soundness induction (`Infer.sourceSound`) to be about.

**Status:** proved (Stage 1); `TypeOfElabHM`/`sourceSound`/`eOut` deletion is Stages
2–3 — they still exist in the tree today.

**Note (important, and easy to get backwards):** this is *independent* of both scoped
type variables and of the mono/poly-recursion distinction. Even monomorphic recursion
needs body generalisation, hence the Λ-nest, in type-passing. The n² is purely "type
passing + let polymorphism", and the machine removes it regardless.

### C2. Monomorphic recursion for `letRec` (poly *outside*, mono *inside*)

**Claim.** `letRec` members are typed at **monotypes** inside the group (recursive and
sibling uses at one type each), and **generalised for the body** (each member's
body-scheme is `genGroup G τ`). Outside the block the members are fully polymorphic.

**Argument.** This is the Damas–Milner `let rec` half of the fused rule: `MonoTyped`
types each RHS at its opened monotype, `RecSpec.bodyScheme (.mono τ) = genGroup G τ`
gives the body-scheme. (The machine's rule also has the `PolyTyped` half; the §2 cut
removes it.) No annotation is needed for this; the schemes are *invented* by
generalisation.

**What is *not* supported:** polymorphic use *inside* the block — a member's own
recursive uses at different types, or a sibling's uses at different types (§2 cut).

### C3. Scoped type variables in lambda ascriptions (`λ(x : a). x`)

**Claim.** Supported, by *dropping* the ascription.

**Argument.** The ascription is a monotype slot. Its dangling `bvar` (`a`) is what
makes the closed term untypable. Dropping it (`λ(x : a). x → λx. x`) is sound because
the lambda rule with `ann = none` *infers* the parameter type from the surrounding
derivation — concretely, in the force case of `f[int] 3`, the continuation demands
`int → B` and the erased `λx. x` infers `int`. The ascription is always a monotype,
always inferable, so dropping loses no typing power.

### C4. Scoped type variables in `letIn` annotations (`let g : …a… = …`)

**Claim.** Supported, by *dropping* the annotation (unconditionally, per the uniform
erase of §5) and re-inferring.

**Argument (corrected from v1).** For a *non-recursive* let, dropping the annotation is
sound, and the proof does **not** need a more general scheme — it reuses the **same**
`M`:
- Annotated cofinite premise: `∀ Xs, TypeOf ctx (rhs.openTyVars Xs) (M.openVars Xs)`.
- Unannotated cofinite premise: `∀ Xs, TypeOf ctx (erase rhs) (M.openVars Xs)`.

Uniform erase deletes exactly the positions `openTyVarsAux` rewrites (λ ascriptions,
nested scheme bodies, `var` tyArgs), so `erase (rhs.openTyVars Xs) = erase rhs`; the
induction hypothesis on the opened derivation yields the unannotated premise with the
same `M`, and the body keeps the same `M` in the environment. `TypeOfHM.var` is
existential, so "drop makes it more general and uses fail" never arises.

**Caveat (v1 omitted):** C4 is not standalone. If only the `letIn` annotation were
dropped and a `λ(x : bvar 0)` ascription kept, `GeneralisesTo none` would type the
*unopened* λ and `paramTy.IsLC` fails. The uniform drop of λ ascriptions is required.

### C5. Scoped type variables in `letRec` annotations, under the §2 cut

**Claim.** Supported, by *dropping* the annotation and re-inferring — **provided** the
program is in the §2 cut (no in-group poly use).

**Argument (corrected from v1).** The v1 claim "under monomorphic recursion the
annotation is restriction-only" is false in general: an annotated member sits at its
full scheme inside the group, so its annotation is load-bearing for any in-group use
that needs instantiation — including *sibling* uses (the revision-note counterexample).
What the §2 cut gives us is exactly that such uses do not occur: every in-group use is
monomorphic, so the annotation is only ever a restriction/check, and dropping it loses
nothing that the group's typing needs. The worked example from v1 is still correct:
after erase, `w : C` pins each member's monotype to `α→C`, `G = [α]` keeps `C` rigid,
and the existential instantiation recovers `f[w] w : C`:

```
let h : ∀c. c → (c × c) =
  λ(w : c). let rec f : ∀a. a→c = λ(x : a). w
                and g : ∀b. b→c = λ(y : b). w
            in (f[w] w, g[w] w)
in h[int] 3
```

erases to `… let rec f = λx. w and g = λy. w in (f[w] w, g[w] w) …` and typechecks at
`(int, int)`.

### C6. Polymorphic recursion *inside* blocks — removed by the cut, not by I1

**Claim (corrected from v1).** Polymorphic use inside a block is **not supported**,
because the §2 cut removes it. This is a *language cut* (uniform erase + "no in-group
poly use"), **not** a corollary of the I1 wall.

**Clarification.** Two things were conflated in v1:
- **Self-contained** poly-rec annotations (`f : ∀a. a→a`, own param only) are `WF` and
  are already supported by Stage 1: `IsErased.letRec` keeps `WF` binding annotations,
  and `PolyTyped` types the RHS scheme-relatively. They need no type-passing.
- **Dangling** poly-rec annotations (referencing an outer scoped tyvar) are what I1 is
  about, and *those* genuinely need type-passing.

The uniform erase drops *both*, because it drops all annotations. So poly-rec-inside is
gone by the cut. If we ever wanted it back, keeping `WF` annotations would recover the
self-contained case for free — but that selective keeping is deliberately out of scope
(uniformity/generality was chosen over the expressivity).

---

## 3. The coherence lemma and the existential-recovery argument

The pattern behind C3–C5 is: **dropping an annotation is sound because the machine's
typing is declarative with existential witnesses.** Whenever the source typing pins a
type to some outer rigid variable, the erased derivation can choose its existential
witnesses (the scheme `M`, the `specs`, the gen-vars `G`, the `instArgs`) to pin the
*inferred* type to the same variable. Generalisation only ever makes a type *more*
general, and more-general types can be instantiated back to whatever the body needed.

**This informal argument is sound for `lambda` and `letIn` (C3/C4), and for `letRec`
only under the §2 cut (C5).** Its formal face is the coherence lemma:

> **Coherence lemma (to be proved).** If `TypeOfHM e τ`, and **every in-group use of
> every `letRec` member (self or sibling) is at one monotype**, then
> `TypeOfHM (erase e) τ`, where `erase` is the structural function of §5.

The side condition is the §2 cut, stated on the *derivation* rather than on whether
annotations are present. Without it the lemma is **false** (revision-note
counterexample). With it, dropping `letRec` annotations is sound because no in-group
use needs the scheme the annotation supplied.

Well-posedness note: `e` is the *closed* whole program; `TypeOfHM e τ` on it **is**
provable because the annotated-let rules open their own scoped variables internally
(`GeneralisesTo`/`openBoundTyVars`) — the top-level `let h : ∀c. …` opens `c → C`
before the inner `letRec`'s `WF` check runs. So the source judgement is not vacuous,
and the coherence statement is exactly "erasing preserves the same monotype τ".

**This lemma is the single highest-risk claim in this document.** If it fails, C3–C5
fail with it. It is the thing the next review should attempt to falsify first.

---

## 4. Incompatibilities: what we cannot support

### I1. Scoped type variables *inside a polymorphically-recursive* `letRec` annotation

The one genuine *machine* wall — now a sub-case of the §2 cut, but with a deeper reason
worth recording. Example (where `f[t]` is shorthand for "`f` instantiated at type `t`";
the surface has no type-application syntax and forces the instantiation by context):

```
let h : ∀c. c → (c × c) =
  λ(w : c). let rec f : ∀a. a→c = λ(x : a). f[List a] [x]   -- recursive call at List a ≠ a (poly-recursive), returns c
            in (f[List c] [w], w)
in h[int] 3
```

`f`'s annotation `∀a. a→c` does two jobs: it enables polymorphic recursion (the
recursive call instantiates `a` at `List a`), *and* it pins the return type to the
outer `c`. The §2 cut already rejects this program (in-group poly use). Independently
of the cut, if one tried to keep this annotation in a closed machine term, all three
options fail:

1. **Keep it** — `c` is a dangling `bvar` (index ≥ `paramCount`), so
   `ContainsBvarsUpTo paramCount body` fails, `PolyTy.WF` fails, `RecSpecs.WF` fails,
   and `ValTyped.recclo` cannot be constructed.
2. **Drop it** — the member becomes monomorphic; the recursive call at `List a` is
   rejected.
3. **Open `c` to a fresh `fvar X`** — `WF` now holds, but at force time the continuation
   demands the *specific* instantiation (e.g. `int`), while the body types at
   `X`-involving types; `X ≠ int`, and the `GeneralisesTo` cofinite check
   (`∀ fresh Y, … Y→Y`) also fails because `X` is fixed while `Y` is fresh.

The *source* typechecker has a fourth move the machine does not: it opens `c → C`
*before* checking, so `∀a. a→C` is `WF` and everything lines up. The machine types
closed and has no opening. The only way to reconcile "load-bearing annotation" with
"outer rigid variable" is to **substitute** the instantiation into the term — i.e.
type-passing.

**Corollary.** `scoped tyvars inside a poly-rec letRec annotation` + `no type-passing`
are jointly impossible, even with selective keeping. (This is also why Haskell, which
erases types only at the runtime boundary, keeps a type-passing System-F core.) Note
the scope: this forbids *dangling* annotations only. Self-contained poly-rec
annotations are fine (Stage 1 keeps them); the §2 cut is what removes them, not I1.

### I2. (Non-claim, for completeness) Un-annotated polymorphic recursion

Inferring polymorphic recursion is undecidable (Mycroft/Henglein); it has always
required an annotation. Nothing about the CEK migration changes this; it is a language
fact, not a machine limitation.

---

## 5. The erasure, precisely

`erase : Expr → Expr` — a **uniform, structural annotation drop**. Every annotation is
dropped; there is no keep/drop branching:

- `lambda (some t) body → lambda none body`;
- `letIn (some σ) rhs body → letIn none (erase rhs) (erase body)`;
- `letRec anns bindings body → letRec (anns.map (fun _ => none)) (bindings.map erase) (erase body)`
  (all member annotations dropped — every member becomes monomorphically recursive,
  which the §2 cut makes sound);
- `var i _ → var i []` (**zero** the tyArgs, do not merely pass `[]` through — this is
  what makes `erase ∘ openTyVars = erase` hold, which C4's proof relies on);
- everything else is structural.

Notes:

- This is a genuine *drop*, not "open bvars to fvars" — call it **annotation dropping**.
- `erase e ≠ e` in general: `wrapCoreParams`/`lowerAnn` keep locally-closed ascriptions
  like `λ(x : int)` that are *not* scoped tyvars but still get dropped. Only programs
  with *no ascriptions at all* satisfy `erase e = e`.
- The §2 cut is what makes dropping `letRec` annotations sound; without it the uniform
  drop is unsound (revision-note counterexample).
- Dropping an annotation never *restricts* the member: the body scheme is the
  generalised monotype, which is at least as general as the dropped annotation. So an
  annotation acts as a floor-check, not a ceiling (§2) — `f : int→int` may come out as
  `∀a. a→a` after erase.
- The coherence lemma (§3) is the proof that dropping is typing-preserving (under the
  cut).

---

## 6. The pipeline (two terms — corrected from v1)

The erase does **not** sit simply "between lowering and the machine". `Bounds.Synth`
reads lambda ascriptions and let annotations off the term and **throws on
`lambda none`**; `Bounds` also reads `letIn`/`letRec` annotations. So there are two
terms, and the erase applies to the *second*:

1. `lower` (Surface → Core) — source term, annotations present, including outer scoped
   refs (requires lifting `lowerPoly`'s self-containment restriction: thread the
   ambient tyvar scope into `lowerPoly` the way `bindingLowerTyScope`/`letAnnTyPrefix`
   already do for lambda ascriptions).
2. **Infer** (`TypeOfHM` on the source) — enforces the §2 cut (rejects in-group poly
   use).
3. **Bounds** (`Bounds.Synth`/`Check`/…) on the source — annotations still present.
4. **`erase`** (§5) → machine term.
5. **Machine** (`CekMachine`) runs on the erased term.

This is a reversal of the original brief's D4 note ("`Expr` keeps its `ann` slots …
needed by `TypeOfHM`"): the source term keeps annotations; the machine term has none.
Also note `Bounds.Pipeline.eraseProgram` is BL-erase on Surface — a *different*
function; do not conflate it with CEK annotation-drop.

---

## 7. Open questions for the reviewer (attack these first)

1. **The coherence lemma (§3).** Is the restricted lemma — with the "no in-group poly
   use" side condition — provable, in particular the `letIn`-annotation and mono-
   `letRec`-annotation cases where the existential recovery must reproduce the exact
   monotype τ? (C3–C5 stand or fall with it.)
2. **`IsErased` / `ErasedState` under uniform erase.** The erased term has no
   annotations at all; the existing `IsErased` keeps `WF` `letIn`/`letRec` annotations
   (`CekMachine.lean` 1–24) and `openTyVars_eq_self_of_erased` / `GeneralisesTo_inst_ann`
   are proved against *that* predicate. Uniform drop is a *different* erase — a change
   of invariant, not a simplification. Confirm the machine's erased-ness predicate
   should be re-cut accordingly.
3. **`GeneralisesTo` for unannotated lets.** Under uniform erase, every annotated let
   becomes unannotated, so `GeneralisesTo … none e M L` types the *closed* `e`. Confirm
   no dangling `bvar` survives the erasure in any position (lambda, `letIn`, `letRec`,
   `var tyArgs`), and that the erased term is closed-typable at `M`'s opening.
4. **`erase ∘ openTyVars = erase`.** This commutation is load-bearing for C4. Confirm it
   holds for the §5 definition (in particular the `var i _ → var i []` zeroing).

---

## 8. Summary: what we get, what we give up

Three independent axes, stated plainly:

- **Scoped type variables — everywhere.** `lambda` ascriptions, `letIn` annotations,
  and `letRec` annotations all work: the uniform erase (§5) drops them and inference
  re-derives the types. *(Contingent on the coherence lemma, §3 — the one unproven
  piece.)*
- **Polymorphic recursion — outside blocks only.** `letRec` members are generalised for
  the body (fully polymorphic *outside*), but monomorphic *inside* the group. This is a
  **language cut** (§2), enforced in inference: no in-group polymorphic use, self or
  sibling.
- **No type-passing, no elaboration, no O(n²).** The erasing CEK machine gives all
  three (§2 C1). Generalisation lives in the environment, so there is no term-level Λ,
  no `TypeOfElabHM`, no `sourceSound`.

Two incompatibilities, stated separately because they are different in kind:

- **The cut** (§2): polymorphic use inside a block is not supported, by design — this is
  what makes uniform erase sound.
- **I1** (§4): even allowing selective keeping, `scoped tyvars inside a poly-rec letRec
  annotation` + `no type-passing` is impossible — that combination needs the outer rigid
  variable substituted at force time, which *is* type-passing.
