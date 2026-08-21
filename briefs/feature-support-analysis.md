# Feature-support analysis: what the CEK migration buys, and what it costs

**Status: draft for adversarial review.** This document records the settled
conclusions of a long design discussion (2026-08-20) about which language/type-system
features are compatible with the type-erasing CEK machine (`FHM/CekMachine.lean`,
Stage 1 complete). It is deliberately written as a list of **claims with arguments**,
so a reviewer can attack each argument independently.

**One-line settled position:** the CEK machine eliminates type-passing, elaboration,
and the O(n²) letRec Λ-nest; we keep **monomorphic recursion** for `letRec` (members
monomorphic *inside* the block, fully polymorphic *outside*); and **scoped type
variables work everywhere** — lambda ascriptions, `letIn` annotations, and (under
monomorphic recursion) `letRec` annotations — by **uniformly dropping all annotations**
at an erase step and letting inference recover the types. Polymorphic recursion
*inside* `letRec` blocks is **not supported** (it needs the annotations the uniform
erase removes).

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
support?** — and the honest answer is that scoped tyvars survive (dropped and
re-inferred), polymorphic recursion *outside* blocks (generalisation) survives, but
polymorphic recursion *inside* `letRec` blocks does not.

---

## 1. The machine (recap, so the rest has a fixed reference)

`CekMachine.lean` defines `Val`/`VEnv`/`Kont`/`State`/`StepM` and the typing
invariant `ValTyped`/`EnvOK`/`KontTyped`/`StateOK`, with headline theorems
`progress`/`preservation`/`preservation_*`/`type_safety`/`type_safety_closed`/
`stepM_deterministic`, all proved.

Two facts about it are load-bearing for everything below:

- **The machine types *closed* terms.** `StateOK (.eval E e k)` requires
  `TypeOfHM ⟨Γ⟩ e τ` on `e` *as it is* — no opening. `TypeOfHM` rejects dangling
  `bvar`s (`λ(x : bvar0). x` fails `paramTy.IsLC`; a scheme `∀b. b→a` with outer `a`
  fails `PolyTy.WF = ContainsBvarsUpTo paramCount body`).
- **The machine's typing is *existential*.** The witnesses in the typing rules are
  proof-level: `TypeOfHM.var` instantiates via `∃ instArgs`;
  `ValTyped.recclo` chooses `specs` and the gen-var pool `G`; `TypeOfHM.letIn`
  chooses the scheme `M` (when unannotated). This existential freedom is what makes
  "drop the annotation and re-infer" sound — see §3.

---

## 2. Claims: what we believe we can support

### C1. CEK eliminates type-passing, elaboration, and the O(n²) Λ-nest

**Argument.** The O(n²) blowup is a *type-passing* artifact, not a letRec artifact.
In type-passing, "generalised value" must be a term-level Λ, because `var j [tyArgs]`
does type-beta against it. For a `letRec` group, the *body* uses each member at its
generalised scheme (`bodyScheme`), so the elaborator re-materialises each member as a
`letIn (some scheme)` Λ wrapped around a **full copy of the group** (`InferW.lean`
`letRecElabNest`, the `.mono τ` case at ~2490) — n members × n bindings = O(n²).
The CEK machine puts generalisation in the environment (`ValTyped.recclo` types each
rec-clo at its `bodyScheme`), so no Λ is manufactured, the term keeps its shape, and
there is nothing for a second typing relation (`TypeOfElabHM`) or a second soundness
induction (`Infer.sourceSound`) to be about.

**Status:** proved (Stage 1); `TypeOfElabHM`/`sourceSound`/`eOut` deletion is Stages 2–3.

**Note (important, and easy to get backwards):** this is *independent* of both scoped
type variables and of the mono/poly-recursion distinction. Even monomorphic recursion
needs body generalisation, hence the Λ-nest, in type-passing. The n² is purely "type
passing + let polymorphism", and the machine removes it regardless.

### C2. Monomorphic recursion for `letRec` (poly *outside*, mono *inside*)

**Claim.** `letRec` members are typed at **monotypes** inside the group (recursive uses
at one type each), and **generalised for the body** (each member's body-scheme is
`genGroup G τ`). Outside the block the members are fully polymorphic.

**Argument.** This is textbook Damas–Milner `let rec`. It is exactly what the
machine's `ValTyped.recclo` already implements: `RecSpecs.MonoTyped` types each RHS at
its opened monotype (monomorphic recursion), and `RecSpec.bodyScheme (.mono τ) =
genGroup G τ` gives the body-scheme. No annotation is needed for this; the schemes are
*invented* by generalisation, so there is no annotation slot for a scoped tyvar to
dangle in.

**What is *not* supported:** polymorphic recursion *inside* the block — using `g` at
two different types inside `f`'s body. (This is the deliberate, acceptable sacrifice;
see §4.)

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

**Argument.** For a *non-recursive* let, an annotation is never load-bearing: the
annotated rule checks the RHS against the scheme and restricts the body's uses; the
unannotated rule infers the most general scheme, which is at least as general. Because
`TypeOfHM.letIn` chooses `M` existentially (when `ann = none`) and `TypeOfHM.var`
instantiates existentially, the erased derivation can pick `M` and the instantiations
to recover the same body type. A worked example is in §3.

### C5. Scoped type variables in `letRec` annotations, *under monomorphic recursion*

**Claim.** Supported, by *dropping* the annotation and re-inferring.

**Argument.** Under monomorphic recursion the annotation is check/restriction-only
(not what *enables* polymorphism — generalisation does that). Dropping it loses the
restriction, and the machine's existential typing recovers a type at least as general:
the proof can choose `specs = [.mono (α→C)]` and `G = [α]` (leaving the outer rigid
`C` *out* of the generalisation), so `f`'s body-scheme is `∀α. α→C` and the body's
uses instantiate at `C` — the linkage is preserved. Concretely:

```
let h : ∀c. c → (c × c) =
  λ(w : c). let rec f : ∀a. a→c = λ(x : a). w
                and g : ∀b. b→c = λ(y : b). w
            in (f[w] w, g[w] w)
in h[int] 3
```

erases to `… let rec f = λx. w and g = λy. w in (f[w] w, g[w] w) …`, and still
typechecks at `(int, int)`: `w : C` pins `f`'s monotype to `α→C`, and the existential
instantiation recovers `f[w] w : C`.

### C6. (Out of scope) Polymorphic recursion *inside* blocks

Not supported. Polymorphic recursion inside a block requires the per-binding
`letRec` annotations (the annotation is what puts a member at its full scheme inside
its own group); the uniform erase (§5) drops those annotations, so every member is
monomorphic inside the group. This is the one deliberate sacrifice (see §4 I1 for the
deeper reason it cannot be recovered without type-passing).

---

## 3. Why "drop and re-infer" is sound: the existential-recovery argument

The pattern behind C3–C5 is: **dropping an annotation is sound because the machine's
typing is declarative with existential witnesses.** Whenever the source typing pins a
type to some outer rigid variable, the erased derivation can choose its existential
witnesses (the scheme `M`, the `specs`, the gen-vars `G`, the `instArgs`) to pin the
*inferred* type to the same variable. Generalisation only ever makes a type *more*
general, and more-general types can be instantiated back to whatever the body needed.

This is the *informal* argument. Its formal face is the coherence lemma, which is the
one genuinely non-trivial piece of new metatheory:

> **Coherence lemma (to be proved).** `TypeOfHM e τ → TypeOfHM (erase e) τ`,
> where `erase` is the structural function defined in §5.

Well-posedness note: `e` is the *closed* whole program; `TypeOfHM e τ` on it **is**
provable because the annotated-let rules open their own scoped variables internally
(`GeneralisesTo`/`openBoundTyVars`) — the top-level `let h : ∀c. …` opens `c → C`
before the inner `letRec`'s `WF` check runs. So the source judgement is not vacuous,
and the coherence statement is exactly "erasing preserves the same monotype τ".

**This lemma is the single highest-risk claim in this document.** If it fails, C3–C5
fail with it. It is the thing the adversarial review should attempt to falsify first.

---

## 4. Incompatibilities: what we cannot support

### I1. Scoped type variables *inside a polymorphically-recursive* `letRec` annotation

The one genuine wall. Example (where `f[t]` is shorthand for "`f` instantiated at type
`t`" — the surface has no type-application syntax and forces the instantiation by
context; the notation just makes the different instantiations visible):

```
let h : ∀c. c → (c × c) =
  λ(w : c). let rec f : ∀a. a→c = λ(x : a). f[List a] [x]   -- recursive call at List a ≠ a (poly-recursive), returns c
            in (f[List c] [w], w)
in h[int] 3
```

Here `f`'s annotation `∀a. a→c` does **two** jobs: it enables polymorphic recursion
(the recursive call instantiates `a` at `List a`, i.e. a *different* type than the
binding's own `a`), *and* it pins the return type to the outer `c`. Both are
load-bearing.

There are exactly three things one might do with this annotation in a closed machine
term, and all three fail:

1. **Keep it** — `c` is a dangling `bvar` (index ≥ `paramCount`), so
   `ContainsBvarsUpTo paramCount body` fails, `PolyTy.WF` fails, `RecSpecs.WF`
   fails, and `ValTyped.recclo` cannot be constructed.
2. **Drop it** — the members become monomorphic-recursion; the recursive uses at
   different types are rejected. Polymorphic recursion is gone.
3. **Open `c` to a fresh `fvar X`** — `WF` now holds, but at force time the
   continuation demands the *specific* instantiation (e.g. `int`), while the body
   types at `X`-involving types; `X ≠ int`, and the `GeneralisesTo` cofinite check
   (`∀ fresh Y, … Y→Y`) also fails because `X` is fixed while `Y` is fresh.

The *source* typechecker has a fourth move the machine does not: it opens `c → C`
*before* checking, so `∀a. a→C` is `WF` and everything lines up. The machine types
closed and has no opening. The only way to reconcile "load-bearing annotation" with
"outer rigid variable" is to **substitute** the instantiation into the term — i.e.
type-passing.

**Corollary.** `scoped tyvars everywhere` + `polymorphic recursion inside` +
`no type-passing` are jointly impossible. Any two of the three are fine. (This is also
why Haskell, which erases types only at the runtime boundary, keeps a type-passing
System-F core: outer rigid variables in binding signatures need substitution.)

### I2. (Non-claim, for completeness) Un-annotated polymorphic recursion

Inferring polymorphic recursion is undecidable (Mycroft/Henglein); it has always
required an annotation. Nothing about the CEK migration changes this; it is a language
fact, not a machine limitation.

---

## 5. The erasure, precisely

`erase : Expr → Expr` — a **uniform, structural annotation drop**. Every annotation is
dropped; there is no keep/drop branching:

- `lambda (some t) body → lambda none body`;
- `letIn (some σ) rhs body → letIn none (erase rhs) (erase body)` (annotation dropped
  unconditionally — for a non-recursive let this is always sound, §2 C4);
- `letRec anns bindings body → letRec (anns.map (fun _ => none)) (bindings.map erase) (erase body)`
  (all member annotations dropped — every member becomes monomorphically recursive,
  §2 C2/C5);
- `var i [] → var i []` (source `var` tyArgs are always `[]`; the `tyArgs → []` clause
  is trivial and disappears with the field in Stage 4);
- everything else is structural.

Notes:

- This is a genuine *drop*, not "open bvars to fvars" — call it **annotation dropping**.
- Because `letRec` annotations are dropped, **polymorphic recursion inside blocks is
  not supported**; every member is monomorphically recursive and generalised for the
  body.
- The coherence lemma (§3) is the proof that dropping is typing-preserving. The
  uniform drop gives one case per constructor, no branching.
- Programs with no scoped type variables satisfy `erase e = e` (modulo the trivial
  `lambda some → none` cases that never occur), so they need no erase step at all.

---

## 6. Surface changes needed (not yet done)

The current surface lowering (`SurfaceBridge.lowerPoly`, ~3504) scopes a scheme body to
exactly its own `foralls`, so outer scoped references are *rejected at lowering*, not
allowed-and-later-erased. To support C4/C5 the surface must:

1. **Lift the `lowerPoly` restriction** — allow scheme annotations to reference
   enclosing scope's type variables (thread the ambient tyvar scope into `lowerPoly`
   the way `bindingLowerTyScope`/`letAnnTyPrefix` already do for lambda ascriptions).
   This matches the Core, which *already* supports scoped refs in scheme bodies
   (`openTyVarsAux` descends scheme bodies at `d + paramCount`, docstring: "a scheme
   may reference an enclosing scope's type variable").
2. **Add `erase`** (§5) between lowering and the machine.
3. **Prove the coherence lemma** (§3).

---

## 7. Open questions for the reviewer (attack these first)

1. **The coherence lemma (§3).** Is `TypeOfHM e τ → TypeOfHM (erase e) τ` actually
   provable, in particular the `letIn`-annotation and mono-`letRec`-annotation cases
   where the existential recovery must reproduce the exact monotype τ? (C3–C5 stand or
   fall with it.)
2. **`IsErased` / `ErasedState` under uniform erase.** The erased term has no
   annotations at all (lambda `none`, `letIn`/`letRec` `none`, `var []`), so the
   existing `IsErased` predicate's `WF`-on-kept-annotations premises become vacuous.
   Confirm the predicate should be simplified accordingly (or that keeping the `WF`
   premises is harmless).
3. **`GeneralisesTo` for unannotated lets.** Under uniform erase, every annotated let
   becomes unannotated, so `GeneralisesTo … none e M L` types the *closed* `e`. Confirm
   no dangling `bvar` survives the erasure in any position (lambda, `letIn`, `letRec`,
   `var tyArgs`), and that the erased term is closed-typable at `M`'s opening.

---

## 8. Summary: what we get, what we give up

Three independent axes, stated plainly:

- **Scoped type variables — everywhere.** `lambda` ascriptions, `letIn` annotations,
  and `letRec` annotations all work: the uniform erase (§5) drops them and inference
  re-derives the types. *(Contingent on the coherence lemma, §3 — the one unproven
  piece.)*
- **Polymorphic recursion — outside blocks only.** `letRec` members are generalised
  for the body (fully polymorphic *outside*), but monomorphic *inside* the group (each
  recursive use at one type). Polymorphic recursion *inside* blocks is **not
  supported**: it needs the `letRec` annotations that the uniform erase removes.
- **No type-passing, no elaboration, no O(n²).** The erasing CEK machine gives all
  three (§2 C1). Generalisation lives in the environment, so there is no term-level Λ,
  no `TypeOfElabHM`, no `sourceSound`.

The one load-bearing incompatibility, as a single sentence (§4 I1): **you cannot have
"scoped tyvars inside a polymorphically-recursive `letRec` annotation" together with
"no type-passing"** — that combination needs the outer rigid variable to be substituted
at force time, which *is* type-passing.
