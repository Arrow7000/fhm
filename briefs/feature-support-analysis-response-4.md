# Feature-support analysis — revision 3 (post second review)

**Status: revision 3.** Supersedes `feature-support-analysis-response-2.md` (v2) and
incorporates `feature-support-analysis-response-3.md`. The second review found that
v2's *restricted* coherence lemma was still false, for a sharper reason than v1's, and
that v2 was internally inconsistent (two non-equivalent formulations of the cut; a
floor-vs-ceiling contradiction; a "`TypeOfHM` on the annotated source" that the rule
cannot deliver). This revision makes the architectural choice explicit instead of
papering over it.

## Revision notes (what changed from v2)

1. **The restricted coherence lemma was still false.** v2's side condition ("every
   in-group use at one monotype") is a *use-site* condition. The counterexample
   `let rec f : ∀a. a→a = λx. x and g = f 3 in (g, f True)` has exactly **one**
   in-group use of `f` (`f 3`, at one monotype), yet after erase it is untypeable:
   under `.mono`, that single ground use pins `f`'s monotype to `int→int`, so the
   body's `f True` fails. The use-site condition does not capture what DM monomorphic
   recursion actually does. The cut is therefore stated as the **rule** (DM
   monomorphic recursion), not the use-site condition.
2. **The architecture is now explicit: two typing relations, not one with a side
   condition.** `TypeOfHM` is the **machine** relation, applied only to *erased* terms
   (annotations absent, `letRec` mono-only). `Infer` is the **source** relation
   (annotations present, ceiling-checked, DM monomorphic recursion). There is no
   "`TypeOfHM` of the annotated source" — impossible anyway, because
   `RecSpecs.WF.anns_eq` (`specs.map RecSpec.ann = anns`) forces `.poly` specs whenever
   annotations are present. The coherence lemma **is** Infer's soundness theorem:
   `Infer e τ → TypeOfHM (erase e) τ`.
3. **Floor vs ceiling resolved: ceiling.** Annotations *restrict* (standard ML/Haskell
   signature semantics), consistent with `letIn`. v2's "floor" (`f : int→int` on a
   `∀a. a→a` RHS leaves `f` at `∀a. a→a`) was wrong: it conflated the *machine*'s
   re-inference (which is more general) with the *source* typing (which the annotation
   restricts). Under ceiling, the extra generality is never user-visible, because Infer
   rejects uses outside the annotation before erase.
4. **Bounds must open (or run on an opened term).** Bounds walks the term *as stored*,
   with dangling `bvar`s; Infer/`TypeOfHM` get those opened by the enclosing
   `GeneralisesTo`/`letInAnn`, but Bounds does not. "Bounds on the source" is necessary
   and not sufficient.

---

## 0. History and motivation (unchanged from v2)

The project went **erasure → type-passing → erasing CEK**. The frame that matters:

**What matters vs. what doesn't.** The actual goals are two *language features*:
**(1) scoped type variables**, usable everywhere, and **(2) polymorphic recursion**
(recursive bindings usable at different types). Whether the operational semantics is
type-erasing or type-passing is **incidental**. The O(n²) elaboration blowup and the
second typing relation (`TypeOfElabHM`) are **costs** to be removed, not features.

- **Erasure era** (`e374bc9`): substitution `Step`, an `IsTyErased` premise.
- **Type-passing migration** (`e7639f7`/`e4c5129`): done to support scoped tyvars +
  polymorphic-recursive bindings, which erasure could not — poly recursion needs
  load-bearing annotations (erasure → monomorphic fallback = loss of power), and scoped
  tyvars leave orphan `bvar`s only resolvable by instantiating across let-reduction
  (i.e. type-passing). This forced `TypeOfElabHM`, `Infer.sourceSound`, and the O(n²)
  Λ-nest.
- **CEK migration** (current, `0c0aa32`): the *sole* motivation was the belief that an
  environment semantics would avoid the n² and eliminate/streamline elaboration. Stage 1
  is proved.

---

## 1. The architecture: two typing relations

This is the load-bearing structural decision, made explicit in this revision.

- **`Infer` — the source relation.** Runs on the **annotated source** term. Enforces
  (i) Damas–Milner **monomorphic recursion** for `letRec` (§2), and (ii) **ceiling**
  annotation checks (§3). Produces `(Φ', S, τ)`. This is the user-facing typechecker.
- **`TypeOfHM` — the machine relation.** Runs only on **erased** terms (no annotations;
  `letRec` is mono-only — the `PolyTyped` premise is vacuous because there are no
  `.poly` specs). This is what `CekMachine`'s `ValTyped`/`StateOK` cite.
- **`erase` — the bridge.** A structural annotation drop (§4).
- **Coherence = `Infer.sound`.** There is **no separate** "`TypeOfHM e τ → TypeOfHM
  (erase e) τ`" lemma. The one theorem needed is the (revised) soundness of inference:

  > **`Infer e τ → TypeOfHM (erase e) τ`** (threading the substitution `S` through the
  > context and the type, i.e. `TypeOfHM (S.onCtx ctx) (erase e) (S.onTy τ)`).

  This *is* Stage 2's "`Infer.sound` against `TypeOfHM` directly", plus the erase step.
  It is not a new kind of metatheory, and it has no side condition on derivations: the
  side condition that v1/v2 tried to state is **baked into the rules** — `Infer`
  enforces mono recursion and ceilings, and `TypeOfHM` only sees erased mono-only terms.

**Why this resolves v2's failures.** v2 tried to keep a fused `TypeOfHM` on the
annotated source and add a use-site side condition; that lemma is false (the `g = f 3`
counterexample). With the split above, there is nothing to be false: `TypeOfHM` is never
applied to annotated terms, so the `anns_eq`-forces-`.poly` problem disappears, and the
"drop and re-infer is sound" reasoning lives inside the ordinary `Infer.sound` proof,
where each dropped annotation is handled by the corresponding rule (λ ascription →
`ann = none` inference; `letIn` ann → existential `M`; `letRec` ann → DM mono).

---

## 2. The language cut: Damas–Milner monomorphic recursion

**Cut.** Inside a `letRec` group, every member is bound at a **fresh monotype**; every
in-group use (self **and** sibling) looks up that monotype and unifies against it; the
monotypes are **generalised for the body**. Equivalently: the `PolyTyped` half of the
fused rule is removed; `letRec` is pure Damas–Milner.

**Why it exists.** It is what makes `Infer.sound → TypeOfHM (erase e) τ` provable:
after erase the `letRec` is annotation-free, so `TypeOfHM` types it mono-only, and the
only question is whether the source's in-group typing was mono — which the cut makes
true by construction.

**Enforcement is automatic.** There is no separate "check for poly use" and no
decidability question: bind the monotypes, unify, and any poly use fails unification.
This is the ordinary DM `let rec` algorithm.

**A consequence that must be stated plainly (the reviewer's point).** Because in-group
uses pin the monotype, an in-group use at a **ground** type reduces the member's
*outside* polymorphism. Concretely, DM **rejects**:

```
let rec f : ∀a. a → a = λx. x
    and g             = f 3
in (g, f True)
```

`f 3` pins `f`'s monotype to `int→int`, so the body's `f True` fails. This program is
accepted by the *current* fused `TypeOfHM` (and by OCaml with an explicit polymorphic
signature); it becomes illegal under the cut. This is a **real expressivity cut**, wider
than "no in-group poly use", and it is the price of uniform erase. (The common case is
unaffected: a recursive use at a *type variable* — `length xs` — does not pin anything,
and the member stays fully polymorphic outside.)

**What it removes, summarised:** self-poly-recursion, sibling-poly-use, *and* the
ground-pinning case above — i.e. all polymorphic behaviour *inside* the group, plus any
in-group use at a concrete type that would pin the member monomorphic outside.
Generalisation for the body (§C2) is untouched.

---

## 3. Annotation semantics: ceiling (annotations restrict)

An annotation is a **ceiling**, exactly as in ML/Haskell and exactly as `letIn`
already behaves: the RHS must type at (an instance of) the annotation, and the binding
is visible at the annotation in the body — no more.

- `let rec f : int→int = λx. x in f True` is **rejected**: `f : int→int`, `f True` fails.
- `let f : int→int = λx. x in f True` is **rejected** for the same reason. `letIn` and
  `letRec` are consistent.
- Scoped-tyvar annotations (`∀a. a→c` with outer `c`) are checked the same way, **after
  the enclosing scope's opening** — i.e. against the opened scheme `∀a. a→C`, not the
  stored `{1, a→bvar1}`. `Infer.letInAnn` already opens first; the `letRec` check must
  do the same.

This reverses v2's "floor" claim. The "drop and re-infer makes things more general"
observation is true *of the machine's* `TypeOfHM` (which sees no annotations), but it is
not user-visible: Infer rejects uses outside the ceiling before erase, so the erased
term's extra generality is only ever exercised at the uses Infer already accepted.
Coherence (`Infer e τ → TypeOfHM (erase e) τ`) is exactly the statement that this works.

---

## 4. The erasure

`erase : Expr → Expr` — a **uniform, structural annotation drop**:

- `lambda (some t) body → lambda none body`;
- `letIn (some σ) rhs body → letIn none (erase rhs) (erase body)`;
- `letRec anns bindings body → letRec (anns.map (fun _ => none)) (bindings.map erase) (erase body)`;
- `var i _ → var i []` (**zero** the tyArgs — this makes `erase ∘ openTyVars = erase`,
  which the `letIn` case of `Infer.sound` relies on);
- everything else structural.

Notes: `erase e ≠ e` in general (`λ(x : int)` is not a scoped tyvar but is still
dropped). Uniformly erased terms already satisfy the machine's current `IsErased`
predicate (`lambda none`, `var []`, and the `∀ σ, some σ ∈ anns → σ.WF` premise is
vacuous for `anns = [none,…]`), so `openTyVars_eq_self_of_erased` and
`GeneralisesTo_inst_ann` still apply — re-cutting `IsErased` is hygiene, not a new
preservation proof.

---

## 5. The pipeline

1. `lower` (Surface → Core), source term, annotations present — requires lifting
   `lowerPoly`'s self-containment restriction (thread the ambient tyvar scope into
   `lowerPoly`).
2. **Infer** on the source — DM mono recursion + ceiling checks (§2, §3).
3. **Bounds** on the source — **and Bounds must open** (or run on an opened copy): it
   walks stored dangling `bvar`s that Infer/`TypeOfHM` only ever see after
   `openTyVars`. This is new work, not a free consequence of "annotations present".
4. **`erase`** (§4) → machine term.
5. **`TypeOfHM`** / `CekMachine` on the erased term.

`Bounds.Pipeline.eraseProgram` is BL-erase on Surface — a different function; do not
conflate it with this annotation drop.

---

## 6. Claims

### C1. CEK eliminates type-passing, elaboration, and the O(n²) Λ-nest — **TRUE**

The nest is a type-passing artifact (`letRecElabNest`, both `.mono` and `.poly` arms,
wraps each member as `letIn (some scheme)` around a full copy of the group → Θ(n²)).
The CEK machine manufactures no term-level Λ; generalisation lives in
`ValTyped.recclo`'s `bodyScheme`. `TypeOfElabHM`/`sourceSound` deletion is Stages 2–3
(still present in the tree). Independent of scoped tyvars and of the mono/poly split.

### C2. Monomorphic recursion (poly outside via generalisation) — **TRUE as the post-cut rule**

`MonoTyped` types RHSs at opened monotypes; `bodyScheme (.mono τ) = genGroup G τ`.
Under the cut, `Infer` produces only `.mono` specs, so the machine's `PolyTyped` premise
is vacuous. "Mono inside" is a *source* constraint; the runtime `forceRecclo` still
types RHSs in the body context (`recclo_body_typed`).

### C3. Scoped tyvars in lambda ascriptions — **TRUE**

Dropped; `ann.Pins` vacuous; the unannotated λ infers `paramTy` from the derivation.
(Requires the uniform drop — nested λ ascriptions must go too.)

### C4. Scoped tyvars in `letIn` annotations — **TRUE** (ceiling)

`Infer` checks the annotation (ceiling) and computes the scheme `M`; the erased
`letIn` types at the same `M` via the existential `M` in `TypeOfHM.letIn`. Proof reuses
the same `M` (not a more general one); `erase (rhs.openTyVars Xs) = erase rhs` under §4.
Do **not** read C4 as "floor": the source typing restricts.

### C5. Scoped tyvars in `letRec` annotations, under the cut — **TRUE** (ceiling, DM)

`Infer` does DM mono recursion (§2) and checks the (opened) annotation as a ceiling
(§3). After erase, `TypeOfHM` types the annotation-free group at the generalised
monotypes. The worked example still checks:

```
let h : ∀c. c → (c × c) =
  λ(w : c). let rec f : ∀a. a→c = λ(x : a). w
                and g : ∀b. b→c = λ(y : b). w
            in (f[w] w, g[w] w)
in h[int] 3
```

(no in-group uses, so `w : C` pins each member's monotype to `α→C`, `G = [α]` keeps `C`
rigid, and the body types at `(C, C)`).

### C6. Polymorphic recursion *inside* blocks — removed by the cut, not by I1

The cut (§2) rejects all in-group polymorphic use, including self-poly-recursion.
Self-contained poly-rec annotations are *already* supported by Stage 1 (kept, `WF`);
the uniform erase drops them as a deliberate policy. I1 (§7) is the separate, deeper
reason that *dangling* (outer-scoped-tyvar) poly-rec annotations cannot be kept even
under selective keeping.

---

## 7. Incompatibilities

### I1. Scoped tyvars inside a polymorphically-recursive `letRec` annotation

The genuine machine wall, independent of the cut. For

```
let h : ∀c. c → (c × c) =
  λ(w : c). let rec f : ∀a. a→c = λ(x : a). f[List a] [x]
            in (f[List c] [w], w)
in h[int] 3
```

(`f[t]` = instantiation shorthand; the surface forces it by context) — in a closed
machine term, keeping the annotation fails `PolyTy.WF` (dangling `bvar 1`), dropping it
loses the poly-recursive call, and pre-opening `c ↦ fvar X` fails the force case
(`X` fixed vs `Y` fresh, and `X ≠ int`). The source typechecker opens `c → C` before
checking. Only substitution (type-passing) reconciles them.

**Corollary.** `scoped tyvars inside a poly-rec letRec annotation` + `no type-passing`
is impossible even with selective keeping. Self-contained poly-rec annotations are *not*
subject to I1; the cut (§2) is what removes them.

### I2. Un-annotated polymorphic recursion — undecidable (non-claim)

Mycroft/Henglein; unchanged by the migration.

---

## 8. Open questions for the reviewer

1. **`Infer.sound : Infer e τ → TypeOfHM (erase e) τ`.** Is the DM-mono + ceiling
   inference sound against the erased-term `TypeOfHM`, in particular the `letIn`-ann and
   mono-`letRec`-ann cases (reuse the inferred `M` / `genGroup`), and the scoped-tyvar
   cases where the check runs on the *opened* scheme? This is the whole game now.
2. **Ground-pinning semantics.** The cut rejects `g = f 3 in (g, f True)`. Confirm this
   is the intended DM behaviour and that Infer's mono-recursion algorithm implements it
   (i.e. that no soundness hole or over-rejection lurks in the `RecSpec.init → .mono`
   change and the removal of `InferRecGroup.consPoly`).
3. **Bounds opening.** Bounds walks stored dangling `bvar`s. Specify precisely how it
   opens in lockstep with Infer (or runs on an opened copy), for λ ascriptions and for
   inner `letIn`/`letRec` scheme bodies.
4. **`IsErased` recut.** Uniformly erased terms already inhabit the current `IsErased`;
   confirm no *new* preservation proof is needed and that the machine never constructs
   `ValTyped.recclo` with `.poly` specs for source-annotated groups (they are erased
   first).
5. **`erase ∘ openTyVars = erase`** under the §4 definition (in particular the
   `var i _ → var i []` zeroing).

---

## 9. Summary

Three independent axes:

- **Scoped type variables — everywhere** (λ ascriptions, `letIn` and `letRec`
  annotations), by uniform drop + the `Infer.sound` coherence theorem. *(Contingent on
  that theorem — the one unproven piece.)*
- **Polymorphic recursion — outside blocks only.** Inside, it is monomorphic recursion
  (the DM cut, §2), with the ground-pinning consequence stated explicitly. This is a
  language cut enforced in `Infer`, not a machine limitation.
- **No type-passing, no elaboration, no O(n²)** — from the erasing CEK machine.

Two incompatibilities, different in kind:

- **The cut** (§2): polymorphic use inside a block is not supported, by design — this is
  what makes uniform erase sound.
- **I1** (§7): even allowing selective keeping, `scoped tyvars inside a poly-rec letRec
  annotation` + `no type-passing` is impossible — that combination needs type-passing.
