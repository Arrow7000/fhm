The coherence lemma as stated is **false**. That is the load-bearing failure; C3–C5 stand only after it is restricted, and C5’s “annotations are restriction-only” argument is already wrong on mixed groups.

---

## Headline: unrestricted coherence is false

**Claim (§3):** `TypeOfHM e τ → TypeOfHM (erase e) τ` for the uniform drop in §5.

**Verdict: FALSE.**

The slogan “dropping makes types more general, and more-general schemes instantiate back to τ” is the right story for `lambda` and `letIn`. It is the **wrong** story for `letRec`. Erase does not keep the same `specs`. `RecSpecs.WF.anns_eq` (`Core.lean` 3081) ties stored annotations to the spec:

```2948:2958:FHM/Core.lean
def RecSpec.ann : RecSpec → Option PolyTy
  | .mono _ => none
  | .poly σ => some σ
...
def RecSpec.rhsEntry (G Xs : List Nat) : RecSpec → PolyTy
  | .mono τ => PolyTy.mkTrivial (Ty.renameG G Xs τ)
  | .poly σ => σ          -- FULL scheme inside the group
```

After `anns.map (fun _ => none)`, every spec is `.mono`. The RHS environment **changes regime** (full schemes → shared monotypes). That is not generalisation, and `TypeOfHM.var` cannot instantiate a monotype to two different types (`InstantiatesBy` on an LC type is the identity).

### Counterexample 1 — I1 itself (the lemma has no C6 side condition)

The I1 program is a closed `TypeOfHM` term. Outer `GeneralisesTo` *does* open inner scheme bodies (`openTyVarsAux` / `RecGroup.openAnns` at `Core.lean` 2313–2357): `∀a. a→c` stored as `{paramCount := 1, body := arrow (bvar 0) (bvar 1)}` becomes `∀a. a→C`, which is `WF`. `TypeOfHM.var` ignores `tyArgs`; the recursive call is ordinary application `f (Cons x Nil)`. `PolyTyped` puts `f` at the full scheme in `rhsCtx`, so one use at `List Y` is fine.

After erase, `anns_eq` forbids `.poly`. `MonoTyped` must type `λx. f (Cons x Nil)` at a **single** opened monotype `τ`. Then `τ` has to be both `α → C` (the λ) and `List α → C` (the rec call). Impossible.

Failing premise: `RecSpecs.MonoTyped` (`Core.lean` 3093–3097). You cannot rescue with `.poly` because of `anns_eq`.

The doc admits I1 is unsupported, then states a lemma with **no** such restriction. As written, the lemma is false.

### Counterexample 2 — mixed group, no self-poly-recursion, no scoped tyvars

C5’s “under monomorphic recursion the annotation is check/restriction-only (not what *enables* polymorphism)” is **false** for mixed groups. `rhsEntry (.poly σ) = σ` is exactly what enables **sibling** polymorphism.

```
let rec f : ∀a. a → a = λx. x
    and g             = (f 3, f True)
in g
```

**Before erase.** `specs = [.poly ⟨1, a→a⟩, .mono (int × bool)]`, `G = []`.

- `f`’s RHS: `PolyTyped`, `λx. x` at `Y→Y`. Does not use `f` or `g`.
- `g`’s RHS: `MonoTyped`, but `rhsCtx` gives `f` the **full** scheme, so `f 3` and `f True` are two `TypeOfHM.var` instantiations. Result `int × bool`.

**After erase.** Both specs are `.mono`.

- If `τf = α→α`, `G = [α]`: in each opening `Y`, `f : Y→Y`, so `f 3` and `f True` force `Y = int` and `Y = bool`.
- If `τf = int→int`, `G = []`: `f True` fails.

Failing premise: `RecSpecs.MonoTyped` on `g`.

`f` is not poly-recursive. There is no outer tyvar. The annotation is load-bearing for in-group *uses*, not a restriction on `f`’s own type. Uniform drop is unsound on a fragment C6 does not describe.

Current `Infer.letRec` **accepts** this program (`RecSpec.init` maps `some σ` to `.poly σ`, `InferW.lean` 1596–1603). If Infer runs on source and the machine runs on `erase e`, you will infer a type for a term the machine cannot type. That is not a footnote; it is a safety gap in the proposed pipeline.

A coherence lemma that could actually be true:

> If `TypeOfHM e τ` and **every in-group use of every member (self or sibling) is at one monotype**, then `TypeOfHM (erase e) τ`.

That is strictly stronger than “no polymorphic recursion.” It is a condition on the derivation, not on whether annotations are present.

---

## Claim-by-claim

### C3 — scoped tyvars in λ ascriptions, by dropping — **TRUE**

`TypeOfHM.lambda` (`Core.lean` 3347–3352) uses the ascription only via `ann.Pins paramTy` plus `paramTy.IsLC`. After `none`, Pins is vacuous; reuse the same `paramTy` (already LC at the point the lambda rule fired, i.e. after the enclosing `openTyVars`).

Standalone closed `λ(x : bvar 0). x` is not a `TypeOfHM` theorem (`IsLC` fails), so coherence is vacuous there. Under an enclosing annotated let, outer opening makes the ascription an fvar, then erase drops it, then the unannotated λ infers that fvar from the cofinite opening / the continuation. Matches the force-case story (`GeneralisesTo_inst_ann`, `CekMachine.lean` 787–815, used at preservation `force` 2877–2890).

### C4 — scoped tyvars in `letIn` anns, by dropping — **TRUE** (tighten the argument)

The informal “infer the most general scheme” is slightly the wrong proof. You do **not** need a more general `M`. Reuse the **same** `M`:

- Annotated: `∀ Xs, TypeOf ctx (rhs.openTyVars Xs) (M.openVars Xs)`.
- Unannotated: `∀ Xs, TypeOf ctx (erase rhs) (M.openVars Xs)`.

Uniform erase only deletes the positions `openTyVarsAux` rewrites (λ ascriptions, nested scheme bodies, `var` tyArgs). So `erase (openTyVars Xs rhs) = erase rhs`. IH on the opened derivation gives the unannotated cofinite premise. Body keeps the same `M` in the env.

Attack “less-general annotation, drop makes it more general, uses fail”: you need not take a more general `M`; `TypeOfHM.var` is existential anyway.

Caveat the doc omits: C4 is not standalone. If you dropped only the `letIn` annotation and kept `λ(x : bvar 0)`, `GeneralisesTo none` types the **unopened** λ and `paramTy.IsLC` fails. Uniform drop of λ ascriptions is required.

There is no value restriction (`letIn` is CBN). `AllMatchesExhaustive` ignores anns.

### C5 — scoped tyvars in `letRec` anns under mono rec — **example TRUE; argument FALSE; general claim NOT-ESTABLISHED**

**The worked example does type after erase**, at `(int × int)`, with the witnesses the doc sketches.

Erased inner group in the opening `w : X`:

| Witness | Value |
|---|---|
| `specs` | `[.mono (α → X), .mono (α → X)]` |
| `G` | `[α]` with `α ≠ X` |
| `anns_eq` | both `none` |
| `MonoTyped` | `renameG [α] [Y] (α→X) = Y→X`; `λx. w` at `Y→X` (`w` is `var 3` after λ, env `[x,f,g,w]`) |
| `PolyTyped` | vacuous |
| `bodyScheme` | `genGroup [α] (α→X) = ∀α. α→X` |
| body `(f w, g w)` | `instArgs = [X]` |

Cofiniteness is exactly what forces “leave `X` out of `G`”: if `X ∈ G`, `renameG` sends the return type to a fresh name and `λx. w` no longer types. That part of C5 is right.

**What is wrong:** an annotated `letRec` member is **not** a `.mono` spec. `RecSpec.ann (.poly σ) = some σ`. C5’s source term is typed by `PolyTyped`, not `MonoTyped`. “Under monomorphic recursion the annotation is restriction-only” is true **only** when no in-group use (self or sibling) needs the scheme in `rhsCtx`. Counterexample 2 above is the refutation. Until coherence is restated with that side condition, C5 as a general feature claim is not established by this doc.

### C6 — poly rec inside not supported — **TRUE under uniform erase; FALSE that this “follows from I1 / needs type-passing”**

Under §5, `anns_eq` ⇒ all `.mono` ⇒ `PolyTyped` vacuous. No remaining path. Confirmed.

The justification is overstated. Self-contained poly rec (no outer tyvar) is **already** what Stage 1 implements:

```
let rec f : ∀a. List a → Nat = λxs.
  match xs with
    Nil        => 0
    Cons x xs' => f (pairs xs)    -- use at List (α×α) ≠ List α
```

Scheme is `WF` (`ContainsBvarsUpTo 1`). Current `IsErased.letRec` **keeps** WF binding annotations (`CekMachine.lean` 3–8, 22–24). `rhsEntry = σ`, `TypeOfHM.var` instantiates existentially. No type-passing, no dangling `bvar`.

I1 only kills *dangling* annotations on closed machine terms. Uniform erase also drops *closed* poly-rec annotations. That is a stricter policy than I1 forces, and it contradicts `cekmachine-design.md` 74–81 (“erase λ ascriptions, **keep** binding annotations”).

### C2 — mono inside, generalised outside, “exactly recclo / textbook DM” — **TRUE for the `.mono` half; FALSE as uniqueness**

For unannotated members: `MonoTyped` types RHSs at `mkTrivial (renameG G Xs τ)` (same `Xs` for the group); `bodyScheme G (.mono τ) = genGroup G τ`. That **is** Damas–Milner / Pottier `LetRec`. `G` is an existential (`WF` only asks `G.Nodup`); Infer’s `genGroupVars` excludes env/rigid names (`InferW.lean` 1524–1525), but Core does not. Putting an env-free `C` in `G` makes `MonoTyped` uninhabited — not a soundness hole, but C5 already depends on choosing `G` to leave `C` out.

The fused rule is **not** “exactly DM”:

```3242:3247:FHM/Core.lean
  /-- ... FUSION of Damas–Milner monomorphic recursion ... and annotated
      *polymorphic* recursion ... -/
```

`TypeOfHM.letRec` and `ValTyped.recclo` both take `hmono` **and** `hpoly` (`Core.lean` 3394–3400, `CekMachine.lean` 296–303). Annotated members sit at full schemes **inside** the group. OCaml “mono by default, poly with a signature” is the better analogy. After uniform erase this extra half becomes vacuous; it is not what recclo “already” is.

Runtime note: `forceRecclo` types the RHS in **`bodyCtx`** (generalised schemes), not `rhsCtx` (`recclo_body_typed`, `CekMachine.lean` 969–981, 2908–2915). “Mono inside” is a source constraint, not the runtime env.

### C1 — CEK eliminates type-passing, elaboration, and the O(n²) Λ-nest — **TRUE as architecture; two inaccuracies in the argument**

`letRecElabNest` (`InferW.lean` 2486–2498) wraps **each** member as `letIn (some scheme)` around a **full copy** of `rawBindings`. n wrappers × n bindings = Θ(n²) AST occurrences. That is independent of scoped tyvars.

**Not** `.mono`-only. The `.poly` arm at 2494–2498 copies the group the same way (declared `σ`, projection `var i (bvarRange …)`, no `closeTyVars`). Pointing at “the `.mono τ` case at ~2490” is misleading. All-`.poly` groups still nest today even though their schemes already exist.

The CEK machine does not manufacture a term-level Λ: `forceRecclo` evaluates the raw member in `bindGroup`; `var` ignores `tyArgs` (`CekMachine.lean` 229–230, 257–259). Generalisation lives in `ValTyped.recclo`’s `bodyScheme`.

“Eliminates `TypeOfElabHM` / `sourceSound`” is Stage 2–3 work (the doc says so). They still exist (`Core.lean` 3139, `InferW.lean` ~12584). Stage 1 CEK does not use them. Live Infer still emits the nest.

### I1 — three-way bind — **TRUE** (with one clarification on “source typechecker”)

`f[t]` is **not** Core syntax. Surface lowering always emits `var i []` (`SurfaceBridge.lean` 4238–4241). The RHS is `app (var f []) (Cons x Nil)`. Two instantiations are two `TypeOfHM.var` nodes, each with its own existential `instArgs`. That requires a **scheme** in the env.

**(a) Keep the annotation on a closed machine term.** Inner scheme `{1, a→c}` has `bvar 1 ≰ paramCount 1`. `PolyTy.WF` fails (`Core.lean` 2875–2876) → `RecSpecs.WF.poly_wf` fails → `TypeOfHM.letRec` / `ValTyped.recclo` / `IsErased.letRec` all fail. If the λ ascription `x : a` is also kept, `paramTy.IsLC` fails independently.

**(b) Drop it.** `anns = [none]` ⇒ `.mono τ`. Instantiation of an LC monotype is identity. `λx. f (Cons x Nil)` cannot have both `α → _` and `List α → _`. `MonoTyped` fails. The **body** use `f (Cons w Nil)` is outside the group (`bodyScheme` / `genGroup`) and would still be polymorphic; I1’s load-bearing call is the **RHS** rec call.

**(c) Pre-open `c ↦ fvar X`.** `∀a. a→X` is `WF` (`fvar` is always in-range). Outer `GeneralisesTo` opens **bvars**, not existing fvars (`Ty.openVarsFrom`, `Core.lean` 2310–2311). Need `∀ fresh Y, X → (X×X) = Y → (Y×Y)`. False. Machine `force` evaluates the thunk body closed and unopened (`CekMachine.lean` 255–256); preservation then wants `int → …` while the body is at `X`. Same bug `cekmachine-design.md` 61–64 already killed.

**Source `TypeOfHM` of the whole program:** true, via outer `GeneralisesTo` rewriting inner anns (`c = bvar 1` in the inner scheme body → `fvar C`). `Infer.letInAnn` does the same (`rhs.openTyVars Ys`, `InferW.lean` 2969–2983), then `Infer.letRec` sees `∀a. a→C` which passes `σ.WF`.

**Surface does not:** `lowerPoly` kinds the scheme body only under its own `foralls` (`SurfaceBridge.lean` 3504–3506). `c` not in `[a]` → `none`. §6 is right that C4/C5/I1-style scoped refs in scheme bodies are currently rejected at lowering, not allowed-and-later-erased.

**`TypeOfElabHM` on the unelaborated source also fails** (`AreLC paramCount []` is false). I1 is a `TypeOfHM` example, not an elaboratum. “The source typechecker handles it” is true of `TypeOfHM` / `Infer.letInAnn`, false of Surface and of `TypeOfElabHM` on the skeleton.

---

## Well-posedness (§3) — **TRUE**

`TypeOfHM ⟨[], ctors⟩ e τ` on the **closed whole program** is not vacuous. `openBoundTyVars (some σ) Xs e = e.openTyVars Xs` (`Core.lean` 2566–2568), and `openTyVarsAux` rewrites:

| Position | Depth |
|---|---|
| λ ascriptions | `d` |
| nested `letIn`/`letRec` scheme bodies | `d + paramCount` (own binders shielded) |
| nested rec bindings | `d + RecAnn.params aⱼ` |
| continuation `body` | unchanged `d` |

Two-level opening for I1/C5: outer `GeneralisesTo` rewrites `c` in inner scheme bodies; `PolyTyped` then opens each member’s own `a` in the RHS. Inner annotations do **not** remain dangling when `letRec` actually fires. Drop the outer annotated let and the inner `poly_wf` fails. The “whole program” qualifier is necessary and sufficient.

---

## Missed interactions

### Match / ADTs — orthogonal

`AllMatchesExhaustive` (`Core.lean` 2082+) ignores annotations. `match_` has no annotation field. `TypeOfMatchBranch` / `BranchCtorSpec` take existential `tyArgs` from the scrutinee. Dropping HM anns does not change coverage or constructor typing.

### Bounds — **not orthogonal to this erase**

`cekmachine-design.md` D6 says bounds walk the **source** because “annotations are already present.” `Bounds.Synth` **reads** those anns off Core:

```662:680:FHM/Bounds/Synth.lean
  | .lambda paramAnn body => do
      let τp ← match paramAnn with
        | some t => pure t
        | none => throw "bounds: lambda param needs a type ascription for synth"
  ...
  | .letIn ann? rhs body =>
      ... some σ => checkBoundsΦ ... rhs σ.body
  | .letRec anns bindings body =>
      ... inferLetRecGroupCore ... (anns.map letRecProvisional ++ bctx)
```

If §5 erase runs before bounds: λ synth **throws**; letRec ascriptions collapse to `.fvar 0` (`letRecProvisional`, `Synth.lean` 430–433). Bounds stays orthogonal **only** if the order is `lower → Infer/bounds on source → CEK erase → machine`. §6 says “add `erase` between lowering and the machine” and never mentions Infer or bounds. That is two terms (source vs machine), a reversal of D4 (“`Expr` keeps its `ann` slots … needed by `TypeOfHM`”). It must be written down.

`Bounds.Pipeline.eraseProgram` is BL-erase on Surface, a different function. Do not conflate it with CEK annotation-drop.

### `var tyArgs` — source is always `[]`; the §5 clause is underspecified

Surface `lowerExpr` / `LowersExpr.var` always emit `.var i []`. Non-empty `tyArgs` exist only on elaborata (`Infer.var` fills `freshVars`; poly `letRecElabNest` uses `Ty.bvarRange`). `TypeOfHM.var` ignores the field; `IsErased.var` requires `[]`.

§5 specifies only `var i [] → var i []`. If erase is ever applied to an elaboratum, it must be `var i _ → var i []`, otherwise `erase ∘ openTyVars ≠ erase` and the C4 proof sketch dies.

### `erase e = e` for programs with no scoped tyvars — **FALSE**

§5: “modulo the trivial `lambda some → none` cases that never occur.” They do occur. `wrapCoreParams` / `lowerAnn` keep LC ascriptions (`λ(x : int). …`, `SurfaceBridge.lean` 3573–3585). Those are not scoped tyvars. `erase e ≠ e`.

### Current `IsErased` ≠ §5 `erase`

Stage 1 `IsErased` drops λ ascriptions and `var` tyArgs and **keeps** `letIn`/`letRec` anns with a `WF` premise (`CekMachine.lean` 1–24). `openTyVars_eq_self_of_erased` and `GeneralisesTo_inst_ann` are proved against **that** predicate. Uniform drop is a different erase than the one `force` currently assumes. §7 Q2 is right that the `WF` premises become vacuous under uniform drop; it understates that this is a change of invariant, not a simplification of the existing one.

---

## Things the doc got right

- Well-posedness of `TypeOfHM` on a closed annotated program: outer `GeneralisesTo` really does rewrite inner scheme bodies.
- C5’s **term**, after erase, typechecks at `(int, int)` with `G = [α]`, `C` kept rigid; cofiniteness is what enforces that.
- C3/C4: for `lambda` and non-recursive `let`, reuse the original `paramTy`/`M`; `erase ∘ openTyVars = erase` under uniform drop.
- I1’s three closed-machine branches all fail, for the reasons given; the 2-of-3 slogan for *scoped tyvars inside a poly-rec annotation* + *no type-passing* is right.
- The Λ-nest is a type-passing artifact, is Θ(n²), exists even for all-`.mono` groups, and the CEK environment makes that Λ unnecessary.
- Surface `lowerPoly` currently rejects outer scoped refs in scheme bodies; lifting that is required for C4/C5 as surface features.
- Source `var` tyArgs are always `[]`.
- Match exhaustiveness does not care about HM annotations.
- Inferring polymorphic recursion remains undecidable (I2).

---

## Things that must change before this is safe to implement

1. **Restate coherence.** Unrestricted `TypeOfHM e τ → TypeOfHM (erase e) τ` is false. Either:
   - restrict to “no in-group polymorphic uses (self **or** sibling)”, and **reject** those programs in Infer before erase (today Infer accepts mixed-group sibling poly use), or
   - change the spec to “`TypeOfHM` of the *erased* term is the meaning; source annotations are extra restriction checks,” and stop claiming preservation of current `TypeOfHM.letRec` derivations.

2. **Stop saying letRec annotations are restriction-only.** They switch `rhsEntry` from a monotype to a scheme. That is load-bearing for any in-group use that needs instantiation, including unannotated siblings.

3. **Separate I1 from uniform erase.** I1 forbids dangling poly-rec annotations on closed terms. It does **not** force dropping WF poly-rec annotations. Current Stage 1 already supports closed poly rec by keeping them. If uniform drop is still wanted, justify it as a language cut (proof simplicity), not as a corollary of I1.

4. **Write the two-term pipeline.** Source (anns present) → Infer + bounds → `erase` → machine. Bounds.Synth throws on `lambda none`. If erase is “between lowering and the machine” with Infer on the erased term, you also lose poly rec *and* bounds ascriptions.

5. **Fix C1/C2 wording.** Nest is both `.mono` and `.poly`. `recclo` is the fused Pottier rule, not “exactly DM.” “Eliminates `TypeOfElabHM`” is not true of the tree today.

6. **Specify `erase` on `var` as zeroing tyArgs**, and drop the “λ ascriptions never occur without scoped tyvars” note.

7. **If the goal is scoped tyvars *and* closed poly rec**, the erase is selective: drop annotations that fail `WF` (dangling outer bvars), keep WF `letRec` anns. Uniform drop is the option that kills C6’s entire feature, not only I1.
