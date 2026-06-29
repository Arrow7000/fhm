<!-- Handoff: make Algorithm-W (InferW) the elaborator for the type-passing Core.
     Successor to next-agent-brief-letrec-typepassing.md. Written 2026-06-25, after
     the type-passing migration + full own-variable polymorphic recursion landed
     (commit `e4c5129`) and passed an independent adversarial review. -->

# Brief: `InferW` — Algorithm-W elaboration for the type-passing Core

## State of play (READ FIRST)

The big campaign is **done and independently reviewed**: `FHM/Core.lean` is now a
**type-passing** declarative core with **literal type safety** (`TypeOfHM.progress`
/ `preservation` / `type_safety` / `type_safety_star`, no `IsTyErased`/erasure
premise), axiom-clean (`propext`/`Classical.choice`/`Quot.sound` only). The whole
type-erasure dynamics layer is gone from the built development. `letRecAnn` supports
**full polymorphic recursion — self and mutual, at the binding's own type variable**
(e.g. `deep` at `List a`), with no language restriction. Committed at `e4c5129`;
`lake build` green; an adversarial reviewer found no soundness hole, no vacuity, no
over-restriction. (Mechanism: `Expr.var` carries `tyArgs`; reduction does type-beta
via `substN`/`instTy`; `let` is call-by-name; `letRecAnn` opens its bindings
scheme-relative and `instTyAux`/`openTyVarsAux` shield each binding by its own
scheme's depth `d + σⱼ.paramCount`.)

**What is NOT done — this campaign:** there is **no verified Algorithm-W inference /
elaboration for the type-passing core.** `FHM/InferW.lean`, `FHM/Examples.lean`, and
`FHM/SpikeLetRecAnn.lean` are **excluded from the build** (`lakefile.toml`): they
predate the migration — they use the old `Expr.var` (no `tyArgs`), the old typing
rules, don't handle the `letRecAnn` constructor, and still reference the deleted
erasure layer.

## Goal

Make Algorithm-W the **elaborator** for the type-passing core, and re-enable the
downstream modules:

1. **Conform to the new Core API** (the same surface `Pretty`/`SpikeC` were updated
   to): `Expr.var (i) (tyArgs : List Ty)`; the strengthened `var` rule
   (`∀ tyArg ∈ tyArgs, ContainsBvarsUpTo 0 tyArg` **and** `tyArgs.length =
   polyTy.paramCount` and `InstantiatesBy tyArgs polyTy.body ty`); the
   **scheme-relative `letRecAnn`** rule. (CBN `let` is a *dynamics* change — it does
   not affect inference, which is static.)
2. **Emit `tyArgs` (the elaboration).** `Infer`/`inferCore` already compute the
   instantiation at each `var`/`ctor` use (open the scheme at `freshVars Φ
   paramCount`, unify). Type-passing means **keeping** it: apply the final
   substitution `S` and record the concrete `tyArgs` in the output term's
   `var`/`ctor` nodes. `tyArgs.length = paramCount` falls out for free (you open at
   exactly `paramCount` fresh vars).
3. **Add `letRecAnn` inference.** Annotated polymorphic recursion is **decidable**
   (Henglein) — you are *given* the schemes, so it's **check-and-elaborate**, not
   infer-the-recursion-types: check each binding against its declared scheme under
   the scheme-relative opening, emit the elaborated bindings. (The locked
   `Infer.letRecAnn` / `InferRecGroupAnn` shape from the original design session:
   per-binding escape conditions, threaded; mirror the existing annotated-`let`
   skolemize-and-unify machinery.)
4. **Re-prove soundness and completeness/principality**, including the new
   `letRecAnn` case, against the type-passing `TypeOfHM`.
5. **Re-enable** `InferW`/`Examples`/`SpikeLetRecAnn` in the lakefile roots; **delete
   the dead erasure code** still living in `InferW.lean`; **refresh `README.md`**
   (it still describes the old type-erasure architecture — now wrong).

## Risk map (calibrated — this should be less of a research slog than Core was)

- **Lower-risk than the Core migration**, for three structural reasons: (i)
  inference is **static**, so the dynamics roadblocks that dominated Core
  (raw-vs-opened, CBN `let`, unfold-monomorphization) simply don't arise; (ii) the
  hard **de-Bruijn encoding is already settled in Core** — you target a fixed,
  reviewed spec rather than co-designing it; (iii) **annotated poly-rec is
  decidable**, so there's no "is this even possible" risk like erasure-vs-type-passing.
- **Mostly mechanical:** emitting `tyArgs` for the existing constructors
  (`var`/`ctor`/`lambda`/`app`/`letIn`/`match`) + updating *soundness*. The algorithm
  already computes the instantiation; recording it threads through the existing
  `InstantiatesBy`/`openWith` machinery.
- **The heavy lift: `letRecAnn` completeness.** Completeness/principality is the
  grindiest part of the existing `InferW` (see the prior completeness briefs:
  `greatest_K`, the skolem-escape kernel, annotated-let completeness). Extending it
  with the recursion-group case is the real effort. Budget for it; it'll be hard
  *proof engineering*, not fundamental walls.
- **Watch-point (moderate):** after the final substitution `S`, an emitted `tyArg`
  can still contain **generalised type variables** (those bound by the enclosing
  scheme). Recording them principally — and proving it — is the one spot where an
  inference-level "raw vs generalised" subtlety could surface (an echo of the Core
  scoping work). Bounded, but be careful there.

## Key landmarks / locked facts

- **Core API to target:** `Expr.var (deBruijnIndex) (tyArgs)`; `TypeOfHM.var`
  (grep `| var :` in the `TypeOfHM` inductive); `TypeOfHM.letRecAnn` (scheme-relative,
  per-binding cofinite — grep `| letRecAnn`); type-passing machinery `Expr.instTy`/
  `instTyAux`, `Expr.openTyVars`/`openTyVarsAux`, `Expr.substN` (type-beta in the
  `var` branch).
- **`InferW` landmarks:** `inferCore` (executable Algorithm W, returns the `Infer`
  derivation alongside the output — soundness by construction); `Infer.completeAt`
  (principality, by strong induction on `Expr.size`, cases on `Expr` — needs a
  `letRecAnn` case); the `var`/annotated-`let` cases (the latter already does
  skolemize-and-unify scoped-var threading — the template for `letRecAnn`).
- **Smoke-test targets** (these type in the declarative core and reduce soundly;
  inference should infer/elaborate them end-to-end): `LetRecAnnSmokeTest.polyRec_typeable`
  and `ownVarSelfRec_typeable` (in `Core`), `SpikeC.mutual_typeable`.

## Suggested staging

1. Get `InferW` **compiling** against the new Core: thread `tyArgs` through the
   existing `infer`/soundness/completeness for the non-`letRecAnn` constructors (now
   *emitting* `tyArgs`), update to the new `var` rule, delete the dead erasure code.
   Re-add `FHM.InferW` to the lakefile roots once green.
2. `letRecAnn` **inference + soundness** (check bindings against schemes under the
   scheme-relative opening; emit elaborated bindings).
3. `letRecAnn` **completeness** (the heavy lift).
4. Re-enable `Examples` + `SpikeLetRecAnn`; refresh `README.md`; final axiom audit
   (`progress`/`preservation`/`type_safety` stay axiom-clean; `infer` soundness +
   `completeAt` axiom-clean).

## Workflow / guardrails

- **NEVER** `sorry`/`admit`/`axiom`/`native_decide`; do not weaken the headline
  inference statements (soundness, completeness, principality). If a proof genuinely
  needs a **Core statement change**, STOP and report (that discipline is how the §2.3
  bug and the mutual-preservation hole were caught).
- Use the **Lean LSP MCP** `project-0-fhm-lean-lsp` (`lean_diagnostic_messages`,
  `lean_goal`, `lean_multi_attempt`, `lean_verify`) for fast iteration; fall back to
  `lake build` / `lake env lean`.
- **Independently verify before claiming done:** a *fresh* `lake build` + axiom audit
  against the rebuilt oleans. The stale-olean trap is real — `#print axioms` against a
  stale olean reported a theorem as an "unknown constant" during this campaign.

---

## Addendum (2026-06-26): the elaboration *shape* — decorate in `inferCore`, no new relation index

<!-- Written in a short follow-up session AFTER the brief above, by reading the
     actual Core/InferW code. It pins down the "how" of item 2 ("emit tyArgs"),
     which the brief left open. Nothing here contradicts the brief — it just makes
     the elaboration mechanism concrete and records what was confirmed against the
     committed code so the implementation push doesn't have to rediscover it. -->

**The open question this resolves.** Item 2 says to "record the concrete `tyArgs`
in the **output term's** `var`/`ctor` nodes" but not *how* inference carries that
output term. The naive reading — re-index the `Infer` relation over a *second*
output `Expr` — is heavy and turns out to be unnecessary.

**Why an output term is unavoidable at all (the irreducible bit).** The new `var`
rule makes `tyArgs` load-bearing (`tyArgs.length = polyTy.paramCount` +
`InstantiatesBy tyArgs polyTy.body ty`). So `TypeOfHM (S.onCtx ctx) e τ` over the
*raw* input `e` (var tyArgs = `[]` placeholders) is **false** for any polymorphic
use. The correct tyArgs at a use are inference-discovered (`freshVars Φ pc`, then
resolved by the final `S`) — they depend on the per-node frontier `Φ` and on `S`,
neither of which lives in the raw input. So soundness *must* be about a term that
inference **produces**, not the one it consumes.

**Why the substitution alone can't stand in for it.** Split "emit tyArgs" into
(a) *place* the right fvars into each var's slot — `(freshVars Φ pc).map .fvar` —
and (b) *resolve* those fvars to concrete types. `S` does (b) perfectly (it's just
`S.onTy` on each tyArg). But `S` is a global `fvar ↦ Ty` map; it has no idea *which*
fvars belong in *which* occurrence's slot. (a) is per-occurrence, term-shaped, and
inference-internal. So `S` can't do (a); something must first write the fvar blocks
into the tree — that "something" is the produced term.

**The confirmed shape (no second index needed).**
- **Decorated term:** each `var`/`ctor` carries its local opening
  `(freshVars Φ pc).map .fvar`. This reuses `Infer`'s existing `Expr` slot — pin
  the tyArgs right in the `var`/`ctor` rule (the rule already produces
  `polyTy.openVars (freshVars Φ pc)`; the matching tyArgs are just that opening).
- **`inferCore`** takes the raw (placeholder) skeleton and **returns** the decorated
  term alongside `(Φ', S, τ)` + derivation. The decoration is emitted *here* (in the
  executable), free, because `inferCore` knows `Φ` and `pc` at every node.
- **Soundness, honest form:** `TypeOfHM (S.onCtx ctx) (e.substTyFvars S) τ`. The
  fully-elaborated, runnable term is `e.substTyFvars S` — literally "apply `S` to the
  vars' tyArgs." At each `app`/`let` combinator the current proof's
  `TypeOfHM.onSubst_fixed` (fixed term) becomes `TypeOfHM.onSubst` (term-rewriting);
  `substTyFvars` composes along the `S₁ ++ S₂ ++ …` threading exactly like `onTy`.

**Already-committed machinery that makes this cheap.** The migration set the track:
- `Expr.substTyFvars` already maps `S.onTy` over every `var`/`ctor` tyArgs slot
  (`Expr.substTyFvar`, Core ~1806).
- `TypeOfHM.onSubst : TypeOfHM ctx e τ → TypeOfHM (S.onCtx ctx) (e.substTyFvars S)
  (S.onTy τ)` is proven for **all** terms incl. the var-tyArgs case
  (`typ_subst_preservation`, Core ~4251/4678). It does all the
  `InstantiatesBy`/`openVars`-under-`S` commuting *internally* — the elaboration
  proof reuses it wholesale rather than re-deriving anything.
- The `var` leaf is a trivial materialization: today's soundness already names the
  instantiation `Xs = freshVars Φ pc` as an existential witness
  (`InstantiatesBy.openVars`); decorated, the term just carries that same `Xs` as
  concrete tyArgs, and the new `length = pc` premise holds by construction.

**The one genuinely new bookkeeping item.** A `var`'s tyArgs now feed
`Expr.tyFreeVars` (Core ~4650: `| .var _ tyArgs => tyArgs.flatMap Ty.freeVars`), so a
decorated term's free type vars include the **fresh inference vars** `Xs`. That
collides with the soundness/principality hypotheses that assume *all* of `e`'s free
type vars are rigid: `hKe : ∀ y ∈ e.tyFreeVars, y ∈ K` would demand `Xs ⊆ K` (false),
and top-level `hclosed : e.tyFreeVars = []` is false for a decorated term. Fix: re-cut
that invariant so it separates **rigid annotation vars** (scoped type vars — stay in
`K`, fixed by `S` since `S` avoids `K`) from **fresh tyArg vars** (∉ `K`, *resolved*
by `S` — the whole point). I.e. `hKe`/`hclosed` should constrain only the *annotation*
free vars (λ/let ascriptions), not the var/ctor tyArgs. Bounded threading through the
invariant layer (`hKe`/`hclosed`/`belowFvars`), not a soundness risk — it's the
brief's "generalised vars survive in tyArgs" watch-point, made concrete.

**The second new piece: closing the elaborated rhs at the annotated binders.**
`letInAnn` (and Stage 2's `letRecAnn`) infer the *opened* rhs
(`rhs.openTyVars (freshVars …)`), so the elaborated rhs comes back with the scheme's
own variables resolved to fresh fvars. But the term in the relation's conclusion
(`.letIn (some σ) rhs body`) lives in the *closed* original scope, and the declarative
rule re-opens it (`Expr.openBoundTyVars`). So the elaborated rhs must be **closed
back** over the inference vars — exactly where the scheme's generalised variables
surface as `bvar`s in a var's tyArgs. Core has `Ty.closeOver` and the type-level
round-trip `Ty.openVars_closeOver_rename` (~3004) but **no `Expr`-level close**, so
this needs a small new `Expr.closeTyVars` + its `openBoundTyVars`/close round-trip
lemma, mirroring the type-level one. Bounded, but genuinely new (not mechanical), and
it is the term-level face of the brief's "generalised vars survive in tyArgs"
watch-point. The non-opening constructors (lambda/app/var/ctor/`letIn`-none/match/
`letRec`) need none of this — they're the mechanical bulk.

**Net:** Stage 1 keeps the relation arity unchanged; the elaboration is
`inferCore`-emits-decorated-tree + `e.substTyFvars S` in the soundness conclusion, on
top of already-committed Core lemmas. The two genuinely-new pieces beyond mechanical
`tyArgs`-threading are (1) the `tyFreeVars`/`K` re-cut and (2) the `Expr.closeTyVars`
round-trip for the annotated binders. Both are bounded and both are concrete instances
of the brief's rigid-vs-generalised watch-point.

---

## Addendum 2 (2026-06-26): session handoff — close-back built; a real `let`-generalisation soundness snag

<!-- Candid handoff after a long working session. The close-back round-trip (the
"watch-point") is built + machine-checked; the honest-soundness rewrite then hit a
genuine type-passing let-generalisation **soundness** snag, detailed below. This
SUPERSEDES Addendum 1's guess that an `annTyFreeVars` "tyFreeVars re-cut" is the fix —
it is NOT (it's unsound). The principled fix is identified below but unverified. -->

### Landed + verified (each green via the lean-lsp MCP; `lake build` green for Core + the built roots)

- **`Infer.var` decorated**: `Infer … (.var i ((freshVars Φ pc).map Ty.fvar)) …`. The whole
  `Infer`/`InferBranches`/`InferRecGroup` relation **and** invariant layer
  (`frontier_le`/`lc`/`belowFvars`) are green. (All the baseline `sorry` warnings were
  cascade artifacts of the under-applied `.var`, now gone.)
- **`genScheme_hasSchemeVars` + `HasSchemeVars.onSubst`** adapted to the new
  `instTy`-carrying `HasScheme*` (via Core's `Expr.instTy_eq_self_of_tyBvarBounded` /
  `Expr.instTy_fvar_eq_openTyVars`).
- **Dead erasure code deleted** (`Expr.IsTyErased.tyFreeVars_eq_nil`, `typecheck_progress`,
  `typecheck_preservation`, and the `eq_nil_of_bodies` helper).
- **The full close-back round-trip** — the brief's watch-point, now machine-checked:
  - `Ty.closeOverFrom` (depth-`d` close) and `Expr.closeTyVars`/`closeTyVarsAux` (the
    structural inverse of Core's `Expr.openTyVarsAux`).
  - Type-level (all depth-general): `Ty.openVarsFrom_closeOverFrom_self` (close∘open = id),
    `Ty.openVarsFrom_closeOverFrom_rename` (close-then-open = rename `Ys↦Xs`),
    `Ty.not_mem_closeOverFrom_freeVars` (closing removes `Ys`).
  - Term-level: `Expr.openTyVars_closeTyVars_self`, `Expr.not_mem_closeTyVarsAux_tyFreeVars`,
    and the headline `Expr.openTyVars_closeTyVars_rename`.
  - `Expr.NoRecAnn` (+ `BranchList_iff`/`RecGroup_iff`): discharges the one non-uniform
    case — `open`/`close` leave `letRecAnn` *schemes* untouched while `substTyFvars` would
    substitute them, so the rename needs `Ys ∉ those schemes`; Stage-1 `Infer`-derived
    terms have no `letRecAnn`, so this is vacuous (prove `Infer … e … → e.NoRecAnn` when wiring).
- **`Expr.annTyFreeVars`** (annotation-only free vars) is defined — but **do NOT** use it as
  the `genScheme` rigid set (see the snag; it's unsound).
- **One benign Core change**: made `BranchList`/`RecGroup`/`RecGroupAnn.openTyVarsAux` and the
  two `*_eq_map` lemmas **public** (they were `private`, unreferenceable from `InferW`). No
  statement changed; pure visibility.

### NOT done
- Honest-form rewrite of `Infer.sound` + `sound_letIn`/`sound_letInAnn` +
  `InferBranches.sound`/`InferRecGroup.sound` (conclusion → `TypeOfHM (S.onCtx ctx)
  (e.substTyFvars S) τ`; `onSubst` instead of `onSubst_fixed`; wire `Infer→NoRecAnn` + the
  close-back rename into `sound_letInAnn`).
- `inferCore` output-term threading (return the elaborated `Expr`) + `letRecAnn => none` stub.
- `AuditCapstone` re-decoration; completeness; re-add `FHM.InferW` to the lakefile; axiom audit.
- **The `genScheme` rigid-set fix** below — do this *first*.

### The snag (the crux — read before touching soundness)

The relation generalises with `genScheme rhs.tyFreeVars (S₁.onCtx ctx).env τ₁` (and `letRec`
with `bindings.flatMap Expr.tyFreeVars`). In the **erasure** Core this was correct
(`rhs.tyFreeVars` = the rigid scoped vars, and `S₁` fixed them). In the **type-passing**
Core it is **unsound**: `genScheme` is computed from the **pre-substitution** decorated term,
but soundness is about the **post-substitution** elaborated term `rhs.substTyFvars S₁`, and the
two disagree exactly on the emitted tyArgs.

Concrete failure — `let g = (λx. id x) in …`, with `id : ∀a.a→a`:
- The elaborated rhs is `λx. id [α] x` (`α` = the lambda's param var). By the type-passing
  `var` rule, `id [α]` types **only** at `α→α`, so `λx. id [α] x` types **only** at `α→α`.
- `λx. id x` has no annotation, and the var carries tyArg `[α]`, so **pre-`S₁`**
  `rhs.tyFreeVars` is `{Φ}` (the raw opening) while the elaborated rhs's free vars are `{α}`
  (after `S₁ = [Φ↦α]`). `genScheme {Φ} … (α→α)` then **generalises `α`** (it's not in `{Φ}`),
  i.e. `M = ∀a.a→a`.
- But `TypeOfHM.letIn` (unannotated; `openBoundTyVars none = id`) requires the *fixed*
  boundExpr to type at **every** `M.openVars Xs = X→X`. It types only at `α→α`. **Premise
  fails ⇒ generalising `α` is unsound.**

This kills both earlier guesses: `annTyFreeVars` generalises `α`/bare-var tyArgs (unsound —
Addendum 1's "re-cut" was wrong); raw `rhs.tyFreeVars` (pre-`S₁`) generalises the post-`S₁`
`α` (also unsound). Root truth: type-passing `let`-generalisation is sound **only** for vars
the boundExpr is *structurally* polymorphic in (e.g. an unannotated lambda's param, which
carries no tyArg), and must keep **tyArg-mediated** vars rigid (`t [α]` is monomorphic at `α`).
This Core has **no let-bound type abstraction (`Λ`)** and `openBoundTyVars none = id`, so a
boundExpr can never be re-instantiated per opening — hence tyArg-mediated polymorphism
(`let f = id in f f`) is genuinely *not expressible*; such bindings must stay monomorphic
(which IS sound). (NB: this is an expressiveness gap vs. surface HM — worth a separate
decision about whether the Core should grow let-bound `Λ`. For now, soundness only needs the
monomorphic-where-tyArg-mediated behaviour.)

### The principled fix (identified, NOT yet verified)

Make `genScheme`'s rigid set the **elaborated (post-`S₁`) boundExpr's** free type vars:

```lean
-- letIn:
genScheme (rhs.substTyFvars S₁).tyFreeVars (S₁.onCtx ctx).env τ₁
-- letRec:
genGroupSchemes ((bindings.map (·.substTyFvars S₁)).flatMap Expr.tyFreeVars) …
```

Why it's right (checked by hand on `λx.x`, `λx. id x`, bare `id`):
- It reduces to the old `rhs.tyFreeVars` in the erasure Core (`rhs.substTyFvars S₁ = rhs`
  there), so it's the faithful generalisation.
- `(elaborated rhs).tyFreeVars` is **exactly** the tyArg-mediated vars: an unannotated lambda's
  structurally-polymorphic param is *not stored* in the term, so it's *not* in `tyFreeVars`
  (→ generalised, sound); a concrete `id [α]` use contributes `{α}` (→ kept rigid, sound).
- It is `S₁`-consistent — rigid set and the boundExpr it constrains are both at the
  elaborated level, dissolving the pre/post mismatch.

This is a **relation change** (`Infer.letIn`/`letRec` + `inferCore` must match) that ripples
through `genScheme_hasSchemeVars`/`sound_letIn`/completeness (~30 `genScheme rhs.tyFreeVars`
sites). Recommended order: (1) make this rigid-set change; (2) re-confirm the invariant layer;
(3) then the honest-soundness rewrite against the post-`S₁` rigid set, reusing the close-back
rename for `sound_letInAnn`.

### Practical notes
- The honest-soundness layer is one `mutual` block + helpers in `InferW.lean` — not
  parallelisable; tight lean-lsp iteration (`lean_diagnostic_messages` scoped by line range,
  `lean_goal`, `lean_multi_attempt`) is the way.
- `InferW`/`Examples`/`SpikeLetRecAnn` stay excluded from the lakefile; the file won't fully
  compile until completeness lands (`completeAt`'s `cases e` needs a `letRecAnn` case, which
  needs `letRecAnn` inference). Verify per-declaration via the MCP meanwhile.
- After any Core edit (e.g. the visibility change), rebuild + restart the LSP (`lean_build`)
  or `InferW` shows stale errors.
- Honest self-assessment for the next agent: the close-back was the right hard kernel to build
  (it's reusable and the watch-point is genuinely closed), but I over-invested in it before
  validating the `letIn` soundness end-to-end — which is where the rigid-set snag lives.
  Validate the post-`S₁` rigid-set fix on `sound_letIn` *early* before grinding the full block.
