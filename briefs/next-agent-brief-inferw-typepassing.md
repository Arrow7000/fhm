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
