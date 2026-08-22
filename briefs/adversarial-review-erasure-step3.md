# Adversarial review brief — erasure-on-`Step` migration, step 3 (`Infer.sound`)

You are reviewing a Lean 4 formalisation of Hindley–Milner type inference at
`/Users/aron/dev/fhm`, branch `main`, commit `a505638` (the migration's "step 3"
checkpoint; `lake build` is green). Your job is to **adversarially verify** that
steps 1–3 of the "erasure on `Step`" migration are correct — in particular that the
headline coherence theorem `Infer.sound` is a genuine, non-vacuous, axiom-clean
theorem, and that the enabling lemma (`PolyTy.Generalizes.freeVars_subset`) is true.
Report every way in which any claim below fails to hold; do not soften.

## Read first (in this order)

1. `briefs/design-memo-erasure-migration.md` — the settled plan; §0–§3 and §6 are the
   substance. §5.3 now carries an execution-status note.
2. `briefs/next-agent-brief-erasure-step4.md` — the authoritative "what's done / what's
   left" handover (steps 4–6 remain).
3. `briefs/feature-support-analysis-response-6.md` — the settled feature design (the
   DM cut + ceiling).

## What was done (steps 1–3) and what to verify

### 1. The DM cut (`Infer.letRec`) — commit `78cf9a1`
`FHM/InferW.lean`: `RecSpec.init` (all-`.mono`), `Infer.letRec` (the `ceilingOK`
premise + `ceilingSchemes` body env), `InferRecGroup` (mono-only path), `ceilingOk`/
`ceilingOKB` (the decidable check).
- **Verify**: `RecSpecs.ceilingOK` (the *semantic* `Generalizes` premise) and the
  decidable `ceilingOk`/`ceilingOKB` agree *exactly* — i.e. `ceilingOk_sound` /
  `ceilingOKB_sound` are sorry-free and their hypotheses are neither stronger nor
  weaker than the semantic relation. The known traps (from the memo's "KNOWN SHARP
  EDGES"): (a) `σ`'s outer free vars must be rigid; (b) unify is bounds-blind
  (erase bounds first); (c) `List.zip` truncates, so equal lengths must be required.
- **Verify**: `InferRecGroup.consPoly` is dead-but-present (unreachable from
  `Infer.letRec`), and the new `InferRecGroup.sound` dispatches its case vacuously —
  i.e. the mono-only conclusion is not accidentally unsound for `.poly` specs.

### 2. `Expr.erase` + `erase_openTyVarsAux` — commit `9380ab0`
`FHM/Core.lean`: `def Expr.erase` (~line 2579), `Expr.erase_openTyVarsAux` (~2690),
`erase_openTyVars`/`erase_openBoundTyVars` (~2721).
- **Verify**: `erase` matches the memo §3.1 spec *exactly* (`lambda _→none`,
  `letIn _→none`, `letRec _→all-none`, `var i _→var i []`, structural elsewhere);
  `erase_openTyVarsAux` is depth-generalised (`∀ e d`, not just `d=0`); all are
  sorry-free and axiom-clean. `#print axioms Expr.erase_openTyVarsAux`.

### 3. The coherence theorem `Infer.sound` — commit `a505638` (THE headline)
`FHM/InferW.lean:16853`:

```
theorem Infer.sound : Infer Φ ctx e Φ' S eOut τ →
    CtxWF ctx → CtxBelow Φ ctx → (K : List Nat) → (∀ k ∈ K, k < Φ) →
    (∀ y ∈ e.tyFreeVars, y ∈ K) → (∀ p ∈ S, p.1 ∉ K) →
    TypeOfHM (S.onCtx ctx).eraseBounds e.erase (Ty.eraseBounds (S.onTy τ))
```
plus `InferBranches.sound` (:18266) and `InferRecGroup.sound` (:18665), in a `mutual`
block. `#print axioms Infer.sound` must be `{propext, Classical.choice, Quot.sound}`
— **no `sorryAx`**.
- **Verify the statement is the right coherence statement**: source checker `Infer`
  (Path R, produces `bl`-annotated types) ⟹ declarative `TypeOfHM` of the *erased
  input* `e.erase`, with `eOut` ignored, at the erased `S`-context and erased `S`-type.
  Check the `eraseBounds` threading is where the memo §6.1 says it must be, and that
  the `K`-list escape preconditions match the old `Infer.sound_elab` (:9688).
- **Verify the opening rewrite**: the proof begins `rw [show S.onTy τ = τ from
  Ty.substFvars_eq_self_of_no_key (… (Infer.eliminates …).2 …)]`. Confirm this is
  sound — i.e. that `Infer.eliminates` really yields `∀ p ∈ S, p.1 ∉ τ.freeVars` for
  the *output* `τ` (the "output type is post-substitution" invariant), not merely
  idempotency of `S`'s own images.
- **Verify no off-script damage**: `git show a505638 --stat` should touch only
  `FHM/InferW.lean` (+ the briefs). Diff should not alter `Infer.sound_elab`,
  `Infer.sourceSound`, or any `TypeOfHM.*` metatheory lemma. The only remaining
  `sorry`s are the 8 listed in the handover doc, all in the doomed bucket.

### 4. The enabling lemma (scrutinise hardest) — `FHM/InferW.lean:3859`

```
theorem PolyTy.Generalizes.freeVars_subset {M' M : PolyTy} (h : PolyTy.Generalizes M' M) :
    M'.body.freeVars ⊆ M.body.freeVars
```

This is the load-bearing new fact for the `letRec` body-lift. **Prove or disprove it
yourself** (don't just check it compiles): is it true that a generalising scheme
introduces no free type variables absent from the scheme it generalises? Look for a
counterexample of the form `Generalizes M' M` with `M'.body.freeVars ⊄ M.body.freeVars`
(e.g. can `M' = ∀a. v → a` generalise some `M` whose body lacks `v`?). If the lemma is
false, the whole `letRec` case is suspect. Also check it is applied correctly at
`:18178` (that `M'` is instantiated to the *erased genGroup* side and `M` to the
*erased annotation* side).

### 5. The invariant layer (REUSE bucket)
`Infer.lc/.belowFvars/.dom_below/.eOut_avoid/.eliminates/.eOut_tyBvarBounded/
.dom_avoid/.gap_avoid/.preservesAnns` + `InferRecGroup.eOut_avoid/.dom_avoid/.gap_avoid`
were re-proved for the post-cut `Infer.letRec` rule. Spot-check a few `letRec` cases
for the post-cut rule shape (ceiling premise, `ceilingSchemes` env, `letRecElab`
output) and that nothing is `sorry` or `admit`/`axiom`/`native_decide`.

## Suggested verification commands

```
lake build                                  # must be green (831 jobs)
#check @Infer.sound                          # the coherence statement
#print axioms Infer.sound                    # {propext, Classical.choice, Quot.sound}
#print axioms InferRecGroup.sound            # {propext, Classical.choice, Quot.sound}
#print axioms PolyTy.Generalizes.freeVars_subset  # {propext, Classical.choice, Quot.sound}
grep -n "sorry" FHM/InferW.lean             # exactly the 8 doomed sites (see handover)
```

## Deliverable

A verdict per numbered section above: PASS / FAIL, with a concrete counterexample or
proof sketch for anything that FAILs. Call out (a) any place `Infer.sound` could be
vacuous or overly-strong/weak, (b) any place the ceiling check disagrees with the
semantic `Generalizes`, and (c) any `sorry`/`admit`/`axiom`/`native_decide` outside the
8 doomed sites.
