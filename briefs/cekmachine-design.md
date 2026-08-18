# CEK machine migration — design + living status

**Status (2026-08-18): Stage 1 IN PROGRESS.** The machine is defined and building
(`FHM/CekMachine.lean`, commit `9fdc746`): `Val`/`VEnv`/`Kont`/`State`/`StepM` + the
typing invariant (`ValTyped`/`EnvOK`/`KontTyped`/`StateOK`) + the exhaustiveness
lifting (`ExhaustiveVal/Env/Kont/State`), with `progress`/`preservation`/
`preservation_star`/`preservation_exhaustive`/`type_safety`/`type_safety_closed`/
`stepM_deterministic`/`ValTyped_inst` stated as `sorry`s ready for farming.
Additive only — `TypeOfElabHM`, the old `SmallStep.Step`, and elaboration are all
still intact, and `lake build` is green.

Two design points settled *while* writing the definitions (they refine §3, not
contradict it):

1. **CBN thunks and rec-closures carry their annotations** (`thunk ann e E`,
   `recclo anns bindings E j`) — inert at reduction time, but needed so `ValTyped`
   can type a CBN binding at its *generalised* scheme (`GeneralisesTo` / the
   `letRec` group premises). A value at a generalised scheme is *used* at a monotype
   via the `ValTyped_inst` instantiation lemma; `StateOK (.ret v k)` types `v` at a
   monotype, which is exactly how a polymorphic value is consumed by a continuation.
2. **Evaluation order is unchanged from the old `Step`** — CBV `app`/`match_`,
   CBN `letIn`/`letRec` (thunks forced on use). This is faithful to the current
   observable behaviour *and* it is what makes non-value recursive RHSs (e.g.
   `letRec [var 0] (var 0)`) diverge correctly via thunk-forcing loops, so no
   separate "recursive values" restriction is needed.
3. **Value consumption is gated on `IsVal`** (found by the first proof farm, not by
   design). `appArgStep`/`beta`/`ctorApp`/`primOpPart` must require the consumed
   value to be *already forced* (`IsVal`, i.e. not a thunk/rec-closure); otherwise a
   thunk leaks into a function/argument/ctor position unforced and `(let f = λx.x in
   f) 3` can get **stuck** (the `appArgStep` path puts the thunk in `appFun`, where
   no rule fires). This was caught as a *failed* `stepM_deterministic` proof, and is
   a genuine soundness bug, not just non-determinism.

**Proof status (farmed):** `preservation_exhaustive` ✅ (structural, over all 18
`StepM` cases, + 3 private helpers `exhaustiveEnv_get/_append/_bindGroup`).
`stepM_deterministic` re-farming after the `IsVal` fix. Remaining sorrys:
`ValTyped_inst`, `GeneralisesTo_inst`, `progress`, `preservation`,
`preservation_star`, `type_safety`, `type_safety_closed`.

This doc remains the plan, living status log, and handover artifact.

**Git state at migration start:**
- `main` = `62b20aa` ("Prove the SurfaceBridge headline: surface_type_safe and its
  corollaries") — the pre-letRec-promotion base, pushed to `origin/main`.
- `letrec-promotion` branch = `9746f42` — the full letRec-promotion Stage-1 work,
  archived (pushed to `origin/letrec-promotion`) in case we ever want it back.
  It is **not** the direction we're going; it's a shelved experiment.

---

## 0. The one-paragraph diagnosis

FHM's ~19k-line inference stack is dominated by a single architectural decision:
**the operational semantics is substitution-on-type-passing-terms**. Because `Step`
rewrites terms and the term is the machine state, every polymorphic instantiation
must be written into the term (`var j [tyArgs]`) and every invented generalisation
(the mono members of a `letRec`) must become a term-level Λ — which, for `letRec`,
means the O(n²) Λ-outside nest, which changes the term's shape, which forces a
second typing relation (`TypeOfElabHM`) and a second soundness induction
(`Infer.sourceSound`), and made the whole letRec-promotion refactor necessary.

**The fix is not to keep patching elaboration. It is to remove the premise:** switch
the dynamics to a type-erasing CEK machine, where generalisation lives in the
machine's (proof-level) type environment instead of in the term. Then elaboration
ceases to exist, `TypeOfElabHM` is deleted, `TypeOfHM` is the only typing relation,
and `Infer` collapses to "compute `(Φ', S, τ)`" with a single soundness theorem.

This is not a novel idea — it is the architecture of essentially every comparable
mechanisation (Charguéraud's mini-ML, Dubois, Garrigue's certint), none of which
elaborate to a type-passing term, and none of which have our letRec problem. We are
migrating **toward** the mainstream, not away from it.

---

## 1. What we're deleting (the causal chain, concretely)

1. `SmallStep.Step` (substitution semantics, `Core.lean:1435`) — `beta`/`letReduce`/
   `letRecUnfold`/`matchReduce` + congruence, all `substN`-based.
2. The type-passing substitution machinery: `Expr.substN` (`Core.lean:1330`),
   `Expr.instTy`/`instTyAux` (`:1125/1172`), `Expr.shiftFrom` (`:1015`),
   `RecGroup.shiftFrom`, `shieldDepths`.
3. The elaboration relation: `Infer`/`InferBranches`/`InferRecGroup`'s `eOut` index
   (`InferW.lean:2908/3049/3096`), the `letRecElab`/`letRecElabNest` nest
   (`InferW.lean:2487/2506`), `Expr.closeTyVars` (`InferW.lean:1966`).
4. The second typing relation: `TypeOfElabHM` (`Core.lean:3139`) + all of its
   metatheory (`Core.lean:5101–10917`, ~5,800 lines), `TypeOfElabHM.faithful`
   (`Core.lean:5260`).
5. `Infer.sourceSound` and its `sourceSound` family (the second induction).
6. The residual eraseBounds bridge over the old machine (`Core.lean:10117–10880`)
   — replaced by the machine's own (simpler) erase-commutation.

## 2. What survives (unchanged or simplified)

- `Expr` (minus `var.tyArgs`), `Ty`, `PolyTy`, `Subst`, unification/MGU, `InstantiatesTo`,
  `GeneralisesTo`, `RecSpecs.*`, `BranchCtorSpec` — the whole *static* typing vocabulary.
- **`TypeOfHM`** (`Core.lean:3309`) + `TypeOfMatchBranch` — becomes THE relation.
  Its `var` rule already instantiates declaratively (`∃ instArgs`, ignores stored
  `tyArgs`); it just drops the (already-ignored) `tyArgs` field from the constructor.
- `Infer`/`inferCore`/`principalType`/`typecheck` — minus `eOut`.
- `TypeOfHM`'s metatheory (`InferW.lean:11661+`): `rec_strong`, `typ_subst_preservation`,
  `onSubst`, `eraseBounds_of` — survives intact.
- The front end: SurfaceLang, Parse, PatComp (its *compile-correct* part), Scc,
  exhaustiveness (`AllMatchesExhaustive`, `checkExhaustive`), Decls, Pretty.
- The bounds layer (see §3.6) — purely static, orthogonal.

## 3. Target architecture

### 3.1 The machine

A small-step CEK machine. Type-erasing: the machine never inspects types; the term's
annotation slots (`lambda paramAnn`, `letIn ann`, `letRec anns`) are inert payload.

```
Val   ::= clo (body : Expr) (E : Env)      -- lambda closure, captures its env
        | ctorVal (name) (args : List Val) -- constructor chain (for match)
        | prim ...                          -- primitives / partial primops
Env   := List Val                          -- de Bruijn-indexed
Frame ::= appArg (E : Env) (arg : Expr)   -- evaluate arg, then apply
        | appFun (v : Val)                 -- apply v to this function value
        | matchSel (branches) ...          -- match continuation frames
Kont  := List Frame
State := Env × Kont × Expr
```

Key reduction rules (shape):
- `var i` in env `E` → replace the term with the looked-up closure (via a `kont`
  frame, or inline at redex positions).
- `app`: push `appArg E arg` frame, evaluate `f`; then evaluate `arg`; then β.
- `letIn ann rhs body` (CBN, see D3): `(E, k, .letIn _ rhs body) ↝ (clo(rhs,E) :: E, k, body)`.
- `letRec anns bindings body`: extend the env with the group's *recursive* closures
  (each `clo(bindingⱼ, E')` where `E'` is the extended env itself — the standard
  recursive-environment / cyclic-closure construction), then evaluate `body`.
- `match_`: evaluate scrutinee to a ctor chain, select the first matching branch,
  extend env with the bound fields, evaluate the branch body.

### 3.2 The typing of the machine (the new metatheory)

```
WellTypedEnv E ctx   := E.length = ctx.env.length ∧ ∀ i, ValTyped (E[i]) (ctx.env[i])
ValTyped (clo body E) σ := ∃ Γ τ, WellTypedEnv E Γ ∧ TypeOfHM Γ body τ ∧ σ "generalises" τ
KontTyped k τ ρ      := "k expects a value of type τ and produces ρ"
StateOK (E,k,e) ρ    := ∃ Γ, WellTypedEnv E Γ ∧ TypeOfHM Γ e (hole k) ∧ KontTyped k (hole k) ρ
```

Headline theorems (replacing the old `TypeOfElabHM.*` ones, same names, new types):

```
progress    : StateOK s ρ → (s is final) ∨ ∃ s', StepM s s'
preservation: StateOK s ρ → StepM s s' → StateOK s' ρ
type_safety / type_safety_star : as before, over machine states
```

The skolem-orphaning problem that originally motivated type-passing **dissolves**:
a skolem lives in the `Γ` captured by a closure's `ValTyped`, which persists exactly
as long as the closure does — lexical scoping does the work, and no type is ever
substituted into a term.

### 3.3 Inference after the migration

```
Infer : Nat → Ctx → Expr → Nat → Subst → Ty → Prop      -- eOut index deleted
Infer.sound : Infer Φ ctx e Φ' S τ → TypeOfHM (S.onCtx ctx) e (S.onTy τ)
```

No `sourceSound`, no `faithful`, no `preservesAnns` (annotations are already in the
source term — the bounds layer reads them off `e` directly). Completeness/principality
are stated against `TypeOfHM` on the *source* term, which is what they already
partially do via the residual bridge; the residual `eraseBounds` wrapper goes away.

---

## 3.4 Decisions (locked, unless evidence says otherwise)

**D1 — CEK (small-step) vs big-step `Eval`.** → **CEK.** Preserves the
progress/preservation/"never gets stuck" headline shape exactly; canonical; the user
asked for CEK. Cost: continuation typing (`KontTyped`). (Big-step is simpler but
can't express "not stuck" without re-deriving progress; rejected.)

**D2 — evaluation order.** → **Preserve CBN `letIn`, CBV `app`/`match`** (current
observable behavior). The CBN `let` becomes "bind the RHS as a zero-arg closure".
This keeps every existing `Examples`/`#guard` valid and minimises semantic drift.
(A full-CBV switch is a pure-lang-legal alternative, but it is a *behavior change*
and not needed for the migration; do not do it here.)

**D3 — `var.tyArgs`.** → **Remove** (principled: a type-erasing machine has no
business carrying type args), but **last**, as a cleanup stage after the machine and
rewiring are green, so the wide mechanical sweep doesn't entangle the risky diff.
The machine works fine with the field present-but-ignored in the interim.

**D4 — machine state carries env explicitly; `Expr` is unchanged.** No closures leak
into the source `Expr`; `Val` is a separate type. `Expr` keeps its `ann` slots (they
are source-level annotations, needed by `TypeOfHM`).

**D5 — `Infer` drops `eOut` wholesale.** No "decorated term" survives; the source
term is the typed term. The `...Out` mirrors, `closeTyVars`, `letRecElab*`, `eOut_*`
invariants, `UserAnnsCopied`, `faithful` all die.

**D6 — bounds (Path R).** Orthogonal (verified: `Step` is bounds-free; bounds live
only in `Ty`/inference/residual-bridge). We re-prove the four machine-side
erase-commutations (`StepM.eraseBounds`, `StepM.of_eraseBounds`,
`Val`-value/`AllMatchesExhaustive` erase-commute) and re-target the few
`Bounds/*` modules that *walk the elaborated term* (`Synth`/`Check`/`Erase`/
`Pipeline`) to walk the source term instead — which is simpler, since annotations
are already present in the source.

**D7 — PatComp adequacy** (`lowerMatch_adequate_of_typed`, stated against
`SmallStep.Step`) is re-stated against `StepM`. Its compile-correctness half is
untouched.

---

## 4. Staging (green checkpoints)

The migration is **big**, so it is staged so the risky novel part (machine
metatheory) lands first and additively, and the rest is deletion + rewiring.

### Stage 1 — the machine, additively (THE risky stage)

New file `FHM/CekMachine.lean` (imports `FHM.Core`, in lakefile roots): define
`Val`/`Env`/`Kont`/`State`/`StepM`, the computable `stepM` + fuelled `evalM`, and
prove against the **existing** `TypeOfHM` (with `var.tyArgs` still present, ignored):

- `WellTypedEnv`, `ValTyped`, `KontTyped`, `StateOK`;
- `progress`, `preservation`, `preservation_star`, `type_safety`, `type_safety_star`;
- `stepM_sound`/`stepM_complete`, `StepM.preserves_exhaustive`;
- the erase-commutation lemmas (D6).

Nothing is deleted. `lake build` stays green; the old `Step`/`TypeOfElabHM` coexist
with the new machine. **This stage de-risks the whole migration**: if the machine
metatheory is tractable, Stages 2–4 are mostly mechanical deletion.

### Stage 2 — rewire `Infer` (drop `eOut`)

In `InferW.lean`: delete the `eOut` index from `Infer`/`InferBranches`/`InferRecGroup`,
re-prove `Infer.sound : TypeOfHM (S.onCtx ctx) e (S.onTy τ)` **directly** (structural,
no residual eraseBounds wrapper), delete `sourceSound`/`faithful`/`eOut_*`/`letRecElab*`/
`closeTyVars`/`...Out` mirrors, simplify `complete`/`principal`. Green: `InferW`
sorry-free, `typecheck_*` theorems unchanged in shape.

### Stage 3 — delete the old dynamics, rewire the surface

Delete `TypeOfElabHM` + its metatheory, `SmallStep.Step` + `substN`/`instTy`/
`shiftFrom`, the residual bridge. Rewire, to `TypeOfHM` + `StepM`:

- `SurfaceBridge`: drop `elaborate`/`elaborateProgram`'s `eOut` threading; re-state
  `surface_type_safe`/`program_type_safe`/`surface_type_safe_of_SurfaceWT` against the
  machine (`StateOK` → `type_safety`), keeping the exhaustiveness premise;
- `Headlines`: `WellTyped := ∃ τ, TypeOfHM ⟨[],ctors⟩ e τ`; `runSafe` loops `stepM`
  over machine states; `elaborateSafe` becomes `typecheckSafe` (API-compatible name
  retained, or renamed — see §6);
- `EvaluateUnsafe`: replace `evaluate`/`evaluateUnsafe` with the machine evaluator +
  the fuel↔`StepM*` bridges;
- `PatComp`: re-state the adequacy half against `StepM`;
- `Examples`, `Live`, `EditorSupport`, `Bounds/*` eOut-walkers: re-target to source
  term / machine evaluator.

Green: `lake build` **and** `lake build fhm` (the CLI pulls in the bounds pipeline).

### Stage 4 — cleanup

Remove `var.tyArgs` from `Expr` and `TypeOfHM.var` (drop the ignored field), delete
now-dead helpers (`AllMatchesExhaustive.substN`, `...shiftFrom`, `...instTy`), refresh
README/`complexity-budget.md`/`letrec-design.md` to the new architecture. Green:
full build, `#print axioms` clean on every headline theorem.

---

## 5. Risk map

| Risk | Severity | Mitigation |
|---|---|---|
| Machine metatheory (well-typed-state invariant) is heavier than hoped | HIGH | Stage 1 is isolated and additive; its outcome is the go/no-go for the whole migration. Fallback: big-step `Eval` (simpler) if continuation typing grinds. |
| `PatComp` Step-adequacy re-proof is large | MED | Its compile-correct half survives; only the adequacy half is re-stated. |
| `surface_type_safe` re-statement regresses | MED | Same shape (typeable + exhaustive ⇒ safe), just over `StateOK`. |
| Bounds modules walking `eOut` | LOW | They already walk the source-level annotations; re-target is mechanical. |
| `var.tyArgs` removal sweep (Stage 4) | LOW–MED | Deferred to last; purely mechanical, wide. |
| Silent semantic drift (CBN/CBV) | LOW | D2 explicitly preserves current order; Examples/`#guard`s are the regression net. |

**The honest open question this doc does not answer:** whether the machine
metatheory's total cost is *less* than the ~5,800 lines of `TypeOfElabHM` metatheory
+ ~4,100 lines of letRec machinery it deletes. That is exactly what Stage 1 measures.
The architecture is right; the magnitude of the win is unproven until Stage 1 lands.

---

## 6. Workflow (proof farming — established protocol)

- **You** make the substantive changes: define all `inductive`s/`def`s/theorem
  *statements*, prove the trivial ones, leave the rest as `sorry`.
- **Proof workhorse = `deepseek v4 flash`** (the `deepseek-flash` subagent), one
  lemma/small cluster per call, instructed to:
  - prove and **nothing else** (no refactors, no statement changes, no new defs);
  - use the **lean-lsp MCP** (`lean_goal`, `lean_diagnostic_messages`,
    `lean_multi_attempt`, `lean_local_search`) for fast iteration, **avoiding
    `lake build` unless necessary**;
  - if the LSP stalls / times out / "diagnostics_unavailable", call **`lean_build`**
    (runs `lake build` + restarts LSP) then re-query — treat >~120s as the kick signal;
  - if a goal looks **unprovable as stated**, STOP and report back (do not weaken the
    statement, do not `admit`/`axiom`/`native_decide`).
- **Edit `.lean` only via Read/Edit** (never Python/`sed`).
- Headline theorems stay **axiom-clean** (`propext`/`Classical.choice`/`Quot.sound`
  only); `#print axioms` is the audit of record.
- Commit at each green checkpoint.

---

## 7. Open questions (for the human, only when load-bearing)

1. `elaborateSafe` → rename to `typecheckSafe`/`checkSafe`? (API/CLI-facing name; the
   `fhm` CLI's `--stage elaborate` label also says "elaborate".) Cosmetic; defer.
2. Is CBN `let` genuinely load-bearing for any existing Example, or can we freely go
   full-CBV in a later, separate change? (D2 says preserve for now; this is a
   follow-up decision, not a blocker.)

---

## 8. References

- Aydemir, Charguéraud, Pierce, Pollack, Weirich — *Engineering Formal Metatheory*,
  POPL 2008 (the locally-nameless framework; its mini-ML eval is the reference
  environment-machine metatheory we're adopting).
- Charguéraud — *The locally nameless representation*, JAR 2012 (Coq sources:
  `formalmetacoq` `ln/ML_*`).
- Garrigue — *A Certified Interpreter for ML with Structural Polymorphism and
  Recursive Types*, MSCS 2014 (certint; the closest comparable certified HM+recursion
  development — environment-based, type-erasing).
- Crary, Weirich, Morrisett — *Intensional Polymorphism in Type-Erasure Semantics*,
  JFP 2002 (the erasure-semantics framing).
- Leroy — *Compilation of extended recursion in CBV functional languages*; and the
  Ariola–Blom / Nordlander–Carlsson–Gill / Scherer–Yallop line (rec-as-environment
  operational semantics — what the CEK machine's `letRec` handling is).
- Pottier — *Hindley–Milner Elaboration in Applicative Style*, ICFP 2014 (documents
  that "elaboration … has received relatively little attention"; its constraint-based
  answer is what we are deliberately NOT doing).
