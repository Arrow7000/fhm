# Next-agent brief: Path R dual-stack metatheory

**Status:** Active (2026-08-12). Read this first when resuming FHM dual-stack / InferW work.  
**Authoritative product packaging:** `design-memo-bounds-preserving-elaboration.md`  
**This brief:** formalization *choice* Path R, WIP state, proof order, do-nots.

---

## 0. Where we are (2026-08-12, later) — start here

### ✅ Path R residual soundness is CLOSED, both stacks, axiom-clean

```text
Infer.sound                InferBranches.sound                InferRecGroup.sound
Infer.sourceSound          InferBranches.sourceSound          InferRecGroup.sourceSound
TypeOfHM.letRec_of_emptyPool
```

All seven verified `[propext, Classical.choice, Quot.sound]` — **no `sorryAx`**.
`FHM/InferW.lean` and `FHM/Headlines.lean` both compile.

Verify with:

```bash
lake build FHM.InferW            # 0 errors; only "declaration uses 'sorry'" warnings
lake env lean FHM/Headlines.lean # 0 errors; §6 guard prints the axiom status
```

### ⚠️ Correction to the previous version of this brief

The previous §0 said “one sorry left for residual soundness”. **That was wrong
in both directions**, and cost a session to discover:

* `HEAD` (`2020f3d`) **did not compile** — ~30 errors: `maxRecDepth` in both
  mutual blocks, a stray `/--` docstring attached to no declaration, and proof
  bodies in `letIn` / `letInAnn` / `consPoly` that had **never been checked**.
* Two “theorems” were **false statements** with `sorry` bodies, and two more
  were `: True` placeholders. Neither is “work remaining”; both are noise that
  reads as work.

**Rule added: never commit a checkpoint that does not compile.** A broken
checkpoint plus an optimistic brief is worse than no checkpoint — the next
agent trusts the brief and debugs the wrong thing. If you must checkpoint WIP,
say `DOES NOT COMPILE: <n> errors` in the commit subject.

### What landed this session

```text
5a0c65c Repair residual sourceSound letIn/letInAnn and RecGroup consPoly.  (21 errors -> 0)
239919e Add TypeOfHM.letRec_of_emptyPool: source rebuild of letRec at shared pool.
17ccfca Close residual Infer.sourceSound letRec; Path R soundness is complete.
054e0d8 Delete false greatest_K lemmas, their dead callers, and two vacuous stubs.
320d0fd Make the Headlines facade honest, and fix its one real error.
```

Key new lemma — **`TypeOfHM.letRec_of_emptyPool`** (just above the `sourceSound`
mutual). `Expr.letRecElab_sound` types the elaboratum, whose inner group sits at
the EMPTY pool with pool-`G` generalisation in the outer `letIn` wrappers. The
source node has no such nest: `TypeOfHM.letRec` wants cofinite
`MonoTyped`/`PolyTyped` at the shared opening `G ↦ Xs` with monotypes renamed.
Since `Ty.renameG G Xs τ` **is** `Ty.substFvars (G.zip (Xs.map Ty.fvar)) τ`, the
gap is one `TypeOfHM.onSubst_fixed` transport, given `G` avoids the ambient env,
the annotated schemes, and the bindings' annotations — exactly the
`genGroupVars` side conditions `Infer.sound`'s scaffolding already proves.

The three `sourceSound` theorems share ONE mutual block, so they cleared
`sorryAx` **together** when `letRec` closed. Do not read any one of them as done
while another has a sorry.

### Honest sorry inventory (41 declarations in InferW, 3 in Headlines, 3 in SurfaceBridge)

Exact, from the compiler's warning count (41 in InferW), not from grepping `sorry`:

| Group | Count | Verdict |
|-------|-------|---------|
| `CompleteAt`-shaped `Infer.complete_*` (incl. Branches/RecGroup) | 22 | real campaign, see §5 |
| `complete'` / `output_unique` / `isPrincipal` / `iff_typeable` | 4 | real campaign |
| ~~Headline demos (`*_headlines_fire`)~~ | 0 | ✅ **proved** (`6fe8340`), all four axiom-clean |
| PhaseC-C2 executable bridge (`inferCore_complete_*`) | 6 | blocked on completeness |
| OptionA residual unify (`UnifyRel.complete_aux`, `complete_K_aux`, `unifyCoreK_complete_aux`) | 3 | blocked on completeness |
| `principalType_principal` / `principalType_iff` | 2 | blocked on completeness |
| ~~`appFiveFive_untypeable` / `openMisuse_untypeable`~~ | 0 | ✅ proved (`8a076ff`), axiom-clean |
| Operational bridge (`Headlines.lean`: `runSafe`, preservation, progress) | 3 | separate axis |
| `SurfaceBridge.lean` (`surface_type_safe`, `..._of_SurfaceWT`, `program_type_safe`) | 3 | why `elaborateSafe` shows `sorryAx` |

### ✅ Completeness statement-repair pass — DONE (2026-08-12, later still)

The repair landed. **Decision: principality is stated UP TO ERASURE, unrestricted.**
Full rationale in `design-memo-bounds-preserving-elaboration.md` **§4.1.2**; read
that before farming. Summary and the three machine-checked facts behind it:

| Fact | Statement | Status |
|---|---|---|
| 1 | `τ₀ = R.onTy τ` is false: `Subst.onTy_bl` keeps a `bl` head stable under every substitution | ✅ proved, axiom-clean |
| 2 | Decoration lifting is false: `σ = List Int` rigid, `τ₀ = bl 3 5 Int` erases into it but no `R'` lifts back | ✅ proved |
| 3 | An erase-normal ctx + a **zero-annotation** term still derives `BL 3 5 Int → BL 3 5 Int` | ✅ proved |

Fact 3 is the decisive one: `TypeOfHM.var` (`Core.lean:3369`) is decoration-blind
— it ignores stored `tyArgs` and instantiates at an **existential** `instArgs`
constrained only by `IsLC`, which does not exclude `bl`. Same for `ctor` and
match-branch `tyArgs`. So "erased ctx + erased term ⟹ erase-normal `τ₀`" is
**false**, and `hnorm : Ty.eraseBounds τ₀ = τ₀` is a *real* restriction. It must
therefore NOT sit on the engine.

Fact 2 kills the repair the previous brief proposed (`τ₀ = R.onTy (Ty.eraseBounds τ)`):
it is unreachable from `FactorsHM`, which delivers only erase-level equality for
every `τ`. Recovering exact equality needs an alignment invariant ("every `bl` in
`τ₀` sits at a variable position of `τ`") threaded through all ~34 goals as a
strengthened IH, for zero product value.

**Statement discipline now in the file:**

```text
core   CompleteAt, complete', complete, complete_*_aux, output_unique,
       IsPrincipal.principal, principalType_principal, typecheck_principal
         ⊢ AgreesHM τ₀ (R.onTy τ)              -- unrestricted, no new hypothesis

exact  complete_instance, complete_id, principal
         hnorm : Ty.eraseBounds τ₀ = τ₀
         ⊢ τ₀ = Ty.eraseBounds (R.onTy τ)
```

`AgreesHM` (`InferW:864`) is this file's own name for "same HM shape" — the exact
relation unification is proved to respect — and it composes through the induction
via `Ty.eraseBounds_onTy_congr`, the pattern already used in
`UnifyRel.greatest_K_factors`. This is not a hedge: Infer unifies bounds-blind, so
demanding structural principality demands principality in a lattice Infer
deliberately does not observe.

`InferBranches.complete` / `InferRecGroup.complete` needed **no** repair — they
carry substitution-agreement clauses only, no type equation.

**The four `*_headlines_fire` demos keep EXACT equality and are unblocked.**
Their terms carry no `bl`, so `τ` is erase-normal *and* all-variable (`polyId` ⇒
`.fvar 0 → .fvar 0`) and every agreeing `τ₀` is a real instance. Like
`appFiveFive_untypeable`, each is a direct `TypeOfHM` inversion on a tiny closed
term — **prove them standalone and early; they do not need `complete'`.**

**Existence is still the easy half** and is very likely true: `Infer` unifies
bounds-blind, so it accepts strictly more than structural `TypeOfHM` and cannot
reject what the erased term types.

### Next farm (in order)

1. ~~`appFiveFive_untypeable` / `openMisuse_untypeable`~~ ✅ done (`8a076ff`).
2. ~~Repair the completeness statements~~ ✅ done (`948cb12`) — see the repair
   section above and design memo §4.1.2.
3. ~~The four `*_headlines_fire` demos~~ ✅ **done** (`6fe8340`), all axiom-clean.
   They were listed as blocked on completeness; they never were. Computed
   principal types, for reference:

   | term | `principalType [] X` |
   |---|---|
   | `polyId` | `.arrow (.fvar 0) (.fvar 0)` |
   | `idid` | `.arrow (.fvar 4) (.fvar 4)` |
   | `matchWild` | `.arrow (.fvar 0) (.prim .int)` |
   | `mutualRec` | `.fvar 3` — a **bare** type variable |

   All erase-normal with no `List`/`bl` rigid structure, which is why exact
   equality (not `AgreesHM`) is correct in these four specifically.

   **Reusable lesson — evaluating `inferCore` in a proof is the hard part, not the
   proof.** `inferCore`/`unifyCoreK`/`inferBranchesCore`/`inferRecGroupCore` are
   well-founded, so `rfl`, `decide`, `unseal`, `conv => whnf` and
   `with_unfolding_all rfl` all stall; `Ty` has no `DecidableEq`, so
   `decide`/`native_decide` are not even typeable. Recipe that works:
   (1) `show` the goal with the literal rigid set / frontier (`tyFreeVars`,
   `freshFloor`); (2) `simp only` with the WF **equation lemmas** — they fire
   because every recursive call sits at a syntactically concrete `Expr`;
   (3) `unfold unifyCoreK` once per unification depth (its arguments are bound by
   enclosing `match`es, so its equations cannot fire); (4) `with_unfolding_all rfl`.
   Each `*_principalType` needs `set_option maxRecDepth 100_000 in`.

   New reusable lemma: `AuditCapstone.instBy_eq_of_lc` — instantiation is the
   identity on a locally-closed body (converse of `InstantiatesBy.refl_of_closed`;
   the `eq_of_closed` named in a `Core.lean` comment does **not** exist).
4. Then farm bottom-up: `UnifyRel.complete_*` → `Infer.complete_*` → `complete'` →
   `completeAt`/`complete`/`principal`/`iff_typeable` → PhaseC-C2.
   Every one of these now concludes `AgreesHM`, so the induction never needs to
   recover exact equality — do not reintroduce a structural pin.
5. Operational bridge (`runSafe`) — independent axis, can go in parallel.

### Sequential-edit rule

**Do not edit Core and InferW in parallel** (InferW reloads after Core). Farm one file at a time. Core is currently stable for residual work.

### Do not re-prove (false under Path R)

- `Unifies` ⇒ structural tree equality  
- `FactorsHM.to_structural` (deleted)  
- Structural `UnifyRel.greatest` / `greatest_lc` — use `*_factors` / `FactorsHM` only  
- Structural `UnifyRel.greatest_K` / `UnifyRelList.greatest_K` — **deleted** (`054e0d8`).
  They had survived an earlier purge by keeping their plain names instead of a
  `_FALSE` suffix, and carried `exact False.elim (by sorry)`, which made their
  callers *look* proved while resting on `False`. Use `*_greatest_K_factors`.
- `customTy_unify_dodge` / `customTy_factor_dodge` — **deleted** with them; restate
  residually on `greatest_K_factors` when branch completeness needs them
  (`customTy_dodge_unifier` is still live and reusable)  
- Intentionally unprovable `*_structural_FALSE` theorems were **deleted**; comments remain  

**Hygiene rule.** A false statement with a `sorry` body is not a TODO — it is a
trap, because everything downstream of it typechecks. If a statement turns out
false under Path R, **delete it** and leave a comment saying what replaced it.
Same for `: True` placeholders: they assert nothing while counting as work.
Audit with `#print axioms`, not by grepping for `sorry`.

---

## 1. Product vision (unchanged)

Dual stack is real — not top-level-only sidecar:

1. **Lower** keeps BL on Core types / binder anns (including nested).
2. **InferW** is pure HM for *shape*: bounds-blind unify (`BL` ≡ bare `List` for unify only); never invents `lo`/`hi`; copies user BL anns through; empty slots → bare List.
3. **Bounds pass** (later product) synth/checks lengths; rewrites bare `List` → tight `BL`; user BL is demand.
4. **Pipeline never uses erase as packaging.** `eraseProgram` / `ofLower` are deprecated; Live may still run them — **do not** keep Live green at the expense of honest metatheory. Live can break.

Erase is a **function / theorem projection**, not a pipeline mutate step that destroys nested BL.

---

## 2. Path R vs Path B (locked: **Path R**)

| | **Path R (chosen)** | Path B (rejected for TypeOf) |
|--|---------------------|------------------------------|
| `TypeOf*` | Golden pure HM: **structural** pins, **no** BL ≡ List | TypeOf itself bounds-blind |
| Infer | Dirty: bounds-blind unify; keeps BL on elaboratum | Same executable story |
| Infer ⇒ TypeOf | **Residual bridge** after erase | More direct on same trees |

**Path R residual elaboratum soundness:**

```text
Infer … e ↝ eOut, τ
  ⇒  TypeOfElabHM
        (S.onCtx ctx).eraseBounds
        (eOut.substTyFvars S).eraseBounds
        (Ty.eraseBounds τ)
```

**Source soundness:**

```text
  ⇒  TypeOfHM (S.onCtx ctx).eraseBounds e.eraseBounds (Ty.eraseBounds τ)
```

**Why erase the term too:** structural Pins mean a binder ann `: BL …` forces the rule-internal type to be that BL tree. Pure TypeOf cannot treat “ann says BL, HM shape is List” the way Infer can. Residual TypeOf judges the **erase-projected** elaboratum/source.

**Why erase CtorEnv too:** structural `InstantiatesBy` has no BL→List rule. Residual `TypeOf*` needs erased ctor field templates. `Ctx.eraseBounds` projects env **and** ctors (`CtorEnv.eraseBounds`).

**Ann preservation is separate** (product honesty), not residual TypeOf:

- Real semi-elaborated AST still carries BL for the bounds pass.
- Theorems: `Expr.UserAnnsCopied` / `Infer.preservesAnns` (proved).
- `UserAnnsCopied.letRec`: group **anns** + body only (bindings not full zip after subst/close — same as let RHS).

**Quotients:** moral quotient via `eraseBounds` / `AgreesHM` only. Do **not** introduce Lean `Quot Ty`.

---

## 3. Code map

| Piece | Location | Status |
|-------|----------|--------|
| `Ty`/`PolyTy`/`Expr`/`Env`/`Ctor`/`CtorEnv`/`Ctx.eraseBounds` | `FHM/Core.lean` | ✅ |
| Structural `Option.Pins` | `FHM/Core.lean` | ✅ |
| `AgreesHM` / `Unifies` / `FactorsHM` / `UnifyRel.*_factors` | `FHM/InferW.lean` | ✅ |
| Residual `Infer.sound` mutual | `FHM/InferW.lean` ~9128+ | ✅ proved |
| Residual `sourceSound` mutual | `FHM/InferW.lean` | ✅ proved (one mutual — all three clear together) |
| `TypeOfHM.letRec_of_emptyPool` | `FHM/InferW.lean`, just above that mutual | ✅ proved |
| `UserAnnsCopied` / `Infer.preservesAnns` | `FHM/InferW.lean` | ✅ |
| Packing / eraseBounds_of / onSubst residual | `FHM/InferW.lean` | ✅ |
| Completeness residual hyps | `FHM/InferW.lean` | ⚠️ **statements need repair** (see §0) |
| Residual `WellTyped` / runSafe | `FHM/Headlines.lean` | deferred (ops bridge, 3 sorries) |
| `surface_type_safe` / `program_type_safe` | `FHM/SurfaceBridge.lean` | deferred — why `elaborateSafe` shows `sorryAx` |
| Product architecture | `briefs/design-memo-bounds-preserving-elaboration.md` | — |

`Headlines.lean` is **not** in `lakefile.toml`, so `lake build` never elaborates
it. Check it explicitly or errors there go unseen (one had, for a while).

```bash
rg -n "sorry -- PathR$|PathR completeness" FHM/InferW.lean
rg -n "theorem Infer\.sourceSound|theorem Infer\.sound " FHM/InferW.lean
lake build FHM.InferW 2>&1 | grep -c "declaration uses 'sorry'"   # authoritative count
lake env lean FHM/Headlines.lean                                   # facade + axiom guard
```

Do **not** count sorries with `grep -c sorry` — several explanatory comments
now contain the word. Use the compiler's warning count above.

---

## 4. Infer elaboratum shapes (ann / packing)

| Infer rule | elaboratum head |
|------------|-----------------|
| `lambda` | `.lambda ann bodyOut` (same `ann`) |
| `letIn` none | `.letIn (some genScheme) (closeTyVars …) bodyOut` |
| `letInAnn` | `.letIn (some σ) (closeTyVars …) bodyOut` |
| **`letRec`** | **`Expr.letRecElab G anns …`** — **not** bare `.letRec` as `eOut` |

Source soundness types the **source** `.letRec` after erase, not the elaboratum nest.

---

## 5. Proof farm order

### Residual soundness — **COMPLETE**

1. ~~Core eraseBounds termination~~ ✅  
2. ~~Erase commute~~ ✅  
3. ~~`TypeOf*.eraseBounds_of` / onSubst / packing / preservesAnns~~ ✅  
4. ~~`Infer.sound` mutual~~ ✅  
5. ~~`TypeOfHM.letRec_of_emptyPool`~~ ✅  
6. ~~`Infer.sourceSound` letRec~~ ✅ — whole `sourceSound` mutual axiom-clean  

Nothing left here. **You are now in §5's completeness track — but read the
statement-repair warning in §0 before proving anything.**

### Defer

**Completeness** — residual-shaped statements; large separate campaign after soundness.

**Operational bridge** (`runSafe`, residual `WellTyped` vs `Step` on decorated terms) — Headlines; not part of Infer residual farm.

**Product Live ofLower** — after metatheory stable.

---

## 6. Strategy notes that worked (for the next agent)

- **Scaffolding** for residual proofs mirrors structural Infer.sound: K, frontier, LC, BelowFvars, `eOut_avoid`, `dom_avoid`, then residual TypeOf rebuild.
- **`UnifyRel.unifies`** only gives **erase-equality** (`AgreesHM`), never tree equality.
- **Match / branches (elaboratum):** residual `BranchCtorSpec` via `CtorEnv.eraseBounds_get?` + `InstantiatesBy.forall2_eraseBounds`.
- **letRec elaboratum sound:** residual mono/poly from `InferRecGroup.sound` → `Expr.letRecElab_sound` at **erased ctx** → `Expr.eraseBounds_letRecElab`.
- **letRec sourceSound (done):** `TypeOfHM.letRec_of_emptyPool` on **source** erased bindings + `InferRecGroup.sourceSound`. ~400 lines of `Infer.sound`'s scaffolding port **verbatim** — none of it depends on elaboratum vs source.
- Farm **one case at a time** when context is large; commit checkpoints often — **but only compiling ones**.
- **No vacuous `True` theorem statements.** No false statements with `sorry` bodies either (see §0's hygiene rule).

### What worked well for delegating (2026-08-12)

- **Isolate the one new idea into a standalone helper first.** `letRec` looked
  like a 500-line monster; factoring out `TypeOfHM.letRec_of_emptyPool` (the
  renaming transport) left the big case as pure mechanical porting, and both
  halves went first-time-ish.
- **Write the statement yourself, farm the proof.** Every failure this session
  traced to a wrong *statement*, never a wrong proof.
- **Give the subagent the working twin's location.** "`Infer.sound`'s letRec case
  is your template, lines X–Y, and here are the six places it differs" is worth
  more than any amount of tactic advice.
- **Point proof subagents at `lean-lsp` MCP, not `lake build`.** A full build of
  `InferW.lean` is ~60s; `lean_diagnostic_messages` / `lean_goal` are far faster.
  Warn them the first call has a slow cold start so they don't retry in a loop.
- **Verify with `#print axioms`, independently.** Do not take a subagent's
  "0 errors" on trust; several theorems live in `namespace AuditCapstone`, so
  qualify the names.

---

## 6.1 Documentation policy (do not multiply)

**Read for new sessions (only these):**

1. **This brief** — Path R formalization + proof order + checklist  
2. **`design-memo-bounds-preserving-elaboration.md`** — product dual-stack packaging  

Prefer updating *this* brief over creating `next-agent-brief-path-r-part-2.md`.

---

## 7. Work style (project convention)

- Orchestrator writes **defs / inductives / theorem statements**; leave `sorry`.  
- Proof subagents discharge proofs (and termination).  
- If unprovable as stated → report; orchestrator restates.  
- Prefer **lean-lsp** diagnostics; `lake build` for full targets.  
- Do not fill main context with proof grit.  
- **Sequential Core then InferW** (no parallel edits).

---

## 8. Session principles (user)

- Dual stack was betrayed by top-bindings-only packaging — never again.  
- Principled metatheory first; no superficial Live-preserving cheats.  
- TypeOf stays pure HM (Path R); Infer accounts for BL-world; residual bridge is honest tax.  

---

## 9. One-paragraph resume prompt

> Continue Path R dual-stack metatheory in FHM. Read `briefs/next-agent-brief-path-r-dual-stack.md` §0 first, and **verify its claims before trusting them** (`lake build FHM.InferW` — expect 0 errors / 41 sorry warnings; `lake env lean FHM/Headlines.lean` — expect 0 errors). Residual soundness is **CLOSED**: all six `Infer.*sound*` theorems plus `TypeOfHM.letRec_of_emptyPool` are axiom-clean, as are both `*_untypeable` demos. **The completeness statement-repair pass is also DONE** (`948cb12`): principality is now stated **up to erasure** — core theorems conclude `AgreesHM τ₀ (R.onTy τ)` unrestricted, and exact equality is a corollary under `hnorm : Ty.eraseBounds τ₀ = τ₀`. Read design memo **§4.1.2** for the three machine-checked facts behind that decision; the short version is that `TypeOfHM.var` is decoration-blind (existential `instArgs`), so `bl`-carrying `τ₀` is derivable even from an erase-normal ctx and an unannotated term, which makes "erase-normal" a real restriction that must not sit on the engine — and `FactorsHM` only ever gives erase-level equality, so exact pins are unreachable anyway. The four `*_headlines_fire` demos are also **proved and axiom-clean** (`6fe8340`) — the product headline is non-vacuous. **Your job is the remaining farm:** bottom-up from `UnifyRel.complete_*` → `Infer.complete_*` → `complete'` → `completeAt`/`complete`/`principal`/`iff_typeable` → PhaseC-C2. 37 sorries left in InferW; see §0 for the exact per-group inventory, and §5 for the `inferCore`-evaluation recipe the demos established. Then go bottom-up: `UnifyRel.complete_*` → `Infer.complete_*` → `complete'` → `completeAt`/`complete`/`principal`/`iff_typeable` → PhaseC-C2. Do not reintroduce a structural MGU pin anywhere. Existence is the easy half (Infer is bounds-blind, so it accepts strictly more than structural `TypeOfHM`). Structural Pins; residual TypeOf via `eraseBounds` on ctx (incl. CtorEnv)/term/result. Live ofLower out of scope. Never commit a checkpoint that does not compile.

---

## 10. Related greps

```bash
# authoritative sorry count (grep -c sorry now over-counts: explanatory comments
# mention the word). touch first, or lake caches away the warnings.
touch FHM/InferW.lean && lake build FHM.InferW 2>&1 | grep -c "declaration uses 'sorry'"

rg -n "sorry -- PathR$|PathR completeness|OptionA residual|PhaseC-C2" FHM/InferW.lean
rg -n "theorem Infer\.(sound|sourceSound) |theorem InferBranches\.(sound|sourceSound)|theorem InferRecGroup\.(sound|sourceSound)" FHM/InferW.lean
rg -n "theorem Infer\.complete'|theorem Infer\.principal|theorem Infer\.isPrincipal" FHM/InferW.lean
rg -n "FactorsHM.to_structural|structural residual factoring" FHM/InferW.lean
rg -n "letRec_of_emptyPool" FHM/InferW.lean
```

Axiom audit (note the `AuditCapstone` namespace on the demo theorems):

```bash
cat > /tmp/ax.lean <<'EOF'
import FHM.InferW
#print axioms Infer.sound
#print axioms Infer.sourceSound
#print axioms InferBranches.sourceSound
#print axioms InferRecGroup.sourceSound
#print axioms TypeOfHM.letRec_of_emptyPool
#print axioms AuditCapstone.appFiveFive_untypeable
#print axioms AuditCapstone.openMisuse_untypeable
EOF
lake env lean /tmp/ax.lean   # all should be [propext, Classical.choice, Quot.sound]
```
