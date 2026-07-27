# Design memo: collapse BLSketch oracle axioms onto the Z3 layer

**Status:** proposal (not implemented)  
**Date:** 2026-07-27  
**Scope:** `FHM/BLSketch.lean` oracle interface + `FHM/Z3/Oracle.lean`  
**Related:** uniqueness leaving declarative `TypeOf`/`Check` (see below); dual-stack HM+bounds merge investigation

---

## 1. Problem

Today the bound layer trusts **six** project axioms:

| Layer | Axioms | What they say |
|-------|--------|----------------|
| **Z3** (`FHM/Z3/Oracle.lean`) | `decide_verified_sound` | `decide q = .verified` ⇒ goal holds under assumptions (∀ mode, no unknowns) |
| | `decide_witness_sound` | `decide q = .witness b` ⇒ goal holds under binding `b` |
| | `decide_sat_sound` | `decideSat as = .sat b` ⇒ assumptions sat |
| **BLSketch** (`FHM/BLSketch.lean`) | `checkValid_sound` | `checkValid φ = .valid` ⇒ `φ.Valid` |
| | `solve_sound` | `solve ψ = .witness σ` ⇒ `ψ.SolvedBy σ` |
| | `unique_sound` | `unique ψ outs = .unique` ⇒ `ψ.UniqueOutputs outs` |

The Z3 layer already has the irreducible trust root: `opaque z3Run` (subprocess IO via `@[implemented_by]`) plus “positive solver answers are correct.”

The BLSketch triple is **not** a second independent TCB about arithmetic. It is a **second opacity boundary**:

```text
ForallProblem / ExistsProblem
        │
        │  pure Lean: Z3Bridge.checkValidZ3 / solveZ3 / uniqueZ3
        │  (countToExpr, constraintToAtom, modelToAssign, multi-goal loops)
        ▼
   decide / decideGoals          ← pure Lean on top of z3Run
        │
        │  axioms decide_*_sound
        ▼
   semantic Holds on Z3 atoms
```

…but then BLSketch re-wraps the pure bridge as:

```text
@[implemented_by checkValidImpl]
opaque checkValid : ForallProblem → ValidVerdict

axiom checkValid_sound : checkValid φ = .valid → φ.Valid
```

Because `checkValid` / `solve` / `unique` are **opaque**, Lean cannot unfold them to the bridge and **cannot** derive the BLSketch axioms from the Z3 ones. The three BL axioms restate, at problem-language level, what should be **theorems** about pure wrappers over `decide`.

**Goal of this task:** delete the three BLSketch axioms; keep (at most) the three Z3 axioms; prove everything BLSketch needs as lemmas.

---

## 2. What “everything we use them for today” actually is

### 2.1 Used in declarative typing / soundness

| Premise shape | Where | Relies on |
|---------------|--------|-----------|
| `checkValid φ = .valid` | `Sub.bl`, `matchNil`, `matchCons`, inhabit-style side conditions | **`checkValid_sound`** (or a proved replacement) if anyone opens `φ.Valid` — today `Sub` only stores the *equality* `= .valid`; semantic `Valid` is for future/meta use |
| `solve ψ = .witness σ` | TypeOf `*Infer` rules, Check `ofInfer` / `nilInfer` | **`solve_sound`** if relating to `SolvedBy`; today σ is mostly existential noise in the inductive |
| `unique ψ outs = .unique` | **algo only** (`forceSubtype`; dropped from TypeOf/Check in `2426eb1`) | **`unique_sound`** — kept for algo policy; **never applied in any proof yet** |

So today, `synth_sound` / `check_sound` never *invoke* `checkValid_sound` / `solve_sound` / `unique_sound`. They only re-package oracle *equalities* into inductive constructors. The axioms are TCB surface area for a future semantic reading of typing, not for the current algorithmic soundness ladder.

That does **not** make collapse pointless: any theorem that says “typed ⇒ arithmetic obligation holds” must eventually open `Valid` / `SolvedBy`, and that step needs either axioms or proved bridges.

### 2.2 Semantic targets (what the proved lemmas must say)

```lean
-- already defined in BLSketch
def ForallProblem.Valid (φ) : Prop :=
  ∀ σ, (∀ c ∈ φ.prem, c.Holds σ) → (∀ g ∈ φ.goals, g.Holds σ)

def ExistsProblem.SolvedBy (ψ) (σ : Assign) : Prop :=
  (∀ c ∈ ψ.prem ++ ψ.cons, c.Holds σ)  -- plus inferable-domain discipline as defined
  -- (exact field names per current defs)

def ExistsProblem.UniqueOutputs (ψ) (outs : List Count) : Prop :=
  ∀ σ τ, ψ.SolvedBy σ → ψ.SolvedBy τ → sameOutputs outs σ τ
```

Target theorems (names illustrative):

```lean
theorem checkValid_sound' (φ : ForallProblem) :
    checkValid φ = .valid → φ.Valid

theorem solve_sound' (ψ : ExistsProblem) (σ : Assign) :
    solve ψ = .witness σ → ψ.SolvedBy σ

-- unique: see §4 — do NOT aim for a free corollary of positive-only Z3 axioms
```

---

## 3. Design: make the bridge definitional, prove the rest

### 3.1 Remove the second opacity layer

**Today:**

```lean
@[implemented_by checkValidImpl]
opaque checkValid : ForallProblem → ValidVerdict
```

**Proposed:**

```lean
def checkValid (φ : ForallProblem) : ValidVerdict :=
  Z3Bridge.checkValidZ3 φ

def solve (ψ : ExistsProblem) : SolveVerdict :=
  Z3Bridge.solveZ3 ψ

-- unique: keep only if algo still wants it; prefer def not opaque (see §4)
def unique (ψ : ExistsProblem) (outs : List Count) : UniqueVerdict :=
  Z3Bridge.uniqueZ3 ψ outs
```

Runtime behaviour stays the same: `checkValidZ3` already calls pure `decide` / `decideGoals`, which call `opaque z3Run`. **One** IO fiction is enough.

Delete:

- `checkValidImpl` / `solveImpl` / `uniqueImpl` (or keep as thin aliases during transition)
- `axiom checkValid_sound` / `solve_sound` / `unique_sound`
- optionally the `@[implemented_by]` on the BL triple entirely

### 3.2 Prove encoding / evaluation correspondence

Core lemma family (sketch):

| Lemma | Content |
|-------|---------|
| `countToExpr_eval` | Under assignment `σ : Assign` and `ρ : Z3.Assignment` with `ρ (varName v) = σ v` for all mentioned vars, `Count.eval c σ = Z3.Expr.eval (countToExpr c) ρ` (or whatever eval the Z3 AST uses in `Atom.Holds`) |
| `constraintToAtom_holds` | `Constraint.Holds c σ ↔ Atom.Holds (constraintToAtom c) ρ` under the same name agreement |
| `constraintsToAssumptions_holds` | list version for prem/cons |
| `modelToAssign_agrees` | for keys present in the model, `modelToAssign b v =` looked-up value; document default-`0` for missing keys and prove solve only relies on bound inferables |

These are ordinary structural inductions on `Count` / lists — no SMT reasoning.

### 3.3 Prove `checkValid_sound'` from `decide_verified_sound`

`checkValidZ3` (current shape):

- empty goals → `.valid` (trivial theorem: empty goal list ⇒ `Valid`)
- else map each goal to `decide { assumptions := premAtoms, goal := g }`
- `.valid` only if **every** goal returns `.verified` (and none refuted)

Proof outline:

1. Assume `checkValid φ = .valid`.
2. For each goal `g ∈ φ.goals`, `decide q_g = .verified` with `q_g.unknowns = []`.
3. Apply `decide_verified_sound` ⇒ ∀ρ, assumptions hold → goal atom holds.
4. Transport along encoding lemmas to `Constraint.Holds` / `Assign`.
5. Package as `φ.Valid`.

Multi-goal is just finite conjunction; no new axiom.

### 3.4 Prove `solve_sound'` from `decide_witness_sound`

`solveZ3` uses `decideGoals unknowns as goals` and maps `.witness b` through `modelToAssign`.

Proof outline:

1. Empty unknowns + empty goals → trivial witness (already special-cased).
2. `.witness b` from `decideGoals` ⇒ for the bundled ∃∀ query, `decide_witness_sound` (or per-goal consequences — match whatever `decideGoals` actually encodes in `Encode.toWitnessScriptGoals`).
3. Show `modelToAssign b` satisfies all prem/cons under `Constraint.Holds`.
4. Caveat: **name coverage** — every inferable mentioned in the problem must appear in `b` or the default-0 must be proved harmless. This is the fiddliest pure-Lean part.

If `decideGoals` multi-goal witness mode is only justified by a *composition* of single-goal axioms, either:

- prove that composition from `decide_witness_sound` + encoding of the multi-goal script, or  
- if the multi-goal encoding is not obviously a conjunction of single-goal queries, add **one** Z3-level axiom for multi-goal witness and keep the BL layer axiom-free (prefer strengthening the Z3 API surface over reintroducing BL axioms).

Audit `Encode.toWitnessScriptGoals` vs `decide_witness_sound`’s single-`goal` statement carefully in implementation.

### 3.5 `decide_sat_sound`

BLSketch does not currently need it for `checkValid`/`solve`. Keep it on the Z3 layer for other callers; no BL re-export required.

---

## 4. Uniqueness: do not smuggle completeness into the TCB

### 4.1 What `uniqueZ3` actually does

After finding a witness `σ`:

1. Evaluate `outs` under `σ`.
2. For each output count, ask Z3 whether there is **another** model where that count is strictly smaller or larger.
3. If any such alternative witness is found → `.multiple`.
4. Otherwise → `.unique` (including when alternative queries return **unknown**/timeout!).

So `.unique` means:

> “we failed to exhibit a second model with different outs”

not

> “every model agrees on outs” (`UniqueOutputs`)

Positive-only soundness axioms **cannot** justify that implication. Turning “no witness for φ” into “¬Sat φ” is **completeness** (or “timeout ⇒ unsat”), which we deliberately refuse for `checkValid` / `solve` failure cases.

### 4.2 Current axiom is over-strong

```lean
axiom unique_sound …
  unique ψ outs = .unique → ψ.UniqueOutputs outs
```

This is not a restatement of `decide_witness_sound`. It is a new, stronger trust assumption — and today **no proof uses it**.

### 4.3 Recommended disposition (aligned with uniqueness leaving `TypeOf`)

Declarative cleanup **done** (`2426eb1`): no unique premises in TypeOf/Check; `forceSubtype` still gates; **`unique_sound` kept** for algorithmic uniqueness policy (project choice — not deleted despite being unused in proofs today).

| Stage | Uniqueness in TypeOf/Check | `unique` oracle | `unique_sound` |
|-------|----------------------------|-----------------|----------------|
| **Done: declarative cleanup** | No `unique` premises | Keep for algo/`forceSubtype` | **Kept** (algo policy / future theorems) |
| **Axiom collapse PR** | Still no unique in TypeOf | Prefer `def unique := uniqueZ3`; document policy strength honestly | Keep only if still wanted for algo proofs; **not** a free corollary of positive-only Z3 axioms |
| **Future elaborator** | Still no unique in TypeOf | Policy: fail/annotate/chooser when non-unique | Optional theorem under an **explicit** completeness hypothesis — do not treat default Z3 “unique” as full `UniqueOutputs` |

**Do not** prove `unique_sound'` from the three Z3 axioms alone. Either keep the axiom for policy, or later introduce a clearly named hypothesis such as:

```lean
axiom decide_unsat_complete …  -- optional, separate product decision
```

and prove uniqueness only under that flag. Default: **no**.

### 4.4 What declarative typing needs from solve without unique

Existence only:

```lean
-- TypeOf *Infer (illustrative)
subtypeProblem Δ ty' ty = some ψ →
solve ψ = .witness σ →   -- or semantic: ∃ σ, ψ.SolvedBy σ
-- no unique
```

For semantic well-typedness (“obligations hold”), `solve_sound'` (proved from Z3) is enough. Non-unique models remain well-typed; elaborator may still refuse to *commit* a printed/elaborated bound without an annotation.

---

## 5. Target TCB after the task

| Keep (irreducible) | Delete | Prove as lemmas |
|--------------------|--------|-----------------|
| `opaque z3Run` + IO fiction | `opaque checkValid/solve/unique` | encoding eval lemmas |
| `decide_verified_sound` | `checkValid_sound` | `checkValid_sound'` |
| `decide_witness_sound` | `solve_sound` | `solve_sound'` |
| `decide_sat_sound` (optional for BL) | `unique_sound` | — (no replacement) |

Net: **3 Z3 axioms (or 2 if sat unused)**; **0 BLSketch axioms**.

Headlines / docs should say: bound-layer theorems that open `Valid`/`SolvedBy` depend on the Z3 positive-answer axioms; HM Core remains axiom-clean.

---

## 6. Work breakdown (implementation plan)

### Phase A — Uniqueness out of well-typedness (prerequisite / parallel)

**Done** (`2426eb1`). Declarative TypeOf/Check no longer require unique.

1. ~~Drop `unique` premises from TypeOf `*Infer` and Check `ofInfer`/`nilInfer`.~~
2. ~~Repair `weakenCtx`, `synth_sound`, `check_sound` (discard `huniq`).~~
3. Leave `forceSubtype` unique gate as **algo policy** or drop it in a follow-up (open).
4. `unique_sound` **kept** for algo policy (not deleted).

### Phase B — Definitional bridge

1. Change `checkValid`/`solve`/(optional)`unique` from `opaque`+`implemented_by` to `def` = `Z3Bridge.*`.
2. Confirm `#eval` / scratch demos still hit Z3 via `decide`→`z3Run`.
3. Grep for remaining `opaque` at BL layer; should be none for oracles.

### Phase C — Encoding lemmas

1. Pin down Z3 atom semantics (`Atom.Holds`, assignment type) vs `Constraint.Holds` / `Assign`.
2. Prove `countToExpr` / `constraintToAtom` correspondence.
3. Prove list/assumption transport.
4. Prove `modelToAssign` agreement on witness domain.

### Phase D — Bridge soundness theorems

1. `checkValid_sound'` by induction/finite cases on goals + `decide_verified_sound`.
2. `solve_sound'` via `decideGoals` audit + `decide_witness_sound` + model map.
3. Replace any future uses of old axioms with these theorems.
4. Update module docstring / `next-agent-brief-blsketch-z3.md` TCB table.

### Phase E — Hygiene

1. Remove dead `*Impl` unsafe wrappers if unused.
2. Optionally stop exporting `unique` from the trusted surface entirely until elaborator needs it.
3. `#print axioms` on `synth_sound` / future semantic lemmas: expect only Z3 `decide_*` + standard classical axioms.

---

## 7. Risks and open points

1. **Multi-goal witness encoding** may not be a trivial corollary of single-goal `decide_witness_sound`. Budget an Encode audit; worst case add one Z3-level multi-goal axiom rather than a BL-level one.
2. **Default-0 in `modelToAssign`** for missing names can make `solve_sound'` false unless solve queries always return all inferables or SolvedBy only constrains mentioned vars. Fix the model map or the SolvedBy statement.
3. **`checkValid` returning `.valid` on empty goals** must match `Valid` (vacuous goals under prem) — easy, but test.
4. **Proofs that only carried `= .valid` equalities** do not automatically need `Valid`; collapse is still worth it so *semantic* theorems are possible without new axioms.
5. **Do not “fix” uniqueness** by treating unknown as unique. If algo keeps a uniqueness gate, document it as incomplete policy, not as `UniqueOutputs`.

---

## 8. Success criteria

- [ ] Zero axioms in `FHM/BLSketch.lean` (oracle section).
- [ ] `checkValid` / `solve` are ordinary `def`s over `Z3Bridge`.
- [ ] `checkValid_sound'` and `solve_sound'` are theorems whose `#print axioms` ⊆ Z3 `decide_*_sound` (+ propext/choice/Quot as usual).
- [ ] No theorem claims `unique _ = .unique → UniqueOutputs` without an explicit completeness hypothesis (default: no such theorem).
- [ ] Existing `synth_sound` / `check_sound` still hold (with uniqueness already removed from TypeOf, or with algo still stricter).
- [ ] Scratch Z3 demos still run with `z3` on PATH.
- [ ] Briefs/README TCB text updated: bound layer trusts Z3 positives only; uniqueness not in well-typedness.

---

## 9. Non-goals

- Verifying Encode/Parse/Process against SMT-LIB or the `z3` binary.
- Completeness of Z3 (`.invalid`/`.unsat`/`.unknown` ⇒ semantic failure).
- Principality of bounds or unique elaborator commitments.
- Wiring into Core/InferW (independent track).
- Replacing subprocess with libz3 FFI.

---

## 10. One-liner

> Stop re-axiomatising the pure problem-language wrappers: define `checkValid`/`solve` as Lean functions over `decide`, prove soundness from the three Z3 positive-answer axioms via encoding lemmas, and drop uniqueness from the TCB entirely (it was never a corollary of those axioms, and it is leaving declarative typing anyway).
