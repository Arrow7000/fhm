<!-- Written 2026-07-07 as the successor to next-agent-brief-verified-pattern-compilation.md
     (now fully completed — H1, H2, and the internal (X) totality layer are proven,
     axiom-clean, and committed). The verified pattern-compilation campaign's
     behavioural theorem is done; what remains is INTEGRATION with the surface
     bridge. Read these FIRST, in order:
       1. briefs/design-memo-verified-pattern-compilation.md  — the full design
          record, theorem inventory, and status log (the canonical reference).
       2. briefs/next-agent-brief-surface-bridge.md           — the bridge
          campaign (the north star; item 5 = pattern compilation = DONE).
     This brief does NOT duplicate either; it specifies the integration work. -->

# Brief: pattern-compilation integration with the surface bridge

## Where the repo stands (2026-07-07)

The verified pattern-compilation campaign ("Option B") is **complete**.
Eight commits (`a9613c2` … `161325a`), all axiom-clean
`{propext, Classical.choice, Quot.sound}`, full `lake build` green:

- **`FHM/PatComp.lean`** (one file, ~2800 lines) contains the entire campaign:
  - Surface spec: `matchPat` / `firstMatch` (the trusted artefact).
  - Normalisation: `GPat` / `norm` (surface `Pattern` → generic patterns).
  - Pattern matrix: `Row` / `Matrix` / `matrixSem` (Maranget-style).
  - Decision-tree IR: `DTree` / `evalDTree` (the denotational pivot).
  - Compiler: `compile` (leftmost-column algorithm + pop rule).
  - Emitter: `emit` / `lowerMatch` (DTree → Core `Expr`, parametric in branch bodies).
  - **H1**: `compile_correct_surface : evalDTree v (compile [[]] (initMatrix ps)) = firstMatch v ps`.
  - **H2**: `lowerMatch_adequate` — surface picks branch `i` with captures `ws` ⟹
    compiled Core term `⟶*` `(bodies i).substN 0 ws` under real `Step`.
  - **(X) internal**: `compile_surface_total_iff` — tree selects a branch ⟺ surface spec does.
  - `CtorSwitches` / `OccsBound` predicates (structural side conditions for H2).
  - `#guard` test suite at three levels (surface spec, H1, H2 end-to-end) incl.
    a realistic `List`-pattern demo (`cons`/`list` sugar, multi-arg ctor binding,
    two-level nesting).

- **`FHM/Core.lean`** now also contains the **term-level closedness** section
  (folded from the former `ExprClosed.lean`): `Expr.varsBelow`, monotonicity,
  `shiftFrom`/`substN` identity on closed terms, `TypeOfElabHM.varsBelow` /
  `TypeOfElabHM.closed` (well-typed ⟹ all free vars below context length).

- **File discipline**: 9 `.lean` files total (no per-concern proliferation).

**The headline theorem** (`lowerMatch_adequate`) is proven end-to-end, modulo
one explicit hypothesis: `CtorSwitches root t` (every switched occurrence in
the compiled tree fetches a ctor-chain value from the scrutinee). This
hypothesis is a path condition awaiting discharge from scrutinee typing —
that discharge is this brief's primary mission.

## What the bridge needs from us (and what we need from the bridge)

The surface-bridge brief (`next-agent-brief-surface-bridge.md`) is the north
star. Its item 5 (pattern compilation) is **our work, done** — both the
implementation (`lowerMatch`) and the proof (`lowerMatch_adequate`). The
bridge's `Lowers` relation has a `match` case whose soundness obligation *is*
`lowerMatch_adequate`; the bridge agent calls `lowerMatch` and inherits the
proof.

Three integration pieces remain, ordered by dependency:

1. **`CtorSwitches` discharge** (removes the last hypothesis from
   `lowerMatch_adequate`). Needs: the bridge's `CtorEnv` wired in + a
   pattern-well-formedness relation. **This is the keystone.**

2. **`AllMatchesExhaustive` connection** (bridge item 6). Needs: the `CtorEnv`
   + a "surface matrix covers all ctors of `T`" notion. Proves: if the surface
   match is exhaustive, the emitted Core term satisfies `AllMatchesExhaustive`
   (feeding `progress`). Partially available: the emitted term always has a
   trailing wildcard on every `match_` (so `AllMatchesExhaustive`'s "every
   ctor has a branch" condition is trivially met); the remaining work is the
   "every named ctor is in the env" condition + recursive body-exhaustiveness.

3. **`checkExhaustive` checker** (bridge item 6, the decidable side). A
   decidable `CtorEnv → Expr → Bool` with `= true → AllMatchesExhaustive`.
   This is the executable front-end; the integration proof (piece 2) is its
   soundness backbone.

## Dependency check — read this first

**Before starting, check whether the surface bridge exists.** The bridge
campaign (items 1–4 of `next-agent-brief-surface-bridge.md`: surface `DataDecl`
lowering, `Surface.Ty → Core.Ty`, `Surface.Expr → Core.Expr` core, sugar
expansion) is the other agent's workstream. The integration pieces above
genuinely depend on it:

- `CtorSwitches` discharge needs the `CtorEnv` from `elabDecls` (bridge item 1)
  and a pattern-well-formedness relation (bridge item 3/4 territory).
- `AllMatchesExhaustive` connection needs the `CtorEnv` + scrutinee typing.

**If the bridge items 1–4 have landed** → proceed with the integration plan
below.

**If they have NOT landed yet** → two productive options (pick based on what's
most useful):
  (a) Help build the bridge (items 1–2 are the natural starting point —
      surface `DataDecl` + `Surface.Ty` lowering; they're house-style and
      low-risk). Coordinate with the other agent to avoid duplicate work.
  (b) Do standalone prep that doesn't need the bridge: the `DTree.NoFail`
      predicate + `evalDTree_total_of_noFail` forward lemma (dropped during
      the campaign due to `DTree` being a nested inductive — a custom recursor
      or `NoFail`-derivation induction should crack it; see the design memo
      status log for the attempted approaches). This is nice-to-have
      scaffolding for the `AllMatchesExhaustive` connection, not blocking.

## The plan (if the bridge is ready)

Each item is a committable slice. Land them top-to-bottom.

### Step 1: `compile_ctorSwitches` — the keystone

**Target theorem** (stated precisely in the design memo's status log):

```
theorem compile_ctorSwitches
    {ctors : CtorEnv} {root : Expr} {name : TyName} {tyArgs : List Ty}
    (hty : TypeOfElabHM ⟨[], ctors⟩ root (.customTy name tyArgs))
    (hval : IsValue root)
    (ps : List Surface.Pattern)
    (hwf : -- patterns well-formed wrt ctors: every ctor pattern's ctor
           -- is in the env and tests an ADT-typed position) :
    CtorSwitches root (compile [[]] (initMatrix ps))
```

**Proof strategy** (the Core lemmas already exist — no prep needed):
- `TypeOfElabHM.canonical_customTy` (Core ~L7540): `hty` + `hval` ⟹ `IsCtorChain root`.
- `TypeOfElabHM.ctor_chain_inversion` (Core ~L7616): a typed ctor chain `c v₀..vₙ`
  decomposes into `CtorAppliedTo` + `Forall₂` giving each arg's instantiated
  field type. This is the sub-value-typing step.
- Iterate along each switch occurrence: `fetch root occ` follows ctor field
  indices; at each step, `ctor_chain_inversion` gives the arg's type, and if
  that type is a `customTy`, `canonical_customTy` (applied to the arg, which is
  a value from `IsCtorChain`'s args being `IsValue`) gives `IsCtorChain` for
  the sub-value. The `hwf` hypothesis ensures `compile`'s switch occurrences
  only test ADT-typed positions (ctors in the patterns correspond to ADT-typed
  columns).
- The proof is by induction on the compiled tree (or on `compile`'s structure
  via `compile.induct`), discharging the `CtorSwitches.switch` case at each
  node.

**The `hwf` hypothesis** is the bridge-dependent piece. Its exact shape
depends on the bridge's pattern-well-formedness relation (TBD when the bridge
lands). A minimal version: "for every ctor pattern `.ctor c ps` at column
position `k` in the matrix, `c` is in `ctors` and the `k`-th field type of the
scrutinee's ctor at that position is a `customTy`." Refine as the bridge's
`Lowers` relation crystallises.

### Step 2: `AllMatchesExhaustive` connection

Prove: if the surface matrix covers all ctors of the scrutinee's type, the
emitted Core term satisfies `AllMatchesExhaustive` (Core ~L1752).

The emitted term's structure helps: `emit` produces a trailing `wildcard`
branch on every `match_` node, so `AllMatchesExhaustive`'s "every ctor of
`tyName` has a matching branch" condition (condition 4) is always met (the
wildcard matches any ctor). The remaining conditions:
- Condition 3: every `named` ctor in emitted branches is in the `CtorEnv`
  with matching `tyName` — from `hwf` (ctor patterns reference env ctors).
- Condition 2: every branch body is exhaustive — recursive on the tree.
- Condition 1: scrutinee is exhaustive — trivial for `Expr.var`.

This is moderate work; the trailing-wildcard insight makes it significantly
easier than a from-scratch exhaustiveness proof.

### Step 3: `checkExhaustive` checker (bridge item 6)

A decidable `checkExhaustive : CtorEnv → Expr → Bool` with
`checkExhaustive ctors e = true → AllMatchesExhaustive ctors e`. This is the
executable front-end that the bridge's pipeline calls. For compiled matches,
step 2 already proves `AllMatchesExhaustive` holds, so `checkExhaustive`
returns `true` trivially on them — the checker is mainly for hand-written
Core matches (if any) and for the pipeline's error path.

### Step 4: Top-level composition

With `CtorSwitches` discharged (step 1) and `AllMatchesExhaustive` connected
(step 2), the headline theorem becomes **unconditional**:

```
theorem lowerMatch_adequate_unconditional
    {ctors : CtorEnv} {root : Expr} {name : TyName} {tyArgs : List Ty}
    (hty : TypeOfElabHM ⟨[], ctors⟩ root (.customTy name tyArgs))
    (hval : IsValue root)
    (ps : List Surface.Pattern) (bodies : Nat → Expr)
    (hwf : ...) (hexh : ...) :
    ∀ (i : Nat) (ws : List Expr),
      firstMatch root ps = some (i, ws) →
      SmallStep.ReflTransGen SmallStep.Step
        (lowerMatch root ps bodies) ((bodies i).substN 0 ws)
```

This is `lowerMatch_adequate` with the `CtorSwitches` hypothesis removed
(discharged by step 1) and the exhaustiveness hypothesis added (from step 2,
needed for `progress` to fire). It's the final form the bridge consumes.

## Key file locations

| What | Where |
|---|---|
| Pattern-compilation definitions + H1 + H2 + (X) + tests | `FHM/PatComp.lean` |
| Core metatheory + `varsBelow` section + `canonical_customTy` + `ctor_chain_inversion` + `AllMatchesExhaustive` | `FHM/Core.lean` |
| Full design record + theorem inventory + status log | `briefs/design-memo-verified-pattern-compilation.md` |
| Bridge campaign (the north star) | `briefs/next-agent-brief-surface-bridge.md` |
| Surface AST | `FHM/SurfaceLang.lean` |
| Type declarations + `elabDecls` + `CtorEnv` | `FHM/Decls.lean` |

**Key line references in Core.lean** (approximate — verify with `rg`):
- `IsValue` / `IsCtorChain` / `CtorAppliedTo` / `getCtorArgs`: ~L1049–1230
- `AllMatchesExhaustive` / `AllBranchBodiesExhaustive`: ~L1752–1817
- `TypeOfElabHM` (the declarative typing relation): ~L2503
- `canonical_customTy`: ~L7540
- `ctor_chain_inversion`: ~L7616
- `progress` / `type_safety` / `type_safety_star`: ~L7683–9203
- `Expr.varsBelow` (folded from ExprClosed): ~L9390

**Key definitions in PatComp.lean** (verify with `rg`):
- `fetch` / `Occ`: ~L60
- `matchPat` / `firstMatch`: ~L80
- `compile` / `compile.induct`: ~L1100
- `emit` / `lowerMatch`: ~L1400
- `CtorSwitches` / `OccsBound`: ~L2280
- `emit_adequate` / `lowerMatch_adequate`: ~L2650 / ~L2786

## Non-negotiables (from the house rules — restated because they bite)

- Headline theorems stay `sorry`/`admit`/`axiom`-free and axiom-clean
  `{propext, Classical.choice, Quot.sound}`; gate every increment with a
  fresh-olean `lake build` + `#print axioms`.
- **Core stays minimal**: don't add to its metatheory unless genuinely forced.
  The `varsBelow` section is already in Core; the integration lemmas
  (`compile_ctorSwitches` etc.) go in `PatComp.lean` (they bridge PatComp's
  `fetch`/`CtorSwitches` with Core's existing typing — they're new lemmas
  about existing definitions, not new Core rules).
- Don't weaken headline statements; add hypotheses to internal helpers instead.
- Delegate bulk proof-plumbing to subagents with precise per-error specs; keep
  design decisions and the build/axiom gate in the parent. Granular commits
  per slice.
- **File discipline**: no new files without strong justification. The project
  runs on 9 `.lean` files; that's the discipline.
- Append to the design memo's status log as you land things; don't rewrite
  history.
