<!-- Written 2026-07-06 as the §6-step-1 DESIGN MEMO demanded by
     next-agent-brief-verified-pattern-compilation.md ("Option B"). Decisions
     were made in discussion with Aron on 2026-07-06; this memo RECORDS them —
     don't re-litigate here, amend only with new evidence. The implementation
     lives in FHM/PatComp.lean. Status log at the bottom, append-only. -->

# Design memo: behaviourally-verified pattern-match compilation

## 0. Decisions (settled — the "or a justified variant" of the parent brief)

1. **DTree denotational pivot: YES** (parent brief §3, confirmed). Surface spec
   and compiled Core are each given a denotation `value → Option (branch ×
   captures)`; the headline is equality of those functions on well-typed
   values. `DTree` (in `FHM/PatComp.lean`) is Maranget-shaped: `switch` nodes
   carry the tested occurrence explicitly; `leaf`s carry the capture
   occurrence-vector — the single source of truth for binding order.
2. **Leftmost-column, heuristics-free compilation** (kills H0). Plus the **pop
   rule** — see §2, this was *discovered during design* and is load-bearing.
3. **Skip `readback`/H3 entirely.** Adequacy (H2) is stated directly about
   `emit t` by induction on `t`. The round-trip buys generality nobody
   consumes.
4. **`emit` is PARAMETRIC in leaf bodies** (`bodies : Nat → Expr`). Reason:
   `SmallStep.Step` runs on *elaborated* terms (`Infer` decorates var
   `tyArgs`), so the term that actually executes is not literally the lowering
   output. With bodies abstract, H2 applies to elaborated bodies without any
   induction over `Infer`; only a shallow "elaboration preserves the match
   skeleton / branch-pointwise" inversion is ever needed, and only at
   integration time.
5. **Leaf-lets, not renaming.** Each leaf re-binds its captures with nested
   `letIn`s so the body sees capture `j` at de Bruijn `j`; body outer-refs get
   one uniform `shiftFrom`. The headline statement is IDENTICAL under either
   design (it never mentions lets); leaf-lets just collapses the H4 proof from
   "a renaming is correct under n levels of shifting" to "each let projects
   the right var". Cost: a few extra `letReduce` steps at runtime — irrelevant
   for a reference compiler.
6. **Refinement, not bisimulation**: "surface says branch `i` with `vs` ⇒ Core
   multi-steps there". Core's `step_deterministic` (Core.lean ~L1590) upgrades
   this wherever a converse is wanted. Surface-`none` ⇒ stuck is a separate
   (lower-priority) statement.
7. **No surface operational semantics.** Only matching gets independent
   meaning (`matchPat`/`firstMatch` over Core values). Scrutinees are Core
   values by the time a match fires; `matchScrut` congruence stays outside the
   theorem.
8. **Well-typed-scrutinee scoping**: H1/top-level assume the scrutinee is a
   well-typed value of the matched ADT; internal lemmas take whatever
   hypotheses they need, discharged at the top (house rule).
9. **GPat normalisation**: all six surface pattern forms collapse to
   `gctor/gbind/gwild` via `norm` before the matrix machinery; `matchPat`
   (surface-level) stays THE trusted spec, with a factoring theorem
   `matchPat v p = matchG v (norm p)`.
10. **Standalone artifact**: PatComp imports only Core + SurfaceLang. It does
    NOT depend on the Option-A bridge; the bridge's item 5 should later
    *consume* `PatComp.lowerMatch`/`compile`/`emit` (proving its Option-A
    type-preservation obligation over them), so Option B's theorems attach to
    the same code with zero rework — and the pre-order capture convention is
    automatically the convention the bridge's name resolver must target.

## 1. The artifacts (all in `FHM/PatComp.lean`)

- `Occ := List Nat`, `fetch : Expr → Occ → Option Expr` — occurrences (paths
  into ctor-chain values). `[]` = the scrutinee.
- `matchPat / matchPats / matchListPat`, `firstMatch` — the surface spec.
  Captures in **pre-order** (left-to-right occurrence order).
- `GPat`, `norm`, `matchG/matchGs` — normalised patterns + their matcher.
- `Row = {captured : List Occ, pats : List GPat, act : Nat}`, `Matrix`,
  `rowSem`, `matrixSem`, `initMatrix` — the matrix vocabulary. Width invariant
  (`r.pats.length = occs.length`, all rows) is carried by proofs, not types.
- `DTree` (`fail | leaf act binds | switch occ cases default`), `evalDTree`.
- `compile : List Occ → Matrix → DTree` — with `specialize` (`S(c,M)`),
  `defaultMatrix` (`D(M)`), `colHeads`. Termination: lex (`Matrix.ctorCount`,
  column count) — switching always consumes ≥1 `gctor` node (the chosen
  column has one, every case unfolds or drops it; wildcard expansion adds
  none); the pop rule keeps the count and drops a column.
- `emit : (env : List Occ) → (bodies : Nat → Expr) → DTree → Expr` +
  `emitLets`, `resolveOcc`, `lowerMatch`. `env` maps de Bruijn index ↦
  occurrence; a switch's Core `match_` binds the tested ctor's fields at
  `0..a-1` (Core opens bodies with `substN 0 (args.take bindCount)`), so a
  case branch's env is `subOccs occ a ++ env`. The scrutinee is let-bound by
  `lowerMatch` (env starts `[[]]`).

## 2. The pop rule (design discovery — do not remove it)

Naive "switch on the leftmost column *containing a ctor*" BREAKS capture
order. Counterexample: matrix rows `[gwild, gctor C []] / [gbind, gbind]` —
the switch is forced by column 1; if the second row's column-1 `gbind` is
captured at switch time, its capture precedes the column-0 capture, violating
pre-order (surface expects `[occ₀, occ₁]`).

Fix: when column 0 is all-irrefutable (`colHeads M = []`), **consume it**
(`defaultMatrix` doubles as this pop) without emitting a tree node. Columns
are then resolved strictly left-to-right, every `gbind` is consumed exactly
when its column is leftmost, and appending to `Row.captured` yields pre-order
by construction. This is why `Row.captured` can be a plain list with no slot
indices. The executable `#guard`s in PatComp include this exact pathology
end-to-end (search "pop-rule").

## 3. Theorem inventory (the campaign)

Names indicative; hypotheses abbreviated. `WT v T` = `v` a value, well-typed
at ADT `T` under `ctors`; width/occs-validity invariants elided here but
threaded in the real statements.

- **(F) Factoring** `matchPat v p = matchG v (norm p)`; pointwise corollary
  for `firstMatch` vs `matrixSem v [v] (initMatrix ps)`.
- **(H1) Algorithm correctness** — the irreducible heart:
  `evalDTree root (compile occs M) = matrixSem root vals M` given
  `vals = occs.mapM (fetch root)` all-defined + width invariant + typing of
  the column values. Key lemmas (Maranget's, mechanised):
  - `S`: `matchGs (v :: vs) (gctor-c-row) …` ⇔ matching `args(v) ++ vs`
    against `specialize c a occ₀ M` — plus the capture-bookkeeping halves
    (`gbind` head ⇒ captured occ₀ prepends the fetch of occ₀).
  - `D`: head-ctor-∉-heads ⇒ matching `vs` against `defaultMatrix occ₀ M`.
  - Pop: `colHeads M = []` ⇒ same equation as `D` (no tree node).
  - Sub-value typing inversion (well-typed `C v₁…vₐ : T` ⇒ fields typed at
    instantiated field types) — derive in-module from the typing derivation;
    do NOT touch Core.
- **(H2) Adequacy** (by induction on `t`, parametric in `bodies`):
  if `evalDTree v t = some (i, occs*)` and env-invariant `EnvHolds v env σ`
  ("the pending substitution σ places, for every `o ∈ env` at position `j`,
  `fetch v o` at var `j`"), then
  `Relation.ReflTransGen Step ((emit env bodies t).substN… ) → … reaches
  (bodies i).substN 0 (occs*.map (fetch v))`. Within the tree only
  `matchReduce`/`matchWildReduce`/`letReduce` fire — inner scrutinees are
  already values after the outer `substN` (no `matchScrut` inside; a real
  simplification vs the parent brief's fears).
  Prerequisite: the **Expr-closedness mini-library** (Core has NONE):
  `Expr.VarsBelow n`, `shiftFrom`/`substN` identity on closed exprs, values of
  closed well-typed programs are closed.
- **(H4)** is not a separate theorem — it's H2's env-invariant + the
  `emitLets` lemma ("after the leaf-lets reduce, capture `j` sits at var `j`
  and outer refs are shifted by `env.length`").
- **(Top)** compose F + H1 + H2 through `lowerMatch`:
  `firstMatch v pats = some (i, vs)` + WT ⇒
  `lowerMatch v pats bodies ⟶* (bodies i).substN 0 vs`.
- **(X) Exhaustiveness corollary** (retires bridge item 6 for compiled
  matches): tree has no reachable `fail` ⇔ `matrixSem` total on WT values ⇔
  emitted matches satisfy `AllMatchesExhaustive` — feeding Core's `progress`.

## 4. Risks & mitigations

- H1 volume (vector splicing × pattern forms): confined by GPat (3 forms) and
  a `matchGs` append/take/drop lemma library built FIRST.
- H2/H4 was de-risked by design (leaf-lets) and validated executably: the
  `#guard`s run the emitted Core under Core's real `step` including the
  binding-order pathologies and 2-deep nesting. If a proof fights, first
  suspect the statement, not the design.
- Termination lemmas (`*_ctorCount_lt/le`) are elementary but must land
  before ANYTHING else builds. First delegation target.
- Elaboration wrinkle: quarantined by decision 4; revisit only at integration.
- Non-exhaustive matches: `fail` emits a canonical stuck term; refinement
  only speaks about `some` outcomes, so nothing to prove there until (X).

## 5. Campaign plan (parent holds design/statements/gates; workhorses grind)

1. ✅ Definitions + executable pipeline + 3-level `#guard` suite (this memo's
   companion commit).
2. Termination lemmas → PatComp builds sorry-free. [delegable, small]
3. `matchGs` list-algebra library + F (factoring). [delegable]
4. Closedness mini-library. [delegable, independent of 2–3]
5. H1: S/D/pop lemmas, then the main induction. [delegable in slices; the
   *statements* are parent-work]
6. H2: env-invariant + emitLets lemma + tree induction. [statements parent;
   grind delegable]
7. Top-level composition + (X). Wire to the bridge when its item 5 arrives.
Gate every slice: fresh-olean `lake build` + `#print axioms` on the slice's
theorems (house non-negotiable). Axiom set: `{propext, Classical.choice,
Quot.sound}`.

## 6. Status log (append-only)

- 2026-07-06: memo written; `FHM/PatComp.lean` definitions + executable
  pipeline landed with 3 sorry'd termination lemmas (slice 2 pending their
  discharge); lakefile root added. `#guard` suite green locally incl. the
  pop-rule pathology and 2-deep-nesting H2 smoke tests (via `SmallStep.step`).
- 2026-07-06: termination lemmas proved (plan step 2 done) — PatComp
  sorry-free, committed a9613c2. Plan step 4 done: `FHM/ExprClosed.lean`
  closedness library complete and axiom-clean (`varsBelow` + mono +
  `shiftFrom`/`substN` identity on scoped terms + `TypeOfElabHM.varsBelow`
  at threshold `ctx.env.length` + empty-ctx `closed` corollary).
  RECORDED, not actioned: Core has an ORPHAN `Expr.WellScopedUnder`
  (~L1616) duplicating `varsBelow` rule-for-rule, never connected to
  typing — candidate for a leaf-module `iff` unification later (backlog;
  do NOT touch Core for it).
- 2026-07-06: plan step 3 done (matchGs algebra + factoring, axiom-clean —
  headlines need only {propext, Quot.sound}). Plan step 5 done: **H1 LANDED** —
  `compile_correct` (functional induction via `compile.induct`; capture-aware
  `matrixSem_specialize`/`matrixSem_default` serving pop/∉-heads/non-ctor from
  ONE default lemma) and the hypothesis-free headline
  `compile_correct_surface : evalDTree v (compile [[]] (initMatrix ps)) =
  firstMatch v ps`. Axioms exactly {propext, Classical.choice, Quot.sound}.
  All parent-audited statements held verbatim (incl.: row-drop congruence
  needs no captured-isSome hypothesis; duplicate colHeads entries carry
  identical subtrees so dedup-uniqueness is never needed).
  Proof-engineering notes for future slices: getting past `compile`'s
  dependent `match _hh : colHeads …` needs `rw [compile]; split` + equation
  rewriting; `List.attach_map_val` needs its function argument fully explicit
  (higher-order unification misses `fun i => f ↑i`); `do`-binds want
  `Option.bind_eq_bind, Option.bind_some` normalisation before `cases`.
- H2 statement note (decided during design, recorded for the H2 slice):
  `evalDTree` DEFAULTS on a non-ctor value at a switch, mirroring `D(M)` —
  so H1 is typing-free and unconditional. But Core's `matchWildReduce`
  only fires when the wildcard branch is FIRST, so an emitted switch is
  STUCK on a non-ctor scrutinee. H2 therefore carries a path condition
  ("every switched occurrence on the taken path holds a ctor-chain
  value"), discharged at top level from scrutinee typing (switches only
  test ADT-typed columns). Do not "fix" this by reordering emitted
  branches — named-first + trailing wildcard is correct for ctor values
  via `FirstMatchingBranch`.
