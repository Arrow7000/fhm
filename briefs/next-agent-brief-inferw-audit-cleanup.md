<!-- Handoff brief: audit + cleanup after the InferW metatheory was completed.
     Companion: next-agent-brief-inferw-reformulation.md (the full story, §7d–§7f).
     Status as of writing: Experiments/FreshTypeSystem/InferW.lean compiles with ZERO
     errors; the whole chain Core.TypeOfHM (declarative) → Infer (relation) →
     inferCore/typecheck (executable) is sound + complete + principal, axiom-clean. -->

# Handoff: audit the finished InferW metatheory, then clean it up

## 0. What you're inheriting (context)
`Experiments/FreshTypeSystem/InferW.lean` (~11.9k lines) is a verified Hindley–Milner
type system with **scoped type variables** (Elm/GHC `ScopedTypeVariables`-style),
checked against the declarative spec `TypeOfHM` in `Core.lean`. After a long repair arc
it is now **fully green and axiom-clean**:
- Relation `Infer`: soundness (`Infer.sound_closed`), completeness (`Infer.completeAt`),
  principality (`Infer.complete'`/`isPrincipal`/`output_unique`).
- Executable `inferCore`/`infer`/`typecheck`: soundness (`infer_sound`), **completeness
  (`inferCore_complete`)**, principality (`infer_isPrincipal`), and the closed-program
  headlines (`typecheck_iff`/`sound`/`principal`/`closed`, `principalType_*`,
  `infer_iff_typeable`), plus Stage C (`typecheck_progress`/`preservation` over *erased*
  runtime programs).
- The two blockers were cracked: the **freshness wall** (`Infer.gap_avoid`,
  `Infer.letInAnn_block_fresh`) and the **orientation wall** — the executable was made
  **rigidity-aware** (`unifyCoreK`: a `unifyCore` that knows a rigid set `K` and refuses
  to bind it; `inferCore` threads `K`, infers an annotated-`let`'s opened rhs at
  `K ++ freshVars Φ pc`). Full story: `next-agent-brief-inferw-reformulation.md` §7d–§7f.

**Two goals for you, in order: (A) AUDIT that none of this is fake — no vacuous
theorems, no unsatisfiable/unavailable premises, no quietly-weakened conclusions — then
(B) a 10,000ft cleanup now that the code is finally stable.**

## 0a. Hard guardrails (non-negotiable)
- NEVER `sorry`/`axiom`/`native_decide`/`admit`; NEVER weaken a statement's conclusion;
  NEVER edit `Core.lean` (it is the ground-truth declarative spec); do NOT run
  `lake build` (an unrelated file is broken — use the Lean LSP).
- Verify with the `project-0-experiments-lean-lsp` MCP: `lean_diagnostic_messages` scoped
  with `start_line`/`end_line` (trust the `items` array, not whole-file `success`);
  `lean_verify` (scan_source:false, fully-qualified names) — axioms must be EXACTLY
  `propext`/`Classical.choice`/`Quot.sound`.
- Commit each green milestone separately; do NOT push. For deletions, delete in small
  steps and re-check green after each.

---

## PART A — Soundness / non-vacuity audit (DO THIS FIRST)
The fear: across ~10 repair sessions, did we make things "go green" by adding
**unsatisfiable premises** (a hypothesis `P` that nothing can satisfy makes the theorem
vacuously true and useless), by **weakening conclusions**, or by requiring **premises a
real typechecker wouldn't have**? Establish trust before touching anything.

### A1. Mechanical integrity
- Re-confirm there is no `sorry`/`admit`/`axiom`/`native_decide` in `InferW.lean` AND
  `Core.lean` (grep; the only hits should be inside doc comments).
- `git diff` `Core.lean` against the last pre-repair commit to CONFIRM the declarative
  spec was never edited (we must be honest against an untouched ground truth).
- `lean_verify` (axioms only) the FULL public headline set and key internals:
  `typecheck_iff`, `typecheck_sound`, `typecheck_principal`, `typecheck_closed`,
  `typecheck_progress`, `typecheck_preservation`, `principalType_sound`,
  `principalType_principal`, `principalType_iff`, `infer_iff_typeable`, `infer_iff`,
  `infer_complete`, `infer_sound`, `infer_isPrincipal`, `Infer.sound_closed`,
  `Infer.completeAt`, `Infer.isPrincipal`, `Infer.output_unique`. All must be exactly the
  standard 3 axioms.

### A2. Per-headline premise audit — "satisfiable AND available in normal use?"
For EVERY public theorem, list each hypothesis and justify it is (a) satisfiable by
genuine programs and (b) a condition a real caller actually has. Scrutinize especially:
- **`hclosed : e.tyFreeVars = []`** on `typecheck_iff`/`principalType_iff`/
  `infer_iff_typeable` (and check which of `typecheck_sound`/`principal`/etc. carry it).
  Is "no free type variables in annotations" the right top-level well-formedness boundary,
  or does it silently exclude programs that *should* typecheck? The relation handles
  scoped vars, but the closed-program headlines fix the executable's rigid set `K := []`.
  **Investigate**: should/could the headlines be generalized to programs with free
  top-level annotation vars by running `inferCore` at `K := e.tyFreeVars` (treating them
  as rigid scoped vars) and generalizing accordingly — or is closed the principled
  boundary? Either generalize it, or document precisely why `hclosed` is correct and not
  a cop-out. (NB: `inferCore` at `K=[]` will happily *bind* a free annotation var; the
  `#eval` of `λ(x:α).x` returns `some (α→α)` — make sure the headline story for such
  programs is coherent.)
- **`he : e.IsTyErased`** on `typecheck_progress`/`typecheck_preservation`. Confirm:
  (i) `IsTyErased` is NON-VACUOUS — exhibit a concrete erased program that takes a `Step`;
  (ii) it is exactly the runtime class the `SmallStep`/`Step` dynamic semantics operates
  on (so progress/preservation are stated where they're meant to be);
  (iii) the restriction is FORCED, not convenient — verify that subject reduction genuinely
  fails for annotated terms (the design reason), modelling on Core's
  `TypeOfHM.erased_type_safety`/preservation. Also check the two helpers
  `Expr.IsTyErased.tyFreeVars_eq_nil` and `Step.preserves_isTyErased` are real (the latter
  must actually hold for the operational semantics, not be a stub).
- **`CtxWF`/`CtxBelow`** side conditions on `infer_*`: confirm they're discharged
  vacuously at the empty top-level context (`CtxWF.empty`/`CtxBelow.empty`), so the
  closed-program headlines have NO leftover obligations beyond `hclosed`.

### A3. Anti-vacuity by WITNESS (the real test — a vacuous theorem cannot fire)
Add a small, committed **demonstration capstone** that drives the full pipeline on
concrete inputs with no escape hatches:
- A typeable program, e.g. `let id : ∀a.a→a = λx.x in id id`: prove via the headlines
  (instantiated + `decide`/`rfl`/`#eval`) that `typecheck [] p = some σ`, that the
  corresponding `TypeOfHM ⟨[],[]⟩ p τ` holds (soundness), and that an arbitrary
  declarative typing factors through it (principality). The point is to witness that the
  headlines *produce* results on real inputs.
- An ill-typed program, e.g. `5 5`: `typecheck [] _ = none` and (via the iff)
  `¬ ∃ τ, TypeOfHM ⟨[],[]⟩ _ τ`. Confirms completeness's contrapositive isn't vacuous.
- The relaxed `Infer.letInAnn` (abstract `N ≥ Φ`) is genuinely inhabited: exhibit
  `∃ Φ' S τ, Infer 0 ⟨[],[]⟩ <an annotated let> Φ' S τ` (the annotated-`let` `#eval`s
  already witness the executable side; make the relational side explicit too if cheap).
- A step+typecheck witness for progress/preservation on a concrete erased program.

### A4. Conclusion-shape review (did churn weaken anything?)
For each headline, compare the CURRENT statement to the INTENDED one (soundness /
completeness / principality / decidability) and confirm no silent degradation: an `↔` that
should be an `↔` (not a one-way `→`), a principality `∀ τ₀, … ∃ R, τ₀ = R.onTy τ` rather
than something weaker, no spurious extra hypotheses. The intended statements are recorded
across the brief files (`-reformulation.md`, `-completeness.md`, `-stage1.md`).

**Part A deliverable:** a committed `.md` audit verdict (per-headline: premises
satisfiable+natural ✓, conclusion faithful ✓, or a precise flag) plus the demonstration
capstone committed green. If you find a genuine vacuity/weakening, STOP and report it
loudly — that's the whole point of this pass.

---

## PART B — 10,000ft cleanup / streamlining (only after Part A passes)
Verify deadness (grep + LSP) before deleting; do it in small separately-committed steps,
re-checking the scoped diagnostics after each.

### B1. Delete now-dead lemmas (superseded by `unifyCoreK`)
These appear only self-/cross-referenced with no live callers (confirm, then remove):
- `OUnify.skolem_escape` / `OUnifyList.skolem_escape` (≈5454),
- `exists_skolem_unifier` (≈5133),
- `skolem_no_env_leak` (≈8218; its only user was the old executable ann case).
Then check whether the entire `OUnify` stack is now orphaned and removable:
`OUnify`/`OUnifyList` inductives, `OUnify.toUnifyRel`/`OUnifyList.toUnifyRelList`,
`OUnify.complete`/`OUnify.complete_aux`, `unifyCore_oUnify` (≈9127). Keep
`exists_app_unifier`/`exists_pair_unifier` (live in app/fst/snd/match).

### B2. De-duplicate the unifier layer (biggest win)
`unifyCore`/`unifyListCore` vs `unifyCoreK`/`unifyListCoreK` are near-identical, and
`unifyCore_complete_aux` vs `unifyCoreK_complete_aux` duplicate a ~120-line size
induction. Consider defining `unifyCore a b := unifyCoreK [] a b` (the `K=[]` instance is
trivial) and deriving `unify`/`unify_sound`/`unify_complete` + the `#eval`s from the
K-version — eliminating the duplicate function and its completeness proof. Caveat:
`unifyCore` carries `{S // UnifyRel a b S}` while `unifyCoreK` carries
`{S // UnifyRel a b S ∧ (∀ p ∈ S, p.1 ∉ K)}`; at `K=[]` the second conjunct is trivial, so
reconcile the subtype (e.g. project, or have `unify` map through). Only do this if it
genuinely simplifies rather than adding adapter noise.

### B3. Prune orphaned block-swap helpers
`blockSwap`/`Subst.conj`/`blockList`/`blockListBack` (+ helpers) are still used by the
RELATION completeness (`complete_var`/`complete_ctor`). Confirm what remains live after B1
and remove any now-orphaned helpers (e.g. ones that only fed `exists_skolem_unifier`).

### B4. Doc/comment sweep
Many doc comments still describe the OLD closed-annotation / pre-rigidity design. Update:
the `### infer completeness` preamble (mentions `unifyCore_complete_aux` / "rebuild the
explicit unifier"), the `inferCore` annotated-`let` comment, `### Gap-avoidance` /
`letInAnn` doc blocks, and any "skolem escape"-era prose. Reflect the rigidity-aware story.

### B5. Naming / ergonomics
`inferCore`/`inferBranchesCore`/`unifyCoreK` now lead with `K` — check the arg order reads
well. Decide whether the carried `avoids K` invariant in `inferCore`'s result type is the
cleanest design (it is currently load-bearing for the annotated-`let` `hesc1`/`hesc2`;
keep unless a separate lemma is clearly tidier).

### B6. Elaboration time
~12k lines. `lean_profile_proof` the heaviest theorems — the two `*_complete_aux` size
inductions, `Infer.gap_avoid`, the `inferCore_complete_letIn` ann assembly, the
`inferCore_complete_match` block — and tighten (`simp` → `simp only`, drop unused
hypotheses, factor repeated `have`s). Watch for `grind`/large-proof hotspots.

### B7. Repo hygiene (ASK the user before deleting briefs)
The brief files `next-agent-brief-inferw-completeness.md`, `-stage1.md`, `-inferw.md` are
superseded by `-reformulation.md` (+ this file). Propose consolidating/retiring them, but
confirm first — the user may want them archived. NOTE: `AbstractTypeSystem.lean`,
`AbstractWalk.lean`, `lake-manifest.json`, `lakefile.toml` carry uncommitted *pre-existing*
changes unrelated to this work — leave them alone / ask.

### B8. (Forward-looking, out of scope) surface language
`next-agent-brief-surface-lang.md` is the north star: a surface language on top of the now-
complete core. Not cleanup, but the natural next feature once A+B land.

## Recommended order
Do ALL of Part A first (commit the verdict + capstone). Only then Part B, in small
independently-verified commits. After cleanup, re-`lean_verify` the full headline set to
confirm the standard-3-axioms property survived.
