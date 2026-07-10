<!-- Written 2026-07-11, at the end of the surface → Core bridge campaign
     (roadmap step 5 — "the north star"). The bridge's HEADLINE is now COMPLETE and
     UNCONDITIONAL. Read these FIRST, in order:
       1. briefs/next-agent-brief-surface-bridge.md — THE ORIGINAL PLAN (items 1–9).
          Still the map; this brief records which items are DONE vs open.
       2. briefs/next-agent-brief-surface-bridge-kickoff.md — the kickoff status +
          the PatComp interface the bridge consumes.
       3. briefs/design-memo-verified-pattern-compilation.md — the pattern-
          compilation record (kernel is DONE + unconditional).
     This brief gives the FRESH status after the bridge landed, an honest map of
     what's finished vs what's left, the campaign's hard-won lessons, and where a
     next agent should start. It does NOT duplicate the plan. -->

# Brief: surface → Core bridge — follow-ups after the headline landed

## TL;DR — the north star is reached

The verified front-end **headline is complete, unconditional, and axiom-clean**:

```
theorem surface_type_safe {ctors : CtorEnv} {s : Surface.Expr} {c : Expr}
    (hlow : lower ctors s = some c)
    (htc : (typecheck ctors c).isSome)
    (hcov : SurfaceCovers ctors s) :
    ∃ e τ, elaborate ctors s = some e ∧
      TypeOfElabHM ⟨[], ctors⟩ e τ ∧
      AllMatchesExhaustive ctors e ∧
      ∀ e', Relation.ReflTransGen Step e e' → (IsValue e' ∨ ∃ e'', Step e' e'')
```

In words: *a surface program that lowers, typechecks, and whose matches cover
their scrutinee types elaborates to a Core term that is well-typed,
all-matches-exhaustive, and never gets stuck under Core's real small-step `Step`.*

`lake build` green (9 `.lean` roots, 7752 jobs); `#print axioms surface_type_safe`
= `{propext, Classical.choice, Quot.sound}`, and likewise for every lemma it
depends on (`lower_elab_exhaustive`, `infer_preserves_AllMatchesExhaustive`,
`lower_exhaustive`, `emit_DTreeExhaustive`, the transport lemmas, …). No
`sorry`/`admit`/`axiom` in `FHM/SurfaceBridge.lean`.

## What the bridge delivers (all in `FHM/SurfaceBridge.lean`, ~2.4k lines)

- **Type lowering (plan item 2):** `lowerTy : KindEnv → List ValName →
  Surface.Ty → Option Ty` (named tvars → de Bruijn `bvar`, arity-checked
  `customTy`, sugar `pair`→`Pair`, `bool`→`Bool`) + `lowerTy_wellKinded`
  (success ⟹ `Ty.WellKinded`). `#guard`-tested on adversarial inputs.
- **Expression lowering (items 3–4):** executable `lower`/`lowerExpr` (name
  resolution → de Bruijn; `app`/λ/`let`/`letRec`; sugar `pair`/`cons`/`list`/
  `bool`/`ife`; `match` via the verified `PatComp.lowerMatch`) + `elaborate`
  (`lower` then `infer` → the decorated runtime term `eOut.substTyFvars S`).
  `#guard`-tested.
- **Declarative spec + bridge:** `Lowers`/`LowersExpr` (the relation;
  **non-deterministic/behavioural at `match`** — any `emitInner` agreeing with
  the surface oracle `firstMatch`), with `lower_sound` (`lower s = some c →
  Lowers … s c`) and `lower_complete` (a valid lowering exists ⟹ `lower` finds
  one). The `match`-case soundness *is* `PatComp.lowerMatch_adequate_of_typed`.
- **Surface well-typedness (item, defined not axiomatised):** `SurfaceWT ctors s
  := ∃ c, Lowers ctors s c ∧ (typecheck ctors c).isSome`. (Defined; **not yet**
  wired into the headline — see follow-ups.)
- **Exhaustiveness (item 6, Prop-level):** `SurfaceCovers` (structural; each
  `match`/`ife` carries a `MatchExhaustive` witness) → `MatchExhaustive` (=
  `DTreeExhaustive` on the compiled tree) → `emit_DTreeExhaustive`
  (`DTreeExhaustive` ⟹ `AllMatchesExhaustive (emit …)`, by induction on the
  coverage derivation) → `lower_exhaustive` → transported across elaboration →
  `lower_elab_exhaustive`. `DTreeExhaustive` is the **syntactic, occurrence-typed
  tree-coverage** predicate matching Core's `AllMatchesExhaustive` exactly.
- **The payoff (item 5-composition):** `surface_type_safe`, composing the above
  with Core's `TypeOfElabHM.type_safety_star`.

`Pair` was added to `Decls.preludeDecls` (arity 2, fields `[.bvar 0, .bvar 1]`)
for tuple sugar. `PatComp.emit` was fixed to **omit the wildcard branch when a
switch's default is `.fail`** (complete signatures) — without this, `if` and
enumerated matches did not typecheck (see Lessons).

## Broader context: where this sits on the roadmap

The project builds a small, fully-verified ML-family language. Prior roadmap
steps (all DONE, axiom-clean): (1) arithmetic primops `intAdd`/`intSub`; (2) type
declarations `FHM/Decls.lean` (`DataDecl`, `Ty.WellKinded`, `elabDecls`
sound+complete, `preludeDecls`); (3) comparison primops `intLt`/`charLt`; (4) the
fused mixed annotated/unannotated `letRec`; plus `str`→primitive `char`
(strings = `List Char`). **Step 5, "the north star", was this surface → Core
bridge** — lowering surface syntax into Core so that *well-typed surface ⇒ safe
Core*, borrowing all of Core's operational meaning through the lowering (there is
no separate surface semantics; matching is the one construct with behavioural
content, and its correctness — `lowerMatch_adequate_of_typed` — is proved). That
headline is now in hand.

## Is the lowering story "complete"? Honest answer: the CORE arc is, the
## front-end PRODUCT is not yet.

**Finished:** surface *expression* + *type* lowering, soundness + completeness,
pattern compilation wired in, exhaustiveness→type-safety, the headline — for a
**single closed surface expression** against a **supplied `CtorEnv`** with an
explicit `SurfaceCovers` hypothesis.

**Not yet done** (a genuine, well-scoped backlog — this is what a next agent
should pick from):

1. **Surface `DataDecl` lowering (plan item 1) — the biggest real gap.** There is
   NO surface-syntax data declaration. `FHM/SurfaceLang.lean` has no `DataDecl`;
   the bridge only *recovers* a `KindEnv` from an already-built `CtorEnv`
   (`kindEnvOfCtors`). Core-side `DataDecl`/`elabDecls`/`preludeDecls` exist in
   `FHM/Decls.lean`. **Task:** add a surface `DataDecl` (named type params +
   named/field ctors), lower it (named params → `bvar` indices; resolve type
   refs) to `Decls.DataDecl`, then reuse `Decls.elabDecls` → `CtorEnv`. This is
   what lets a *program* declare its own types rather than being handed a
   `CtorEnv`. House-style (relation + function + sound/complete), low-risk.

2. **Whole-program / top-level pipeline (plan item 7).** Lowering is
   expression-level only (there's a `letRecIn` *expression* case, but no
   program-level structure). **Task:** a top-level program = data decls + a list
   of (mutually recursive) top-level bindings; do SCC / dependency analysis →
   topological order → desugar into nested `letRec`/`letIn` (reuse the fused
   Core node — NO new Core metatheory). Then a *whole-program* headline:
   "a well-formed surface program elaborates to a safe Core program."

3. **Executable exhaustiveness checker (plan item 6, the decidable half).** The
   exhaustiveness *predicate* (`DTreeExhaustive`) and its consequence
   (`AllMatchesExhaustive`) are done, but `SurfaceCovers` is a `Prop` the caller
   must supply. **Task:** an executable `checkExhaustive`/`dTreeExhaustiveB : …
   → Bool` with `= true → DTreeExhaustive …` (hence `→ SurfaceCovers`), so the
   coverage hypothesis is *decided*, not assumed. Then the pipeline
   (`lower` + `typecheck` + `checkExhaustive`) is fully executable end-to-end.
   `DTreeExhaustive`'s occurrence-typed shape was chosen to make this a clean
   structural Bool recursion + soundness.

4. **`SurfaceWT`-phrased headline corollary.** `surface_type_safe` is stated over
   the *executable* preconditions (`lower`/`typecheck`/`SurfaceCovers`). A
   corollary phrased over the declarative `SurfaceWT` (via `lower_complete` +
   "typeability is invariant across valid lowerings", needed because `Lowers` is
   non-deterministic at matches) would close the spec/impl loop. Medium.

5. **Pattern-λ desugaring (item 4 leftover).** `lower` defers a λ whose parameter
   is a *non-trivial pattern* (returns `none`; only `lambda_name`/`lambda_wild`
   in `Lowers`). **Task:** desugar `λ(p : Pattern). body` → `λx. match x with p
   => body` and add the `Lowers` rules.

6. **Friendly error messages (plan item 8, optional/UX).** Make the lowering/check
   total (`… → Except Error _`); totality gives "a message for every failure",
   and an `iff_typeable`-style theorem proves error-soundness. Beware the *blame
   problem* (where to report is heuristic). Do last / opportunistically.

7. **Surface strings.** `Surface.PrimLitExpr` currently has no `str` constructor,
   so the brief's `str → List Char` sugar has nothing to desugar. If string
   literals are wanted, add `PrimLitExpr.str` + desugar to a `Cons`/`Nil` of
   `char` literals.

### DEFERRED (item 9 — far horizon; record, do NOT build casually)

Quoted from `next-agent-brief-surface-bridge.md`:
- **Typeclasses / Elm-style constrained vars** (`number`, `comparable`) — the real
  path to polymorphic `+`/`<` over several types.
- **Row types / extensible records** — far horizon.
- **Floats** — need a full arithmetic primop kernel (not inductively generated).
- **`ord`/`chr`** (Char↔Int) — the first arity-1 ops; build a `primUnOp` node
  PARAMETRIC (single rule + a `PrimUnOp → Ty` function).
- **`nat` → Peano data** (retire primitive `nat`) — fold into numeric-literal
  desugaring.
- **Core naming/hygiene backlog + `Core.lean` file split.**

## Cleanups worth doing (small, low-risk)

- **Dead code:** `AllMatchesExhaustive.eraseVarTyArgs` / `.of_eraseVarTyArgs` /
  `.eraseVarTyArgs_iff` in `FHM/InferW.lean` (~L17141–17235) are now UNUSED (the
  final transport routes through `infer_preserves_AllMatchesExhaustive` +
  `AllMatchesExhaustive.substTyFvars`, not erasure). Prune them, or leave with a
  note. Also a doc comment (`InferW.lean` ~L16908) references a non-existent
  `Infer.eraseVarTyArgs_invariant`.
- The transport lemmas `AllMatchesExhaustive.substTyFvar/.substTyFvars` live in
  `Core.lean` and the (dead) erasure ones in `InferW.lean` — placement approved
  by Aron (each sits with its ingredients).

## The hard-won lessons (this campaign's, heed them)

1. **A checker/coverage predicate can be subtly WRONG in both directions.** We
   went through THREE coverage designs: (a) a *flat* "top-level ctors covered"
   check — UNSOUND (missed nested gaps: `Cons (Just x) t | Nil` leaves
   `Cons Nothing Nil` unmatched); (b) a *semantic* "`firstMatch` total on all
   well-typed values" — sound but CANNOT imply Core's *syntactic*
   `AllMatchesExhaustive` (an uninhabitable ctor like `Just @ Void` needn't be
   covered semantically, yet Core demands it — the "inhabitation gap"); (c) the
   *syntactic occurrence-typed* `DTreeExhaustive` — the principled choice that
   matches Core's predicate exactly and is decidable. **Lesson:** for exhaustive-
   ness in an HM language, the principled notion is *syntactic* (cover all
   declared ctors), matching the metatheory's own predicate — not semantic
   totality (a dependent-types refinement that isn't decidable and needs Core
   surgery). Pick the coverage notion that your consumer (`progress`/
   `type_safety`) actually requires.

2. **`#eval`/`#guard` the executable side on adversarial inputs BEFORE proving.**
   The `emit` bug (unconditional `| _ => PatCompFail` wildcard) made `if` and
   every enumerated match fail to typecheck — caught by `#eval`-ing `elaborate`
   on `if true then 1 else 0`, not by staring at proofs. The PatComp campaign
   never hit it because it only ran emitted terms under `Step`, never
   *typechecked* them. Construct concrete instances; check hypotheses are
   satisfiable (non-vacuous).

3. **`lake build` is the gate, not the LSP.** After editing a dependency
   (PatComp/Core), the lean-lsp-mcp serves STALE `.olean`s — it reported passing
   `#guard`s as failing. Use `lake build` (or the `lean_build` MCP tool, which
   rebuilds + restarts the LSP) as the source of truth, especially for
   `#print axioms`.

4. **Freeze statements, delegate proofs, audit by `#print axioms`.** The bulk
   proofs were delegated to subagents against FROZEN statements; correctness was
   guaranteed by auditing `#print axioms` on the *unchanged* headline (no
   `sorryAx`) — so intermediate lemma design didn't have to be trusted.

## Non-negotiables (house rules)

- Headline theorems stay `sorry`/`admit`/`axiom`-free and axiom-clean
  `{propext, Classical.choice, Quot.sound}`; gate every increment with a
  fresh-olean `lake build` + `#print axioms` (the LSP alone is NOT the gate after
  a Core/dependency edit).
- **Core stays minimal**: front-end concerns live in the bridge module /
  `Decls.lean`, not Core's metatheory. (Small `AllMatchesExhaustive` companion
  lemmas alongside the existing `.instTy`/`.substN` family are acceptable.)
- **File discipline**: 9 built `.lean` roots — no new files without strong
  justification.
- Don't weaken headline statements; add hypotheses to internal helpers instead.
- Delegate bulk proof-plumbing to subagents with precise per-error specs; keep
  design decisions (relation/predicate shapes, statement wording) and the
  build/axiom gate in the parent. Granular commits per slice.

## Recommended starting point

**Item 1 (surface `DataDecl`) then item 7 (top-level pipeline)** — together they
turn "lower one expression against a given `CtorEnv`" into "elaborate a whole
surface program (decls + bindings) into safe Core", which is the natural
*complete front-end* end state. Both are house-style and reuse existing machinery
(`Decls.elabDecls`, the fused `letRec`, `surface_type_safe`). Then **item 6's
executable `checkExhaustive`** to make coverage decidable, and the **`SurfaceWT`
corollary** to close the spec/impl loop. Do the `InferW` dead-code prune
opportunistically. Item 8 (errors) and item 9 (typeclasses etc.) are later.
