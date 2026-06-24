<!-- Handoff brief written at the end of the "Core v2 (pair removal + wildcard
     match patterns) + surface-language groundwork" session.
     Supersedes nothing; companion to next-agent-brief-surface-lang.md.
     Files: FHM/{Core,InferW,SurfaceLang}.lean -->

# Handoff: finish Core v2 (the match-wildcard fix), then build the surface language

## 0. TL;DR / current state (READ FIRST)

The verified HM core (`Core.lean` = declarative `TypeOfHM` + dynamics + safety; `InferW.lean`
= Algorithm-W `Infer`/`inferCore`/`typecheck` + sound/complete/principal metatheory) was
**fully green + axiom-clean**. This session we started **"Core v2"**: removing redundant
built-ins and adding wildcard match patterns. We got most of the way but stopped on a real
design issue (below).

**Right now:**
- `Core.lean`: **GREEN + axiom-clean.** `TypeOfHM.progress`/`preservation`/`erased_type_safety`
  verify with exactly `propext`/`Classical.choice`/`Quot.sound`.
- `InferW.lean`: **RED** — exactly two proofs are unfinished: the `match_` case of
  `Infer.complete'` and `inferCore_complete_match`. Everything else is threaded. These two are
  blocked by the design issue in §1; the headline completeness/principality theorems
  (`typecheck_iff`/`principal`/`infer_complete`/`Infer.complete'`/`isPrincipal`/`output_unique`/
  `inferCore_complete` + progress/preservation + the `AuditCapstone.*`) are `sorryAx`-tainted
  *via* those two. The soundness headlines (`*_sound`, `Infer.completeAt`) are clean.
- `SurfaceLang.lean`: data types for the surface language (`Expr`/`Ty`/`Pattern`/`PolyTy`),
  design-in-progress. Not yet connected to Core.
- Committed as a deliberately-not-fully-green checkpoint; **§1 is how you get back to green.**

**Do NOT** edit `AbstractTypeSystem.lean`/`AbstractWalk.lean`/`lake-manifest.json`/`lakefile.toml`
(pre-existing unrelated dirty changes). Don't run whole-project `lake build` (the unrelated
`Experiments/Filterings.lean` is broken). Use the `project-0-experiments-lean-lsp` MCP.

---

## 1. IMMEDIATE TASK — fix the all-wildcard match, get InferW green again

### What Core v2 already changed (these are DONE and correct)
- **`PrimTy.bool` removed** from Core earlier (Bool is a `customTy` `True | False`).
- **The object-language pair removed**: no more `Ty.pair`/`Expr.pair`/`fst`/`snd` (a pair is
  a 1-ctor `customTy`). `customTy` subsumes it.
- **`MatchPattern` is now `inductive | named (ctor : CtorName) (contents : Nat) | wildcard`**,
  with helpers `MatchPattern.bindCount` (`named _ n ↦ n`, `wildcard ↦ 0`) and
  `MatchPattern.matchesCtor`. Threaded through Core (dynamics/typing/safety — all green) and
  InferW (`InferBranches.cons` now `.named`, new `InferBranches.consWild`, `inferBranchesCore`
  cases on the pattern).

### The issue (a genuine type-theory fact — don't re-misdiagnose it)
An **all-wildcard match** (no named branch) currently has **no principal type**, because
`TypeOfHM.match_` (and `Infer.match_`) force the scrutinee to be `customTy tyName tyArgs`
*unconditionally*. So `λx. match x with | _ => 0` is typeable at `customTy T [] → Int` for
**any** `T` — infinitely many incomparable types, no MGU. That breaks
completeness/principality (the two blocked proofs).

**This is NOT how real languages behave** (and an earlier "require a named branch" patch — now
reverted — was a wrong, non-standard restriction). In Haskell/OCaml/F#/Elm, `\x -> case x of _ -> 0`
is `∀α. α → Int` — a wildcard imposes **no** constraint on the scrutinee type. The bug is the
unconditional `customTy` requirement, not the wildcard. (`branches ≠ []` is unrelated — it
grounds the *result* type in a real branch body; it has nothing to do with the scrutinee.)

### The fix (the correct, real-language-faithful design — implement THIS)
1. **Scrutinee type is free; only named patterns constrain it.** Change `TypeOfMatchBranch` to
   take the **scrutinee type** `scrutTy : Ty` instead of `tyName`/`tyArgs`:
   - `mk` (named `c n`): `∃ ctor tyArgs, lookup c = ctor ∧ scrutTy = .customTy ctor.tyName tyArgs
     ∧ ctor.paramCount = tyArgs.length ∧ n = ctor.contents.length ∧ <instantiate contents by
     tyArgs as the pattern bindings> ∧ TypeOfHM bodyCtx body resultTy`. (A constructor pattern
     *forces* `scrutTy` to be its ADT; all named patterns in a match thus agree on the ADT.)
   - `wildcard`: just `TypeOfHM ctx body resultTy` (no `scrutTy` constraint).
   And `TypeOfHM.match_`: `TypeOfHM ctx scrutinee scrutTy → branches ≠ [] →
   (∀ branch ∈ branches, TypeOfMatchBranch ctx branch scrutTy resultTy) → …`.
   ⇒ all-wildcard ⇒ `scrutTy` free ⇒ principal `∀α. α → result`. Named ⇒ `scrutTy` pinned.
2. **Dynamics: a wildcard fires on ANY value.** `match 5 with | _ => 0` now typechecks
   (scrutinee `Int`), so progress needs it to step even though `5` isn't a ctor chain. Add a
   reduction: scrutinee is a value that is *not* a ctor chain ⇒ the first (necessarily wildcard,
   by typing) branch fires. Ctor-chain scrutinees keep the existing `matchReduce`
   (`body.substN 0 (args.take pat.bindCount)`). (`AllMatchesExhaustive` already treats a
   wildcard as trivially exhaustive — keep that.)
3. **Inference mirrors it.** `Infer.match_` should NOT unify the scrutinee with `customTy …`
   up front; instead the **named** branches unify it inside `inferBranchesCore` (the `cons`
   case already requires `ctor.tyName = tyName`), and an all-wildcard match leaves the
   scrutinee type a free var. **`inferCore` must INFER all-wildcard matches, not reject them**
   — undo the placeholder `| .wildcard => none` reject arm that's currently in `inferCore`'s
   match handling.
4. Re-thread/re-prove progress/preservation (new dynamic case + generalized typing), the
   `Infer`/`InferBranches` metatheory, and **finish the two blocked proofs** (now genuinely
   true: `complete'`/`inferCore_complete` for all-wildcard succeed with a free scrutinee type).

### How to know you're back to green
`lean_verify` (axioms = exactly `propext`/`Classical.choice`/`Quot.sound`) on the headline set:
`typecheck_iff`/`_sound`/`_principal`/`_closed`/`_progress`/`_preservation`,
`principalType_sound`/`_principal`/`_iff`, `infer_sound`/`_complete`/`_isPrincipal`,
`Infer.completeAt`/`complete'`/`isPrincipal`/`output_unique`, `inferCore_complete`, and
`AuditCapstone.idid_headlines_fire`/`appFiveFive_rejected`/`appIdFive_preserves`. Then **commit
the Core-v2 milestone**. (Add an `AuditCapstone` witness or two for matches with a wildcard,
e.g. `match c with True => 1 | _ => 0` typechecks, while you're at it.)

### Workflow note (bit us repeatedly)
After editing `Core.lean`, `InferW` keeps elaborating against the **stale Core `.olean`**. To
refresh: targeted `lake build FHM.Core` (only this module — NOT whole
project), then MCP `lean_build` to restart the LSP (it "fails" on the unrelated `Filterings.lean`
— ignore that). Otherwise you'll chase phantom errors about removed constructors.

---

## 2. Core decisions still to make (deferred — tackle when the surface needs them)

The surface language can't express much without these; decide intentionally.

- **Recursion (the big one).** Core's `letIn` is non-recursive and there's no `fix`/`letrec`,
  so **no recursive functions exist** — you can't write `map`/`length`/`fold`. HM can't type a
  fixpoint combinator (needs recursive/untyped types), so this needs a Core primitive: a `fix`
  (`fix : (a→a)→a`, `fix f → f (fix f)`) or a recursive `let rec` with **monomorphic** recursion
  (the recursive occurrence at a monotype, generalized after; polymorphic recursion is
  undecidable). Type safety survives (you just lose normalization). It's a *new constructor* ⇒
  a new case in every `Expr`/`Infer` induction (incl. `complete'`). Heaviest remaining Core task.
- **Primitive ops** (`+`, comparisons, `++`). *Typing* can live entirely in a prelude env
  (`add : Int→Int→Int` as a constant) — zero Core change, programs typecheck. *Evaluation*
  needs Core δ-rules (`add (int m) (int n) → int (m+n)`) + their progress/preservation — defer
  until you want to run programs.
- **Type declarations** (`data List a = …`). Just *elaborate to `CtorEnv` entries* — **no new
  Core metatheory** (Core handles any `CtorEnv`). Reuse the tvar-resolution machinery (named →
  de Bruijn `bvar`, scoped by the decl's params). New (small): a type-name env for resolving
  `customTy` refs + arity checks. **Type-level recursion is free** (just put the type name in
  scope before its ctors; no fixpoint). The `Ctor` structure's `bound`/`closed` fields enforce
  well-formedness *by construction* — you literally can't build an ill-formed ctor.
- **Prelude.** Define a fixed `prelude : CtorEnv` (List `Nil`/`Cons`, Bool `True`/`False`, a
  `Pair` ctor, …). `typecheck`/`principalType` already take a `ctors` parameter, so a program's
  effective env is `prelude ++ userDeclaredCtors` — no Core change needed.

---

## 3. The surface language — planned stages (the north star)

`SurfaceLang.lean` has `Surface.{Expr,Ty,Pattern,PolyTy,PrimTy,PrimLitExpr}`. Elm-flavoured
(lambdas with pattern params + optional annotation; `let` with optional `∀`-scheme annotation;
`app`; `cons`/`list`/`pair` literals; `ife`; `match_` with `Pattern` branches; `ctor`/`var`).
Goal: a verified surface HM language on top of the (finally complete) core.

**Stage ordering** (after §1 lands + the §2 decisions you need):

0. **Core v2 (§1)** — finish the match fix, green + axiom-clean, committed. *(prerequisite)*
1. **Pretty-printers** for `Core.{Expr,Ty,PolyTy}` (and `Surface.*`). Quick, independent,
   pays for itself immediately (ends the `[1, .arrow (.fvar 0) (.fvar 0)]` misery). Do early.
2. **`Elaborates` relation** (surface → core): the *declarative* spec, carrying term- and
   type-name scope contexts (name resolution + scoped-tvar lowering are part of it; no
   intermediate IR). Mirror the proven `TypeOfHM`-relation architecture — clean, no error
   plumbing. Start with the non-pattern-compilation fragment (literals, lambda/app/let/var/ctor,
   the scoped-tvar lowering — which lands precisely on the Core scoped-var machinery).
3. **Bridge lemmas over the relation**: typing preservation, leaning on `TypeOfHM`/`typecheck`
   (the user wants "`surfaceE` elaborates to `coreE` ⇒ `coreE` typechecks", and converse). You
   can define surface well-typedness *via* elaboration (makes one direction definitional) or add
   an independent `Surface.TypeOf` and prove they agree — start with the former.
4. **`elaborate` function** (`Except Err Core.Expr`), proven to **refine** `Elaborates`
   (sound + complete) — exactly as `infer` refines `Infer`. Error plumbing lives only here.
5. **Pattern compilation** (nested surface patterns → Core's shallow ctor-match + the new
   wildcard; `fst`/`snd` are gone so pairs go via `Pair`-ctor match — uniform). *Unverified
   function + tests first.* This is the meaty algorithm (Augustsson/Maranget).
6. **(Optional, much later)** verified pattern compilation / dynamic-semantics preservation —
   the research-grade part; only needed if you give the surface its own operational semantics
   (you likely won't — "run a surface program = elaborate then run Core").

**Surface design facts settled this session:**
- **Pattern-`let`s DO generalize** (pure language, no value restriction): `let (a,b) = e in body`
  ⟿ `let t = e in let a = (π₁ via match) t in let b = (π₂ via match) t in body` — the outer
  name-`let`s generalize. Only *irrefutable* let-patterns; **refutable** let-patterns (e.g.
  `let (Cons h t) = e`) lower to a *non-exhaustive single-branch match* — well-typed, just
  partial/stuck on the unmatched case (no error term needed; that IS the failure semantics).
- **Typing ⊥ exhaustiveness.** `AllMatchesExhaustive` is a *separate premise of `progress` only*
  (not of `TypeOfHM`, not even of `preservation`). So refutable patterns are fine to typecheck;
  exhaustiveness is an orthogonal analysis you run only to *claim* progress.
- Scheme (`∀`) annotations pair with a single name binding; a monotype ascription can wrap any
  pattern (`let ((a,b) : (A,B)) = …`) as a scrutinee ascription.
- `ife c t f` ⟿ `match c with True => t | False => f` (Bool is a prelude `customTy`).
- A `match` must emit catch-alls/wildcards in a way consistent with §1's design; an all-wildcard
  match is fine now (after §1) and is `∀α. α → result`.

---

## 4. Bigger future idea (out of scope, noted): row types

Elm-style records via **Daan Leijen, "Extensible Records with Scoped Labels" (2005)**
(duplicate labels allowed, no lacks/presence machinery). It's **Core-deep** (a `Row` kind +
row unification with rewriting + re-proving unification completeness/principality + kinding the
type syntax) — a real project, NOT a surface-only layer. Deferred. (Parser library, for when you
reach parsing: research said `fgdorais/lean4-parser` (Reservoir `@fgdorais/Parser`) is the
de-facto community standard — actively maintained, Apache-2.0; pin it to a stable-matching tag,
or roll a ~100-line combinator set over a verified core.)

---

## 5. Guardrails + the workflow that worked

- **NEVER** `sorry`/`admit`/`axiom`/`native_decide`; **NEVER** weaken/restate a theorem to force
  green. Verify with `lean_verify` (axioms must be exactly `propext`/`Classical.choice`/`Quot.sound`).
  Decline/report beats a half-baked push. If a goal is unprovable without changing a *statement*,
  STOP and surface it (that's how the all-wildcard issue was caught).
- **The delegation pattern that worked well:** the human/lead locks the soundness-critical
  *definitions* (so no statement can drift), then a subagent re-threads the *proofs* under the
  guardrails, then the lead reviews (statements unchanged + axiom-clean). Subagents that are
  only *deleting* or *threading-given-fixed-defs* can't weaken anything. Give them: "restart the
  LSP first for fresh Core", "don't whole-project build", "report blockers, don't fake them".
- `lean_diagnostic_messages`: trust the `items` array (whole-file `success` is false while any
  part of a big file is red); scope with line ranges. Big proofs need time to re-elaborate.
- The `Infer.complete'` mutual carries `set_option maxRecDepth 4000` (needed — it's a ~1500-line
  mutual; the bump is structural, not a smell). `maxHeartbeats` is NOT needed (we removed it).
- Commit each green milestone separately; do NOT push.

---

## 6. What was accomplished this session (context)
Earlier in the session (all committed, green, axiom-clean): an **open-program soundness fix**
(seed the rigid set from `e.tyFreeVars`); a full **Part A audit** (`inferw-audit-verdict.md`) +
an anti-vacuity **capstone** (`namespace AuditCapstone`); **Part B cleanup** (deleted the dead
~735-line OUnify orientation stack, collapsed `unifyCore` into `unifyCoreK []`, doc sweep,
dropped an unnecessary `maxHeartbeats` bump). Then this Core-v2 effort (above). The metatheory
*was* fully sound+complete+principal+type-safe and axiom-clean; getting back there = §1.
