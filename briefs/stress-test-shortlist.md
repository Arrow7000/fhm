# Suspect-feature stress-test shortlist (subagent survey, 2026-09-03)

> Editor's note: the subagent's stream was cut mid-way through the last line of item 8 (a provider error, cost 0); items 1–8 are otherwise complete and intact as delivered.

---

# FHM smoke/stress-test shortlist — ranked by bug-finding probability per test file

**Ground truth note (build state).** `lake build fhm` is currently **broken on `main`**: `FHM/Bounds/Typing.lean`'s `agreesTemplate` is missing the `Ty.bl` case (added only on the `erasure-migration` branch, which is where the stale `.lake/build/bin/fhm` in the workspace came from). All probing below was done on a fresh build of `main` in a throwaway clone (`/private/var/folders/.../T/opencode/fhm-clone`) with that one-line branch fix applied — the workspace itself was not modified. Whoever writes the tests needs that fix landed (or `main` re-pointed) first; the in-tree binary predates the current tree by weeks.

Polymorphic recursion is excluded per instructions. Every "expected" below was either observed on the freshly built CLI or follows from the README's advertised behavior; "actual today" entries are measured facts, not speculation.

---

## 1. Executable exhaustiveness checker vs declarative coverage — false negatives on nested ADTs

**Where:** `FHM/SurfaceBridge.lean` — `checkExhaustive` / `matchExhaustiveB` / `tyArgsGuess` (~L4478–4653), `dTreeExhaustiveB`; soundness theorem `checkExhaustive_sound`; design record `briefs/next-agent-brief-surface-bridge-followups.md` lesson 1 (three coverage designs, "fail-closed").

**Why suspect:** `checkExhaustive_sound` claims only `= true → SurfaceCovers` — soundness, *not* completeness. At `match_` the checker recovers the scrutinee type by `tyNameFromPatterns` and seeds `tyArgs` via `tyArgsGuess`, which emits `List.replicate paramCount (.prim .unit)` placeholders; the docstring admits this is "fail-closed for nested ADTs when placeholders don't instantiate field ADTs." So the theorem is true while the checker rejects **fully-covered** matches. I confirmed the exact boundary empirically: nested `Tree` patterns pass (fields share the same ADT), but nested `Maybe` and nested `List` fail **in both spellings** (explicit ctors and sugar). The gap is invisible to the theorem and to type safety — it just makes correct programs unrunnable.

**Test sketch** (positive cases are all expected to run; today the first two are *rejected*):

```elm
type Maybe a =
  | Just a
  | Nothing

let f m =
  match m with
  | Just (Just x) -> x
  | Just Nothing -> 0
  | Nothing -> 0

(f (Just (Just 7)), f (Just Nothing), f Nothing)
```
Expected `(7, (0, 0)) : (Int, (Int, Int))`. **Actual today: `[exhaustiveness] match not exhaustive`.**

```elm
let g l =
  match l with
  | (h :: t) :: rest -> h
  | [] :: rest -> 0
  | [] -> 9

g [[1,2],[]]
```
Expected `1 : Int` (same failure with explicit `Cons (Cons h t) rest | Cons Nil rest | Nil`). **Actual today: rejected.** Control that *does* pass (pin it): nested `Tree` — `Node x Leaf (Node y _ _) -> x + y` gives `3`.

Negatives that must stay rejected: `Cons h (Cons i t) | Nil` (missing `Cons h Nil`) — exhaustiveness; `Cons (Cons h t) rest | Nil` on a `List Int` scrutinee — *typecheck* (ill-typed nested pattern, and the checker must not be blamed).

**Bug classes caught:** checker/`tyArgsGuess` regressions, occurrence-typing drift for nested columns, sugar-vs-ctor asymmetries (`::` and `[]` vs `Cons`/`Nil` take different code paths in `checkExhaustive`). Also note the if-compiler path: `emit` was once fixed to omit wildcard branches (briefs lesson 2) — this suite is the executable regression net for that class.

---

## 2. Data-decl parser greediness: a top-level body starting with an identifier is eaten as a constructor field

**Where:** `FHM/Surface/Parse.lean` — `dataCtor` (`takeMany (withBacktracking ctorField)`), `ctorField` → `tyApp` → `tyAtom` (~L490–520); `program`/`programItems` (~L1282+). README: *"Lexer/parser correctness is deliberately not proven; the verified story starts at the Surface AST."*

**Why suspect:** This is the one stage with **zero theorem coverage**, and I confirmed a live bug in it. `dataCtor`'s field list has no layout guard, so after the last ctor of a `type` decl, a following line that begins with an identifier-like token is absorbed as a ctor field; the program body then defaults to `()`. Verified with a Lean `#eval` probe on the clone: `parseProgram "type Color = Red | Green | Blue\nRed\n"` yields ctor field counts **`[0, 0, 1]`** (ctor `Blue` gained a phantom field named `Red`) and body `primLit unit`. The same happens for a lowercase body (`red`), and `red + 1` becomes a raw parse error. Bodies that start with non-identifiers (`5`, `()`, `[]`, `True`) are unaffected, and **inserting any top-level `let` before the body masks the bug** — which is why the existing fixtures (`live.fhm`, `hover-rich.fhm`) never hit it.

**Test sketch** (must-parse-then-eval; today it mis-lowers):

```elm
type Color = Red | Green | Blue

Red
```
Expected: report `Red : Color`, result `Red`. **Actual today: `[lower] lowering failed (unbound name, bad decl, or rejected sugar)`** — the worst failure mode: the decl is silently corrupted and the body dropped, rather than a parse error at the right span. Sibling cases for the same file: body `Just 1` after `type Maybe a = …` (ctor `Nothing` gains field `Just 1`), body `red` (absorbed), body `red + 1` (parse error), and the masking control `let z = 0` before the body (works).

**Bug classes caught:** lexer/parser drift (regression net for the one unverified layer), silent wrong-program acceptance (corrupted decl + missing body), error-span honesty (`fhm diagnose` reports the decl span, not the body).

---

## 3. "Annotation-wins" display: BL sidecar leaks into HM mode + tyvar misalignment in ascriptions

**Where:** `FHM/Bounds/Report.lean` — `BindingReport.pretty` / `ProgramReport.programPretty` (priority: ascription-ann → synth → HM), `assembleProgramReport`; sidecar produced by `FHM/Bounds/Erase.lean` `eraseTy`/`erasePolyTy`/`defaultListAnn`/`eraseSchemeAnn`; wired in `FHM/Live.lean` (`assembleProgramReport … ep`).

**Why suspect:** The report path is unproven glue between the verified pipeline and the user, and it has two confirmed defects visible in the *existing* fixture `scratch/live.fhm`: `filter`, written `{a} (p : a -> Bool) : {b} List a -> List a`, is displayed as **`∀ b. (b → Bool) → BL 0 0 b → BL 0 0 b`**. Two distinct bugs: (a) `eraseTy` invents `defaultListAnn [0,0]` for every *bare* `List` in an ascription, and `BindingReport.pretty` prefers the sidecar over the HM type whenever an ann exists (which is always when foralls are present, since `eraseSchemeAnn` returns `some` iff foralls are nonempty) — so HM mode prints bounds syntax the user never wrote; (b) `erasePolyTy` resolves named tyvars against `σ.foralls` **only**, missing the head `{a}` merged in by `finalizeAnn`, so `a` collapses onto `b` via `getD 0` — the displayed quantifier is misaligned with the real scheme (`∀ a b. …`).

**Test sketch:** a fixture with several ascription shapes — bare-`List` scheme (`let len {a} (l : List a) : Int = …`), mixed head/residual tyvars (`filter` as above), mono ascription (`let f (x : Int) : Int = x`), unannotated binder — run `fhm --json` and assert each `bindings[].type` string. Expected for `filter`: `∀ a b. (a → Bool) → List a → List a` (or at minimum: `List`, never `BL`, in HM mode). Also pin `hover-rich.fhm`'s current correct outputs (`map : ∀ a b. (a → b) → List a → List b`) as controls. No negative stage — this is a display-equality suite.

**Bug classes caught:** ascription-wins priority misapplied in HM mode, sidecar/HM misalignment feeding editor hover + the Monaco playground (`enrichFromSynth` path), silent misnaming that users will read as a type error.

---

## 4. Lexically scoped type variables: README claim vs what annotations can actually see

**Where:** `FHM/SurfaceBridge.lean` — `finalizeAnn`, `letAnnTyPrefix` ("Empty when there is no finalized scheme… `{t}` alone does not extend the scope"), `wrapCoreParams`, `lowerPolyAnn`; `FHM/Surface/Parse.lean` `tvarIndex` (first-match shadowing); `FHM/Core.lean` `LamSeed`/rigid-`K` story; briefs: `next-agent-brief-surface-lang.md` §4, `next-agent-brief-type-holes.md`, `next-agent-brief-phase6-adversarial-review.md` ("nested `letRecAnn` schemes cannot reference an outer scoped type variable" — flagged limitation).

**Why suspect:** The README advertises *"annotations can reference type variables quantified in outer scopes"*, but I measured a three-way asymmetry: **λ-param annotations** see the outer scheme (`let f {a} (x : a) : Wrap a = Mk ((\ (y : a) -> y) x)` works, `f True` → `Mk True`); **let-RHS annotations do not** (`let f {a} (x : a) : Wrap a = let g : a -> a = \y -> x in …` fails at *lower* with the generic message — the tyvar scope for let-anns is empty unless the inner let itself finalizes a scheme); and **inner `{a}` re-bindings are silently merged/fresh-decided** with no documented rule (inner `let g {a} (y : Int) : a = x` under outer `x : a = Bool` is correctly rejected, so inner `{a}` behaves fresh — but `mergeTyParamNames`/`eraseDups` merging of duplicate names is untested and undiagnosed). Additionally the phase-6 memo's flagged limitation (nested rec-group schemes can't reference outer scoped vars) is exactly the kind of restriction a smoke test should pin.

**Test sketch:**

Positive (must keep working): the λ-param case above, plus `let f {a} (x : a) : Wrap a -> Wrap a = \w -> Mk x` with `f True (Mk True)` → `Wrap Bool` (verified).
Negative that today *contradicts the README* (expected to work if the claim were true; currently `[lower]` reject):
```elm
let f {a} (x : a) : Wrap a =
  let g : a -> a = \y -> x in
  Mk (g x)
```
Shadowing pin (must-fail at **typecheck**): `let f {a} (x : a) : Wrap a = let g {a} (y : Int) : a = x in Mk (g 3)` with `f True` — inner `a` is fresh ≠ outer `Bool`. (Verified correctly rejected today; keep as regression.)
Head-binder-only variant (must-fail at **lower**, per the type-holes brief): `let f {a} (x : a) (w : Wrap a) = Mk x` — typarams never enter scope without a finalized scheme; with `: Wrap a` added it must pass (verified).

**Bug classes caught:** tyvar-scope resolution regressions, rigid-vs-flexible classification (`LamSeed`, escape checks), README/documentation drift, silent merging of duplicate tyvar names.

---

## 5. Head-binder packing fallback: partial params + return annotation are broken (type-holes brief PR1)

**Where:** `FHM/SurfaceBridge.lean` `finalizeAnn` (~L3561: on `paramsToArrows` failure it falls back to `mergeTyParams tyParams ann`, i.e. the scheme body becomes the *bare return*), `paramsToArrows` (any `none` domain → `none`); `briefs/next-agent-brief-type-holes.md` (PR1: "No packing fallback that sets scheme body to bare return"; success criterion unmet).

**Why suspect:** The brief predicted exactly this bug and its PR1 success criteria are checkable from a `.fhm` file: `let f (x : Int) y : Int = y + 1` must typecheck (outer `letIn none`, λ-pin `Int`, λ-none for `y`, inner return pin) — **today it fails at typecheck**, while the identical program without `: Int` works (`Int → Int → Int`, result `3`). The fallback sets the let's scheme to bare `Int`, so the λs sit *outside* the ascription and the body check degenerates. This is a case where the surface syntax can express something the elaborator mishandles — precisely a "premises easy to violate invisibly" gap: no theorem is false, but a documented-must-work program is rejected.

**Test sketch:**

Negative (currently broken; per brief must become positive): `let f (x : Int) y : Int = y + 1` then `f 1 2` → expected `3`, binder type `Int → ?b → Int` (mono in `y`), *not* `Int → Int` and not a typecheck reject.
Positive control (works, pin it): `let f (x : Int) y = y + 1` → `Int → Int → Int`, `3`.
Negative that must keep failing (typecheck): `let f (x : Int) y : Int = x + y` then `f True 1`.
Also pin the fully-annotated packing path: `let addInts (a : Int) : Int -> Int = \b -> a + b` → `Int → Int → Int` (verified working).

**Bug classes caught:** `finalizeAnn` fallback shape, `wrapCoreParams`/`letAnnTyPrefix` interaction, docs-vs-reality for head binders (the README showcases `addInts`-style hybrid binders but not the partial ones).

---

## 6. `eraseProgram` always runs in HM mode — the sorried shim between parse and the proven pipeline

**Where:** `FHM/Live.lean` `checkPipeline` (L184–191: `hmRequireNoBl` gate, then `let ep := eraseProgram p; let p := ep.toProgram` — **every** HM-mode program is rewritten before `lowerProgram`); `FHM/Bounds/Erase.lean` `eraseProgram` (carries `noBl := by sorry`, ~L356) and `FHM/Bounds/Pipeline.lean` (five `sorry`ed bridge theorems, L124–196); gate tests `programContainsBl`/`hmRequireNoBl_*`.

**Why suspect:** `surface_type_safe` is stated for a `Surface.Program`, but the CLI hands the verified pipeline the *erased rewrite* of the parsed program. The rewrite rewrites annotation types (`eraseTy` maps `bool`→`customTy Bool`, invents list sidecars), strips `natBinders` from bindings, and normalizes param anns — with a `sorry` inside the package invariant. Nothing proved covers "erase is identity on BL-free programs"; a bug here would silently change what the theorems' input actually is. The gate side (`hmRequireNoBl`) I verified behaves correctly today (BL in λ-param anns, inside arrow schemes, and in ctor fields all rejected at the *bounds* stage; plain `List Int` accepted; `--bl` mode runs), so the file is mostly a *regression net plus a gap* — and the type-holes-style question "what else does erase touch?" is exactly what a smoke file answers.

**Test sketch:** a BL-gate sweep as must-fail-at-**bounds** (verified today, keep): `let f (xs : BL 0 5 Int) = 5`, `let f : (BL 0 5 Int -> Bool) -> Bool = …`, ctor-field `BL`; controls that must pass in HM mode: `let xs : List Int = [1,2,3]`, `bl-hole-ok.fhm` under `--bl` (verified: `BL 2 5 Int`, `[1,2]`). Add an identity probe: for each fixture, compare `fhm run` binder types against hand-written expectations — any mismatch is the erase rewrite leaking (e.g. the `Nat` case: `let f (n : Nat) = n` fails at lower today although Core has a primitive `Nat` — the surface `KindEnv` never declares it; likely a finding that `Nat` is unnameable in `.fhm`).

**Bug classes caught:** silent pre-lower rewrites, sorried-glue regressions (the only `sorry`s between the user and the proven stack), stage-label honesty for the gate.

---

## 7. Surface `letIn` is unreachable: every top-level binding is a `letRec` (singleton groups included)

**Where:** `FHM/SurfaceLang.lean` `desugarGroups` (foldr, nonempty groups → always `letRecIn`, incl. size 1), `Program.term`; `FHM/Core.lean` `TypeOfHM.letIn` vs `TypeOfHM.letRec` (cofinite premises differ); `briefs/next-agent-brief-surface-bridge-program-scc.md` decision 2 ("Always `letRecIn` for nonempty groups (incl. size 1). Tagged nonrec/rec deferred") and `briefs/letrec-design.md` §2.4.

**Why suspect:** The declarative metatheory has *two* generalisation rules (`letIn` generalises before use; `letRec` binds mono in RHSs and generalises at exit), and the differences between them (e.g. a non-recursive binding that could be used polymorphically inside its own RHS) are exactly what the surface **cannot express**: `desugarGroups` makes every top-level binding a `letRec`. So the proven `letIn` rule is exercised only *internally* by the elaborator's wrapper nest (the `letRecElab` Λ-nest), never from source. Related fragile spots worth pinning: generalisation timing for singleton unannotated groups (verified working: `let g = \y -> k` after `let k = 5` gives `∀ a. a → Int` and `g 1`/`g True` both run), presentation-order reversal in the report (`zipBindingTypes` reverses each group chunk — writing `let z = …; let y = …` prints `y, z`), and the n² elaboratum (complexity-budget §3: n members ⇒ n copies of an n-binding group + `shiftFrom` renumbering — "does the n² blowup actually serve a purpose or hide a design flaw" is the user's stated worry; it is *not yet landed as the promoted form*).

**Test sketch:**

```elm
let k = 5
let g = \y -> k
(g 1, g True)
```
Expected `(5, 5)`, `g : ∀ a. a → Int` (verified — pins mono-then-generalise for size-1 groups).
Singleton annotated member (only binding): `let f : {a} a -> a = \x -> x` + `(f 1, f True)` → `(1, True)` (verified).
Order/reversal pin: write `z` then `y` (dependent), assert the JSON binding order and each type (verified: report prints `y, z` — decide and pin the intended order).
Negative: `let x = x` then `x` — must fail at **typecheck** (occurs-check/infinite type through the mono group); duplicate names (`let a = 1` twice) — must fail at **lower** (`sccGroups` Nodup guard).
Scale probe (document, don't assert): 12- and 24-member annotated groups — my timings were too noisy to demonstrate the n² shape; the file should record `checkNs`/`evalNs` so a post-promotion refactor has a before/after.

**Bug classes caught:** generalisation-timing regressions, `zipBindingTypes`/`collectTopSchemes` misalignment (this same plumbing produced the misaligned names in item 3), deep `shiftFrom` index arithmetic at group size ≥ 3.

---

## 8. SCC condensation + Kahn ordering edge cases (groups depending on groups)

**Where:** `FHM/SurfaceBridge.lean` — `sccGroups`, `bindDigraph`/`bindSuccTable`, `sccBeforeEdges`, `kahnTopo`/`kahnGo`, `ValidBindingGroups` (~L1006–1255); `FHM/Scc/Kosaraju.lean` (`kosaraju_sound`, `ValidSccPartition.eqv_mutual`); adequacy `sccGroups_sound`/`_complete`; brief warnings: name-Nodup is load-bearing ("without it condensation can cycle and Kahn truncates — unconstrained form was false"), `kahnTopo_edge_before` was once false (OOB indeg 0).

**Why suspect:** `sccGroups_complete` is deliberately `isSome`-only (order freedom), and `ValidBindingGroups.topo` fixes callee-outer; the *concrete* order the executable picks is untested from source. I probed the main shapes and they all pass today — backward-order declarations (`let z = y + 1` before `let y = 41`), a diamond, even/odd + dependent, a 5-group order-insensitive mix with annotated poly callees, and cross-group use of a poly singleton at two instantiations (`let g = \k -> (f k, f [k])` with `f : {a} a -> List a` in a later group → works, `g : ∀ a. a → (List a, List (List a))`). What remains unexercised: disjoint SCC pairs written interleaved (intra-condensation order freedom), a group whose only dependency is through an *annotated* member's body (rigid-scheme path in the condensation), and self-edge-only singletons.

**Test sketch:** one file with 3 disjoint mutually-recursive pairs declared interleaved (A1 B1 A2 B2 A3 B3 with each Ai↔Bi mutual, cross-pair independent), body referencing all six; assert all six binder types and the result — pins condensation order-independence. Second file: a poly callee group (`f : {a} a -> List a` + `h`) consumed by an unannotated pair (`p`, `q` mutually recursive, both calling `f` at different types) — expected `p, q` each at their pinned monotype then generalised (crosses `sccBeforeEdges` direction and the annotated-callee path). Negative: duplicate names → lower-stage reject (Nodup guard, verified reachable).

**Bug classes caught:** Kahn indeg/OOB regressions, topo