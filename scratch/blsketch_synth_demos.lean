import FHM.BLSketch
import FHM.BLSketch.Pretty

/-! # BLSketch — `synth` / `check` demos

Run with `z3` on `PATH`:
```
lake env lean scratch/blsketch_synth_demos.lean
```

Companion to `blsketch_z3_demos.lean` (raw oracle APIs). Exercises structural
synth, `check` via `Sub`, hole solving, match join / refine, nonlinear
scheme / mul, richer `let`/`letScheme` programs, and a small **stdlib** of
non-recursive BL helpers. Style matches `FHM/Examples.lean`.

**Recursion:** not supported (`Expr` has no `letRec`). See the stdlib section
for what is expressible today vs what needs recursive lets. -/

namespace BLSketch.Demo

/-- Rigid count variable `a`/`b`/… (index `i`). -/
def r (i : Nat) : Count := cvar .rigid i

/-- Print a judgement under `ctx`, with env lines when `ctx` is non-empty. -/
def showUnder (ctx : Ctx) (line : String) : IO Unit := do
  if !ctx.isEmpty then
    IO.println (Ctx.prettyEnv ctx)
    IO.println "---------"
  IO.println line

/-- Result string for `synth` (pretty type, optionally folded when ground). -/
def synthStr (ctx : Ctx) (e : Expr) : String :=
  match synth 0 [] ctx e with
  | none => "ill-typed"
  | some (_, ty) => Ty.prettyFolded ty

/-- Print `e  :  τ` (judgement parens for anno/match/if/let). -/
def showSynth (e : Expr) (ctx : Ctx := []) : IO Unit :=
  let eStr := Expr.prettyJudgement e (Ctx.termNames ctx)
  showUnder ctx s!"{eStr}  :  {synthStr ctx e}"

/-- Print `(e : τ) => typechecks ✓` / `doesn't typecheck ✗` for `check`. -/
def showCheck (e : Expr) (ty : Ty) (ctx : Ctx := []) : IO Unit :=
  let ok := (check 0 [] ctx e ty).isSome
  let verdict := if ok then "typechecks ✓" else "doesn't typecheck ✗"
  let eStr := Expr.prettyJudgement e (Ctx.termNames ctx)
  showUnder ctx s!"({eStr} : {ty}) => {verdict}"

/-- Print a bound scheme on its own. -/
def showScheme (s : BScheme) : IO Unit :=
  IO.println (toString s)

/-- Print `(τ' <: τ) => assignable ✓` / `not assignable ✗` for `forceSubtype`. -/
private def showForceSubtype (ty' ty : Ty) : IO Unit :=
  let ok := forceSubtype [] ty' ty
  let verdict := if ok then "assignable ✓" else "not assignable ✗"
  IO.println s!"({ty'}  <:  {ty}) => {verdict}"

/-- Show how `fillHoles` turns annotation holes into fresh inferables. -/
private def showFillHoles (ann : AnnoTy) : IO Unit :=
  let (_, ty) := fillHoles 0 ann
  IO.println s!"fillHoles: {ann}  ↦  {ty}  (each `_` → a fresh ?var)"

/-- Show one `solve` witness for inhabiting `ann` after `fillHoles`
(existence only — not a uniqueness check). -/
private def showAnnoWitness (e : Expr) (ann : AnnoTy) (ctx : Ctx := []) : IO Unit :=
  let (_, ty) := fillHoles 0 ann
  let eStr := Expr.prettyJudgement e (Ctx.termNames ctx)
  let msg :=
    match synth 0 [] ctx e with
    | none => "synth failed (no source type)"
    | some (_, ty') =>
      match subtypeProblem [] ty' ty with
      | none => "no subtype problem (shape mismatch)"
      | some ψ =>
        match solve ψ with
        | .unsat => "unsat — cannot inhabit that annotation"
        | .unknown => "unknown (oracle inconclusive)"
        | .witness σ =>
          "demand holes can be solved as " ++ Assign.prettyOn σ ty.inferVars
  showUnder ctx s!"can {eStr} inhabit {ann}?  ⇒  {msg}"

/-! ## Structural synth (no oracle) -/

-- []  :  BL 0 0
#eval showSynth .nil

-- [()]  :  BL (0 + 1) (0 + 1)  ↦  BL 1 1
#eval showSynth (.cons .unit .nil)

/-! ## `check` — wider demand via `Sub` / Z3 -/

-- ([] : BL 0 0) => typechecks ✓
#eval showCheck .nil (.bl (.lit 0) (.lit 0) .unit)

-- ([] : BL 0 5) => typechecks ✓
#eval showCheck .nil (.bl (.lit 0) (.lit 5) .unit)

-- ([] : BL 1 1) => doesn't typecheck ✗
#eval showCheck .nil (.bl (.lit 1) (.lit 1) .unit)

/-! ## Annotation holes

`BL _ _` is an *annotation* with holes. `fillHoles` replaces each `_` by a
fresh inferable (`?a`, `?b`, …). Synth of `([] : BL _ _)` returns that holey
demand type as-is (it does not substitute a solved assignment). Separately,
`showAnnoWitness` asks whether some assignment to those holes makes the
ascription succeed via `solve`. -/

/-- `nil` ascribed at `BL _ _` (holes filled by `synth`). -/
private def eAnnoNilHoles : Expr := .anno .nil (.bl none none .unit)

-- fillHoles: BL _ _  ↦  BL ?a ?b  (each `_` → a fresh ?var)
#eval showFillHoles (.bl none none .unit)

-- ([] : BL _ _)  :  BL ?a ?b
#eval showSynth eAnnoNilHoles

-- can [] inhabit BL _ _?  ⇒  demand holes can be solved as {?a↦0, ?b↦0}
#eval showAnnoWitness .nil (.bl none none .unit)

/-! ## `matchBL` — join bounds -/

/-- Context with a single mono binding `BL 0 5`. -/
private def ctxBL05 : Ctx := [.mono (.bl (.lit 0) (.lit 5) .unit)]

/-- Match on that binding: nil → `[]`, cons → `[()]`; join bounds. -/
private def eMatchJoin : Expr := .matchBL (.var 0 []) .nil (.cons .unit .nil)

-- x : BL 0 5
-- ---------
-- (match x with | [] => [] | y :: z => [()])  :  BL min(0, 0 + 1) max(0, 0 + 1)  ↦  BL 0 1
#eval showSynth eMatchJoin ctxBL05

-- Same join bounds, folded explicitly via `Count.fold` + `by decide`.
#eval IO.println s!"fold min(0, 0+1) = {Count.fold (.min (.lit 0) (.add (.lit 0) (.lit 1))) (by decide)}"
#eval IO.println s!"fold max(0, 0+1) = {Count.fold (.max (.lit 0) (.add (.lit 0) (.lit 1))) (by decide)}"

-- x : BL 0 5
-- ---------
-- (match x with | [] => () | y :: z => ())  :  Unit
#eval showSynth (.matchBL (.var 0 []) .unit .unit) ctxBL05

/-! ## `matchNil` / `matchCons` — ∀ guards -/

/-- Context: empty list type `BL 0 0`. -/
private def ctxEmpty : Ctx := [.mono (.bl (.lit 0) (.lit 0) .unit)]

/-- Context: non-empty list type `BL 3 5`. -/
private def ctxNonempty : Ctx := [.mono (.bl (.lit 3) (.lit 5) .unit)]

-- x : BL 0 0
-- ---------
-- (match x with | [] => ())  :  Unit
#eval showSynth (.matchNil (.var 0 []) .unit) ctxEmpty

-- x : BL 0 0
-- ---------
-- (match x with | y :: z => ())  :  ill-typed
#eval showSynth (.matchCons (.var 0 []) .unit) ctxEmpty

-- x : BL 3 5
-- ---------
-- (match x with | y :: z => ())  :  Unit
#eval showSynth (.matchCons (.var 0 []) .unit) ctxNonempty

/-! ## App — concrete check (no leftover holes) -/

/-- `λ(_ : BL 5 5). ()`. -/
private def eId5 : Expr := .lam (.bl (some (.lit 5)) (some (.lit 5)) .unit) .unit

/-- Context: mono `BL 5 5`. -/
private def ctxFive : Ctx := [.mono (.bl (.lit 5) (.lit 5) .unit)]

-- λ(x : BL 5 5). ()  :  BL 5 5 → Unit
#eval showSynth eId5

-- x : BL 5 5
-- ---------
-- (λ(y : BL 5 5). ()) x  :  Unit
#eval showSynth (.app eId5 (.var 0 [])) ctxFive

-- x : BL 5 5
-- ---------
-- (x : BL 5 5) => typechecks ✓
#eval showCheck (.var 0 []) (.bl (.lit 5) (.lit 5) .unit) ctxFive

-- x : BL 5 5
-- ---------
-- (x : BL 0 10) => typechecks ✓
#eval showCheck (.var 0 []) (.bl (.lit 0) (.lit 10) .unit) ctxFive

-- x : BL 5 5
-- ---------
-- (x : BL 20 20) => doesn't typecheck ✗
#eval showCheck (.var 0 []) (.bl (.lit 20) (.lit 20) .unit) ctxFive

/-! ## Nonlinear — flatMap scheme inst + mul subtype -/

/-- `∀ a b c d. BL a b → (Unit → BL c d) → BL (a*c) (b*d)`. -/
private def flatMapScheme : BScheme where
  binders := 4
  body :=
    .arrow (.bl (r 0) (r 1) .unit)
      (.arrow (.arrow .unit (.bl (r 2) (r 3) .unit))
        (.bl (.mul (r 0) (r 2)) (.mul (r 1) (r 3)) .unit))

/-- Context whose nearest binder is `flatMapScheme`. -/
private def ctxFlat : Ctx := [.scheme flatMapScheme]

-- ∀ a b c d. BL a b → (Unit → BL c d) → BL (a * c) (b * d)
#eval showScheme flatMapScheme

-- x : ∀ a b c d. BL a b → (Unit → BL c d) → BL (a * c) (b * d)
-- ---------
-- x @2 @5 @3 @4  :  BL 2 5 → (Unit → BL 3 4) → BL (2 * 3) (5 * 4)  ↦  …
#eval showSynth (.var 0 [.lit 2, .lit 5, .lit 3, .lit 4]) ctxFlat

-- (BL (2 * 3) (5 * 4)  <:  BL 6 20) => assignable ✓
#eval showForceSubtype
  (.bl (.mul (.lit 2) (.lit 3)) (.mul (.lit 5) (.lit 4)) .unit)
  (.bl (.lit 6) (.lit 20) .unit)

/-! ## Richer programs — nested `let` / `letScheme`

Non-recursive plumbing: build lists, pack a scheme, use it under a let. -/

/-- `let xs = [(), ()] in let ys = () :: xs in match ys with | _ :: t => t`. -/
private def eLetTail : Expr :=
  .let_ (.cons .unit (.cons .unit .nil))
    (.let_ (.cons .unit (.var 0 []))
      (.matchCons (.var 0 []) (.var 1 [])))

-- let x = [(), ()] in
-- let y = () :: x in
-- (match y with | z :: u => u)  :  BL pred(0 + 1 + 1 + 1) …  ↦  BL 2 2
#eval showSynth eLetTail

/-- Pack `∀ a. BL a a → BL a a` (same as library `idScheme`) and instantiate. -/
private def eLetSchemeId : Expr :=
  .letScheme
    { binders := 1, body := .arrow (.bl (r 0) (r 0) .unit) (.bl (r 0) (r 0) .unit) }
    (.lam (.bl (some (r 0)) (some (r 0)) .unit) (.var 0 []))
    (.app (.var 0 [.lit 3]) (.cons .unit (.cons .unit (.cons .unit .nil))))

-- let x : ∀ a. BL a a → BL a a = λ(y : BL a a). y in
-- x @3 [(), (), ()]  :  BL 3 3
#eval showSynth eLetSchemeId

/-! ## Stdlib — definable **without** recursion

Element type is fixed to `Unit` in this toy. Bounds are the interesting bit.
Bodies are real `Expr`s packed with `letScheme` where useful. -/

namespace Stdlib

/-- `singleton : Unit → BL 1 1`. -/
def eSingleton : Expr :=
  .lam .unit (.cons (.var 0 []) .nil)

/-- `∀ a b. Unit → BL a b → BL (a+1) (b+1)`. -/
def consScheme : BScheme where
  binders := 2
  body :=
    .arrow .unit
      (.arrow (.bl (r 0) (r 1) .unit)
        (.bl (.add (r 0) (.lit 1)) (.add (r 1) (.lit 1)) .unit))

/-- Body of `cons`. -/
def eCons : Expr :=
  .lam .unit
    (.lam (.bl (some (r 0)) (some (r 1)) .unit)
      (.cons (.var 1 []) (.var 0 [])))

/-- `∀ a b. BL (a+1) b → Unit` — cons-only match (`1 ≤ a+1` always). -/
def headScheme : BScheme where
  binders := 2
  body := .arrow (.bl (.add (r 0) (.lit 1)) (r 1) .unit) .unit

/-- Body of `head`. -/
def eHead : Expr :=
  .lam (.bl (some (.add (r 0) (.lit 1))) (some (r 1)) .unit)
    (.matchCons (.var 0 []) (.var 0 []))

/-- `∀ a b. BL (a+1) (b+1) → BL a b` — `Sub` folds `pred(·+1)`. -/
def tailScheme : BScheme where
  binders := 2
  body :=
    .arrow (.bl (.add (r 0) (.lit 1)) (.add (r 1) (.lit 1)) .unit)
      (.bl (r 0) (r 1) .unit)

/-- Body of `tail`. -/
def eTail : Expr :=
  .lam (.bl (some (.add (r 0) (.lit 1))) (some (.add (r 1) (.lit 1))) .unit)
    (.matchCons (.var 0 []) (.var 1 []))

/-- Defaulting “head”: nil and cons both return `Unit`. -/
def eHeadOrUnit : Expr :=
  .lam (.bl (some (.lit 0)) (some (.lit 5)) .unit)
    (.matchBL (.var 0 []) .unit (.var 0 []))

-- λ(x : Unit). [x]  :  Unit → BL (0 + 1) (0 + 1)
#eval showSynth eSingleton

-- λ(x : Unit). λ(y : BL a b). x :: y  :  Unit → BL a b → BL (a + 1) (b + 1)
#eval showSynth eCons

-- λ(x : BL (a + 1) b). match x with | y :: z => y  :  BL (a + 1) b → Unit
#eval showSynth eHead

-- λ(x : BL (a + 1) (b + 1)). match x with | y :: z => z
--   :  BL (a + 1) (b + 1) → BL pred(a + 1) pred(b + 1)
#eval showSynth eTail

-- Pack + use: `head @0 @5 [(), (), ()]`
def eUseHead : Expr :=
  .letScheme headScheme eHead
    (.app (.var 0 [.lit 0, .lit 5])
      (.cons .unit (.cons .unit (.cons .unit .nil))))

-- let x : ∀ a b. BL (a+1) b → Unit = … in x @0 @5 [(), (), ()]  :  Unit
#eval showSynth eUseHead

-- Pack cons + head: `head @0 @4 (cons @2 @3 () [(), ()])`
def eUseConsHead : Expr :=
  .letScheme consScheme eCons
    (.letScheme headScheme eHead
      (.app (.var 0 [.lit 0, .lit 4])
        (.app (.app (.var 1 [.lit 2, .lit 3]) .unit)
          (.cons .unit (.cons .unit .nil)))))

-- nested let cons/head pipeline  :  Unit
#eval showSynth eUseConsHead

-- Pack tail and strip one cons off a length-3 list
def eUseTail : Expr :=
  .letScheme tailScheme eTail
    (.app (.var 0 [.lit 2, .lit 2])
      (.cons .unit (.cons .unit (.cons .unit .nil))))

-- let x : ∀ a b. BL (a+1) (b+1) → BL a b = … in
-- x @2 @2 [(), (), ()]  :  BL 2 2
#eval showSynth eUseTail

-- λ(x : BL 0 5). match x with | [] => () | y :: z => y  :  BL 0 5 → Unit
#eval showSynth eHeadOrUnit

/-! ### Signatures that need recursion (not yet expressible as bodies)

`Expr` has `let_` / `letScheme` but **no `letRec`**. Non-goals in `BLSketch.lean`
explicitly list recursion. So these stay signature-only until we add annotated
recursive lets:

| Function | Typical bounds | Why recursion |
| --- | --- | --- |
| `map` | `BL a b → BL a b` | walk every cons |
| `filter` | `BL a b → BL 0 b` | walk + conditional keep |
| `flatMap` / `concatMap` | mul of lengths | walk + append results |
| `append` | `BL a b → BL c d → BL (a+c) (b+d)` | walk the left list |
| `reverse` | `BL a b → BL a b` | walk + cons onto accumulator |
| `fold` / `length` | needs a value `Nat` or similar | walk |

**What it would take** (minimal path):
1. Add `Expr.letRec` (single binding is enough for the table above).
2. Typing: binder in scope in its own body; **require an annotation / scheme**
   (Mycroft: polymorphic recursion isn’t inferable). Mono recursion can reuse
   `let_`-style synth; bound-poly recursion should pack like `letScheme` and
   instantiate at recursive call sites (`f @lo @hi …`).
3. Reuse existing match refinement (`consCtx` / `pred`) — that part is ready.
4. Wire `synth` / `TypeOf` / `synth_sound` (and Pretty).

Until then, `flatMapScheme` in the parent demo is a **library axiom** (scheme in
the context), not a userland definition. -/

/-- Signature-only reminder. -/
def mapScheme : BScheme where
  binders := 2
  body :=
    .arrow (.arrow .unit .unit)
      (.arrow (.bl (r 0) (r 1) .unit) (.bl (r 0) (r 1) .unit))

/-- Signature-only: filter may shrink to `0..hi`. -/
def filterScheme : BScheme where
  binders := 2
  body :=
    .arrow (.arrow .unit .unit)
      (.arrow (.bl (r 0) (r 1) .unit) (.bl (.lit 0) (r 1) .unit))

/-- Signature-only append. -/
def appendScheme : BScheme where
  binders := 4
  body :=
    .arrow (.bl (r 0) (r 1) .unit)
      (.arrow (.bl (r 2) (r 3) .unit)
        (.bl (.add (r 0) (r 2)) (.add (r 1) (r 3)) .unit))

-- ∀ a b. (Unit → Unit) → BL a b → BL a b   (needs letRec to implement)
#eval showScheme mapScheme

-- ∀ a b. (Unit → Unit) → BL a b → BL 0 b   (needs letRec)
#eval showScheme filterScheme

-- ∀ a b c d. BL a b → BL c d → BL (a + c) (b + d)   (needs letRec)
#eval showScheme appendScheme

end Stdlib

end BLSketch.Demo
