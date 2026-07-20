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

open BLSketch

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

-- []  :  ill-typed  (bare nil does not synth — use nil @α)
#eval showSynth .nil

-- nil @Unit  :  BL 0 0 Unit
private def ctxNil : Ctx := [.scheme BLSketch.Examples.nilScheme]
#eval showSynth (.var 0 [.ty .unit]) ctxNil

-- [()]  :  BL 1 1 Unit  (nil @Unit in spine)
#eval showSynth (.cons .unit (.var 0 [.ty .unit])) ctxNil

-- true / false  :  Bool
#eval showSynth .true
#eval showSynth .false

/-! ## `check` — wider demand via `Sub` / Z3 -/

-- (nil @Unit : BL 0 0) => typechecks ✓
#eval showCheck (.var 0 [.ty .unit]) (.bl (.lit 0) (.lit 0) .unit) ctxNil

-- (nil @Unit : BL 0 5) => typechecks ✓
#eval showCheck (.var 0 [.ty .unit]) (.bl (.lit 0) (.lit 5) .unit) ctxNil

-- (nil @Unit : BL 1 1) => doesn't typecheck ✗
#eval showCheck (.var 0 [.ty .unit]) (.bl (.lit 1) (.lit 1) .unit) ctxNil

-- ([] : BL 0 0) => doesn't typecheck ✗  (bare nil)
#eval showCheck .nil (.bl (.lit 0) (.lit 0) .unit)

/-! ## Annotation holes

`BL _ _` is an *annotation* with holes. `fillHoles` replaces each `_` by a
fresh inferable (`?a`, `?b`, …). Synth of `([] : BL _ _)` returns that holey
demand type as-is (it does not substitute a solved assignment). Separately,
`showAnnoWitness` asks whether some assignment to those holes makes the
ascription succeed via `solve`. -/

/-- `nil` ascribed at `BL _ _` (holes filled by `synth`) — still needs a synthable source. -/
private def eAnnoNilHoles : Expr := .anno (.var 0 [.ty .unit]) (.bl none none .unit)

-- fillHoles: BL _ _  ↦  BL ?a ?b  (each `_` → a fresh ?var)
#eval showFillHoles (.bl none none .unit)

-- (nil @Unit : BL _ _)  :  BL ?a ?b  (with ctxNil)
#eval showSynth eAnnoNilHoles ctxNil

-- can nil @Unit inhabit BL _ _?  ⇒  demand holes can be solved as {?a↦0, ?b↦0}
#eval showAnnoWitness (.var 0 [.ty .unit]) (.bl none none .unit) ctxNil

/-! ## `matchBL` — join bounds -/

/-- Context with a single mono binding `BL 0 5`. -/
private def ctxBL05 : Ctx := [.mono (.bl (.lit 0) (.lit 5) .unit)]

/-- Match on that binding: nil → `nil @Unit`, cons → `[()]`; join bounds. -/
private def eMatchJoin : Expr :=
  .matchBL (.var 0 []) (.var 1 [.ty .unit]) (.cons .unit (.var 1 []))

-- x : BL 0 5
-- nil : ∀ {α}. BL 0 0 α
-- ---------
-- (match x with | [] => nil @Unit | y :: z => [()])  :  BL 0 1
#eval showSynth eMatchJoin (ctxBL05 ++ ctxNil)

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
  binders := [.count, .count, .count, .count]
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
#eval showSynth (.var 0 [.count (.lit 2), .count (.lit 5), .count (.lit 3), .count (.lit 4)]) ctxFlat

-- (BL (2 * 3) (5 * 4)  <:  BL 6 20) => assignable ✓
#eval showForceSubtype
  (.bl (.mul (.lit 2) (.lit 3)) (.mul (.lit 5) (.lit 4)) .unit)
  (.bl (.lit 6) (.lit 20) .unit)

/-! ## Richer programs — nested `let` / `letScheme`

Non-recursive plumbing: build lists, pack a scheme, use it under a let. -/

/-- `let xs = [(), ()] in let ys = () :: xs in match ys with | _ :: t => t`. -/
private def eLetTail : Expr :=
  .let_ (.cons .unit (.cons .unit (.var 0 [.ty .unit])))
    (.let_ (.cons .unit (.var 0 []))
      (.matchCons (.var 0 []) (.var 1 [])))

-- let x = [(), ()] in …  :  BL 2 2  (needs nil @Unit in ctx)
#eval showSynth eLetTail ctxNil

/-- Pack `∀ a. BL a a → BL a a` (same as library `idScheme`) and instantiate. -/
private def eLetSchemeId : Expr :=
  .letScheme
    { binders := [.count],
      body := .arrow (.bl (r 0) (r 0) .unit) (.bl (r 0) (r 0) .unit) }
    (.lam (.bl (some (r 0)) (some (r 0)) .unit) (.var 0 []))
    (.app (.var 0 [.count (.lit 3)]) (.cons .unit (.cons .unit (.cons .unit (.var 1 [.ty .unit])))))

-- let x : ∀ a. BL a a → BL a a = λ(y : BL a a). y in
-- x @3 [(), (), ()]  :  BL 3 3
#eval showSynth eLetSchemeId ctxNil

/-! ## Element mismatch — `Unit` into `BL _ _ Bool` -/

private def ctxNilBool : Ctx := [.scheme BLSketch.Examples.nilScheme]

-- nil @Bool  :  BL 0 0 Bool
#eval showSynth (.var 0 [.ty .bool]) ctxNilBool

-- () :: nil @Bool  :  ill-typed  (head is Unit, tail elem is Bool)
#eval showSynth (.cons .unit (.var 0 [.ty .bool])) ctxNilBool

-- (() :: nil @Bool : BL 1 1 Bool) => doesn't typecheck ✗
#eval showCheck (.cons .unit (.var 0 [.ty .bool])) (.bl (.lit 1) (.lit 1) .bool) ctxNilBool

/-! ## Stdlib — type-polymorphic nil / cons / head / tail -/

namespace Stdlib

open BLSketch.Examples

/-- `singleton : ∀ {α}. α → BL 1 1 α`. -/
def singletonScheme : BScheme where
  binders := [.type]
  body := .arrow (.tbind 0) (.bl (.lit 1) (.lit 1) (.tbind 0))

def eSingleton : Expr :=
  .lam (.tbind 0) (.cons (.var 0 []) (.var 1 [.ty (.tbind 0)]))

/-- `∀ {a b : Nat, α}. α → BL a b α → BL (a+1) (b+1) α`. -/
def consScheme : BScheme where
  binders := [.count, .count, .type]
  body :=
    .arrow (.tbind 0)
      (.arrow (.bl (r 0) (r 1) (.tbind 0))
        (.bl (.add (r 0) (.lit 1)) (.add (r 1) (.lit 1)) (.tbind 0)))

def eCons : Expr :=
  .lam (.tbind 0)
    (.lam (.bl (some (r 0)) (some (r 1)) (.tbind 0))
      (.cons (.var 1 []) (.var 0 [])))

/-- `∀ {a b : Nat, α}. BL (a+1) b α → α`. -/
def headScheme : BScheme where
  binders := [.count, .count, .type]
  body := .arrow (.bl (.add (r 0) (.lit 1)) (r 1) (.tbind 0)) (.tbind 0)

def eHead : Expr :=
  .lam (.bl (some (.add (r 0) (.lit 1))) (some (r 1)) (.tbind 0))
    (.matchCons (.var 0 []) (.var 0 []))

/-- `∀ {a b : Nat, α}. BL (a+1) (b+1) α → BL a b α`. -/
def tailScheme : BScheme where
  binders := [.count, .count, .type]
  body :=
    .arrow (.bl (.add (r 0) (.lit 1)) (.add (r 1) (.lit 1)) (.tbind 0))
      (.bl (r 0) (r 1) (.tbind 0))

def eTail : Expr :=
  .lam (.bl (some (.add (r 0) (.lit 1))) (some (.add (r 1) (.lit 1))) (.tbind 0))
    (.matchCons (.var 0 []) (.var 1 []))

/-- Context for stdlib demos: `nil` scheme at 0, user programs use `var 1+`. -/
private def ctxStd : Ctx := [.scheme nilScheme]

/-- synth context for polymorphic bodies that mention `nil @α` at index 1. -/
private def ctxPoly (extra : Ctx := []) : Ctx := extra ++ [.scheme nilScheme]

-- λ(x : α). x :: nil @α  :  ∀ {α}. α → BL 1 1 α
#eval showSynth eSingleton (ctxPoly [])

-- λ(x : α). λ(y : BL a b α). x :: y  :  …
#eval showSynth eCons

-- λ(x : BL (a + 1) b α). match x with | y :: z => y
#eval showSynth eHead

-- λ(x : BL (a + 1) (b + 1) α). match x with | y :: z => z
#eval showSynth eTail

-- Pack + use: `head @0 @5 (cons @2 @3 () [(), ()])` with typed nil in spine
def eUseConsHead : Expr :=
  .letScheme consScheme eCons
    (.letScheme headScheme eHead
      (.app (.var 0 [.count (.lit 0), .count (.lit 4), .ty .unit])
        (.app (.app (.var 1 [.count (.lit 2), .count (.lit 3), .ty .unit]) .unit)
          (.cons .unit (.cons .unit (.var 2 [.ty .unit]))))))

-- nested let cons/head pipeline  :  Unit
#eval showSynth eUseConsHead (ctxPoly [])

-- Pack tail and strip one cons off a length-3 list
def eUseTail : Expr :=
  .letScheme tailScheme eTail
    (.app (.var 0 [.count (.lit 2), .count (.lit 2), .ty .unit])
      (.cons .unit (.cons .unit (.cons .unit (.var 1 [.ty .unit])))))

-- let x : ∀ a b α. BL (a+1) (b+1) α → BL a b α = … in x @2 @2 @Unit [(), (), ()]
#eval showSynth eUseTail (ctxPoly [])

-- Pack + use head on a concrete list
def eUseHead : Expr :=
  .letScheme headScheme eHead
    (.app (.var 0 [.count (.lit 0), .count (.lit 5), .ty .unit])
      (.cons .unit (.cons .unit (.cons .unit (.var 1 [.ty .unit])))))

#eval showSynth eUseHead (ctxPoly [])

/-- Defaulting “head”: nil and cons both return `Unit`. -/
def eHeadOrUnit : Expr :=
  .lam (.bl (some (.lit 0)) (some (.lit 5)) .unit)
    (.matchBL (.var 0 []) .unit (.var 0 []))

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
  binders := [.count, .count]
  body :=
    .arrow (.arrow .unit .unit)
      (.arrow (.bl (r 0) (r 1) .unit) (.bl (r 0) (r 1) .unit))

/-- Signature-only: filter may shrink to `0..hi`. -/
def filterScheme : BScheme where
  binders := [.count, .count]
  body :=
    .arrow (.arrow .unit .unit)
      (.arrow (.bl (r 0) (r 1) .unit) (.bl (.lit 0) (r 1) .unit))

/-- Signature-only append. -/
def appendScheme : BScheme where
  binders := [.count, .count, .count, .count]
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
