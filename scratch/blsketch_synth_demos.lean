import FHM.BLSketch
import FHM.BLSketch.Pretty

/-! # BLSketch — `synth` / `check` demos

Run with `z3` on `PATH`:
```
lake env lean scratch/blsketch_synth_demos.lean
```

Companion to `blsketch_z3_demos.lean` (raw oracle APIs). Exercises structural
synth, `check` via `Sub`, hole solving, match join / refine, nonlinear
scheme / mul, richer `let`/`letScheme`/`letRecScheme` programs, and a small **stdlib** of
BL helpers including recursive `map` / `filter` / `append` / `flatMap`. Style matches `FHM/Examples.lean`. -/

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

-- ([] : BL 0 0 Unit) => typechecks ✓  (bare nil under check via Check.nil)
#eval showCheck .nil (.bl (.lit 0) (.lit 0) .unit)

-- ([] : BL 0 5 Unit) => typechecks ✓  (subtype from BL 0 0)
#eval showCheck .nil (.bl (.lit 0) (.lit 5) .unit)

-- (BL 1 1 Unit : BL 0 5 Unit) => typechecks ✓  (wider bounds; same elem)
#eval showCheck (.cons .unit (.var 0 [.ty .unit])) (.bl (.lit 0) (.lit 5) .unit) ctxNil

/-! ## Annotation holes

`BL _ _` is an *annotation* with holes. `fillHoles` replaces each `_` by a
fresh inferable (`?a`, `?b`, …). Synth of `([] : BL _ _)` returns that holey
demand type as-is (it does not substitute a solved assignment). Separately,
`showAnnoWitness` asks whether some assignment to those holes makes the
ascription succeed via `solve`. Bare `[]` ascribed at a concrete `BL` uses
`TypeOf.annoNil` (forceSubtype from `BL 0 0 elem`) without calling `check`. -/

-- ([] : BL 0 5 Unit)  :  BL 0 5 Unit  (annoNil path)
#eval showSynth (.anno .nil (.bl (some (.lit 0)) (some (.lit 5)) .unit))

/-- `nil @Unit` ascribed at `BL _ _` (holes filled by `synth`). -/
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

/-! ### Recursive stdlib — `map` / `filter` via `letRecScheme` -/

/-- `∀ {a b : Nat, α β}. (α → β) → BL a b α → BL a b β`. -/
def mapScheme : BScheme where
  binders := [.count, .count, .type, .type]
  body :=
    .arrow (.arrow (.tbind 0) (.tbind 1))
      (.arrow (.bl (r 0) (r 1) (.tbind 0))
        (.bl (r 0) (r 1) (.tbind 1)))

/-- Recursive map body (expects `mapScheme` and `nilScheme` in ctx). -/
def eMap : Expr :=
  .lam (.arrow (.tbind 0) (.tbind 1))
    (.lam (.bl (some (r 0)) (some (r 1)) (.tbind 0))
      (.matchBL (.var 0 [])
        (.anno (.var 3 [.ty (.tbind 1)]) (.bl (some (r 0)) (some (r 1)) (.tbind 1)))
        (.anno (.cons (.app (.var 3 []) (.var 0 []))
            (.app (.app (.var 4 [.count (.pred (r 0)), .count (.pred (r 1)), .ty (.tbind 0), .ty (.tbind 1)])
                (.var 3 []))
              (.var 1 [])))
          (.bl (some (r 0)) (some (r 1)) (.tbind 1)))))

def eMapRec : Expr :=
  .letRecScheme mapScheme eMap
    (.var 0 [.count (r 0), .count (r 1), .ty (.tbind 0), .ty (.tbind 1)])

/-- `∀ {a b : Nat, α}. (α → Bool) → BL a b α → BL 0 b α`. -/
def filterScheme : BScheme where
  binders := [.count, .count, .type]
  body :=
    .arrow (.arrow (.tbind 0) .bool)
      (.arrow (.bl (r 0) (r 1) (.tbind 0))
        (.bl (.lit 0) (r 1) (.tbind 0)))

/-- Recursive filter body (expects `filterScheme` and `nilScheme` in ctx). -/
def eFilter : Expr :=
  .lam (.arrow (.tbind 0) .bool)
    (.lam (.bl (some (r 0)) (some (r 1)) (.tbind 0))
      (.matchBL (.var 0 [])
        (.anno (.var 3 [.ty (.tbind 0)]) (.bl (some (.lit 0)) (some (r 1)) (.tbind 0)))
        (.if_ (.app (.var 3 []) (.var 0 []))
          (.anno (.cons (.var 0 [])
              (.app (.app (.var 4 [.count (.pred (r 0)), .count (.pred (r 1)), .ty (.tbind 0)])
                  (.var 3 []))
                (.var 1 [])))
            (.bl (some (.lit 0)) (some (r 1)) (.tbind 0)))
          (.anno
            (.app (.app (.var 4 [.count (.pred (r 0)), .count (.pred (r 1)), .ty (.tbind 0)])
                (.var 3 []))
              (.var 1 []))
            (.bl (some (.lit 0)) (some (r 1)) (.tbind 0))))))

def eFilterRec : Expr :=
  .letRecScheme filterScheme eFilter
    (.var 0 [.count (r 0), .count (r 1), .ty (.tbind 0)])

-- let rec f : mapScheme = … in f @a @b @α @β
--   :  (α → β) → BL a b α → BL a b β
-- (free `a,b,α,β` — same didactic pattern as free rigid counts elsewhere;
--  not a returned scheme; quantify by packing / instantiate at use sites)
#eval showSynth eMapRec (ctxPoly [])

-- let rec f : filterScheme = … in f @a @b @α
--   :  (α → Bool) → BL a b α → BL 0 b α
#eval showSynth eFilterRec (ctxPoly [])

-- map / filter applied to small lists
def eMapDemo : Expr :=
  .letRecScheme mapScheme eMap
    (.app (.app (.var 0 [.count (.lit 0), .count (.lit 2), .ty .unit, .ty .unit])
        (.lam .unit (.var 0 [])))
      (.cons .unit (.cons .unit (.var 1 [.ty .unit]))))

#eval showSynth eMapDemo (ctxPoly [])

/-- `filter (λx. true) [(), ()]` at `BL 0 2 Unit`. -/
def eFilterDemo : Expr :=
  .letRecScheme filterScheme eFilter
    (.app (.app (.var 0 [.count (.lit 0), .count (.lit 2), .ty .unit])
        (.lam .unit .true))
      (.cons .unit (.cons .unit (.var 1 [.ty .unit]))))

#eval showSynth eFilterDemo (ctxPoly [])

/-- `∀ {a b c d : Nat, α}. BL a b α → BL c d α → BL (a+c) (b+d) α`. -/
def appendScheme : BScheme where
  binders := [.count, .count, .count, .count, .type]
  body :=
    .arrow (.bl (r 0) (r 1) (.tbind 0))
      (.arrow (.bl (r 2) (r 3) (.tbind 0))
        (.bl (.add (r 0) (r 2)) (.add (r 1) (r 3)) (.tbind 0)))

/-- Recursive append body (expects `appendScheme` and `nilScheme` in ctx). -/
def eAppend : Expr :=
  .lam (.bl (some (r 0)) (some (r 1)) (.tbind 0))
    (.lam (.bl (some (r 2)) (some (r 3)) (.tbind 0))
      (.matchBL (.var 1 [])
        (.anno (.var 0 []) (.bl (some (.add (r 0) (r 2))) (some (.add (r 1) (r 3))) (.tbind 0)))
        (.anno (.cons (.var 0 [])
            (.app (.app (.var 4 [.count (.pred (r 0)), .count (.pred (r 1)), .count (r 2), .count (r 3), .ty (.tbind 0)])
                (.var 1 []))
              (.var 2 [])))
          (.bl (some (.add (r 0) (r 2))) (some (.add (r 1) (r 3))) (.tbind 0)))))

def eAppendRec : Expr :=
  .letRecScheme appendScheme eAppend
    (.var 0 [.count (r 0), .count (r 1), .count (r 2), .count (r 3), .ty (.tbind 0)])

-- let rec f : appendScheme = … in f @a @b @c @d @α
--   :  BL a b α → BL c d α → BL (a + c) (b + d) α
#eval showSynth eAppendRec (ctxPoly [])

def eAppendDemo : Expr :=
  .letRecScheme appendScheme eAppend
    (.app (.app (.var 0 [.count (.lit 2), .count (.lit 2), .count (.lit 1), .count (.lit 1), .ty .unit])
        (.cons .unit (.cons .unit (.var 1 [.ty .unit]))))
      (.cons .unit (.var 1 [.ty .unit])))

-- append [(), ()] [()]  :  BL 3 3 Unit
#eval showSynth eAppendDemo (ctxPoly [])

/-- `∀ {a b c d : Nat, α β}. (α → BL c d β) → BL a b α → BL (a*c) (b*d) β`. -/
def flatMapScheme : BScheme where
  binders := [.count, .count, .count, .count, .type, .type]
  body :=
    .arrow (.arrow (.tbind 0) (.bl (r 2) (r 3) (.tbind 1)))
      (.arrow (.bl (r 0) (r 1) (.tbind 0))
        (.bl (.mul (r 0) (r 2)) (.mul (r 1) (r 3)) (.tbind 1)))

/-- Recursive flatMap body (expects `flatMapScheme`, `appendScheme`, and `nilScheme` in ctx). -/
def eFlatMap : Expr :=
  .lam (.arrow (.tbind 0) (.bl (some (r 2)) (some (r 3)) (.tbind 1)))
    (.lam (.bl (some (r 0)) (some (r 1)) (.tbind 0))
      (.matchBL (.var 0 [])
        (.anno (.var 4 [.ty (.tbind 1)]) (.bl (some (.mul (r 0) (r 2))) (some (.mul (r 1) (r 3))) (.tbind 1)))
        (.anno
          (.app (.app (.var 5 [.count (r 2), .count (r 3), .count (.mul (.pred (r 0)) (r 2)), .count (.mul (.pred (r 1)) (r 3)), .ty (.tbind 1)])
              (.app (.var 3 []) (.var 0 [])))
            (.app (.app (.var 4 [.count (.pred (r 0)), .count (.pred (r 1)), .count (r 2), .count (r 3), .ty (.tbind 0), .ty (.tbind 1)])
                (.var 3 []))
              (.var 1 [])))
          (.bl (some (.mul (r 0) (r 2))) (some (.mul (r 1) (r 3))) (.tbind 1)))))

def eFlatMapRec : Expr :=
  .letRecScheme appendScheme eAppend
    (.letRecScheme flatMapScheme eFlatMap
      (.var 0 [.count (r 0), .count (r 1), .count (r 2), .count (r 3), .ty (.tbind 0), .ty (.tbind 1)]))

-- let rec append … in let rec flatMap … in flatMap @a @b @c @d @α @β
--   :  (α → BL c d β) → BL a b α → BL (a * c) (b * d) β
#eval showSynth eFlatMapRec (ctxPoly [])

/-- `flatMap (λx. [x]) [(), ()]` at `BL 2 2 Unit` (each element maps to a singleton). -/
def eFlatMapDemo : Expr :=
  .letRecScheme appendScheme eAppend
    (.letRecScheme flatMapScheme eFlatMap
      (.app (.app (.var 0 [.count (.lit 2), .count (.lit 2), .count (.lit 1), .count (.lit 1), .ty .unit, .ty .unit])
          (.lam .unit (.cons (.var 0 []) (.var 3 [.ty .unit]))))
        (.cons .unit (.cons .unit (.var 2 [.ty .unit])))))

-- flatMap (λx. [x]) [(), ()]  :  BL 2 2 Unit
#eval showSynth eFlatMapDemo (ctxPoly [])

end Stdlib

end BLSketch.Demo
