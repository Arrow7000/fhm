import FHM.BLSketch
import FHM.BLSketch.Pretty

/-! # BLSketch — `synth` / `check` demos

Run with `z3` on `PATH`:
```
lake env lean scratch/blsketch_synth_demos.lean
```

Companion to `blsketch_z3_demos.lean` (raw oracle APIs). Exercises structural
synth, `check` via `Sub`, hole solving, match join / refine, and nonlinear
scheme / mul. Style matches `FHM/Examples.lean`. -/

namespace BLSketch.Demo

/-- Rigid count variable `a`/`b`/… (index `i`). -/
private def r (i : Nat) : Count := cvar .rigid i

/-- Print a judgement under `ctx`, with env lines when `ctx` is non-empty. -/
private def showUnder (ctx : Ctx) (line : String) : IO Unit := do
  if !ctx.isEmpty then
    IO.println (Ctx.prettyEnv ctx)
    IO.println "---------"
  IO.println line

/-- Result string for `synth` (pretty type, optionally folded when ground). -/
private def synthStr (ctx : Ctx) (e : Expr) : String :=
  match synth 0 [] ctx e with
  | none => "ill-typed"
  | some (_, ty) => Ty.prettyFolded ty

/-- Print `e  :  τ` (judgement parens for anno/match/if/let). -/
private def showSynth (e : Expr) (ctx : Ctx := []) : IO Unit :=
  let eStr := Expr.prettyJudgement e (Ctx.termNames ctx)
  showUnder ctx s!"{eStr}  :  {synthStr ctx e}"

/-- Print `(e : τ) => typechecks ✓` / `doesn't typecheck ✗` for `check`. -/
private def showCheck (e : Expr) (ty : Ty) (ctx : Ctx := []) : IO Unit :=
  let ok := (check 0 [] ctx e ty).isSome
  let verdict := if ok then "typechecks ✓" else "doesn't typecheck ✗"
  let eStr := Expr.prettyJudgement e (Ctx.termNames ctx)
  showUnder ctx s!"({eStr} : {ty}) => {verdict}"

/-- Print a bound scheme on its own. -/
private def showScheme (s : BScheme) : IO Unit :=
  IO.println (toString s)

/-- Print `ty'  ≤  ty  ✓/✗` for `forceSubtype`. -/
private def showForceSubtype (ty' ty : Ty) : IO Unit :=
  let ok := forceSubtype [] ty' ty
  IO.println s!"{ty'}  ≤  {ty}  {if ok then "✓" else "✗"}"

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
#eval showCheck .nil (.bl (.lit 0) (.lit 0))

-- ([] : BL 0 5) => typechecks ✓
#eval showCheck .nil (.bl (.lit 0) (.lit 5))

-- ([] : BL 1 1) => doesn't typecheck ✗
#eval showCheck .nil (.bl (.lit 1) (.lit 1))

/-! ## Annotation holes

`BL _ _` is an *annotation* with holes. `fillHoles` replaces each `_` by a
fresh inferable (`?a`, `?b`, …). Synth of `([] : BL _ _)` returns that holey
demand type as-is (it does not substitute a solved assignment). Separately,
`showAnnoWitness` asks whether some assignment to those holes makes the
ascription succeed via `solve`. -/

/-- `nil` ascribed at `BL _ _` (holes filled by `synth`). -/
private def eAnnoNilHoles : Expr := .anno .nil (.bl none none)

-- fillHoles: BL _ _  ↦  BL ?a ?b  (each `_` → a fresh ?var)
#eval showFillHoles (.bl none none)

-- ([] : BL _ _)  :  BL ?a ?b
#eval showSynth eAnnoNilHoles

-- can [] inhabit BL _ _?  ⇒  demand holes can be solved as {?a↦0, ?b↦0}
#eval showAnnoWitness .nil (.bl none none)

/-! ## `matchBL` — join bounds -/

/-- Context with a single mono binding `BL 0 5`. -/
private def ctxBL05 : Ctx := [.mono (.bl (.lit 0) (.lit 5))]

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
private def ctxEmpty : Ctx := [.mono (.bl (.lit 0) (.lit 0))]

/-- Context: non-empty list type `BL 3 5`. -/
private def ctxNonempty : Ctx := [.mono (.bl (.lit 3) (.lit 5))]

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
private def eId5 : Expr := .lam (.bl (some (.lit 5)) (some (.lit 5))) .unit

/-- Context: mono `BL 5 5`. -/
private def ctxFive : Ctx := [.mono (.bl (.lit 5) (.lit 5))]

-- λ(x : BL 5 5). ()  :  BL 5 5 → Unit
#eval showSynth eId5

-- x : BL 5 5
-- ---------
-- (λ(y : BL 5 5). ()) x  :  Unit
#eval showSynth (.app eId5 (.var 0 [])) ctxFive

-- x : BL 5 5
-- ---------
-- (x : BL 5 5) => typechecks ✓
#eval showCheck (.var 0 []) (.bl (.lit 5) (.lit 5)) ctxFive

-- x : BL 5 5
-- ---------
-- (x : BL 0 10) => typechecks ✓
#eval showCheck (.var 0 []) (.bl (.lit 0) (.lit 10)) ctxFive

-- x : BL 5 5
-- ---------
-- (x : BL 20 20) => doesn't typecheck ✗
#eval showCheck (.var 0 []) (.bl (.lit 20) (.lit 20)) ctxFive

/-! ## Nonlinear — flatMap scheme inst + mul subtype -/

/-- `∀ a b c d. BL a b → (Unit → BL c d) → BL (a*c) (b*d)`. -/
private def flatMapScheme : BScheme where
  binders := 4
  body :=
    .arrow (.bl (r 0) (r 1))
      (.arrow (.arrow .unit (.bl (r 2) (r 3)))
        (.bl (.mul (r 0) (r 2)) (.mul (r 1) (r 3))))

/-- Context whose nearest binder is `flatMapScheme`. -/
private def ctxFlat : Ctx := [.scheme flatMapScheme]

-- ∀ a b c d. BL a b → (Unit → BL c d) → BL (a * c) (b * d)
#eval showScheme flatMapScheme

-- x : ∀ a b c d. BL a b → (Unit → BL c d) → BL (a * c) (b * d)
-- ---------
-- x @2 @5 @3 @4  :  BL 2 5 → (Unit → BL 3 4) → BL (2 * 3) (5 * 4)  ↦  …
#eval showSynth (.var 0 [.lit 2, .lit 5, .lit 3, .lit 4]) ctxFlat

-- BL (2 * 3) (5 * 4)  ≤  BL 6 20  ✓
#eval showForceSubtype
  (.bl (.mul (.lit 2) (.lit 3)) (.mul (.lit 5) (.lit 4)))
  (.bl (.lit 6) (.lit 20))

end BLSketch.Demo
