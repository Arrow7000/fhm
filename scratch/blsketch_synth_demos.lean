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

/-- Pretty names for typing-context binders (de Bruijn → `x`, `y`, …). -/
private def ctxNames (ctx : Ctx) : List String :=
  (List.range ctx.length).map prettyTermVarName |>.reverse

/-- Result string for `synth` (pretty type, or `ill-typed`). -/
private def synthStr (ctx : Ctx) (e : Expr) : String :=
  match synth 0 [] ctx e with
  | none => "ill-typed"
  | some (_, ty) => toString ty

/-- Print `e  :  τ` using Pretty precedence (no forced outer parens). -/
private def showSynth (e : Expr) (ctx : Ctx := []) : IO Unit :=
  IO.println s!"{e.pretty (ctxNames ctx)}  :  {synthStr ctx e}"

/-- Print `e  ⊨  τ  ✓/✗` for algorithmic `check`. -/
private def showCheck (e : Expr) (ty : Ty) (ctx : Ctx := []) : IO Unit :=
  let ok := (check 0 [] ctx e ty).isSome
  IO.println s!"{e.pretty (ctxNames ctx)}  ⊨  {ty}  {if ok then "✓" else "✗"}"

/-- Print `ty'  ≤  ty  ✓/✗` for `forceSubtype`. -/
private def showForceSubtype (ty' ty : Ty) : IO Unit :=
  let ok := forceSubtype [] ty' ty
  IO.println s!"{ty'}  ≤  {ty}  {if ok then "✓" else "✗"}"

/-- Print one `solve` witness for `e` ascribed at `ann` after `fillHoles`
(existence only — not a uniqueness check). -/
private def showAnnoWitness (e : Expr) (ann : AnnoTy) (ctx : Ctx := []) : IO Unit :=
  let (_, ty) := fillHoles 0 ann
  let msg :=
    match synth 0 [] ctx e with
    | none => "synth failed"
    | some (_, ty') =>
      match subtypeProblem [] ty' ty with
      | none => "no subtypeProblem"
      | some ψ =>
        match solve ψ with
        | .unsat => "unsat"
        | .unknown => "unknown"
        | .witness σ =>
          "witness " ++ Assign.prettyOn σ ty.inferVars
  IO.println s!"{e.pretty (ctxNames ctx)}  :  {ann}  ⇒  {msg}"

/-- Print `ann  ↦  ty` for `fillHoles 0`. -/
private def showFillHoles (ann : AnnoTy) : IO Unit :=
  let (_, ty) := fillHoles 0 ann
  IO.println s!"{ann}  ↦  {ty}"

/-! ## Structural synth (no oracle) -/

-- []  :  BL 0 0
#eval showSynth .nil

-- [()]  :  BL (0 + 1) (0 + 1)
#eval showSynth (.cons .unit .nil)

/-! ## `check` — wider demand via `Sub` / Z3 -/

-- []  ⊨  BL 0 0  ✓
#eval showCheck .nil (.bl (.lit 0) (.lit 0))

-- []  ⊨  BL 0 5  ✓
#eval showCheck .nil (.bl (.lit 0) (.lit 5))

-- []  ⊨  BL 1 1  ✗
#eval showCheck .nil (.bl (.lit 1) (.lit 1))

/-! ## Annotation holes

Ascribing `nil` at `BL _ _`: source bounds are concrete (unique as outs);
demand holes get *some* witness. Returned synth type may still mention
inferables — algo does not substitute `σ`. -/

/-- `nil` ascribed at `BL _ _` (holes filled by `synth`). -/
private def eAnnoNilHoles : Expr := .anno .nil (.bl none none)

-- BL _ _  ↦  BL ?a ?b
#eval showFillHoles (.bl none none)

-- ([] : BL _ _)  :  BL ?a ?b
#eval showSynth eAnnoNilHoles

-- []  :  BL _ _  ⇒  witness {?a↦0, ?b↦0}
#eval showAnnoWitness .nil (.bl none none)

/-! ## `matchBL` — join bounds -/

/-- Context with a single mono binding `BL 0 5`. -/
private def ctxBL05 : Ctx := [.mono (.bl (.lit 0) (.lit 5))]

/-- Match on that binding: nil → `[]`, cons → `[()]`; join bounds. -/
private def eMatchJoin : Expr := .matchBL (.var 0 []) .nil (.cons .unit .nil)

-- match x with | [] => [] | y :: z => [()]  :  BL (min(0, 0 + 1)) (max(0, 0 + 1))
#eval showSynth eMatchJoin ctxBL05

-- match x with | [] => () | y :: z => ()  :  Unit
#eval showSynth (.matchBL (.var 0 []) .unit .unit) ctxBL05

/-! ## `matchNil` / `matchCons` — ∀ guards -/

/-- Context: empty list type `BL 0 0`. -/
private def ctxEmpty : Ctx := [.mono (.bl (.lit 0) (.lit 0))]

/-- Context: non-empty list type `BL 3 5`. -/
private def ctxNonempty : Ctx := [.mono (.bl (.lit 3) (.lit 5))]

-- matchNil x => ()  :  Unit   (at BL 0 0)
#eval showSynth (.matchNil (.var 0 []) .unit) ctxEmpty

-- matchCons x | h :: t => ()  :  ill-typed   (at BL 0 0)
#eval showSynth (.matchCons (.var 0 []) .unit) ctxEmpty

-- matchCons x | h :: t => ()  :  Unit   (at BL 3 5)
#eval showSynth (.matchCons (.var 0 []) .unit) ctxNonempty

/-! ## App — concrete check (no leftover holes) -/

/-- `λ(_ : BL 5 5). ()`. -/
private def eId5 : Expr := .lam (.bl (some (.lit 5)) (some (.lit 5))) .unit

/-- Context: mono `BL 5 5`. -/
private def ctxFive : Ctx := [.mono (.bl (.lit 5) (.lit 5))]

-- λ(x : BL 5 5). ()  :  BL 5 5 → Unit
#eval showSynth eId5

-- (λ(x : BL 5 5). ()) x  :  Unit
#eval showSynth (.app eId5 (.var 0 [])) ctxFive

-- x  ⊨  BL 5 5  ✓
#eval showCheck (.var 0 []) (.bl (.lit 5) (.lit 5)) ctxFive

-- x  ⊨  BL 0 10  ✓
#eval showCheck (.var 0 []) (.bl (.lit 0) (.lit 10)) ctxFive

/-! ## Nonlinear — flatMap scheme inst + mul subtype -/

/-- `∀ a b. BL a a → (Unit → BL b b) → BL (a*b) (a*b)`. -/
private def flatMapScheme : BScheme where
  binders := 2
  body :=
    .arrow (.bl (r 0) (r 0))
      (.arrow (.arrow .unit (.bl (r 1) (r 1)))
        (.bl (.mul (r 0) (r 1)) (.mul (r 0) (r 1))))

/-- Context whose nearest binder is `flatMapScheme`. -/
private def ctxFlat : Ctx := [.scheme flatMapScheme]

-- x⟨2, 6⟩  :  BL 2 2 → (Unit → BL 6 6) → BL (2 * 6) (2 * 6)
-- (`x` = scheme in ctx; `⟨2, 6⟩` = bound instantiation, not a slice)
#eval showSynth (.var 0 [.lit 2, .lit 6]) ctxFlat

-- BL (2 * 6) (2 * 6)  ≤  BL 12 12  ✓
#eval showForceSubtype
  (.bl (.mul (.lit 2) (.lit 6)) (.mul (.lit 2) (.lit 6)))
  (.bl (.lit 12) (.lit 12))

end BLSketch.Demo
