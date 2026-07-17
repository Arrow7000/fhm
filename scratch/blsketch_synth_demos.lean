import FHM.BLSketch

/-!
# BLSketch — live `synth` / `check` demos (Z3)

Run with `z3` on `PATH`:
```
lake env lean scratch/blsketch_synth_demos.lean
```

Companion to `blsketch_z3_demos.lean` (raw oracle APIs). This file exercises the
type-system surface: structural synth, `check` via `Sub`, hole solving, match
join / refine, and nonlinear scheme / mul.
-/

open BLSketch

def r (i : Nat) : Count := cvar .rigid i

def showOptTy : Option (Nat × Ty) → String
  | none => "fail"
  | some (_, ty) => toString (repr ty)

def showCheck : Option Nat → String
  | none => "fail"
  | some Φ => s!"ok (Φ={Φ})"

/-- Print one `solve` witness for `ty' ≤ ann` after `fillHoles` (does not imply uniqueness). -/
def showAnnoWitness (ctx : Ctx) (e : Expr) (ann : AnnoTy) : String :=
  let (_, ty) := fillHoles 0 ann
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
        let pairs := ty.inferVars.map fun v =>
          s!"i_{v.idx}={σ ⟨.inferable, v.idx⟩}"
        "witness: " ++ String.intercalate ", " pairs

/-! ## 1. Structural synth (no oracle) -/

#eval! IO.println "=== synth (structural) ==="
#eval! IO.println s!"nil:        {showOptTy (synth 0 [] [] .nil)}"
#eval! IO.println s!"cons unit:  {showOptTy (synth 0 [] [] (.cons .unit .nil))}"

/-! ## 2. `check` — wider demand via `Sub` / Z3 -/

#eval! IO.println "=== check (subtype) ==="
#eval! IO.println s!"nil ⊨ BL 0 0:  {showCheck (check 0 [] [] .nil (.bl (.lit 0) (.lit 0)))}"
#eval! IO.println s!"nil ⊨ BL 0 5:  {showCheck (check 0 [] [] .nil (.bl (.lit 0) (.lit 5)))}"
#eval! IO.println s!"nil ⊨ BL 1 1:  {showCheck (check 0 [] [] .nil (.bl (.lit 1) (.lit 1)))}"

/-! ## 3. Annotation holes

Ascribing `nil` at `BL _ _`: source bounds are concrete `[0,0]` (unique),
demand holes get *some* witness (e.g. `i0=0,i1=0`). The returned synth type may
still mention inferables — algo does not substitute `σ` (see brief soft spot B).
-/

def eAnnoNilHoles : Expr := .anno .nil (.bl none none)

#eval! IO.println "=== anno holes ==="
#eval! IO.println s!"fillHoles BL _ _: {toString (repr (fillHoles 0 (.bl none none)))}"
#eval! IO.println s!"synth anno:       {showOptTy (synth 0 [] [] eAnnoNilHoles)}"
#eval! IO.println s!"one witness:      {showAnnoWitness [] .nil (.bl none none)}"

/-! ## 4. `matchBL` — join bounds -/

def ctxBL05 : Ctx := [.mono (.bl (.lit 0) (.lit 5))]
def eMatchJoin : Expr := .matchBL (.var 0 []) .nil (.cons .unit .nil)

#eval! IO.println "=== matchBL join ==="
#eval! IO.println s!"nil|cons → join: {showOptTy (synth 0 [] ctxBL05 eMatchJoin)}"
#eval! IO.println s!"unit|unit:       {showOptTy (synth 0 [] ctxBL05 (.matchBL (.var 0 []) .unit .unit))}"

/-! ## 5. `matchNil` / `matchCons` — ∀ guards -/

def ctxEmpty : Ctx := [.mono (.bl (.lit 0) (.lit 0))]
def ctxNonempty : Ctx := [.mono (.bl (.lit 3) (.lit 5))]

#eval! IO.println "=== matchNil / matchCons ==="
#eval! IO.println s!"matchNil  @ BL 0 0: {showOptTy (synth 0 [] ctxEmpty (.matchNil (.var 0 []) .unit))}"
#eval! IO.println s!"matchCons @ BL 0 0: {showOptTy (synth 0 [] ctxEmpty (.matchCons (.var 0 []) .unit))}"
#eval! IO.println s!"matchCons @ BL 3 5: {showOptTy (synth 0 [] ctxNonempty (.matchCons (.var 0 []) .unit))}"

/-! ## 6. App — concrete check (no leftover holes) -/

def eId5 : Expr := .lam (.bl (some (.lit 5)) (some (.lit 5))) .unit
def ctxFive : Ctx := [.mono (.bl (.lit 5) (.lit 5))]

#eval! IO.println "=== app / check ==="
#eval! IO.println s!"synth id5:           {showOptTy (synth 0 [] [] eId5)}"
#eval! IO.println s!"app id5 v0:          {showOptTy (synth 0 [] ctxFive (.app eId5 (.var 0 [])))}"
#eval! IO.println s!"check v0 ⊨ BL 5 5:   {showCheck (check 0 [] ctxFive (.var 0 []) (.bl (.lit 5) (.lit 5)))}"
#eval! IO.println s!"check v0 ⊨ BL 0 10:  {showCheck (check 0 [] ctxFive (.var 0 []) (.bl (.lit 0) (.lit 10)))}"

/-! ## 7. Nonlinear — flatMap scheme inst + mul subtype -/

def flatMapScheme : BScheme where
  binders := 2
  body :=
    .arrow (.bl (r 0) (r 0))
      (.arrow (.arrow .unit (.bl (r 1) (r 1)))
        (.bl (.mul (r 0) (r 1)) (.mul (r 0) (r 1))))

def ctxFlat : Ctx := [.scheme flatMapScheme]

#eval! IO.println "=== flatMap / mul ==="
#eval! IO.println s!"flatMap @ 2,6: {showOptTy (synth 0 [] ctxFlat (.var 0 [.lit 2, .lit 6]))}"
#eval! IO.println s!"forceSubtype BL(2*6) ≤ BL 12 12: {
  forceSubtype []
    (.bl (.mul (.lit 2) (.lit 6)) (.mul (.lit 2) (.lit 6)))
    (.bl (.lit 12) (.lit 12))}"
