import FHM.BLSketch

/-!
# BLSketch × Z3 demos

Run with `z3` on `PATH`:
```
lake env lean scratch/blsketch_z3_demos.lean
```

Shows: validity, invalidity, witness synthesis, uniqueness / multiplicity.
-/

open BLSketch

def r (i : Nat) : Count := cvar .rigid i
def x (i : Nat) : Count := cvar .inferable i

def le (a b : Count) : Constraint := ⟨a, b⟩

/-- Pretty-print a solve verdict for a fixed list of inferable slots. -/
def showSolve (ψ : ExistsProblem) (slots : List Nat) : String :=
  match solve ψ with
  | .unsat => "unsat"
  | .unknown => "unknown"
  | .witness σ =>
      let pairs := slots.map fun i => s!"i_{i}={σ ⟨.inferable, i⟩}"
      "witness: " ++ String.intercalate ", " pairs

def showUnique (ψ : ExistsProblem) (outs : List Count) : String :=
  match unique ψ outs with
  | .unique => "unique"
  | .multiple => "multiple"
  | .unknown => "unknown"

/-! ## 1. checkValid — ∀ -/

/-- `r0 + 0 ≤ r0` — should be `.valid`. -/
def qAddZero : ForallProblem where
  prem := []
  goals := [le (.add (r 0) (.lit 0)) (r 0)]

/-- `r0 + 1 ≤ r0` — should be `.invalid`. -/
def qAddOneFalse : ForallProblem where
  prem := []
  goals := [le (.add (r 0) (.lit 1)) (r 0)]

/-- Under premise `r0 ≤ 5`, goal `r0 ≤ 10` — `.valid`. -/
def qPremises : ForallProblem where
  prem := [le (r 0) (.lit 5)]
  goals := [le (r 0) (.lit 10)]

/-! ## 2. solve — ∃∀ witnesses -/

/-- Find `i0` with `5 ≤ i0` and `i0 ≤ 5` ⇒ witness `i0 = 5`. -/
def qPinFive : ExistsProblem where
  inferables := [⟨.inferable, 0⟩]
  cons := [le (.lit 5) (x 0), le (x 0) (.lit 5)]

/-- `i0 + i1 = 7` as two inequalities — some partition of 7. -/
def qSumSeven : ExistsProblem where
  inferables := [⟨.inferable, 0⟩, ⟨.inferable, 1⟩]
  cons := [
    le (.add (x 0) (x 1)) (.lit 7),
    le (.lit 7) (.add (x 0) (x 1))
  ]

/-- Nonlinear: `i0 * i1 = 12`. -/
def qProductTwelve : ExistsProblem where
  inferables := [⟨.inferable, 0⟩, ⟨.inferable, 1⟩]
  cons := [
    le (.mul (x 0) (x 1)) (.lit 12),
    le (.lit 12) (.mul (x 0) (x 1))
  ]

/-- Unsat: `i0 ≤ 3` and `5 ≤ i0`. -/
def qUnsat : ExistsProblem where
  inferables := [⟨.inferable, 0⟩]
  cons := [le (x 0) (.lit 3), le (.lit 5) (x 0)]

/-! ## 3. unique — outputs -/

/-- Product 12: many factorizations ⇒ `multiple` on `[i0, i1]`. -/
def qProdOuts : List Count := [x 0, x 1]

/-- Same product, but uniqueness of the *product* alone (always 12) ⇒ `unique`. -/
def qProdValueOnly : List Count := [.mul (x 0) (x 1)]

/-- Pin to 5: only one value ⇒ `unique` on `[i0]`. -/
def qPinOuts : List Count := [x 0]

/-! ## Run -/

#eval IO.println "=== checkValid ==="
#eval IO.println s!"addZero:     {repr (checkValid qAddZero)}"
#eval IO.println s!"addOneFalse: {repr (checkValid qAddOneFalse)}"
#eval IO.println s!"premises:    {repr (checkValid qPremises)}"

#eval IO.println "=== solve (witnesses) ==="
#eval IO.println s!"pinFive:        {showSolve qPinFive [0]}"
#eval IO.println s!"sumSeven:       {showSolve qSumSeven [0, 1]}"
#eval IO.println s!"productTwelve:  {showSolve qProductTwelve [0, 1]}"
#eval IO.println s!"unsat:          {showSolve qUnsat [0]}"

#eval IO.println "=== unique ==="
#eval IO.println s!"prod factors:   {showUnique qProductTwelve qProdOuts}"
#eval IO.println s!"prod value:     {showUnique qProductTwelve qProdValueOnly}"
#eval IO.println s!"pinFive outs:   {showUnique qPinFive qPinOuts}"
