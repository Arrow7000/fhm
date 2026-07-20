import FHM.BLSketch
import FHM.BLSketch.Pretty

/-! # BLSketch × Z3 demos

Run with `z3` on `PATH`:
```
lake env lean scratch/blsketch_z3_demos.lean
```

Shows: validity, invalidity, witness synthesis, uniqueness / multiplicity.
Style matches `FHM/Examples.lean`. -/

namespace BLSketch.OracleDemo

/-- Rigid count var (`a`, `b`, …). -/
private def r (i : Nat) : Count := cvar .rigid i

/-- Inferable count var (`?a`, `?b`, …). -/
private def x (i : Nat) : Count := cvar .inferable i

/-- Sugar for a `≤` constraint. -/
private def le (a b : Count) : Constraint := ⟨a, b⟩

private def validStr : ValidVerdict → String
  | .valid => "valid"
  | .invalid => "invalid"
  | .unknown => "unknown"

/-- Print `φ  ⇒  valid|invalid|unknown` for `checkValid`. -/
private def showValid (φ : ForallProblem) : IO Unit :=
  IO.println s!"{φ.pretty}  ⇒  {validStr (checkValid φ)}"

/-- Format one `solve` result. **One** witness model if sat — not all models.
Use `unique` / `showUnique` to ask whether chosen outputs are forced. -/
private def solveStr (ψ : ExistsProblem) : String :=
  match solve ψ with
  | .unsat => "unsat"
  | .unknown => "unknown"
  | .witness σ => "witness " ++ Assign.prettyOn σ ψ.inferables

/-- Print `ψ  ⇒  unsat|unknown|witness …` for `solve`. -/
private def showSolve (ψ : ExistsProblem) : IO Unit :=
  IO.println s!"{ψ.pretty}  ⇒  {solveStr ψ}"

private def uniqueStr : UniqueVerdict → String
  | .unique => "unique"
  | .multiple => "multiple"
  | .unknown => "unknown"

/-- Print uniqueness of `outs` under solutions of `ψ`. -/
private def showUnique (ψ : ExistsProblem) (outs : List Count) : IO Unit :=
  let outsStr := "[" ++ String.intercalate ", " (outs.map toString) ++ "]"
  IO.println s!"{ψ.pretty}  outs {outsStr}  ⇒  {uniqueStr (unique ψ outs)}"

/-! ## checkValid — ∀ -/

/-- `a + 0 ≤ a` — should be `.valid`. -/
private def qAddZero : ForallProblem where
  prem := []
  goals := [le (.add (r 0) (.lit 0)) (r 0)]

/-- `a + 1 ≤ a` — should be `.invalid`. -/
private def qAddOneFalse : ForallProblem where
  prem := []
  goals := [le (.add (r 0) (.lit 1)) (r 0)]

/-- Under premise `a ≤ 5`, goal `a ≤ 10` — `.valid`. -/
private def qPremises : ForallProblem where
  prem := [le (r 0) (.lit 5)]
  goals := [le (r 0) (.lit 10)]

-- ∀σ. a + 0 ≤ a  ⇒  valid
#eval showValid qAddZero

-- ∀σ. a + 1 ≤ a  ⇒  invalid
#eval showValid qAddOneFalse

-- ∀σ. (a ≤ 5) ⇒ (a ≤ 10)  ⇒  valid
#eval showValid qPremises

/-! ## solve — ∃∀ witnesses (one model) -/

/-- Find `?a` with `5 ≤ ?a` and `?a ≤ 5` ⇒ witness `?a = 5`. -/
private def qPinFive : ExistsProblem where
  inferables := [⟨.inferable, 0⟩]
  cons := [le (.lit 5) (x 0), le (x 0) (.lit 5)]

/-- `?a + ?b = 7` as two inequalities — some partition of 7. -/
private def qSumSeven : ExistsProblem where
  inferables := [⟨.inferable, 0⟩, ⟨.inferable, 1⟩]
  cons := [
    le (.add (x 0) (x 1)) (.lit 7),
    le (.lit 7) (.add (x 0) (x 1))
  ]

/-- Nonlinear: `?a * ?b = 12`. -/
private def qProductTwelve : ExistsProblem where
  inferables := [⟨.inferable, 0⟩, ⟨.inferable, 1⟩]
  cons := [
    le (.mul (x 0) (x 1)) (.lit 12),
    le (.lit 12) (.mul (x 0) (x 1))
  ]

/-- Unsat: `?a ≤ 3` and `5 ≤ ?a`. -/
private def qUnsat : ExistsProblem where
  inferables := [⟨.inferable, 0⟩]
  cons := [le (x 0) (.lit 3), le (.lit 5) (x 0)]

-- ∃ ?a. 5 ≤ ?a ∧ ?a ≤ 5  ⇒  witness {?a↦5}
#eval showSolve qPinFive

-- ∃ ?a, ?b. ?a + ?b = 7  ⇒  some witness partition
#eval showSolve qSumSeven

-- ∃ ?a, ?b. ?a * ?b = 12  ⇒  some factorization
#eval showSolve qProductTwelve

-- ∃ ?a. ?a ≤ 3 ∧ 5 ≤ ?a  ⇒  unsat
#eval showSolve qUnsat

/-! ## unique — outputs under the solution set -/

/-- Product 12: many factorizations ⇒ `multiple` on `[?a, ?b]`. -/
private def qProdOuts : List Count := [x 0, x 1]

/-- Same product, uniqueness of the *product* alone ⇒ `unique`. -/
private def qProdValueOnly : List Count := [.mul (x 0) (x 1)]

/-- Pin to 5: only one value ⇒ `unique` on `[?a]`. -/
private def qPinOuts : List Count := [x 0]

-- productTwelve outs [?a, ?b]  ⇒  multiple
#eval showUnique qProductTwelve qProdOuts

-- productTwelve outs [?a * ?b]  ⇒  unique
#eval showUnique qProductTwelve qProdValueOnly

-- pinFive outs [?a]  ⇒  unique
#eval showUnique qPinFive qPinOuts

end BLSketch.OracleDemo
