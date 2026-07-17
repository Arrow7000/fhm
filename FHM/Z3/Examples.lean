import FHM.Z3.Oracle

/-!
# FHM — Z3 smoke examples

Run with `z3` on PATH:
```
#eval FHM.Z3.Examples.smokeIO
```
Encode-only (no z3):
```
#eval FHM.Z3.Examples.encodeSmoke
```
-/

namespace FHM.Z3.Examples

private def x : Expr := .name "x"
private def y : Expr := .name "y"
private def n0 : Expr := .lit 0
private def n1 : Expr := .lit 1

def easyAddZero : Query :=
  Query.alwaysEq (.add x n0) x

def easyLe : Query :=
  Query.alwaysLe x (.add x n1)

def encodeSmoke : String :=
  Encode.Query.toCheckScript easyAddZero Config.default

def smokeIO : IO String := do
  let v ← Process.decideIO easyAddZero
  return v.describe

def smokeLeIO : IO String := do
  let v ← Process.decideIO easyLe
  return v.describe

end FHM.Z3.Examples
