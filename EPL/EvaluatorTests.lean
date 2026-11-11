import EPL.Examples
import EPL.InferenceTests
import EPL.Properties.InferenceEvaluation

namespace EPL.EvaluatorTests

open EPL EPL.Examples EPL.InferenceTests

/-- `(fun x => x + 1) 41` -/
def incrementApplied : Source :=
  .app inferredIntLambda (.primLit (.int 41))

/-- `let x = 40 in x + 2` -/
def letAdd : Source :=
  .letIn none (.primLit (.int 40))
    (.app (.app (.primOp .intAdd) (.var 0)) (.primLit (.int 2)))

/-- Final value of `evaluate`, or `none` if inference rejected the program or
fuel ran out. -/
def finalValue (input : Source) (fuel : Nat) : Option RuntimeExpr :=
  (evaluate input fuel).bind (·.2.value?)

#guard finalValue incrementApplied 10 = some (.primLit (.int 42))
#guard finalValue letAdd 10 = some (.primLit (.int 42))
#guard finalValue explicitPolyProgram 50 = some (.primLit (.bool true))

-- Divergent programs are well-typed but never finish.
#guard finalValue (.app integerLoop (.primLit (.int 0))) 100 = none
#guard finalValue inferredIntegerFix 100 = none

-- Rejected programs never run.
#guard (evaluate deadAmbiguousLambda 10).isNone

end EPL.EvaluatorTests
