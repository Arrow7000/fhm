import Mathlib.Logic.Relation
import EPL.Core

namespace EPL
namespace Eval

/-- Runtime values for strict left-to-right evaluation. -/
inductive Value : RuntimeExpr → Prop
  | primLit : Value (.primLit literal)
  | primOp : Value (.primOp op)
  | lambda : Value (.lambda ann body)
  | intAddPartial : Value (.app (.primOp .intAdd) (.primLit (.int value)))

inductive Step : RuntimeExpr → RuntimeExpr → Prop
  | beta :
      Value argument →
      Step (.app (.lambda ann body) argument) (body.subst1 argument)
  | appFunction :
      Step function function' →
      Step (.app function argument) (.app function' argument)
  | appArgument :
      Value function →
      Step argument argument' →
      Step (.app function argument) (.app function argument')
  | intAdd :
      Step
        (.app (.app (.primOp .intAdd) (.primLit (.int left)))
          (.primLit (.int right)))
        (.primLit (.int (left + right)))
  | letRhs :
      Step rhs rhs' →
      Step (.letIn ann rhs body) (.letIn ann rhs' body)
  | letValue :
      Value rhs →
      Step (.letIn ann rhs body) (body.subst1 rhs)
  | fixUnfold :
      Step (.fix () body) (body.subst1 (.fix () body))

/-- Finite execution: the reflexive-transitive closure of `Step`. -/
abbrev Steps : RuntimeExpr → RuntimeExpr → Prop :=
  Relation.ReflTransGen Step

end Eval
end EPL
