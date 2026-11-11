import EPL.Eval

/-!
# Executable evaluator

A deterministic one-step function `Eval.step?` and a fuel-bounded driver
`Eval.run` for the erased runtime language. `EPL.Properties.Evaluator` proves
that `step?` computes exactly the `Eval.Step` relation and that `run` follows
it; fuel is needed because `fix` admits divergence.
-/

namespace EPL
namespace Eval

/-- Executable check for `Value`. -/
def isValue : RuntimeExpr → Bool
  | .primLit _ => true
  | .primOp _ => true
  | .lambda _ _ => true
  | .app (.primOp .intAdd) (.primLit (.int _)) => true
  | _ => false

/-- Contract an application whose function and argument are both values:
beta reduction or saturated integer addition. `none` if neither applies. -/
def reduceApp : RuntimeExpr → RuntimeExpr → Option RuntimeExpr
  | .lambda _ body, argument => some (body.subst1 argument)
  | .app (.primOp .intAdd) (.primLit (.int left)), .primLit (.int right) =>
      some (.primLit (.int (left + right)))
  | _, _ => none

/-- One step of strict left-to-right evaluation. Returns `none` exactly when
the expression has no `Step` successor (it is a value or stuck). -/
def step? : RuntimeExpr → Option RuntimeExpr
  | .app function argument =>
      match step? function with
      | some function' => some (.app function' argument)
      | none =>
          if isValue function then
            match step? argument with
            | some argument' => some (.app function argument')
            | none =>
                if isValue argument then reduceApp function argument else none
          else none
  | .letIn ann rhs body =>
      match step? rhs with
      | some rhs' => some (.letIn ann rhs' body)
      | none => if isValue rhs then some (body.subst1 rhs) else none
  | .fix ann body => some (body.subst1 (.fix ann body))
  | _ => none

/-- Take up to `fuel` steps, stopping early at an expression with no
successor. -/
def run : Nat → RuntimeExpr → RuntimeExpr
  | 0, expr => expr
  | fuel + 1, expr =>
      match step? expr with
      | some next => run fuel next
      | none => expr

end Eval
end EPL
