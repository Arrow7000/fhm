import Mathlib.Logic.Relation
import EPL.Typing

/-!
# Runtime: strict left-to-right evaluation of erased programs

Evaluation does not consult the signature: a constructor applied to values
is a value however many fields it has (an over-applied constructor is ill
typed), and a match dispatches on the constructor's name alone.
-/

namespace EPL

namespace Eval

/-- `True` or `False`, following the `Bool` convention of `PrimOp.ty`. -/
def boolValue (value : Bool) : RuntimeExpr :=
  .ctor ⟨0, if value then 0 else 1⟩

end Eval

/-- A primitive operator on literal operands; `none` on operands of the wrong
kind. -/
def PrimOp.eval : PrimOp → PrimLit → PrimLit → Option RuntimeExpr
  | .intAdd, .int left, .int right => some (.lit (.int (left + right)))
  | .intSub, .int left, .int right => some (.lit (.int (left - right)))
  | .intLt, .int left, .int right => some (Eval.boolValue (decide (left < right)))
  | .charLt, .char left, .char right => some (Eval.boolValue (decide (left < right)))
  | _, _, _ => none

namespace Eval

/-- Fully evaluated expressions. -/
inductive Value : RuntimeExpr → Prop

  /-- A literal. -/
  | lit : Value (.lit literal)

  /-- An operator awaiting both operands. -/
  | primOp : Value (.primOp op)

  /-- A function. -/
  | lambda : Value (.lambda param body)

  /-- A primitive operator awaiting its second operand. -/
  | primOpPartial : Value argument → Value (.app (.primOp op) argument)

  /-- A constructor applied to values: a data value if it has all its fields,
  a function if it has fewer. -/
  | ctor :
      expr.spine = (.ctor ref, fields) →
      (∀ field ∈ fields, Value field) →
      Value expr

/-- One step of strict, left-to-right evaluation. -/
inductive Step : RuntimeExpr → RuntimeExpr → Prop

  /-- Apply a function to a value. -/
  | beta :
      Value argument →
      Step (.app (.lambda param body) argument) (body.subst1 argument)

  /-- Evaluate the function first. -/
  | appFunction :
      Step function function' →
      Step (.app function argument) (.app function' argument)

  /-- Then the argument. -/
  | appArgument :
      Value function →
      Step argument argument' →
      Step (.app function argument) (.app function argument')

  /-- Apply an operator to both operands. -/
  | primOp :
      op.eval left right = some result →
      Step (.app (.app (.primOp op) (.lit left)) (.lit right)) result

  /-- Evaluate the scrutinee. Branches are not evaluated. -/
  | matchScrutinee :
      Step scrutinee scrutinee' →
      Step (.match scrutinee branches) (.match scrutinee' branches)

  /-- A constructor value meets a match: apply the first branch for that
  constructor to the fields. -/
  | matchCtor :
      Value scrutinee →
      scrutinee.spine = (.ctor ref, fields) →
      Expr.findBranch ref branches = some body →
      Step (.match scrutinee branches) (Expr.apps body fields)

  /-- Evaluate a let's right-hand side. -/
  | letRhs :
      Step rhs rhs' →
      Step (.letIn ann rhs body) (.letIn ann rhs' body)

  /-- Substitute a let's value into its body. -/
  | letValue :
      Value rhs →
      Step (.letIn ann rhs body) (body.subst1 rhs)

  /-- Unfold recursion once. -/
  | fixUnfold :
      Step (.fix self body) (body.subst1 (.fix self body))

/-- Any number of steps. -/
abbrev Steps : RuntimeExpr → RuntimeExpr → Prop :=
  Relation.ReflTransGen Step

/-! ## Executable evaluator -/

/-- `Value`, as a check. -/
def isValue : RuntimeExpr → Bool
  | .lit _ | .primOp _ | .lambda _ _ | .ctor _ => true
  | .app (.primOp _) argument => isValue argument
  | .app function argument =>
      isValue function && isValue argument &&
        match function.spine.1 with
        | .ctor _ => true
        | _ => false
  | _ => false

/-- Contract an application of a value to a value, if it is a redex. -/
def reduceApp : RuntimeExpr → RuntimeExpr → Option RuntimeExpr
  | .lambda _ body, argument => some (body.subst1 argument)
  | .app (.primOp op) (.lit left), .lit right => op.eval left right
  | _, _ => none

/-- Contract a match on a value, if it has a branch for the value's
constructor. -/
def reduceMatch (scrutinee : RuntimeExpr) (branches : List (CtorRef × RuntimeExpr)) :
    Option RuntimeExpr :=
  match scrutinee.spine with
  | (.ctor ref, fields) => (Expr.findBranch ref branches).map (Expr.apps · fields)
  | _ => none

/-- One step; `none` exactly when there is no `Step` successor. -/
def step? : RuntimeExpr → Option RuntimeExpr
  | .app function argument =>
      match step? function with
      | some function' => some (.app function' argument)
      | none =>
          if isValue function then
            match step? argument with
            | some argument' => some (.app function argument')
            | none => if isValue argument then reduceApp function argument else none
          else none
  | .match scrutinee branches =>
      match step? scrutinee with
      | some scrutinee' => some (.match scrutinee' branches)
      | none => if isValue scrutinee then reduceMatch scrutinee branches else none
  | .letIn ann rhs body =>
      match step? rhs with
      | some rhs' => some (.letIn ann rhs' body)
      | none => if isValue rhs then some (body.subst1 rhs) else none
  | .fix self body => some (body.subst1 (.fix self body))
  | _ => none

/-- Up to `fuel` steps, stopping early where no step applies. (Fuel because
`fix` admits divergence.) -/
def run : Nat → RuntimeExpr → RuntimeExpr
  | 0, expr => expr
  | fuel + 1, expr =>
      match step? expr with
      | some next => run fuel next
      | none => expr

end Eval
end EPL
