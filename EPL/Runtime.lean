import Mathlib.Logic.Relation
import EPL.Typing

/-!
# Runtime: strict left-to-right evaluation of erased programs

Evaluation consults the signature for constants' arities.
-/

namespace EPL

/-- How many arguments a constant takes while still a value: all of a
constructor's fields, or an eliminator's scrutinee and all its branches but
the last. -/
def Signature.valueArity (sig : Signature) : DataConst → Option Nat
  | .ctor type index => do
      let decl ← sig[type]?
      let fields ← decl.ctors[index]?
      some fields.length
  | .elim type => do
      let decl ← sig[type]?
      some decl.ctors.length

namespace Eval

/-- `True` or `False`, following the `Bool` convention of `PrimOp.ty`. -/
def boolValue (value : Bool) : RuntimeExpr :=
  .const (.ctor 0 (if value then 0 else 1))

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

/-- Contract a saturated eliminator whose scrutinee is a saturated constructor
of the same type: the chosen branch receives `()` and then the fields. -/
def reduceConst (sig : Signature) : DataConst → List RuntimeExpr → Option RuntimeExpr
  | .elim type, scrutinee :: branches => do
      let decl ← sig[type]?
      if branches.length ≠ decl.ctors.length then none
      match scrutinee.spine with
      | (.const (.ctor type' index), fields) => do
          if type' ≠ type then none
          let fieldTys ← decl.ctors[index]?
          if fields.length ≠ fieldTys.length then none
          let branch ← branches[index]?
          some (Expr.apps branch (.lit .unit :: fields))
      | _ => none
  | _, _ => none

inductive Value (sig : Signature) : RuntimeExpr → Prop
  | lit : Value sig (.lit literal)
  | primOp : Value sig (.primOp op)
  | lambda : Value sig (.lambda param body)
  /-- A primitive operator awaiting its second operand. -/
  | primOpPartial : Value sig argument → Value sig (.app (.primOp op) argument)
  /-- A constant applied to values, short of a redex. -/
  | const :
      expr.spine = (.const c, args) →
      sig.valueArity c = some arity →
      args.length ≤ arity →
      (∀ arg ∈ args, Value sig arg) →
      Value sig expr

inductive Step (sig : Signature) : RuntimeExpr → RuntimeExpr → Prop
  | beta :
      Value sig argument →
      Step sig (.app (.lambda param body) argument) (body.subst1 argument)
  | appFunction :
      Step sig function function' →
      Step sig (.app function argument) (.app function' argument)
  | appArgument :
      Value sig function →
      Step sig argument argument' →
      Step sig (.app function argument) (.app function argument')
  | primOp :
      op.eval left right = some result →
      Step sig (.app (.app (.primOp op) (.lit left)) (.lit right)) result
  | const :
      (Expr.app function argument).spine = (.const c, args) →
      (∀ arg ∈ args, Value sig arg) →
      reduceConst sig c args = some result →
      Step sig (.app function argument) result
  | letRhs :
      Step sig rhs rhs' →
      Step sig (.letIn ann rhs body) (.letIn ann rhs' body)
  | letValue :
      Value sig rhs →
      Step sig (.letIn ann rhs body) (body.subst1 rhs)
  | fixUnfold :
      Step sig (.fix self body) (body.subst1 (.fix self body))

abbrev Steps (sig : Signature) : RuntimeExpr → RuntimeExpr → Prop :=
  Relation.ReflTransGen (Step sig)

/-! ## Executable evaluator -/

def isValue (sig : Signature) : RuntimeExpr → Bool
  | .lit _ | .primOp _ | .lambda _ _ => true
  | .const c => (sig.valueArity c).isSome
  | .app (.primOp _) argument => isValue sig argument
  | .app function argument =>
      isValue sig function && isValue sig argument &&
        match (Expr.app function argument).spine with
        | (.const c, args) =>
            match sig.valueArity c with
            | some arity => decide (args.length ≤ arity)
            | none => false
        | _ => false
  | _ => false

/-- Contract an application of a value to a value, if it is a redex. -/
def reduceApp (sig : Signature) : RuntimeExpr → RuntimeExpr → Option RuntimeExpr
  | .lambda _ body, argument => some (body.subst1 argument)
  | .app (.primOp op) (.lit left), .lit right => op.eval left right
  | function, argument =>
      match (Expr.app function argument).spine with
      | (.const c, args) => reduceConst sig c args
      | _ => none

/-- One step; `none` exactly when there is no `Step` successor. -/
def step? (sig : Signature) : RuntimeExpr → Option RuntimeExpr
  | .app function argument =>
      match step? sig function with
      | some function' => some (.app function' argument)
      | none =>
          if isValue sig function then
            match step? sig argument with
            | some argument' => some (.app function argument')
            | none => if isValue sig argument then reduceApp sig function argument else none
          else none
  | .letIn ann rhs body =>
      match step? sig rhs with
      | some rhs' => some (.letIn ann rhs' body)
      | none => if isValue sig rhs then some (body.subst1 rhs) else none
  | .fix self body => some (body.subst1 (.fix self body))
  | _ => none

/-- Up to `fuel` steps, stopping early where no step applies. (Fuel because
`fix` admits divergence.) -/
def run (sig : Signature) : Nat → RuntimeExpr → RuntimeExpr
  | 0, expr => expr
  | fuel + 1, expr =>
      match step? sig expr with
      | some next => run sig fuel next
      | none => expr

end Eval
end EPL
