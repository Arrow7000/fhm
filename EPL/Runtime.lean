import Mathlib.Logic.Relation
import EPL.Typing

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

namespace EPL

/-- Typing after annotations have been erased. Runtime syntax does not retain
whether a source let was monomorphic or carried an explicit scheme, so the
relation has separate derivations for the same erased constructor. -/
inductive RuntimeTyping : Nat → Ctx → RuntimeExpr → Ty → Prop
  | primLit :
      RuntimeTyping rigidCount ctx (.primLit literal) literal.ty

  | primOp :
      RuntimeTyping rigidCount ctx (.primOp op) op.ty

  | var :
      ctx[index]? = some scheme →
      scheme.WF rigidCount →
      args.length = scheme.paramCount →
      (∀ arg ∈ args, arg.WF rigidCount 0) →
      RuntimeTyping rigidCount ctx (.var index) (scheme.openWith args)

  | lambda :
      paramTy.WF rigidCount 0 →
      RuntimeTyping rigidCount (PolyTy.mono paramTy :: ctx) body bodyTy →
      RuntimeTyping rigidCount ctx (.lambda ann body) (.arrow paramTy bodyTy)

  | app :
      RuntimeTyping rigidCount ctx function (.arrow argumentTy resultTy) →
      RuntimeTyping rigidCount ctx argument argumentTy →
      RuntimeTyping rigidCount ctx (.app function argument) resultTy

  | letMono :
      rhsTy.WF rigidCount 0 →
      RuntimeTyping rigidCount ctx rhs rhsTy →
      RuntimeTyping rigidCount (PolyTy.mono rhsTy :: ctx) body bodyTy →
      RuntimeTyping rigidCount ctx (.letIn ann rhs body) bodyTy

  | letPoly :
      scheme.WF rigidCount →
      ctx.WF rigidCount →
      RuntimeTyping (rigidCount + scheme.paramCount) ctx rhs
        (scheme.openRigids rigidCount) →
      RuntimeTyping rigidCount (scheme :: ctx) body bodyTy →
      RuntimeTyping rigidCount ctx (.letIn ann rhs body) bodyTy

  | fix :
      selfTy.WF rigidCount 0 →
      RuntimeTyping rigidCount (PolyTy.mono selfTy :: ctx) body selfTy →
      RuntimeTyping rigidCount ctx (.fix () body) selfTy

/-- A runtime expression inhabits every semantic instance of a scheme. -/
structure RuntimeHasScheme (rigidCount : Nat) (ctx : Ctx)
    (expr : RuntimeExpr) (scheme : PolyTy) : Prop where
  schemeWF : scheme.WF rigidCount
  typed : ∀ larger, rigidCount ≤ larger → ∀ args,
    args.length = scheme.paramCount →
    (∀ arg ∈ args, arg.WF larger 0) →
    RuntimeTyping larger ctx expr (scheme.openWith args)

end EPL

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
