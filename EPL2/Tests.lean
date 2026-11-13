import EPL2.Infer
import EPL2.Runtime

/-! Executable sanity checks for the definitions. -/

namespace EPL2.Tests

open Expr

def int : SemTy := .prim .int
def boolTy : SemTy := .con 0

def boolSig : Signature := [boolDecl]

/-- `List a = Nil | Cons a (List a)` as declaration 1 after `Bool`. -/
def listSig : Signature :=
  [boolDecl, ⟨1, [[], [.bvar 0, .app (.con 1) (.bvar 0)]]⟩]

def one : Source := .lit (.int 1)

/-- Type of an accepted program. -/
def tyOf (sig : Signature) (src : Source) : Option SemTy := (infer sig src).map (·.ty)

/-- Evaluate an accepted program for at most 1000 steps. -/
def evalOf (sig : Signature) (src : Source) : Option RuntimeExpr :=
  (infer sig src).map fun _ => Eval.run sig 1000 src.erase

-- `fun x => x` alone has an undetermined parameter type: rejected.
#guard infer [] (.lambda none (.var 0)) = none
-- `(fun x => x) 1 : Int`, elaborated with the parameter type.
#guard infer [] (.app (.lambda none (.var 0)) one) =
  some ⟨.app (.lambda (some int) (.var 0)) (.lit (.int 1)), int⟩

/-- `let id : forall a. a -> a = fun x => x in id 1`; at depth 0 the binder is
`rigid 0`. -/
def polyId : Source :=
  .letIn (some ⟨1, .arrow (.rigid 0) (.rigid 0)⟩) (.lambda none (.var 0)) (.app (.var 0) one)

#guard tyOf [] polyId = some int
#guard (infer [] polyId).map (·.elaboration) =
  some (.letIn (some ⟨1, .arrow (.rigid 0) (.rigid 0)⟩)
    (.lambda (some (.rigid 0)) (.var 0)) (.app (.var 0) (.lit (.int 1))))
#guard evalOf [] polyId = some (.lit (.int 1))

/-- A partial polymorphic signature `forall a. a -> _`, completed from the
definition. -/
def partialId : Source :=
  .letIn (some ⟨1, .arrow (.rigid 0) (.var "r")⟩) (.lambda none (.var 0)) (.app (.var 0) one)

#guard tyOf [] partialId = some int

/-- `let f : forall a. _ -> a -> a = fun z y => y in f True True`: the hole
could be `a` or `Bool`, so it is rejected. -/
def ambiguous : Source :=
  .letIn (some ⟨1, .arrow (.var "h") (.arrow (.rigid 0) (.rigid 0))⟩)
    (.lambda none (.lambda none (.var 0)))
    (.app (.app (.var 0) (.const (.ctor 0 0))) (.const (.ctor 0 0)))

#guard tyOf boolSig ambiguous = none

/-- A written scheme cannot be more general than its definition. -/
def tooGeneral : Source :=
  .letIn (some ⟨1, .arrow (.rigid 0) (.rigid 0)⟩) (.lambda none one) one

#guard tyOf [] tooGeneral = none

-- `let c : forall a. Int = 1 in c`: the use instantiates `a` with an
-- unknown that nothing determines, which is fine.
#guard tyOf [] (.letIn (some ⟨1, int.lift⟩) one (.var 0)) = some int

/-- `if 1 < 2 then 'y' else 'n'`. -/
def ifLt : Source :=
  .app (.app (.app (.const (.elim 0))
      (.app (.app (.primOp .intLt) one) (.lit (.int 2))))
      (.lambda none (.lit (.char 'y'))))
    (.lambda none (.lit (.char 'n')))

#guard tyOf boolSig ifLt = some (.prim .char)
#guard evalOf boolSig ifLt = some (.lit (.char 'y'))
#guard tyOf [] ifLt = none

/-- `length (Cons 1 (Cons 2 Nil))` by `fix`. -/
def lengthProgram : Source :=
  let length : Source :=
    .fix (.arrow (.app (.con 1) (.var "a")) int.lift)
      (.lambda none
        (.app (.app (.app (.const (.elim 1)) (.var 0))
          (.lambda none (.lit (.int 0))))
          (.lambda none (.lambda none (.lambda none
            (.app (.app (.primOp .intAdd) one) (.app (.var 4) (.var 0))))))))
  let list : Source :=
    .app (.app (.const (.ctor 1 1)) one)
      (.app (.app (.const (.ctor 1 1)) (.lit (.int 2))) (.const (.ctor 1 0)))
  .app length list

#guard tyOf listSig lengthProgram = some int
#guard evalOf listSig lengthProgram = some (.lit (.int 2))

-- Inference is structural and unification has internal fuel, so the kernel
-- can evaluate inference.
example : tyOf [] polyId = some int := by decide

end EPL2.Tests
