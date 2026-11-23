import EPL.Theorems

/-!
# Tests

Executable checks of unification, annotation allocation, inference and
evaluation, on programs small enough to read. `by decide` tests run in the
kernel; `#guard` tests run in the evaluator.
-/

namespace EPL.Tests

open Expr

/-! ## Shared types and helpers -/

/-- `Int`, at any variable type. -/
def int : Ty V := .prim .int

/-- `Char`, at any variable type. -/
def charTy : Ty V := .prim .char

/-- `Bool`, declaration 0 by the signature convention. -/
def boolTy : Ty V := .con 0

def boolSig : Signature := [boolDecl]

/-- `List a = Nil | Cons a (List a)` as declaration 1 after `Bool`. -/
def listSig : Signature :=
  [boolDecl, ⟨1, [.plain [], .plain [.bvar 0, .app (.con 1) (.bvar 0)]]⟩]

def trueExpr : Expr A := .ctor ⟨0, 0⟩

def falseExpr : Expr A := .ctor ⟨0, 1⟩

def one : Source := .lit (.int 1)

/-- Type of an accepted program. -/
def tyOf (sig : Signature) (src : Source) : Option SemTy := (infer sig src).toOption.map (·.ty)

/-- Evaluate an accepted program for at most 1000 steps. -/
def evalOf (sig : Signature) (src : Source) : Option RuntimeExpr :=
  (infer sig src).toOption.map fun _ => Eval.run 1000 src.erase

/-- `infer` succeeds with `result` exactly when its `Option` form is `some result`. -/
private theorem infer_eq_ok_of_toOption {sig : Signature} {src : Source}
    {result : InferenceResult} (accepted : (infer sig src).toOption = some result) :
    infer sig src = .ok result := by
  cases run : infer sig src with
  | error error => simp [run, Except.toOption] at accepted
  | ok actual => simpa [run, Except.toOption] using accepted

/-! ## A first tour -/

-- `fun x => x` alone has an undetermined parameter type: rejected.
#guard (infer [] (.lambda none (.var 0))).toOption = none
-- `(fun x => x) 1 : Int`, elaborated with the parameter type.
#guard (infer [] (.app (.lambda none (.var 0)) one)).toOption =
  some ⟨.app (.lambda (some int) (.var 0)) (.lit (.int 1)), int⟩

/-- `let id : forall a. a -> a = fun x => x in id 1`; at depth 0 the binder is
`rigid 0`. -/
def polyId : Source :=
  .letIn (some ⟨1, .arrow (.rigid 0) (.rigid 0)⟩) (.lambda none (.var 0)) (.app (.var 0) one)

#guard tyOf [] polyId = some int
#guard (infer [] polyId).toOption.map (·.elaboration) =
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
    (.app (.app (.var 0) (.ctor ⟨0, 0⟩)) (.ctor ⟨0, 0⟩))

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
  .match (.app (.app (.primOp .intLt) one) (.lit (.int 2)))
    [(⟨0, 0⟩, .lit (.char 'y')), (⟨0, 1⟩, .lit (.char 'n'))]

#guard tyOf boolSig ifLt = some (.prim .char)
#guard evalOf boolSig ifLt = some (.lit (.char 'y'))
#guard tyOf [] ifLt = none

/-- `length (Cons 1 (Cons 2 Nil))` by `fix`. -/
def lengthProgram : Source :=
  let length : Source :=
    .fix (some (.arrow (.app (.con 1) (.var "a")) int.lift))
      (.lambda none
        (.match (.var 0)
          [(⟨1, 0⟩, .lit (.int 0)),
           (⟨1, 1⟩, .lambda none (.lambda none
             (.app (.app (.primOp .intAdd) one) (.app (.var 3) (.var 0)))))]))
  let list : Source :=
    .app (.app (.ctor ⟨1, 1⟩) one)
      (.app (.app (.ctor ⟨1, 1⟩) (.lit (.int 2))) (.ctor ⟨1, 0⟩))
  .app length list

#guard tyOf listSig lengthProgram = some int
#guard evalOf listSig lengthProgram = some (.lit (.int 2))

-- Inference is structural and unification has internal fuel, so the kernel
-- can evaluate inference.
example : tyOf [] polyId = some int := by decide

/-! ## Unification -/

/-- `?0` and `?1` both live at level 1, so `?1` may be solved to rigid 0. -/
def arrowExample : Option MStore :=
  (MStore.unify [⟨1, none⟩, ⟨1, none⟩]
    (.arrow (.var 0) (.rigid 0))
    (.arrow (.prim .int) (.var 1))).toOption

example : arrowExample = some [⟨1, some (.prim .int)⟩, ⟨1, some (.rigid 0)⟩] := by
  decide

/-- Solving `?0 := ?1` and then `?1 := Int` rewrites the earlier entry, so the
store stays normalized. -/
example :
    (MStore.unify [⟨0, none⟩, ⟨0, none⟩]
        (.arrow (.var 0) (.var 1))
        (.arrow (.var 1) (.prim .int))).toOption =
      some [⟨0, some (.prim .int)⟩, ⟨0, some (.prim .int)⟩] := by
  decide

/-- A level-0 metavariable cannot be solved to rigid 0: it would escape. -/
example : (MStore.unify [⟨0, none⟩] (.var 0) (.rigid 0)).toOption = none := by
  decide

/-- Binding a level-0 metavariable lowers the metavariables of its solution. -/
example :
    (MStore.unify [⟨0, none⟩, ⟨1, none⟩] (.var 0) (.arrow (.var 1) (.prim .int))).toOption =
      some [⟨0, some (.arrow (.var 1) (.prim .int))⟩, ⟨0, none⟩] := by
  decide

example : (MStore.unify [] (.rigid 0) (.prim .int)).toOption = none := by
  decide

/-- Type applications decompose: `List ?0 ~ List Int` solves `?0 := Int`. -/
example :
    (MStore.unify [⟨0, none⟩] (.app (.con 0) (.var 0)) (.app (.con 0) (.prim .int))).toOption =
      some [⟨0, some (.prim .int)⟩] := by
  decide

/-- Distinct type constructors do not unify, even at the same arguments. -/
example :
    (MStore.unify [] (.app (.con 0) (.prim .int)) (.app (.con 1) (.prim .int))).toOption = none := by
  decide

/-- A higher-kinded unknown may be solved to a type constructor. -/
example :
    (MStore.unify [⟨0, none⟩] (.app (.var 0) (.prim .int)) (.app (.con 3) (.prim .int))).toOption =
      some [⟨0, some (.con 3)⟩] := by
  decide

example : (MStore.unify [⟨0, none⟩] (.var 0) (.arrow (.var 0) (.prim .int))).toOption = none := by
  decide

/-! ## Annotation allocation -/

def repeated : Template :=
  .arrow (.var "a") (.var "a")

def independent : Template :=
  .arrow (.var "a") (.arrow (.var "_") (.var "b"))

example : (MStore.allocate (List.replicate 10 ⟨0, none⟩) 10 repeated).1 =
    .arrow (.var 10) (.var 10) := by
  decide

example : (MStore.allocate (List.replicate 10 ⟨0, none⟩) 10 repeated).2.length = 11 := by
  decide

/-- Holes are numbered in order of first occurrence. -/
example : (MStore.allocate (List.replicate 20 ⟨0, none⟩) 20 independent).1 =
    .arrow (.var 20) (.arrow (.var 21) (.var 22)) := by
  decide

example : (MStore.allocate (List.replicate 20 ⟨0, none⟩) 20 independent).2.length = 23 := by
  decide

/-! ## Inference -/

def polyIdentityAnnotation : PolyAnn Template :=
  ⟨1, .arrow (.rigid 0) (.rigid 0)⟩

def identityRhs : Source :=
  .lambda none (.var 0)

/-- The outer identity is explicitly polymorphic. The nested monomorphic let
uses it at `Int`, then the continuation uses it independently at `Bool`. -/
def explicitPolyProgram : Source :=
  .letIn (some polyIdentityAnnotation) identityRhs
    (.letIn none
      (.app (.var 0) (.lit (.int 5)))
      (.app (.var 1) trueExpr))

/-- Without the written `forall`, the same identity has one monotype and
cannot be used at both `Int` and `Bool`. -/
def implicitPolyProgram : Source :=
  .letIn none identityRhs
    (.letIn none
      (.app (.var 0) (.lit (.int 5)))
      (.app (.var 1) trueExpr))

/-- An omitted lambda annotation is constrained by how its parameter is used
inside the body. -/
def inferredIntLambda : Source :=
  .lambda none
    (.app (.app (.primOp .intAdd) (.var 0)) (.lit (.int 1)))

/-- General recursion is monomorphic and has no recursive binding group. This
loop is intentionally divergent but has the ordinary function type. -/
def integerLoop : Source :=
  .fix (some (.arrow int int))
    (.lambda (some int)
      (.app (.var 1) (.var 0)))

example : (infer boolSig inferredIntLambda).toOption.map (·.ty) =
    some (.arrow int int) := by
  decide

example : (infer boolSig explicitPolyProgram).toOption.map (·.ty) = some boolTy := by
  decide

example : (infer boolSig implicitPolyProgram).toOption.map (·.ty) = none := by
  decide

example : (infer boolSig identityRhs).toOption.map (·.ty) = none := by
  decide

def deadAmbiguousLambda : Source :=
  .letIn none identityRhs (.lit .unit)

example : (infer boolSig deadAmbiguousLambda).toOption.map (·.ty) = none := by
  decide

def deadAmbiguousLambdaInScheme : Source :=
  .letIn (some ⟨0, .prim .unit⟩)
    deadAmbiguousLambda
    (.lit .unit)

example : (infer boolSig deadAmbiguousLambdaInScheme).toOption.map (·.ty) = none := by
  decide

example : (infer boolSig integerLoop).toOption.map (·.ty) =
    some (.arrow int int) := by
  decide

def skolemEscape : Source :=
  .lambda none
    (.letIn (some ⟨1, .rigid 0⟩)
      (.var 0)
      (.lit .unit))

example : (infer boolSig skolemEscape).toOption.map (·.ty) = none := by
  decide

def outerConstraint : Source :=
  .lambda none
    (.letIn (some ⟨0, int⟩)
      (.var 0)
      (.var 1))

example : (infer boolSig outerConstraint).toOption.map (·.ty) =
    some (.arrow int int) := by
  decide

def solvedSignatureHole : Source :=
  .letIn (some ⟨1, .var "_"⟩)
    (.lit (.int 5))
    (.var 0)

example : (infer boolSig solvedSignatureHole).toOption.map (·.ty) = some int := by
  decide

def namedIdentityAnnotation : PolyAnn Template :=
  ⟨1, .arrow (.var "domain") (.rigid 0)⟩

def namedIdentity : Source :=
  .letIn (some namedIdentityAnnotation)
    identityRhs
    (.app (.var 0) (.lit (.int 5)))

example : (infer boolSig namedIdentity).toOption.map (·.ty) = some int := by
  decide

def hiddenBadBoundAnnotation : Source :=
  .letIn none
    (.lambda (some (.bvar 0)) (.lit .unit))
    (.lit .unit)

def hiddenBadRigidAnnotation : Source :=
  .letIn none
    (.lambda (some (.rigid 0)) (.lit .unit))
    (.lit .unit)

example : (infer boolSig hiddenBadBoundAnnotation).toOption.map (·.ty) = none := by decide
example : (infer boolSig hiddenBadRigidAnnotation).toOption.map (·.ty) = none := by decide

/-- An unknown created while checking an explicit scheme may survive it: here
`x : Int -> ?r` is constrained inside `f`'s region, and `?r` is only
determined (as `Int`) after leaving it.

`fun x => let f : forall a. a -> a = (let _ = x 1 in fun y => y) in x 1 + 1` -/
def regionUnknownEscapes : Source :=
  .lambda none
    (.letIn (some polyIdentityAnnotation)
      (.letIn none (.app (.var 0) (.lit (.int 1))) (.lambda none (.var 0)))
      (.app (.app (.primOp .intAdd) (.app (.var 1) (.lit (.int 1))))
        (.lit (.int 1))))

example : (infer boolSig regionUnknownEscapes).toOption.map (·.ty) =
    some (.arrow (.arrow int int) int) := by
  decide

/-- `x 1 + 1`, with `x` at de Bruijn index 1. -/
def applyXPlusOne : Source :=
  .app (.app (.primOp .intAdd) (.app (.var 1) (.lit (.int 1))))
    (.lit (.int 1))

/-- An implicit type inside an explicit scheme's region may be determined only
after the region: `z`'s type becomes `Int` through the later `x 1`.

`fun x => let f : forall a. a -> a = (let _ = (fun z => x z) in fun y => y) in x 1 + 1` -/
def deferredParameter : Source :=
  .lambda none (.letIn (some polyIdentityAnnotation)
    (.letIn none (.lambda none (.app (.var 1) (.var 0))) (.lambda none (.var 0)))
    applyXPlusOne)

example : (infer boolSig deferredParameter).toOption.map (·.ty) =
    some (.arrow (.arrow int int) int) := by
  decide

/-- `forall a. _ -> a -> a` -/
def holeFirstScheme : PolyAnn Template :=
  ⟨1, .arrow (.var "_") (.arrow (.rigid 0) (.rigid 0))⟩

/-- A hole in a written scheme may likewise be determined after its region.

`fun x => let f : forall a. _ -> a -> a = fun z y => (let _ = x z in y) in x 1 + 1` -/
def deferredSchemeHole : Source :=
  .lambda none (.letIn (some holeFirstScheme)
    (.lambda none (.lambda none (.letIn none (.app (.var 2) (.var 1)) (.var 1))))
    applyXPlusOne)

example : (infer boolSig deferredSchemeHole).toOption.map (·.ty) =
    some (.arrow (.arrow int int) int) := by
  decide

/-- The completed scheme is recorded in the elaboration. -/
example : (infer boolSig deferredSchemeHole).toOption.map (·.elaboration) =
    some (.lambda (some (.arrow int int))
      (.letIn (some ⟨1, .arrow int (.arrow (.rigid 0) (.rigid 0))⟩)
        (.lambda (some int) (.lambda (some (.rigid 0))
          (.letIn none (.app (.var 2) (.var 1)) (.var 1))))
        (.app (.app (.primOp .intAdd) (.app (.var 1) (.lit (.int 1))))
          (.lit (.int 1))))) := by
  decide

/-- A scheme hole that nothing determines is still rejected.

`fun (x : Int) => let f : forall a. _ -> a -> a = fun z y => y in 0` -/
example : (infer boolSig (.lambda (some int)
    (.letIn (some holeFirstScheme) (.lambda none (.lambda none (.var 0)))
      (.lit (.int 0))))).toOption = none := by
  decide

/-- A hole that only uses could determine is rejected: `_ := a` and
`_ := Bool` both elaborate.

`let f : forall a. _ -> a -> a = fun z y => y in f true true` -/
example : (infer boolSig (.letIn (some holeFirstScheme) (.lambda none (.lambda none (.var 0)))
    (.app (.app (.var 0) trueExpr) trueExpr))).toOption = none := by
  decide

/-- Holes are completed from the definition and its context, not from uses:
this is rejected even though only `_ := Int` would typecheck.

`let f : forall a. _ -> a -> a = fun z y => y in f 1 true` -/
example : (infer boolSig (.letIn (some holeFirstScheme) (.lambda none (.lambda none (.var 0)))
    (.app (.app (.var 0) (.lit (.int 1))) trueExpr))).toOption = none := by
  decide

/-- A hole fixed to the scheme's own binder by its definition.

`let f : forall a. _ -> a -> a = fun (z : a) y => y in 0` -/
example : (infer boolSig (.letIn (some holeFirstScheme)
    (.lambda (some (.rigid 0)) (.lambda none (.var 0)))
    (.lit (.int 0)))).toOption.map (·.elaboration) =
    some (.letIn (some ⟨1, .arrow (.rigid 0) (.arrow (.rigid 0) (.rigid 0))⟩)
      (.lambda (some (.rigid 0)) (.lambda (some (.rigid 0)) (.var 0)))
      (.lit (.int 0))) := by
  decide

/-- A rigid variable may not escape through an outer unknown.

`fun x => let f : forall a. a -> a = fun y => (let _ = x y in y) in 0` -/
example : (infer boolSig (.lambda none (.letIn (some polyIdentityAnnotation)
    (.lambda none (.letIn none (.app (.var 1) (.var 0)) (.var 1)))
    (.lit (.int 0))))).toOption = none := by
  decide

/-- `_ -> Int`: a signature without binders is an ordinary partial annotation. -/
def monoHoleScheme : PolyAnn Template :=
  ⟨0, .arrow (.var "_") int⟩

/-- Its hole may be determined by a later use.

`let f : _ -> Int = fun x => 1 in f 3` -/
example : (infer boolSig (.letIn (some monoHoleScheme) (.lambda none (.lit (.int 1)))
    (.app (.var 0) (.lit (.int 3))))).toOption.map (·.ty) = some int := by
  decide

/-- If nothing determines it, the program is ambiguous.

`let f : _ -> Int = fun x => 1 in 0` -/
example : (infer boolSig (.letIn (some monoHoleScheme) (.lambda none (.lit (.int 1)))
    (.lit (.int 0)))).toOption = none := by
  decide

def inferredHoleLambda : Source :=
  .lambda (some (.var "_"))
    (.app
      (.app (.primOp .intAdd) (.var 0))
      (.lit (.int 1)))

example : (infer boolSig inferredHoleLambda).toOption.map (·.ty) =
    some (.arrow int int) := by
  decide

def ambiguousHoleLambda : Source :=
  .lambda (some (.var "_")) (.var 0)

example : (infer boolSig ambiguousHoleLambda).toOption.map (·.ty) = none := by
  decide

def partlyInferredPolyAnnotation : PolyAnn Template :=
  ⟨1, .arrow (.var "_") (.rigid 0)⟩

def partlyInferredPolyProgram : Source :=
  .letIn (some partlyInferredPolyAnnotation) identityRhs
    (.app (.var 0) trueExpr)

example : (infer boolSig partlyInferredPolyProgram).toOption.map (·.ty) = some boolTy := by
  decide

def falsePolyAnnotation : PolyAnn Template :=
  ⟨1, .arrow (.rigid 0) int⟩

def falsePolyProgram : Source :=
  .letIn (some falsePolyAnnotation) identityRhs
    (.lit .unit)

example : (infer boolSig falsePolyProgram).toOption.map (·.ty) = none := by
  decide

def inferredIntegerFix : Source :=
  .fix none
    (.app
      (.app (.primOp .intAdd) (.var 0))
      (.lit (.int 1)))

example : (infer boolSig inferredIntegerFix).toOption.map (·.ty) = some int := by
  decide

def incoherentNamedHole : Source :=
  .app
    (.lambda
      (some (.arrow (.var "shared") (.var "shared")))
      (.var 0))
    (.lambda (some int) trueExpr)

example : (infer boolSig incoherentNamedHole).toOption.map (·.ty) = none := by decide

def namedIntegerLambda : Source :=
  .lambda (some (.var "local"))
    (.app
      (.app (.primOp .intAdd) (.var 0))
      (.lit (.int 1)))

def namedBooleanLambda : Source :=
  .lambda (some (.var "local"))
    (.app
      (.lambda (some boolTy) (.lit (.int 1)))
      (.var 0))

def independentNamedHoles : Source :=
  .letIn none namedIntegerLambda namedBooleanLambda

example : (infer boolSig independentNamedHoles).toOption.map (·.ty) =
    some (.arrow boolTy int) := by
  decide

def reuseAfterPolyCheck : Source :=
  .letIn (some polyIdentityAnnotation) identityRhs inferredIntLambda

example : (infer boolSig reuseAfterPolyCheck).toOption.map (·.ty) =
    some (.arrow int int) := by
  decide

/-! ## Inference soundness canaries

These declarative derivations are obtained solely from a successful run of the
public inference function. -/

example : ∃ elaboration, Typing boolSig 0 [] inferredIntLambda elaboration
    (.arrow int int) :=
  ⟨_, infer_typing (infer_eq_ok_of_toOption (by
    decide : (infer boolSig inferredIntLambda).toOption = some
      ⟨.lambda (some int) (.app (.app (.primOp .intAdd) (.var 0)) (.lit (.int 1))),
        .arrow int int⟩))⟩

example : ∃ elaboration, Typing boolSig 0 [] explicitPolyProgram elaboration boolTy :=
  ⟨_, infer_typing (infer_eq_ok_of_toOption (by
    decide : (infer boolSig explicitPolyProgram).toOption = some
      ⟨.letIn (some ⟨1, .arrow (.rigid 0) (.rigid 0)⟩)
          (.lambda (some (.rigid 0)) (.var 0))
          (.letIn none (.app (.var 0) (.lit (.int 5))) (.app (.var 1) trueExpr)),
        boolTy⟩))⟩

example : ∃ elaboration, Typing boolSig 0 [] partlyInferredPolyProgram elaboration boolTy :=
  ⟨_, infer_typing (infer_eq_ok_of_toOption (by
    decide : (infer boolSig partlyInferredPolyProgram).toOption = some
      ⟨.letIn (some ⟨1, .arrow (.rigid 0) (.rigid 0)⟩)
          (.lambda (some (.rigid 0)) (.var 0))
          (.app (.var 0) trueExpr),
        boolTy⟩))⟩

example : ∃ elaboration, Typing boolSig 0 [] inferredIntegerFix elaboration int :=
  ⟨_, infer_typing (infer_eq_ok_of_toOption (by
    decide : (infer boolSig inferredIntegerFix).toOption = some
      ⟨.fix (some int)
          (.app (.app (.primOp .intAdd) (.var 0)) (.lit (.int 1))),
        int⟩))⟩

example : ∃ elaboration, Typing boolSig 0 [] integerLoop elaboration (.arrow int int) :=
  ⟨_, infer_typing (infer_eq_ok_of_toOption (by
    decide : (infer boolSig integerLoop).toOption = some
      ⟨.fix (some (.arrow int int)) (.lambda (some int) (.app (.var 1) (.var 0))),
        .arrow int int⟩))⟩

/-! ## Evaluator -/

/-- `(fun x => x + 1) 41` -/
def incrementApplied : Source :=
  .app inferredIntLambda (.lit (.int 41))

/-- `let x = 40 in x + 2` -/
def letAdd : Source :=
  .letIn none (.lit (.int 40))
    (.app (.app (.primOp .intAdd) (.var 0)) (.lit (.int 2)))

/-- Final value of `evaluate`, or `none` if inference rejected the program or
fuel ran out. -/
def finalValue (input : Source) (fuel : Nat) : Option RuntimeExpr :=
  (evaluate boolSig input fuel).toOption.bind (·.2.value?)

#guard finalValue incrementApplied 10 = some (.lit (.int 42))
#guard finalValue letAdd 10 = some (.lit (.int 42))
#guard finalValue explicitPolyProgram 50 = some trueExpr

-- Divergent programs are well-typed but never finish.
#guard finalValue (.app integerLoop (.lit (.int 0))) 100 = none
#guard finalValue inferredIntegerFix 100 = none

-- Rejected programs never run.
#guard (evaluate boolSig deadAmbiguousLambda 10).toOption.isNone

/-! ## Data types -/

/-- A field mentioning an undeclared parameter makes its declaration ill
formed: `decl?` hides it, so none of its constructors has a scheme and no
match can name it. Other declarations are unaffected. -/
def illScopedSig : Signature := [boolDecl, ⟨0, [.plain [.bvar 0]]⟩]

example : illScopedSig.decl? 1 = none := by decide
example : illScopedSig.decl? 0 = some boolDecl := by decide
example : illScopedSig.ctorScheme ⟨1, 0⟩ = none := by decide
example : (infer illScopedSig trueExpr).toOption.map (·.ty) = some boolTy := by decide
example : (listSig.decl? 1).isSome := by decide
example : (listSig.ctorScheme ⟨1, 1⟩).isSome := by decide

/-- `if c then a else b` as a match on `Bool`. -/
def ifThen (c a b : Source) : Source :=
  .match c [(⟨0, 0⟩, a), (⟨0, 1⟩, b)]

def nil : Source := .ctor ⟨1, 0⟩

def cons (h t : Source) : Source := .app (.app (.ctor ⟨1, 1⟩) h) t

def listTy : Ty V := .app (.con 1) int

/-- `if False then 1 else 2 : Int`, evaluating to `2`. -/
def ifFalse : Source :=
  ifThen falseExpr (.lit (.int 1)) (.lit (.int 2))

example : (infer listSig ifFalse).toOption.map (·.ty) = some int := by
  decide

#guard ((evaluate listSig ifFalse 50).toOption.bind (·.2.value?)) =
  some (.lit (.int 2))

/-- `match Cons 5 Nil with Nil => 0 | Cons x xs => x : Int`, evaluating to
`5`, and annotating `x : Int` and `xs : List Int`. -/
def matchCons : Source :=
  .match (cons (.lit (.int 5)) nil)
    [(⟨1, 0⟩, .lit (.int 0)),
     (⟨1, 1⟩, .lambda none (.lambda none (.var 1)))]

example : (infer listSig matchCons).toOption.map (·.ty) = some int := by
  decide

example : (infer listSig matchCons).toOption.map (·.elaboration) =
    some (.match (.app (.app (.ctor ⟨1, 1⟩) (.lit (.int 5)))
          (.ctor ⟨1, 0⟩))
      [(⟨1, 0⟩, .lit (.int 0)),
       (⟨1, 1⟩, .lambda (some int) (.lambda (some listTy) (.var 1)))]) := by
  decide

#guard ((evaluate listSig matchCons 50).toOption.bind (·.2.value?)) =
  some (.lit (.int 5))

/-- `if 1 then True else False` is rejected: the scrutinee must be `Bool`. -/
def ifInt : Source :=
  ifThen (.lit (.int 1)) trueExpr falseExpr

example : (infer listSig ifInt).toOption = none := by
  decide

/-- A partial constructor application is a value of function type. -/
def partialCons : Source :=
  .app (.ctor ⟨1, 1⟩) (.lit (.int 1))

example : (infer listSig partialCons).toOption.map (·.ty) =
    some (.arrow listTy listTy) := by
  decide

example : Eval.Value partialCons.erase :=
  Eval.Value.ctor (ref := ⟨1, 1⟩) (fields := [.lit (.int 1)]) rfl (by
    intro field h
    rcases List.mem_singleton.mp h with rfl
    exact .lit)

#guard ((evaluate listSig partialCons 10).toOption.bind (·.2.value?)) =
  some (.app (.ctor ⟨1, 1⟩) (.lit (.int 1)))

/-- Recursive list length via `fix`, over `listSig`. -/
def listInt : Source :=
  cons (.lit (.int 1))
    (cons (.lit (.int 2)) (cons (.lit (.int 3)) nil))

def listNilBranch : Source :=
  .lit (.int 0)

def listConsBranch : Source :=
  .lambda none (.lambda none
    (.app (.app (.primOp .intAdd) (.lit (.int 1)))
      (.app (.var 3) (.var 0))))

def listMatch (scrutinee : Source) : Source :=
  .match scrutinee [(⟨1, 0⟩, listNilBranch), (⟨1, 1⟩, listConsBranch)]

def listLength : Source :=
  .fix (some (.arrow listTy int))
    (.lambda (some listTy) (listMatch (.var 0)))

example : (infer listSig (.app listLength listInt)).toOption.map (·.ty) = some int := by
  decide

#guard ((evaluate listSig (.app listLength listInt) 200).toOption.bind (·.2.value?)) =
  some (.lit (.int 3))

/-! ## Partial, empty and mixed matches

A match may be partial; exhaustiveness is a separate check that `evaluate`
requires. -/

/-- `match False with True => 1`, missing the `False` branch. -/
def partialMatch : Source :=
  .match falseExpr [(⟨0, 0⟩, .lit (.int 1))]

example : (infer boolSig partialMatch).toOption.map (·.ty) = some int := by
  decide

example : partialMatch.exhaustive boolSig = false := by decide

-- Inference accepts it, but `evaluate` refuses non-exhaustive programs.
#guard (evaluate boolSig partialMatch 50).toOption.isNone

-- Evaluation of the erasure stops at the match, which is not a value.
#guard (Eval.step? (Eval.run 50 partialMatch.erase)).isNone
#guard Eval.isValue (Eval.run 50 partialMatch.erase) = false

/-- A match with no branches has no type to give its result. -/
def emptyMatch : Source :=
  .match trueExpr []

example : (infer boolSig emptyMatch).toOption = none := by decide

/-- Patterns naming two different types are rejected. -/
def crossTypedMatch : Source :=
  .match trueExpr [(⟨0, 0⟩, trueExpr), (⟨1, 0⟩, nil)]

example : (infer listSig crossTypedMatch).toOption = none := by decide

/-! ## Primitive operations -/

def intSubExpr : Source :=
  .app (.app (.primOp .intSub) (.lit (.int 1))) (.lit (.int 5))

example : (infer boolSig intSubExpr).toOption.map (·.ty) = some int := by
  decide

#guard ((evaluate boolSig intSubExpr 50).toOption.bind (·.2.value?)) =
  some (.lit (.int (-4)))

def intLtExpr (left right : Int) : Source :=
  .app (.app (.primOp .intLt) (.lit (.int left))) (.lit (.int right))

def charIf : Source :=
  ifThen (intLtExpr 1 2) (.lit (.char 'y')) (.lit (.char 'n'))

def charIfFalse : Source :=
  ifThen (intLtExpr 2 1) (.lit (.char 'y')) (.lit (.char 'n'))

example : (infer boolSig charIf).toOption.map (·.ty) = some charTy := by
  decide

#guard ((evaluate boolSig charIf 50).toOption.bind (·.2.value?)) =
  some (.lit (.char 'y'))

#guard ((evaluate boolSig charIfFalse 50).toOption.bind (·.2.value?)) =
  some (.lit (.char 'n'))

def charLtExpr : Source :=
  .app (.app (.primOp .charLt) (.lit (.char 'a'))) (.lit (.char 'b'))

example : (infer boolSig charLtExpr).toOption.map (·.ty) = some boolTy := by
  decide

#guard ((evaluate boolSig charLtExpr 50).toOption.bind (·.2.value?)) =
  some (Eval.boolValue true)

/-- Declaration 0 is `List`-shaped rather than `True | False`. -/
def listShapedSig : Signature :=
  [⟨1, [.plain [], .plain [.bvar 0, .app (.con 0) (.bvar 0)]]⟩]

example : (infer [] (intLtExpr 1 2)).toOption = none := by
  decide

example : (infer listShapedSig (intLtExpr 1 2)).toOption = none := by
  decide

example : (infer boolSig (.app (.app (.primOp .intAdd) (.lit (.int 1)))
    (.lit (.char 'c')))).toOption = none := by
  decide

def partialIntLt : Source :=
  .app (.primOp .intLt) (.lit (.int 1))

example : (infer boolSig partialIntLt).toOption.map (·.ty) =
    some (.arrow int boolTy) := by
  decide

example : Eval.Value partialIntLt.erase :=
  Eval.Value.primOpPartial (op := .intLt) .lit

/-- `fix f : Int -> Int. fun n => if n < 1 then 0 else n + f (n - 1)`. -/
def primRecursive : Source :=
  .app
    (.fix (some (.arrow int int))
      (.lambda (some int)
        (ifThen
          (.app (.app (.primOp .intLt) (.var 0)) (.lit (.int 1)))
          (.lit (.int 0))
          (.app (.app (.primOp .intAdd) (.var 0))
            (.app (.var 1)
              (.app (.app (.primOp .intSub) (.var 0)) (.lit (.int 1))))))))
    (.lit (.int 4))

example : (infer boolSig primRecursive).toOption.map (·.ty) = some int := by
  decide

#guard ((evaluate boolSig primRecursive 500).toOption.bind (·.2.value?)) =
  some (.lit (.int 10))

/-! ## `implicitPolyProgram` is untypable

Rejection by `infer` only says there is no unique elaboration. This program
has no typing at all, in any signature, by inversion of `Typing`. -/

/-- A variable whose context entry is monomorphic has that entry's type. -/
private theorem mono_var_inv {sig : Signature} {k : Nat} {ctx : Ctx Empty} {index : Nat}
    {expected : SemTy} {elaboration : Elab} {ty : SemTy}
    (typing : Typing sig k ctx (.var index) elaboration ty)
    (lookup : ctx[index]? = some (Scheme.mono expected)) : ty = expected := by
  cases typing with
  | var found inst =>
      rw [lookup] at found
      injection found with hscheme
      rw [← hscheme] at inst
      exact Scheme.instance_mono.mp inst

/-- The identity function's type is `param -> param` for some `param`. -/
private theorem identity_type {sig : Signature} {k : Nat} {ctx : Ctx Empty}
    {elaboration : Elab} {ty : SemTy}
    (typing : Typing sig k ctx identityRhs elaboration ty) :
    ∃ param, ty = .arrow param param := by
  cases typing with
  | lambda _ _ bodyTyping =>
      cases bodyTyping with
      | var found inst =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at found
          rw [← found] at inst
          have bodyEq : _ = _ := Scheme.instance_mono.mp inst
          exact ⟨_, by rw [bodyEq]⟩

/-- A fold of type applications over `.con` is never a primitive type. -/
private theorem foldl_app_ne_prim (head : SemTy) (xs : List SemTy) (p : PrimTy)
    (hhead : ∀ q, head ≠ .prim q) :
    xs.foldl (fun h a => .app h a) head ≠ .prim p := by
  induction xs generalizing head with
  | nil => exact hhead p
  | cons x xs ih =>
      exact ih (.app head x) (by intro q h; cases h)

private theorem apps_ne_prim (head : SemTy) (xs : List SemTy) (p : PrimTy)
    (hhead : ∀ q, head ≠ .prim q) : Ty.apps head xs ≠ .prim p :=
  foldl_app_ne_prim head xs p hhead

private theorem arrows_ne_prim (domains : List SemTy) (codomain : SemTy) (p : PrimTy)
    (hcod : ∀ q, codomain ≠ .prim q) : Ty.arrows domains codomain ≠ .prim p := by
  cases domains with
  | nil => exact hcod p
  | cons domain domains => intro h; cases h

private theorem instantiate_apps (args : List SemTy) (xs : List SemTy) :
    ∀ head : SemTy, (Ty.apps head xs).instantiate args =
      Ty.apps (head.instantiate args) (xs.map (·.instantiate args)) := by
  induction xs with
  | nil => intro head; rfl
  | cons x xs ih =>
      intro head
      rw [show Ty.apps head (x :: xs) = Ty.apps (.app head x) xs from rfl]
      rw [ih (.app head x)]
      rfl

private theorem instantiate_arrows (args : List SemTy) (codomain : SemTy) :
    ∀ domains : List SemTy, (Ty.arrows domains codomain).instantiate args =
      Ty.arrows (domains.map (·.instantiate args)) (codomain.instantiate args) := by
  intro domains
  induction domains with
  | nil => rfl
  | cons domain domains ih =>
      change Ty.arrow (domain.instantiate args)
          ((Ty.arrows domains codomain).instantiate args) =
        Ty.arrow (domain.instantiate args)
          (Ty.arrows (domains.map (·.instantiate args)) (codomain.instantiate args))
      rw [ih]

/-- The instance of a constructor's scheme is headed by its data type, so it is
never a primitive type. -/
private theorem ctorScheme_inst_ne_prim (decl : DataDecl) (type : Nat)
    (ctor : CtorDecl) (args : List SemTy) (p : PrimTy) :
    (decl.ctorScheme type ctor).inst args ≠ .prim p := by
  unfold DataDecl.ctorScheme Scheme.inst DataDecl.selfTy
  rw [instantiate_arrows, instantiate_apps]
  apply arrows_ne_prim
  intro q
  exact apps_ne_prim (.con type) _ q (by intro r h; cases h)

/-- A constructor's scheme is its declaration's `ctorScheme`. -/
private theorem ctorScheme_eq {sig : Signature} {type index : Nat}
    {scheme : Scheme Empty} (found : sig.ctorScheme ⟨type, index⟩ = some scheme) :
    ∃ (decl : DataDecl) (ctor : CtorDecl),
      sig.decl? type = some decl ∧ decl.ctors[index]? = some ctor ∧
        scheme = decl.ctorScheme type ctor := by
  cases hdecl : sig.decl? type with
  | none => simp [Signature.ctorScheme, hdecl] at found
  | some decl =>
      cases hfields : decl.ctors[index]? with
      | none => simp [Signature.ctorScheme, hdecl, hfields] at found
      | some fields =>
          have hsome : sig.ctorScheme ⟨type, index⟩ = some (decl.ctorScheme type fields) := by
            simp [Signature.ctorScheme, hdecl, hfields]
          rw [hsome] at found
          exact ⟨decl, fields, rfl, hfields, (Option.some.inj found).symm⟩

/-- A constructor constant never has a primitive type. -/
private theorem ctor_ne_prim {sig : Signature} {k : Nat} {ctx : Ctx Empty}
    {ref : CtorRef} {elaboration : Elab} {p : PrimTy}
    (typing : Typing sig k ctx (.ctor ref) elaboration (.prim p)) :
    False := by
  cases typing with
  | ctor found inst =>
      obtain ⟨decl, fields, _, _, rfl⟩ := ctorScheme_eq found
      obtain ⟨args, _, _, hinst⟩ := inst
      exact ctorScheme_inst_ne_prim decl ref.type fields args p hinst

theorem implicitPolyProgram_untypable {sig : Signature} :
    ¬ ∃ elaboration ty, Typing sig 0 [] implicitPolyProgram elaboration ty := by
  rintro ⟨elaboration, ty, typing⟩
  cases typing with
  | letMono rhsTyping bodyTyping =>
      obtain ⟨param, rhsEq⟩ := identity_type rhsTyping
      cases rhsEq
      cases bodyTyping with
      | letMono nestedRhsTyping nestedBodyTyping =>
          cases nestedRhsTyping with
          | app functionTyping argumentTyping =>
              cases argumentTyping with
              | lit =>
                  have funEq :=
                    mono_var_inv functionTyping (expected := .arrow param param) (by simp)
                  have paramEq : param = (.prim .int : SemTy) :=
                    ((Ty.arrow.inj funEq).1).symm
                  cases nestedBodyTyping with
                  | app finalFunctionTyping finalArgumentTyping =>
                      have finalFunEq :=
                        mono_var_inv finalFunctionTyping
                          (expected := .arrow param param) (by simp)
                      rw [paramEq] at finalFunEq
                      cases (Ty.arrow.inj finalFunEq).1
                      exact ctor_ne_prim finalArgumentTyping

/-! ## Errors

Which error inference reports is not part of the specification; these tests
pin down the current choices, one per kind of error. -/

/-- The error `infer` reports, if any. -/
def errorOf (sig : Signature) (src : Source) : Option InferError :=
  match infer sig src with
  | .error error => some error
  | .ok _ => none

/-- `1 x`, with `x` unbound: the error is at the argument. -/
example : errorOf boolSig (.app one (.var 5)) = some ⟨[.appArgument], .unboundVar⟩ := by
  decide

example : errorOf boolSig (.ctor ⟨7, 0⟩) = some ⟨[], .unknownCtor⟩ := by decide

/-- `1 < 2` without `Bool`: the error is at the operator. -/
example : errorOf listShapedSig (intLtExpr 1 2) =
    some ⟨[.appFunction, .appFunction], .noBool⟩ := by
  decide

example : errorOf boolSig hiddenBadRigidAnnotation =
    some ⟨[.letRhs], .illScopedAnnotation⟩ := by
  decide

example : errorOf boolSig emptyMatch = some ⟨[], .emptyMatch⟩ := by decide

/-- Without `Bool`, an `if` names an undeclared type. -/
example : errorOf [] ifLt = some ⟨[.matchBranch 0], .unknownType⟩ := by decide

example : errorOf listSig crossTypedMatch = some ⟨[.matchBranch 1], .foreignPattern⟩ := by
  decide

/-- `1 + 'c'`: the function `(+) 1 : Int -> Int` against `Char -> ?1`. -/
example : errorOf boolSig (.app (.app (.primOp .intAdd) one) (.lit (.char 'c'))) =
    some ⟨[], .mismatch (.arrow (.prim .char) (.var 1))
      (.arrow (.prim .int) (.prim .int)) (.clash (.prim .int) (.prim .char))⟩ := by
  decide

/-- `if 1 then True else False`: the scrutinee is at fault. -/
example : errorOf listSig ifInt =
    some ⟨[.matchScrutinee], .mismatch (.con 0) (.prim .int)
      (.clash (.prim .int) (.con 0))⟩ := by
  decide

/-- `fix f => fun x => f f`: the occurs check, at the inner application. -/
example : errorOf boolSig (.fix none (.lambda none (.app (.var 1) (.var 1)))) =
    some ⟨[.fixBody, .lambdaBody], .mismatch (.arrow (.var 0) (.var 2)) (.var 0)
      (.occurs 0 (.arrow (.var 0) (.var 2)))⟩ := by
  decide

/-- The rigid `a` cannot escape into the outer `x`'s unknown type. -/
example : errorOf boolSig skolemEscape =
    some ⟨[.lambdaBody], .mismatch (.rigid 0) (.var 0) (.escape 0 (.rigid 0))⟩ := by
  decide

/-- The hole `h` of `forall a. h -> a -> a` could be `a` or `Bool`. -/
example : errorOf boolSig ambiguous = some ⟨[], .ambiguousSignature ["h"]⟩ := by decide

/-- `fun x => x`: the program's type is not determined. -/
example : errorOf [] (.lambda none (.var 0)) =
    some ⟨[], .undeterminedType (.arrow (.var 0) (.var 0))⟩ := by
  decide

/-- `let f : _ -> Int = fun x => 1 in 0`: the annotation's hole is not
determined. -/
example : errorOf boolSig (.letIn (some monoHoleScheme) (.lambda none one) (.lit (.int 0))) =
    some ⟨[], .undeterminedAnnotation (.arrow (.var 0) (.prim .int))⟩ := by
  decide

/-- A rejected program is not run. -/
example : (match evaluate boolSig emptyMatch 10 with
    | .error error => some error
    | .ok _ => none) = some (.rejected ⟨[], .emptyMatch⟩) := by
  decide

/-! ## Existential constructors

`Pack a = MkPack {s} s (s -> a)`: a value of some hidden type `s`, with a way
to turn it into an `a`. A match on `MkPack` sees `s` as a fresh rigid type
variable, and the match's result type may not mention it. -/

/-- `Pack` as declaration 1 after `Bool`. -/
def packSig : Signature := [boolDecl, ⟨1, [⟨1, [.bvar 1, .arrow (.bvar 1) (.bvar 0)]⟩]⟩]

/-- `MkPack : forall a s. s -> (s -> a) -> Pack a`. -/
example : packSig.ctorScheme ⟨1, 0⟩ =
    some ⟨2, .arrow (.bvar 1) (.arrow (.arrow (.bvar 1) (.bvar 0)) (.app (.con 1) (.bvar 0)))⟩ := by
  decide

def mkPack : Expr A := .ctor ⟨1, 0⟩

/-- A `Pack Int` hiding a `Bool`:
`MkPack True (fun b => match b with True => 1 | False => 0)`. -/
def packedBool : Source :=
  .app (.app mkPack trueExpr)
    (.lambda none (.match (.var 0) [(⟨0, 0⟩, one), (⟨0, 1⟩, .lit (.int 0))]))

/-- `match packedBool with MkPack s f => f s`: applying the function to the
hidden value is fine. -/
def unpackApply : Source :=
  .match packedBool [(⟨1, 0⟩, .lambda none (.lambda none (.app (.var 0) (.var 1))))]

#guard tyOf packSig unpackApply = some int
#guard evalOf packSig unpackApply = some (.lit (.int 1))
-- Inside the branch, the hidden type is the rigid level 0.
#guard (infer packSig unpackApply).toOption.map (·.elaboration) = some
  (.match (.app (.app mkPack trueExpr)
      (.lambda (some boolTy) (.match (.var 0) [(⟨0, 0⟩, .lit (.int 1)), (⟨0, 1⟩, .lit (.int 0))])))
    [(⟨1, 0⟩, .lambda (some (.rigid 0)) (.lambda (some (.arrow (.rigid 0) int))
      (.app (.var 0) (.var 1))))])

/-- The path and unification failure of a rejected program's mismatch. -/
def mismatchCause (sig : Signature) (src : Source) : Option (List ExprStep × UnifyError) :=
  match errorOf sig src with
  | some ⟨path, .mismatch _ _ cause⟩ => some (path, cause)
  | _ => none

/-- `match packedBool with MkPack s f => s`: returning the hidden value would
let its type escape. The match's result type is `?7`, at level 0. -/
def unpackEscape : Source :=
  .match packedBool [(⟨1, 0⟩, .lambda none (.lambda none (.var 1)))]

#guard mismatchCause packSig unpackEscape = some ([.matchBranch 0], .escape 7 (.rigid 0))

/-- `(fun y => match packedBool with MkPack s f => f y) True`: the branch
would need the outer `y : ?0` to have the hidden type. -/
def unpackLeak : Source :=
  .app (.lambda none
    (.match packedBool [(⟨1, 0⟩, .lambda none (.lambda none (.app (.var 0) (.var 2))))]))
    trueExpr

#guard mismatchCause packSig unpackLeak =
  some ([.appFunction, .lambdaBody, .matchBranch 0], .escape 0 (.rigid 0))

end EPL.Tests
