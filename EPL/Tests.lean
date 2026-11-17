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
  [boolDecl, ⟨1, [[], [.bvar 0, .app (.con 1) (.bvar 0)]]⟩]

def trueExpr : Expr A := .const (.ctor 0 0)

def falseExpr : Expr A := .const (.ctor 0 1)

def one : Source := .lit (.int 1)

/-- Type of an accepted program. -/
def tyOf (sig : Signature) (src : Source) : Option SemTy := (infer sig src).map (·.ty)

/-- Evaluate an accepted program for at most 1000 steps. -/
def evalOf (sig : Signature) (src : Source) : Option RuntimeExpr :=
  (infer sig src).map fun _ => Eval.run sig 1000 src.erase

/-! ## A first tour -/

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
    .fix (some (.arrow (.app (.con 1) (.var "a")) int.lift))
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

/-! ## Unification -/

/-- `?0` and `?1` both live at level 1, so `?1` may be solved to rigid 0. -/
def arrowExample : Option MStore :=
  MStore.unify [⟨1, none⟩, ⟨1, none⟩]
    (.arrow (.var 0) (.rigid 0))
    (.arrow (.prim .int) (.var 1))

example : arrowExample = some [⟨1, some (.prim .int)⟩, ⟨1, some (.rigid 0)⟩] := by
  decide

/-- Solving `?0 := ?1` and then `?1 := Int` rewrites the earlier entry, so the
store stays normalized. -/
example :
    MStore.unify [⟨0, none⟩, ⟨0, none⟩]
        (.arrow (.var 0) (.var 1))
        (.arrow (.var 1) (.prim .int)) =
      some [⟨0, some (.prim .int)⟩, ⟨0, some (.prim .int)⟩] := by
  decide

/-- A level-0 metavariable cannot be solved to rigid 0: it would escape. -/
example : MStore.unify [⟨0, none⟩] (.var 0) (.rigid 0) = none := by
  decide

/-- Binding a level-0 metavariable lowers the metavariables of its solution. -/
example :
    MStore.unify [⟨0, none⟩, ⟨1, none⟩] (.var 0) (.arrow (.var 1) (.prim .int)) =
      some [⟨0, some (.arrow (.var 1) (.prim .int))⟩, ⟨0, none⟩] := by
  decide

example : MStore.unify [] (.rigid 0) (.prim .int) = none := by
  decide

/-- Type applications decompose: `List ?0 ~ List Int` solves `?0 := Int`. -/
example :
    MStore.unify [⟨0, none⟩] (.app (.con 0) (.var 0)) (.app (.con 0) (.prim .int)) =
      some [⟨0, some (.prim .int)⟩] := by
  decide

/-- Distinct type constructors do not unify, even at the same arguments. -/
example :
    MStore.unify [] (.app (.con 0) (.prim .int)) (.app (.con 1) (.prim .int)) = none := by
  decide

/-- A higher-kinded unknown may be solved to a type constructor. -/
example :
    MStore.unify [⟨0, none⟩] (.app (.var 0) (.prim .int)) (.app (.con 3) (.prim .int)) =
      some [⟨0, some (.con 3)⟩] := by
  decide

example : MStore.unify [⟨0, none⟩] (.var 0) (.arrow (.var 0) (.prim .int)) = none := by
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

example : (infer boolSig inferredIntLambda).map (·.ty) =
    some (.arrow int int) := by
  decide

example : (infer boolSig explicitPolyProgram).map (·.ty) = some boolTy := by
  decide

example : (infer boolSig implicitPolyProgram).map (·.ty) = none := by
  decide

example : (infer boolSig identityRhs).map (·.ty) = none := by
  decide

def deadAmbiguousLambda : Source :=
  .letIn none identityRhs (.lit .unit)

example : (infer boolSig deadAmbiguousLambda).map (·.ty) = none := by
  decide

def deadAmbiguousLambdaInScheme : Source :=
  .letIn (some ⟨0, .prim .unit⟩)
    deadAmbiguousLambda
    (.lit .unit)

example : (infer boolSig deadAmbiguousLambdaInScheme).map (·.ty) = none := by
  decide

example : (infer boolSig integerLoop).map (·.ty) =
    some (.arrow int int) := by
  decide

def skolemEscape : Source :=
  .lambda none
    (.letIn (some ⟨1, .rigid 0⟩)
      (.var 0)
      (.lit .unit))

example : (infer boolSig skolemEscape).map (·.ty) = none := by
  decide

def outerConstraint : Source :=
  .lambda none
    (.letIn (some ⟨0, int⟩)
      (.var 0)
      (.var 1))

example : (infer boolSig outerConstraint).map (·.ty) =
    some (.arrow int int) := by
  decide

def solvedSignatureHole : Source :=
  .letIn (some ⟨1, .var "_"⟩)
    (.lit (.int 5))
    (.var 0)

example : (infer boolSig solvedSignatureHole).map (·.ty) = some int := by
  decide

def namedIdentityAnnotation : PolyAnn Template :=
  ⟨1, .arrow (.var "domain") (.rigid 0)⟩

def namedIdentity : Source :=
  .letIn (some namedIdentityAnnotation)
    identityRhs
    (.app (.var 0) (.lit (.int 5)))

example : (infer boolSig namedIdentity).map (·.ty) = some int := by
  decide

def hiddenBadBoundAnnotation : Source :=
  .letIn none
    (.lambda (some (.bvar 0)) (.lit .unit))
    (.lit .unit)

def hiddenBadRigidAnnotation : Source :=
  .letIn none
    (.lambda (some (.rigid 0)) (.lit .unit))
    (.lit .unit)

example : (infer boolSig hiddenBadBoundAnnotation).map (·.ty) = none := by decide
example : (infer boolSig hiddenBadRigidAnnotation).map (·.ty) = none := by decide

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

example : (infer boolSig regionUnknownEscapes).map (·.ty) =
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

example : (infer boolSig deferredParameter).map (·.ty) =
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

example : (infer boolSig deferredSchemeHole).map (·.ty) =
    some (.arrow (.arrow int int) int) := by
  decide

/-- The completed scheme is recorded in the elaboration. -/
example : (infer boolSig deferredSchemeHole).map (·.elaboration) =
    some (.lambda (some (.arrow int int))
      (.letIn (some ⟨1, .arrow int (.arrow (.rigid 0) (.rigid 0))⟩)
        (.lambda (some int) (.lambda (some (.rigid 0))
          (.letIn none (.app (.var 2) (.var 1)) (.var 1))))
        (.app (.app (.primOp .intAdd) (.app (.var 1) (.lit (.int 1))))
          (.lit (.int 1))))) := by
  decide

/-- A scheme hole that nothing determines is still rejected.

`fun (x : Int) => let f : forall a. _ -> a -> a = fun z y => y in 0` -/
example : infer boolSig (.lambda (some int)
    (.letIn (some holeFirstScheme) (.lambda none (.lambda none (.var 0)))
      (.lit (.int 0)))) = none := by
  decide

/-- A hole that only uses could determine is rejected: `_ := a` and
`_ := Bool` both elaborate.

`let f : forall a. _ -> a -> a = fun z y => y in f true true` -/
example : infer boolSig (.letIn (some holeFirstScheme) (.lambda none (.lambda none (.var 0)))
    (.app (.app (.var 0) trueExpr) trueExpr)) = none := by
  decide

/-- Holes are completed from the definition and its context, not from uses:
this is rejected even though only `_ := Int` would typecheck.

`let f : forall a. _ -> a -> a = fun z y => y in f 1 true` -/
example : infer boolSig (.letIn (some holeFirstScheme) (.lambda none (.lambda none (.var 0)))
    (.app (.app (.var 0) (.lit (.int 1))) trueExpr)) = none := by
  decide

/-- A hole fixed to the scheme's own binder by its definition.

`let f : forall a. _ -> a -> a = fun (z : a) y => y in 0` -/
example : (infer boolSig (.letIn (some holeFirstScheme)
    (.lambda (some (.rigid 0)) (.lambda none (.var 0)))
    (.lit (.int 0)))).map (·.elaboration) =
    some (.letIn (some ⟨1, .arrow (.rigid 0) (.arrow (.rigid 0) (.rigid 0))⟩)
      (.lambda (some (.rigid 0)) (.lambda (some (.rigid 0)) (.var 0)))
      (.lit (.int 0))) := by
  decide

/-- A rigid variable may not escape through an outer unknown.

`fun x => let f : forall a. a -> a = fun y => (let _ = x y in y) in 0` -/
example : infer boolSig (.lambda none (.letIn (some polyIdentityAnnotation)
    (.lambda none (.letIn none (.app (.var 1) (.var 0)) (.var 1)))
    (.lit (.int 0)))) = none := by
  decide

/-- `_ -> Int`: a signature without binders is an ordinary partial annotation. -/
def monoHoleScheme : PolyAnn Template :=
  ⟨0, .arrow (.var "_") int⟩

/-- Its hole may be determined by a later use.

`let f : _ -> Int = fun x => 1 in f 3` -/
example : (infer boolSig (.letIn (some monoHoleScheme) (.lambda none (.lit (.int 1)))
    (.app (.var 0) (.lit (.int 3))))).map (·.ty) = some int := by
  decide

/-- If nothing determines it, the program is ambiguous.

`let f : _ -> Int = fun x => 1 in 0` -/
example : infer boolSig (.letIn (some monoHoleScheme) (.lambda none (.lit (.int 1)))
    (.lit (.int 0))) = none := by
  decide

def inferredHoleLambda : Source :=
  .lambda (some (.var "_"))
    (.app
      (.app (.primOp .intAdd) (.var 0))
      (.lit (.int 1)))

example : (infer boolSig inferredHoleLambda).map (·.ty) =
    some (.arrow int int) := by
  decide

def ambiguousHoleLambda : Source :=
  .lambda (some (.var "_")) (.var 0)

example : (infer boolSig ambiguousHoleLambda).map (·.ty) = none := by
  decide

def partlyInferredPolyAnnotation : PolyAnn Template :=
  ⟨1, .arrow (.var "_") (.rigid 0)⟩

def partlyInferredPolyProgram : Source :=
  .letIn (some partlyInferredPolyAnnotation) identityRhs
    (.app (.var 0) trueExpr)

example : (infer boolSig partlyInferredPolyProgram).map (·.ty) = some boolTy := by
  decide

def falsePolyAnnotation : PolyAnn Template :=
  ⟨1, .arrow (.rigid 0) int⟩

def falsePolyProgram : Source :=
  .letIn (some falsePolyAnnotation) identityRhs
    (.lit .unit)

example : (infer boolSig falsePolyProgram).map (·.ty) = none := by
  decide

def inferredIntegerFix : Source :=
  .fix none
    (.app
      (.app (.primOp .intAdd) (.var 0))
      (.lit (.int 1)))

example : (infer boolSig inferredIntegerFix).map (·.ty) = some int := by
  decide

def incoherentNamedHole : Source :=
  .app
    (.lambda
      (some (.arrow (.var "shared") (.var "shared")))
      (.var 0))
    (.lambda (some int) trueExpr)

example : (infer boolSig incoherentNamedHole).map (·.ty) = none := by decide

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

example : (infer boolSig independentNamedHoles).map (·.ty) =
    some (.arrow boolTy int) := by
  decide

def reuseAfterPolyCheck : Source :=
  .letIn (some polyIdentityAnnotation) identityRhs inferredIntLambda

example : (infer boolSig reuseAfterPolyCheck).map (·.ty) =
    some (.arrow int int) := by
  decide

/-! ## Inference soundness canaries

These declarative derivations are obtained solely from a successful run of the
public inference function. -/

example : ∃ elaboration, Typing boolSig 0 [] inferredIntLambda elaboration
    (.arrow int int) :=
  ⟨_, infer_typing (by
    decide : infer boolSig inferredIntLambda = some
      ⟨.lambda (some int) (.app (.app (.primOp .intAdd) (.var 0)) (.lit (.int 1))),
        .arrow int int⟩)⟩

example : ∃ elaboration, Typing boolSig 0 [] explicitPolyProgram elaboration boolTy :=
  ⟨_, infer_typing (by
    decide : infer boolSig explicitPolyProgram = some
      ⟨.letIn (some ⟨1, .arrow (.rigid 0) (.rigid 0)⟩)
          (.lambda (some (.rigid 0)) (.var 0))
          (.letIn none (.app (.var 0) (.lit (.int 5))) (.app (.var 1) trueExpr)),
        boolTy⟩)⟩

example : ∃ elaboration, Typing boolSig 0 [] partlyInferredPolyProgram elaboration boolTy :=
  ⟨_, infer_typing (by
    decide : infer boolSig partlyInferredPolyProgram = some
      ⟨.letIn (some ⟨1, .arrow (.rigid 0) (.rigid 0)⟩)
          (.lambda (some (.rigid 0)) (.var 0))
          (.app (.var 0) trueExpr),
        boolTy⟩)⟩

example : ∃ elaboration, Typing boolSig 0 [] inferredIntegerFix elaboration int :=
  ⟨_, infer_typing (by
    decide : infer boolSig inferredIntegerFix = some
      ⟨.fix (some int)
          (.app (.app (.primOp .intAdd) (.var 0)) (.lit (.int 1))),
        int⟩)⟩

example : ∃ elaboration, Typing boolSig 0 [] integerLoop elaboration (.arrow int int) :=
  ⟨_, infer_typing (by
    decide : infer boolSig integerLoop = some
      ⟨.fix (some (.arrow int int)) (.lambda (some int) (.app (.var 1) (.var 0))),
        .arrow int int⟩)⟩

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
  (evaluate boolSig input fuel).bind (·.2.value?)

#guard finalValue incrementApplied 10 = some (.lit (.int 42))
#guard finalValue letAdd 10 = some (.lit (.int 42))
#guard finalValue explicitPolyProgram 50 = some trueExpr

-- Divergent programs are well-typed but never finish.
#guard finalValue (.app integerLoop (.lit (.int 0))) 100 = none
#guard finalValue inferredIntegerFix 100 = none

-- Rejected programs never run.
#guard (evaluate boolSig deadAmbiguousLambda 10).isNone

/-! ## Data types -/

/-- A field mentioning an undeclared parameter makes its declaration ill
formed, so none of that declaration's constants has a scheme. In particular
the eliminator, whose scheme has one more binder, does not read the field's
`bvar 0` as its result variable. Other declarations are unaffected. -/
def illScopedSig : Signature := [boolDecl, ⟨0, [[.bvar 0]]⟩]

example : illScopedSig.schemeOf (.ctor 1 0) = none := by decide
example : illScopedSig.schemeOf (.elim 1) = none := by decide
example : (infer illScopedSig trueExpr).map (·.ty) = some boolTy := by decide
example : (listSig.schemeOf (.elim 1)).isSome := by decide

/-- `if c then a else b` as an application of `Bool`'s eliminator. -/
def ifThen (c a b : Source) : Source :=
  .app (.app (.app (.const (.elim 0)) c) (.lambda none a)) (.lambda none b)

def nil : Source := .const (.ctor 1 0)

def cons (h t : Source) : Source := .app (.app (.const (.ctor 1 1)) h) t

def listTy : Ty V := .app (.con 1) int

/-- `if False then 1 else 2 : Int`, evaluating to `2`. -/
def ifFalse : Source :=
  ifThen falseExpr (.lit (.int 1)) (.lit (.int 2))

example : (infer listSig ifFalse).map (·.ty) = some int := by
  decide

#guard ((evaluate listSig ifFalse 50).bind (·.2.value?)) =
  some (.lit (.int 2))

/-- `match Cons 5 Nil with Nil => 0 | Cons x xs => x : Int`, evaluating to
`5`, and annotating `x : Int` and `xs : List Int`. -/
def matchCons : Source :=
  .app (.app (.app (.const (.elim 1))
      (cons (.lit (.int 5)) nil))
    (.lambda none (.lit (.int 0))))
    (.lambda none (.lambda none (.lambda none (.var 1))))

example : (infer listSig matchCons).map (·.ty) = some int := by
  decide

example : (infer listSig matchCons).map (·.elaboration) =
    some (.app (.app (.app (.const (.elim 1))
        (.app (.app (.const (.ctor 1 1)) (.lit (.int 5)))
          (.const (.ctor 1 0))))
      (.lambda (some (.prim .unit)) (.lit (.int 0))))
      (.lambda (some (.prim .unit))
        (.lambda (some int) (.lambda (some listTy) (.var 1))))) := by
  decide

#guard ((evaluate listSig matchCons 50).bind (·.2.value?)) =
  some (.lit (.int 5))

/-- `if 1 then True else False` is rejected: the scrutinee must be `Bool`. -/
def ifInt : Source :=
  ifThen (.lit (.int 1)) trueExpr falseExpr

example : infer listSig ifInt = none := by
  decide

/-- A partial constructor application is a value of function type. -/
def partialCons : Source :=
  .app (.const (.ctor 1 1)) (.lit (.int 1))

example : (infer listSig partialCons).map (·.ty) =
    some (.arrow listTy listTy) := by
  decide

example : Eval.Value listSig partialCons.erase :=
  Eval.Value.const (c := .ctor 1 1) (args := [.lit (.int 1)]) (arity := 2) rfl
    (by decide) (by decide) (by
      intro arg h
      rcases List.mem_singleton.mp h with rfl
      exact .lit)

#guard ((evaluate listSig partialCons 10).bind (·.2.value?)) =
  some (.app (.const (.ctor 1 1)) (.lit (.int 1)))

/-- Recursive list length via `fix`, over `listSig`. -/
def listInt : Source :=
  cons (.lit (.int 1))
    (cons (.lit (.int 2)) (cons (.lit (.int 3)) nil))

def listNilBranch : Source :=
  .lambda none (.lit (.int 0))

def listConsBranch : Source :=
  .lambda none (.lambda none (.lambda none
    (.app (.app (.primOp .intAdd) (.lit (.int 1)))
      (.app (.var 4) (.var 0)))))

def listMatch (scrutinee : Source) : Source :=
  .app (.app (.app (.const (.elim 1)) scrutinee) listNilBranch)
    listConsBranch

def listLength : Source :=
  .fix (some (.arrow listTy int))
    (.lambda (some listTy) (listMatch (.var 0)))

example : (infer listSig (.app listLength listInt)).map (·.ty) = some int := by
  decide

#guard ((evaluate listSig (.app listLength listInt) 200).bind (·.2.value?)) =
  some (.lit (.int 3))

/-! ## Primitive operations -/

def intSubExpr : Source :=
  .app (.app (.primOp .intSub) (.lit (.int 1))) (.lit (.int 5))

example : (infer boolSig intSubExpr).map (·.ty) = some int := by
  decide

#guard ((evaluate boolSig intSubExpr 50).bind (·.2.value?)) =
  some (.lit (.int (-4)))

def intLtExpr (left right : Int) : Source :=
  .app (.app (.primOp .intLt) (.lit (.int left))) (.lit (.int right))

def charIf : Source :=
  ifThen (intLtExpr 1 2) (.lit (.char 'y')) (.lit (.char 'n'))

def charIfFalse : Source :=
  ifThen (intLtExpr 2 1) (.lit (.char 'y')) (.lit (.char 'n'))

example : (infer boolSig charIf).map (·.ty) = some charTy := by
  decide

#guard ((evaluate boolSig charIf 50).bind (·.2.value?)) =
  some (.lit (.char 'y'))

#guard ((evaluate boolSig charIfFalse 50).bind (·.2.value?)) =
  some (.lit (.char 'n'))

def charLtExpr : Source :=
  .app (.app (.primOp .charLt) (.lit (.char 'a'))) (.lit (.char 'b'))

example : (infer boolSig charLtExpr).map (·.ty) = some boolTy := by
  decide

#guard ((evaluate boolSig charLtExpr 50).bind (·.2.value?)) =
  some (Eval.boolValue true)

/-- Declaration 0 is `List`-shaped rather than `True | False`. -/
def listShapedSig : Signature :=
  [⟨1, [[], [.bvar 0, .app (.con 0) (.bvar 0)]]⟩]

example : infer [] (intLtExpr 1 2) = none := by
  decide

example : infer listShapedSig (intLtExpr 1 2) = none := by
  decide

example : infer boolSig (.app (.app (.primOp .intAdd) (.lit (.int 1)))
    (.lit (.char 'c'))) = none := by
  decide

def partialIntLt : Source :=
  .app (.primOp .intLt) (.lit (.int 1))

example : (infer boolSig partialIntLt).map (·.ty) =
    some (.arrow int boolTy) := by
  decide

example : Eval.Value boolSig partialIntLt.erase :=
  Eval.Value.primOpPartial (op := .intLt) .lit

/-- `fix f : Int -> Int. fun n => if n < 1 then 0 else n + f (n - 1)`. -/
def primRecursive : Source :=
  .app
    (.fix (some (.arrow int int))
      (.lambda (some int)
        (ifThen
          (.app (.app (.primOp .intLt) (.var 0)) (.lit (.int 1)))
          (.lit (.int 0))
          (.app (.app (.primOp .intAdd) (.var 1))
            (.app (.var 2)
              (.app (.app (.primOp .intSub) (.var 1)) (.lit (.int 1))))))))
    (.lit (.int 4))

example : (infer boolSig primRecursive).map (·.ty) = some int := by
  decide

#guard ((evaluate boolSig primRecursive 500).bind (·.2.value?)) =
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
    (fields : List SemTy) (args : List SemTy) (p : PrimTy) :
    (decl.ctorScheme type fields).inst args ≠ .prim p := by
  unfold DataDecl.ctorScheme Scheme.inst DataDecl.selfTy
  rw [instantiate_arrows, instantiate_apps]
  apply arrows_ne_prim
  intro q
  exact apps_ne_prim (.con type) _ q (by intro r h; cases h)

/-- A constructor's scheme is its declaration's `ctorScheme`. -/
private theorem schemeOf_ctor_eq {sig : Signature} {type index : Nat}
    {scheme : Scheme Empty} (found : sig.schemeOf (.ctor type index) = some scheme) :
    ∃ (decl : DataDecl) (fields : List SemTy),
      sig[type]? = some decl ∧ decl.ctors[index]? = some fields ∧
        scheme = decl.ctorScheme type fields := by
  cases hdecl : sig[type]? with
  | none => simp [Signature.schemeOf, hdecl] at found
  | some decl =>
      cases hfields : decl.ctors[index]? with
      | none => simp [Signature.schemeOf, hdecl, hfields] at found
      | some fields =>
          have hwf : decl.WF := by
            by_contra h
            simp [Signature.schemeOf, hdecl, h] at found
          have hsome : sig.schemeOf (.ctor type index) =
                some (decl.ctorScheme type fields) := by
            simp [Signature.schemeOf, hdecl, hfields, hwf]
          rw [hsome] at found
          exact ⟨decl, fields, rfl, hfields, (Option.some.inj found).symm⟩

/-- A constructor constant never has a primitive type. -/
private theorem const_ctor_ne_prim {sig : Signature} {k : Nat} {ctx : Ctx Empty}
    {type index : Nat} {elaboration : Elab} {p : PrimTy}
    (typing : Typing sig k ctx (.const (.ctor type index)) elaboration (.prim p)) :
    False := by
  cases typing with
  | const found inst =>
      obtain ⟨decl, fields, _, _, rfl⟩ := schemeOf_ctor_eq found
      obtain ⟨args, _, _, hinst⟩ := inst
      exact ctorScheme_inst_ne_prim decl type fields args p hinst

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
                      exact const_ctor_ne_prim finalArgumentTyping

end EPL.Tests
