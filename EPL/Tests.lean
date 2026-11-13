import EPL.Examples
import EPL.Inference
import EPL.Properties.Unification
import EPL.Properties.InferenceState
import EPL.Properties.InferenceSound
import EPL.Properties.EndToEnd

namespace EPL.UnificationTests

/-- `?0` and `?1` both live at level 1, so `?1` may be solved to rigid 0. -/
def arrowExample : Option MStore :=
  MStore.unify [⟨1, none⟩, ⟨1, none⟩]
    (.arrow (.mvar 0) (.rigid 0))
    (.arrow (.prim .int) (.mvar 1))

example : arrowExample = some [⟨1, some (.prim .int)⟩, ⟨1, some (.rigid 0)⟩] := by
  decide

/-- Solving `?0 := ?1` and then `?1 := Int` rewrites the earlier entry, so the
store stays normalized. -/
example :
    MStore.unify [⟨0, none⟩, ⟨0, none⟩]
        (.arrow (.mvar 0) (.mvar 1))
        (.arrow (.mvar 1) (.prim .int)) =
      some [⟨0, some (.prim .int)⟩, ⟨0, some (.prim .int)⟩] := by
  decide

/-- A level-0 metavariable cannot be solved to rigid 0: it would escape. -/
example : MStore.unify [⟨0, none⟩] (.mvar 0) (.rigid 0) = none := by
  decide

/-- Binding a level-0 metavariable lowers the metavariables of its solution. -/
example :
    MStore.unify [⟨0, none⟩, ⟨1, none⟩] (.mvar 0) (.arrow (.mvar 1) (.prim .int)) =
      some [⟨0, some (.arrow (.mvar 1) (.prim .int))⟩, ⟨0, none⟩] := by
  decide

example : MStore.unify [] (.rigid 0) (.prim .int) = none := by
  decide

/-- Type applications decompose: `List ?0 ~ List Int` solves `?0 := Int`. -/
example :
    MStore.unify [⟨0, none⟩] (.app (.con 0) (.mvar 0)) (.app (.con 0) (.prim .int)) =
      some [⟨0, some (.prim .int)⟩] := by
  decide

/-- Distinct type constructors do not unify, even at the same arguments. -/
example :
    MStore.unify [] (.app (.con 0) (.prim .int)) (.app (.con 1) (.prim .int)) = none := by
  decide

/-- A higher-kinded unknown may be solved to a type constructor. -/
example :
    MStore.unify [⟨0, none⟩] (.app (.mvar 0) (.prim .int)) (.app (.con 3) (.prim .int)) =
      some [⟨0, some (.con 3)⟩] := by
  decide

example : MStore.unify [⟨0, none⟩] (.mvar 0) (.arrow (.mvar 0) (.prim .int)) = none := by
  decide

end EPL.UnificationTests

namespace EPL.AnnotationAllocationTests

def repeated : Template :=
  .arrow (.named "a") (.named "a")

def independent : Template :=
  .arrow (.named "a") (.arrow .hole (.named "b"))

example : (repeated.allocate 10).ty = .arrow (.mvar 10) (.mvar 10) := by
  decide

example : (repeated.allocate 10).next = 11 := by
  decide

example : (independent.allocate 20).ty =
    .arrow (.mvar 20) (.arrow (.mvar 22) (.mvar 21)) := by
  decide

example : (independent.allocate 20).next = 23 := by
  decide

end EPL.AnnotationAllocationTests

namespace EPL.InferenceTests

open EPL EPL.Examples

example : (infer boolSig inferredIntLambda).map (·.ty) =
    some (.arrow intTy intTy) := by
  decide

example : (infer boolSig explicitPolyProgram).map (·.ty) = some boolTy := by
  decide

example : (infer boolSig implicitPolyProgram).map (·.ty) = none := by
  decide

example : (infer boolSig identityRhs).map (·.ty) = none := by
  decide

def deadAmbiguousLambda : Source :=
  .letIn none identityRhs (.primLit .unit)

example : (infer boolSig deadAmbiguousLambda).map (·.ty) = none := by
  decide

def deadAmbiguousLambdaInScheme : Source :=
  .letIn (some ⟨0, .fixed (.prim .unit)⟩)
    deadAmbiguousLambda
    (.primLit .unit)

example : (infer boolSig deadAmbiguousLambdaInScheme).map (·.ty) = none := by
  decide

example : (infer boolSig integerLoop).map (·.ty) =
    some (.arrow intTy intTy) := by
  decide

def skolemEscape : Source :=
  .lambda none
    (.letIn (some ⟨1, .fixed (.bvar 0)⟩)
      (.var 0)
      (.primLit .unit))

example : (infer boolSig skolemEscape).map (·.ty) = none := by
  decide

def outerConstraint : Source :=
  .lambda none
    (.letIn (some ⟨0, .fixed intTy⟩)
      (.var 0)
      (.var 1))

example : (infer boolSig outerConstraint).map (·.ty) =
    some (.arrow intTy intTy) := by
  decide

def solvedSignatureHole : Source :=
  .letIn (some ⟨1, .hole⟩)
    (.primLit (.int 5))
    (.var 0)

example : (infer boolSig solvedSignatureHole).map (·.ty) = some intTy := by
  decide

def namedIdentityAnnotation : Scheme Template :=
  ⟨1, .arrow (.named "domain") (.fixed (.bvar 0))⟩

def namedIdentity : Source :=
  .letIn (some namedIdentityAnnotation)
    identityRhs
    (.app (.var 0) (.primLit (.int 5)))

example : (infer boolSig namedIdentity).map (·.ty) = some intTy := by
  decide

/-- Authored annotations cannot forge or capture inference metavariables. -/
def forgedMetaAnnotation : Source :=
  .lambda (some (.fixed (.mvar 0)))
    (.app
      (.app (.primOp .intAdd) (.var 0))
      (.primLit (.int 1)))

example : (infer boolSig forgedMetaAnnotation).map (·.ty) = none := by
  decide

def hiddenBadBoundAnnotation : Source :=
  .letIn none
    (.lambda (some (.fixed (.bvar 0))) (.primLit .unit))
    (.primLit .unit)

def hiddenBadRigidAnnotation : Source :=
  .letIn none
    (.lambda (some (.fixed (.rigid 0))) (.primLit .unit))
    (.primLit .unit)

example : (infer boolSig hiddenBadBoundAnnotation).map (·.ty) = none := by decide
example : (infer boolSig hiddenBadRigidAnnotation).map (·.ty) = none := by decide

/-- An unknown created while checking an explicit scheme may survive it: here
`x : Int -> ?r` is constrained inside `f`'s region, and `?r` is only
determined (as `Int`) after leaving it.

`fun x => let f : forall a. a -> a = (let _ = x 1 in fun y => y) in x 1 + 1` -/
def regionUnknownEscapes : Source :=
  .lambda none
    (.letIn (some polyIdentityAnnotation)
      (.letIn none (.app (.var 0) (.primLit (.int 1))) (.lambda none (.var 0)))
      (.app (.app (.primOp .intAdd) (.app (.var 1) (.primLit (.int 1))))
        (.primLit (.int 1))))

example : (infer boolSig regionUnknownEscapes).map (·.ty) =
    some (.arrow (.arrow intTy intTy) intTy) := by
  decide

/-- `x 1 + 1`, with `x` at de Bruijn index 1. -/
def applyXPlusOne : Source :=
  .app (.app (.primOp .intAdd) (.app (.var 1) (.primLit (.int 1))))
    (.primLit (.int 1))

/-- An implicit type inside an explicit scheme's region may be determined only
after the region: `z`'s type becomes `Int` through the later `x 1`.

`fun x => let f : forall a. a -> a = (let _ = (fun z => x z) in fun y => y) in x 1 + 1` -/
def deferredParameter : Source :=
  .lambda none (.letIn (some polyIdentityAnnotation)
    (.letIn none (.lambda none (.app (.var 1) (.var 0))) (.lambda none (.var 0)))
    applyXPlusOne)

example : (infer boolSig deferredParameter).map (·.ty) =
    some (.arrow (.arrow intTy intTy) intTy) := by
  decide

/-- `forall a. _ -> a -> a` -/
def holeFirstScheme : Scheme Template :=
  ⟨1, .arrow .hole (.arrow (.fixed (.bvar 0)) (.fixed (.bvar 0)))⟩

/-- A hole in a written scheme may likewise be determined after its region.

`fun x => let f : forall a. _ -> a -> a = fun z y => (let _ = x z in y) in x 1 + 1` -/
def deferredSchemeHole : Source :=
  .lambda none (.letIn (some holeFirstScheme)
    (.lambda none (.lambda none (.letIn none (.app (.var 2) (.var 1)) (.var 1))))
    applyXPlusOne)

example : (infer boolSig deferredSchemeHole).map (·.ty) =
    some (.arrow (.arrow intTy intTy) intTy) := by
  decide

/-- The completed scheme is recorded in the elaboration. -/
example : (infer boolSig deferredSchemeHole).map (·.elaborated) =
    some (.lambda (some (.arrow intTy intTy))
      (.letIn (some ⟨1, .arrow intTy (.arrow (.bvar 0) (.bvar 0))⟩)
        (.lambda (some intTy) (.lambda (some (.rigid 0))
          (.letIn none (.app (.var 2) (.var 1)) (.var 1))))
        (.app (.app (.primOp .intAdd) (.app (.var 1) (.primLit (.int 1))))
          (.primLit (.int 1))))) := by
  decide

/-- A scheme hole that nothing determines is still rejected.

`fun (x : Int) => let f : forall a. _ -> a -> a = fun z y => y in 0` -/
example : infer boolSig (.lambda (some (.fixed intTy))
    (.letIn (some holeFirstScheme) (.lambda none (.lambda none (.var 0)))
      (.primLit (.int 0)))) = none := by
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
    (.app (.app (.var 0) (.primLit (.int 1))) trueExpr)) = none := by
  decide

/-- A hole fixed to the scheme's own binder by its definition.

`let f : forall a. _ -> a -> a = fun (z : a) y => y in 0` -/
example : (infer boolSig (.letIn (some holeFirstScheme)
    (.lambda (some (.fixed (.bvar 0))) (.lambda none (.var 0)))
    (.primLit (.int 0)))).map (·.elaborated) =
    some (.letIn (some ⟨1, .arrow (.bvar 0) (.arrow (.bvar 0) (.bvar 0))⟩)
      (.lambda (some (.rigid 0)) (.lambda (some (.rigid 0)) (.var 0)))
      (.primLit (.int 0))) := by
  decide

/-- A rigid variable may not escape through an outer unknown.

`fun x => let f : forall a. a -> a = fun y => (let _ = x y in y) in 0` -/
example : infer boolSig (.lambda none (.letIn (some polyIdentityAnnotation)
    (.lambda none (.letIn none (.app (.var 1) (.var 0)) (.var 1)))
    (.primLit (.int 0)))) = none := by
  decide

/-- `_ -> Int`: a signature without binders is an ordinary partial annotation. -/
def monoHoleScheme : Scheme Template :=
  ⟨0, .arrow .hole (.fixed intTy)⟩

/-- Its hole may be determined by a later use.

`let f : _ -> Int = fun x => 1 in f 3` -/
example : (infer boolSig (.letIn (some monoHoleScheme) (.lambda none (.primLit (.int 1)))
    (.app (.var 0) (.primLit (.int 3))))).map (·.ty) = some intTy := by
  decide

/-- If nothing determines it, the program is ambiguous.

`let f : _ -> Int = fun x => 1 in 0` -/
example : infer boolSig (.letIn (some monoHoleScheme) (.lambda none (.primLit (.int 1)))
    (.primLit (.int 0))) = none := by
  decide

def inferredHoleLambda : Source :=
  .lambda (some .hole)
    (.app
      (.app (.primOp .intAdd) (.var 0))
      (.primLit (.int 1)))

example : (infer boolSig inferredHoleLambda).map (·.ty) =
    some (.arrow intTy intTy) := by
  decide

def ambiguousHoleLambda : Source :=
  .lambda (some .hole) (.var 0)

example : (infer boolSig ambiguousHoleLambda).map (·.ty) = none := by
  decide

def partlyInferredPolyAnnotation : Scheme Template :=
  ⟨1, .arrow .hole (.fixed (.bvar 0))⟩

def partlyInferredPolyProgram : Source :=
  .letIn (some partlyInferredPolyAnnotation) identityRhs
    (.app (.var 0) trueExpr)

example : (infer boolSig partlyInferredPolyProgram).map (·.ty) = some boolTy := by
  decide

def falsePolyAnnotation : Scheme Template :=
  ⟨1, .arrow (.fixed (.bvar 0)) (.fixed intTy)⟩

def falsePolyProgram : Source :=
  .letIn (some falsePolyAnnotation) identityRhs
    (.primLit .unit)

example : (infer boolSig falsePolyProgram).map (·.ty) = none := by
  decide

def inferredIntegerFix : Source :=
  .fix .hole
    (.app
      (.app (.primOp .intAdd) (.var 0))
      (.primLit (.int 1)))

example : (infer boolSig inferredIntegerFix).map (·.ty) = some intTy := by
  decide

def incoherentNamedHole : Source :=
  .app
    (.lambda
      (some (.arrow (.named "shared") (.named "shared")))
      (.var 0))
    (.lambda (some (.fixed intTy)) trueExpr)

example : (infer boolSig incoherentNamedHole).map (·.ty) = none := by decide

def namedIntegerLambda : Source :=
  .lambda (some (.named "local"))
    (.app
      (.app (.primOp .intAdd) (.var 0))
      (.primLit (.int 1)))

def namedBooleanLambda : Source :=
  .lambda (some (.named "local"))
    (.app
      (.lambda (some (.fixed boolTy)) (.primLit (.int 1)))
      (.var 0))

def independentNamedHoles : Source :=
  .letIn none namedIntegerLambda namedBooleanLambda

example : (infer boolSig independentNamedHoles).map (·.ty) =
    some (.arrow boolTy intTy) := by
  decide

def reuseAfterPolyCheck : Source :=
  .letIn (some polyIdentityAnnotation) identityRhs inferredIntLambda

example : (infer boolSig reuseAfterPolyCheck).map (·.ty) =
    some (.arrow intTy intTy) := by
  decide

end EPL.InferenceTests

namespace EPL.InferenceSoundTests

open EPL EPL.Examples EPL.InferenceTests

/-- End-to-end canaries: these declarative derivations are obtained solely
from successful execution of the public inference function. -/
example : Typing boolSig 0 [] inferredIntLambda (.arrow intTy intTy) := by
  exact infer_typing_of_ty (by decide)

example : Typing boolSig 0 [] explicitPolyProgram boolTy := by
  exact infer_typing_of_ty (by decide)

example : Typing boolSig 0 [] partlyInferredPolyProgram boolTy := by
  exact infer_typing_of_ty (by decide)

example : Typing boolSig 0 [] inferredIntegerFix intTy := by
  exact infer_typing_of_ty (by decide)

end EPL.InferenceSoundTests

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
  (evaluate boolSig input fuel).bind (·.2.value?)

#guard finalValue incrementApplied 10 = some (.primLit (.int 42))
#guard finalValue letAdd 10 = some (.primLit (.int 42))
#guard finalValue explicitPolyProgram 50 = some trueExpr

-- Divergent programs are well-typed but never finish.
#guard finalValue (.app integerLoop (.primLit (.int 0))) 100 = none
#guard finalValue inferredIntegerFix 100 = none

-- Rejected programs never run.
#guard (evaluate boolSig deadAmbiguousLambda 10).isNone

end EPL.EvaluatorTests

namespace EPL.DataTests

open EPL EPL.Examples

-- sig: Bool = con 0 (True | False); List = con 1 (Nil | Cons a (List a))
def listSig : Signature := [⟨0, [[], []]⟩, ⟨1, [[], [.bvar 0, .app (.con 1) (.bvar 0)]]⟩]

def ifThen (c a b : Source) : Source :=
  .app (.app (.app (.const (.elim 0 2)) c) (.lambda none a)) (.lambda none b)

def nil : Source := .const (.ctor 1 0 0)
def cons (h t : Source) : Source := .app (.app (.const (.ctor 1 1 2)) h) t

def listTy : Ty := .app (.con 1) intTy

/-- `if False then 1 else 2 : Int`, evaluating to `2`. -/
def ifFalse : Source :=
  ifThen falseExpr (.primLit (.int 1)) (.primLit (.int 2))

example : (infer listSig ifFalse).map (·.ty) = some intTy := by
  decide

#guard ((evaluate listSig ifFalse 50).bind (·.2.value?)) =
  some (.primLit (.int 2))

/-- `match Cons 5 Nil with Nil => 0 | Cons x xs => x : Int`, evaluating to
`5`, and annotating `x : Int` and `xs : List Int`. -/
def matchCons : Source :=
  .app (.app (.app (.const (.elim 1 2))
      (cons (.primLit (.int 5)) nil))
    (.lambda none (.primLit (.int 0))))
    (.lambda none (.lambda none (.lambda none (.var 1))))

example : (infer listSig matchCons).map (·.ty) = some intTy := by
  decide

example : (infer listSig matchCons).map (·.elaborated) =
    some (.app (.app (.app (.const (.elim 1 2))
        (.app (.app (.const (.ctor 1 1 2)) (.primLit (.int 5)))
          (.const (.ctor 1 0 0))))
      (.lambda (some (.prim .unit)) (.primLit (.int 0))))
      (.lambda (some (.prim .unit))
        (.lambda (some intTy) (.lambda (some listTy) (.var 1))))) := by
  decide

#guard ((evaluate listSig matchCons 50).bind (·.2.value?)) =
  some (.primLit (.int 5))

/-- `if 1 then True else False` is rejected: the scrutinee must be `Bool`. -/
def ifInt : Source :=
  ifThen (.primLit (.int 1)) trueExpr falseExpr

example : infer listSig ifInt = none := by
  decide

/-- Constructors and eliminators of the wrong arity are rejected. -/
example : infer listSig (.const (.ctor 1 1 3)) = none := by
  decide

example : infer listSig (.const (.elim 0 3)) = none := by
  decide

/-- A partial constructor application is a value of function type. -/
def partialCons : Source :=
  .app (.const (.ctor 1 1 2)) (.primLit (.int 1))

example : (infer listSig partialCons).map (·.ty) =
    some (.arrow listTy listTy) := by
  decide

example : Eval.Value partialCons.erase :=
  Eval.Value.const (c := .ctor 1 1 2) (args := [.primLit (.int 1)]) rfl
    (by decide) (by
      intro arg h
      rcases List.mem_singleton.mp h with rfl
      exact .primLit)

#guard ((evaluate listSig partialCons 10).bind (·.2.value?)) =
  some (.app (.const (.ctor 1 1 2)) (.primLit (.int 1)))

/-- Recursive list length via `fix`, over `listSig`. -/
def listInt : Source :=
  cons (.primLit (.int 1))
    (cons (.primLit (.int 2)) (cons (.primLit (.int 3)) nil))

def listNilBranch : Source :=
  .lambda none (.primLit (.int 0))

def listConsBranch : Source :=
  .lambda none (.lambda none (.lambda none
    (.app (.app (.primOp .intAdd) (.primLit (.int 1)))
      (.app (.var 4) (.var 0)))))

def listMatch (scrutinee : Source) : Source :=
  .app (.app (.app (.const (.elim 1 2)) scrutinee) listNilBranch)
    listConsBranch

def listLength : Source :=
  .fix (.fixed (.arrow listTy intTy))
    (.lambda (some (.fixed listTy)) (listMatch (.var 0)))

example : (infer listSig (.app listLength listInt)).map (·.ty) = some intTy := by
  decide

#guard ((evaluate listSig (.app listLength listInt) 200).bind (·.2.value?)) =
  some (.primLit (.int 3))

end EPL.DataTests

namespace EPL.PrimTests

open EPL EPL.Examples

def charTy : Ty := .prim .char

/-- `if c then a else b` as an application of `Bool`'s eliminator. -/
def primIfThen (c a b : Source) : Source :=
  .app (.app (.app (.const (.elim 0 2)) c) (.lambda none a)) (.lambda none b)

def intSubExpr : Source :=
  .app (.app (.primOp .intSub) (.primLit (.int 1))) (.primLit (.int 5))

example : (infer boolSig intSubExpr).map (·.ty) = some intTy := by
  decide

#guard ((evaluate boolSig intSubExpr 50).bind (·.2.value?)) =
  some (.primLit (.int (-4)))

def intLtExpr (left right : Int) : Source :=
  .app (.app (.primOp .intLt) (.primLit (.int left))) (.primLit (.int right))

def charIf : Source :=
  primIfThen (intLtExpr 1 2) (.primLit (.char 'y')) (.primLit (.char 'n'))

def charIfFalse : Source :=
  primIfThen (intLtExpr 2 1) (.primLit (.char 'y')) (.primLit (.char 'n'))

example : (infer boolSig charIf).map (·.ty) = some charTy := by
  decide

#guard ((evaluate boolSig charIf 50).bind (·.2.value?)) =
  some (.primLit (.char 'y'))

#guard ((evaluate boolSig charIfFalse 50).bind (·.2.value?)) =
  some (.primLit (.char 'n'))

def charLtExpr : Source :=
  .app (.app (.primOp .charLt) (.primLit (.char 'a'))) (.primLit (.char 'b'))

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

example : infer boolSig (.app (.app (.primOp .intAdd) (.primLit (.int 1)))
    (.primLit (.char 'c'))) = none := by
  decide

example : (infer boolSig (.primLit (.nat 7))).map (·.ty) = some (.prim .nat) := by
  decide

def partialIntLt : Source :=
  .app (.primOp .intLt) (.primLit (.int 1))

example : (infer boolSig partialIntLt).map (·.ty) =
    some (.arrow intTy boolTy) := by
  decide

example : Eval.Value partialIntLt.erase :=
  Eval.Value.primOpPartial (op := .intLt) .primLit

/-- `fix f : Int -> Int. fun n => if n < 1 then 0 else n + f (n - 1)`. -/
def primRecursive : Source :=
  .app
    (.fix (.fixed (.arrow intTy intTy))
      (.lambda (some (.fixed intTy))
        (primIfThen
          (.app (.app (.primOp .intLt) (.var 0)) (.primLit (.int 1)))
          (.primLit (.int 0))
          (.app (.app (.primOp .intAdd) (.var 1))
            (.app (.var 2)
              (.app (.app (.primOp .intSub) (.var 1)) (.primLit (.int 1))))))))
    (.primLit (.int 4))

example : (infer boolSig primRecursive).map (·.ty) = some intTy := by
  decide

#guard ((evaluate boolSig primRecursive 500).bind (·.2.value?)) =
  some (.primLit (.int 10))

end EPL.PrimTests
