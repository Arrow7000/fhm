import EPL.Examples
import EPL.Inference
import EPL.Properties.Unification
import EPL.Properties.InferenceState
import EPL.Properties.InferenceSound
import EPL.Properties.EndToEnd

namespace EPL.UnificationTests

def arrowExample : Option MStore :=
  MStore.unify [none, none]
    (.arrow (.mvar 0) (.rigid 0))
    (.arrow (.prim .int) (.mvar 1))

example : arrowExample = some [some (.prim .int), some (.rigid 0)] := by
  decide

/-- Solving `?0 := ?1` and then `?1 := Int` rewrites the earlier entry, so the
store stays normalized. -/
example :
    MStore.unify [none, none]
        (.arrow (.mvar 0) (.mvar 1))
        (.arrow (.mvar 1) (.prim .int)) =
      some [some (.prim .int), some (.prim .int)] := by
  decide

example : MStore.unify [] (.rigid 0) (.prim .int) = none := by
  decide

example : MStore.unify [none] (.mvar 0) (.arrow (.mvar 0) (.prim .int)) = none := by
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

example : (infer inferredIntLambda).map (·.ty) =
    some (.arrow intTy intTy) := by
  decide

example : (infer explicitPolyProgram).map (·.ty) = some boolTy := by
  decide

example : (infer implicitPolyProgram).map (·.ty) = none := by
  decide

example : (infer identityRhs).map (·.ty) = none := by
  decide

def deadAmbiguousLambda : Source :=
  .letIn none identityRhs (.primLit .unit)

example : (infer deadAmbiguousLambda).map (·.ty) = none := by
  decide

def deadAmbiguousLambdaInScheme : Source :=
  .letIn (some ⟨0, .fixed (.prim .unit)⟩)
    deadAmbiguousLambda
    (.primLit .unit)

example : (infer deadAmbiguousLambdaInScheme).map (·.ty) = none := by
  decide

example : (infer integerLoop).map (·.ty) =
    some (.arrow intTy intTy) := by
  decide

def skolemEscape : Source :=
  .lambda none
    (.letIn (some ⟨1, .fixed (.bvar 0)⟩)
      (.var 0)
      (.primLit .unit))

example : (infer skolemEscape).map (·.ty) = none := by
  decide

def outerConstraint : Source :=
  .lambda none
    (.letIn (some ⟨0, .fixed intTy⟩)
      (.var 0)
      (.var 1))

example : (infer outerConstraint).map (·.ty) =
    some (.arrow intTy intTy) := by
  decide

def solvedSignatureHole : Source :=
  .letIn (some ⟨1, .hole⟩)
    (.primLit (.int 5))
    (.var 0)

example : (infer solvedSignatureHole).map (·.ty) = some intTy := by
  decide

def namedIdentityAnnotation : Scheme Template :=
  ⟨1, .arrow (.named "domain") (.fixed (.bvar 0))⟩

def namedIdentity : Source :=
  .letIn (some namedIdentityAnnotation)
    identityRhs
    (.app (.var 0) (.primLit (.int 5)))

example : (infer namedIdentity).map (·.ty) = some intTy := by
  decide

/-- Authored annotations cannot forge or capture inference metavariables. -/
def forgedMetaAnnotation : Source :=
  .lambda (some (.fixed (.mvar 0)))
    (.app
      (.app (.primOp .intAdd) (.var 0))
      (.primLit (.int 1)))

example : (infer forgedMetaAnnotation).map (·.ty) = none := by
  decide

def hiddenBadBoundAnnotation : Source :=
  .letIn none
    (.lambda (some (.fixed (.bvar 0))) (.primLit .unit))
    (.primLit .unit)

def hiddenBadRigidAnnotation : Source :=
  .letIn none
    (.lambda (some (.fixed (.rigid 0))) (.primLit .unit))
    (.primLit .unit)

example : (infer hiddenBadBoundAnnotation).map (·.ty) = none := by decide
example : (infer hiddenBadRigidAnnotation).map (·.ty) = none := by decide

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

example : (infer regionUnknownEscapes).map (·.ty) =
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

example : (infer deferredParameter).map (·.ty) =
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

example : (infer deferredSchemeHole).map (·.ty) =
    some (.arrow (.arrow intTy intTy) intTy) := by
  decide

/-- The completed scheme is recorded in the elaboration. -/
example : (infer deferredSchemeHole).map (·.elaborated) =
    some (.lambda (some (.arrow intTy intTy))
      (.letIn (some ⟨1, .arrow intTy (.arrow (.bvar 0) (.bvar 0))⟩)
        (.lambda (some intTy) (.lambda (some (.rigid 0))
          (.letIn none (.app (.var 2) (.var 1)) (.var 1))))
        (.app (.app (.primOp .intAdd) (.app (.var 1) (.primLit (.int 1))))
          (.primLit (.int 1))))) := by
  decide

/-- A scheme hole that nothing determines is still rejected.

`fun (x : Int) => let f : forall a. _ -> a -> a = fun z y => y in 0` -/
example : infer (.lambda (some (.fixed intTy))
    (.letIn (some holeFirstScheme) (.lambda none (.lambda none (.var 0)))
      (.primLit (.int 0)))) = none := by
  decide

def inferredHoleLambda : Source :=
  .lambda (some .hole)
    (.app
      (.app (.primOp .intAdd) (.var 0))
      (.primLit (.int 1)))

example : (infer inferredHoleLambda).map (·.ty) =
    some (.arrow intTy intTy) := by
  decide

def ambiguousHoleLambda : Source :=
  .lambda (some .hole) (.var 0)

example : (infer ambiguousHoleLambda).map (·.ty) = none := by
  decide

def partlyInferredPolyAnnotation : Scheme Template :=
  ⟨1, .arrow .hole (.fixed (.bvar 0))⟩

def partlyInferredPolyProgram : Source :=
  .letIn (some partlyInferredPolyAnnotation) identityRhs
    (.app (.var 0) (.primLit (.bool true)))

example : (infer partlyInferredPolyProgram).map (·.ty) = some boolTy := by
  decide

def falsePolyAnnotation : Scheme Template :=
  ⟨1, .arrow (.fixed (.bvar 0)) (.fixed intTy)⟩

def falsePolyProgram : Source :=
  .letIn (some falsePolyAnnotation) identityRhs
    (.primLit .unit)

example : (infer falsePolyProgram).map (·.ty) = none := by
  decide

def inferredIntegerFix : Source :=
  .fix .hole
    (.app
      (.app (.primOp .intAdd) (.var 0))
      (.primLit (.int 1)))

example : (infer inferredIntegerFix).map (·.ty) = some intTy := by
  decide

def incoherentNamedHole : Source :=
  .app
    (.lambda
      (some (.arrow (.named "shared") (.named "shared")))
      (.var 0))
    (.lambda (some (.fixed intTy)) (.primLit (.bool true)))

example : (infer incoherentNamedHole).map (·.ty) = none := by decide

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

example : (infer independentNamedHoles).map (·.ty) =
    some (.arrow boolTy intTy) := by
  decide

def reuseAfterPolyCheck : Source :=
  .letIn (some polyIdentityAnnotation) identityRhs inferredIntLambda

example : (infer reuseAfterPolyCheck).map (·.ty) =
    some (.arrow intTy intTy) := by
  decide

end EPL.InferenceTests

namespace EPL.InferenceSoundTests

open EPL EPL.Examples EPL.InferenceTests

/-- End-to-end canaries: these declarative derivations are obtained solely
from successful execution of the public inference function. -/
example : Typing 0 [] inferredIntLambda (.arrow intTy intTy) := by
  exact infer_typing_of_ty (by decide)

example : Typing 0 [] explicitPolyProgram boolTy := by
  exact infer_typing_of_ty (by decide)

example : Typing 0 [] partlyInferredPolyProgram boolTy := by
  exact infer_typing_of_ty (by decide)

example : Typing 0 [] inferredIntegerFix intTy := by
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
