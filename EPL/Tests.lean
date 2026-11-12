import EPL.Examples
import EPL.Inference
import EPL.Properties.Unification
import EPL.Properties.InferenceState
import EPL.Properties.InferenceSound
import EPL.Properties.EndToEnd

namespace EPL.UnificationTests

def arrowExample : Option MSubst :=
  unify
    (.arrow (.mvar 0) (.rigid 0))
    (.arrow (.prim .int) (.mvar 1))

example : arrowExample = some [(0, .prim .int), (1, .rigid 0)] := by
  decide

example : unify (.rigid 0) (.prim .int) = none := by
  decide

example : unify (.mvar 0) (.arrow (.mvar 0) (.prim .int)) = none := by
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
  apply infer_sound (result := ⟨.arrow intTy intTy⟩)
  decide

example : Typing 0 [] explicitPolyProgram boolTy := by
  apply infer_sound (result := ⟨boolTy⟩)
  decide

example : Typing 0 [] partlyInferredPolyProgram boolTy := by
  apply infer_sound (result := ⟨boolTy⟩)
  decide

example : Typing 0 [] inferredIntegerFix intTy := by
  apply infer_sound (result := ⟨intTy⟩)
  decide

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
