import EPL.Examples
import EPL.Inference

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
