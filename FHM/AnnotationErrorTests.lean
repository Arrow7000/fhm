import FHM.InferW

/-! Native annotation failures and preservation of annotation-local allocation,
rigidity and source-completeness contracts. -/

namespace AnnotationErrorTests

#guard match seedResult [] 5 none with
  | .ok ⟨(6, .fvar 5), _⟩ => true
  | _ => false
#guard match seedResult [] 5 (some (.fixed (.bvar 0))) with
  | .error (.invalidBoundVariables (.bvar 0) 0) => true
  | _ => false
#guard match seedResult [1] 5 (some (.arrow (.fixed (.fvar 1)) (.fixed (.fvar 2)))) with
  | .error (.outOfScopeVariables [2]) => true
  | _ => false
#guard match seedResult [7] 10 (some (.fixed (.fvar 7))) with
  | .ok ⟨(10, .fvar 7), _⟩ => true
  | _ => false
#guard match seedResult [] 5 (some (.arrow (.named "item") (.named "item"))) with
  | .ok ⟨(6, .arrow (.fvar 5) (.fvar 5)), _⟩ => true
  | _ => false

-- A whole-annotation hole must not allocate an unused unification variable.
#guard match checkLetResult [] [] 5 (.template .hole) (.prim .int) with
  | .ok ⟨(5, []), _⟩ => true
  | _ => false
#guard match checkLetResult [] [] 5 (.template (.fixed (.bvar 0))) (.prim .int) with
  | .error (.invalidBoundVariables (.bvar 0) 0) => true
  | _ => false
#guard match checkLetResult [1] [] 5
    (.template (.arrow (.fixed (.fvar 1)) (.fixed (.fvar 2)))) (.prim .int) with
  | .error (.outOfScopeVariables [2]) => true
  | _ => false

-- Soft outer variables are in scope without becoming rigid.
#guard match checkLetResult [] [.fvar 0] 5 (.template (.fixed (.fvar 0))) (.prim .int) with
  | .ok ⟨(5, [(0, .prim .int)]), _⟩ => true
  | _ => false
#guard match checkLetResult [0] [] 5 (.template (.fixed (.prim .int))) (.fvar 0) with
  | .error (.unification (.rigidVariable 0 (.prim .int))) => true
  | _ => false
#guard match checkLetResult [] [.fvar 0] 5
    (.template (.arrow (.fixed (.fvar 0)) (.fixed (.prim .int)))) (.fvar 0) with
  | .error (.unification (.occursCheck 0 (.arrow (.fvar 0) (.prim .int)))) => true
  | _ => false

private def repeated : TyTemplate := .custom ⟨"Pair"⟩ [.named "item", .named "item"]
private def conflicting : Ty := .customTy ⟨"Pair"⟩ [.prim .int, .prim .char]
#guard match checkLetResult [] [] 5 (.template repeated) conflicting with
  | .error (.unification (.mismatch (.prim .char) (.prim .int))) => true
  | _ => false
#guard match checkSignatureResult [] [] [4] 5 (.partialForall 1 repeated) conflicting with
  | .error (.unification (.mismatch (.prim .char) (.prim .int))) => true
  | _ => false

#guard match checkSignatureResult [] [] [4] 5 (.complete ⟨1, .bvar 1⟩) (.prim .int) with
  | .error (.invalidBoundVariables (.bvar 1) 1) => true
  | _ => false
#guard match checkSignatureResult [] [] [] 5 (.complete ⟨0, .fvar 7⟩) (.prim .int) with
  | .error (.outOfScopeVariables [7]) => true
  | _ => false

-- Written forall variables stay rigid; anonymous result holes stay flexible.
#guard match checkSignatureResult [] [] [4] 5
    (.complete ⟨1, .arrow (.bvar 0) (.bvar 0)⟩) (.arrow (.prim .int) (.prim .int)) with
  | .error (.unification (.rigidVariable 4 (.prim .int))) => true
  | _ => false
#guard match checkSignatureResult [] [] [4] 5
    (.complete ⟨1, .arrow (.bvar 0) (.bvar 0)⟩) (.arrow (.fvar 4) (.fvar 4)) with
  | .ok ⟨(5, []), _⟩ => true
  | _ => false
#guard match checkSignatureResult [] [] [4] 5
    (.partialForall 1 (.arrow (.fixed (.bvar 0)) .hole)) (.arrow (.fvar 4) (.prim .int)) with
  | .ok ⟨(6, [(5, .prim .int)]), _⟩ => true
  | _ => false
#guard match checkSignatureResult [] [] [4] 5
    (.partialForall 1 (.arrow (.fixed (.bvar 0)) (.fixed (.fvar 7)))) (.prim .int) with
  | .error (.outOfScopeVariables [7]) => true
  | _ => false
#guard match checkSignatureResult [] [] [] 5 (.partialForall 1 (.fixed (.bvar 0))) (.prim .int) with
  | .error (.invalidBoundVariables (.bvar 0) 0) => true
  | _ => false

-- Using the wrong worker is distinguishable from a source annotation failure.
#guard match checkLetResult [] [] 5 (.complete ⟨0, .prim .int⟩) (.prim .int) with
  | .error .expectedMonotype => true
  | _ => false
#guard match checkSignatureResult [] [] [] 5 (.template .hole) (.prim .int) with
  | .error .expectedSignature => true
  | _ => false

end AnnotationErrorTests
