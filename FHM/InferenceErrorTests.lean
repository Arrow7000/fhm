import FHM.InferW

/-! Native inference failure data and logical ownership across branches and
recursive groups. Recovery remains outside the acceptance worker. -/

namespace InferenceErrorTests

private def badApplication : InferInput := .app (.primLit (.int 1)) (.primLit (.int 2))

#guard match inferWithTypesResult [] (.var 0) with
  | .error ⟨[], .unboundVariable 0⟩ => true
  | _ => false
#guard match inferWithTypesResult [] (.ctor ⟨"Missing"⟩) with
  | .error ⟨[], .unknownConstructor ⟨"Missing"⟩⟩ => true
  | _ => false
#guard match inferWithTypesResult [] badApplication with
  | .error ⟨[], .application (.prim .int) (.prim .int) [] (.mismatch (.prim .int) (.arrow (.prim .int) _))⟩ => true
  | _ => false
#guard match inferWithTypesResult [] (.lambda none (.app (.var 0) (.var 0))) with
  | .error ⟨[.lambdaBody], .application _ _ [] (.occursCheck 0 (.arrow (.fvar 0) (.fvar 1)))⟩ => true
  | _ => false

-- A recursive wrapper must preserve failures in both member RHSs and the body.
#guard match inferWithTypesResult []
    (.letRec [{ ann := none, rhs := badApplication }] (.primLit (.int 0))) with
  | .error ⟨[.letRecRhs 0], .application ..⟩ => true
  | _ => false
#guard match inferWithTypesResult []
    (.letRec [{ ann := none, rhs := .lambda none (.app (.var 1) (.var 0)) }] badApplication) with
  | .error ⟨[.letRecBody], .application ..⟩ => true
  | _ => false

#guard match inferWithTypesResult []
    (.match_ (.primLit (.int 0)) [(.wildcard, badApplication)]) with
  | .error ⟨[.matchBranch 0], .application ..⟩ => true
  | _ => false
#guard match inferWithTypesResult []
    (.match_ (.primLit (.int 0)) [(.wildcard, .primLit (.int 1)), (.wildcard, .primLit (.char 'x'))]) with
  | .error ⟨[.matchBranch 1], .unification (.mismatch (.prim .char) (.prim .int))⟩ => true
  | _ => false
#guard match inferWithTypesResult [] (.match_ (.primLit (.int 0)) []) with
  | .error ⟨[], .emptyMatch⟩ => true
  | _ => false

-- Invalid bundled requests carry the actual failed boundary and variables.
#guard match inferWithTypesResultCore [5] 5 ⟨[], []⟩ (.primLit (.int 0)) with
  | .error ⟨[], .frontierViolation .rigid 5 [5]⟩ => true
  | _ => false
#guard match inferWithTypesResultCore [] 5 ⟨[PolyTy.mkTrivial (.fvar 5)], []⟩ (.primLit (.int 0)) with
  | .error ⟨[], .frontierViolation .context 5 [5]⟩ => true
  | _ => false
#guard match inferWithTypesResultCore [] 5 ⟨[], []⟩ (.primLit (.int 0)) [.fvar 5] with
  | .error ⟨[], .frontierViolation .soft 5 [5]⟩ => true
  | _ => false
#guard match inferWithTypesResultCore [] 5 ⟨[], []⟩ (.lambda (some (.fixed (.fvar 2))) (.var 0)) with
  | .error ⟨[], .outOfScopeVariables [2]⟩ => true
  | _ => false

-- Prefix validity distinguishes specialization, repeated names and escape.
#guard match resolveRecWrittenResult [.prim .int] [] with
  | .error (.notVariables [.prim .int]) => true
  | _ => false
#guard match resolveRecWrittenResult [.fvar 0, .fvar 0] [] with
  | .error (.repeatedVariables [0, 0]) => true
  | _ => false
#guard match resolveRecWrittenResult [.fvar 0, .fvar 1] [1] with
  | .error (.escapingVariables [1]) => true
  | _ => false
#guard match resolveRecSlotsResult [2] [] 0 [[.prim .int], [], [.prim .char]] with
  | .error (2, .notVariables [.prim .char]) => true
  | _ => false

-- Skipped shapes and successful earlier constraints retain the original index.
#guard match checkRecShapesResult []
    [(.prim .int, none), (.prim .int, some (.prim .int)), (.prim .char, some (.prim .int))] with
  | .error (2, .mismatch (.prim .char) (.prim .int)) => true
  | _ => false

private def completed : RecMemberState :=
  { RecMemberState.init 0 (.complete ⟨0, .prim .int⟩) with checked := true }
#guard match collectCompletedRecMembersResult [completed, RecMemberState.init 1 .absent] with
  | .error (1, .missingExport) => true
  | _ => false
#guard match collectCompletedRecMembersResult [RecMemberState.init 0 (.complete ⟨0, .prim .int⟩)] with
  | .error (0, .uncheckedMember) => true
  | _ => false

#guard match typecheckResult [] (.lambda none (.var 0)) with
  | .ok ⟨1, .arrow (.bvar 0) (.bvar 0)⟩ => true
  | _ => false

end InferenceErrorTests
