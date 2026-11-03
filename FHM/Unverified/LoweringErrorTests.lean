import FHM.Unverified.Diagnostics

/-! Metadata corruption is distinct from a rejected source term, and typed
source failures keep both their logical location and their authored span. -/
namespace FHM.Unverified.LoweringErrorTests
open SurfaceBridge SurfaceBridge.Provenance Surface.Span

private def owner : SourceNode := ⟨17, ⟨2, 3, 2, 10⟩, true⟩

#guard match lowerIdentifiedExprResult preludeKindEnv [] []
    (.var ⟨"missing"⟩) (.leaf owner) with
  | .error (.sourceFailure source { reason := .unboundValue ⟨"missing"⟩, .. }) => source == owner
  | _ => false
#guard match lowerIdentifiedExprResult preludeKindEnv [] []
    (.primLit .unit) (.list owner []) with
  | .error (.provenance { source? := some source, reason := .expressionShape }) => source == owner
  | _ => false
#guard match lowerIdentifiedExprResult preludeKindEnv [] []
    (.list [.primLit .unit]) (.list owner []) with
  | .error (.provenance { source? := some source, reason := .listShape 1 0 }) => source == owner
  | _ => false
#guard match lowerIdentifiedBranchesResult preludeKindEnv [] []
    [(.wildcard, .primLit .unit)] [] with
  | .error (.provenance { reason := .branchShape 1 0, .. }) => true
  | _ => false
#guard match lowerIdentifiedRecBindsResult preludeKindEnv [] [] owner 0
    [⟨⟨"value"⟩, [], [], none, .primLit .unit⟩] [] with
  | .error (.provenance { reason := .bindingShape 1 0, .. }) => true
  | _ => false
#guard match mergeSourceTargetsResult [owner] [] with
  | .error (.provenance { source? := some source, reason := .missingSourceClassification 17 }) => source == owner
  | _ => false
#guard match mergeBinderTargetsResult [(.lambda 17, .present [])] with
  | .error (.provenance { reason := .missingBinderClassification (.lambda 17), .. }) => true
  | _ => false

private def program : Surface.Program := { decls := [], groups := [], body := .primLit .unit }
private def spanned : SpannedProgram := { groups := [[.leaf Span.empty]], body := .leaf Span.empty }
#guard match HMArtifacts.programSpannedResult program spanned Span.empty with
  | .error (.provenance { reason := .programGroups 0 0 1, .. }) => true
  | _ => false

#check @lowerWithProvenanceResult_project
#print axioms lowerWithProvenanceResult_project

end FHM.Unverified.LoweringErrorTests
