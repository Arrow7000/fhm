import FHM.SurfaceBridge

/-! Native lowering failures preserve the failed source boundary and indexes.
Successful compatibility APIs are projections of these same workers. -/
namespace LoweringErrorTests
open SurfaceBridge

#guard match lowerTyResult preludeKindEnv [] (.tvar ⟨"a"⟩) with
  | .error { reason := .unboundTypeVariable ⟨"a"⟩, typePath := [], .. } => true
  | _ => false
#guard match lowerTyResult preludeKindEnv [] (.customTy ⟨"Absent"⟩ []) with
  | .error { reason := .unknownType ⟨"Absent"⟩, .. } => true
  | _ => false
#guard match lowerTyResult preludeKindEnv [] (.customTy ⟨"List"⟩ []) with
  | .error { reason := .typeArity ⟨"List"⟩ 1 0, .. } => true
  | _ => false
#guard match lowerTyResult preludeKindEnv [] (.arrow (.prim .int) (.namedHole "x")) with
  | .error { reason := .holeNotAllowed (some "x"), typePath := [.codomain], .. } => true
  | _ => false
#guard match lowerTyListResult preludeKindEnv [] [.prim .int, .prim .char, .hole] with
  | .error { reason := .holeNotAllowed none, typePath := [.argument 2], .. } => true
  | _ => false

private def badDecl : Surface.DataDecl :=
  ⟨⟨"Box"⟩, [], [(⟨"Box"⟩, [.prim .int, .customTy ⟨"List"⟩ []])]⟩
#guard match lowerDataDeclsInResult preludeKindEnv [badDecl] with
  | .error { reason := .typeArity ⟨"List"⟩ 1 0, site := .constructorFields ⟨"Box"⟩ ⟨"Box"⟩, typePath := [.argument 1], .. } => true
  | _ => false
#guard match lowerDataDeclsResult [badDecl, badDecl] with
  | .error { reason := .duplicateTypes [⟨"Box"⟩], .. } => true
  | _ => false
#guard match lowerDataDeclsResult [⟨⟨"Box"⟩, [⟨"a"⟩, ⟨"a"⟩], []⟩] with
  | .error { reason := .duplicateTypeParameters ⟨"Box"⟩ [⟨"a"⟩], .. } => true
  | _ => false
#guard match elabDeclsResult (preludeDecls ++ [⟨⟨"Bool"⟩, 0, []⟩]) with
  | .error (.duplicateTypes [⟨"Bool"⟩]) => true
  | _ => false
#guard match elabDeclsResult [⟨⟨"Box"⟩, 0, [(⟨"Box"⟩, [.bvar 0])]⟩] with
  | .error (.inConstructor ⟨"Box"⟩ (.invalidFields ⟨"Box"⟩ 0 [.bvar 0])) => true
  | _ => false

private def missing : Surface.Expr := .var ⟨"missing"⟩
#guard match lowerInputExprResult preludeKindEnv [] []
    (.list [.primLit (.int 1), .primLit (.int 2), .pair (.primLit .unit) missing]) with
  | .error { path := [.listItem 2, .pairRight], reason := .unboundValue ⟨"missing"⟩, .. } => true
  | _ => false
#guard match lowerInputExprResult preludeKindEnv [] []
    (.match_ (.primLit (.int 0)) [(.wildcard, .primLit .unit), (.wildcard, missing)]) with
  | .error { path := [.matchBranch 1], reason := .unboundValue ⟨"missing"⟩, .. } => true
  | _ => false
#guard match lowerInputExprResult preludeKindEnv [] []
    (.letRecIn [⟨⟨"a"⟩, [], [], none, .primLit .unit⟩,
      ⟨⟨"b"⟩, [], [], none, missing⟩] (.primLit .unit)) with
  | .error { path := [.letRecRhs 1], binding? := some ⟨"b"⟩, reason := .unboundValue ⟨"missing"⟩, .. } => true
  | _ => false
#guard match wrapInputParamsResult preludeKindEnv []
    [(⟨"x"⟩, none), (⟨"y"⟩, some (.customTy ⟨"Missing"⟩ []))] (.var 0) with
  | .error { site := .parameterAnnotation 1, reason := .unknownType ⟨"Missing"⟩, .. } => true
  | _ => false

-- Typed success retains the original term and declarative acceptance theorem.
example {ctors s input} (h : InputLowers ctors s input) : lowerInputResult ctors s = .ok input :=
  lowerInputResult_complete h
example {p error} (h : lowerInputProgramResult p = .error error) :
    ¬ ∃ ctors input, InputLowersProgram p ctors input :=
  lowerInputProgramResult_error_not_lowers h

end LoweringErrorTests
