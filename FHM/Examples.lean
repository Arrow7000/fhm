import FHM.Headlines

/-! Canonical source derivations and inference certificates. Executable program
regressions live in `FHM.Examples.Programs`. -/

namespace Source.Demo

def identity : InferInput := .lambda none (.var 0)
def anonymous : InferInput := .lambda (some .hole) (.var 0)
def repeated : InferInput := .lambda
  (some (.custom ⟨"Pair"⟩ [.named "item", .named "item"])) (.var 0)

def polymorphicLet : InferInput := .letIn none identity
  (.letIn none (.app (.var 0) (.primLit (.int 1)))
    (.app (.var 1) (.primLit (.char 'x'))))

def partialSignature : InferInput := .letIn
  (some ⟨1, .arrow (.fixed (.bvar 0)) (.named "item")⟩)
  (.lambda (some (.fixed (.bvar 0))) (.var 0))
  (.app (.var 0) (.primLit (.int 42)))

/-- The canonical judgment admits the identity at every locally closed type. -/
theorem identity_typed (hty : ty.IsLC) :
    InputTyping ctx identity (.arrow ty ty) :=
  .lambda hty (by intro template h; cases h)
    (.var (args := []) rfl (by simp) (InstantiatesBy.refl_of_closed hty))

theorem anonymous_typed (hty : ty.IsLC) :
    InputTyping ctx anonymous (.arrow ty ty) :=
  .lambda hty (by intro template h; cases h; exact .hole)
    (.var (args := []) rfl (by simp) (InstantiatesBy.refl_of_closed hty))

def idid : InferInput := .letIn none identity (.app (.var 0) (.var 0))

/-- Ordinary implicit let-polymorphism is unchanged: the two uses of `id`
instantiate one scheme independently. No inference run is assumed. -/
theorem idid_typed (hty : ty.IsLC) : InputTyping ctx idid (.arrow ty ty) := by
  let scheme : PolyTy := ⟨1, .arrow (.bvar 0) (.bvar 0)⟩
  have hwf : scheme.WF := by
    change ContainsBvarsUpTo 1 (.arrow (.bvar 0) (.bvar 0))
    exact .arrow (.bvar (by decide)) (.bvar (by decide))
  refine .letIn (M := scheme) (L := []) hwf ?_ ?_ ?_
  · exact PartialCore.Ann.MonoMatches.absent hwf
  · intro names hfresh
    obtain ⟨name, rfl⟩ := List.length_eq_one_iff.mp hfresh.length
    exact identity_typed .fvar
  · exact .app
      (.var (args := [.arrow ty ty]) rfl (by simp; exact .arrow hty hty)
        (.arrow (.bvar rfl) (.bvar rfl)))
      (.var (args := [ty]) rfl (by simp; exact hty)
        (.arrow (.bvar rfl) (.bvar rfl)))

def appFiveFive : InferInput := .app (.primLit (.int 5)) (.primLit (.int 5))

theorem appFiveFive_untypable : ¬ InputTyping ctx appFiveFive ty := by
  intro h
  cases h with
  | app hf _ => cases hf

theorem idid_accepted : (inferWithTypes [] idid).isSome :=
  inferWithTypes_complete (idid_typed (ctx := ⟨[], []⟩) (ty := .fvar 0) .fvar)

private def showType (label : String) (input : InferInput) : IO Unit :=
  IO.println s!"{label}: {match typecheck [] input with
    | some scheme => toString scheme
    | none => "ill-typed"}"

#eval showType "identity" identity
#eval showType "anonymous parameter" anonymous
#eval showType "repeated local named hole" repeated
#eval showType "implicit let polymorphism" polymorphicLet
#eval showType "partial written signature" partialSignature

#guard match inferWithTypes [] polymorphicLet with
  | some result => match result.ty with | .prim .char => true | _ => false
  | none => false
#guard match SmallStep.evaluate 20 polymorphicLet.erase with
  | some (.primLit (.char 'x')) => true
  | _ => false
#guard match SmallStep.evaluate 20 partialSignature.erase with
  | some (.primLit (.int 42)) => true
  | _ => false

theorem inferred_source (h : inferWithTypes [] partialSignature = some result) :
    InputTyping ⟨[], []⟩ partialSignature result.ty := inferWithTypes_input_sound h

theorem inferred_runtime (h : inferWithTypes [] partialSignature = some result) :
    RuntimeTyping.RunWT ⟨[], []⟩ partialSignature.erase result.ty :=
  inferWithTypes_runtime_sound h

theorem inferred_principal (h : inferWithTypes [] partialSignature = some result)
    (ht : InputTyping ⟨[], []⟩ partialSignature ty) :
    ∃ R : Subst, (∀ pair ∈ R, pair.2.IsLC) ∧ ty = R.onTy result.ty := by
  obtain ⟨R, hlc, heq, _⟩ := inferWithTypes_principal h ty ht
  exact ⟨R, hlc, heq⟩

end Source.Demo

section

/-! Semantic canaries for anonymous lambda, signature, match, and recursive elaboration.
These run inference itself; source typing follows from `InferCert.inputSound`.
-/

namespace InferenceExamples

private def ctors : CtorEnv := (elabDecls preludeDecls).getD []
private def ctx : Ctx := ⟨[], ctors⟩

private def schemeAt (result : InferenceResult) (site : CoreBinderSite) : Option PolyTy :=
  (result.binderSchemes.find? (fun p => p.1 == site)).map Prod.snd

private def typeAt (result : InferenceResult) (path : CorePath) : Option Ty :=
  (result.nodeTypes.find? (fun p => p.1 == path)).map Prod.snd

/-! ### Bundled request/run canaries -/

private def literalRequest : InferRequest :=
  { protectedVars := [], soft := [], frontier := 0, ctx := ⟨[], []⟩,
    input := .primLit (.int 7) }

private def literalResult : InferCoreResult :=
  { frontier := 0
    subst := []
    ty := .prim .int
    nodeTypes := .root (.prim .int)
    binderSchemes := [] }

/-- A successful run records the exact executable result and exposes its certificate. -/
theorem literalRequest_run : InferRun literalRequest literalResult := by
  simp [InferRun, InferRequest.run, inferRequestCore, literalRequest, literalResult,
    inferWithTypesCore, inferWithTypesResultCore, Except.toOption,
    Expr.rigidVars, softVars, TyList.freeVars, Env.freeVars,
    InferredNodeTypes.root]

theorem literalRequest_cert : InferCert literalRequest literalResult.toInferResult :=
  literalRequest_run.cert

private def invalidGuardRequest : InferRequest :=
  { protectedVars := [0], soft := [], frontier := 0, ctx := ⟨[], []⟩,
    input := .primLit .unit }

private def invalidGuardResult : InferResult :=
  { frontier := 0, subst := [], ty := .prim .unit }

/-- Guard failure is operational: the underlying inference certificate still exists. -/
theorem invalidGuardRequest_rejected : invalidGuardRequest.run = none := by
  simp [InferRequest.run, inferRequestCore, invalidGuardRequest,
    inferWithTypesCore, inferWithTypesResultCore, Except.toOption]

theorem invalidGuardRequest_cert : InferCert invalidGuardRequest invalidGuardResult :=
  .primLitUnit

private def wrongLiteralMetadata : InferCoreResult :=
  { literalResult with nodeTypes := [] }

/-- `InferRun` is sensitive to metadata even when the semantic projection agrees. -/
theorem literalRequest_metadata_sensitive :
    wrongLiteralMetadata.toInferResult = literalResult.toInferResult ∧
      ¬ InferRun literalRequest wrongLiteralMetadata := by
  constructor
  · rfl
  · intro hwrong
    have heq := InferRun.result_eq literalRequest_run hwrong
    have htypes := congrArg InferCoreResult.nodeTypes heq
    simp [literalResult, wrongLiteralMetadata, InferredNodeTypes.root] at htypes

/-- The relational unifier admits either orientation for two flexible variables. -/
theorem flexibleFvars_unify_left :
    RigidUnify [] (.fvar 0) (.fvar 1) [(0, .fvar 1)] :=
  ⟨UnifyRel.fvarL (by simp) (by simp [Ty.freeVars]), by simp⟩

theorem flexibleFvars_unify_right :
    RigidUnify [] (.fvar 0) (.fvar 1) [(1, .fvar 0)] :=
  ⟨UnifyRel.fvarR (by simp) (by simp [Ty.freeVars]), by simp⟩

/-- The executable unifier resolves that freedom by choosing the left variable. -/
theorem flexibleFvars_executable_orientation :
    (unifyCoreK [] (.fvar 0) (.fvar 1)).map Subtype.val =
      some [(0, .fvar 1)] := by
  simp [unifyCoreK, unifyResultK, Except.toOption]

private def pair (left right : InferInput) : InferInput :=
  .app (.app (.ctor ⟨"Pair"⟩) left) right

/-- `let id = \(x : _) -> x in (id 1, id True)`. -/
def polymorphicId : InferInput :=
  .letIn none (.lambda (some .hole) (.var 0))
    (pair (.app (.var 0) (.primLit (.int 1))) (.app (.var 0) (.ctor ⟨"True"⟩)))

/-- Both occurrences of `_` are independently flexible. -/
def independentHoles : InferInput :=
  .letIn (some ⟨0, (.arrow .hole .hole)⟩)
    (.lambda none (.primLit (.int 1)))
    (pair (.app (.var 0) (.ctor ⟨"True"⟩)) (.app (.var 0) (.primLit (.int 1))))

def structuredId : InferInput :=
  .letIn (some ⟨0, (.arrow .hole .hole)⟩) (.lambda none (.var 0))
    (pair (.app (.var 0) (.primLit (.int 1))) (.app (.var 0) (.ctor ⟨"True"⟩)))

/-- Variables reachable through the outer context cannot be generalized. -/
def outerMonomorphic : InferInput :=
  .lambda none
    (.letIn (some ⟨0, .hole⟩) (.var 0)
      (pair (.app (.var 0) (.primLit (.int 1))) (.app (.var 0) (.ctor ⟨"True"⟩))))

def occursCheck : InferInput :=
  .lambda (some .hole) (.app (.var 0) (.var 0))

def fixedDomainAccepted : InferInput :=
  .letIn (some ⟨0, (.arrow (.fixed (.prim .int)) .hole)⟩) (.lambda none (.var 0))
    (.app (.var 0) (.primLit (.int 1)))

def fixedDomainRejected : InferInput :=
  .letIn (some ⟨0, (.arrow (.fixed (.prim .int)) .hole)⟩) (.lambda none (.var 0))
    (.app (.var 0) (.ctor ⟨"True"⟩))

def quantifiedId : InferInput :=
  .letIn (some ⟨1, (.arrow (.fixed (.bvar 0)) .hole)⟩)
    (.lambda none (.var 0)) (.var 0)

def quantifiedExtras : InferInput :=
  .letIn (some ⟨1, (.arrow (.fixed (.bvar 0)) .hole)⟩)
    (.lambda none (.lambda none (.var 1))) (.var 0)

def vacuousWritten : InferInput :=
  .letIn (some ⟨1, .hole⟩) (.primLit (.int 1)) (.var 0)

def quantifiedRigidRejected : InferInput :=
  .letIn (some ⟨1, (.arrow .hole (.fixed (.bvar 0)))⟩)
    (.lambda none (.primLit (.int 0))) (.var 0)

def signedRhsHole : InferInput :=
  .letIn (Option.fromScheme (some ⟨1, .arrow (.bvar 0) (.bvar 0)⟩))
    (.lambda (some .hole) (.var 0))
    (pair (.app (.var 0) (.primLit (.int 1))) (.app (.var 0) (.ctor ⟨"True"⟩)))

def signedBodyHole : InferInput :=
  .letIn (Option.fromScheme (some ⟨1, .arrow (.bvar 0) (.bvar 0)⟩))
    (.lambda none (.var 0)) (.lambda (some .hole) (.app (.var 1) (.var 0)))

#guard (inferCore [] 0 ctx quantifiedExtras).isSome
#guard (inferCore [] 0 ctx vacuousWritten).isSome
#guard !(inferCore [] 0 ctx quantifiedRigidRejected).isSome
#guard (inferCore [] 0 ctx signedRhsHole).isSome
#guard (inferCore [] 0 ctx signedBodyHole).isSome
#guard match inferWithTypes ctors quantifiedExtras with
  | some result => match schemeAt result (.letIn []) with
    | some ⟨2, .arrow (.bvar 0) (.arrow (.bvar 1) (.bvar 0))⟩ => true
    | _ => false
  | _ => false
#guard match inferWithTypes ctors vacuousWritten with
  | some result => match schemeAt result (.letIn []) with
    | some scheme => scheme.paramCount == 1
    | _ => false
  | _ => false

def partialRecursion : InferInput :=
  .letRec
    [{ ann := (some ⟨0, (.arrow .hole (.fixed (.prim .int)))⟩),
       rhs := .lambda none (.primLit (.int 0)) }]
    (.var 0)

def partialRecursionCodomainRejected : InferInput :=
  .letRec
    [{ ann := (some ⟨0, (.arrow .hole (.fixed (.prim .int)))⟩),
       rhs := .lambda none (.primLit .unit) }]
    (.var 0)

#guard (inferCore [] 0 ctx polymorphicId).isSome
#guard (inferCore [] 0 ctx independentHoles).isSome
#guard (inferCore [] 0 ctx structuredId).isSome
#guard !(inferCore [] 0 ctx outerMonomorphic).isSome
#guard !(inferCore [] 0 ctx occursCheck).isSome
#guard (inferCore [] 0 ctx fixedDomainAccepted).isSome
#guard !(inferCore [] 0 ctx fixedDomainRejected).isSome
#guard (inferCore [] 0 ctx quantifiedId).isSome
#guard match inferWithTypes ctors partialRecursion with
  | some result => match
      schemeAt result (.letRec [] 0), result.ty with
    | some ⟨1, .arrow (.bvar 0) (.prim .int)⟩, .arrow (.fvar _) (.prim .int) => true
    | _, _ => false
  | _ => false
#guard !(inferCore [] 0 ctx partialRecursionCodomainRejected).isSome

/- The id canary exports one quantified binder while its RHS metadata retains
the same inferred variable in the lambda's domain and codomain. -/
#guard match inferWithTypes ctors polymorphicId with
  | some result => match
      schemeAt result (.letIn []),
      typeAt result [.letRhs] with
    | some ⟨1, .arrow (.bvar 0) (.bvar 0)⟩, some (.arrow (.fvar a) (.fvar b)) => a == b
    | _, _ => false
  | _ => false

private def idHole : InferInput := .lambda (some .hole) (.var 0)

-- Independent local allocation: two syntactic visits, unrelated types.
def distinctCopies : InferInput := pair idHole idHole
#guard match inferCore [] 0 ctx distinctCopies with
  | some result => match result.val.ty with
    | .customTy ⟨"Pair"⟩ [.arrow (.fvar a) (.fvar a'), .arrow (.fvar b) (.fvar b')] =>
      a == a' && b == b' && a != b
    | _ => false
  | _ => false

-- Independent local uses: same InferInput value copied, each used at a different type.
def differentlyUsedCopies : InferInput :=
  pair (.app idHole (.primLit (.int 1))) (.app idHole (.ctor ⟨"True"⟩))
#guard (inferCore [] 0 ctx differentlyUsedCopies).isSome

-- Reallocating the holes must not reallocate the shared outer monomorphic f.
def sharedOuterRejected : InferInput :=
  .lambda none
    (pair
      (.app (.lambda (some .hole) (.app (.var 1) (.var 0))) (.primLit (.int 1)))
      (.app (.lambda (some .hole) (.app (.var 1) (.var 0))) (.ctor ⟨"True"⟩)))
#guard !(inferCore [] 0 ctx sharedOuterRejected).isSome

private def branches (yes no : InferInput) : List (MatchPattern × InferInput) :=
  [(.named ⟨"True"⟩ 0, yes), (.named ⟨"False"⟩ 0, no)]

-- Partial scrutinees use the same branch inference and constructor checks.
def directPartialScrutinee : InferInput :=
  .match_ (.app idHole (.ctor ⟨"True"⟩))
    (branches (.primLit (.int 1)) (.primLit (.int 0)))
#guard (inferCore [] 0 ctx directPartialScrutinee).isSome

-- Anonymous parameters in named and fallback bodies are solved in one thread.
def partialBranches : InferInput :=
  .match_ (.ctor ⟨"True"⟩) (branches idHole idHole)
#guard (inferCore [] 0 ctx partialBranches).isSome

-- Every branch must agree on the result; fresh local holes do not relax it.
def incompatiblePartialBranches : InferInput :=
  .match_ (.ctor ⟨"True"⟩)
    [(.wildcard, .app idHole (.primLit (.int 1))),
     (.wildcard, .app idHole (.ctor ⟨"True"⟩))]
#guard !(inferCore [] 0 ctx incompatiblePartialBranches).isSome

-- Equivalent normal lowering shape: the match scrutinee is bound once first.
def loweredPartialScrutinee : InferInput :=
  .letIn none (.app idHole (.ctor ⟨"True"⟩))
    (.match_ (.var 0) (branches (.primLit (.int 1)) (.primLit (.int 0))))
#guard (inferCore [] 0 ctx loweredPartialScrutinee).isSome

-- Nested complete match is an argument to the partial scrutinee expression.
def nestedScrutinee : InferInput :=
  .letIn none
    (.app idHole
      (.letIn none (.ctor ⟨"False"⟩)
        (.match_ (.var 0) (branches (.ctor ⟨"False"⟩) (.ctor ⟨"True"⟩)))))
    (.match_ (.var 0) (branches (.primLit (.int 1)) (.primLit (.int 0))))
#guard (inferCore [] 0 ctx nestedScrutinee).isSome

-- Lowering an irrefutable named pattern makes another ordinary let. This
-- checks the existing lowering/generalization policy, independently of copying.
def irrefutableCapture : InferInput :=
  .letIn none idHole
    (.letIn none (.var 0)
      (pair (.app (.var 0) (.primLit (.int 1)))
        (.app (.var 0) (.ctor ⟨"True"⟩))))
#guard (inferCore [] 0 ctx irrefutableCapture).isSome


private def rigidArrow : TyTemplate := .arrow (.fixed (.fvar 7)) .hole
private def rigidIdentity : InferInput := .lambda (some rigidArrow) (.var 0)
private def violatesRigid : InferInput :=
  .lambda (some rigidArrow) (.app (.var 0) (.primLit (.int 1)))
private def rigidLet : InferInput :=
  .letIn (some ⟨0, rigidArrow⟩) (.lambda none (.var 0)) (.var 0)
private def violatesRigidLet : InferInput :=
  .letIn (some ⟨0, rigidArrow⟩) (.lambda none (.var 0))
    (.app (.var 0) (.primLit (.int 1)))

#guard (inferCore [7] 8 ctx rigidIdentity).isSome
#guard !(inferCore [7] 8 ctx violatesRigid).isSome
#guard !(inferCore [] 8 ctx rigidIdentity).isSome
#guard (inferCore [7] 8 ctx rigidLet).isSome
#guard !(inferCore [7] 8 ctx violatesRigidLet).isSome
#guard match inferWithTypes ctors rigidLet with
  | some result => match schemeAt result (.letIn []), result.ty with
    | some scheme, .arrow (.fvar 7) (.fvar 7) => scheme.paramCount == 0
    | _, _ => false
  | _ => false

private def polyrec : InferInput :=
  .letRec
    [{ ann := (Option.fromScheme (some ⟨1, .arrow (.bvar 0) (.prim .int)⟩)),
       rhs := .lambda none
         (.app (.var 1) (.app (.app (.ctor ⟨"Pair"⟩) (.var 0)) (.var 0))) }]
    (.app (.var 0) (.ctor ⟨"True"⟩))
#guard (inferCore [] 0 ctx polyrec).isSome
#guard (inferCore [] 0 ctx
  (.letIn none (.lambda (some .hole) (.var 0)) polyrec)).isSome
private def unsignedPolyrec : InferInput :=
  match polyrec with
  | .letRec bindings body => .letRec (bindings.map fun binding => { binding with ann := none }) body
  | other => other
#guard !(principalType ctx.ctors unsignedPolyrec).isSome

-- Complete signatures protect their authored skolems while filling RHS holes.
def completeForallWithPartialRhs : InferInput :=
  .letIn (Option.fromScheme (some ⟨1, .arrow (.bvar 0) (.bvar 0)⟩))
    (.lambda (some .hole) (.var 0)) (.var 0)
#guard (inferCore [] 0 ctx completeForallWithPartialRhs).isSome

-- An unused hole still generalizes at its own binding even when it is absent
-- from the whole-program result type.
def unusedHole : InferInput :=
  .letIn (some ⟨0, .hole⟩) (.ctor ⟨"Nil"⟩) (.primLit (.int 1))
#guard match inferWithTypes ctors unusedHole with
  | some result => match schemeAt result (.letIn []), result.ty with
    | some ⟨1, .customTy ⟨"List"⟩ [.bvar 0]⟩, .prim .int => true
    | _, _ => false
  | _ => false

-- Public type and scheme artifacts come from the same run. Synthetic
-- scheme binders do not turn source hover monotypes into dangling bvars.
#guard match inferWithTypes ctors polymorphicId with
  | some result => result.binderSchemes.any (fun fact => fact.2.paramCount == 1)
  | none => false
#guard match (inferWithTypes ctors polymorphicId).bind (fun result =>
    result.nodeTypes.find? (fun fact => fact.1 == [.letRhs])) with
  | some (_, .arrow (.fvar 0) (.fvar 0)) => true
  | _ => false

#print axioms InferCert.inputSound

end InferenceExamples

end
