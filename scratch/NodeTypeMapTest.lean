import FHM.InferW
import FHM.Decls

/-! Executable canaries for the path-keyed inference metadata side tables. -/

mutual
private def sameTy : Ty → Ty → Bool
  | .prim a, .prim b => decide (a = b)
  | .arrow a b, .arrow c d => sameTy a c && sameTy b d
  | .bvar a, .bvar b => a == b
  | .fvar a, .fvar b => a == b
  | .customTy a as, .customTy b bs => decide (a = b) && sameTys as bs
  | _, _ => false

private def sameTys : List Ty → List Ty → Bool
  | [], [] => true
  | a :: as, b :: bs => sameTy a b && sameTys as bs
  | _, _ => false
end

private def nodeTyAt (types : NodeTypeMap) (path : CorePath) : Option Ty :=
  (types.find? fun pair => pair.1 == path).map (·.2)

private def hasTy (types : NodeTypeMap) (path : CorePath) (expected : Ty) : Bool :=
  match nodeTyAt types path with
  | some actual => sameTy actual expected
  | none => false

mutual
private def logicalPaths : Expr → List CorePath
  | .primLit _ | .primBinOp _ | .var _ | .ctor _ => [[]]
  | .lambda _ body => [] :: (logicalPaths body).map (.lambdaBody :: ·)
  | .app fn arg => [] ::
      (logicalPaths fn).map (.appFun :: ·) ++
      (logicalPaths arg).map (.appArg :: ·)
  | .letIn _ rhs body => [] ::
      (logicalPaths rhs).map (.letRhs :: ·) ++
      (logicalPaths body).map (.letBody :: ·)
  | .match_ scrut branches => [] ::
      (logicalPaths scrut).map (.matchScrut :: ·) ++
      logicalBranchPaths 0 branches
  | .letRec _ bindings body => [] ::
      logicalBindingPaths 0 bindings ++
      (logicalPaths body).map (.letRecBody :: ·)

private def logicalBranchPaths (index : Nat) : List (MatchPattern × Expr) → List CorePath
  | [] => []
  | (_, body) :: rest =>
      (logicalPaths body).map (.matchBranch index :: ·) ++
        logicalBranchPaths (index + 1) rest

private def logicalBindingPaths (member : Nat) : List Expr → List CorePath
  | [] => []
  | rhs :: rest =>
      (logicalPaths rhs).map (.letRecRhs member :: ·) ++
        logicalBindingPaths (member + 1) rest
end

private def exactlyOnce [BEq α] (expected actual : List α) : Bool :=
  expected.length == actual.length &&
    expected.all fun x => (actual.filter fun y => y == x).length == 1

private def nodeTypesTotalFor (source : Expr) (types : NodeTypeMap) : Bool :=
  exactlyOnce (logicalPaths source) (types.map Prod.fst)

private def appIdSeven : Expr :=
  .app (.lambda none (.var 0)) (.primLit (.int 7))

/-- The outer application's unifier must be applied back through every child
    fact, not merely to the result type. -/
private def applicationSubstitutionReachesChildren : Bool :=
  match inferWithTypes [] appIdSeven with
  | some r =>
      sameTy r.ty (.prim .int) &&
      hasTy r.nodeTypes [] (.prim .int) &&
      hasTy r.nodeTypes [.appFun] (.arrow (.prim .int) (.prim .int)) &&
      hasTy r.nodeTypes [.appFun, .lambdaBody] (.prim .int) &&
      hasTy r.nodeTypes [.appArg] (.prim .int) &&
      r.subst.any fun pair => sameTy pair.2 (.prim .int)
  | none => false

private def annotatedId : Expr :=
  .letIn (some ⟨1, .arrow (.bvar 0) (.bvar 0)⟩)
    (.lambda none (.var 0))
    (.app (.var 0) (.primLit (.int 1)))

/-- Fresh skolems used while checking the annotated RHS must be closed back to
    the annotation's binder depth before the public map is returned. -/
private def annotatedSkolemsAreClosed : Bool :=
  match inferWithTypes [] annotatedId with
  | some r =>
      hasTy r.nodeTypes [.letRhs] (.arrow (.bvar 0) (.bvar 0)) &&
      hasTy r.nodeTypes [.letRhs, .lambdaBody] (.bvar 0) &&
      hasTy r.nodeTypes [.letBody] (.prim .int) &&
      hasTy r.nodeTypes [.letBody, .appFun]
        (.arrow (.prim .int) (.prim .int)) &&
      r.nodeTypes.all fun (path, ty) =>
        match path with
        | .letRhs :: _ => ty.freeVars.isEmpty
        | _ => true
  | none => false

private def preludeCtors : CtorEnv :=
  (elabDecls preludeDecls).getD []

private def namedMatch : Expr :=
  .match_ (.app (.ctor ⟨"Just"⟩) (.primLit (.int 5)))
    [(.named ⟨"Just"⟩ 1, .var 0),
     (.named ⟨"Nothing"⟩ 0, .primLit (.int 0))]

private def maybeCtors : CtorEnv :=
  (elabDecls
    [{ name := ⟨"Maybe"⟩, paramCount := 1,
       ctors := [(⟨"Just"⟩, [.bvar 0]), (⟨"Nothing"⟩, [])] }]).getD []

private def matchBranchPathsAreTyped : Bool :=
  match inferWithTypes maybeCtors namedMatch with
  | some r =>
      hasTy r.nodeTypes [] (.prim .int) &&
      hasTy r.nodeTypes [.matchScrut] (.customTy ⟨"Maybe"⟩ [.prim .int]) &&
      hasTy r.nodeTypes [.matchBranch 0] (.prim .int) &&
      hasTy r.nodeTypes [.matchBranch 1] (.prim .int)
  | none => false

private def recursiveId : Expr :=
  .letRec [none] [.lambda none (.var 0)]
    (.app (.var 0) (.primLit (.int 3)))

private def letRecRhsPathsAreTyped : Bool :=
  match inferWithTypes [] recursiveId with
  | some r =>
      match nodeTyAt r.nodeTypes [.letRecRhs 0],
          nodeTyAt r.nodeTypes [.letRecRhs 0, .lambdaBody] with
      | some (.arrow domain codomain), some parameter =>
          sameTy domain parameter && sameTy codomain parameter &&
          hasTy r.nodeTypes [.letRecBody] (.prim .int) &&
          hasTy r.nodeTypes [.letRecBody, .appFun]
            (.arrow (.prim .int) (.prim .int))
      | _, _ => false
  | none => false

private def allMapsAreTotalAndUnique : Bool :=
  [(appIdSeven, inferWithTypes [] appIdSeven),
   (annotatedId, inferWithTypes [] annotatedId),
   (namedMatch, inferWithTypes maybeCtors namedMatch),
   (recursiveId, inferWithTypes [] recursiveId)].all fun (source, result) =>
    match result with
    | some r => nodeTypesTotalFor source r.nodeTypes
    | none => false

private def letSchemeIndexed : Bool :=
  let source : Expr :=
    .letIn none (.lambda none (.var 0))
      (.app (.var 0) (.primLit (.int 1)))
  match inferWithTypes [] source with
  | some r => match r.binderSchemes with
    | [(.letIn [], ⟨1, .arrow (.bvar 0) (.bvar 0)⟩)] => true
    | _ => false
  | none => false

private def branchSchemePaths : Bool :=
  let branchBody : Expr := .letIn none (.lambda none (.var 0)) (.var 0)
  let source : Expr := .match_ (.primLit .unit)
    [(.wildcard, branchBody), (.wildcard, branchBody)]
  match inferWithTypes [] source with
  | some r => match r.binderSchemes with
    | [(.letIn [.matchBranch 0], ⟨1, .arrow (.bvar 0) (.bvar 0)⟩),
       (.letIn [.matchBranch 1], ⟨1, .arrow (.bvar 0) (.bvar 0)⟩)] => true
    | _ => false
  | none => false

private def recSchemesIndexed : Bool :=
  let binding : Expr := .letIn none (.lambda none (.var 0)) (.var 0)
  let source : Expr := .letRec [none] [binding] (.var 0)
  match inferWithTypes [] source with
  | some r => match r.binderSchemes with
    | [(.letRec [] 0, ⟨1, .arrow (.bvar 0) (.bvar 0)⟩),
       (.letIn [.letRecRhs 0], ⟨1, .arrow (.bvar 0) (.bvar 0)⟩)] => true
    | _ => false
  | none => false

private def nestedAnnotatedSchemeDepthIsClosed : Bool :=
  let outerAnn : PolyTy := ⟨1, .arrow (.bvar 0) (.bvar 0)⟩
  let innerAnn : PolyTy :=
    ⟨1, .arrow (.bvar 1) (.arrow (.bvar 0) (.bvar 1))⟩
  let zRhs : Expr :=
    .lambda (some (.bvar 1))
      (.lambda (some (.bvar 0)) (.var 1))
  let source : Expr :=
    .letIn (some outerAnn)
      (.letIn (some innerAnn) (.letIn none zRhs (.var 0))
        (.lambda (some (.bvar 0)) (.var 0)))
      (.var 0)
  match inferWithTypes [] source with
  | some r => match r.binderSchemes with
    | [(.letIn [.letRhs, .letRhs],
        ⟨0, .arrow (.bvar 1) (.arrow (.bvar 0) (.bvar 1))⟩)] => true
    | _ => false
  | none => false

private def pair (a b : Expr) : Expr :=
  .app (.app (.ctor ⟨"Pair"⟩) a) b

private def polyIdAnn : PolyTy :=
  ⟨1, .arrow (.bvar 0) (.bvar 0)⟩

/-- The rigid variable used while checking an annotated recursive RHS is an
    implementation detail. Public hover metadata must close it back to the
    source annotation's bound variable, just as annotated non-recursive `let`
    does. -/
private def annotatedRecursiveSkolemsAreClosed : Bool :=
  let source : Expr :=
    .letRec [some polyIdAnn] [.lambda none (.var 0)] (.var 0)
  match inferWithTypes [] source with
  | some r =>
      hasTy r.nodeTypes [.letRecRhs 0]
        (.arrow (.bvar 0) (.bvar 0)) &&
      hasTy r.nodeTypes [.letRecRhs 0, .lambdaBody] (.bvar 0) &&
      r.nodeTypes.all fun (path, ty) =>
        match path with
        | .letRecRhs 0 :: _ => ty.freeVars.isEmpty
        | _ => true
  | none => false

/-- Once the recursive block is exited, its annotated member is available at
    separate instantiations in the body. -/
private def annotatedPolyUseAfterBlockAccepted : Bool :=
  let source : Expr :=
    .letRec [some polyIdAnn] [.lambda none (.var 0)]
      (pair
        (.app (.var 0) (.primLit (.int 1)))
        (.app (.var 0) (.primLit (.char 'x'))))
  match inferWithTypes preludeCtors source with
  | some r => sameTy r.ty
      (.customTy ⟨"Pair"⟩ [.prim .int, .prim .char]) &&
      nodeTypesTotalFor source r.nodeTypes
  | none => false

/-- A complete recursive annotation is available at its declared scheme inside
    the SCC, so an ordinary sibling may instantiate it independently. -/
private def annotatedPolyUseInsideBlockAccepted : Bool :=
  let source : Expr :=
    .letRec [some polyIdAnn, none]
      [.lambda none (.var 0),
       pair
        (.app (.var 0) (.primLit (.int 1)))
        (.app (.var 0) (.primLit (.char 'x')))]
      (.primLit .unit)
  (inferWithTypes preludeCtors source).isSome

private def negativeInferenceCases : Bool :=
  let badApp : Expr := .app (.primLit (.int 5)) (.primLit (.int 5))
  let rigidAnn : Expr :=
    .app (.lambda (some (.fvar 0)) (.var 0)) (.primLit (.int 5))
  let illScopedAnn : Expr := .lambda (some (.bvar 0)) (.var 0)
  let emptyMatch : Expr := .match_ (.primLit .unit) []
  (inferWithTypes [] badApp).isNone &&
    (inferWithTypes [] rigidAnn).isNone &&
    (inferWithTypes [] illScopedAnn).isNone &&
    (inferWithTypes [] emptyMatch).isNone

def main : IO Unit := do
  let checks := [
    ("application substitution reaches child paths", applicationSubstitutionReachesChildren),
    ("annotated skolems close in node metadata", annotatedSkolemsAreClosed),
    ("match branch paths are typed", matchBranchPathsAreTyped),
    ("let-rec RHS paths are typed", letRecRhsPathsAreTyped),
    ("node maps are total and unique", allMapsAreTotalAndUnique),
    ("let scheme path", letSchemeIndexed),
    ("branch scheme paths", branchSchemePaths),
    ("let-rec scheme paths", recSchemesIndexed),
    ("nested annotated scheme depth", nestedAnnotatedSchemeDepthIsClosed),
    ("annotated recursive skolems close in node metadata", annotatedRecursiveSkolemsAreClosed),
    ("polymorphic use after recursive block", annotatedPolyUseAfterBlockAccepted),
    ("polymorphic use inside recursive block", annotatedPolyUseInsideBlockAccepted),
    ("negative inference cases", negativeInferenceCases)
  ]
  for (name, ok) in checks do
    IO.println s!"{if ok then "PASS" else "FAIL"}: {name}"
  if checks.all (·.2) then pure ()
  else throw (IO.userError "node-type metadata check failed")
