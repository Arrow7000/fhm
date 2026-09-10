import FHM.Surface.Provenance
import FHM.Surface.Parse

open Surface Surface.Span SurfaceBridge SurfaceBridge.Provenance
open Surface.Parse

private def span (startCol endCol : Nat) : Span := ⟨1, startCol, 1, endCol⟩

private def demoCtors : CtorEnv := (elabDecls preludeDecls).getD []

private def pairSurface : Surface.Expr :=
  .pair (.primLit (.int 1)) (.primLit (.int 2))

private def pairSpanned : SpannedExpr :=
  .pair (span 1 7) (.leaf (span 2 3)) (.leaf (span 5 6))

private def pairTargetsAndOrigins : Bool :=
  match lowerWithProvenance demoCtors pairSurface pairSpanned with
  | some r =>
      r.sourceTargets ==
        [(0, .present [[]]),
         (1, .present [[.appFun, .appArg]]),
         (2, .present [[.appArg]])] &&
      r.provenanceTotal
  | none => false

private def pairProjection : Bool :=
  match lowerWithProvenance demoCtors pairSurface pairSpanned,
      lower demoCtors pairSurface with
  | some r,
      some (.app (.app (.ctor ⟨"Pair"⟩) (.primLit (.int 1))) (.primLit (.int 2))) =>
      match r.expr with
      | .app (.app (.ctor ⟨"Pair"⟩) (.primLit (.int 1))) (.primLit (.int 2)) => true
      | _ => false
  | _, _ => false

private def letSurface : Surface.Expr :=
  .letIn ⟨"id"⟩ [] [(⟨"x"⟩, none)] none (.var ⟨"x"⟩)
    (.app (.var ⟨"id"⟩) (.primLit (.int 7)))

private def letSpanned : SpannedExpr :=
  .letIn (span 1 25) (.leaf (span 12 13))
    (.app (span 17 21) (.leaf (span 17 19)) (.leaf (span 20 21)))

private def letParamPaths : Bool :=
  match lowerWithProvenance demoCtors letSurface letSpanned with
  | some r =>
      r.binderTargets ==
        [(.letIn 0, .present [.letIn []]),
         (.letParam 0 0, .present [.lambda [.letRhs]])] &&
      r.sourceTargets.contains (1, .present [[.letRhs, .lambdaBody]]) &&
      r.provenanceTotal
  | none => false

private def letInferenceJoin : Bool :=
  match lowerWithProvenance demoCtors letSurface letSpanned with
  | none => false
  | some lowering =>
      match inferWithProvenance demoCtors lowering with
      | some typed =>
          let schemeOk := match typed.inferredBinderSchemes with
            | [(.letIn 0, ⟨1, .arrow (.bvar 0) (.bvar 0)⟩)] => true
            | _ => false
          let stripOk := match typed.inference.output.stripFound, lowering.expr with
            | .letIn none (.lambda none (.var 0))
                (.app (.var 0) (.primLit (.int 7))),
              .letIn none (.lambda none (.var 0))
                (.app (.var 0) (.primLit (.int 7))) => true
            | _, _ => false
          schemeOk && typed.sourceTypes.length == 5 &&
            typed.sourceTypes.all (fun (_, targets) => targets.length == 1) &&
            typed.sourceTypesTotal && stripOk
      | none => false

private def expressionHoverUsesProvenance : Bool :=
  match lowerWithProvenance demoCtors letSurface letSpanned with
  | none => false
  | some lowering =>
      match inferWithProvenance demoCtors lowering with
      | some typed =>
          match typed.hoverAt? 1 20 with
          | some ⟨⟨4, ⟨1, 20, 1, 21⟩⟩, [([.letBody, .appArg], .prim .int)]⟩ => true
          | _ => false
      | none => false

private def listSurface : Surface.Expr :=
  .list [.primLit (.int 1), .primLit (.int 2)]

private def listSpanned : SpannedExpr :=
  .list (span 1 7) [.leaf (span 2 3), .leaf (span 5 6)]

private def listOriginsTotal : Bool :=
  match lowerWithProvenance demoCtors listSurface listSpanned with
  | some r =>
      r.provenanceTotal &&
      r.sourceTargets ==
        [(0, .present [[]]),
         (1, .present [[.appFun, .appArg]]),
         (2, .present [[.appArg, .appFun, .appArg]])]
  | none => false

private def recSurface : Surface.Expr :=
  .letRecIn
    [{ name := ⟨"id"⟩, params := [(⟨"x"⟩, none)], ann := none, rhs := .var ⟨"x"⟩ }]
    (.app (.var ⟨"id"⟩) (.primLit (.int 4)))

private def recSpanned : SpannedExpr :=
  .letRecIn (span 1 28) [.leaf (span 12 13)]
    (.app (span 18 22) (.leaf (span 18 20)) (.leaf (span 21 22)))

private def recBinderJoin : Bool :=
  match lowerWithProvenance demoCtors recSurface recSpanned with
  | none => false
  | some lowering =>
      lowering.provenanceTotal &&
      lowering.binderTargets ==
        [(.letRec 0 0, .present [.letRec [] 0]),
         (.letRecParam 0 0 0, .present [.lambda [.letRecRhs 0]])] &&
      match inferWithProvenance demoCtors lowering with
      | some typed =>
          match typed.inferredBinderSchemes with
          | [(.letRec 0 0, ⟨1, .arrow (.bvar 0) (.bvar 0)⟩)] => true
          | _ => false
      | none => false

private def patCompFormsHaveTotalProvenance : Bool :=
  let ifSurface : Surface.Expr :=
    .ife (.primLit (.bool true)) (.primLit (.int 1)) (.primLit (.int 0))
  let ifSpanned : SpannedExpr :=
    .ife (span 1 17) (.leaf (span 4 8)) (.leaf (span 10 11)) (.leaf (span 16 17))
  let matchSurface : Surface.Expr :=
    .match_ (.primLit (.bool true)) [(.wildcard, .primLit (.int 1))]
  let matchSpanned : SpannedExpr :=
    .match_ (span 1 20) (.leaf (span 7 11)) [.leaf (span 19 20)]
  match lowerWithProvenance demoCtors ifSurface ifSpanned,
      lowerWithProvenance demoCtors matchSurface matchSpanned with
  | some ifLowering, some matchLowering =>
      ifLowering.provenanceTotal && matchLowering.provenanceTotal &&
        toString (repr ifLowering.expr) ==
          toString (repr ((lower demoCtors ifSurface).getD (.ctor ⟨"bad"⟩))) &&
        toString (repr matchLowering.expr) ==
          toString (repr ((lower demoCtors matchSurface).getD (.ctor ⟨"bad"⟩)))
  | _, _ => false

private def duplicatedArmAndCapturesAreCoalesced : Bool :=
  let surface : Surface.Expr :=
    .match_ (.pair (.primLit (.bool true)) (.primLit (.bool false)))
      [(.pair (.ctor ⟨"True"⟩ []) (.ctor ⟨"True"⟩ []), .primLit (.int 0)),
       (.pair (.name ⟨"x"⟩) (.name ⟨"y"⟩), .primLit (.int 1)),
       (.wildcard, .primLit (.int 2))]
  let spanned : SpannedExpr :=
    .match_ (span 1 40)
      (.pair (span 7 18) (.leaf (span 8 12)) (.leaf (span 13 18)))
      [.leaf (span 20 21), .leaf (span 28 29), .leaf (span 39 40)]
  match lowerWithProvenance demoCtors surface spanned with
  | none => false
  | some lowering =>
      let armTargetsOk := match lowering.sourceTargets.find? (fun pair => pair.1 == 5) with
        | some (_, .present paths) => paths.length == 2
        | _ => false
      let captureOk := fun capture =>
        match lowering.binderTargets.find? (fun pair => pair.1 == .patCapture 0 1 capture) with
        | some (_, .present [.patCapture paths foundCapture]) =>
            foundCapture == capture && paths.length == 2
        | _ => false
      lowering.provenanceTotal && armTargetsOk && captureOk 0 && captureOk 1 &&
        match inferWithProvenance demoCtors lowering with
        | none => false
        | some typed =>
            typed.sourceTypesTotal && typed.patternBinderTypesTotal &&
              typed.patternBinderTypes.length == 2 &&
              typed.patternBinderTypes.all fun (site, types) =>
                match site with
                | .patCapture 0 1 _ =>
                    types.length == 2 && types.all fun (_, ty) =>
                      match ty with
                      | .customTy ⟨"Bool"⟩ [] => true
                      | _ => false
                | _ => false

private def eliminatedArmAndBinderAreExplicit : Bool :=
  let surface : Surface.Expr :=
    .match_ (.primLit (.bool true))
      [(.wildcard, .primLit (.int 1)),
       (.name ⟨"dead"⟩, .primLit (.int 2))]
  let spanned : SpannedExpr :=
    .match_ (span 1 30) (.leaf (span 7 11))
      [.leaf (span 18 19), .leaf (span 29 30)]
  match lowerWithProvenance demoCtors surface spanned with
  | none => false
  | some lowering =>
      lowering.provenanceTotal &&
        lowering.sourceTargets.contains
          (3, .absent .eliminatedByPatternCompilation) &&
        lowering.binderTargets.contains
          (.patCapture 0 1 0, .absent .eliminatedByPatternCompilation)

private def emptyMatchFailureOriginsAreTotal : Bool :=
  let surface : Surface.Expr := .match_ (.primLit (.bool true)) []
  let spanned : SpannedExpr := .match_ (span 1 12) (.leaf (span 7 11)) []
  match lowerWithProvenance demoCtors surface spanned with
  | some lowering =>
      lowering.provenanceTotal && lowering.coreOrigins.any fun (_, origin) =>
        origin.kind == .generated (.patternCompilation .failureSentinel)
  | none => false

private def nestedPatCompTraceRebases : Bool :=
  let surface : Surface.Expr :=
    .lambda (.name ⟨"b"⟩) none
      (.ife (.var ⟨"b"⟩) (.primLit (.int 1)) (.primLit (.int 0)))
  let spanned : SpannedExpr :=
    .lambda (span 1 24)
      (.ife (span 7 24) (.leaf (span 10 11))
        (.leaf (span 17 18)) (.leaf (span 23 24)))
  match lowerWithProvenance demoCtors surface spanned with
  | none => false
  | some lowering =>
      lowering.provenanceTotal && lowering.coreOrigins.contains
        ([.lambdaBody], ⟨⟨1, span 7 24⟩,
          .generated (.patternCompilation .scrutineeLet)⟩) &&
        match inferWithProvenance demoCtors lowering with
        | some typed => typed.sourceTypesTotal
        | none => false

private def parserMirrorFeedsProvenance : Bool :=
  match parseExprWithSpans "let id x = x in id 7" with
  | .ok (surface, _, spanned) =>
      match lowerWithProvenance demoCtors surface spanned with
      | some lowering => lowering.provenanceTotal
      | none => false
  | .error _ => false

def main : IO Unit := do
  let checks := [
    ("pair targets and total origins", pairTargetsAndOrigins),
    ("pair projection agrees", pairProjection),
    ("let parameter paths", letParamPaths),
    ("let inference join", letInferenceJoin),
    ("expression hover uses provenance", expressionHoverUsesProvenance),
    ("list origins total", listOriginsTotal),
    ("recursive binder join", recBinderJoin),
    ("PatComp forms have total provenance", patCompFormsHaveTotalProvenance),
    ("duplicated arm and captures coalesced", duplicatedArmAndCapturesAreCoalesced),
    ("eliminated arm and binder explicit", eliminatedArmAndBinderAreExplicit),
    ("empty match failure origins total", emptyMatchFailureOriginsAreTotal),
    ("nested PatComp trace rebases", nestedPatCompTraceRebases),
    ("parser mirror feeds provenance", parserMirrorFeedsProvenance)
  ]
  for (name, ok) in checks do
    IO.println s!"{if ok then "PASS" else "FAIL"}: {name}"
  if checks.all (·.2) then pure () else throw (IO.userError "provenance check failed")
