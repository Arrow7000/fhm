import FHM.InferW
import FHM.Decls

mutual
private def sameTy : Ty → Ty → Bool
  | .prim a, .prim b => decide (a = b)
  | .arrow a b, .arrow c d => sameTy a c && sameTy b d
  | .bvar a, .bvar b => decide (a = b)
  | .fvar a, .fvar b => decide (a = b)
  | .customTy a as, .customTy b bs => decide (a = b) && sameTys as bs
  | .bl lo hi a, .bl lo' hi' b => decide (lo = lo') && decide (hi = hi') && sameTy a b
  | _, _ => false

private def sameTys : List Ty → List Ty → Bool
  | [], [] => true
  | a :: as, b :: bs => sameTy a b && sameTys as bs
  | _, _ => false
end

mutual
private def fullyFound : Expr → Bool
  | .found _ inner => foundChildren inner
  | _ => false
termination_by e => 2 * e.size
decreasing_by all_goals simp [Expr.size]; omega

def foundChildren : Expr → Bool
  | .primLit _ | .primBinOp _ | .var _ | .ctor _ => true
  | .lambda _ body => fullyFound body
  | .app fn arg | .letIn _ fn arg => fullyFound fn && fullyFound arg
  | .match_ scrut branches => fullyFound scrut && foundBranches branches
  | .letRec _ bindings body => foundBindings bindings && fullyFound body
  | .found _ _ => false
termination_by e => 2 * e.size + 1
decreasing_by all_goals simp [Expr.size]; omega

def foundBranches : List (MatchPattern × Expr) → Bool
  | [] => true
  | (_, body) :: rest => fullyFound body && foundBranches rest
termination_by branches => 2 * Expr.sizeBranches branches
decreasing_by
  all_goals simp only [Expr.sizeBranches]
  all_goals omega

def foundBindings : List Expr → Bool
  | [] => true
  | binding :: rest => fullyFound binding && foundBindings rest
termination_by bindings => 2 * Expr.sizeRecGroup bindings
decreasing_by
  all_goals simp only [Expr.sizeRecGroup]
  all_goals omega
end

private def appIdSeven : Expr :=
  .app (.lambda none (.var 0)) (.primLit (.int 7))

private def appPayloadsSolved : Bool :=
  match inferFound [] appIdSeven with
  | some r =>
    match r.ty, r.output with
    | .prim .int,
        .found (.prim .int)
          (.app
            (.found (.arrow (.prim .int) (.prim .int))
              (.lambda none (.found (.prim .int) (.var 0))))
            (.found (.prim .int) (.primLit (.int 7)))) => true
    | _, _ => false
  | _ => false

private def annotatedId : Expr :=
  .letIn (some ⟨1, .arrow (.bvar 0) (.bvar 0)⟩)
    (.lambda none (.var 0))
    (.app (.var 0) (.primLit (.int 1)))

private def annotatedPayloadsClosed : Bool :=
  match inferFound [] annotatedId with
  | some r =>
    match r.ty, r.output with
    | .prim .int,
        .found (.prim .int)
          (.letIn (some ⟨1, .arrow (.bvar 0) (.bvar 0)⟩)
            (.found (.arrow (.bvar 0) (.bvar 0))
              (.lambda none (.found (.bvar 0) (.var 0))))
            _) => true
    | _, _ => false
  | _ => false

private def closeDepthCorrect : Bool :=
  match Ty.closeVarsFrom 1 [40, 41] (.arrow (.fvar 41) (.bvar 0)) with
  | .arrow (.bvar 2) (.bvar 0) => true
  | _ => false

private def stripAppExact : Bool :=
  match inferFound [] appIdSeven with
  | some r =>
    match r.output.stripFound with
    | .app (.lambda none (.var 0)) (.primLit (.int 7)) => true
    | _ => false
  | none => false

private def matchBranches : Expr :=
  .match_ (.primLit .unit)
    [(.wildcard, .lambda none (.var 0)),
     (.wildcard, .lambda none (.var 0))]

private def matchBranchSuffixes : Bool :=
  match inferFound [] matchBranches with
  | some r =>
    match r.output with
    | .found rootTy (.match_ _
        [(.wildcard, .found firstTy (.lambda none (.found firstArgTy (.var 0)))),
         (.wildcard, .found secondTy (.lambda none (.found secondArgTy (.var 0))))]) =>
        sameTy rootTy firstTy && sameTy firstTy secondTy &&
          sameTy firstArgTy secondArgTy
    | _ => false
  | none => false

private def maybeCtors : CtorEnv :=
  (elabDecls
    [{ name := ⟨"Maybe"⟩, paramCount := 1,
       ctors := [(⟨"Just"⟩, [.bvar 0]), (⟨"Nothing"⟩, [])] }]).getD []

private def namedMatch : Expr :=
  .match_ (.app (.ctor ⟨"Just"⟩) (.primLit (.int 5)))
    [(.named ⟨"Just"⟩ 1, .var 0),
     (.named ⟨"Nothing"⟩ 0, .primLit (.int 0))]

private def namedMatchPayloads : Bool :=
  match inferFound maybeCtors namedMatch with
  | some r =>
    match r.output with
    | .found (.prim .int) (.match_ (.found (.customTy ⟨"Maybe"⟩ [.prim .int]) _)
        [(.named ⟨"Just"⟩ 1, .found (.prim .int) (.var 0)),
         (.named ⟨"Nothing"⟩ 0, .found (.prim .int) (.primLit (.int 0)))]) => true
    | _ => false
  | none => false

private def recBodyRefinesBinding : Expr :=
  .lambda none
    (.letRec [none] [.var 1]
      (.app (.var 0) (.primLit (.int 1))))

private def recBindingSuffix : Bool :=
  match inferFound [] recBodyRefinesBinding with
  | some r =>
    match r.output with
    | .found _ (.lambda none
        (.found _ (.letRec [none]
          [.found bindingTy (.var 1)] _))) =>
        match bindingTy with
        | .arrow (.prim .int) _ => true
        | _ => false
    | _ => false
  | none => false

private def nestedCloseDepths : Bool :=
  let opened : Expr :=
    .letRec [some ⟨1, .fvar 41⟩, some ⟨2, .fvar 41⟩, none]
      [.found (.fvar 41) (.var 0),
       .found (.fvar 41) (.var 1),
       .found (.fvar 41) (.var 2)]
      (.found (.fvar 41) (.var 0))
  match opened.closeTyVars [41] with
  | .letRec [some ⟨1, .bvar 1⟩, some ⟨2, .bvar 2⟩, none]
      [.found (.bvar 1) (.var 0),
       .found (.bvar 2) (.var 1),
       .found (.bvar 0) (.var 2)]
      (.found (.bvar 0) (.var 0)) => true
  | _ => false

private def substitutionLeavesSourceAnn : Bool :=
  let term : Expr := .lambda (some (.fvar 7)) (.found (.fvar 7) (.var 0))
  match term.substFoundTys [(7, .prim .int)] with
  | .lambda (some (.fvar 7)) (.found (.prim .int) (.var 0)) => true
  | _ => false

private def openAnnotationMisuseRejected : Bool :=
  let source := .app (.lambda (some (.fvar 0)) (.var 0)) (.primLit (.int 5))
  (inferFound [] source).isNone

private def skolemCollisionCannotCorruptShape : Bool :=
  let source : Expr :=
    .letIn (some ⟨1, .arrow (.bvar 0) (.bvar 0)⟩)
      (.lambda (some (.fvar 0)) (.var 0)) (.var 0)
  -- The safe entry starts above source fvar 0, so this invalid signature is
  -- rejected without ever confusing that source variable for a fresh skolem.
  (inferFound [] source).isNone

private def oneWrapperPerLogicalNode : Bool :=
  [(inferFound [] appIdSeven), (inferFound [] annotatedId),
   (inferFound [] matchBranches), (inferFound maybeCtors namedMatch),
   (inferFound [] recBodyRefinesBinding)].all fun result =>
    match result with
    | some r => fullyFound r.output
    | none => false

def main : IO Unit := do
  let checks := [
    ("app payload suffixes", appPayloadsSolved),
    ("annotated payload closure", annotatedPayloadsClosed),
    ("depth-aware close", closeDepthCorrect),
    ("strict strip/source shape", stripAppExact),
    ("match branch suffixes", matchBranchSuffixes),
    ("parameterized named match", namedMatchPayloads),
    ("recursive binding suffix", recBindingSuffix),
    ("nested let-rec close depths", nestedCloseDepths),
    ("payload-only substitution", substitutionLeavesSourceAnn),
    ("open annotation remains rigid", openAnnotationMisuseRejected),
    ("no skolem/source collision", skolemCollisionCannotCorruptShape),
    ("one wrapper per logical node", oneWrapperPerLogicalNode)
  ]
  for (name, ok) in checks do
    IO.println s!"{if ok then "PASS" else "FAIL"}: {name}"
  if checks.all (·.2) then pure () else throw (IO.userError "found-output check failed")
