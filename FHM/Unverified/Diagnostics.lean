import Lean.Data.Json
import FHM.Unverified.TypeDiagnostics

open Surface.Span

structure HoverDiag where
  message : String
  code? : Option String := none
  /-- Internal native mismatch data for recovery deduplication; never JSON or
  an inference input. Diagnostic wording has no effect on recovery. -/
  constraint? : Option (Ty × Ty) := none
  /-- A native generated constraint origin replaced by a precise source child. -/
  relocatedFrom? : Option Span := none
  missingPatterns : List String := []
  moreMissing : Bool := false
  line : Nat := 1
  col : Nat := 1
  endLine : Nat := 1
  endCol : Nat := 2
  deriving Repr

def HoverDiag.toJson (d : HoverDiag) : Lean.Json :=
  Lean.Json.mkObj <| [
    ("severity", Lean.Json.str "error"),
    ("message", Lean.Json.str d.message),
    ("line", Lean.Json.num d.line),
    ("col", Lean.Json.num d.col),
    ("endLine", Lean.Json.num d.endLine),
    ("endCol", Lean.Json.num d.endCol)
  ] ++ (d.code?.map fun code => ("code", Lean.Json.str code)).toList ++
    (if d.missingPatterns.isEmpty then [] else [
      ("missingPatterns", Lean.Json.arr (d.missingPatterns.map Lean.Json.str).toArray),
      ("moreMissing", Lean.Json.bool d.moreMissing)])

def diagAtSpan (msg : String) (s? : Option Span) : HoverDiag :=
  match s? with
  | some s => {
      message := msg
      line := s.startLine
      col := s.startCol
      endLine := s.endLine
      endCol := s.endCol
    }
  | none => { message := msg }

namespace FHM.Unverified.Diagnostics

open SurfaceBridge SurfaceBridge.Provenance HMArtifacts

private def valName : ValName → String | .mk name => name
private def tyName : TyName → String | .mk name => name
private def ctorName : CtorName → String | .mk name => name
private def quoted (names : List String) : String :=
  String.intercalate ", " (names.map fun name => "`" ++ name ++ "`")

private def diagnostic (code message : String) (span : Span) : HoverDiag :=
  { diagAtSpan message (some span) with code? := some code }

private def declSpan (p : Surface.Program) (sp : SpannedProgram) (name : TyName) : Option Span :=
  ((p.decls.zip sp.declSpans).filter fun pair => pair.1.name == name).getLast? |>.map (·.2)

private def binderSpan (binders : List BinderSpan) (kind : BinderKind) (name : String)
    (scope : Span) : Option Span :=
  (binders.filter fun binder => binder.kind == kind && binder.name == name && inside binder.span scope).getLast?
    |>.map (·.span)

private def ctorRegion (binders : List BinderSpan) (name : CtorName) (scope : Span) : Span :=
  match binderSpan binders .ctor (ctorName name) scope with
  | none => scope
  | some own =>
      let next := (binders.find? fun binder => binder.kind == .ctor &&
        inside binder.span scope && before own binder.span).map (·.span)
      { startLine := own.startLine, startCol := own.startCol
        endLine := (next.map (·.startLine)).getD scope.endLine
        endCol := (next.map (·.startCol)).getD scope.endCol }

/-- Surface paths follow authored children, including the pre-desugaring RHS. -/
def surfaceAtPath : Surface.Expr → SurfacePath → Option Surface.Expr
  | expr, [] => some expr
  | .pair a _, .pairLeft :: rest => surfaceAtPath a rest
  | .pair _ b, .pairRight :: rest => surfaceAtPath b rest
  | .cons head _, .consHead :: rest => surfaceAtPath head rest
  | .cons _ tail, .consTail :: rest => surfaceAtPath tail rest
  | .list items, .listItem index :: rest => do surfaceAtPath (← items[index]?) rest
  | .lambda _ _ body, .lambdaBody :: rest => surfaceAtPath body rest
  | .app fn _, .appFun :: rest => surfaceAtPath fn rest
  | .app _ arg, .appArg :: rest => surfaceAtPath arg rest
  | .letIn _ _ _ _ rhs _, .letRhs :: rest => surfaceAtPath rhs rest
  | .letIn _ _ _ _ _ body, .letBody :: rest => surfaceAtPath body rest
  | .letRecIn bindings _, .letRecRhs index :: rest => do
      surfaceAtPath (← bindings[index]?).rhs rest
  | .letRecIn _ body, .letRecBody :: rest => surfaceAtPath body rest
  | .ife condition _ _, .ifCondition :: rest => surfaceAtPath condition rest
  | .ife _ yes _, .ifThen :: rest => surfaceAtPath yes rest
  | .ife _ _ no, .ifElse :: rest => surfaceAtPath no rest
  | .match_ scrutinee _, .matchScrut :: rest => surfaceAtPath scrutinee rest
  | .match_ _ branches, .matchBranch index :: rest => do
      surfaceAtPath (← branches[index]?).2 rest
  | _, _ => none
termination_by _ path => path.length

private def bindingAtPath (expr : Surface.Expr) (path : SurfacePath) : Option Surface.Binding := do
  match ← surfaceAtPath expr path with
  | .letIn name tyParams params ann rhs _ => some ⟨name, tyParams, params, ann, rhs⟩
  | _ => do
      let .letRecRhs index ← path.getLast? | none
      let .letRecIn bindings _ ← surfaceAtPath expr path.dropLast | none
      bindings[index]?

private structure TypeAtom where
  path : List LowerTypeStep
  name : String
  kind : ReferenceKind

mutual
private def typeAtoms (path : List LowerTypeStep) : Surface.Ty → List TypeAtom
  | .hole => [⟨path, "_", .typeHole⟩]
  | .namedHole name => [⟨path, "?" ++ name, .typeHole⟩]
  | .prim .bool => [⟨path, "Bool", .type⟩]
  | .prim _ => []
  | .tvar name => [⟨path, valName name, .typeVar⟩]
  | .arrow a b => typeAtoms (path ++ [.domain]) a ++ typeAtoms (path ++ [.codomain]) b
  | .pair a b => typeAtoms (path ++ [.pairLeft]) a ++ typeAtoms (path ++ [.pairRight]) b
  | .customTy name args => ⟨path, tyName name, .type⟩ :: typeAtomsList path 0 args
private def typeAtomsList (path : List LowerTypeStep) (index : Nat) : List Surface.Ty → List TypeAtom
  | [] => []
  | ty :: rest => typeAtoms (path ++ [.argument index]) ty ++ typeAtomsList path (index + 1) rest
end

private def annotationAtoms (p : Surface.Program) (error : LoweringError) : List TypeAtom × List LowerTypeStep :=
  match error.site with
  | .constructorFields parent name =>
      let fields := ((p.decls.find? (·.name == parent)).bind fun decl =>
        (decl.ctors.find? (·.1 == name)).map (·.2)).getD []
      (typeAtomsList [] 0 fields, error.typePath)
  | .lambdaAnnotation =>
      let ann := (surfaceAtPath p.term error.path).bind fun
        | .lambda _ ann _ => ann
        | _ => none
      ((ann.map (typeAtoms [])).getD [], error.typePath)
  | .bindingAnnotation =>
      let ann := (bindingAtPath p.term error.path).bind fun binding =>
        finalizeInputAnn binding.tyParams binding.params binding.ann
      ((ann.map fun scheme => typeAtoms [] scheme.body).getD [], error.typePath)
  | .parameterAnnotation index =>
      let params := ((bindingAtPath p.term error.path).map (·.params)).getD []
      let atoms := (params.zipIdx).flatMap fun ((_, ann), param) =>
        (ann.map (typeAtoms [.argument param])).getD []
      (atoms, .argument index :: error.typePath)
  | _ => ([], error.typePath)

private def typeReferenceSpan (p : Surface.Program) (sp : SpannedProgram) (error : LoweringError)
    (scope : Span) : Option Span := do
  let (atoms, path) := annotationAtoms p error
  let index ← atoms.findIdx? (fun atom => atom.path == path)
  let atom ← atoms[index]?
  let ordinal := (atoms.take index).countP fun previous => previous.name == atom.name && previous.kind == atom.kind
  let refs := sp.references.filter fun ref => ref.name == atom.name && ref.kind == atom.kind && inside ref.span scope
  (refs[ordinal]?).map (·.span)

private def declErrorData : DeclError → String × String
  | .duplicateTypes names => ("decl.duplicateType", "duplicate type names: " ++ quoted (names.map tyName))
  | .duplicateConstructors names => ("decl.duplicateConstructor", "duplicate constructor names: " ++ quoted (names.map ctorName))
  | .invalidFields parent _ _ => ("decl.invalidFields", "invalid constructor field type in `" ++ tyName parent ++ "`")
  | .inConstructor name error =>
      let (code, message) := declErrorData error
      (code, message ++ " (constructor `" ++ ctorName name ++ "`)")

private def declErrorScope (p : Surface.Program) (sp : SpannedProgram) (binders : List BinderSpan) : DeclError → Span
  | .duplicateTypes names =>
      ((names.head?).bind (declSpan p sp)).getD sp.body.span
  | .duplicateConstructors names =>
      ((names.head?).bind fun name =>
        (binders.filter fun binder => binder.kind == .ctor && binder.name == ctorName name).getLast?).map (·.span)
        |>.getD sp.body.span
  | .invalidFields parent _ _ => (declSpan p sp parent).getD sp.body.span
  | .inConstructor name error => ctorRegion binders name (declErrorScope p sp binders error)

def declarationDiag (error : DeclError) (p : Surface.Program) (sp : SpannedProgram)
    (binders : List BinderSpan) : HoverDiag :=
  let (code, message) := declErrorData error
  diagnostic code message (declErrorScope p sp binders error)

private def loweringData : LoweringErrorReason → String × String
  | .unboundValue name => ("lower.unboundName", "unbound name `" ++ valName name ++ "`")
  | .unboundTypeVariable name => ("lower.unknownTypeVariable", "unknown type variable `" ++ valName name ++ "`")
  | .unknownType name => ("lower.unknownType", "unknown type `" ++ tyName name ++ "`")
  | .typeArity name expected actual => ("lower.typeArity",
      s!"type `{tyName name}` expects {expected} type arguments, got {actual}")
  | .holeNotAllowed name => ("lower.holeNotAllowed",
      "type hole `" ++ (name.map ("?" ++ ·)).getD "_" ++ "` is not allowed in a data declaration")
  | .duplicateTypeParameters parent names => ("decl.duplicateTypeParameters",
      "duplicate type parameters in `" ++ tyName parent ++ "`: " ++ quoted (names.map valName))
  | .duplicateTypes names => ("decl.duplicateType", "duplicate type names: " ++ quoted (names.map tyName))
  | .duplicateConstructors names => ("decl.duplicateConstructor", "duplicate constructor names: " ++ quoted (names.map ctorName))
  | .duplicateBindings names => ("lower.duplicateBinding", "duplicate binding names: " ++ quoted (names.map valName))
  | .declarationElaboration error => declErrorData error

def loweringDiag (error : LoweringError) (p : Surface.Program) (sp : SpannedProgram)
    (binders : List BinderSpan) (fallback : Span) : HoverDiag :=
  let scope := match error.site with
    | .declaration name => (declSpan p sp name).getD fallback
    | .constructorFields parent name => ctorRegion binders name ((declSpan p sp parent).getD fallback)
    | .bindingAnnotation | .parameterAnnotation _ =>
        ((error.binding?.bind fun name =>
          (sp.bindingHeaders.find? (fun entry => entry.1 == valName name && inside entry.2 fallback)).map (·.2))).getD fallback
    | _ => fallback
  match error.reason with
  | .declarationElaboration cause => declarationDiag cause p sp binders
  | _ =>
    let span := match error.reason with
      | .duplicateTypes names => ((names.head?).bind (declSpan p sp)).getD scope
      | .duplicateConstructors names =>
          (((names.head?).bind fun name => (binders.filter fun binder =>
            binder.kind == .ctor && binder.name == ctorName name).getLast?).map (·.span)).getD scope
      | .duplicateBindings names =>
          (((names.head?).bind fun name => (binders.filter fun binder =>
            binder.kind == .val && binder.name == valName name).getLast?).map (·.span)).getD scope
      | _ => (typeReferenceSpan p sp error scope).getD scope
    let (code, message) := loweringData error.reason
    diagnostic code message span

def provenanceDiag (error : ProvenanceLowerError) (p : Surface.Program) (sp : SpannedProgram)
    (binders : List BinderSpan) (fallback : Span) : HoverDiag :=
  match error with
  | .sourceFailure source cause => loweringDiag cause p sp binders source.span
  | .provenance failure =>
      let code := match failure.reason with
        | .programGroups .. | .programMembers .. => "internal.programProvenance"
        | .expressionShape | .listShape .. | .branchShape .. | .bindingShape .. => "internal.provenanceShape"
        | .missingSourceClassification .. => "internal.sourceClassification"
        | .missingBinderClassification .. => "internal.binderClassification"
      diagnostic code "internal source/provenance alignment failure"
        ((failure.source?.map (·.span)).getD fallback)

private def unificationData (cause : UnifyError) : String × String :=
  let types := match cause with
    | .mismatch actual expected => [actual, expected]
    | .rigidVariable variableId other => [.fvar variableId, other]
    | .occursCheck variableId within => [.fvar variableId, within]
    | .arityMismatch left right => left ++ right
  let context : HMDisplay.Context := { freeIds := (types.flatMap Ty.freeVars).eraseDups }
  let pretty := HMDisplay.pretty context
  match cause with
  | .mismatch actual expected => ("type.mismatch", s!"expected {pretty expected}, got {pretty actual}")
  | .rigidVariable variableId other => ("type.rigidVariable", s!"expected {pretty (.fvar variableId)}, got {pretty other}")
  | .occursCheck variableId within => ("type.infiniteType", s!"infinite type: {pretty (.fvar variableId)} would have to equal {pretty within}")
  | .arityMismatch .. => ("type.constructorArity", "type constructors have incompatible numbers of arguments")

private def annotationData : AnnotationError → String × String
  | .unification cause =>
      let (code, message) := unificationData cause
      (if code == "type.infiniteType" then code else "type.annotationMismatch", message)
  | .invalidBoundVariables .. => ("type.invalidAnnotation", "type annotation contains an unbound type variable")
  | .outOfScopeVariables .. => ("type.outOfScope", "type annotation refers to variables outside its scope")
  | .expectedMonotype | .expectedSignature => ("internal.annotationMode", "internal annotation checking mode mismatch")

private def effectivePath (error : InferError) : CorePath :=
  match error.reason with
  | .recursiveShape members shapeIndex _ =>
      (members[shapeIndex]?.map fun member => error.path ++ [.letRecRhs member]).getD error.path
  | .invalidRecursiveSignatures members =>
      (members.head?.map fun member => error.path ++ [.letRecRhs member]).getD error.path
  | _ => error.path

private def ownerDepth (path : CorePath) : CoreBinderSite → Option Nat
  | .letIn basePath =>
      if (basePath ++ [CoreStep.letRhs]).isPrefixOf path then some (basePath.length + 1) else none
  | .letRec basePath member =>
      if (basePath ++ [CoreStep.letRecRhs member]).isPrefixOf path then some (basePath.length + 1) else none
  | _ => none

private def bindingOwner (p : Surface.Program) (binders : List BinderSpan) (tree : SpannedExpr)
    (lowered : InputLowered) (path : CorePath) : Option String :=
  let locations := HMArtifacts.collect binders p.term (identify tree)
  let candidates := lowered.binderTargets.flatMap fun (surface, target) =>
    let name := (locations.binders.find? (fun binder => binder.site == surface)).map (·.name)
    match target, name with
    | .present sites, some name => sites.filterMap fun site => (ownerDepth path site).map (·, name)
    | _, _ => []
  (candidates.foldl (fun best candidate =>
    match best with
    | none => some candidate
    | some previous => if previous.1 < candidate.1 then some candidate else best) none).map (·.2)

private def originSpan (lowered : InputLowered) (path : CorePath) : Option Span :=
  ((List.range (path.length + 1)).reverse.filterMap fun length =>
    (lowered.coreOrigins.find? (fun entry => entry.1 == path.take length)).map (·.2.source.span)).head?

private def mismatchMessage (owner : Option String) (message : String) : String :=
  if message.startsWith "infinite type:" then message else
  let target := owner.map fun name =>
    if Surface.internalBindingName (.mk name) then "pattern binding" else "`" ++ name ++ "`"
  "type mismatch" ++ (target.map (" in " ++ ·)).getD "" ++ ": " ++ message

def inferenceDiag (error : InferError) (lowered : InputLowered) (p : Surface.Program)
    (sp : SpannedProgram) (binders : List BinderSpan) (tree : SpannedExpr) : HoverDiag :=
  let constraint := match error.reason with
    | .unification (.mismatch a b) | .recursiveShape _ _ (.mismatch a b)
    | .application _ _ _ (.mismatch a b) | .annotation (.unification (.mismatch a b)) => some (a, b)
    | _ => none
  let report :=
    match TypeDiagnostics.explain error lowered with
    | some (reason, span) => diagnostic reason.code reason.message span
    | none =>
      let path := effectivePath error
      let span := (originSpan lowered path).getD sp.body.span
      let owner := bindingOwner p binders tree lowered path
      let (code, message) := match error.reason with
        | .application fn arg names cause =>
            let reason := (TypeDiagnostics.applicationError path fn arg names cause).reason
            (reason.code, reason.message)
        | .annotation cause =>
            let (code, message) := annotationData cause
            (code, match cause with | .unification _ => mismatchMessage owner message | _ => message)
        | .unification cause | .recursiveShape _ _ cause =>
            let (code, message) := unificationData cause
            (code, mismatchMessage owner message)
        | .unboundVariable _ => ("type.unboundVariable", "unbound variable")
        | .unknownConstructor name => ("type.unknownConstructor", "unknown constructor `" ++ ctorName name ++ "`")
        | .invalidBooleanConstructor name => ("type.invalidBooleanConstructor", "invalid boolean constructor `" ++ ctorName name ++ "`")
        | .emptyMatch => ("type.emptyMatch", "a match must have at least one branch")
        | .patternArity name expected actual => ("type.patternArity",
            s!"constructor `{ctorName name}` expects {expected} pattern arguments, got {actual}")
        | .outOfScopeVariables _ => ("type.outOfScope", "type annotation refers to variables outside its scope")
        | .escapingVariables _ => ("type.escapingVariable", "a declared type variable escapes its binding")
        | .invalidRecursiveSignatures _ => ("type.invalidAnnotation", "invalid recursive type annotation")
        | .recursivePrefix cause => match cause with
            | .notVariables _ => ("type.specializedTypeVariable", "a declared type variable must remain abstract")
            | .repeatedVariables _ => ("type.repeatedTypeVariable", "declared type variables must remain distinct")
            | .escapingVariables _ => ("type.escapingVariable", "a declared type variable escapes its binding")
        | .recursiveCompletion _ => ("internal.recursiveCompletion", "recursive binding did not finish checking")
        | .frontierViolation .. => ("internal.inferenceFrontier", "internal inference scope invariant failed")
        | .recursiveStateLength .. => ("internal.recursiveState", "internal recursive-state shape mismatch")
      diagnostic code message span
  { report with constraint? := constraint }

end FHM.Unverified.Diagnostics
