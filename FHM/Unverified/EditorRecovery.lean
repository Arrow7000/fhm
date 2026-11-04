import FHM.Unverified.Diagnostics
import FHM.Unverified.DeclarationRecovery
import FHM.Unverified.RecoveryArtifacts
import FHM.Unverified.ExpressionRecovery

/-! Editor-only recovery at top-level dependency boundaries. Successful groups
export native closed schemes. Rejected implementations with complete valid
annotations provide explicitly declared editor interfaces; residual components
can check conditionally against them. Other failed bindings remain unavailable.
No recovery result certifies an executable program. -/

namespace FHM.Unverified.EditorRecovery
open SurfaceBridge SurfaceBridge.Provenance Surface.Span RecoveryDependencies

abbrev CheckedSlice := RecoveryArtifacts.CheckedSlice

structure Blocked where
  names : List ValName
  causes : List Cause
  deriving Repr

abbrev UnavailableSlice := RecoveryArtifacts.UnavailableSlice

structure Result where
  checked : List CheckedSlice := []
  diagnostics : List HoverDiag := []
  blocked : List Blocked := []
  unavailable : List UnavailableSlice := []
  unavailableDeclarations : List DeclarationRecovery.Unavailable := []
  declared : List RecoveryArtifacts.DeclaredInterface := []

private def internalError (message : String) (scope : Span) : HoverDiag :=
  { diagAtSpan message (some scope) with code? := some "internal.recoveryArtifact" }

/-- Keep only the authored region for this slice, alongside shared declarations.
Synthetic wrapper spans cover the program so checked definitions retain their
lexical scope, but must not make unrelated value parameters look like type binders. -/
private def sliceSpans (sp : SpannedProgram) (regions : List Span) (span : Span) : Bool :=
  (regions ++ sp.declSpans).any (HMArtifacts.inside span ·)

private def groupSpanned (sp : SpannedProgram) (group : List Surface.Binding)
    (rhss : List SpannedExpr) (scope : Span) : SpannedProgram :=
  let headers := sp.bindingHeaders.filter fun (name, _) => group.any fun binding =>
    binding.name == .mk name
  let regions := headers.map (·.2) ++ rhss.map (·.span)
  { sp with
    groups := [rhss]
    body := .generated (.leaf scope)
    bindingHeaders := headers
    references := sp.references.filter fun ref => sliceSpans sp regions ref.span }

private def sliceBinders (binders : List BinderSpan) (sp : SpannedProgram)
    (regions : List Span) : List BinderSpan :=
  binders.filter fun binder => sliceSpans sp regions binder.span

private def checkSlice (ctors : CtorEnv) (names : List ValName) (schemes : List PolyTy)
    (program : Surface.Program) (spanned : SpannedProgram) (binders : List BinderSpan)
    (scope : Span) (isBody : Bool := false)
    (assumed : List (ValName × List RecoveryArtifacts.InterfaceRef) := []) : Except HoverDiag CheckedSlice := do
  if Surface.PartialSyntax.hasHole program.term then
    throw (internalError "internal partial syntax reached whole-group checker" scope)
  let tree ← (HMArtifacts.programSpannedResult program spanned scope).mapError
    (fun error => Diagnostics.provenanceDiag error program spanned binders scope)
  let identified := identify tree
  let lowered ← (lowerIdentifiedExprResult (kindEnvOfCtors ctors) [] names program.term identified).mapError
    (fun error => Diagnostics.provenanceDiag error program spanned binders scope)
  let lowered := { lowered with sourceNodes := identified.nodes }
  let typed ← (inferWithProvenanceInResult ⟨schemes, ctors⟩ lowered).mapError
    (fun error => Diagnostics.inferenceDiag error lowered program spanned binders tree)
  if !(typed.lowering.mapExpr Expr.erase).provenanceTotal ||
      !typed.nodeTypesTotal || !typed.sourceTypesTotal || !typed.patternBinderTypesTotal then
    .error (internalError "internal recovered provenance coverage failure" scope)
  else
    .ok ⟨program, spanned, binders, tree, typed, isBody, [], true,
      (RecoveryArtifacts.Context.assumptionsFor { assumed := assumed } (Surface.freeNames [] program.term))⟩

/-- Lexical artifacts describe unavailable hovers without supplying any type to
inference. They also preserve shadowing and definition navigation in rejected code. -/
private def unavailableSlice (program : Surface.Program) (spanned : SpannedProgram)
    (binders : List BinderSpan) (scope : Span) (causes : List Cause) :
    Except HoverDiag UnavailableSlice := do
  let tree ← (HMArtifacts.programSpannedResult program spanned scope).mapError
    (fun error => Diagnostics.provenanceDiag error program spanned binders scope)
  pure ⟨program, spanned, binders, tree, causes⟩

/-- Read actual group-exit schemes. Complete signatures are intentionally absent
from inferred scheme metadata; their validated lowered annotations are authoritative. -/
private def exports (group : List Surface.Binding) (typed : TypedLowered)
    (scope : Span) : Except HoverDiag (List PolyTy) := do
  let schemes ← group.zipIdx.mapM fun (_, member) => do
    let (declared, site) := match typed.input with
      | .letIn ann _ _ => (ann.recModeAnn, CoreBinderSite.letIn [])
      | .letRec bindings _ =>
          ((bindings[member]?).bind (fun binding => binding.ann.recModeAnn), .letRec [] member)
      | _ => (none, .letIn [])
    match declared.orElse (fun _ => (typed.inference.binderSchemes.find? (·.1 == site)).map (·.2)) with
    | some scheme => pure scheme
    | none => .error (internalError "internal recovery error: missing group export" scope)
  -- Top-level exports must be closed. Never carry a guessed or unresolved
  -- monotype across a recovery boundary, where a later group could constrain it.
  if schemes.all (fun scheme => scheme.body.freeVars.isEmpty) then pure schemes
  else .error (internalError "internal recovery error: open group export" scope)

private def causesFor (unavailable : List (ValName × List Cause)) (uses : List ValName) : List Cause :=
  (uses.flatMap fun name =>
    ((unavailable.find? (·.1 == name)).map (·.2)).getD []).eraseDups

private def addPartials (result : Result) (partialResult : ExpressionRecovery.State) : Result :=
  { result with
    checked := result.checked ++ partialResult.checked
    unavailable := result.unavailable ++ partialResult.unavailable
    diagnostics := result.diagnostics ++ partialResult.diagnostics
    declared := result.declared ++ partialResult.declared }

private def diagnosticSpan (diagnostic : HoverDiag) : Span :=
  ⟨diagnostic.line, diagnostic.col, diagnostic.endLine, diagnostic.endCol⟩

private def addFailure (result : Result) (diagnostic : HoverDiag) (partialResult : ExpressionRecovery.State) : Result :=
  addPartials result (ExpressionRecovery.withNativeFailure 0 diagnostic partialResult)

private def deduplicate (diagnostics : List HoverDiag) : List HoverDiag :=
  diagnostics.foldl (fun found diagnostic =>
    if found.any (fun prior => prior.code? == diagnostic.code? && prior.line == diagnostic.line && prior.col == diagnostic.col) then
      found.map (fun prior => if prior.code? == diagnostic.code? && prior.line == diagnostic.line && prior.col == diagnostic.col &&
        (diagnostic.endLine < prior.endLine || (diagnostic.endLine == prior.endLine && diagnostic.endCol < prior.endCol)) then diagnostic else prior)
    else found ++ [diagnostic]) []

/-- Check each group once in dependency order. Only the editor consumes this
result; successful slices do not certify the rejected whole program. -/
def check (program : Surface.Program) (spanned : SpannedProgram)
    (binders : List BinderSpan) (scope : Span) (seed : Seed := {}) : Except HoverDiag Result := do
  let declarations ← DeclarationRecovery.check program spanned binders scope seed
  let ctors := declarations.ctors
  let program := { program with decls := declarations.declarations }
  let spanned := { spanned with declSpans := declarations.spans }
  -- Validate the entire sidecar shape before zipping; no group can disappear.
  let wholeTree ← (HMArtifacts.programSpannedResult program spanned scope).mapError
    (fun error => Diagnostics.provenanceDiag error program spanned binders scope)
  let mut result : Result := {
    diagnostics := declarations.diagnostics
    unavailableDeclarations := declarations.unavailable }
  if !declarations.unavailable.isEmpty then
    let declarationProgram := { program with groups := [], body := .primLit .unit }
    let declarationSpanned := { spanned with
      groups := []
      body := .generated (.leaf scope)
      bindingHeaders := []
      references := spanned.references.filter fun ref => spanned.declSpans.any (HMArtifacts.inside ref.span ·) }
    let declarationBinders := binders.filter fun binder => spanned.declSpans.any (HMArtifacts.inside binder.span ·)
    let slice ← checkSlice ctors [] [] declarationProgram declarationSpanned declarationBinders scope
    result := { result with checked := [slice] }
  let source : RecoveryArtifacts.Source := {
    program := program
    spanned := spanned
    binders := binders
    scope := scope
    declarations := declarations
    valueBinderSpans := (HMArtifacts.collect binders program.term (identify wholeTree)).binders.map (·.span)
    quarantined := seed.values.map (·.1) }
  let mut names : List ValName := []
  let mut schemes : List PolyTy := []
  let mut unavailable : List (ValName × List Cause) := seed.values
  let mut assumed : List (ValName × List RecoveryArtifacts.InterfaceRef) := []
  for (group, rhss) in program.groups.zip spanned.groups do
    if !group.isEmpty then
      let groupNames := group.map (·.name)
      let uses := Surface.freeNamesBinds groupNames group
      let causes := (causesFor unavailable (groupNames ++ uses) ++
        DeclarationRecovery.causesFor declarations (RecoveryDependencies.bindings group)).eraseDups
      let localProgram := { program with groups := [group], body := .primLit .unit }
      let localSpanned := groupSpanned spanned group rhss scope
      let regions := localSpanned.bindingHeaders.map (·.2) ++ rhss.map (·.span)
      let localBinders := sliceBinders binders spanned regions
      if !causes.isEmpty then
        result := { result with blocked := result.blocked ++ [⟨groupNames, causes⟩] }
        let slice ← unavailableSlice localProgram localSpanned localBinders scope causes
        result := { result with unavailable := result.unavailable ++ [slice] }
        let partialResult := ExpressionRecovery.group source
          { names, schemes, unavailable, assumed } group rhss causes
        if !partialResult.context.schemes.all (fun scheme => scheme.body.freeVars.isEmpty) then
          throw (internalError "internal open interface export" scope)
        result := addPartials result partialResult
        names := partialResult.context.names
        schemes := partialResult.context.schemes
        unavailable := partialResult.context.unavailable
        assumed := partialResult.context.assumed
      else
        match checkSlice ctors names schemes localProgram localSpanned localBinders scope false assumed with
        | .error diagnostic =>
            let slice ← unavailableSlice localProgram localSpanned localBinders scope (groupNames.map Cause.binding)
            result := { result with unavailable := result.unavailable ++ [slice] }
            let partialResult := ExpressionRecovery.group source
              { names, schemes, unavailable, assumed } group rhss (groupNames.map Cause.binding)
            if !partialResult.context.schemes.all (fun scheme => scheme.body.freeVars.isEmpty) then
              throw (internalError "internal open interface export" scope)
            result := addFailure result diagnostic partialResult
            names := partialResult.context.names
            schemes := partialResult.context.schemes
            unavailable := partialResult.context.unavailable
            assumed := partialResult.context.assumed
        | .ok slice =>
            let exported ← exports group slice.typed scope
            names := groupNames ++ names
            schemes := exported ++ schemes
            if !slice.assumptions.isEmpty then assumed := groupNames.map (·, slice.assumptions) ++ assumed
            result := { result with checked := result.checked ++ [slice] }
  let bodyCauses := (seed.body ++ causesFor unavailable (Surface.freeNames [] program.body) ++
    DeclarationRecovery.causesFor declarations (expression program.body)).eraseDups
  let localProgram := { program with groups := [] }
  let localSpanned := { spanned with
    groups := []
    bindingHeaders := []
    references := spanned.references.filter fun ref => sliceSpans spanned [spanned.body.span] ref.span }
  let localBinders := sliceBinders binders spanned [spanned.body.span]
  if !bodyCauses.isEmpty then
    let slice ← unavailableSlice localProgram localSpanned localBinders scope bodyCauses
    result := { result with
      blocked := result.blocked ++ [⟨[], bodyCauses⟩]
      unavailable := result.unavailable ++ [slice] }
    if seed.body.isEmpty then
      result := addPartials result (ExpressionRecovery.expression source { names, schemes, unavailable, assumed } program.body spanned.body)
  else
    match checkSlice ctors names schemes localProgram localSpanned localBinders scope true assumed with
    | .error diagnostic =>
        let slice ← unavailableSlice localProgram localSpanned localBinders scope []
        result := { result with unavailable := result.unavailable ++ [slice] }
        result := addFailure result diagnostic (ExpressionRecovery.expression source { names, schemes, unavailable, assumed } program.body spanned.body)
    | .ok slice => result := { result with checked := result.checked ++ [slice] }
  let diagnostics := deduplicate result.diagnostics
  let diagnostics := diagnostics.filter fun diagnostic =>
    diagnostic.code? != some "type.escapingVariable" || !diagnostics.any fun child =>
      child.code? == diagnostic.code? && diagnosticSpan child != diagnosticSpan diagnostic &&
        HMArtifacts.inside (diagnosticSpan child) (diagnosticSpan diagnostic)
  let blocked := result.blocked.filterMap fun entry =>
    if entry.names.isEmpty then some entry else
      let names := entry.names.filter fun name => unavailable.any (·.1 == name)
      if names.isEmpty then none else some { entry with names }
  pure { result with diagnostics, blocked }

end FHM.Unverified.EditorRecovery
