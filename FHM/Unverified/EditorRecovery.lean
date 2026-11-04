import FHM.Unverified.Diagnostics
import FHM.Unverified.DeclarationRecovery

/-! Editor-only recovery at top-level SCC boundaries. Each group uses the
canonical native workers and only closed schemes exported by checked groups.
Failed groups export nothing. Their transitive dependants are skipped, without
inventing types or emitting cascades. This module produces editor artifacts,
never a checked executable program. Declaration groups are recovered independently; parsing remains atomic. -/

namespace FHM.Unverified.EditorRecovery
open SurfaceBridge SurfaceBridge.Provenance Surface.Span RecoveryDependencies

structure CheckedSlice where
  program : Surface.Program
  spanned : SpannedProgram
  binders : List BinderSpan
  tree : SpannedExpr
  typed : TypedLowered
  isBody : Bool := false

structure Blocked where
  names : List ValName
  causes : List Cause
  deriving Repr

structure UnavailableSlice where
  program : Surface.Program
  spanned : SpannedProgram
  binders : List BinderSpan
  tree : SpannedExpr
  causes : List Cause

structure Result where
  checked : List CheckedSlice := []
  diagnostics : List HoverDiag := []
  blocked : List Blocked := []
  unavailable : List UnavailableSlice := []
  unavailableDeclarations : List DeclarationRecovery.Unavailable := []

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
    (scope : Span) (isBody : Bool := false) : Except HoverDiag CheckedSlice := do
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
    .ok ⟨program, spanned, binders, tree, typed, isBody⟩

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

/-- Check each group once in dependency order. Only the editor consumes this
result; successful slices do not certify the rejected whole program. -/
def check (program : Surface.Program) (spanned : SpannedProgram)
    (binders : List BinderSpan) (scope : Span) (seed : Seed := {}) : Except HoverDiag Result := do
  let declarations ← DeclarationRecovery.check program spanned binders scope seed
  let ctors := declarations.ctors
  let program := { program with decls := declarations.declarations }
  let spanned := { spanned with declSpans := declarations.spans }
  -- Validate the entire sidecar shape before zipping; no group can disappear.
  let _ ← (HMArtifacts.programSpannedResult program spanned scope).mapError
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
  let mut names : List ValName := []
  let mut schemes : List PolyTy := []
  let mut unavailable : List (ValName × List Cause) := seed.values
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
        unavailable := groupNames.map (·, causes) ++ unavailable
      else
        match checkSlice ctors names schemes localProgram localSpanned localBinders scope with
        | .error diagnostic =>
            result := { result with diagnostics := result.diagnostics ++ [diagnostic] }
            let slice ← unavailableSlice localProgram localSpanned localBinders scope (groupNames.map Cause.binding)
            result := { result with unavailable := result.unavailable ++ [slice] }
            unavailable := groupNames.map (fun name => (name, groupNames.map Cause.binding)) ++ unavailable
        | .ok slice =>
            let exported ← exports group slice.typed scope
            names := groupNames ++ names
            schemes := exported ++ schemes
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
  else
    match checkSlice ctors names schemes localProgram localSpanned localBinders scope true with
    | .error diagnostic =>
        let slice ← unavailableSlice localProgram localSpanned localBinders scope []
        result := { result with
          diagnostics := result.diagnostics ++ [diagnostic]
          unavailable := result.unavailable ++ [slice] }
    | .ok slice => result := { result with checked := result.checked ++ [slice] }
  pure result

end FHM.Unverified.EditorRecovery
