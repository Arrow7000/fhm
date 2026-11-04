import FHM.Unverified.DeclarationRecovery

/-! Contextual native checks and editor artifact containers shared by recovery
passes. No value in this module certifies a rejected whole program. -/
namespace FHM.Unverified.RecoveryArtifacts
open SurfaceBridge SurfaceBridge.Provenance Surface.Span RecoveryDependencies

structure CheckedSlice where
  program : Surface.Program
  spanned : SpannedProgram
  binders : List BinderSpan
  tree : SpannedExpr
  typed : TypedLowered
  isBody : Bool := false
  outerBinders : List HMArtifacts.BinderLocation := []
  checkCoverage : Bool := true

structure UnavailableSlice where
  program : Surface.Program
  spanned : SpannedProgram
  binders : List BinderSpan
  tree : SpannedExpr
  causes : List Cause

structure Context where
  names : List ValName := []
  schemes : List PolyTy := []
  unavailable : List (ValName × List Cause) := []
  tvs : List ValName := []
  written : List Nat := []
  protectedVars : List Nat := []
  frontier : Nat := 0
  lexical : List HMArtifacts.BinderLocation := []
  /-- Rigid variables that must not enter the saved surrounding environments. -/
  boundaries : List (List Nat × List PolyTy) := []

def Context.onSubst (context : Context) (subst : Subst) : Context :=
  { context with
    schemes := context.schemes.map subst.onPolyTy
    boundaries := context.boundaries.map (fun (written, env) => (written, env.map subst.onPolyTy)) }

def Context.escaping (context : Context) (subst : Subst) : List Nat :=
  (context.boundaries.flatMap fun (written, env) => written.filter fun name =>
    env.any (fun scheme => (subst.onPolyTy scheme).body.freeVars.contains name)).eraseDups

def Context.causesFor (context : Context) (uses : List ValName) : List Cause :=
  (uses.flatMap (fun name => ((context.unavailable.find? (·.1 == name)).map (·.2)).getD [])).eraseDups

/-- A lexical binder shadows both available and unavailable outer names. -/
def Context.withBindings (context : Context) (names : List ValName) (schemes : List PolyTy) : Context :=
  { context with
    names := names ++ context.names
    schemes := schemes ++ context.schemes
    unavailable := context.unavailable.filter (fun (name, _) => !names.contains name) }

def Context.withUnavailable (context : Context) (names : List ValName) (causes : List Cause) : Context :=
  let available := (context.names.zip context.schemes).filter (fun (name, _) => !names.contains name)
  { context with
    names := available.map (·.1)
    schemes := available.map (·.2)
    unavailable := names.map (·, causes) ++ context.unavailable }

structure Source where
  program : Surface.Program
  spanned : SpannedProgram
  binders : List BinderSpan
  scope : Span
  declarations : DeclarationRecovery.Result
  valueBinderSpans : List Span := []

private def insideAny (regions : List Span) (span : Span) : Bool := regions.any (HMArtifacts.inside span ·)

def Source.slice (source : Source) (program : Surface.Program) (spanned : SpannedProgram)
    (regions : List Span) : Source :=
  let regions := regions ++ spanned.declSpans
  let represented := (HMArtifacts.programSpannedResult program spanned source.scope).toOption.map fun tree =>
    (HMArtifacts.collect source.binders program.term (identify tree)).binders.map (·.span)
  { source with
    program
    spanned := { spanned with references := spanned.references.filter (fun ref => insideAny regions ref.span) }
    binders := source.binders.filter (fun binder => insideAny regions binder.span &&
      (!source.valueBinderSpans.contains binder.span ||
        (represented.map (·.contains binder.span)).getD true)) }

def Source.expression (source : Source) (expr : Surface.Expr) (tree : SpannedExpr) : Source :=
  source.slice { source.program with groups := [], body := expr }
    { source.spanned with groups := [], body := tree, bindingHeaders := [] } [tree.span]

def Source.group (source : Source) (bindings : List Surface.Binding) (rhss : List SpannedExpr)
    (scope : Span) : Source :=
  let headers := (bindings.zip rhss).map fun (binding, rhs) =>
    let name := match binding.name with | .mk name => name
    let authored := (source.spanned.bindingHeaders.find? (fun header => header.1 == name && HMArtifacts.inside header.2 scope)).map (·.2)
    let binder := (source.binders.filter fun binder => binder.name == name && binder.kind == .val &&
      HMArtifacts.inside binder.span scope && HMArtifacts.before binder.span rhs.span).getLast?
    let start := (binder.map (·.span)).getD scope
    let fallback : Span := ⟨start.startLine, start.startCol, rhs.span.startLine, rhs.span.startCol⟩
    (name, authored.getD fallback)
  source.slice { source.program with groups := [bindings], body := .primLit .unit }
    { source.spanned with groups := [rhss], body := .generated (.leaf scope), bindingHeaders := headers }
    (headers.map (·.2) ++ rhss.map (·.span))

def unavailable (source : Source) (causes : List Cause) : Except HoverDiag UnavailableSlice := do
  let tree ← (HMArtifacts.programSpannedResult source.program source.spanned source.scope).mapError
    (fun error => Diagnostics.provenanceDiag error source.program source.spanned source.binders source.scope)
  pure ⟨source.program, source.spanned, source.binders, tree, causes⟩

/-- The source is lowered without changing annotations. Only enclosing authored
forall variables are opened, as they are in the canonical enclosing checker. -/
def check (context : Context) (source : Source) (ctors : CtorEnv) (isBody : Bool := false) :
    Except HoverDiag CheckedSlice := do
  let tree ← (HMArtifacts.programSpannedResult source.program source.spanned source.scope).mapError
    (fun error => Diagnostics.provenanceDiag error source.program source.spanned source.binders source.scope)
  let identified := identify tree
  let lowered ← (lowerIdentifiedExprResult (kindEnvOfCtors ctors) context.tvs context.names
    source.program.term identified).mapError
    (fun error => Diagnostics.provenanceDiag error source.program source.spanned source.binders source.scope)
  let lowered := { lowered.mapExpr (fun expr => expr.openSourceTyVars context.written) with sourceNodes := identified.nodes }
  let typed ← (inferWithProvenanceAtResult context.protectedVars context.frontier ⟨context.schemes, ctors⟩ lowered).mapError
    (fun error => Diagnostics.inferenceDiag error lowered source.program source.spanned source.binders tree)
  let escaped := context.escaping typed.inference.subst
  if !escaped.isEmpty then
    throw (Diagnostics.inferenceDiag (InferError.root (.escapingVariables escaped)) lowered
      source.program source.spanned source.binders tree)
  let aliases := context.written.zip (context.tvs.map (fun | .mk name => name))
  let typed := { typed with outerAliases := aliases }
  if !(typed.lowering.mapExpr Expr.erase).provenanceTotal ||
      !typed.nodeTypesTotal || !typed.sourceTypesTotal || !typed.patternBinderTypesTotal then
    .error { diagAtSpan "internal recovered provenance coverage failure" (some source.scope) with
      code? := some "internal.recoveryArtifact" }
  else pure ⟨source.program, source.spanned, source.binders, tree, typed, isBody, context.lexical, true⟩

/-- Read validated native group-exit schemes, including complete signatures.
Nested schemes may mention their real monomorphic or rigid outer context. -/
def groupSchemes (group : List Surface.Binding) (typed : TypedLowered) : Option (List PolyTy) :=
  group.zipIdx.mapM fun (_, member) =>
    let (declared, site) := match typed.input with
      | .letIn ann _ _ => (ann.recModeAnn, CoreBinderSite.letIn [])
      | .letRec bindings _ =>
          ((bindings[member]?).bind (fun binding => binding.ann.recModeAnn), .letRec [] member)
      | _ => (none, .letIn [])
    declared.orElse (fun _ => (typed.inference.binderSchemes.find? (·.1 == site)).map (·.2))

end FHM.Unverified.RecoveryArtifacts
