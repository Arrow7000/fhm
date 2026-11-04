import FHM.Unverified.Diagnostics
import FHM.Unverified.RecoveryDependencies

/-! Recover declaration environments by dependency SCC. Each accepted group is
lowered and elaborated by the native workers. Conflicting definitions belong
to one rejection unit; no arbitrary duplicate is kept as a usable declaration. -/
namespace FHM.Unverified.DeclarationRecovery
open SurfaceBridge Surface.Span RecoveryDependencies

structure Unavailable where
  declaration : Surface.DataDecl
  span : Span
  causes : List Cause

structure Result where
  declarations : List Surface.DataDecl := []
  spans : List Span := []
  ctors : CtorEnv
  diagnostics : List HoverDiag := []
  unavailableTypes : List (TyName × List Cause) := []
  unavailableConstructors : List (CtorName × List Cause) := []
  unavailable : List Unavailable := []

def causesFor (result : Result) (uses : Uses) : List Cause :=
  ((uses.types.flatMap fun name =>
      ((result.unavailableTypes.find? (·.1 == name)).map (·.2)).getD []) ++
    uses.constructors.flatMap (fun name =>
      ((result.unavailableConstructors.find? (·.1 == name)).map (·.2)).getD [])).eraseDups

private def depends (left right : Surface.DataDecl × Span) : Bool :=
  left.1.name == right.1.name ||
  (left.1.ctors.any fun ctor => right.1.ctors.any (·.1 == ctor.1)) ||
  (declaration left.1).contains right.1.name

private def withhold (result : Result) (group : List (Surface.DataDecl × Span))
    (causes : List Cause) : Result :=
  { result with
    unavailableTypes := group.map (fun (decl, _) => (decl.name, causes)) ++ result.unavailableTypes
    unavailableConstructors := group.flatMap (fun (decl, _) => decl.ctors.map (·.1, causes)) ++
      result.unavailableConstructors
    unavailable := result.unavailable ++ group.map (fun (decl, span) => ⟨decl, span, causes⟩) }

/-- Declaration recovery does not manufacture kinds or constructor signatures.
Unavailable names suppress their dependants before native lowering. -/
def check (program : Surface.Program) (spanned : SpannedProgram) (binders : List BinderSpan)
    (scope : Span) : Except HoverDiag Result := do
  if program.decls.length != spanned.declSpans.length then
    .error { diagAtSpan "internal declaration provenance shape mismatch" (some scope) with
      code? := some "internal.declarationProvenance" }
  else do
    let initial ← (elabDeclsResult preludeDecls).mapError
      (fun error => Diagnostics.declarationDiag error program spanned binders)
    let mut result : Result := { ctors := initial }
    let mut core : List DataDecl := []
    for component in components (program.decls.zip spanned.declSpans) depends do
      let group := component.mergeSort (fun a b => a.2.startLine < b.2.startLine ||
        (a.2.startLine == b.2.startLine && a.2.startCol ≤ b.2.startCol))
      let surface := group.map (·.1)
      let uses : Uses := ⟨surface.flatMap declaration, []⟩
      let causes := causesFor result uses
      if !causes.isEmpty then result := withhold result group causes
      else
        match lowerDataDeclsInResult (DataDecls.kindEnv (preludeDecls ++ core)) surface with
        | .error error =>
            let diagnostic := Diagnostics.loweringDiag error program spanned binders scope
            result := withhold { result with diagnostics := result.diagnostics ++ [diagnostic] }
              group (surface.map (Cause.declaration ∘ (·.name))).eraseDups
        | .ok lowered =>
            match elabDeclsResult (preludeDecls ++ core ++ lowered) with
            | .error error =>
                let diagnostic := Diagnostics.declarationDiag error program spanned binders
                result := withhold { result with diagnostics := result.diagnostics ++ [diagnostic] }
                  group (surface.map (Cause.declaration ∘ (·.name))).eraseDups
            | .ok ctors =>
                core := core ++ lowered
                result := { result with
                  declarations := result.declarations ++ surface
                  spans := result.spans ++ group.map (·.2)
                  ctors }
    pure result

end FHM.Unverified.DeclarationRecovery
