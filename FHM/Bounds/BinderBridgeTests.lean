import FHM.Bounds.Found

namespace FHM.Bounds.BinderBridgeTests

open BinderBridge

private def identity : PolyTy := ⟨1, .arrow (.bvar 0) (.bvar 0)⟩
private def actual : BoundsTy := .arrow (.fvar 7) (.fvar 7)
private def captureScheme : PolyTy := ⟨1, .arrow (.fvar 65) (.bvar 0)⟩
private def scopedActual : BoundsTy := .arrow (.fvar 65) (.fvar 7)
private def n : Count := .var ⟨.rigid, 7⟩

private def isInstance (σ : PolyTy) (τ : Ty) : Bool :=
  match instantiate σ τ with | .ok _ => true | .error _ => false

private def isAbstract (σ : PolyTy) (β : BoundsTy) (captures : List Ty := []) : Bool :=
  match abstract σ β captures with | .ok _ => true | .error _ => false

private def atSiteOK (facts : BinderSchemeMap) (site : CoreBinderSite) (β : BoundsTy) : Bool :=
  match atSite facts site β [] with | .ok _ => true | .error _ => false

private def recovered : Bool :=
  match abstract identity actual [] with
  | .ok a => a.ids == [7] && (close a.ids actual).pretty == "a → a"
  | .error _ => false

private def captureRetained : Bool :=
  match abstract captureScheme scopedActual [.fvar 65] with
  | .ok a => match close a.ids scopedActual with
      | .arrow (.fvar 65) (.bvar 0) => true
      | _ => false
  | .error _ => false

private def countsRetained : Bool :=
  let β : BoundsTy := .list n n (.fvar 7)
  let σ : PolyTy := ⟨1, listTy (.bvar 0)⟩
  match abstract σ β [] with
  | .ok a => match close a.ids β with
      | .list lo hi (.bvar 0) => lo == n && hi == n
      | _ => false
  | .error _ => false

-- The exact instance theorem is available for a checked artifact bridge,
-- without trusting the proposal collector or rerunning HM inference.
example {σ β captures found} (binding : Abstraction σ β captures)
    (use : Instance σ found) (args : Nat → BoundsTy)
    (ha : ∀ i t, use.args[i]? = some t → Synth.BoundsTy.toTy (args i) = t) :
    Synth.BoundsTy.toTy (TypeSubstitution.combined [] args (close binding.ids β)) =
      found.eraseBounds := use_shape binding use [] args ha

private def cases : List (String × Bool) := [
  ("identity instance at Int", isInstance identity (.arrow (.prim .int) (.prim .int))),
  ("identity instance at List", isInstance identity (.arrow (listTy (.prim .int)) (listTy (.prim .int)))),
  ("repeated slot mismatch rejected", !isInstance identity (.arrow (.prim .int) (.prim .char))),
  ("free HM capture preserved at use", isInstance captureScheme (.arrow (.fvar 65) (.prim .int))),
  ("free HM capture mismatch rejected", !isInstance captureScheme (.arrow (.fvar 66) (.prim .int))),
  ("out-of-range slot rejected", !isInstance ⟨1, .bvar 1⟩ (.prim .int)),
  ("unused slot has explicit valid Unit witness", isInstance ⟨1, .prim .int⟩ (.prim .int)),
  ("bounds annotations do not affect HM instance", isInstance
    ⟨1, .bl (.solid (.lit 9)) (.solid (.lit 9)) (.bvar 0)⟩ (listTy (.prim .int))),
  ("arbitrary data arguments matched", isInstance
    ⟨1, .customTy ⟨"Pair"⟩ [.bvar 0, .bvar 0]⟩ (.customTy ⟨"Pair"⟩ [.prim .int, .prim .int])),
  ("data argument arity mismatch rejected", !isInstance
    ⟨1, .customTy ⟨"Pair"⟩ [.bvar 0, .bvar 0]⟩ (.customTy ⟨"Pair"⟩ [.prim .int])),
  ("generalized pool recovered from inferred slots", recovered),
  ("captured free HM variable is not abstracted", captureRetained),
  ("count identities are not abstracted as HM variables", countsRetained),
  ("generalized identity in environment rejected", !isAbstract identity actual [.fvar 7]),
  ("nested generalized identity in environment rejected", !isAbstract identity actual [listTy (.fvar 7)]),
  ("two slots aliasing one identity rejected", !isAbstract
    ⟨2, .arrow (.bvar 0) (.bvar 1)⟩ actual),
  ("constrained type is not a generalized identity", !isAbstract identity (.arrow (.prim .int) (.prim .int))),
  ("phantom slot is not an invented generalized identity", !isAbstract ⟨1, .prim .int⟩ (.prim .int)),
  ("enclosing bound-variable scope explicitly deferred", !isAbstract ⟨0, .bvar 0⟩ (.bvar 0)),
  ("monomorphic binder abstraction", isAbstract ⟨0, .prim .int⟩ (.prim .int)),
  ("inferred fact selected by exact Core site", atSiteOK [(.letIn [.lambdaBody], identity)]
    (.letIn [.lambdaBody]) actual),
  ("wrong Core site is not reconciled by type", !atSiteOK [(.letIn [.lambdaBody], identity)] (.letIn []) actual),
  ("duplicate inferred facts rejected", !atSiteOK [(.letIn [], identity), (.letIn [], identity)] (.letIn []) actual),
  ("compiler clones selected independently", atSiteOK
    [(.letIn [.appFun], identity), (.letIn [.appArg], identity)] (.letIn [.appArg]) actual)]

private def span : Surface.Span.Span := ⟨1, 1, 1, 80⟩
private def leaf : Surface.Span.SpannedExpr := .leaf span
private def ctors : CtorEnv := (elabDecls preludeDecls).getD []

private def artifact (e : Surface.Expr) (sp : Surface.Span.SpannedExpr) :
    Option SurfaceBridge.Provenance.TypedLowered := do
  let lower ← SurfaceBridge.Provenance.lowerWithProvenance ctors e sp
  SurfaceBridge.Provenance.inferWithProvenance ctors lower

private def monoArtifact : Option SurfaceBridge.Provenance.TypedLowered :=
  artifact (.letIn ⟨"x"⟩ [] [] none (.primLit (.int 1)) (.var ⟨"x"⟩))
    (.letIn span leaf leaf)

private def acceptsArtifact (typed : Option SurfaceBridge.Provenance.TypedLowered) : Bool :=
  match typed with
  | none => false
  | some typed => match Found.synthNodes typed with | .ok _ => true | .error _ => false

private def rejectsFacts (facts : BinderSchemeMap) (message : String) : Bool :=
  match monoArtifact with
  | none => false
  | some typed =>
      let damaged := { typed with inference := { typed.inference with binderSchemes := facts } }
      match Found.synthNodes damaged with | .error msg => msg == message | .ok _ => false

private def capturedArtifact : Option SurfaceBridge.Provenance.TypedLowered :=
  artifact (.lambda (.name ⟨"x"⟩) none
    (.letIn ⟨"alias"⟩ [] [] none (.var ⟨"x"⟩) (.var ⟨"alias"⟩)))
    (.lambda span (.letIn span leaf leaf))

private def withPolyBody (body : Surface.Expr) (bodySpan : Surface.Span.SpannedExpr) :
    Option SurfaceBridge.Provenance.TypedLowered :=
  artifact (.letIn ⟨"id"⟩ [] [] none
    (.lambda (.name ⟨"x"⟩) none (.var ⟨"x"⟩)) body)
    (.letIn span (.lambda span leaf) bodySpan)

private def polyArtifact (use : Bool) : Option SurfaceBridge.Provenance.TypedLowered :=
  let body := if use then Surface.Expr.app (.var ⟨"id"⟩) (.primLit (.int 1))
    else .primLit (.int 1)
  let bodySpan := if use then Surface.Span.SpannedExpr.app span leaf leaf else leaf
  withPolyBody body bodySpan

private def polyUseDeferred : Bool :=
  match polyArtifact true with
  | none => false
  | some typed => match Found.synthNodes typed with
      | .error msg => msg == "bounds: polymorphic binding use needs a generalized RHS bounds derivation"
      | .ok _ => false

private def annotatedArtifact : Option SurfaceBridge.Provenance.TypedLowered :=
  artifact (.letIn ⟨"x"⟩ [] [] (some ⟨[], .prim .int⟩) (.primLit (.int 1)) (.var ⟨"x"⟩))
    (.letIn span leaf leaf)

private def nestedPolyUseDeferred : Bool :=
  let typed := withPolyBody
    (.lambda (.name ⟨"local"⟩) none (.app (.var ⟨"id"⟩) (.primLit (.int 1))))
    (.lambda span (.app span leaf leaf))
  match typed with
  | none => false
  | some typed => match Found.synthNodes typed with
      | .error msg => msg == "bounds: polymorphic binding use needs a generalized RHS bounds derivation"
      | .ok _ => false

private def sourceAnnotationCaptureRejected : Bool :=
  let τ : Ty := .arrow (.fvar 7) (.fvar 7)
  let e : Expr := .found (.prim .int) (.letIn none
    (.found τ (.lambda (some (.fvar 7)) (.found (.fvar 7) (.var 0))))
    (.found (.prim .int) (.primLit (.int 1))))
  match Typed.walk [] [] [] e (some [(.letIn [], identity)]) with
  | .error msg => msg == "bounds: generalized HM identity escapes into captured type interface"
  | .ok _ => false

private def artifactCases : List (String × Bool) := [
  ("actual inferred monomorphic let map checked", acceptsArtifact monoArtifact),
  ("missing inferred fact rejects typed artifact", rejectsFacts []
    "bounds: missing inferred binder scheme at Core site"),
  ("duplicate inferred fact rejects typed artifact", rejectsFacts
    [(.letIn [], ⟨0, .prim .int⟩), (.letIn [], ⟨0, .prim .int⟩)]
    "bounds: duplicate inferred binder schemes at Core site"),
  ("wrong-path inferred fact rejects typed artifact", rejectsFacts [(.letIn [.lambdaBody], ⟨0, .prim .int⟩)]
    "bounds: missing inferred binder scheme at Core site"),
  ("wrong-type inferred fact rejects typed artifact", rejectsFacts [(.letIn [], ⟨0, .prim .char⟩)]
    "bounds: found type is not an instance of inferred binder scheme"),
  ("invented quantifier rejects typed artifact", rejectsFacts [(.letIn [], ⟨1, .bvar 0⟩)]
    "bounds: inferred binder slot is not a generalized free identity"),
  ("captured lambda parameter remains monomorphic", acceptsArtifact capturedArtifact),
  ("unused poly binder has certified abstraction", acceptsArtifact (polyArtifact false)),
  ("poly use remains deferred rather than assumed valid", polyUseDeferred),
  ("annotated binder need not invent an inferred fact", acceptsArtifact annotatedArtifact),
  ("lambda parameter does not inherit poly binding restriction", acceptsArtifact
    (withPolyBody (.lambda (.name ⟨"local"⟩) none (.var ⟨"local"⟩)) (.lambda span leaf))),
  ("outer poly binding restriction shifts under lambda", nestedPolyUseDeferred),
  ("shadowing monomorphic let does not inherit poly restriction", acceptsArtifact
    (withPolyBody (.letIn ⟨"id"⟩ [] [] none (.primLit (.int 2)) (.var ⟨"id"⟩))
      (.letIn span leaf leaf))),
  ("source annotation identity cannot be generalized", sourceAnnotationCaptureRejected)]

def main : IO Unit := do
  for (name, ok) in cases ++ artifactCases do
    IO.println s!"{if ok then "PASS" else "FAIL"}: {name}"
    unless ok do throw (IO.userError s!"binder bridge regression: {name}")

#eval main

end FHM.Bounds.BinderBridgeTests
