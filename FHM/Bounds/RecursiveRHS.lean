import FHM.Bounds.RecursiveWalk
import FHM.Bounds.ScopedDeclaration

/-! # Universal count certificates from checked recursive RHS artifacts

Certificates remain conditional on the explicit recursive assumption environment.
All members must be certified together before a group can be introduced. This
component supplies the universal RHS/annotation/inclusion premises; it does not
accept a group, generalize HM at group exit or change the production launch.
-/

namespace FHM.Bounds.RecursiveRHS

open RecursiveTyping RecursiveContract CountSubstitution ScopedScheme

structure Certified (c : Declared) (env : List Binding) (rhs : Expr) (ann : Option PolyTy) where
  actual : BoundsTy
  shape : Synth.BoundsTy.toTy actual = c.hm
  typing : Derives (c.counts.quantified ++ c.counts.captures) [] c.counts.premises env rhs actual
  annotation : InterpretedAnnotation.BindingOK (c.counts.quantified ++ c.counts.captures)
    [] c.counts.premises ann actual
  inclusion : SemanticSub c.counts.premises actual c.counts.body
  noGroups : RecursiveCountTransport.NoGroups rhs
  monoCaptured : ∀ β, .mono β ∈ env → BoundsScoped c.counts.captures β
  recursiveFresh : ∀ d, .recursive d ∈ env → ∀ i ∈ d.counts.captures, i ∉ c.counts.quantified

structure Use {c env rhs ann} (cert : Certified c env rhs ann) {args caller}
    (inst : Instance c.counts args caller) where
  typing : Derives (c.counts.quantified ++ c.counts.captures) (c.counts.quantified.zip args)
    inst.premises env rhs (bounds (c.counts.quantified.zip args) cert.actual)
  annotation : InterpretedAnnotation.BindingOK (c.counts.quantified ++ c.counts.captures)
    (c.counts.quantified.zip args) inst.premises ann (bounds (c.counts.quantified.zip args) cert.actual)
  inclusion : SemanticSub inst.premises (bounds (c.counts.quantified.zip args) cert.actual) inst.bounds

def use {c env rhs ann} (cert : Certified c env rhs ann) {args caller}
    (inst : Instance c.counts args caller) : Use cert inst := by
  refine ⟨RecursiveCountTransport.universal_rhs cert.typing cert.noGroups
    cert.monoCaptured cert.recursiveFresh args caller inst, ?_, inst.subtype cert.inclusion⟩
  cases ann with
  | none => trivial
  | some σ =>
      exact ⟨cert.annotation.1, by
        simpa only [CountAlgebra.compose, List.map_nil, List.nil_append, Instance.premises] using
          InterpretedAnnotation.transport (c.counts.quantified.zip args) inst.finite cert.annotation.2⟩

private def environmentOK (c : Declared) : Binding → Bool
  | .mono β => boundsScopedBool c.counts.captures β
  | .recursive d => d.counts.captures.all (fun i => !c.counts.quantified.contains i)

private def checkAnnotation (ids : List Nat) (Δ : List Constraint)
    (ann : Option PolyTy) (actual : BoundsTy) :
    Except String (PLift (InterpretedAnnotation.BindingOK ids [] Δ ann actual)) := do
  match ann with
  | none => pure ⟨True.intro⟩
  | some σ =>
      if hσ : σ.paramCount = 0 then
        let demand ← InterpretedAnnotation.check ids [] ids Δ σ.body actual
        pure ⟨hσ, demand.down⟩
      else throw "bounds: fixed polymorphic recursive annotation opening unsupported"

structure Checked (c : Declared) (env : List Binding) where
  rhs : ScopedDeclaration.RHS
  typed : RecursiveWalk.Result (c.counts.quantified ++ c.counts.captures) []
    (c.counts.quantified ++ c.counts.captures) c.counts.premises env rhs.expr
  certificate : Certified c env rhs.expr.stripFound rhs.annotation

structure LocatedChecked (c : Declared) (env : List Binding) (rhs : ScopedDeclaration.RHS) where
  typed : RecursiveWalk.Result (c.counts.quantified ++ c.counts.captures) []
    (c.counts.quantified ++ c.counts.captures) c.counts.premises env rhs.expr
  certificate : Certified c env rhs.expr.stripFound rhs.annotation

/-- Check an already located RHS against its explicit count telescope. The
    group checker supplies children directly from its found root; standalone
    inspection below reconciles them through the exact Core site. -/
def checkLocated (schemes : BinderSchemeMap) (quantified : List Nat)
    (rhs : ScopedDeclaration.RHS) (c : Declared) (env : List Binding) :
    Except String (LocatedChecked c env rhs) := do
  unless quantified = c.counts.quantified do throw "bounds: recursive RHS telescope disagrees with declared assumption"
  let ids := c.counts.quantified ++ c.counts.captures
  let actual ← RecursiveWalk.walk ids [] ids c.counts.premises env rhs.path rhs.expr schemes
  let hm ← match BinderBridge.equalTy actual.hm c.hm with
    | none => throw "bounds: recursive RHS needs specialization to fixed HM monotype"
    | some h => pure h
  let annotation ← checkAnnotation ids c.counts.premises rhs.annotation actual.bounds
  let inclusion ← Typed.subtype c.counts.premises actual.bounds c.counts.body
  if he : env.all (environmentOK c) = true then
    let cert : Certified c env rhs.expr.stripFound rhs.annotation :=
      { actual := actual.bounds, shape := actual.shape.trans hm.down
        typing := actual.derivation, annotation := annotation.down, inclusion := inclusion.down
        noGroups := actual.noGroups
        monoCaptured := by
          intro β hβ
          exact boundsScopedBool_sound (List.all_eq_true.mp he _ hβ)
        recursiveFresh := by
          intro d hd i hi
          simpa [environmentOK, List.contains_iff_mem] using
            List.all_eq_true.mp (List.all_eq_true.mp he _ hd) i hi }
    pure ⟨actual, cert⟩
  else throw "bounds: recursive RHS environment violates capture or quantified-count freshness"

/-- The telescope is reconciled at the exact Core site. No quantified IDs are
    inferred from names or from a carried HM annotation. -/
def check (output : Expr) (schemes : BinderSchemeMap) (metadata : Scope.Metadata)
    (site : CoreBinderSite) (c : Declared) (env : List Binding) : Except String (Checked c env) := do
  unless metadata.problems.isEmpty do throw "bounds: unresolved recursive RHS count scope"
  let rhs ← ScopedDeclaration.locate output site
  let quantified ← ScopedDeclaration.telescope metadata site
  let checked ← checkLocated schemes quantified rhs c env
  pure ⟨rhs, checked.typed, checked.certificate⟩

#print axioms use
#print axioms check

end FHM.Bounds.RecursiveRHS
