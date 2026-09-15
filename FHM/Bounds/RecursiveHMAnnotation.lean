import FHM.Bounds.HMFoundView

/-! Executable source-annotation checks for the interpreted recursive RHS
judgement. Counts in source syntax are interpreted BEFORE full HM replacements
are inserted. Source scope, final caller scope and semantic inclusion are
independent obligations; no expression or annotation is rewritten. -/

namespace FHM.Bounds.RecursiveHMAnnotation

open CountSubstitution SchemeSpecialization ScopedScheme

abbrev ScopedDemand := ScopedHMAnnotation.Demand

abbrev decodeScoped := ScopedHMAnnotation.decode
abbrev checkScoped := ScopedHMAnnotation.check

structure ScopedParameter (types slots : Nat → BoundsTy) (ids : List Nat) (rows : Bindings)
    (caller : List Nat) (Δ : List Constraint) (ann : Option Ty) (originalHM : Ty) where
  bounds : BoundsTy
  shape : Synth.BoundsTy.toTy bounds = ScopedHMInterpretation.ty types slots originalHM
  inScope : BoundsScoped caller bounds
  obligation : ScopedHMAnnotation.ParamOK types slots ids rows Δ ann bounds

private def scopedParameterCandidate (types slots : Nat → BoundsTy) (ids : List Nat) (rows : Bindings)
    (caller : List Nat) (Δ : List Constraint) (ann : Option Ty) (originalHM : Ty)
    (expected : Option BoundsTy) :
    Except String (Σ β, PLift (ScopedHMAnnotation.ParamOK types slots ids rows Δ ann β)) := do
  match ann with
    | some τ => do
        let demand ← decodeScoped types slots ids rows caller τ
        pure ⟨demand.bounds, ⟨demand.source, demand.decoded, SemanticSub.refl _ _⟩⟩
    | none => do
        let param ← match expected with
          | some β => pure β
          | none => do
              let interpreted := ScopedHMInterpretation.ty types slots originalHM
              match interpreted with
              | .customTy name _ =>
                  if name = listTyName then
                    let ⟨β, _⟩ ← Typed.chooseParam Δ none interpreted
                    pure β
                  else Typed.shapeTop interpreted
              | _ =>
                  let ⟨β, _⟩ ← Typed.chooseParam Δ none interpreted
                  pure β
        pure ⟨param, ⟨True.intro⟩⟩

/-- A parameter is an assumption at its declared or explicitly guided domain,
    not a synthesized RHS result. Whole-function inclusion remains separate. -/
def chooseScopedParam (types slots : Nat → BoundsTy) (ids : List Nat) (rows : Bindings)
    (caller : List Nat) (Δ : List Constraint) (ann : Option Ty) (originalHM : Ty)
    (expected : Option BoundsTy) : Except String (ScopedParameter types slots ids rows caller Δ ann originalHM) := do
  let ⟨param, obligation⟩ ← scopedParameterCandidate types slots ids rows caller Δ ann originalHM expected
  let shape ← match BinderBridge.equalTy (Synth.BoundsTy.toTy param) (ScopedHMInterpretation.ty types slots originalHM) with
    | some h => pure h
    | none => throw "bounds: parameter disagrees with HM-interpreted found payload"
  if hs : boundsScopedBool caller param = true then
    pure ⟨param, shape.down, boundsScopedBool_sound hs, obligation.down⟩
  else throw "bounds: HM-interpreted parameter counts are outside caller scope"

def checkScopedBinding (types slots : Nat → BoundsTy) (ids : List Nat) (rows : Bindings)
    (caller : List Nat) (Δ : List Constraint) (ann : Option PolyTy) (actual : BoundsTy) :
    Except String (PLift (ScopedHMAnnotation.BindingOK types slots ids rows Δ ann actual)) := do
  match ann with
  | none => pure ⟨True.intro⟩
  | some σ =>
      if hm : σ.paramCount = 0 then
        let checked ← checkScoped types slots ids rows caller Δ σ.body actual
        pure ⟨hm, checked.down⟩
      else throw "bounds: polymorphic HM internal binding unsupported in interpreted recursive RHS slice"

def scopedBindingHint (types slots : Nat → BoundsTy) (ids : List Nat) (rows : Bindings)
    (caller : List Nat) (ann : Option PolyTy) : Except String (Option BoundsTy) := do
  match ann with
  | some σ => if σ.paramCount = 0 then pure (some (← decodeScoped types slots ids rows caller σ.body).bounds) else pure none
  | none => pure none

/-- The old free-only API is a view of the same scoped checks. -/
abbrev Demand (types : Nat → BoundsTy) := ScopedDemand types BoundsTy.bvar

namespace Demand
def bounds {types ids rows caller τ} (d : Demand types ids rows caller τ) : BoundsTy :=
  ScopedHMAnnotation.Demand.bounds d

theorem shape {types ids rows caller τ} (d : Demand types ids rows caller τ) :
    Synth.BoundsTy.toTy d.bounds = HMFoundView.ty types τ := by
  rw [bounds, ScopedHMAnnotation.Demand.shape, HMFoundView.scoped_identity_slots]
end Demand

abbrev Parameter (types : Nat → BoundsTy) := ScopedParameter types BoundsTy.bvar

namespace Parameter
theorem shape {types ids rows caller Δ ann originalHM}
    (p : Parameter types ids rows caller Δ ann originalHM) :
    Synth.BoundsTy.toTy p.bounds = HMFoundView.ty types originalHM := by
  rw [← HMFoundView.scoped_identity_slots]
  exact ScopedParameter.shape p
end Parameter

def decode (types : Nat → BoundsTy) := decodeScoped types BoundsTy.bvar
def check (types : Nat → BoundsTy) := checkScoped types BoundsTy.bvar
def chooseParam (types : Nat → BoundsTy) := chooseScopedParam types BoundsTy.bvar
def checkBinding (types : Nat → BoundsTy) := checkScopedBinding types BoundsTy.bvar
def bindingHint (types : Nat → BoundsTy) := scopedBindingHint types BoundsTy.bvar

#print axioms Demand.shape
#print axioms decode
#print axioms check
#print axioms chooseScopedParam
#print axioms checkScopedBinding
#print axioms Parameter.shape

end FHM.Bounds.RecursiveHMAnnotation
