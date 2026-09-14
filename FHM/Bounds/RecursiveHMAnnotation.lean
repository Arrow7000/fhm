import FHM.Bounds.HMFoundView

/-! Executable source-annotation checks for the interpreted recursive RHS
judgement. Counts in source syntax are interpreted BEFORE full HM replacements
are inserted. Source scope, final caller scope and semantic inclusion are
independent obligations; no expression or annotation is rewritten. -/

namespace FHM.Bounds.RecursiveHMAnnotation

open CountSubstitution SchemeSpecialization ScopedScheme

structure Demand (types : Nat → BoundsTy) (ids : List Nat) (rows : Bindings)
    (caller : List Nat) (τ : Ty) where
  source : ScopedAnnotation.Decoded ids τ
  decoded : ScopedAnnotation.decode ids τ = .ok source
  finite : Finite rows
  inScope : BoundsScoped caller (mapFree types (bounds rows source.bounds))

def Demand.bounds {types ids rows caller τ} (d : Demand types ids rows caller τ) : BoundsTy :=
  mapFree types (CountSubstitution.bounds rows d.source.bounds)

theorem Demand.shape {types ids rows caller τ} (d : Demand types ids rows caller τ) :
    Synth.BoundsTy.toTy d.bounds = HMFoundView.ty types τ := by
  rw [Demand.bounds, HMFoundView.bounds_shape, bounds_shape, d.source.shape, HMFoundView.erased]

def decode (types : Nat → BoundsTy) (ids : List Nat) (rows : Bindings)
    (caller : List Nat) (τ : Ty) : Except String (Demand types ids rows caller τ) := do
  if hf : rows.all (fun row => row.2.noInf) = true then
    match hd : ScopedAnnotation.decode ids τ with
    | .error message => throw message
    | .ok source =>
        if hs : boundsScopedBool caller (mapFree types (bounds rows source.bounds)) = true then
          pure ⟨source, hd, fun row hr => Count.noInf_of_isNoInf (List.all_eq_true.mp hf row hr),
            boundsScopedBool_sound hs⟩
        else throw "bounds: HM-interpreted annotation counts are outside caller scope"
  else throw "bounds: HM annotation interpretation contains an infinite Nat replacement"

def check (types : Nat → BoundsTy) (ids : List Nat) (rows : Bindings) (caller : List Nat)
    (Δ : List Constraint) (τ : Ty) (actual : BoundsTy) :
    Except String (PLift (HMInterpretation.AnnotationOK types ids rows Δ τ actual)) := do
  let demand ← decode types ids rows caller τ
  let inclusion ← Typed.subtype Δ actual demand.bounds
  pure ⟨demand.source, demand.decoded, inclusion.down⟩

structure Parameter (types : Nat → BoundsTy) (ids : List Nat) (rows : Bindings)
    (caller : List Nat) (Δ : List Constraint) (ann : Option Ty) (originalHM : Ty) where
  bounds : BoundsTy
  shape : Synth.BoundsTy.toTy bounds = HMFoundView.ty types originalHM
  inScope : BoundsScoped caller bounds
  obligation : HMInterpretation.ParamOK types ids rows Δ ann bounds

private def parameterCandidate (types : Nat → BoundsTy) (ids : List Nat) (rows : Bindings)
    (caller : List Nat) (Δ : List Constraint) (ann : Option Ty) (originalHM : Ty)
    (expected : Option BoundsTy) :
    Except String (Σ β, PLift (HMInterpretation.ParamOK types ids rows Δ ann β)) := do
  match ann with
    | some τ => do
        let demand ← decode types ids rows caller τ
        pure ⟨demand.bounds, ⟨demand.source, demand.decoded, SemanticSub.refl _ _⟩⟩
    | none => do
        let param ← match expected with
          | some β => pure β
          | none => do
              let ⟨β, _⟩ ← Typed.chooseParam Δ none (HMFoundView.ty types originalHM)
              pure β
        pure ⟨param, ⟨True.intro⟩⟩

/-- A parameter is an assumption at its declared or explicitly guided domain,
    not a synthesized RHS result. Whole-function inclusion remains separate. -/
def chooseParam (types : Nat → BoundsTy) (ids : List Nat) (rows : Bindings)
    (caller : List Nat) (Δ : List Constraint) (ann : Option Ty) (originalHM : Ty)
    (expected : Option BoundsTy) : Except String (Parameter types ids rows caller Δ ann originalHM) := do
  let ⟨param, obligation⟩ ← parameterCandidate types ids rows caller Δ ann originalHM expected
  let shape ← match BinderBridge.equalTy (Synth.BoundsTy.toTy param) (HMFoundView.ty types originalHM) with
    | some h => pure h
    | none => throw "bounds: parameter disagrees with HM-interpreted found payload"
  if hs : boundsScopedBool caller param = true then
    pure ⟨param, shape.down, boundsScopedBool_sound hs, obligation.down⟩
  else throw "bounds: HM-interpreted parameter counts are outside caller scope"

def checkBinding (types : Nat → BoundsTy) (ids : List Nat) (rows : Bindings)
    (caller : List Nat) (Δ : List Constraint) (ann : Option PolyTy) (actual : BoundsTy) :
    Except String (PLift (HMInterpretation.BindingOK types ids rows Δ ann actual)) := do
  match ann with
  | none => pure ⟨True.intro⟩
  | some σ =>
      if hm : σ.paramCount = 0 then
        let checked ← check types ids rows caller Δ σ.body actual
        pure ⟨hm, checked.down⟩
      else throw "bounds: polymorphic HM internal binding unsupported in interpreted recursive RHS slice"

def bindingHint (types : Nat → BoundsTy) (ids : List Nat) (rows : Bindings)
    (caller : List Nat) (ann : Option PolyTy) : Except String (Option BoundsTy) := do
  match ann with
  | some σ => if σ.paramCount = 0 then pure (some (← decode types ids rows caller σ.body).bounds) else pure none
  | none => pure none

#print axioms Demand.shape
#print axioms decode
#print axioms check
#print axioms chooseParam
#print axioms checkBinding

end FHM.Bounds.RecursiveHMAnnotation
