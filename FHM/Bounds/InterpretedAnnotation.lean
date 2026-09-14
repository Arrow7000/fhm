import FHM.Bounds.CountAlgebra
import FHM.Bounds.ScopedAnnotation
import FHM.Bounds.Typed

/-! Source annotations retain their lexical identities. A separate simultaneous
count interpretation determines their demand at a specialization. Source scope,
caller scope and actual semantic inclusion are independent checks. -/

namespace FHM.Bounds.InterpretedAnnotation

open CountSubstitution

def OK (ids : List Nat) (rows : Bindings) (Δ : List Constraint) (τ : Ty) (β : BoundsTy) : Prop :=
  ∃ d : ScopedAnnotation.Decoded ids τ,
    ScopedAnnotation.decode ids τ = .ok d ∧ SemanticSub Δ β (bounds rows d.bounds)

def ParamOK (ids : List Nat) (rows : Bindings) (Δ : List Constraint)
    (ann : Option Ty) (β : BoundsTy) : Prop :=
  match ann with | none => True | some τ => OK ids rows Δ τ β

def BindingOK (ids : List Nat) (rows : Bindings) (Δ : List Constraint)
    (ann : Option PolyTy) (β : BoundsTy) : Prop :=
  match ann with
  | none => True
  | some σ => σ.paramCount = 0 ∧ OK ids rows Δ σ.body β

theorem transport (outer : Bindings) (hf : Finite outer) {ids inner Δ τ β}
    (h : OK ids inner Δ τ β) :
    OK ids (CountAlgebra.compose outer inner) (Δ.map (constraint outer)) τ (bounds outer β) := by
  obtain ⟨d, hd, hs⟩ := h
  exact ⟨d, hd, by simpa only [CountAlgebra.bounds_compose] using subtype outer hf hs⟩

theorem assuming {ids rows Δ Δ' τ β} (h : OK ids rows Δ τ β)
    (hp : (⟨Δ', Δ⟩ : ForallProblem).Valid) : OK ids rows Δ' τ β := by
  obtain ⟨d, hd, hs⟩ := h
  exact ⟨d, hd, hs.assuming hp⟩

structure Demand (ids : List Nat) (rows : Bindings) (caller : List Nat) (τ : Ty) where
  source : ScopedAnnotation.Decoded ids τ
  decoded : ScopedAnnotation.decode ids τ = .ok source
  finite : Finite rows
  inScope : ScopedScheme.BoundsScoped caller (bounds rows source.bounds)

def Demand.bounds {ids rows caller τ} (d : Demand ids rows caller τ) : BoundsTy :=
  CountSubstitution.bounds rows d.source.bounds

theorem Demand.shape {ids rows caller τ} (d : Demand ids rows caller τ) :
    Synth.BoundsTy.toTy d.bounds = τ.eraseBounds :=
  (bounds_shape rows d.source.bounds).trans d.source.shape

def decode (ids : List Nat) (rows : Bindings) (caller : List Nat) (τ : Ty) :
    Except String (Demand ids rows caller τ) := do
  if hf : rows.all (fun row => row.2.noInf) = true then
    match hd : ScopedAnnotation.decode ids τ with
    | .error message => throw message
    | .ok source =>
        if hs : ScopedScheme.boundsScopedBool caller (bounds rows source.bounds) = true then
          pure ⟨source, hd,
            fun row hr => Count.noInf_of_isNoInf (List.all_eq_true.mp hf row hr),
            ScopedScheme.boundsScopedBool_sound hs⟩
        else throw "bounds: interpreted annotation counts are outside caller scope"
  else throw "bounds: annotation interpretation contains an infinite Nat replacement"

def check (ids : List Nat) (rows : Bindings) (caller : List Nat) (Δ : List Constraint)
    (τ : Ty) (actual : BoundsTy) : Except String (PLift (OK ids rows Δ τ actual)) := do
  let demand ← decode ids rows caller τ
  let inclusion ← Typed.subtype Δ actual demand.bounds
  pure ⟨demand.source, demand.decoded, inclusion.down⟩

#print axioms transport
#print axioms Demand.shape
#print axioms decode
#print axioms check

end FHM.Bounds.InterpretedAnnotation
