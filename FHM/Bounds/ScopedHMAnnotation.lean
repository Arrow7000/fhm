import FHM.Bounds.ScopedHMInterpretation
import FHM.Bounds.ScopedAnnotation
import FHM.Bounds.Typed

/-! Source obligations with simultaneous free/lexical HM interfaces. Count
specialization transforms both interfaces and the original source interpretation;
full caller types inserted subsequently cannot be captured by that telescope.
No expression/annotation rewriting, RHS typing or group export is assumed here.
-/

namespace FHM.Bounds.ScopedHMAnnotation

open ScopedHMInterpretation CountSubstitution ScopedScheme

def AnnotationOK (free slots : Nat → BoundsTy) (ids : List Nat) (rows : Bindings)
    (Δ : List Constraint) (τ : Ty) (actual : BoundsTy) : Prop :=
  ∃ d : ScopedAnnotation.Decoded ids τ, ScopedAnnotation.decode ids τ = .ok d ∧
    SemanticSub Δ actual (read free slots (bounds rows d.bounds))

def ParamOK (free slots : Nat → BoundsTy) (ids : List Nat) (rows : Bindings)
    (Δ : List Constraint) (ann : Option Ty) (actual : BoundsTy) : Prop :=
  match ann with | none => True | some τ => AnnotationOK free slots ids rows Δ τ actual

def BindingOK (free slots : Nat → BoundsTy) (ids : List Nat) (rows : Bindings)
    (Δ : List Constraint) (ann : Option PolyTy) (actual : BoundsTy) : Prop :=
  match ann with
  | none => True
  | some σ => σ.paramCount = 0 ∧ AnnotationOK free slots ids rows Δ σ.body actual

theorem AnnotationOK.types {free slots ids rows Δ τ actual}
    (h : AnnotationOK free slots ids rows Δ τ actual) (outer : Nat → BoundsTy) :
    AnnotationOK (fun i => SchemeSpecialization.mapFree outer (free i))
      (fun i => SchemeSpecialization.mapFree outer (slots i)) ids rows Δ τ
      (SchemeSpecialization.mapFree outer actual) := by
  obtain ⟨d, hd, hs⟩ := h
  exact ⟨d, hd, by simpa only [map_types] using SchemeSpecialization.subtype outer hs⟩

theorem AnnotationOK.counts {free slots ids rows Δ τ actual}
    (h : AnnotationOK free slots ids rows Δ τ actual) (outer : Bindings) (finite : Finite outer) :
    AnnotationOK (fun i => bounds outer (free i)) (fun i => bounds outer (slots i))
      ids (CountAlgebra.compose outer rows) (Δ.map (constraint outer)) τ (bounds outer actual) := by
  obtain ⟨d, hd, hs⟩ := h
  exact ⟨d, hd, by simpa only [map_counts, CountAlgebra.bounds_compose] using subtype outer finite hs⟩

theorem AnnotationOK.assuming {free slots ids rows Δ Δ' τ actual}
    (h : AnnotationOK free slots ids rows Δ τ actual) (premises : (⟨Δ', Δ⟩ : ForallProblem).Valid) :
    AnnotationOK free slots ids rows Δ' τ actual := by
  obtain ⟨d, hd, hs⟩ := h
  exact ⟨d, hd, hs.assuming premises⟩

/-- Source checking may change solved artifact identities without changing
    the meaning of identities carried by the original annotation. -/
theorem AnnotationOK.congrFree {free free' slots ids rows Δ τ actual}
    (h : AnnotationOK free slots ids rows Δ τ actual)
    (agree : ∀ i ∈ τ.freeVars, free i = free' i) :
    AnnotationOK free' slots ids rows Δ τ actual := by
  obtain ⟨d, decoded, inclusion⟩ := h
  have same : read free slots (bounds rows d.bounds) = read free' slots (bounds rows d.bounds) :=
    ScopedHMInterpretation.congrFree (fun i member => agree i (by
      simpa only [bounds_shape, d.shape, eraseFreeVars] using member))
  exact ⟨d, decoded, by rw [← same]; exact inclusion⟩

/-- Lexical readers may likewise be changed outside the bound slots actually
    named by the source annotation. -/
theorem AnnotationOK.congrSlots {free slots slots' ids rows Δ τ actual n}
    (h : AnnotationOK free slots ids rows Δ τ actual)
    (bounded : ContainsBvarsUpTo n τ)
    (agree : ∀ i < n, slots i = slots' i) :
    AnnotationOK free slots' ids rows Δ τ actual := by
  obtain ⟨d, decoded, inclusion⟩ := h
  have sourceBounded : ContainsBvarsUpTo n (Synth.BoundsTy.toTy (bounds rows d.bounds)) := by
    simpa only [bounds_shape, d.shape] using bounded.eraseBounds
  have same := ScopedHMInterpretation.congrSlots (free := free) sourceBounded agree
  exact ⟨d, decoded, by rw [← same]; exact inclusion⟩

theorem ParamOK.congrFree {free free' slots ids rows Δ ann actual}
    (h : ParamOK free slots ids rows Δ ann actual)
    (agree : ∀ i ∈ ann.elim [] Ty.freeVars, free i = free' i) :
    ParamOK free' slots ids rows Δ ann actual := by
  cases ann with
  | none => trivial
  | some τ => exact AnnotationOK.congrFree h agree

theorem ParamOK.congrSlots {free slots slots' ids rows Δ ann actual n}
    (h : ParamOK free slots ids rows Δ ann actual)
    (bounded : ∀ τ, ann = some τ → ContainsBvarsUpTo n τ)
    (agree : ∀ i < n, slots i = slots' i) :
    ParamOK free slots' ids rows Δ ann actual := by
  cases ann with
  | none => trivial
  | some τ => exact AnnotationOK.congrSlots h (bounded τ rfl) agree

theorem BindingOK.congrFree {free free' slots ids rows Δ ann actual}
    (h : BindingOK free slots ids rows Δ ann actual)
    (agree : ∀ i ∈ ann.elim [] (fun σ => σ.body.freeVars), free i = free' i) :
    BindingOK free' slots ids rows Δ ann actual := by
  cases ann with
  | none => trivial
  | some σ => exact ⟨h.1, AnnotationOK.congrFree h.2 agree⟩

theorem BindingOK.congrSlots {free slots slots' ids rows Δ ann actual n}
    (h : BindingOK free slots ids rows Δ ann actual)
    (bounded : ∀ σ, ann = some σ → ContainsBvarsUpTo (n + σ.paramCount) σ.body)
    (agree : ∀ i < n, slots i = slots' i) :
    BindingOK free slots' ids rows Δ ann actual := by
  cases ann with
  | none => trivial
  | some σ =>
      refine ⟨h.1, AnnotationOK.congrSlots h.2 ?_ agree⟩
      simpa [h.1] using bounded σ rfl

structure Demand (free slots : Nat → BoundsTy) (ids : List Nat) (rows : Bindings)
    (caller : List Nat) (τ : Ty) where
  source : ScopedAnnotation.Decoded ids τ
  decoded : ScopedAnnotation.decode ids τ = .ok source
  finite : Finite rows
  inScope : BoundsScoped caller (read free slots (bounds rows source.bounds))

def Demand.bounds {free slots ids rows caller τ} (d : Demand free slots ids rows caller τ) : BoundsTy :=
  read free slots (CountSubstitution.bounds rows d.source.bounds)

theorem Demand.shape {free slots ids rows caller τ} (d : Demand free slots ids rows caller τ) :
    Synth.BoundsTy.toTy d.bounds = ty free slots τ := by
  rw [Demand.bounds, ScopedHMInterpretation.shape, bounds_shape, d.source.shape, erased]

def decode (free slots : Nat → BoundsTy) (ids : List Nat) (rows : Bindings)
    (caller : List Nat) (τ : Ty) : Except String (Demand free slots ids rows caller τ) := do
  if hf : rows.all (fun row => row.2.noInf) = true then
    match hd : ScopedAnnotation.decode ids τ with
    | .error message => throw message
    | .ok source =>
        if hs : boundsScopedBool caller (read free slots (bounds rows source.bounds)) = true then
          pure ⟨source, hd, fun row hr => Count.noInf_of_isNoInf (List.all_eq_true.mp hf row hr),
            boundsScopedBool_sound hs⟩
        else throw "bounds: lexical HM annotation counts are outside caller scope"
  else throw "bounds: lexical HM annotation interpretation contains an infinite Nat replacement"

def check (free slots : Nat → BoundsTy) (ids : List Nat) (rows : Bindings) (caller : List Nat)
    (Δ : List Constraint) (τ : Ty) (actual : BoundsTy) :
    Except String (PLift (AnnotationOK free slots ids rows Δ τ actual)) := do
  let demand ← decode free slots ids rows caller τ
  let inclusion ← Typed.subtype Δ actual demand.bounds
  pure ⟨demand.source, demand.decoded, inclusion.down⟩

#print axioms AnnotationOK.types
#print axioms AnnotationOK.counts
#print axioms AnnotationOK.assuming
#print axioms AnnotationOK.congrFree
#print axioms AnnotationOK.congrSlots
#print axioms Demand.shape
#print axioms decode
#print axioms check

end FHM.Bounds.ScopedHMAnnotation
