import FHM.Bounds.InterpretedAnnotation
import FHM.Bounds.FreeAlgebra
import FHM.Bounds.ScopedHMAnnotation

/-! Proof-side simultaneous interpretation of source HM identities. Source
annotations and the runtime term stay unchanged. Counts in inserted complete
types belong to the caller, rather than to the source annotation's telescope. -/

namespace FHM.Bounds.HMInterpretation

open SchemeSpecialization CountSubstitution

theorem identity (β : BoundsTy) : mapFree BoundsTy.fvar β = β :=
  SchemeSpecialization.fixed (fun _ _ => rfl)

mutual
theorem compose (f g : Nat → BoundsTy) (β : BoundsTy) :
    mapFree f (mapFree g β) = mapFree (fun i => mapFree f (g i)) β := by
  cases β with
  | prim | fvar | bvar => rfl
  | arrow a b => simp only [mapFree, compose f g a, compose f g b]
  | list lo hi a => exact congrArg (BoundsTy.list lo hi) (compose f g a)
  | custom n as => exact congrArg (BoundsTy.custom n) (compose_list f g as)
termination_by sizeOf β

private theorem compose_list (f g : Nat → BoundsTy) (as : List BoundsTy) :
    mapFreeList f (mapFreeList g as) = mapFreeList (fun i => mapFree f (g i)) as := by
  cases as with
  | nil => rfl
  | cons a as => simp only [mapFreeList, compose f g a, compose_list f g as]
termination_by sizeOf as
end

mutual
theorem counts (rows : Bindings) (f : Nat → BoundsTy) (β : BoundsTy) :
    bounds rows (mapFree f β) = mapFree (fun i => bounds rows (f i)) (bounds rows β) := by
  cases β with
  | prim | fvar | bvar => rfl
  | arrow a b => simp only [mapFree, bounds, counts rows f a, counts rows f b]
  | list lo hi a => exact congrArg (BoundsTy.list (count rows lo) (count rows hi)) (counts rows f a)
  | custom n as => exact congrArg (BoundsTy.custom n) (counts_list rows f as)
termination_by sizeOf β

private theorem counts_list (rows : Bindings) (f : Nat → BoundsTy) (as : List BoundsTy) :
    boundsList rows (mapFreeList f as) =
      mapFreeList (fun i => bounds rows (f i)) (boundsList rows as) := by
  cases as with
  | nil => rfl
  | cons a as => simp only [mapFreeList, boundsList, counts rows f a, counts_list rows f as]
termination_by sizeOf as
end

def AnnotationOK (types : Nat → BoundsTy) (ids : List Nat) (rows : Bindings)
    (Δ : List Constraint) (τ : Ty) (actual : BoundsTy) : Prop :=
  ScopedHMAnnotation.AnnotationOK types BoundsTy.bvar ids rows Δ τ actual

def ParamOK (types : Nat → BoundsTy) (ids : List Nat) (rows : Bindings)
    (Δ : List Constraint) (ann : Option Ty) (actual : BoundsTy) : Prop :=
  match ann with | none => True | some τ => AnnotationOK types ids rows Δ τ actual

def BindingOK (types : Nat → BoundsTy) (ids : List Nat) (rows : Bindings)
    (Δ : List Constraint) (ann : Option PolyTy) (actual : BoundsTy) : Prop :=
  match ann with
  | none => True
  | some σ => σ.paramCount = 0 ∧ AnnotationOK types ids rows Δ σ.body actual

theorem AnnotationOK.identity {ids rows Δ τ actual}
    (h : InterpretedAnnotation.OK ids rows Δ τ actual) :
    AnnotationOK BoundsTy.fvar ids rows Δ τ actual := by
  obtain ⟨d, hd, hs⟩ := h
  exact ⟨d, hd, by simpa only [ScopedHMInterpretation.identity_slots, HMInterpretation.identity] using hs⟩

theorem AnnotationOK.types {types ids rows Δ τ actual}
    (h : AnnotationOK types ids rows Δ τ actual) (f : Nat → BoundsTy) :
    AnnotationOK (fun i => mapFree f (types i)) ids rows Δ τ (mapFree f actual) := by
  simpa only [mapFree] using ScopedHMAnnotation.AnnotationOK.types h f

theorem AnnotationOK.counts {types ids rows Δ τ actual}
    (h : AnnotationOK types ids rows Δ τ actual) (outer : Bindings) (hf : Finite outer) :
    AnnotationOK (fun i => bounds outer (types i)) ids (CountAlgebra.compose outer rows)
      (Δ.map (constraint outer)) τ (bounds outer actual) := by
  simpa only [bounds] using ScopedHMAnnotation.AnnotationOK.counts h outer hf

theorem AnnotationOK.assuming {types ids rows Δ Δ' τ actual}
    (h : AnnotationOK types ids rows Δ τ actual) (hp : (⟨Δ', Δ⟩ : ForallProblem).Valid) :
    AnnotationOK types ids rows Δ' τ actual := by
  exact ScopedHMAnnotation.AnnotationOK.assuming h hp

mutual
theorem scope_mono {ids target β} (h : ScopedScheme.BoundsScoped ids β)
    (includeIds : ∀ i ∈ ids, i ∈ target) : ScopedScheme.BoundsScoped target β := by
  cases β with
  | prim | bvar | fvar => trivial
  | arrow a b => exact ⟨scope_mono h.1 includeIds, scope_mono h.2 includeIds⟩
  | list lo hi a =>
      exact ⟨count_mono h.1 includeIds, count_mono h.2.1 includeIds, scope_mono h.2.2 includeIds⟩
  | custom n as => exact scope_list_mono h includeIds
termination_by sizeOf β

private theorem scope_list_mono {ids target as} (h : ScopedScheme.BoundsListScoped ids as)
    (includeIds : ∀ i ∈ ids, i ∈ target) : ScopedScheme.BoundsListScoped target as := by
  cases as with
  | nil => trivial
  | cons a as => exact ⟨scope_mono h.1 includeIds, scope_list_mono h.2 includeIds⟩
termination_by sizeOf as

theorem count_mono {ids target c} (h : Scope.CountScoped ids c)
    (includeIds : ∀ i ∈ ids, i ∈ target) : Scope.CountScoped target c := by
  induction c with
  | lit | inf => trivial
  | var v =>
      cases v with | mk kind i =>
        cases kind with
        | rigid => exact includeIds i h
        | inferable => cases h
  | add a b ha hb | mul a b ha hb | min a b ha hb | max a b ha hb => exact ⟨ha h.1, hb h.2⟩
  | pred a ha => exact ha h
end

mutual
theorem map_scope {ids target β} (h : ScopedScheme.BoundsScoped ids β)
    (f : Nat → BoundsTy) (scope : ∀ i, ScopedScheme.BoundsScoped target (f i)) :
    ScopedScheme.BoundsScoped (ids ++ target) (mapFree f β) := by
  cases β with
  | prim | bvar => trivial
  | fvar i => exact scope_mono (scope i) (fun _ hi => List.mem_append_right _ hi)
  | arrow a b => exact ⟨map_scope h.1 f scope, map_scope h.2 f scope⟩
  | list lo hi a =>
      exact ⟨count_mono h.1 (fun _ hi => List.mem_append_left _ hi),
        count_mono h.2.1 (fun _ hi => List.mem_append_left _ hi), map_scope h.2.2 f scope⟩
  | custom n as => exact map_list_scope h f scope
termination_by sizeOf β

private theorem map_list_scope {ids target as} (h : ScopedScheme.BoundsListScoped ids as)
    (f : Nat → BoundsTy) (scope : ∀ i, ScopedScheme.BoundsScoped target (f i)) :
    ScopedScheme.BoundsListScoped (ids ++ target) (mapFreeList f as) := by
  cases as with
  | nil => trivial
  | cons a as => exact ⟨map_scope h.1 f scope, map_list_scope h.2 f scope⟩
termination_by sizeOf as
end

#print axioms compose
#print axioms counts
#print axioms AnnotationOK.types
#print axioms AnnotationOK.counts

end FHM.Bounds.HMInterpretation
