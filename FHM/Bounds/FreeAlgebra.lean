import FHM.Bounds.SchemeSpecialization

/-! # Algebra for capture-safe bounds scheme transport

Free replacements must be locally closed when crossing HM bound slots.
Without this condition, bound-slot instantiation would capture slots inside
inserted free replacements. Counts remain outside these HM operations.
-/

namespace FHM.Bounds.FreeAlgebra

open SchemeSpecialization

mutual
theorem congrFree {f g : Nat → BoundsTy} {β}
    (h : ∀ i ∈ (Synth.BoundsTy.toTy β).freeVars, f i = g i) :
    mapFree f β = mapFree g β := by
  cases β with
  | prim | bvar => rfl
  | fvar i => exact h i (by simp [Synth.BoundsTy.toTy, Ty.freeVars])
  | arrow a b =>
      simp only [mapFree]
      congr 1
      · exact congrFree (fun i hi => h i (by simp [Synth.BoundsTy.toTy, Ty.freeVars, hi]))
      · exact congrFree (fun i hi => h i (by simp [Synth.BoundsTy.toTy, Ty.freeVars, hi]))
  | list lo hi a => exact congrArg (BoundsTy.list lo hi) (congrFree
      (fun i hi => h i (by simpa [Synth.BoundsTy.toTy, listTy, Ty.freeVars, TyList.freeVars] using hi)))
  | custom n as => exact congrArg (BoundsTy.custom n) (list_congrFree
      (by simpa only [Synth.BoundsTy.toTy, Ty.freeVars] using h))
termination_by sizeOf β

private theorem list_congrFree {f g : Nat → BoundsTy} {as}
    (h : ∀ i ∈ TyList.freeVars (as.map Synth.BoundsTy.toTy), f i = g i) :
    mapFreeList f as = mapFreeList g as := by
  cases as with
  | nil => rfl
  | cons a as =>
      simp only [mapFreeList]
      congr 1
      · exact congrFree (fun i hi => h i (by simp [TyList.freeVars, hi]))
      · exact list_congrFree (fun i hi => h i (by simp [TyList.freeVars, hi]))
termination_by sizeOf as
end

mutual
theorem bvars (f : Nat → BoundsTy) (hf : ∀ i, (Synth.BoundsTy.toTy (f i)).IsLC)
    {n β} (h : ContainsBvarsUpTo n (Synth.BoundsTy.toTy β)) :
    ContainsBvarsUpTo n (Synth.BoundsTy.toTy (mapFree f β)) := by
  cases β with
  | prim => simp only [mapFree, Synth.BoundsTy.toTy]; exact .prim
  | fvar i => exact (hf i).mono (Nat.zero_le n)
  | bvar i => simpa only [mapFree] using h
  | arrow a b =>
      simp only [Synth.BoundsTy.toTy] at h
      cases h with
      | arrow ha hb =>
          simp only [mapFree, Synth.BoundsTy.toTy]
          exact .arrow (bvars f hf ha) (bvars f hf hb)
  | list lo hi a =>
      simp only [Synth.BoundsTy.toTy, listTy] at h
      cases h with
      | customTy hall =>
          simp only [mapFree, Synth.BoundsTy.toTy, listTy]
          exact .customTy (by
            intro t ht
            simp only [List.mem_singleton] at ht
            subst t
            exact bvars f hf (hall _ (by simp)))
  | custom name as =>
      simp only [Synth.BoundsTy.toTy] at h
      cases h with
      | customTy hall =>
          simp only [mapFree, Synth.BoundsTy.toTy]
          exact .customTy (list_bvars f hf hall)
termination_by sizeOf β

private theorem list_bvars (f : Nat → BoundsTy) (hf : ∀ i, (Synth.BoundsTy.toTy (f i)).IsLC)
    {n as} (h : ∀ t ∈ as.map Synth.BoundsTy.toTy, ContainsBvarsUpTo n t) :
    ∀ t ∈ (mapFreeList f as).map Synth.BoundsTy.toTy, ContainsBvarsUpTo n t := by
  cases as with
  | nil => simp [mapFreeList]
  | cons a as =>
      intro t ht
      simp only [mapFreeList, List.map_cons, List.mem_cons] at ht
      rcases ht with rfl | ht
      · exact bvars f hf (h _ (by simp))
      · exact list_bvars f hf (fun t ht => h t (List.mem_cons_of_mem _ ht)) t ht
termination_by sizeOf as
end

mutual
theorem shape_erased (β : BoundsTy) : (Synth.BoundsTy.toTy β).eraseBounds = Synth.BoundsTy.toTy β := by
  cases β with
  | prim | fvar | bvar => simp only [Synth.BoundsTy.toTy, Ty.eraseBounds]
  | arrow a b => simp only [Synth.BoundsTy.toTy, Ty.eraseBounds, shape_erased a, shape_erased b]
  | list lo hi a => simp only [Synth.BoundsTy.toTy, listTy, Ty.eraseBounds, TyList.eraseBounds,
      shape_erased a]
  | custom n as => simp only [Synth.BoundsTy.toTy, Ty.eraseBounds, list_shape_erased as]
termination_by sizeOf β

private theorem list_shape_erased (as : List BoundsTy) :
    TyList.eraseBounds (as.map Synth.BoundsTy.toTy) = as.map Synth.BoundsTy.toTy := by
  cases as with
  | nil => rfl
  | cons a as => simp only [List.map_cons, TyList.eraseBounds, shape_erased a, list_shape_erased as]
termination_by sizeOf as
end

mutual
theorem instantiate_fixed (args : Nat → BoundsTy) {β}
    (h : (Synth.BoundsTy.toTy β).IsLC) : TypeSubstitution.substitute args β = β := by
  cases β with
  | prim | fvar => rfl
  | bvar i => simp only [Synth.BoundsTy.toTy] at h; cases h with | bvar hi => omega
  | arrow a b =>
      simp only [Synth.BoundsTy.toTy] at h
      cases h with
      | arrow ha hb => simp only [TypeSubstitution.substitute, instantiate_fixed args ha, instantiate_fixed args hb]
  | list lo hi a =>
      simp only [Synth.BoundsTy.toTy, listTy] at h
      cases h with
      | customTy hall => exact congrArg (BoundsTy.list lo hi) (instantiate_fixed args (hall _ (by simp)))
  | custom n as =>
      simp only [Synth.BoundsTy.toTy] at h
      cases h with
      | customTy hall => exact congrArg (BoundsTy.custom n) (list_instantiate_fixed args hall)
termination_by sizeOf β

private theorem list_instantiate_fixed (args : Nat → BoundsTy) {as}
    (h : ∀ t ∈ as.map Synth.BoundsTy.toTy, t.IsLC) : TypeSubstitution.substituteList args as = as := by
  cases as with
  | nil => rfl
  | cons a as =>
      simp only [TypeSubstitution.substituteList]
      congr 1
      · exact instantiate_fixed args (h _ (by simp))
      · exact list_instantiate_fixed args (fun t ht => h t (List.mem_cons_of_mem _ ht))
termination_by sizeOf as
end

mutual
theorem instantiate_commute (f : Nat → BoundsTy)
    (hf : ∀ i, (Synth.BoundsTy.toTy (f i)).IsLC) (args : Nat → BoundsTy) (β : BoundsTy) :
    mapFree f (TypeSubstitution.substitute args β) =
      TypeSubstitution.substitute (fun i => mapFree f (args i)) (mapFree f β) := by
  cases β with
  | prim | bvar => rfl
  | fvar i => exact (instantiate_fixed _ (hf i)).symm
  | arrow a b => simp only [TypeSubstitution.substitute, mapFree, instantiate_commute f hf args a,
      instantiate_commute f hf args b]
  | list lo hi a => exact congrArg (BoundsTy.list lo hi) (instantiate_commute f hf args a)
  | custom n as => exact congrArg (BoundsTy.custom n) (list_instantiate_commute f hf args as)
termination_by sizeOf β

private theorem list_instantiate_commute (f : Nat → BoundsTy)
    (hf : ∀ i, (Synth.BoundsTy.toTy (f i)).IsLC) (args : Nat → BoundsTy) (as : List BoundsTy) :
    mapFreeList f (TypeSubstitution.substituteList args as) =
      TypeSubstitution.substituteList (fun i => mapFree f (args i)) (mapFreeList f as) := by
  cases as with
  | nil => rfl
  | cons a as => simp only [TypeSubstitution.substituteList, mapFreeList,
      instantiate_commute f hf args a, list_instantiate_commute f hf args as]
termination_by sizeOf as
end

mutual
theorem instantiate_congr {args args' : Nat → BoundsTy} {n β}
    (h : ContainsBvarsUpTo n (Synth.BoundsTy.toTy β)) (ha : ∀ i < n, args i = args' i) :
    TypeSubstitution.substitute args β = TypeSubstitution.substitute args' β := by
  cases β with
  | prim | fvar => rfl
  | bvar i => simp only [Synth.BoundsTy.toTy] at h; cases h with | bvar hi => exact ha i hi
  | arrow a b =>
      simp only [Synth.BoundsTy.toTy] at h
      cases h with
      | arrow hd hc => simp only [TypeSubstitution.substitute, instantiate_congr hd ha, instantiate_congr hc ha]
  | list lo hi a =>
      simp only [Synth.BoundsTy.toTy, listTy] at h
      cases h with
      | customTy hall => exact congrArg (BoundsTy.list lo hi) (instantiate_congr (hall _ (by simp)) ha)
  | custom name as =>
      simp only [Synth.BoundsTy.toTy] at h
      cases h with
      | customTy hall => exact congrArg (BoundsTy.custom name) (list_instantiate_congr hall ha)
termination_by sizeOf β

theorem list_instantiate_congr {args args' : Nat → BoundsTy} {n as}
    (h : ∀ t ∈ as.map Synth.BoundsTy.toTy, ContainsBvarsUpTo n t) (ha : ∀ i < n, args i = args' i) :
    TypeSubstitution.substituteList args as = TypeSubstitution.substituteList args' as := by
  cases as with
  | nil => rfl
  | cons a as =>
      simp only [TypeSubstitution.substituteList]
      congr 1
      · exact instantiate_congr (h _ (by simp)) ha
      · exact list_instantiate_congr (fun t ht => h t (List.mem_cons_of_mem _ ht)) ha
termination_by sizeOf as
end

#print axioms bvars
#print axioms instantiate_commute
#print axioms instantiate_congr

end FHM.Bounds.FreeAlgebra
