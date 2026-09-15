import FHM.Bounds.FreeAlgebra
import FHM.Bounds.CountAlgebra

/-! Simultaneous free/bound HM readers for lexical forall RHS artifacts.
Both namespaces are explicit; neither replacement is recursively reinterpreted.
These are interpretation/coherence lemmas, not a new typing judgement or source
annotation acceptance. Count specialization acts on both replacement interfaces.
-/

namespace FHM.Bounds.ScopedHMInterpretation

open SchemeSpecialization CountSubstitution

mutual
def read (free slots : Nat → BoundsTy) : BoundsTy → BoundsTy
  | .prim p => .prim p
  | .fvar i => free i
  | .bvar i => slots i
  | .arrow a b => .arrow (read free slots a) (read free slots b)
  | .list lo hi a => .list lo hi (read free slots a)
  | .custom name as => .custom name (readList free slots as)

def readList (free slots : Nat → BoundsTy) : List BoundsTy → List BoundsTy
  | [] => []
  | a :: as => read free slots a :: readList free slots as
end

mutual
/-- Reader changes outside the source's free identities are irrelevant, even
    with an independent lexical-slot interface. Inserted types are not reread. -/
theorem congrFree {f g slots : Nat → BoundsTy} {β}
    (h : ∀ i ∈ (Synth.BoundsTy.toTy β).freeVars, f i = g i) :
    read f slots β = read g slots β := by
  cases β with
  | prim | bvar => rfl
  | fvar i => exact h i (by simp [Synth.BoundsTy.toTy, Ty.freeVars])
  | arrow a b =>
      simp only [read]
      congr 1
      · exact congrFree (fun i hi => h i (by simp [Synth.BoundsTy.toTy, Ty.freeVars, hi]))
      · exact congrFree (fun i hi => h i (by simp [Synth.BoundsTy.toTy, Ty.freeVars, hi]))
  | list lo hi a => exact congrArg (BoundsTy.list lo hi) (congrFree
      (fun i hi => h i (by simpa [Synth.BoundsTy.toTy, listTy, Ty.freeVars, TyList.freeVars] using hi)))
  | custom n as => exact congrArg (BoundsTy.custom n) (list_congrFree
      (by simpa only [Synth.BoundsTy.toTy, Ty.freeVars] using h))
termination_by sizeOf β

private theorem list_congrFree {f g slots : Nat → BoundsTy} {as}
    (h : ∀ i ∈ TyList.freeVars (as.map Synth.BoundsTy.toTy), f i = g i) :
    readList f slots as = readList g slots as := by
  cases as with
  | nil => rfl
  | cons a as =>
      simp only [readList]
      congr 1
      · exact congrFree (fun i hi => h i (by simp [TyList.freeVars, hi]))
      · exact list_congrFree (fun i hi => h i (by simp [TyList.freeVars, hi]))
termination_by sizeOf as
end

mutual
/-- Lexical readers agree on a source whose every bound slot lies below the
    checked limit. Inserted full types are opaque and are never reread. -/
theorem congrSlots {free slots slots' : Nat → BoundsTy} {β n}
    (bounded : ContainsBvarsUpTo n (Synth.BoundsTy.toTy β))
    (agree : ∀ i < n, slots i = slots' i) :
    read free slots β = read free slots' β := by
  cases β with
  | prim | fvar => rfl
  | bvar i =>
      simp only [Synth.BoundsTy.toTy] at bounded
      cases bounded with | bvar small => exact agree i small
  | arrow a b =>
      simp only [Synth.BoundsTy.toTy] at bounded
      cases bounded with
      | arrow sa sb => simp only [read, congrSlots sa agree, congrSlots sb agree]
  | list lo hi a =>
      simp only [Synth.BoundsTy.toTy, listTy] at bounded
      cases bounded with
      | customTy all =>
          exact congrArg (BoundsTy.list lo hi)
            (congrSlots (all _ (by simp)) agree)
  | custom name as =>
      simp only [Synth.BoundsTy.toTy] at bounded
      cases bounded with
      | customTy all => exact congrArg (BoundsTy.custom name) (list_congrSlots all agree)
termination_by sizeOf β

private theorem list_congrSlots {free slots slots' : Nat → BoundsTy} {as n}
    (bounded : ∀ τ ∈ as.map Synth.BoundsTy.toTy, ContainsBvarsUpTo n τ)
    (agree : ∀ i < n, slots i = slots' i) :
    readList free slots as = readList free slots' as := by
  cases as with
  | nil => rfl
  | cons a as =>
      simp only [readList]
      congr 1
      · exact congrSlots (bounded _ (by simp)) agree
      · exact list_congrSlots (fun τ member => bounded τ (by simp [member])) agree
termination_by sizeOf as
end

mutual
def ty (free slots : Nat → BoundsTy) : Ty → Ty
  | .prim p => .prim p
  | .fvar i => Synth.BoundsTy.toTy (free i)
  | .bvar i => Synth.BoundsTy.toTy (slots i)
  | .arrow a b => .arrow (ty free slots a) (ty free slots b)
  | .bl _ _ a => listTy (ty free slots a)
  | .customTy name as => .customTy name (tys free slots as)

def tys (free slots : Nat → BoundsTy) : List Ty → List Ty
  | [] => []
  | a :: as => ty free slots a :: tys free slots as
end

mutual
/-- Bounds erasure does not remove or invent source HM identities. -/
theorem eraseFreeVars (τ : Ty) (i : Nat) : i ∈ τ.eraseBounds.freeVars ↔ i ∈ τ.freeVars := by
  cases τ with
  | prim | bvar | fvar => rfl
  | arrow a b => simp [Ty.eraseBounds_arrow, Ty.freeVars, eraseFreeVars a i, eraseFreeVars b i]
  | bl lo hi a =>
      simp [Ty.eraseBounds_bl, bareListTy, Ty.freeVars, TyList.freeVars, eraseFreeVars a i]
  | customTy name as =>
      simp only [Ty.eraseBounds_customTy, Ty.freeVars, TyList.eraseBounds_eq_map]
      exact list_eraseFreeVars as i
termination_by sizeOf τ

private theorem list_eraseFreeVars (as : List Ty) (i : Nat) :
    i ∈ TyList.freeVars (as.map Ty.eraseBounds) ↔ i ∈ TyList.freeVars as := by
  cases as with
  | nil => rfl
  | cons a as => simp [List.map_cons, TyList.freeVars, eraseFreeVars a i, list_eraseFreeVars as i]
termination_by sizeOf as
end

mutual
theorem identity_slots (free : Nat → BoundsTy) (β : BoundsTy) :
    read free BoundsTy.bvar β = mapFree free β := by
  cases β with
  | prim | fvar | bvar => rfl
  | arrow a b => simp only [read, mapFree, identity_slots free a, identity_slots free b]
  | list lo hi a => exact congrArg (BoundsTy.list lo hi) (identity_slots free a)
  | custom name as => exact congrArg (BoundsTy.custom name) (identity_slots_list free as)
termination_by sizeOf β

private theorem identity_slots_list (free : Nat → BoundsTy) (as : List BoundsTy) :
    readList free BoundsTy.bvar as = mapFreeList free as := by
  cases as with
  | nil => rfl
  | cons a as => simp only [readList, mapFreeList, identity_slots free a, identity_slots_list free as]
termination_by sizeOf as
end

mutual
theorem map_types (outer free slots : Nat → BoundsTy) (β : BoundsTy) :
    mapFree outer (read free slots β) =
      read (fun i => mapFree outer (free i)) (fun i => mapFree outer (slots i)) β := by
  cases β with
  | prim | fvar | bvar => rfl
  | arrow a b => simp only [read, mapFree, map_types outer free slots a, map_types outer free slots b]
  | list lo hi a => exact congrArg (BoundsTy.list lo hi) (map_types outer free slots a)
  | custom name as => exact congrArg (BoundsTy.custom name) (map_types_list outer free slots as)
termination_by sizeOf β

private theorem map_types_list (outer free slots : Nat → BoundsTy) (as : List BoundsTy) :
    mapFreeList outer (readList free slots as) =
      readList (fun i => mapFree outer (free i)) (fun i => mapFree outer (slots i)) as := by
  cases as with
  | nil => rfl
  | cons a as => simp only [readList, mapFreeList, map_types outer free slots a, map_types_list outer free slots as]
termination_by sizeOf as
end

mutual
theorem map_counts (rows : Bindings) (free slots : Nat → BoundsTy) (β : BoundsTy) :
    bounds rows (read free slots β) =
      read (fun i => bounds rows (free i)) (fun i => bounds rows (slots i)) (bounds rows β) := by
  cases β with
  | prim | fvar | bvar => rfl
  | arrow a b => simp only [read, bounds, map_counts rows free slots a, map_counts rows free slots b]
  | list lo hi a => exact congrArg (BoundsTy.list (count rows lo) (count rows hi)) (map_counts rows free slots a)
  | custom name as => exact congrArg (BoundsTy.custom name) (map_counts_list rows free slots as)
termination_by sizeOf β

private theorem map_counts_list (rows : Bindings) (free slots : Nat → BoundsTy) (as : List BoundsTy) :
    boundsList rows (readList free slots as) =
      readList (fun i => bounds rows (free i)) (fun i => bounds rows (slots i)) (boundsList rows as) := by
  cases as with
  | nil => rfl
  | cons a as => simp only [readList, boundsList, map_counts rows free slots a, map_counts_list rows free slots as]
termination_by sizeOf as
end

mutual
theorem shape (free slots : Nat → BoundsTy) (β : BoundsTy) :
    Synth.BoundsTy.toTy (read free slots β) = ty free slots (Synth.BoundsTy.toTy β) := by
  cases β with
  | prim | fvar | bvar => simp only [read, Synth.BoundsTy.toTy, ty]
  | arrow a b => simp only [read, Synth.BoundsTy.toTy, ty, shape free slots a, shape free slots b]
  | list lo hi a =>
      simpa only [read, Synth.BoundsTy.toTy, ty, tys, listTy] using congrArg listTy (shape free slots a)
  | custom name as =>
      simpa only [read, Synth.BoundsTy.toTy, ty] using congrArg (Ty.customTy name) (shape_list free slots as)
termination_by sizeOf β

private theorem shape_list (free slots : Nat → BoundsTy) (as : List BoundsTy) :
    (readList free slots as).map Synth.BoundsTy.toTy = tys free slots (as.map Synth.BoundsTy.toTy) := by
  cases as with
  | nil => rfl
  | cons a as => simp only [readList, List.map_cons, tys, shape free slots a, shape_list free slots as]
termination_by sizeOf as
end

mutual
theorem erased (free slots : Nat → BoundsTy) (τ : Ty) : ty free slots τ.eraseBounds = ty free slots τ := by
  cases τ with
  | prim | fvar | bvar => simp only [ty, Ty.eraseBounds]
  | arrow a b => simp only [ty, Ty.eraseBounds, erased free slots a, erased free slots b]
  | bl lo hi a =>
      simpa only [Ty.eraseBounds, bareListTy, ty, tys, listTy] using congrArg listTy (erased free slots a)
  | customTy name as => exact congrArg (Ty.customTy name) (erased_list free slots as)
termination_by sizeOf τ

private theorem erased_list (free slots : Nat → BoundsTy) (as : List Ty) :
    tys free slots (TyList.eraseBounds as) = tys free slots as := by
  cases as with
  | nil => rfl
  | cons a as => simp only [TyList.eraseBounds, tys, erased free slots a, erased_list free slots as]
termination_by sizeOf as
end

/-- Out-of-range slots remain bound slots, never guessed Unit/type witnesses.
    The consuming signature interface must separately check arity and WF. -/
def vector (args : List BoundsTy) (i : Nat) : BoundsTy := args[i]?.getD (.bvar i)

mutual
theorem counts_blind {free free' slots slots' : Nat → BoundsTy}
    (hf : ∀ i, Synth.BoundsTy.toTy (free i) = Synth.BoundsTy.toTy (free' i))
    (hs : ∀ i, Synth.BoundsTy.toTy (slots i) = Synth.BoundsTy.toTy (slots' i))
    (τ : Ty) : ty free slots τ = ty free' slots' τ := by
  cases τ with
  | prim => rfl
  | fvar i => exact hf i
  | bvar i => exact hs i
  | arrow a b => simp only [ty, counts_blind hf hs a, counts_blind hf hs b]
  | bl lo hi a => exact congrArg listTy (counts_blind hf hs a)
  | customTy name as => exact congrArg (Ty.customTy name) (counts_blind_list hf hs as)
termination_by sizeOf τ

private theorem counts_blind_list {free free' slots slots' : Nat → BoundsTy}
    (hf : ∀ i, Synth.BoundsTy.toTy (free i) = Synth.BoundsTy.toTy (free' i))
    (hs : ∀ i, Synth.BoundsTy.toTy (slots i) = Synth.BoundsTy.toTy (slots' i))
    (as : List Ty) : tys free slots as = tys free' slots' as := by
  cases as with
  | nil => rfl
  | cons a as => simp only [tys, counts_blind hf hs a, counts_blind_list hf hs as]
termination_by sizeOf as
end

#print axioms identity_slots
#print axioms congrFree
#print axioms congrSlots
#print axioms eraseFreeVars
#print axioms map_types
#print axioms map_counts
#print axioms shape
#print axioms counts_blind

end FHM.Bounds.ScopedHMInterpretation
