import FHM.AnnotationAllocation

/-! Shared allocation and factorization for production annotation checking.
Named tables are local to an annotation; anonymous occurrences stay distinct. -/

namespace PartialCore.AllocationTests

def pair (a b : Ty) : Ty := .customTy ⟨"Pair"⟩ [a, b]
def repeated : Template := .custom ⟨"Pair"⟩ [.named "item", .named "item"]

#guard match allocate 5 repeated with
  | some a => a.frontier == 6 && a.completion.holes.length == 1 && match a.ty with
    | .customTy _ [.fvar x, .fvar y] => x == y
    | _ => false
  | none => false

#guard match allocate 5 (.custom ⟨"Triple"⟩ [.named "item", .hole, .named "item"]) with
  | some a => a.frontier == 7 && match a.ty with
    | .customTy _ [.fvar x, .fvar y, .fvar z] => x == z && x != y
    | _ => false
  | none => false

#guard match allocate 5 (.named "item"), allocate 10 (.named "item") with
  | some a, some b => match a.ty, b.ty with
    | .fvar x, .fvar y => x != y
    | _, _ => false
  | _, _ => false

theorem repeated_fit : repeated.Fits [("item", .prim .int)] (pair (.prim .int) (.prim .int)) :=
  .custom (.cons (.named rfl) (.cons (.named rfl) .nil))

private theorem pair_lc (a b : Ty) (ha : a.IsLC) (hb : b.IsLC) : (pair a b).IsLC := by
  apply ContainsBvarsUpTo.customTy
  intro ty ht
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl
  · exact ha
  · exact hb

-- The executable checker reports the same solved assignment its proof matches.
#guard match checkAnnotation 5 repeated (pair (.prim .int) (.prim .int))
    (pair_lc _ _ .prim .prim) with
  | some checked => match LookupList.get? checked.completion.holes "item" with
    | some (.prim .int) => true
    | _ => false
  | none => false
#guard (checkAnnotation 5 repeated (pair (.prim .int) (.prim .char))
  (pair_lc _ _ .prim .prim)).isNone
#guard match checkAnnotationResult 5 repeated (pair (.prim .int) (.prim .char))
    (pair_lc _ _ .prim .prim) with
  | .error (.unification (.mismatch (.prim .int) (.prim .char))) => true
  | _ => false
#guard match allocateResult 5 (.fixed (.bvar 0)) with
  | .error (.invalidBoundVariables (.bvar 0) 0) => true
  | _ => false

/-- The factor realizes one named solution, with proof of the reported lookup.
Production inference uses this same theorem for anonymous and named holes. -/
theorem repeated_factor (Φ : Nat) :
    ∃ U : Subst, (∀ p ∈ U, p.2.IsLC) ∧ Subst.AgreesBelow Φ [] U ∧
      U.onTy (repeated.allocate Φ).2 = pair (.prim .int) (.prim .int) ∧
      ∀ name ∈ repeated.names,
        LookupList.get? (HoleAssignment.map U.onTy (repeated.allocationHoles Φ)) name =
          LookupList.get? [("item", .prim .int)] name := by
  apply Template.Fits.allocate_override_source (S0 := [])
  · exact repeated_fit
  · apply ContainsBvarsUpTo.customTy
    intro ty ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl <;> exact .prim
  · intro entry he
    simp only [List.mem_singleton] at he
    subst entry
    exact .prim
  · simp
  · simp [repeated, Template.rigidVars, templateRigidVars]

/-- Targets may mention allocated variables. Earlier ambient images still
remain unchanged; the factor does not assume a globally fresh target. -/
theorem overlapping_target_factor (Φ : Nat) :
    ∃ U : Subst, (∀ p ∈ U, p.2.IsLC) ∧
      Subst.AgreesBelow Φ [(0, .fvar Φ)] U ∧
      U.onTy (repeated.allocate Φ).2 = pair (.fvar Φ) (.fvar Φ) ∧
      ∀ name ∈ repeated.names,
        LookupList.get? (HoleAssignment.map U.onTy (repeated.allocationHoles Φ)) name =
          LookupList.get? [("item", .fvar Φ)] name := by
  apply Template.Fits.allocate_override_source (S0 := [(0, .fvar Φ)])
  · exact .custom (.cons (.named rfl) (.cons (.named rfl) .nil))
  · apply ContainsBvarsUpTo.customTy
    intro ty ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl <;> exact .fvar
  · intro entry he
    simp only [List.mem_singleton] at he
    subst entry
    exact .fvar
  · intro entry he
    simp only [List.mem_singleton] at he
    subst entry
    exact .fvar
  · simp [repeated, Template.rigidVars, templateRigidVars]

def opened (x : Nat) : Template := .arrow (.fixed (.fvar x)) (.named "item")

/-- Opening the written binder gives the same local named solution at each
opening. The declarative completion is stored before these openings. -/
theorem written_factor (x Φ : Nat) (hx : x < Φ) :
    ∃ U : Subst, (∀ p ∈ U, p.2.IsLC) ∧ Subst.AgreesBelow Φ [] U ∧
      U.onTy ((opened x).allocate Φ).2 = .arrow (.fvar x) (.fvar x) ∧
      ∀ name ∈ (opened x).names,
        LookupList.get? (HoleAssignment.map U.onTy ((opened x).allocationHoles Φ)) name =
          LookupList.get? [("item", .fvar x)] name := by
  apply Template.Fits.allocate_override_source (S0 := [])
  · exact .arrow .fixed (.named rfl)
  · exact .arrow .fvar .fvar
  · intro entry he
    simp only [List.mem_singleton] at he
    subst entry
    exact .fvar
  · simp
  · simpa only [opened, Template.rigidVars, Ty.freeVars, List.append_nil,
      List.mem_singleton, forall_eq] using hx

example (Φ : Nat) : Φ ≤ (repeated.allocate Φ).1 := (repeated.allocate_bounds Φ).1
example (Φ : Nat) : (repeated.allocate Φ).2.IsLC :=
  Template.allocate_lc (.custom (by
    intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl <;> exact .named)) Φ

-- Malformed authored bound variables cannot pass the allocation check.
#guard (allocate 0 (.fixed (.bvar 0))).isNone

-- Completion keeps only the relevant local keys. Unused, unscoped entries
-- do not force an arbitrary extra solution or a uniqueness claim about it.
def noisy : HoleAssignment :=
  [("unused", .bvar 99), ("item", .prim .int), ("item", .prim .char)]
theorem noisy_fits : repeated.Fits noisy (pair (.prim .int) (.prim .int)) :=
  .custom (.cons (.named rfl) (.cons (.named rfl) .nil))
def normalized : Completion 0 repeated (pair (.prim .int) (.prim .int)) :=
  noisy_fits.completion (.customTy (by
    intro ty ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl <;> exact .prim))
#guard normalized.holes.length == 1
#guard match LookupList.get? normalized.holes "item" with
  | some (.prim .int) => true
  | _ => false
#guard (LookupList.get? normalized.holes "unused").isNone

#print axioms Template.Fits.allocate_override_source
#print axioms Template.Fits.completion
#print axioms Template.allocate_bounds
#print axioms Template.Fits.allocate_lc_source
#print axioms repeated_factor
#print axioms overlapping_target_factor
#print axioms written_factor

end PartialCore.AllocationTests
