import FHM.Elaboration.RecOpening

namespace Elaboration

abbrev RecShape := Ty × Option Ty

def substRecShapes (S : Subst) (shapes : List RecShape) : List RecShape :=
  shapes.map (fun shape => (S.onTy shape.1, shape.2.map S.onTy))

@[simp] theorem substRecShapes_length (S : Subst) (shapes : List RecShape) :
    (substRecShapes S shapes).length = shapes.length := by simp [substRecShapes]

/-- Solve all component shapes before entering any recursive body. -/
inductive CheckRecShapes (K : List Nat) : List RecShape → Subst → Prop
  | nil : CheckRecShapes K [] []
  | skipNone : CheckRecShapes K rest S → CheckRecShapes K ((ty, none) :: rest) S
  | consSome : RigidUnify K ty expected first →
      CheckRecShapes K (substRecShapes first rest) tail →
      CheckRecShapes K ((ty, some expected) :: rest) (first ++ tail)

/-- One rigidity-aware unification for each expected shape; no allocation. -/
def checkRecShapes (K : List Nat) (shapes : List RecShape) :
    Option { S : Subst // CheckRecShapes K shapes S } :=
  match shapes with
  | [] => some ⟨[], .nil⟩
  | (ty, none) :: rest =>
      match checkRecShapes K rest with
      | none => none
      | some ⟨S, hS⟩ => some ⟨S, .skipNone hS⟩
  | (ty, some expected) :: rest =>
      match unifyCoreK K ty expected with
      | none => none
      | some ⟨first, hu, hav⟩ =>
          match checkRecShapes K (substRecShapes first rest) with
          | none => none
          | some ⟨tail, ht⟩ => some ⟨first ++ tail, .consSome ⟨hu, hav⟩ ht⟩
termination_by shapes.length
decreasing_by all_goals simp_wf

/-- Both the shared monotype and optional expected shape are locally closed. -/
def RecShape.LC (shape : RecShape) : Prop :=
  shape.1.IsLC ∧ ∀ ty, shape.2 = some ty → ty.IsLC

def RecShape.BelowFvars (frontier : Nat) (shape : RecShape) : Prop :=
  Ty.BelowFvars frontier shape.1 ∧ ∀ ty, shape.2 = some ty → Ty.BelowFvars frontier ty

theorem substRecShapes_lc {S : Subst} (hS : ∀ pair ∈ S, pair.2.IsLC)
    (h : ∀ shape ∈ shapes, RecShape.LC shape) :
    ∀ shape ∈ substRecShapes S shapes, RecShape.LC shape := by
  intro shape hm
  unfold substRecShapes at hm
  obtain ⟨originalShape, horiginal, heq⟩ := List.mem_map.mp hm
  subst shape
  rcases originalShape with ⟨ty, expected⟩
  obtain ⟨hty, he⟩ := h _ horiginal
  refine ⟨Subst.onTy_lc hS hty, ?_⟩
  intro target ht
  obtain ⟨original, ho, rfl⟩ := Option.map_eq_some_iff.mp ht
  exact Subst.onTy_lc hS (he original ho)

theorem substRecShapes_below {S : Subst} (hS : ∀ pair ∈ S, Ty.BelowFvars frontier pair.2)
    (h : ∀ shape ∈ shapes, RecShape.BelowFvars frontier shape) :
    ∀ shape ∈ substRecShapes S shapes, RecShape.BelowFvars frontier shape := by
  intro shape hm
  unfold substRecShapes at hm
  obtain ⟨originalShape, horiginal, heq⟩ := List.mem_map.mp hm
  subst shape
  rcases originalShape with ⟨ty, expected⟩
  obtain ⟨hty, he⟩ := h _ horiginal
  refine ⟨Subst.onTy_belowFvars hS hty, ?_⟩
  intro target ht
  obtain ⟨original, ho, rfl⟩ := Option.map_eq_some_iff.mp ht
  exact Subst.onTy_belowFvars hS (he original ho)

theorem CheckRecShapes.dom_avoids (h : CheckRecShapes K shapes S) :
    ∀ pair ∈ S, pair.1 ∉ K := by
  induction h with
  | nil => simp
  | skipNone _ ih => exact ih
  | consSome hu _ ih =>
      intro pair hp
      exact (List.mem_append.mp hp).elim (hu.dom_avoids pair) (ih pair)

theorem CheckRecShapes.lc (h : CheckRecShapes K shapes S)
    (hshapes : ∀ shape ∈ shapes, RecShape.LC shape) : ∀ pair ∈ S, pair.2.IsLC := by
  induction h with
  | nil => simp
  | skipNone _ ih => exact ih (fun shape hm => hshapes shape (List.mem_cons_of_mem _ hm))
  | @consSome ty expected first rest tail hu ht ih =>
      have hh := hshapes (ty, some expected) (List.mem_cons_self)
      have hfirst := hu.unifies.lc hh.1 (hh.2 expected rfl)
      have htail := ih (substRecShapes_lc hfirst (fun shape hm => hshapes shape (List.mem_cons_of_mem _ hm)))
      intro pair hp
      exact (List.mem_append.mp hp).elim (hfirst pair) (htail pair)

theorem CheckRecShapes.belowFvars (h : CheckRecShapes K shapes S)
    (hshapes : ∀ shape ∈ shapes, RecShape.BelowFvars frontier shape) :
    ∀ pair ∈ S, Ty.BelowFvars frontier pair.2 := by
  induction h with
  | nil => simp
  | skipNone _ ih => exact ih (fun shape hm => hshapes shape (List.mem_cons_of_mem _ hm))
  | @consSome ty expected first rest tail hu ht ih =>
      have hh := hshapes (ty, some expected) (List.mem_cons_self)
      have hfirst := hu.unifies.belowFvars hh.1 (hh.2 expected rfl)
      have htail := ih (substRecShapes_below hfirst (fun shape hm => hshapes shape (List.mem_cons_of_mem _ hm)))
      intro pair hp
      exact (List.mem_append.mp hp).elim (hfirst pair) (htail pair)

end Elaboration

