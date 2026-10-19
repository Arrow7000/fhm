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



private theorem recShape_unify_sourceAvoid (h : UnifyRel ty expected S)
    (ht : w ∉ ty.freeVars) (he : w ∉ expected.freeVars) :
    (∀ p ∈ S, w ∉ p.2.freeVars) ∧ w ∉ S.map Prod.fst := by
  constructor
  · intro p hp hw
    exact (h.range_mem p hp w hw).elim ht he
  · intro hw
    obtain ⟨p, hp, heq⟩ := List.mem_map.mp hw
    have hm := h.dom_mem p hp
    rw [heq] at hm
    exact hm.elim ht he

theorem CheckRecShapes.sourceAvoid (h : CheckRecShapes K shapes S)
    (hshapes : ∀ shape ∈ shapes, w ∉ shape.1.freeVars ∧
      ∀ expected, shape.2 = some expected → w ∉ expected.freeVars) :
    (∀ p ∈ S, w ∉ p.2.freeVars) ∧ w ∉ S.map Prod.fst := by
  induction h with
  | nil => simp
  | skipNone _ ih => exact ih (fun shape hm => hshapes shape (List.mem_cons_of_mem _ hm))
  | @consSome ty expected first rest tail hu ht ih =>
      have hh := hshapes (ty, some expected) List.mem_cons_self
      have hfirst := recShape_unify_sourceAvoid hu.unifies hh.1 (hh.2 expected rfl)
      have htail := ih (by
        intro shape hm
        obtain ⟨⟨original, expected⟩, ho, heq⟩ := List.mem_map.mp hm
        subst shape
        have hold := hshapes (original, expected) (List.mem_cons_of_mem _ ho)
        refine ⟨Subst.notMemOnTy hfirst.1 hold.1, ?_⟩
        intro target ht
        obtain ⟨old, holdEq, rfl⟩ := Option.map_eq_some_iff.mp ht
        exact Subst.notMemOnTy hfirst.1 (hold.2 old holdEq))
      refine ⟨fun p hp => (List.mem_append.mp hp).elim (hfirst.1 p) (htail.1 p), ?_⟩
      simpa only [List.map_append, List.mem_append, not_or] using And.intro hfirst.2 htail.2


end Elaboration


namespace Elaboration

private theorem recShape_solutions_factor {shapes : List RecShape} {S U R : Subst}
    (hsolve : ∀ ty expected, (ty,some expected) ∈ shapes → U.onTy ty = U.onTy expected)
    (hfactor : ∀ ty, U.onTy ty = R.onTy (S.onTy ty)) :
    ∀ ty expected, (ty,some expected) ∈ substRecShapes S shapes → R.onTy ty = R.onTy expected := by
  intro ty expected hm
  obtain ⟨⟨oldTy,oldExpected⟩,hmem,heq⟩ := List.mem_map.mp hm
  cases oldExpected with
  | none => cases heq
  | some oldExpected =>
    cases heq
    rw [←hfactor oldTy,←hfactor oldExpected]
    exact hsolve oldTy oldExpected hmem

/-- A successful shape pass is principal for every LC solution, preserving an
independent protected set. Neither source LC nor a frontier is needed here. -/
theorem CheckRecShapes.factor {K P : List Nat} {shapes : List RecShape} {S U : Subst}
    (h : CheckRecShapes K shapes S) (hU : ∀ p ∈ U, p.2.IsLC)
    (hsolve : ∀ ty expected, (ty,some expected) ∈ shapes → U.onTy ty = U.onTy expected)
    (hP : ∀ p ∈ P, U.onTy (.fvar p) = .fvar p) :
    ∃ R : Subst, (∀ p ∈ R,p.2.IsLC) ∧ (∀ p ∈ P,R.onTy (.fvar p) = .fvar p) ∧
      ∀ ty,U.onTy ty = R.onTy (S.onTy ty) := by
  induction h generalizing U with
  | nil => exact ⟨U,hU,hP,fun _ => rfl⟩
  | skipNone hr ih => exact ih hU (fun ty expected hm => hsolve ty expected (List.mem_cons_of_mem _ hm)) hP
  | consSome hu hr ih =>
    obtain ⟨V,hfac,hV,hVP⟩ := hu.unifies.greatest_K U hU (hsolve _ _ List.mem_cons_self) hP
    obtain ⟨R,hR,hRP,hrest⟩ := ih hV
      (recShape_solutions_factor (fun ty expected hm => hsolve ty expected (List.mem_cons_of_mem _ hm)) hfac) hVP
    exact ⟨R,hR,hRP,fun ty => by rw [hfac ty,hrest,Subst.onTy_append]⟩

/-- Any LC solution fixing the actual rigid set makes the executable shape
checker succeed. Candidate targets may contain arbitrary variable IDs. -/
theorem checkRecShapes_complete {K : List Nat} {shapes : List RecShape} {U : Subst}
    (hLC : ∀ shape ∈ shapes, RecShape.LC shape) (hU : ∀ p ∈ U,p.2.IsLC)
    (hsolve : ∀ ty expected,(ty,some expected) ∈ shapes → U.onTy ty = U.onTy expected)
    (hK : ∀ k ∈ K,U.onTy (.fvar k) = .fvar k) :
    (checkRecShapes K shapes).isSome := by
  match shapes with
  | [] => simp only [checkRecShapes,Option.isSome_some]
  | (ty,none)::rest =>
    have ht := checkRecShapes_complete
      (fun shape hm => hLC shape (List.mem_cons_of_mem _ hm)) hU
      (fun ty expected hm => hsolve ty expected (List.mem_cons_of_mem _ hm)) hK
    cases hc : checkRecShapes K rest with
    | none => simp only [hc,Option.isSome_none] at ht; contradiction
    | some result => simp only [checkRecShapes,hc,Option.isSome_some]
  | (ty,some expected)::rest =>
    have hh := hLC (ty,some expected) List.mem_cons_self
    have hu := unifyCoreK_complete hh.1 (hh.2 expected rfl) hU (hsolve _ _ List.mem_cons_self) hK
    cases hc : unifyCoreK K ty expected with
    | none => simp only [hc,Option.isSome_none] at hu; contradiction
    | some result =>
      obtain ⟨first,hfirst,havoid⟩ := result
      have hfirstLC := hfirst.lc hh.1 (hh.2 expected rfl)
      obtain ⟨V,hfac,hV,hVK⟩ := hfirst.greatest_K U hU (hsolve _ _ List.mem_cons_self) hK
      have ht := checkRecShapes_complete
        (substRecShapes_lc hfirstLC (fun shape hm => hLC shape (List.mem_cons_of_mem _ hm))) hV
        (recShape_solutions_factor (fun ty expected hm => hsolve ty expected (List.mem_cons_of_mem _ hm)) hfac) hVK
      cases ht' : checkRecShapes K (substRecShapes first rest) with
      | none => simp only [ht',Option.isSome_none] at ht; contradiction
      | some tail => simp only [checkRecShapes,hc,ht',Option.isSome_some]
 termination_by shapes.length
 decreasing_by all_goals simp_wf

end Elaboration
