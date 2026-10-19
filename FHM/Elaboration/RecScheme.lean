import FHM.Elaboration.Input
import FHM.CoreBackend.Infer

/-! Ordered completion schemes for recursive members. Written slots retain
all authored positions; remaining occurring pool variables follow them. -/

namespace Elaboration

/-- Preserve the written prefix, including vacuous slots, then quantify the
remaining pool variables that occur in this member's monotype. -/
def recNames (written pool : List Nat) (ty : Ty) : List Nat :=
  written ++ pool.filter (fun v => decide (v ∈ ty.freeVars) && decide (v ∉ written))

def recScheme (written pool : List Nat) (ty : Ty) : PolyTy :=
  ⟨(recNames written pool ty).length, Ty.closeOver (recNames written pool ty) ty⟩

/-- Complete signatures retain their exact scheme; monotypes use the member's
own ordered written prefix and the shared pool. -/
def _root_.RecSpec.completedScheme (written pool : List Nat) : RecSpec → PolyTy
  | .mono ty => recScheme written pool ty
  | .poly scheme => scheme

@[simp] theorem recNames_take_prefix (written pool : List Nat) (ty : Ty) :
    (recNames written pool ty).take written.length = written := by
  simp [recNames]

theorem recNames_prefix (written pool : List Nat) (ty : Ty) :
    List.IsPrefix written (recNames written pool ty) :=
  ⟨_, rfl⟩

theorem recNames_prefix_length_le (written pool : List Nat) (ty : Ty) :
    written.length ≤ (recNames written pool ty).length := by
  simp only [recNames, List.length_append]
  omega

@[simp] theorem mem_recNames {written pool : List Nat} {ty : Ty} {v : Nat} :
    v ∈ recNames written pool ty ↔
      v ∈ written ∨ (v ∈ pool ∧ v ∈ ty.freeVars ∧ v ∉ written) := by
  simp [recNames, List.mem_filter]

theorem recNames_nodup {written pool : List Nat} {ty : Ty}
    (hprefix : written.Nodup) (hpool : pool.Nodup) :
    (recNames written pool ty).Nodup := by
  refine List.nodup_append.mpr ⟨hprefix, hpool.filter _, ?_⟩
  intro v hv w hw heq
  have hparts : w ∈ ty.freeVars ∧ w ∉ written := by
    simpa only [Bool.and_eq_true, decide_eq_true_eq] using (List.mem_filter.mp hw).2
  exact hparts.2 (heq ▸ hv)

/-- Every pool variable occurring in this member is quantified. -/
theorem mem_recNames_of_mem_pool {written pool : List Nat} {ty : Ty} {v : Nat}
    (hpool : v ∈ pool) (hfree : v ∈ ty.freeVars) :
    v ∈ recNames written pool ty := by
  by_cases hp : v ∈ written
  · exact mem_recNames.mpr (Or.inl hp)
  · exact mem_recNames.mpr (Or.inr ⟨hpool, hfree, hp⟩)

theorem not_mem_pool_of_not_mem_recNames {written pool : List Nat} {ty : Ty} {v : Nat}
    (hfree : v ∈ ty.freeVars) (hnames : v ∉ recNames written pool ty) : v ∉ pool :=
  fun hpool => hnames (mem_recNames_of_mem_pool hpool hfree)

theorem recScheme_wf {written pool : List Nat} {ty : Ty} (hlc : ty.IsLC) :
    (recScheme written pool ty).WF :=
  Ty.closeOver_preserves_bvars hlc

/-- Closing names generalizes the original monotype; uniqueness is needed for
other opening arguments, but not for this direction of scheme generality. -/
theorem recScheme_generalizes_mono {written pool : List Nat} {ty : Ty} (hlc : ty.IsLC) :
    (recScheme written pool ty).Generalizes (PolyTy.mkTrivial ty) := by
  intro args target _ hinst
  have htarget : target = ty := InstantiatesBy.eq_of_closed hlc hinst
  subst target
  refine ⟨(recNames written pool ty).map Ty.fvar, ?_, ?_⟩
  · intro t ht
    obtain ⟨_, _, heq⟩ := List.mem_map.mp ht
    rw [← heq]
    exact .fvar
  · have hopen := InstantiatesBy.openVars (Xs := recNames written pool ty)
      (Ty.closeOver_preserves_bvars hlc) (Nat.le_refl _)
    rwa [Ty.openVars_closeOver_self hlc] at hopen

/-- Closing the occurring pool variables leaves only outer variables free. -/
theorem recScheme_freeVars_outer {written pool outer : List Nat} {ty : Ty}
    (hcover : ∀ v ∈ ty.freeVars, v ∈ pool ++ outer) :
    ∀ v ∈ (recScheme written pool ty).body.freeVars, v ∈ outer := by
  intro v hv
  have hty := Ty.freeVars_closeOver_subset hv
  rcases List.mem_append.mp (hcover v hty) with hpool | houter
  · exact False.elim (Ty.not_mem_closeOver_freeVars
      (mem_recNames_of_mem_pool hpool hty) hv)
  · exact houter

@[simp] theorem _root_.RecSpec.completedScheme_mono (written pool : List Nat) (ty : Ty) :
    RecSpec.completedScheme written pool (.mono ty) = recScheme written pool ty := rfl

@[simp] theorem _root_.RecSpec.completedScheme_poly (written pool : List Nat) (scheme : PolyTy) :
    RecSpec.completedScheme written pool (.poly scheme) = scheme := rfl

theorem _root_.RecSpec.completedScheme_wf {written pool : List Nat} {spec : RecSpec}
    (h : spec.LC) : (spec.completedScheme written pool).WF := by
  cases spec with
  | mono ty => exact recScheme_wf h
  | poly scheme => exact h

end Elaboration
