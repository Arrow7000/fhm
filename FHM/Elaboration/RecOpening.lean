import FHM.Elaboration.Typing

namespace Elaboration

structure RecOpening where
  written : List Nat
  expected : Option Ty

def RecOpening.empty : RecOpening := ⟨[], none⟩

/-- Allocate flexible written slots and partial expected shapes, without
changing scope or performing inference. Complete contracts are handled later. -/
inductive OpenRecAnn : Nat → LetAnn → Nat → RecOpening → Prop
  | absent : OpenRecAnn frontier .absent frontier .empty
  | complete : OpenRecAnn frontier (.complete scheme) frontier .empty
  | template :
      template.allocate frontier = (next, ty) → ty.IsLC →
      OpenRecAnn frontier (.template template) next ⟨[], some ty⟩
  | partialForall :
      (template.openTyVarsFrom 0 (freshVars frontier count)).allocate (frontier + count) = (next, ty) →
      ty.IsLC →
      OpenRecAnn frontier (.partialForall count template) next ⟨freshVars frontier count, some ty⟩

/-- Scan the whole aligned annotation list; only selected indices allocate. -/
inductive OpenRecAnns (selected : List Nat) : Nat → Nat → List LetAnn → Nat → List RecOpening → Prop
  | nil : OpenRecAnns selected index frontier [] frontier []
  | skip :
      index ∉ selected → OpenRecAnns selected (index + 1) frontier rest next openings →
      OpenRecAnns selected index frontier (ann :: rest) next (.empty :: openings)
  | cons :
      index ∈ selected → OpenRecAnn frontier ann middle opening →
      OpenRecAnns selected (index + 1) middle rest next openings →
      OpenRecAnns selected index frontier (ann :: rest) next (opening :: openings)

def openRecAnn (frontier : Nat) (ann : LetAnn) :
    Option { result : Nat × RecOpening // OpenRecAnn frontier ann result.1 result.2 } :=
  match ann with
  | .absent => some ⟨(frontier, .empty), .absent⟩
  | .complete _ => some ⟨(frontier, .empty), .complete⟩
  | .template template =>
      let result := template.allocate frontier
      if hlc : result.2.bvarsBelow 0 = true then
        some ⟨(result.1, ⟨[], some result.2⟩), .template rfl ((Ty.bvarsBelow_iff _).mp hlc)⟩
      else none
  | .partialForall count template =>
      let written := freshVars frontier count
      let result := (template.openTyVarsFrom 0 written).allocate (frontier + count)
      if hlc : result.2.bvarsBelow 0 = true then
        some ⟨(result.1, ⟨written, some result.2⟩), .partialForall rfl ((Ty.bvarsBelow_iff _).mp hlc)⟩
      else none

def openRecAnns (selected : List Nat) (index frontier : Nat) (anns : List LetAnn) :
    Option { result : Nat × List RecOpening // OpenRecAnns selected index frontier anns result.1 result.2 } :=
  match anns with
  | [] => some ⟨(frontier, []), .nil⟩
  | ann :: rest =>
      if hs : index ∈ selected then
        match openRecAnn frontier ann with
        | none => none
        | some ⟨(middle, opening), hhead⟩ =>
            match openRecAnns selected (index + 1) middle rest with
            | none => none
            | some ⟨(next, openings), htail⟩ =>
                some ⟨(next, opening :: openings), .cons hs hhead htail⟩
      else
        match openRecAnns selected (index + 1) frontier rest with
        | none => none
        | some ⟨(next, openings), htail⟩ =>
            some ⟨(next, .empty :: openings), .skip hs htail⟩

theorem OpenRecAnns.length (h : OpenRecAnns selected index frontier anns next openings) :
    openings.length = anns.length := by
  induction h with
  | nil => rfl
  | skip _ _ ih => exact congrArg Nat.succ ih
  | cons _ _ _ ih => exact congrArg Nat.succ ih

theorem OpenRecAnn.expected_lc (h : OpenRecAnn frontier ann next opening)
    (he : opening.expected = some ty) : ty.IsLC := by
  cases h with
  | absent | complete => cases he
  | template _ hlc => exact Option.some.inj he ▸ hlc
  | partialForall _ hlc => exact Option.some.inj he ▸ hlc

theorem OpenRecAnns.expected_lc (h : OpenRecAnns selected index frontier anns next openings) :
    ∀ opening ∈ openings, ∀ ty, opening.expected = some ty → ty.IsLC := by
  induction h with
  | nil => intro opening hm; cases hm
  | skip _ _ ih =>
    intro opening hm ty he
    rcases List.mem_cons.mp hm with rfl | hm
    · cases he
    · exact ih opening hm ty he
  | cons _ hhead _ ih =>
    intro opening hm ty he
    rcases List.mem_cons.mp hm with rfl | hm
    · exact hhead.expected_lc he
    · exact ih opening hm ty he


theorem OpenRecAnn.frontier_le (h : OpenRecAnn frontier ann next opening) : frontier ≤ next := by
  cases h with
  | absent | complete => exact Nat.le_refl _
  | @template next ty frontier template heq _ =>
    have hle := (template.allocate_bounds frontier).1
    rwa [heq] at hle
  | @partialForall next ty frontier count template heq _ =>
    have hle := ((template.openTyVarsFrom 0 (freshVars frontier count)).allocate_bounds (frontier + count)).1
    rw [heq] at hle
    exact (Nat.le_add_right _ _).trans hle

theorem OpenRecAnns.frontier_le (h : OpenRecAnns selected index frontier anns next openings) :
    frontier ≤ next := by
  induction h with
  | nil => exact Nat.le_refl _
  | skip _ _ ih => exact ih
  | cons _ hhead _ ih => exact hhead.frontier_le.trans ih

theorem OpenRecAnn.written_nodup (h : OpenRecAnn frontier ann next opening) : opening.written.Nodup := by
  cases h with
  | absent | complete | template => exact List.nodup_nil
  | partialForall => exact freshVars_nodup

theorem OpenRecAnn.written_length (h : OpenRecAnn frontier ann next opening) :
    opening.written.length = (match ann with | .partialForall n _ => n | _ => 0) := by
  cases h <;> simp [RecOpening.empty, freshVars_length]

theorem OpenRecAnn.written_range (h : OpenRecAnn frontier ann next opening) :
    ∀ v ∈ opening.written, frontier ≤ v ∧ v < next := by
  cases h with
  | absent | complete | template => intro v hv; cases hv
  | @partialForall next ty frontier count template heq hlc =>
    have hle := ((template.openTyVarsFrom 0 (freshVars frontier count)).allocate_bounds (frontier + count)).1
    rw [heq] at hle
    intro v hv
    exact ⟨freshVars_ge v hv, Nat.lt_of_lt_of_le (freshVars_lt v hv) hle⟩

theorem OpenRecAnns.written_range (h : OpenRecAnns selected index frontier anns next openings) :
    ∀ v ∈ openings.flatMap RecOpening.written, frontier ≤ v ∧ v < next := by
  induction h with
  | nil => intro v hv; cases hv
  | skip _ _ ih =>
    simpa only [List.flatMap_cons, RecOpening.empty, List.nil_append] using ih
  | cons _ hhead htail ih =>
    intro v hv
    rcases List.mem_append.mp hv with hv | hv
    · have hh := hhead.written_range v hv
      exact ⟨hh.1, Nat.lt_of_lt_of_le hh.2 htail.frontier_le⟩
    · have ht := ih v hv
      exact ⟨hhead.frontier_le.trans ht.1, ht.2⟩

theorem OpenRecAnns.written_nodup (h : OpenRecAnns selected index frontier anns next openings) :
    (openings.flatMap RecOpening.written).Nodup := by
  induction h with
  | nil => exact List.nodup_nil
  | skip _ _ ih =>
    simpa only [List.flatMap_cons, RecOpening.empty, List.nil_append] using ih
  | cons _ hhead htail ih =>
    refine List.nodup_append.mpr ⟨hhead.written_nodup, ih, ?_⟩
    intro v hv w hw heq
    have hh := hhead.written_range v hv
    have ht := htail.written_range w hw
    omega

theorem OpenRecAnn.expected_below (h : OpenRecAnn frontier ann next opening)
    (hraw : ∀ v ∈ ann.rigidVars, v < frontier)
    (he : opening.expected = some ty) : Ty.BelowFvars next ty := by
  cases h with
  | absent | complete => cases he
  | @template next target frontier template heq _ =>
    have hb := (template.allocate_bounds frontier).2 hraw
    rw [heq] at hb
    exact Option.some.inj he ▸ hb
  | @partialForall next target frontier count template heq _ =>
    have hopen : ∀ v ∈ (template.openTyVarsFrom 0 (freshVars frontier count)).rigidVars,
        v < frontier + count := by
      intro v hv
      have hmem := template.openTyVarsFrom_scope (K := template.rigidVars) (fun _ h => h)
        0 (freshVars frontier count) v hv
      rcases List.mem_append.mp hmem with hmem | hmem
      · have hvold := hraw v hmem
        omega
      · exact freshVars_lt v hmem
    have hb := ((template.openTyVarsFrom 0 (freshVars frontier count)).allocate_bounds (frontier + count)).2 hopen
    rw [heq] at hb
    exact Option.some.inj he ▸ hb

theorem OpenRecAnns.expected_below (h : OpenRecAnns selected index frontier anns next openings)
    (hraw : ∀ ann ∈ anns, ∀ v ∈ ann.rigidVars, v < frontier) :
    ∀ opening ∈ openings, ∀ ty, opening.expected = some ty → Ty.BelowFvars next ty := by
  induction h with
  | nil => intro opening hm; cases hm
  | skip _ _ ih =>
    intro opening hm ty he
    rcases List.mem_cons.mp hm with rfl | hm
    · cases he
    · exact ih (fun ann ha => hraw ann (List.mem_cons_of_mem _ ha)) opening hm ty he
  | cons _ hhead htail ih =>
    intro opening hm ty he
    rcases List.mem_cons.mp hm with rfl | hm
    · exact (hhead.expected_below (hraw _ List.mem_cons_self) he).mono htail.frontier_le
    · exact ih (fun ann ha v hv => Nat.lt_of_lt_of_le
        (hraw ann (List.mem_cons_of_mem _ ha) v hv) hhead.frontier_le) opening hm ty he

theorem OpenRecAnns.expectedTypes_lc (h : OpenRecAnns selected index frontier anns next openings) :
    ∀ ty ∈ openings.filterMap RecOpening.expected, ty.IsLC := by
  intro ty hm
  obtain ⟨opening, hopening, he⟩ := List.mem_filterMap.mp hm
  exact h.expected_lc opening hopening ty he

theorem OpenRecAnns.expectedTypes_below (h : OpenRecAnns selected index frontier anns next openings)
    (hraw : ∀ ann ∈ anns, ∀ v ∈ ann.rigidVars, v < frontier) :
    ∀ ty ∈ openings.filterMap RecOpening.expected, Ty.BelowFvars next ty := by
  intro ty hm
  obtain ⟨opening, hopening, he⟩ := List.mem_filterMap.mp hm
  exact h.expected_below hraw opening hopening ty he

end Elaboration
