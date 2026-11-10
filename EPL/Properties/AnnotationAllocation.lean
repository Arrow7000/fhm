import EPL.AnnotationAllocation

namespace EPL

private theorem namedHoleTable_unique (names : List String) (frontier : Nat) :
    (namedHoleTable names frontier).Unique := by
  simp only [HoleAssignment.Unique, namedHoleTable]
  rw [List.map_fst_zip]
  · exact List.nodup_dedup _
  · simp

private theorem lookup_of_mem_key {holes : HoleAssignment} {name : String}
    (hmem : name ∈ holes.map Prod.fst) :
    ∃ ty, holes.lookup name = some ty := by
  induction holes with
  | nil => simp at hmem
  | cons entry rest ih =>
      rcases entry with ⟨key, ty⟩
      simp only [List.map_cons, List.mem_cons] at hmem
      by_cases hkey : name = key
      · subst key
        exact ⟨ty, by simp [List.lookup]⟩
      · obtain ⟨result, hlookup⟩ := ih (hmem.resolve_left hkey)
        have hbeq : (name == key) = false := beq_false_of_ne hkey
        exact ⟨result, by simpa [List.lookup, hbeq] using hlookup⟩

private theorem namedHoleTable_covers {names : List String} {frontier : Nat}
    {name : String} (hmem : name ∈ names) :
    ∃ ty, (namedHoleTable names frontier).lookup name = some ty := by
  apply lookup_of_mem_key
  simp only [namedHoleTable]
  rw [List.map_fst_zip]
  · exact List.mem_dedup.mpr hmem
  · simp

private theorem allocateWith_fits (template : Template) (holes : HoleAssignment)
    (frontier : Nat)
    (hcover : ∀ name ∈ template.names, ∃ ty, holes.lookup name = some ty) :
    template.Fits holes (template.allocateWith holes frontier).2 := by
  induction template generalizing frontier with
  | fixed ty => exact .fixed
  | hole => exact .hole
  | named name =>
      obtain ⟨ty, hlookup⟩ := hcover name (by simp [Template.names])
      simp only [Template.allocateWith, hlookup, Option.getD_some]
      exact .named hlookup
  | arrow domain codomain ihDomain ihCodomain =>
      exact .arrow
        (ihDomain frontier fun name hmem =>
          hcover name (List.mem_append_left _ hmem))
        (ihCodomain (domain.allocateWith holes frontier).1 fun name hmem =>
          hcover name (List.mem_append_right _ hmem))

private theorem lookup_scoped {holes : HoleAssignment} {name : String} {ty : Ty}
    {rigidCount binderCount : Nat}
    (hall : ∀ entry ∈ holes, entry.2.Scoped rigidCount binderCount)
    (hlookup : holes.lookup name = some ty) :
    ty.Scoped rigidCount binderCount := by
  induction holes with
  | nil => simp [List.lookup] at hlookup
  | cons entry rest ih =>
      rcases entry with ⟨key, value⟩
      by_cases hkey : name = key
      · subst key
        simp [List.lookup] at hlookup
        subst ty
        exact hall (name, value) (by simp)
      · apply ih
        · intro entry hmem
          exact hall entry (List.mem_cons_of_mem _ hmem)
        · have hbeq : (name == key) = false := beq_false_of_ne hkey
          simpa [List.lookup, hbeq] using hlookup

private theorem zip_second_scoped {keys : List String} {types : List Ty}
    {entry : String × Ty} {rigidCount binderCount : Nat}
    (hall : ∀ ty ∈ types, ty.Scoped rigidCount binderCount)
    (hmem : entry ∈ keys.zip types) :
    entry.2.Scoped rigidCount binderCount := by
  induction keys generalizing types with
  | nil => simp at hmem
  | cons key keys ih =>
      cases types with
      | nil => simp at hmem
      | cons ty types =>
          simp only [List.zip_cons_cons, List.mem_cons] at hmem
          rcases hmem with rfl | hmem
          · exact hall ty (by simp)
          · exact ih (fun result hresult => hall result (by simp [hresult])) hmem

private theorem namedHoleTable_scoped (names : List String) (frontier : Nat)
    (rigidCount binderCount : Nat) :
    ∀ entry ∈ namedHoleTable names frontier,
      entry.2.Scoped rigidCount binderCount := by
  intro entry hmem
  apply zip_second_scoped (hmem := hmem)
  intro ty hty
  obtain ⟨offset, _, rfl⟩ := List.mem_map.mp hty
  exact .mvar _

private theorem allocateWith_scoped {template : Template} {holes : HoleAssignment}
    {rigidCount binderCount frontier : Nat}
    (hscoped : template.Scoped rigidCount binderCount)
    (hholes : ∀ entry ∈ holes, entry.2.Scoped rigidCount binderCount) :
    (template.allocateWith holes frontier).2.Scoped rigidCount binderCount := by
  induction hscoped generalizing frontier with
  | fixed hwf => exact hwf.1
  | hole => exact .mvar _
  | named =>
      simp only [Template.allocateWith]
      cases hlookup : holes.lookup _ with
      | none =>
          simp only [Option.getD_none]
          exact .mvar _
      | some ty =>
          simp only [Option.getD_some]
          exact lookup_scoped hholes hlookup
  | arrow _ _ ihDomain ihCodomain =>
      exact .arrow ihDomain ihCodomain

/-- The allocator's local named-hole table has no duplicate keys. -/
theorem Template.allocate_unique (template : Template) (frontier : Nat) :
    (template.allocate frontier).holes.Unique := by
  exact namedHoleTable_unique template.names.dedup frontier

/-- The allocated type is a declarative fit of the original template using
exactly the allocator's annotation-local named table. -/
theorem Template.allocate_fits (template : Template) (frontier : Nat) :
    template.Fits (template.allocate frontier).holes
      (template.allocate frontier).ty := by
  apply allocateWith_fits
  intro name hmem
  exact namedHoleTable_covers (List.mem_dedup.mpr hmem)

/-- Allocation preserves authored rigid/bound scope and introduces only
flexible metavariables. -/
theorem Template.allocate_scoped
    {template : Template} {rigidCount binderCount frontier : Nat}
    (hscoped : template.Scoped rigidCount binderCount) :
    (template.allocate frontier).ty.Scoped rigidCount binderCount := by
  apply allocateWith_scoped hscoped
  exact namedHoleTable_scoped template.names.dedup frontier rigidCount binderCount

end EPL
