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



/-- Read a list of bare variable images without changing their order. -/
private def recWrittenNames : List Ty → Option (List Nat)
  | [] => some []
  | .fvar name :: rest => (recWrittenNames rest).map (name :: ·)
  | _ :: _ => none

private theorem recWrittenNames_sound {images : List Ty} {names : List Nat}
    (h : recWrittenNames images = some names) : names.map Ty.fvar = images := by
  induction images generalizing names with
  | nil => cases h; rfl
  | cons ty rest ih =>
      cases ty with
      | fvar name =>
          simp only [recWrittenNames, Option.map_eq_some_iff] at h
          obtain ⟨tail, ht, rfl⟩ := h
          simpa only [List.map_cons] using congrArg (Ty.fvar name :: ·) (ih ht)
      | prim | arrow | bvar | customTy => cases h

private theorem recWrittenNames_map (names : List Nat) :
    recWrittenNames (names.map Ty.fvar) = some names := by
  induction names with
  | nil => rfl
  | cons name rest ih => simp only [List.map_cons, recWrittenNames, ih, Option.map_some]

/-- Validate one member's normalized prefix. Sharing roots with another member
is permitted; this call checks distinctness only within the supplied prefix. -/
def resolveRecWritten (images : List Ty) (forbidden : List Nat) :
    Option { names : List Nat // names.map Ty.fvar = images ∧ names.Nodup ∧
      ∀ name ∈ names, name ∉ forbidden } :=
  match hp : recWrittenNames images with
  | none => none
  | some names =>
      if hnd : names.Nodup then
        if havoid : ∀ name ∈ names, name ∉ forbidden then
          some ⟨names, recWrittenNames_sound hp, hnd, havoid⟩
        else none
      else none

theorem resolveRecWritten_isSome_iff : (resolveRecWritten images forbidden).isSome ↔
    ∃ names : List Nat, names.map Ty.fvar = images ∧ names.Nodup ∧
      ∀ name ∈ names, name ∉ forbidden := by
  constructor
  · intro hs
    obtain ⟨⟨names, hnames⟩, _⟩ := Option.isSome_iff_exists.mp hs
    exact ⟨names, hnames⟩
  · rintro ⟨names, rfl, hnd, havoid⟩
    unfold resolveRecWritten
    split
    · rename_i hp
      rw [recWrittenNames_map] at hp
      cases hp
    · rename_i names' hp
      have heq : names' = names := Option.some.inj (hp.symm.trans (recWrittenNames_map names))
      subst names'
      simp only [dif_pos hnd, dif_pos havoid, Option.isSome_some]

theorem resolveRecWritten_length {result}
    (_h : resolveRecWritten images forbidden = some result) : result.val.length = images.length := by
  exact (List.length_map ..).symm.trans (congrArg List.length result.property.1)

/-- Substitution cannot erase a structured/concrete/bound type into a bare
free variable. No LC or freshness hypothesis on the substitution is required. -/
private theorem bare_of_subst_bare {R : Subst} {ty : Ty} {name : Nat}
    (h : R.onTy ty = .fvar name) : ∃ original, ty = .fvar original := by
  cases ty with
  | fvar original => exact ⟨original, rfl⟩
  | prim | arrow | bvar | customTy => simp only [Subst.onTy_prim, Subst.onTy_arrow, Subst.onTy_bvar, Subst.onTy_customTy, reduceCtorEq] at h

private theorem bareList_of_subst_bareList {R : Subst} {images : List Ty} {candidates : List Nat}
    (h : images.map R.onTy = candidates.map Ty.fvar) :
    ∃ names : List Nat, names.map Ty.fvar = images := by
  have hall : ∀ ty ∈ images, ∃ name, ty = .fvar name := by
    intro ty ht
    have hm : R.onTy ty ∈ candidates.map Ty.fvar := h ▸ List.mem_map.mpr ⟨ty, ht, rfl⟩
    obtain ⟨name, _, heq⟩ := List.mem_map.mp hm
    exact bare_of_subst_bare heq.symm
  clear h
  induction images with
  | nil => exact ⟨[], rfl⟩
  | cons ty rest ih =>
      obtain ⟨name, rfl⟩ := hall ty List.mem_cons_self
      obtain ⟨names, heq⟩ := ih (fun ty ht => hall ty (List.mem_cons_of_mem _ ht))
      exact ⟨name :: names, congrArg (Ty.fvar name :: ·) heq⟩

/-- A factor into a distinct bare candidate prefix certifies the concrete
validator, provided the candidate prefix avoids the images of forbidden roots.
These are per-call frame facts; no global candidate freshness is assumed. -/
theorem resolveRecWritten_complete_of_factor {R : Subst} {candidates : List Nat}
    (hfactor : images.map R.onTy = candidates.map Ty.fvar) (hnd : candidates.Nodup)
    (havoid : ∀ name ∈ candidates, ∀ v ∈ forbidden, name ∉ (R.onTy (.fvar v)).freeVars) :
    (resolveRecWritten images forbidden).isSome := by
  obtain ⟨names, hbare⟩ := bareList_of_subst_bareList hfactor
  apply resolveRecWritten_isSome_iff.mpr
  refine ⟨names, hbare, ?_, ?_⟩
  · have hmap := hnd.map (fun _ _ heq => Ty.fvar.inj heq)
    rw [← hfactor, ← hbare] at hmap
    exact hmap.of_map.of_map
  · intro name hn hf
    have hm : R.onTy (.fvar name) ∈ candidates.map Ty.fvar :=
      hfactor ▸ List.mem_map.mpr ⟨.fvar name, hbare ▸ List.mem_map.mpr ⟨name, hn, rfl⟩, rfl⟩
    obtain ⟨candidate, hc, heq⟩ := List.mem_map.mp hm
    apply havoid candidate hc name hf
    rw [← heq]
    exact List.mem_cons_self


end Elaboration

namespace Elaboration


theorem OpenRecAnn.recFits_of_images {S : Subst}
    (h : OpenRecAnn frontier ann next opening) (hmode : ann.recModeAnn = none)
    (hS : ∀ p ∈ S, p.2.IsLC)
    (himages : opening.written.map (fun x => S.onTy (.fvar x)) = resolved.map Ty.fvar)
    (htarget : ∀ expected, opening.expected = some expected → target = S.onTy expected) :
    (ann.substTyFvars S).RecFits resolved target := by
  cases h with
  | absent => trivial
  | complete => cases hmode
  | @template next ty frontier template heq _ =>
      have hfit := template.allocate_fits frontier
      rw [heq] at hfit
      rw [htarget ty rfl]
      exact hfit.substTyFvars S
  | @partialForall next ty frontier count template heq _ =>
      have hfit := (template.openTyVarsFrom 0 (freshVars frontier count)).allocate_fits (frontier + count)
      rw [heq] at hfit
      have hcount := congrArg List.length himages
      simp only [List.length_map, freshVars_length] at hcount
      refine ⟨hcount.symm, ?_⟩
      have hfitS := hfit.substTyFvars S
      rw [Template.substTyFvars_openTyVarsFrom_of_images _ hS himages 0] at hfitS
      rw [htarget ty rfl]
      exact hfitS

/-- Closing a recursively checked annotation retains its cofinite binding fit. -/
theorem LetAnn.RecFits.cofinite_bindingFits {ann : LetAnn} {written pool Q : List Nat} {ty : Ty}
    (hfit : ann.RecFits written ty) (hcount : written.length = ann.recPrefixCount)
    (hnd : written.Nodup) (hsub : ∀ v ∈ written, v ∈ pool) (hpool : pool.Nodup)
    (hlc : ty.IsLC) (hsource : ∀ v ∈ ann.rigidVars, v ∈ Q)
    (havoid : ∀ v ∈ pool, v ∉ Q) :
    ∃ L, ∀ Xs, FreshNames L (recScheme written pool ty).paramCount Xs →
      ann.BindingFits (recScheme written pool ty) Xs := by
  have hnames := recNames_nodup (ty := ty) hnd hpool
  have hnamesQ : ∀ v ∈ recNames written pool ty, v ∉ Q := by
    intro v hv
    rcases mem_recNames.mp hv with hv | ⟨hv, _, _⟩
    · exact havoid v (hsub v hv)
    · exact havoid v hv
  cases ann with
  | absent => exact ⟨[], fun _ _ => trivial⟩
  | complete => cases hfit
  | template template =>
      refine ⟨recNames written pool ty, ?_⟩
      intro Xs hXs
      change template.Fits (Ty.openVars Xs (Ty.closeOver (recNames written pool ty) ty))
      rw [Ty.openVars_closeOver_rename hlc hnames hXs.length
        (fun v hv hx => hXs.avoid v hx hv)]
      exact Template.Fits.onSubst hfit hsource
        (fun pair hp => hnamesQ pair.1 (List.of_mem_zip hp).1)
  | partialForall count template =>
      have hcomp : (LetAnn.partialForall count template).SignatureCompletion written ty
          (recScheme written pool ty) (recNames written pool ty) :=
        .partialSignature hcount hfit.2
      obtain ⟨L, hL⟩ := hcomp.cofinite_fits hnames hnamesQ hsource hlc
      exact ⟨L, fun Xs hXs => hL Xs hXs⟩


end Elaboration

namespace Elaboration
theorem OpenRecAnns.selected_lookup (h : OpenRecAnns members index frontier anns next openings)
    (hi : index + i ∈ members) (ha : anns[i]? = some ann) :
    ∃ a b opening, openings[i]? = some opening ∧ OpenRecAnn a ann b opening := by
  induction h generalizing i with
  | nil => simp at ha
  | skip hn hr ih =>
    cases i with
    | zero => exact False.elim (hn (by simpa using hi))
    | succ i => exact ih (by simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hi) ha
  | cons hm hh hr ih =>
    cases i with
    | zero => cases Option.some.inj ha; exact ⟨_, _, _, rfl, hh⟩
    | succ i => exact ih (by simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hi) ha


end Elaboration
