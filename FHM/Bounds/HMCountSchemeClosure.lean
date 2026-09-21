import FHM.Bounds.HMCountScheme
import FHM.Bounds.CountTransport
import FHM.Bounds.HMInterpretation

/-! # Closing captured coordinates of HM/count schemes

An exported scheme may mention count and HM identities supplied by an enclosing
scope.  Transporting that enclosing scope must not substitute directly under
the scheme's own telescopes: doing so would allow an inner quantified identity
to capture an expression inserted by the caller.

The capture-safe representation is ordinary lambda lifting.  Count captures
become trailing quantified count coordinates.  Free HM captures become leading
bound HM slots, while the scheme's existing slots are shifted above them.  A
later use supplies the enclosing interpretations as additional arguments.  The
operations in this file only build the closed interface; the corresponding use
transport is proved separately.
-/

namespace FHM.Bounds.HMCountSchemeClosure

open ScopedScheme

/-- Captured count identities are set-like, even though the source interface
    stores a list.  Removing duplicates makes the promoted telescope lawful
    without changing which identities occur in the body or premises. -/
def countCaptures (s : HMCountScheme.Scheme) : List Nat :=
  s.counts.captures.eraseDups

/-- Every free HM identity in the erased scheme body is an interface capture.
    The bounds body has exactly this HM shape. -/
def typeCaptures (s : HMCountScheme.Scheme) : List Nat :=
  s.hm.body.freeVars.eraseDups

mutual
/-- Close selected free HM identities into a fresh leading slot block and move
    every existing bound slot above that block. -/
def closeTypes (ids : List Nat) : BoundsTy → BoundsTy
  | .prim p => .prim p
  | .fvar i => match ids.idxOf? i with
      | none => .fvar i
      | some slot => .bvar slot
  | .bvar i => .bvar (ids.length + i)
  | .arrow a b => .arrow (closeTypes ids a) (closeTypes ids b)
  | .list lo hi elem => .list lo hi (closeTypes ids elem)
  | .custom name args => .custom name (closeTypeList ids args)

def closeTypeList (ids : List Nat) : List BoundsTy → List BoundsTy
  | [] => []
  | a :: rest => closeTypes ids a :: closeTypeList ids rest
end

private theorem idxOf?_lt_length {i slot : Nat} {ids : List Nat}
    (h : ids.idxOf? i = some slot) : slot < ids.length := by
  have member : i ∈ ids := by
    by_contra absent
    have none := List.idxOf?_eq_none_iff.mpr absent
    rw [none] at h
    cases h
  have inside := List.idxOf_lt_length_iff.mpr member
  rw [List.idxOf_eq_getD_idxOf?, h] at inside
  simpa using inside

@[simp] theorem closeTypeList_eq_map (ids : List Nat) (args : List BoundsTy) :
    closeTypeList ids args = args.map (closeTypes ids) := by
  induction args with
  | nil => rfl
  | cons a rest => simp only [closeTypeList, List.map_cons, *]

/-- Strong induction for the nested `List BoundsTy` constructor. -/
@[elab_as_elim]
private def recStrong.{u} {motive : BoundsTy → Sort u}
    (prim : ∀ p, motive (.prim p))
    (arrow : ∀ a b, motive a → motive b → motive (.arrow a b))
    (bvar : ∀ i, motive (.bvar i))
    (fvar : ∀ i, motive (.fvar i))
    (list : ∀ lo hi elem, motive elem → motive (.list lo hi elem))
    (custom : ∀ name args, (∀ a ∈ args, motive a) → motive (.custom name args)) :
    (β : BoundsTy) → motive β
  | .prim p => prim p
  | .arrow a b => arrow a b
      (recStrong prim arrow bvar fvar list custom a)
      (recStrong prim arrow bvar fvar list custom b)
  | .bvar i => bvar i
  | .fvar i => fvar i
  | .list lo hi elem => list lo hi elem
      (recStrong prim arrow bvar fvar list custom elem)
  | .custom name args => custom name args
      (fun a _member => recStrong prim arrow bvar fvar list custom a)
termination_by β => sizeOf β
decreasing_by
  all_goals simp_wf
  all_goals first
    | omega
    | (have := List.sizeOf_lt_of_mem _member; omega)

theorem closeTypes_bvars {ids : List Nat} {limit : Nat} {β : BoundsTy}
    (h : ContainsBvarsUpTo limit (Synth.BoundsTy.toTy β)) :
    ContainsBvarsUpTo (ids.length + limit) (Synth.BoundsTy.toTy (closeTypes ids β)) := by
  induction β using recStrong with
  | prim p => simpa [closeTypes, Synth.BoundsTy.toTy] using
      (ContainsBvarsUpTo.prim : ContainsBvarsUpTo (ids.length + limit) (.prim p))
  | fvar i =>
      simp only [closeTypes]
      cases found : ids.idxOf? i with
      | none => simpa [found, Synth.BoundsTy.toTy] using
          (ContainsBvarsUpTo.fvar : ContainsBvarsUpTo (ids.length + limit) (.fvar i))
      | some slot =>
          simp only [Synth.BoundsTy.toTy]
          exact .bvar (by have := idxOf?_lt_length found; omega)
  | bvar i =>
      simp only [Synth.BoundsTy.toTy] at h
      cases h with
      | bvar inside =>
          simp only [closeTypes, Synth.BoundsTy.toTy]
          exact .bvar (by omega)
  | arrow a b iha ihb =>
      simp only [Synth.BoundsTy.toTy] at h
      cases h with
      | arrow ha hb =>
          simpa only [closeTypes, Synth.BoundsTy.toTy] using .arrow (iha ha) (ihb hb)
  | list lo hi elem ih =>
      simp only [Synth.BoundsTy.toTy, listTy] at h ⊢
      cases h with
      | customTy hall =>
          simp only [closeTypes, Synth.BoundsTy.toTy, listTy]
          exact .customTy (fun t member => by
            simp only [List.mem_singleton] at member
            subst t
            exact ih (hall _ (by simp)))
  | custom name args ih =>
      simp only [Synth.BoundsTy.toTy] at h
      cases h with
      | customTy hall =>
          simp only [closeTypes, closeTypeList_eq_map, Synth.BoundsTy.toTy,
            List.map_map, Function.comp_def]
          exact .customTy (fun t member => by
            obtain ⟨a, source, rfl⟩ := List.mem_map.mp member
            exact ih a source (hall _ (List.mem_map.mpr ⟨a, source, rfl⟩)))

theorem closeTypes_scope {ids scope : List Nat} {β : BoundsTy}
    (h : BoundsScoped scope β) : BoundsScoped scope (closeTypes ids β) := by
  induction β using recStrong with
  | prim | bvar => trivial
  | fvar i => simp only [closeTypes]; cases ids.idxOf? i <;> trivial
  | arrow a b iha ihb => exact ⟨iha h.1, ihb h.2⟩
  | list lo hi elem ih => exact ⟨h.1, h.2.1, ih h.2.2⟩
  | custom name args ih =>
      simp only [closeTypes, closeTypeList_eq_map]
      induction args with
      | nil => trivial
      | cons a rest tail =>
          exact ⟨ih a (by simp) h.1,
            tail (fun b member => ih b (List.mem_cons_of_mem _ member)) h.2⟩

/-- Closing every free identity in the source removes the free HM interface
    entirely. -/
theorem closeTypes_noFree {ids : List Nat} {β : BoundsTy}
    (covers : ∀ i ∈ (Synth.BoundsTy.toTy β).freeVars, i ∈ ids) :
    ∀ i, i ∉ (Synth.BoundsTy.toTy (closeTypes ids β)).freeVars := by
  induction β using recStrong with
  | prim | bvar => simp [closeTypes, Synth.BoundsTy.toTy, Ty.freeVars]
  | fvar j =>
      intro i member
      have captured := covers j (by simp [Synth.BoundsTy.toTy, Ty.freeVars])
      cases found : ids.idxOf? j with
      | none => exact False.elim ((List.idxOf?_eq_none_iff.mp found) captured)
      | some slot => simp [closeTypes, found, Synth.BoundsTy.toTy, Ty.freeVars] at member
  | arrow a b iha ihb =>
      intro i member
      simp only [closeTypes, Synth.BoundsTy.toTy, Ty.freeVars, List.mem_dedup,
        List.mem_append] at member
      rcases member with left | right
      · exact iha (fun j used => covers j (by
          simp [Synth.BoundsTy.toTy, Ty.freeVars, used])) i left
      · exact ihb (fun j used => covers j (by
          simp [Synth.BoundsTy.toTy, Ty.freeVars, used])) i right
  | list lo hi elem ih =>
      intro i member
      have inside : i ∈ (Synth.BoundsTy.toTy (closeTypes ids elem)).freeVars := by
        simpa [closeTypes, Synth.BoundsTy.toTy, listTy, Ty.freeVars,
          TyList.freeVars] using member
      exact ih (fun j used => covers j (by
        simpa [Synth.BoundsTy.toTy, listTy, Ty.freeVars, TyList.freeVars] using used)) i inside
  | custom name fields ih =>
      intro i member
      simp only [closeTypes, Synth.BoundsTy.toTy, Ty.freeVars] at member
      rw [closeTypeList_eq_map] at member
      rw [mem_TyList_freeVars] at member
      obtain ⟨closedField, closedMember, used⟩ := member
      simp only [List.map_map, Function.comp_def] at closedMember
      obtain ⟨field, fieldMember, rfl⟩ := List.mem_map.mp closedMember
      exact ih field fieldMember (fun j fieldUsed => covers j (by
        simp only [Synth.BoundsTy.toTy, Ty.freeVars]
        rw [mem_TyList_freeVars]
        exact ⟨Synth.BoundsTy.toTy field, List.mem_map.mpr
              ⟨field, fieldMember, rfl⟩, fieldUsed⟩)) i used

private theorem countScope_mono {source target : List Nat} {c : Count}
    (h : Scope.CountScoped source c) (subset : ∀ i ∈ source, i ∈ target) :
    Scope.CountScoped target c := by
  induction c with
  | lit | inf => trivial
  | var v =>
      cases v with
      | mk kind i =>
          cases kind with
          | rigid => exact subset i h
          | inferable => cases h
  | add a b ha hb | mul a b ha hb | min a b ha hb | max a b ha hb =>
      exact ⟨ha h.1, hb h.2⟩
  | pred a ha => exact ha h

mutual
private theorem boundsScope_mono {source target : List Nat} {β : BoundsTy}
    (h : BoundsScoped source β) (subset : ∀ i ∈ source, i ∈ target) :
    BoundsScoped target β := by
  cases β with
  | prim | fvar | bvar => trivial
  | arrow a b => exact ⟨boundsScope_mono h.1 subset, boundsScope_mono h.2 subset⟩
  | list lo hi elem =>
      exact ⟨countScope_mono h.1 subset, countScope_mono h.2.1 subset,
        boundsScope_mono h.2.2 subset⟩
  | custom name args => exact boundsListScope_mono h subset
termination_by sizeOf β

private theorem boundsListScope_mono {source target : List Nat} {args : List BoundsTy}
    (h : BoundsListScoped source args) (subset : ∀ i ∈ source, i ∈ target) :
    BoundsListScoped target args := by
  cases args with
  | nil => trivial
  | cons a rest => exact ⟨boundsScope_mono h.1 subset, boundsListScope_mono h.2 subset⟩
termination_by sizeOf args
end

private theorem constraintScope_mono {source target : List Nat} {c : Constraint}
    (h : ConstraintScoped source c) (subset : ∀ i ∈ source, i ∈ target) :
    ConstraintScoped target c :=
  ⟨countScope_mono h.1 subset, countScope_mono h.2 subset⟩

private theorem mem_eraseDups {a : Nat} {l : List Nat}
    (h : a ∈ l.eraseDups) : a ∈ l := by
  have go : ∀ n, ∀ (l : List Nat), l.length = n → ∀ a, a ∈ l.eraseDups → a ∈ l := by
    intro n
    refine Nat.strongRecOn n (motive := fun n =>
      ∀ (l : List Nat), l.length = n → ∀ a, a ∈ l.eraseDups → a ∈ l) fun n ih => ?_
    intro l hn a member
    match l with
    | [] => cases member
    | b :: rest =>
        simp only [List.length_cons] at hn
        simp only [List.eraseDups_cons, List.mem_cons] at member
        rcases member with rfl | tail
        · simp
        · have smaller : (rest.filter (fun x => !x == b)).length < n := by
            rw [← hn]
            exact Nat.lt_add_one_of_le (List.length_filter_le _ rest)
          exact List.mem_cons_of_mem b
            (List.mem_of_mem_filter (ih _ smaller _ rfl _ tail))
  exact go l.length l rfl a h

private theorem mem_eraseDups_of_mem {a : Nat} {l : List Nat}
    (h : a ∈ l) : a ∈ l.eraseDups := by
  have go : ∀ n, ∀ (l : List Nat), l.length = n → ∀ a, a ∈ l → a ∈ l.eraseDups := by
    intro n
    refine Nat.strongRecOn n (motive := fun n =>
      ∀ (l : List Nat), l.length = n → ∀ a, a ∈ l → a ∈ l.eraseDups) fun n ih => ?_
    intro l hn a member
    match l with
    | [] => cases member
    | b :: rest =>
        simp only [List.length_cons] at hn
        rcases List.mem_cons.mp member with rfl | tail
        · simp [List.eraseDups_cons]
        · simp only [List.eraseDups_cons, List.mem_cons]
          by_cases same : a = b
          · exact Or.inl same
          · apply Or.inr
            have filtered : a ∈ rest.filter (fun x => !x == b) := by
              simp [List.mem_filter, same, tail]
            have smaller : (rest.filter (fun x => !x == b)).length < n := by
              rw [← hn]
              exact Nat.lt_add_one_of_le (List.length_filter_le _ rest)
            exact ih _ smaller _ rfl _ filtered
  exact go l.length l rfl a h

private theorem nodup_eraseDups (l : List Nat) : l.eraseDups.Nodup := by
  have go : ∀ n, ∀ (l : List Nat), l.length = n → l.eraseDups.Nodup := by
    intro n
    refine Nat.strongRecOn n (motive := fun n =>
      ∀ (l : List Nat), l.length = n → l.eraseDups.Nodup) fun n ih => ?_
    intro l hn
    match l with
    | [] => exact .nil
    | b :: rest =>
        simp only [List.length_cons] at hn
        simp only [List.eraseDups_cons]
        apply List.Nodup.cons
        · intro member
          have filtered := List.mem_filter.mp (mem_eraseDups member)
          simpa using filtered.2
        · have smaller : (rest.filter (fun x => !x == b)).length < n := by
            rw [← hn]
            exact Nat.lt_add_one_of_le (List.length_filter_le _ rest)
          exact ih _ smaller _ rfl
  exact go l.length l rfl

private theorem promoted_subset (s : HMCountScheme.Scheme) :
    ∀ i ∈ s.counts.quantified ++ s.counts.captures,
      i ∈ s.counts.quantified ++ countCaptures s := by
  intro i member
  rcases List.mem_append.mp member with quantified | captured
  · exact List.mem_append_left _ quantified
  · exact List.mem_append_right _ (mem_eraseDups_of_mem captured)

private theorem promoted_nodup (s : HMCountScheme.Scheme) :
    (s.counts.quantified ++ countCaptures s).Nodup := by
  apply List.Nodup.append s.countWF.1 (nodup_eraseDups _)
  intro i quantified captured
  have original : i ∈ s.counts.captures := mem_eraseDups captured
  exact s.countWF.2.1 i original quantified

/-- Close every lexical capture into an ordinary explicit parameter.  Count
    captures trail the old count telescope; HM captures lead the old HM slots.
    The resulting interface is closed with respect to both capture namespaces. -/
def close (s : HMCountScheme.Scheme) : HMCountScheme.Scheme where
  hm := ⟨(typeCaptures s).length + s.hm.paramCount,
    Synth.BoundsTy.toTy (closeTypes (typeCaptures s) s.counts.body)⟩
  counts := ⟨s.counts.quantified ++ countCaptures s, [], s.counts.premises,
    closeTypes (typeCaptures s) s.counts.body⟩
  hmWF := by
    apply closeTypes_bvars
    rw [s.shape]
    exact s.hmWF
  countWF := by
    refine ⟨promoted_nodup s, (by simp), ?_, ?_⟩
    · exact closeTypes_scope
        (boundsScope_mono s.countWF.2.2.1 (by
          intro i member
          exact List.mem_append_left [] (promoted_subset s i member)))
    · intro c member
      exact constraintScope_mono (s.countWF.2.2.2 c member) (by
        intro i used
        exact List.mem_append_left [] (promoted_subset s i used))
  shape := rfl

@[simp] theorem close_countCaptures (s : HMCountScheme.Scheme) :
    (close s).counts.captures = [] := rfl

@[simp] theorem close_countQuantified (s : HMCountScheme.Scheme) :
    (close s).counts.quantified = s.counts.quantified ++ countCaptures s := rfl

@[simp] theorem close_typeParamCount (s : HMCountScheme.Scheme) :
    (close s).hm.paramCount = (typeCaptures s).length + s.hm.paramCount := rfl

theorem close_typeFree (s : HMCountScheme.Scheme) :
    (close s).hm.body.freeVars = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro i
  change i ∉ (Synth.BoundsTy.toTy (closeTypes (typeCaptures s) s.counts.body)).freeVars
  apply closeTypes_noFree
  intro j member
  apply mem_eraseDups_of_mem
  simpa only [typeCaptures, s.shape] using member

/-- Count arguments for the closed interface.  Existing quantified arguments
    are first transported through the enclosing substitution.  Promoted
    captures then receive exactly the enclosing meaning of their rigid names. -/
def countArguments (outer : CountSubstitution.Bindings)
    (s : HMCountScheme.Scheme) (args : List Count) : List Count :=
  args.map (CountSubstitution.count outer) ++
    (countCaptures s).map (fun i =>
      CountSubstitution.count outer (.var ⟨.rigid, i⟩))

/-- HM arguments for the closed interface.  Promoted captures lead the old
    slots, matching `closeTypes`; old caller arguments are transported too. -/
def typeArguments (f : Nat → BoundsTy) (s : HMCountScheme.Scheme)
    (args : List BoundsTy) : List BoundsTy :=
  (typeCaptures s).map f ++ args.map (SchemeSpecialization.mapFree f)

/-- Count specialization precedes full HM insertion, so counts inside existing
    caller HM arguments are transported before the enclosing HM map is applied.
    Promoted HM captures are inserted last and remain caller-owned. -/
def specializedTypeArguments (outer : CountSubstitution.Bindings)
    (f : Nat → BoundsTy) (s : HMCountScheme.Scheme)
    (args : List BoundsTy) : List BoundsTy :=
  typeArguments f s (args.map (CountSubstitution.bounds outer))

/-- Recover the original scheme's quantified-count arguments from a use of its
    closed interface. -/
def sourceCountArguments (s : HMCountScheme.Scheme) (args : List Count) : List Count :=
  args.take s.counts.quantified.length

/-- Recover the explicit arguments corresponding to the source scheme's
    promoted lexical count captures. -/
def captureCountArguments (s : HMCountScheme.Scheme) (args : List Count) : List Count :=
  args.drop s.counts.quantified.length

/-- Recover the explicit leading HM arguments corresponding to promoted free
    identities in the source scheme. -/
def captureTypeArguments (s : HMCountScheme.Scheme)
    (args : List BoundsTy) : List BoundsTy :=
  args.take (typeCaptures s).length

/-- Recover the original scheme's HM arguments from the tail of a closed use. -/
def sourceTypeArguments (s : HMCountScheme.Scheme)
    (args : List BoundsTy) : List BoundsTy :=
  args.drop (typeCaptures s).length

/-- A use of the lambda-lifted interface is a use of a lexical closure only
    when its promoted prefix/trailing coordinates equal that closure's stored
    environment. Without these equalities `close s` would expose ambient
    captures as fresh caller-chosen quantifiers, which is strictly stronger
    than ordinary HM let-polymorphism. -/
structure HasCaptureArguments (s : HMCountScheme.Scheme)
    (countArgs : List Count) (typeArgs : List BoundsTy)
    {Δ : List Constraint} {found : Ty} {caller : List Nat}
    (u : HMCountScheme.Use (close s) Δ found caller) : Prop where
  counts : captureCountArguments s u.counts = countArgs
  types : captureTypeArguments s u.types = typeArgs

theorem HasCaptureArguments.ofAppended
    {s : HMCountScheme.Scheme} {countArgs : List Count}
    {typeArgs : List BoundsTy} {Δ found caller}
    {u : HMCountScheme.Use (close s) Δ found caller}
    (sourceCounts : List Count) (sourceTypes : List BoundsTy)
    (countLength : sourceCounts.length = s.counts.quantified.length)
    (typeLength : typeArgs.length = (typeCaptures s).length)
    (counts : u.counts = sourceCounts ++ countArgs)
    (types : u.types = typeArgs ++ sourceTypes) :
    HasCaptureArguments s countArgs typeArgs u := by
  constructor
  · simp [captureCountArguments, counts, ← countLength]
  · simp [captureTypeArguments, types, ← typeLength]

/-- Captured count meanings at one enclosing count interpretation. -/
def interpretedCountCaptures (outer : CountSubstitution.Bindings)
    (s : HMCountScheme.Scheme) : List Count :=
  (countCaptures s).map (fun i =>
    CountSubstitution.count outer (.var ⟨.rigid, i⟩))

/-- Captured HM meanings at one enclosing type interpretation. -/
def interpretedTypeCaptures (f : Nat → BoundsTy)
    (s : HMCountScheme.Scheme) : List BoundsTy :=
  (typeCaptures s).map f

theorem interpretedCountCaptures_compose
    (outer inner : CountSubstitution.Bindings) (s : HMCountScheme.Scheme) :
    interpretedCountCaptures (CountAlgebra.compose outer inner) s =
      (interpretedCountCaptures inner s).map (CountSubstitution.count outer) := by
  simp only [interpretedCountCaptures, List.map_map, Function.comp_def,
    CountAlgebra.count_compose]

theorem interpretedTypeCaptures_map
    (outer : CountSubstitution.Bindings) (f types : Nat → BoundsTy)
    (s : HMCountScheme.Scheme) :
    interpretedTypeCaptures (fun i =>
      SchemeSpecialization.mapFree f (CountSubstitution.bounds outer (types i))) s =
      ((interpretedTypeCaptures types s).map (CountSubstitution.bounds outer)).map
        (SchemeSpecialization.mapFree f) := by
  simp only [interpretedTypeCaptures, List.map_map, Function.comp_def]

abbrev CapturesAgree (s : HMCountScheme.Scheme)
    (outer : CountSubstitution.Bindings) (f : Nat → BoundsTy)
    {Δ : List Constraint} {found : Ty} {caller : List Nat}
    (u : HMCountScheme.Use (close s) Δ found caller) : Prop :=
  HasCaptureArguments s (interpretedCountCaptures outer s)
    (interpretedTypeCaptures f s) u

private theorem drop_map_local (f : α → β) (n : Nat) (xs : List α) :
    (xs.map f).drop n = (xs.drop n).map f := by
  induction n generalizing xs with
  | zero => rfl
  | succ n ih => cases xs with
    | nil => rfl
    | cons _ rest => exact ih rest

private theorem take_map_local (f : α → β) (n : Nat) (xs : List α) :
    (xs.map f).take n = (xs.take n).map f := by
  induction n generalizing xs with
  | zero => rfl
  | succ n ih => cases xs with
    | nil => rfl
    | cons head rest => simp only [List.map_cons, List.take_succ_cons, ih]

/-- Mapping every supplied argument preserves the boundary between the
    source-owned arguments and the stored closure environment. -/
theorem HasCaptureArguments.map
    {s : HMCountScheme.Scheme} {countArgs : List Count}
    {typeArgs : List BoundsTy} {Δ found caller}
    {u : HMCountScheme.Use (close s) Δ found caller}
    (h : HasCaptureArguments s countArgs typeArgs u)
    (mapCount : Count → Count) (mapType : BoundsTy → BoundsTy)
    {Δ' found' caller'}
    {u' : HMCountScheme.Use (close s) Δ' found' caller'}
    (counts : u'.counts = u.counts.map mapCount)
    (types : u'.types = u.types.map mapType) :
    HasCaptureArguments s (countArgs.map mapCount)
      (typeArgs.map mapType) u' := by
  constructor
  · rw [captureCountArguments, counts, drop_map_local,
      ← captureCountArguments, h.counts]
  · rw [captureTypeArguments, types, take_map_local,
      ← captureTypeArguments, h.types]

theorem HasCaptureArguments.mapTypes
    {s : HMCountScheme.Scheme} {countArgs : List Count}
    {typeArgs : List BoundsTy} {Δ found caller}
    {u : HMCountScheme.Use (close s) Δ found caller}
    (h : HasCaptureArguments s countArgs typeArgs u)
    (mapType : BoundsTy → BoundsTy) {Δ' found' caller'}
    {u' : HMCountScheme.Use (close s) Δ' found' caller'}
    (counts : u'.counts = u.counts)
    (types : u'.types = u.types.map mapType) :
    HasCaptureArguments s countArgs (typeArgs.map mapType) u' := by
  constructor
  · rw [captureCountArguments, counts, ← captureCountArguments, h.counts]
  · rw [captureTypeArguments, types, take_map_local,
      ← captureTypeArguments, h.types]

theorem HasCaptureArguments.closedTypeFixed
    {s : HMCountScheme.Scheme} {countArgs : List Count}
    {typeArgs : List BoundsTy} {Δ found caller}
    {u : HMCountScheme.Use (close s) Δ found caller}
    (_h : HasCaptureArguments s countArgs typeArgs u)
    (f : Nat → BoundsTy) : ∀ i ∈ (close s).hm.body.freeVars,
      f i = .fvar i := by
  intro i member
  rw [close_typeFree] at member
  cases member

theorem HasCaptureArguments.closedCountFixed
    {s : HMCountScheme.Scheme} {countArgs : List Count}
    {typeArgs : List BoundsTy} {Δ found caller}
    {u : HMCountScheme.Use (close s) Δ found caller}
    (_h : HasCaptureArguments s countArgs typeArgs u)
    (outer : CountSubstitution.Bindings) :
    ∀ i ∈ (close s).counts.captures,
      CountSubstitution.lookup outer i = none := by
  intro i member
  rw [close_countCaptures] at member
  cases member

theorem closedUse_countArguments
    {s : HMCountScheme.Scheme} {Δ : List Constraint} {found : Ty}
    {caller : List Nat} (u : HMCountScheme.Use (close s) Δ found caller) :
    sourceCountArguments s u.counts ++ captureCountArguments s u.counts = u.counts :=
  List.take_append_drop _ _

theorem closedUse_sourceCountLength
    {s : HMCountScheme.Scheme} {Δ : List Constraint} {found : Ty}
    {caller : List Nat} (u : HMCountScheme.Use (close s) Δ found caller) :
    (sourceCountArguments s u.counts).length = s.counts.quantified.length := by
  simp only [sourceCountArguments, List.length_take]
  have total := u.countInstance.arity
  simp only [close_countQuantified, List.length_append] at total
  omega

theorem closedUse_captureCountLength
    {s : HMCountScheme.Scheme} {Δ : List Constraint} {found : Ty}
    {caller : List Nat} (u : HMCountScheme.Use (close s) Δ found caller) :
    (captureCountArguments s u.counts).length = (countCaptures s).length := by
  simp only [captureCountArguments, List.length_drop]
  have total := u.countInstance.arity
  simp only [close_countQuantified, List.length_append] at total
  omega

theorem closedUse_typeArguments
    {s : HMCountScheme.Scheme} {Δ : List Constraint} {found : Ty}
    {caller : List Nat} (u : HMCountScheme.Use (close s) Δ found caller) :
    captureTypeArguments s u.types ++ sourceTypeArguments s u.types = u.types :=
  List.take_append_drop _ _

theorem closedUse_captureTypeLength
    {s : HMCountScheme.Scheme} {Δ : List Constraint} {found : Ty}
    {caller : List Nat} (u : HMCountScheme.Use (close s) Δ found caller) :
    (captureTypeArguments s u.types).length = (typeCaptures s).length := by
  simp only [captureTypeArguments, List.length_take]
  have total := u.arity
  simp only [close_typeParamCount] at total
  omega

theorem closedUse_sourceTypeLength
    {s : HMCountScheme.Scheme} {Δ : List Constraint} {found : Ty}
    {caller : List Nat} (u : HMCountScheme.Use (close s) Δ found caller) :
    (sourceTypeArguments s u.types).length = s.hm.paramCount := by
  simp only [sourceTypeArguments, List.length_drop]
  have total := u.arity
  simp only [close_typeParamCount] at total
  omega

/-- Forget the promoted lexical coordinates of a closed use.  The remaining
    count arguments form a genuine instance of the source count scheme when
    its lexical captures are restored to the caller scope.  This projection is
    proof-only: it does not rerun the executable instantiator. -/
def sourceCountInstance
    {s : HMCountScheme.Scheme} {Δ : List Constraint} {found : Ty}
    {caller : List Nat} (u : HMCountScheme.Use (close s) Δ found caller) :
    ScopedScheme.Instance s.counts (sourceCountArguments s u.counts)
      (s.counts.captures ++ caller) := by
  let args := sourceCountArguments s u.counts
  have arity : s.counts.quantified.length = args.length :=
    (closedUse_sourceCountLength u).symm
  have argsMember : ∀ a ∈ args, a ∈ u.counts := by
    intro a member
    exact List.mem_of_mem_take member
  have argsScoped : ∀ a ∈ args, Scope.CountScoped (s.counts.captures ++ caller) a := by
    intro a member
    exact HMInterpretation.count_mono (u.countInstance.argsScoped a (argsMember a member))
      (fun _ used => List.mem_append_right _ used)
  have rowsScoped : ∀ row ∈ s.counts.quantified.zip args,
      Scope.CountScoped (s.counts.captures ++ caller) row.2 := by
    intro row member
    exact argsScoped row.2 (List.of_mem_zip member).2
  have keep : ∀ i ∈ s.counts.quantified ++ s.counts.captures,
      CountSubstitution.lookup (s.counts.quantified.zip args) i = none →
        i ∈ s.counts.captures ++ caller := by
    intro i member absent
    rcases List.mem_append.mp member with quantified | captured
    · have keyMember : i ∈ (s.counts.quantified.zip args).map Prod.fst := by
        rw [List.map_fst_zip (Nat.le_of_eq arity)]
        exact quantified
      exact False.elim ((lookup_none_iff.mp absent) keyMember)
    · exact List.mem_append_left _ captured
  refine {
    wf := s.countWF
    arity := arity
    finiteArgs := fun a member => u.countInstance.finiteArgs a (argsMember a member)
    argsScoped := argsScoped
    capturesScoped := fun i member => List.mem_append_left _ member
    bodyScoped := bounds_scoped s.countWF.2.2.1 rowsScoped keep
    premisesScoped := ?_ }
  intro c member
  obtain ⟨original, source, rfl⟩ := List.mem_map.mp member
  have hscope := s.countWF.2.2.2 original source
  exact ⟨count_scoped hscope.1 rowsScoped keep,
    count_scoped hscope.2 rowsScoped keep⟩

theorem sourceTypeArguments_lc
    {s : HMCountScheme.Scheme} {Δ : List Constraint} {found : Ty}
    {caller : List Nat} (u : HMCountScheme.Use (close s) Δ found caller) :
    ∀ a ∈ sourceTypeArguments s u.types, (Synth.BoundsTy.toTy a).IsLC := by
  intro a member
  exact u.typesLC a (List.mem_of_mem_drop member)

theorem sourceTypeArguments_scoped
    {s : HMCountScheme.Scheme} {Δ : List Constraint} {found : Ty}
    {caller : List Nat} (u : HMCountScheme.Use (close s) Δ found caller) :
    (sourceTypeArguments s u.types).all
      (boundsScopedBool (s.counts.captures ++ caller)) = true := by
  apply List.all_eq_true.mpr
  intro a member
  apply boundsScopedBool_complete
  exact boundsScope_mono
    (boundsScopedBool_sound
      (List.all_eq_true.mp u.typesScoped a (List.mem_of_mem_drop member)))
    (fun _ used => List.mem_append_right _ used)

/-- Canonical open-source view of a closed use.  Its caller assumptions are
    exactly its instantiated source premises, so this object records lawful
    specialization without claiming that the original closed call site has
    already discharged the untransported lexical premises. -/
def sourceUse
    {s : HMCountScheme.Scheme} {Δ : List Constraint} {found : Ty}
    {caller : List Nat} (u : HMCountScheme.Use (close s) Δ found caller) :
    let inst := sourceCountInstance u
    HMCountScheme.Use s inst.premises
      (Synth.BoundsTy.toTy
        (TypeSubstitution.combined
          (s.counts.quantified.zip (sourceCountArguments s u.counts))
          (SchemeUse.vector (sourceTypeArguments s u.types)) s.counts.body))
      (s.counts.captures ++ caller) := by
  let inst := sourceCountInstance u
  let types := sourceTypeArguments s u.types
  let β := TypeSubstitution.combined
    (s.counts.quantified.zip (sourceCountArguments s u.counts))
    (SchemeUse.vector types) s.counts.body
  refine {
    counts := sourceCountArguments s u.counts
    countInstance := inst
    usable := ?_
    types := types
    arity := closedUse_sourceTypeLength u
    typesLC := sourceTypeArguments_lc u
    typesScoped := sourceTypeArguments_scoped u
    shape := ?_ }
  · intro σ premises c member
    exact premises c member
  · change Synth.BoundsTy.toTy β = (Synth.BoundsTy.toTy β).eraseBounds
    exact (FreeAlgebra.shape_erased β).symm

private theorem vector_capture {ids : List Nat}
    (f : Nat → BoundsTy) (tail : List BoundsTy) {i : Nat} (member : i ∈ ids) :
    SchemeUse.vector (ids.map f ++ tail) (ids.idxOf i) = f i := by
  have inside : ids.idxOf i < ids.length := List.idxOf_lt_length_iff.mpr member
  have atIndex := List.getElem?_idxOf member
  unfold SchemeUse.vector
  rw [List.getElem?_append_left (by simpa using inside), List.getElem?_map, atIndex]
  rfl

private theorem vector_shift (head tail : List BoundsTy) (i : Nat) :
    SchemeUse.vector (head ++ tail) (head.length + i) = SchemeUse.vector tail i := by
  unfold SchemeUse.vector
  rw [List.getElem?_append_right (Nat.le_add_right _ _), Nat.add_sub_cancel_left]

private theorem vector_mapped (f : Nat → BoundsTy) (args : List BoundsTy) (i : Nat) :
    SchemeUse.vector (args.map (SchemeSpecialization.mapFree f)) i =
      SchemeSpecialization.mapFree f (SchemeUse.vector args i) := by
  unfold SchemeUse.vector
  rw [List.getElem?_map]
  cases args[i]? <;> rfl

/-- Closing free HM captures and supplying their enclosing meanings commutes
    with ordinary HM instantiation.  This is the type-coordinate half of the
    ambient-capture theorem; inserted arguments are never traversed again. -/
theorem substitute_closeTypes (ids : List Nat)
    (f : Nat → BoundsTy) (args : List BoundsTy) {β : BoundsTy}
    (covers : ∀ i ∈ (Synth.BoundsTy.toTy β).freeVars, i ∈ ids) :
    TypeSubstitution.substitute
        (SchemeUse.vector (ids.map f ++ args.map (SchemeSpecialization.mapFree f)))
        (closeTypes ids β) =
      SchemeSpecialization.mapFree f
        (TypeSubstitution.substitute (SchemeUse.vector args) β) := by
  induction β using recStrong with
  | prim p => rfl
  | fvar i =>
      have member : i ∈ ids := covers i (by simp [Synth.BoundsTy.toTy, Ty.freeVars])
      simp only [closeTypes]
      cases found : ids.idxOf? i with
      | none => exact False.elim ((List.idxOf?_eq_none_iff.mp found) member)
      | some slot =>
          have slotEq : slot = ids.idxOf i := by
            rw [List.idxOf_eq_getD_idxOf?, found]
            rfl
          subst slot
          simp only [TypeSubstitution.substitute, SchemeSpecialization.mapFree]
          exact vector_capture f _ member
  | bvar i =>
      simp only [closeTypes, TypeSubstitution.substitute]
      have shifted := vector_shift (ids.map f)
        (args.map (SchemeSpecialization.mapFree f)) i
      have mapped := vector_mapped f args i
      simpa only [List.length_map] using shifted.trans mapped
  | arrow a b iha ihb =>
      simp only [closeTypes, TypeSubstitution.substitute, SchemeSpecialization.mapFree]
      rw [iha (fun i member => covers i (by
        simp [Synth.BoundsTy.toTy, Ty.freeVars, member])),
        ihb (fun i member => covers i (by
          simp [Synth.BoundsTy.toTy, Ty.freeVars, member]))]
  | list lo hi elem ih =>
      simp only [closeTypes, TypeSubstitution.substitute, SchemeSpecialization.mapFree]
      rw [ih (fun i member => covers i (by
        simpa [Synth.BoundsTy.toTy, listTy, Ty.freeVars, TyList.freeVars] using member))]
  | custom name fields ih =>
      simp only [closeTypes, TypeSubstitution.substitute, SchemeSpecialization.mapFree]
      apply congrArg (BoundsTy.custom name)
      induction fields with
      | nil => rfl
      | cons field rest tail =>
          simp only [closeTypeList, TypeSubstitution.substituteList,
            SchemeSpecialization.mapFreeList, List.cons.injEq]
          constructor
          · exact ih field (by simp) (fun i used => covers i (by
              simp [Synth.BoundsTy.toTy, Ty.freeVars, TyList.freeVars, used]))
          · exact tail (fun a member => ih a (List.mem_cons_of_mem _ member))
              (fun i used => covers i (by
                simp only [Synth.BoundsTy.toTy, Ty.freeVars] at used ⊢
                apply List.mem_dedup.mpr
                exact List.mem_append_right _ used))

theorem substitute_close (s : HMCountScheme.Scheme) (f : Nat → BoundsTy)
    (args : List BoundsTy) :
    TypeSubstitution.substitute (SchemeUse.vector (typeArguments f s args))
        (close s).counts.body =
      SchemeSpecialization.mapFree f
        (TypeSubstitution.substitute (SchemeUse.vector args) s.counts.body) := by
  apply substitute_closeTypes (typeCaptures s) f args
  intro i member
  apply mem_eraseDups_of_mem
  simpa only [typeCaptures, s.shape] using member

private theorem lookup_append (left right : CountSubstitution.Bindings) (i : Nat) :
    CountSubstitution.lookup (left ++ right) i =
      match CountSubstitution.lookup left i with
      | some value => some value
      | none => CountSubstitution.lookup right i := by
  induction left with
  | nil => rfl
  | cons row rest ih =>
      rcases row with ⟨key, value⟩
      simp only [List.cons_append, CountSubstitution.lookup]
      split
      · rfl
      · exact ih

private theorem lookup_mapped (outer rows : CountSubstitution.Bindings) (i : Nat) :
    CountSubstitution.lookup
        (rows.map (Prod.map id (CountSubstitution.count outer))) i =
      (CountSubstitution.lookup rows i).map (CountSubstitution.count outer) := by
  induction rows with
  | nil => rfl
  | cons row rest ih =>
      rcases row with ⟨key, value⟩
      simp only [List.map_cons, CountSubstitution.lookup, Prod.map_fst, Prod.map_snd, id_eq]
      split
      · rfl
      · exact ih

private theorem capture_lookup (ids : List Nat) (distinct : ids.Nodup)
    (outer : CountSubstitution.Bindings) {i : Nat} (member : i ∈ ids) :
    CountSubstitution.lookup
        (ids.zip (ids.map (fun i =>
          CountSubstitution.count outer (.var ⟨.rigid, i⟩)))) i =
      some (CountSubstitution.count outer (.var ⟨.rigid, i⟩)) := by
  induction ids with
  | nil => cases member
  | cons head rest ih =>
      have parts := List.nodup_cons.mp distinct
      have tailDistinct := parts.2
      rcases List.mem_cons.mp member with rfl | tail
      · simp [CountSubstitution.lookup]
      · have different : head ≠ i := by
          intro same
          subst head
          exact parts.1 tail
        simpa [CountSubstitution.lookup, different] using ih tailDistinct tail

private theorem lookup_zip_none {ids : List Nat} {args : List Count}
    (arity : ids.length = args.length) {i : Nat} (absent : i ∉ ids) :
    CountSubstitution.lookup (ids.zip args) i = none := by
  apply ScopedScheme.lookup_none
  rw [List.map_fst_zip (Nat.le_of_eq arity)]
  exact absent

/-- Promoting captured count identities to explicit trailing parameters
    realizes exactly outer-after-inner simultaneous substitution. -/
theorem count_promoted (outer : CountSubstitution.Bindings)
    (quantified captures : List Nat) (args : List Count)
    (capturesNodup : captures.Nodup)
    (arity : quantified.length = args.length) {c : Count}
    (hscope : Scope.CountScoped (quantified ++ captures) c) :
    CountSubstitution.count
        ((quantified ++ captures).zip
          (args.map (CountSubstitution.count outer) ++
            captures.map (fun i =>
              CountSubstitution.count outer (.var ⟨.rigid, i⟩)))) c =
      CountSubstitution.count outer
        (CountSubstitution.count (quantified.zip args) c) := by
  let inner := quantified.zip args
  let captured := captures.zip (captures.map (fun i =>
    CountSubstitution.count outer (.var ⟨.rigid, i⟩)))
  have rowsEq :
      (quantified ++ captures).zip
          (args.map (CountSubstitution.count outer) ++
            captures.map (fun i =>
              CountSubstitution.count outer (.var ⟨.rigid, i⟩))) =
        inner.map (Prod.map id (CountSubstitution.count outer)) ++ captured := by
    rw [List.zip_append (by simpa only [List.length_map] using arity),
      List.zip_map_right]
  rw [rowsEq]
  induction c with
  | lit | inf => rfl
  | var v =>
      cases v with
      | mk kind i =>
          cases kind with
          | inferable => cases hscope
          | rigid =>
              simp only [CountSubstitution.count, lookup_append, lookup_mapped]
              cases found : CountSubstitution.lookup inner i with
              | some value => simp only [Option.map_some, Option.getD_some]
              | none =>
                  have absent : i ∉ quantified := by
                    intro member
                    have keyMember : i ∈ inner.map Prod.fst := by
                      simpa only [inner, List.map_fst_zip (Nat.le_of_eq arity)] using member
                    exact (ScopedScheme.lookup_none_iff.mp found) keyMember
                  have captureMember : i ∈ captures := by
                    rcases List.mem_append.mp hscope with quantifiedMember | capturedMember
                    · exact False.elim (absent quantifiedMember)
                    · exact capturedMember
                  have selected := capture_lookup captures capturesNodup outer captureMember
                  have selected' : CountSubstitution.lookup captured i =
                      some (CountSubstitution.count outer (.var ⟨.rigid, i⟩)) := by
                    simpa only [captured] using selected
                  simp only [Option.map_none, Option.getD_none]
                  rw [selected']
                  rfl
  | add a b iha ihb | mul a b iha ihb | min a b iha ihb | max a b iha ihb =>
      simp only [CountSubstitution.count]
      rw [iha hscope.1, ihb hscope.2]
  | pred a ih =>
      simp only [CountSubstitution.count]
      rw [ih hscope]

/-- The same promotion law for complete bounds types. -/
theorem bounds_promoted (outer : CountSubstitution.Bindings)
    (quantified captures : List Nat) (args : List Count)
    (capturesNodup : captures.Nodup)
    (arity : quantified.length = args.length) {β : BoundsTy}
    (hscope : ScopedScheme.BoundsScoped (quantified ++ captures) β) :
    CountSubstitution.bounds
        ((quantified ++ captures).zip
          (args.map (CountSubstitution.count outer) ++
            captures.map (fun i =>
              CountSubstitution.count outer (.var ⟨.rigid, i⟩)))) β =
      CountSubstitution.bounds outer
        (CountSubstitution.bounds (quantified.zip args) β) := by
  induction β using recStrong with
  | prim | fvar | bvar => rfl
  | arrow a b iha ihb =>
      simp only [CountSubstitution.bounds]
      rw [iha hscope.1, ihb hscope.2]
  | list lo hi elem ih =>
      simp only [CountSubstitution.bounds]
      rw [count_promoted outer quantified captures args capturesNodup arity hscope.1,
        count_promoted outer quantified captures args capturesNodup arity hscope.2.1,
        ih hscope.2.2]
  | custom name fields ih =>
      simp only [CountSubstitution.bounds]
      apply congrArg (BoundsTy.custom name)
      induction fields with
      | nil => rfl
      | cons field rest tail =>
          simp only [CountSubstitution.boundsList, List.cons.injEq]
          exact ⟨ih field (by simp) hscope.1,
            tail (fun a member => ih a (List.mem_cons_of_mem _ member)) hscope.2⟩

theorem constraint_promoted (outer : CountSubstitution.Bindings)
    (quantified captures : List Nat) (args : List Count)
    (capturesNodup : captures.Nodup)
    (arity : quantified.length = args.length) {c : Constraint}
    (hscope : ScopedScheme.ConstraintScoped (quantified ++ captures) c) :
    CountSubstitution.constraint
        ((quantified ++ captures).zip
          (args.map (CountSubstitution.count outer) ++
            captures.map (fun i =>
              CountSubstitution.count outer (.var ⟨.rigid, i⟩)))) c =
    CountSubstitution.constraint outer
        (CountSubstitution.constraint (quantified.zip args) c) := by
  cases c with
  | mk lhs rhs =>
      simp only [CountSubstitution.constraint]
      rw [count_promoted outer quantified captures args capturesNodup arity hscope.1,
        count_promoted outer quantified captures args capturesNodup arity hscope.2]

/-- Count substitution is orthogonal to closing HM captures. -/
theorem bounds_closeTypes (rows : CountSubstitution.Bindings) (ids : List Nat)
    (β : BoundsTy) :
    CountSubstitution.bounds rows (closeTypes ids β) =
      closeTypes ids (CountSubstitution.bounds rows β) := by
  induction β using recStrong with
  | prim | bvar => rfl
  | fvar i => simp only [closeTypes, CountSubstitution.bounds]; cases ids.idxOf? i <;> rfl
  | arrow a b iha ihb =>
      simp only [closeTypes, CountSubstitution.bounds, iha, ihb]
  | list lo hi elem ih =>
      simp only [closeTypes, CountSubstitution.bounds, ih]
  | custom name fields ih =>
      simp only [closeTypes, CountSubstitution.bounds]
      apply congrArg (BoundsTy.custom name)
      induction fields with
      | nil => rfl
      | cons field rest tail =>
          simp only [closeTypeList, CountSubstitution.boundsList, List.cons.injEq]
          exact ⟨ih field (by simp),
            tail (fun a member => ih a (List.mem_cons_of_mem _ member))⟩

/-- Full count-first/HM-second instantiation of the lifted interface equals
    specializing the original use in the enclosing environment. -/
theorem combined_close (s : HMCountScheme.Scheme)
    (outer : CountSubstitution.Bindings) (f : Nat → BoundsTy)
    (counts : List Count) (types : List BoundsTy)
    (countArity : s.counts.quantified.length = counts.length) :
    TypeSubstitution.combined
        ((close s).counts.quantified.zip (countArguments outer s counts))
        (SchemeUse.vector (specializedTypeArguments outer f s types)) (close s).counts.body =
      SchemeSpecialization.mapFree f
        (CountSubstitution.bounds outer
          (TypeSubstitution.combined (s.counts.quantified.zip counts)
            (SchemeUse.vector types) s.counts.body)) := by
  change TypeSubstitution.substitute
      (SchemeUse.vector (specializedTypeArguments outer f s types))
      (CountSubstitution.bounds
        ((s.counts.quantified ++ countCaptures s).zip (countArguments outer s counts))
        (closeTypes (typeCaptures s) s.counts.body)) = _
  rw [bounds_closeTypes]
  change TypeSubstitution.substitute
      (SchemeUse.vector (typeArguments f s (types.map (CountSubstitution.bounds outer))))
      (closeTypes (typeCaptures s)
        (CountSubstitution.bounds
          ((s.counts.quantified ++ countCaptures s).zip (countArguments outer s counts))
          s.counts.body)) = _
  simp only [typeArguments]
  rw [substitute_closeTypes (typeCaptures s) f
    (types.map (CountSubstitution.bounds outer))]
  · simp only [countArguments]
    rw [bounds_promoted outer s.counts.quantified (countCaptures s) counts
      (nodup_eraseDups _) countArity
      (boundsScope_mono s.countWF.2.2.1 (promoted_subset s))]
    rw [TypeSubstitution.combined, CountTransport.instantiate_commute]
    apply congrArg (SchemeSpecialization.mapFree f)
    congr 1
    funext i
    exact CountTransport.vector_mapped outer types i
  · intro i member
    apply mem_eraseDups_of_mem
    rw [CountSubstitution.bounds_shape, s.shape] at member
    exact member

/-- A use of an open lexical interface transports to a use of its closed,
    lambda-lifted interface.  Both kinds of ambient capture become ordinary
    arguments, so no freshness side condition is required. -/
def transportUse {s : HMCountScheme.Scheme} {Δ : List Constraint} {found : Ty}
    {caller : List Nat} (u : HMCountScheme.Use s Δ found caller)
    (outer : CountSubstitution.Bindings) (outerFinite : CountSubstitution.Finite outer)
    (countTarget : List Nat)
    (countScope : ∀ row ∈ outer, Scope.CountScoped countTarget row.2)
    (f : Nat → BoundsTy) (typeLC : ∀ i, (Synth.BoundsTy.toTy (f i)).IsLC)
    (typeTarget : List Nat)
    (typeScope : ∀ i, ScopedScheme.BoundsScoped typeTarget (f i)) :
    HMCountScheme.Use (close s) (Δ.map (CountSubstitution.constraint outer))
      (Synth.BoundsTy.toTy
        (SchemeSpecialization.mapFree f (CountSubstitution.bounds outer u.bounds)))
      ((caller ++ countTarget) ++ typeTarget) := by
  let countArgs := countArguments outer s u.counts
  let typeArgs := specializedTypeArguments outer f s u.types
  have outerRowsScoped : ∀ row ∈ outer,
      Scope.CountScoped ((caller ++ countTarget) ++ typeTarget) row.2 := by
    intro row member
    exact countScope_mono (countScope row member) (fun _ used =>
      List.mem_append_left typeTarget (List.mem_append_right caller used))
  have keepCaller : ∀ i ∈ caller, CountSubstitution.lookup outer i = none →
      i ∈ (caller ++ countTarget) ++ typeTarget := by
    intro i member _
    exact List.mem_append_left typeTarget (List.mem_append_left countTarget member)
  let countInstance : ScopedScheme.Instance (close s).counts countArgs
      ((caller ++ countTarget) ++ typeTarget) := by
    refine
      { wf := (close s).countWF
        arity := ?_
        finiteArgs := ?_
        argsScoped := ?_
        capturesScoped := ?_
        bodyScoped := ?_
        premisesScoped := ?_ }
    · simp only [countArgs, countArguments, close_countQuantified, List.length_append,
        List.length_map]
      rw [u.countInstance.arity]
    · intro a member
      simp only [countArgs, countArguments] at member
      rcases List.mem_append.mp member with old | captured
      · obtain ⟨source, sourceMember, rfl⟩ := List.mem_map.mp old
        exact CountAlgebra.count_noInf outer outerFinite
          (u.countInstance.finiteArgs source sourceMember)
      · obtain ⟨i, _, rfl⟩ := List.mem_map.mp captured
        exact CountAlgebra.count_noInf outer outerFinite Count.NoInf.var
    · intro a member
      simp only [countArgs, countArguments] at member
      rcases List.mem_append.mp member with old | captured
      · obtain ⟨source, sourceMember, rfl⟩ := List.mem_map.mp old
        exact ScopedScheme.count_scoped (u.countInstance.argsScoped source sourceMember)
          outerRowsScoped keepCaller
      · obtain ⟨i, captureMember, rfl⟩ := List.mem_map.mp captured
        apply ScopedScheme.count_scoped (rows := outer) (ids := [i])
        · exact List.mem_singleton_self i
        · exact outerRowsScoped
        · intro j singleton absent
          have same : j = i := by simpa using singleton
          subst j
          exact List.mem_append_left typeTarget
            (List.mem_append_left countTarget
              (u.countInstance.capturesScoped i (mem_eraseDups captureMember)))
    · intro i member
      simp only [close_countCaptures] at member
      cases member
    · simp only [countArgs, countArguments, close_countQuantified]
      change BoundsScoped ((caller ++ countTarget) ++ typeTarget)
        (CountSubstitution.bounds
          ((s.counts.quantified ++ countCaptures s).zip
            (u.counts.map (CountSubstitution.count outer) ++
              (countCaptures s).map (fun i =>
                CountSubstitution.count outer (.var ⟨.rigid, i⟩))))
          (closeTypes (typeCaptures s) s.counts.body))
      rw [bounds_closeTypes]
      apply closeTypes_scope
      rw [bounds_promoted outer s.counts.quantified (countCaptures s) u.counts
        (nodup_eraseDups _) u.countInstance.arity
        (boundsScope_mono s.countWF.2.2.1 (promoted_subset s))]
      exact ScopedScheme.bounds_scoped u.countInstance.bodyScoped outerRowsScoped keepCaller
    · intro c member
      simp only [countArgs, countArguments, close_countQuantified] at member ⊢
      obtain ⟨source, sourceMember, rfl⟩ := List.mem_map.mp member
      rw [constraint_promoted outer s.counts.quantified (countCaptures s) u.counts
        (nodup_eraseDups _) u.countInstance.arity
        (constraintScope_mono (s.countWF.2.2.2 source sourceMember) (promoted_subset s))]
      have originalScoped := u.countInstance.premisesScoped
        (CountSubstitution.constraint (s.counts.quantified.zip u.counts) source)
        (List.mem_map.mpr ⟨source, sourceMember, rfl⟩)
      exact ⟨ScopedScheme.count_scoped originalScoped.1 outerRowsScoped keepCaller,
        ScopedScheme.count_scoped originalScoped.2 outerRowsScoped keepCaller⟩
  have usable : countInstance.Usable (Δ.map (CountSubstitution.constraint outer)) := by
    have moved := CountSubstitution.valid outer outerFinite u.usable
    change (⟨Δ.map (CountSubstitution.constraint outer),
      (close s).counts.premises.map
        (CountSubstitution.constraint ((close s).counts.quantified.zip countArgs))⟩ :
          ForallProblem).Valid
    have premisesEq :
        (close s).counts.premises.map
            (CountSubstitution.constraint ((close s).counts.quantified.zip countArgs)) =
          (s.counts.premises.map
            (CountSubstitution.constraint (s.counts.quantified.zip u.counts))).map
              (CountSubstitution.constraint outer) := by
      simp only [countArgs, countArguments, close, List.map_map]
      apply List.map_congr_left
      intro c member
      exact constraint_promoted outer s.counts.quantified (countCaptures s) u.counts
        (nodup_eraseDups _) u.countInstance.arity
        (constraintScope_mono (s.countWF.2.2.2 c member) (promoted_subset s))
    rw [premisesEq]
    exact moved
  refine ⟨countArgs, countInstance, usable, typeArgs, ?_, ?_, ?_, ?_⟩
  · simp only [typeArgs, specializedTypeArguments, typeArguments, close_typeParamCount,
      List.length_append, List.length_map]
    rw [u.arity]
  · intro a member
    simp only [typeArgs, specializedTypeArguments, typeArguments] at member
    rcases List.mem_append.mp member with captured | old
    · obtain ⟨i, _, rfl⟩ := List.mem_map.mp captured
      exact typeLC i
    · obtain ⟨counted, countedMember, rfl⟩ := List.mem_map.mp old
      obtain ⟨source, sourceMember, rfl⟩ := List.mem_map.mp countedMember
      apply FreeAlgebra.bvars f typeLC
      rw [CountSubstitution.bounds_shape]
      exact u.typesLC source sourceMember
  · apply List.all_eq_true.mpr
    intro a member
    simp only [typeArgs, specializedTypeArguments, typeArguments] at member
    rcases List.mem_append.mp member with captured | old
    · obtain ⟨i, _, rfl⟩ := List.mem_map.mp captured
      apply ScopedScheme.boundsScopedBool_complete
      exact boundsScope_mono (typeScope i) (fun _ used =>
        List.mem_append_right (caller ++ countTarget) used)
    · obtain ⟨counted, countedMember, rfl⟩ := List.mem_map.mp old
      obtain ⟨source, sourceMember, rfl⟩ := List.mem_map.mp countedMember
      apply ScopedScheme.boundsScopedBool_complete
      apply HMInterpretation.map_scope
      · exact ScopedScheme.bounds_scoped
          (ScopedScheme.boundsScopedBool_sound
            (List.all_eq_true.mp u.typesScoped source sourceMember))
          (fun row rowMember => countScope_mono (countScope row rowMember)
            (fun _ used => List.mem_append_right caller used))
          (fun _ used _ => List.mem_append_left countTarget used)
      · exact typeScope
  · rw [FreeAlgebra.shape_erased]
    exact congrArg Synth.BoundsTy.toTy
      (combined_close s outer f u.counts u.types u.countInstance.arity)

theorem transportUse_bounds {s : HMCountScheme.Scheme} {Δ : List Constraint} {found : Ty}
    {caller : List Nat} (u : HMCountScheme.Use s Δ found caller)
    (outer : CountSubstitution.Bindings) (outerFinite : CountSubstitution.Finite outer)
    (countTarget : List Nat)
    (countScope : ∀ row ∈ outer, Scope.CountScoped countTarget row.2)
    (f : Nat → BoundsTy) (typeLC : ∀ i, (Synth.BoundsTy.toTy (f i)).IsLC)
    (typeTarget : List Nat)
    (typeScope : ∀ i, ScopedScheme.BoundsScoped typeTarget (f i)) :
    (transportUse u outer outerFinite countTarget countScope f typeLC typeTarget typeScope).bounds =
      SchemeSpecialization.mapFree f (CountSubstitution.bounds outer u.bounds) :=
  combined_close s outer f u.counts u.types u.countInstance.arity

/-- `transportUse` does not quantify over the enclosing environment. Its new
    coordinates carry exactly the enclosing count and HM interpretations, so
    the transported interface denotes the same lexical closure. -/
theorem transportUse_capturesAgree
    {s : HMCountScheme.Scheme} {Δ : List Constraint} {found : Ty}
    {caller : List Nat} (u : HMCountScheme.Use s Δ found caller)
    (outer : CountSubstitution.Bindings) (outerFinite : CountSubstitution.Finite outer)
    (countTarget : List Nat)
    (countScope : ∀ row ∈ outer, Scope.CountScoped countTarget row.2)
    (f : Nat → BoundsTy) (typeLC : ∀ i, (Synth.BoundsTy.toTy (f i)).IsLC)
    (typeTarget : List Nat)
    (typeScope : ∀ i, ScopedScheme.BoundsScoped typeTarget (f i)) :
    CapturesAgree s outer f
      (transportUse u outer outerFinite countTarget countScope f typeLC
        typeTarget typeScope) := by
  constructor
  · simp [captureCountArguments, transportUse, countArguments,
      interpretedCountCaptures, u.countInstance.arity]
  · simp [captureTypeArguments, transportUse, specializedTypeArguments,
      typeArguments, interpretedTypeCaptures]

#print axioms closeTypes_bvars
#print axioms closeTypes_scope
#print axioms closeTypes_noFree
#print axioms close
#print axioms close_typeFree
#print axioms closedUse_countArguments
#print axioms closedUse_sourceCountLength
#print axioms closedUse_captureCountLength
#print axioms closedUse_typeArguments
#print axioms closedUse_captureTypeLength
#print axioms closedUse_sourceTypeLength
#print axioms sourceCountInstance
#print axioms sourceTypeArguments_lc
#print axioms sourceTypeArguments_scoped
#print axioms sourceUse
#print axioms substitute_closeTypes
#print axioms substitute_close
#print axioms combined_close
#print axioms transportUse
#print axioms transportUse_bounds
#print axioms transportUse_capturesAgree

end FHM.Bounds.HMCountSchemeClosure
