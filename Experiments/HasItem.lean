import Mathlib


/-- This is a type that proves that in this list, the item at index `n` is the specified item -/
inductive HasItem {α : Type u} : (index : Nat) → List α → α → Prop where
  /-- The proof that the item at this point in the context has the type `ty` we're interested in -/
  | stop :
    HasItem 0 (item :: ctx) item

  /-- The proof that if we have a proof that the item at index `n` has type `ty` in a context `ctx`, then we still know that it contains that type `ty` even when we shove more items onto the context. In other words, given a `HasItem` for a given `Ctx`, we can make a `HasItem` for a bigger `Ctx`. -/
  | pop :
    HasItem n ctx item → HasItem (n+1) (otherItem :: ctx) item


@[grind .]
theorem HasItem.unique
  (h₁ : HasItem i list item₁)
  (h₂ : HasItem i list item₂) : item₁ = item₂ := by
  induction h₁ generalizing item₂ with
  | stop =>
    cases h₂
    rfl
  | pop h ih =>
    cases h₂
    grind


@[grind →]
theorem HasItem.isLt (h : HasItem i list item) : i < list.length := by
  induction h
  · simp
  · simp; trivial

/-- If HasItem i list2 b and List.Forall₂ R list1 list2, then ∃ a in list1 at index i with R a b. -/
theorem HasItem.of_forall2 {R : α → β → Prop}
    (hitem : HasItem i list2 b)
    (hrel : List.Forall₂ R list1 list2) :
    ∃ a, HasItem i list1 a ∧ R a b := by
  match hitem with
  | .stop =>
    match hrel with
    | .cons hr _ => exact ⟨_, .stop, hr⟩
  | .pop hitem' =>
    match hrel with
    | .cons _ hrel' =>
      obtain ⟨a, ha, hr⟩ := of_forall2 hitem' hrel'
      exact ⟨a, ha.pop, hr⟩

/-- HasItem is preserved by List.map. -/
theorem HasItem.map {α : Type u} {i : Nat} {list : List α} {item : α}
    (h : HasItem i list item) {β : Type u} (f : α → β)
    : HasItem i (list.map f) (f item) := by
  induction h with
  | stop => exact .stop
  | pop _ ih => exact .pop ih


def HasItem.lookup (index : Nat) (list : List α) : Option α :=
  match index, list with
  | 0, h :: _ => some h
  | n+1, _ :: t =>
    match lookup n t with
    | some item => some item
    | none => none
  | _, [] => none


@[grind =>]
theorem HasItem.lookup_sound (h : HasItem.lookup i list = some item) : HasItem i list item := by
  fun_induction HasItem.lookup i list generalizing item
  · simp at h
    subst_eqs
    refine .stop
  · expose_names
    simp at h
    subst h
    have := ih1 h_1
    refine .pop this
  · expose_names
    simp at h
  · simp at h



@[grind =>]
theorem HasItem.lookup_complete (h : HasItem i list item) :  HasItem.lookup i list = some item := by
  fun_induction HasItem.lookup i list generalizing item
  · cases h
    rfl
  · simp at h ⊢
    cases h
    expose_names
    have := ih1 h_1
    rw [h] at this
    simp at this
    subst this
    rfl
  · cases h
    expose_names
    have := ih1 h_1
    rw [h] at this
    simp at this
  · cases h




@[grind .]
theorem HasItem.lookup_iff : HasItem i list item ↔ HasItem.lookup i list = some item :=
  ⟨ HasItem.lookup_complete, HasItem.lookup_sound ⟩



/-- Look up an item at a given index in a list, returning the item along with a HasItem proof -/
def HasItem.lookupWithPrf (index : Nat) (list : List α) : Option { item // HasItem index list item } :=
  match h : HasItem.lookup index list with
  | none => none
  | some item => some ⟨item, lookup_iff.mpr h⟩




@[grind =]
theorem HasItem.lookup_some_iff_lt : i < list.length ↔ ∃ item, HasItem.lookup i list = some item := by
  constructor
  · intro prem
    fun_induction HasItem.lookup i list
    · simp
    · simp
    · expose_names
      simp at prem
      have ⟨item,prf⟩ := ih1 prem
      rw [h] at prf
      simp at prf
    · simp at prem
  · intro prem
    fun_induction HasItem.lookup i list
    · simp
    · expose_names
      simp at prem ⊢
      exact ih1 ⟨ item, h ⟩
    · expose_names
      simp at prem
    · simp at prem


@[grind →]
theorem HasItem.transfer_list_len_eq {item₁ : α₁} {list₂ : List α₂} (h : HasItem i list₁ item₁) (hlen : list₁.length = list₂.length) : ∃ item₂, HasItem i list₂ item₂ := by grind


/-- The item is in the list -/
@[grind →]
theorem HasItem.mem (h : HasItem i list item) : item ∈ list := by
  induction h
  · simp
  · expose_names; exact List.mem_cons_of_mem otherItem a_ih


@[grind =>]
theorem HasItem.append (h : HasItem i list item) : HasItem i (list ++ other) item := by
  induction h with
  | stop => exact .stop
  | pop _ ih => exact .pop ih

/-- If we have a HasItem in the first part of an appended list, we have it in the first list alone -/
@[grind →]
theorem HasItem.of_append_left (h : HasItem i (list ++ other) item) (hlt : i < list.length) : HasItem i list item := by
  induction list generalizing i with
  | nil => simp at hlt
  | cons head tail ih =>
    match i, h with
    | 0, .stop => exact .stop
    | i'+1, .pop h' =>
      have : i' < tail.length := by simp at hlt; omega
      exact .pop (ih h' this)

/-- If we have a HasItem in the second part of an appended list, we have it in the second list alone -/
@[grind →]
theorem HasItem.of_append_right (h : HasItem i (list ++ other) item) (hge : i ≥ list.length) : HasItem (i - list.length) other item := by
  induction list generalizing i with
  | nil => simp at h ⊢; exact h
  | cons head tail ih =>
    match i, h with
    | 0, .stop => simp at hge
    | i'+1, .pop h' =>
      have : i' ≥ tail.length := by simp at hge; omega
      have := ih h' this
      simp at this ⊢
      exact this

/-- Sum type for decidable split of an index into an appended list -/
inductive HasItemSplit {α : Type} (i : Nat) (list other : List α) (item : α) where
  | inFirst (h : HasItem i list item) (hlt : i < list.length) : HasItemSplit i list other item
  | inSecond (j : Nat) (h : HasItem j other item) (heq : i = list.length + j) : HasItemSplit i list other item

/-- Decidable version: check if index is in the first or second part of an appended list -/
def HasItem.splitAppend {list : List α} {other : List α}
    (h : HasItem i (list ++ other) item) : HasItemSplit i list other item :=
  if hlt : i < list.length then
    .inFirst (h.of_append_left hlt) hlt
  else
    have hge : i ≥ list.length := Nat.ge_of_not_lt hlt
    .inSecond (i - list.length) (h.of_append_right hge) (by omega)
