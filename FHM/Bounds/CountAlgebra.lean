import FHM.Bounds.ScopedScheme

/-! Composition of simultaneous count interpretations. The inner lookup wins;
its replacement is then interpreted by the outer substitution. This operation
is for interpreting source annotations, not for rewriting inserted caller HM
arguments. It requires no solver and introduces no inference/escape policy. -/

namespace FHM.Bounds.CountAlgebra

open CountSubstitution

def compose (outer inner : Bindings) : Bindings :=
  inner.map (fun row => (row.1, count outer row.2)) ++ outer

theorem lookup_compose (outer inner : Bindings) (i : Nat) :
    lookup (compose outer inner) i =
      match lookup inner i with
      | some c => some (count outer c)
      | none => lookup outer i := by
  induction inner with
  | nil => rfl
  | cons row rest ih =>
      rcases row with ⟨key, value⟩
      simp only [compose, List.map_cons, List.cons_append, lookup]
      split
      · rfl
      · exact ih

theorem count_compose (outer inner : Bindings) (c : Count) :
    count (compose outer inner) c = count outer (count inner c) := by
  induction c with
  | lit | inf => rfl
  | @var v =>
      cases v with | mk kind i =>
        cases kind with
        | inferable => rfl
        | rigid =>
            simp only [count, lookup_compose]
            cases hi : lookup inner i <;> simp only [Option.getD_none, Option.getD_some, count]
  | add a b ha hb | mul a b ha hb | min a b ha hb | max a b ha hb =>
      simp only [count, ha, hb]
  | pred a ha => simp only [count, ha]

mutual
theorem bounds_compose (outer inner : Bindings) (β : BoundsTy) :
    bounds (compose outer inner) β = bounds outer (bounds inner β) := by
  cases β with
  | prim | fvar | bvar => rfl
  | arrow a b => simp only [bounds, bounds_compose outer inner a, bounds_compose outer inner b]
  | list lo hi elem => simp only [bounds, count_compose, bounds_compose outer inner elem]
  | custom name as => exact congrArg (BoundsTy.custom name) (list_compose outer inner as)
termination_by sizeOf β

private theorem list_compose (outer inner : Bindings) (as : List BoundsTy) :
    boundsList (compose outer inner) as = boundsList outer (boundsList inner as) := by
  cases as with
  | nil => rfl
  | cons a as => simp only [boundsList, bounds_compose outer inner a, list_compose outer inner as]
termination_by sizeOf as
end

theorem count_noInf (rows : Bindings) (hf : Finite rows) {c : Count} (h : c.NoInf) :
    (count rows c).NoInf := by
  induction h with
  | lit => exact .lit
  | @var v =>
      cases v with | mk kind i =>
        cases kind with
        | inferable => exact .var
        | rigid =>
            cases hl : lookup rows i with
            | none => simpa only [count, hl, Option.getD_none] using (Count.NoInf.var (v := ⟨.rigid, i⟩))
            | some c => simpa only [count, hl, Option.getD_some] using hf _ (ScopedScheme.lookup_row hl)
  | add _ _ ha hb => exact .add ha hb
  | mul _ _ ha hb => exact .mul ha hb
  | pred _ ha => exact .pred ha
  | min _ _ ha hb => exact .min ha hb
  | max _ _ ha hb => exact .max ha hb

theorem finite_compose {outer inner : Bindings} (ho : Finite outer) (hi : Finite inner) :
    Finite (compose outer inner) := by
  intro row hr
  rcases List.mem_append.mp hr with h | h
  · obtain ⟨original, hm, rfl⟩ := List.mem_map.mp h
    exact count_noInf outer ho (hi original hm)
  · exact ho row h

#print axioms bounds_compose
#print axioms finite_compose

end FHM.Bounds.CountAlgebra
