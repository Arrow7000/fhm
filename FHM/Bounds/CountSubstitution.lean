import FHM.Bounds.Scheme
import FHM.Bounds.Synth

/-! # Semantic substitution of selected count identities

Unlike scheme-local `applyArgs`, this replaces only explicitly selected rigid
identities. Captured outer identities are left intact. Substituting finite Nat
arguments transports count evaluation, path conditions and semantic subtyping;
it does not assert that arbitrary inferred unknowns may escape or generalize.
-/

namespace FHM.Bounds.CountSubstitution

abbrev Bindings := List (Nat × Count)

def lookup : Bindings → Nat → Option Count
  | [], _ => none
  | (key, value) :: rest, i => if key = i then some value else lookup rest i

private theorem lookup_mem {rows : Bindings} {i : Nat} {c : Count}
    (h : lookup rows i = some c) : ∃ row ∈ rows, row.2 = c := by
  induction rows with
  | nil => cases h
  | cons row rest ih =>
      rcases row with ⟨key, value⟩
      simp only [lookup] at h
      split at h
      · exact ⟨(key, value), by simp, Option.some.inj h⟩
      · obtain ⟨row, hr, hc⟩ := ih h
        exact ⟨row, by simp [hr], hc⟩

def Finite (rows : Bindings) : Prop := ∀ row ∈ rows, row.2.NoInf

def count (rows : Bindings) : Count → Count
  | .lit n => .lit n
  | .inf => .inf
  | .var ⟨.rigid, i⟩ => (lookup rows i).getD (.var ⟨.rigid, i⟩)
  | .var ⟨.inferable, i⟩ => .var ⟨.inferable, i⟩
  | .add a b => .add (count rows a) (count rows b)
  | .mul a b => .mul (count rows a) (count rows b)
  | .pred a => .pred (count rows a)
  | .min a b => .min (count rows a) (count rows b)
  | .max a b => .max (count rows a) (count rows b)

def assignment (rows : Bindings) (σ : Assign) : Assign :=
  fun v => match v.kind with
    | .inferable => σ v
    | .rigid => match lookup rows v.idx with
        | none => σ v
        | some c => c.evalNat σ

theorem count_eval (rows : Bindings) (hf : Finite rows) (c : Count) (σ : Assign) :
    (count rows c).eval σ = c.eval (assignment rows σ) := by
  induction c with
  | lit | inf => rfl
  | var v =>
      cases v with | mk kind i =>
        cases kind with
        | inferable => rfl
        | rigid =>
            cases h : lookup rows i with
            | none => simp only [count, h, Option.getD_none, Count.eval, assignment]
            | some a =>
                obtain ⟨row, hr, ha⟩ := lookup_mem h
                have hfinite : a.NoInf := ha ▸ hf row hr
                simpa only [count, h, Option.getD_some, Count.eval, assignment] using
                  hfinite.eval_eq_ofNat σ
  | add a b ha hb | mul a b ha hb | min a b ha hb | max a b ha hb =>
      simp only [count, Count.eval, ha, hb]
  | pred a ha => simp only [count, Count.eval, ha]

theorem captured_count {rows : Bindings} {i : Nat} (h : lookup rows i = none) :
    count rows (.var ⟨.rigid, i⟩) = .var ⟨.rigid, i⟩ := by
  simp only [count, h, Option.getD_none]

theorem captured_assignment {rows : Bindings} {i : Nat} (h : lookup rows i = none)
    (σ : Assign) : assignment rows σ ⟨.rigid, i⟩ = σ ⟨.rigid, i⟩ := by
  simp only [assignment, h]

def constraint (rows : Bindings) (c : Constraint) : Constraint :=
  ⟨count rows c.lhs, count rows c.rhs⟩

theorem constraint_holds (rows : Bindings) (hf : Finite rows)
    (c : Constraint) (σ : Assign) :
    (constraint rows c).Holds σ ↔ c.Holds (assignment rows σ) := by
  simp only [Constraint.Holds, constraint, count_eval rows hf]

def problem (rows : Bindings) (φ : ForallProblem) : ForallProblem :=
  ⟨φ.prem.map (constraint rows), φ.goals.map (constraint rows)⟩

/-- Valid implications remain valid after simultaneous finite substitution of
    both premises and goals. No oracle completeness or monotonicity is used. -/
theorem valid (rows : Bindings) (hf : Finite rows) {φ : ForallProblem} (h : φ.Valid) :
    (problem rows φ).Valid := by
  intro σ hp g hg
  obtain ⟨original, hmem, rfl⟩ := List.mem_map.mp hg
  apply (constraint_holds rows hf original σ).mpr
  apply h (assignment rows σ) _ original hmem
  intro c hc
  apply (constraint_holds rows hf c σ).mp
  exact hp (constraint rows c) (List.mem_map.mpr ⟨c, hc, rfl⟩)

mutual
def bounds (rows : Bindings) : BoundsTy → BoundsTy
  | .prim p => .prim p
  | .fvar i => .fvar i
  | .bvar i => .bvar i
  | .arrow a b => .arrow (bounds rows a) (bounds rows b)
  | .list lo hi elem => .list (count rows lo) (count rows hi) (bounds rows elem)
  | .custom name args => .custom name (boundsList rows args)

def boundsList (rows : Bindings) : List BoundsTy → List BoundsTy
  | [] => []
  | a :: as => bounds rows a :: boundsList rows as
end

mutual
/-- Semantic inclusion is preserved by instantiating selected count identities,
    provided their path assumptions are instantiated along with the bounds. -/
theorem subtype (rows : Bindings) (hf : Finite rows) {Δ a b}
    (h : SemanticSub Δ a b) :
    SemanticSub (Δ.map (constraint rows)) (bounds rows a) (bounds rows b) := by
  cases h with
  | prim => simpa only [bounds] using (SemanticSub.prim (Δ := Δ.map (constraint rows)))
  | fvar => simpa only [bounds] using (SemanticSub.fvar (Δ := Δ.map (constraint rows)))
  | bvar => simpa only [bounds] using (SemanticSub.bvar (Δ := Δ.map (constraint rows)))
  | arrow ha hb => simpa only [bounds] using SemanticSub.arrow (subtype rows hf ha) (subtype rows hf hb)
  | list hv he =>
      have hv' := valid rows hf hv
      simpa only [bounds] using SemanticSub.list
        (by simpa only [problem, Interval.subGoals, constraint, List.map_cons, List.map_nil] using hv')
        (subtype rows hf he)
  | custom hs => simpa only [bounds] using SemanticSub.custom (subtypes rows hf hs)
termination_by sizeOf a + sizeOf b

private theorem subtypes (rows : Bindings) (hf : Finite rows) {Δ as bs}
    (h : List.Forall₂ (SemanticSub Δ) as bs) :
    List.Forall₂ (SemanticSub (Δ.map (constraint rows))) (boundsList rows as) (boundsList rows bs) := by
  cases h with
  | nil => simpa only [boundsList] using (List.Forall₂.nil (R := SemanticSub (Δ.map (constraint rows))))
  | cons hh ht => simpa only [boundsList] using List.Forall₂.cons (subtype rows hf hh) (subtypes rows hf ht)
termination_by sizeOf as + sizeOf bs
end

mutual
/-- Count instantiation never changes the HM type skeleton. -/
theorem bounds_shape (rows : Bindings) (β : BoundsTy) :
    FHM.Bounds.Synth.BoundsTy.toTy (bounds rows β) = FHM.Bounds.Synth.BoundsTy.toTy β := by
  cases β with
  | prim | fvar | bvar => rfl
  | arrow a b => simp only [bounds, FHM.Bounds.Synth.BoundsTy.toTy, bounds_shape rows a, bounds_shape rows b]
  | list lo hi elem => simp only [bounds, FHM.Bounds.Synth.BoundsTy.toTy, bounds_shape rows elem]
  | custom n as => simp only [bounds, FHM.Bounds.Synth.BoundsTy.toTy, boundsList_shape rows as]
termination_by sizeOf β

private theorem boundsList_shape (rows : Bindings) (as : List BoundsTy) :
    (boundsList rows as).map FHM.Bounds.Synth.BoundsTy.toTy = as.map FHM.Bounds.Synth.BoundsTy.toTy := by
  cases as with
  | nil => rfl
  | cons a as => simp only [boundsList, List.map_cons, bounds_shape rows a, boundsList_shape rows as]
termination_by sizeOf as
end

#print axioms count_eval
#print axioms valid
#print axioms subtype
#print axioms bounds_shape

end FHM.Bounds.CountSubstitution
