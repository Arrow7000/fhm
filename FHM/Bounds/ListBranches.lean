import FHM.Bounds.Semantic
import FHM.Bounds.ScopedScheme

/-! # Semantic List coverage and constructor path refinements

Coverage is specified with arithmetic validity, not solver verdicts. Its soundness
theorem covers every finite length admitted by the input interval. Constructor
refinements and predecessor tail intervals preserve that arithmetic meaning.
Connecting lengths to Core runtime values and accepting typed match branches are
separate obligations; this module alone does neither.
-/

namespace FHM.Bounds.ListBranches

inductive Covers (Δ : List Constraint) (i : Interval) (branches : List (MatchPattern × Expr)) : Prop where
  | full : hasNilBranch branches → hasConsBranch branches → Covers Δ i branches
  | emptyOnly : (mustBeEmpty Δ i.hi).Valid → hasNilBranch branches → Covers Δ i branches
  | nonemptyOnly : (mustBeNonempty Δ i.lo).Valid → hasConsBranch branches → Covers Δ i branches
  | wildcard : hasWildcardBranch branches → Covers Δ i branches

def CoveredAt (branches : List (MatchPattern × Expr)) (n : Nat) : Prop :=
  hasWildcardBranch branches ∨ (n = 0 ∧ hasNilBranch branches) ∨ (0 < n ∧ hasConsBranch branches)

theorem Covers.sound {Δ i branches} (h : Covers Δ i branches) {σ n}
    (hp : ∀ c ∈ Δ, c.Holds σ) (hn : i.Contains σ (.ofNat n)) : CoveredAt branches n := by
  cases h with
  | full hN hC =>
      by_cases hz : n = 0
      · exact .inr (.inl ⟨hz, hN⟩)
      · exact .inr (.inr ⟨Nat.pos_of_ne_zero hz, hC⟩)
  | emptyOnly hv hN =>
      have hh := hv σ hp ⟨i.hi, .lit 0⟩ (by simp [mustBeEmpty])
      have hz := ExtNat.le_trans hn.2 hh
      have hz : n = 0 := by simpa [Constraint.Holds, Count.eval, ExtNat.le] using hz
      exact .inr (.inl ⟨hz, hN⟩)
  | nonemptyOnly hv hC =>
      have hl := hv σ hp ⟨.lit 1, i.lo⟩ (by simp [mustBeNonempty])
      have hn := ExtNat.le_trans hl hn.1
      have hn : 0 < n := by simpa [Constraint.Holds, Count.eval, ExtNat.le] using hn
      exact .inr (.inr ⟨hn, hC⟩)
  | wildcard hw => exact .inl hw

theorem Covers.ofLegacy {Δ lo hi elem branches}
    (h : BoundCovers Δ (.list lo hi elem) branches) : Covers Δ ⟨lo, hi⟩ branches := by
  cases h with
  | listFull hN hC => exact .full hN hC
  | listNilOnly hv hN => exact .emptyOnly (checkValid_sound _ hv) hN
  | listConsOnly hv hC => exact .nonemptyOnly (checkValid_sound _ hv) hC
  | listWild hw => exact .wildcard hw

theorem Covers.assuming {Δ Δ' i branches} (h : Covers Δ i branches)
    (hp : (⟨Δ', Δ⟩ : ForallProblem).Valid) : Covers Δ' i branches := by
  cases h with
  | full hN hC => exact .full hN hC
  | emptyOnly hv hN => exact .emptyOnly (fun σ hΔ => hv σ (hp σ hΔ)) hN
  | nonemptyOnly hv hC => exact .nonemptyOnly (fun σ hΔ => hv σ (hp σ hΔ)) hC
  | wildcard hw => exact .wildcard hw

def interpret (rows : CountSubstitution.Bindings) (i : Interval) : Interval :=
  ⟨CountSubstitution.count rows i.lo, CountSubstitution.count rows i.hi⟩

/-- Instantiation transports the path premises together with the interval.
    Coverage needs no additional successful solver call at a specialization. -/
theorem Covers.transport (rows : CountSubstitution.Bindings) (hf : CountSubstitution.Finite rows)
    {Δ i branches} (h : Covers Δ i branches) :
    Covers (Δ.map (CountSubstitution.constraint rows)) (interpret rows i) branches := by
  cases h with
  | full hN hC => exact .full hN hC
  | emptyOnly hv hN =>
      apply Covers.emptyOnly ?_ hN
      simpa only [interpret, mustBeEmpty, CountSubstitution.problem, List.map_cons,
        List.map_nil, CountSubstitution.constraint, CountSubstitution.count] using
        CountSubstitution.valid rows hf hv
  | nonemptyOnly hv hC =>
      apply Covers.nonemptyOnly ?_ hC
      simpa only [interpret, mustBeNonempty, CountSubstitution.problem, List.map_cons,
        List.map_nil, CountSubstitution.constraint, CountSubstitution.count] using
        CountSubstitution.valid rows hf hv
  | wildcard hw => exact .wildcard hw

def check (Δ : List Constraint) (i : Interval) (branches : List (MatchPattern × Expr)) :
    Except String (PLift (Covers Δ i branches)) := do
  if hw : hasWildcardBranchB branches = true then
    pure ⟨.wildcard ((hasWildcardBranch_iff branches).mp hw)⟩
  else if hN : hasNilBranchB branches = true then
    let hN := (hasNilBranch_iff branches).mp hN
    if hC : hasConsBranchB branches = true then
      pure ⟨.full hN ((hasConsBranch_iff branches).mp hC)⟩
    else if hv : checkValid (mustBeEmpty Δ i.hi) = .valid then
      pure ⟨.emptyOnly (checkValid_sound _ hv) hN⟩
    else throw "bounds: Nil-only match does not prove every admitted List is empty"
  else if hC : hasConsBranchB branches = true then
    if hv : checkValid (mustBeNonempty Δ i.lo) = .valid then
      pure ⟨.nonemptyOnly (checkValid_sound _ hv) ((hasConsBranch_iff branches).mp hC)⟩
    else throw "bounds: Cons-only match does not prove every admitted List is nonempty"
  else throw "bounds: List match has no covering Nil, Cons or wildcard branch"

theorem nil_refine {i : Interval} {σ} (hn : i.Contains σ (.ofNat 0)) :
    ∀ c ∈ nilRefine i.lo, c.Holds σ := by
  intro c hc
  simp [nilRefine] at hc
  subst c
  exact hn.1

theorem cons_refine {i : Interval} {σ n} (hn : i.Contains σ (.ofNat (n + 1))) :
    ∀ c ∈ consRefine i.hi, c.Holds σ := by
  intro c hc
  simp [consRefine] at hc
  subst c
  exact ExtNat.le_trans (show ExtNat.le (.ofNat 1) (.ofNat (n + 1)) by simp [ExtNat.le]) hn.2

def tail (i : Interval) : Interval := ⟨.pred i.lo, .pred i.hi⟩

theorem tail_interpret (rows : CountSubstitution.Bindings) (i : Interval) :
    interpret rows (tail i) = tail (interpret rows i) := rfl

theorem tail_contains {i : Interval} {σ n} (hn : i.Contains σ (.ofNat (n + 1))) :
    (tail i).Contains σ (.ofNat n) := by
  constructor
  · change ExtNat.le (ExtNat.pred (i.lo.eval σ)) (.ofNat n)
    have hl := hn.1
    cases he : i.lo.eval σ with
    | inf => simp [he, ExtNat.le] at hl
    | ofNat k =>
        simp [he, ExtNat.le] at hl
        simp only [ExtNat.pred, ExtNat.le]
        omega
  · change ExtNat.le (.ofNat n) (ExtNat.pred (i.hi.eval σ))
    have hh := hn.2
    cases he : i.hi.eval σ with
    | inf => trivial
    | ofNat k =>
        simp [he, ExtNat.le] at hh
        simp only [ExtNat.pred, ExtNat.le]
        omega

/-- The nonempty path premise is essential: `pred 0 = 0` alone would falsely
    let a zero-length tail reconstruct a length-one list inside `[0,0]`. -/
theorem cons_contains {i : Interval} {σ n}
    (hp : ∀ c ∈ consRefine i.hi, c.Holds σ) (hn : (tail i).Contains σ (.ofNat n)) :
    i.Contains σ (.ofNat (n + 1)) := by
  constructor
  · have hl := hn.1
    change ExtNat.le (ExtNat.pred (i.lo.eval σ)) (.ofNat n) at hl
    cases he : i.lo.eval σ with
    | inf => simp [he, ExtNat.pred, ExtNat.le] at hl
    | ofNat k =>
        simp [he, ExtNat.pred, ExtNat.le] at hl
        simp only [ExtNat.le]
        omega
  · have hh := hn.2
    change ExtNat.le (.ofNat n) (ExtNat.pred (i.hi.eval σ)) at hh
    have positive := hp ⟨.lit 1, i.hi⟩ (by simp [consRefine])
    cases he : i.hi.eval σ with
    | inf => trivial
    | ofNat k =>
        simp [he, ExtNat.pred, ExtNat.le] at hh
        simp [Constraint.Holds, Count.eval, he, ExtNat.le] at positive
        simp only [ExtNat.le]
        omega

#print axioms Covers.sound
#print axioms Covers.transport
#print axioms check
#print axioms tail_contains
#print axioms cons_contains

end FHM.Bounds.ListBranches
