import FHM.Bounds.Semantic

/-! Pair coverage is finite single-constructor coverage. It is independent of
arithmetic constraints, but it retains the constructor's exact field arity. -/

namespace FHM.Bounds.PairBranches

def Pattern (p : MatchPattern) : Prop :=
  p = .wildcard ∨ p = .named pairCtorName 2

instance (p : MatchPattern) : Decidable (Pattern p) :=
  inferInstanceAs (Decidable (p = .wildcard ∨ p = .named pairCtorName 2))

inductive Covers (branches : List (MatchPattern × Expr)) : Prop where
  | constructor : (∃ body, (.named pairCtorName 2, body) ∈ branches) → Covers branches
  | wildcard : hasWildcardBranch branches → Covers branches

theorem Covers.sound {branches} (h : Covers branches) :
    hasWildcardBranch branches ∨ ∃ body, (.named pairCtorName 2, body) ∈ branches := by
  cases h with
  | constructor pair => exact .inr pair
  | wildcard wild => exact .inl wild

private def hasPair (branches : List (MatchPattern × Expr)) : Bool :=
  branches.any (fun br => br.1 == .named pairCtorName 2)

private theorem hasPair_sound {branches} (h : hasPair branches = true) :
    ∃ body, (.named pairCtorName 2, body) ∈ branches := by
  rcases List.any_eq_true.mp h with ⟨⟨pat, body⟩, member, isPair⟩
  have same : pat = .named pairCtorName 2 := by simpa using isPair
  subst pat
  exact ⟨body, member⟩

def check (branches : List (MatchPattern × Expr)) : Except String (PLift (Covers branches)) := do
  if hw : hasWildcardBranchB branches = true then
    pure ⟨.wildcard ((hasWildcardBranch_iff branches).mp hw)⟩
  else if hp : hasPair branches = true then
    pure ⟨.constructor (hasPair_sound hp)⟩
  else throw "bounds: Pair match is missing Pair coverage"

#print axioms Covers.sound
#print axioms check

end FHM.Bounds.PairBranches
