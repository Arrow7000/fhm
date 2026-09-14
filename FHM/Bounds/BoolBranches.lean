import FHM.Bounds.Semantic

/-! Bool coverage is finite constructor coverage, independent of arithmetic
    solver verdicts. A comparison introduces no additional length assumption. -/

namespace FHM.Bounds.BoolBranches

def trueCtorName : CtorName := ⟨"True"⟩
def falseCtorName : CtorName := ⟨"False"⟩

def IsCtor (name : CtorName) : Prop := name = trueCtorName ∨ name = falseCtorName
instance (name : CtorName) : Decidable (IsCtor name) :=
  inferInstanceAs (Decidable (name = trueCtorName ∨ name = falseCtorName))

def Pattern (p : MatchPattern) : Prop :=
  p = .wildcard ∨ p = .named trueCtorName 0 ∨ p = .named falseCtorName 0
instance (p : MatchPattern) : Decidable (Pattern p) :=
  inferInstanceAs (Decidable
    (p = .wildcard ∨ p = .named trueCtorName 0 ∨ p = .named falseCtorName 0))

inductive Covers (branches : List (MatchPattern × Expr)) : Prop where
  | full : (∃ body, (.named trueCtorName 0, body) ∈ branches) →
      (∃ body, (.named falseCtorName 0, body) ∈ branches) → Covers branches
  | wildcard : hasWildcardBranch branches → Covers branches

theorem Covers.sound {branches} (h : Covers branches) (value : Bool) :
    hasWildcardBranch branches ∨
      ∃ body, (.named (if value then trueCtorName else falseCtorName) 0, body) ∈ branches := by
  cases h with
  | full ht hf => cases value <;> simp_all
  | wildcard hw => exact .inl hw

private def has (name : CtorName) (branches : List (MatchPattern × Expr)) : Bool :=
  branches.any (fun br => br.1 == .named name 0)

private theorem has_sound {name branches} (h : has name branches = true) :
    ∃ body, (.named name 0, body) ∈ branches := by
  rcases List.any_eq_true.mp h with ⟨⟨pat, body⟩, hm, hp⟩
  have hp : pat = .named name 0 := by simpa using hp
  subst pat
  exact ⟨body, hm⟩

def check (branches : List (MatchPattern × Expr)) : Except String (PLift (Covers branches)) := do
  if hw : hasWildcardBranchB branches = true then
    pure ⟨.wildcard ((hasWildcardBranch_iff branches).mp hw)⟩
  else if ht : has trueCtorName branches = true then
    if hf : has falseCtorName branches = true then
      pure ⟨.full (has_sound ht) (has_sound hf)⟩
    else throw "bounds: Bool match is missing False coverage"
  else throw "bounds: Bool match is missing True coverage"

#print axioms Covers.sound
#print axioms check

end FHM.Bounds.BoolBranches
