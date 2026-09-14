import FHM.Bounds.ListBranches

namespace FHM.Bounds.ListBranchesTests

open ListBranches

private def body : Expr := .primLit (.int 1)
private def nil : List (MatchPattern × Expr) := [(.named nilCtorName 0, body)]
private def cons : List (MatchPattern × Expr) := [(.named consCtorName 2, body)]
private def interval (lo hi : Nat) : Interval := ⟨.lit lo, .lit hi⟩
private def accepts (i : Interval) (branches : List (MatchPattern × Expr)) (Δ : List Constraint := []) : Bool :=
  match check Δ i branches with | .ok _ => true | .error _ => false

private def leBool : ExtNat → ExtNat → Bool
  | _, .inf => true
  | .inf, .ofNat _ => false
  | .ofNat a, .ofNat b => a ≤ b

private def contains (i : Interval) (n : Nat) : Bool :=
  leBool (i.lo.eval (fun _ => 0)) (.ofNat n) && leBool (.ofNat n) (i.hi.eval (fun _ => 0))

example {Δ i branches σ n} (h : Covers Δ i branches)
    (hp : ∀ c ∈ Δ, c.Holds σ) (hn : i.Contains σ (.ofNat n)) : CoveredAt branches n := h.sound hp hn

example {i σ n} (hn : i.Contains σ (.ofNat (n + 1))) :
    (tail i).Contains σ (.ofNat n) := tail_contains hn

example {i σ n} (hp : ∀ c ∈ consRefine i.hi, c.Holds σ)
    (hn : (tail i).Contains σ (.ofNat n)) : i.Contains σ (.ofNat (n + 1)) := cons_contains hp hn

example {Δ i branches} (h : Covers Δ i branches) (rows : CountSubstitution.Bindings)
    (hf : CountSubstitution.Finite rows) :
    Covers (Δ.map (CountSubstitution.constraint rows)) (interpret rows i) branches := h.transport rows hf

private def k : Count := .var ⟨.rigid, 7⟩
private def cases : List (String × Bool) := [
  ("both proper constructors cover open List bounds", accepts ⟨.lit 0, .inf⟩ (nil ++ cons)),
  ("wildcard covers open List bounds", accepts ⟨.lit 0, .inf⟩ [(.wildcard, body)]),
  ("Nil-only covers exact empty List", accepts (interval 0 0) nil),
  ("Cons-only covers exact positive List", accepts (interval 2 2) cons),
  ("Cons-only covers nonempty unbounded List", accepts ⟨.lit 1, .inf⟩ cons),
  ("Nil-only cannot cover maybe-nonempty List", !accepts (interval 0 1) nil),
  ("Cons-only cannot cover maybe-empty List", !accepts (interval 0 5) cons),
  ("empty branch set rejects", !accepts (interval 0 0) []),
  ("wrong Nil pattern arity is not coverage evidence", !accepts (interval 0 0) [(.named nilCtorName 1, body)]),
  ("wrong Cons pattern arity is not coverage evidence", !accepts (interval 1 1) [(.named consCtorName 1, body)]),
  ("unrelated constructor is not List coverage", !accepts (interval 0 0) [(.named ⟨"Other"⟩ 0, body)]),
  ("symbolic nonempty path can justify Cons-only", accepts ⟨k, k⟩ cons [⟨.lit 1, k⟩]),
  ("symbolic empty path can justify Nil-only", accepts ⟨k, k⟩ nil [⟨k, .lit 0⟩]),
  ("symbolic count without path evidence cannot justify Cons-only", !accepts ⟨k, k⟩ cons),
  ("predecessor tail of singleton is empty", contains (tail (interval 1 1)) 0),
  ("predecessor tail of positive exact length preserves exactness", contains (tail (interval 3 3)) 2),
  ("predecessor preserves infinite upper endpoint", contains (tail ⟨.lit 0, .inf⟩) 100),
  ("truncated predecessor alone is insufficient for Cons reconstruction",
    contains (tail (interval 0 0)) 0 && !contains (interval 0 0) 1)]

def main : IO Unit := do
  for (name, ok) in cases do
    IO.println s!"{if ok then "PASS" else "FAIL"}: {name}"
    unless ok do throw (IO.userError s!"List branch regression: {name}")

#eval main

end FHM.Bounds.ListBranchesTests
