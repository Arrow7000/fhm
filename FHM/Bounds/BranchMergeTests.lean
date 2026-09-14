import FHM.Bounds.BranchMerge

/-! Solver-free regressions for variance-correct upper/lower branch candidates.
Empty list intersections are permitted: they describe no possible argument,
not a fabricated inhabitant or evidence that a branch is unreachable.
-/

namespace FHM.Bounds.BranchMergeTests

open BranchMerge

private def int : BoundsTy := .prim .int
private def list (lo hi : Nat) (elem : BoundsTy := int) : BoundsTy := .list (.lit lo) (.lit hi) elem
private def merged (mode : Mode) (a b : BoundsTy) (expected : String) : Bool :=
  match combine mode a b with | .ok ⟨c, _⟩ => c.pretty == expected | .error _ => false
private def rejected (mode : Mode) (a b : BoundsTy) : Bool :=
  match combine mode a b with | .error _ => true | _ => false

example {a b c} (h : Combines .upper a b c) (Δ : List Constraint) :
    SemanticSub Δ a c ∧ SemanticSub Δ b c := h.sound Δ

example {a b c} (h : Combines .lower a b c) (Δ : List Constraint) :
    SemanticSub Δ c a ∧ SemanticSub Δ c b := h.sound Δ

example {mode a b c} (h : Combines mode a b c) :
    Synth.BoundsTy.toTy c = Synth.BoundsTy.toTy a ∧
    Synth.BoundsTy.toTy c = Synth.BoundsTy.toTy b := h.shape

example {mode a b c ids} (h : Combines mode a b c)
    (ha : ScopedScheme.BoundsScoped ids a) (hb : ScopedScheme.BoundsScoped ids b) :
    ScopedScheme.BoundsScoped ids c := h.scoped ids ha hb

example {a a' b b' d r} (hd : Combines .lower a a' d) (hr : Combines .upper b b' r)
    (Δ : List Constraint) :
    SemanticSub Δ (.arrow a b) (.arrow d r) ∧ SemanticSub Δ (.arrow a' b') (.arrow d r) :=
  (Combines.arrow (mode := .upper) hd hr).sound Δ

private def cases : List (String × Bool) := [
  ("List branch join uses union interval", merged .upper (list 1 2) (list 3 4) "BL 1 4 Int"),
  ("List lower candidate uses intersection interval", merged .lower (list 1 4) (list 2 3) "BL 2 3 Int"),
  ("disjoint list intersection remains explicitly empty", merged .lower (list 1 1) (list 2 2) "BL 2 1 Int"),
  ("arrow branch join intersects domains rather than widening them", merged .upper
    (.arrow (list 1 1) int) (.arrow (list 2 2) int) "BL 2 1 Int → Int"),
  ("arrow lower candidate unions domains", merged .lower
    (.arrow (list 1 1) int) (.arrow (list 2 2) int) "BL 1 2 Int → Int"),
  ("arrow branch join unions codomains", merged .upper
    (.arrow int (list 1 1)) (.arrow int (list 2 2)) "Int → BL 1 2 Int"),
  ("nested arrow domain reverses variance twice", merged .upper
    (.arrow (.arrow (list 1 1) int) int) (.arrow (.arrow (list 2 2) int) int)
    "(BL 1 2 Int → Int) → Int"),
  ("nested List element bounds also merge", merged .upper (list 1 1 (list 2 2)) (list 2 2 (list 3 3))
    "BL 1 2 (BL 2 3 Int)"),
  ("positive infinity upper endpoint survives union", merged .upper
    (.list (.lit 1) .inf int) (list 2 4) "BL 1 ∞ Int"),
  ("finite upper endpoint survives intersection with infinity", merged .lower
    (.list (.lit 1) .inf int) (list 2 4) "BL 2 4 Int"),
  ("symbolic counts are retained without oracle solving", match combine .upper
    (.list (.var ⟨.rigid, 7⟩) (.var ⟨.rigid, 7⟩) int)
    (.list (.var ⟨.rigid, 7⟩) (.var ⟨.rigid, 7⟩) int) with
    | .ok ⟨.list (.min (.var ⟨.rigid, 7⟩) (.var ⟨.rigid, 7⟩))
        (.max (.var ⟨.rigid, 7⟩) (.var ⟨.rigid, 7⟩)) (.prim .int), _⟩ => true
    | _ => false),
  ("same captured HM identity is preserved", match combine .upper (.fvar 7) (.fvar 7) with
    | .ok ⟨.fvar 7, _⟩ => true | _ => false),
  ("distinct captured HM identities are never unified by bounds", rejected .upper (.fvar 7) (.fvar 8)),
  ("distinct primitive shapes reject", rejected .upper int (.prim .char)),
  ("constructor arity disagreement rejects", rejected .upper (.custom ⟨"Box"⟩ [int]) (.custom ⟨"Box"⟩ [])),
  ("constructor name disagreement rejects", rejected .lower (.custom ⟨"Box"⟩ [int]) (.custom ⟨"Other"⟩ [int]))]

def main : IO Unit := do
  for (name, ok) in cases do
    IO.println s!"{if ok then "PASS" else "FAIL"}: {name}"
    unless ok do throw (IO.userError s!"branch merge regression: {name}")

#eval main

end FHM.Bounds.BranchMergeTests
