import FHM.Bounds.CountContract

namespace FHM.Bounds.CountContractTests

open SchemeTyping CountSubstitution CountContract

private def n : Count := .var ⟨.rigid, 7⟩
private def hmScheme : SchemeTyping.Scheme :=
  ⟨⟨1, .arrow (listTy (.bvar 0)) (listTy (.bvar 0))⟩,
    .arrow (.list n n (.bvar 0)) (.list n n (.bvar 0)),
    by
      change ContainsBvarsUpTo 1 (.arrow (listTy (.bvar 0)) (listTy (.bvar 0)))
      have h : ContainsBvarsUpTo 1 (listTy (.bvar 0)) := .customTy (by
        intro t ht
        simp only [List.mem_singleton] at ht
        subst t
        exact .bvar (by omega))
      exact .arrow h h,
    by simp [Synth.BoundsTy.toTy, listTy, FHM.Bounds.listTyName, _root_.listTyName]⟩
private def rhs : Expr := .lambda none (.var 0)

-- These are formal RHS certificates, not invented maps fed into a production
-- traversal. The implementation meets its exact function contract for all
-- locally closed caller type bounds under the declared count premises.
private def certificate (guarded : Bool := false) : Certified [] rhs where
  hm := hmScheme
  counts := { quantified := [7], captures := []
              premises := if guarded then [⟨n, .lit 5⟩] else []
              body := hmScheme.body }
  body := rfl
  wf := by
    cases guarded <;> exact ScopedScheme.Scheme.wfBool_sound (by decide)
  captureScope := by simp
  typing := by
    intro args _
    exact .lambda True.intro (.varMono rfl)

private def found (a : Ty) : Ty := .arrow (listTy a) (listTy a)
private def succeeds (r : Except String α) : Bool := match r with | .ok _ => true | _ => false
private def fails (r : Except String α) (needle : String) : Bool :=
  match r with | .error m => (m.splitOn needle).length > 1 | _ => false

private def run (counts : List Count) (args : List BoundsTy) (hm : Ty)
    (scope : List Nat := []) (Δ : List Constraint := []) (guarded : Bool := false) :=
  CountContract.check (certificate guarded) Δ hm counts args scope

private def cap : Count := .var ⟨.rigid, 99⟩
private def outer : BoundsTy := .list cap cap (.prim .char)
private def capturedHM : SchemeTyping.Scheme :=
  ⟨⟨1, .arrow (listTy (.bvar 0)) (listTy (.prim .char))⟩,
    .arrow (.list n n (.bvar 0)) outer,
    by
      change ContainsBvarsUpTo 1 (.arrow (listTy (.bvar 0)) (listTy (.prim .char)))
      exact .arrow (.customTy (by
        intro t ht
        simp only [List.mem_singleton] at ht
        subst t
        exact .bvar (by omega))) (.customTy (by
        intro t ht
        simp only [List.mem_singleton] at ht
        subst t
        exact .prim)),
    by simp [outer, Synth.BoundsTy.toTy, listTy, FHM.Bounds.listTyName, _root_.listTyName]⟩
private def capturedCertificate : Certified [.mono outer] (.lambda none (.var 1)) where
  hm := capturedHM
  counts := { quantified := [7], captures := [99], premises := [⟨n, cap⟩], body := capturedHM.body }
  body := rfl
  wf := ScopedScheme.Scheme.wfBool_sound (by decide)
  captureScope := by
    intro b hb
    simp only [List.mem_singleton] at hb
    subst b
    change ScopedScheme.BoundsScoped [99] (.list cap cap (.prim .char))
    exact ⟨by simp [Scope.CountScoped, cap], by simp [Scope.CountScoped, cap], trivial⟩
  typing := by
    intro args _
    exact .lambda True.intro (.varMono rfl)

private def capturedRun (scope : List Nat) (Δ : List Constraint) :=
  CountContract.check capturedCertificate Δ (found (.prim .char)) [.lit 3] [.prim .char] scope

private def cases : List (String × Bool) := [
  ("RHS-certified count and HM specialization", match run [.lit 3] [.prim .char] (found (.prim .char)) with
    | .ok r => r.bounds.pretty == "BL 3 3 Char → BL 3 3 Char" | _ => false),
  ("different count uses remain independent", succeeds (run [.lit 1] [.prim .int] (found (.prim .int))) &&
    succeeds (run [.lit 4] [.prim .int] (found (.prim .int)))),
  ("caller count colliding with scheme ID is not rewritten", match
    run [.lit 3] [.list n n (.prim .char)] (found (listTy (.prim .char))) [7] with
    | .ok r => match r.bounds with
      | .arrow (.list (.lit 3) (.lit 3) (.list lo hi (.prim .char)))
          (.list (.lit 3) (.lit 3) (.list lo' hi' (.prim .char))) =>
          lo == n && hi == n && lo' == n && hi' == n
      | _ => false
    | _ => false),
  ("symbolic count arguments checked in caller scope", succeeds
    (run [.var ⟨.rigid, 99⟩] [.prim .char] (found (.prim .char)) [99])),
  ("unscoped symbolic count argument rejected", fails
    (run [.var ⟨.rigid, 99⟩] [.prim .char] (found (.prim .char))) "outside caller scope"),
  ("infinite Nat count argument rejected", fails
    (run [.inf] [.prim .char] (found (.prim .char))) "finite"),
  ("wrong count arity rejected", fails (run [] [.prim .char] (found (.prim .char))) "arity"),
  ("wrong HM arguments rejected", fails
    (run [.lit 3] [.prim .int] (found (.prim .char))) "disagree"),
  ("missing HM argument rejected", fails (run [.lit 3] [] (found (.prim .char))) "disagree"),
  ("extra HM argument rejected", fails
    (run [.lit 3] [.prim .char, .prim .int] (found (.prim .char))) "disagree"),
  ("uncaptured caller slot counts rejected", fails
    (run [.lit 3] [.list n n (.prim .char)] (found (listTy (.prim .char)))) "outside caller scope"),
  ("non-LC HM argument rejected", fails (run [.lit 3] [.bvar 0] (found (.bvar 0))) "enclosing"),
  ("true instantiated declaration premise discharged", succeeds
    (run [.lit 3] [.prim .char] (found (.prim .char)) [] [] true)),
  ("false instantiated declaration premise rejected", fails
    (run [.lit 8] [.prim .char] (found (.prim .char)) [] [] true) "not established"),
  ("caller assumptions discharge symbolic declaration premise", succeeds
    (run [.var ⟨.rigid, 99⟩] [.prim .char] (found (.prim .char)) [99]
      [⟨.var ⟨.rigid, 99⟩, .lit 5⟩] true)),
  ("symbolic declaration premise is not silently asserted", fails
    (run [.var ⟨.rigid, 99⟩] [.prim .char] (found (.prim .char)) [99] [] true) "not established"),
  ("captured outer count and environment preserved", match capturedRun [99] [⟨.lit 3, cap⟩] with
    | .ok r => match r.bounds with
      | .arrow (.list (.lit 3) (.lit 3) (.prim .char)) (.list lo hi (.prim .char)) => lo == cap && hi == cap
      | _ => false
    | _ => false),
  ("captured count must exist in caller scope", fails (capturedRun [] [⟨.lit 3, cap⟩]) "capture"),
  ("captured requirement needs independent caller evidence", fails (capturedRun [99] []) "not established")]

example {env rhs Δ found scope} (r : CountContract.Result Δ env rhs found scope) :
    Derives Δ env rhs r.bounds ∧ Synth.BoundsTy.toTy r.bounds = found.eraseBounds ∧
    ScopedScheme.BoundsScoped scope r.bounds := ⟨r.derivation, r.shape, r.countScope⟩

def main : IO Unit := do
  for (name, ok) in cases do
    IO.println s!"{if ok then "PASS" else "FAIL"}: {name}"
    unless ok do throw (IO.userError s!"certified count-contract regression: {name}")

#eval main
#print axioms certificate

end FHM.Bounds.CountContractTests
