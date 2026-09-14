import FHM.Bounds.RecursiveHMContract

namespace FHM.Bounds.RecursiveHMContractTests

open RecursiveHMContract HMCountScheme

private def n : Count := .var ⟨.rigid, 7⟩
private def exact (c : Count) (a : BoundsTy := .prim .int) : BoundsTy := .list c c a
private def ann : PolyTy :=
  ⟨1, .arrow (.bl (.solid n) (.solid n) (.bvar 0)) (.bl (.solid n) (.solid n) (.bvar 0))⟩
private def hm (a : Ty := .fvar 90) : Ty := .arrow (listTy a) (listTy a)
private def succeeds (r : Except String α) : Bool := match r with | .ok _ => true | _ => false
private def fails (r : Except String α) (needle : String) : Bool :=
  match r with | .error m => (m.splitOn needle).length > 1 | _ => false

private def call (types : List BoundsTy := [.fvar 90]) (fixed : Ty := hm)
    (atCall : Ty := hm) (counts : List Count := [.lit 2]) (caller : List Nat := [])
    (premises : List Constraint := []) : Except String BoundsTy := do
  let s ← HMCountScheme.decode ann [7] [] premises
  let c ← fix s fixed types
  pure (← RecursiveHMContract.check c [] atCall counts caller).bounds

private def collision (count : Nat) : Bool :=
  match call [exact n] (hm (listTy (.prim .int))) (hm (listTy (.prim .int))) [.lit count] [7] with
  | .ok (.arrow (.list lo hi (.list a b (.prim .int)))
      (.list lo' hi' (.list a' b' (.prim .int)))) =>
      lo == .lit count && hi == .lit count && lo' == .lit count && hi' == .lit count &&
      a == n && b == n && a' == n && b' == n
  | _ => false

private def opaqueCall : Except String BoundsTy := do
  let s ← HMCountScheme.decode ann [7] []
  let o ← openFixed s hm [90] []
  pure (← RecursiveHMContract.check (fromOpaque o) [] hm [.lit 4] []).bounds

private def vacuous : Except String BoundsTy := do
  let s ← HMCountScheme.decode ⟨1, .arrow (.prim .int) (.prim .int)⟩ [] []
  let c ← fix s (.arrow (.prim .int) (.prim .int)) [.prim .char]
  pure (← RecursiveHMContract.check c [] (.arrow (.prim .int) (.prim .int)) [] []).bounds

private def formalScheme : HMCountScheme.Scheme :=
  { hm := ⟨1, .arrow (listTy (.bvar 0)) (listTy (.bvar 0))⟩
    counts := ⟨[7], [], [], .arrow (exact n (.bvar 0)) (exact n (.bvar 0))⟩
    hmWF := (Ty.bvarsBelow_iff _).mp (by decide)
    countWF := ScopedScheme.Scheme.wfBool_sound (by decide)
    shape := by simp [exact, Synth.BoundsTy.toTy, listTy, FHM.Bounds.listTyName] }

private def transportedCounts (symbolic : Bool) : Except String Bool := do
  let found := hm (listTy (.prim .int))
  let c ← fix formalScheme found [exact n]
  let u ← RecursiveHMContract.check c [] found [if symbolic then n else .lit 2] [7]
  let outer : CountSubstitution.Bindings := [(7, .lit 3)]
  let hf : CountSubstitution.Finite outer := by
    intro row hr
    have hr : row = (7, Count.lit 3) := by simpa [outer] using hr
    subst row
    exact .lit
  let hs : ∀ row ∈ outer, Scope.CountScoped [] row.2 := by
    intro row hr
    have hr : row = (7, Count.lit 3) := by simpa [outer] using hr
    subst row
    trivial
  let hk : ∀ i ∈ formalScheme.counts.captures, CountSubstitution.lookup outer i = none := by
    simp [formalScheme]
  let mapped := u.mapCounts outer hf [] hs hk
  pure (match mapped.bounds with
    | .arrow (.list lo hi (.list a b (.prim .int)))
        (.list lo' hi' (.list a' b' (.prim .int))) =>
        let result := Count.lit (if symbolic then 3 else 2)
        lo == result && hi == result && lo' == result && hi' == result &&
        a == .lit 3 && b == .lit 3 && a' == .lit 3 && b' == .lit 3
    | _ => false)

private def trueResult (r : Except String Bool) : Bool := match r with | .ok b => b | _ => false

private def cases : List (String × Bool) := [
  ("opaque group interface produces a count-only recursive assumption", succeeds opaqueCall),
  ("a recursive count call preserves the fixed opaque HM identity", succeeds call),
  ("recursive calls cannot specialize the fixed opaque identity to Int", fails
    (call [.fvar 90] hm (hm (.prim .int))) "fixed HM argument vector"),
  ("a group interface may specialize its entire HM vector once", succeeds
    (call [.prim .int] (hm (.prim .int)) (hm (.prim .int)))),
  ("calls cannot reopen an already specialized group at Char", fails
    (call [.prim .int] (hm (.prim .int)) (hm (.prim .char))) "fixed HM argument vector"),
  ("fixed HM vectors have exact arity", fails (call []) "wrong arity"),
  ("fixed vectors agree with every repeated HM slot", fails
    (call [.prim .int] (.arrow (listTy (.prim .int)) (listTy (.prim .char)))) "group monotype"),
  ("fixed HM arguments cannot contain enclosing bound slots", fails
    (call [.bvar 0]) "enclosing bound slot"),
  ("caller-owned count 7 survives callee count 7 becoming 2", collision 2),
  ("the same fixed HM vector supports a different count-only call", collision 5),
  ("complete fixed HM arguments require caller count scope", fails
    (call [exact n] (hm (listTy (.prim .int))) (hm (listTy (.prim .int)))) "outside caller scope"),
  ("recursive count witnesses retain exact arity", fails
    (call [.fvar 90] hm hm []) "arity"),
  ("recursive count witnesses must be finite", fails
    (call [.fvar 90] hm hm [.inf]) "finite"),
  ("recursive calls discharge rather than assume contract premises", fails
    (call [.fvar 90] hm hm [.lit 2] [] [⟨n, .lit 0⟩]) "premises"),
  ("a vacuous forall retains an arbitrary fixed non-Unit witness", succeeds vacuous),
  ("outer count transport maps symbolic call and caller-owned type counts together", trueResult (transportedCounts true)),
  ("outer count transport leaves literal callee arguments independent of caller-owned types", trueResult (transportedCounts false))]

/-- This is a universally quantified assumption-use transport proof, not a
    solver verdict and not an assertion that the recursive implementation exists. -/
theorem fullBoundsUseTransport {s fixedFound Δ found caller} {c : Fixed s fixedFound}
    (u : RecursiveHMContract.Use c Δ found caller) (f : Nat → BoundsTy)
    (hf : ∀ i, (Synth.BoundsTy.toTy (f i)).IsLC)
    (captured : ∀ i ∈ s.hm.body.freeVars, f i = .fvar i)
    (scope : (c.types.map (SchemeSpecialization.mapFree f)).all (ScopedScheme.boundsScopedBool caller) = true) :
    (u.map f hf captured scope).bounds = SchemeSpecialization.mapFree f u.bounds ∧
    (u.map f hf captured scope).counts = u.counts ∧
    ScopedScheme.BoundsScoped caller (u.map f hf captured scope).bounds :=
  ⟨u.map_bounds f hf captured scope, rfl, (u.map f hf captured scope).inScope⟩

#print axioms fullBoundsUseTransport

theorem finiteCountUseTransport {s fixedFound Δ found caller} {c : Fixed s fixedFound}
    (u : RecursiveHMContract.Use c Δ found caller) (outer : CountSubstitution.Bindings)
    (hf : CountSubstitution.Finite outer) (target : List Nat)
    (hs : ∀ row ∈ outer, Scope.CountScoped target row.2)
    (hk : ∀ i ∈ s.counts.captures, CountSubstitution.lookup outer i = none) :
    (u.mapCounts outer hf target hs hk).bounds = CountSubstitution.bounds outer u.bounds ∧
    ScopedScheme.BoundsScoped (caller ++ target) (u.mapCounts outer hf target hs hk).bounds :=
  ⟨u.mapCounts_bounds outer hf target hs hk, (u.mapCounts outer hf target hs hk).inScope⟩

#print axioms finiteCountUseTransport

def main : IO Unit := do
  let mut failures := 0
  for (name, ok) in cases do
    IO.println s!"{if ok then "PASS" else "FAIL"}: {name}"
    unless ok do failures := failures + 1
  unless failures = 0 do throw (IO.userError s!"{failures} fixed recursive HM contract regressions failed")

#eval main

end FHM.Bounds.RecursiveHMContractTests
