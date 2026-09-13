import FHM.Bounds.ScopedScheme

namespace FHM.Bounds.ScopedSchemeTests

open ScopedScheme Scope CountSubstitution

private def n : Count := .var ⟨.rigid, 7⟩
private def capture : Count := .var ⟨.rigid, 99⟩

private def scheme : Scheme :=
  { quantified := [7], captures := [99]
    premises := [⟨n, capture⟩]
    body := .arrow (.list n n (.prim .int)) (.list (.lit 0) capture (.prim .int)) }

private def accepted (s : Scheme) (args : List Count) (caller : List Nat) : Bool :=
  match s.instantiate args caller with
  | .ok _ => true
  | .error _ => false

private def hasBounds (s : Scheme) (args : List Count) (caller : List Nat)
    (expected : String) : Bool :=
  match s.instantiate args caller with
  | .ok inst => inst.bounds.pretty == expected
  | .error _ => false

private def premiseRetained : Bool :=
  match scheme.instantiate [.lit 3] [99] with
  | .ok inst => match inst.premises with
      | [c] => c.lhs == .lit 3 && c.rhs == capture
      | _ => false
  | .error _ => false

private def usable (s : Scheme) (args : List Count) (caller : List Nat)
    (Δ : List Constraint) : Bool :=
  match s.instantiate args caller with
  | .ok inst => match inst.checkPremises Δ with
      | .ok _ => true
      | .error _ => false
  | .error _ => false

private def finiteContract : Scheme :=
  { quantified := [7], captures := [], premises := [⟨n, .lit 5⟩]
    body := .list n n (.prim .int) }

-- A scoped result does not prove the caller meets its premises. At capture=1
-- this instance's 3≤capture requirement is false, despite successful scoping.
example : ¬ (⟨[], [⟨.lit 3, capture⟩]⟩ : ForallProblem).Valid := by
  intro h
  have bad := h (fun _ => 1) (by simp) ⟨.lit 3, capture⟩ (by simp)
  simp [capture, Constraint.Holds, Count.eval, ExtNat.le] at bad

example {args caller} (inst : Instance scheme args caller) (σ : Assign) :
    assignment (scheme.quantified.zip args) σ ⟨.rigid, 99⟩ = σ ⟨.rigid, 99⟩ :=
  inst.capture_assignment σ (by simp [scheme])

example {args caller} (inst : Instance scheme args caller) :
    BoundsScoped caller inst.bounds := inst.bodyScoped

private theorem declaredInclusion : SemanticSub scheme.premises
    (.list n n (.prim .int)) (.list (.lit 0) capture (.prim .int)) := by
  apply SemanticSub.list
  · apply Interval.subGoals_valid_iff.mpr
    intro σ hp
    constructor
    · simp [n, Count.eval, ExtNat.le]
    · exact hp ⟨n, capture⟩ (by simp [scheme])
  · exact .prim

-- Instantiation may be used under caller assumptions only with independent
-- evidence discharging its instantiated premises.
example {args caller Δ} (inst : Instance scheme args caller) (hu : inst.Usable Δ) :
    SemanticSub Δ (bounds (scheme.quantified.zip args) (.list n n (.prim .int)))
      (bounds (scheme.quantified.zip args) (.list (.lit 0) capture (.prim .int))) :=
  inst.useSubtype hu declaredInclusion

private def cases : List (String × Bool) := [
  ("noncontiguous quantified ID with fixed capture", hasBounds scheme [.lit 3] [99]
    "BL 3 3 Int → BL 0 n99 Int"),
  ("symbolic caller argument remains in caller scope", hasBounds scheme
    [.pred (.var ⟨.rigid, 1234⟩)] [99, 1234]
    "BL (pred n1234) (pred n1234) Int → BL 0 n99 Int"),
  ("instantiated premises are retained, not discharged", premiseRetained),
  ("different uses instantiate independently", hasBounds scheme [.lit 3] [99]
    "BL 3 3 Int → BL 0 n99 Int" && hasBounds scheme [.lit 8] [99]
    "BL 8 8 Int → BL 0 n99 Int"),
  ("monomorphic scheme", accepted { quantified := [], captures := [], body := .prim .int } [] []),
  ("literal infinity endpoint remains legal", accepted
    { quantified := [7], captures := [], body := .list n .inf (.prim .int) } [.lit 3] []),
  ("repeated quantifier rejected", !accepted { scheme with quantified := [7, 7] } [.lit 3, .lit 4] [99]),
  ("capture cannot also be quantified", !accepted { scheme with captures := [7, 99] } [.lit 3] [7, 99]),
  ("unknown identity in body rejected", !accepted { scheme with captures := [] } [.lit 3] [99]),
  ("inferable machine identity is not implicitly generalized", !accepted
    { scheme with body := .list (.var ⟨.inferable, 7⟩) .inf (.prim .int) } [.lit 3] [99]),
  ("unknown identity in premise rejected", !accepted
    { scheme with premises := [⟨n, .var ⟨.rigid, 1234⟩⟩] } [.lit 3] [99, 1234]),
  ("wrong arity rejected", !accepted scheme [] [99]),
  ("infinite Nat argument rejected", !accepted scheme [.inf] [99]),
  ("argument outside caller scope rejected", !accepted scheme [.var ⟨.rigid, 1234⟩] [99]),
  ("capture outside caller scope rejected", !accepted scheme [.lit 3] []),
  ("ground instantiated premise discharged", usable finiteContract [.lit 3] [] []),
  ("false ground instantiated premise rejects use", !usable finiteContract [.lit 8] [] []),
  ("caller premise discharges captured requirement", usable scheme [.lit 3] [99] [⟨.lit 3, capture⟩]),
  ("scope alone does not discharge captured requirement", !usable scheme [.lit 3] [99] [])]

def main : IO Unit := do
  for (name, ok) in cases do
    IO.println s!"{if ok then "PASS" else "FAIL"}: {name}"
    unless ok do throw (IO.userError s!"scoped scheme regression: {name}")

#eval main

end FHM.Bounds.ScopedSchemeTests
