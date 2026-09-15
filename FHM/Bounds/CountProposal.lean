import FHM.Bounds.ScopedScheme

/-! # Untrusted direct count proposals from argument bounds

Selected declaration identities exposed directly at interval endpoints are
proposed.  We also peel a literal summand from a ground finite endpoint, the
single unambiguous arithmetic inversion needed by domains such as `n + 1`.
Captured identities are never generalized and HM slots are opaque. Repeated
coordinates keep their first proposal: the consuming checker must validate all remaining obligations.
Truly domain-absent coordinates receive zero as a finite witness, not an inferred
invariant. No proposal establishes typing, scope, finiteness or premise validity.
-/

namespace FHM.Bounds.CountProposal

private def selected (ids : List Nat) : Count → List Nat
  | .lit _ | .inf => []
  | .var ⟨.rigid, i⟩ => if ids.contains i then [i] else []
  | .var ⟨.inferable, _⟩ => []
  | .add a b | .mul a b | .min a b | .max a b => selected ids a ++ selected ids b
  | .pred a => selected ids a

private abbrev Proposals := List (Nat × Count) × List Nat

private def combine (a b : Proposals) : Proposals := (a.1 ++ b.1, a.2 ++ b.2)

/-- A direct proposal at one endpoint cannot erase an unsupported compound
    occurrence of the same coordinate at the other endpoint.  Such a List
    domain denotes an inequality range, not an exact pin (for example
    `BL x (2*x)` against an exact length).  Cross-argument origins are still
    combined later and may independently discharge an earlier compound use. -/
private def keepUnblocked (p : Proposals) : Proposals :=
  (p.1.filter (fun row => !p.2.contains row.1), p.2)

/-- Evaluate only syntactically ground, finite count arithmetic.  This is a
    proposal helper, not a solver and not acceptance evidence. -/
private def groundNat? : Count → Option Nat
  | .lit n => some n
  | .add a b => do pure ((← groundNat? a) + (← groundNat? b))
  | .mul a b => do pure ((← groundNat? a) * (← groundNat? b))
  | .pred a => do pure ((← groundNat? a) - 1)
  | .min a b => do pure (min (← groundNat? a) (← groundNat? b))
  | .max a b => do pure (max (← groundNat? a) (← groundNat? b))
  | .var _ | .inf => none

private def peelLiteral (actual : Count) (offset : Nat) : Option Count := do
  let value ← groundNat? actual
  if offset ≤ value then some (.lit (value - offset)) else none

/-- Deliberately narrow inversion.  We do not invert multiplication, `pred`,
    min/max, multiple variables, or symbolic right-hand sides. -/
private def additiveEndpoint (ids : List Nat) (pattern actual : Count) : Option (Nat × Count) :=
  match pattern with
  | .add (.var ⟨.rigid, i⟩) (.lit offset)
  | .add (.lit offset) (.var ⟨.rigid, i⟩) =>
      if ids.contains i then (peelLiteral actual offset).map fun value => (i, value) else none
  | _ => none

private def endpoint (ids : List Nat) (pattern actual : Count) : Proposals :=
  match pattern with
  | .var ⟨.rigid, i⟩ => if ids.contains i then ([(i, actual)], []) else ([], [])
  | _ => match additiveEndpoint ids pattern actual with
      | some proposal => ([proposal], [])
      | none => ([], selected ids pattern)

mutual
private def collect (ids : List Nat) (pattern actual : BoundsTy) : Option Proposals :=
  match pattern, actual with
  | .bvar _, _ => some ([], [])
  | .prim _, .prim _ | .fvar _, .fvar _ => some ([], [])
  | .arrow a b, .arrow c d => do pure (combine (← collect ids a c) (← collect ids b d))
  | .list lo hi elem, .list actualLo actualHi actualElem => do
      pure (combine (keepUnblocked
        (combine (endpoint ids lo actualLo) (endpoint ids hi actualHi)))
        (← collect ids elem actualElem))
  | .custom n as, .custom m bs => if n = m then collectList ids as bs else none
  | _, _ => none
termination_by sizeOf pattern + sizeOf actual

private def collectList (ids : List Nat) (as bs : List BoundsTy) : Option Proposals :=
  match as, bs with
  | [], [] => some ([], [])
  | a :: as, b :: bs => do pure (combine (← collect ids a b) (← collectList ids as bs))
  | _, _ => none
termination_by sizeOf as + sizeOf bs
end

mutual
private def occurrences (ids : List Nat) : BoundsTy → List Nat
  | .prim _ | .fvar _ | .bvar _ => []
  | .arrow a b => occurrences ids a ++ occurrences ids b
  | .list lo hi elem => selected ids lo ++ selected ids hi ++ occurrences ids elem
  | .custom _ as => occurrencesList ids as
termination_by β => sizeOf β

private def occurrencesList (ids : List Nat) : List BoundsTy → List Nat
  | [] => []
  | a :: as => occurrences ids a ++ occurrencesList ids as
termination_by as => sizeOf as
end

/-- Coordinates in input domains not yet supplied, excluding result-only
    coordinates. These must not be silently fixed to zero by a partial call. -/
private def pending (ids : List Nat) : BoundsTy → List Nat
  | .arrow domain result => occurrences ids domain ++ pending ids result
  | _ => []

private def collectArguments (ids : List Nat) (contract : BoundsTy)
    (actuals : List (Option BoundsTy)) : Option (Proposals × List Nat × List Nat) :=
  match actuals with
  | [] => some (([], []), pending ids contract, [])
  | actual :: rest =>
      match contract with
      | .arrow domain result => do
          let (later, unsupplied, deferred) ← collectArguments ids result rest
          match actual with
          | some β => do
              let here ← collect ids domain β
              pure (combine here later, unsupplied, deferred)
          | none => pure (later, unsupplied, occurrences ids domain ++ deferred)
      | _ => none

/-- Proposal order is the declaration telescope's order, not traversal order.
    Unsupported or ambiguous compound-only occurrences reject instead of guessing an inverse.
    Successful proposals must still pass the certified application checker. -/
def propose (quantified : List Nat) (pattern actual : BoundsTy) : Except String (List Count) := do
  let (uses, blocked) ← match collect quantified pattern actual with
    | none => throw "bounds: unsupported count argument proposal shape"
    | some p => pure p
  quantified.mapM fun id =>
    match CountSubstitution.lookup uses id with
    | some c => pure c
    | none =>
        if blocked.contains id then
          throw "bounds: non-unique count constraint or unsupported arithmetic inversion"
        else pure (.lit 0)

/-- One proposal vector for the whole supplied application spine. Repeated
    coordinates keep their first witness; ALL domains must subsequently pass
    inclusion. A later direct occurrence can supply an unsupported compound
    earlier one. This function establishes no typing fact.
    Missing actuals are deferred checking obligations, NEVER proposal origins.
    Every coordinate in a deferred domain needs an independent actual origin. -/
def proposeOrigins (quantified : List Nat) (contract : BoundsTy)
    (actuals : List (Option BoundsTy)) : Except String (List Count) := do
  let ((uses, blocked), unsupplied, deferred) ← match collectArguments quantified contract actuals with
    | none => throw "bounds: unsupported full-spine count proposal shape or excess arguments"
    | some p => pure p
  quantified.mapM fun id =>
    match CountSubstitution.lookup uses id with
    | some c => pure c
    | none =>
        if unsupplied.contains id then
          throw "bounds: count-polymorphic partial application needs a later argument origin"
        else if deferred.contains id then
          throw "bounds: count argument needs an independent origin before deferred argument checking"
        else if blocked.contains id then
          throw "bounds: non-unique count constraint or unsupported arithmetic inversion"
        else pure (.lit 0)

def proposeArguments (quantified : List Nat) (contract : BoundsTy)
    (actuals : List BoundsTy) : Except String (List Count) :=
  proposeOrigins quantified contract (actuals.map some)

#print axioms propose
#print axioms proposeOrigins
#print axioms proposeArguments

end FHM.Bounds.CountProposal
