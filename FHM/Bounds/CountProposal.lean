import FHM.Bounds.ScopedScheme

/-! # Untrusted direct count proposals from argument bounds

Only selected declaration identities exposed directly at interval endpoints are
proposed. Captured identities are never generalized, HM slots are opaque, and
compound arithmetic is not inverted. Repeated coordinates keep their first
proposal: the consuming checker must validate all remaining obligations.
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

private def endpoint (ids : List Nat) (pattern actual : Count) : Proposals :=
  match pattern with
  | .var ⟨.rigid, i⟩ => if ids.contains i then ([(i, actual)], []) else ([], [])
  | _ => ([], selected ids pattern)

mutual
private def collect (ids : List Nat) (pattern actual : BoundsTy) : Option Proposals :=
  match pattern, actual with
  | .bvar _, _ => some ([], [])
  | .prim _, .prim _ | .fvar _, .fvar _ => some ([], [])
  | .arrow a b, .arrow c d => do pure (combine (← collect ids a c) (← collect ids b d))
  | .list lo hi elem, .list actualLo actualHi actualElem => do
      pure (combine (combine (endpoint ids lo actualLo) (endpoint ids hi actualHi))
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
    (actuals : List BoundsTy) : Option (Proposals × List Nat) :=
  match actuals with
  | [] => some (([], []), pending ids contract)
  | actual :: rest =>
      match contract with
      | .arrow domain result => do
          let here ← collect ids domain actual
          let (later, unsupplied) ← collectArguments ids result rest
          pure (combine here later, unsupplied)
      | _ => none

/-- Proposal order is the declaration telescope's order, not traversal order.
    Compound-only occurrences reject instead of guessing an arithmetic inverse.
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
          throw "bounds: implicit count argument needs unsupported arithmetic inversion"
        else pure (.lit 0)

/-- One proposal vector for the whole supplied application spine. Repeated
    coordinates keep their first witness; ALL domains must subsequently pass
    inclusion. A later direct occurrence can supply a compound earlier one,
    but no arithmetic is inverted. This function establishes no typing fact. -/
def proposeArguments (quantified : List Nat) (contract : BoundsTy)
    (actuals : List BoundsTy) : Except String (List Count) := do
  let ((uses, blocked), unsupplied) ← match collectArguments quantified contract actuals with
    | none => throw "bounds: unsupported full-spine count proposal shape or excess arguments"
    | some p => pure p
  quantified.mapM fun id =>
    match CountSubstitution.lookup uses id with
    | some c => pure c
    | none =>
        if unsupplied.contains id then
          throw "bounds: count-polymorphic partial application needs a later argument origin"
        else if blocked.contains id then
          throw "bounds: implicit count argument needs unsupported arithmetic inversion"
        else pure (.lit 0)

#print axioms propose
#print axioms proposeArguments

end FHM.Bounds.CountProposal
