import FHM.Z3.Atom

/-!
# FHM — Z3 query / verdict types

Adapted from Percissus.Fresh.Z3.
-/

namespace FHM.Z3

inductive Verdict where
  | verified
  | refuted (witness : List (String × Nat))
  | witness (binding : List (String × Nat))
  | unknown (reason : String)
  deriving Repr, BEq, DecidableEq, Inhabited

namespace Verdict

@[inline] def isVerified : Verdict → Bool
  | .verified => true
  | _ => false

@[inline] def isRefuted : Verdict → Bool
  | .refuted _ => true
  | _ => false

@[inline] def isWitness : Verdict → Bool
  | .witness _ => true
  | _ => false

@[inline] def isUnknown : Verdict → Bool
  | .unknown _ => true
  | _ => false

def describe : Verdict → String
  | .verified => "verified"
  | .refuted w => s!"refuted by {reprStr w}"
  | .witness b => s!"witness {reprStr b}"
  | .unknown r => s!"unknown ({r})"

end Verdict

inductive SatVerdict where
  | sat (witness : List (String × Nat))
  | unsat
  | unknown (reason : String)
  deriving Repr, BEq, DecidableEq, Inhabited

namespace SatVerdict

@[inline] def isSat : SatVerdict → Bool
  | .sat _ => true
  | _ => false

@[inline] def isUnsat : SatVerdict → Bool
  | .unsat => true
  | _ => false

@[inline] def isUnknown : SatVerdict → Bool
  | .unknown _ => true
  | _ => false

def describe : SatVerdict → String
  | .sat w => s!"sat with model {reprStr w}"
  | .unsat => "unsat"
  | .unknown r => s!"unknown ({r})"

end SatVerdict

structure Query where
  unknowns    : List String := []
  assumptions : Assumptions := []
  goal        : Atom
  deriving Repr, BEq, Inhabited

namespace Query

@[inline] def alwaysEq
    (lhs rhs : Expr) (assumptions : Assumptions := []) : Query :=
  { unknowns := [], assumptions, goal := .eq lhs rhs }

@[inline] def alwaysLe
    (lhs rhs : Expr) (assumptions : Assumptions := []) : Query :=
  { unknowns := [], assumptions, goal := .le lhs rhs }

@[inline] def findWitness
    (unknowns : List String) (goal : Atom)
    (assumptions : Assumptions := []) : Query :=
  { unknowns, assumptions, goal }

def allNames (q : Query) : List String :=
  let fromAssumptions := q.assumptions.flatMap Atom.names
  let fromGoal := q.goal.names
  (fromAssumptions ++ fromGoal ++ q.unknowns).eraseDups

def universalNames (q : Query) : List String :=
  q.allNames.filter (fun n => !q.unknowns.contains n)

end Query

structure Config where
  timeoutMs : UInt32 := 2000
  deriving Repr, BEq, Inhabited

namespace Config

def default : Config := {}
def patient : Config := { timeoutMs := 8000 }

end Config

end FHM.Z3
