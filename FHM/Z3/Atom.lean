/-!
# FHM — Z3 atomic-formula layer

First-order arithmetic atoms over `FHM.Z3.Expr`. Adapted from Percissus.Fresh.Z3.
-/

namespace FHM.Z3

/-- Count-like expressions for SMT encoding (names are plain `String`s). -/
inductive Expr where
  | lit  (n : Nat)
  | name (s : String)
  | add  (a b : Expr)
  | mul  (a b : Expr)
  | pred (a : Expr)
  | min  (a b : Expr)
  | max  (a b : Expr)
  deriving Repr, BEq, DecidableEq, Inhabited

abbrev Assignment := String → Nat

namespace Expr

def eval : Expr → Assignment → Nat
  | .lit n,   _ => n
  | .name s,  σ => σ s
  | .add a b, σ => a.eval σ + b.eval σ
  | .mul a b, σ => a.eval σ * b.eval σ
  | .pred a,  σ => a.eval σ - 1  -- truncated on Nat via non-neg constraints in SMT
  | .min a b, σ => Nat.min (a.eval σ) (b.eval σ)
  | .max a b, σ => Nat.max (a.eval σ) (b.eval σ)

def names : Expr → List String
  | .lit _ => []
  | .name s => [s]
  | .add a b => a.names ++ b.names
  | .mul a b => a.names ++ b.names
  | .pred a => a.names
  | .min a b => a.names ++ b.names
  | .max a b => a.names ++ b.names

end Expr

/-- A first-order atom: equality, ≤, or strict < between two expressions. -/
inductive Atom where
  | eq (lhs rhs : Expr)
  | le (lhs rhs : Expr)
  | lt (lhs rhs : Expr)
  deriving Repr, BEq, DecidableEq, Inhabited

namespace Atom

def Holds (σ : Assignment) : Atom → Prop
  | .eq lhs rhs => lhs.eval σ = rhs.eval σ
  | .le lhs rhs => lhs.eval σ ≤ rhs.eval σ
  | .lt lhs rhs => lhs.eval σ < rhs.eval σ

def Always (a : Atom) : Prop :=
  ∀ σ : Assignment, Holds σ a

@[inline] def mkEq (lhs rhs : Expr) : Atom := .eq lhs rhs
@[inline] def mkLe (lhs rhs : Expr) : Atom := .le lhs rhs
@[inline] def mkLt (lhs rhs : Expr) : Atom := .lt lhs rhs

def names : Atom → List String
  | .eq l r => (l.names ++ r.names).eraseDups
  | .le l r => (l.names ++ r.names).eraseDups
  | .lt l r => (l.names ++ r.names).eraseDups

end Atom

abbrev Assumptions := List Atom

namespace Assumptions

def Holds (σ : Assignment) (as : Assumptions) : Prop :=
  ∀ a ∈ as, a.Holds σ

def names (as : Assumptions) : List String :=
  (as.flatMap Atom.names).eraseDups

@[simp] theorem holds_nil (σ : Assignment) :
    Holds σ ([] : Assumptions) := by
  intro a hMem; cases hMem

theorem holds_cons {σ : Assignment} {a : Atom} {rest : Assumptions} :
    Holds σ (a :: rest) ↔ a.Holds σ ∧ Holds σ rest := by
  refine ⟨fun h => ⟨h a (by simp), fun b hb => h b (by simp [hb])⟩, ?_⟩
  rintro ⟨ha, hRest⟩ b hb
  rcases List.mem_cons.mp hb with rfl | hb
  · exact ha
  · exact hRest b hb

end Assumptions

end FHM.Z3
