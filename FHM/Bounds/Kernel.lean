/-!
# Bounds kernel — counts, constraints, demand, intervals

Arithmetic and constraint language shared by the bound layer. No Core/Surface/Ty.

## Slice 1 — `ExtNat` + `Count.inf` (API for ✅)

`inf` is **vocabulary** for unbounded counts (analysis result or explicit surface
syntax). **Not** a default stamp on bare `List` (D22).

Counts evaluate in `ExtNat` (ℕ ∪ {∞}). `Constraint.Holds` uses `ExtNat.le`.
Finite programs that never mention `inf` behave as before (`.ofNat` path).

Z3 encoding of `inf`: normalize in Lean to taut/absurd/`FiniteConstraint`
(`Count.NoInf` proofs); only `NoInf` counts reach `countToExpr` (total).
-/

namespace FHM.Bounds

/-! ## Extended naturals (ℕ ∪ {∞}) -/

/-- Semiring-ish top for count evaluation / interval endpoints. -/
inductive ExtNat where
  | ofNat (n : Nat)
  | inf
  deriving DecidableEq, Repr, Inhabited

namespace ExtNat

/-- `a ≤ b` on ℕ∪{∞}: everything ≤ ∞; ∞ ≰ finite. -/
def le : ExtNat → ExtNat → Prop
  | _, .inf => True
  | .inf, .ofNat _ => False
  | .ofNat a, .ofNat b => a ≤ b

def add : ExtNat → ExtNat → ExtNat
  | .inf, _ => .inf
  | _, .inf => .inf
  | .ofNat a, .ofNat b => .ofNat (a + b)

def mul : ExtNat → ExtNat → ExtNat
  | .ofNat 0, _ => .ofNat 0
  | _, .ofNat 0 => .ofNat 0
  | .inf, _ => .inf
  | _, .inf => .inf
  | .ofNat a, .ofNat b => .ofNat (a * b)

/-- Truncated predecessor; `pred ∞ = ∞`. -/
def pred : ExtNat → ExtNat
  | .inf => .inf
  | .ofNat n => .ofNat (n - 1)

def min : ExtNat → ExtNat → ExtNat
  | .inf, b => b
  | a, .inf => a
  | .ofNat a, .ofNat b => .ofNat (Nat.min a b)

def max : ExtNat → ExtNat → ExtNat
  | .inf, _ => .inf
  | _, .inf => .inf
  | .ofNat a, .ofNat b => .ofNat (Nat.max a b)

end ExtNat

/-! ## Variables and counts -/

inductive VarKind where
  | rigid
  | inferable
  deriving DecidableEq, Repr

structure Var where
  kind : VarKind
  idx  : Nat
  deriving DecidableEq, Repr

inductive Count where
  | lit  (n : Nat)
  | var  (v : Var)
  | add  (a b : Count)
  | mul  (a b : Count)
  | pred (a : Count)
  | min  (a b : Count)
  | max  (a b : Count)
  /-- Unbounded count (⊤). Not a List default — see module docstring / D22. -/
  | inf
  deriving DecidableEq, Repr

/-! ## Count slots (BL endpoints)

Shared by Core `Ty.bl` and surface/bounds ascriptions. Same shape as historical
`AnnoCount` / `Surface.CountSlot`.
-/

/-- One endpoint of a bounded list: `_` or a solid count expression. -/
inductive CountSlot where
  | hole
  | solid (c : Count)
  deriving DecidableEq, Repr

instance : Coe Count CountSlot where
  coe := .solid

/-- Assignments range over all `Var`s (see `ExistsProblem.SolvedBy` / `agreesOn`). -/
abbrev Assign := Var → Nat

def cvar (kind : VarKind) (i : Nat) : Count := .var ⟨kind, i⟩

/-- Evaluate a count in ℕ∪{∞}. -/
@[simp] def Count.eval : Count → Assign → ExtNat
  | .lit n,   _ => .ofNat n
  | .var v,   σ => .ofNat (σ v)
  | .inf,     _ => .inf
  | .add a b, σ => ExtNat.add (a.eval σ) (b.eval σ)
  | .mul a b, σ => ExtNat.mul (a.eval σ) (b.eval σ)
  | .pred a,  σ => ExtNat.pred (a.eval σ)
  | .min a b, σ => ExtNat.min (a.eval σ) (b.eval σ)
  | .max a b, σ => ExtNat.max (a.eval σ) (b.eval σ)

/-- Variable-free count expressions (closed under ops; no `var`). Includes `inf`. -/
inductive Count.Ground : Count → Prop where
  | lit {n} : Ground (.lit n)
  | inf : Ground .inf
  | add {a b} : Ground a → Ground b → Ground (.add a b)
  | mul {a b} : Ground a → Ground b → Ground (.mul a b)
  | pred {a} : Ground a → Ground (.pred a)
  | min {a b} : Ground a → Ground b → Ground (.min a b)
  | max {a b} : Ground a → Ground b → Ground (.max a b)

@[simp] def Count.isGround : Count → Bool
  | .lit _ | .inf => true
  | .var _ => false
  | .add a b | .mul a b | .min a b | .max a b => a.isGround && b.isGround
  | .pred a => a.isGround

/-- Executable mirror of `Ground`. -/
@[simp] theorem Count.isGround_of_ground {c : Count} (h : c.Ground) : c.isGround = true := by
  induction h <;> simp [*]

theorem Count.ground_of_isGround {c : Count} (h : c.isGround = true) : c.Ground := by
  induction c with
  | lit n => exact .lit
  | var _ => simp at h
  | inf => exact .inf
  | add a b iha ihb =>
      simp [Bool.and_eq_true] at h
      exact .add (iha h.1) (ihb h.2)
  | mul a b iha ihb =>
      simp [Bool.and_eq_true] at h
      exact .mul (iha h.1) (ihb h.2)
  | pred a ih =>
      simp at h
      exact .pred (ih h)
  | min a b iha ihb =>
      simp [Bool.and_eq_true] at h
      exact .min (iha h.1) (ihb h.2)
  | max a b iha ihb =>
      simp [Bool.and_eq_true] at h
      exact .max (iha h.1) (ihb h.2)

theorem Count.isGround_iff {c : Count} : c.isGround = true ↔ c.Ground :=
  ⟨Count.ground_of_isGround, Count.isGround_of_ground⟩

/-- Evaluate a ground count (no assignment needed). -/
def Count.fold (c : Count) (h : c.Ground) : ExtNat :=
  match c with
  | .lit n => .ofNat n
  | .inf => .inf
  | .var _ => False.elim (by cases h)
  | .add a b =>
      ExtNat.add (a.fold (by cases h; assumption)) (b.fold (by cases h; assumption))
  | .mul a b =>
      ExtNat.mul (a.fold (by cases h; assumption)) (b.fold (by cases h; assumption))
  | .pred a =>
      ExtNat.pred (a.fold (by cases h; assumption))
  | .min a b =>
      ExtNat.min (a.fold (by cases h; assumption)) (b.fold (by cases h; assumption))
  | .max a b =>
      ExtNat.max (a.fold (by cases h; assumption)) (b.fold (by cases h; assumption))

theorem Count.fold_eq_eval {c : Count} (h : c.Ground) (σ : Assign) :
    c.fold h = c.eval σ := by
  induction h with
  | lit => rfl
  | inf => rfl
  | add _ _ iha ihb => simp [Count.fold, iha, ihb]
  | mul _ _ iha ihb => simp [Count.fold, iha, ihb]
  | pred _ ih => simp [Count.fold, ih]
  | min _ _ iha ihb => simp [Count.fold, iha, ihb]
  | max _ _ iha ihb => simp [Count.fold, iha, ihb]

/-! ## Constraints and problems -/

structure Constraint where
  lhs : Count
  rhs : Count
  deriving DecidableEq, Repr

/-- Semantic meaning: `lhs ≤ rhs` under assignment (ℕ∪{∞}). -/
def Constraint.Holds (c : Constraint) (σ : Assign) : Prop :=
  ExtNat.le (c.lhs.eval σ) (c.rhs.eval σ)

structure ForallProblem where
  prem  : List Constraint
  goals : List Constraint
  deriving Repr

/-- Premises imply goals for every assignment. -/
def ForallProblem.Valid (φ : ForallProblem) : Prop :=
  ∀ σ : Assign, (∀ c ∈ φ.prem, c.Holds σ) → (∀ g ∈ φ.goals, g.Holds σ)

structure ExistsProblem where
  inferables : List Var
  prem       : List Constraint := []
  cons       : List Constraint
  deriving Repr

def agreesOn (vs : List Var) (σ τ : Assign) : Prop :=
  ∀ v ∈ vs, σ v = τ v

/-- σ solves ψ if every τ agreeing on inferables that satisfies prem also satisfies cons. -/
def ExistsProblem.SolvedBy (ψ : ExistsProblem) (σ : Assign) : Prop :=
  ∀ τ : Assign, agreesOn ψ.inferables σ τ →
    (∀ c ∈ ψ.prem, c.Holds τ) → (∀ c ∈ ψ.cons, c.Holds τ)

def ExistsProblem.Sat (ψ : ExistsProblem) : Prop :=
  ∃ σ, ψ.SolvedBy σ

def sameOutputs (outs : List Count) (σ τ : Assign) : Prop :=
  outs.map (·.eval σ) = outs.map (·.eval τ)

def ExistsProblem.UniqueOutputs (ψ : ExistsProblem) (outs : List Count) : Prop :=
  ∀ σ τ, ψ.SolvedBy σ → ψ.SolvedBy τ → sameOutputs outs σ τ

theorem ForallProblem.valid_empty_goals (prem : List Constraint) :
    (⟨prem, []⟩ : ForallProblem).Valid := by
  intro σ _ g hg; cases hg

/-! ## DemandOK (syntactic restriction on demanded bounds) -/

inductive Count.RigidOnly : Count → Prop where
  | lit {n} : RigidOnly (.lit n)
  | inf : RigidOnly .inf
  | var {i} : RigidOnly (.var ⟨.rigid, i⟩)
  | add {a b} : RigidOnly a → RigidOnly b → RigidOnly (.add a b)
  | mul {a b} : RigidOnly a → RigidOnly b → RigidOnly (.mul a b)
  | pred {a} : RigidOnly a → RigidOnly (.pred a)
  | min {a b} : RigidOnly a → RigidOnly b → RigidOnly (.min a b)
  | max {a b} : RigidOnly a → RigidOnly b → RigidOnly (.max a b)

/-- At most one inferable, affine, rigid coeffs/offsets. Syntactic, not semantic. -/
inductive Count.DemandOK : Count → Prop where
  | ofRigid {c} : Count.RigidOnly c → DemandOK c
  | infer {i} : DemandOK (.var ⟨.inferable, i⟩)
  | scale {c i} : Count.RigidOnly c → DemandOK (.mul c (.var ⟨.inferable, i⟩))
  | scaleComm {c i} : Count.RigidOnly c → DemandOK (.mul (.var ⟨.inferable, i⟩) c)
  | offset {i e} : Count.RigidOnly e → DemandOK (.add (.var ⟨.inferable, i⟩) e)
  | offsetComm {i e} : Count.RigidOnly e → DemandOK (.add e (.var ⟨.inferable, i⟩))
  | aff {c i e} :
    Count.RigidOnly c → Count.RigidOnly e →
    DemandOK (.add (.mul c (.var ⟨.inferable, i⟩)) e)
  | affComm {c i e} :
    Count.RigidOnly c → Count.RigidOnly e →
    DemandOK (.add (.mul (.var ⟨.inferable, i⟩) c) e)

@[simp] def Count.isRigidOnly : Count → Bool
  | .lit _ | .inf => true
  | .var ⟨.rigid, _⟩ => true
  | .var ⟨.inferable, _⟩ => false
  | .add a b | .mul a b | .min a b | .max a b => a.isRigidOnly && b.isRigidOnly
  | .pred a => a.isRigidOnly

/-- Executable mirror of `DemandOK` (clauses match BLSketch). -/
@[simp] def Count.isDemandOK : Count → Bool
  | .var ⟨.inferable, _⟩ => true
  | .mul c (.var ⟨.inferable, _⟩) => c.isRigidOnly
  | .mul (.var ⟨.inferable, _⟩) c => c.isRigidOnly
  | .add (.var ⟨.inferable, _⟩) e => e.isRigidOnly
  | .add e (.var ⟨.inferable, _⟩) => e.isRigidOnly
  | .add (.mul c (.var ⟨.inferable, _⟩)) e => c.isRigidOnly && e.isRigidOnly
  | .add (.mul (.var ⟨.inferable, _⟩) c) e => c.isRigidOnly && e.isRigidOnly
  | c => c.isRigidOnly

@[simp] theorem Count.isRigidOnly_of_rigidOnly {c : Count} (h : Count.RigidOnly c) :
    c.isRigidOnly = true := by
  induction h with
  | lit => rfl
  | inf => rfl
  | var => rfl
  | add _ _ iha ihb => simp [iha, ihb]
  | mul _ _ iha ihb => simp [iha, ihb]
  | pred _ ih => simp [ih]
  | min _ _ iha ihb => simp [iha, ihb]
  | max _ _ iha ihb => simp [iha, ihb]

theorem Count.rigidOnly_of_isRigidOnly {c : Count} (h : c.isRigidOnly = true) :
    Count.RigidOnly c := by
  induction c with
  | lit => exact .lit
  | inf => exact .inf
  | var v =>
    cases v with | mk kind idx =>
    cases kind with
    | rigid => exact .var
    | inferable => simp at h
  | add a b iha ihb =>
    simp at h
    exact .add (iha h.1) (ihb h.2)
  | mul a b iha ihb =>
    simp at h
    exact .mul (iha h.1) (ihb h.2)
  | pred a ih =>
    simp at h
    exact .pred (ih h)
  | min a b iha ihb =>
    simp at h
    exact .min (iha h.1) (ihb h.2)
  | max a b iha ihb =>
    simp at h
    exact .max (iha h.1) (ihb h.2)

theorem Count.isRigidOnly_iff {c : Count} :
    c.isRigidOnly = true ↔ Count.RigidOnly c :=
  ⟨Count.rigidOnly_of_isRigidOnly, Count.isRigidOnly_of_rigidOnly⟩

/-- Rigid counts never hit a DemandOK special-form arm (those embed an inferable). -/
@[simp] theorem Count.isDemandOK_of_isRigidOnly {c : Count} (h : c.isRigidOnly = true) :
    c.isDemandOK = true := by
  unfold Count.isDemandOK
  split <;> try (exact h)
  · rename_i i
    simp at h
  · rename_i c i
    simp at h
  · rename_i i c
    simp at h
  · rename_i i e
    simp at h
  · rename_i e i
    simp at h
  · rename_i c i e
    simp at h
  · rename_i i c e
    simp at h

@[simp] theorem Count.isDemandOK_of_demandOK {c : Count} (h : Count.DemandOK c) :
    c.isDemandOK = true := by
  induction h with
  | ofRigid h => exact Count.isDemandOK_of_isRigidOnly (Count.isRigidOnly_of_rigidOnly h)
  | infer => rfl
  | scale h => simp [h]
  | scaleComm h =>
    cases h with
    | lit => rfl
    | inf => rfl
    | var => rfl
    | add ha hb =>
      simp [ha, hb]
    | mul ha hb =>
      simp [ha, hb]
    | pred ha =>
      simp [ha]
    | min ha hb =>
      simp [ha, hb]
    | max ha hb =>
      simp [ha, hb]
  | offset h => simp [h]
  | offsetComm h =>
    cases h with
    | lit => rfl
    | inf => rfl
    | var => rfl
    | add ha hb =>
      simp [ha, hb]
    | mul ha hb =>
      simp [ha, hb]
    | pred ha =>
      simp [ha]
    | min ha hb =>
      simp [ha, hb]
    | max ha hb =>
      simp [ha, hb]
  | aff hc he =>
    have hc' := Count.isRigidOnly_of_rigidOnly hc
    cases he with
    | lit => simp [hc']
    | inf => simp [hc']
    | var => simp [hc']
    | add ha hb =>
      simp [hc', ha, hb]
    | mul ha hb =>
      simp [hc', ha, hb]
    | pred ha =>
      simp [hc', ha]
    | min ha hb =>
      simp [hc', ha, hb]
    | max ha hb =>
      simp [hc', ha, hb]
  | affComm hc he =>
    have hc' := Count.isRigidOnly_of_rigidOnly hc
    have he' := Count.isRigidOnly_of_rigidOnly he
    cases hc with
    | lit =>
      cases he with
      | lit => rfl
      | inf => rfl
      | var => rfl
      | add ha hb =>
        simp [ha, hb]
      | mul ha hb =>
        simp [ha, hb]
      | pred ha =>
        simp [ha]
      | min ha hb =>
        simp [ha, hb]
      | max ha hb =>
        simp [ha, hb]
    | inf =>
      cases he with
      | lit => rfl
      | inf => rfl
      | var => rfl
      | add ha hb =>
        simp [ha, hb]
      | mul ha hb =>
        simp [ha, hb]
      | pred ha =>
        simp [ha]
      | min ha hb =>
        simp [ha, hb]
      | max ha hb =>
        simp [ha, hb]
    | var =>
      cases he with
      | lit => rfl
      | inf => rfl
      | var => rfl
      | add ha hb =>
        simp [ha, hb]
      | mul ha hb =>
        simp [ha, hb]
      | pred ha =>
        simp [ha]
      | min ha hb =>
        simp [ha, hb]
      | max ha hb =>
        simp [ha, hb]
    | add hca hcb =>
      cases he with
      | lit =>
        simp [hca, hcb]
      | inf =>
        simp [hca, hcb]
      | var =>
        simp [hca, hcb]
      | add ha hb =>
        simp [hca, hcb, ha, hb]
      | mul ha hb =>
        simp [hca, hcb, ha, hb]
      | pred ha =>
        simp [hca, hcb, ha]
      | min ha hb =>
        simp [hca, hcb, ha, hb]
      | max ha hb =>
        simp [hca, hcb, ha, hb]
    | mul hca hcb =>
      cases he with
      | lit =>
        simp [hca, hcb]
      | inf =>
        simp [hca, hcb]
      | var =>
        simp [hca, hcb]
      | add ha hb =>
        simp [hca, hcb, ha, hb]
      | mul ha hb =>
        simp [hca, hcb, ha, hb]
      | pred ha =>
        simp [hca, hcb, ha]
      | min ha hb =>
        simp [hca, hcb, ha, hb]
      | max ha hb =>
        simp [hca, hcb, ha, hb]
    | pred hca =>
      cases he with
      | lit =>
        simp [hca]
      | inf =>
        simp [hca]
      | var =>
        simp [hca]
      | add ha hb =>
        simp [hca, ha, hb]
      | mul ha hb =>
        simp [hca, ha, hb]
      | pred ha =>
        simp [hca, ha]
      | min ha hb =>
        simp [hca, ha, hb]
      | max ha hb =>
        simp [hca, ha, hb]
    | min hca hcb =>
      cases he with
      | lit =>
        simp [hca, hcb]
      | inf =>
        simp [hca, hcb]
      | var =>
        simp [hca, hcb]
      | add ha hb =>
        simp [hca, hcb, ha, hb]
      | mul ha hb =>
        simp [hca, hcb, ha, hb]
      | pred ha =>
        simp [hca, hcb, ha]
      | min ha hb =>
        simp [hca, hcb, ha, hb]
      | max ha hb =>
        simp [hca, hcb, ha, hb]
    | max hca hcb =>
      cases he with
      | lit =>
        simp [hca, hcb]
      | inf =>
        simp [hca, hcb]
      | var =>
        simp [hca, hcb]
      | add ha hb =>
        simp [hca, hcb, ha, hb]
      | mul ha hb =>
        simp [hca, hcb, ha, hb]
      | pred ha =>
        simp [hca, hcb, ha]
      | min ha hb =>
        simp [hca, hcb, ha, hb]
      | max ha hb =>
        simp [hca, hcb, ha, hb]

theorem Count.demandOK_of_isDemandOK {c : Count} (h : c.isDemandOK = true) :
    Count.DemandOK c := by
  induction c with
  | lit => exact .ofRigid .lit
  | inf => exact .ofRigid .inf
  | var v =>
    cases v with | mk kind idx =>
    cases kind with
    | rigid => exact .ofRigid .var
    | inferable => exact .infer
  | add a b iha ihb =>
    unfold Count.isDemandOK at h
    split at h
    · next i heq => nomatch heq
    · next c i heq => nomatch heq
    · next i c heq => nomatch heq
    · next i e heq =>
      cases heq
      exact .offset (Count.rigidOnly_of_isRigidOnly h)
    · next e i heq =>
      cases heq
      exact .offsetComm (Count.rigidOnly_of_isRigidOnly h)
    · next c i e heq =>
      cases heq
      simp at h
      exact .aff (Count.rigidOnly_of_isRigidOnly h.1) (Count.rigidOnly_of_isRigidOnly h.2)
    · next i c e heq =>
      cases heq
      simp at h
      exact .affComm (Count.rigidOnly_of_isRigidOnly h.1) (Count.rigidOnly_of_isRigidOnly h.2)
    · exact .ofRigid (Count.rigidOnly_of_isRigidOnly h)
  | mul a b iha ihb =>
    unfold Count.isDemandOK at h
    split at h
    · next i heq => nomatch heq
    · next c i heq =>
      cases heq
      exact .scale (Count.rigidOnly_of_isRigidOnly h)
    · next i c heq =>
      cases heq
      exact .scaleComm (Count.rigidOnly_of_isRigidOnly h)
    · next i e heq => nomatch heq
    · next e i heq => nomatch heq
    · next c i e heq => nomatch heq
    · next i c e heq => nomatch heq
    · exact .ofRigid (Count.rigidOnly_of_isRigidOnly h)
  | pred a ih =>
    simp at h
    exact .ofRigid (Count.rigidOnly_of_isRigidOnly h)
  | min a b iha ihb =>
    simp only [Count.isDemandOK] at h
    exact .ofRigid (Count.rigidOnly_of_isRigidOnly h)
  | max a b iha ihb =>
    simp only [Count.isDemandOK] at h
    exact .ofRigid (Count.rigidOnly_of_isRigidOnly h)

theorem Count.isDemandOK_iff {c : Count} :
    c.isDemandOK = true ↔ Count.DemandOK c :=
  ⟨Count.demandOK_of_isDemandOK, Count.isDemandOK_of_demandOK⟩

/-! ## Intervals and path-condition helpers -/

structure Interval where
  lo : Count
  hi : Count
  deriving DecidableEq, Repr

/-- Interval inclusion goals under premises `Δ`: `b.lo ≤ a.lo` and `a.hi ≤ b.hi`. -/
def Interval.subGoals (Δ : List Constraint) (a b : Interval) : ForallProblem where
  prem  := Δ
  goals := [⟨b.lo, a.lo⟩, ⟨a.hi, b.hi⟩]

def Interval.meet (a b : Interval) : Interval :=
  ⟨.max a.lo b.lo, .min a.hi b.hi⟩

/-- Join of bounds (match branches): min lo, max hi. -/
def Interval.join (a b : Interval) : Interval :=
  ⟨.min a.lo b.lo, .max a.hi b.hi⟩

def inhabitProblem (Δ : List Constraint) (i : Interval) : ForallProblem where
  prem  := Δ
  goals := [⟨i.lo, i.hi⟩]

/-- Nil branch refine: `lo ≤ 0` -/
def nilRefine (lo : Count) : List Constraint :=
  [⟨lo, .lit 0⟩]

/-- Cons branch refine: `1 ≤ hi`. -/
def consRefine (hi : Count) : List Constraint :=
  [⟨.lit 1, hi⟩]

/-- `hi ≤ 0` under `Δ` — scrutinee must be empty (nil-only match). -/
def mustBeEmpty (Δ : List Constraint) (hi : Count) : ForallProblem where
  prem  := Δ
  goals := [⟨hi, .lit 0⟩]

/-- `1 ≤ lo` under `Δ` — scrutinee must be non-empty (cons-only match). -/
def mustBeNonempty (Δ : List Constraint) (lo : Count) : ForallProblem where
  prem  := Δ
  goals := [⟨.lit 1, lo⟩]

/-! ## `inf` normalization (before Z3)

Inferables stay finite (`Assign := Var → Nat`). Ground `Count.inf` is simplified
away in Lean; residual constraints must be `inf`-free before `countToExpr`.
-/

/-- Does this count mention `inf` (pre-simplify)? -/
def Count.containsInf : Count → Bool
  | .inf => true
  | .lit _ | .var _ => false
  | .pred a => a.containsInf
  | .add a b | .mul a b | .min a b | .max a b => a.containsInf || b.containsInf

/-- Count expression with no `inf` subterm — safe for Z3 encoding. -/
inductive Count.NoInf : Count → Prop where
  | lit {n} : NoInf (.lit n)
  | var {v} : NoInf (.var v)
  | add {a b} : NoInf a → NoInf b → NoInf (.add a b)
  | mul {a b} : NoInf a → NoInf b → NoInf (.mul a b)
  | pred {a} : NoInf a → NoInf (.pred a)
  | min {a b} : NoInf a → NoInf b → NoInf (.min a b)
  | max {a b} : NoInf a → NoInf b → NoInf (.max a b)

@[simp] def Count.noInf : Count → Bool
  | .inf => false
  | .lit _ | .var _ => true
  | .add a b | .mul a b | .min a b | .max a b => a.noInf && b.noInf
  | .pred a => a.noInf

@[simp] theorem Count.noInf_of_noInf {c : Count} (h : c.NoInf) : c.noInf = true := by
  induction h <;> simp [*]

theorem Count.noInf_of_not_containsInf {c : Count} (h : c.containsInf = false) : c.NoInf := by
  induction c with
  | lit => exact .lit
  | var => exact .var
  | inf => simp [containsInf] at h
  | pred a ih =>
      simp [containsInf] at h
      exact .pred (ih h)
  | add a b iha ihb =>
      simp [containsInf, Bool.or_eq_false_iff] at h
      exact .add (iha h.1) (ihb h.2)
  | mul a b iha ihb =>
      simp [containsInf, Bool.or_eq_false_iff] at h
      exact .mul (iha h.1) (ihb h.2)
  | min a b iha ihb =>
      simp [containsInf, Bool.or_eq_false_iff] at h
      exact .min (iha h.1) (ihb h.2)
  | max a b iha ihb =>
      simp [containsInf, Bool.or_eq_false_iff] at h
      exact .max (iha h.1) (ihb h.2)

theorem Count.noInf_of_isNoInf {c : Count} (h : c.noInf = true) : c.NoInf := by
  induction c with
  | lit => exact .lit
  | var => exact .var
  | inf => simp at h
  | pred a ih =>
      simp at h
      exact .pred (ih h)
  | add a b iha ihb =>
      simp [Bool.and_eq_true] at h
      exact .add (iha h.1) (ihb h.2)
  | mul a b iha ihb =>
      simp [Bool.and_eq_true] at h
      exact .mul (iha h.1) (ihb h.2)
  | min a b iha ihb =>
      simp [Bool.and_eq_true] at h
      exact .min (iha h.1) (ihb h.2)
  | max a b iha ihb =>
      simp [Bool.and_eq_true] at h
      exact .max (iha h.1) (ihb h.2)

theorem Count.noInf_iff {c : Count} : c.noInf = true ↔ c.NoInf :=
  ⟨Count.noInf_of_isNoInf, Count.noInf_of_noInf⟩

theorem Count.noInf_eq_not_containsInf (c : Count) : c.noInf = !c.containsInf := by
  induction c with
  | lit | var | inf => simp [noInf, containsInf]
  | pred a ih => simp [noInf, containsInf, ih]
  | add a b iha ihb | mul a b iha ihb | min a b iha ihb | max a b iha ihb =>
      simp [noInf, containsInf, iha, ihb, Bool.not_or]

/-- Push `inf` through ops and fold ground arithmetic. Used by Oracle normalize
and by display pretty (`Count.pretty*`). Check/Synth leave counts unsimplified
in `bctx` (see memo §12 — pipeline folding is an open design). -/
def Count.simplify : Count → Count
  | .lit n => .lit n
  | .var v => .var v
  | .inf => .inf
  | .pred a =>
      match simplify a with
      | .inf => .inf
      | .lit n => .lit (n - 1)
      | a' => .pred a'
  | .add a b =>
      match simplify a, simplify b with
      | .inf, _ | _, .inf => .inf
      | .lit n, .lit m => .lit (n + m)
      | .lit 0, b' => b'
      | a', .lit 0 => a'
      | a', b' => .add a' b'
  | .mul a b =>
      match simplify a, simplify b with
      | .lit 0, _ | _, .lit 0 => .lit 0
      | .lit 1, b' => b'
      | a', .lit 1 => a'
      | .inf, .lit n | .lit n, .inf => if n = 0 then .lit 0 else .inf
      | .inf, .inf => .inf
      | .inf, b' => .mul .inf b'  -- keep; do not assume b' ≠ 0
      | a', .inf => .mul a' .inf
      | .lit n, .lit m => .lit (n * m)
      | a', b' => .mul a' b'
  | .min a b =>
      match simplify a, simplify b with
      | .inf, b' => b'
      | a', .inf => a'
      | .lit n, .lit m => .lit (Nat.min n m)
      | a', b' => .min a' b'
  | .max a b =>
      match simplify a, simplify b with
      | .inf, _ | _, .inf => .inf
      | .lit n, .lit m => .lit (Nat.max n m)
      | a', b' => .max a' b'

#guard Count.simplify (.add (.lit 0) (.add (.lit 1) (.lit 1))) == .lit 2
#guard Count.simplify (.mul (.add (.lit 1) (.lit 1)) (.add (.lit 0) (.lit 1))) == .lit 2
#guard Count.simplify (.add (.var ⟨.rigid, 0⟩) (.lit 0)) == .var ⟨.rigid, 0⟩

/-- Residual constraint with `NoInf` proofs for Z3 encoding. -/
structure FiniteConstraint where
  c : Constraint
  hl : Count.NoInf c.lhs
  hr : Count.NoInf c.rhs
  deriving Repr

/-- Outcome of simplifying a ≤-constraint for the oracle. -/
inductive ConstraintNorm where
  /-- Holds for every assignment. -/
  | taut
  /-- Holds for no assignment. -/
  | absurd
  /-- Finite `lhs ≤ rhs` (no `inf`); safe for Z3. -/
  | finite (fc : FiniteConstraint)
  /-- Still involves `inf` with vars; do not encode. -/
  | stuck
  deriving Repr

/-- Normalize one constraint. Prefer taut/absurd/finite; `stuck` ⇒ oracle `.unknown`. -/
def Constraint.normalize (c : Constraint) : ConstraintNorm :=
  let lhs := Count.simplify c.lhs
  let rhs := Count.simplify c.rhs
  match rhs with
  | .inf => .taut  -- everything ≤ ∞
  | _ =>
    match lhs with
    | .inf =>
        -- ∞ ≤ rhs: only if rhs simplifies to ∞ (already handled); else rhs finite ⇒ absurd
        if rhs.containsInf then .stuck else .absurd
    | _ =>
        match hl : lhs.containsInf, hr : rhs.containsInf with
        | false, false =>
            .finite ⟨⟨lhs, rhs⟩,
              Count.noInf_of_not_containsInf (by simp [hl]),
              Count.noInf_of_not_containsInf (by simp [hr])⟩
        | _, _ => .stuck

def ConstraintNorm.finiteConstraint? : ConstraintNorm → Option Constraint
  | .finite fc => some fc.c
  | _ => none

/-- Premises + goals after dropping taunts; `none` ⇒ problem is vacuously valid
(absurd premise) or trivially invalid handling is on the goals side. -/
structure ProblemNorm where
  /-- Finite premises (tauts dropped). -/
  prem : List FiniteConstraint := []
  /-- Finite goals (tauts dropped). -/
  goals : List FiniteConstraint := []
  /-- Some constraint still stuck on `inf`. -/
  stuck : Bool := false
  /-- A premise is absurd ⇒ ∀-Valid holds vacuously. -/
  vacuous : Bool := false
  /-- A goal is absurd (and not vacuous) ⇒ invalid if we can confirm. -/
  absurdGoal : Bool := false
  deriving Repr

def normalizeForall (φ : ForallProblem) : ProblemNorm :=
  Id.run do
    let mut prem : List FiniteConstraint := []
    let mut vacuous := false
    let mut stuck := false
    for c in φ.prem do
      match Constraint.normalize c with
      | .taut => pure ()
      | .absurd => vacuous := true
      | .finite fc => prem := prem ++ [fc]
      | .stuck => stuck := true
    let mut goals : List FiniteConstraint := []
    let mut absurdGoal := false
    for g in φ.goals do
      match Constraint.normalize g with
      | .taut => pure ()
      | .absurd => absurdGoal := true
      | .finite fc => goals := goals ++ [fc]
      | .stuck => stuck := true
    pure { prem, goals, stuck, vacuous, absurdGoal }

/-- Exists problems: absurd cons ⇒ unsat; absurd prem is just dropped (never helps). -/
structure ExistsNorm where
  prem : List FiniteConstraint := []
  cons : List FiniteConstraint := []
  stuck : Bool := false
  unsat : Bool := false
  deriving Repr

def normalizeExists (ψ : ExistsProblem) : ExistsNorm :=
  Id.run do
    let mut prem : List FiniteConstraint := []
    let mut cons : List FiniteConstraint := []
    let mut stuck := false
    let mut unsat := false
    for c in ψ.prem do
      match Constraint.normalize c with
      | .taut | .absurd => pure ()  -- absurd prem never holds; drop
      | .finite fc => prem := prem ++ [fc]
      | .stuck => stuck := true
    for c in ψ.cons do
      match Constraint.normalize c with
      | .taut => pure ()
      | .absurd => unsat := true
      | .finite fc => cons := cons ++ [fc]
      | .stuck => stuck := true
    pure { prem, cons, stuck, unsat }

/-! ## Guards (`inf` normalize) -/

def ConstraintNorm.isTaut : ConstraintNorm → Bool
  | .taut => true
  | _ => false

def ConstraintNorm.isAbsurd : ConstraintNorm → Bool
  | .absurd => true
  | _ => false

#guard Count.simplify (.min .inf (.lit 3)) == .lit 3
#guard Count.simplify (.max .inf (.lit 3)) == .inf
#guard Count.simplify (.add .inf (.var ⟨.inferable, 0⟩)) == .inf
#guard (Constraint.normalize ⟨.lit 0, .inf⟩).isTaut
#guard (Constraint.normalize ⟨.inf, .lit 0⟩).isAbsurd
#guard (Constraint.normalize ⟨.lit 0, .lit 5⟩).finiteConstraint? == some ⟨.lit 0, .lit 5⟩
#guard (normalizeForall ⟨[], [⟨.var ⟨.rigid, 0⟩, .inf⟩]⟩).goals.isEmpty
#guard (normalizeForall ⟨[], [⟨.inf, .lit 0⟩]⟩).absurdGoal
#guard (normalizeForall ⟨[⟨.inf, .lit 0⟩], [⟨.lit 0, .lit 1⟩]⟩).vacuous
#guard Count.noInf (.lit 3) && !Count.noInf .inf
#guard decide (Count.noInf (.add (.lit 1) (.var ⟨.rigid, 0⟩)))

end FHM.Bounds
