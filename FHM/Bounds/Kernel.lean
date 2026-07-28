/-!
# Bounds kernel — counts, constraints, demand, intervals

**Status:** P1 API for sign-off (not yet wired through BLSketch).

Arithmetic and constraint language shared by the bound layer. No Core/Surface/Ty.
-/

namespace FHM.Bounds

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
  -- TODO(bounds-inf): add `| inf` (unbounded upper/lower as needed). Semantics:
  --   eval inf = none / ⊤ on ℕ∪{∞}; min/max/add absorb as usual; Z3 encode as
  --   unconstrained or a dedicated large sort. Then default list hi can be `.inf`
  --   instead of `.lit 0` (see `defaultBounds` in Typing.lean).
  deriving DecidableEq, Repr

/-- Assignments range over all `Var`s (see `ExistsProblem.SolvedBy` / `agreesOn`). -/
abbrev Assign := Var → Nat

def cvar (kind : VarKind) (i : Nat) : Count := .var ⟨kind, i⟩

@[simp] def Count.eval : Count → Assign → Nat
  | .lit n,   _ => n
  | .var v,   σ => σ v
  | .add a b, σ => a.eval σ + b.eval σ
  | .mul a b, σ => a.eval σ * b.eval σ
  | .pred a,  σ => a.eval σ - 1
  | .min a b, σ => Nat.min (a.eval σ) (b.eval σ)
  | .max a b, σ => Nat.max (a.eval σ) (b.eval σ)

/-- Variable-free count expressions (closed under ops; no `var`). -/
inductive Count.Ground : Count → Prop where
  | lit {n} : Ground (.lit n)
  | add {a b} : Ground a → Ground b → Ground (.add a b)
  | mul {a b} : Ground a → Ground b → Ground (.mul a b)
  | pred {a} : Ground a → Ground (.pred a)
  | min {a b} : Ground a → Ground b → Ground (.min a b)
  | max {a b} : Ground a → Ground b → Ground (.max a b)

@[simp] def Count.isGround : Count → Bool
  | .lit _ => true
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

/-- Evaluate a ground count to a `Nat` (no assignment needed). -/
def Count.fold (c : Count) (h : c.Ground) : Nat :=
  match c with
  | .lit n => n
  | .var _ => False.elim (by cases h)
  | .add a b =>
      a.fold (by cases h; assumption) + b.fold (by cases h; assumption)
  | .mul a b =>
      a.fold (by cases h; assumption) * b.fold (by cases h; assumption)
  | .pred a =>
      a.fold (by cases h; assumption) - 1
  | .min a b =>
      Nat.min (a.fold (by cases h; assumption)) (b.fold (by cases h; assumption))
  | .max a b =>
      Nat.max (a.fold (by cases h; assumption)) (b.fold (by cases h; assumption))

theorem Count.fold_eq_eval {c : Count} (h : c.Ground) (σ : Assign) :
    c.fold h = c.eval σ := by
  induction h with
  | lit => rfl
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

/-- Semantic meaning: `lhs ≤ rhs` under assignment. -/
def Constraint.Holds (c : Constraint) (σ : Assign) : Prop :=
  c.lhs.eval σ ≤ c.rhs.eval σ

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
  | .lit _ => true
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
  · -- `.var inferable` arm
    rename_i i
    simp at h
  · -- `.mul c (var inferable)`
    rename_i c i
    simp at h
  · -- `.mul (var inferable) c`
    rename_i i c
    simp at h
  · -- `.add (var inferable) e`
    rename_i i e
    simp at h
  · -- `.add e (var inferable)`
    rename_i e i
    simp at h
  · -- `.add (.mul c (var inferable)) e`
    rename_i c i e
    simp at h
  · -- `.add (.mul (var inferable) c) e`
    rename_i i c e
    simp at h

@[simp] theorem Count.isDemandOK_of_demandOK {c : Count} (h : Count.DemandOK c) :
    c.isDemandOK = true := by
  induction h with
  | ofRigid h => exact Count.isDemandOK_of_isRigidOnly (Count.isRigidOnly_of_rigidOnly h)
  | infer => rfl
  | scale h => simp [h]
  | scaleComm h =>
    -- Right factor is rigid ⇒ first mul-arm does not match.
    cases h with
    | lit => rfl
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
    -- Left is rigid ⇒ first add-arm does not match; second arm fires.
    cases h with
    | lit => rfl
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
    -- Case on offset so `.add _ (var inferable)` cannot match.
    cases he with
    | lit => simp [hc']
    | var => simp [hc']
    | add ha hb =>
      simp [hc',
        ha, hb]
    | mul ha hb =>
      simp [hc',
        ha, hb]
    | pred ha =>
      simp [hc', ha]
    | min ha hb =>
      simp [hc',
        ha, hb]
    | max ha hb =>
      simp [hc',
        ha, hb]
  | affComm hc he =>
    have hc' := Count.isRigidOnly_of_rigidOnly hc
    have he' := Count.isRigidOnly_of_rigidOnly he
    -- Case so higher-priority add arms cannot match.
    cases hc with
    | lit =>
      cases he with
      | lit => rfl
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
      | var =>
        simp [hca, hcb]
      | add ha hb =>
        simp [hca, hcb,
          ha, hb]
      | mul ha hb =>
        simp [hca, hcb,
          ha, hb]
      | pred ha =>
        simp [hca, hcb,
          ha]
      | min ha hb =>
        simp [hca, hcb,
          ha, hb]
      | max ha hb =>
        simp [hca, hcb,
          ha, hb]
    | mul hca hcb =>
      cases he with
      | lit =>
        simp [hca, hcb]
      | var =>
        simp [hca, hcb]
      | add ha hb =>
        simp [hca, hcb,
          ha, hb]
      | mul ha hb =>
        simp [hca, hcb,
          ha, hb]
      | pred ha =>
        simp [hca, hcb,
          ha]
      | min ha hb =>
        simp [hca, hcb,
          ha, hb]
      | max ha hb =>
        simp [hca, hcb,
          ha, hb]
    | pred hca =>
      cases he with
      | lit =>
        simp [hca]
      | var =>
        simp [hca]
      | add ha hb =>
        simp [hca,
          ha, hb]
      | mul ha hb =>
        simp [hca,
          ha, hb]
      | pred ha =>
        simp [hca,
          ha]
      | min ha hb =>
        simp [hca,
          ha, hb]
      | max ha hb =>
        simp [hca,
          ha, hb]
    | min hca hcb =>
      cases he with
      | lit =>
        simp [hca, hcb]
      | var =>
        simp [hca, hcb]
      | add ha hb =>
        simp [hca, hcb,
          ha, hb]
      | mul ha hb =>
        simp [hca, hcb,
          ha, hb]
      | pred ha =>
        simp [hca, hcb,
          ha]
      | min ha hb =>
        simp [hca, hcb,
          ha, hb]
      | max ha hb =>
        simp [hca, hcb,
          ha, hb]
    | max hca hcb =>
      cases he with
      | lit =>
        simp [hca, hcb]
      | var =>
        simp [hca, hcb]
      | add ha hb =>
        simp [hca, hcb,
          ha, hb]
      | mul ha hb =>
        simp [hca, hcb,
          ha, hb]
      | pred ha =>
        simp [hca, hcb,
          ha]
      | min ha hb =>
        simp [hca, hcb,
          ha, hb]
      | max ha hb =>
        simp [hca, hcb,
          ha, hb]

theorem Count.demandOK_of_isDemandOK {c : Count} (h : c.isDemandOK = true) :
    Count.DemandOK c := by
  induction c with
  | lit => exact .ofRigid .lit
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

/-- Nil branch refine: `lo ≤ 0` and `0 ≤ hi` (hi not forced to 0). -/
def nilRefine (lo hi : Count) : List Constraint :=
  [⟨lo, .lit 0⟩, ⟨.lit 0, hi⟩]

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

end FHM.Bounds
