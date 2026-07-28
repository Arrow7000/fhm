import FHM.Bounds.Oracle

/-!
# Bounds commit policy — elaborator accept/reject after narrowing

**Status:** P1 API for sign-off.

Uniqueness is **not** part of declarative well-typedness; it is policy here.
`NarrowingEvidence` stores oracle **certificates** (computable); semantic content
via `solve_sound` / `unique_sound` theorems below.
-/

namespace FHM.Bounds

/-- Elaborator decision after narrowing evidence is gathered. -/
inductive Commit where
  /-- Accept auto-commit; `σ` is the witness (caller may apply to bound info later). -/
  | accept (σ : Assign)
  /-- Refuse auto-commit under the current policy. -/
  | reject

/-- Evidence for one solve+unique probe (exclusive cases). -/
inductive NarrowingEvidence (ψ : ExistsProblem) (outs : List Count) where
  /-- No usable witness (`unsat` or `unknown`). -/
  | none
  /-- Witness plus oracle `.unique` on `outs`. -/
  | unique (σ : Assign)
      (hσ : solve ψ = .witness σ)
      (hu : unique ψ outs = .unique)
  /-- Witness without uniqueness. -/
  | some_ (σ : Assign)
      (hσ : solve ψ = .witness σ)

theorem evidence_solvedBy_of_unique {ψ : ExistsProblem} {outs : List Count}
    {σ : Assign} (hσ : solve ψ = .witness σ) (_hu : unique ψ outs = .unique) :
    ψ.SolvedBy σ :=
  solve_sound ψ σ hσ

theorem evidence_uniqueOutputs_of_unique {ψ : ExistsProblem} {outs : List Count}
    {σ : Assign} (_hσ : solve ψ = .witness σ) (hu : unique ψ outs = .unique) :
    ψ.UniqueOutputs outs :=
  unique_sound ψ outs hu

theorem evidence_solvedBy_of_some {ψ : ExistsProblem} {σ : Assign}
    (hσ : solve ψ = .witness σ) :
    ψ.SolvedBy σ :=
  solve_sound ψ σ hσ

theorem evidence_semantic_of_unique {ψ : ExistsProblem} {outs : List Count}
    {σ : Assign} (hσ : solve ψ = .witness σ) (hu : unique ψ outs = .unique) :
    ψ.SolvedBy σ ∧ ψ.UniqueOutputs outs :=
  ⟨evidence_solvedBy_of_unique hσ hu, evidence_uniqueOutputs_of_unique hσ hu⟩

inductive PolicyKind where
  /-- Auto-commit only when oracle reports unique (historical default). -/
  | uniqueOnly
  /-- Auto-commit any solve witness; ignore uniqueness. -/
  | anyWitness
  deriving DecidableEq, Repr

/-- Declarative: which commits each policy allows on each evidence shape. -/
inductive Commits :
    PolicyKind → {ψ : ExistsProblem} → {outs : List Count} →
      NarrowingEvidence ψ outs → Commit → Prop where
  | uniqueOnly_accept {ψ outs σ hσ hu} :
      Commits .uniqueOnly (ψ := ψ) (outs := outs) (.unique σ hσ hu) (.accept σ)
  | uniqueOnly_reject_none {ψ outs} :
      Commits .uniqueOnly (ψ := ψ) (outs := outs) .none .reject
  | uniqueOnly_reject_some {ψ outs σ hσ} :
      Commits .uniqueOnly (ψ := ψ) (outs := outs) (.some_ σ hσ) .reject
  | anyWitness_accept_unique {ψ outs σ hσ hu} :
      Commits .anyWitness (ψ := ψ) (outs := outs) (.unique σ hσ hu) (.accept σ)
  | anyWitness_accept_some {ψ outs σ hσ} :
      Commits .anyWitness (ψ := ψ) (outs := outs) (.some_ σ hσ) (.accept σ)
  | anyWitness_reject_none {ψ outs} :
      Commits .anyWitness (ψ := ψ) (outs := outs) .none .reject

def decideCommit (k : PolicyKind) {ψ : ExistsProblem} {outs : List Count} :
    NarrowingEvidence ψ outs → Commit
  | .none => .reject
  | .unique σ _ _ => .accept σ
  | .some_ σ _ =>
    match k with
    | .uniqueOnly => .reject
    | .anyWitness => .accept σ

abbrev CommitHandler : Type :=
  (ψ : ExistsProblem) → (outs : List Count) → NarrowingEvidence ψ outs → Commit

def CommitHandler.ofKind (k : PolicyKind) : CommitHandler :=
  fun _ψ _outs e => decideCommit k e

theorem decideCommit_sound {k ψ outs} (e : NarrowingEvidence ψ outs) :
    Commits k e (decideCommit k e) := by
  cases k <;> cases e <;> constructor

theorem decideCommit_complete {k ψ outs} (e : NarrowingEvidence ψ outs) {c : Commit}
    (h : Commits k e c) : decideCommit k e = c := by
  cases h <;> rfl

theorem decideCommit_iff {k ψ outs} (e : NarrowingEvidence ψ outs) (c : Commit) :
    Commits k e c ↔ decideCommit k e = c :=
  ⟨decideCommit_complete e, fun h => h ▸ decideCommit_sound e⟩

def gatherNarrowingEvidence (ψ : ExistsProblem) (outs : List Count) :
    NarrowingEvidence ψ outs :=
  match hσ : solve ψ with
  | .unsat | .unknown => .none
  | .witness σ =>
    match hu : unique ψ outs with
    | .unique => .unique σ hσ hu
    | .multiple | .unknown => .some_ σ hσ

/-- Success of force-subtype style narrowing (no Core/toy Ty here). -/
inductive ForceOk where
  | plainSub
  | solved (σ : Assign)

end FHM.Bounds
