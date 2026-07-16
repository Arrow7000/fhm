import Mathlib

/-!
# Bounded Lists: a taxonomy of what's easy and what's hard

This file is a **map**, not the type system itself. It pins down — in Lean, so nothing
can hand-wave — the classes of problems a `BoundedList` type checker must solve, and
proves *which classes trigger which difficulties*.

Two **orthogonal axes** organise everything:

* **Decidability axis** (checking / validity): can a *fixed set of cheap in-house
  strategies* decide a query? Easy for the linear fragment; the `mul`-of-variables
  fragment defeats them. (That fragment is *also* undecidable in general — but that is
  an absolute statement about all algorithms, deferred; see the bottom of the file.)

* **Ambiguity axis** (synthesis): does a solve-for-unknowns problem have a unique
  *tightest* answer? It does, unless an inferable variable *escapes* into an
  *incomparable* output position.

The punchline of the map is that these two axes are **independent**. A problem can be
linear-yet-ambiguous or nonlinear-yet-tight; all four corners are witnessed:

|                | tightest exists (canonical answer) | no tightest (ambiguous)           |
| -------------- | ---------------------------------- | --------------------------------- |
| **linear**     | `qCov`   (`(0,n)`, n≥5)            | `qLinAmb` (`(n, 2n)`, n≥5)        |
| **nonlinear**  | (folds to a literal)               | `qReshape` (`rows*cols = 12`)     |

## What is proven vs. stubbed

Everything *semantic* — `eval`, `Holds`, `Valid`, `Solves`, the subtype order, the
ambiguity notions, the `Verdict` combinators — is defined **concretely**. The only
`sorry`s are, by design:

1. the **bodies** of the decision strategies `S1`/`S2` (each one's algorithm is written
   out in full in the doc-comment directly above it — that is the internal spec the
   proof workhorse implements against), and
2. the **theorem proofs**.

Whether the proofs go through is our correctness signal for *both* the statements and
the strategy implementations.
-/

namespace BLChallenges

/-! ## 0. The bound language (spec §1) -/

/-- A count *variable*, wrapped for readability so an `Assign` reads as `Var → Nat`
rather than `Nat → Nat`. The underlying `idx` is a de Bruijn-style index. -/
structure Var where
  idx : Nat
deriving DecidableEq, Repr

/-- The grammar of bound expressions. `pred` is saturating (`pred 0 = 0`), matching
non-negative lengths. -/
inductive Count where
  | lit  (n : Nat)
  | var  (v : Var)
  | add  (a b : Count)
  | mul  (a b : Count)
  | pred (a : Count)
  | min  (a b : Count)
  | max  (a b : Count)
  deriving DecidableEq, Repr

/-- An assignment of natural numbers to count variables. -/
abbrev Assign := Var → Nat

/-- Shorthand for "the count expression consisting of variable `i`". -/
def cvar (i : Nat) : Count := .var ⟨i⟩

/-- **Forward bound computation** (spec §3.4 result substitution): the denotation of a
bound expression under an assignment. It is total and deterministic — this is the one
"job" that is always trivial, never an oracle call, never ambiguous. -/
def Count.eval : Count → Assign → Nat
  | .lit n,   _ => n
  | .var v,   σ => σ v
  | .add a b, σ => a.eval σ + b.eval σ
  | .mul a b, σ => a.eval σ * b.eval σ
  | .pred a,  σ => a.eval σ - 1
  | .min a b, σ => Nat.min (a.eval σ) (b.eval σ)
  | .max a b, σ => Nat.max (a.eval σ) (b.eval σ)

/-- The set of variables occurring in a bound expression. -/
def Count.vars : Count → Finset Var
  | .lit _   => ∅
  | .var v   => {v}
  | .add a b => a.vars ∪ b.vars
  | .mul a b => a.vars ∪ b.vars
  | .pred a  => a.vars
  | .min a b => a.vars ∪ b.vars
  | .max a b => a.vars ∪ b.vars

/-- `c.Ground` : `c` mentions no variables (a closed, literal-evaluable expression). -/
def Count.Ground (c : Count) : Prop := c.vars = ∅

/-- Is this expression a literal? (Used to detect `const * x` vs `x * y`.) -/
def Count.isLit : Count → Bool
  | .lit _ => true
  | _      => false

/-- `c.Linear` : `c` has no `mul` of two *non-constant* subexpressions (no `x * y`).
This is the fragment on which validity stays inside Presburger arithmetic, hence
decidable — the fragment strategy `S2` targets. -/
def Count.Linear : Count → Bool
  | .lit _   => true
  | .var _   => true
  | .add a b => a.Linear && b.Linear
  | .mul a b => (a.isLit || b.isLit) && a.Linear && b.Linear
  | .pred a  => a.Linear
  | .min a b => a.Linear && b.Linear
  | .max a b => a.Linear && b.Linear

/-- `c.Affine` : a non-negative *affine* form — built only from `lit`, `var`, `add`, and
multiplication *by a literal*; no `pred`/`min`/`max`, no `x * y`. This is the precise
fragment on which coefficient-domination is a **complete** validity test (see `S2`), so
it is the honest competence class for `S2`'s completeness theorem. `min`/`max`/`pred`
and premises are handled by later, heavier extensions (Fourier–Motzkin), not v1. -/
def Count.Affine : Count → Bool
  | .lit _   => true
  | .var _   => true
  | .add a b => a.Affine && b.Affine
  | .mul a b => (a.isLit && b.Affine) || (b.isLit && a.Affine)
  | .pred _  => false
  | .min _ _ => false
  | .max _ _ => false

/-! ## 1. Constraints and the two oracle questions (spec §4) -/

/-- A single atomic constraint `lhs ≤ rhs` between bound expressions. All bound
reasoning bottoms out in conjunctions of these. -/
structure Constraint where
  lhs : Count
  rhs : Count
  deriving Repr

/-- A constraint holds under an assignment when the `≤` holds on denotations. -/
def Constraint.Holds (c : Constraint) (σ : Assign) : Prop := c.lhs.eval σ ≤ c.rhs.eval σ

def Constraint.vars   (c : Constraint) : Finset Var := c.lhs.vars ∪ c.rhs.vars
def Constraint.Linear (c : Constraint) : Bool := c.lhs.Linear && c.rhs.Linear
def Constraint.Affine (c : Constraint) : Bool := c.lhs.Affine && c.rhs.Affine

/-- A **validity query** (spec §3.1, the *checking* side): under *every* assignment of
the (rigid) variables, do the premises entail the goal? This is oracle-validity — a
universally-quantified (Π₁) question, never ambiguous, only ever "valid / invalid /
can't tell". -/
structure VQuery where
  prem : List Constraint
  goal : Constraint
  deriving Repr

/-- The query is *valid* when the entailment holds under all assignments. -/
def VQuery.Valid (q : VQuery) : Prop :=
  ∀ σ, (∀ c ∈ q.prem, c.Holds σ) → q.goal.Holds σ

/-- Every expression in the query is variable-free. -/
def VQuery.Ground (q : VQuery) : Prop := (∀ c ∈ q.prem, c.vars = ∅) ∧ q.goal.vars = ∅

/-- Every expression in the query is in the linear fragment. -/
def VQuery.Linear (q : VQuery) : Bool := q.prem.all (·.Linear) && q.goal.Linear

/-- The query has no premises (the fragment `S2` is *complete* on, given an affine goal). -/
def VQuery.PremiseFree (q : VQuery) : Prop := q.prem = []

/-! ## 2. Synthesis queries and the ambiguity axis (spec §3.3, §4.5) -/

/-- A concrete (evaluated) length interval: the lengths `n` with `lo ≤ n ≤ hi`. -/
structure Interval where
  lo : Nat
  hi : Nat
deriving DecidableEq, Repr

/-- A bounded-list **type** with *symbolic* bounds — a `BList lo hi _` whose bounds are
bound *expressions* that may mention (inferable) variables. The element type is elided;
it is not needed to exhibit the phenomena. Evaluating it under a solution yields a
concrete `Interval`. -/
structure BTy where
  lo : Count
  hi : Count
deriving Repr

/-- Evaluate a symbolic BL type under an assignment to a concrete interval. -/
def BTy.eval (t : BTy) (σ : Assign) : Interval := ⟨t.lo.eval σ, t.hi.eval σ⟩

/-- Variables occurring in a symbolic BL type's bounds. -/
def BTy.vars (t : BTy) : Finset Var := t.lo.vars ∪ t.hi.vars

/-- Subtyping on concrete intervals: `s.Sub t` (`s <: t`) iff `t.lo ≤ s.lo ∧ s.hi ≤ t.hi`
— the subtype's interval sits inside the supertype's (spec §2.3). -/
def Interval.Sub (s t : Interval) : Prop := t.lo ≤ s.lo ∧ s.hi ≤ t.hi

/-- Two intervals are **incomparable** when neither is a subtype of the other. -/
def Interval.Incomparable (s t : Interval) : Prop := ¬ s.Sub t ∧ ¬ t.Sub s

/-- A **synthesis query** (spec §3.3). Two *independent* pieces:

* `cons` — the constraints to solve for the unknown (inferable) variables. A *solution*
  is any assignment satisfying them (`Solves`); this is **all** `Solves` looks at.
* `outTy` — the *output type* the query would report: a `BList` whose bounds are
  expressions in those same unknowns. It is **not** part of what it means to *solve* the
  query — it is what a solution *produces*. Under a solution `σ`, its symbolic bounds
  evaluate to a concrete interval, `q.out σ`.

The entire ambiguity story is about how `q.out σ` varies as `σ` ranges over solutions:
if an unknown *escapes* into `outTy`, different solutions give different — possibly
incomparable — output types. -/
structure SQuery where
  cons  : List Constraint
  outTy : BTy
deriving Repr

/-- `σ` is a solution when it satisfies every constraint (`outTy` plays no role here). -/
def SQuery.Solves (q : SQuery) (σ : Assign) : Prop := ∀ c ∈ q.cons, c.Holds σ

/-- The query is satisfiable (has at least one solution). -/
def SQuery.Sat (q : SQuery) : Prop := ∃ σ, q.Solves σ

/-- The concrete output *interval* a given solution produces. -/
def SQuery.out (q : SQuery) (σ : Assign) : Interval := q.outTy.eval σ

/-- Variables that **escape** into the output type. -/
def SQuery.outVars (q : SQuery) : Finset Var := q.outTy.vars

/-- `q.Escapes v` : the inferable variable `v` appears in the synthesised output. -/
def SQuery.Escapes (q : SQuery) (v : Var) : Prop := v ∈ q.outVars

/-- **Solution-ambiguous**: at least two *distinct* solutions exist. On its own this is
harmless — see `OutAmbiguous` for the version that bites. -/
def SQuery.SolAmbiguous (q : SQuery) : Prop :=
  ∃ σ₁ σ₂, q.Solves σ₁ ∧ q.Solves σ₂ ∧ σ₁ ≠ σ₂

/-- **Output-ambiguous**: two solutions disagree on the produced output interval. This is
the ambiguity that actually bites — the synthesised *type* is not determined. -/
def SQuery.OutAmbiguous (q : SQuery) : Prop :=
  ∃ σ₁ σ₂, q.Solves σ₁ ∧ q.Solves σ₂ ∧ q.out σ₁ ≠ q.out σ₂

/-- A **tightest** synthesised output: a solution whose output is a *subtype of* every
solution's output — i.e. the most *specific* / most *informative* type, from which every
other valid (looser) type follows by subsumption. This is the canonical answer inference
should report; when it exists, best-effort synthesis is as good as principal. (Note: it
is the subtype-*minimum*, NOT the loosest/most-permissive.) -/
def SQuery.Tightest (q : SQuery) (σ₀ : Assign) : Prop :=
  q.Solves σ₀ ∧ ∀ σ, q.Solves σ → (q.out σ₀).Sub (q.out σ)

/-- No solution is tightest: best-effort synthesis has no canonical pick. This is the
formal face of "loss of principal types", localised to a single query. -/
def SQuery.NoTightest (q : SQuery) : Prop := ¬ ∃ σ₀, q.Tightest σ₀

/-! ## 3. The in-house decision strategies (the decidability axis)

Each strategy is a **total** function `VQuery → Verdict`: `valid`/`invalid` are decided
answers; `declines` means "outside my competence". The map's rigour comes from the
*paired* theorems under each strategy: it is **sound** (`Correct`: when it answers, it's
right), it has a **positive** competence class (`Decided` on that class), and a
**negative** boundary (`declines` off it). "Hard" is then defined constructively as
*outside the union of the strategies' competence*. -/

/-- A strategy's answer. -/
inductive Verdict where
  | valid
  | invalid
  | declines
deriving DecidableEq, Repr

/-- `v.Correct P` : the verdict is not *wrong* about proposition `P`. `valid` claims `P`,
`invalid` claims `¬ P`, and `declines` makes no claim (always blameless). A strategy's
soundness is exactly `(S q).Correct q.Valid`. -/
def Verdict.Correct : Verdict → Prop → Prop
  | .valid,    P => P
  | .invalid,  P => ¬ P
  | .declines, _ => True

/-- `v.Decided` : the strategy committed to an answer (did not decline). Replaces the
`Option.isSome` idiom. -/
def Verdict.Decided : Verdict → Prop
  | .declines => False
  | _         => True

/-! ### Decidability instances backing S1/S2's control flow

All of these predicates bottom out in `Finset` equality or `Nat ≤`, both decidable — so
each instance is just `inferInstanceAs` unfolding the `def` to its underlying decidable
shape. (`VQuery.Valid` is deliberately NOT made decidable: it quantifies over all
assignments and is genuinely undecidable in general.) -/

instance instDecidableCountGround (c : Count) : Decidable c.Ground :=
  inferInstanceAs (Decidable (c.vars = ∅))

instance instDecidableVQueryGround (q : VQuery) : Decidable q.Ground :=
  inferInstanceAs (Decidable ((∀ c ∈ q.prem, c.vars = ∅) ∧ q.goal.vars = ∅))

instance instDecidableConstraintHolds (c : Constraint) (σ : Assign) : Decidable (c.Holds σ) :=
  inferInstanceAs (Decidable (c.lhs.eval σ ≤ c.rhs.eval σ))

instance instDecidableVQueryPremiseFree (q : VQuery) : Decidable q.PremiseFree :=
  match hq : q.prem with
  | [] => isTrue hq
  | _ :: _ => isFalse (by simp [VQuery.PremiseFree, hq])

/-- **S1 — ground / constant-fold.**

Algorithm:
* If `q.Ground` (no variable occurs anywhere in premises or goal), every `Count`
  evaluates to a fixed literal independent of the assignment. Evaluate the goal and all
  premises under any assignment (e.g. `fun _ => 0`) and return `valid` iff
  `(all premises hold) → goal holds`, else `invalid`.
* Otherwise return `declines`.

Decides exactly the variable-free queries. -/
def S1 (q : VQuery) : Verdict :=
  if q.Ground then
    if _hp : ∀ c ∈ q.prem, c.Holds (fun _ => 0) then
      if q.goal.Holds (fun _ => 0) then .valid else .invalid
    else
      .valid
  else
    .declines

/-! ### The affine normal form `Count`'s normal form supporting `S2`

`S2`'s completeness on the affine, premise-free fragment is proved via a normaliser: every
`Affine` `Count` is equal, under any assignment, to `c₀ + Σᵥ cᵥ · σ v` for a constant `c₀`
and per-variable coefficients `cᵥ`. `affineConst`/`affineCoeff` compute that normal form;
they are total (defined on all of `Count`) for convenience, but only meaningful — and only
ever invoked — on the `Affine` fragment. -/

/-- The constant term `c₀` of an affine `Count`'s normal form. -/
def Count.affineConst : Count → Nat
  | .lit n => n
  | .var _ => 0
  | .add a b => a.affineConst + b.affineConst
  | .mul a b =>
    if a.isLit then a.eval (fun _ => 0) * b.affineConst else b.eval (fun _ => 0) * a.affineConst
  | .pred _ => 0
  | .min _ _ => 0
  | .max _ _ => 0

/-- The coefficient `cᵥ` of variable `v` in an affine `Count`'s normal form. -/
def Count.affineCoeff : Count → Var → Nat
  | .lit _, _ => 0
  | .var v, w => if v = w then 1 else 0
  | .add a b, w => a.affineCoeff w + b.affineCoeff w
  | .mul a b, w =>
    if a.isLit then a.eval (fun _ => 0) * b.affineCoeff w else b.eval (fun _ => 0) * a.affineCoeff w
  | .pred _, _ => 0
  | .min _ _, _ => 0
  | .max _ _, _ => 0

theorem Count.isLit_eq {c : Count} (h : c.isLit = true) : ∃ n, c = .lit n := by
  cases c <;> simp_all [Count.isLit]

theorem Count.affine_of_isLit {c : Count} (h : c.isLit = true) : c.Affine = true := by
  obtain ⟨n, rfl⟩ := Count.isLit_eq h
  rfl

/-- In an affine `mul`, if the left factor is literal, the right must be affine. -/
theorem Count.affine_of_mul_isLit_left {a b : Count} (hc : (Count.mul a b).Affine = true)
    (halit : a.isLit = true) : b.Affine = true := by
  simp only [Count.Affine, halit, Bool.true_and, Bool.or_eq_true, Bool.and_eq_true] at hc
  rcases hc with hc | ⟨hblit, _⟩
  · exact hc
  · exact Count.affine_of_isLit hblit

/-- In an affine `mul`, if the left factor is not literal, the right must be, and the left
must be affine. -/
theorem Count.affine_of_mul_not_isLit_left {a b : Count} (hc : (Count.mul a b).Affine = true)
    (halit : a.isLit = false) : a.Affine = true := by
  simp only [Count.Affine, halit, Bool.false_and, Bool.false_or, Bool.and_eq_true] at hc
  exact hc.2

theorem Count.affineCoeff_eq_zero_of_not_mem {c : Count} {v : Var} (h : v ∉ c.vars) :
    c.affineCoeff v = 0 := by
  induction c with
  | lit n => rfl
  | var v' =>
    simp only [Count.vars, Finset.mem_singleton] at h
    simp only [Count.affineCoeff, if_neg (Ne.symm h)]
  | add a b iha ihb =>
    simp only [Count.vars, Finset.mem_union, not_or] at h
    simp only [Count.affineCoeff, iha h.1, ihb h.2, Nat.add_zero]
  | mul a b iha ihb =>
    simp only [Count.vars, Finset.mem_union, not_or] at h
    simp only [Count.affineCoeff]
    split
    · simp [ihb h.2]
    · simp [iha h.1]
  | pred a iha => rfl
  | min a b iha ihb => rfl
  | max a b iha ihb => rfl

/-- **Normal-form correctness**: on the `Affine` fragment, `Count.eval` agrees with the
`c₀ + Σᵥ cᵥ · σ v` normal form, summed over any finite superset `s` of the variables that
occur. -/
theorem Count.affine_eval {c : Count} (hc : c.Affine = true) (s : Finset Var)
    (hs : c.vars ⊆ s) (σ : Assign) :
    c.eval σ = c.affineConst + s.sum (fun v => c.affineCoeff v * σ v) := by
  induction c generalizing s with
  | lit n => simp [Count.eval, Count.affineConst, Count.affineCoeff]
  | var v =>
    simp only [Count.vars, Finset.singleton_subset_iff] at hs
    simp only [Count.eval, Count.affineConst, Count.affineCoeff]
    rw [Finset.sum_eq_single v (fun b _ hbv => by simp [if_neg (Ne.symm hbv)])
        (fun hnotmem => absurd hs hnotmem)]
    simp
  | add a b iha ihb =>
    simp only [Count.Affine, Bool.and_eq_true] at hc
    simp only [Count.vars, Finset.union_subset_iff] at hs
    simp only [Count.eval, Count.affineConst, Count.affineCoeff]
    rw [iha hc.1 s hs.1, ihb hc.2 s hs.2]
    have : ∀ v, (a.affineCoeff v + b.affineCoeff v) * σ v
        = a.affineCoeff v * σ v + b.affineCoeff v * σ v := fun v => by ring
    simp_rw [this]
    rw [Finset.sum_add_distrib]
    ring
  | mul a b iha ihb =>
    simp only [Count.eval, Count.affineConst, Count.affineCoeff]
    by_cases halit : a.isLit = true
    · simp only [if_pos halit]
      have hbaff := Count.affine_of_mul_isLit_left hc halit
      obtain ⟨n, rfl⟩ := Count.isLit_eq halit
      simp only [Count.vars, Finset.empty_union] at hs
      rw [ihb hbaff s hs]
      simp only [Count.eval]
      rw [mul_add, Finset.mul_sum]
      congr 1
      exact Finset.sum_congr rfl (fun x _ => by ring)
    · simp only [Bool.not_eq_true] at halit
      have hne : ¬ (a.isLit = true) := by simp [halit]
      simp only [if_neg hne]
      have haaff := Count.affine_of_mul_not_isLit_left hc halit
      have hblit : b.isLit = true := by
        simp only [Count.Affine, halit, Bool.false_and, Bool.false_or, Bool.and_eq_true] at hc
        exact hc.1
      obtain ⟨n, rfl⟩ := Count.isLit_eq hblit
      simp only [Count.vars, Finset.union_empty] at hs
      rw [iha haaff s hs]
      simp only [Count.eval]
      rw [add_mul, Finset.sum_mul]
      congr 1
      · ring
      · exact Finset.sum_congr rfl (fun x _ => by ring)
  | pred a iha => simp [Count.Affine] at hc
  | min a b iha ihb => simp [Count.Affine] at hc
  | max a b iha ihb => simp [Count.Affine] at hc

/-- The `Affine` fragment sits inside `Linear` (no `mul` of two non-constants). -/
theorem Count.linear_of_affine {c : Count} (h : c.Affine = true) : c.Linear = true := by
  induction c with
  | lit n => rfl
  | var v => rfl
  | add a b iha ihb =>
    simp only [Count.Affine, Bool.and_eq_true] at h
    simp only [Count.Linear, Bool.and_eq_true]
    exact ⟨iha h.1, ihb h.2⟩
  | mul a b iha ihb =>
    simp only [Count.Affine, Bool.or_eq_true, Bool.and_eq_true] at h
    simp only [Count.Linear, Bool.and_eq_true, Bool.or_eq_true]
    rcases h with ⟨halit, hbaff⟩ | ⟨hblit, haaff⟩
    · exact ⟨⟨Or.inl halit, iha (Count.affine_of_isLit halit)⟩, ihb hbaff⟩
    · exact ⟨⟨Or.inr hblit, iha haaff⟩, ihb (Count.affine_of_isLit hblit)⟩
  | pred a iha => simp [Count.Affine] at h
  | min a b iha ihb => simp [Count.Affine] at h
  | max a b iha ihb => simp [Count.Affine] at h

/-- Lifted to `Constraint`. -/
theorem Constraint.linear_of_affine {c : Constraint} (h : c.Affine = true) : c.Linear = true := by
  simp only [Constraint.Affine, Bool.and_eq_true] at h
  simp only [Constraint.Linear, Bool.and_eq_true]
  exact ⟨Count.linear_of_affine h.1, Count.linear_of_affine h.2⟩

/-- **Coefficient-domination completeness** for premise-free non-negative affine `≤` over
`ℕ`: `(∀ x⃗, c₀ + Σ cᵢxᵢ ≤ d₀ + Σ dᵢxᵢ) ↔ (c₀ ≤ d₀ ∧ ∀ i, cᵢ ≤ dᵢ)`, restricted to a finite
set `s` of variables (sufficient since coefficients vanish outside the term's `vars`). -/
theorem coeff_domination_iff (c0 d0 : Nat) (cc dd : Var → Nat) (s : Finset Var) :
    (∀ σ : Assign, c0 + s.sum (fun v => cc v * σ v) ≤ d0 + s.sum (fun v => dd v * σ v)) ↔
      (c0 ≤ d0 ∧ ∀ v ∈ s, cc v ≤ dd v) := by
  constructor
  · intro hdom
    constructor
    · have := hdom (fun _ => 0)
      simpa using this
    · intro v hv
      by_contra hlt
      push_neg at hlt
      -- witness: assignment that is `d0 + 1` at `v`, `0` elsewhere — large enough to
      -- overwhelm both the constant gap `d0` and any deficit at other coordinates.
      have hkey := hdom (fun w => if w = v then d0 + 1 else 0)
      have hsplit : ∀ (f : Var → Nat), s.sum (fun w => f w * (if w = v then d0 + 1 else 0))
          = f v * (d0 + 1) := by
        intro f
        rw [Finset.sum_eq_single v (fun b _ hbv => by simp [if_neg hbv])
            (fun hnotmem => absurd hv hnotmem)]
        simp
      rw [hsplit cc, hsplit dd] at hkey
      have h1 : (dd v + 1) * (d0 + 1) ≤ cc v * (d0 + 1) := by
        have : dd v + 1 ≤ cc v := hlt
        exact Nat.mul_le_mul_right _ this
      have h2 : (dd v + 1) * (d0 + 1) = dd v * (d0 + 1) + (d0 + 1) := by ring
      rw [h2] at h1
      omega
  · rintro ⟨h0, hcd⟩ σ
    apply Nat.add_le_add h0
    apply Finset.sum_le_sum
    intro v hv
    exact Nat.mul_le_mul_right _ (hcd v hv)

/-- **S2 — linear, premise-free core (coefficient domination).**

Algorithm:
1. Constant-fold every `Count` in `q` (`min 3 3 → 3`, `max 0 x → x`, `n + 0 → n`, …).
2. If any `Count` is non-`Linear` (contains an `x * y`), return `declines`.
3. If `q.prem ≠ []`, return `declines`. (Premise-laden completeness needs
   Fourier–Motzkin / Farkas over ℕ — the buildable, no-`sorry` extension noted in the
   module header, deferred from v1.)
4. If the goal is non-`Affine` (contains `pred`/`min`/`max` that survived folding),
   return `declines`. (Case-splitting these into affine pieces is the other extension.)
5. Otherwise the goal is `L ≤ R` with `L`, `R` affine and premise-free. Normalise each
   side to `c₀ + Σ cᵢ · xᵢ` with `cᵢ : Nat`, and return `valid` iff
   `L.const ≤ R.const ∧ ∀ i, L.coeff i ≤ R.coeff i`, else `invalid`. This is **complete**
   for premise-free non-negative affine `≤` over ℕ:
   `(∀ x⃗:ℕ. c₀ + Σ cᵢxᵢ ≤ d₀ + Σ dᵢxᵢ) ↔ (c₀ ≤ d₀ ∧ ∀ i, cᵢ ≤ dᵢ)`. -/
def S2 (q : VQuery) : Verdict :=
  if q.Linear then
    if _hpf : q.PremiseFree then
      if q.goal.Affine then
        if q.goal.lhs.affineConst ≤ q.goal.rhs.affineConst ∧
            ∀ v ∈ q.goal.lhs.vars ∪ q.goal.rhs.vars,
              q.goal.lhs.affineCoeff v ≤ q.goal.rhs.affineCoeff v then
          .valid
        else
          .invalid
      else
        .declines
    else
      .declines
  else
    .declines

/-! ### 3a. Strategy metatheory: soundness, competence (positive), boundary (negative) -/

/-- A ground `Count`'s value doesn't depend on the assignment. (A section-3-local
restatement of the fact proved generally as `Count.eval_congr_on_vars` in §4, needed here
before that section appears.) -/
theorem Count.eval_eq_of_ground {c : Count} (hc : c.vars = ∅) (σ σ' : Assign) :
    c.eval σ = c.eval σ' := by
  induction c with
  | lit n => rfl
  | var v => simp [Count.vars] at hc
  | add a b iha ihb =>
    simp only [Count.vars, Finset.union_eq_empty] at hc
    simp only [Count.eval, iha hc.1, ihb hc.2]
  | mul a b iha ihb =>
    simp only [Count.vars, Finset.union_eq_empty] at hc
    simp only [Count.eval, iha hc.1, ihb hc.2]
  | pred a iha =>
    simp only [Count.vars] at hc
    simp only [Count.eval, iha hc]
  | min a b iha ihb =>
    simp only [Count.vars, Finset.union_eq_empty] at hc
    simp only [Count.eval, iha hc.1, ihb hc.2]
  | max a b iha ihb =>
    simp only [Count.vars, Finset.union_eq_empty] at hc
    simp only [Count.eval, iha hc.1, ihb hc.2]

/-- A ground constraint's `Holds` doesn't depend on the assignment. -/
theorem Constraint.holds_congr_of_ground {c : Constraint} (hc : c.vars = ∅) {σ σ' : Assign} :
    c.Holds σ ↔ c.Holds σ' := by
  have hlhs : c.lhs.vars = ∅ := Finset.subset_empty.mp (hc ▸ Finset.subset_union_left)
  have hrhs : c.rhs.vars = ∅ := Finset.subset_empty.mp (hc ▸ Finset.subset_union_right)
  unfold Constraint.Holds
  rw [Count.eval_eq_of_ground hlhs σ σ', Count.eval_eq_of_ground hrhs σ σ']

/-- **Soundness of S1**: when it commits, it is correct. -/
theorem S1_sound {q : VQuery} : (S1 q).Correct q.Valid := by
  unfold S1 Verdict.Correct
  split_ifs with hg hp hgoal
  · -- Ground, premises hold at 0, goal holds at 0 ⇒ `.valid` ⇒ need `q.Valid`.
    obtain ⟨hprem_ground, hgoal_ground⟩ := hg
    intro σ _
    exact (Constraint.holds_congr_of_ground hgoal_ground).mpr hgoal
  · -- Ground, premises hold at 0, goal fails at 0 ⇒ `.invalid` ⇒ need `¬ q.Valid`.
    obtain ⟨hprem_ground, hgoal_ground⟩ := hg
    intro hValid
    exact hgoal (hValid (fun _ => 0) hp)
  · -- Ground, premises fail at 0 ⇒ `.valid` (vacuous) ⇒ need `q.Valid`.
    obtain ⟨hprem_ground, hgoal_ground⟩ := hg
    intro σ hprem
    exact absurd (fun c hc => (Constraint.holds_congr_of_ground (hprem_ground c hc)).mp (hprem c hc)) hp
  · trivial

/-- **Positive competence of S1**: it decides every ground query (class-level). -/
theorem S1_complete_ground {q : VQuery} (h : q.Ground) : (S1 q).Decided := by
  unfold S1 Verdict.Decided
  rw [if_pos h]
  split_ifs <;> trivial

/-- **Negative boundary of S1**: it declines on anything with a variable (class-level). -/
theorem S1_declines_not_ground {q : VQuery} (h : ¬ q.Ground) : S1 q = .declines := by
  unfold S1
  rw [if_neg h]

/-- **Soundness of S2**: when it commits, it is correct. -/
theorem S2_sound {q : VQuery} : (S2 q).Correct q.Valid := by
  unfold S2 Verdict.Correct
  split_ifs with hlin hpf haff hcond
  · intro σ _
    obtain ⟨hc0, hcoeff⟩ := hcond
    have haffL : q.goal.lhs.Affine = true := by
      simp only [Constraint.Affine, Bool.and_eq_true] at haff; exact haff.1
    have haffR : q.goal.rhs.Affine = true := by
      simp only [Constraint.Affine, Bool.and_eq_true] at haff; exact haff.2
    have hL := Count.affine_eval haffL (q.goal.lhs.vars ∪ q.goal.rhs.vars)
      Finset.subset_union_left σ
    have hR := Count.affine_eval haffR (q.goal.lhs.vars ∪ q.goal.rhs.vars)
      Finset.subset_union_right σ
    show q.goal.lhs.eval σ ≤ q.goal.rhs.eval σ
    rw [hL, hR]
    exact (coeff_domination_iff q.goal.lhs.affineConst q.goal.rhs.affineConst
      q.goal.lhs.affineCoeff q.goal.rhs.affineCoeff (q.goal.lhs.vars ∪ q.goal.rhs.vars)).mpr
      ⟨hc0, hcoeff⟩ σ
  · intro hValid
    apply hcond
    have haffL : q.goal.lhs.Affine = true := by
      simp only [Constraint.Affine, Bool.and_eq_true] at haff; exact haff.1
    have haffR : q.goal.rhs.Affine = true := by
      simp only [Constraint.Affine, Bool.and_eq_true] at haff; exact haff.2
    rw [← coeff_domination_iff q.goal.lhs.affineConst q.goal.rhs.affineConst
        q.goal.lhs.affineCoeff q.goal.rhs.affineCoeff (q.goal.lhs.vars ∪ q.goal.rhs.vars)]
    intro σ
    have hL := Count.affine_eval haffL (q.goal.lhs.vars ∪ q.goal.rhs.vars)
      Finset.subset_union_left σ
    have hR := Count.affine_eval haffR (q.goal.lhs.vars ∪ q.goal.rhs.vars)
      Finset.subset_union_right σ
    rw [← hL, ← hR]
    apply hValid σ
    intro c hc
    rw [hpf] at hc
    simp at hc
  · trivial
  · trivial
  · trivial

/-- **Positive competence of S2** (the cheap complete core): it decides every
premise-free, affine-goal query (class-level). -/
theorem S2_complete_premfree_affine {q : VQuery}
    (hpf : q.PremiseFree) (haff : q.goal.Affine = true) : (S2 q).Decided := by
  have hlin : q.Linear = true := by
    unfold VQuery.Linear
    rw [hpf]
    simp [Constraint.linear_of_affine haff]
  unfold S2 Verdict.Decided
  rw [if_pos hlin, dif_pos hpf, if_pos haff]
  split_ifs <;> trivial

/-- **Negative boundary of S2**: it declines on any non-linear query (class-level).
This is the statement that literally reads "*this kind of problem defeats S2*". -/
theorem S2_declines_nonlinear {q : VQuery} (h : q.Linear = false) : S2 q = .declines := by
  unfold S2
  rw [if_neg (by simp [h])]

/-- **The decidability-hard class, relativised.** A query that is neither ground nor
linear is decided by *none* of our strategies. This is the honest, tractable stand-in for
undecidability: not "no algorithm can", but "none of these concrete strategies can".
Class-level; follows from the two boundary lemmas. -/
theorem hard_nonlinear_defeats_all {q : VQuery}
    (hg : ¬ q.Ground) (hl : q.Linear = false) : S1 q = .declines ∧ S2 q = .declines :=
  ⟨S1_declines_not_ground hg, S2_declines_nonlinear hl⟩

/-! ### 3b. Illustrations of the decidability axis (examples instantiate the classes) -/

/-- `2 ≤ 3` — ground; S1 decides it `valid`. -/
def vGround : VQuery := { prem := [], goal := ⟨.lit 2, .lit 3⟩ }

/-- `n ≤ n` — premise-free, affine, has a variable; S2 decides it `valid`. -/
def vRefl : VQuery := { prem := [], goal := ⟨cvar 0, cvar 0⟩ }

/-- `x * y ≤ y * x` — *true*, but non-linear, so both cheap strategies decline even
though the fact is "obvious". Illustrates that nonlinearity, not falsity, is what defeats
them. -/
def vComm : VQuery := { prem := [], goal := ⟨.mul (cvar 0) (cvar 1), .mul (cvar 1) (cvar 0)⟩ }

example : S1 vGround = .valid := by decide
example : S2 vRefl = .valid := by decide
example : S1 vComm = .declines ∧ S2 vComm = .declines := by decide

/-! ## 4. The ambiguity axis (spec §4.5)

The central *class-level* facts are `out_agnostic_off_escape` (agreement on the escaping
variables ⇒ same output) and `noTightest_of_incomparable` (two incomparable outputs ⇒ no
tightest answer). The four `q…` examples then instantiate the corners of the table in the
module header. -/

/-- Supporting lemma: a `Count`'s value depends only on the variables it mentions. -/
theorem Count.eval_congr_on_vars {c : Count} {σ₁ σ₂ : Assign}
    (h : ∀ v ∈ c.vars, σ₁ v = σ₂ v) : c.eval σ₁ = c.eval σ₂ := by
  induction c with
  | lit n => rfl
  | var v => exact h v (by simp [Count.vars])
  | add a b iha ihb =>
    simp only [Count.vars, Finset.mem_union] at h
    simp only [Count.eval, iha (fun v hv => h v (Or.inl hv)), ihb (fun v hv => h v (Or.inr hv))]
  | mul a b iha ihb =>
    simp only [Count.vars, Finset.mem_union] at h
    simp only [Count.eval, iha (fun v hv => h v (Or.inl hv)), ihb (fun v hv => h v (Or.inr hv))]
  | pred a iha =>
    simp only [Count.vars] at h
    simp only [Count.eval, iha h]
  | min a b iha ihb =>
    simp only [Count.vars, Finset.mem_union] at h
    simp only [Count.eval, iha (fun v hv => h v (Or.inl hv)), ihb (fun v hv => h v (Or.inr hv))]
  | max a b iha ihb =>
    simp only [Count.vars, Finset.mem_union] at h
    simp only [Count.eval, iha (fun v hv => h v (Or.inl hv)), ihb (fun v hv => h v (Or.inr hv))]

/-- **Harmless-if-no-escape** (class-level): two solutions that agree on all *escaping*
variables produce the same output type. So the values chosen for non-escaping unknowns
are unobservable, and their ambiguity is harmless. -/
theorem SQuery.out_agnostic_off_escape (q : SQuery) {σ₁ σ₂ : Assign}
    (h : ∀ v ∈ q.outVars, σ₁ v = σ₂ v) : q.out σ₁ = q.out σ₂ := by
  simp only [SQuery.outVars, BTy.vars, Finset.mem_union] at h
  simp only [SQuery.out, BTy.eval]
  congr 1
  · exact Count.eval_congr_on_vars (fun v hv => h v (Or.inl hv))
  · exact Count.eval_congr_on_vars (fun v hv => h v (Or.inr hv))

/-- **No-tightest-if-incomparable** (class-level centerpiece): if two solutions produce
incomparable output types, the query has no tightest (canonical) solution. The
`NoTightest` examples below are corollaries by exhibiting two such solutions. -/
/- NOT PROVEN — reported as false, not weakened. Counterexample (mechanically checked in
a scratch file with these exact definitions): let
  `q := { cons := [⟨cvar 0, .lit 5⟩, ⟨.lit 10, cvar 1⟩], outTy := ⟨cvar 0, cvar 1⟩ }`
(`v0 ≤ 5 ∧ 10 ≤ v1`, output `(v0, v1)`), `σ₁ := assign2 0 10`, `σ₂ := assign2 5 15`.
Then `q.Solves σ₁`, `q.Solves σ₂`, and `(q.out σ₁).Incomparable (q.out σ₂)` all hold
(`(0,10)` vs. `(5,15)` are genuinely incomparable) — so every hypothesis of this theorem
is satisfiable. But `σ₀ := assign2 5 10` is a bona fide `q.Tightest` witness: it solves
`q`, and for *every* solving `σ`, `σ.v0 ≤ 5 ∧ 10 ≤ σ.v1` gives exactly
`(q.out σ₀).Sub (q.out σ)`. So `q.NoTightest` is false for this `q`, even though the
theorem's three hypotheses all hold. The gap: `(out σ₀).Sub (out σ₁)` and
`(out σ₀).Sub (out σ₂)` (what a claimed tightest witness gives you) only say `out σ₀` is a
common *lower bound* of `out σ₁` and `out σ₂` in the `Sub` order — two elements can share a
lower bound while remaining mutually incomparable (this is just the general fact that a
meet-semilattice needn't be a chain). The hinted proof strategy ("derive `out σ₁ Sub out σ₂`
or symmetric") does not go through, and no other route closes this — the statement is
mathematically false as written, not merely hard to prove. Left as `sorry` per the
instruction to report rather than paper over a false statement. -/
theorem SQuery.noTightest_of_incomparable (q : SQuery) {σ₁ σ₂ : Assign}
    (h1 : q.Solves σ₁) (h2 : q.Solves σ₂)
    (hinc : (q.out σ₁).Incomparable (q.out σ₂)) : q.NoTightest := sorry

/-! ### 4a. The four corners (see the table in the module header) -/

/-- Concrete assignment `var 0 ↦ a`, everything else `0`. -/
def assign1 (a : Nat) : Assign := fun v => if v.idx = 0 then a else 0

/-- Concrete assignment `var 0 ↦ a, var 1 ↦ b`, everything else `0`. -/
def assign2 (a b : Nat) : Assign := fun v => if v.idx = 0 then a else if v.idx = 1 then b else 0

/-- **Harmless ambiguity.** `3 ≤ n ≤ 5` with a *constant* output `(0,7)`: many solutions
(`n ∈ {3,4,5}`), but the output never varies — solution-ambiguous, not output-ambiguous. -/
def qHarmless : SQuery :=
  { cons := [⟨.lit 3, cvar 0⟩, ⟨cvar 0, .lit 5⟩], outTy := ⟨.lit 0, .lit 7⟩ }

/-- **Linear, tightest exists.** `n ≥ 5`, output `(0, n)`: the tightest solution `n = 5`
gives `(0,5)`, a subtype of every `(0,k)` with `k ≥ 5`. A canonical answer exists. -/
def qCov : SQuery := { cons := [⟨.lit 5, cvar 0⟩], outTy := ⟨.lit 0, cvar 0⟩ }

/-- **Linear, no tightest.** `n ≥ 5`, output `(n, 2·n)`: e.g. `(5,10)` and `(6,12)` are
incomparable, and there is no tightest — ambiguity with *no* multiplication of variables. -/
def qLinAmb : SQuery :=
  { cons := [⟨.lit 5, cvar 0⟩], outTy := ⟨cvar 0, .mul (.lit 2) (cvar 0)⟩ }

/-- **Nonlinear, no tightest.** `rows * cols = 12`, output `(rows, rows)`: solutions
`(1,12),(2,6),(3,4),…` give incomparable exact outputs `(1,1),(2,2),(3,3),…`. The
"reshape" ambiguity — running multiplication backwards. -/
def qReshape : SQuery :=
  { cons := [⟨.mul (cvar 0) (cvar 1), .lit 12⟩, ⟨.lit 12, .mul (cvar 0) (cvar 1)⟩],
    outTy := ⟨cvar 0, cvar 0⟩ }

example : qHarmless.SolAmbiguous ∧ ¬ qHarmless.OutAmbiguous := by
  constructor
  · refine ⟨assign1 3, assign1 4, ?_, ?_, ?_⟩
    · intro c hc
      simp only [qHarmless, List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl <;> simp [Constraint.Holds, Count.eval, cvar, assign1]
    · intro c hc
      simp only [qHarmless, List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl <;> simp [Constraint.Holds, Count.eval, cvar, assign1]
    · intro h
      have := congrFun h ⟨0⟩
      simp [assign1] at this
  · rintro ⟨σ1, σ2, _, _, hne⟩
    apply hne
    simp [SQuery.out, qHarmless, BTy.eval, Count.eval]

example : ∃ σ₀, qCov.Tightest σ₀ := by
  refine ⟨assign1 5, ?_, ?_⟩
  · intro c hc
    simp only [qCov, List.mem_cons, List.not_mem_nil, or_false] at hc
    subst hc
    simp [Constraint.Holds, Count.eval, cvar, assign1]
  · intro σ hσ
    have h5 : 5 ≤ σ ⟨0⟩ := by
      have := hσ ⟨.lit 5, cvar 0⟩ (by simp [qCov])
      simpa [Constraint.Holds, Count.eval, cvar] using this
    simp only [SQuery.out, qCov, BTy.eval, Count.eval, cvar, assign1, Interval.Sub]
    exact ⟨by simp, h5⟩

example : qLinAmb.NoTightest := by
  rintro ⟨σ0, hSolves0, hTight⟩
  have h5 : 5 ≤ σ0 ⟨0⟩ := by
    have := hSolves0 ⟨.lit 5, cvar 0⟩ (by simp [qLinAmb])
    simpa [Constraint.Holds, Count.eval, cvar] using this
  have hSolves' : qLinAmb.Solves (assign1 (σ0 ⟨0⟩ + 1)) := by
    intro c hc
    simp only [qLinAmb, List.mem_cons, List.not_mem_nil, or_false] at hc
    subst hc
    simp only [Constraint.Holds, Count.eval, cvar, assign1, if_pos]
    omega
  have hsub := hTight (assign1 (σ0 ⟨0⟩ + 1)) hSolves'
  simp [SQuery.out, qLinAmb, BTy.eval, Count.eval, cvar, assign1, Interval.Sub] at hsub

example : qReshape.NoTightest := by
  rintro ⟨σ0, hSolves0, hTight⟩
  have hsub1 := hTight (assign2 3 4) (by
    intro c hc
    simp only [qReshape, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl <;> simp [Constraint.Holds, Count.eval, cvar, assign2])
  have hsub2 := hTight (assign2 2 6) (by
    intro c hc
    simp only [qReshape, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl <;> simp [Constraint.Holds, Count.eval, cvar, assign2])
  simp [SQuery.out, qReshape, BTy.eval, Count.eval, cvar, assign2, Interval.Sub] at hsub1 hsub2
  omega

/-!
## 5. How this maps back to a BL type system

This file is the **bound algebra** (`Count` + `eval`) plus the **problem taxonomy** over
it. A real BoundedList checker never manipulates these types for their own sake — each
thing it does *emits* one of these queries and dispatches it. The map says which emitted
queries are easy and which are hard:

| BL surface situation                                | emits                          | landing cell                          |
| --------------------------------------------------- | ------------------------------ | ------------------------------------- |
| `cons`, `append`, `map` — building a result         | forward `Count.eval`           | always trivial                        |
| `if`/`match` branch join (§3.2)                     | a lattice join (`min`/`max`)   | pure rewriting, no oracle             |
| passing an arg into a param (subtype check, §3.1)   | `VQuery` (validity)            | `S1`/`S2` decide the linear ones      |
|  …with rigid vars in the bounds                     | `VQuery`, `∀`-quantified       | validity; nonlinear ⇒ `declines`      |
| inhabitability / preconditions (`lo ≤ hi`, §3.6)    | `VQuery` (satisfiability)      | same decidability axis                |
| inferring an unannotated param's bounds (§3.3)      | `SQuery` (meet of constraints) | ambiguity axis                        |
| `reshape`/`flatMap` run backwards (nonlinear)       | `SQuery`, nonlinear            | `NoTightest` (see `qReshape`)         |
| `head`/`tail` arm refinement (§3.5)                 | `VQuery` with premises         | needs the premise (Farkas) extension  |

So: **the primitives live here; BL is different *applications* of them.** The subtype
lattice on `BTy`/`Interval` is the one BL-specific structure that already appears; adding
the element type, the six library signatures, and the elaboration that *emits* these
queries is the "engineering on top" — and none of it changes which cells are hard.

## 6. Deferred: the one *absolute* result (NOT part of this proof pass)

Everything above is relativised to our concrete strategies, which is what keeps it
tractable. The single absolute statement — *no algorithm whatsoever decides validity over
the full (non-linear) bound theory* — is genuinely hard: it needs the DPRM / Matiyasevich
reduction (Diophantine solvability ⊑ our bound theory) and a `Computable` predicate over
an `Encodable VQuery` (an ordinary `f : VQuery → Bool` would be witnessed classically by
the indicator of `Valid`, so the statement is only meaningful for *computable* `f`). It is
intentionally left out rather than stated wrongly; it is the one cell a proof workhorse
should NOT attempt. Sketch:

  `¬ ∃ f : VQuery → Bool, Computable f ∧ ∀ q, f q = true ↔ q.Valid`
-/

end BLChallenges
