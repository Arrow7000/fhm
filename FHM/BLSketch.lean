import FHM.Z3.Oracle
import FHM.Z3.Encode

/-!
# Bounded Lists — rigorous toy sketch

Declarative bound layer on top of ordinary HM. Judgment: `TypeOf Δ Γ e τ`.

## Contract

If `TypeOf Δ Γ e τ` is derivable, every bound obligation for this toy language
appears as a premise in that derivation:

| Job | Where it shows up |
| --- | --- |
| **Compare (∀)** | `Sub` / inhabitability → `checkValid` under assumptions `Δ` |
| **Join** | `ifBL`, `matchBL` (both branches `BL`) via `min`/`max`; non-`BL` branches must be equal |
| **Meet inhabitability** | not an `Expr` form — when one value faces several BL demands, discharge `checkValid (inhabitProblem Δ (Interval.meet …))` |
| **Solve + unique outputs** | HM-style narrowing at use/ascription: `annoInfer` / `appInfer` / `letSchemeInfer` via `subtypeProblem` |
| **Demand discipline** | `Count.DemandOK` / `Ty.DemandOK` on demanded types |
| **Bound schemes** | `letScheme` (pack with `Sub` or solve) + `varScheme` (`InstantiatesTo`); bodies are WF (only rigid binders `0..n-1`) |
| **Match refinement** | `matchBL` / `matchNil` / `matchCons` extend `Δ`; single-branch forms need a ∀-proof the other case is impossible (`hi ≤ 0` or `1 ≤ lo`) |
| **Checking** | separate `Check` judgment (synth type + `Sub` / solve+unique); not a `TypeOf` ctor — keeps `TypeOf` syntax-directed |

Oracle answers other than success (`unknown` / `invalid` / `unsat` / `multiple`)
simply yield **no** derivation — policy (annotate / commit / error) is outside
this relation.

**Declarative (like Core `TypeOfHM`):** the relation existentially picks types,
scheme args, and solve witnesses; it does not return a substitution. An
algorithmic checker would invent inferables and compute `σ`.

**Algorithmic layer (§9):** `synth` / `check` thread freshness frontier `Φ`
(as in `InferW`); `AnnoTy` allows `BL _ _` holes filled by `fillHoles`.
`synth_sound` relates synthesis to `TypeOf`; `check_sound` relates checking to `Check`.

**Term binders:** de Bruijn via `Ctx` extension; bodies are already scoped.
**Scheme binders (story A):** flat rigid indices `0..binders-1` in `s.body` only;
no nested scheme-hygiene / LN. Enough for top-level library schemes in the demo.

## Non-goals

`zip` / `take` / `drop` / `splitAt`, value-`Nat` in types, recursion, type-level
`∀`, inferred generalisation algorithm, commit-vs-annotate policy, `unknown` UX,
opsem / preservation, checker completeness.
-/

namespace BLSketch

/-! ## 0. Counts -/

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
  deriving DecidableEq, Repr

/-- Assignments range over all `Var`s (see `ExistsProblem.SolvedBy` / `agreesOn`). -/
abbrev Assign := Var → Nat

def cvar (kind : VarKind) (i : Nat) : Count := .var ⟨kind, i⟩

def Count.eval : Count → Assign → Nat
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

def Count.isGround : Count → Bool
  | .lit _ => true
  | .var _ => false
  | .add a b | .mul a b | .min a b | .max a b => a.isGround && b.isGround
  | .pred a => a.isGround

theorem Count.isGround_of_ground {c : Count} (h : c.Ground) : c.isGround = true := by
  induction h <;> simp [Count.isGround, *]

theorem Count.ground_of_isGround {c : Count} (h : c.isGround = true) : c.Ground := by
  induction c with
  | lit n => exact .lit
  | var _ => simp [Count.isGround] at h
  | add a b iha ihb =>
      simp [Count.isGround, Bool.and_eq_true] at h
      exact .add (iha h.1) (ihb h.2)
  | mul a b iha ihb =>
      simp [Count.isGround, Bool.and_eq_true] at h
      exact .mul (iha h.1) (ihb h.2)
  | pred a ih =>
      simp [Count.isGround] at h
      exact .pred (ih h)
  | min a b iha ihb =>
      simp [Count.isGround, Bool.and_eq_true] at h
      exact .min (iha h.1) (ihb h.2)
  | max a b iha ihb =>
      simp [Count.isGround, Bool.and_eq_true] at h
      exact .max (iha h.1) (ihb h.2)

theorem Count.isGround_iff {c : Count} : c.isGround = true ↔ c.Ground :=
  ⟨Count.ground_of_isGround, Count.isGround_of_ground⟩

instance (c : Count) : Decidable c.Ground :=
  decidable_of_decidable_of_iff (Count.isGround_iff (c := c))

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
  | add _ _ iha ihb => simp [Count.fold, Count.eval, iha, ihb]
  | mul _ _ iha ihb => simp [Count.fold, Count.eval, iha, ihb]
  | pred _ ih => simp [Count.fold, Count.eval, ih]
  | min _ _ iha ihb => simp [Count.fold, Count.eval, iha, ihb]
  | max _ _ iha ihb => simp [Count.fold, Count.eval, iha, ihb]

/-! ## 1. Constraints -/

structure Constraint where
  lhs : Count
  rhs : Count
  deriving DecidableEq, Repr

def Constraint.Holds (c : Constraint) (σ : Assign) : Prop :=
  c.lhs.eval σ ≤ c.rhs.eval σ

structure ForallProblem where
  prem  : List Constraint
  goals : List Constraint
  deriving Repr

def ForallProblem.Valid (φ : ForallProblem) : Prop :=
  ∀ σ : Assign, (∀ c ∈ φ.prem, c.Holds σ) → (∀ g ∈ φ.goals, g.Holds σ)

structure ExistsProblem where
  inferables : List Var
  prem       : List Constraint := []
  cons       : List Constraint
  deriving Repr

def agreesOn (vs : List Var) (σ τ : Assign) : Prop :=
  ∀ v ∈ vs, σ v = τ v

def ExistsProblem.SolvedBy (ψ : ExistsProblem) (σ : Assign) : Prop :=
  ∀ τ : Assign, agreesOn ψ.inferables σ τ →
    (∀ c ∈ ψ.prem, c.Holds τ) → (∀ c ∈ ψ.cons, c.Holds τ)

def ExistsProblem.Sat (ψ : ExistsProblem) : Prop :=
  ∃ σ, ψ.SolvedBy σ

def sameOutputs (outs : List Count) (σ τ : Assign) : Prop :=
  outs.map (·.eval σ) = outs.map (·.eval τ)

def ExistsProblem.UniqueOutputs (ψ : ExistsProblem) (outs : List Count) : Prop :=
  ∀ σ τ, ψ.SolvedBy σ → ψ.SolvedBy τ → sameOutputs outs σ τ

/-! ## 2. DemandOK (syntactic language restriction on demands) -/

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

/-! ## 3. Types, intervals, schemes -/

structure Interval where
  lo : Count
  hi : Count
  deriving DecidableEq, Repr

def Interval.subGoals (Δ : List Constraint) (a b : Interval) : ForallProblem where
  prem  := Δ
  goals := [⟨b.lo, a.lo⟩, ⟨a.hi, b.hi⟩]

def Interval.meet (a b : Interval) : Interval :=
  ⟨.max a.lo b.lo, .min a.hi b.hi⟩

def Interval.join (a b : Interval) : Interval :=
  ⟨.min a.lo b.lo, .max a.hi b.hi⟩

def inhabitProblem (Δ : List Constraint) (i : Interval) : ForallProblem where
  prem  := Δ
  goals := [⟨i.lo, i.hi⟩]

inductive Ty where
  | unit
  | tbind (i : Nat)
  | arrow (dom cod : Ty)
  | bl (lo hi : Count) (elem : Ty)
  deriving DecidableEq, Repr

def Ty.obsBounds : Ty → List Count
  | .unit => []
  | .tbind _ => []
  | .bl lo hi elem => [lo, hi] ++ elem.obsBounds
  | .arrow d c => d.obsBounds ++ c.obsBounds

def Count.inferVars : Count → List Var
  | .lit _ => []
  | .var v => if v.kind = .inferable then [v] else []
  | .add a b => a.inferVars ++ b.inferVars
  | .mul a b => a.inferVars ++ b.inferVars
  | .min a b => a.inferVars ++ b.inferVars
  | .max a b => a.inferVars ++ b.inferVars
  | .pred a => a.inferVars

def Ty.inferVars : Ty → List Var
  | .unit => []
  | .tbind _ => []
  | .bl lo hi elem => lo.inferVars ++ hi.inferVars ++ elem.inferVars
  | .arrow d c => d.inferVars ++ c.inferVars

def Ty.size : Ty → Nat
  | .unit => 1
  | .tbind _ => 1
  | .bl _ _ elem => 1 + elem.size
  | .arrow d c => 1 + d.size + c.size

/-- Types whose count bounds are all `Count.Ground`. -/
inductive Ty.Ground : Ty → Prop where
  | unit : Ground .unit
  | bl {lo hi elem} :
    Count.Ground lo → Count.Ground hi → Ground elem → Ground (.bl lo hi elem)
  | arrow {a b} : Ground a → Ground b → Ground (.arrow a b)

def Ty.isGround : Ty → Bool
  | .unit => true
  | .tbind _ => false
  | .bl lo hi elem => lo.isGround && hi.isGround && elem.isGround
  | .arrow a b => a.isGround && b.isGround

theorem Ty.isGround_of_ground {t : Ty} (h : t.Ground) : t.isGround = true := by
  induction h with
  | unit => rfl
  | bl hlo hhi helem ih =>
    simp [Ty.isGround, Count.isGround_of_ground hlo, Count.isGround_of_ground hhi, ih]
  | arrow _ _ iha ihb => simp [Ty.isGround, iha, ihb]

theorem Ty.ground_of_isGround {t : Ty} (h : t.isGround = true) : t.Ground := by
  induction t with
  | unit => exact .unit
  | tbind i => simp [Ty.isGround] at h
  | bl lo hi elem ih =>
      simp [Ty.isGround, Bool.and_eq_true] at h
      exact .bl (Count.ground_of_isGround h.1.1) (Count.ground_of_isGround h.1.2) (ih h.2)
  | arrow a b iha ihb =>
      simp [Ty.isGround, Bool.and_eq_true] at h
      exact .arrow (iha h.1) (ihb h.2)

theorem Ty.isGround_iff {t : Ty} : t.isGround = true ↔ t.Ground :=
  ⟨Ty.ground_of_isGround, Ty.isGround_of_ground⟩

instance (t : Ty) : Decidable t.Ground :=
  decidable_of_decidable_of_iff (Ty.isGround_iff (t := t))

/-- Fold ground count structure in a type down to literal bounds. -/
def Ty.fold (t : Ty) (h : t.Ground) : Ty :=
  match t with
  | .unit => .unit
  | .tbind i => .tbind i
  | .bl lo hi elem =>
      .bl (.lit (lo.fold (by cases h; assumption)))
        (.lit (hi.fold (by cases h; assumption)))
        (elem.fold (by cases h; assumption))
  | .arrow a b =>
      .arrow (a.fold (by cases h; assumption)) (b.fold (by cases h; assumption))

def subConstraints (ty' ty : Ty) : Option (List Constraint) :=
  match ty', ty with
  | .unit, .unit => some []
  | .tbind i, .tbind i' => if i = i' then some [] else none
  | .bl lo hi elem, .bl lo' hi' elem' =>
      if elem = elem' then some [⟨lo', lo⟩, ⟨hi, hi'⟩] else none
  | .arrow a b, .arrow a' b' =>
      match subConstraints a' a, subConstraints b b' with
      | some cs₁, some cs₂ => some (cs₁ ++ cs₂)
      | _, _ => none
  | _, _ => none
termination_by ty'.size + ty.size
decreasing_by all_goals (simp_wf; simp [Ty.size]; omega)

def subtypeProblem (Δ : List Constraint) (ty' ty : Ty) : Option ExistsProblem :=
  match subConstraints ty' ty with
  | none => none
  | some cs =>
    let vs := ty'.inferVars ++ ty.inferVars
    some {
      inferables := vs.foldl (fun acc v => if v ∈ acc then acc else acc ++ [v]) []
      prem := Δ
      cons := cs
    }

inductive Ty.DemandOK : Ty → Prop where
  | unit : Ty.DemandOK .unit
  | arrow {d c} : Ty.DemandOK d → Ty.DemandOK c → Ty.DemandOK (.arrow d c)
  | bl {lo hi elem} :
    Count.DemandOK lo → Count.DemandOK hi → Ty.DemandOK elem → Ty.DemandOK (.bl lo hi elem)

/-! ### Annotation types — holes only in bound positions

`AnnoTy` mirrors `Ty`, but each BL bound is `Option Count` (`none` = `_`).
Holes become fresh inferables in the algorithm (`fillHoles`), or any `Count`
existentially in declarative `AnnoTy.Elab`.
-/

inductive AnnoTy where
  | unit
  | tbind (i : Nat)
  | arrow (dom cod : AnnoTy)
  | bl (lo hi : Option Count) (elem : Ty)
  deriving DecidableEq, Repr

def AnnoTy.ofTy : Ty → AnnoTy
  | .unit => .unit
  | .tbind i => .tbind i
  | .arrow d c => .arrow (ofTy d) (ofTy c)
  | .bl lo hi elem => .bl (some lo) (some hi) elem

inductive AnnoTy.ElabBound : Option Count → Count → Prop where
  | known {c} : ElabBound (some c) c
  | hole {c} : ElabBound none c

inductive AnnoTy.Elab : AnnoTy → Ty → Prop where
  | unit : Elab .unit .unit
  | tbind {i} : Elab (.tbind i) (.tbind i)
  | arrow {d c d' c'} :
    Elab d d' → Elab c c' → Elab (.arrow d c) (.arrow d' c')
  | bl {lo hi lo' hi' elem} :
    ElabBound lo lo' → ElabBound hi hi' → Elab (.bl lo hi elem) (.bl lo' hi' elem)

/-- Scheme body may mention only **rigid** vars with `idx < binders` (no inferables). -/
def Count.BinderRigid (n : Nat) : Count → Prop
  | .lit _ => True
  | .var ⟨.rigid, i⟩ => i < n
  | .var ⟨.inferable, _⟩ => False
  | .add a b | .mul a b | .min a b | .max a b =>
      Count.BinderRigid n a ∧ Count.BinderRigid n b
  | .pred a => Count.BinderRigid n a

def Ty.BinderRigid (n : Nat) : Ty → Prop
  | .unit => True
  | .tbind _ => False
  | .bl lo hi elem =>
    Count.BinderRigid n lo ∧ Count.BinderRigid n hi ∧ Ty.BinderRigid n elem
  | .arrow d c => Ty.BinderRigid n d ∧ Ty.BinderRigid n c

structure BScheme where
  binders : Nat
  body    : Ty
  deriving DecidableEq, Repr

def BScheme.WF (s : BScheme) : Prop :=
  Ty.BinderRigid s.binders s.body

inductive Count.Subst : List Count → Count → Count → Prop where
  | lit {args n} : Subst args (.lit n) (.lit n)
  | var {args i c} : args[i]? = some c → Subst args (.var ⟨.rigid, i⟩) c
  | add {args a b a' b'} :
    Subst args a a' → Subst args b b' → Subst args (.add a b) (.add a' b')
  | mul {args a b a' b'} :
    Subst args a a' → Subst args b b' → Subst args (.mul a b) (.mul a' b')
  | pred {args a a'} : Subst args a a' → Subst args (.pred a) (.pred a')
  | min {args a b a' b'} :
    Subst args a a' → Subst args b b' → Subst args (.min a b) (.min a' b')
  | max {args a b a' b'} :
    Subst args a a' → Subst args b b' → Subst args (.max a b) (.max a' b')

inductive Ty.Subst : List Count → Ty → Ty → Prop where
  | unit {args} : Subst args .unit .unit
  | tbind {args i} : Subst args (.tbind i) (.tbind i)
  | arrow {args d c d' c'} :
    Subst args d d' → Subst args c c' → Subst args (.arrow d c) (.arrow d' c')
  | bl {args lo hi lo' hi' elem} :
    Count.Subst args lo lo' → Count.Subst args hi hi' →
    Subst args (.bl lo hi elem) (.bl lo' hi' elem)

inductive BScheme.InstantiatesTo : BScheme → List Count → Ty → Prop where
  | intro {s args ty} :
    s.WF →
    args.length = s.binders →
    Ty.Subst args s.body ty →
    InstantiatesTo s args ty

inductive Binding where
  | mono   : Ty → Binding
  | scheme : BScheme → Binding
  deriving Repr

abbrev Ctx := List Binding

/-! ## 4. Expressions -/

inductive Expr where
  | unit
  | nil
  | cons (head tail : Expr)
  | var (idx : Nat) (boundArgs : List Count)
  | lam (paramTy : AnnoTy) (body : Expr)
  | app (fn arg : Expr)
  | if_ (cond thn els : Expr)
  | anno (e : Expr) (ty : AnnoTy)
  | let_ (binding body : Expr)
  | letScheme (s : BScheme) (binding body : Expr)
  /-- Exhaustive match on `BL`. Nil branch under refined `Δ`; cons branch under
  `var 0 = head : Unit`, `var 1 = tail : BL (pred lo) (pred hi)`. -/
  | matchBL (scrut nilBranch consBranch : Expr)
  /-- Nil-only match — allowed when `hi ≤ 0` (list must be empty). -/
  | matchNil (scrut nilBranch : Expr)
  /-- Cons-only match — allowed when `1 ≤ lo` (list must be non-empty). -/
  | matchCons (scrut consBranch : Expr)
  deriving DecidableEq, Repr

/-! ## 5. Oracles (Z3-backed; see `FHM/Z3/` for TCB)

Bridge: `BLSketch.Count` → `FHM.Z3.Expr`, constraints → `Atom.le`.
`checkValid` = ∀ over prem ⇒ goals (UNSAT of negation).
`solve` = ∃∀ over inferables with prem/cons.
`unique` = block-and-recheck on output counts after a witness.
-/

inductive ValidVerdict where
  | valid | invalid | unknown
  deriving DecidableEq, Repr

inductive SolveVerdict where
  | witness (σ : Assign)
  | unsat
  | unknown

inductive UniqueVerdict where
  | unique | multiple | unknown
  deriving DecidableEq, Repr

instance : Inhabited ValidVerdict := ⟨.unknown⟩
instance : Inhabited SolveVerdict := ⟨.unknown⟩
instance : Inhabited UniqueVerdict := ⟨.unknown⟩

namespace Z3Bridge

open FHM.Z3 (Atom Assumptions Config Verdict decide decideGoals)
open FHM.Z3

def varName (v : Var) : String :=
  match v.kind with
  | .rigid     => s!"r_{v.idx}"
  | .inferable => s!"i_{v.idx}"

def countToExpr : Count → FHM.Z3.Expr
  | .lit n   => .lit n
  | .var v   => .name (varName v)
  | .add a b => .add (countToExpr a) (countToExpr b)
  | .mul a b => .mul (countToExpr a) (countToExpr b)
  | .pred a  => .pred (countToExpr a)
  | .min a b => .min (countToExpr a) (countToExpr b)
  | .max a b => .max (countToExpr a) (countToExpr b)

def constraintToAtom (c : Constraint) : Atom :=
  .le (countToExpr c.lhs) (countToExpr c.rhs)

def constraintsToAssumptions (cs : List Constraint) : Assumptions :=
  cs.map constraintToAtom

def inferableNames (vs : List Var) : List String :=
  vs.filter (·.kind = .inferable) |>.map varName |>.eraseDups

def modelToAssign (model : List (String × Nat)) : Assign :=
  fun v =>
    model.find? (fun p => p.1 = varName v) |>.map (·.2) |>.getD 0

def checkValidZ3 (φ : ForallProblem) : ValidVerdict :=
  let as := constraintsToAssumptions φ.prem
  let goals := φ.goals.map constraintToAtom
  if goals.isEmpty then .valid
  else
    let results := goals.map fun g => decide { assumptions := as, goal := g }
    if results.any Verdict.isRefuted then .invalid
    else if results.all Verdict.isVerified then .valid
    else .unknown

def solveZ3 (ψ : ExistsProblem) : SolveVerdict :=
  let unknowns := inferableNames ψ.inferables
  let as := constraintsToAssumptions ψ.prem
  let goals := constraintsToAssumptions ψ.cons
  if unknowns.isEmpty && goals.isEmpty then
    .witness (fun _ => 0)
  else
    match decideGoals unknowns as goals with
    | .witness b => .witness (modelToAssign b)
    | .unknown "z3 reports no witness exists" => .unsat
    | _ => .unknown

/-- After a witness, try to find another solution with a different output value. -/
def uniqueZ3 (ψ : ExistsProblem) (outs : List Count) : UniqueVerdict :=
  match solveZ3 ψ with
  | .unsat => .unknown
  | .unknown => .unknown
  | .witness σ =>
    let vals := outs.map (·.eval σ)
    let unknowns := inferableNames ψ.inferables
    let baseAs := constraintsToAssumptions (ψ.prem ++ ψ.cons)
    let goals := constraintsToAssumptions ψ.cons
    let differs (c : Count) (v : Nat) : List Assumptions :=
      [[.lt (countToExpr c) (.lit v)], [.lt (.lit v) (countToExpr c)]]
    let anyOther :=
      (outs.zip vals).any fun (c, v) =>
        (differs c v).any fun extra =>
          match decideGoals unknowns (baseAs ++ extra) goals with
          | .witness _ => true
          | _ => false
    if anyOther then .multiple else .unique

end Z3Bridge

unsafe def checkValidImpl (φ : ForallProblem) : ValidVerdict :=
  Z3Bridge.checkValidZ3 φ

unsafe def solveImpl (ψ : ExistsProblem) : SolveVerdict :=
  Z3Bridge.solveZ3 ψ

unsafe def uniqueImpl (ψ : ExistsProblem) (outs : List Count) : UniqueVerdict :=
  Z3Bridge.uniqueZ3 ψ outs

/-- Opaque interface for the ∀ oracle. At runtime Lean replaces this with
`checkValidImpl` (`@[implemented_by]`). The `*Impl` helpers are `unsafe`
because they perform IO (spawn `z3`); `opaque` keeps the logical interface
looking pure so proofs can mention `checkValid φ = .valid`. -/
@[implemented_by checkValidImpl]
opaque checkValid : ForallProblem → ValidVerdict

/-- Opaque ∃∀ witness oracle (runtime: `solveImpl`). Returns **one** model if
sat — not an enumeration of all solutions. -/
@[implemented_by solveImpl]
opaque solve : ExistsProblem → SolveVerdict

/-- Opaque uniqueness oracle on chosen outputs (runtime: `uniqueImpl`).
Separate from `solve`: first find a witness, then ask whether those `outs`
are forced across all solutions. -/
@[implemented_by uniqueImpl]
opaque unique (ψ : ExistsProblem) (outs : List Count) : UniqueVerdict

/-- Soundness: only `.valid` is axiomatised (mirrors `decide_verified_sound`). -/
axiom checkValid_sound (φ : ForallProblem) :
    checkValid φ = .valid → φ.Valid

/-- Soundness: only `.witness` is axiomatised (mirrors `decide_witness_sound`). -/
axiom solve_sound (ψ : ExistsProblem) (σ : Assign) :
    solve ψ = .witness σ → ψ.SolvedBy σ

/-- Soundness: only `.unique` is axiomatised. `.multiple` / `.unknown` carry no theorems. -/
axiom unique_sound (ψ : ExistsProblem) (outs : List Count) :
    unique ψ outs = .unique → ψ.UniqueOutputs outs

/-! ## 6. Match refinements on `Δ` -/

/-- Nil branch: list is empty ⇒ `lo ≤ 0`. Upper bound `hi` is **unchanged**
(empty is allowed whenever `lo = 0`, even if `0 < hi`, e.g. `BL 0 5`).
Also `0 ≤ hi` so the observation sits under the upper bound. -/
def nilRefine (lo hi : Count) : List Constraint :=
  [⟨lo, .lit 0⟩, ⟨.lit 0, hi⟩]

/-- Cons branch: list non-empty ⇒ `1 ≤ hi`. Tail length bounds are `pred lo/hi`. -/
def consRefine (hi : Count) : List Constraint :=
  [⟨.lit 1, hi⟩]

/-- `hi ≤ 0` under `Δ` — scrutinee must be empty (nil-only match). -/
def mustBeEmpty (Δ : List Constraint) (hi : Count) : ForallProblem where
  prem  := Δ
  goals := [⟨hi, .lit 0⟩]

/-- `1 ≤ lo` under `Δ` — scrutinee must be non-empty (cons-only match).
(`0 < lo` on `ℕ` is `1 ≤ lo`.) -/
def mustBeNonempty (Δ : List Constraint) (lo : Count) : ForallProblem where
  prem  := Δ
  goals := [⟨.lit 1, lo⟩]

/-- Ctx for a cons branch: `var 0 = head`, `var 1 = tail`. -/
def consCtx (ctx : Ctx) (lo hi : Count) : Ctx :=
  .mono .unit :: .mono (.bl (.pred lo) (.pred hi) .unit) :: ctx

/-! ## 7. `Sub` and `TypeOf` -/

inductive Sub (Δ : List Constraint) : Ty → Ty → Prop where
  | unit :
    Sub Δ .unit .unit
  | arrow {a a' b b'} :
    Sub Δ a' a →
    Sub Δ b b' →
    Sub Δ (.arrow a b) (.arrow a' b')
  | tbind {i} :
    Sub Δ (.tbind i) (.tbind i)
  | bl {lo hi lo' hi' elem} :
    Count.DemandOK lo' →
    Count.DemandOK hi' →
    checkValid (Interval.subGoals Δ ⟨lo, hi⟩ ⟨lo', hi'⟩) = .valid →
    Sub Δ (.bl lo hi elem) (.bl lo' hi' elem)
  | bl_refl {lo hi elem} :
    Count.DemandOK lo →
    Count.DemandOK hi →
    Sub Δ (.bl lo hi elem) (.bl lo hi elem)

inductive TypeOf : List Constraint → Ctx → Expr → Ty → Prop where
  | unit {Δ ctx} :
    TypeOf Δ ctx .unit .unit

  | nil {Δ ctx} :
    TypeOf Δ ctx .nil (.bl (.lit 0) (.lit 0) .unit)

  | cons {Δ ctx head tail lo hi elem} :
    TypeOf Δ ctx head .unit →
    TypeOf Δ ctx tail (.bl lo hi elem) →
    TypeOf Δ ctx (.cons head tail) (.bl (.add lo (.lit 1)) (.add hi (.lit 1)) elem)

  | varMono {Δ ctx i ty} :
    ctx[i]? = some (.mono ty) →
    TypeOf Δ ctx (.var i []) ty

  | varScheme {Δ ctx i s args ty} :
    ctx[i]? = some (.scheme s) →
    s.InstantiatesTo args ty →
    TypeOf Δ ctx (.var i args) ty

  | lam {Δ ctx paramAnn paramTy body bodyTy} :
    AnnoTy.Elab paramAnn paramTy →
    Ty.DemandOK paramTy →
    TypeOf Δ (.mono paramTy :: ctx) body bodyTy →
    TypeOf Δ ctx (.lam paramAnn body) (.arrow paramTy bodyTy)

  | app {Δ ctx f arg argTy retTy argTy'} :
    TypeOf Δ ctx f (.arrow argTy retTy) →
    TypeOf Δ ctx arg argTy' →
    Sub Δ argTy' argTy →
    TypeOf Δ ctx (.app f arg) retTy

  /-- HM-style narrowing at the call site (mirror of `annoInfer`). -/
  | appInfer {Δ ctx f arg argTy retTy argTy' ψ σ} :
    TypeOf Δ ctx f (.arrow argTy retTy) →
    TypeOf Δ ctx arg argTy' →
    Ty.DemandOK argTy →
    subtypeProblem Δ argTy' argTy = some ψ →
    solve ψ = .witness σ →
    unique ψ argTy'.obsBounds = .unique →
    TypeOf Δ ctx (.app f arg) retTy

  | ifBL {Δ ctx cond thn els lo₁ hi₁ lo₂ hi₂ elem} :
    TypeOf Δ ctx cond .unit →
    TypeOf Δ ctx thn (.bl lo₁ hi₁ elem) →
    TypeOf Δ ctx els (.bl lo₂ hi₂ elem) →
    TypeOf Δ ctx (.if_ cond thn els) (.bl (.min lo₁ lo₂) (.max hi₁ hi₂) elem)

  | anno {Δ ctx e ann ty ty'} :
    AnnoTy.Elab ann ty →
    TypeOf Δ ctx e ty' →
    Sub Δ ty' ty →
    TypeOf Δ ctx (.anno e ann) ty

  | annoInfer {Δ ctx e ann ty ty' ψ σ} :
    AnnoTy.Elab ann ty →
    TypeOf Δ ctx e ty' →
    Ty.DemandOK ty →
    subtypeProblem Δ ty' ty = some ψ →
    solve ψ = .witness σ →
    unique ψ ty'.obsBounds = .unique →
    TypeOf Δ ctx (.anno e ann) ty

  | letMono {Δ ctx e1 e2 ty1 ty2} :
    TypeOf Δ ctx e1 ty1 →
    TypeOf Δ (.mono ty1 :: ctx) e2 ty2 →
    TypeOf Δ ctx (.let_ e1 e2) ty2

  /-- Pack: bind may be a subtype of the scheme body (wider annotation OK). -/
  | letScheme {Δ ctx s e1 e2 ty1 bodyTy} :
    s.WF →
    TypeOf Δ ctx e1 ty1 →
    Sub Δ ty1 s.body →
    TypeOf Δ (.scheme s :: ctx) e2 bodyTy →
    TypeOf Δ ctx (.letScheme s e1 e2) bodyTy

  /-- Pack with HM-style hole narrowing (mirror of `annoInfer`). -/
  | letSchemeInfer {Δ ctx s e1 e2 ty1 bodyTy ψ σ} :
    s.WF →
    TypeOf Δ ctx e1 ty1 →
    Ty.DemandOK s.body →
    subtypeProblem Δ ty1 s.body = some ψ →
    solve ψ = .witness σ →
    unique ψ ty1.obsBounds = .unique →
    TypeOf Δ (.scheme s :: ctx) e2 bodyTy →
    TypeOf Δ ctx (.letScheme s e1 e2) bodyTy

  /-- Exhaustive match, equal branch types (non-`BL`, or identical `BL`s).
  * nil: `Δ ++ nilRefine lo hi` (`lo ≤ 0`; `hi` not forced to `0`)
  * cons: `Δ ++ consRefine hi`; `consCtx` binds head / tail -/
  | matchBL {Δ ctx e eNil eCons lo hi ty} :
    TypeOf Δ ctx e (.bl lo hi .unit) →
    TypeOf (Δ ++ nilRefine lo hi) ctx eNil ty →
    TypeOf (Δ ++ consRefine hi) (consCtx ctx lo hi) eCons ty →
    TypeOf Δ ctx (.matchBL e eNil eCons) ty

  /-- Exhaustive match: both branches `BL` → join bounds.
  Phase A: scrutinee is Unit-hardwired (matches `synth` / `consCtx`); branch elem is free. -/
  | matchBL_join {Δ ctx e eNil eCons lo hi lo₁ hi₁ lo₂ hi₂ elem} :
    TypeOf Δ ctx e (.bl lo hi .unit) →
    TypeOf (Δ ++ nilRefine lo hi) ctx eNil (.bl lo₁ hi₁ elem) →
    TypeOf (Δ ++ consRefine hi) (consCtx ctx lo hi) eCons (.bl lo₂ hi₂ elem) →
    TypeOf Δ ctx (.matchBL e eNil eCons)
      (.bl (.min lo₁ lo₂) (.max hi₁ hi₂) elem)

  /-- Nil-only: require `hi ≤ 0` under `Δ` (empty is forced). -/
  | matchNil {Δ ctx e eNil lo hi ty} :
    TypeOf Δ ctx e (.bl lo hi .unit) →
    checkValid (mustBeEmpty Δ hi) = .valid →
    TypeOf (Δ ++ nilRefine lo hi) ctx eNil ty →
    TypeOf Δ ctx (.matchNil e eNil) ty

  /-- Cons-only: require `1 ≤ lo` under `Δ` (non-empty is forced). -/
  | matchCons {Δ ctx e eCons lo hi ty} :
    TypeOf Δ ctx e (.bl lo hi .unit) →
    checkValid (mustBeNonempty Δ lo) = .valid →
    TypeOf (Δ ++ consRefine hi) (consCtx ctx lo hi) eCons ty →
    TypeOf Δ ctx (.matchCons e eCons) ty

/-- Checking judgment: synthesized type fits a demand (plain `Sub` or solve+unique).
Keeps `TypeOf` syntax-directed — no general subsumption inside `TypeOf`. -/
inductive Check (Δ : List Constraint) (ctx : Ctx) : Expr → Ty → Prop where
  | ofSub {e ty ty'} :
    TypeOf Δ ctx e ty' →
    Sub Δ ty' ty →
    Check Δ ctx e ty
  | ofInfer {e ty ty' ψ σ} :
    TypeOf Δ ctx e ty' →
    Ty.DemandOK ty →
    subtypeProblem Δ ty' ty = some ψ →
    solve ψ = .witness σ →
    unique ψ ty'.obsBounds = .unique →
    Check Δ ctx e ty

/-! ## 8. Structural lemmas -/

/-- `Count.Subst` is deterministic. -/
theorem Count.Subst.unique {args c c₁ c₂}
    (h₁ : Count.Subst args c c₁) (h₂ : Count.Subst args c c₂) : c₁ = c₂ := by
  induction h₁ with
  | lit =>
    cases h₂
    rfl
  | var h₁ =>
    cases h₂ with | var h₂ =>
    exact Option.some.inj (h₁.symm.trans h₂)
  | add ha hb =>
    cases h₂ with | add ha' hb' =>
    congr 1
    · exact (Count.Subst.unique ha ha')
    · exact (Count.Subst.unique hb hb')
  | mul ha hb =>
    cases h₂ with | mul ha' hb' =>
    congr 1
    · exact (Count.Subst.unique ha ha')
    · exact (Count.Subst.unique hb hb')
  | pred ha =>
    cases h₂ with | pred ha' =>
    congr 1
    exact (Count.Subst.unique ha ha')
  | min ha hb =>
    cases h₂ with | min ha' hb' =>
    congr 1
    · exact (Count.Subst.unique ha ha')
    · exact (Count.Subst.unique hb hb')
  | max ha hb =>
    cases h₂ with | max ha' hb' =>
    congr 1
    · exact (Count.Subst.unique ha ha')
    · exact (Count.Subst.unique hb hb')

/-- `Ty.Subst` is deterministic. -/
theorem Ty.Subst.unique {args t t₁ t₂}
    (h₁ : Ty.Subst args t t₁) (h₂ : Ty.Subst args t t₂) : t₁ = t₂ := by
  induction h₁ with
  | unit =>
    cases h₂
    rfl
  | tbind =>
    cases h₂
    rfl
  | arrow hd hc =>
    cases h₂ with | arrow hd' hc' =>
    congr 1
    · exact (Ty.Subst.unique hd hd')
    · exact (Ty.Subst.unique hc hc')
  | bl hlo hhi =>
    cases h₂ with | bl hlo' hhi' =>
    congr 1
    · exact (Count.Subst.unique hlo hlo')
    · exact (Count.Subst.unique hhi hhi')

/-- Instantiation yields at most one type for a given scheme and args. -/
theorem BScheme.InstantiatesTo.unique {s : BScheme} {args ty₁ ty₂}
    (h₁ : s.InstantiatesTo args ty₁) (h₂ : s.InstantiatesTo args ty₂) :
    ty₁ = ty₂ := by
  cases h₁ with | intro _ _ h₁ =>
  cases h₂ with | intro _ _ h₂ =>
  exact (Ty.Subst.unique h₁ h₂)

private theorem ctx_getElem?_append_left {ctx ctx' : Ctx} {i : Nat} {b : Binding}
    (h : ctx[i]? = some b) : (ctx ++ ctx')[i]? = some b := by
  obtain ⟨hi, rfl⟩ := List.getElem?_eq_some_iff.1 h
  rw [List.getElem?_append_left hi, h]

private theorem consCtx_append (ctx ctx' : Ctx) (lo hi : Count) :
    consCtx (ctx ++ ctx') lo hi = consCtx ctx lo hi ++ ctx' := by
  simp [consCtx, List.cons_append]

/-- Context weakening by appending unused bindings at the **end**
(de Bruijn indices in `e` unchanged). -/
theorem TypeOf.weakenCtx {Δ ctx ctx' e ty}
    (h : TypeOf Δ ctx e ty) : TypeOf Δ (ctx ++ ctx') e ty := by
  induction h with
  | unit => exact .unit
  | nil => exact .nil
  | cons hhead htail ih₁ ih₂ => exact .cons ih₁ ih₂
  | varMono h => exact .varMono (ctx_getElem?_append_left h)
  | varScheme h hinst => exact .varScheme (ctx_getElem?_append_left h) hinst
  | lam helab hok hbody ih => exact .lam helab hok ih
  | app hf harg hsub ih₁ ih₂ => exact .app ih₁ ih₂ hsub
  | appInfer hf harg hok hψ hσ huniq ih₁ ih₂ =>
    exact .appInfer ih₁ ih₂ hok hψ hσ huniq
  | ifBL hcond hthn hels ih₁ ih₂ ih₃ => exact .ifBL ih₁ ih₂ ih₃
  | anno helab he hsub ih => exact .anno helab ih hsub
  | annoInfer helab he hok hψ hσ huniq ih => exact .annoInfer helab ih hok hψ hσ huniq
  | letMono he₁ he₂ ih₁ ih₂ => exact .letMono ih₁ ih₂
  | letScheme hwf he₁ hsub he₂ ih₁ ih₂ => exact .letScheme hwf ih₁ hsub ih₂
  | letSchemeInfer hwf he₁ hok hψ hσ huniq he₂ ih₁ ih₂ =>
    exact .letSchemeInfer hwf ih₁ hok hψ hσ huniq ih₂
  | matchBL he heNil heCons ih₁ ih₂ ih₃ =>
    refine .matchBL ih₁ ih₂ ?_
    rw [consCtx_append]
    exact ih₃
  | matchBL_join he heNil heCons ih₁ ih₂ ih₃ =>
    refine .matchBL_join ih₁ ih₂ ?_
    rw [consCtx_append]
    exact ih₃
  | matchNil he hvalid heNil ih₁ ih₂ => exact .matchNil ih₁ hvalid ih₂
  | matchCons he hvalid heCons ih₁ ih₂ =>
    refine .matchCons ih₁ hvalid ?_
    rw [consCtx_append]
    exact ih₂

/-- `BinderRigid` counts are rigid-only (hence demand-OK as rigid). -/
theorem Count.rigidOnly_of_binderRigid {n : Nat} {c : Count}
    (h : Count.BinderRigid n c) : Count.RigidOnly c := by
  induction c with
  | lit => exact .lit
  | var v =>
    cases v with | mk kind idx =>
    cases kind with
    | rigid => exact .var
    | inferable => exact False.elim h
  | add a b iha ihb =>
    exact .add (iha h.1) (ihb h.2)
  | mul a b iha ihb =>
    exact .mul (iha h.1) (ihb h.2)
  | pred a ih => exact .pred (ih h)
  | min a b iha ihb => exact .min (iha h.1) (ihb h.2)
  | max a b iha ihb => exact .max (iha h.1) (ihb h.2)

theorem Ty.demandOK_of_binderRigid {n : Nat} {ty : Ty}
    (h : Ty.BinderRigid n ty) : Ty.DemandOK ty := by
  induction ty with
  | unit => exact .unit
  | tbind i => exact False.elim h
  | arrow _ _ ih₁ ih₂ => exact .arrow (ih₁ h.1) (ih₂ h.2)
  | bl lo hi elem ih =>
    exact .bl (.ofRigid (Count.rigidOnly_of_binderRigid h.1))
      (.ofRigid (Count.rigidOnly_of_binderRigid h.2.1))
      (ih h.2.2)

/-- Reflexivity of `Sub` on demand-OK types. -/
theorem Sub.refl_of_demandOK {Δ : List Constraint} {ty : Ty}
    (h : Ty.DemandOK ty) : Sub Δ ty ty := by
  induction h with
  | unit => exact .unit
  | arrow _ _ ih₁ ih₂ => exact .arrow ih₁ ih₂
  | bl hlo hhi helem => exact .bl_refl hlo hhi

/-- `ofTy` elaborates to itself (no holes). -/
theorem AnnoTy.elab_ofTy (t : Ty) : AnnoTy.Elab (AnnoTy.ofTy t) t := by
  induction t with
  | unit => exact .unit
  | tbind i => exact .tbind
  | arrow _ _ ihd ihc => exact .arrow ihd ihc
  | bl lo hi elem => exact .bl .known .known

/-! ## 9. Algorithmic inference (freshness frontier `Φ`)

Same pattern as `InferW`: thread `Φ : Nat` as the next inferable index.
`fillHoles` turns `AnnoTy` blanks into `cvar .inferable Φ`.
Oracle calls are the opaque `checkValid` / `solve` / `unique`; failure/`multiple`/`unknown`
⇒ `none` (require annotation).

`forceSubtype` is HM-style narrowing: plain `checkSub` first, else `solve`+`unique`
on escaping `obsBounds`. Used at `.anno`, `.app`, `.letScheme`, and `check`.
`matchBL` joins `BL` branch bounds (or requires equal non-`BL` types).
-/

def Count.isRigidOnly : Count → Bool
  | .lit _ => true
  | .var ⟨.rigid, _⟩ => true
  | .var ⟨.inferable, _⟩ => false
  | .add a b | .mul a b | .min a b | .max a b => a.isRigidOnly && b.isRigidOnly
  | .pred a => a.isRigidOnly

def Count.isDemandOK : Count → Bool
  | .var ⟨.inferable, _⟩ => true
  | .mul c (.var ⟨.inferable, _⟩) => c.isRigidOnly
  | .mul (.var ⟨.inferable, _⟩) c => c.isRigidOnly
  | .add (.var ⟨.inferable, _⟩) e => e.isRigidOnly
  | .add e (.var ⟨.inferable, _⟩) => e.isRigidOnly
  | .add (.mul c (.var ⟨.inferable, _⟩)) e => c.isRigidOnly && e.isRigidOnly
  | .add (.mul (.var ⟨.inferable, _⟩) c) e => c.isRigidOnly && e.isRigidOnly
  | c => c.isRigidOnly

def Ty.isDemandOK : Ty → Bool
  | .unit => true
  | .tbind _ => false
  | .arrow d c => d.isDemandOK && c.isDemandOK
  | .bl lo hi elem => lo.isDemandOK && hi.isDemandOK && elem.isDemandOK

/-- Algorithmic subtype check (mirrors `Sub`). -/
def checkSub (Δ : List Constraint) (t u : Ty) : Bool :=
  match t, u with
  | .unit, .unit => true
  | .tbind i, .tbind j => decide (i = j)
  | .arrow a b, .arrow a' b' => checkSub Δ a' a && checkSub Δ b b'
  | .bl lo hi elem, .bl lo' hi' elem' =>
      elem == elem' && lo'.isDemandOK && hi'.isDemandOK &&
        checkValid (Interval.subGoals Δ ⟨lo, hi⟩ ⟨lo', hi'⟩) == .valid
  | _, _ => false
termination_by t.size + u.size
decreasing_by all_goals (simp_wf; simp [Ty.size]; omega)

def Count.applyArgs (args : List Count) : Count → Count
  | .lit n => .lit n
  | .var ⟨.rigid, i⟩ => args.getD i (.lit 0)
  | .var v => .var v
  | .add a b => .add (applyArgs args a) (applyArgs args b)
  | .mul a b => .mul (applyArgs args a) (applyArgs args b)
  | .pred a => .pred (applyArgs args a)
  | .min a b => .min (applyArgs args a) (applyArgs args b)
  | .max a b => .max (applyArgs args a) (applyArgs args b)

def Ty.applyArgs (args : List Count) : Ty → Ty
  | .unit => .unit
  | .tbind i => .tbind i
  | .arrow d c => .arrow (applyArgs args d) (applyArgs args c)
  | .bl lo hi elem => .bl (Count.applyArgs args lo) (Count.applyArgs args hi) elem

def Count.binderRigidBool (n : Nat) : Count → Bool
  | .lit _ => true
  | .var ⟨.rigid, i⟩ => decide (i < n)
  | .var ⟨.inferable, _⟩ => false
  | .add a b | .mul a b | .min a b | .max a b =>
      binderRigidBool n a && binderRigidBool n b
  | .pred a => binderRigidBool n a

def Ty.binderRigidBool (n : Nat) : Ty → Bool
  | .unit => true
  | .tbind _ => false
  | .bl lo hi elem =>
      Count.binderRigidBool n lo && Count.binderRigidBool n hi && binderRigidBool n elem
  | .arrow d c => binderRigidBool n d && binderRigidBool n c

def BScheme.WF_bool (s : BScheme) : Bool :=
  Ty.binderRigidBool s.binders s.body

def BScheme.instantiate? (s : BScheme) (args : List Count) : Option Ty :=
  if s.WF_bool && args.length = s.binders then
    some (Ty.applyArgs args s.body)
  else
    none

/-- Fill `none` bounds with fresh inferables starting at `Φ`. -/
def fillBound (Φ : Nat) : Option Count → Nat × Count
  | some c => (Φ, c)
  | none => (Φ + 1, cvar .inferable Φ)

def fillHoles (Φ : Nat) : AnnoTy → Nat × Ty
  | .unit => (Φ, .unit)
  | .tbind i => (Φ, .tbind i)
  | .arrow d c =>
      let (Φ₁, d') := fillHoles Φ d
      let (Φ₂, c') := fillHoles Φ₁ c
      (Φ₂, .arrow d' c')
  | .bl lo hi elem =>
      let (Φ₁, lo') := fillBound Φ lo
      let (Φ₂, hi') := fillBound Φ₁ hi
      (Φ₂, .bl lo' hi' elem)

def Expr.size : Expr → Nat
  | .unit | .nil => 1
  | .var _ _ => 1
  | .cons h t => 1 + h.size + t.size
  | .lam _ b => 1 + b.size
  | .app f a => 1 + f.size + a.size
  | .if_ c t e => 1 + c.size + t.size + e.size
  | .anno e _ => 1 + e.size
  | .let_ b e => 1 + b.size + e.size
  | .letScheme _ b e => 1 + b.size + e.size
  | .matchBL s n c => 1 + s.size + n.size + c.size
  | .matchNil s n => 1 + s.size + n.size
  | .matchCons s c => 1 + s.size + c.size

/-- Force `ty'` into demand `ty`: prefer plain `checkSub`; else `solve`+`unique`.
Fails on `multiple` / `unknown` / `unsat` (annotation required).
Used at ascription and HM-style use sites (app domain, scheme pack, `check`). -/
def forceSubtype (Δ : List Constraint) (ty' ty : Ty) : Bool :=
  if checkSub Δ ty' ty then true
  else if !ty.isDemandOK then false
  else
    match subtypeProblem Δ ty' ty with
    | none => false
    | some ψ =>
      match solve ψ with
      | .witness _ => unique ψ ty'.obsBounds == .unique
      | _ => false

/-- Join branch types for `matchBL`: both `BL` → join bounds; else require equality. -/
def joinBranchTy (t u : Ty) : Option Ty :=
  match t, u with
  | .bl lo₁ hi₁ elem, .bl lo₂ hi₂ elem' =>
      if elem == elem' then some (.bl (.min lo₁ lo₂) (.max hi₁ hi₂) elem) else none
  | _, _ => if t == u then some t else none

/-- Synthesize a type for `e`.

Returns `some (Φ', τ)` with updated freshness frontier, or `none` on failure
(including when `forceSubtype` rejects non-unique *escaping* source bounds).

**Uniqueness.** The returned *type shape* is determined by the syntax-directed
algorithm (one successful path ⇒ one `τ`). That does **not** mean every bound
expression inside `τ` is a unique solution of an arithmetic problem: after hole
filling, `τ` may still mention inferables (`?a`, …), and `forceSubtype` only
demands uniqueness of the *source* type’s `obsBounds` when solving into a
demand — it does not substitute a witness into `τ`. So you can get a unique
synthesized type that still contains non-unique / unsolved bound variables in
the printed form.
-/
def synth (Φ : Nat) (Δ : List Constraint) (ctx : Ctx) : Expr → Option (Nat × Ty)
  | .unit => some (Φ, .unit)
  | .nil => some (Φ, .bl (.lit 0) (.lit 0) .unit)
  | .cons h t =>
    match synth Φ Δ ctx h with
    | none => none
    | some (Φ₁, ht) =>
      match synth Φ₁ Δ ctx t with
      | none => none
      | some (Φ₂, tty) =>
        match ht, tty with
        | .unit, .bl lo hi elem => some (Φ₂, .bl (.add lo (.lit 1)) (.add hi (.lit 1)) elem)
        | _, _ => none
  | .var i args =>
    match ctx[i]? with
    | some (.mono ty) =>
        if args.isEmpty then some (Φ, ty) else none
    | some (.scheme s) =>
        match s.instantiate? args with
        | some ty => some (Φ, ty)
        | none => none
    | none => none
  | .lam paramAnn body =>
    let (Φ₁, paramTy) := fillHoles Φ paramAnn
    if !paramTy.isDemandOK then none
    else
      match synth Φ₁ Δ (.mono paramTy :: ctx) body with
      | some (Φ₂, bodyTy) => some (Φ₂, .arrow paramTy bodyTy)
      | none => none
  | .app f arg =>
    match synth Φ Δ ctx f with
    | none => none
    | some (Φ₁, fty) =>
      match fty with
      | .arrow dom cod =>
        match synth Φ₁ Δ ctx arg with
        | none => none
        | some (Φ₂, aty) =>
          if forceSubtype Δ aty dom then some (Φ₂, cod) else none
      | _ => none
  | .if_ cond thn els =>
    match synth Φ Δ ctx cond with
    | none => none
    | some (Φ₁, ct) =>
      match synth Φ₁ Δ ctx thn with
      | none => none
      | some (Φ₂, tt) =>
        match synth Φ₂ Δ ctx els with
        | none => none
        | some (Φ₃, et) =>
          match ct, tt, et with
          | .unit, .bl lo₁ hi₁ elem, .bl lo₂ hi₂ elem' =>
              if elem == elem' then
                some (Φ₃, .bl (.min lo₁ lo₂) (.max hi₁ hi₂) elem)
              else none
          | _, _, _ => none
  | .anno e ann =>
    let (Φ₁, ty) := fillHoles Φ ann
    match synth Φ₁ Δ ctx e with
    | none => none
    | some (Φ₂, ty') =>
      if forceSubtype Δ ty' ty then some (Φ₂, ty) else none
  | .let_ bind body =>
    match synth Φ Δ ctx bind with
    | none => none
    | some (Φ₁, ty1) => synth Φ₁ Δ (.mono ty1 :: ctx) body
  | .letScheme s bind body =>
    if !s.WF_bool then none
    else
      match synth Φ Δ ctx bind with
      | none => none
      | some (Φ₁, tyb) =>
        if forceSubtype Δ tyb s.body then
          synth Φ₁ Δ (.scheme s :: ctx) body
        else none
  | .matchBL scrut eNil eCons =>
    match synth Φ Δ ctx scrut with
    | none => none
    | some (Φ₁, sty) =>
      match sty with
      | .bl lo hi .unit =>
        match synth Φ₁ (Δ ++ nilRefine lo hi) ctx eNil with
        | none => none
        | some (Φ₂, tNil) =>
          match synth Φ₂ (Δ ++ consRefine hi) (consCtx ctx lo hi) eCons with
          | none => none
          | some (Φ₃, tCons) =>
            match joinBranchTy tNil tCons with
            | some ty => some (Φ₃, ty)
            | none => none
      | _ => none
  | .matchNil scrut eNil =>
    match synth Φ Δ ctx scrut with
    | none => none
    | some (Φ₁, sty) =>
      match sty with
      | .bl lo hi .unit =>
        if checkValid (mustBeEmpty Δ hi) != .valid then none
        else synth Φ₁ (Δ ++ nilRefine lo hi) ctx eNil
      | _ => none
  | .matchCons scrut eCons =>
    match synth Φ Δ ctx scrut with
    | none => none
    | some (Φ₁, sty) =>
      match sty with
      | .bl lo hi .unit =>
        if checkValid (mustBeNonempty Δ lo) != .valid then none
        else synth Φ₁ (Δ ++ consRefine hi) (consCtx ctx lo hi) eCons
      | _ => none
termination_by e => e.size
decreasing_by all_goals (simp_wf; simp [Expr.size] <;> omega)

/-- Check `e` against expected `ty` (synth then force into demand — HM narrowing). -/
def check (Φ : Nat) (Δ : List Constraint) (ctx : Ctx) (e : Expr) (ty : Ty) :
    Option Nat :=
  match synth Φ Δ ctx e with
  | none => none
  | some (Φ', ty') =>
    if forceSubtype Δ ty' ty then some Φ' else none

/-! ### Soundness helpers (partial — synth_sound ladder) -/

/-- Bool `&&` characterization (used throughout §9 soundness). -/
private theorem bool_and_eq_true {a b : Bool} : a && b = true ↔ a = true ∧ b = true := by
  cases a <;> cases b <;> simp

theorem Count.isRigidOnly_of_rigidOnly {c : Count} (h : Count.RigidOnly c) :
    c.isRigidOnly = true := by
  induction h with
  | lit => rfl
  | var => rfl
  | add _ _ iha ihb => simp [Count.isRigidOnly, iha, ihb]
  | mul _ _ iha ihb => simp [Count.isRigidOnly, iha, ihb]
  | pred _ ih => simp [Count.isRigidOnly, ih]
  | min _ _ iha ihb => simp [Count.isRigidOnly, iha, ihb]
  | max _ _ iha ihb => simp [Count.isRigidOnly, iha, ihb]

theorem Count.rigidOnly_of_isRigidOnly {c : Count} (h : c.isRigidOnly = true) :
    Count.RigidOnly c := by
  induction c with
  | lit => exact .lit
  | var v =>
    cases v with | mk kind idx =>
    cases kind with
    | rigid => exact .var
    | inferable => simp [Count.isRigidOnly] at h
  | add a b iha ihb =>
    simp [Count.isRigidOnly] at h
    exact .add (iha h.1) (ihb h.2)
  | mul a b iha ihb =>
    simp [Count.isRigidOnly] at h
    exact .mul (iha h.1) (ihb h.2)
  | pred a ih =>
    simp [Count.isRigidOnly] at h
    exact .pred (ih h)
  | min a b iha ihb =>
    simp [Count.isRigidOnly] at h
    exact .min (iha h.1) (ihb h.2)
  | max a b iha ihb =>
    simp [Count.isRigidOnly] at h
    exact .max (iha h.1) (ihb h.2)

theorem Count.isRigidOnly_iff {c : Count} :
    c.isRigidOnly = true ↔ Count.RigidOnly c :=
  ⟨Count.rigidOnly_of_isRigidOnly, Count.isRigidOnly_of_rigidOnly⟩

/-- Rigid counts never hit a DemandOK special-form arm (those embed an inferable). -/
theorem Count.isDemandOK_of_isRigidOnly {c : Count} (h : c.isRigidOnly = true) :
    c.isDemandOK = true := by
  unfold Count.isDemandOK
  split <;> try (exact h)
  · -- `.var inferable` arm
    rename_i i
    simp [Count.isRigidOnly] at h
  · -- `.mul c (var inferable)`
    rename_i c i
    simp [Count.isRigidOnly] at h
  · -- `.mul (var inferable) c`
    rename_i i c
    simp [Count.isRigidOnly] at h
  · -- `.add (var inferable) e`
    rename_i i e
    simp [Count.isRigidOnly] at h
  · -- `.add e (var inferable)`
    rename_i e i
    simp [Count.isRigidOnly] at h
  · -- `.add (.mul c (var inferable)) e`
    rename_i c i e
    simp [Count.isRigidOnly] at h
  · -- `.add (.mul (var inferable) c) e`
    rename_i i c e
    simp [Count.isRigidOnly] at h

theorem Count.isDemandOK_of_demandOK {c : Count} (h : Count.DemandOK c) :
    c.isDemandOK = true := by
  induction h with
  | ofRigid h => exact Count.isDemandOK_of_isRigidOnly (Count.isRigidOnly_of_rigidOnly h)
  | infer => rfl
  | scale h => simp [Count.isDemandOK, Count.isRigidOnly_of_rigidOnly h]
  | scaleComm h =>
    -- Right factor is rigid ⇒ first mul-arm does not match.
    cases h with
    | lit => rfl
    | var => rfl
    | add ha hb =>
      simp [Count.isDemandOK, Count.isRigidOnly,
        Count.isRigidOnly_of_rigidOnly ha, Count.isRigidOnly_of_rigidOnly hb]
    | mul ha hb =>
      simp [Count.isDemandOK, Count.isRigidOnly,
        Count.isRigidOnly_of_rigidOnly ha, Count.isRigidOnly_of_rigidOnly hb]
    | pred ha =>
      simp [Count.isDemandOK, Count.isRigidOnly, Count.isRigidOnly_of_rigidOnly ha]
    | min ha hb =>
      simp [Count.isDemandOK, Count.isRigidOnly,
        Count.isRigidOnly_of_rigidOnly ha, Count.isRigidOnly_of_rigidOnly hb]
    | max ha hb =>
      simp [Count.isDemandOK, Count.isRigidOnly,
        Count.isRigidOnly_of_rigidOnly ha, Count.isRigidOnly_of_rigidOnly hb]
  | offset h => simp [Count.isDemandOK, Count.isRigidOnly_of_rigidOnly h]
  | offsetComm h =>
    -- Left is rigid ⇒ first add-arm does not match; second arm fires.
    cases h with
    | lit => rfl
    | var => rfl
    | add ha hb =>
      simp [Count.isDemandOK, Count.isRigidOnly,
        Count.isRigidOnly_of_rigidOnly ha, Count.isRigidOnly_of_rigidOnly hb]
    | mul ha hb =>
      simp [Count.isDemandOK, Count.isRigidOnly,
        Count.isRigidOnly_of_rigidOnly ha, Count.isRigidOnly_of_rigidOnly hb]
    | pred ha =>
      simp [Count.isDemandOK, Count.isRigidOnly, Count.isRigidOnly_of_rigidOnly ha]
    | min ha hb =>
      simp [Count.isDemandOK, Count.isRigidOnly,
        Count.isRigidOnly_of_rigidOnly ha, Count.isRigidOnly_of_rigidOnly hb]
    | max ha hb =>
      simp [Count.isDemandOK, Count.isRigidOnly,
        Count.isRigidOnly_of_rigidOnly ha, Count.isRigidOnly_of_rigidOnly hb]
  | aff hc he =>
    have hc' := Count.isRigidOnly_of_rigidOnly hc
    -- Case on offset so `.add _ (var inferable)` cannot match.
    cases he with
    | lit => simp [Count.isDemandOK, Count.isRigidOnly, hc']
    | var => simp [Count.isDemandOK, Count.isRigidOnly, hc']
    | add ha hb =>
      simp [Count.isDemandOK, Count.isRigidOnly, hc',
        Count.isRigidOnly_of_rigidOnly ha, Count.isRigidOnly_of_rigidOnly hb]
    | mul ha hb =>
      simp [Count.isDemandOK, Count.isRigidOnly, hc',
        Count.isRigidOnly_of_rigidOnly ha, Count.isRigidOnly_of_rigidOnly hb]
    | pred ha =>
      simp [Count.isDemandOK, Count.isRigidOnly, hc', Count.isRigidOnly_of_rigidOnly ha]
    | min ha hb =>
      simp [Count.isDemandOK, Count.isRigidOnly, hc',
        Count.isRigidOnly_of_rigidOnly ha, Count.isRigidOnly_of_rigidOnly hb]
    | max ha hb =>
      simp [Count.isDemandOK, Count.isRigidOnly, hc',
        Count.isRigidOnly_of_rigidOnly ha, Count.isRigidOnly_of_rigidOnly hb]
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
        simp [Count.isDemandOK, Count.isRigidOnly,
          Count.isRigidOnly_of_rigidOnly ha, Count.isRigidOnly_of_rigidOnly hb]
      | mul ha hb =>
        simp [Count.isDemandOK, Count.isRigidOnly,
          Count.isRigidOnly_of_rigidOnly ha, Count.isRigidOnly_of_rigidOnly hb]
      | pred ha =>
        simp [Count.isDemandOK, Count.isRigidOnly, Count.isRigidOnly_of_rigidOnly ha]
      | min ha hb =>
        simp [Count.isDemandOK, Count.isRigidOnly,
          Count.isRigidOnly_of_rigidOnly ha, Count.isRigidOnly_of_rigidOnly hb]
      | max ha hb =>
        simp [Count.isDemandOK, Count.isRigidOnly,
          Count.isRigidOnly_of_rigidOnly ha, Count.isRigidOnly_of_rigidOnly hb]
    | var =>
      cases he with
      | lit => rfl
      | var => rfl
      | add ha hb =>
        simp [Count.isDemandOK, Count.isRigidOnly,
          Count.isRigidOnly_of_rigidOnly ha, Count.isRigidOnly_of_rigidOnly hb]
      | mul ha hb =>
        simp [Count.isDemandOK, Count.isRigidOnly,
          Count.isRigidOnly_of_rigidOnly ha, Count.isRigidOnly_of_rigidOnly hb]
      | pred ha =>
        simp [Count.isDemandOK, Count.isRigidOnly, Count.isRigidOnly_of_rigidOnly ha]
      | min ha hb =>
        simp [Count.isDemandOK, Count.isRigidOnly,
          Count.isRigidOnly_of_rigidOnly ha, Count.isRigidOnly_of_rigidOnly hb]
      | max ha hb =>
        simp [Count.isDemandOK, Count.isRigidOnly,
          Count.isRigidOnly_of_rigidOnly ha, Count.isRigidOnly_of_rigidOnly hb]
    | add hca hcb =>
      cases he with
      | lit =>
        simp [Count.isDemandOK, Count.isRigidOnly,
          Count.isRigidOnly_of_rigidOnly hca, Count.isRigidOnly_of_rigidOnly hcb]
      | var =>
        simp [Count.isDemandOK, Count.isRigidOnly,
          Count.isRigidOnly_of_rigidOnly hca, Count.isRigidOnly_of_rigidOnly hcb]
      | add ha hb =>
        simp [Count.isDemandOK, Count.isRigidOnly,
          Count.isRigidOnly_of_rigidOnly hca, Count.isRigidOnly_of_rigidOnly hcb,
          Count.isRigidOnly_of_rigidOnly ha, Count.isRigidOnly_of_rigidOnly hb]
      | mul ha hb =>
        simp [Count.isDemandOK, Count.isRigidOnly,
          Count.isRigidOnly_of_rigidOnly hca, Count.isRigidOnly_of_rigidOnly hcb,
          Count.isRigidOnly_of_rigidOnly ha, Count.isRigidOnly_of_rigidOnly hb]
      | pred ha =>
        simp [Count.isDemandOK, Count.isRigidOnly,
          Count.isRigidOnly_of_rigidOnly hca, Count.isRigidOnly_of_rigidOnly hcb,
          Count.isRigidOnly_of_rigidOnly ha]
      | min ha hb =>
        simp [Count.isDemandOK, Count.isRigidOnly,
          Count.isRigidOnly_of_rigidOnly hca, Count.isRigidOnly_of_rigidOnly hcb,
          Count.isRigidOnly_of_rigidOnly ha, Count.isRigidOnly_of_rigidOnly hb]
      | max ha hb =>
        simp [Count.isDemandOK, Count.isRigidOnly,
          Count.isRigidOnly_of_rigidOnly hca, Count.isRigidOnly_of_rigidOnly hcb,
          Count.isRigidOnly_of_rigidOnly ha, Count.isRigidOnly_of_rigidOnly hb]
    | mul hca hcb =>
      cases he with
      | lit =>
        simp [Count.isDemandOK, Count.isRigidOnly,
          Count.isRigidOnly_of_rigidOnly hca, Count.isRigidOnly_of_rigidOnly hcb]
      | var =>
        simp [Count.isDemandOK, Count.isRigidOnly,
          Count.isRigidOnly_of_rigidOnly hca, Count.isRigidOnly_of_rigidOnly hcb]
      | add ha hb =>
        simp [Count.isDemandOK, Count.isRigidOnly,
          Count.isRigidOnly_of_rigidOnly hca, Count.isRigidOnly_of_rigidOnly hcb,
          Count.isRigidOnly_of_rigidOnly ha, Count.isRigidOnly_of_rigidOnly hb]
      | mul ha hb =>
        simp [Count.isDemandOK, Count.isRigidOnly,
          Count.isRigidOnly_of_rigidOnly hca, Count.isRigidOnly_of_rigidOnly hcb,
          Count.isRigidOnly_of_rigidOnly ha, Count.isRigidOnly_of_rigidOnly hb]
      | pred ha =>
        simp [Count.isDemandOK, Count.isRigidOnly,
          Count.isRigidOnly_of_rigidOnly hca, Count.isRigidOnly_of_rigidOnly hcb,
          Count.isRigidOnly_of_rigidOnly ha]
      | min ha hb =>
        simp [Count.isDemandOK, Count.isRigidOnly,
          Count.isRigidOnly_of_rigidOnly hca, Count.isRigidOnly_of_rigidOnly hcb,
          Count.isRigidOnly_of_rigidOnly ha, Count.isRigidOnly_of_rigidOnly hb]
      | max ha hb =>
        simp [Count.isDemandOK, Count.isRigidOnly,
          Count.isRigidOnly_of_rigidOnly hca, Count.isRigidOnly_of_rigidOnly hcb,
          Count.isRigidOnly_of_rigidOnly ha, Count.isRigidOnly_of_rigidOnly hb]
    | pred hca =>
      cases he with
      | lit =>
        simp [Count.isDemandOK, Count.isRigidOnly, Count.isRigidOnly_of_rigidOnly hca]
      | var =>
        simp [Count.isDemandOK, Count.isRigidOnly, Count.isRigidOnly_of_rigidOnly hca]
      | add ha hb =>
        simp [Count.isDemandOK, Count.isRigidOnly, Count.isRigidOnly_of_rigidOnly hca,
          Count.isRigidOnly_of_rigidOnly ha, Count.isRigidOnly_of_rigidOnly hb]
      | mul ha hb =>
        simp [Count.isDemandOK, Count.isRigidOnly, Count.isRigidOnly_of_rigidOnly hca,
          Count.isRigidOnly_of_rigidOnly ha, Count.isRigidOnly_of_rigidOnly hb]
      | pred ha =>
        simp [Count.isDemandOK, Count.isRigidOnly, Count.isRigidOnly_of_rigidOnly hca,
          Count.isRigidOnly_of_rigidOnly ha]
      | min ha hb =>
        simp [Count.isDemandOK, Count.isRigidOnly, Count.isRigidOnly_of_rigidOnly hca,
          Count.isRigidOnly_of_rigidOnly ha, Count.isRigidOnly_of_rigidOnly hb]
      | max ha hb =>
        simp [Count.isDemandOK, Count.isRigidOnly, Count.isRigidOnly_of_rigidOnly hca,
          Count.isRigidOnly_of_rigidOnly ha, Count.isRigidOnly_of_rigidOnly hb]
    | min hca hcb =>
      cases he with
      | lit =>
        simp [Count.isDemandOK, Count.isRigidOnly,
          Count.isRigidOnly_of_rigidOnly hca, Count.isRigidOnly_of_rigidOnly hcb]
      | var =>
        simp [Count.isDemandOK, Count.isRigidOnly,
          Count.isRigidOnly_of_rigidOnly hca, Count.isRigidOnly_of_rigidOnly hcb]
      | add ha hb =>
        simp [Count.isDemandOK, Count.isRigidOnly,
          Count.isRigidOnly_of_rigidOnly hca, Count.isRigidOnly_of_rigidOnly hcb,
          Count.isRigidOnly_of_rigidOnly ha, Count.isRigidOnly_of_rigidOnly hb]
      | mul ha hb =>
        simp [Count.isDemandOK, Count.isRigidOnly,
          Count.isRigidOnly_of_rigidOnly hca, Count.isRigidOnly_of_rigidOnly hcb,
          Count.isRigidOnly_of_rigidOnly ha, Count.isRigidOnly_of_rigidOnly hb]
      | pred ha =>
        simp [Count.isDemandOK, Count.isRigidOnly,
          Count.isRigidOnly_of_rigidOnly hca, Count.isRigidOnly_of_rigidOnly hcb,
          Count.isRigidOnly_of_rigidOnly ha]
      | min ha hb =>
        simp [Count.isDemandOK, Count.isRigidOnly,
          Count.isRigidOnly_of_rigidOnly hca, Count.isRigidOnly_of_rigidOnly hcb,
          Count.isRigidOnly_of_rigidOnly ha, Count.isRigidOnly_of_rigidOnly hb]
      | max ha hb =>
        simp [Count.isDemandOK, Count.isRigidOnly,
          Count.isRigidOnly_of_rigidOnly hca, Count.isRigidOnly_of_rigidOnly hcb,
          Count.isRigidOnly_of_rigidOnly ha, Count.isRigidOnly_of_rigidOnly hb]
    | max hca hcb =>
      cases he with
      | lit =>
        simp [Count.isDemandOK, Count.isRigidOnly,
          Count.isRigidOnly_of_rigidOnly hca, Count.isRigidOnly_of_rigidOnly hcb]
      | var =>
        simp [Count.isDemandOK, Count.isRigidOnly,
          Count.isRigidOnly_of_rigidOnly hca, Count.isRigidOnly_of_rigidOnly hcb]
      | add ha hb =>
        simp [Count.isDemandOK, Count.isRigidOnly,
          Count.isRigidOnly_of_rigidOnly hca, Count.isRigidOnly_of_rigidOnly hcb,
          Count.isRigidOnly_of_rigidOnly ha, Count.isRigidOnly_of_rigidOnly hb]
      | mul ha hb =>
        simp [Count.isDemandOK, Count.isRigidOnly,
          Count.isRigidOnly_of_rigidOnly hca, Count.isRigidOnly_of_rigidOnly hcb,
          Count.isRigidOnly_of_rigidOnly ha, Count.isRigidOnly_of_rigidOnly hb]
      | pred ha =>
        simp [Count.isDemandOK, Count.isRigidOnly,
          Count.isRigidOnly_of_rigidOnly hca, Count.isRigidOnly_of_rigidOnly hcb,
          Count.isRigidOnly_of_rigidOnly ha]
      | min ha hb =>
        simp [Count.isDemandOK, Count.isRigidOnly,
          Count.isRigidOnly_of_rigidOnly hca, Count.isRigidOnly_of_rigidOnly hcb,
          Count.isRigidOnly_of_rigidOnly ha, Count.isRigidOnly_of_rigidOnly hb]
      | max ha hb =>
        simp [Count.isDemandOK, Count.isRigidOnly,
          Count.isRigidOnly_of_rigidOnly hca, Count.isRigidOnly_of_rigidOnly hcb,
          Count.isRigidOnly_of_rigidOnly ha, Count.isRigidOnly_of_rigidOnly hb]

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
    simp [Count.isDemandOK] at h
    exact .ofRigid (Count.rigidOnly_of_isRigidOnly h)
  | min a b iha ihb =>
    simp [Count.isDemandOK] at h
    exact .ofRigid (Count.rigidOnly_of_isRigidOnly h)
  | max a b iha ihb =>
    simp [Count.isDemandOK] at h
    exact .ofRigid (Count.rigidOnly_of_isRigidOnly h)

theorem Count.isDemandOK_iff {c : Count} : c.isDemandOK = true ↔ Count.DemandOK c :=
  ⟨Count.demandOK_of_isDemandOK, Count.isDemandOK_of_demandOK⟩

theorem Ty.isDemandOK_of_demandOK {ty : Ty} (h : Ty.DemandOK ty) : ty.isDemandOK = true := by
  induction h with
  | unit => rfl
  | arrow _ _ ihd ihc => simp [Ty.isDemandOK, ihd, ihc]
  | bl hlo hhi helem ih =>
    simp [Ty.isDemandOK, Count.isDemandOK_of_demandOK hlo, Count.isDemandOK_of_demandOK hhi, ih]

theorem Ty.demandOK_of_isDemandOK {ty : Ty} (h : ty.isDemandOK = true) : Ty.DemandOK ty := by
  induction ty with
  | unit => exact Ty.DemandOK.unit
  | tbind i => simp [Ty.isDemandOK] at h
  | arrow d c ihd ihc =>
    simp [Ty.isDemandOK] at h
    obtain ⟨hd, hc⟩ := h
    exact Ty.DemandOK.arrow (ihd hd) (ihc hc)
  | bl lo hi elem ih =>
    simp [Ty.isDemandOK] at h
    obtain ⟨hh, helem⟩ := h
    obtain ⟨hlo, hhi⟩ := hh
    exact Ty.DemandOK.bl (Count.demandOK_of_isDemandOK hlo) (Count.demandOK_of_isDemandOK hhi)
      (ih helem)

theorem Ty.isDemandOK_iff {ty : Ty} : ty.isDemandOK = true ↔ Ty.DemandOK ty :=
  ⟨Ty.demandOK_of_isDemandOK, Ty.isDemandOK_of_demandOK⟩

theorem checkSub_sound {Δ t u} (h : checkSub Δ t u = true) : Sub Δ t u := by
  match t, u with
  | .unit, .unit => exact .unit
  | .tbind i, .tbind j =>
    simp [checkSub, decide_eq_true_eq] at h
    subst h
    exact .tbind
  | .arrow a b, .arrow a' b' =>
    simp [checkSub] at h
    exact .arrow (checkSub_sound h.1) (checkSub_sound h.2)
  | .bl lo hi elem, .bl lo' hi' elem' =>
    simp [checkSub, beq_iff_eq] at h
    have helem : elem = elem' := h.1.1.1
    have hlo' : lo'.isDemandOK = true := h.1.1.2
    have hhi' : hi'.isDemandOK = true := h.1.2
    have hvalid : checkValid (Interval.subGoals Δ ⟨lo, hi⟩ ⟨lo', hi'⟩) = .valid := h.2
    subst helem
    exact Sub.bl (Count.demandOK_of_isDemandOK hlo') (Count.demandOK_of_isDemandOK hhi') hvalid
  | .unit, .arrow _ _ | .unit, .bl _ _ _ | .unit, .tbind _
  | .arrow _ _, .unit | .arrow _ _, .bl _ _ _ | .arrow _ _, .tbind _
  | .bl _ _ _, .unit | .bl _ _ _, .arrow _ _ | .bl _ _ _, .tbind _
  | .tbind _, .unit | .tbind _, .arrow _ _ | .tbind _, .bl _ _ _ =>
    simp [checkSub] at h
termination_by t.size + u.size
decreasing_by all_goals (simp_wf; simp [Ty.size] <;> omega)

theorem forceSubtype_of_true {Δ ty' ty} (h : forceSubtype Δ ty' ty = true) :
    checkSub Δ ty' ty = true ∨
      (Ty.DemandOK ty ∧
        ∃ ψ σ, subtypeProblem Δ ty' ty = some ψ ∧
          solve ψ = .witness σ ∧ unique ψ ty'.obsBounds = .unique) := by
  by_cases hcs : checkSub Δ ty' ty = true
  · exact Or.inl hcs
  · have hcsf : checkSub Δ ty' ty = false := eq_false_of_ne_true hcs
    simp [forceSubtype, hcsf] at h
    by_cases hok : ty.isDemandOK = true
    · simp [hok] at h
      cases hψ : subtypeProblem Δ ty' ty with
      | none => simp [hψ] at h
      | some ψ =>
        simp [hψ] at h
        cases hσ : solve ψ with
        | witness σ =>
          simp [hσ, beq_iff_eq] at h
          exact Or.inr ⟨Ty.demandOK_of_isDemandOK hok, ψ, σ, rfl, hσ, h⟩
        | unsat => simp [hσ] at h
        | unknown => simp [hσ] at h
    · simp [hok] at h

theorem forceSubtype_sub {Δ ty' ty} (h : forceSubtype Δ ty' ty = true) :
    Sub Δ ty' ty ∨
      (Ty.DemandOK ty ∧
        ∃ ψ σ, subtypeProblem Δ ty' ty = some ψ ∧
          solve ψ = .witness σ ∧ unique ψ ty'.obsBounds = .unique) := by
  cases forceSubtype_of_true h with
  | inl hcs => exact Or.inl (checkSub_sound hcs)
  | inr hr => exact Or.inr hr

theorem Count.binderRigid_of_bool {n : Nat} {c : Count}
    (h : Count.binderRigidBool n c = true) : Count.BinderRigid n c := by
  induction c with
  | lit => trivial
  | var v =>
    cases v with | mk kind idx =>
    cases kind with
    | rigid =>
      simpa [Count.binderRigidBool, decide_eq_true_eq] using h
    | inferable => simp [Count.binderRigidBool] at h
  | add a b iha ihb =>
    simp [Count.binderRigidBool] at h
    exact ⟨iha h.1, ihb h.2⟩
  | mul a b iha ihb =>
    simp [Count.binderRigidBool] at h
    exact ⟨iha h.1, ihb h.2⟩
  | pred a ih =>
    simp [Count.binderRigidBool] at h
    exact ih h
  | min a b iha ihb =>
    simp [Count.binderRigidBool] at h
    exact ⟨iha h.1, ihb h.2⟩
  | max a b iha ihb =>
    simp [Count.binderRigidBool] at h
    exact ⟨iha h.1, ihb h.2⟩

theorem Ty.binderRigid_of_bool {n : Nat} {ty : Ty}
    (h : Ty.binderRigidBool n ty = true) : Ty.BinderRigid n ty := by
  induction ty with
  | unit => trivial
  | tbind i => simp [Ty.binderRigidBool] at h
  | arrow d c ihd ihc =>
    simp [Ty.binderRigidBool] at h
    exact ⟨ihd h.1, ihc h.2⟩
  | bl lo hi elem ihelem =>
    simp [Ty.binderRigidBool] at h
    exact ⟨Count.binderRigid_of_bool h.1.1, Count.binderRigid_of_bool h.1.2, ihelem h.2⟩

theorem BScheme.wf_of_WF_bool {s : BScheme} (h : s.WF_bool = true) : s.WF :=
  Ty.binderRigid_of_bool (by simpa [BScheme.WF_bool] using h)

theorem fillHoles_elab (Φ : Nat) (ann : AnnoTy) :
    AnnoTy.Elab ann (fillHoles Φ ann).2 := by
  induction ann generalizing Φ with
  | unit => simp [fillHoles]; exact AnnoTy.Elab.unit
  | tbind i => simp [fillHoles]; exact AnnoTy.Elab.tbind
  | arrow d c ih₁ ih₂ =>
    simp [fillHoles]
    exact AnnoTy.Elab.arrow (ih₁ _) (ih₂ _)
  | bl lo hi elem =>
    simp [fillHoles, fillBound]
    apply AnnoTy.Elab.bl
    · cases lo with | none => exact AnnoTy.ElabBound.hole | some _ => exact AnnoTy.ElabBound.known
    · cases hi with | none => exact AnnoTy.ElabBound.hole | some _ => exact AnnoTy.ElabBound.known

theorem Count.subst_applyArgs_binderRigid {n args c}
    (hb : Count.BinderRigid n c) (hlen : args.length = n) :
    Count.Subst args c (Count.applyArgs args c) := by
  induction c with
  | lit => exact .lit
  | var v =>
    cases v with | mk kind idx =>
    cases kind with
    | rigid =>
      have hi : idx < args.length := by rw [hlen]; exact hb
      simp [Count.applyArgs, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
      exact .var (List.getElem?_eq_getElem hi)
    | inferable => exact False.elim hb
  | add a b iha ihb => exact .add (iha hb.1) (ihb hb.2)
  | mul a b iha ihb => exact .mul (iha hb.1) (ihb hb.2)
  | pred a ih => exact .pred (ih hb)
  | min a b iha ihb => exact .min (iha hb.1) (ihb hb.2)
  | max a b iha ihb => exact .max (iha hb.1) (ihb hb.2)

theorem subst_applyArgs_binderRigid {n args t}
    (hb : Ty.BinderRigid n t) (hlen : args.length = n) :
    (Ty.Subst args t (Ty.applyArgs args t)) := by
  induction t with
  | unit => exact .unit
  | tbind i => exact .tbind
  | arrow d c ihd ihc => exact .arrow (ihd hb.1) (ihc hb.2)
  | bl lo hi _ =>
    exact .bl (Count.subst_applyArgs_binderRigid hb.1 hlen)
      (Count.subst_applyArgs_binderRigid hb.2.1 hlen)

theorem instantiatesOf_instantiate?_sound {s : BScheme} {args : List Count} {ty : Ty}
    (hlen : args.length = s.binders) (h : s.instantiate? args = some ty) :
    s.InstantiatesTo args ty := by
  unfold BScheme.instantiate? at h
  split at h
  · rename_i hcond
    cases h
    simp [decide_eq_true_eq] at hcond
    exact .intro (BScheme.wf_of_WF_bool hcond.1) hlen
      (subst_applyArgs_binderRigid (BScheme.wf_of_WF_bool hcond.1) hlen)
  · cases h

theorem joinBranchTy_eq {t u ty} (h : joinBranchTy t u = some ty) :
    (∃ lo₁ hi₁ lo₂ hi₂ elem, t = .bl lo₁ hi₁ elem ∧ u = .bl lo₂ hi₂ elem ∧
      ty = .bl (.min lo₁ lo₂) (.max hi₁ hi₂) elem) ∨ (t = ty ∧ u = ty) := by
  unfold joinBranchTy at h
  split at h
  · split at h
    · rename_i heq
      simp [beq_iff_eq] at heq
      cases h
      subst heq
      exact Or.inl ⟨_, _, _, _, _, rfl, rfl, rfl⟩
    · cases h
  · split at h
    · rename_i heq
      cases h
      have : t = u := by simpa [beq_iff_eq] using heq
      exact Or.inr ⟨rfl, this.symm⟩
    · cases h

/-- Main soundness theorem: algorithmic `synth` implies declarative `TypeOf`. -/
theorem synth_sound {Φ Δ ctx e Φ' ty}
    (h : synth Φ Δ ctx e = some (Φ', ty)) :
    TypeOf Δ ctx e ty := by
  induction e generalizing Φ Φ' ty ctx Δ with
  | unit => simp [synth] at h; obtain ⟨_, hty⟩ := h; subst hty; exact TypeOf.unit
  | nil => simp [synth] at h; obtain ⟨_, hty⟩ := h; subst hty; exact TypeOf.nil
  | cons head tail ih_head ih_tail =>
    cases hhead : synth Φ Δ ctx head with
    | none => simp [synth, hhead] at h
    | some Φht =>
      obtain ⟨Φ₁, ht⟩ := Φht
      cases htail : synth Φ₁ Δ ctx tail with
      | none => simp [synth, hhead, htail] at h
      | some Φtty =>
        obtain ⟨Φ₂, tty⟩ := Φtty
        simp [synth, hhead, htail] at h
        cases ht with
        | unit =>
          cases tty with
          | bl lo hi elem =>
            cases h
            exact .cons (ih_head hhead) (ih_tail htail)
          | unit | arrow _ _ | tbind _ => simp at h
        | arrow _ _ | bl _ _ _ | tbind _ => simp at h
  | var i args =>
    cases hctx : ctx[i]? with
    | none => simp [synth, hctx] at h
    | some b =>
      cases b with
      | mono mty =>
        simp [synth, hctx] at h
        obtain ⟨ha, rfl, rfl⟩ := h
        have ha' : args = [] := by simpa [List.isEmpty_iff] using ha
        subst ha'
        exact .varMono hctx
      | scheme s =>
        simp [synth, hctx] at h
        cases hinst : s.instantiate? args with
        | none => simp [hinst] at h
        | some ity =>
          simp [hinst] at h
          obtain ⟨rfl, rfl⟩ := h
          have hlen : args.length = s.binders := by
            unfold BScheme.instantiate? at hinst
            split at hinst
            · rename_i hcond
              simp [decide_eq_true_eq] at hcond
              exact hcond.2
            · cases hinst
          exact .varScheme hctx (instantiatesOf_instantiate?_sound hlen hinst)
  | lam paramAnn body ih_body =>
    cases hfill : fillHoles Φ paramAnn with
    | mk Φ₁ paramTy =>
      simp [synth, hfill] at h
      by_cases hok : paramTy.isDemandOK = true
      · simp [hok] at h
        cases hb : synth Φ₁ Δ (.mono paramTy :: ctx) body with
        | none => simp [hb] at h
        | some Φb =>
          obtain ⟨Φ₂, bodyTy⟩ := Φb
          simp [hb] at h
          obtain ⟨rfl, rfl⟩ := h
          have helab : AnnoTy.Elab paramAnn paramTy := by
            have := fillHoles_elab Φ paramAnn
            rwa [hfill] at this
          exact .lam helab (Ty.demandOK_of_isDemandOK hok) (ih_body hb)
      · simp [hok] at h
  | app f arg ih_f ih_arg =>
    cases hf : synth Φ Δ ctx f with
    | none => simp [synth, hf] at h
    | some Φf =>
      obtain ⟨Φ₁, fty⟩ := Φf
      cases fty with
      | arrow dom cod =>
        cases ha : synth Φ₁ Δ ctx arg with
        | none => simp [synth, hf, ha] at h
        | some Φa =>
          obtain ⟨Φ₂, aty⟩ := Φa
          simp [synth, hf, ha] at h
          obtain ⟨hfs, rfl, rfl⟩ := h
          cases forceSubtype_sub hfs with
          | inl hsub =>
            exact .app (ih_f hf) (ih_arg ha) hsub
          | inr hr =>
            obtain ⟨hok, ψ, σ, hψ, hσ, huniq⟩ := hr
            exact .appInfer (ih_f hf) (ih_arg ha) hok hψ hσ huniq
      | unit | bl _ _ _ | tbind _ => simp [synth, hf] at h
  | if_ cond thn els ih_c ih_t ih_e =>
    cases hc : synth Φ Δ ctx cond with
    | none => simp [synth, hc] at h
    | some Φc =>
      obtain ⟨Φ₁, ct⟩ := Φc
      cases ht : synth Φ₁ Δ ctx thn with
      | none => simp [synth, hc, ht] at h
      | some Φt =>
        obtain ⟨Φ₂, tt⟩ := Φt
        cases he : synth Φ₂ Δ ctx els with
        | none => simp [synth, hc, ht, he] at h
        | some Φe =>
          obtain ⟨Φ₃, et⟩ := Φe
          simp [synth, hc, ht, he] at h
          cases ct with
          | unit =>
            cases tt with
            | bl lo₁ hi₁ elem =>
              cases et with
              | bl lo₂ hi₂ elem' =>
                by_cases heq : elem = elem'
                · subst heq
                  simp at h
                  obtain ⟨rfl, rfl⟩ := h
                  exact .ifBL (ih_c hc) (ih_t ht) (ih_e he)
                · simp [heq] at h
              | unit | arrow _ _ | tbind _ => simp at h
            | unit | arrow _ _ | tbind _ => simp at h
          | arrow _ _ | bl _ _ _ | tbind _ => simp at h
  | anno e ann ih_e =>
    cases hfill : fillHoles Φ ann with
    | mk Φ₁ aty =>
      cases he : synth Φ₁ Δ ctx e with
      | none => simp [synth, hfill, he] at h
      | some Φe =>
        obtain ⟨Φ₂, ty'⟩ := Φe
        simp [synth, hfill, he] at h
        obtain ⟨hfs, rfl, rfl⟩ := h
        have helab : AnnoTy.Elab ann aty := by
          have := fillHoles_elab Φ ann
          rwa [hfill] at this
        cases forceSubtype_sub hfs with
        | inl hsub =>
          exact .anno helab (ih_e he) hsub
        | inr hr =>
          obtain ⟨hok, ψ, σ, hψ, hσ, huniq⟩ := hr
          exact .annoInfer helab (ih_e he) hok hψ hσ huniq
  | let_ bind body ih_b ih_body =>
    cases hb : synth Φ Δ ctx bind with
    | none => simp [synth, hb] at h
    | some Φb =>
      obtain ⟨Φ₁, ty1⟩ := Φb
      simp [synth, hb] at h
      exact .letMono (ih_b hb) (ih_body h)
  | letScheme s bind body ih_b ih_body =>
    simp [synth] at h
    by_cases hwf : s.WF_bool = true
    · simp [hwf] at h
      cases hb : synth Φ Δ ctx bind with
      | none => simp [hb] at h
      | some Φb =>
        obtain ⟨Φ₁, tyb⟩ := Φb
        simp [hb] at h
        obtain ⟨hfs, hbody⟩ := h
        cases forceSubtype_sub hfs with
        | inl hsub =>
          exact .letScheme (BScheme.wf_of_WF_bool hwf) (ih_b hb) hsub (ih_body hbody)
        | inr hr =>
          obtain ⟨hok, ψ, σ, hψ, hσ, huniq⟩ := hr
          exact .letSchemeInfer (BScheme.wf_of_WF_bool hwf) (ih_b hb) hok hψ hσ huniq
            (ih_body hbody)
    · simp [hwf] at h
  | matchBL scrut eNil eCons ih_s ih_n ih_c =>
    cases hs : synth Φ Δ ctx scrut with
    | none => simp [synth, hs] at h
    | some Φs =>
      obtain ⟨Φ₁, sty⟩ := Φs
      cases sty with
      | bl lo hi elem =>
        cases elem with
        | unit =>
          cases hn : synth Φ₁ (Δ ++ nilRefine lo hi) ctx eNil with
          | none => simp [synth, hs, hn] at h
          | some Φn =>
            obtain ⟨Φ₂, tNil⟩ := Φn
            cases hc : synth Φ₂ (Δ ++ consRefine hi) (consCtx ctx lo hi) eCons with
            | none => simp [synth, hs, hn, hc] at h
            | some Φc =>
              obtain ⟨Φ₃, tCons⟩ := Φc
              simp [synth, hs, hn, hc] at h
              cases hj : joinBranchTy tNil tCons with
              | none => simp [hj] at h
              | some jty =>
                simp [hj] at h
                obtain ⟨rfl, rfl⟩ := h
                cases joinBranchTy_eq hj with
                | inl hex =>
                  obtain ⟨lo₁, hi₁, lo₂, hi₂, _, rfl, rfl, rfl⟩ := hex
                  exact .matchBL_join (ih_s hs) (ih_n hn) (ih_c hc)
                | inr hEq =>
                  obtain ⟨rfl, rfl⟩ := hEq
                  exact .matchBL (ih_s hs) (ih_n hn) (ih_c hc)
        | tbind _ | arrow _ _ | bl _ _ _ => simp [synth, hs] at h
      | unit | arrow _ _ | tbind _ => simp [synth, hs] at h
  | matchNil scrut eNil ih_s ih_n =>
    cases hs : synth Φ Δ ctx scrut with
    | none => simp [synth, hs] at h
    | some Φs =>
      obtain ⟨Φ₁, sty⟩ := Φs
      cases sty with
      | bl lo hi elem =>
        cases elem with
        | unit =>
          simp [synth, hs] at h
          by_cases hv : checkValid (mustBeEmpty Δ hi) = .valid
          · simp [hv] at h
            exact .matchNil (ih_s hs) hv (ih_n h)
          · simp [hv] at h
        | tbind _ | arrow _ _ | bl _ _ _ => simp [synth, hs] at h
      | unit | arrow _ _ | tbind _ => simp [synth, hs] at h
  | matchCons scrut eCons ih_s ih_c =>
    cases hs : synth Φ Δ ctx scrut with
    | none => simp [synth, hs] at h
    | some Φs =>
      obtain ⟨Φ₁, sty⟩ := Φs
      cases sty with
      | bl lo hi elem =>
        cases elem with
        | unit =>
          simp [synth, hs] at h
          by_cases hv : checkValid (mustBeNonempty Δ lo) = .valid
          · simp [hv] at h
            exact .matchCons (ih_s hs) hv (ih_c h)
          · simp [hv] at h
        | tbind _ | arrow _ _ | bl _ _ _ => simp [synth, hs] at h
      | unit | arrow _ _ | tbind _ => simp [synth, hs] at h

/-- Algorithmic `check` ⇒ declarative `Check` (not `TypeOf` — no general subsumption). -/
theorem check_sound {Φ Δ ctx e ty Φ'}
    (h : check Φ Δ ctx e ty = some Φ') :
    Check Δ ctx e ty := by
  unfold check at h
  cases hs : synth Φ Δ ctx e with
  | none => simp [hs] at h
  | some pair =>
    obtain ⟨Φ'', ty'⟩ := pair
    by_cases hfs : forceSubtype Δ ty' ty = true
    · simp [hs, hfs] at h
      obtain ⟨rfl, rfl⟩ := h
      cases forceSubtype_sub hfs with
      | inl hsub =>
        exact .ofSub (synth_sound hs) hsub
      | inr hr =>
        obtain ⟨hok, ψ, σ, hψ, hσ, huniq⟩ := hr
        exact .ofInfer (synth_sound hs) hok hψ hσ huniq
    · simp [hs, hfs] at h

/-! ## 10. Tour / examples -/

namespace Examples

def r (i : Nat) : Count := cvar .rigid i
def x (i : Nat) : Count := cvar .inferable i

/- Need `BinderRigid` proofs for scheme bodies using `r i`. -/
theorem binderRigid_r {n i : Nat} (h : i < n) :
    Count.BinderRigid n (r i) := h

theorem idScheme_wf : Ty.BinderRigid 1
    (.arrow (.bl (r 0) (r 0) .unit) (.bl (r 0) (r 0) .unit)) := by
  refine And.intro ?_ ?_
  · exact And.intro (binderRigid_r Nat.zero_lt_one)
      (And.intro (binderRigid_r Nat.zero_lt_one) trivial)
  · exact And.intro (binderRigid_r Nat.zero_lt_one)
      (And.intro (binderRigid_r Nat.zero_lt_one) trivial)

/-- ### Build -/
example : TypeOf [] [] .nil (.bl (.lit 0) (.lit 0) .unit) := .nil

example : TypeOf [] [] (.cons .unit .nil)
    (.bl (.add (.lit 0) (.lit 1)) (.add (.lit 0) (.lit 1)) .unit) :=
  .cons .unit .nil

/-- ### Bound scheme: `∀ α. BL α α → BL α α` -/
def idScheme : BScheme where
  binders := 1
  body := .arrow (.bl (r 0) (r 0) .unit) (.bl (r 0) (r 0) .unit)

example : idScheme.WF := idScheme_wf

example : TypeOf [] [.scheme idScheme] (.var 0 [.lit 3])
    (.arrow (.bl (.lit 3) (.lit 3) .unit) (.bl (.lit 3) (.lit 3) .unit)) :=
  .varScheme rfl <| .intro idScheme_wf rfl <|
    .arrow (.bl (.var rfl) (.var rfl)) (.bl (.var rfl) (.var rfl))

example : TypeOf [] []
    (.letScheme idScheme
      (.lam (.bl (some (r 0)) (some (r 0)) .unit) (.var 0 []))
      (.var 0 [.lit 3]))
    (.arrow (.bl (.lit 3) (.lit 3) .unit) (.bl (.lit 3) (.lit 3) .unit)) :=
  .letScheme idScheme_wf
    (.lam (.bl .known .known) (.bl (.ofRigid .var) (.ofRigid .var) Ty.DemandOK.unit) (.varMono rfl))
    (Sub.refl_of_demandOK (Ty.demandOK_of_binderRigid idScheme_wf))
    (.varScheme rfl <| .intro idScheme_wf rfl <|
      .arrow (.bl (.var rfl) (.var rfl)) (.bl (.var rfl) (.var rfl)))

/-- ### Holes: `BL _ _` fills with fresh inferables via `fillHoles`. -/
example : fillHoles 0 (.bl none none .unit) =
    (2, .bl (cvar .inferable 0) (cvar .inferable 1) .unit) := rfl

/-- ### flatMap scheme (positive `lo*lo'` / `hi*hi'`)

Four binders: input list `[a,b]`, per-element lists `[c,d]`; result length
bounds multiply covariantly. -/
def flatMapScheme : BScheme where
  binders := 4
  body :=
    .arrow (.bl (r 0) (r 1) .unit)
      (.arrow (.arrow .unit (.bl (r 2) (r 3) .unit))
        (.bl (.mul (r 0) (r 2)) (.mul (r 1) (r 3)) .unit))

theorem flatMapScheme_wf : flatMapScheme.WF := by
  dsimp [BScheme.WF, flatMapScheme, Ty.BinderRigid, Count.BinderRigid, r, cvar]
  decide

example :
    flatMapScheme.InstantiatesTo [.lit 2, .lit 5, .lit 3, .lit 4]
      (.arrow (.bl (.lit 2) (.lit 5) .unit)
        (.arrow (.arrow .unit (.bl (.lit 3) (.lit 4) .unit))
          (.bl (.mul (.lit 2) (.lit 3)) (.mul (.lit 5) (.lit 4)) .unit))) := by
  refine .intro flatMapScheme_wf rfl ?_
  refine .arrow ?_ ?_
  · exact .bl (.var rfl) (.var (by native_decide))
  · refine .arrow ?_ ?_
    · exact .arrow .unit (.bl (.var (by native_decide)) (.var (by native_decide)))
    · exact .bl (.mul (.var rfl) (.var (by native_decide)))
        (.mul (.var (by native_decide)) (.var (by native_decide)))

/-- ### Match refines `Δ`

Scrutinee `BL lo hi`. Nil branch sees `lo ≤ 0` (and `0 ≤ hi`); cons sees `1 ≤ hi`
and types the tail at `pred`. Equal non-`BL` branches share a type; both-`BL`
branches join bounds (`matchBL_join`). -/
example (lo hi : Count) :
    TypeOf [] [.mono (.bl lo hi .unit)]
      (.matchBL (.var 0 []) .unit .unit) .unit :=
  .matchBL (.varMono rfl) .unit .unit

example (lo hi : Count) :
    TypeOf [] [.mono (.bl lo hi .unit)]
      (.matchBL (.var 0 []) .nil (.cons .unit .nil))
      (.bl (.min (.lit 0) (.add (.lit 0) (.lit 1)))
        (.max (.lit 0) (.add (.lit 0) (.lit 1))) .unit) :=
  .matchBL_join (.varMono rfl) .nil (.cons .unit .nil)

/-- Nil refine does **not** set `hi = 0` — only `lo ≤ 0` and `0 ≤ hi`. -/
example : nilRefine (.lit 0) (.lit 5) =
    [⟨.lit 0, .lit 0⟩, ⟨.lit 0, .lit 5⟩] := rfl

/-- Nil-only / cons-only: impossibility is a `checkValid` premise
(`mustBeEmpty` / `mustBeNonempty`). Closed proofs need a concrete oracle answer,
so these are shape reminders only. -/
example : mustBeEmpty [] (.lit 0) =
    { prem := [], goals := [⟨.lit 0, .lit 0⟩] } := rfl

example : mustBeNonempty [] (.lit 3) =
    { prem := [], goals := [⟨.lit 1, .lit 3⟩] } := rfl

/-- ### Escape ambiguity (prose)

Synthesizing `BL x (2x)` under weak constraints can yield many incomparable
`obsBounds`; `unique` fails ⇒ no `annoInfer` derivation ⇒ annotate or commit. -/
def linearAmbiguousProblem : ExistsProblem where
  inferables := [⟨.inferable, 0⟩]
  cons := [⟨.lit 5, x 0⟩]

def linearAmbiguousOuts : List Count :=
  [x 0, .mul (.lit 2) (x 0)]

/-- Meet inhabitability (side condition, not an `Expr`): -/
example (Δ : List Constraint) (i j : Interval) :
    ForallProblem :=
  inhabitProblem Δ (Interval.meet i j)

end Examples

end BLSketch
