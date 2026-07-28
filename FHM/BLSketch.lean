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
| **Join** | `ifBL` / `ifBool`, `matchBL` (both branches `BL`) via `min`/`max`; non-`BL` branches must be equal |
| **Meet inhabitability** | not an `Expr` form — when one value faces several BL demands, discharge `checkValid (inhabitProblem Δ (Interval.meet …))` |
| **Solve (∃ witness)** | HM-style narrowing at use/ascription: `annoInfer` / `appInfer` / `letSchemeInfer` via `subtypeProblem` + `solve = .witness` |
| **Demand discipline** | `Count.DemandOK` / `Ty.DemandOK` on demanded types |
| **Bound schemes** | `letScheme` / `letRecScheme` (pack with `Sub` or solve) + `varScheme` (`InstantiatesTo`); bodies are WF (only rigid binders `0..n-1`) |
| **Recursion** | `letRec` (mono, annotated) + `letRecScheme` (scheme in scope for the binding) |
| **Match refinement** | `matchBL` / `matchNil` / `matchCons` extend `Δ`; single-branch forms need a ∀-proof the other case is impossible (`hi ≤ 0` or `1 ≤ lo`) |
| **Checking** | separate `Check` judgment (synth type + `Sub` / solve existence); not a `TypeOf` ctor — keeps `TypeOf` syntax-directed |

**Uniqueness is not well-typedness.** A non-unique model means several assignments
work (commit / printed bounds are ambiguous). Declarative `TypeOf` / `Check` require
only existence of a solve witness. The algorithmic layer may still gate on
`unique` (elaborator policy); that is stricter than the relation and does not
affect soundness of `synth_sound` / `check_sound`.

Oracle answers other than success (`unknown` / `invalid` / `unsat` / `multiple`)
simply yield **no** algorithmic derivation — policy (annotate / commit / error)
is outside the declarative relation.

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

`zip` / `take` / `drop` / `splitAt`, value-`Nat` in types, inferred generalisation
algorithm, commit-vs-annotate policy, `unknown` UX,
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
  | add _ _ iha ihb => simp [Count.fold, iha, ihb]
  | mul _ _ iha ihb => simp [Count.fold, iha, ihb]
  | pred _ ih => simp [Count.fold, ih]
  | min _ _ iha ihb => simp [Count.fold, iha, ihb]
  | max _ _ iha ihb => simp [Count.fold, iha, ihb]

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
  | bool
  | tbind (i : Nat)
  | arrow (dom cod : Ty)
  | bl (lo hi : Count) (elem : Ty)
  deriving DecidableEq, Repr

def Ty.obsBounds : Ty → List Count
  | .unit | .bool => []
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
  | .unit | .bool => []
  | .tbind _ => []
  | .bl lo hi elem => lo.inferVars ++ hi.inferVars ++ elem.inferVars
  | .arrow d c => d.inferVars ++ c.inferVars

def Ty.size : Ty → Nat
  | .unit | .bool => 1
  | .tbind _ => 1
  | .bl _ _ elem => 1 + elem.size
  | .arrow d c => 1 + d.size + c.size

/-- Types whose count bounds are all `Count.Ground`. -/
inductive Ty.Ground : Ty → Prop where
  | unit : Ground .unit
  | bool : Ground .bool
  | bl {lo hi elem} :
    Count.Ground lo → Count.Ground hi → Ground elem → Ground (.bl lo hi elem)
  | arrow {a b} : Ground a → Ground b → Ground (.arrow a b)

@[simp] def Ty.isGround : Ty → Bool
  | .unit | .bool => true
  | .tbind _ => false
  | .bl lo hi elem => lo.isGround && hi.isGround && elem.isGround
  | .arrow a b => a.isGround && b.isGround

@[simp] theorem Ty.isGround_of_ground {t : Ty} (h : t.Ground) : t.isGround = true := by
  induction h with
  | unit => rfl
  | bool => rfl
  | bl hlo hhi helem ih =>
    simp [Count.isGround_of_ground hlo, Count.isGround_of_ground hhi, ih]
  | arrow _ _ iha ihb => simp [iha, ihb]

theorem Ty.ground_of_isGround {t : Ty} (h : t.isGround = true) : t.Ground := by
  induction t with
  | unit => exact .unit
  | bool => exact .bool
  | tbind i => simp at h
  | bl lo hi elem ih =>
      simp [Bool.and_eq_true] at h
      exact .bl (Count.ground_of_isGround h.1.1) (Count.ground_of_isGround h.1.2) (ih h.2)
  | arrow a b iha ihb =>
      simp [Bool.and_eq_true] at h
      exact .arrow (iha h.1) (ihb h.2)

theorem Ty.isGround_iff {t : Ty} : t.isGround = true ↔ t.Ground :=
  ⟨Ty.ground_of_isGround, Ty.isGround_of_ground⟩

instance (t : Ty) : Decidable t.Ground :=
  decidable_of_decidable_of_iff (Ty.isGround_iff (t := t))

/-- Fold ground count structure in a type down to literal bounds. -/
def Ty.fold (t : Ty) (h : t.Ground) : Ty :=
  match t with
  | .unit => .unit
  | .bool => .bool
  | .tbind i => .tbind i
  | .bl lo hi elem =>
      .bl (.lit (lo.fold (by cases h; assumption)))
        (.lit (hi.fold (by cases h; assumption)))
        (elem.fold (by cases h; assumption))
  | .arrow a b =>
      .arrow (a.fold (by cases h; assumption)) (b.fold (by cases h; assumption))

def subConstraints (ty' ty : Ty) : Option (List Constraint) :=
  match ty', ty with
  | .unit, .unit | .bool, .bool => some []
  | .tbind i, .tbind i' => if i = i' then some [] else none
  | .bl lo hi elem, .bl lo' hi' elem' =>
      match subConstraints elem elem' with
      | some cs => some (cs ++ [⟨lo', lo⟩, ⟨hi, hi'⟩])
      | none => none
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
  | bool : Ty.DemandOK .bool
  | tbind {i} : Ty.DemandOK (.tbind i)
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
  | bool
  | tbind (i : Nat)
  | arrow (dom cod : AnnoTy)
  | bl (lo hi : Option Count) (elem : Ty)
  deriving DecidableEq, Repr

def AnnoTy.ofTy : Ty → AnnoTy
  | .unit => .unit
  | .bool => .bool
  | .tbind i => .tbind i
  | .arrow d c => .arrow (ofTy d) (ofTy c)
  | .bl lo hi elem => .bl (some lo) (some hi) elem

inductive AnnoTy.ElabBound : Option Count → Count → Prop where
  | known {c} : ElabBound (some c) c
  | hole {c} : ElabBound none c

inductive AnnoTy.Elab : AnnoTy → Ty → Prop where
  | unit : Elab .unit .unit
  | bool : Elab .bool .bool
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

def Ty.SchemeWF (nCounts nTypes : Nat) : Ty → Prop
  | .unit | .bool => True
  | .tbind i => i < nTypes
  | .bl lo hi elem =>
    Count.BinderRigid nCounts lo ∧ Count.BinderRigid nCounts hi ∧
      Ty.SchemeWF nCounts nTypes elem
  | .arrow d c => Ty.SchemeWF nCounts nTypes d ∧ Ty.SchemeWF nCounts nTypes c

inductive SchemeBinder where
  | count
  | type
  deriving DecidableEq, Repr

inductive SchemeArg where
  | count : Count → SchemeArg
  | ty : Ty → SchemeArg
  deriving DecidableEq, Repr

structure BScheme where
  binders : List SchemeBinder  -- v1: all `.count` then all `.type`
  body : Ty
  deriving DecidableEq, Repr

def BScheme.nCounts (s : BScheme) : Nat := (s.binders.filter (· == .count)).length

def BScheme.nTypes (s : BScheme) : Nat := (s.binders.filter (· == .type)).length

/-- v1 telescope discipline: counts then types (no interleaving). -/
@[simp] def SchemeBinder.countsThenTypes : List SchemeBinder → Bool
  | [] => true
  | .count :: rest => countsThenTypes rest
  | .type :: rest => rest.all (· == .type)

def BScheme.WF (s : BScheme) : Prop :=
  SchemeBinder.countsThenTypes s.binders = true ∧
    Ty.SchemeWF s.nCounts s.nTypes s.body

@[simp] def schemeArgsOK : List SchemeBinder → List SchemeArg → Bool
  | [], [] => true
  | .count :: bs, .count _ :: as => schemeArgsOK bs as
  | .type :: bs, .ty _ :: as => schemeArgsOK bs as
  | _, _ => false

@[simp] def schemeCountArgs (args : List SchemeArg) : List Count :=
  args.filterMap fun | .count c => some c | .ty _ => none

@[simp] def schemeTyArgs (args : List SchemeArg) : List Ty :=
  args.filterMap fun | .ty t => some t | .count _ => none

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

inductive Ty.Subst : List Count → List Ty → Ty → Ty → Prop where
  | unit {cargs targs} : Subst cargs targs .unit .unit
  | bool {cargs targs} : Subst cargs targs .bool .bool
  | tbind {cargs targs i t} : targs[i]? = some t → Subst cargs targs (.tbind i) t
  | arrow {cargs targs d c d' c'} :
    Subst cargs targs d d' → Subst cargs targs c c' →
    Subst cargs targs (.arrow d c) (.arrow d' c')
  | bl {cargs targs lo hi lo' hi' elem elem'} :
    Count.Subst cargs lo lo' → Count.Subst cargs hi hi' →
    Subst cargs targs elem elem' →
    Subst cargs targs (.bl lo hi elem) (.bl lo' hi' elem')

inductive BScheme.InstantiatesTo : BScheme → List SchemeArg → Ty → Prop where
  | intro {s args ty} :
    s.WF →
    schemeArgsOK s.binders args = true →
    Ty.Subst (schemeCountArgs args) (schemeTyArgs args) s.body ty →
    InstantiatesTo s args ty

inductive Binding where
  | mono   : Ty → Binding
  | scheme : BScheme → Binding
  deriving Repr

abbrev Ctx := List Binding

/-! ## 4. Expressions -/

inductive Expr where
  | unit
  | true
  | false
  | nil
  | cons (head tail : Expr)
  | var (idx : Nat) (boundArgs : List SchemeArg)
  | lam (paramTy : AnnoTy) (body : Expr)
  | app (fn arg : Expr)
  | if_ (cond thn els : Expr)
  | anno (e : Expr) (ty : AnnoTy)
  | let_ (binding body : Expr)
  | letScheme (s : BScheme) (binding body : Expr)
  /-- Mono recursive let; `ann` is the type of the recursive binder. -/
  | letRec (ann : AnnoTy) (binding body : Expr)
  /-- Like `letScheme`, but the binding is typed with `s` already in scope. -/
  | letRecScheme (s : BScheme) (binding body : Expr)
  /-- Exhaustive match on `BL`. Nil branch under refined `Δ`; cons branch under
  `var 0 = head : elem`, `var 1 = tail : BL (pred lo) (pred hi) elem`. -/
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

/-- Strong negative on a witness-mode `decideGoals` query: no model exists.
Matches `solveZ3`'s mapping of this parse tag to `.unsat`. -/
def isWitnessUnsat : FHM.Z3.Verdict → Bool
  | .unknown "z3 reports no witness exists" => true
  | _ => false

/-- After a witness, try to find another solution with a different output value.

Honesty: `.unique` only if **every** “outs differ from σ” alternative query is
strongly unsat (no witness exists). Solver `unknown` / timeout / partial results
yield `.unknown`, never `.unique`. A `.witness` on any alternative ⇒ `.multiple`. -/
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
    -- Classify each alternative: found other / no other / inconclusive.
    let statuses : List (Option Bool) :=
      (outs.zip vals).flatMap fun (c, v) =>
        (differs c v).map fun extra =>
          match decideGoals unknowns (baseAs ++ extra) goals with
          | .witness _ => some true           -- found another model
          | v => if isWitnessUnsat v then some false  -- strong unsat
                 else none                    -- unknown / inconclusive
    if statuses.any (· == some true) then .multiple
    else if statuses.any (· == none) then .unknown
    else .unique  -- all some false, or no alternatives (empty outs)

end Z3Bridge

/-! ### Definitional BL oracles (no second opacity layer)

`checkValid` / `solve` / `unique` are plain wrappers over `Z3Bridge.*`, which
call pure `decide` / `decideGoals` on top of `opaque z3Run`. **One** IO fiction
(no `@[implemented_by]` / `unsafe` re-shim at the BL layer).

Soundness axioms below still sit at the BL problem-language level. Proving them
from `decide_*_sound` needs encoding lemmas (`countToExpr` ↔ `Count.eval`, etc.);
that is the remaining PR4 proof work. Removing the second opacity layer is the
structural half: Lean can now unfold BL oracles to the Z3 bridge. -/

/-- ∀ oracle: every goal verified under premises (runtime: Z3 via `decide`). -/
def checkValid (φ : ForallProblem) : ValidVerdict :=
  Z3Bridge.checkValidZ3 φ

/-- ∃∀ witness oracle. Returns **one** model if sat — not all solutions. -/
def solve (ψ : ExistsProblem) : SolveVerdict :=
  Z3Bridge.solveZ3 ψ

/-- Uniqueness oracle on chosen outputs (block-and-recheck after a witness).
`.unique` only after strong unsat on every alternative. -/
def unique (ψ : ExistsProblem) (outs : List Count) : UniqueVerdict :=
  Z3Bridge.uniqueZ3 ψ outs

/-- Soundness: only `.valid` is axiomatised (to be proved from `decide_verified_sound`). -/
axiom checkValid_sound (φ : ForallProblem) :
    checkValid φ = .valid → φ.Valid

/-- Soundness: only `.witness` is axiomatised (multi-goal witness bridge TBD). -/
axiom solve_sound (ψ : ExistsProblem) (σ : Assign) :
    solve ψ = .witness σ → ψ.SolvedBy σ

/-- Soundness: only `.unique` is axiomatised (block-and-recheck bridge TBD). -/
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

/-- Ctx for a cons branch: `var 0 = head : elem`, `var 1 = tail`. -/
def consCtx (ctx : Ctx) (lo hi : Count) (elem : Ty) : Ctx :=
  .mono elem :: .mono (.bl (.pred lo) (.pred hi) elem) :: ctx

/-- Join branch types: same shape; on every `BL`, join bounds and recurse into elems. -/
def joinBranchTy (t u : Ty) : Option Ty :=
  match t, u with
  | .unit, .unit => some .unit
  | .bool, .bool => some .bool
  | .tbind i, .tbind j => if i = j then some (.tbind i) else none
  | .arrow a b, .arrow a' b' =>
      match joinBranchTy a a', joinBranchTy b b' with
      | some d, some c => some (.arrow d c)
      | _, _ => none
  | .bl lo₁ hi₁ e₁, .bl lo₂ hi₂ e₂ =>
      match joinBranchTy e₁ e₂ with
      | some e => some (.bl (.min lo₁ lo₂) (.max hi₁ hi₂) e)
      | none => none
  | _, _ => none
termination_by t.size + u.size
decreasing_by all_goals (simp_wf; simp [Ty.size]; omega)

/-! ## 7. `Sub` and `TypeOf` -/

inductive Sub (Δ : List Constraint) : Ty → Ty → Prop where
  | unit :
    Sub Δ .unit .unit
  | bool :
    Sub Δ .bool .bool
  | arrow {a a' b b'} :
    Sub Δ a' a →
    Sub Δ b b' →
    Sub Δ (.arrow a b) (.arrow a' b')
  | tbind {i} :
    Sub Δ (.tbind i) (.tbind i)
  | bl {lo hi lo' hi' elem elem'} :
    Count.DemandOK lo' →
    Count.DemandOK hi' →
    checkValid (Interval.subGoals Δ ⟨lo, hi⟩ ⟨lo', hi'⟩) = .valid →
    Sub Δ elem elem' →
    Sub Δ (.bl lo hi elem) (.bl lo' hi' elem')
  | bl_refl {lo hi elem} :
    Count.DemandOK lo →
    Count.DemandOK hi →
    Ty.DemandOK elem →
    Sub Δ (.bl lo hi elem) (.bl lo hi elem)

inductive TypeOf : List Constraint → Ctx → Expr → Ty → Prop where
  | unit {Δ ctx} :
    TypeOf Δ ctx .unit .unit

  | true {Δ ctx} :
    TypeOf Δ ctx .true .bool

  | false {Δ ctx} :
    TypeOf Δ ctx .false .bool

  | cons {Δ ctx head tail lo hi elem} :
    TypeOf Δ ctx head elem →
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
    TypeOf Δ ctx (.app f arg) retTy

  | ifBL {Δ ctx cond thn els t u ty} :
    TypeOf Δ ctx cond .unit →
    TypeOf Δ ctx thn t →
    TypeOf Δ ctx els u →
    joinBranchTy t u = some ty →
    TypeOf Δ ctx (.if_ cond thn els) ty

  | ifBool {Δ ctx cond thn els t u ty} :
    TypeOf Δ ctx cond .bool →
    TypeOf Δ ctx thn t →
    TypeOf Δ ctx els u →
    joinBranchTy t u = some ty →
    TypeOf Δ ctx (.if_ cond thn els) ty

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
    TypeOf Δ ctx (.anno e ann) ty

  /-- Ascription of bare `[]` under an expected `BL` (checking intro; no synth of `.nil`). -/
  | annoNil {Δ ctx ann lo hi elem} :
    AnnoTy.Elab ann (.bl lo hi elem) →
    Sub Δ (.bl (.lit 0) (.lit 0) elem) (.bl lo hi elem) →
    TypeOf Δ ctx (.anno .nil ann) (.bl lo hi elem)

  /-- Bare `[]` ascription via solve when plain `Sub` does not apply. -/
  | annoNilInfer {Δ ctx ann lo hi elem ψ σ} :
    AnnoTy.Elab ann (.bl lo hi elem) →
    Ty.DemandOK (.bl lo hi elem) →
    subtypeProblem Δ (.bl (.lit 0) (.lit 0) elem) (.bl lo hi elem) = some ψ →
    solve ψ = .witness σ →
    TypeOf Δ ctx (.anno .nil ann) (.bl lo hi elem)

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
    TypeOf Δ (.scheme s :: ctx) e2 bodyTy →
    TypeOf Δ ctx (.letScheme s e1 e2) bodyTy

  | letRec {Δ ctx ann ty binding body tyB bodyTy} :
    AnnoTy.Elab ann ty →
    Ty.DemandOK ty →
    TypeOf Δ (.mono ty :: ctx) binding tyB →
    Sub Δ tyB ty →
    TypeOf Δ (.mono ty :: ctx) body bodyTy →
    TypeOf Δ ctx (.letRec ann binding body) bodyTy

  | letRecInfer {Δ ctx ann ty binding body tyB bodyTy ψ σ} :
    AnnoTy.Elab ann ty →
    Ty.DemandOK ty →
    TypeOf Δ (.mono ty :: ctx) binding tyB →
    subtypeProblem Δ tyB ty = some ψ →
    solve ψ = .witness σ →
    TypeOf Δ (.mono ty :: ctx) body bodyTy →
    TypeOf Δ ctx (.letRec ann binding body) bodyTy

  | letRecScheme {Δ ctx s binding body ty1 bodyTy} :
    s.WF →
    TypeOf Δ (.scheme s :: ctx) binding ty1 →
    Sub Δ ty1 s.body →
    TypeOf Δ (.scheme s :: ctx) body bodyTy →
    TypeOf Δ ctx (.letRecScheme s binding body) bodyTy

  | letRecSchemeInfer {Δ ctx s binding body ty1 bodyTy ψ σ} :
    s.WF →
    TypeOf Δ (.scheme s :: ctx) binding ty1 →
    Ty.DemandOK s.body →
    subtypeProblem Δ ty1 s.body = some ψ →
    solve ψ = .witness σ →
    TypeOf Δ (.scheme s :: ctx) body bodyTy →
    TypeOf Δ ctx (.letRecScheme s binding body) bodyTy

  /-- Exhaustive match, equal branch types (non-`BL`, or identical `BL`s).
  * nil: `Δ ++ nilRefine lo hi` (`lo ≤ 0`; `hi` not forced to `0`)
  * cons: `Δ ++ consRefine hi`; `consCtx` binds head / tail -/
  | matchBL {Δ ctx e eNil eCons lo hi elem ty} :
    TypeOf Δ ctx e (.bl lo hi elem) →
    TypeOf (Δ ++ nilRefine lo hi) ctx eNil ty →
    TypeOf (Δ ++ consRefine hi) (consCtx ctx lo hi elem) eCons ty →
    TypeOf Δ ctx (.matchBL e eNil eCons) ty

  /-- Exhaustive match: join branch types structurally (bounds on every `BL`). -/
  | matchBL_join {Δ ctx e eNil eCons lo hi scrutElem tNil tCons ty} :
    TypeOf Δ ctx e (.bl lo hi scrutElem) →
    TypeOf (Δ ++ nilRefine lo hi) ctx eNil tNil →
    TypeOf (Δ ++ consRefine hi) (consCtx ctx lo hi scrutElem) eCons tCons →
    joinBranchTy tNil tCons = some ty →
    TypeOf Δ ctx (.matchBL e eNil eCons) ty

  /-- Nil-only: require `hi ≤ 0` under `Δ` (empty is forced). -/
  | matchNil {Δ ctx e eNil lo hi elem ty} :
    TypeOf Δ ctx e (.bl lo hi elem) →
    checkValid (mustBeEmpty Δ hi) = .valid →
    TypeOf (Δ ++ nilRefine lo hi) ctx eNil ty →
    TypeOf Δ ctx (.matchNil e eNil) ty

  /-- Cons-only: require `1 ≤ lo` under `Δ` (non-empty is forced). -/
  | matchCons {Δ ctx e eCons lo hi elem ty} :
    TypeOf Δ ctx e (.bl lo hi elem) →
    checkValid (mustBeNonempty Δ lo) = .valid →
    TypeOf (Δ ++ consRefine hi) (consCtx ctx lo hi elem) eCons ty →
    TypeOf Δ ctx (.matchCons e eCons) ty

/-- Checking judgment: synthesized type fits a demand (plain `Sub` or solve existence),
or intro forms that only make sense under a demand (bare `nil`).
Keeps `TypeOf` syntax-directed — no general subsumption inside `TypeOf`.
Uniqueness of models is elaborator policy (`forceSubtype`), not a premise here. -/
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
    Check Δ ctx e ty
  /-- Bare `[]` checks against `BL lo hi α` when `BL 0 0 α <: BL lo hi α`. -/
  | nil {lo hi elem} :
    Sub Δ (.bl (.lit 0) (.lit 0) elem) (.bl lo hi elem) →
    Check Δ ctx .nil (.bl lo hi elem)

  /-- Bare `[]` check via solve when plain `Sub` does not apply. -/
  | nilInfer {lo hi elem ψ σ} :
    Ty.DemandOK (.bl lo hi elem) →
    subtypeProblem Δ (.bl (.lit 0) (.lit 0) elem) (.bl lo hi elem) = some ψ →
    solve ψ = .witness σ →
    Check Δ ctx .nil (.bl lo hi elem)

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
theorem Ty.Subst.unique {cargs targs t t₁ t₂}
    (h₁ : Ty.Subst cargs targs t t₁) (h₂ : Ty.Subst cargs targs t t₂) : t₁ = t₂ := by
  induction h₁ with
  | unit =>
    cases h₂
    rfl
  | bool =>
    cases h₂
    rfl
  | tbind hi =>
    cases h₂ with | tbind hj =>
    exact Option.some.inj (hi.symm.trans hj)
  | arrow hd hc =>
    cases h₂ with | arrow hd' hc' =>
    congr 1
    · exact (Ty.Subst.unique hd hd')
    · exact (Ty.Subst.unique hc hc')
  | bl hlo hhi helem =>
    cases h₂ with | bl hlo' hhi' helem' =>
    congr 1
    · exact (Count.Subst.unique hlo hlo')
    · exact (Count.Subst.unique hhi hhi')
    · exact (Ty.Subst.unique helem helem')

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

private theorem consCtx_append (ctx ctx' : Ctx) (lo hi : Count) (elem : Ty) :
    consCtx (ctx ++ ctx') lo hi elem = consCtx ctx lo hi elem ++ ctx' := by
  simp [consCtx, List.cons_append]

/-- Context weakening by appending unused bindings at the **end**
(de Bruijn indices in `e` unchanged). -/
theorem TypeOf.weakenCtx {Δ ctx ctx' e ty}
    (h : TypeOf Δ ctx e ty) : TypeOf Δ (ctx ++ ctx') e ty := by
  induction h with
  | unit => exact .unit
  | true => exact .true
  | false => exact .false
  | cons hhead htail ih₁ ih₂ => exact .cons ih₁ ih₂
  | varMono h => exact .varMono (ctx_getElem?_append_left h)
  | varScheme h hinst => exact .varScheme (ctx_getElem?_append_left h) hinst
  | lam helab hok hbody ih => exact .lam helab hok ih
  | app hf harg hsub ih₁ ih₂ => exact .app ih₁ ih₂ hsub
  | appInfer hf harg hok hψ hσ ih₁ ih₂ =>
    exact .appInfer ih₁ ih₂ hok hψ hσ
  | ifBL hcond hthn hels hjoin ih₁ ih₂ ih₃ => exact .ifBL ih₁ ih₂ ih₃ hjoin
  | ifBool hcond hthn hels hjoin ih₁ ih₂ ih₃ => exact .ifBool ih₁ ih₂ ih₃ hjoin
  | anno helab he hsub ih => exact .anno helab ih hsub
  | annoInfer helab he hok hψ hσ ih => exact .annoInfer helab ih hok hψ hσ
  | annoNil helab hsub => exact .annoNil helab hsub
  | annoNilInfer helab hok hψ hσ => exact .annoNilInfer helab hok hψ hσ
  | letMono he₁ he₂ ih₁ ih₂ => exact .letMono ih₁ ih₂
  | letScheme hwf he₁ hsub he₂ ih₁ ih₂ => exact .letScheme hwf ih₁ hsub ih₂
  | letSchemeInfer hwf he₁ hok hψ hσ he₂ ih₁ ih₂ =>
    exact .letSchemeInfer hwf ih₁ hok hψ hσ ih₂
  | letRec helab hok hb hsub hbody ih_b ih_body =>
    exact .letRec helab hok ih_b hsub ih_body
  | letRecInfer helab hok hb hψ hσ hbody ih_b ih_body =>
    exact .letRecInfer helab hok ih_b hψ hσ ih_body
  | letRecScheme hwf hb hsub hbody ih_b ih_body =>
    exact .letRecScheme hwf ih_b hsub ih_body
  | letRecSchemeInfer hwf hb hok hψ hσ hbody ih_b ih_body =>
    exact .letRecSchemeInfer hwf ih_b hok hψ hσ ih_body
  | matchBL he heNil heCons ih₁ ih₂ ih₃ =>
    refine .matchBL ih₁ ih₂ ?_
    rw [consCtx_append]
    exact ih₃
  | matchBL_join he heNil heCons hjoin ih₁ ih₂ ih₃ =>
    refine .matchBL_join ih₁ ih₂ ?_ hjoin
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

theorem Ty.demandOK_of_schemeWF {nCounts nTypes : Nat} {ty : Ty}
    (h : Ty.SchemeWF nCounts nTypes ty) (hTypes : nTypes = 0) : Ty.DemandOK ty := by
  induction ty generalizing nCounts nTypes with
  | unit => exact .unit
  | bool => exact .bool
  | tbind i =>
    rw [hTypes] at h
    exact False.elim (Nat.not_lt_zero i h)
  | arrow d c ih₁ ih₂ =>
    exact .arrow (ih₁ h.1 hTypes) (ih₂ h.2 hTypes)
  | bl lo hi elem ih =>
    exact .bl (.ofRigid (Count.rigidOnly_of_binderRigid h.1))
      (.ofRigid (Count.rigidOnly_of_binderRigid h.2.1))
      (ih h.2.2 hTypes)

/-- Reflexivity of `Sub` on demand-OK types. -/
theorem Sub.refl_of_demandOK {Δ : List Constraint} {ty : Ty}
    (h : Ty.DemandOK ty) : Sub Δ ty ty := by
  induction h with
  | unit => exact .unit
  | bool => exact .bool
  | tbind => exact .tbind
  | arrow _ _ ih₁ ih₂ => exact .arrow ih₁ ih₂
  | bl hlo hhi helem ih => exact .bl_refl hlo hhi helem

/-- `ofTy` elaborates to itself (no holes). -/
theorem AnnoTy.elab_ofTy (t : Ty) : AnnoTy.Elab (AnnoTy.ofTy t) t := by
  induction t with
  | unit => exact .unit
  | bool => exact .bool
  | tbind i => exact .tbind
  | arrow _ _ ihd ihc => exact .arrow ihd ihc
  | bl lo hi elem => exact .bl .known .known

/-! ## 9. Algorithmic inference (freshness frontier `Φ`)

Same pattern as `InferW`: thread `Φ : Nat` as the next inferable index.
`fillHoles` turns `AnnoTy` blanks into `cvar .inferable Φ`.
Oracle calls are the opaque `checkValid` / `solve` / `unique`; failure/`multiple`/`unknown`
⇒ `none` (require annotation).

`forceSubtype` is HM-style narrowing: plain `checkSub` first, else gather solve/unique
**evidence** and consult a pluggable **commit handler** (elaborator policy; stricter than
declarative `TypeOf` / `Check`, which only require a solve witness). Used at `.anno`,
`.app`, `.letScheme`, and `check`. PR3a: policy gates success and may return a witness
`σ`; PR3b will apply `σ` into types. `matchBL` joins `BL` branch bounds (or requires
equal non-`BL` types).
-/

/-! ### Commit policy (pluggable elaborator uniqueness / accept) -/

/-- Elaborator decision after narrowing evidence is gathered. -/
inductive Commit where
  /-- Accept auto-commit; `σ` is the witness from evidence (forceSubtype reuses it). -/
  | accept (σ : Assign)

  /-- Refuse auto-commit for this evidence under the current policy. -/
  | reject

/-- Oracle-shaped evidence for one solve+unique probe (exclusive cases).
Payloads are oracle equalities (v1); semantic `SolvedBy` / `UniqueOutputs` later
once uniqueness is honest — see TODO(unique-honesty). -/
inductive NarrowingEvidence (ψ : ExistsProblem) (outs : List Count) where
  /-- No usable witness (`unsat` or `unknown`). -/
  | none

  /-- Witness plus oracle `.unique` on `outs`. -/
  | unique (σ : Assign)
      (hσ : solve ψ = .witness σ)
      (hu : unique ψ outs = .unique)

  /-- Witness without uniqueness (oracle `.multiple` or `.unknown`). -/
  | some_ (σ : Assign)
      (hσ : solve ψ = .witness σ)
      (hnot : unique ψ outs ≠ .unique)

/-- Named policies (declarative source of truth via `Commits`). -/
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
  /-- `uniqueOnly` accepts a unique solve witness. -/
  | uniqueOnly_accept {ψ outs σ hσ hu} :
      Commits .uniqueOnly (ψ := ψ) (outs := outs) (.unique σ hσ hu) (.accept σ)

  /-- `uniqueOnly` rejects when there is no witness. -/
  | uniqueOnly_reject_none {ψ outs} :
      Commits .uniqueOnly (ψ := ψ) (outs := outs) .none .reject

  /-- `uniqueOnly` rejects a non-unique witness. -/
  | uniqueOnly_reject_some {ψ outs σ hσ hnot} :
      Commits .uniqueOnly (ψ := ψ) (outs := outs) (.some_ σ hσ hnot) .reject

  /-- `anyWitness` accepts a unique solve witness. -/
  | anyWitness_accept_unique {ψ outs σ hσ hu} :
      Commits .anyWitness (ψ := ψ) (outs := outs) (.unique σ hσ hu) (.accept σ)

  /-- `anyWitness` accepts any solve witness (even non-unique). -/
  | anyWitness_accept_some {ψ outs σ hσ hnot} :
      Commits .anyWitness (ψ := ψ) (outs := outs) (.some_ σ hσ hnot) (.accept σ)

  /-- `anyWitness` rejects when there is no witness. -/
  | anyWitness_reject_none {ψ outs} :
      Commits .anyWitness (ψ := ψ) (outs := outs) .none .reject

/-- Executable policy. Opaque to `synth`/`check` (pass as `CommitHandler`). -/
def decideCommit (k : PolicyKind) {ψ : ExistsProblem} {outs : List Count} :
    NarrowingEvidence ψ outs → Commit
  | .none => .reject
  | .unique σ _ _ => .accept σ
  | .some_ σ _ _ =>
    match k with
    | .uniqueOnly => .reject
    | .anyWitness => .accept σ

/-- Handler type threaded through algo inference (stable if policies change). -/
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

/-- Build exclusive oracle evidence for `ψ` / `outs`. -/
def gatherNarrowingEvidence (ψ : ExistsProblem) (outs : List Count) :
    NarrowingEvidence ψ outs :=
  match hσ : solve ψ with
  | .unsat | .unknown => .none
  | .witness σ =>
    match hu : unique ψ outs with
    | .unique => .unique σ hσ hu
    | .multiple =>
      .some_ σ hσ (by
        intro h
        rw [hu] at h
        exact (nomatch h))
    | .unknown =>
      .some_ σ hσ (by
        intro h
        rw [hu] at h
        exact (nomatch h))

/-- Success of `forceSubtype`: plain `Sub` or a solve witness (not yet applied to types). -/
inductive ForceOk where
  /-- Plain algorithmic subtype (`checkSub`) succeeded; no solve needed. -/
  | plainSub

  /-- Narrowing via solve; `σ` is the evidence witness (not yet applied to types — PR3b). -/
  | solved (σ : Assign)

@[simp] def Count.isRigidOnly : Count → Bool
  | .lit _ => true
  | .var ⟨.rigid, _⟩ => true
  | .var ⟨.inferable, _⟩ => false
  | .add a b | .mul a b | .min a b | .max a b => a.isRigidOnly && b.isRigidOnly
  | .pred a => a.isRigidOnly

@[simp] def Count.isDemandOK : Count → Bool
  | .var ⟨.inferable, _⟩ => true
  | .mul c (.var ⟨.inferable, _⟩) => c.isRigidOnly
  | .mul (.var ⟨.inferable, _⟩) c => c.isRigidOnly
  | .add (.var ⟨.inferable, _⟩) e => e.isRigidOnly
  | .add e (.var ⟨.inferable, _⟩) => e.isRigidOnly
  | .add (.mul c (.var ⟨.inferable, _⟩)) e => c.isRigidOnly && e.isRigidOnly
  | .add (.mul (.var ⟨.inferable, _⟩) c) e => c.isRigidOnly && e.isRigidOnly
  | c => c.isRigidOnly

@[simp] def Ty.isDemandOK : Ty → Bool
  | .unit | .bool | .tbind _ => true
  | .arrow d c => d.isDemandOK && c.isDemandOK
  | .bl lo hi elem => lo.isDemandOK && hi.isDemandOK && elem.isDemandOK

/-- Algorithmic subtype check (mirrors `Sub`). -/
@[simp] def checkSub (Δ : List Constraint) (t u : Ty) : Bool :=
  match t, u with
  | .unit, .unit | .bool, .bool => true
  | .tbind i, .tbind j => decide (i = j)
  | .arrow a b, .arrow a' b' => checkSub Δ a' a && checkSub Δ b b'
  | .bl lo hi elem, .bl lo' hi' elem' =>
      checkSub Δ elem elem' && lo'.isDemandOK && hi'.isDemandOK &&
        checkValid (Interval.subGoals Δ ⟨lo, hi⟩ ⟨lo', hi'⟩) == .valid
  | _, _ => false
termination_by t.size + u.size
decreasing_by all_goals (simp_wf; simp [Ty.size]; omega)

@[simp] def Count.applyArgs (args : List Count) : Count → Count
  | .lit n => .lit n
  | .var ⟨.rigid, i⟩ => args.getD i (.lit 0)
  | .var v => .var v
  | .add a b => .add (applyArgs args a) (applyArgs args b)
  | .mul a b => .mul (applyArgs args a) (applyArgs args b)
  | .pred a => .pred (applyArgs args a)
  | .min a b => .min (applyArgs args a) (applyArgs args b)
  | .max a b => .max (applyArgs args a) (applyArgs args b)

@[simp] def Count.binderRigidBool (n : Nat) : Count → Bool
  | .lit _ => true
  | .var ⟨.rigid, i⟩ => decide (i < n)
  | .var ⟨.inferable, _⟩ => false
  | .add a b | .mul a b | .min a b | .max a b =>
      binderRigidBool n a && binderRigidBool n b
  | .pred a => binderRigidBool n a

@[simp] def Ty.applyArgs (cargs : List Count) (targs : List Ty) : Ty → Ty
  | .unit => .unit
  | .bool => .bool
  | .tbind i => targs.getD i .unit
  | .arrow d c => .arrow (applyArgs cargs targs d) (applyArgs cargs targs c)
  | .bl lo hi elem =>
      .bl (Count.applyArgs cargs lo) (Count.applyArgs cargs hi) (applyArgs cargs targs elem)

@[simp] def Ty.schemeWFBool (nCounts nTypes : Nat) : Ty → Bool
  | .unit | .bool => true
  | .tbind i => decide (i < nTypes)
  | .bl lo hi elem =>
      Count.binderRigidBool nCounts lo && Count.binderRigidBool nCounts hi &&
        schemeWFBool nCounts nTypes elem
  | .arrow d c => schemeWFBool nCounts nTypes d && schemeWFBool nCounts nTypes c

def BScheme.WF_bool (s : BScheme) : Bool :=
  SchemeBinder.countsThenTypes s.binders &&
    Ty.schemeWFBool s.nCounts s.nTypes s.body

def BScheme.instantiate? (s : BScheme) (args : List SchemeArg) : Option Ty :=
  if s.WF_bool && schemeArgsOK s.binders args then
    some (Ty.applyArgs (schemeCountArgs args) (schemeTyArgs args) s.body)
  else
    none

/-- Fill `none` bounds with fresh inferables starting at `Φ`. -/
@[simp] def fillBound (Φ : Nat) : Option Count → Nat × Count
  | some c => (Φ, c)
  | none => (Φ + 1, cvar .inferable Φ)

@[simp] def fillHoles (Φ : Nat) : AnnoTy → Nat × Ty
  | .unit => (Φ, .unit)
  | .bool => (Φ, .bool)
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
  | .unit | .true | .false | .nil => 1
  | .var _ _ => 1
  | .cons h t => 1 + h.size + t.size
  | .lam _ b => 1 + b.size
  | .app f a => 1 + f.size + a.size
  | .if_ c t e => 1 + c.size + t.size + e.size
  | .anno e _ => 1 + e.size
  | .let_ b e => 1 + b.size + e.size
  | .letScheme _ b e => 1 + b.size + e.size
  | .letRec _ b e => 1 + b.size + e.size
  | .letRecScheme _ b e => 1 + b.size + e.size
  | .matchBL s n c => 1 + s.size + n.size + c.size
  | .matchNil s n => 1 + s.size + n.size
  | .matchCons s c => 1 + s.size + c.size

/-- Force `ty'` into demand `ty`: prefer plain `checkSub`; else gather evidence and
consult `policy`. Returns `none` on failure; on success either `.plainSub` or
`.solved σ` (PR3a does **not** apply `σ` to types yet — PR3b).
`σ` always comes from evidence; a handler that `.accept`s on `.none` is ignored. -/
def forceSubtype (policy : CommitHandler) (Δ : List Constraint) (ty' ty : Ty) :
    Option ForceOk :=
  if checkSub Δ ty' ty then some .plainSub
  else if !ty.isDemandOK then none
  else
    match subtypeProblem Δ ty' ty with
    | none => none
    | some ψ =>
      let outs := ty'.obsBounds
      let e := gatherNarrowingEvidence ψ outs
      match e, policy ψ outs e with
      | .unique σ _ _, .accept _ => some (.solved σ)
      | .some_ σ _ _, .accept _ => some (.solved σ)
      | _, _ => none

/-- Synthesize a type for `e` under commit `policy`.

Returns `some (Φ', τ)` with updated freshness frontier, or `none` on failure
(including when `forceSubtype` rejects per policy — e.g. non-unique under
`uniqueOnly`).

**Uniqueness / commit.** Policy is elaborator-only. Returned `τ` is still not
rewritten under solve witnesses (PR3b); holes may remain in printed types.
-/
def synthWith (policy : CommitHandler) (Φ : Nat) (Δ : List Constraint) (ctx : Ctx) :
    Expr → Option (Nat × Ty)
  | .unit => some (Φ, .unit)
  | .true => some (Φ, .bool)
  | .false => some (Φ, .bool)
  | .nil => none
  | .cons h t =>
    match synthWith policy Φ Δ ctx h with
    | none => none
    | some (Φ₁, ht) =>
      match synthWith policy Φ₁ Δ ctx t with
      | none => none
      | some (Φ₂, tty) =>
        match tty with
        | .bl lo hi elem =>
          if ht == elem then
            some (Φ₂, .bl (.add lo (.lit 1)) (.add hi (.lit 1)) elem)
          else none
        | _ => none
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
    if paramTy.isDemandOK then
      match synthWith policy Φ₁ Δ (.mono paramTy :: ctx) body with
      | some (Φ₂, bodyTy) => some (Φ₂, .arrow paramTy bodyTy)
      | none => none
    else none
  | .app f arg =>
    match synthWith policy Φ Δ ctx f with
    | none => none
    | some (Φ₁, fty) =>
      match fty with
      | .arrow dom cod =>
        match synthWith policy Φ₁ Δ ctx arg with
        | none => none
        | some (Φ₂, aty) =>
          if (forceSubtype policy Δ aty dom).isSome then some (Φ₂, cod) else none
      | _ => none
  | .if_ cond thn els =>
    match synthWith policy Φ Δ ctx cond with
    | none => none
    | some (Φ₁, ct) =>
      match synthWith policy Φ₁ Δ ctx thn with
      | none => none
      | some (Φ₂, tt) =>
        match synthWith policy Φ₂ Δ ctx els with
        | none => none
        | some (Φ₃, et) =>
          match ct with
          | .unit | .bool =>
              match joinBranchTy tt et with
              | some ty => some (Φ₃, ty)
              | none => none
          | _ => none
  | .anno e ann =>
    let (Φ₁, ty) := fillHoles Φ ann
    if e = .nil then
      match ty with
      | .bl lo hi elem =>
        if (forceSubtype policy Δ (.bl (.lit 0) (.lit 0) elem) (.bl lo hi elem)).isSome then
          some (Φ₁, ty)
        else none
      | _ => none
    else
      match synthWith policy Φ₁ Δ ctx e with
      | none => none
      | some (Φ₂, ty') =>
        if (forceSubtype policy Δ ty' ty).isSome then some (Φ₂, ty) else none
  | .let_ bind body =>
    match synthWith policy Φ Δ ctx bind with
    | none => none
    | some (Φ₁, ty1) => synthWith policy Φ₁ Δ (.mono ty1 :: ctx) body
  | .letScheme s bind body =>
    if s.WF_bool then
      match synthWith policy Φ Δ ctx bind with
      | none => none
      | some (Φ₁, tyb) =>
        if (forceSubtype policy Δ tyb s.body).isSome then
          synthWith policy Φ₁ Δ (.scheme s :: ctx) body
        else none
    else none
  | .letRec ann bind body =>
    let (Φ₁, ty) := fillHoles Φ ann
    if ty.isDemandOK then
      match synthWith policy Φ₁ Δ (.mono ty :: ctx) bind with
      | none => none
      | some (Φ₂, tyb) =>
        if (forceSubtype policy Δ tyb ty).isSome then
          synthWith policy Φ₂ Δ (.mono ty :: ctx) body
        else none
    else none
  | .letRecScheme s bind body =>
    if s.WF_bool then
      match synthWith policy Φ Δ (.scheme s :: ctx) bind with
      | none => none
      | some (Φ₁, tyb) =>
        if (forceSubtype policy Δ tyb s.body).isSome then
          synthWith policy Φ₁ Δ (.scheme s :: ctx) body
        else none
    else none
  | .matchBL scrut eNil eCons =>
    match synthWith policy Φ Δ ctx scrut with
    | none => none
    | some (Φ₁, sty) =>
      match sty with
      | .bl lo hi elem =>
        match synthWith policy Φ₁ (Δ ++ nilRefine lo hi) ctx eNil with
        | none => none
        | some (Φ₂, tNil) =>
          match synthWith policy Φ₂ (Δ ++ consRefine hi) (consCtx ctx lo hi elem) eCons with
          | none => none
          | some (Φ₃, tCons) =>
            match joinBranchTy tNil tCons with
            | some ty => some (Φ₃, ty)
            | none => none
      | _ => none
  | .matchNil scrut eNil =>
    match synthWith policy Φ Δ ctx scrut with
    | none => none
    | some (Φ₁, sty) =>
      match sty with
      | .bl lo hi _elem =>
        if checkValid (mustBeEmpty Δ hi) = .valid then
          synthWith policy Φ₁ (Δ ++ nilRefine lo hi) ctx eNil
        else none
      | _ => none
  | .matchCons scrut eCons =>
    match synthWith policy Φ Δ ctx scrut with
    | none => none
    | some (Φ₁, sty) =>
      match sty with
      | .bl lo hi elem =>
        if checkValid (mustBeNonempty Δ lo) = .valid then
          synthWith policy Φ₁ (Δ ++ consRefine hi) (consCtx ctx lo hi elem) eCons
        else none
      | _ => none
termination_by e => e.size + 1
decreasing_by all_goals (simp_wf; simp [Expr.size]; try omega)

/-- Default synth: `uniqueOnly` commit policy (historical elaborator behavior). -/
def synth (Φ : Nat) (Δ : List Constraint) (ctx : Ctx) (e : Expr) : Option (Nat × Ty) :=
  synthWith (CommitHandler.ofKind .uniqueOnly) Φ Δ ctx e

/-- Check `e` against expected `ty` under `policy`.
Bare `nil` is checked directly against a `BL` demand; otherwise synth then force. -/
def checkWith (policy : CommitHandler) (Φ : Nat) (Δ : List Constraint) (ctx : Ctx)
    (e : Expr) (ty : Ty) : Option Nat :=
  match e, ty with
  | .nil, .bl lo hi elem =>
    if (forceSubtype policy Δ (.bl (.lit 0) (.lit 0) elem) (.bl lo hi elem)).isSome then
      some Φ
    else none
  | _, _ =>
    match synthWith policy Φ Δ ctx e with
    | none => none
    | some (Φ', ty') =>
      if (forceSubtype policy Δ ty' ty).isSome then some Φ' else none

/-- Default check: `uniqueOnly` commit policy. -/
def check (Φ : Nat) (Δ : List Constraint) (ctx : Ctx) (e : Expr) (ty : Ty) : Option Nat :=
  checkWith (CommitHandler.ofKind .uniqueOnly) Φ Δ ctx e ty

/-! ### Soundness helpers (partial — synth_sound ladder) -/

/-- Bool `&&` characterization (used throughout §9 soundness). -/
private theorem bool_and_eq_true {a b : Bool} : a && b = true ↔ a = true ∧ b = true := by
  cases a <;> cases b <;> simp

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

theorem Count.isDemandOK_iff {c : Count} : c.isDemandOK = true ↔ Count.DemandOK c :=
  ⟨Count.demandOK_of_isDemandOK, Count.isDemandOK_of_demandOK⟩

@[simp] theorem Ty.isDemandOK_of_demandOK {ty : Ty} (h : Ty.DemandOK ty) : ty.isDemandOK = true := by
  induction h with
  | unit => rfl
  | bool => rfl
  | tbind => rfl
  | arrow _ _ ihd ihc => simp [ihd, ihc]
  | bl hlo hhi helem ih =>
    simp only [Ty.isDemandOK, Count.isDemandOK_of_demandOK hlo, Count.isDemandOK_of_demandOK hhi, ih]; simp

theorem Ty.demandOK_of_isDemandOK {ty : Ty} (h : ty.isDemandOK = true) : Ty.DemandOK ty := by
  induction ty with
  | unit => exact Ty.DemandOK.unit
  | bool => exact Ty.DemandOK.bool
  | tbind i => exact Ty.DemandOK.tbind
  | arrow d c ihd ihc =>
    simp at h
    obtain ⟨hd, hc⟩ := h
    exact Ty.DemandOK.arrow (ihd hd) (ihc hc)
  | bl lo hi elem ih =>
    simp at h
    obtain ⟨hh, helem⟩ := h
    obtain ⟨hlo, hhi⟩ := hh
    exact Ty.DemandOK.bl (Count.demandOK_of_isDemandOK hlo) (Count.demandOK_of_isDemandOK hhi)
      (ih helem)

theorem Ty.isDemandOK_iff {ty : Ty} : ty.isDemandOK = true ↔ Ty.DemandOK ty :=
  ⟨Ty.demandOK_of_isDemandOK, Ty.isDemandOK_of_demandOK⟩

theorem checkSub_sound {Δ t u} (h : checkSub Δ t u = true) : Sub Δ t u := by
  match t, u with
  | .unit, .unit => exact .unit
  | .bool, .bool => exact .bool
  | .tbind i, .tbind j =>
    simp [decide_eq_true_eq] at h
    subst h
    exact .tbind
  | .arrow a b, .arrow a' b' =>
    simp at h
    exact .arrow (checkSub_sound h.1) (checkSub_sound h.2)
  | .bl lo hi elem, .bl lo' hi' elem' =>
    simp at h
    obtain ⟨h12, hvalid⟩ := h
    obtain ⟨h1, hhi'⟩ := h12
    obtain ⟨helem, hlo'⟩ := h1
    exact Sub.bl (Count.demandOK_of_isDemandOK hlo') (Count.demandOK_of_isDemandOK hhi') hvalid
      (checkSub_sound helem)
  | .unit, .arrow _ _ | .unit, .bl _ _ _ | .unit, .tbind _ | .unit, .bool
  | .bool, .unit | .bool, .arrow _ _ | .bool, .bl _ _ _ | .bool, .tbind _
  | .arrow _ _, .unit | .arrow _ _, .bl _ _ _ | .arrow _ _, .tbind _ | .arrow _ _, .bool
  | .bl _ _ _, .unit | .bl _ _ _, .arrow _ _ | .bl _ _ _, .tbind _ | .bl _ _ _, .bool
  | .tbind _, .unit | .tbind _, .arrow _ _ | .tbind _, .bl _ _ _ | .tbind _, .bool =>
    simp at h
termination_by t.size + u.size
decreasing_by all_goals (simp_wf; simp [Ty.size] <;> omega)

/-- After plain `checkSub` fails and demand is OK, a successful force is a solve witness. -/
private theorem forceSubtype_of_some_aux {policy : CommitHandler} {Δ ty' ty ok}
    (hcsf : checkSub Δ ty' ty = false) (hok : ty.isDemandOK = true)
    (h : forceSubtype policy Δ ty' ty = some ok) :
    ∃ σ, ok = ForceOk.solved σ ∧ Ty.DemandOK ty ∧
      ∃ ψ, subtypeProblem Δ ty' ty = some ψ ∧ solve ψ = .witness σ := by
  unfold forceSubtype at h
  have hcs_ne : ¬ checkSub Δ ty' ty = true := by simp [hcsf]
  have hdem_ne : ¬ (!ty.isDemandOK) = true := by simp [hok]
  rw [if_neg hcs_ne, if_neg hdem_ne] at h
  generalize hsp : subtypeProblem Δ ty' ty = sp at h
  cases sp with
  | none => simp at h
  | some ψ =>
    cases hg : gatherNarrowingEvidence ψ ty'.obsBounds with
    | none =>
      simp [hg] at h
    | unique σ hσ hu =>
      cases hpol : policy ψ ty'.obsBounds (NarrowingEvidence.unique σ hσ hu) with
      | accept _ =>
        simp [hg, hpol] at h
        exact ⟨σ, h.symm, Ty.demandOK_of_isDemandOK hok, ψ, rfl, hσ⟩
      | reject =>
        simp [hg, hpol] at h
    | some_ σ hσ hnot =>
      cases hpol : policy ψ ty'.obsBounds (NarrowingEvidence.some_ σ hσ hnot) with
      | accept _ =>
        simp [hg, hpol] at h
        exact ⟨σ, h.symm, Ty.demandOK_of_isDemandOK hok, ψ, rfl, hσ⟩
      | reject =>
        simp [hg, hpol] at h

/-- Success of `forceSubtype` under any handler: plain sub, or a solve witness
from evidence (handler may only accept on `unique` / `some_`; `σ` from evidence). -/
theorem forceSubtype_of_some {policy : CommitHandler} {Δ ty' ty ok}
    (h : forceSubtype policy Δ ty' ty = some ok) :
    (ok = ForceOk.plainSub ∧ checkSub Δ ty' ty = true) ∨
      (∃ σ, ok = ForceOk.solved σ ∧ Ty.DemandOK ty ∧
        ∃ ψ, subtypeProblem Δ ty' ty = some ψ ∧ solve ψ = .witness σ) := by
  by_cases hcs : checkSub Δ ty' ty = true
  · simp [forceSubtype, hcs] at h
    cases h
    exact Or.inl ⟨rfl, hcs⟩
  · have hcsf : checkSub Δ ty' ty = false := eq_false_of_ne_true hcs
    by_cases hokb : ty.isDemandOK = true
    · exact Or.inr (forceSubtype_of_some_aux hcsf hokb h)
    · simp [forceSubtype, hcsf, hokb] at h

theorem forceSubtype_isSome_sub {policy : CommitHandler} {Δ ty' ty}
    (h : (forceSubtype policy Δ ty' ty).isSome = true) :
    Sub Δ ty' ty ∨
      (Ty.DemandOK ty ∧
        ∃ ψ σ, subtypeProblem Δ ty' ty = some ψ ∧ solve ψ = .witness σ) := by
  cases hfs : forceSubtype policy Δ ty' ty with
  | none => simp [hfs] at h
  | some ok =>
    cases forceSubtype_of_some hfs with
    | inl hp =>
      obtain ⟨rfl, hcs⟩ := hp
      exact Or.inl (checkSub_sound hcs)
    | inr hr =>
      obtain ⟨σ, _, hDem, ψ, hψ, hσ⟩ := hr
      exact Or.inr ⟨hDem, ψ, σ, hψ, hσ⟩

/-- uniqueOnly accepts only `.unique` evidence; a solved result carries oracle unique. -/
private theorem forceSubtype_uniqueOnly_solved {Δ ty' ty σ}
    (hcsf : checkSub Δ ty' ty = false) (hok : ty.isDemandOK = true)
    (h : forceSubtype (CommitHandler.ofKind .uniqueOnly) Δ ty' ty = some (ForceOk.solved σ)) :
    Ty.DemandOK ty ∧
      ∃ ψ, subtypeProblem Δ ty' ty = some ψ ∧
        solve ψ = .witness σ ∧ unique ψ ty'.obsBounds = .unique := by
  unfold forceSubtype at h
  have hcs_ne : ¬ checkSub Δ ty' ty = true := by simp [hcsf]
  have hdem_ne : ¬ (!ty.isDemandOK) = true := by simp [hok]
  rw [if_neg hcs_ne, if_neg hdem_ne] at h
  generalize hsp : subtypeProblem Δ ty' ty = sp at h
  cases sp with
  | none => simp at h
  | some ψ =>
    cases hg : gatherNarrowingEvidence ψ ty'.obsBounds with
    | none =>
      simp [hg, CommitHandler.ofKind, decideCommit] at h
    | unique σ' hσ hu =>
      simp [hg, CommitHandler.ofKind, decideCommit] at h
      subst h
      exact ⟨Ty.demandOK_of_isDemandOK hok, ψ, rfl, hσ, hu⟩
    | some_ σ' hσ hnot =>
      simp [hg, CommitHandler.ofKind, decideCommit] at h

/-- Default-policy (`uniqueOnly`) characterization: solve path implies oracle unique. -/
theorem forceSubtype_sub {Δ ty' ty}
    (h : (forceSubtype (CommitHandler.ofKind .uniqueOnly) Δ ty' ty).isSome = true) :
    Sub Δ ty' ty ∨
      (Ty.DemandOK ty ∧
        ∃ ψ σ, subtypeProblem Δ ty' ty = some ψ ∧
          solve ψ = .witness σ ∧ unique ψ ty'.obsBounds = .unique) := by
  cases hfs : forceSubtype (CommitHandler.ofKind .uniqueOnly) Δ ty' ty with
  | none => simp [hfs] at h
  | some ok =>
    by_cases hcs : checkSub Δ ty' ty = true
    · simp [forceSubtype, hcs] at hfs
      cases hfs
      exact Or.inl (checkSub_sound hcs)
    · have hcsf : checkSub Δ ty' ty = false := eq_false_of_ne_true hcs
      by_cases hokb : ty.isDemandOK = true
      · match ok with
        | ForceOk.plainSub =>
          have := forceSubtype_of_some_aux (policy := CommitHandler.ofKind .uniqueOnly) hcsf hokb hfs
          obtain ⟨_, hsolved, _⟩ := this
          cases hsolved
        | ForceOk.solved σ =>
          obtain ⟨hDem, ψ, hψ, hσ, hu⟩ := forceSubtype_uniqueOnly_solved hcsf hokb hfs
          exact Or.inr ⟨hDem, ψ, σ, hψ, hσ, hu⟩
      · simp [forceSubtype, hcsf, hokb] at hfs

theorem Count.binderRigid_of_bool {n : Nat} {c : Count}
    (h : Count.binderRigidBool n c = true) : Count.BinderRigid n c := by
  induction c with
  | lit => trivial
  | var v =>
    cases v with | mk kind idx =>
    cases kind with
    | rigid =>
      simpa [Count.binderRigidBool, decide_eq_true_eq] using h
    | inferable => simp at h
  | add a b iha ihb =>
    simp at h
    exact ⟨iha h.1, ihb h.2⟩
  | mul a b iha ihb =>
    simp at h
    exact ⟨iha h.1, ihb h.2⟩
  | pred a ih =>
    simp at h
    exact ih h
  | min a b iha ihb =>
    simp at h
    exact ⟨iha h.1, ihb h.2⟩
  | max a b iha ihb =>
    simp at h
    exact ⟨iha h.1, ihb h.2⟩

theorem Ty.schemeWF_of_bool {nCounts nTypes : Nat} {ty : Ty}
    (h : Ty.schemeWFBool nCounts nTypes ty = true) : Ty.SchemeWF nCounts nTypes ty := by
  induction ty with
  | unit => trivial
  | bool => trivial
  | tbind i =>
    simpa [Ty.schemeWFBool, decide_eq_true_eq] using h
  | arrow d c ihd ihc =>
    simp at h
    exact ⟨ihd h.1, ihc h.2⟩
  | bl lo hi elem ihelem =>
    simp at h
    exact ⟨Count.binderRigid_of_bool h.1.1, Count.binderRigid_of_bool h.1.2, ihelem h.2⟩


theorem BScheme.wf_of_WF_bool {s : BScheme} (h : s.WF_bool = true) : s.WF := by
  simp [BScheme.WF, BScheme.WF_bool] at h ⊢
  exact ⟨h.1, Ty.schemeWF_of_bool h.2⟩

theorem fillHoles_elab (Φ : Nat) (ann : AnnoTy) :
    AnnoTy.Elab ann (fillHoles Φ ann).2 := by
  induction ann generalizing Φ with
  | unit => simp; exact AnnoTy.Elab.unit
  | bool => simp; exact AnnoTy.Elab.bool
  | tbind i => simp; exact AnnoTy.Elab.tbind
  | arrow d c ih₁ ih₂ =>
    simp
    exact AnnoTy.Elab.arrow (ih₁ _) (ih₂ _)
  | bl lo hi elem =>
    simp
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
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
      exact .var (List.getElem?_eq_getElem hi)
    | inferable => exact False.elim hb
  | add a b iha ihb => exact .add (iha hb.1) (ihb hb.2)
  | mul a b iha ihb => exact .mul (iha hb.1) (ihb hb.2)
  | pred a ih => exact .pred (ih hb)
  | min a b iha ihb => exact .min (iha hb.1) (ihb hb.2)
  | max a b iha ihb => exact .max (iha hb.1) (ihb hb.2)

theorem subst_applyArgs_schemeWF {nCounts nTypes cargs targs t}
    (hb : Ty.SchemeWF nCounts nTypes t) (hcLen : cargs.length = nCounts)
    (htLen : targs.length = nTypes) :
    Ty.Subst cargs targs t (Ty.applyArgs cargs targs t) := by
  induction t with
  | unit => exact .unit
  | bool => exact .bool
  | tbind i =>
    have hi : i < targs.length := by rw [htLen]; exact hb
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
    exact .tbind (List.getElem?_eq_getElem hi)
  | arrow d c ihd ihc =>
    exact .arrow (ihd hb.1) (ihc hb.2)
  | bl lo hi elem ihelem =>
    exact .bl (Count.subst_applyArgs_binderRigid hb.1 hcLen)
      (Count.subst_applyArgs_binderRigid hb.2.1 hcLen)
      (ihelem hb.2.2)

theorem schemeCountArgs_length {bs as}
    (h : schemeArgsOK bs as = true) :
    (schemeCountArgs as).length = (bs.filter (· == .count)).length := by
  induction bs generalizing as with
  | nil =>
    cases as with
    | nil => rfl
    | cons _ _ => simp at h
  | cons b bs ih =>
    cases b with
    | count =>
      cases as with
      | nil => simp at h
      | cons a as =>
        cases a with
        | count c =>
          simp at h ⊢
          exact ih h
        | ty _ => simp at h
    | type =>
      cases as with
      | nil => simp at h
      | cons a as =>
        cases a with
        | count _ => simp at h
        | ty t =>
          simp at h ⊢
          exact ih h

theorem schemeTyArgs_length {bs as}
    (h : schemeArgsOK bs as = true) :
    (schemeTyArgs as).length = (bs.filter (· == .type)).length := by
  induction bs generalizing as with
  | nil =>
    cases as with
    | nil => rfl
    | cons _ _ => simp at h
  | cons b bs ih =>
    cases b with
    | count =>
      cases as with
      | nil => simp at h
      | cons a as =>
        cases a with
        | count c =>
          simp at h ⊢
          exact ih h
        | ty _ => simp at h
    | type =>
      cases as with
      | nil => simp at h
      | cons a as =>
        cases a with
        | count _ => simp at h
        | ty t =>
          simp at h ⊢
          exact ih h

theorem instantiatesOf_instantiate?_sound {s : BScheme} {args : List SchemeArg} {ty : Ty}
    (h : s.instantiate? args = some ty) :
    s.InstantiatesTo args ty := by
  unfold BScheme.instantiate? at h
  split at h
  · rename_i hcond
    cases h
    simp only [Bool.and_eq_true] at hcond
    obtain ⟨hwfb, hok⟩ := hcond
    have hwf := BScheme.wf_of_WF_bool hwfb
    exact .intro hwf hok
      (subst_applyArgs_schemeWF hwf.2
        (schemeCountArgs_length hok)
        (schemeTyArgs_length hok))
  · cases h

/-- Main soundness theorem: algorithmic `synth` implies declarative `TypeOf`. -/
theorem synth_sound {Φ Δ ctx e Φ' ty}
    (h : synth Φ Δ ctx e = some (Φ', ty)) :
    TypeOf Δ ctx e ty := by
  -- Work under the default uniqueOnly policy (`synth` is a thin wrapper).
  simp only [synth] at h
  induction e generalizing Φ Φ' ty ctx Δ with
  | unit =>
    simp [synthWith] at h
    obtain ⟨rfl, rfl⟩ := h
    exact TypeOf.unit
  | true =>
    simp [synthWith] at h
    obtain ⟨rfl, rfl⟩ := h
    exact TypeOf.true
  | false =>
    simp [synthWith] at h
    obtain ⟨rfl, rfl⟩ := h
    exact TypeOf.false
  | nil => simp [synthWith] at h
  | cons head tail ih_head ih_tail =>
    cases hhead : synthWith (CommitHandler.ofKind .uniqueOnly) Φ Δ ctx head with
    | none => simp [synthWith, hhead] at h
    | some Φht =>
      obtain ⟨Φ₁, ht⟩ := Φht
      cases htail : synthWith (CommitHandler.ofKind .uniqueOnly) Φ₁ Δ ctx tail with
      | none => simp [synthWith, hhead, htail] at h
      | some Φtty =>
        obtain ⟨Φ₂, tty⟩ := Φtty
        cases tty with
        | bl lo hi elem =>
          simp [synthWith, hhead, htail, beq_iff_eq] at h
          obtain ⟨heq, rfl, rfl⟩ := h
          subst heq
          exact .cons (ih_head hhead) (ih_tail htail)
        | unit | bool | arrow _ _ | tbind _ =>
          simp [synthWith, hhead, htail] at h
  | var i args =>
    cases hctx : ctx[i]? with
    | none => simp [synthWith, hctx] at h
    | some b =>
      cases b with
      | mono mty =>
        simp [synthWith, hctx] at h
        obtain ⟨ha, rfl, rfl⟩ := h
        have ha' : args = [] := by simpa [List.isEmpty_iff] using ha
        subst ha'
        exact .varMono hctx
      | scheme s =>
        simp [synthWith, hctx] at h
        cases hinst : s.instantiate? args with
        | none => simp [hinst] at h
        | some ity =>
          simp [hinst] at h
          obtain ⟨rfl, rfl⟩ := h
          exact .varScheme hctx (instantiatesOf_instantiate?_sound hinst)
  | lam paramAnn body ih_body =>
    cases hfill : fillHoles Φ paramAnn with
    | mk Φ₁ paramTy =>
      simp [synthWith, hfill] at h
      by_cases hok : paramTy.isDemandOK = true
      · simp [hok] at h
        cases hb : synthWith (CommitHandler.ofKind .uniqueOnly) Φ₁ Δ (.mono paramTy :: ctx) body with
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
    cases hf : synthWith (CommitHandler.ofKind .uniqueOnly) Φ Δ ctx f with
    | none => simp [synthWith, hf] at h
    | some Φf =>
      obtain ⟨Φ₁, fty⟩ := Φf
      cases fty with
      | arrow dom cod =>
        cases ha : synthWith (CommitHandler.ofKind .uniqueOnly) Φ₁ Δ ctx arg with
        | none => simp [synthWith, hf, ha] at h
        | some Φa =>
          obtain ⟨Φ₂, aty⟩ := Φa
          simp [synthWith, hf, ha] at h
          obtain ⟨hfs, rfl, rfl⟩ := h
          cases forceSubtype_sub hfs with
          | inl hsub =>
            exact .app (ih_f hf) (ih_arg ha) hsub
          | inr hr =>
            obtain ⟨hok, ψ, σ, hψ, hσ, _huniq⟩ := hr
            exact .appInfer (ih_f hf) (ih_arg ha) hok hψ hσ
      | unit | bl _ _ _ | tbind _ | bool => simp [synthWith, hf] at h
  | if_ cond thn els ih_c ih_t ih_e =>
    cases hc : synthWith (CommitHandler.ofKind .uniqueOnly) Φ Δ ctx cond with
    | none => simp [synthWith, hc] at h
    | some Φc =>
      obtain ⟨Φ₁, ct⟩ := Φc
      cases ht : synthWith (CommitHandler.ofKind .uniqueOnly) Φ₁ Δ ctx thn with
      | none => simp [synthWith, hc, ht] at h
      | some Φt =>
        obtain ⟨Φ₂, tt⟩ := Φt
        cases he : synthWith (CommitHandler.ofKind .uniqueOnly) Φ₂ Δ ctx els with
        | none => simp [synthWith, hc, ht, he] at h
        | some Φe =>
          obtain ⟨Φ₃, et⟩ := Φe
          simp [synthWith, hc, ht, he] at h
          cases ct with
          | unit =>
            cases hj : joinBranchTy tt et with
            | none => simp [hj] at h
            | some jty =>
              simp [hj] at h
              obtain ⟨rfl, rfl⟩ := h
              exact .ifBL (ih_c hc) (ih_t ht) (ih_e he) hj
          | bool =>
            cases hj : joinBranchTy tt et with
            | none => simp [hj] at h
            | some jty =>
              simp [hj] at h
              obtain ⟨rfl, rfl⟩ := h
              exact .ifBool (ih_c hc) (ih_t ht) (ih_e he) hj
          | arrow _ _ | bl _ _ _ | tbind _ => simp at h
  | anno e ann ih_e =>
    cases hfill : fillHoles Φ ann with
    | mk Φ₁ aty =>
      by_cases hen : e = .nil
      · subst hen
        cases aty with
        | bl lo hi elem =>
          simp [synthWith, hfill] at h
          by_cases hfs :
            (forceSubtype (CommitHandler.ofKind .uniqueOnly) Δ
              (.bl (.lit 0) (.lit 0) elem) (.bl lo hi elem)).isSome = true
          · simp [hfs] at h
            obtain ⟨rfl, rfl⟩ := h
            have helab : AnnoTy.Elab ann (.bl lo hi elem) := by
              have := fillHoles_elab Φ ann
              rwa [hfill] at this
            cases forceSubtype_sub hfs with
            | inl hsub => exact .annoNil helab hsub
            | inr hr =>
              obtain ⟨hok, ψ, σ, hψ, hσ, _huniq⟩ := hr
              exact .annoNilInfer helab hok hψ hσ
          · simp [hfs] at h
        | unit | bool | tbind _ | arrow _ _ => simp [synthWith, hfill] at h
      · cases he : synthWith (CommitHandler.ofKind .uniqueOnly) Φ₁ Δ ctx e with
        | none =>
          simp [synthWith, hfill, he] at h
          exact absurd h.1 hen
        | some Φe =>
          have heq : (e = Expr.nil) = false := by simp [hen]
          simp [synthWith, hfill, he, heq] at h
          obtain ⟨hfs, rfl, rfl⟩ := h
          obtain ⟨Φ₂, ty'⟩ := Φe
          have helab : AnnoTy.Elab ann aty := by
            have := fillHoles_elab Φ ann
            rwa [hfill] at this
          cases forceSubtype_sub hfs with
          | inl hsub =>
            exact .anno helab (ih_e he) hsub
          | inr hr =>
            obtain ⟨hok, ψ, σ, hψ, hσ, _huniq⟩ := hr
            exact .annoInfer helab (ih_e he) hok hψ hσ
  | let_ bind body ih_b ih_body =>
    cases hb : synthWith (CommitHandler.ofKind .uniqueOnly) Φ Δ ctx bind with
    | none => simp [synthWith, hb] at h
    | some Φb =>
      obtain ⟨Φ₁, ty1⟩ := Φb
      simp [synthWith, hb] at h
      exact .letMono (ih_b hb) (ih_body h)
  | letScheme s bind body ih_b ih_body =>
    simp [synthWith] at h
    by_cases hwf : s.WF_bool = true
    · simp [hwf] at h
      cases hb : synthWith (CommitHandler.ofKind .uniqueOnly) Φ Δ ctx bind with
      | none => simp [hb] at h
      | some Φb =>
        obtain ⟨Φ₁, tyb⟩ := Φb
        simp [hb] at h
        obtain ⟨hfs, hbody⟩ := h
        cases forceSubtype_sub hfs with
        | inl hsub =>
          exact .letScheme (BScheme.wf_of_WF_bool hwf) (ih_b hb) hsub (ih_body hbody)
        | inr hr =>
          obtain ⟨hok, ψ, σ, hψ, hσ, _huniq⟩ := hr
          exact .letSchemeInfer (BScheme.wf_of_WF_bool hwf) (ih_b hb) hok hψ hσ
            (ih_body hbody)
    · simp [hwf] at h
  | letRec ann bind body ih_b ih_body =>
    cases hfill : fillHoles Φ ann with
    | mk Φ₁ ty =>
      simp [synthWith, hfill] at h
      by_cases hok : ty.isDemandOK = true
      · simp [hok] at h
        cases hb : synthWith (CommitHandler.ofKind .uniqueOnly) Φ₁ Δ (.mono ty :: ctx) bind with
        | none => simp [hb] at h
        | some Φb =>
          obtain ⟨Φ₂, tyb⟩ := Φb
          simp [hb] at h
          obtain ⟨hfs, hbody⟩ := h
          have helab : AnnoTy.Elab ann ty := by
            have := fillHoles_elab Φ ann
            rwa [hfill] at this
          have hok' : Ty.DemandOK ty := Ty.demandOK_of_isDemandOK hok
          cases forceSubtype_sub hfs with
          | inl hsub =>
            exact .letRec helab hok' (ih_b hb) hsub (ih_body hbody)
          | inr hr =>
            obtain ⟨_, ψ, σ, hψ, hσ, _huniq⟩ := hr
            exact .letRecInfer helab hok' (ih_b hb) hψ hσ (ih_body hbody)
      · simp [hok] at h
  | letRecScheme s bind body ih_b ih_body =>
    simp [synthWith] at h
    by_cases hwf : s.WF_bool = true
    · simp [hwf] at h
      cases hb : synthWith (CommitHandler.ofKind .uniqueOnly) Φ Δ (.scheme s :: ctx) bind with
      | none => simp [hb] at h
      | some Φb =>
        obtain ⟨Φ₁, tyb⟩ := Φb
        simp [hb] at h
        obtain ⟨hfs, hbody⟩ := h
        cases forceSubtype_sub hfs with
        | inl hsub =>
          exact .letRecScheme (BScheme.wf_of_WF_bool hwf) (ih_b hb) hsub (ih_body hbody)
        | inr hr =>
          obtain ⟨hok, ψ, σ, hψ, hσ, _huniq⟩ := hr
          exact .letRecSchemeInfer (BScheme.wf_of_WF_bool hwf) (ih_b hb) hok hψ hσ
            (ih_body hbody)
    · simp [hwf] at h
  | matchBL scrut eNil eCons ih_s ih_n ih_c =>
    cases hs : synthWith (CommitHandler.ofKind .uniqueOnly) Φ Δ ctx scrut with
    | none => simp [synthWith, hs] at h
    | some Φs =>
      obtain ⟨Φ₁, sty⟩ := Φs
      cases sty with
      | bl lo hi elem₀ =>
        cases hn : synthWith (CommitHandler.ofKind .uniqueOnly) Φ₁
            (Δ ++ nilRefine lo hi) ctx eNil with
        | none => simp [synthWith, hs, hn] at h
        | some Φn =>
          obtain ⟨Φ₂, tNil⟩ := Φn
          cases hc : synthWith (CommitHandler.ofKind .uniqueOnly) Φ₂
              (Δ ++ consRefine hi) (consCtx ctx lo hi elem₀) eCons with
          | none => simp [synthWith, hs, hn, hc] at h
          | some Φc =>
            obtain ⟨Φ₃, tCons⟩ := Φc
            simp [synthWith, hs, hn, hc] at h
            cases hj : joinBranchTy tNil tCons with
            | none => simp [hj] at h
            | some jty =>
              simp [hj] at h
              obtain ⟨rfl, rfl⟩ := h
              exact .matchBL_join (ih_s hs) (ih_n hn) (ih_c hc) hj
      | unit | arrow _ _ | tbind _ | bool => simp [synthWith, hs] at h
  | matchNil scrut eNil ih_s ih_n =>
    cases hs : synthWith (CommitHandler.ofKind .uniqueOnly) Φ Δ ctx scrut with
    | none => simp [synthWith, hs] at h
    | some Φs =>
      obtain ⟨Φ₁, sty⟩ := Φs
      cases sty with
      | bl lo hi elem =>
        simp [synthWith, hs] at h
        by_cases hv : checkValid (mustBeEmpty Δ hi) = .valid
        · simp [hv] at h
          exact .matchNil (ih_s hs) hv (ih_n h)
        · simp [hv] at h
      | unit | arrow _ _ | tbind _ | bool => simp [synthWith, hs] at h
  | matchCons scrut eCons ih_s ih_c =>
    cases hs : synthWith (CommitHandler.ofKind .uniqueOnly) Φ Δ ctx scrut with
    | none => simp [synthWith, hs] at h
    | some Φs =>
      obtain ⟨Φ₁, sty⟩ := Φs
      cases sty with
      | bl lo hi elem =>
        simp [synthWith, hs] at h
        by_cases hv : checkValid (mustBeNonempty Δ lo) = .valid
        · simp [hv] at h
          exact .matchCons (ih_s hs) hv (ih_c h)
        · simp [hv] at h
      | unit | arrow _ _ | tbind _ | bool => simp [synthWith, hs] at h

/-- Non-`nil` check is synth-then-force (default uniqueOnly policy). -/
private theorem check_eq_of_ne_nil (he : e ≠ .nil) :
    check Φ Δ ctx e ty =
      match synth Φ Δ ctx e with
      | none => none
      | some (Φ', ty') =>
        if (forceSubtype (CommitHandler.ofKind .uniqueOnly) Δ ty' ty).isSome then some Φ'
        else none := by
  cases e with
  | nil => exact absurd rfl he
  | unit | true | false | cons _ _ | var _ _ | lam _ _ | app _ _ | if_ _ _ _
    | anno _ _ | let_ _ _ | letScheme _ _ _ | letRec _ _ _ | letRecScheme _ _ _
    | matchBL _ _ _ | matchNil _ _ | matchCons _ _ =>
      cases ty <;> simp [check, checkWith, synth]

private theorem check_none_of_synth_none
    (he : e ≠ .nil) (hs : synth Φ Δ ctx e = none) :
    check Φ Δ ctx e ty = none := by
  rw [check_eq_of_ne_nil he, hs]

private theorem check_nil_non_bl_none
    (hty : ty = .unit ∨ ty = .bool ∨ (∃ i, ty = .tbind i) ∨
      (∃ dom cod, ty = .arrow dom cod)) :
    check Φ Δ ctx .nil ty = none := by
  rcases hty with hty | hty | ⟨i, hty⟩ | ⟨dom, cod, hty⟩ <;> subst hty
  · simp [check, checkWith, synthWith]
  · simp [check, checkWith, synthWith]
  · simp [check, checkWith, synthWith]
  · simp [check, checkWith, synthWith]

private theorem check_some_of_synth_force
    (he : e ≠ .nil)
    (hs : synth Φ Δ ctx e = some (Φ', ty'))
    (hfs : (forceSubtype (CommitHandler.ofKind .uniqueOnly) Δ ty' ty).isSome = true) :
    check Φ Δ ctx e ty = some Φ' := by
  rw [check_eq_of_ne_nil he, hs]
  simp [hfs]

private theorem check_none_of_synth_force_false
    (he : e ≠ .nil)
    (hs : synth Φ Δ ctx e = some (Φ', ty'))
    (hfs : ¬ (forceSubtype (CommitHandler.ofKind .uniqueOnly) Δ ty' ty).isSome = true) :
    check Φ Δ ctx e ty = none := by
  rw [check_eq_of_ne_nil he, hs]
  simp [hfs]

private theorem check_nil_bl_some
    (hfs : (forceSubtype (CommitHandler.ofKind .uniqueOnly) Δ
      (.bl (.lit 0) (.lit 0) elem) (.bl lo hi elem)).isSome = true) :
    check Φ Δ ctx .nil (.bl lo hi elem) = some Φ := by
  simp [check, checkWith, hfs]

private theorem check_nil_bl_none
    (hfs : ¬ (forceSubtype (CommitHandler.ofKind .uniqueOnly) Δ
      (.bl (.lit 0) (.lit 0) elem) (.bl lo hi elem)).isSome = true) :
    check Φ Δ ctx .nil (.bl lo hi elem) = none := by
  simp [check, checkWith, hfs]

/-- Algorithmic `check` ⇒ declarative `Check` (not `TypeOf` — no general subsumption). -/
theorem check_sound {Φ Δ ctx e ty Φ'}
    (h : check Φ Δ ctx e ty = some Φ') :
    Check Δ ctx e ty := by
  by_cases hn : e = .nil
  · subst hn
    cases ty with
    | bl lo hi elem =>
      by_cases hfs :
        (forceSubtype (CommitHandler.ofKind .uniqueOnly) Δ
          (.bl (.lit 0) (.lit 0) elem) (.bl lo hi elem)).isSome = true
      · rw [check_nil_bl_some hfs] at h
        injection h with hΦ
        subst hΦ
        cases forceSubtype_sub hfs with
        | inl hsub => exact .nil hsub
        | inr hr =>
          obtain ⟨hok, ψ, σ, hψ, hσ, _huniq⟩ := hr
          exact .nilInfer hok hψ hσ
      · rw [check_nil_bl_none hfs] at h
        cases h
    | unit =>
      rw [check_nil_non_bl_none (Or.inl rfl)] at h
      cases h
    | bool =>
      rw [check_nil_non_bl_none (Or.inr (Or.inl rfl))] at h
      cases h
    | tbind i =>
      rw [check_nil_non_bl_none (Or.inr (Or.inr (Or.inl ⟨i, rfl⟩)))] at h
      cases h
    | arrow dom cod =>
      rw [check_nil_non_bl_none (Or.inr (Or.inr (Or.inr ⟨dom, cod, rfl⟩)))] at h
      cases h
  · cases hs : synth Φ Δ ctx e with
    | none =>
      rw [check_none_of_synth_none hn hs] at h
      cases h
    | some pair =>
      obtain ⟨Φ'', ty'⟩ := pair
      by_cases hfs :
        (forceSubtype (CommitHandler.ofKind .uniqueOnly) Δ ty' ty).isSome = true
      · rw [check_some_of_synth_force hn hs hfs] at h
        injection h with hΦ
        subst hΦ
        cases forceSubtype_sub hfs with
        | inl hsub =>
          exact .ofSub (synth_sound hs) hsub
        | inr hr =>
          obtain ⟨hok, ψ, σ, hψ, hσ, _huniq⟩ := hr
          exact .ofInfer (synth_sound hs) hok hψ hσ
      · rw [check_none_of_synth_force_false hn hs hfs] at h
        cases h

/-! ## 10. Tour / examples -/

namespace Examples

def r (i : Nat) : Count := cvar .rigid i
def x (i : Nat) : Count := cvar .inferable i

/- Need `SchemeWF` proofs for scheme bodies using `r i`. -/
theorem binderRigid_r {n i : Nat} (h : i < n) :
    Count.BinderRigid n (r i) := h

theorem idScheme_wf : Ty.SchemeWF 1 0
    (.arrow (.bl (r 0) (r 0) .unit) (.bl (r 0) (r 0) .unit)) := by
  refine And.intro ?_ ?_
  · exact And.intro (binderRigid_r Nat.zero_lt_one)
      (And.intro (binderRigid_r Nat.zero_lt_one) trivial)
  · exact And.intro (binderRigid_r Nat.zero_lt_one)
      (And.intro (binderRigid_r Nat.zero_lt_one) trivial)

/-! ### Build -/

/-- `∀ {α}. BL 0 0 α` — empty lists are type-polymorphic; bare `Expr.nil` does not synth. -/
def nilScheme : BScheme where
  binders := [.type]
  body := .bl (.lit 0) (.lit 0) (.tbind 0)

theorem nilScheme_wf : nilScheme.WF := by
  dsimp [BScheme.WF, nilScheme, Ty.SchemeWF, Count.BinderRigid]
  decide

example : TypeOf [] [.scheme nilScheme] (.var 0 [.ty .unit])
    (.bl (.lit 0) (.lit 0) .unit) :=
  .varScheme rfl (instantiatesOf_instantiate?_sound (by native_decide))

example : TypeOf [] [.scheme nilScheme]
    (.cons .unit (.var 0 [.ty .unit]))
    (.bl (.add (.lit 0) (.lit 1)) (.add (.lit 0) (.lit 1)) .unit) :=
  .cons .unit (.varScheme rfl (instantiatesOf_instantiate?_sound (by native_decide)))

/-- ### Bound scheme: `∀ {α : Nat}. BL α α → BL α α` -/
def idScheme : BScheme where
  binders := [.count]
  body := .arrow (.bl (r 0) (r 0) .unit) (.bl (r 0) (r 0) .unit)

def idScheme_wf' : idScheme.WF :=
  ⟨by decide, idScheme_wf⟩

example : TypeOf [] [.scheme idScheme] (.var 0 [.count (.lit 3)])
    (.arrow (.bl (.lit 3) (.lit 3) .unit) (.bl (.lit 3) (.lit 3) .unit)) :=
  .varScheme rfl (instantiatesOf_instantiate?_sound (by native_decide))

example : TypeOf [] []
    (.letScheme idScheme
      (.lam (.bl (some (r 0)) (some (r 0)) .unit) (.var 0 []))
      (.var 0 [.count (.lit 3)]))
    (.arrow (.bl (.lit 3) (.lit 3) .unit) (.bl (.lit 3) (.lit 3) .unit)) :=
  .letScheme idScheme_wf'
    (.lam (.bl .known .known) (.bl (.ofRigid .var) (.ofRigid .var) Ty.DemandOK.unit) (.varMono rfl))
    (Sub.refl_of_demandOK (Ty.demandOK_of_schemeWF idScheme_wf (by decide)))
    (.varScheme rfl (instantiatesOf_instantiate?_sound (by native_decide)))

/-- ### Holes: `BL _ _` fills with fresh inferables via `fillHoles`. -/
example : fillHoles 0 (.bl none none .unit) =
    (2, .bl (cvar .inferable 0) (cvar .inferable 1) .unit) := rfl

/-- ### flatMap scheme (positive `lo*lo'` / `hi*hi'`)

Four binders: input list `[a,b]`, per-element lists `[c,d]`; result length
bounds multiply covariantly. -/
def flatMapScheme : BScheme where
  binders := [.count, .count, .count, .count]
  body :=
    .arrow (.bl (r 0) (r 1) .unit)
      (.arrow (.arrow .unit (.bl (r 2) (r 3) .unit))
        (.bl (.mul (r 0) (r 2)) (.mul (r 1) (r 3)) .unit))

theorem flatMapScheme_wf : flatMapScheme.WF := by
  dsimp [BScheme.WF, flatMapScheme, Ty.SchemeWF, Count.BinderRigid, r, cvar]
  decide

example :
    flatMapScheme.InstantiatesTo
      [.count (.lit 2), .count (.lit 5), .count (.lit 3), .count (.lit 4)]
      (.arrow (.bl (.lit 2) (.lit 5) .unit)
        (.arrow (.arrow .unit (.bl (.lit 3) (.lit 4) .unit))
          (.bl (.mul (.lit 2) (.lit 3)) (.mul (.lit 5) (.lit 4)) .unit))) :=
  instantiatesOf_instantiate?_sound (by native_decide)

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
      (.matchBL (.var 0 []) .unit .unit) .unit :=
  .matchBL (.varMono rfl) .unit .unit

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

Synthesizing `BL x (2x)` under weak constraints can yield many models for
escaping `obsBounds`. Declarative `TypeOf` still allows `*Infer` if some witness
exists. Algorithmic `forceSubtype` may reject on `unique` failure (elaborator
policy: annotate or commit) — stricter than the relation. -/
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
