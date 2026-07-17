/-!
# Bounded Lists: a tiny typing sketch

Spine: the declarative judgment `TypeOf` (§5). Each constructor is a usage site;
premises show which bound obligations fire. Oracle `unknown` never appears in a
premise — those cases simply fail to inhabit `TypeOf` and are left to the
implementor (annotate, commit, error, …).

## Picture (bound layer on top of ordinary HM)

* **Compare (∀):** subtype / inhabitability via `checkValid`.
* **Combine:** branch `join` = `min`/`max` (free). Meet is the dual; not needed
  in the tiny rules below.
* **Solve (∃ under ∀):** invent/instantiate inferables; when solutions **escape**
  into an observable type, require **unique outputs** (or an annotation).
* **Demand restriction (contravariant bounds):** at most one inferable, affine in
  it, coefficients/offsets rigid-only — see `Count.DemandOK`. Positive / result
  bounds may still use `n*k` (e.g. `flatMap`).
* **Generalisation:** HM-style `let` — see `TypeOf.letMono` / `letScheme`.
  Scheme packing here is **annotated** (`letScheme s …`): `s` is given and the
  binding must inhabit `s.body`. A real checker may infer `s` by generalising
  unconstrained bound inferables (or ask for an annotation / commit if ambiguous).

Out of scope here: `zip`/`take`/`drop` (need value-level `Nat`s in types),
`splitAt`-style length splitting on inputs, match refinements, indexing APIs,
type-level polymorphism, `unknown` UX.
-/

namespace BLSketch

/-! ## 0. Counts and rigid / inferable -/

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

/-- Full `Var → Nat` (rigid **and** inferable). ∀-validity quantifies over every
slot; ∃∀ fixes inferables via a witness and still ranges over all `Assign`s that
agree on those slots (`agreesOn`). Restricting the domain to rigid-only would
need a “no inferables in this `Count`” side condition on every `eval` — extra
bookkeeping for no real gain in this sketch. -/
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

/-! ## 1. Constraint problems -/

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
  cons       : List Constraint
  deriving Repr

def agreesOn (vs : List Var) (σ τ : Assign) : Prop :=
  ∀ v ∈ vs, σ v = τ v

def ExistsProblem.SolvedBy (ψ : ExistsProblem) (σ : Assign) : Prop :=
  ∀ τ : Assign, agreesOn ψ.inferables σ τ → (∀ c ∈ ψ.cons, c.Holds τ)

def ExistsProblem.Sat (ψ : ExistsProblem) : Prop :=
  ∃ σ, ψ.SolvedBy σ

def sameOutputs (outs : List Count) (σ τ : Assign) : Prop :=
  outs.map (·.eval σ) = outs.map (·.eval τ)

def ExistsProblem.UniqueOutputs (ψ : ExistsProblem) (outs : List Count) : Prop :=
  ∀ σ τ, ψ.SolvedBy σ → ψ.SolvedBy τ → sameOutputs outs σ τ

/-! ## 2. Demand-OK (contravariant bound discipline)

A **demand** bound may mention at most one inferable, **affinely**, with
rigid-only coefficient/offset.

This predicate is **syntactic / canonical-form**: constructors fix operand order
(`c*x` not `x*c`, etc.). Commuted variants are included as extra constructors so
minor surface noise still passes. Deciding whether an *arbitrary* `Count` is
*semantically* equivalent to some `DemandOK` form means normalising (rearrange,
fold, cancel) — possible in principle for the affine fragment, but real work,
and easy to get incomplete. The sketch keeps the cheap syntactic check; a
checker may normalise first, then match.
-/

/-- Built from literals and **rigid** vars only (any ops). -/
inductive Count.RigidOnly : Count → Prop where
  | lit {n} :
    RigidOnly (.lit n)
  | var {i} :
    RigidOnly (.var ⟨.rigid, i⟩)
  | add {a b} :
    RigidOnly a → RigidOnly b → RigidOnly (.add a b)
  | mul {a b} :
    RigidOnly a → RigidOnly b → RigidOnly (.mul a b)
  | pred {a} :
    RigidOnly a → RigidOnly (.pred a)
  | min {a b} :
    RigidOnly a → RigidOnly b → RigidOnly (.min a b)
  | max {a b} :
    RigidOnly a → RigidOnly b → RigidOnly (.max a b)

/-- Legal bound expression in a **demand** position. -/
inductive Count.DemandOK : Count → Prop where
  /-- Fully rigid (no inferables). -/
  | ofRigid {c} :
    Count.RigidOnly c → DemandOK c
  /-- Bare inferable `x`. -/
  | infer {i} :
    DemandOK (.var ⟨.inferable, i⟩)
  /-- `c·x` with rigid coefficient. -/
  | scale {c i} :
    Count.RigidOnly c → DemandOK (.mul c (.var ⟨.inferable, i⟩))
  | scaleComm {c i} :
    Count.RigidOnly c → DemandOK (.mul (.var ⟨.inferable, i⟩) c)
  | offset {i e} :
    Count.RigidOnly e → DemandOK (.add (.var ⟨.inferable, i⟩) e)
  | offsetComm {i e} :
    Count.RigidOnly e → DemandOK (.add e (.var ⟨.inferable, i⟩))
  | aff {c i e} :
    Count.RigidOnly c → Count.RigidOnly e →
    DemandOK (.add (.mul c (.var ⟨.inferable, i⟩)) e)
  | affComm {c i e} :
    Count.RigidOnly c → Count.RigidOnly e →
    DemandOK (.add (.mul (.var ⟨.inferable, i⟩) c) e)

/-! ## 3. Types, schemes, intervals -/

structure Interval where
  lo : Count
  hi : Count
  deriving DecidableEq, Repr

def Interval.subGoals (a b : Interval) : ForallProblem where
  prem  := []
  goals := [⟨b.lo, a.lo⟩, ⟨a.hi, b.hi⟩]

inductive Ty where
  | unit
  | arrow (dom cod : Ty)
  | bl (lo hi : Count)
  deriving DecidableEq, Repr

/-- Bound expressions that appear in an observable type (for uniqueness-of-outputs).
For `BL`, the interval; for arrows, both sides; `unit` contributes nothing. -/
def Ty.obsBounds : Ty → List Count
  | .unit => []
  | .bl lo hi => [lo, hi]
  | .arrow d c => d.obsBounds ++ c.obsBounds

/-- Demanded types: `BL` bounds must be `Count.DemandOK`. -/
inductive Ty.DemandOK : Ty → Prop where
  | unit :
    Ty.DemandOK .unit
  | arrow {d c} :
    Ty.DemandOK d → Ty.DemandOK c → Ty.DemandOK (.arrow d c)
  | bl {lo hi} :
    Count.DemandOK lo → Count.DemandOK hi → Ty.DemandOK (.bl lo hi)

/-- Bound-only scheme. Binder `i` appears in the body as `cvar .rigid i`. -/
structure BScheme where
  binders : Nat
  body    : Ty
  deriving DecidableEq, Repr

/-- Substitution of scheme args for rigid binders `0..args.length`. -/
inductive Count.Subst : List Count → Count → Count → Prop where
  | lit {args n} :
    Subst args (.lit n) (.lit n)
  | var {args i c} :
    args[i]? = some c →
    Subst args (.var ⟨.rigid, i⟩) c
  | add {args a b a' b'} :
    Subst args a a' → Subst args b b' → Subst args (.add a b) (.add a' b')
  | mul {args a b a' b'} :
    Subst args a a' → Subst args b b' → Subst args (.mul a b) (.mul a' b')
  | pred {args a a'} :
    Subst args a a' → Subst args (.pred a) (.pred a')
  | min {args a b a' b'} :
    Subst args a a' → Subst args b b' → Subst args (.min a b) (.min a' b')
  | max {args a b a' b'} :
    Subst args a a' → Subst args b b' → Subst args (.max a b) (.max a' b')

inductive Ty.Subst : List Count → Ty → Ty → Prop where
  | unit {args} :
    Subst args .unit .unit
  | arrow {args d c d' c'} :
    Subst args d d' → Subst args c c' → Subst args (.arrow d c) (.arrow d' c')
  | bl {args lo hi lo' hi'} :
    Count.Subst args lo lo' → Count.Subst args hi hi' →
    Subst args (.bl lo hi) (.bl lo' hi')

/-- `s.InstantiatesTo args ty` — scheme applied to `args` yields `ty`. -/
inductive BScheme.InstantiatesTo : BScheme → List Count → Ty → Prop where
  | intro {s args ty} :
    args.length = s.binders →
    Ty.Subst args s.body ty →
    InstantiatesTo s args ty

inductive Binding where
  | mono   : Ty → Binding
  | scheme : BScheme → Binding
  deriving Repr

abbrev Ctx := List Binding

/-! ## 4. Expressions

No built-in `flatMap` primitive — library ops are ordinary `scheme` bindings
in the context (see `Examples.flatMapScheme`).
-/

inductive Expr where
  | unit
  | nil
  | cons (head tail : Expr)
  | var  (idx : Nat) (boundArgs : List Count)
  | lam  (paramTy : Ty) (body : Expr)
  | app  (fn arg : Expr)
  | if_  (cond thn els : Expr)
  | anno (e : Expr) (ty : Ty)
  /-- Monomorphic let: bind `e1`, then `e2` under `var 0`. Ctx extension only —
  no term-level substitution in the typing rules. -/
  | let_ (binding body : Expr)
  /-- Pack `binding : s.body` as a bound scheme `s`, then type `body` with that
  scheme at `var 0`. `s` is an annotation (inferred gen is a checker policy). -/
  | letScheme (s : BScheme) (binding body : Expr)
  deriving DecidableEq, Repr

/-! ## 5. Oracles

Soundness axioms for non-`unknown` answers. `TypeOf` only ever requires
successful answers; `unknown` / failure ⇒ no derivable typing.
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

opaque checkValid : ForallProblem → ValidVerdict
opaque solve : ExistsProblem → SolveVerdict
opaque unique (ψ : ExistsProblem) (outs : List Count) : UniqueVerdict

axiom checkValid_sound (φ : ForallProblem) :
    match checkValid φ with
    | .valid => φ.Valid
    | .invalid => ¬ φ.Valid
    | .unknown => True

axiom solve_sound (ψ : ExistsProblem) :
    match solve ψ with
    | .witness σ => ψ.SolvedBy σ
    | .unsat => ¬ ψ.Sat
    | .unknown => True

axiom unique_sound (ψ : ExistsProblem) (outs : List Count) :
    match unique ψ outs with
    | .unique => ψ.UniqueOutputs outs
    | .multiple => ¬ ψ.UniqueOutputs outs
    | .unknown => True

/-! ## 6. `Sub` and `TypeOf` -/

/-- Subtyping. On `BL`, the **supertype** (demand) must be `DemandOK`, then
`checkValid` on `lo'/≤/lo` and `hi/≤/hi'`. -/
inductive Sub : Ty → Ty → Prop where
  | unit :
    Sub .unit .unit
  | arrow {a a' b b'} :
    Sub a' a →
    Sub b b' →
    Sub (.arrow a b) (.arrow a' b')
  | bl {lo hi lo' hi'} :
    Count.DemandOK lo' →
    Count.DemandOK hi' →
    checkValid (Interval.subGoals ⟨lo, hi⟩ ⟨lo', hi'⟩) = .valid →
    Sub (.bl lo hi) (.bl lo' hi')

/-- **The judgment to read.** -/
inductive TypeOf : Ctx → Expr → Ty → Prop where
  | unit {ctx} :
    TypeOf ctx .unit .unit

  | nil {ctx} :
    TypeOf ctx .nil (.bl (.lit 0) (.lit 0))

  | cons {ctx head tail lo hi} :
    TypeOf ctx head .unit →
    TypeOf ctx tail (.bl lo hi) →
    TypeOf ctx (.cons head tail) (.bl (.add lo (.lit 1)) (.add hi (.lit 1)))

  | varMono {ctx i ty} :
    ctx[i]? = some (.mono ty) →
    TypeOf ctx (.var i []) ty

  | varScheme {ctx i s args ty} :
    ctx[i]? = some (.scheme s) →
    s.InstantiatesTo args ty →
    TypeOf ctx (.var i args) ty

  | lam {ctx paramTy body bodyTy} :
    Ty.DemandOK paramTy →
    TypeOf (.mono paramTy :: ctx) body bodyTy →
    TypeOf ctx (.lam paramTy body) (.arrow paramTy bodyTy)

  /-- App: subtype argument into domain (`DemandOK` + `checkValid` via `Sub`). -/
  | app {ctx f arg argTy retTy argTy'} :
    TypeOf ctx f (.arrow argTy retTy) →
    TypeOf ctx arg argTy' →
    Sub argTy' argTy →
    TypeOf ctx (.app f arg) retTy

  /-- Branch join — pure `min`/`max`, no oracle. -/
  | ifBL {ctx cond thn els lo₁ hi₁ lo₂ hi₂} :
    TypeOf ctx cond .unit →
    TypeOf ctx thn (.bl lo₁ hi₁) →
    TypeOf ctx els (.bl lo₂ hi₂) →
    TypeOf ctx (.if_ cond thn els) (.bl (.min lo₁ lo₂) (.max hi₁ hi₂))

  /-- Ascription when subtype already holds (demand must be `DemandOK` via `Sub`). -/
  | anno {ctx e ty ty'} :
    TypeOf ctx e ty' →
    Sub ty' ty →
    TypeOf ctx (.anno e ty) ty

  /-- Ascription that **solves** inferables in the synthesized type `ty'`.
  Uniqueness is checked on `ty'.obsBounds` — the bound exprs in the observable
  synthesized type — **not** on the witness `σ` itself. So `a*b = 12` with
  obsBounds `[a*b, a*b]` can be unique-as-outputs even when `(a,b)` is not.
  `ψ` packs the ∃∀ constraints (informal in this sketch). -/
  | annoInfer {ctx e ty ty' ψ σ} :
    TypeOf ctx e ty' →
    Ty.DemandOK ty →
    solve ψ = .witness σ →
    unique ψ ty'.obsBounds = .unique →
    Sub ty' ty →
    TypeOf ctx (.anno e ty) ty

  /-- Mono let — extend ctx; body refers to the binding as `var 0`. -/
  | letMono {ctx e1 e2 ty1 ty2} :
    TypeOf ctx e1 ty1 →
    TypeOf (.mono ty1 :: ctx) e2 ty2 →
    TypeOf ctx (.let_ e1 e2) ty2

  /-- Pack an annotated bound scheme. Typing uses only ctx extension (de Bruijn
  for *terms*); Count-level binders in `s.body` are just rigid `Count` vars —
  no term-subst machinery beyond `InstantiatesTo` at use sites. -/
  | letScheme {ctx s e1 e2 bodyTy} :
    TypeOf ctx e1 s.body →
    TypeOf (.scheme s :: ctx) e2 bodyTy →
    TypeOf ctx (.letScheme s e1 e2) bodyTy

/-! ## 7. Examples -/

namespace Examples

def r (i : Nat) : Count := cvar .rigid i
def x (i : Nat) : Count := cvar .inferable i

example : TypeOf [] .nil (.bl (.lit 0) (.lit 0)) :=
  .nil

example : TypeOf [] (.cons .unit .nil)
    (.bl (.add (.lit 0) (.lit 1)) (.add (.lit 0) (.lit 1))) :=
  .cons .unit .nil

/-- `∀ α. BL α α → BL α α`. -/
def idScheme : BScheme where
  binders := 1
  body := .arrow (.bl (r 0) (r 0)) (.bl (r 0) (r 0))

example : TypeOf [.scheme idScheme] (.var 0 [.lit 3])
    (.arrow (.bl (.lit 3) (.lit 3)) (.bl (.lit 3) (.lit 3))) :=
  .varScheme rfl <| .intro rfl <|
    .arrow (.bl (.var rfl) (.var rfl)) (.bl (.var rfl) (.var rfl))

/-- Create a scheme with `letScheme`, then instantiate — no pre-loaded ctx. -/
example : TypeOf []
    (.letScheme idScheme
      (.lam (.bl (r 0) (r 0)) (.var 0 []))
      (.var 0 [.lit 3]))
    (.arrow (.bl (.lit 3) (.lit 3)) (.bl (.lit 3) (.lit 3))) :=
  .letScheme
    (.lam (.bl (.ofRigid .var) (.ofRigid .var)) (.varMono rfl))
    (.varScheme rfl <| .intro rfl <|
      .arrow (.bl (.var rfl) (.var rfl)) (.bl (.var rfl) (.var rfl)))

/-- `∀ n k. BL n n → (Unit → BL k k) → BL (n*k) (n*k)` — library scheme, not a
language primitive. Positive `n*k` is allowed; a demand of shape `a*b` with two
inferables would fail `Count.DemandOK`. -/
def flatMapScheme : BScheme where
  binders := 2
  body :=
    .arrow (.bl (r 0) (r 0))
      (.arrow (.arrow .unit (.bl (r 1) (r 1)))
        (.bl (.mul (r 0) (r 1)) (.mul (r 0) (r 1))))

/-- Instantiate `flatMap` at `n=2`, `k=6`. -/
example :
    flatMapScheme.InstantiatesTo [.lit 2, .lit 6]
      (.arrow (.bl (.lit 2) (.lit 2))
        (.arrow (.arrow .unit (.bl (.lit 6) (.lit 6)))
          (.bl (.mul (.lit 2) (.lit 6)) (.mul (.lit 2) (.lit 6))))) := by
  refine .intro rfl ?_
  refine .arrow ?_ ?_
  · exact .bl (.var rfl) (.var rfl)
  · refine .arrow ?_ ?_
    · refine .arrow .unit ?_
      exact .bl (.var (by native_decide)) (.var (by native_decide))
    · exact .bl (.mul (.var rfl) (.var (by native_decide)))
        (.mul (.var rfl) (.var (by native_decide)))

/-- Escape ambiguity (prose): result `BL x (2x)` under `5 ≤ x` has many
incomparable outputs — `unique` fails, `annoInfer` does not apply. -/
def linearAmbiguousProblem : ExistsProblem where
  inferables := [⟨.inferable, 0⟩]
  cons := [⟨.lit 5, x 0⟩]

def linearAmbiguousOuts : List Count :=
  [x 0, .mul (.lit 2) (x 0)]

end Examples

end BLSketch
