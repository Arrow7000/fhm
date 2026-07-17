/-!
# Bounded Lists: a tiny typing sketch

Spine: the declarative judgment `TypeOf` (§5). Each constructor is a usage site;
premises show which bound obligations fire. Oracle `unknown` never appears in a
premise — those cases simply fail to inhabit `TypeOf` and are left to the
implementor (annotate, commit, error, …).

## Picture (bound layer on top of ordinary HM)

* **Compare (∀):** subtype / inhabitability via `checkValid`, under assumption
  set `Δ` (first index of `TypeOf` / `Sub`).
* **Combine:** branch `join` = `min`/`max` (free). **Meet** inhabitability =
  `checkValid (inhabitProblem Δ (Interval.meet …))`.
* **Solve (∃ under ∀):** `annoInfer` uses `subtypeProblem Δ ty' ty` as `ψ`, then
  `solve` + `unique` on `ty'.obsBounds`.
* **Demand restriction (contravariant bounds):** at most one inferable, affine in
  it, coefficients/offsets rigid-only — see `Count.DemandOK`. Positive / result
  bounds may still use `n*k` (e.g. `flatMap`).
* **Generalisation:** HM-style `let` — see `TypeOf.letMono` / `letScheme`.
  Scheme packing here is **annotated** (`letScheme s …`): `s` is given and the
  binding must inhabit `s.body`. A real checker may infer `s` by generalising
  unconstrained bound inferables (or ask for an annotation / commit if ambiguous).

Term de Bruijn: under `lam`/`let`, extend `Ctx` at the front; bodies are already
written in that scope (`var 0` = new binding). No `Expr.subst` in `TypeOf`.

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
  /-- Ambient assumptions (threaded from `Δ` in `TypeOf` / `Sub`). -/
  prem       : List Constraint := []
  cons       : List Constraint
  deriving Repr

def agreesOn (vs : List Var) (σ τ : Assign) : Prop :=
  ∀ v ∈ vs, σ v = τ v

/-- Witness: for every assignment agreeing on inferables, premises imply goals. -/
def ExistsProblem.SolvedBy (ψ : ExistsProblem) (σ : Assign) : Prop :=
  ∀ τ : Assign, agreesOn ψ.inferables σ τ →
    (∀ c ∈ ψ.prem, c.Holds τ) → (∀ c ∈ ψ.cons, c.Holds τ)

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

def Interval.subGoals (Δ : List Constraint) (a b : Interval) : ForallProblem where
  prem  := Δ
  goals := [⟨b.lo, a.lo⟩, ⟨a.hi, b.hi⟩]

/-- Candidate meet; inhabitability is a ∀-check (see `inhabitProblem`). -/
def Interval.meet (a b : Interval) : Interval :=
  ⟨.max a.lo b.lo, .min a.hi b.hi⟩

def inhabitProblem (Δ : List Constraint) (i : Interval) : ForallProblem where
  prem  := Δ
  goals := [⟨i.lo, i.hi⟩]

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
  | .bl lo hi => lo.inferVars ++ hi.inferVars
  | .arrow d c => d.inferVars ++ c.inferVars

def Ty.size : Ty → Nat
  | .unit => 1
  | .bl _ _ => 1
  | .arrow d c => 1 + d.size + c.size

/-- Structural subtype obligations (`none` if shapes mismatch). -/
def subConstraints (ty' ty : Ty) : Option (List Constraint) :=
  match ty', ty with
  | .unit, .unit => some []
  | .bl lo hi, .bl lo' hi' => some [⟨lo', lo⟩, ⟨hi, hi'⟩]
  | .arrow a b, .arrow a' b' =>
      match subConstraints a' a, subConstraints b b' with
      | some cs₁, some cs₂ => some (cs₁ ++ cs₂)
      | _, _ => none
  | _, _ => none
termination_by ty'.size + ty.size
decreasing_by all_goals (simp_wf; simp [Ty.size]; omega)

/-- ∃∀ problem for “choose inferables so `ty' <: ty` under assumptions `Δ`. -/
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
  no term-level substitution in the typing rules. Under a new binder, indices in
  an *already-built* body are already scoped: `var 0` = this binding, `var 1` =
  previous `var 0`. Lookup in the extended `Ctx` does the “shift”; we do not
  rewrite the body. (Rewriting would be needed only if you wrapped a term that
  was typed in the *outer* scope without rebuilding it — not how these ASTs work.) -/
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

/-! ## 6. `Sub` and `TypeOf`

`Δ` is the ambient assumption set (bound premises): subtype/`lo ≤ hi` checks
are ∀-validity *under* `Δ`. Empty `Δ` is the closed case used in most examples.
-/

/-- Subtyping under assumptions `Δ`. -/
inductive Sub (Δ : List Constraint) : Ty → Ty → Prop where
  | unit :
    Sub Δ .unit .unit
  | arrow {a a' b b'} :
    Sub Δ a' a →
    Sub Δ b b' →
    Sub Δ (.arrow a b) (.arrow a' b')
  | bl {lo hi lo' hi'} :
    Count.DemandOK lo' →
    Count.DemandOK hi' →
    checkValid (Interval.subGoals Δ ⟨lo, hi⟩ ⟨lo', hi'⟩) = .valid →
    Sub Δ (.bl lo hi) (.bl lo' hi')

/-- **The judgment to read.** First index: assumption set `Δ`. -/
inductive TypeOf : List Constraint → Ctx → Expr → Ty → Prop where
  | unit {Δ ctx} :
    TypeOf Δ ctx .unit .unit

  | nil {Δ ctx} :
    TypeOf Δ ctx .nil (.bl (.lit 0) (.lit 0))

  | cons {Δ ctx head tail lo hi} :
    TypeOf Δ ctx head .unit →
    TypeOf Δ ctx tail (.bl lo hi) →
    TypeOf Δ ctx (.cons head tail) (.bl (.add lo (.lit 1)) (.add hi (.lit 1)))

  | varMono {Δ ctx i ty} :
    ctx[i]? = some (.mono ty) →
    TypeOf Δ ctx (.var i []) ty

  | varScheme {Δ ctx i s args ty} :
    ctx[i]? = some (.scheme s) →
    s.InstantiatesTo args ty →
    TypeOf Δ ctx (.var i args) ty

  /-- Body is typed in an extended ctx; de Bruijn indices in `body` are already
  relative to that scope (`var 0` = param). -/
  | lam {Δ ctx paramTy body bodyTy} :
    Ty.DemandOK paramTy →
    TypeOf Δ (.mono paramTy :: ctx) body bodyTy →
    TypeOf Δ ctx (.lam paramTy body) (.arrow paramTy bodyTy)

  | app {Δ ctx f arg argTy retTy argTy'} :
    TypeOf Δ ctx f (.arrow argTy retTy) →
    TypeOf Δ ctx arg argTy' →
    Sub Δ argTy' argTy →
    TypeOf Δ ctx (.app f arg) retTy

  | ifBL {Δ ctx cond thn els lo₁ hi₁ lo₂ hi₂} :
    TypeOf Δ ctx cond .unit →
    TypeOf Δ ctx thn (.bl lo₁ hi₁) →
    TypeOf Δ ctx els (.bl lo₂ hi₂) →
    TypeOf Δ ctx (.if_ cond thn els) (.bl (.min lo₁ lo₂) (.max hi₁ hi₂))

  | anno {Δ ctx e ty ty'} :
    TypeOf Δ ctx e ty' →
    Sub Δ ty' ty →
    TypeOf Δ ctx (.anno e ty) ty

  /-- Solve inferables so `ty' <: ty` under `Δ`, with unique observable outputs.
  `ψ` is exactly `subtypeProblem Δ ty' ty`. -/
  | annoInfer {Δ ctx e ty ty' ψ σ} :
    TypeOf Δ ctx e ty' →
    Ty.DemandOK ty →
    subtypeProblem Δ ty' ty = some ψ →
    solve ψ = .witness σ →
    unique ψ ty'.obsBounds = .unique →
    TypeOf Δ ctx (.anno e ty) ty

  | letMono {Δ ctx e1 e2 ty1 ty2} :
    TypeOf Δ ctx e1 ty1 →
    TypeOf Δ (.mono ty1 :: ctx) e2 ty2 →
    TypeOf Δ ctx (.let_ e1 e2) ty2

  | letScheme {Δ ctx s e1 e2 bodyTy} :
    TypeOf Δ ctx e1 s.body →
    TypeOf Δ (.scheme s :: ctx) e2 bodyTy →
    TypeOf Δ ctx (.letScheme s e1 e2) bodyTy

/-! ## 7. Examples -/

namespace Examples

def r (i : Nat) : Count := cvar .rigid i
def x (i : Nat) : Count := cvar .inferable i

example : TypeOf [] [] .nil (.bl (.lit 0) (.lit 0)) :=
  .nil

example : TypeOf [] [] (.cons .unit .nil)
    (.bl (.add (.lit 0) (.lit 1)) (.add (.lit 0) (.lit 1))) :=
  .cons .unit .nil

/-- `∀ α. BL α α → BL α α`. -/
def idScheme : BScheme where
  binders := 1
  body := .arrow (.bl (r 0) (r 0)) (.bl (r 0) (r 0))

example : TypeOf [] [.scheme idScheme] (.var 0 [.lit 3])
    (.arrow (.bl (.lit 3) (.lit 3)) (.bl (.lit 3) (.lit 3))) :=
  .varScheme rfl <| .intro rfl <|
    .arrow (.bl (.var rfl) (.var rfl)) (.bl (.var rfl) (.var rfl))

/-- Create a scheme with `letScheme`, then instantiate — no pre-loaded ctx. -/
example : TypeOf [] []
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
