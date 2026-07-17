/-!
# Bounded Lists — rigorous toy sketch

Declarative bound layer on top of ordinary HM. Judgment: `TypeOf Δ Γ e τ`.

## Contract

If `TypeOf Δ Γ e τ` is derivable, every bound obligation for this toy language
appears as a premise in that derivation:

| Job | Where it shows up |
| --- | --- |
| **Compare (∀)** | `Sub` / inhabitability → `checkValid` under assumptions `Δ` |
| **Join** | `ifBL`, `matchBL` result bounds via `min`/`max` (free) |
| **Meet inhabitability** | not an `Expr` form — when one value faces several BL demands, discharge `checkValid (inhabitProblem Δ (Interval.meet …))` |
| **Solve + unique outputs** | `annoInfer` via `subtypeProblem Δ ty' ty` |
| **Demand discipline** | `Count.DemandOK` / `Ty.DemandOK` on demanded types |
| **Bound schemes** | `letScheme` (annotated pack) + `varScheme` (`InstantiatesTo`); bodies are WF (only rigid binders `0..n-1`) |
| **Match refinement** | `matchBL` / `matchNil` / `matchCons` extend `Δ`; single-branch forms need a ∀-proof the other case is impossible (`hi ≤ 0` or `1 ≤ lo`) |

Oracle answers other than success (`unknown` / `invalid` / `unsat` / `multiple`)
simply yield **no** derivation — policy (annotate / commit / error) is outside
this relation.

**Declarative (like Core `TypeOfHM`):** the relation existentially picks types,
scheme args, and solve witnesses; it does not return a substitution. An
algorithmic checker would invent inferables and compute `σ`.

**Algorithmic layer (§9):** `synth` / `check` thread freshness frontier `Φ`
(as in `InferW`); `AnnoTy` allows `BL _ _` holes filled by `fillHoles`.
`synth_sound` is stated and `sorry`'d for the next session.

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
  | arrow (dom cod : Ty)
  | bl (lo hi : Count)
  deriving DecidableEq, Repr

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
  | bl {lo hi} : Count.DemandOK lo → Count.DemandOK hi → Ty.DemandOK (.bl lo hi)

/-! ### Annotation types — holes only in bound positions

`AnnoTy` mirrors `Ty`, but each BL bound is `Option Count` (`none` = `_`).
Holes become fresh inferables in the algorithm (`fillHoles`), or any `Count`
existentially in declarative `AnnoTy.Elab`.
-/

inductive AnnoTy where
  | unit
  | arrow (dom cod : AnnoTy)
  | bl (lo hi : Option Count)
  deriving DecidableEq, Repr

def AnnoTy.ofTy : Ty → AnnoTy
  | .unit => .unit
  | .arrow d c => .arrow (ofTy d) (ofTy c)
  | .bl lo hi => .bl (some lo) (some hi)

inductive AnnoTy.ElabBound : Option Count → Count → Prop where
  | known {c} : ElabBound (some c) c
  | hole {c} : ElabBound none c

inductive AnnoTy.Elab : AnnoTy → Ty → Prop where
  | unit : Elab .unit .unit
  | arrow {d c d' c'} :
    Elab d d' → Elab c c' → Elab (.arrow d c) (.arrow d' c')
  | bl {lo hi lo' hi'} :
    ElabBound lo lo' → ElabBound hi hi' → Elab (.bl lo hi) (.bl lo' hi')

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
  | .bl lo hi => Count.BinderRigid n lo ∧ Count.BinderRigid n hi
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
  | arrow {args d c d' c'} :
    Subst args d d' → Subst args c c' → Subst args (.arrow d c) (.arrow d' c')
  | bl {args lo hi lo' hi'} :
    Count.Subst args lo lo' → Count.Subst args hi hi' →
    Subst args (.bl lo hi) (.bl lo' hi')

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

/-! ## 5. Oracles (TCB) -/

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
  .mono .unit :: .mono (.bl (.pred lo) (.pred hi)) :: ctx

/-! ## 7. `Sub` and `TypeOf` -/

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

  | ifBL {Δ ctx cond thn els lo₁ hi₁ lo₂ hi₂} :
    TypeOf Δ ctx cond .unit →
    TypeOf Δ ctx thn (.bl lo₁ hi₁) →
    TypeOf Δ ctx els (.bl lo₂ hi₂) →
    TypeOf Δ ctx (.if_ cond thn els) (.bl (.min lo₁ lo₂) (.max hi₁ hi₂))

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

  | letScheme {Δ ctx s e1 e2 bodyTy} :
    s.WF →
    TypeOf Δ ctx e1 s.body →
    TypeOf Δ (.scheme s :: ctx) e2 bodyTy →
    TypeOf Δ ctx (.letScheme s e1 e2) bodyTy

  /-- Exhaustive match on `BL lo hi`.
  * nil: `Δ ++ nilRefine lo hi` (`lo ≤ 0`; `hi` not forced to `0`)
  * cons: `Δ ++ consRefine hi`; `consCtx` binds head / tail -/
  | matchBL {Δ ctx e eNil eCons lo hi ty} :
    TypeOf Δ ctx e (.bl lo hi) →
    TypeOf (Δ ++ nilRefine lo hi) ctx eNil ty →
    TypeOf (Δ ++ consRefine hi) (consCtx ctx lo hi) eCons ty →
    TypeOf Δ ctx (.matchBL e eNil eCons) ty

  /-- Nil-only: require `hi ≤ 0` under `Δ` (empty is forced). -/
  | matchNil {Δ ctx e eNil lo hi ty} :
    TypeOf Δ ctx e (.bl lo hi) →
    checkValid (mustBeEmpty Δ hi) = .valid →
    TypeOf (Δ ++ nilRefine lo hi) ctx eNil ty →
    TypeOf Δ ctx (.matchNil e eNil) ty

  /-- Cons-only: require `1 ≤ lo` under `Δ` (non-empty is forced). -/
  | matchCons {Δ ctx e eCons lo hi ty} :
    TypeOf Δ ctx e (.bl lo hi) →
    checkValid (mustBeNonempty Δ lo) = .valid →
    TypeOf (Δ ++ consRefine hi) (consCtx ctx lo hi) eCons ty →
    TypeOf Δ ctx (.matchCons e eCons) ty

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
  | ifBL hcond hthn hels ih₁ ih₂ ih₃ => exact .ifBL ih₁ ih₂ ih₃
  | anno helab he hsub ih => exact .anno helab ih hsub
  | annoInfer helab he hok hψ hσ huniq ih => exact .annoInfer helab ih hok hψ hσ huniq
  | letMono he₁ he₂ ih₁ ih₂ => exact .letMono ih₁ ih₂
  | letScheme hwf he₁ he₂ ih₁ ih₂ => exact .letScheme hwf ih₁ ih₂
  | matchBL he heNil heCons ih₁ ih₂ ih₃ =>
    refine .matchBL ih₁ ih₂ ?_
    rw [consCtx_append]
    exact ih₃
  | matchNil he hvalid heNil ih₁ ih₂ => exact .matchNil ih₁ hvalid ih₂
  | matchCons he hvalid heCons ih₁ ih₂ =>
    refine .matchCons ih₁ hvalid ?_
    rw [consCtx_append]
    exact ih₂

/-- `ofTy` elaborates to itself (no holes). -/
theorem AnnoTy.elab_ofTy (t : Ty) : AnnoTy.Elab (AnnoTy.ofTy t) t := by
  induction t with
  | unit => exact .unit
  | arrow _ _ ihd ihc => exact .arrow ihd ihc
  | bl lo hi => exact .bl .known .known

/-! ## 9. Algorithmic inference (freshness frontier `Φ`)

Same pattern as `InferW`: thread `Φ : Nat` as the next inferable index.
`fillHoles` turns `AnnoTy` blanks into `cvar .inferable Φ`.
Oracle calls are the opaque `checkValid` / `solve` / `unique`; failure/`multiple`/`unknown`
⇒ `none` (require annotation).
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
  | .arrow d c => d.isDemandOK && c.isDemandOK
  | .bl lo hi => lo.isDemandOK && hi.isDemandOK

/-- Algorithmic subtype check (mirrors `Sub`). -/
def checkSub (Δ : List Constraint) (t u : Ty) : Bool :=
  match t, u with
  | .unit, .unit => true
  | .arrow a b, .arrow a' b' => checkSub Δ a' a && checkSub Δ b b'
  | .bl lo hi, .bl lo' hi' =>
      lo'.isDemandOK && hi'.isDemandOK &&
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
  | .arrow d c => .arrow (applyArgs args d) (applyArgs args c)
  | .bl lo hi => .bl (Count.applyArgs args lo) (Count.applyArgs args hi)

def Count.binderRigidBool (n : Nat) : Count → Bool
  | .lit _ => true
  | .var ⟨.rigid, i⟩ => decide (i < n)
  | .var ⟨.inferable, _⟩ => false
  | .add a b | .mul a b | .min a b | .max a b =>
      binderRigidBool n a && binderRigidBool n b
  | .pred a => binderRigidBool n a

def Ty.binderRigidBool (n : Nat) : Ty → Bool
  | .unit => true
  | .bl lo hi => Count.binderRigidBool n lo && Count.binderRigidBool n hi
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
  | .arrow d c =>
      let (Φ₁, d') := fillHoles Φ d
      let (Φ₂, c') := fillHoles Φ₁ c
      (Φ₂, .arrow d' c')
  | .bl lo hi =>
      let (Φ₁, lo') := fillBound Φ lo
      let (Φ₂, hi') := fillBound Φ₁ hi
      (Φ₂, .bl lo' hi')

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
Fails on `multiple` / `unknown` / `unsat` (annotation required). -/
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

/-- Synthesize a type. Returns updated freshness frontier and type. -/
partial def synth (Φ : Nat) (Δ : List Constraint) (ctx : Ctx) : Expr → Option (Nat × Ty)
  | .unit => some (Φ, .unit)
  | .nil => some (Φ, .bl (.lit 0) (.lit 0))
  | .cons h t => do
      let (Φ₁, ht) ← synth Φ Δ ctx h
      let (Φ₂, tty) ← synth Φ₁ Δ ctx t
      match ht, tty with
      | .unit, .bl lo hi => some (Φ₂, .bl (.add lo (.lit 1)) (.add hi (.lit 1)))
      | _, _ => none
  | .var i args =>
      match ctx[i]? with
      | some (.mono ty) =>
          if args.isEmpty then some (Φ, ty) else none
      | some (.scheme s) => (Φ, ·) <$> s.instantiate? args
      | none => none
  | .lam paramAnn body => do
      let (Φ₁, paramTy) := fillHoles Φ paramAnn
      if !paramTy.isDemandOK then none
      else do
        let (Φ₂, bodyTy) ← synth Φ₁ Δ (.mono paramTy :: ctx) body
        some (Φ₂, .arrow paramTy bodyTy)
  | .app f arg => do
      let (Φ₁, fty) ← synth Φ Δ ctx f
      match fty with
      | .arrow dom cod => do
          let (Φ₂, aty) ← synth Φ₁ Δ ctx arg
          if forceSubtype Δ aty dom then some (Φ₂, cod) else none
      | _ => none
  | .if_ cond thn els => do
      let (Φ₁, ct) ← synth Φ Δ ctx cond
      let (Φ₂, tt) ← synth Φ₁ Δ ctx thn
      let (Φ₃, et) ← synth Φ₂ Δ ctx els
      match ct, tt, et with
      | .unit, .bl lo₁ hi₁, .bl lo₂ hi₂ =>
          some (Φ₃, .bl (.min lo₁ lo₂) (.max hi₁ hi₂))
      | _, _, _ => none
  | .anno e ann => do
      let (Φ₁, ty) := fillHoles Φ ann
      let (Φ₂, ty') ← synth Φ₁ Δ ctx e
      if forceSubtype Δ ty' ty then some (Φ₂, ty) else none
  | .let_ bind body => do
      let (Φ₁, ty1) ← synth Φ Δ ctx bind
      synth Φ₁ Δ (.mono ty1 :: ctx) body
  | .letScheme s bind body => do
      if !s.WF_bool then none
      else do
        let (Φ₁, tyb) ← synth Φ Δ ctx bind
        if forceSubtype Δ tyb s.body then
          synth Φ₁ Δ (.scheme s :: ctx) body
        else none
  | .matchBL scrut eNil eCons => do
      let (Φ₁, sty) ← synth Φ Δ ctx scrut
      match sty with
      | .bl lo hi => do
          let (Φ₂, tNil) ← synth Φ₁ (Δ ++ nilRefine lo hi) ctx eNil
          let (Φ₃, tCons) ← synth Φ₂ (Δ ++ consRefine hi) (consCtx ctx lo hi) eCons
          if tNil == tCons then some (Φ₃, tNil) else none
      | _ => none
  | .matchNil scrut eNil => do
      let (Φ₁, sty) ← synth Φ Δ ctx scrut
      match sty with
      | .bl lo hi =>
          if checkValid (mustBeEmpty Δ hi) != .valid then none
          else synth Φ₁ (Δ ++ nilRefine lo hi) ctx eNil
      | _ => none
  | .matchCons scrut eCons => do
      let (Φ₁, sty) ← synth Φ Δ ctx scrut
      match sty with
      | .bl lo hi =>
          if checkValid (mustBeNonempty Δ lo) != .valid then none
          else synth Φ₁ (Δ ++ consRefine hi) (consCtx ctx lo hi) eCons
      | _ => none

/-- Check `e` against expected `ty` (synth then `forceSubtype`). -/
def check (Φ : Nat) (Δ : List Constraint) (ctx : Ctx) (e : Expr) (ty : Ty) :
    Option Nat := do
  let (Φ', ty') ← synth Φ Δ ctx e
  if forceSubtype Δ ty' ty then some Φ' else none

/-- Soundness of synthesis (next session). -/
theorem synth_sound {Φ Δ ctx e Φ' ty}
    (h : synth Φ Δ ctx e = some (Φ', ty)) :
    TypeOf Δ ctx e ty := by
  sorry

/-! ## 10. Tour / examples -/

namespace Examples

def r (i : Nat) : Count := cvar .rigid i
def x (i : Nat) : Count := cvar .inferable i

/- Need `BinderRigid` proofs for scheme bodies using `r i`. -/
theorem binderRigid_r {n i : Nat} (h : i < n) :
    Count.BinderRigid n (r i) := h

theorem idScheme_wf : Ty.BinderRigid 1
    (.arrow (.bl (r 0) (r 0)) (.bl (r 0) (r 0))) :=
  ⟨⟨binderRigid_r (Nat.zero_lt_one), binderRigid_r (Nat.zero_lt_one)⟩,
   ⟨binderRigid_r (Nat.zero_lt_one), binderRigid_r (Nat.zero_lt_one)⟩⟩

/-- ### Build -/
example : TypeOf [] [] .nil (.bl (.lit 0) (.lit 0)) := .nil

example : TypeOf [] [] (.cons .unit .nil)
    (.bl (.add (.lit 0) (.lit 1)) (.add (.lit 0) (.lit 1))) :=
  .cons .unit .nil

/-- ### Bound scheme: `∀ α. BL α α → BL α α` -/
def idScheme : BScheme where
  binders := 1
  body := .arrow (.bl (r 0) (r 0)) (.bl (r 0) (r 0))

example : idScheme.WF := idScheme_wf

example : TypeOf [] [.scheme idScheme] (.var 0 [.lit 3])
    (.arrow (.bl (.lit 3) (.lit 3)) (.bl (.lit 3) (.lit 3))) :=
  .varScheme rfl <| .intro idScheme_wf rfl <|
    .arrow (.bl (.var rfl) (.var rfl)) (.bl (.var rfl) (.var rfl))

example : TypeOf [] []
    (.letScheme idScheme
      (.lam (.bl (some (r 0)) (some (r 0))) (.var 0 []))
      (.var 0 [.lit 3]))
    (.arrow (.bl (.lit 3) (.lit 3)) (.bl (.lit 3) (.lit 3))) :=
  .letScheme idScheme_wf
    (.lam (.bl .known .known) (.bl (.ofRigid .var) (.ofRigid .var)) (.varMono rfl))
    (.varScheme rfl <| .intro idScheme_wf rfl <|
      .arrow (.bl (.var rfl) (.var rfl)) (.bl (.var rfl) (.var rfl)))

/-- ### Holes: `BL _ _` fills with fresh inferables via `fillHoles`. -/
example : fillHoles 0 (.bl none none) =
    (2, .bl (cvar .inferable 0) (cvar .inferable 1)) := rfl

/-- ### flatMap scheme (positive `n*k`) -/
def flatMapScheme : BScheme where
  binders := 2
  body :=
    .arrow (.bl (r 0) (r 0))
      (.arrow (.arrow .unit (.bl (r 1) (r 1)))
        (.bl (.mul (r 0) (r 1)) (.mul (r 0) (r 1))))

theorem flatMapScheme_wf : flatMapScheme.WF := by
  dsimp [BScheme.WF, flatMapScheme, Ty.BinderRigid, Count.BinderRigid, r, cvar]
  decide

example :
    flatMapScheme.InstantiatesTo [.lit 2, .lit 6]
      (.arrow (.bl (.lit 2) (.lit 2))
        (.arrow (.arrow .unit (.bl (.lit 6) (.lit 6)))
          (.bl (.mul (.lit 2) (.lit 6)) (.mul (.lit 2) (.lit 6))))) := by
  refine .intro flatMapScheme_wf rfl ?_
  refine .arrow ?_ ?_
  · exact .bl (.var rfl) (.var rfl)
  · refine .arrow ?_ ?_
    · exact .arrow .unit (.bl (.var (by native_decide)) (.var (by native_decide)))
    · exact .bl (.mul (.var rfl) (.var (by native_decide)))
        (.mul (.var rfl) (.var (by native_decide)))

/-- ### Match refines `Δ`

Scrutinee `BL lo hi`. Nil branch sees `lo ≤ 0` (and `0 ≤ hi`); cons sees `1 ≤ hi`
and types the tail at `pred`. Example: return `unit` in both branches. -/
example (lo hi : Count) :
    TypeOf [] [.mono (.bl lo hi)]
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
