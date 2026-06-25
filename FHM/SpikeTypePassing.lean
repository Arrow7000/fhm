import FHM.Core

/-! # SPIKE: type-passing rescues the case type-erasure cannot (`probeV`)

`Core`'s `PreservationProbe` section proves that literal subject reduction is FALSE
under type-erasure. The witness: the well-typed
`let f : (∀a. a → a) = (λ(x : a). x) in f` steps — via the *erased* let-reduction,
which carries no type — to `λ(x : a). x`, a term whose annotation is the dangling
scoped type variable `a = bvar 0` (it had referenced the now-consumed `∀a`). That
reduct is untypeable, which is the whole reason `Core` re-bases dynamic safety on
type-erased terms.

This spike shows the **type-passing** alternative dissolves that very counterexample.
The use site records the instantiation (`f [Int]`), and the consuming reduction does
**type-beta**: it substitutes the concrete `Int` through the annotation
(`Ty.openWith [Int]`) instead of dropping it. The reduct is then `λ(x : Int). x` —
locally closed and well-typed at `Int → Int`. So subject reduction holds for the
exact configuration erasure breaks.

Part A (here) confirms the *mechanism* on Core's own `TypeOfHM`/`Ty.openWith`, with
no parallel reimplementation. Part B (next) builds the minimal `var i tyArgs` /
generalising-binder / type-beta-in-`substN` fragment and proves witness-level subject
reduction over an actual reduction relation — that's where the term-depth-vs-
type-depth de Bruijn bookkeeping gets nailed down. -/

namespace SpikeTypePassing

/-- The reduct produced by the **erased** let-reduction: `λ(x : a). x`, where the
    scoped type variable `a` is `bvar 0` — it referenced the `∀a` that the
    let-reduction just consumed, and erasure left nothing in its place. -/
def erasureReduct : Expr := .lambda (some (.bvar 0)) (.var 0)

/-- The reduct produced by the **type-passing** let-reduction, where the use site
    recorded `f [Int]`. Type-beta substitutes `Int` for the scheme's `bvar 0`
    through the annotation; `Ty.openWith [Int]` is exactly that substitution. -/
def typePassingReduct : Expr := .lambda (some (.prim .int)) (.var 0)

/-- The type-passing reduct is *literally* the erased reduct with its annotation
    type-beta'd at `[Int]`: the scheme's `bvar 0` becomes the concrete `Int`. This
    is the one-line essence of "substitute the type, don't delete it". -/
theorem typePassing_is_typeBeta :
    typePassingReduct
      = .lambda (some (Ty.openWith [.prim .int] (.bvar 0))) (.var 0) := by
  rfl

/-- (1) The **erased** reduct is untypeable at any type: the `lambda` rule pins the
    parameter type to the annotation `bvar 0`, yet also demands it be locally closed
    (`ContainsBvarsUpTo 0`), which `bvar 0` is not. (This is the same argument as
    `Core`'s private `probe_reduct_untypeable`, restated here so the spike is
    self-contained.) -/
theorem erasureReduct_untypeable (ctx : Ctx) (τ : Ty) :
    ¬ TypeOfHM ctx erasureReduct τ := by
  intro h
  cases h with
  | lambda hpc hann _ _ =>
    rw [hann _ rfl] at hpc
    cases hpc with
    | bvar hlt => omega

/-- (2) The **type-passing** reduct *is* typeable, at `Int → Int`. With the scoped
    variable resolved to the concrete `Int` by type-beta, the annotation is locally
    closed and the lambda is just the identity on `Int`. Together with (1) this is the
    subject-reduction payoff: the reduct of the well-typed source stays well-typed
    under type-passing, exactly where it fails under erasure. -/
theorem typePassingReduct_typeable :
    TypeOfHM ⟨[], []⟩ typePassingReduct (.arrow (.prim .int) (.prim .int)) := by
  refine TypeOfHM.lambda ?_ (fun T h => Option.some.inj h) rfl ?_
  · exact .prim
  · exact TypeOfHM.var (tyArgs := []) rfl (by intro t ht; cases ht) .prim

/-! ## Part B: a minimal type-passing fragment with an actual reduction relation

Part A confirmed the *principle* pointwise. Part B builds the smallest fragment that
has the structure type-passing actually needs — `var i tyArgs` (explicit type
application), a generalising binder `tlet` (the implicit `Λ`), and **type-beta folded
into term substitution** — and proves witness-level subject reduction over a real
`Step` relation. The point is to exercise the de Bruijn bookkeeping where term-binder
depth meets type-binder depth, which is the part a naive implementation gets wrong.

We reuse Core's `Ty`, `ContainsBvarsUpTo`, `InstantiatesBy`, `Ty.openVars`,
`FreshNames`, and `PolyTy` verbatim. -/

/-- Type-passing terms. `var` carries explicit type arguments; `tlet` is a
    (non-recursive) generalising let whose `paramCount` type variables appear as
    type-`bvar`s in the rhs's annotations — the implicit `Λ`. -/
inductive TExpr where
  | var (i : Nat) (tyArgs : List Ty)
  | lam (ann : Ty) (body : TExpr)
  | app (fn arg : TExpr)
  | tlet (paramCount : Nat) (rhs body : TExpr)

/-- Open type-`bvar`s at level `d`: `bvar (d+i) ↦ Ts[i]`, leaving `bvar < d` (bound
    by inner schemes) and out-of-range `bvar`s untouched. `d = 0` is the
    types-analogue of `Ty.openVars`. -/
def openTyFrom (d : Nat) (Ts : List Ty) (ty : Ty) : Ty :=
  ty.instantiate (fun i => if i < d then .bvar i else (Ts[i - d]?).getD (.bvar i))

/-- Type-beta through a term's annotations: substitute `Ts` for the variables of the
    *outermost* (depth-`d`) scheme. A `lam` is a TERM binder — it binds no type
    variables, so it leaves `d` unchanged (this is the key bookkeeping point). A
    `tlet`'s rhs sits under that let's `paramCount` extra type binders, so `d` grows
    by `paramCount` there. -/
def TExpr.instTyAux (d : Nat) (Ts : List Ty) : TExpr → TExpr
  | .var i tyArgs => .var i (tyArgs.map (openTyFrom d Ts))
  | .lam ann body => .lam (openTyFrom d Ts ann) (body.instTyAux d Ts)
  | .app f a => .app (f.instTyAux d Ts) (a.instTyAux d Ts)
  | .tlet n rhs body => .tlet n (rhs.instTyAux (d + n) Ts) (body.instTyAux d Ts)

/-- Type-beta at the outermost scheme (depth 0). -/
def TExpr.instTy (Ts : List Ty) (e : TExpr) : TExpr := e.instTyAux 0 Ts

/-- Term-variable shifting. `tyArgs` are types, untouched by term-var shifting. -/
def TExpr.shiftFrom (threshold n : Nat) : TExpr → TExpr
  | .var i tyArgs => if i < threshold then .var i tyArgs else .var (i + n) tyArgs
  | .lam ann body => .lam ann (body.shiftFrom (threshold + 1) n)
  | .app f a => .app (f.shiftFrom threshold n) (a.shiftFrom threshold n)
  | .tlet m rhs body => .tlet m (rhs.shiftFrom threshold n) (body.shiftFrom (threshold + 1) n)

/-- Capture-avoiding term substitution **with type-beta folded in**: when a use
    `var (k+j) Ts` is replaced by the bound value `vs[j]`, that value's outermost
    scheme is instantiated at the use's own `Ts` (type-beta) before the usual shift.
    This single clause is the type-passing reduction's defining move — every use gets
    its own instantiation, and scoped variables are *substituted*, never dropped. -/
def TExpr.substN (k : Nat) (vs : List TExpr) : TExpr → TExpr
  | .var i tyArgs =>
      if i < k then .var i tyArgs
      else if h : i - k < vs.length then ((vs[i - k]).instTy tyArgs).shiftFrom 0 k
      else .var (i - vs.length) tyArgs
  | .lam ann body => .lam ann (body.substN (k + 1) vs)
  | .app f a => .app (f.substN k vs) (a.substN k vs)
  | .tlet m rhs body => .tlet m (rhs.substN k vs) (body.substN (k + 1) vs)

/-- Call-by-value type-passing reduction (the two rules the witness needs). -/
inductive Step : TExpr → TExpr → Prop
  | beta {ann body v} :
      Step (.app (.lam ann body) v) (body.substN 0 [v])
  /-- Generalising-let reduction: substitute the rhs into the body, type-beta'ing it
      at each use's recorded type arguments (via `substN`). -/
  | letReduce {n rhs body} :
      Step (.tlet n rhs body) (body.substN 0 [rhs])

/-- Type-passing typing. `var`/`lam`/`app` mirror `TypeOfHM`. `tlet` is Core's
    cofinite let-generalisation, with the rhs *opened by type-beta* (`instTy` at fresh
    `fvar`s) — the static counterpart of `letReduce`'s type-beta. -/
inductive THasType : List PolyTy → TExpr → Ty → Prop
  | var {env i polyTy tyArgs ty} :
      env[i]? = some polyTy →
      (∀ t ∈ tyArgs, ContainsBvarsUpTo 0 t) →
      InstantiatesBy tyArgs polyTy.body ty →
      THasType env (.var i tyArgs) ty
  | lam {env ann body bodyTy} :
      ContainsBvarsUpTo 0 ann →
      THasType (PolyTy.mkTrivial ann :: env) body bodyTy →
      THasType env (.lam ann body) (.arrow ann bodyTy)
  | app {env f a argTy retTy} :
      THasType env f (.arrow argTy retTy) →
      THasType env a argTy →
      THasType env (.app f a) retTy
  | tlet {env n rhs body bodyTy} {schemeBody : Ty} {L : List Nat} :
      ContainsBvarsUpTo n schemeBody →
      (∀ Xs : List Nat, FreshNames L n Xs →
          THasType env (rhs.instTy (Xs.map Ty.fvar)) (Ty.openVars Xs schemeBody)) →
      THasType (⟨n, schemeBody⟩ :: env) body bodyTy →
      THasType env (.tlet n rhs body) bodyTy

/-! ### The `probeV` witness, now over the type-passing reduction

`let (f : ∀a. a → a) = (λ(x : a). x) in (f [Int])`, with the scoped `a = bvar 0`. -/

/-- `λ(x : a). x`, with `a = bvar 0` (the enclosing `tlet`'s scheme variable). -/
def witnessRhs : TExpr := .lam (.bvar 0) (.var 0 [])

/-- `let f = (λ(x:a).x) in f [Int]` — the body instantiates `f` at `Int`. -/
def witnessSource : TExpr := .tlet 1 witnessRhs (.var 0 [.prim .int])

/-- The reduct: `λ(x : Int). x` — the scoped `a` resolved to `Int` by type-beta. -/
def witnessReduct : TExpr := .lam (.prim .int) (.var 0 [])

/-- The source steps to the reduct, and `letReduce`'s `substN` computes *exactly*
    `λ(x:Int).x` — the type-beta substituted `Int` for `a` through the annotation. -/
theorem witnessSource_steps : Step witnessSource witnessReduct := Step.letReduce

/-- The source is well-typed at `Int → Int` (polymorphic recursion-free, but the
    scoped variable is live in the rhs's annotation). -/
theorem witnessSource_typeable :
    THasType [] witnessSource (.arrow (.prim .int) (.prim .int)) := by
  refine THasType.tlet (schemeBody := .arrow (.bvar 0) (.bvar 0)) (L := []) ?_ ?_ ?_
  · exact .arrow (.bvar (by omega)) (.bvar (by omega))
  · intro Xs hfresh
    obtain ⟨X, rfl⟩ : ∃ X, Xs = [X] := List.length_eq_one_iff.mp hfresh.length
    show THasType [] (TExpr.lam (Ty.fvar X) (TExpr.var 0 [])) (Ty.arrow (Ty.fvar X) (Ty.fvar X))
    refine THasType.lam .fvar ?_
    exact THasType.var (polyTy := PolyTy.mkTrivial (.fvar X)) (tyArgs := []) rfl
      (by intro t ht; cases ht) .fvar
  · exact THasType.var (polyTy := ⟨1, Ty.arrow (Ty.bvar 0) (Ty.bvar 0)⟩)
      (tyArgs := [Ty.prim .int]) rfl
      (by intro t ht; simp only [List.mem_singleton] at ht; subst ht; exact .prim)
      (.arrow (.bvar rfl) (.bvar rfl))

/-- The reduct is well-typed at the same type. -/
theorem witnessReduct_typeable :
    THasType [] witnessReduct (.arrow (.prim .int) (.prim .int)) := by
  refine THasType.lam .prim ?_
  exact THasType.var (polyTy := PolyTy.mkTrivial (.prim .int)) (tyArgs := []) rfl
    (by intro t ht; cases ht) .prim

/-- **Subject reduction holds for the witness under type-passing.** The well-typed
    source steps to a term that is still well-typed at the same type — precisely the
    property that is FALSE for this configuration under type-erasure (Part A's
    `erasureReduct_untypeable`). The de Bruijn bookkeeping (type-beta in `substN`,
    `lam` leaving the type-depth unchanged) goes through. -/
theorem witness_subject_reduction :
    THasType [] witnessSource (.arrow (.prim .int) (.prim .int))
      ∧ Step witnessSource witnessReduct
      ∧ THasType [] witnessReduct (.arrow (.prim .int) (.prim .int)) :=
  ⟨witnessSource_typeable, witnessSource_steps, witnessReduct_typeable⟩

/-! ### A second witness that actually exercises the shift

In witness 1 the use of `f` sits at de Bruijn index 0, so `substN`'s `shiftFrom 0 k`
runs at `k = 0` (a no-op). Here the use sits **under a `λ(y : Int)`**, so the
type-beta'd value must be shifted past that binder (`shiftFrom 0 1`). This is the
exact spot where term-binder depth and the type instantiation interact, and where a
botched de Bruijn implementation would corrupt the result. -/

/-- `let f = (λ(x:a).x) in (λ(y:Int). f [Int])`. -/
def witness2Source : TExpr :=
  .tlet 1 witnessRhs (.lam (.prim .int) (.var 1 [.prim .int]))

/-- `λ(y:Int). λ(x:Int). x` — `f`'s value, type-beta'd at `Int` and shifted under `λy`. -/
def witness2Reduct : TExpr := .lam (.prim .int) (.lam (.prim .int) (.var 0 []))

/-- `letReduce`'s `substN` shifts the type-beta'd value past the inner `λy`
    (`shiftFrom 0 1`) and produces exactly `witness2Reduct`. -/
theorem witness2_steps : Step witness2Source witness2Reduct := Step.letReduce

theorem witness2Source_typeable :
    THasType [] witness2Source
      (.arrow (.prim .int) (.arrow (.prim .int) (.prim .int))) := by
  refine THasType.tlet (schemeBody := .arrow (.bvar 0) (.bvar 0)) (L := []) ?_ ?_ ?_
  · exact .arrow (.bvar (by omega)) (.bvar (by omega))
  · intro Xs hfresh
    obtain ⟨X, rfl⟩ : ∃ X, Xs = [X] := List.length_eq_one_iff.mp hfresh.length
    show THasType [] (TExpr.lam (Ty.fvar X) (TExpr.var 0 [])) (Ty.arrow (Ty.fvar X) (Ty.fvar X))
    refine THasType.lam .fvar ?_
    exact THasType.var (polyTy := PolyTy.mkTrivial (.fvar X)) (tyArgs := []) rfl
      (by intro t ht; cases ht) .fvar
  · refine THasType.lam .prim ?_
    exact THasType.var (polyTy := ⟨1, Ty.arrow (Ty.bvar 0) (Ty.bvar 0)⟩)
      (tyArgs := [Ty.prim .int]) rfl
      (by intro t ht; simp only [List.mem_singleton] at ht; subst ht; exact .prim)
      (.arrow (.bvar rfl) (.bvar rfl))

theorem witness2Reduct_typeable :
    THasType [] witness2Reduct
      (.arrow (.prim .int) (.arrow (.prim .int) (.prim .int))) := by
  refine THasType.lam .prim (THasType.lam .prim ?_)
  exact THasType.var (polyTy := PolyTy.mkTrivial (.prim .int)) (tyArgs := []) rfl
    (by intro t ht; cases ht) .prim

/-- Subject reduction holds for the under-a-binder witness too — the `shiftFrom 0 1`
    in `substN` lines up. -/
theorem witness2_subject_reduction :
    THasType [] witness2Source (.arrow (.prim .int) (.arrow (.prim .int) (.prim .int)))
      ∧ Step witness2Source witness2Reduct
      ∧ THasType [] witness2Reduct (.arrow (.prim .int) (.arrow (.prim .int) (.prim .int))) :=
  ⟨witness2Source_typeable, witness2_steps, witness2Reduct_typeable⟩

end SpikeTypePassing
