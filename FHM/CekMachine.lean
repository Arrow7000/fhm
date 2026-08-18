import FHM.Core

/-! # CEK machine — a type-erasing environment machine for FHM

This is the target semantics of the CEK migration (`briefs/cekmachine-design.md`).
The machine is **type-erasing**: it never inspects types. The term's annotation
slots (`lambda paramAnn`, `letIn ann`, `letRec anns`) and the `var` node's `tyArgs`
are inert payload — the machine runs on any syntactically well-formed `Expr`.
Values carry their *own* annotations (`thunk ann`, `recclo anns`) only so the
*typing* invariant (`ValTyped`) can reconstruct the static scheme; they are still
inert at reduction time.

The point (vs. the old `SmallStep.Step` substitution semantics): because the machine
carries an *environment*, an invented generalisation (a `letRec` mono member's
scheme) never needs to be written into the term as a Λ. `TypeOfHM` — the declarative,
decoration-blind relation — is the machine's typing relation; `TypeOfElabHM` and
elaboration do not exist here.

Evaluation order matches the old `Step`: call-by-value for `app`/`match_`
(argument and scrutinee are reduced first), call-by-name for `letIn`/`letRec`
(a binding is bound as a *thunk*, forced on each use).

State = `(value environment, continuation, term)` in `eval` mode, or
`(value, continuation)` in `ret` mode. Values are closures/thunks/rec-closures/
ctor chains/primitives; they never leak into `Expr`.

-/

namespace CekMachine

open SmallStep

/-! ## Machine data -/

/-- A runtime value. Closures and thunks capture their environment; a `recclo` is
    one member of a recursive group (it stores the whole group's bindings and its
    index, so forcing it rebuilds the recursive environment without cyclic data). -/
inductive Val
  | prim (p : PrimLitExpr)
  | primOp (op : PrimBinOp)
  /-- A partially-applied primitive operator (one operand supplied, one missing). -/
  | primOpApp (op : PrimBinOp) (v : Val)
  /-- A lambda value: `body` is the lambda body (its `var 0` is the parameter). -/
  | lam (body : Expr) (E : List Val)
  /-- A call-by-name thunk: an unevaluated term, forced on use. Carries the `letIn`
      annotation (inert at runtime) so `ValTyped` can type it at its scheme. -/
  | thunk (ann : Option PolyTy) (e : Expr) (E : List Val)
  /-- Member `j` of a mutually-recursive group `bindings` (captures the outer env).
      Carries the group's `anns` (inert) for typing. -/
  | recclo (anns : List (Option PolyTy)) (bindings : List Expr) (E : List Val) (j : Nat)
  /-- A constructor value applied to zero or more (already-evaluated) arguments. -/
  | ctorV (name : CtorName) (args : List Val)

/-- The machine's value environment (de Bruijn-indexed). -/
abbrev VEnv := List Val

/-- δ-result for a saturated primop application to two literal operands. The
    comparison ops emit the prelude `Bool` constructor (their well-typedness in a
    context is a *typing*-side fact, exactly as in the old `deltaIntLt`). -/
def PrimBinOp.delta (op : PrimBinOp) (a b : PrimLitExpr) : Option Val :=
  match op, a, b with
  | .intAdd, .int m, .int n => some (.prim (.int (m + n)))
  | .intSub, .int m, .int n => some (.prim (.int (m - n)))
  | .intLt,  .int m, .int n => some (.ctorV (if m < n then ⟨"True"⟩ else ⟨"False"⟩) [])
  | .charLt, .char m, .char n => some (.ctorV (if m.toNat < n.toNat then ⟨"True"⟩ else ⟨"False"⟩) [])
  | _, _, _ => none

/-- A continuation frame. `KontTyped` below gives each frame its typing meaning:
    `appArg E arg k` awaits the function value, then evaluates `arg`; `appFun fv k`
    awaits the argument value, then applies `fv`; `matchSel E branches k` awaits the
    scrutinee value, then selects a branch. -/
inductive Kont
  | nil
  | appArg (E : VEnv) (arg : Expr) (k : Kont)
  | appFun (fv : Val) (k : Kont)
  | matchSel (E : VEnv) (branches : List (MatchPattern × Expr)) (k : Kont)

/-- A machine state: `eval` is "evaluate term `e` in env `E`, continue with `k`";
    `ret` is "pass value `v` to continuation `k`". -/
inductive State
  | eval (E : VEnv) (e : Expr) (k : Kont)
  | ret (v : Val) (k : Kont)

/-- Build the recursive environment for a `letRec`: member `j` is a `recclo` that,
    when forced, rebuilds this same environment (no cyclic *data* — each `recclo`
    stores the finite `bindings`/`E`). -/
def bindGroup (anns : List (Option PolyTy)) (bindings : List Expr) (E : VEnv) : VEnv :=
  (List.range bindings.length).map (fun j => .recclo anns bindings E j) ++ E

/-- Values that can serve as a match scrutinee *without* being a constructor chain:
    literals, primops, and closures. (Thunks and rec-closures are forced by `force`
    / `forceRecclo` before any match rule sees them.) -/
def IsNonCtorVal : Val → Prop
  | .prim _ => True
  | .primOp _ => True
  | .primOpApp _ _ => True
  | .lam _ _ => True
  | .thunk _ _ _ => False
  | .recclo _ _ _ _ => False
  | .ctorV _ _ => False

/-! ## Reduction -/

/-- Small-step reduction of the CEK machine. Call-by-value for `app`/`match_`;
    call-by-name (thunks) for `letIn`/`letRec`. -/
inductive StepM : State → State → Prop
  | primLit {E p k} :
      StepM (.eval E (.primLit p) k) (.ret (.prim p) k)
  | primBinOp {E op k} :
      StepM (.eval E (.primBinOp op) k) (.ret (.primOp op) k)
  | ctor {E name k} :
      StepM (.eval E (.ctor name) k) (.ret (.ctorV name []) k)
  | lambda {E ann body k} :
      StepM (.eval E (.lambda ann body) k) (.ret (.lam body E) k)
  | var {E i tyArgs k} (h : i < E.length) :
      StepM (.eval E (.var i tyArgs) k) (.ret (E.get ⟨i, h⟩) k)
  | app {E f a k} :
      StepM (.eval E (.app f a) k) (.eval E f (.appArg E a k))
  | appArgStep {fv E a k} :
      StepM (.ret fv (.appArg E a k)) (.eval E a (.appFun fv k))
  | beta {body E av k} :
      StepM (.ret av (.appFun (.lam body E) k)) (.eval (av :: E) body k)
  | primOpPart {op av k} :
      StepM (.ret av (.appFun (.primOp op) k)) (.ret (.primOpApp op av) k)
  | primOpDelta {op a b r k} (h : PrimBinOp.delta op a b = some r) :
      StepM (.ret (.prim b) (.appFun (.primOpApp op (.prim a)) k)) (.ret r k)
  | ctorApp {name args av k} :
      StepM (.ret av (.appFun (.ctorV name args) k)) (.ret (.ctorV name (args ++ [av])) k)
  | letIn {E ann rhs body k} :
      StepM (.eval E (.letIn ann rhs body) k) (.eval (.thunk ann rhs E :: E) body k)
  | letRec {E anns bindings body k} :
      StepM (.eval E (.letRec anns bindings body) k) (.eval (bindGroup anns bindings E) body k)
  | matchScrut {E scrut branches k} :
      StepM (.eval E (.match_ scrut branches) k) (.eval E scrut (.matchSel E branches k))
  | matchCtor {name args E branches k pat body}
      (h : FirstMatchingBranch name args.length branches pat body) :
      StepM (.ret (.ctorV name args) (.matchSel E branches k))
            (.eval (args.take pat.bindCount ++ E) body k)
  | matchWild {v E branches k body} (h : IsNonCtorVal v) :
      StepM (.ret v (.matchSel E ((.wildcard, body) :: branches) k)) (.eval E body k)
  | force {ann e E k} :
      StepM (.ret (.thunk ann e E) k) (.eval E e k)
  | forceRecclo {anns bindings E j k} (h : j < bindings.length) :
      StepM (.ret (.recclo anns bindings E j) k)
            (.eval (bindGroup anns bindings E) (bindings.get ⟨j, h⟩) k)

/-! ## Typing of the machine

The machine is typed by the *declarative* `TypeOfHM`. The invariant has three
layers: values are typed at schemes (`ValTyped`), the value environment matches a
typing context (`EnvOK`), continuations are typed (`KontTyped`); `StateOK` puts
them together for a state. -/

mutual

  /-- Value `v` is a denotation of scheme `σ` (in ctor env `ctors`). A closure is
      typed by re-typing its body in its captured context; a thunk is typed at its
      scheme via the cofinite `GeneralisesTo` premise (exactly the `letIn` premise);
      a `recclo` is typed by the whole `letRec` group premise (its scheme is the
      member's `bodyScheme`). -/
  inductive ValTyped (ctors : CtorEnv) : Val → PolyTy → Prop
    | prim {p} :
        ValTyped ctors (.prim p) (PolyTy.mkTrivial p.ty)
    | primOp {op} {τ : Ty} (h : PrimBinOp.ty ctors op = some τ) :
        ValTyped ctors (.primOp op) (PolyTy.mkTrivial τ)
    | primOpApp {op v} {τ₁ τ₂ : Ty}
        (hv : ValTyped ctors v (PolyTy.mkTrivial τ₁))
        (h : PrimBinOp.ty ctors op = some (.arrow τ₁ τ₂)) :
        ValTyped ctors (.primOpApp op v) (PolyTy.mkTrivial τ₂)
    | lam {body E} {τ₁ τ₂ : Ty} {Γ : Env}
        (hE : EnvOK ctors E Γ)
        (hbody : TypeOfHM ⟨PolyTy.mkTrivial τ₁ :: Γ, ctors⟩ body τ₂) :
        ValTyped ctors (.lam body E) (PolyTy.mkTrivial (.arrow τ₁ τ₂))
    | thunk {ann e E} {M : PolyTy} {L : List Nat} {Γ : Env}
        (hE : EnvOK ctors E Γ)
        (hpin : ann.Pins M)
        (hgen : GeneralisesTo TypeOfHM ⟨Γ, ctors⟩ ann e M L) :
        ValTyped ctors (.thunk ann e E) M
    | recclo {anns bindings E j} {σ : PolyTy} {specs : List RecSpec} {G L : List Nat} {Γ : Env}
        (hj : j < specs.length)
        (hE : EnvOK ctors E Γ)
        (hwf : RecSpecs.WF anns bindings specs G)
        (hmono : RecSpecs.MonoTyped TypeOfHM ⟨Γ, ctors⟩ bindings specs G L)
        (hpoly : RecSpecs.PolyTyped TypeOfHM ⟨Γ, ctors⟩ bindings specs G L)
        (hσ : σ = RecSpec.bodyScheme G (specs.get ⟨j, hj⟩)) :
        ValTyped ctors (.recclo anns bindings E j) σ
    | ctorV {name args} {ctor : Ctor} {tyArgs instContents : List Ty}
        (hlook : LookupList.get? ctors name = some ctor)
        (hargs : List.Forall₂ (fun a t => ValTyped ctors a (PolyTy.mkTrivial t)) args instContents)
        (hfields : List.Forall₂ (InstantiatesBy tyArgs) ctor.contents instContents) :
        ValTyped ctors (.ctorV name args) (PolyTy.mkTrivial (.customTy ctor.tyName tyArgs))

  /-- Value environment `E` matches typing context `Γ` pointwise (same length, each
      value a denotation of the scheme at its index). -/
  inductive EnvOK (ctors : CtorEnv) : VEnv → Env → Prop
    | nil : EnvOK ctors [] []
    | cons {v E σ Γ} :
        ValTyped ctors v σ → EnvOK ctors E Γ → EnvOK ctors (v :: E) (σ :: Γ)

end

/-- Scheme `σ` instantiates to monotype `τ` (the declarative `TypeOfHM.var`
    instantiation: some locally-closed args, no length constraint). -/
def Instantiates (σ : PolyTy) (τ : Ty) : Prop :=
  ∃ instArgs, (∀ a ∈ instArgs, a.IsLC) ∧ σ.InstantiatesTo instArgs τ

/-- A value at scheme `σ` is also at any monotype `τ` that `σ` instantiates to
    (instantiation closes `ValTyped` downward). -/
theorem ValTyped_inst {ctors : CtorEnv} {v : Val} {σ : PolyTy} {τ : Ty}
    (hv : ValTyped ctors v σ) (hinst : Instantiates σ τ) :
    ValTyped ctors v (PolyTy.mkTrivial τ) := by
  sorry

/-- If a term types at every opening of scheme `M`, and `M` instantiates to `τ`,
    then the term types at `τ` (the `GeneralisesTo`-instantiation lemma, the
    unannotated case — the annotated case collapses via `ann.Pins M`). -/
theorem GeneralisesTo_inst {ctx : Ctx} {e : Expr} {M : PolyTy} {L : List Nat} {τ : Ty}
    (hgen : GeneralisesTo TypeOfHM ctx none e M L) (hinst : Instantiates M τ) :
    TypeOfHM ctx e τ := by
  sorry

/-- Continuation `k` awaits a value of type `τ` (its "hole") and produces a result
    of type `ρ`. -/
inductive KontTyped (ctors : CtorEnv) : Kont → Ty → Ty → Prop
  | nil {ρ : Ty} :
      KontTyped ctors .nil ρ ρ
  | appArg {E arg k} {A B ρ : Ty} {Γ : Env}
      (hE : EnvOK ctors E Γ)
      (harg : TypeOfHM ⟨Γ, ctors⟩ arg A)
      (hk : KontTyped ctors k B ρ) :
      KontTyped ctors (.appArg E arg k) (.arrow A B) ρ
  | appFun {fv k} {A B ρ : Ty}
      (hv : ValTyped ctors fv (PolyTy.mkTrivial (.arrow A B)))
      (hk : KontTyped ctors k B ρ) :
      KontTyped ctors (.appFun fv k) A ρ
  | matchSel {E branches k} {τ ρ : Ty} {Γ : Env}
      (hE : EnvOK ctors E Γ)
      (hbranches : ∀ branch ∈ branches, TypeOfMatchBranch ⟨Γ, ctors⟩ branch τ ρ)
      (hk : KontTyped ctors k ρ ρ) :
      KontTyped ctors (.matchSel E branches k) τ ρ

/-- A machine state is well-typed at result type `ρ`. -/
def StateOK (ctors : CtorEnv) (s : State) (ρ : Ty) : Prop :=
  match s with
  | .eval E e k => ∃ Γ τ, EnvOK ctors E Γ ∧ TypeOfHM ⟨Γ, ctors⟩ e τ ∧ KontTyped ctors k τ ρ
  | .ret v k => ∃ τ, ValTyped ctors v (PolyTy.mkTrivial τ) ∧ KontTyped ctors k τ ρ

/-! ## Exhaustiveness of a machine state

Every term embedded in a state — the current term, closure bodies, thunk terms,
rec-group bindings, and the terms in continuations — is match-exhaustive. This is
the machine-level analogue of `AllMatchesExhaustive`; progress needs it for the
match case. -/

mutual

  def ExhaustiveVal (ctors : CtorEnv) : Val → Prop
    | .prim _ => True
    | .primOp _ => True
    | .primOpApp _ v => ExhaustiveVal ctors v
    | .lam body E => AllMatchesExhaustive ctors body ∧ ExhaustiveEnv ctors E
    | .thunk _ e E => AllMatchesExhaustive ctors e ∧ ExhaustiveEnv ctors E
    | .recclo _ bindings E _ =>
        (∀ b ∈ bindings, AllMatchesExhaustive ctors b) ∧ ExhaustiveEnv ctors E
    | .ctorV _ args => ∀ a ∈ args, ExhaustiveVal ctors a

  def ExhaustiveEnv (ctors : CtorEnv) : VEnv → Prop
    | [] => True
    | v :: E => ExhaustiveVal ctors v ∧ ExhaustiveEnv ctors E

  def ExhaustiveKont (ctors : CtorEnv) : Kont → Prop
    | .nil => True
    | .appArg E arg k => ExhaustiveEnv ctors E ∧ AllMatchesExhaustive ctors arg ∧ ExhaustiveKont ctors k
    | .appFun v k => ExhaustiveVal ctors v ∧ ExhaustiveKont ctors k
    | .matchSel E branches k =>
        ExhaustiveEnv ctors E ∧
          (∀ pb ∈ branches, AllMatchesExhaustive ctors pb.2) ∧ ExhaustiveKont ctors k

end

/-- Exhaustiveness of a whole machine state. -/
def ExhaustiveState (ctors : CtorEnv) : State → Prop
  | .eval E e k => ExhaustiveEnv ctors E ∧ AllMatchesExhaustive ctors e ∧ ExhaustiveKont ctors k
  | .ret v k => ExhaustiveVal ctors v ∧ ExhaustiveKont ctors k

/-! ## Type safety -/

/-- Progress: a well-typed, exhaustive machine state is final (a value with an
    empty continuation) or can take a step. -/
theorem progress {ctors : CtorEnv} {s : State} {ρ : Ty}
    (h : StateOK ctors s ρ) (hexh : ExhaustiveState ctors s) :
    (∃ v, s = .ret v .nil) ∨ ∃ s', StepM s s' := by
  sorry

/-- Preservation: stepping preserves well-typedness. -/
theorem preservation {ctors : CtorEnv} {s s' : State} {ρ : Ty}
    (h : StateOK ctors s ρ) (hstep : StepM s s') :
    StateOK ctors s' ρ := by
  sorry

/-- Stepping preserves exhaustiveness. -/
theorem preservation_exhaustive {ctors : CtorEnv} {s s' : State}
    (hexh : ExhaustiveState ctors s) (hstep : StepM s s') :
    ExhaustiveState ctors s' := by
  sorry

/-- Multi-step preservation. -/
theorem preservation_star {ctors : CtorEnv} {s s' : State} {ρ : Ty}
    (h : StateOK ctors s ρ) (hstep : Relation.ReflTransGen StepM s s') :
    StateOK ctors s' ρ := by
  sorry

/-- Type safety: from a well-typed, exhaustive state, every reachable state is
    final or can step (the machine never gets stuck). -/
theorem type_safety {ctors : CtorEnv} {s : State} {ρ : Ty}
    (h : StateOK ctors s ρ) (hexh : ExhaustiveState ctors s) :
    ∀ s', Relation.ReflTransGen StepM s s' →
      (∃ v, s' = .ret v .nil) ∨ ∃ s'', StepM s' s'' := by
  sorry

/-- Type safety for a closed program: a well-typed, exhaustive closed term is safe
    under the machine (corollary of `type_safety` at the empty environment). -/
theorem type_safety_closed {ctors : CtorEnv} {e : Expr} {τ : Ty}
    (h : TypeOfHM ⟨[], ctors⟩ e τ) (hexh : AllMatchesExhaustive ctors e) :
    ∀ s', Relation.ReflTransGen StepM (.eval [] e .nil) s' →
      (∃ v, s' = .ret v .nil) ∨ ∃ s'', StepM s' s'' := by
  sorry

/-- The machine is deterministic. -/
theorem stepM_deterministic {s s₁ s₂ : State}
    (h₁ : StepM s s₁) (h₂ : StepM s s₂) : s₁ = s₂ := by
  sorry

end CekMachine
