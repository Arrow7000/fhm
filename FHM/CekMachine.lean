import FHM.Core
import FHM.InferW

/-- A term carries no *scoped* type-variable references: `var` nodes carry no
    `tyArgs`, and lambdas carry no parameter ascription. Binding annotations
    (`letIn ann` / `letRec anns`) are KEPT — they carry polymorphic recursion and
    generalisation pinning. This is the shape of the term the (type-erasing)
    machine runs on; the source's scoped variables live only in the two erased
    positions and are dropped by the pipeline's `erase` before the machine. -/
inductive Expr.IsErased : Expr → Prop
  | primLit {p : PrimLitExpr} : Expr.IsErased (.primLit p)
  | primBinOp {op : PrimBinOp} : Expr.IsErased (.primBinOp op)
  | lambda {body : Expr} : Expr.IsErased body → Expr.IsErased (.lambda none body)
  | app {f a : Expr} : Expr.IsErased f → Expr.IsErased a → Expr.IsErased (.app f a)
  | letIn {ann : Option PolyTy} {rhs body : Expr} :
      (∀ σ, ann = some σ → σ.WF) →
      Expr.IsErased rhs → Expr.IsErased body → Expr.IsErased (.letIn ann rhs body)
  | var {i : Nat} : Expr.IsErased (.var i [])
  | ctor {name : CtorName} : Expr.IsErased (.ctor name)
  | match_ {scrut : Expr} {branches : List (MatchPattern × Expr)} :
      Expr.IsErased scrut → (∀ pb ∈ branches, Expr.IsErased pb.2) → Expr.IsErased (.match_ scrut branches)
  | letRec {anns : List (Option PolyTy)} {bindings : List Expr} {body : Expr} :
      (∀ σ, some σ ∈ anns → σ.WF) →
      (∀ b ∈ bindings, Expr.IsErased b) → Expr.IsErased body → Expr.IsErased (.letRec anns bindings body)

/-- Opening a recursion group's bindings is a no-op when each binding is already
    erased (`b.openTyVarsAux d Xs = b` for every depth). The depth per member
    (`d + RecAnn.params aⱼ`) is irrelevant precisely because the member is
    depth-independent. -/
private theorem RecGroup.openTyVarsAux_eq_self_of_erased {d : Nat} {Xs : List Nat}
    {anns : List (Option PolyTy)} {bindings : List Expr}
    (h : ∀ b ∈ bindings, ∀ d Xs, b.openTyVarsAux d Xs = b) :
    RecGroup.openTyVarsAux d Xs anns bindings = bindings := by
  revert h
  induction bindings generalizing anns with
  | nil => intro _; cases anns <;> rfl
  | cons hd tl ihtl =>
      intro h
      cases anns with
      | nil =>
          simp only [RecGroup.openTyVarsAux]
          rw [h hd List.mem_cons_self d Xs,
              ihtl (fun b hb => h b (List.mem_cons_of_mem hd hb))]
      | cons a as =>
          simp only [RecGroup.openTyVarsAux]
          rw [h hd List.mem_cons_self (d + RecAnn.params a) Xs,
              ihtl (fun b hb => h b (List.mem_cons_of_mem hd hb))]

private theorem Expr.openTyVarsAux_eq_self_of_erased {e : Expr} (h : e.IsErased) :
    ∀ d Xs, e.openTyVarsAux d Xs = e := by
  induction h with
  | primLit => intro d Xs; rfl
  | primBinOp => intro d Xs; rfl
  | lambda hbody ih =>
      intro d Xs
      simp [Expr.openTyVarsAux, ih d Xs]
  | app hf ha ihf iha =>
      intro d Xs
      simp [Expr.openTyVarsAux, ihf d Xs, iha d Xs]
  | letIn hann hrhs hbody ihrhs ihbody =>
      rename_i ann rhs body
      intro d Xs
      rcases ann with hnone | σ
      · simp [Expr.openTyVarsAux, ihrhs d Xs, ihbody d Xs]
      · simp [Expr.openTyVarsAux, ihrhs (d + σ.paramCount) Xs, ihbody d Xs]
        have hwf : ContainsBvarsUpTo σ.paramCount σ.body := hann σ rfl
        rw [Ty.openVarsFrom_eq_self_of_bvars
          (ContainsBvarsUpTo.mono (Nat.le_add_left σ.paramCount d) hwf)]
  | var => intro d Xs; rfl
  | ctor => intro d Xs; rfl
  | match_ hscrut hbranches ih_scrut ih_branches =>
      rename_i scrut branches
      intro d Xs
      simp only [Expr.openTyVarsAux, ih_scrut d Xs]
      congr 1
      rw [BranchList.openTyVarsAux_eq_map]
      conv_rhs => rw [← List.map_id branches]
      apply List.map_congr_left
      intro pb hpb
      cases pb with
      | mk pat body =>
          simp only [id_eq]
          rw [ih_branches (pat, body) hpb d Xs]
  | letRec hanns hbindings hbody ih_bindings ih_body =>
      rename_i anns bindings body
      intro d Xs
      simp only [Expr.openTyVarsAux, ih_body d Xs]
      have hanns_open : RecGroup.openAnns d Xs anns = anns :=
        RecGroup.openAnns_eq_self_of_bvars
          (fun σ hmem => ContainsBvarsUpTo.mono (Nat.le_add_left σ.paramCount d) (hanns σ hmem))
      have hbind_open : RecGroup.openTyVarsAux d Xs anns bindings = bindings :=
        RecGroup.openTyVarsAux_eq_self_of_erased ih_bindings
      rw [hanns_open, hbind_open]

/-- Opening is a no-op on an erased term: an erased term has no scoped type
    variables (`lambda` ascriptions, `var` tyArgs) to open. This is the bridge that
    makes the `recclo_body_typed` poly half provable for the machine's terms. -/
theorem Expr.openTyVars_eq_self_of_erased {e : Expr} (h : e.IsErased) :
    ∀ Xs, e.openTyVars Xs = e := by
  intro Xs
  simpa [Expr.openTyVars] using Expr.openTyVarsAux_eq_self_of_erased h 0 Xs

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

/-- A *machine value* — an already-evaluated value, i.e. NOT a thunk or rec-closure.
    Thunks/rec-closures are suspended computations, forced by `force`/`forceRecclo`
    *before* any value-consuming rule (`appArgStep`/`beta`/`ctorApp`/`primOpPart`)
    sees them; this is what keeps `StepM` deterministic and sound (a thunk can
    never leak into a function/argument/constructor position unforced). -/
def IsVal : Val → Prop
  | .prim _ => True
  | .primOp _ => True
  | .primOpApp _ _ => True
  | .lam _ _ => True
  | .thunk _ _ _ => False
  | .recclo _ _ _ _ => False
  | .ctorV _ _ => True

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
  | appArgStep {fv E a k} (h : IsVal fv) :
      StepM (.ret fv (.appArg E a k)) (.eval E a (.appFun fv k))
  | beta {body E av k} (h : IsVal av) :
      StepM (.ret av (.appFun (.lam body E) k)) (.eval (av :: E) body k)
  | primOpPart {op av k} (h : IsVal av) :
      StepM (.ret av (.appFun (.primOp op) k)) (.ret (.primOpApp op av) k)
  | primOpDelta {op a b r k} (h : PrimBinOp.delta op a b = some r) :
      StepM (.ret (.prim b) (.appFun (.primOpApp op (.prim a)) k)) (.ret r k)
  | ctorApp {name args av k} (h : IsVal av) :
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
        (hIsVal : IsVal v)
        (hv : ValTyped ctors v (PolyTy.mkTrivial τ₁))
        (h : PrimBinOp.ty ctors op = some (.arrow τ₁ τ₂)) :
        ValTyped ctors (.primOpApp op v) (PolyTy.mkTrivial τ₂)
    | lam {body E} {τ₁ τ₂ : Ty} {Γ : Env}
        (hτ₁ : τ₁.IsLC) (hτ₂ : τ₂.IsLC)
        (hE : EnvOK ctors E Γ)
        (hbody : TypeOfHM ⟨PolyTy.mkTrivial τ₁ :: Γ, ctors⟩ body τ₂) :
        ValTyped ctors (.lam body E) (PolyTy.mkTrivial (.arrow τ₁ τ₂))
    | thunk {ann e E} {M : PolyTy} {L : List Nat} {Γ : Env}
        (hE : EnvOK ctors E Γ)
        (hpin : ann.Pins M)
        (hMwf : M.WF)
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
    | ctorV {name args} {ctor : Ctor} {tyArgs instContents remContents : List Ty}
        (hlook : LookupList.get? ctors name = some ctor)
        (htyArgs : ∀ a ∈ tyArgs, a.IsLC)
        (hargs : List.Forall₂ (fun a t => ValTyped ctors a (PolyTy.mkTrivial t)) args instContents)
        (hfields : List.Forall₂ (InstantiatesBy tyArgs) ctor.contents (instContents ++ remContents)) :
        ValTyped ctors (.ctorV name args)
          (PolyTy.mkTrivial (Ty.wrapArrows (.customTy ctor.tyName tyArgs) remContents))

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

/-- Instantiation is the identity on locally-closed types: if `ty` has no
    bvars, `InstantiatesBy tyArgs ty τ` forces `τ = ty` (reverse of
    `InstantiatesBy.refl_of_closed`). -/
private theorem InstantiatesBy.eq_of_closed {tyArgs : List Ty} {ty τ : Ty}
    (h : ContainsBvarsUpTo 0 ty) (hinst : InstantiatesBy tyArgs ty τ) : τ = ty := by
  induction ty using Ty.rec_strong generalizing τ with
  | prim p =>
      cases hinst
      rfl
  | arrow a b iha ihb =>
      cases h with
      | arrow ha hb =>
          cases hinst with
          | arrow hinstA hinstB =>
              rw [iha ha hinstA, ihb hb hinstB]
  | bvar i =>
      cases h with
      | bvar hlt => exact absurd hlt (by omega)
  | fvar n =>
      cases hinst
      rfl
  | customTy nm tys ih =>
      cases h with
      | customTy hall =>
          cases hinst with
          | customTy hforall =>
              refine congrArg (Ty.customTy nm) ?_
              revert hall
              induction hforall with
              | nil => intro hall; rfl
              | cons hhd htl ihtl =>
                  rename_i a b l₁ l₂
                  intro hall
                  rw [List.cons.injEq]
                  constructor
                  · exact ih a List.mem_cons_self (hall a List.mem_cons_self) hhd
                  · exact ihtl (fun t ht => ih t (List.mem_cons_of_mem _ ht))
                      (fun ty hty => hall ty (List.mem_cons_of_mem _ hty))
  | bl lo hi e ih =>
      cases h with
      | bl he =>
          cases hinst with
          | bl hinstElem =>
              exact congrArg (Ty.bl lo hi) (ih he hinstElem)

/-- `PrimBinOp.ty` always returns a locally-closed type (no `bvar`s): the built-in
    ops are monomorphic — `int`/`char` literals, `Bool` with no type args. -/
private theorem PrimBinOp.ty_lc {ctors : CtorEnv} {op : PrimBinOp} {τ : Ty}
    (h : PrimBinOp.ty ctors op = some τ) : τ.IsLC := by
  cases op with
  | intAdd =>
      simp [PrimBinOp.ty] at h
      rw [← h]
      exact ContainsBvarsUpTo.arrow ContainsBvarsUpTo.prim
        (ContainsBvarsUpTo.arrow ContainsBvarsUpTo.prim ContainsBvarsUpTo.prim)
  | intSub =>
      simp [PrimBinOp.ty] at h
      rw [← h]
      exact ContainsBvarsUpTo.arrow ContainsBvarsUpTo.prim
        (ContainsBvarsUpTo.arrow ContainsBvarsUpTo.prim ContainsBvarsUpTo.prim)
  | intLt =>
      cases h1 : LookupList.get? ctors ⟨"True"⟩ with
      | none => simp [PrimBinOp.ty, h1] at h
      | some tc =>
          cases h2 : LookupList.get? ctors ⟨"False"⟩ with
          | none => simp [PrimBinOp.ty, h1, h2] at h
          | some fc =>
              simp [PrimBinOp.ty, h1, h2] at h
              rcases h with ⟨htc, hx⟩
              rw [← hx]
              exact ContainsBvarsUpTo.arrow ContainsBvarsUpTo.prim
                (ContainsBvarsUpTo.arrow ContainsBvarsUpTo.prim
                  (ContainsBvarsUpTo.customTy (by intro t ht; simp at ht)))
  | charLt =>
      cases h1 : LookupList.get? ctors ⟨"True"⟩ with
      | none => simp [PrimBinOp.ty, h1] at h
      | some tc =>
          cases h2 : LookupList.get? ctors ⟨"False"⟩ with
          | none => simp [PrimBinOp.ty, h1, h2] at h
          | some fc =>
              simp [PrimBinOp.ty, h1, h2] at h
              rcases h with ⟨htc, hx⟩
              rw [← hx]
              exact ContainsBvarsUpTo.arrow ContainsBvarsUpTo.prim
                (ContainsBvarsUpTo.arrow ContainsBvarsUpTo.prim
                  (ContainsBvarsUpTo.customTy (by intro t ht; simp at ht)))

/-- Right component of a locally-closed arrow is locally closed. -/
private theorem arrow_lc_r {τ₁ τ₂ : Ty} (h : (Ty.arrow τ₁ τ₂).IsLC) : τ₂.IsLC := by
  cases h with
  | arrow _ hb => exact hb

/-- Appending a list of typed values (pointwise) to a typed environment keeps
    `EnvOK`. -/
private theorem EnvOK_append {ctors : CtorEnv} {E : VEnv} {Γ : Env}
    (hE : EnvOK ctors E Γ) :
    ∀ (xs : VEnv) (schemes : List PolyTy),
      List.Forall₂ (fun v σ => ValTyped ctors v σ) xs schemes →
      EnvOK ctors (xs ++ E) (schemes ++ Γ) := by
  intro xs
  induction xs with
  | nil =>
      intro schemes h
      cases schemes with
      | nil => simpa using hE
      | cons σ schemes_tl => cases h
  | cons v xs ih =>
      intro schemes h
      cases schemes with
      | nil => cases h
      | cons σ schemes_tl =>
          cases h with
          | cons hv htl => exact EnvOK.cons hv (ih schemes_tl htl)

/-- The prefix-general form of `EnvOK_bindGroup`: `(preA, preB, preS)` is the
    already-consumed prefix of the group (each step adds one binding and one
    spec), and position `j` of the value list stores a `recclo` of the WHOLE
    group at index `preS.length + j`, typed at `bodyScheme G (specs[j])` via
    the full group's cofinite premises. -/
private theorem EnvOK_bindGroup_pre {ctors : CtorEnv} {Γ : Env}
    {preA : List (Option PolyTy)} {preB : List Expr} {preS : List RecSpec}
    {anns : List (Option PolyTy)} {bindings : List Expr} {specs : List RecSpec}
    {G L : List Nat} {E : VEnv}
    (hE : EnvOK ctors E Γ)
    (hpre : preB.length = preS.length)
    (hwf : RecSpecs.WF (preA ++ anns) (preB ++ bindings) (preS ++ specs) G)
    (hmono : RecSpecs.MonoTyped TypeOfHM ⟨Γ, ctors⟩ (preB ++ bindings) (preS ++ specs) G L)
    (hpoly : RecSpecs.PolyTyped TypeOfHM ⟨Γ, ctors⟩ (preB ++ bindings) (preS ++ specs) G L) :
    EnvOK ctors ((List.range bindings.length).map
        (fun j => .recclo (preA ++ anns) (preB ++ bindings) E (preS.length + j)) ++ E)
      (specs.map (RecSpec.bodyScheme G) ++ Γ) := by
  induction specs generalizing anns bindings preA preB preS with
  | nil =>
      have hb : bindings = [] := by
        apply List.eq_nil_of_length_eq_zero
        have h : preB.length + bindings.length = preS.length := by
          simpa [List.length_append] using hwf.length
        omega
      subst bindings
      simpa using hE
  | cons spec specs_tl ih =>
      cases bindings with
      | nil =>
          have hcontra : preS.length = preS.length + (specs_tl.length + 1) := by
            simpa [List.length_append, hpre] using hwf.length
          omega
      | cons b bindings_tl =>
          rw [List.length_cons, List.range_succ_eq_map, List.map_cons, List.map_map]
          refine EnvOK.cons ?_ ?_
          · refine ValTyped.recclo (specs := preS ++ spec :: specs_tl) (j := preS.length) ?_ hE hwf hmono hpoly ?_
            · rw [List.length_append, List.length_cons]
              omega
            · apply congrArg (RecSpec.bodyScheme G)
              simp
          · have hpre' : (preB ++ [b]).length = (preS ++ [spec]).length := by simp [hpre]
            have hwf' : RecSpecs.WF (preA ++ anns) ((preB ++ [b]) ++ bindings_tl)
                ((preS ++ [spec]) ++ specs_tl) G := by
              simpa [List.append_assoc] using hwf
            have hmono' : RecSpecs.MonoTyped TypeOfHM ⟨Γ, ctors⟩ ((preB ++ [b]) ++ bindings_tl)
                ((preS ++ [spec]) ++ specs_tl) G L := by
              simpa [List.append_assoc] using hmono
            have hpoly' : RecSpecs.PolyTyped TypeOfHM ⟨Γ, ctors⟩ ((preB ++ [b]) ++ bindings_tl)
                ((preS ++ [spec]) ++ specs_tl) G L := by
              simpa [List.append_assoc] using hpoly
            simpa [List.append_assoc, Function.comp_def, Nat.succ_eq_add_one,
              Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
              ih (anns := anns) (bindings := bindings_tl) (preA := preA)
                (preB := preB ++ [b]) (preS := preS ++ [spec]) hpre' hwf' hmono' hpoly'

/-- Pointwise: a `Forall₂` witness reaches every element of the right list. -/
private theorem Forall₂_mem_right {α β : Type} {R : α → β → Prop}
    {l₁ : List α} {l₂ : List β} (h : List.Forall₂ R l₁ l₂) :
    ∀ b ∈ l₂, ∃ a ∈ l₁, R a b := by
  induction h with
  | nil =>
      intro b hb
      simp at hb
  | cons ha htl ih =>
      intro b hb
      simp at hb
      rcases hb with rfl | hb
      · exact ⟨_, List.mem_cons_self, ha⟩
      · rcases ih b hb with ⟨a, ha', hR⟩
        exact ⟨a, List.mem_cons_of_mem _ ha', hR⟩

/-- Instantiation preserves local closure: if `t` (whose bvars are all below `n`)
    instantiates to `τ` at locally-closed args, then `τ` is locally closed. The
    `bvar` case is discharged by the LC of the corresponding `tyArgs` entry; the
    `NoFreeVars`-ness of `t` is irrelevant (instantiating only ever *replaces*
    bvars, and the input side's other constructors pass closure through
    compositionally). Used to show `ValTyped.ctorV`'s remaining-field types are
    LC — each is an `InstantiatesBy` instance of a `ctor.contents` field, and
    fields are `ContainsBvarsUpTo ctor.paramCount`. -/
private theorem InstantiatesBy_lc {n : Nat} {tyArgs : List Ty} {t τ : Ty}
    (hLC : ∀ a ∈ tyArgs, a.IsLC)
    (hbound : ContainsBvarsUpTo n t)
    (hinst : InstantiatesBy tyArgs t τ) : τ.IsLC := by
  induction t using Ty.rec_strong generalizing τ with
  | prim p =>
      cases hinst
      exact ContainsBvarsUpTo.prim
  | arrow a b iha ihb =>
      cases hbound with
      | arrow hba hbb =>
          cases hinst with
          | arrow hinstA hinstB =>
              exact ContainsBvarsUpTo.arrow (iha hba hinstA) (ihb hbb hinstB)
  | bvar i =>
      cases hbound
      cases hinst with
      | bvar hsome =>
          exact hLC _ (List.mem_of_getElem? hsome)
  | fvar n =>
      cases hinst
      exact ContainsBvarsUpTo.fvar
  | customTy nm tys ih =>
      cases hbound with
      | customTy hball =>
          cases hinst with
          | customTy hforall =>
              refine ContainsBvarsUpTo.customTy ?_
              intro τ hτ
              rcases Forall₂_mem_right hforall τ hτ with ⟨a, ha, hinstA⟩
              exact ih a ha (hball a ha) hinstA
  | bl lo hi e ih =>
      cases hbound with
      | bl hbe =>
          cases hinst with
          | bl hinstE =>
              exact ContainsBvarsUpTo.bl (ih hbe hinstE)

/-- `wrapArrows` of a locally-closed result at locally-closed arguments is
    locally closed. -/
private theorem wrapArrows_lc {result : Ty} {args : List Ty}
    (hres : result.IsLC) (hargs : ∀ a ∈ args, a.IsLC) : (Ty.wrapArrows result args).IsLC := by
  induction args with
  | nil => simpa [Ty.wrapArrows] using hres
  | cons a as ih =>
      simp only [Ty.wrapArrows]
      exact ContainsBvarsUpTo.arrow (hargs a List.mem_cons_self)
        (ih (fun b hb => hargs b (List.mem_cons_of_mem _ hb)))

/-- An already-forced value at scheme `σ` is also at any monotype `τ` that `σ`
    instantiates to. (This closes `ValTyped` downward only for `IsVal` values —
    the ones consumed at a monotype without being forced first; thunks and
    rec-closures are instead consumed via the `Instantiates` premise in
    `StateOK`/`KontTyped`, never through this lemma.) -/
-- NOTE: previously claimed unprovable because the `mutual`-compiled `ValTyped`
-- was thought to drop the `.IsLC` premises of the `lam`/`ctorV` constructors.
-- The current source keeps them, so the proof below goes through: every `IsVal`
-- constructor forces `σ = mkTrivial t` for a locally-closed `t`, hence `hinst`
-- is the identity on `t` (`InstantiatesBy.eq_of_closed`) and `τ = t`.
theorem ValTyped_inst_of_isVal {ctors : CtorEnv} {v : Val} {σ : PolyTy} {τ : Ty}
    (hvIsVal : IsVal v) (hv : ValTyped ctors v σ) (hinst : Instantiates σ τ) :
    ValTyped ctors v (PolyTy.mkTrivial τ) := by
  cases hv with
  | prim =>
      rename_i p
      cases p <;>
        (rcases hinst with ⟨instArgs, hinstLC, hinstTo⟩
         have hEq := InstantiatesBy.eq_of_closed ContainsBvarsUpTo.prim hinstTo
         subst hEq
         exact ValTyped.prim)
  | primOp hty =>
      rcases hinst with ⟨instArgs, hinstLC, hinstTo⟩
      have hEq := InstantiatesBy.eq_of_closed (PrimBinOp.ty_lc hty) hinstTo
      subst hEq
      exact ValTyped.primOp hty
  | primOpApp hIsVal hv' hty =>
      rcases hinst with ⟨instArgs, hinstLC, hinstTo⟩
      have hτ₂lc := arrow_lc_r (PrimBinOp.ty_lc hty)
      have hEq := InstantiatesBy.eq_of_closed hτ₂lc hinstTo
      subst hEq
      exact ValTyped.primOpApp hIsVal hv' hty
  | lam hτ₁ hτ₂ hE hbody =>
      rcases hinst with ⟨instArgs, hinstLC, hinstTo⟩
      have hEq := InstantiatesBy.eq_of_closed (ContainsBvarsUpTo.arrow hτ₁ hτ₂) hinstTo
      subst hEq
      exact ValTyped.lam hτ₁ hτ₂ hE hbody
  | thunk =>
      simp [IsVal] at hvIsVal
  | recclo =>
      simp [IsVal] at hvIsVal
  | ctorV hlook htyArgs hargs hfields =>
      rename_i name args ctor tyArgs instContents remContents
      rcases hinst with ⟨instArgs, hinstLC, hinstTo⟩
      -- Each remaining-field type is an `InstantiatesBy tyArgs` instance of a
      -- `ctor.contents` field, and fields are bounded by `ctor.paramCount`.
      have hmem_lc : ∀ τ ∈ (instContents ++ remContents), τ.IsLC := by
        intro τ hτ
        rcases Forall₂_mem_right hfields τ hτ with ⟨a, ha, hinstA⟩
        exact InstantiatesBy_lc htyArgs (ctor.bound a ha) hinstA
      have hBodyLC : (Ty.wrapArrows (.customTy ctor.tyName tyArgs) remContents).IsLC :=
        wrapArrows_lc (ContainsBvarsUpTo.customTy htyArgs)
          (fun a ha => hmem_lc a (List.mem_append.mpr (Or.inr ha)))
      have hEq := InstantiatesBy.eq_of_closed hBodyLC hinstTo
      subst hEq
      exact ValTyped.ctorV hlook htyArgs hargs hfields

/-- `bindGroup anns bindings E` is well-typed against the group's BODY context:
    each rec-closure at its member's body scheme, and `E` at `Γ`. (Needed by
    `preservation`'s `forceRecclo` case to type the recursive environment.) -/
theorem EnvOK_bindGroup {ctors : CtorEnv} {Γ : Env} {anns : List (Option PolyTy)}
    {bindings : List Expr} {specs : List RecSpec} {G L : List Nat} {E : VEnv}
    (hE : EnvOK ctors E Γ)
    (hwf : RecSpecs.WF anns bindings specs G)
    (hmono : RecSpecs.MonoTyped TypeOfHM ⟨Γ, ctors⟩ bindings specs G L)
    (hpoly : RecSpecs.PolyTyped TypeOfHM ⟨Γ, ctors⟩ bindings specs G L) :
    EnvOK ctors (bindGroup anns bindings E) (specs.map (RecSpec.bodyScheme G) ++ Γ) := by
  unfold bindGroup
  simpa using (EnvOK_bindGroup_pre (preA := []) (preB := []) (preS := []) hE rfl hwf hmono hpoly)

/-- A length-free variant of `Ty.substFvars_zip_fvar_eq`: the `i`-th pair
    `(Xs[i], Vs[i])` is present in `Xs.zip Vs` and fires on `.fvar (Xs[i])`,
    provided `Vs[i]` is defined (no `Vs.length = Xs.length` hypothesis needed). -/
private theorem Ty.substFvars_zip_fvar_eq' {Xs : List Nat} {Vs : List Ty}
    {i : Nat} {x : Nat} {v : Ty}
    (h_nodup : Xs.Nodup)
    (h_fresh : ∀ X ∈ Xs, X ∉ Ty.freeVarsList Vs)
    (hx : Xs[i]? = some x)
    (hv : Vs[i]? = some v) :
    Ty.substFvars (Xs.zip Vs) (.fvar x) = v := by
  induction Xs generalizing Vs i x v with
  | nil => simp at hx
  | cons X0 Xs' ih =>
      cases Vs with
      | nil => simp at hv
      | cons V0 Vs' =>
          cases i with
          | zero =>
              simp only [List.getElem?_cons_zero, Option.some.injEq] at hx hv
              simp only [List.zip_cons_cons, Ty.substFvars]
              rw [← hx, show Ty.substFvar X0 V0 (.fvar X0) = V0 by simp [Ty.substFvar], ← hv]
              apply Ty.substFvars_eq_self_of_no_key
              intro p hp hcontra
              have hp1 : p.1 ∈ Xs' := (List.of_mem_zip hp).1
              have hXf : p.1 ∉ Ty.freeVarsList (V0 :: Vs') :=
                h_fresh p.1 (List.mem_cons_of_mem _ hp1)
              simp only [Ty.freeVarsList, List.mem_dedup, List.mem_append] at hXf
              exact hXf (Or.inl hcontra)
          | succ k =>
              simp only [List.getElem?_cons_succ] at hx hv
              have h_X0_notin : X0 ∉ Xs' := (List.nodup_cons.mp h_nodup).1
              have h_x_mem : x ∈ Xs' := List.mem_of_getElem? hx
              have h_ne : x ≠ X0 := fun h => h_X0_notin (h ▸ h_x_mem)
              have h_fresh' : ∀ X ∈ Xs', X ∉ Ty.freeVarsList Vs' := by
                intro X hX hc
                refine h_fresh X (List.mem_cons_of_mem _ hX) ?_
                simp only [Ty.freeVarsList, List.mem_dedup, List.mem_append]
                exact .inr hc
              simp only [List.zip_cons_cons, Ty.substFvars]
              rw [show Ty.substFvar X0 V0 (.fvar x) = .fvar x by simp [Ty.substFvar, h_ne]]
              exact ih (List.nodup_cons.mp h_nodup).2 h_fresh' hx hv

/-- `GeneralisesTo_inst`'s type-side round-trip: substituting the zipped fresh
    names `Xs` back to `Vs` through `ty.openVars Xs` recovers exactly the
    `InstantiatesBy Vs ty τ` instance, PROVIDED the opened type is locally closed
    (which `TypeOfHM.regular` supplies — the LC hypothesis rules out dangling
    bvars of `ty` beyond `Xs.length`, where the two sides would diverge). -/
private theorem substFvars_zip_openVars_eq {Xs : List Nat} {Vs : List Ty}
    (hXs_nodup : Xs.Nodup)
    (hXs_fresh_Vs : ∀ X ∈ Xs, X ∉ Ty.freeVarsList Vs) :
    ∀ (ty τ : Ty), InstantiatesBy Vs ty τ →
      (∀ X ∈ Xs, X ∉ ty.freeVars) →
      ContainsBvarsUpTo 0 (Ty.openVars Xs ty) →
      Ty.substFvars (Xs.zip Vs) (Ty.openVars Xs ty) = τ := by
  intro ty
  induction ty using Ty.rec_strong with
  | prim p =>
      intro τ h _ _
      cases h
      unfold Ty.openVars
      simp only [Ty.instantiate]
      exact Ty.substFvars_prim
  | arrow a b iha ihb =>
      intro τ h hfresh hLC
      cases h with
      | arrow ha hb =>
          rename_i instFst instSnd
          rw [Ty.openVars_arrow, Ty.substFvars_arrow]
          cases hLC with
          | arrow hLCa hLCb =>
              rw [iha instFst ha (fun X hX hc => hfresh X hX (by
                    simp only [Ty.freeVars, List.mem_dedup, List.mem_append]
                    exact .inl hc)) hLCa,
                  ihb instSnd hb (fun X hX hc => hfresh X hX (by
                    simp only [Ty.freeVars, List.mem_dedup, List.mem_append]
                    exact .inr hc)) hLCb]
  | bvar i =>
      intro τ h hfresh hLC
      cases h with
      | bvar hsome =>
          by_cases hi : i < Xs.length
          · obtain ⟨x, hx⟩ : ∃ x, Xs[i]? = some x := ⟨_, List.getElem?_eq_getElem hi⟩
            simp only [Ty.openVars, Ty.instantiate, hx, Option.elim]
            exact Ty.substFvars_zip_fvar_eq' hXs_nodup hXs_fresh_Vs hx hsome
          · have hx : Xs[i]? = none := List.getElem?_eq_none (by omega)
            have hLCi : ContainsBvarsUpTo 0 (.bvar i) := by
              simpa only [Ty.openVars, Ty.instantiate, hx, Option.elim] using hLC
            cases hLCi with
            | bvar hlt => omega
  | fvar n =>
      intro τ h hfresh hLC
      cases h
      simp only [Ty.openVars, Ty.instantiate]
      apply Ty.substFvars_eq_self_of_no_key
      intro p hp hcontra
      have hp1 : p.1 ∈ Xs := (List.of_mem_zip hp).1
      have hnf : p.1 ∉ Ty.freeVars (.fvar n) := hfresh p.1 hp1
      simp only [Ty.freeVars, List.mem_singleton] at hnf hcontra
      exact hnf hcontra
  | customTy nm tys ih =>
      intro τ h hfresh hLC
      cases h with
      | customTy hforall =>
          rw [Ty.openVars_customTy, Ty.substFvars_customTy]
          apply congrArg (Ty.customTy nm)
          cases hLC with
          | customTy hball =>
              induction hforall with
              | nil => rfl
              | cons hhd htl ihtl =>
                  rename_i hd_ty hd_inst tl_tys tl_inst
                  have h_hd : Ty.substFvars (Xs.zip Vs) (Ty.openVars Xs hd_ty) = hd_inst :=
                    ih hd_ty List.mem_cons_self hd_inst hhd
                      (fun X hX hc => hfresh X hX (by
                        simp only [Ty.freeVars, TyList.freeVars, List.mem_dedup, List.mem_append]
                        exact .inl hc))
                      (hball (Ty.openVars Xs hd_ty) (by
                        exact List.mem_cons_self))
                  have hfresh_tl : ∀ X ∈ Xs, X ∉ (Ty.customTy nm tl_tys).freeVars := by
                    intro X hX hc
                    exact hfresh X hX (by
                      simp only [Ty.freeVars, TyList.freeVars, List.mem_dedup, List.mem_append]
                      exact .inr hc)
                  have hball_tl :
                      ∀ ty ∈ TyList.instantiate (fun i => Xs[i]?.elim (Ty.bvar i) Ty.fvar) tl_tys,
                        ContainsBvarsUpTo 0 ty :=
                    fun ty ht => hball ty (List.mem_cons_of_mem _ ht)
                  have h_tl : List.map (Ty.substFvars (Xs.zip Vs))
                      (List.map (Ty.openVars Xs) tl_tys) = tl_inst :=
                    ihtl (fun t ht => ih t (List.mem_cons_of_mem _ ht)) hfresh_tl hball_tl
                  simp only [List.map_cons]
                  rw [← h_hd, h_tl]
  | bl lo hi e ih =>
      intro τ h hfresh hLC
      cases h with
      | bl he =>
          rename_i instElem
          rw [Ty.openVars_bl, Ty.substFvars_bl]
          rw [Ty.openVars_bl] at hLC
          cases hLC with
          | bl hLCe =>
              exact congrArg (Ty.bl lo hi) (ih instElem he (fun X hX hc => hfresh X hX hc) hLCe)

/-- The annotated/erased analogue of `GeneralisesTo_inst`: if an ERASED term types
    at every opening of scheme `M` (whether the `let` was annotated or not), and
    `M` instantiates to `τ`, then the term types at `τ`. Erased-ness rewrites the
    opening `openBoundTyVars ann Xs e` to `e` itself, so both the `none` and
    `some σ` cases collapse to the same substitution argument. Needed by
    `preservation`'s `force` case (whose thunk may be annotated). -/
theorem GeneralisesTo_inst_ann {ctx : Ctx} {ann : Option PolyTy} {e : Expr}
    {M : PolyTy} {L : List Nat} {τ : Ty}
    (herased : e.IsErased)
    (hgen : GeneralisesTo TypeOfHM ctx ann e M L) (hinst : Instantiates M τ) :
    TypeOfHM ctx e τ := by
  rcases hinst with ⟨instArgs, hinstLC, hinstTo⟩
  -- Pick fresh names `Xs` (length `M.paramCount`) avoiding `L`, the context env's
  -- free vars, `e`'s annotation free vars, and the free vars of `instArgs` / `M.body`.
  obtain ⟨Xs, hXlen, hXnodup, hXavoid⟩ :=
    exists_fresh_names
      (L ++ ctx.env.freeVars ++ e.tyFreeVars ++ Ty.freeVarsList instArgs ++ M.body.freeVars)
      M.paramCount
  have hXL : ∀ x ∈ Xs, x ∉ L := fun x hx hc => hXavoid x hx (by simp only [List.mem_append]; tauto)
  have hXenv : ∀ x ∈ Xs, x ∉ ctx.env.freeVars := fun x hx hc =>
    hXavoid x hx (by simp only [List.mem_append]; tauto)
  have hXe : ∀ x ∈ Xs, x ∉ e.tyFreeVars := fun x hx hc =>
    hXavoid x hx (by simp only [List.mem_append]; tauto)
  have hXVs : ∀ x ∈ Xs, x ∉ Ty.freeVarsList instArgs := fun x hx hc =>
    hXavoid x hx (by simp only [List.mem_append]; tauto)
  have hXM : ∀ x ∈ Xs, x ∉ M.body.freeVars := fun x hx hc =>
    hXavoid x hx (by simp only [List.mem_append]; tauto)
  have hfresh : FreshNames L M.paramCount Xs := ⟨hXlen, hXnodup, hXL⟩
  -- Erased-ness collapses the opening: `openBoundTyVars none` is the identity,
  -- and `openBoundTyVars (some σ)` is `e.openTyVars Xs = e` (no scoped tyVars).
  have he : TypeOfHM ctx e (M.openVars Xs) := by
    cases ann with
    | none => simpa [Expr.openBoundTyVars] using hgen Xs hfresh
    | some σ =>
        simpa [Expr.openBoundTyVars, Expr.openTyVars_eq_self_of_erased herased Xs] using hgen Xs hfresh
  -- Push the type-fvar substitution `Xs[i] ↦ instArgs[i]` through the derivation;
  -- the fresh names fix both the context and the term.
  have h_lc : ∀ p ∈ Xs.zip instArgs, Ty.IsLC p.2 := fun p hp =>
    hinstLC p.2 (List.of_mem_zip hp).2
  have hsub : TypeOfHM ctx (e.substTyFvars (Xs.zip instArgs))
      (Ty.substFvars (Xs.zip instArgs) (M.openVars Xs)) :=
    TypeOfHM.typ_substs_preservation (Xs.zip instArgs)
      (fun p hp => hXenv p.1 (List.of_mem_zip hp).1) h_lc he
  have hfix : e.substTyFvars (Xs.zip instArgs) = e :=
    Expr.substTyFvars_eq_self_of_not_mem_tyFreeVars (by
      intro p hp
      exact hXe p.1 (List.of_mem_zip hp).1)
  have hreg : (M.openVars Xs).IsLC := TypeOfHM.regular he
  have hty : Ty.substFvars (Xs.zip instArgs) (M.openVars Xs) = τ := by
    change Ty.substFvars (Xs.zip instArgs) (Ty.openVars Xs M.body) = τ
    exact substFvars_zip_openVars_eq (Xs := Xs) (Vs := instArgs)
      hXnodup hXVs M.body τ hinstTo hXM hreg
  rw [hfix, hty] at hsub
  exact hsub

/-- If a term types at every opening of scheme `M`, and `M` instantiates to `τ`,
    then the term types at `τ` (the `GeneralisesTo`-instantiation lemma, the
    unannotated case — the annotated case collapses via `ann.Pins M`). -/
theorem GeneralisesTo_inst {ctx : Ctx} {e : Expr} {M : PolyTy} {L : List Nat} {τ : Ty}
    (hgen : GeneralisesTo TypeOfHM ctx none e M L) (hinst : Instantiates M τ) :
    TypeOfHM ctx e τ := by
  rcases hinst with ⟨instArgs, hinstLC, hinstTo⟩
  -- Pick fresh names `Xs` (length `M.paramCount`) avoiding `L`, the context env's
  -- free vars, `e`'s annotation free vars, and the free vars of `instArgs` / `M.body`.
  obtain ⟨Xs, hXlen, hXnodup, hXavoid⟩ :=
    exists_fresh_names
      (L ++ ctx.env.freeVars ++ e.tyFreeVars ++ Ty.freeVarsList instArgs ++ M.body.freeVars)
      M.paramCount
  have hXL : ∀ x ∈ Xs, x ∉ L := fun x hx hc => hXavoid x hx (by simp only [List.mem_append]; tauto)
  have hXenv : ∀ x ∈ Xs, x ∉ ctx.env.freeVars := fun x hx hc =>
    hXavoid x hx (by simp only [List.mem_append]; tauto)
  have hXe : ∀ x ∈ Xs, x ∉ e.tyFreeVars := fun x hx hc =>
    hXavoid x hx (by simp only [List.mem_append]; tauto)
  have hXVs : ∀ x ∈ Xs, x ∉ Ty.freeVarsList instArgs := fun x hx hc =>
    hXavoid x hx (by simp only [List.mem_append]; tauto)
  have hXM : ∀ x ∈ Xs, x ∉ M.body.freeVars := fun x hx hc =>
    hXavoid x hx (by simp only [List.mem_append]; tauto)
  have hfresh : FreshNames L M.paramCount Xs := ⟨hXlen, hXnodup, hXL⟩
  have he : TypeOfHM ctx e (M.openVars Xs) := by
    simpa [Expr.openBoundTyVars] using hgen Xs hfresh
  -- Push the type-fvar substitution `Xs[i] ↦ instArgs[i]` through the derivation;
  -- the fresh names fix both the context and the term.
  have h_lc : ∀ p ∈ Xs.zip instArgs, Ty.IsLC p.2 := fun p hp =>
    hinstLC p.2 (List.of_mem_zip hp).2
  have hsub : TypeOfHM ctx (e.substTyFvars (Xs.zip instArgs))
      (Ty.substFvars (Xs.zip instArgs) (M.openVars Xs)) :=
    TypeOfHM.typ_substs_preservation (Xs.zip instArgs)
      (fun p hp => hXenv p.1 (List.of_mem_zip hp).1) h_lc he
  have hfix : e.substTyFvars (Xs.zip instArgs) = e :=
    Expr.substTyFvars_eq_self_of_not_mem_tyFreeVars (by
      intro p hp
      exact hXe p.1 (List.of_mem_zip hp).1)
  have hreg : (M.openVars Xs).IsLC := TypeOfHM.regular he
  have hty : Ty.substFvars (Xs.zip instArgs) (M.openVars Xs) = τ := by
    change Ty.substFvars (Xs.zip instArgs) (Ty.openVars Xs M.body) = τ
    exact substFvars_zip_openVars_eq (Xs := Xs) (Vs := instArgs)
      hXnodup hXVs M.body τ hinstTo hXM hreg
  rw [hfix, hty] at hsub
  exact hsub

/-- The BODY scheme of a mono member (`genGroup G τ`) is at least as general as
    its RHS entry (`mkTrivial (renameG G Xs τ)`): every instance of the opened
    shared monotype is an instance of the generalised scheme. -/
private theorem genGroup_generalizes_mkTrivial {G Xs : List Nat} {τ : Ty}
    (hτ : τ.IsLC) (hG : G.Nodup) (hX : Xs.Nodup) (hlen : Xs.length = G.length)
    (hdisj : ∀ g ∈ G, g ∉ Xs) (hXsτ : ∀ x ∈ Xs, x ∉ τ.freeVars) :
    PolyTy.Generalizes (PolyTy.genGroup G τ) (PolyTy.mkTrivial (Ty.renameG G Xs τ)) := by
  intro tyArgs ty hlc hinstTo
  have hLC : (Ty.renameG G Xs τ).IsLC := by
    unfold Ty.renameG
    refine ContainsBvarsUpTo.substFvars (fun p hp => ?_) hτ
    obtain ⟨x, _, heq⟩ := List.mem_map.mp (List.of_mem_zip hp).2
    rw [← heq]
    exact .fvar
  have hty : ty = Ty.renameG G Xs τ := InstantiatesBy.eq_of_closed hLC hinstTo
  subst ty
  set Xs' := Ty.genFilter Xs (Ty.renameG G Xs τ) with hXsdef
  refine ⟨Xs'.map (Ty.fvar ·), ?_, ?_⟩
  · intro t ht
    rcases List.mem_map.mp ht with ⟨x, _, rfl⟩
    exact .fvar
  · show InstantiatesBy (Xs'.map (Ty.fvar ·)) (Ty.closeOver (Ty.genFilter G τ) τ) (Ty.renameG G Xs τ)
    have hXlen' : Xs'.length = (Ty.genFilter G τ).length := by
      have h := congrArg PolyTy.paramCount (PolyTy.genGroup_renameG hτ hlen hG hX hdisj hXsτ)
      simp only [PolyTy.genGroup] at h
      rw [hXsdef]
      exact h.symm
    have hXnodup' : Xs'.Nodup := by rw [hXsdef]; unfold Ty.genFilter; exact hX.filter _
    have hGFnodup : (Ty.genFilter G τ).Nodup := by unfold Ty.genFilter; exact hG.filter _
    have hGFdisj : ∀ g ∈ Ty.genFilter G τ, g ∉ Xs' := by
      intro g hg hc
      exact hdisj g (Ty.mem_of_mem_genFilter hg) (by rw [hXsdef] at hc; exact Ty.mem_of_mem_genFilter hc)
    have hiv := InstantiatesBy.openVars (ty := Ty.closeOver (Ty.genFilter G τ) τ) (Xs := Xs')
      (Ty.closeOver_preserves_bvars hτ) (by rw [hXlen'])
    rw [Ty.openVars_closeOver_rename hτ hGFnodup hXlen' hGFdisj] at hiv
    rw [hXsdef] at hiv
    change InstantiatesBy ((Ty.genFilter Xs (Ty.renameG G Xs τ)).map (Ty.fvar ·))
      (Ty.closeOver (Ty.genFilter G τ) τ)
      (Ty.renameG (Ty.genFilter G τ) (Ty.genFilter Xs (Ty.renameG G Xs τ)) τ) at hiv
    rw [← Ty.renameG_eq_genFilter hlen hG hX hdisj hXsτ] at hiv
    exact hiv

/-- Pointwise: the BODY env entry of each member is at least as general as its
    RHS env entry (identical for poly members; `genGroup`-generalised for mono
    members). -/
private theorem bodyScheme_generalizes_rhsEntry {anns : List (Option PolyTy)}
    {bindings : List Expr} {specs : List RecSpec} {G Xs : List Nat}
    (hwf : RecSpecs.WF anns bindings specs G)
    (hX : Xs.Nodup) (hlen : Xs.length = G.length)
    (hdisj : ∀ g ∈ G, g ∉ Xs)
    (hXs : ∀ s ∈ specs, ∀ x ∈ Xs, x ∉ RecSpec.monoFreeVars s) :
    List.Forall₂ (PolyTy.Generalizes)
      (specs.map (RecSpec.bodyScheme G))
      (specs.map (RecSpec.rhsEntry G Xs)) := by
  have hone : ∀ s ∈ specs,
      (RecSpec.bodyScheme G s).Generalizes (RecSpec.rhsEntry G Xs s) := by
    intro s hs
    cases s with
    | mono τ =>
        simpa [RecSpec.bodyScheme, RecSpec.rhsEntry] using
          genGroup_generalizes_mkTrivial (hwf.mono_lc τ hs) hwf.nodup hX hlen hdisj
            (fun x hx => hXs (RecSpec.mono τ) hs x hx)
    | poly σ =>
        simpa [RecSpec.bodyScheme, RecSpec.rhsEntry] using
          (show PolyTy.Generalizes σ σ from fun tyArgs ty hlc hinstTo => ⟨tyArgs, hlc, hinstTo⟩)
  apply List.forall₂_of_mem_zip
  · rw [List.length_map, List.length_map]
  · intro p hp
    obtain ⟨a, b, ha, hab, hpEq⟩ := List.mem_zip_map_left hp
    have hself : ∀ {l : List RecSpec} {a : RecSpec} {b : PolyTy},
        (a, b) ∈ l.zip (l.map (RecSpec.rhsEntry G Xs)) → b = RecSpec.rhsEntry G Xs a := by
      intro l
      induction l with
      | nil => intro a b h; simp at h
      | cons hd tl ih =>
          intro a b h
          simp only [List.map_cons, List.zip_cons_cons, List.mem_cons] at h
          cases h with
          | inl heq =>
              injection heq with h1 h2
              subst a
              subst b
              rfl
          | inr h' => exact ih h'
    rw [hself hab] at hpEq
    subst hpEq
    exact hone a ha

/-- Each recursive-group member's RHS types, in the BODY context, at any instance
    of its body scheme. The machine analogue of `TypeOfElabHM.rewrap_hasScheme_*`;
    needed by `preservation`'s `forceRecclo` case. -/
theorem recclo_body_typed {ctors : CtorEnv} {Γ : Env} {anns : List (Option PolyTy)}
    {bindings : List Expr} {specs : List RecSpec} {G L : List Nat}
    {e : Expr} {spec : RecSpec} {τ : Ty}
    (hwf : RecSpecs.WF anns bindings specs G)
    (hmono : RecSpecs.MonoTyped TypeOfHM ⟨Γ, ctors⟩ bindings specs G L)
    (hpoly : RecSpecs.PolyTyped TypeOfHM ⟨Γ, ctors⟩ bindings specs G L)
    (herased : e.IsErased)
    (hmem : (e, spec) ∈ bindings.zip specs)
    (hinst : Instantiates (RecSpec.bodyScheme G spec) τ) :
    TypeOfHM (RecSpecs.bodyCtx ⟨Γ, ctors⟩ specs G) e τ := by
  cases spec with
  | mono τ₀ =>
      have hτlc : τ₀.IsLC := hwf.mono_lc τ₀ (List.of_mem_zip hmem).2
      rcases hinst with ⟨instArgs, hinstLC, hinstTo⟩
      obtain ⟨Xs, hXlen, hXnodup, hXavoid⟩ :=
        exists_fresh_names
          (L ++ G ++ (specs.map RecSpec.monoFreeVars).flatten
            ++ Env.freeVars (specs.map (RecSpec.bodyScheme G) ++ Γ)
            ++ e.tyFreeVars ++ Ty.freeVarsList instArgs ++ ((PolyTy.genGroup G τ₀).body).freeVars)
          G.length
      have hXL : ∀ x ∈ Xs, x ∉ L := fun x hx hc =>
        hXavoid x hx (by
          simp [List.mem_append]
          tauto)
      have hXfresh : FreshNames L G.length Xs := ⟨hXlen, hXnodup, hXL⟩
      have hdisj : ∀ g ∈ G, g ∉ Xs := fun g hg hc =>
        hXavoid g hc (by
          simp [List.mem_append]
          tauto)
      have hXs_monos : ∀ s ∈ specs, ∀ x ∈ Xs, x ∉ RecSpec.monoFreeVars s := fun s hs x hx hc =>
        hXavoid x hx (by
          have hflat : x ∈ (specs.map RecSpec.monoFreeVars).flatten :=
            List.mem_flatten.mpr ⟨RecSpec.monoFreeVars s, List.mem_map.mpr ⟨s, hs, rfl⟩, hc⟩
          simp [List.mem_append, hflat])
      have hXsτ₀ : ∀ x ∈ Xs, x ∉ τ₀.freeVars := hXs_monos (RecSpec.mono τ₀) (List.of_mem_zip hmem).2
      have hXs_env : ∀ x ∈ Xs, x ∉ Env.freeVars (specs.map (RecSpec.bodyScheme G) ++ Γ) := fun x hx hc =>
        hXavoid x hx (by
          simp [List.mem_append]
          tauto)
      have hXs_e : ∀ x ∈ Xs, x ∉ e.tyFreeVars := fun x hx hc =>
        hXavoid x hx (by
          simp [List.mem_append]
          tauto)
      have hXs_Vs : ∀ x ∈ Xs, x ∉ Ty.freeVarsList instArgs := fun x hx hc =>
        hXavoid x hx (by
          simp [List.mem_append]
          tauto)
      have hXs_M : ∀ x ∈ Xs, x ∉ ((PolyTy.genGroup G τ₀).body).freeVars := fun x hx hc =>
        hXavoid x hx (by
          simp [List.mem_append]
          tauto)
      have he : TypeOfHM (RecSpecs.rhsCtx ⟨Γ, ctors⟩ specs G Xs) e (Ty.renameG G Xs τ₀) :=
        hmono Xs hXfresh (e, .mono τ₀) hmem τ₀ rfl
      have hb : TypeOfHM ⟨specs.map (RecSpec.bodyScheme G) ++ Γ, ctors⟩ e (Ty.renameG G Xs τ₀) :=
        TypeOfHM.weaken_schemes
          (bodyScheme_generalizes_rhsEntry hwf hXnodup hXlen hdisj hXs_monos) he
      set Xs' := Ty.genFilter Xs (Ty.renameG G Xs τ₀) with hXsdef
      have hXlen' : Xs'.length = (Ty.genFilter G τ₀).length := by
        have h := congrArg PolyTy.paramCount (PolyTy.genGroup_renameG hτlc hXlen hwf.nodup hXnodup hdisj hXsτ₀)
        simp only [PolyTy.genGroup] at h
        rw [hXsdef]
        exact h.symm
      have hXnodup' : Xs'.Nodup := by rw [hXsdef]; unfold Ty.genFilter; exact hXnodup.filter _
      have hGFnodup : (Ty.genFilter G τ₀).Nodup := by unfold Ty.genFilter; exact hwf.nodup.filter _
      have hGFdisj : ∀ g ∈ Ty.genFilter G τ₀, g ∉ Xs' := by
        intro g hg hc
        exact hdisj g (Ty.mem_of_mem_genFilter hg) (by rw [hXsdef] at hc; exact Ty.mem_of_mem_genFilter hc)
      have hrewrite : Ty.renameG G Xs τ₀ = Ty.openVars Xs' (Ty.closeOver (Ty.genFilter G τ₀) τ₀) := by
        rw [Ty.renameG_eq_genFilter hXlen hwf.nodup hXnodup hdisj hXsτ₀]
        exact (Ty.openVars_closeOver_rename hτlc hGFnodup hXlen' hGFdisj).symm
      rw [hrewrite] at hb
      have h_lc : ∀ p ∈ Xs'.zip instArgs, Ty.IsLC p.2 := fun p hp => hinstLC p.2 (List.of_mem_zip hp).2
      have hsub := TypeOfHM.typ_substs_preservation (Xs'.zip instArgs)
        (fun p hp => hXs_env p.1 (Ty.mem_of_mem_genFilter (List.of_mem_zip hp).1)) h_lc hb
      have hfix : e.substTyFvars (Xs'.zip instArgs) = e :=
        Expr.substTyFvars_eq_self_of_not_mem_tyFreeVars (by
          intro p hp
          exact hXs_e p.1 (Ty.mem_of_mem_genFilter (List.of_mem_zip hp).1))
      have hreg : (((PolyTy.genGroup G τ₀).body).openVars Xs').IsLC := TypeOfHM.regular hb
      have hty : Ty.substFvars (Xs'.zip instArgs) (Ty.openVars Xs' (Ty.closeOver (Ty.genFilter G τ₀) τ₀)) = τ := by
        exact substFvars_zip_openVars_eq (Xs := Xs') (Vs := instArgs) hXnodup'
          (fun X hX => hXs_Vs X (Ty.mem_of_mem_genFilter hX))
          (Ty.closeOver (Ty.genFilter G τ₀) τ₀) τ hinstTo
          (fun X hX => hXs_M X (Ty.mem_of_mem_genFilter hX)) hreg
      rw [hfix, hty] at hsub
      exact hsub
  | poly σ =>
      rcases hinst with ⟨instArgs, hinstLC, hinstTo⟩
      obtain ⟨Xs, hXlen, hXnodup, hXavoid⟩ :=
        exists_fresh_names
          (L ++ G ++ (specs.map RecSpec.monoFreeVars).flatten
            ++ Env.freeVars (specs.map (RecSpec.bodyScheme G) ++ Γ))
          G.length
      have hXL : ∀ x ∈ Xs, x ∉ L := fun x hx hc =>
        hXavoid x hx (by
          simp [List.mem_append]
          tauto)
      have hXfresh : FreshNames L G.length Xs := ⟨hXlen, hXnodup, hXL⟩
      have hdisj : ∀ g ∈ G, g ∉ Xs := fun g hg hc =>
        hXavoid g hc (by
          simp [List.mem_append]
          tauto)
      have hXs_monos : ∀ s ∈ specs, ∀ x ∈ Xs, x ∉ RecSpec.monoFreeVars s := fun s hs x hx hc =>
        hXavoid x hx (by
          have hflat : x ∈ (specs.map RecSpec.monoFreeVars).flatten :=
            List.mem_flatten.mpr ⟨RecSpec.monoFreeVars s, List.mem_map.mpr ⟨s, hs, rfl⟩, hc⟩
          simp [List.mem_append, hflat])
      obtain ⟨Ys, hYlen, hYnodup, hYavoid⟩ :=
        exists_fresh_names
          (L ++ Xs ++ Env.freeVars (specs.map (RecSpec.bodyScheme G) ++ Γ)
            ++ e.tyFreeVars ++ Ty.freeVarsList instArgs ++ σ.body.freeVars)
          σ.paramCount
      have hYLX : ∀ y ∈ Ys, y ∉ L ++ Xs := fun y hy hc =>
        hYavoid y hy (by
          simp only [List.mem_append] at hc ⊢
          tauto)
      have hYfresh : FreshNames (L ++ Xs) σ.paramCount Ys := ⟨hYlen, hYnodup, hYLX⟩
      have hYs_env : ∀ y ∈ Ys, y ∉ Env.freeVars (specs.map (RecSpec.bodyScheme G) ++ Γ) := fun y hy hc =>
        hYavoid y hy (by
          simp [List.mem_append]
          tauto)
      have hYs_e : ∀ y ∈ Ys, y ∉ e.tyFreeVars := fun y hy hc =>
        hYavoid y hy (by
          simp [List.mem_append]
          tauto)
      have hYs_Vs : ∀ y ∈ Ys, y ∉ Ty.freeVarsList instArgs := fun y hy hc =>
        hYavoid y hy (by
          simp [List.mem_append]
          tauto)
      have hYs_σ : ∀ y ∈ Ys, y ∉ σ.body.freeVars := fun y hy hc =>
        hYavoid y hy (by
          simp [List.mem_append]
          tauto)
      have hpoly' : TypeOfHM (RecSpecs.rhsCtx ⟨Γ, ctors⟩ specs G Xs) (e.openTyVars Ys) (σ.openVars Ys) :=
        hpoly Xs hXfresh (e, .poly σ) hmem σ rfl Ys hYfresh
      have hopen : e.openTyVars Ys = e := Expr.openTyVars_eq_self_of_erased herased Ys
      have he : TypeOfHM (RecSpecs.rhsCtx ⟨Γ, ctors⟩ specs G Xs) e (σ.openVars Ys) := by
        simpa [hopen] using hpoly'
      have hb : TypeOfHM ⟨specs.map (RecSpec.bodyScheme G) ++ Γ, ctors⟩ e (σ.openVars Ys) :=
        TypeOfHM.weaken_schemes
          (bodyScheme_generalizes_rhsEntry hwf hXnodup hXlen hdisj hXs_monos) he
      have h_lc : ∀ p ∈ Ys.zip instArgs, Ty.IsLC p.2 := fun p hp => hinstLC p.2 (List.of_mem_zip hp).2
      have hsub := TypeOfHM.typ_substs_preservation (Ys.zip instArgs)
        (fun p hp => hYs_env p.1 (List.of_mem_zip hp).1) h_lc hb
      have hfix : e.substTyFvars (Ys.zip instArgs) = e :=
        Expr.substTyFvars_eq_self_of_not_mem_tyFreeVars (by
          intro p hp
          exact hYs_e p.1 (List.of_mem_zip hp).1)
      have hreg : ContainsBvarsUpTo 0 (Ty.openVars Ys σ.body) := by
        simpa [PolyTy.openVars] using TypeOfHM.regular hb
      have hty : Ty.substFvars (Ys.zip instArgs) (σ.openVars Ys) = τ := by
        simpa [PolyTy.openVars] using
          (substFvars_zip_openVars_eq (Xs := Ys) (Vs := instArgs) hYnodup
            (fun X hX => hYs_Vs X hX)
            σ.body τ hinstTo
            (fun X hX => hYs_σ X hX) hreg)
      rw [hfix, hty] at hsub
      exact hsub

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
      (hfv : IsVal fv)
      (hv : ∃ σ, ValTyped ctors fv σ ∧ Instantiates σ (.arrow A B))
      (hk : KontTyped ctors k B ρ) :
      KontTyped ctors (.appFun fv k) A ρ
  | matchSel {E branches k} {τ ρ ρ' : Ty} {Γ : Env}
      (hE : EnvOK ctors E Γ)
      (hbranches : ∀ branch ∈ branches, TypeOfMatchBranch ⟨Γ, ctors⟩ branch τ ρ)
      (hne : branches ≠ [])
      (hk : KontTyped ctors k ρ ρ') :
      KontTyped ctors (.matchSel E branches k) τ ρ'

/-- A machine state is well-typed at result type `ρ`. -/
def StateOK (ctors : CtorEnv) (s : State) (ρ : Ty) : Prop :=
  match s with
  | .eval E e k => ∃ Γ τ, EnvOK ctors E Γ ∧ TypeOfHM ⟨Γ, ctors⟩ e τ ∧ KontTyped ctors k τ ρ
  | .ret v k => ∃ σ τ, ValTyped ctors v σ ∧ Instantiates σ τ ∧ KontTyped ctors k τ ρ

/-- Match coverage (machine-level analogue of `AllMatchesExhaustive.match_`): there
    is a type name `tyName` such that every NAMED branch's ctor has that type name
    (the "pin" — what links the coverage to the scrutinee's type via the branch's
    `scrut_eq`), and every ctor of `tyName` is matched by some branch (a named
    branch by name+arity, a wildcard by default). Carried by `ExhaustiveKont.matchSel`
    so `progress` can find a branch for whatever ctor the scrutinee evaluates to. -/
def MatchCovered (ctors : CtorEnv) (branches : List (MatchPattern × Expr)) : Prop :=
  ∃ tyName : TyName,
    (∀ (c : CtorName) (n : Nat) (body : Expr), (MatchPattern.named c n, body) ∈ branches →
       ∃ ctor, LookupList.get? ctors c = some ctor ∧ ctor.tyName = tyName) ∧
    (∀ (name : CtorName) (ctor : Ctor), LookupList.get? ctors name = some ctor →
      ctor.tyName = tyName →
      ∃ (pat : MatchPattern) (body : Expr), (pat, body) ∈ branches ∧
        pat.matchesCtor name ctor.contents.length = true)

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
          (∀ pb ∈ branches, AllMatchesExhaustive ctors pb.2) ∧
          MatchCovered ctors branches ∧ ExhaustiveKont ctors k

end

/-- Exhaustiveness of a whole machine state. -/
def ExhaustiveState (ctors : CtorEnv) : State → Prop
  | .eval E e k => ExhaustiveEnv ctors E ∧ AllMatchesExhaustive ctors e ∧ ExhaustiveKont ctors k
  | .ret v k => ExhaustiveVal ctors v ∧ ExhaustiveKont ctors k

/-! ## Erased-ness of a machine state

Every term embedded in a state is `Expr.IsErased` (no scoped type-variable
references). This is a *structural* property — the reduction never introduces
annotations, so it is preserved by stepping — and it is what makes the machine's
polymorphic members typeable: a poly member's RHS is closed, so `openTyVars` is a
no-op on it (`Expr.openTyVars_eq_self_of_erased`). -/

mutual

  def Val.IsErased : Val → Prop
    | .prim _ => True
    | .primOp _ => True
    | .primOpApp _ v => v.IsErased
    | .lam body E => body.IsErased ∧ ∀ v ∈ E, v.IsErased
    | .thunk ann e E => (∀ σ, ann = some σ → σ.WF) ∧ e.IsErased ∧ ∀ v ∈ E, v.IsErased
    | .recclo anns bindings E _ => (∀ σ, some σ ∈ anns → σ.WF) ∧ (∀ b ∈ bindings, b.IsErased) ∧ ∀ v ∈ E, v.IsErased
    | .ctorV _ args => ∀ a ∈ args, a.IsErased

  def ErasedEnv : VEnv → Prop
    | [] => True
    | v :: E => v.IsErased ∧ ErasedEnv E

  def ErasedKont : Kont → Prop
    | .nil => True
    | .appArg E arg k => ErasedEnv E ∧ arg.IsErased ∧ ErasedKont k
    | .appFun v k => v.IsErased ∧ ErasedKont k
    | .matchSel E branches k =>
        ErasedEnv E ∧ (∀ pb ∈ branches, pb.2.IsErased) ∧ ErasedKont k

end

/-- Erased-ness of a whole machine state. -/
def ErasedState : State → Prop
  | .eval E e k => ErasedEnv E ∧ e.IsErased ∧ ErasedKont k
  | .ret v k => v.IsErased ∧ ErasedKont k

/-! ## Type safety -/

/-! ## Progress helpers -/

/-- A well-typed value environment has the same length as the typing context. -/
private theorem envOK_length {ctors : CtorEnv} {E : VEnv} {Γ : Env} (hE : EnvOK ctors E Γ) :
    E.length = Γ.length := by
  cases hE with
  | nil => rfl
  | cons hv htl => simp [envOK_length htl]

/-- `PrimBinOp.ty` never returns a bare primitive type. -/
private theorem primOp_ty_not_prim {ctors : CtorEnv} {op : PrimBinOp} {τ : Ty} {p : PrimTy}
    (h : PrimBinOp.ty ctors op = some τ) (hp : τ = Ty.prim p) : False := by
  subst hp
  cases op with
  | intAdd => simp [PrimBinOp.ty] at h
  | intSub => simp [PrimBinOp.ty] at h
  | intLt =>
      cases h1 : LookupList.get? ctors ⟨"True"⟩ with
      | none => simp [PrimBinOp.ty, h1] at h
      | some tc =>
          cases h2 : LookupList.get? ctors ⟨"False"⟩ with
          | none => simp [PrimBinOp.ty, h1, h2] at h
          | some fc => simp [PrimBinOp.ty, h1, h2] at h
  | charLt =>
      cases h1 : LookupList.get? ctors ⟨"True"⟩ with
      | none => simp [PrimBinOp.ty, h1] at h
      | some tc =>
          cases h2 : LookupList.get? ctors ⟨"False"⟩ with
          | none => simp [PrimBinOp.ty, h1, h2] at h
          | some fc => simp [PrimBinOp.ty, h1, h2] at h

/-- `PrimBinOp.ty` never returns an arrow whose result is the `int` type. -/
private theorem primOp_ty_arrow_not_int {ctors : CtorEnv} {op : PrimBinOp} {τ₁ : Ty}
    (h : PrimBinOp.ty ctors op = some (.arrow τ₁ (Ty.prim .int))) : False := by
  cases op with
  | intAdd => simp [PrimBinOp.ty] at h
  | intSub => simp [PrimBinOp.ty] at h
  | intLt =>
      cases h1 : LookupList.get? ctors ⟨"True"⟩ with
      | none => simp [PrimBinOp.ty, h1] at h
      | some tc =>
          cases h2 : LookupList.get? ctors ⟨"False"⟩ with
          | none => simp [PrimBinOp.ty, h1, h2] at h
          | some fc => simp [PrimBinOp.ty, h1, h2] at h
  | charLt =>
      cases h1 : LookupList.get? ctors ⟨"True"⟩ with
      | none => simp [PrimBinOp.ty, h1] at h
      | some tc =>
          cases h2 : LookupList.get? ctors ⟨"False"⟩ with
          | none => simp [PrimBinOp.ty, h1, h2] at h
          | some fc => simp [PrimBinOp.ty, h1, h2] at h

/-- `PrimBinOp.ty` never returns an arrow whose result is the `char` type. -/
private theorem primOp_ty_arrow_not_char {ctors : CtorEnv} {op : PrimBinOp} {τ₁ : Ty}
    (h : PrimBinOp.ty ctors op = some (.arrow τ₁ (Ty.prim .char))) : False := by
  cases op with
  | intAdd => simp [PrimBinOp.ty] at h
  | intSub => simp [PrimBinOp.ty] at h
  | intLt =>
      cases h1 : LookupList.get? ctors ⟨"True"⟩ with
      | none => simp [PrimBinOp.ty, h1] at h
      | some tc =>
          cases h2 : LookupList.get? ctors ⟨"False"⟩ with
          | none => simp [PrimBinOp.ty, h1, h2] at h
          | some fc => simp [PrimBinOp.ty, h1, h2] at h
  | charLt =>
      cases h1 : LookupList.get? ctors ⟨"True"⟩ with
      | none => simp [PrimBinOp.ty, h1] at h
      | some tc =>
          cases h2 : LookupList.get? ctors ⟨"False"⟩ with
          | none => simp [PrimBinOp.ty, h1, h2] at h
          | some fc => simp [PrimBinOp.ty, h1, h2] at h

/-- `PrimBinOp.ty` never returns a `customTy` type. -/
private theorem primOp_ty_not_customTy {ctors : CtorEnv} {op : PrimBinOp} {τ : Ty}
    {nm : TyName} {tys : List Ty}
    (h : PrimBinOp.ty ctors op = some τ) (hc : τ = Ty.customTy nm tys) : False := by
  subst hc
  cases op with
  | intAdd => simp [PrimBinOp.ty] at h
  | intSub => simp [PrimBinOp.ty] at h
  | intLt =>
      cases h1 : LookupList.get? ctors ⟨"True"⟩ with
      | none => simp [PrimBinOp.ty, h1] at h
      | some tc =>
          cases h2 : LookupList.get? ctors ⟨"False"⟩ with
          | none => simp [PrimBinOp.ty, h1, h2] at h
          | some fc => simp [PrimBinOp.ty, h1, h2] at h
  | charLt =>
      cases h1 : LookupList.get? ctors ⟨"True"⟩ with
      | none => simp [PrimBinOp.ty, h1] at h
      | some tc =>
          cases h2 : LookupList.get? ctors ⟨"False"⟩ with
          | none => simp [PrimBinOp.ty, h1, h2] at h
          | some fc => simp [PrimBinOp.ty, h1, h2] at h

/-- `PrimBinOp.ty` never returns an arrow whose result is a `customTy`. -/
private theorem primOp_ty_arrow_not_customTy {ctors : CtorEnv} {op : PrimBinOp} {τ₁ : Ty}
    {nm : TyName} {tys : List Ty}
    (h : PrimBinOp.ty ctors op = some (.arrow τ₁ (Ty.customTy nm tys))) : False := by
  cases op with
  | intAdd => simp [PrimBinOp.ty] at h
  | intSub => simp [PrimBinOp.ty] at h
  | intLt =>
      cases h1 : LookupList.get? ctors ⟨"True"⟩ with
      | none => simp [PrimBinOp.ty, h1] at h
      | some tc =>
          cases h2 : LookupList.get? ctors ⟨"False"⟩ with
          | none => simp [PrimBinOp.ty, h1, h2] at h
          | some fc => simp [PrimBinOp.ty, h1, h2] at h
  | charLt =>
      cases h1 : LookupList.get? ctors ⟨"True"⟩ with
      | none => simp [PrimBinOp.ty, h1] at h
      | some tc =>
          cases h2 : LookupList.get? ctors ⟨"False"⟩ with
          | none => simp [PrimBinOp.ty, h1, h2] at h
          | some fc => simp [PrimBinOp.ty, h1, h2] at h

/-- A `wrapArrows` of a `customTy` head is never a bare primitive type. -/
private theorem wrapArrows_customTy_ne_prim {nm : TyName} {tys rem : List Ty} {p : PrimTy}
    (h : Ty.wrapArrows (.customTy nm tys) rem = Ty.prim p) : False := by
  cases rem with
  | nil => simp [Ty.wrapArrows] at h
  | cons a as => simp [Ty.wrapArrows] at h

/-- Canonical forms at `int`: an already-evaluated value at the `int` monotype is
    an integer literal. -/
private theorem valTyped_mono_canonical_int {ctors : CtorEnv} {v : Val}
    (hvIsVal : IsVal v) (hv : ValTyped ctors v (PolyTy.mkTrivial (Ty.prim .int))) :
    ∃ n, v = .prim (.int n) := by
  cases v with
  | prim p =>
      cases p with
      | int n => exact ⟨n, rfl⟩
      | unit => cases hv
      | nat n => cases hv
      | char c => cases hv
  | primOp op =>
      cases hv with
      | primOp hprim => exfalso; exact primOp_ty_not_prim hprim rfl
  | primOpApp op v' =>
      cases hv with
      | primOpApp hIsVal' hv' hprim =>
          exfalso
          exact primOp_ty_arrow_not_int hprim
  | lam body E => cases hv
  | thunk ann e E => simp [IsVal] at hvIsVal
  | recclo anns bindings E j => simp [IsVal] at hvIsVal
  | ctorV name args =>
      exfalso
      generalize hty : PolyTy.mkTrivial (Ty.prim .int) = M at hv
      cases hv with
      | ctorV hlook htyArgs hargs hfields =>
          exact wrapArrows_customTy_ne_prim (by
            symm
            simpa [PolyTy.mkTrivial] using congrArg PolyTy.body hty)

/-- Canonical forms at `char`: an already-evaluated value at the `char` monotype
    is a character literal. -/
private theorem valTyped_mono_canonical_char {ctors : CtorEnv} {v : Val}
    (hvIsVal : IsVal v) (hv : ValTyped ctors v (PolyTy.mkTrivial (Ty.prim .char))) :
    ∃ c, v = .prim (.char c) := by
  cases v with
  | prim p =>
      cases p with
      | char c => exact ⟨c, rfl⟩
      | unit => cases hv
      | int n => cases hv
      | nat n => cases hv
  | primOp op =>
      cases hv with
      | primOp hprim => exfalso; exact primOp_ty_not_prim hprim rfl
  | primOpApp op v' =>
      cases hv with
      | primOpApp hIsVal' hv' hprim =>
          exfalso
          exact primOp_ty_arrow_not_char hprim
  | lam body E => cases hv
  | thunk ann e E => simp [IsVal] at hvIsVal
  | recclo anns bindings E j => simp [IsVal] at hvIsVal
  | ctorV name args =>
      exfalso
      generalize hty : PolyTy.mkTrivial (Ty.prim .char) = M at hv
      cases hv with
      | ctorV hlook htyArgs hargs hfields =>
          exact wrapArrows_customTy_ne_prim (by
            symm
            simpa [PolyTy.mkTrivial] using congrArg PolyTy.body hty)

/-- Canonical forms at the `int` scheme: an already-evaluated value whose scheme
    instantiates to `int` is an integer literal. -/
private theorem valTyped_canonical_int {ctors : CtorEnv} {v : Val} {σ : PolyTy} {A : Ty}
    (hvIsVal : IsVal v) (hv : ValTyped ctors v σ) (hinst : Instantiates σ A)
    (hA : A = Ty.prim .int) : ∃ n, v = .prim (.int n) := by
  have hv' : ValTyped ctors v (PolyTy.mkTrivial (Ty.prim .int)) := by
    simpa [hA] using (ValTyped_inst_of_isVal hvIsVal hv hinst)
  exact valTyped_mono_canonical_int hvIsVal hv'

/-- Canonical forms at the `char` scheme: an already-evaluated value whose scheme
    instantiates to `char` is a character literal. -/
private theorem valTyped_canonical_char {ctors : CtorEnv} {v : Val} {σ : PolyTy} {A : Ty}
    (hvIsVal : IsVal v) (hv : ValTyped ctors v σ) (hinst : Instantiates σ A)
    (hA : A = Ty.prim .char) : ∃ c, v = .prim (.char c) := by
  have hv' : ValTyped ctors v (PolyTy.mkTrivial (Ty.prim .char)) := by
    simpa [hA] using (ValTyped_inst_of_isVal hvIsVal hv hinst)
  exact valTyped_mono_canonical_char hvIsVal hv'

/-- The `int`-arithmetic primops' operands are `int`. -/
private theorem primOp_int_operands {ctors : CtorEnv} {op : PrimBinOp} {τ₁ A B : Ty}
    (h : PrimBinOp.ty ctors op = some (.arrow τ₁ (.arrow A B)))
    (hop : op = .intAdd ∨ op = .intSub) :
    τ₁ = .prim .int ∧ A = .prim .int := by
  rcases hop with hEq | hEq
  · subst hEq
    simp [PrimBinOp.ty] at h
    rcases h with ⟨hτ₁, hA, hB⟩
    exact ⟨hτ₁.symm, hA.symm⟩
  · subst hEq
    simp [PrimBinOp.ty] at h
    rcases h with ⟨hτ₁, hA, hB⟩
    exact ⟨hτ₁.symm, hA.symm⟩

/-- The `intLt` primop's operands are `int`. -/
private theorem primOp_intLt_operands {ctors : CtorEnv} {τ₁ A B : Ty}
    (h : PrimBinOp.ty ctors .intLt = some (.arrow τ₁ (.arrow A B))) :
    τ₁ = .prim .int ∧ A = .prim .int := by
  cases h1 : LookupList.get? ctors ⟨"True"⟩ with
  | none => simp [PrimBinOp.ty, h1] at h
  | some tc =>
      cases h2 : LookupList.get? ctors ⟨"False"⟩ with
      | none => simp [PrimBinOp.ty, h1, h2] at h
      | some fc =>
          simp [PrimBinOp.ty, h1, h2] at h
          rcases h with ⟨htc, hx⟩
          rcases hx with ⟨hτ₁, hA, hB⟩
          exact ⟨hτ₁.symm, hA.symm⟩

/-- The `charLt` primop's operands are `char`. -/
private theorem primOp_charLt_operands {ctors : CtorEnv} {τ₁ A B : Ty}
    (h : PrimBinOp.ty ctors .charLt = some (.arrow τ₁ (.arrow A B))) :
    τ₁ = .prim .char ∧ A = .prim .char := by
  cases h1 : LookupList.get? ctors ⟨"True"⟩ with
  | none => simp [PrimBinOp.ty, h1] at h
  | some tc =>
      cases h2 : LookupList.get? ctors ⟨"False"⟩ with
      | none => simp [PrimBinOp.ty, h1, h2] at h
      | some fc =>
          simp [PrimBinOp.ty, h1, h2] at h
          rcases h with ⟨htc, hx⟩
          rcases hx with ⟨hτ₁, hA, hB⟩
          exact ⟨hτ₁.symm, hA.symm⟩

/-- A primop typing an application shape is one of the four built-ins. -/
private theorem primOp_ty_delta {ctors : CtorEnv} {op : PrimBinOp} {τ₁ A B : Ty}
    (h : PrimBinOp.ty ctors op = some (.arrow τ₁ (.arrow A B))) :
    (op = .intAdd ∨ op = .intSub) ∨ (op = .intLt ∨ op = .charLt) := by
  cases op with
  | intAdd => exact .inl (.inl rfl)
  | intSub => exact .inl (.inr rfl)
  | intLt => exact .inr (.inl rfl)
  | charLt => exact .inr (.inr rfl)

/-- A `wrapArrows` instantiation decomposes pointwise: the instantiated type is
    the wrapped result at the instantiated contents. (A copy of
    `instantiatesBy_wrapArrows`, defined earlier so `progress` can use it.) -/
private theorem wrapArrows_inst {tyArgs : List Ty} {result : Ty} :
    ∀ (contents : List Ty) (τ : Ty),
      InstantiatesBy tyArgs (Ty.wrapArrows result contents) τ →
      ∃ resultI contentsI, τ = Ty.wrapArrows resultI contentsI ∧
        InstantiatesBy tyArgs result resultI ∧
        List.Forall₂ (InstantiatesBy tyArgs) contents contentsI := by
  intro contents
  induction contents with
  | nil =>
      intro τ h
      exact ⟨τ, [], rfl, h, .nil⟩
  | cons c cs ih =>
      intro τ h
      change InstantiatesBy tyArgs (Ty.arrow c (Ty.wrapArrows result cs)) τ at h
      cases h with
      | arrow hc hrest =>
          rename_i instFst instSnd
          rcases ih instSnd hrest with ⟨resultI, csI, hEq, hres, hcs⟩
          refine ⟨resultI, instFst :: csI, ?_, hres, .cons hc hcs⟩
          rw [hEq]
          simp [Ty.wrapArrows]

/-- If some branch matches a constructor (name, arity), the FIRST such branch is
    a `FirstMatchingBranch` witness. -/
private theorem firstMatchingBranch_exists {name : CtorName} {arity : Nat}
    {branches : List (MatchPattern × Expr)}
    (h : ∃ pat body, (pat, body) ∈ branches ∧ pat.matchesCtor name arity = true) :
    ∃ pat body, FirstMatchingBranch name arity branches pat body := by
  induction branches with
  | nil =>
      obtain ⟨pat, body, hmem, hcov⟩ := h
      exact nomatch hmem
  | cons hd tl ih =>
      obtain ⟨pat, body, hmem, hcov⟩ := h
      cases hmem with
      | head _ =>
          exact ⟨pat, body, .here hcov⟩
      | tail _ hmem' =>
          by_cases hc : hd.1.matchesCtor name arity = true
          · exact ⟨hd.1, hd.2, .here hc⟩
          · rcases ih ⟨pat, body, hmem', hcov⟩ with ⟨p, b, hf⟩
            exact ⟨p, b, .there ((Bool.not_eq_true _).mp hc) hf⟩

/-- In a `matchSel` frame awaiting a constructor value `(.ctorV name args)`, the
    `MatchCovered` guarantee plus the branch typings produce a
    `FirstMatchingBranch` for the scrutinee's constructor. (The branch-typing
    pin: the scrutinee's ctor has the covered `tyName`.) -/
private theorem matchSel_ctorV_first {ctors : CtorEnv} {name : CtorName} {args : List Val}
    {branches : List (MatchPattern × Expr)} {τ ρ' : Ty} {Γ : Env}
    {ctor : Ctor} {tyArgs instContents remContents : List Ty}
    (hlook : LookupList.get? ctors name = some ctor)
    (hargs : List.Forall₂ (fun a t => ValTyped ctors a (PolyTy.mkTrivial t)) args instContents)
    (hfields : List.Forall₂ (InstantiatesBy tyArgs) ctor.contents (instContents ++ remContents))
    (hinst : Instantiates (PolyTy.mkTrivial (Ty.wrapArrows (Ty.customTy ctor.tyName tyArgs) remContents)) τ)
    (hbranches : ∀ branch ∈ branches, TypeOfMatchBranch ⟨Γ, ctors⟩ branch τ ρ')
    (hne : branches ≠ [])
    (hcover : MatchCovered ctors branches) :
    ∃ pat body, FirstMatchingBranch name args.length branches pat body := by
  rcases hinst with ⟨instArgs, hinstLC, hinstTo⟩
  rcases wrapArrows_inst (result := Ty.customTy ctor.tyName tyArgs) (contents := remContents) (τ := τ) hinstTo
    with ⟨resultI, contentsI, hEq2, hresI, hcontI⟩
  obtain ⟨⟨pat0, body0⟩, rest0, hbeq⟩ := List.exists_cons_of_ne_nil hne
  have hb0 : (pat0, body0) ∈ branches := by
    rw [hbeq]
    exact List.mem_cons_self
  rcases hcover with ⟨tyName, hpin, hcoverage⟩
  cases pat0 with
  | wildcard =>
      refine ⟨.wildcard, body0, ?_⟩
      rw [hbeq]
      exact FirstMatchingBranch.here (pat := .wildcard) rfl
  | named c0 n0 =>
      cases hbranches (.named c0 n0, body0) hb0 with
      | mk bspec _hbctx _hbodies =>
          rename_i ctorS tyArgsS instContentsS
          rcases bspec with ⟨hlookS, hscrutEq, _arity, _bindcount, _fieldsS⟩
          have hcontentsI_nil : contentsI = [] := by
            cases contentsI with
            | nil => rfl
            | cons c' cs' =>
                have hcon : Ty.customTy ctorS.tyName tyArgsS = Ty.arrow c' (Ty.wrapArrows resultI cs') :=
                  hscrutEq.symm.trans hEq2
                simp at hcon
          have hresultI : resultI = Ty.customTy ctorS.tyName tyArgsS := by
            rw [hcontentsI_nil] at hEq2
            simpa [Ty.wrapArrows] using hEq2.symm.trans hscrutEq
          have hresI' : InstantiatesBy instArgs (Ty.customTy ctor.tyName tyArgs) (Ty.customTy ctorS.tyName tyArgsS) := by
            simpa [hresultI] using hresI
          have htyName : ctor.tyName = ctorS.tyName := by
            generalize hnm1 : ctor.tyName = n1 at hresI'
            generalize hnm2 : ctorS.tyName = n2 at hresI'
            cases hresI' with
            | customTy _ => rfl
          rcases hpin c0 n0 body0 hb0 with ⟨ctor', hlook', htyName'⟩
          have hctorEq : ctor' = ctorS := Option.some.inj (hlook'.symm.trans hlookS)
          have htyS : ctorS.tyName = tyName := by
            rw [← hctorEq]
            exact htyName'
          have htyN : ctor.tyName = tyName := by
            rw [htyName]
            exact htyS
          rcases hcoverage name ctor hlook htyN with ⟨pat, body, hmem, hcov⟩
          have hremContents : remContents = [] := by
            rw [hcontentsI_nil] at hcontI
            by_contra hc
            rcases List.exists_cons_of_ne_nil hc with ⟨hd, tl, hceq⟩
            rw [hceq] at hcontI
            cases hcontI
          have hlen : args.length = ctor.contents.length := by
            have h1 := hargs.length_eq
            have h2 := hfields.length_eq
            rw [hremContents] at h2
            simp [h1, h2]
          have hcov' : pat.matchesCtor name args.length = true := by
            rw [hlen]
            exact hcov
          rcases firstMatchingBranch_exists ⟨pat, body, hmem, hcov'⟩ with ⟨pat', body', hfirst⟩
          exact ⟨pat', body', hfirst⟩

/-- Progress: a well-typed, exhaustive machine state is final (a value with an
    empty continuation) or can take a step. -/
theorem progress {ctors : CtorEnv} {s : State} {ρ : Ty}
    (h : StateOK ctors s ρ) (hexh : ExhaustiveState ctors s) :
    (∃ v, s = .ret v .nil) ∨ ∃ s', StepM s s' := by
  cases s with
  | eval E e k =>
      unfold StateOK at h
      rcases h with ⟨Γ, τ, hE, he, hk⟩
      cases he with
      | primLitUnit =>
          exact .inr ⟨_, StepM.primLit⟩
      | primLitInt =>
          exact .inr ⟨_, StepM.primLit⟩
      | primLitNat =>
          exact .inr ⟨_, StepM.primLit⟩
      | primLitChar =>
          exact .inr ⟨_, StepM.primLit⟩
      | primBinOpIntAdd =>
          exact .inr ⟨_, StepM.primBinOp⟩
      | primBinOpIntSub =>
          exact .inr ⟨_, StepM.primBinOp⟩
      | primBinOpIntLt _ _ =>
          exact .inr ⟨_, StepM.primBinOp⟩
      | primBinOpCharLt _ _ =>
          exact .inr ⟨_, StepM.primBinOp⟩
      | lambda =>
          exact .inr ⟨_, StepM.lambda⟩
      | app =>
          exact .inr ⟨_, StepM.app⟩
      | letIn =>
          exact .inr ⟨_, StepM.letIn⟩
      | letRec =>
          exact .inr ⟨_, StepM.letRec⟩
      | match_ =>
          exact .inr ⟨_, StepM.matchScrut⟩
      | ctor =>
          exact .inr ⟨_, StepM.ctor⟩
      | var hlookup hLC hinstTo =>
          have hlen : E.length = Γ.length := envOK_length hE
          exact .inr ⟨_, StepM.var (by rw [hlen]; exact (List.getElem?_eq_some_iff.mp hlookup).1)⟩
  | ret v k =>
      unfold StateOK at h
      rcases h with ⟨σ, τ, hv, hinst, hk⟩
      cases k with
      | nil =>
          exact .inl ⟨v, rfl⟩
      | appArg E arg k' =>
          cases hv with
          | thunk =>
              exact .inr ⟨_, StepM.force⟩
          | recclo hj hE' hwf hmono hpoly hσ =>
              rw [← hwf.length] at hj
              exact .inr ⟨_, StepM.forceRecclo hj⟩
          | prim =>
              exact .inr ⟨_, StepM.appArgStep (by simp [IsVal])⟩
          | primOp =>
              exact .inr ⟨_, StepM.appArgStep (by simp [IsVal])⟩
          | primOpApp =>
              exact .inr ⟨_, StepM.appArgStep (by simp [IsVal])⟩
          | lam =>
              exact .inr ⟨_, StepM.appArgStep (by simp [IsVal])⟩
          | ctorV =>
              exact .inr ⟨_, StepM.appArgStep (by simp [IsVal])⟩
      | appFun fv k' =>
          cases hk with
          | appFun hfv hvlam hk_tl =>
              rcases hvlam with ⟨σf, hvfv, hinstf⟩
              cases hvfv with
              | prim =>
                  rename_i p
                  rcases hinstf with ⟨instArgs, hinstLC, hinstTo⟩
                  cases p <;>
                    (have hEq := InstantiatesBy.eq_of_closed ContainsBvarsUpTo.prim hinstTo
                     simp at hEq)
              | primOp hprim =>
                  cases hv with
                  | thunk =>
                      exact .inr ⟨_, StepM.force⟩
                  | recclo hj hE' hwf hmono hpoly hσ =>
                      rw [← hwf.length] at hj
                      exact .inr ⟨_, StepM.forceRecclo hj⟩
                  | prim =>
                      exact .inr ⟨_, StepM.primOpPart (by simp [IsVal])⟩
                  | primOp =>
                      exact .inr ⟨_, StepM.primOpPart (by simp [IsVal])⟩
                  | primOpApp =>
                      exact .inr ⟨_, StepM.primOpPart (by simp [IsVal])⟩
                  | lam =>
                      exact .inr ⟨_, StepM.primOpPart (by simp [IsVal])⟩
                  | ctorV =>
                      exact .inr ⟨_, StepM.primOpPart (by simp [IsVal])⟩
              | primOpApp hIsValA hvA hprim =>
                  rcases hinstf with ⟨instArgs, hinstLC, hinstTo⟩
                  have hEq := InstantiatesBy.eq_of_closed (arrow_lc_r (PrimBinOp.ty_lc hprim)) hinstTo
                  subst hEq
                  rcases primOp_ty_delta hprim with hEqop | hEqop
                  · rcases hEqop with hEqop | hEqop
                    · subst hEqop
                      rcases primOp_int_operands hprim (Or.inl rfl) with ⟨hτ₁, hA⟩
                      have hvA' := by simpa [hτ₁] using hvA
                      obtain ⟨n, rfl⟩ := valTyped_mono_canonical_int hIsValA hvA'
                      cases v with
                      | thunk =>
                          exact .inr ⟨_, StepM.force⟩
                      | recclo anns bindings E j =>
                          cases hv with
                          | recclo hj hE' hwf hmono hpoly hσ =>
                              rw [← hwf.length] at hj
                              exact .inr ⟨_, StepM.forceRecclo hj⟩
                      | prim =>
                          rcases valTyped_canonical_int (by simp [IsVal]) hv hinst hA with ⟨m, hEqv⟩
                          rw [hEqv]
                          exact .inr ⟨_, StepM.primOpDelta (op := .intAdd) (a := .int n) (b := .int m) (k := k') (by rfl)⟩
                      | primOp =>
                          exfalso
                          rcases valTyped_canonical_int (by simp [IsVal]) hv hinst hA with ⟨m, hEqv⟩
                          simp at hEqv
                      | primOpApp =>
                          exfalso
                          rcases valTyped_canonical_int (by simp [IsVal]) hv hinst hA with ⟨m, hEqv⟩
                          simp at hEqv
                      | lam =>
                          exfalso
                          rcases valTyped_canonical_int (by simp [IsVal]) hv hinst hA with ⟨m, hEqv⟩
                          simp at hEqv
                      | ctorV =>
                          exfalso
                          rcases valTyped_canonical_int (by simp [IsVal]) hv hinst hA with ⟨m, hEqv⟩
                          simp at hEqv
                    · subst hEqop
                      rcases primOp_int_operands hprim (Or.inr rfl) with ⟨hτ₁, hA⟩
                      have hvA' := by simpa [hτ₁] using hvA
                      obtain ⟨n, rfl⟩ := valTyped_mono_canonical_int hIsValA hvA'
                      cases v with
                      | thunk =>
                          exact .inr ⟨_, StepM.force⟩
                      | recclo anns bindings E j =>
                          cases hv with
                          | recclo hj hE' hwf hmono hpoly hσ =>
                              rw [← hwf.length] at hj
                              exact .inr ⟨_, StepM.forceRecclo hj⟩
                      | prim =>
                          rcases valTyped_canonical_int (by simp [IsVal]) hv hinst hA with ⟨m, hEqv⟩
                          rw [hEqv]
                          exact .inr ⟨_, StepM.primOpDelta (op := .intSub) (a := .int n) (b := .int m) (k := k') (by rfl)⟩
                      | primOp =>
                          exfalso
                          rcases valTyped_canonical_int (by simp [IsVal]) hv hinst hA with ⟨m, hEqv⟩
                          simp at hEqv
                      | primOpApp =>
                          exfalso
                          rcases valTyped_canonical_int (by simp [IsVal]) hv hinst hA with ⟨m, hEqv⟩
                          simp at hEqv
                      | lam =>
                          exfalso
                          rcases valTyped_canonical_int (by simp [IsVal]) hv hinst hA with ⟨m, hEqv⟩
                          simp at hEqv
                      | ctorV =>
                          exfalso
                          rcases valTyped_canonical_int (by simp [IsVal]) hv hinst hA with ⟨m, hEqv⟩
                          simp at hEqv
                  · rcases hEqop with hEqop | hEqop
                    · subst hEqop
                      rcases primOp_intLt_operands hprim with ⟨hτ₁, hA⟩
                      have hvA' := by simpa [hτ₁] using hvA
                      obtain ⟨n, rfl⟩ := valTyped_mono_canonical_int hIsValA hvA'
                      cases v with
                      | thunk =>
                          exact .inr ⟨_, StepM.force⟩
                      | recclo anns bindings E j =>
                          cases hv with
                          | recclo hj hE' hwf hmono hpoly hσ =>
                              rw [← hwf.length] at hj
                              exact .inr ⟨_, StepM.forceRecclo hj⟩
                      | prim =>
                          rcases valTyped_canonical_int (by simp [IsVal]) hv hinst hA with ⟨m, hEqv⟩
                          rw [hEqv]
                          exact .inr ⟨_, StepM.primOpDelta (op := .intLt) (a := .int n) (b := .int m) (k := k') (by rfl)⟩
                      | primOp =>
                          exfalso
                          rcases valTyped_canonical_int (by simp [IsVal]) hv hinst hA with ⟨m, hEqv⟩
                          simp at hEqv
                      | primOpApp =>
                          exfalso
                          rcases valTyped_canonical_int (by simp [IsVal]) hv hinst hA with ⟨m, hEqv⟩
                          simp at hEqv
                      | lam =>
                          exfalso
                          rcases valTyped_canonical_int (by simp [IsVal]) hv hinst hA with ⟨m, hEqv⟩
                          simp at hEqv
                      | ctorV =>
                          exfalso
                          rcases valTyped_canonical_int (by simp [IsVal]) hv hinst hA with ⟨m, hEqv⟩
                          simp at hEqv
                    · subst hEqop
                      rcases primOp_charLt_operands hprim with ⟨hτ₁, hA⟩
                      have hvA' := by simpa [hτ₁] using hvA
                      obtain ⟨n, rfl⟩ := valTyped_mono_canonical_char hIsValA hvA'
                      cases v with
                      | thunk =>
                          exact .inr ⟨_, StepM.force⟩
                      | recclo anns bindings E j =>
                          cases hv with
                          | recclo hj hE' hwf hmono hpoly hσ =>
                              rw [← hwf.length] at hj
                              exact .inr ⟨_, StepM.forceRecclo hj⟩
                      | prim =>
                          rcases valTyped_canonical_char (by simp [IsVal]) hv hinst hA with ⟨m, hEqv⟩
                          rw [hEqv]
                          exact .inr ⟨_, StepM.primOpDelta (op := .charLt) (a := .char n) (b := .char m) (k := k') (by rfl)⟩
                      | primOp =>
                          exfalso
                          rcases valTyped_canonical_char (by simp [IsVal]) hv hinst hA with ⟨m, hEqv⟩
                          simp at hEqv
                      | primOpApp =>
                          exfalso
                          rcases valTyped_canonical_char (by simp [IsVal]) hv hinst hA with ⟨m, hEqv⟩
                          simp at hEqv
                      | lam =>
                          exfalso
                          rcases valTyped_canonical_char (by simp [IsVal]) hv hinst hA with ⟨m, hEqv⟩
                          simp at hEqv
                      | ctorV =>
                          exfalso
                          rcases valTyped_canonical_char (by simp [IsVal]) hv hinst hA with ⟨m, hEqv⟩
                          simp at hEqv
              | lam =>
                  cases hv with
                  | thunk =>
                      exact .inr ⟨_, StepM.force⟩
                  | recclo hj hE' hwf hmono hpoly hσ =>
                      rw [← hwf.length] at hj
                      exact .inr ⟨_, StepM.forceRecclo hj⟩
                  | prim =>
                      exact .inr ⟨_, StepM.beta (by simp [IsVal])⟩
                  | primOp =>
                      exact .inr ⟨_, StepM.beta (by simp [IsVal])⟩
                  | primOpApp =>
                      exact .inr ⟨_, StepM.beta (by simp [IsVal])⟩
                  | lam =>
                      exact .inr ⟨_, StepM.beta (by simp [IsVal])⟩
                  | ctorV =>
                      exact .inr ⟨_, StepM.beta (by simp [IsVal])⟩
              | thunk =>
                  simp [IsVal] at hfv
              | recclo =>
                  simp [IsVal] at hfv
              | ctorV =>
                  cases hv with
                  | thunk =>
                      exact .inr ⟨_, StepM.force⟩
                  | recclo hj hE' hwf hmono hpoly hσ =>
                      rw [← hwf.length] at hj
                      exact .inr ⟨_, StepM.forceRecclo hj⟩
                  | prim =>
                      exact .inr ⟨_, StepM.ctorApp (by simp [IsVal])⟩
                  | primOp =>
                      exact .inr ⟨_, StepM.ctorApp (by simp [IsVal])⟩
                  | primOpApp =>
                      exact .inr ⟨_, StepM.ctorApp (by simp [IsVal])⟩
                  | lam =>
                      exact .inr ⟨_, StepM.ctorApp (by simp [IsVal])⟩
                  | ctorV =>
                      exact .inr ⟨_, StepM.ctorApp (by simp [IsVal])⟩
      | matchSel E branches k' =>
          cases hk with
          | matchSel hE hbranches hne hk_tl =>
              simp only [ExhaustiveState, ExhaustiveKont] at hexh
              rcases hexh with ⟨_hvalExh, _hE_exh, _hbranchExh, hcover, _hk_exh⟩
              obtain ⟨⟨pat0, body0⟩, rest0, hbeq⟩ := List.exists_cons_of_ne_nil hne
              have hb0 : (pat0, body0) ∈ branches := by
                rw [hbeq]
                exact List.mem_cons_self
              cases hv with
              | thunk =>
                  exact .inr ⟨_, StepM.force⟩
              | recclo hj hE' hwf hmono hpoly hσ =>
                  rw [← hwf.length] at hj
                  exact .inr ⟨_, StepM.forceRecclo hj⟩
              | prim =>
                  rename_i p
                  have hwild : pat0 = .wildcard := by
                    cases pat0 with
                    | wildcard => rfl
                    | named c0 n0 =>
                        exfalso
                        cases hbranches (.named c0 n0, body0) hb0 with
                        | mk bspec _hbctx _hbodies =>
                            rcases bspec with ⟨hlookS, hscrutEq, _arity, _bindcount, _fields⟩
                            rcases hinst with ⟨_instArgs, _hinstLC, hinstTo⟩
                            cases p <;>
                              (have hEq := InstantiatesBy.eq_of_closed ContainsBvarsUpTo.prim hinstTo
                               have hpc := hEq.symm.trans hscrutEq
                               simp at hpc)
                  subst hwild
                  rw [hbeq]
                  exact .inr ⟨_, StepM.matchWild (branches := rest0) (body := body0) (k := k') (by simp [IsNonCtorVal])⟩
              | primOp hprim =>
                  have hwild : pat0 = .wildcard := by
                    cases pat0 with
                    | wildcard => rfl
                    | named c0 n0 =>
                        exfalso
                        cases hbranches (.named c0 n0, body0) hb0 with
                        | mk bspec _hbctx _hbodies =>
                            rcases bspec with ⟨hlookS, hscrutEq, _arity, _bindcount, _fields⟩
                            rcases hinst with ⟨_instArgs, _hinstLC, hinstTo⟩
                            have hEq := InstantiatesBy.eq_of_closed (PrimBinOp.ty_lc hprim) hinstTo
                            have hpc := hEq.symm.trans hscrutEq
                            exact primOp_ty_not_customTy hprim hpc
                  subst hwild
                  rw [hbeq]
                  exact .inr ⟨_, StepM.matchWild (branches := rest0) (body := body0) (k := k') (by simp [IsNonCtorVal])⟩
              | primOpApp hIsValV hvV hprim =>
                  have hwild : pat0 = .wildcard := by
                    cases pat0 with
                    | wildcard => rfl
                    | named c0 n0 =>
                        exfalso
                        cases hbranches (.named c0 n0, body0) hb0 with
                        | mk bspec _hbctx _hbodies =>
                            rcases bspec with ⟨hlookS, hscrutEq, _arity, _bindcount, _fields⟩
                            rcases hinst with ⟨_instArgs, _hinstLC, hinstTo⟩
                            have hEq := InstantiatesBy.eq_of_closed (arrow_lc_r (PrimBinOp.ty_lc hprim)) hinstTo
                            have hτ₂c := hEq.symm.trans hscrutEq
                            exact primOp_ty_arrow_not_customTy (by simpa [hτ₂c] using hprim)
                  subst hwild
                  rw [hbeq]
                  exact .inr ⟨_, StepM.matchWild (branches := rest0) (body := body0) (k := k') (by simp [IsNonCtorVal])⟩
              | lam hτ₁ hτ₂ hE' hbody =>
                  have hwild : pat0 = .wildcard := by
                    cases pat0 with
                    | wildcard => rfl
                    | named c0 n0 =>
                        exfalso
                        cases hbranches (.named c0 n0, body0) hb0 with
                        | mk bspec _hbctx _hbodies =>
                            rcases bspec with ⟨hlookS, hscrutEq, _arity, _bindcount, _fields⟩
                            rcases hinst with ⟨_instArgs, _hinstLC, hinstTo⟩
                            have hEq := InstantiatesBy.eq_of_closed (ContainsBvarsUpTo.arrow hτ₁ hτ₂) hinstTo
                            have hAc := hEq.symm.trans hscrutEq
                            simp at hAc
                  subst hwild
                  rw [hbeq]
                  exact .inr ⟨_, StepM.matchWild (branches := rest0) (body := body0) (k := k') (by simp [IsNonCtorVal])⟩
              | ctorV hlook htyArgs hargs hfields =>
                  rcases matchSel_ctorV_first hlook hargs hfields hinst hbranches hne hcover
                    with ⟨pat', body', hfirst⟩
                  exact .inr ⟨_, StepM.matchCtor (pat := pat') (body := body') hfirst⟩

/-! ## Preservation helpers

Small lemmas supporting the `preservation` proof below: the trivial
self-instantiation of a monotype, the pointwise `EnvOK` accessor, the
`bvarRange` instantiation round-trips needed by the `ctor`/`matchCtor` cases,
and the nullary-`Bool`-constructor facts needed by the primop cases. -/

/-- A locally-closed monotype instantiates to itself (trivially). -/
private theorem instantiates_trivial {τ : Ty} (h : τ.IsLC) :
    Instantiates (PolyTy.mkTrivial τ) τ := by
  exact ⟨[], by intro a ha; simp at ha,
    by simpa [PolyTy.InstantiatesTo] using (InstantiatesBy.refl_of_closed h)⟩

/-- A well-typed value environment is pointwise well-typed. -/
private def envOK_get {ctors : CtorEnv} {E : VEnv} {Γ : Env}
    (hE : EnvOK ctors E Γ) :
    ∀ i (hE' : i < E.length) (hΓ : i < Γ.length),
      ValTyped ctors (E.get ⟨i, hE'⟩) (Γ.get ⟨i, hΓ⟩) := by
  cases hE with
  | nil =>
      intro i hE' hΓ
      simp at hΓ
  | cons hv htl =>
      intro i hE' hΓ
      cases i with
      | zero => simpa using hv
      | succ i =>
          exact envOK_get htl i (Nat.lt_of_succ_lt_succ hE') (Nat.lt_of_succ_lt_succ hΓ)

/-- `bvarRangeFrom` reads back its definition pointwise: the `k`-th entry of a
    `bvarRangeFrom start n` list is `.bvar (start + k)`. -/
private theorem bvarRangeFrom_getElem? {n s k : Nat} (hk : k < n) :
    (Ty.bvarRangeFrom s n)[k]? = some (Ty.bvar (s + k)) := by
  induction n generalizing s k with
  | zero => omega
  | succ m ih =>
      cases k with
      | zero => simp [Ty.bvarRangeFrom]
      | succ j =>
          simp only [Ty.bvarRangeFrom, List.getElem?_cons_succ]
          have hshift : s + 1 + j = s + (j + 1) := by omega
          rw [ih (by omega), hshift]

/-- From `Forall₂ (InstantiatesBy tyArgs') (bvarRangeFrom start n) tyArgs`: the
    `k`-th entry (k < n) forces `tyArgs[k]? = tyArgs'[start + k]?`. -/
private theorem bvarRangeFrom_forall₂_agreement {tyArgs tyArgs' : List Ty} :
    ∀ {start n : Nat},
      List.Forall₂ (InstantiatesBy tyArgs') (Ty.bvarRangeFrom start n) tyArgs →
      ∀ k, k < n → tyArgs[k]? = tyArgs'[start + k]? := by
  intro start n
  induction n generalizing start tyArgs with
  | zero =>
      intro h k hk
      simp [Ty.bvarRangeFrom] at h
      cases h
      omega
  | succ m ih =>
      intro h k hk
      simp only [Ty.bvarRangeFrom] at h
      cases h with
      | cons hhd htl =>
          rename_i hd tl
          cases hhd with
          | bvar hidx =>
              cases k with
              | zero =>
                  rw [show start + 0 = start from by omega, hidx]
                  rfl
              | succ k =>
                  have hrec : tl[k]? = tyArgs'[(start + 1) + k]? :=
                    ih (tyArgs := tl) htl k (by omega)
                  rw [show start + (k + 1) = (start + 1) + k from by omega]
                  simpa using hrec

private theorem bvarRange_forall₂_agreement {tyArgs tyArgs' : List Ty} {n : Nat}
    (h : List.Forall₂ (InstantiatesBy tyArgs') (Ty.bvarRange n) tyArgs) (k : Nat) (hk : k < n) :
    tyArgs[k]? = tyArgs'[k]? := by
  have := bvarRangeFrom_forall₂_agreement (start := 0) h k hk
  rwa [Nat.zero_add] at this

private def bvarRangeFrom_length : ∀ (start n : Nat), (Ty.bvarRangeFrom start n).length = n
  | _, 0 => rfl
  | start, m + 1 => by
      simp [Ty.bvarRangeFrom, bvarRangeFrom_length (start + 1) m]

/-- Instantiating `bvarRange n` pointwise reads back `tyArgs.take n`. -/
private theorem bvarRange_instantiates_take {tyArgs instTys : List Ty} {n : Nat}
    (h : List.Forall₂ (InstantiatesBy tyArgs) (Ty.bvarRange n) instTys) :
    instTys = tyArgs.take n := by
  apply List.ext_getElem?
  intro i
  by_cases hi : i < n
  · rw [List.getElem?_take_of_lt hi]
    exact bvarRange_forall₂_agreement h i hi
  · have hlen : instTys.length = n := by
      simpa [Ty.bvarRange, bvarRangeFrom_length] using (List.Forall₂.length_eq h).symm
    rw [List.getElem?_eq_none (by omega), List.getElem?_eq_none (by simp [List.length_take]; omega)]

/-- A `wrapArrows` instantiation decomposes pointwise: the instantiated type is
    the wrapped result at the instantiated contents, with each content
    instantiated separately. -/
private theorem instantiatesBy_wrapArrows {tyArgs : List Ty} {result : Ty} :
    ∀ (contents : List Ty) (τ : Ty),
      InstantiatesBy tyArgs (Ty.wrapArrows result contents) τ →
      ∃ resultI contentsI, τ = Ty.wrapArrows resultI contentsI ∧
        InstantiatesBy tyArgs result resultI ∧
        List.Forall₂ (InstantiatesBy tyArgs) contents contentsI := by
  intro contents
  induction contents with
  | nil =>
      intro τ h
      exact ⟨τ, [], rfl, h, .nil⟩
  | cons c cs ih =>
      intro τ h
      change InstantiatesBy tyArgs (Ty.arrow c (Ty.wrapArrows result cs)) τ at h
      cases h with
      | arrow hc hrest =>
          rename_i instFst instSnd
          rcases ih instSnd hrest with ⟨resultI, csI, hEq, hres, hcs⟩
          refine ⟨resultI, instFst :: csI, ?_, hres, .cons hc hcs⟩
          rw [hEq]
          simp [Ty.wrapArrows]

/-- Instantiating by `tyArgs` or by its `n`-prefix agrees on types all of whose
    bvars are below `n`. -/
private theorem instantiatesBy_take_of_agree {n : Nat} {tyArgs : List Ty} {t ti : Ty}
    (hbound : ContainsBvarsUpTo n t) (hinst : InstantiatesBy tyArgs t ti) :
    InstantiatesBy (tyArgs.take n) t ti := by
  induction hbound generalizing ti with
  | prim =>
      cases hinst
      exact .prim
  | arrow hba hbb iha ihb =>
      cases hinst with
      | arrow hfa hfb =>
          exact .arrow (iha hfa) (ihb hfb)
  | fvar =>
      cases hinst
      exact .fvar
  | customTy hball ih =>
      cases hinst with
      | customTy hforall =>
          apply InstantiatesBy.customTy
          induction hforall with
          | nil => exact .nil
          | cons hhd htl ihtl =>
              rename_i a b l1 l2
              refine .cons (ih a List.mem_cons_self hhd) (ihtl ?_ ?_)
              · intro ty hty
                exact hball ty (List.mem_cons_of_mem a hty)
              · intro ty hty _ hinst'
                exact ih ty (List.mem_cons_of_mem a hty) hinst'
  | bvar hi =>
      cases hinst with
      | bvar hget =>
          exact .bvar (by
            rw [List.getElem?_take_of_lt hi]
            exact hget)
  | bl hbe ih =>
      cases hinst with
      | bl hie =>
          exact .bl (ih hie)

/-- Pointwise: `instantiatesBy_take_of_agree` through a `Forall₂`. -/
private theorem forall2_instantiatesBy_take_of_agree {n : Nat} {tyArgs : List Ty}
    {tys its : List Ty} (hbound : ∀ t ∈ tys, ContainsBvarsUpTo n t)
    (hinst : ∀ t ∈ tys, ∀ {ti : Ty}, InstantiatesBy tyArgs t ti → InstantiatesBy (tyArgs.take n) t ti)
    (h : List.Forall₂ (InstantiatesBy tyArgs) tys its) :
    List.Forall₂ (InstantiatesBy (tyArgs.take n)) tys its := by
  induction h with
  | nil => exact .nil
  | cons hhd htl ih =>
      refine .cons (hinst _ List.mem_cons_self hhd) (ih ?_ ?_)
      · intro t ht
        exact hbound t (List.mem_cons_of_mem _ ht)
      · intro t ht _ hinst'
        exact hinst t (List.mem_cons_of_mem _ ht) hinst'

/-- Append one pair to a `Forall₂`. -/
private theorem forall2_snoc {α β : Type _} {R : α → β → Prop} {l1 : List α} {l2 : List β}
    {a : α} {b : β} (h : List.Forall₂ R l1 l2) (hab : R a b) :
    List.Forall₂ R (l1 ++ [a]) (l2 ++ [b]) := by
  induction h with
  | nil => exact .cons hab .nil
  | cons hhd htl ih => exact .cons hhd ih

/-- Element-wise determinism for two `Forall₂ (InstantiatesBy …)` over a common
    source list, given a per-element determinism hypothesis. -/
private theorem forall2_det_instantiates {tyArgs1 tyArgs2 : List Ty} :
    ∀ {tys its1 its2 : List Ty},
      (∀ t ∈ tys, ∀ {a b : Ty},
        InstantiatesBy tyArgs1 t a → InstantiatesBy tyArgs2 t b → a = b) →
      List.Forall₂ (InstantiatesBy tyArgs1) tys its1 →
      List.Forall₂ (InstantiatesBy tyArgs2) tys its2 →
      its1 = its2 := by
  intro tys
  induction tys with
  | nil =>
      intro its1 its2 hdet hf1 hf2
      cases hf1
      cases hf2
      rfl
  | cons hd tl ihtl =>
      intro its1 its2 hdet hf1 hf2
      cases hf1 with
      | cons h1 h1t =>
          cases hf2 with
          | cons h2 h2t =>
              have hhd : _ = _ := hdet hd List.mem_cons_self h1 h2
              have htl' := ihtl (fun t ht => hdet t (List.mem_cons_of_mem _ ht)) h1t h2t
              rw [hhd, htl']

/-- Pointwise: `ValTyped` on `mkTrivial` entries is a pointwise `ValTyped`. -/
private theorem forall2_valTyped_mkTrivial {ctors : CtorEnv} {args : List Val} {its : List Ty}
    (h : List.Forall₂ (fun a t => ValTyped ctors a (PolyTy.mkTrivial t)) args its) :
    List.Forall₂ (fun v σ => ValTyped ctors v σ) args (its.map PolyTy.mkTrivial) := by
  induction h with
  | nil => exact .nil
  | cons hv' htl ih => exact .cons hv' ih

/-- A `Forall₂ (InstantiatesBy …)` over two lists of locally-closed types is an
    identity (instantiation is deterministic on locally-closed types). -/
private theorem forall2_instantiatesBy_eq_of_lc {tyArgs1 tyArgs2 instArgs : List Ty}
    (hLC : ∀ a ∈ tyArgs1, a.IsLC)
    (h : List.Forall₂ (InstantiatesBy instArgs) tyArgs1 tyArgs2) :
    tyArgs1 = tyArgs2 := by
  induction h with
  | nil => rfl
  | cons hhd htl ih =>
      have hEq : _ = _ := InstantiatesBy.eq_of_closed (hLC _ List.mem_cons_self) hhd
      rw [hEq]
      congr 1
      exact ih (fun a ha => hLC a (List.mem_cons_of_mem _ ha))

/-- `bvarRange n` is nonempty unless `n = 0`. -/
private theorem bvarRange_ne_nil {n : Nat} (h : Ty.bvarRange n = []) : n = 0 := by
  cases n with
  | zero => rfl
  | succ n' => simp [Ty.bvarRange, Ty.bvarRangeFrom] at h

/-- A `customTy` instantiation of a `bvarRange` list reads back the type name
    and the instantiated argument list. -/
private theorem instantiatesBy_customTy_bvarRange {tyArgs : List Ty} {n : Nat}
    {tyName : TyName} {τ : Ty}
    (h : InstantiatesBy tyArgs (Ty.customTy tyName (Ty.bvarRange n)) τ) :
    ∃ tyArgs', τ = Ty.customTy tyName tyArgs' ∧
      List.Forall₂ (InstantiatesBy tyArgs) (Ty.bvarRange n) tyArgs' := by
  cases h with
  | customTy hforall =>
      rename_i instTys
      exact ⟨instTys, rfl, hforall⟩

/-- A nullary-`Bool` constructor is `Bool`, nullary, and has no fields. -/
private theorem isNullaryBool_decomp {c : Ctor} (h : c.isNullaryBool = true) :
    c.tyName = ⟨"Bool"⟩ ∧ c.paramCount = 0 ∧ c.contents = [] := by
  unfold Ctor.isNullaryBool at h
  have hsplit : ((c.tyName == TyName.mk "Bool" && c.paramCount == 0) = true ∧
      c.contents.isEmpty = true) := (Bool.and_eq_true_eq_eq_true_and_eq_true _ _).mp h
  have h1 : (c.tyName == TyName.mk "Bool" && c.paramCount == 0) = true := hsplit.1
  have h2 : c.contents.isEmpty = true := hsplit.2
  have h3 : (c.tyName == TyName.mk "Bool") = true :=
    ((Bool.and_eq_true_eq_eq_true_and_eq_true _ _).mp h1).1
  have h4 : (c.paramCount == 0) = true :=
    ((Bool.and_eq_true_eq_eq_true_and_eq_true _ _).mp h1).2
  constructor
  · change decide (c.tyName = TyName.mk "Bool") = true at h3
    exact of_decide_eq_true h3
  constructor
  · change decide (c.paramCount = 0) = true at h4
    exact of_decide_eq_true h4
  · by_contra hc
    rcases List.exists_cons_of_ne_nil hc with ⟨hd, tl, hceq⟩
    rw [hceq] at h2
    exact Bool.noConfusion h2

/-- The `⟨"True"⟩`/`⟨"False"⟩` constructors of a typed nullary `Bool` are nullary
    `Bool` constructors in the environment. -/
private theorem bool_ctor_nullary_of_typed {ctors : CtorEnv} {Γ : Env} {bname : CtorName}
    (h : TypeOfHM ⟨Γ, ctors⟩ (.ctor bname) (.customTy ⟨"Bool"⟩ [])) :
    ∃ c, LookupList.get? ctors bname = some c ∧ c.isNullaryBool = true := by
  cases h with
  | ctor hlook htyArgs hinst =>
      rename_i c tyArgs
      have hinst' : InstantiatesBy tyArgs
          (Ty.wrapArrows (Ty.customTy c.tyName (Ty.bvarRange c.paramCount)) c.contents)
          (.customTy ⟨"Bool"⟩ []) := by
        simpa [Ctor.toTy, PolyTy.InstantiatesTo] using hinst
      rcases instantiatesBy_wrapArrows (contents := c.contents) (τ := .customTy ⟨"Bool"⟩ []) hinst'
        with ⟨resultI, contentsI, hEq, hresI, hcontI⟩
      have hcontentsI_nil : contentsI = [] := by
        cases contentsI with
        | nil => rfl
        | cons c' cs' =>
            simp [Ty.wrapArrows] at hEq
      have hresultI : resultI = Ty.customTy ⟨"Bool"⟩ [] := by
        rw [hcontentsI_nil] at hEq
        simpa [Ty.wrapArrows] using hEq.symm
      have hcontents : c.contents = [] := by
        by_contra hc
        rcases List.exists_cons_of_ne_nil hc with ⟨hd, tl, hceq⟩
        rw [hcontentsI_nil] at hcontI
        rw [hceq] at hcontI
        cases hcontI
      have hresI' : InstantiatesBy tyArgs (Ty.customTy c.tyName (Ty.bvarRange c.paramCount))
          (Ty.customTy ⟨"Bool"⟩ []) := by
        simpa [hresultI] using hresI
      rcases instantiatesBy_customTy_bvarRange hresI' with ⟨tyArgs', hResEq, hf⟩
      have htyName : c.tyName = ⟨"Bool"⟩ := by
        injection hResEq.symm
      have hparamCount : c.paramCount = 0 := by
        have hts' : tyArgs' = [] := by
          injection hResEq.symm
        rw [hts'] at hf
        have hrange : Ty.bvarRange c.paramCount = [] := by
          by_contra hc
          rcases List.exists_cons_of_ne_nil hc with ⟨hd, tl, hceq⟩
          rw [hceq] at hf
          cases hf
        exact bvarRange_ne_nil hrange
      have hnull : c.isNullaryBool = true := by
        unfold Ctor.isNullaryBool
        rw [htyName, hparamCount, hcontents]
        simp
      exact ⟨c, hlook, hnull⟩

/-- A nullary-`Bool` constructor value types at the nullary `Bool` type. -/
private theorem valTyped_bool_ctor {ctors : CtorEnv} {bname : CtorName}
    (h : ∃ c, LookupList.get? ctors bname = some c ∧ c.isNullaryBool = true) :
    ValTyped ctors (.ctorV bname []) (PolyTy.mkTrivial (.customTy ⟨"Bool"⟩ [])) := by
  rcases h with ⟨c, hlook, hnull⟩
  rcases isNullaryBool_decomp hnull with ⟨htyName, hparamCount, hcontents⟩
  rw [← htyName]
  refine ValTyped.ctorV (tyArgs := []) (instContents := []) (remContents := []) hlook ?_ .nil ?_
  · intro a ha
    simp at ha
  · rw [hcontents]
    exact .nil

/-- The comparison primops are the only primops whose arrow type ends in the
    nullary `Bool` type; their return type is `Bool` and both `Bool` ctors exist. -/
private theorem primOp_bool_ret {ctors : CtorEnv} {op : PrimBinOp} {τ₁ A B : Ty}
    (h : PrimBinOp.ty ctors op = some (.arrow τ₁ (.arrow A B)))
    (hop : op = .intLt ∨ op = .charLt) :
    B = .customTy ⟨"Bool"⟩ [] ∧
    (∃ c, LookupList.get? ctors ⟨"True"⟩ = some c ∧ c.isNullaryBool = true) ∧
    (∃ c, LookupList.get? ctors ⟨"False"⟩ = some c ∧ c.isNullaryBool = true) := by
  rcases hop with ⟨opEq⟩ | ⟨opEq⟩
  · subst op
    cases h1 : LookupList.get? ctors ⟨"True"⟩ with
    | none => simp [PrimBinOp.ty, h1] at h
    | some tc =>
        cases h2 : LookupList.get? ctors ⟨"False"⟩ with
        | none => simp [PrimBinOp.ty, h1, h2] at h
        | some fc =>
            simp [PrimBinOp.ty, h1, h2] at h
            rcases h with ⟨htc, hx⟩
            constructor
            · exact hx.2.2.symm
            constructor
            · exact ⟨tc, rfl, htc.1⟩
            · exact ⟨fc, rfl, htc.2⟩
  · subst op
    cases h1 : LookupList.get? ctors ⟨"True"⟩ with
    | none => simp [PrimBinOp.ty, h1] at h
    | some tc =>
        cases h2 : LookupList.get? ctors ⟨"False"⟩ with
        | none => simp [PrimBinOp.ty, h1, h2] at h
        | some fc =>
            simp [PrimBinOp.ty, h1, h2] at h
            rcases h with ⟨htc, hx⟩
            constructor
            · exact hx.2.2.symm
            constructor
            · exact ⟨tc, rfl, htc.1⟩
            · exact ⟨fc, rfl, htc.2⟩

/-- The arithmetic primops return `int`. -/
private theorem primOp_int_ret {ctors : CtorEnv} {op : PrimBinOp} {τ₁ A B : Ty}
    (h : PrimBinOp.ty ctors op = some (.arrow τ₁ (.arrow A B)))
    (hop : op = .intAdd ∨ op = .intSub) :
    B = .prim .int := by
  rcases hop with ⟨hopEq⟩ | ⟨hopEq⟩
  · subst op
    simp [PrimBinOp.ty] at h
    exact h.2.2.symm
  · subst op
    simp [PrimBinOp.ty] at h
    exact h.2.2.symm

/-- The `j`-th entries of two same-length lists sit in their zip. -/
private def mem_zip_get {α β : Type _} (l1 : List α) (l2 : List β) (j : Nat)
    (h1 : j < l1.length) (h2 : j < l2.length) :
    (l1.get ⟨j, h1⟩, l2.get ⟨j, h2⟩) ∈ l1.zip l2 := by
  revert l2 j h1 h2
  induction l1 with
  | nil =>
      intro l2 j h1 h2
      simp at h1
  | cons a as ihas =>
      intro l2 j h1 h2
      cases l2 with
      | nil => simp at h2
      | cons b bs =>
          cases j with
          | zero => simp
          | succ j' =>
              simp
              exact Or.inr (ihas bs j' (Nat.lt_of_succ_lt_succ h1) (Nat.lt_of_succ_lt_succ h2))

/-- A constructor chain value's fully-applied arguments: `args.take n = args`
    when the pattern binds all `args`. -/
private theorem take_all_of_eq_length {α : Type _} {l : List α} {n : Nat}
    (h : n = l.length) : l.take n = l := by
  rw [h]
  induction l with
  | nil => rfl
  | cons a as ih => simp

/-- Preservation: stepping preserves well-typedness. -/
theorem preservation {ctors : CtorEnv} {s s' : State} {ρ : Ty}
    (h : StateOK ctors s ρ) (herased : ErasedState s) (hstep : StepM s s') :
    StateOK ctors s' ρ := by
  cases hstep
  case primLit =>
      rename_i E p k
      unfold StateOK at h
      rcases h with ⟨Γ, τ, hE, he, hk⟩
      cases he with
      | primLitUnit =>
          unfold StateOK
          exact ⟨PolyTy.mkTrivial (.prim .unit), .prim .unit, ValTyped.prim,
            instantiates_trivial (ContainsBvarsUpTo.prim), hk⟩
      | primLitInt =>
          unfold StateOK
          exact ⟨PolyTy.mkTrivial (.prim .int), .prim .int, ValTyped.prim,
            instantiates_trivial (ContainsBvarsUpTo.prim), hk⟩
      | primLitNat =>
          unfold StateOK
          exact ⟨PolyTy.mkTrivial (.prim .nat), .prim .nat, ValTyped.prim,
            instantiates_trivial (ContainsBvarsUpTo.prim), hk⟩
      | primLitChar =>
          unfold StateOK
          exact ⟨PolyTy.mkTrivial (.prim .char), .prim .char, ValTyped.prim,
            instantiates_trivial (ContainsBvarsUpTo.prim), hk⟩
  case primBinOp =>
      rename_i E op k
      unfold StateOK at h
      rcases h with ⟨Γ, τ, hE, he, hk⟩
      cases he with
      | primBinOpIntAdd =>
          unfold StateOK
          exact ⟨PolyTy.mkTrivial (.arrow (.prim .int) (.arrow (.prim .int) (.prim .int))),
            .arrow (.prim .int) (.arrow (.prim .int) (.prim .int)),
            ValTyped.primOp (h := rfl),
            instantiates_trivial (ContainsBvarsUpTo.arrow ContainsBvarsUpTo.prim
              (ContainsBvarsUpTo.arrow ContainsBvarsUpTo.prim ContainsBvarsUpTo.prim)), hk⟩
      | primBinOpIntSub =>
          unfold StateOK
          exact ⟨PolyTy.mkTrivial (.arrow (.prim .int) (.arrow (.prim .int) (.prim .int))),
            .arrow (.prim .int) (.arrow (.prim .int) (.prim .int)),
            ValTyped.primOp (h := rfl),
            instantiates_trivial (ContainsBvarsUpTo.arrow ContainsBvarsUpTo.prim
              (ContainsBvarsUpTo.arrow ContainsBvarsUpTo.prim ContainsBvarsUpTo.prim)), hk⟩
      | primBinOpIntLt hTrue hFalse =>
          have hT : ∃ c, LookupList.get? ctors ⟨"True"⟩ = some c ∧ c.isNullaryBool = true :=
            bool_ctor_nullary_of_typed hTrue
          have hF : ∃ c, LookupList.get? ctors ⟨"False"⟩ = some c ∧ c.isNullaryBool = true :=
            bool_ctor_nullary_of_typed hFalse
          rcases hT with ⟨cT, h1, htc⟩
          rcases hF with ⟨cF, h2, hfc⟩
          unfold StateOK
          refine ⟨PolyTy.mkTrivial (.arrow (.prim .int) (.arrow (.prim .int) (.customTy ⟨"Bool"⟩ []))),
            .arrow (.prim .int) (.arrow (.prim .int) (.customTy ⟨"Bool"⟩ [])), ?_,
            instantiates_trivial (ContainsBvarsUpTo.arrow ContainsBvarsUpTo.prim
              (ContainsBvarsUpTo.arrow ContainsBvarsUpTo.prim
                (ContainsBvarsUpTo.customTy (by intro t ht; simp at ht)))), hk⟩
          exact ValTyped.primOp (h := by simp [PrimBinOp.ty, h1, h2, htc, hfc])
      | primBinOpCharLt hTrue hFalse =>
          have hT : ∃ c, LookupList.get? ctors ⟨"True"⟩ = some c ∧ c.isNullaryBool = true :=
            bool_ctor_nullary_of_typed hTrue
          have hF : ∃ c, LookupList.get? ctors ⟨"False"⟩ = some c ∧ c.isNullaryBool = true :=
            bool_ctor_nullary_of_typed hFalse
          rcases hT with ⟨cT, h1, htc⟩
          rcases hF with ⟨cF, h2, hfc⟩
          unfold StateOK
          refine ⟨PolyTy.mkTrivial (.arrow (.prim .char) (.arrow (.prim .char) (.customTy ⟨"Bool"⟩ []))),
            .arrow (.prim .char) (.arrow (.prim .char) (.customTy ⟨"Bool"⟩ [])), ?_,
            instantiates_trivial (ContainsBvarsUpTo.arrow ContainsBvarsUpTo.prim
              (ContainsBvarsUpTo.arrow ContainsBvarsUpTo.prim
                (ContainsBvarsUpTo.customTy (by intro t ht; simp at ht)))), hk⟩
          exact ValTyped.primOp (h := by simp [PrimBinOp.ty, h1, h2, htc, hfc])
  case ctor =>
      rename_i E name k
      unfold StateOK at h
      rcases h with ⟨Γ, τ, hE, he, hk⟩
      have hτLC : τ.IsLC := TypeOfHM.regular he
      cases he with
      | ctor hlook hLC hinstTo =>
          rename_i ctor tyArgs
          have hinstTo' : InstantiatesBy tyArgs
              (Ty.wrapArrows (Ty.customTy ctor.tyName (Ty.bvarRange ctor.paramCount)) ctor.contents) τ := by
            simpa [Ctor.toTy, PolyTy.InstantiatesTo] using hinstTo
          rcases instantiatesBy_wrapArrows (contents := ctor.contents) (τ := τ) hinstTo'
            with ⟨resultI, contentsI, hEq, hresI, hcontI⟩
          rcases instantiatesBy_customTy_bvarRange hresI with ⟨instTys, hResEq, hforall⟩
          have hinstTys : instTys = tyArgs.take ctor.paramCount := bvarRange_instantiates_take hforall
          have hresultI' : resultI = Ty.customTy ctor.tyName (tyArgs.take ctor.paramCount) := by
            rw [hResEq, hinstTys]
          have htyArgsTake : ∀ a ∈ tyArgs.take ctor.paramCount, a.IsLC := by
            intro a ha
            exact hLC a (List.mem_of_mem_take ha)
          have hfields : List.Forall₂ (InstantiatesBy (tyArgs.take ctor.paramCount)) ctor.contents contentsI := by
            refine forall2_instantiatesBy_take_of_agree (tys := ctor.contents) (its := contentsI)
              (fun t ht => ctor.bound t ht) ?_ hcontI
            intro t ht _ hinst'
            exact instantiatesBy_take_of_agree (n := ctor.paramCount) (ctor.bound t ht) hinst'
          have hct : ValTyped ctors (.ctorV name [])
              (PolyTy.mkTrivial (Ty.wrapArrows (Ty.customTy ctor.tyName (tyArgs.take ctor.paramCount)) contentsI)) := by
            exact ValTyped.ctorV (tyArgs := tyArgs.take ctor.paramCount)
              (instContents := []) (remContents := contentsI) hlook htyArgsTake .nil hfields
          have hWrap : Ty.wrapArrows (Ty.customTy ctor.tyName (tyArgs.take ctor.paramCount)) contentsI = τ := by
            rw [hEq, hresultI']
          have hv : ValTyped ctors (.ctorV name []) (PolyTy.mkTrivial τ) := by
            simpa [hWrap] using hct
          unfold StateOK
          exact ⟨PolyTy.mkTrivial τ, τ, hv, instantiates_trivial hτLC, hk⟩
  case lambda =>
      rename_i E ann body k
      unfold StateOK at h
      rcases h with ⟨Γ, τ, hE, he, hk⟩
      have hτLC : τ.IsLC := TypeOfHM.regular he
      cases he with
      | lambda hparamLC hpin hbctx hbody =>
          rename_i codom dom
          have hbody' : TypeOfHM ⟨PolyTy.mkTrivial dom :: Γ, ctors⟩ body codom := by
            rw [hbctx] at hbody
            simpa using hbody
          have hcodomLC : codom.IsLC := arrow_lc_r (by simpa using hτLC)
          unfold StateOK
          exact ⟨PolyTy.mkTrivial (.arrow dom codom), .arrow dom codom,
            ValTyped.lam hparamLC hcodomLC hE hbody', instantiates_trivial hτLC, hk⟩
  case var =>
      rename_i E i tyArgs k hlt
      unfold StateOK at h
      rcases h with ⟨Γ, τ, hE, he, hk⟩
      cases he with
      | var hlook hinstLC hinstTo =>
          rename_i polyTy instArgs
          have hΓlt : i < Γ.length := by
            by_contra hc
            have hn : Γ[i]? = none := List.getElem?_eq_none (by omega)
            rw [hlook] at hn
            simp at hn
          have hget : Γ.get ⟨i, hΓlt⟩ = polyTy := by
            have h := List.getElem?_eq_getElem hΓlt
            rw [hlook] at h
            exact (Option.some.inj h).symm
          have hv : ValTyped ctors (E.get ⟨i, hlt⟩) (Γ.get ⟨i, hΓlt⟩) := envOK_get hE i hlt hΓlt
          unfold StateOK
          refine ⟨Γ.get ⟨i, hΓlt⟩, τ, hv, ?_, hk⟩
          rw [hget]
          exact ⟨instArgs, hinstLC, hinstTo⟩
  case app =>
      rename_i E f a k
      unfold StateOK at h
      rcases h with ⟨Γ, τ, hE, he, hk⟩
      cases he with
      | app hf ha =>
          unfold StateOK
          exact ⟨Γ, .arrow _ _, hE, hf, KontTyped.appArg hE ha hk⟩
  case appArgStep =>
      rename_i fv E a k hIsVal
      unfold StateOK at h
      rcases h with ⟨σ, τ, hv, hinst, hk⟩
      cases hk with
      | appArg hE harg hk' =>
          rename_i A B Γ
          unfold StateOK
          refine ⟨Γ, A, hE, harg, ?_⟩
          exact KontTyped.appFun hIsVal ⟨σ, hv, hinst⟩ hk'
  case beta =>
      rename_i body E av k hIsVal
      unfold StateOK at h
      rcases h with ⟨σ, τ, hv, hinst, hk⟩
      cases hk with
      | appFun _hfvlam hvlam hk' =>
          rename_i B
          rcases hvlam with ⟨σl, hvlam', hinstl⟩
          cases hvlam' with
          | lam hτ₁ hτ₂ hElam hbody =>
              rename_i τ₁ τ₂ Γlam
              rcases hinstl with ⟨instArgs, hinstLC, hinstTo⟩
              have hEq := InstantiatesBy.eq_of_closed (ContainsBvarsUpTo.arrow hτ₁ hτ₂) hinstTo
              have hA : τ = τ₁ := by injection hEq
              have hB : B = τ₂ := by injection hEq
              have hvA : ValTyped ctors av (PolyTy.mkTrivial τ) :=
                ValTyped_inst_of_isVal hIsVal hv hinst
              have hbody' : TypeOfHM ⟨PolyTy.mkTrivial τ :: Γlam, ctors⟩ body B := by
                simpa [hA.symm, hB.symm] using hbody
              unfold StateOK
              exact ⟨PolyTy.mkTrivial τ :: Γlam, B, EnvOK.cons hvA hElam, hbody', hk'⟩
  case primOpPart =>
      rename_i op av k hIsVal
      unfold StateOK at h
      rcases h with ⟨σ, τ, hv, hinst, hk⟩
      cases hk with
      | appFun _hfvfun hvfun hk' =>
          rename_i B
          rcases hvfun with ⟨σf, hvprim, hinstf⟩
          cases hvprim with
          | primOp hprim =>
              rename_i τop
              rcases hinstf with ⟨instArgs, hinstLC, hinstTo⟩
              have hτopLC : τop.IsLC := PrimBinOp.ty_lc hprim
              have hEq := InstantiatesBy.eq_of_closed hτopLC hinstTo
              have hprim' : PrimBinOp.ty ctors op = some (.arrow τ B) := by
                simpa [hEq] using hprim
              have hvA : ValTyped ctors av (PolyTy.mkTrivial τ) :=
                ValTyped_inst_of_isVal hIsVal hv hinst
              have hBLC : B.IsLC := arrow_lc_r (by simpa [← hEq] using hτopLC)
              unfold StateOK
              exact ⟨PolyTy.mkTrivial B, B, ValTyped.primOpApp hIsVal hvA hprim',
                instantiates_trivial hBLC, hk'⟩
  case primOpDelta =>
      rename_i op a b r k hd
      unfold StateOK at h
      rcases h with ⟨σ, τ, hv, hinst, hk⟩
      cases hk with
      | appFun _hfvfun hvfun hk' =>
          rename_i B
          rcases hvfun with ⟨σf, hvpa, hinstf⟩
          cases hvpa with
          | primOpApp _hIsValA hvA hprim =>
              rename_i τ₁ τ₂
              rcases hinstf with ⟨instArgs, hinstLC, hinstTo⟩
              have hτ₂lc : τ₂.IsLC := arrow_lc_r (PrimBinOp.ty_lc hprim)
              have hEq := InstantiatesBy.eq_of_closed hτ₂lc hinstTo
              subst hEq
              cases op with
              | intAdd =>
                  have hB : B = .prim .int := primOp_int_ret hprim (Or.inl rfl)
                  cases a with
                  | unit => cases b <;> simp [PrimBinOp.delta] at hd
                  | int m =>
                      cases b with
                      | unit => simp [PrimBinOp.delta] at hd
                      | int n =>
                          simp [PrimBinOp.delta] at hd
                          have hr : r = .prim (.int (m + n)) := hd.symm
                          unfold StateOK
                          refine ⟨PolyTy.mkTrivial B, B, ?_,
                            instantiates_trivial (by simpa [hB] using (ContainsBvarsUpTo.prim : ContainsBvarsUpTo 0 (Ty.prim PrimTy.int))), hk'⟩
                          rw [hr, hB]
                          exact ValTyped.prim
                      | nat n => simp [PrimBinOp.delta] at hd
                      | char n => simp [PrimBinOp.delta] at hd
                  | nat n => cases b <;> simp [PrimBinOp.delta] at hd
                  | char n => cases b <;> simp [PrimBinOp.delta] at hd
              | intSub =>
                  have hB : B = .prim .int := primOp_int_ret hprim (Or.inr rfl)
                  cases a with
                  | unit => cases b <;> simp [PrimBinOp.delta] at hd
                  | int m =>
                      cases b with
                      | unit => simp [PrimBinOp.delta] at hd
                      | int n =>
                          simp [PrimBinOp.delta] at hd
                          have hr : r = .prim (.int (m - n)) := hd.symm
                          unfold StateOK
                          refine ⟨PolyTy.mkTrivial B, B, ?_,
                            instantiates_trivial (by simpa [hB] using (ContainsBvarsUpTo.prim : ContainsBvarsUpTo 0 (Ty.prim PrimTy.int))), hk'⟩
                          rw [hr, hB]
                          exact ValTyped.prim
                      | nat n => simp [PrimBinOp.delta] at hd
                      | char n => simp [PrimBinOp.delta] at hd
                  | nat n => cases b <;> simp [PrimBinOp.delta] at hd
                  | char n => cases b <;> simp [PrimBinOp.delta] at hd
              | intLt =>
                  rcases primOp_bool_ret hprim (Or.inl rfl) with ⟨hB, hT, hF⟩
                  cases a with
                  | unit => cases b <;> simp [PrimBinOp.delta] at hd
                  | int m =>
                      cases b with
                      | unit => simp [PrimBinOp.delta] at hd
                      | int n =>
                          simp [PrimBinOp.delta] at hd
                          have hr : r = .ctorV (if m < n then ⟨"True"⟩ else ⟨"False"⟩) [] := hd.symm
                          unfold StateOK
                          refine ⟨PolyTy.mkTrivial B, B, ?_,
                            instantiates_trivial (by simpa [hB] using (ContainsBvarsUpTo.customTy (by intro t ht; simp at ht) : ContainsBvarsUpTo 0 (Ty.customTy ⟨"Bool"⟩ []))), hk'⟩
                          by_cases hmn : m < n
                          · simpa [hr, hmn, hB] using valTyped_bool_ctor hT
                          · simpa [hr, hmn, hB] using valTyped_bool_ctor hF
                      | nat n => simp [PrimBinOp.delta] at hd
                      | char n => simp [PrimBinOp.delta] at hd
                  | nat n => cases b <;> simp [PrimBinOp.delta] at hd
                  | char n => cases b <;> simp [PrimBinOp.delta] at hd
              | charLt =>
                  rcases primOp_bool_ret hprim (Or.inr rfl) with ⟨hB, hT, hF⟩
                  cases a with
                  | unit => cases b <;> simp [PrimBinOp.delta] at hd
                  | int m => cases b <;> simp [PrimBinOp.delta] at hd
                  | nat n => cases b <;> simp [PrimBinOp.delta] at hd
                  | char m =>
                      cases b with
                      | unit => simp [PrimBinOp.delta] at hd
                      | int n => simp [PrimBinOp.delta] at hd
                      | nat n => simp [PrimBinOp.delta] at hd
                      | char n =>
                          simp [PrimBinOp.delta] at hd
                          have hr : r = .ctorV (if m.toNat < n.toNat then ⟨"True"⟩ else ⟨"False"⟩) [] := hd.symm
                          unfold StateOK
                          refine ⟨PolyTy.mkTrivial B, B, ?_,
                            instantiates_trivial (by simpa [hB] using (ContainsBvarsUpTo.customTy (by intro t ht; simp at ht) : ContainsBvarsUpTo 0 (Ty.customTy ⟨"Bool"⟩ []))), hk'⟩
                          by_cases hmn : m.toNat < n.toNat
                          · simpa [hr, hmn, hB] using valTyped_bool_ctor hT
                          · simpa [hr, hmn, hB] using valTyped_bool_ctor hF
  case ctorApp =>
      rename_i name args av k hIsVal
      unfold StateOK at h
      rcases h with ⟨σ, τ, hv, hinst, hk⟩
      cases hk with
      | appFun _hfvfun hvfun hk' =>
          rename_i B
          have hvA : ValTyped ctors av (PolyTy.mkTrivial τ) := ValTyped_inst_of_isVal hIsVal hv hinst
          rcases hvfun with ⟨σf, hvctorV, hinstf⟩
          cases hvctorV with
          | ctorV hlook htyArgs hargs hfields =>
              rename_i ctor tyArgs instContents remContents
              rcases hinstf with ⟨instArgs, hinstLC, hinstTo⟩
              cases remContents with
              | nil =>
                  cases hinstTo
              | cons c rest =>
                  cases hinstTo with
                  | arrow hc hrest =>
                      have hcLC : c.IsLC := by
                        rcases Forall₂_mem_right hfields c (List.mem_append.mpr (Or.inr List.mem_cons_self))
                          with ⟨content, hmemC, hinstC⟩
                        exact InstantiatesBy_lc htyArgs (ctor.bound content hmemC) hinstC
                      have hcEq : τ = c := InstantiatesBy.eq_of_closed hcLC hc
                      have hargs' : List.Forall₂ (fun a t => ValTyped ctors a (PolyTy.mkTrivial t))
                          (args ++ [av]) (instContents ++ [τ]) := by
                        exact forall2_snoc hargs hvA
                      have hfields' : List.Forall₂ (InstantiatesBy tyArgs) ctor.contents
                          ((instContents ++ [τ]) ++ rest) := by
                        simpa [List.append_assoc, hcEq] using hfields
                      have hct : ValTyped ctors (.ctorV name (args ++ [av]))
                          (PolyTy.mkTrivial (Ty.wrapArrows (Ty.customTy ctor.tyName tyArgs) rest)) := by
                        exact ValTyped.ctorV (remContents := rest) hlook htyArgs hargs' hfields'
                      unfold StateOK
                      refine ⟨PolyTy.mkTrivial (Ty.wrapArrows (Ty.customTy ctor.tyName tyArgs) rest), B, hct, ?_, hk'⟩
                      exact ⟨instArgs, hinstLC, hrest⟩
  case letIn =>
      rename_i E ann rhs body k
      unfold StateOK at h
      rcases h with ⟨Γ, τ, hE, he, hk⟩
      cases he with
      | letIn hwf hpin hgen hbctx hbody =>
          rename_i M L
          have hbody' : TypeOfHM ⟨M :: Γ, ctors⟩ body τ := by
            rw [hbctx] at hbody
            simpa using hbody
          unfold StateOK
          exact ⟨M :: Γ, τ, EnvOK.cons (ValTyped.thunk hE hpin hwf hgen) hE, hbody', hk⟩
  case letRec =>
      rename_i E anns bindings body k
      unfold StateOK at h
      rcases h with ⟨Γ, τ, hE, he, hk⟩
      cases he with
      | letRec hwf hmono hpoly hbctx hbody =>
          rename_i specs G L
          have hbody' : TypeOfHM ⟨specs.map (RecSpec.bodyScheme G) ++ Γ, ctors⟩ body τ := by
            rw [hbctx] at hbody
            simpa [RecSpecs.bodyCtx] using hbody
          unfold StateOK
          exact ⟨specs.map (RecSpec.bodyScheme G) ++ Γ, τ, EnvOK_bindGroup hE hwf hmono hpoly, hbody', hk⟩
  case matchScrut =>
      rename_i E scrut branches k
      unfold StateOK at h
      rcases h with ⟨Γ, τ, hE, he, hk⟩
      cases he with
      | match_ hscrut hne hbrs =>
          rename_i scrutTy
          unfold StateOK
          exact ⟨Γ, scrutTy, hE, hscrut, KontTyped.matchSel hE hbrs hne hk⟩
  case matchCtor =>
      rename_i name args E branches k pat body hfirst
      unfold StateOK at h
      rcases h with ⟨σ, τ, hv, hinst, hk⟩
      cases hv with
      | ctorV hlook htyArgs hargs hfields =>
          rename_i ctor tyArgs instContents remContents
          rcases hinst with ⟨instArgs, hinstLC, hinstTo⟩
          cases hk with
          | matchSel hE hbranches _hne hk' =>
              rename_i ρ' Γ
              have hbranch : TypeOfMatchBranch ⟨Γ, ctors⟩ (pat, body) τ ρ' :=
                hbranches (pat, body) (FirstMatchingBranch.mem hfirst)
              cases hbranch with
              | mk bspec hbctx hbodies =>
                  rename_i c n tyArgsS instContentsS
                  rcases bspec with ⟨hlookS, hscrutEq, harity, hbindcount, hfieldsS⟩
                  rename_i ctorS
                  have hmatches : (c == name && n == args.length) = true := by
                    simpa [MatchPattern.matchesCtor] using (FirstMatchingBranch.ctor_eq hfirst)
                  have hcand := (Bool.and_eq_true_eq_eq_true_and_eq_true _ _).mp hmatches
                  have hcbeq : (c == name) = true := hcand.1
                  have hnbeq : (n == args.length) = true := hcand.2
                  have hc : c = name := by
                    unfold BEq.beq at hcbeq
                    exact of_decide_eq_true hcbeq
                  have hn : n = args.length := by
                    unfold BEq.beq at hnbeq
                    exact of_decide_eq_true hnbeq
                  have hlookS' : LookupList.get? ctors name = some ctorS := by
                    simpa [hc] using hlookS
                  have hctorEq : ctorS = ctor := Option.some.inj (hlookS'.symm.trans hlook)
                  subst ctorS
                  rcases instantiatesBy_wrapArrows (result := Ty.customTy ctor.tyName tyArgs)
                    (contents := remContents) (τ := τ) hinstTo
                    with ⟨resultI, contentsI, hEq2, hresI, hcontI⟩
                  have hcontentsI_nil : contentsI = [] := by
                    cases contentsI with
                    | nil => rfl
                    | cons c' cs' =>
                        have hcon : Ty.customTy ctor.tyName tyArgsS = Ty.arrow c' (Ty.wrapArrows resultI cs') :=
                          hscrutEq.symm.trans hEq2
                        simp at hcon
                  have hresultI : resultI = Ty.customTy ctor.tyName tyArgsS := by
                    rw [hcontentsI_nil] at hEq2
                    simpa [Ty.wrapArrows] using hEq2.symm.trans hscrutEq
                  have hremContents : remContents = [] := by
                    rw [hcontentsI_nil] at hcontI
                    by_contra hc
                    rcases List.exists_cons_of_ne_nil hc with ⟨hd, tl, hceq⟩
                    rw [hceq] at hcontI
                    cases hcontI
                  have hresI' : InstantiatesBy instArgs (Ty.customTy ctor.tyName tyArgs)
                      (Ty.customTy ctor.tyName tyArgsS) := by
                    simpa [hresultI] using hresI
                  have hforall : List.Forall₂ (InstantiatesBy instArgs) tyArgs tyArgsS := by
                    cases hresI' with
                    | customTy hf => exact hf
                  have htyArgs_eq : tyArgs = tyArgsS := forall2_instantiatesBy_eq_of_lc htyArgs hforall
                  subst tyArgs
                  have hinstEq : instContents ++ remContents = instContentsS := by
                    refine forall2_det_instantiates ?_ hfields hfieldsS
                    intro t ht a b ha hb
                    exact InstantiatesBy.det_agree (fun k hk => rfl) (ctor.bound t ht) ha hb
                  have hinstContents : instContents = instContentsS := by
                    rw [hremContents] at hinstEq
                    simpa using hinstEq
                  have hpatBind : args.take (MatchPattern.bindCount (.named c n)) = args := by
                    rw [hn]
                    exact take_all_of_eq_length (l := args) rfl
                  have hargsV : List.Forall₂ (fun v σ => ValTyped ctors v σ) args
                      (instContents.map PolyTy.mkTrivial) := forall2_valTyped_mkTrivial hargs
                  have htakeV : List.Forall₂ (fun v σ => ValTyped ctors v σ)
                      (args.take (MatchPattern.bindCount (.named c n))) (instContentsS.map PolyTy.mkTrivial) := by
                    rw [hpatBind, ← hinstContents]
                    exact hargsV
                  have hEnv : EnvOK ctors (args.take (MatchPattern.bindCount (.named c n)) ++ E)
                      (instContentsS.map PolyTy.mkTrivial ++ Γ) :=
                    EnvOK_append hE (args.take (MatchPattern.bindCount (.named c n)))
                      (instContentsS.map PolyTy.mkTrivial) htakeV
                  have hbody' : TypeOfHM ⟨instContentsS.map PolyTy.mkTrivial ++ Γ, ctors⟩ body ρ' := by
                    rw [hbctx] at hbodies
                    simpa using hbodies
                  unfold StateOK
                  exact ⟨instContentsS.map PolyTy.mkTrivial ++ Γ, ρ', hEnv, hbody', hk'⟩
              | wildcard hbody =>
                  have hpatBind : args.take (MatchPattern.bindCount MatchPattern.wildcard) = [] := by
                    simp [MatchPattern.bindCount]
                  unfold StateOK
                  refine ⟨Γ, ρ', ?_, hbody, hk'⟩
                  simpa [hpatBind] using hE
  case matchWild =>
      rename_i v E branches k body hnon
      unfold StateOK at h
      rcases h with ⟨σ, τ, hv, hinst, hk⟩
      cases hk with
      | matchSel hE hbranches _hne hk' =>
          rename_i ρ' Γ
          have hbranch : TypeOfMatchBranch ⟨Γ, ctors⟩ (.wildcard, body) τ ρ' :=
            hbranches (.wildcard, body) List.mem_cons_self
          cases hbranch with
          | wildcard hbody =>
              unfold StateOK
              exact ⟨Γ, ρ', hE, hbody, hk'⟩
  case force =>
      rename_i ann e E k
      unfold StateOK at h
      rcases h with ⟨σ, τ, hv, hinst, hk⟩
      cases hv with
      | thunk hE hpin hMwf hgen =>
          rename_i L Γ
          unfold ErasedState at herased
          rcases herased with ⟨hthunk, hkErased⟩
          unfold Val.IsErased at hthunk
          rcases hthunk with ⟨hannWf, he, hEerased⟩
          have hty : TypeOfHM ⟨Γ, ctors⟩ e τ := GeneralisesTo_inst_ann he hgen hinst
          unfold StateOK
          exact ⟨Γ, τ, hE, hty, hk⟩
  case forceRecclo =>
      rename_i anns bindings E j k hlt
      unfold StateOK at h
      rcases h with ⟨σ, τ, hv, hinst, hk⟩
      cases hv with
      | recclo hj hE hwf hmono hpoly hσ =>
          rename_i specs G L Γ
          have hinst' : Instantiates (RecSpec.bodyScheme G (specs.get ⟨j, hj⟩)) τ := by
            simpa [hσ] using hinst
          have hmem : (bindings.get ⟨j, hlt⟩, specs.get ⟨j, hj⟩) ∈ bindings.zip specs :=
            mem_zip_get bindings specs j hlt hj
          have herasedBody : (bindings.get ⟨j, hlt⟩).IsErased := by
            unfold ErasedState at herased
            rcases herased with ⟨hrec, hkErased⟩
            unfold Val.IsErased at hrec
            rcases hrec with ⟨hannsWf, hbind, hEerased⟩
            exact hbind (bindings.get ⟨j, hlt⟩) (List.get_mem bindings ⟨j, hlt⟩)
          have hbody : TypeOfHM (RecSpecs.bodyCtx ⟨Γ, ctors⟩ specs G) (bindings.get ⟨j, hlt⟩) τ :=
            recclo_body_typed hwf hmono hpoly herasedBody hmem hinst'
          have hbody' : TypeOfHM ⟨specs.map (RecSpec.bodyScheme G) ++ Γ, ctors⟩
              (bindings.get ⟨j, hlt⟩) τ := by
            simpa [RecSpecs.bodyCtx] using hbody
          unfold StateOK
          exact ⟨specs.map (RecSpec.bodyScheme G) ++ Γ, τ,
            EnvOK_bindGroup hE hwf hmono hpoly, hbody', hk⟩

/-- Every value stored in an erased environment is itself erased. -/
private theorem erasedEnv_get {E : VEnv} (hE : ErasedEnv E) :
    ∀ i (h : i < E.length), (E.get ⟨i, h⟩).IsErased := by
  induction E with
  | nil =>
      intro i h
      simp at h
  | cons v E' ih =>
      intro i h
      cases i with
      | zero =>
          simp [ErasedEnv] at hE
          exact hE.1
      | succ i =>
          simp [ErasedEnv] at hE
          exact ih hE.2 i (Nat.lt_of_succ_lt_succ h)

/-- An erased environment is pointwise erased. -/
private theorem erasedEnv_mem {E : VEnv} (hE : ErasedEnv E) :
    ∀ v ∈ E, v.IsErased := by
  induction E with
  | nil =>
      intro v hv
      simp at hv
  | cons v E' ih =>
      simp [ErasedEnv] at hE
      intro w hw
      simp [List.mem_cons] at hw
      rcases hw with rfl | hw'
      · exact hE.1
      · exact ih hE.2 w hw'

/-- A pointwise-erased list is an erased environment. -/
private theorem erasedEnv_of_all {E : VEnv} (h : ∀ v ∈ E, v.IsErased) : ErasedEnv E := by
  induction E with
  | nil => simp [ErasedEnv]
  | cons v E' ih =>
      simp [ErasedEnv, h v (List.mem_cons_self ..),
        ih (fun w hw => h w (List.mem_cons_of_mem v hw))]

/-- An erased tail environment appended to a list of erased values is erased. -/
private theorem erasedEnv_append {E : VEnv} (hE : ErasedEnv E) :
    ∀ (xs : VEnv), (∀ x ∈ xs, x.IsErased) → ErasedEnv (xs ++ E) := by
  intro xs hxs
  induction xs with
  | nil => simp [hE]
  | cons x xs ih =>
      simp [ErasedEnv, hxs x (List.mem_cons_self ..),
        ih (fun y hy => hxs y (List.mem_cons_of_mem x hy))]

/-- A `bindGroup` environment is erased when every binding, every group scheme
    annotation (well-formed), and the captured environment are. -/
private theorem erasedEnv_bindGroup {anns : List (Option PolyTy)}
    {bindings : List Expr} {E : VEnv}
    (hannsWf : ∀ σ, some σ ∈ anns → σ.WF)
    (hbind : ∀ b ∈ bindings, b.IsErased) (hE : ErasedEnv E) :
    ErasedEnv (bindGroup anns bindings E) := by
  unfold bindGroup
  apply erasedEnv_append hE
  intro x hx
  rcases List.mem_map.mp hx with ⟨j, _, rfl⟩
  simp [Val.IsErased]
  exact ⟨hannsWf, hbind, erasedEnv_mem hE⟩

/-- Stepping preserves erased-ness (structural: reduction never introduces
    annotations). -/
theorem preservation_erased {s s' : State}
    (herased : ErasedState s) (hstep : StepM s s') :
    ErasedState s' := by
  cases hstep
  case primLit =>
      simp only [ErasedState, Val.IsErased] at herased ⊢
      exact ⟨trivial, herased.2.2⟩
  case primBinOp =>
      simp only [ErasedState, Val.IsErased] at herased ⊢
      exact ⟨trivial, herased.2.2⟩
  case ctor =>
      simp only [ErasedState, Val.IsErased] at herased ⊢
      refine ⟨?_, herased.2.2⟩
      simp
  case lambda =>
      simp only [ErasedState, Val.IsErased] at herased ⊢
      rcases herased with ⟨hE, hlam, hk⟩
      cases hlam with
      | lambda hbody => exact ⟨⟨hbody, erasedEnv_mem hE⟩, hk⟩
  case var =>
      rename_i E i tyArgs k hlt
      simp only [ErasedState] at herased ⊢
      rcases herased with ⟨hE, _, hk⟩
      exact ⟨erasedEnv_get hE i hlt, hk⟩
  case app =>
      simp only [ErasedState, ErasedKont] at herased ⊢
      rcases herased with ⟨hE, happ, hk⟩
      cases happ with
      | app hf ha => exact ⟨hE, hf, hE, ha, hk⟩
  case appArgStep =>
      simp only [ErasedState, ErasedKont] at herased ⊢
      rcases herased with ⟨hfv, hE, ha, hk⟩
      exact ⟨hE, ha, hfv, hk⟩
  case beta =>
      simp only [ErasedState, Val.IsErased, ErasedKont] at herased ⊢
      rcases herased with ⟨hav, hlam, hk⟩
      rcases hlam with ⟨hbody, hE⟩
      unfold ErasedEnv at ⊢
      exact ⟨⟨hav, erasedEnv_of_all hE⟩, hbody, hk⟩
  case primOpPart =>
      simp only [ErasedState, Val.IsErased, ErasedKont] at herased ⊢
      rcases herased with ⟨hav, hprim, hk⟩
      exact ⟨hav, hk⟩
  case primOpDelta =>
      rename_i op a b r k hd
      simp only [ErasedState, Val.IsErased, ErasedKont] at herased ⊢
      rcases herased with ⟨hpb, hpa, hk⟩
      have hrv : r.IsErased := by
        cases op <;> cases a <;> cases b <;> simp [PrimBinOp.delta] at hd
        all_goals
          cases hd
          simp [Val.IsErased]
      exact ⟨hrv, hk⟩
  case ctorApp =>
      simp only [ErasedState, Val.IsErased, ErasedKont] at herased ⊢
      rcases herased with ⟨hav, hargs, hk⟩
      refine ⟨?_, hk⟩
      intro a ha
      rw [List.mem_append] at ha
      rcases ha with ha | ha
      · exact hargs a ha
      · rw [List.mem_singleton] at ha
        subst a
        exact hav
  case letIn =>
      simp only [ErasedState] at herased ⊢
      rcases herased with ⟨hE, hlet, hk⟩
      cases hlet with
      | letIn hannWf hrhs hbody =>
          unfold ErasedEnv at ⊢
          unfold Val.IsErased at ⊢
          exact ⟨⟨⟨hannWf, hrhs, erasedEnv_mem hE⟩, hE⟩, hbody, hk⟩
  case letRec =>
      simp only [ErasedState] at herased ⊢
      rcases herased with ⟨hE, hrec, hk⟩
      cases hrec with
      | letRec hannsWf hbind hbody => exact ⟨erasedEnv_bindGroup hannsWf hbind hE, hbody, hk⟩
  case matchScrut =>
      simp only [ErasedState, ErasedKont] at herased ⊢
      rcases herased with ⟨hE, hmatch, hk⟩
      cases hmatch with
      | match_ hscrut hbodies =>
          refine ⟨hE, hscrut, hE, ?_, hk⟩
          intro pb hpb
          exact hbodies pb hpb
  case matchCtor =>
      rename_i name args E branches k pat body hfirst
      simp only [ErasedState, Val.IsErased, ErasedKont] at herased ⊢
      rcases herased with ⟨hargs, hE, hbranches, hk⟩
      refine ⟨erasedEnv_append hE _ (fun a ha => hargs a (List.mem_of_mem_take ha)), ?_, hk⟩
      exact hbranches (pat, body) (FirstMatchingBranch.mem hfirst)
  case matchWild =>
      rename_i v E branches k body hnon
      simp only [ErasedState, ErasedKont] at herased ⊢
      rcases herased with ⟨hv, hE, hbranches, hk⟩
      exact ⟨hE, hbranches (.wildcard, body) (List.mem_cons_self ..), hk⟩
  case force =>
      simp only [ErasedState, Val.IsErased] at herased ⊢
      rcases herased with ⟨hthunk, hk⟩
      rcases hthunk with ⟨hannWf, he, hE⟩
      exact ⟨erasedEnv_of_all hE, he, hk⟩
  case forceRecclo =>
      rename_i anns bindings E j k hlt
      simp only [ErasedState, Val.IsErased] at herased ⊢
      rcases herased with ⟨hrec, hk⟩
      rcases hrec with ⟨hannsWf, hbind, hE⟩
      exact ⟨erasedEnv_bindGroup hannsWf hbind (erasedEnv_of_all hE),
        hbind (bindings.get ⟨j, hlt⟩) (List.get_mem bindings ⟨j, hlt⟩), hk⟩

/-- Every value stored in an exhaustive environment is itself exhaustive. -/
private theorem exhaustiveEnv_get {ctors : CtorEnv} {E : VEnv} (hE : ExhaustiveEnv ctors E) :
    ∀ i (h : i < E.length), ExhaustiveVal ctors (E.get ⟨i, h⟩) := by
  induction E with
  | nil =>
      intro i h
      simp at h
  | cons v E' ih =>
      intro i h
      cases i with
      | zero =>
          simp [ExhaustiveEnv] at hE
          exact hE.1
      | succ i =>
          simp [ExhaustiveEnv] at hE
          exact ih hE.2 i (Nat.lt_of_succ_lt_succ h)

/-- An exhaustive tail environment appended to a list of exhaustive values is
    exhaustive (the list's elements are all covered by `ExhaustiveVal`). -/
private theorem exhaustiveEnv_append {ctors : CtorEnv} {E : VEnv} (hE : ExhaustiveEnv ctors E) :
    ∀ (xs : VEnv), (∀ x ∈ xs, ExhaustiveVal ctors x) → ExhaustiveEnv ctors (xs ++ E) := by
  intro xs hxs
  induction xs with
  | nil => simp [hE]
  | cons x xs ih =>
      simp [ExhaustiveEnv, hxs x (List.mem_cons_self ..),
        ih (fun y hy => hxs y (List.mem_cons_of_mem x hy))]

/-- A `bindGroup` environment is exhaustive when every binding and the captured
    environment are (each group member is a `recclo` built from them). -/
private theorem exhaustiveEnv_bindGroup {ctors : CtorEnv} {anns : List (Option PolyTy)}
    {bindings : List Expr} {E : VEnv}
    (hbind : ∀ b ∈ bindings, AllMatchesExhaustive ctors b) (hE : ExhaustiveEnv ctors E) :
    ExhaustiveEnv ctors (bindGroup anns bindings E) := by
  unfold bindGroup
  apply exhaustiveEnv_append hE
  intro x hx
  rcases List.mem_map.mp hx with ⟨j, _, rfl⟩
  simp [ExhaustiveVal, hE]
  exact hbind

/-- Stepping preserves exhaustiveness. -/
theorem preservation_exhaustive {ctors : CtorEnv} {s s' : State}
    (hexh : ExhaustiveState ctors s) (hstep : StepM s s') :
    ExhaustiveState ctors s' := by
  cases hstep
  case primLit =>
      simp only [ExhaustiveState, ExhaustiveVal] at hexh ⊢
      exact ⟨trivial, hexh.2.2⟩
  case primBinOp =>
      simp only [ExhaustiveState, ExhaustiveVal] at hexh ⊢
      exact ⟨trivial, hexh.2.2⟩
  case ctor =>
      simp only [ExhaustiveState, ExhaustiveVal] at hexh ⊢
      refine ⟨?_, hexh.2.2⟩
      simp
  case lambda =>
      simp only [ExhaustiveState, ExhaustiveVal] at hexh ⊢
      rcases hexh with ⟨hE, hlam, hk⟩
      cases hlam with
      | lambda hbody => exact ⟨⟨hbody, hE⟩, hk⟩
  case var =>
      rename_i E i tyArgs k hlt
      simp only [ExhaustiveState] at hexh ⊢
      rcases hexh with ⟨hE, _, hk⟩
      exact ⟨exhaustiveEnv_get hE i hlt, hk⟩
  case app =>
      simp only [ExhaustiveState, ExhaustiveKont] at hexh ⊢
      rcases hexh with ⟨hE, happ, hk⟩
      cases happ with
      | app hf ha => exact ⟨hE, hf, hE, ha, hk⟩
  case appArgStep =>
      simp only [ExhaustiveState, ExhaustiveKont] at hexh ⊢
      rcases hexh with ⟨hfv, hE, ha, hk⟩
      exact ⟨hE, ha, hfv, hk⟩
  case beta =>
      simp only [ExhaustiveState, ExhaustiveVal, ExhaustiveKont] at hexh ⊢
      rcases hexh with ⟨hav, hlam, hk⟩
      rcases hlam with ⟨hbody, hE⟩
      unfold ExhaustiveEnv at ⊢
      exact ⟨⟨hav, hE⟩, hbody, hk⟩
  case primOpPart =>
      simp only [ExhaustiveState, ExhaustiveVal, ExhaustiveKont] at hexh ⊢
      rcases hexh with ⟨hav, hprim, hk⟩
      exact ⟨hav, hk⟩
  case primOpDelta =>
      rename_i op a b r k hd
      simp only [ExhaustiveState, ExhaustiveVal, ExhaustiveKont] at hexh ⊢
      rcases hexh with ⟨hpb, hpa, hk⟩
      have hrv : ExhaustiveVal ctors r := by
        cases op <;> cases a <;> cases b <;> simp [PrimBinOp.delta] at hd
        all_goals
          cases hd
          simp [ExhaustiveVal]
      exact ⟨hrv, hk⟩
  case ctorApp =>
      simp only [ExhaustiveState, ExhaustiveVal, ExhaustiveKont] at hexh ⊢
      rcases hexh with ⟨hav, hargs, hk⟩
      refine ⟨?_, hk⟩
      intro a ha
      rw [List.mem_append] at ha
      rcases ha with ha | ha
      · exact hargs a ha
      · rw [List.mem_singleton] at ha
        subst a
        exact hav
  case letIn =>
      simp only [ExhaustiveState] at hexh ⊢
      rcases hexh with ⟨hE, hlet, hk⟩
      cases hlet with
      | letIn hrhs hbody =>
          unfold ExhaustiveEnv at ⊢
          unfold ExhaustiveVal at ⊢
          exact ⟨⟨⟨hrhs, hE⟩, hE⟩, hbody, hk⟩
  case letRec =>
      simp only [ExhaustiveState] at hexh ⊢
      rcases hexh with ⟨hE, hrec, hk⟩
      cases hrec with
      | letRec hbind hbody => exact ⟨exhaustiveEnv_bindGroup hbind hE, hbody, hk⟩
  case matchScrut =>
      simp only [ExhaustiveState, ExhaustiveKont] at hexh ⊢
      rcases hexh with ⟨hE, hmatch, hk⟩
      cases hmatch with
      | match_ hscrut hbodies hpin hcoverage =>
          rename_i tyName
          refine ⟨hE, hscrut, hE, ?_, ?_, hk⟩
          · intro pb hpb
            rcases pb with ⟨pat, body⟩
            exact hbodies.mem hpb
          · exact ⟨tyName, hpin, hcoverage⟩
  case matchCtor =>
      rename_i name args E branches k pat body hfirst
      simp only [ExhaustiveState, ExhaustiveVal, ExhaustiveKont] at hexh ⊢
      rcases hexh with ⟨hargs, hE, hbranches, _hcover, hk⟩
      refine ⟨exhaustiveEnv_append hE _ (fun a ha => hargs a (List.mem_of_mem_take ha)), ?_, hk⟩
      exact hbranches (pat, body) (FirstMatchingBranch.mem hfirst)
  case matchWild =>
      rename_i v E branches k body hnon
      simp only [ExhaustiveState, ExhaustiveKont] at hexh ⊢
      rcases hexh with ⟨hv, hE, hbranches, _hcover, hk⟩
      exact ⟨hE, hbranches (.wildcard, body) (List.mem_cons_self ..), hk⟩
  case force =>
      simp only [ExhaustiveState, ExhaustiveVal] at hexh ⊢
      rcases hexh with ⟨hthunk, hk⟩
      rcases hthunk with ⟨he, hE⟩
      exact ⟨hE, he, hk⟩
  case forceRecclo =>
      rename_i anns bindings E j k hlt
      simp only [ExhaustiveState, ExhaustiveVal] at hexh ⊢
      rcases hexh with ⟨hrec, hk⟩
      rcases hrec with ⟨hbind, hE⟩
      exact ⟨exhaustiveEnv_bindGroup hbind hE,
        hbind (bindings.get ⟨j, hlt⟩) (List.get_mem bindings ⟨j, hlt⟩), hk⟩

/-- Multi-step preservation. -/
theorem preservation_star {ctors : CtorEnv} {s s' : State} {ρ : Ty}
    (h : StateOK ctors s ρ) (herased : ErasedState s) (hstep : Relation.ReflTransGen StepM s s') :
    StateOK ctors s' ρ := by
  suffices hstrong : ErasedState s' ∧ StateOK ctors s' ρ from hstrong.2
  induction hstep with
  | refl =>
      exact ⟨herased, h⟩
  | tail hprev hstep' ih =>
      rcases ih with ⟨hEb, hOKb⟩
      exact ⟨preservation_erased hEb hstep', preservation hOKb hEb hstep'⟩

/-- Type safety: from a well-typed, exhaustive state, every reachable state is
    final or can step (the machine never gets stuck). -/
theorem type_safety {ctors : CtorEnv} {s : State} {ρ : Ty}
    (h : StateOK ctors s ρ) (hexh : ExhaustiveState ctors s) (herased : ErasedState s) :
    ∀ s', Relation.ReflTransGen StepM s s' →
      (∃ v, s' = .ret v .nil) ∨ ∃ s'', StepM s' s'' := by
  have hbundled : ∀ s', Relation.ReflTransGen StepM s s' →
      StateOK ctors s' ρ ∧ ExhaustiveState ctors s' ∧ ErasedState s' := by
    intro s' hs'
    induction hs' with
    | refl =>
        exact ⟨h, hexh, herased⟩
    | tail hprev hstep ih =>
        rcases ih with ⟨hOK, hExh, hEr⟩
        exact ⟨preservation hOK hEr hstep, preservation_exhaustive hExh hstep,
          preservation_erased hEr hstep⟩
  intro s' hs'
  exact progress (hbundled s' hs').1 (hbundled s' hs').2.1

/-- Type safety for a closed program: a well-typed, exhaustive, ERASED closed term
    is safe under the machine (corollary of `type_safety` at the empty environment).
    The erased-ness hypothesis is discharged by the pipeline's `erase` step, with a
    coherence lemma `TypeOfHM e τ → TypeOfHM (erase e) τ` (a separate slice). -/
theorem type_safety_closed {ctors : CtorEnv} {e : Expr} {τ : Ty}
    (h : TypeOfHM ⟨[], ctors⟩ e τ) (hexh : AllMatchesExhaustive ctors e) (herased : e.IsErased) :
    ∀ s', Relation.ReflTransGen StepM (.eval [] e .nil) s' →
      (∃ v, s' = .ret v .nil) ∨ ∃ s'', StepM s' s'' := by
  refine type_safety (ctors := ctors) (ρ := τ) ?_ ?_ ?_
  · unfold StateOK
    exact ⟨[], τ, EnvOK.nil, h, KontTyped.nil⟩
  · unfold ExhaustiveState
    simpa [ExhaustiveEnv, ExhaustiveKont] using hexh
  · unfold ErasedState
    simpa [ErasedEnv, ErasedKont] using herased

/-- The first branch of `brs` matching `(name, arity)` is unique. -/
private theorem FirstMatchingBranch_unique {name : CtorName} {arity : Nat}
    {brs : List (MatchPattern × Expr)} {p₁ p₂ : MatchPattern} {b₁ b₂ : Expr}
    (h₁ : FirstMatchingBranch name arity brs p₁ b₁)
    (h₂ : FirstMatchingBranch name arity brs p₂ b₂) : p₁ = p₂ ∧ b₁ = b₂ := by
  induction h₁ generalizing p₂ b₂ with
  | here hmatch =>
      cases h₂ with
      | here _ => simp
      | there hnmatch _ => simp [hmatch] at hnmatch
  | there hnmatch htail ih =>
      cases h₂ with
      | here hmatch₂ => simp [hnmatch] at hmatch₂
      | there hnmatch₂ htail₂ => exact ih htail₂

/-- The machine is deterministic. -/
theorem stepM_deterministic {s s₁ s₂ : State}
    (h₁ : StepM s s₁) (h₂ : StepM s s₂) : s₁ = s₂ := by
  induction h₁ generalizing s₂ with
  | primLit =>
      cases h₂
      rfl
  | primBinOp =>
      cases h₂
      rfl
  | ctor =>
      cases h₂
      rfl
  | lambda =>
      cases h₂
      rfl
  | var h =>
      cases h₂
      simp
  | app =>
      cases h₂
      rfl
  | appArgStep h =>
      cases h₂ with
      | appArgStep => rfl
      | force => simp [IsVal] at h
      | forceRecclo => simp [IsVal] at h
  | beta h =>
      cases h₂ with
      | beta => rfl
      | force => simp [IsVal] at h
      | forceRecclo => simp [IsVal] at h
  | primOpPart h =>
      cases h₂ with
      | primOpPart => rfl
      | force => simp [IsVal] at h
      | forceRecclo => simp [IsVal] at h
  | primOpDelta h =>
      cases h₂ with
      | primOpDelta hδ =>
          rw [h] at hδ
          cases hδ
          rfl
  | ctorApp h =>
      cases h₂ with
      | ctorApp => rfl
      | force => simp [IsVal] at h
      | forceRecclo => simp [IsVal] at h
  | letIn =>
      cases h₂
      rfl
  | letRec =>
      cases h₂
      rfl
  | matchScrut =>
      cases h₂
      rfl
  | matchCtor h =>
      cases h₂ with
      | matchCtor h₂first =>
          simp [FirstMatchingBranch_unique h h₂first]
      | matchWild h₂non =>
          simp [IsNonCtorVal] at h₂non
  | matchWild h =>
      cases h₂ with
      | matchWild => rfl
      | matchCtor => simp [IsNonCtorVal] at h
      | force => simp [IsNonCtorVal] at h
      | forceRecclo => simp [IsNonCtorVal] at h
  | force =>
      cases h₂ with
      | force => rfl
      | appArgStep h₂v => simp [IsVal] at h₂v
      | beta h₂v => simp [IsVal] at h₂v
      | primOpPart h₂v => simp [IsVal] at h₂v
      | ctorApp h₂v => simp [IsVal] at h₂v
      | matchWild h₂v => simp [IsNonCtorVal] at h₂v
  | forceRecclo h =>
      cases h₂ with
      | forceRecclo => rfl
      | appArgStep h₂v => simp [IsVal] at h₂v
      | beta h₂v => simp [IsVal] at h₂v
      | primOpPart h₂v => simp [IsVal] at h₂v
      | ctorApp h₂v => simp [IsVal] at h₂v
      | matchWild h₂v => simp [IsNonCtorVal] at h₂v

end CekMachine
