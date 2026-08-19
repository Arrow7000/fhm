import FHM.Core
import FHM.InferW

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
    | ctorV {name args} {ctor : Ctor} {tyArgs instContents : List Ty}
        (hlook : LookupList.get? ctors name = some ctor)
        (htyArgs : ∀ a ∈ tyArgs, a.IsLC)
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

/-- An already-forced value at scheme `σ` is also at any monotype `τ` that `σ`
    instantiates to. (This closes `ValTyped` downward only for `IsVal` values —
    the ones consumed at a monotype without being forced first; thunks and
    rec-closures are instead consumed via the `Instantiates` premise in
    `StateOK`/`KontTyped`, never through this lemma.) -/
theorem ValTyped_inst_of_isVal {ctors : CtorEnv} {v : Val} {σ : PolyTy} {τ : Ty}
    (hvIsVal : IsVal v) (hv : ValTyped ctors v σ) (hinst : Instantiates σ τ) :
    ValTyped ctors v (PolyTy.mkTrivial τ) := by
  sorry

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
  sorry

/-- Each recursive-group member's RHS types, in the BODY context, at any instance
    of its body scheme. The machine analogue of `TypeOfElabHM.rewrap_hasScheme_*`;
    needed by `preservation`'s `forceRecclo` case. -/
theorem recclo_body_typed {ctors : CtorEnv} {Γ : Env} {anns : List (Option PolyTy)}
    {bindings : List Expr} {specs : List RecSpec} {G L : List Nat}
    {e : Expr} {spec : RecSpec} {τ : Ty}
    (hwf : RecSpecs.WF anns bindings specs G)
    (hmono : RecSpecs.MonoTyped TypeOfHM ⟨Γ, ctors⟩ bindings specs G L)
    (hpoly : RecSpecs.PolyTyped TypeOfHM ⟨Γ, ctors⟩ bindings specs G L)
    (hmem : (e, spec) ∈ bindings.zip specs)
    (hinst : Instantiates (RecSpec.bodyScheme G spec) τ) :
    TypeOfHM (RecSpecs.bodyCtx ⟨Γ, ctors⟩ specs G) e τ := by
  sorry

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
      (hv : ∃ σ, ValTyped ctors fv σ ∧ Instantiates σ (.arrow A B))
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
  | .ret v k => ∃ σ τ, ValTyped ctors v σ ∧ Instantiates σ τ ∧ KontTyped ctors k τ ρ

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
      | match_ hscrut hbodies _ _ =>
          refine ⟨hE, hscrut, hE, ?_, hk⟩
          intro pb hpb
          rcases pb with ⟨pat, body⟩
          exact hbodies.mem hpb
  case matchCtor =>
      rename_i name args E branches k pat body hfirst
      simp only [ExhaustiveState, ExhaustiveVal, ExhaustiveKont] at hexh ⊢
      rcases hexh with ⟨hargs, hE, hbranches, hk⟩
      refine ⟨exhaustiveEnv_append hE _ (fun a ha => hargs a (List.mem_of_mem_take ha)), ?_, hk⟩
      exact hbranches (pat, body) (FirstMatchingBranch.mem hfirst)
  case matchWild =>
      rename_i v E branches k body hnon
      simp only [ExhaustiveState, ExhaustiveKont] at hexh ⊢
      rcases hexh with ⟨hv, hE, hbranches, hk⟩
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
