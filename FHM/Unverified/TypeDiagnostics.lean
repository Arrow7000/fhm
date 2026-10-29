import FHM.Unverified.HMDisplay

/-!
# Structured explanations for application errors

The verified inferer remains the acceptance gate. On rejection, this editor-only
probe reuses its successful subexpression results and the same unifier to locate
an application failure. Unsupported failures retain the existing diagnostic.
This is a first diagnostic slice, not a second type checker or error recovery.
-/

namespace FHM.Unverified.TypeDiagnostics

open SurfaceBridge.Provenance Surface.Span

inductive Reason where
  | argumentMismatch (expected actual : Ty)
  | namedArgumentMismatch (names : List String) (expected actual : Ty)
  | notFunction (actual : Ty)
  | infiniteType (varId : Nat) (within : Ty)
  | incompatibleApplication (functionType argumentType : Ty)
  deriving Repr

structure Error where
  path : CorePath
  reason : Reason
  deriving Repr

def Reason.code : Reason → String
  | .argumentMismatch .. | .namedArgumentMismatch .. => "type.argumentMismatch"
  | .notFunction .. => "type.notFunction"
  | .infiniteType .. => "type.infiniteType"
  | .incompatibleApplication .. => "type.incompatibleApplication"

def Error.below (step : CoreStep) (e : Error) : Error :=
  { e with path := step :: e.path }

/-- Follow only a failed inference path, using verified inference for successful
    siblings. No inferred placeholder or error result enters program checking. -/
def probeCore (K : List Nat) (Φ : Nat) (ctx : Ctx) : Expr → Option Error
  | .lambda ann body =>
      let T := ann.getD (.fvar Φ)
      let next := if ann.isSome then Φ else Φ + 1
      (probeCore K next { ctx with env := PolyTy.mkTrivial T :: ctx.env } body).map
        (Error.below .lambdaBody)
  | .app f arg =>
      match inferCore K Φ ctx (Expr.ofCore f) with
      | none => (probeCore K Φ ctx f).map (Error.below .appFun)
      | some result =>
        let ⟨Φ₁, S₁, τf⟩ := result.val
        match inferCore K Φ₁ (S₁.onCtx ctx) (Expr.ofCore arg) with
        | none => (probeCore K Φ₁ (S₁.onCtx ctx) arg).map (Error.below .appArg)
        | some result =>
          let ⟨Φ₂, S₂, τa⟩ := result.val
          let fnTy := S₂.onTy τf
          if (unifyCoreK K fnTy (.arrow τa (.fvar Φ₂))).isSome then none
          else match fnTy with
            | .arrow expected _ => some ⟨[.appArg], .argumentMismatch expected τa⟩
            | .fvar n =>
                if n ∈ τa.freeVars then
                  some ⟨[], .infiniteType n (.arrow τa (.fvar Φ₂))⟩
                else some ⟨[], .incompatibleApplication fnTy τa⟩
            | _ => some ⟨[.appFun], .notFunction fnTy⟩
  | .letIn none rhs body =>
      match inferCore K Φ ctx (Expr.ofCore rhs) with
      | none => (probeCore K Φ ctx rhs).map (Error.below .letRhs)
      | some result =>
          let ⟨Φ₁, S₁, τ₁⟩ := result.val
          let ctx₁ := S₁.onCtx ctx
          let σ := genScheme K ctx₁.env τ₁
          (probeCore K Φ₁ { ctx₁ with env := σ :: ctx₁.env } body).map
            (Error.below .letBody)
  | .letIn (some σ) rhs body =>
      let Ys := freshVars Φ σ.paramCount
      let rigid := K ++ Ys
      let opened := rhs.openTyVars Ys
      match inferCore rigid (Φ + σ.paramCount) ctx (Expr.ofCore opened) with
      | none => (probeCore rigid (Φ + σ.paramCount) ctx opened).map (Error.below .letRhs)
      | some result =>
        let ⟨Φ₁, S₁, τ₁⟩ := result.val
        match unifyCoreK rigid τ₁ (PolyTy.openVars Ys σ) with
        | none => none -- Existing annotation diagnostics handle this case.
        | some ⟨Schk, _⟩ =>
          if ∀ y ∈ Ys, y ∉ (Schk.onCtx (S₁.onCtx ctx)).env.freeVars then
            let ctx₁ := Schk.onCtx (S₁.onCtx ctx)
            (probeCore K Φ₁ { ctx₁ with env := σ :: ctx₁.env } body).map
              (Error.below .letBody)
          else none
  | _ => none
termination_by e => e.size
decreasing_by
  all_goals simp only [Expr.size, Expr.size_openTyVars]
  all_goals omega

/-- Keep repeated source names local to this one written parameter annotation.
This explains a failed application; it does not supply types to inference. -/
private def argumentReason (fn : InferInput) (expected actual : Ty) : Reason :=
  let names := match fn with
    | .lambda (some t) _ => t.names.dedup.filter fun name => 1 < t.names.count name
    | _ => []
  if names.isEmpty then .argumentMismatch expected actual
  else .namedArgumentMismatch names expected actual

/-- Partial annotations follow the canonical worker. Completed subtrees retain
    the existing, more detailed annotation diagnostics. -/
partial def probe (K : List Nat) (Φ : Nat) (ctx : Ctx)
    (input : InferInput) : Option Error :=
  match input.toCore with
  | some core => probeCore K Φ ctx core
  | none => match input with
    | .lambda ann body => do
        let result ← seed K Φ ann
        (probe K result.val.1 { ctx with env := PolyTy.mkTrivial result.val.2 :: ctx.env } body).map
          (Error.below .lambdaBody)
    | .app f arg =>
        match inferCore K Φ ctx f with
        | none => (probe K Φ ctx f).map (Error.below .appFun)
        | some result =>
          let ⟨Φ₁, S₁, τf⟩ := result.val
          match inferCore K Φ₁ (S₁.onCtx ctx) arg with
          | none => (probe K Φ₁ (S₁.onCtx ctx) arg).map (Error.below .appArg)
          | some result =>
            let ⟨Φ₂, S₂, τa⟩ := result.val
            let fnTy := S₂.onTy τf
            if (unifyCoreK K fnTy (.arrow τa (.fvar Φ₂))).isSome then none
            else match fnTy with
              | .arrow expected _ => some ⟨[.appArg], argumentReason f expected τa⟩
              | .fvar n =>
                  if n ∈ τa.freeVars then
                    some ⟨[], .infiniteType n (.arrow τa (.fvar Φ₂))⟩
                  else some ⟨[], .incompatibleApplication fnTy τa⟩
              | _ => some ⟨[.appFun], .notFunction fnTy⟩
    -- A signed RHS has to be opened in the worker's scoped context. Until a
    -- canonical failure result is available, retain the binding-level fallback.
    | .letIn ann rhs body =>
        if ann.isSignature then none
        else match inferCore K Φ ctx rhs with
        | none => (probe K Φ ctx rhs).map (Error.below .letRhs)
        | some result => do
            let ⟨Φ₁, S₁, τ₁⟩ := result.val
            let checked ← checkLet K [] Φ₁ ann.annotationView τ₁
            let ctx₁ := checked.val.2.onCtx (S₁.onCtx ctx)
            let σ := genScheme K ctx₁.env (checked.val.2.onTy τ₁)
            (probe K checked.val.1 { ctx₁ with env := σ :: ctx₁.env } body).map
              (Error.below .letBody)
    | _ => none

/-- Keep type values and location separate from human-facing wording. -/
def Reason.message (reason : Reason) : String :=
  let types := match reason with
    | .argumentMismatch a b | .namedArgumentMismatch _ a b | .incompatibleApplication a b => [a, b]
    | .notFunction a => [a]
    | .infiniteType n a => [.fvar n, a]
  let display : FHM.Unverified.HMDisplay.Context := {
    freeIds := (types.flatMap Ty.freeVars).eraseDups
  }
  let pretty := FHM.Unverified.HMDisplay.pretty display
  match reason with
  | .argumentMismatch expected actual =>
      s!"type mismatch: expected {pretty expected}, got {pretty actual}"
  | .namedArgumentMismatch names expected actual =>
      let labels := String.intercalate ", " (names.map ("?" ++ ·))
      s!"type mismatch: expected {pretty expected}, got {pretty actual}; repeated names ({labels}) each keep one type within this parameter annotation"
  | .notFunction actual => s!"cannot apply a value of type {pretty actual} as a function"
  | .infiniteType n within =>
      s!"infinite type: {pretty (.fvar n)} would have to equal {pretty within}"
  | .incompatibleApplication fn arg =>
      s!"cannot apply a value of type {pretty fn} to an argument of type {pretty arg}"

/-- Only report explanations for rejected programs and authored source spans.
    Generated lowering nodes may share an owner's span, so unsupported origins
    fall back to the existing binding-level error. -/
def explain (ctors : CtorEnv) (lowered : InputLowered) : Option (Reason × Span) := do
  if (inferCore lowered.expr.rigidVars lowered.expr.source_freshFloor ⟨[], ctors⟩ lowered.expr).isSome then none
  else do
    let error ← probe lowered.expr.rigidVars lowered.expr.source_freshFloor ⟨[], ctors⟩ lowered.expr
    let origin ← (lowered.coreOrigins.find? fun p => p.1 == error.path).map (·.2)
    if origin.kind == .authored then some (error.reason, origin.source.span) else none

end FHM.Unverified.TypeDiagnostics
