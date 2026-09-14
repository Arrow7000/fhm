import FHM.Bounds.InterpretedAnnotation
import FHM.Bounds.CountContract

/-! # Annotation-aware monomorphic fragment under a count interpretation

The source term and lexical count identities do not change at specialization.
Every carried lambda/let annotation is an obligation interpreted by `rows`.
Forgetting checked annotations recovers a derivation for the existing erased
runtime term; this is static bounds typing, not runtime length soundness.
Polymorphic let introduction, matches and recursion are deliberately absent.
-/

namespace FHM.Bounds.ScopedTyping

open CountSubstitution

inductive Derives (ids : List Nat) (rows : Bindings) (Δ : List Constraint) :
    List BoundsTy → Expr → BoundsTy → Prop where
  | literal {env p} : Derives ids rows Δ env (.primLit p) (boundInfoOfPrimLit p)
  | primBinOp {env op} : Derives ids rows Δ env (.primBinOp op) (Typed.primOpBounds op)
  | nil {env elem} : Derives ids rows Δ env (.ctor nilCtorName) (.list (.lit 0) (.lit 0) elem)
  | cons {env h t head elem lo hi} :
      Derives ids rows Δ env h head → Derives ids rows Δ env t (.list lo hi elem) →
      SemanticSub Δ head elem →
      Derives ids rows Δ env (.app (.app (.ctor consCtorName) h) t)
        (.list (.add lo (.lit 1)) (.add hi (.lit 1)) elem)
  | var {env i β} : env[i]? = some β → Derives ids rows Δ env (.var i) β
  | app {env f arg domain actual result} :
      Derives ids rows Δ env f (.arrow domain result) → Derives ids rows Δ env arg actual →
      SemanticSub Δ actual domain → Derives ids rows Δ env (.app f arg) result
  | lambda {env ann body param result} :
      InterpretedAnnotation.ParamOK ids rows Δ ann param →
      Derives ids rows Δ (param :: env) body result →
      Derives ids rows Δ env (.lambda ann body) (.arrow param result)
  | letMono {env ann rhs body actual result} :
      InterpretedAnnotation.BindingOK ids rows Δ ann actual →
      Derives ids rows Δ env rhs actual → Derives ids rows Δ (actual :: env) body result →
      Derives ids rows Δ env (.letIn ann rhs body) result

theorem erase {ids rows Δ env e β} (h : Derives ids rows Δ env e β) :
    Typed.Derives Δ env e.erase β := by
  induction h with
  | literal => simp only [Expr.erase]; exact .literal
  | primBinOp => simp only [Expr.erase]; exact .primBinOp
  | nil => simp only [Expr.erase]; exact .nil
  | cons _ _ hs ihh iht => simp only [Expr.erase]; exact .cons ihh iht hs
  | var hv => simp only [Expr.erase]; exact .var hv
  | app _ _ hs ihh iht => simp only [Expr.erase]; exact .app ihh iht hs
  | lambda _ _ ih => simp only [Expr.erase]; exact .lambda (ann := none) True.intro ih
  | letMono _ _ _ ihr ihb => simp only [Expr.erase]; exact .letIn (ann := none) True.intro ihr ihb

private theorem param_transport (outer : Bindings) (hf : Finite outer) {ids inner Δ ann β}
    (h : InterpretedAnnotation.ParamOK ids inner Δ ann β) :
    InterpretedAnnotation.ParamOK ids (CountAlgebra.compose outer inner)
      (Δ.map (constraint outer)) ann (bounds outer β) := by
  cases ann with
  | none => trivial
  | some τ => exact InterpretedAnnotation.transport outer hf h

private theorem binding_transport (outer : Bindings) (hf : Finite outer) {ids inner Δ ann β}
    (h : InterpretedAnnotation.BindingOK ids inner Δ ann β) :
    InterpretedAnnotation.BindingOK ids (CountAlgebra.compose outer inner)
      (Δ.map (constraint outer)) ann (bounds outer β) := by
  cases ann with
  | none => trivial
  | some σ => exact ⟨h.1, InterpretedAnnotation.transport outer hf h.2⟩

theorem transport (outer : Bindings) (hf : Finite outer) {ids inner Δ env e β}
    (h : Derives ids inner Δ env e β) :
    Derives ids (CountAlgebra.compose outer inner) (Δ.map (constraint outer))
      (env.map (bounds outer)) e (bounds outer β) := by
  induction h with
  | literal => cases ‹PrimLitExpr› <;> exact .literal
  | primBinOp => cases ‹PrimBinOp› <;> exact .primBinOp
  | nil => exact .nil
  | cons _ _ hs ihh iht => exact .cons ihh iht (subtype outer hf hs)
  | var hv => exact .var (by simpa using congrArg (Option.map (bounds outer)) hv)
  | app _ _ hs ihh iht => exact .app ihh iht (subtype outer hf hs)
  | lambda hp _ ih => exact .lambda (param_transport outer hf hp) ih
  | letMono hp _ _ ihr ihb => exact .letMono (binding_transport outer hf hp) ihr ihb

private theorem param_assuming {ids rows Δ Δ' ann β}
    (h : InterpretedAnnotation.ParamOK ids rows Δ ann β)
    (hp : (⟨Δ', Δ⟩ : ForallProblem).Valid) : InterpretedAnnotation.ParamOK ids rows Δ' ann β := by
  cases ann with
  | none => trivial
  | some τ => exact InterpretedAnnotation.assuming h hp

private theorem binding_assuming {ids rows Δ Δ' ann β}
    (h : InterpretedAnnotation.BindingOK ids rows Δ ann β)
    (hp : (⟨Δ', Δ⟩ : ForallProblem).Valid) : InterpretedAnnotation.BindingOK ids rows Δ' ann β := by
  cases ann with
  | none => trivial
  | some σ => exact ⟨h.1, InterpretedAnnotation.assuming h.2 hp⟩

theorem assuming {ids rows Δ Δ' env e β} (h : Derives ids rows Δ env e β)
    (hp : (⟨Δ', Δ⟩ : ForallProblem).Valid) : Derives ids rows Δ' env e β := by
  induction h with
  | literal => exact .literal
  | primBinOp => exact .primBinOp
  | nil => exact .nil
  | cons _ _ hs ihh iht => exact .cons ihh iht (hs.assuming hp)
  | var hv => exact .var hv
  | app _ _ hs ihh iht => exact .app ihh iht (hs.assuming hp)
  | lambda hp' _ ih => exact .lambda (param_assuming hp' hp) ih
  | letMono hp' _ _ ihr ihb => exact .letMono (binding_assuming hp' hp) ihr ihb

#print axioms erase
#print axioms transport
#print axioms assuming

theorem erased_tyFreeVars {ids rows Δ env e β} (h : Derives ids rows Δ env e β) :
    e.erase.tyFreeVars = [] := by
  induction h <;> simp_all [Expr.erase, Expr.tyFreeVars]

/-- An annotation-checked RHS generalizes only identities fresh for both its
    captured environment and original source annotations. The existing erased
    RHS specialization theorem is reused; unchecked annotations are not erased
    to manufacture a certificate. Caller HM/count identities may overlap. -/
theorem binder_instances {σ ids rows Δ env e β}
    (a : BinderBridge.Abstraction σ β
      (env.map Synth.BoundsTy.toTy ++ e.tyFreeVars.map Ty.fvar))
    (h : Derives ids rows Δ env e β) :
    ∀ args, (SchemeTyping.fromBinder a).Arguments args →
      SchemeTyping.Derives Δ (env.map SchemeTyping.Binding.mono) e.erase
        ((SchemeTyping.fromBinder a).instantiate args) := by
  intro args _
  let erased : BinderBridge.Abstraction σ β
      (env.map Synth.BoundsTy.toTy ++ e.erase.tyFreeVars.map Ty.fvar) :=
    { a with
      fresh := by
        intro i hi t ht
        simp only [erased_tyFreeVars h, List.map_nil, List.append_nil] at ht
        exact a.fresh i hi t (List.mem_append_left _ ht) }
  exact SchemeTyping.ofMonomorphic
    (SchemeSpecialization.fromBinder erased (erase h) (SchemeUse.vector args))

#print axioms binder_instances

end FHM.Bounds.ScopedTyping
