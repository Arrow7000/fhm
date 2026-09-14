import FHM.Bounds.SchemeUse

/-! # Scheme-aware static bounds judgement

HM schemes remain supplied by the authoritative artifact. Count quantification
is not introduced here: counts in a scheme body are captured lexical identities.
A polymorphic let requires a universally typed RHS, not shape abstraction alone.
These rules extend the initial static fragment; runtime soundness, generalization
transport for scheme environments and executable traversal remain separate work.
-/

namespace FHM.Bounds.SchemeTyping

structure Scheme where
  hm : PolyTy
  body : BoundsTy
  wf : hm.eraseBounds.WF
  shape : Synth.BoundsTy.toTy body = hm.body.eraseBounds

inductive Binding where
  | mono (bounds : BoundsTy)
  | poly (scheme : Scheme)

def Scheme.instantiate (s : Scheme) (args : List BoundsTy) : BoundsTy :=
  TypeSubstitution.substitute (SchemeUse.vector args) s.body

/-- Finite caller type arguments have the exact scheme arity and contain no
    enclosing HM bound slots. Count-scope/origin evidence belongs to the caller. -/
def Scheme.Arguments (s : Scheme) (args : List BoundsTy) : Prop :=
  Ty.AreLC s.hm.paramCount (args.map Synth.BoundsTy.toTy)

inductive Derives (Δ : List Constraint) : List Binding → Expr → BoundsTy → Prop where
  | literal {env p} : Derives Δ env (.primLit p) (boundInfoOfPrimLit p)
  | primBinOp {env op} : Derives Δ env (.primBinOp op) (Typed.primOpBounds op)
  | nil {env elem} : Derives Δ env (.ctor nilCtorName) (.list (.lit 0) (.lit 0) elem)
  | cons {env h t head elem lo hi} :
      Derives Δ env h head → Derives Δ env t (.list lo hi elem) →
      SemanticSub Δ head elem →
      Derives Δ env (.app (.app (.ctor consCtorName) h) t)
        (.list (.add lo (.lit 1)) (.add hi (.lit 1)) elem)
  | varMono {env i β} : env[i]? = some (.mono β) → Derives Δ env (.var i) β
  | varPoly {env i s args} : env[i]? = some (.poly s) → s.Arguments args →
      Derives Δ env (.var i) (s.instantiate args)
  | app {env f arg domain actual result} :
      Derives Δ env f (.arrow domain result) → Derives Δ env arg actual →
      SemanticSub Δ actual domain → Derives Δ env (.app f arg) result
  | lambda {env ann body param result} :
      Typed.ParamOK Δ ann param → Derives Δ (.mono param :: env) body result →
      Derives Δ env (.lambda ann body) (.arrow param result)
  | letMono {env ann rhs body actual result} :
      Typed.BindingOK Δ ann actual → Derives Δ env rhs actual →
      Derives Δ (.mono actual :: env) body result →
      Derives Δ env (.letIn ann rhs body) result
  | letPoly {env rhs body s result} :
      (∀ args, s.Arguments args → Derives Δ env rhs (s.instantiate args)) →
      Derives Δ (.poly s :: env) body result →
      Derives Δ env (.letIn none rhs body) result

/-- Every initial monomorphic derivation embeds without changing its bounds or
    source. The old fragment is not silently reinterpreted as polymorphic. -/
theorem ofMonomorphic {Δ env e β} (h : Typed.Derives Δ env e β) :
    Derives Δ (env.map Binding.mono) e β := by
  induction h with
  | literal => exact .literal
  | primBinOp => exact .primBinOp
  | nil => exact .nil
  | cons _ _ hs ihh iht => exact .cons ihh iht hs
  | var hv => exact .varMono (by simpa using congrArg (Option.map Binding.mono) hv)
  | app _ _ hs ihh iht => exact .app ihh iht hs
  | lambda hp _ ih => exact .lambda hp ih
  | letIn hp _ _ ihr ihb => exact .letMono hp ihr ihb

def fromBinder {σ β captures} (a : BinderBridge.Abstraction σ β captures) : Scheme :=
  ⟨σ, BinderBridge.close a.ids β, a.hmOpening.wf, a.shape⟩

/-- Existing certified RHS specialization supplies the genuine universal premise
    of `letPoly` when the RHS belongs to the initial monomorphic fragment. -/
theorem binder_instances {σ Δ env rhs β}
    (a : BinderBridge.Abstraction σ β
      (env.map Synth.BoundsTy.toTy ++ rhs.tyFreeVars.map Ty.fvar))
    (h : Typed.Derives Δ env rhs β) :
    ∀ args, (fromBinder a).Arguments args →
      Derives Δ (env.map Binding.mono) rhs ((fromBinder a).instantiate args) := by
  intro args _
  exact ofMonomorphic (SchemeSpecialization.fromBinder a h (SchemeUse.vector args))

/-- A checked artifact abstraction and universally typed fragment RHS may be
    introduced into the scheme-aware body environment. Annotated polymorphic
    declarations deliberately require a separate future rule. -/
theorem let_fromBinder {σ Δ env rhs body β result}
    (a : BinderBridge.Abstraction σ β
      (env.map Synth.BoundsTy.toTy ++ rhs.tyFreeVars.map Ty.fvar))
    (h : Typed.Derives Δ env rhs β)
    (hb : Derives Δ (.poly (fromBinder a) :: env.map Binding.mono) body result) :
    Derives Δ (env.map Binding.mono) (.letIn none rhs body) result :=
  .letPoly (binder_instances a h) hb

/-- Every declarative scheme use has an actual relational HM instance, not
    merely an unconstrained shape constructed by the bounds pass. -/
theorem instance_shape (s : Scheme) (args : List BoundsTy) (ha : s.Arguments args) :
    s.hm.eraseBounds.InstantiatesTo (args.map Synth.BoundsTy.toTy)
      (Synth.BoundsTy.toTy (s.instantiate args)) := by
  have arity : args.length = s.hm.paramCount := by simpa using ha.1
  have hlen : s.hm.eraseBounds.paramCount ≤ (args.map Synth.BoundsTy.toTy).length := by
    simp only [PolyTy.eraseBounds_paramCount, List.length_map]
    omega
  have hi := InstantiatesBy.openWith s.wf hlen
  change InstantiatesBy (args.map Synth.BoundsTy.toTy) s.hm.body.eraseBounds
    (Ty.openWith (args.map Synth.BoundsTy.toTy) s.hm.body.eraseBounds) at hi
  change InstantiatesBy (args.map Synth.BoundsTy.toTy) s.hm.body.eraseBounds _
  rw [Scheme.instantiate, TypeSubstitution.shape, s.shape]
  rw [TypeSubstitution.hm_instance hi _ (fun _ _ h => SchemeUse.vector_shape rfl h)]
  exact hi

#print axioms ofMonomorphic
#print axioms binder_instances
#print axioms let_fromBinder
#print axioms instance_shape

end FHM.Bounds.SchemeTyping
