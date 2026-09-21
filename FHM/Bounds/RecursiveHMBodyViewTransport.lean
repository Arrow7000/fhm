import FHM.Bounds.RecursiveHMClosedSpecializableEnvironment

/-! # Static transport through raw recursive-environment views

Recursive RHS certificates use one raw `Binding` environment.  Generalized
bodies observe that environment through either its fixed in-SCC view or its
ordinary post-exit view.  This module makes that choice explicit and packages
the common target of count-first/HM-second closing.  The initial constructors
below cover the view-independent structural fragment; generalized binding and
group boundaries remain separate work.
-/

namespace FHM.Bounds.RecursiveHMUniform

open RecursiveHMJudgement SchemeSpecialization CountSubstitution

/-- The two body interpretations of one raw recursive environment. -/
inductive RawBodyView where
  | fixed
  | ordinary
  deriving DecidableEq

def RawBodyView.env (view : RawBodyView) (raw : List Binding) : List BodyBinding :=
  match view with
  | .fixed => fixedBodyEnv raw
  | .ordinary => ordinaryBodyEnv raw

@[simp] theorem RawBodyView.env_fixed (raw : List Binding) :
    RawBodyView.fixed.env raw = fixedBodyEnv raw := rfl

@[simp] theorem RawBodyView.env_ordinary (raw : List Binding) :
    RawBodyView.ordinary.env raw = ordinaryBodyEnv raw := rfl

theorem RawBodyView.env_length (view : RawBodyView) (raw : List Binding) :
    (view.env raw).length = raw.length := by
  cases view <;> simp [RawBodyView.env, fixedBodyEnv, ordinaryBodyEnv]

theorem RawBodyView.env_append (view : RawBodyView) (left right : List Binding) :
    view.env (left ++ right) = view.env left ++ view.env right := by
  cases view <;> simp [RawBodyView.env, fixedBodyEnv, ordinaryBodyEnv]

/-- The bounds transformation shared by the closed recursive judgment and its
    fixed/ordinary body views. -/
def EnvSpecialization.mapBounds {raw : List Binding}
    (world : EnvSpecialization raw) (beta : BoundsTy) : BoundsTy :=
  mapFree world.types (bounds world.outer beta)

/-- One static derivation transported into a recursively closed environment
    while retaining the selected body view.  Keeping this as a package lets
    later induction cases compose without repeatedly exposing the dependent
    target environment. -/
structure BodyViewSpecialized
    (view : RawBodyView) (raw : List Binding)
    {types slots : Nat → BoundsTy} {ids : List Nat} {rows : Bindings}
    {Delta : List Constraint} {expr : Expr} {beta : BoundsTy}
    (source : ScopedBodyDerives types slots ids rows Delta (view.env raw) expr beta)
    (world : EnvSpecialization raw) where
  typing : ScopedBodyDerives
    (fun i => world.mapBounds (types i))
    (fun i => world.mapBounds (slots i))
    ids (CountAlgebra.compose world.outer rows)
    (Delta.map (constraint world.outer))
    (view.env (closeRecursiveEnv world.outer world.types raw))
    expr (world.mapBounds beta)

namespace BodyViewSpecialized

def literal (view : RawBodyView) (raw : List Binding) (world : EnvSpecialization raw)
    (p : PrimLitExpr) :
    BodyViewSpecialized view raw
      (@ScopedBodyDerives.literal types slots ids rows Delta (view.env raw) p) world := by
  refine ⟨?_⟩
  cases p <;> exact .literal

def primBinOp (view : RawBodyView) (raw : List Binding) (world : EnvSpecialization raw)
    (op : PrimBinOp) :
    BodyViewSpecialized view raw
      (@ScopedBodyDerives.primBinOp types slots ids rows Delta (view.env raw) op) world := by
  refine ⟨?_⟩
  cases op <;> exact .primBinOp

def app
    {view : RawBodyView} {raw : List Binding}
    {types slots : Nat → BoundsTy} {ids : List Nat} {rows : Bindings}
    {Delta : List Constraint} {fn arg : Expr} {domain actual result : BoundsTy}
    {hfn : ScopedBodyDerives types slots ids rows Delta (view.env raw) fn
      (.arrow domain result)}
    {harg : ScopedBodyDerives types slots ids rows Delta (view.env raw) arg actual}
    (sub : SemanticSub Delta actual domain) (world : EnvSpecialization raw)
    (fnClosed : BodyViewSpecialized view raw hfn world)
    (argClosed : BodyViewSpecialized view raw harg world) :
    BodyViewSpecialized view raw (ScopedBodyDerives.app hfn harg sub) world := by
  refine ⟨.app fnClosed.typing argClosed.typing ?_⟩
  exact SchemeSpecialization.subtype world.types
    (CountSubstitution.subtype world.outer world.outerFinite sub)

def subsumption
    {view : RawBodyView} {raw : List Binding}
    {types slots : Nat → BoundsTy} {ids : List Nat} {rows : Bindings}
    {Delta : List Constraint} {expr : Expr} {actual demand : BoundsTy}
    {source : ScopedBodyDerives types slots ids rows Delta (view.env raw) expr actual}
    (sub : SemanticSub Delta actual demand) (world : EnvSpecialization raw)
    (closed : BodyViewSpecialized view raw source world) :
    BodyViewSpecialized view raw (ScopedBodyDerives.subsumption source sub) world := by
  refine ⟨.subsumption closed.typing ?_⟩
  exact SchemeSpecialization.subtype world.types
    (CountSubstitution.subtype world.outer world.outerFinite sub)

end BodyViewSpecialized

#print axioms RawBodyView.env_append
#print axioms BodyViewSpecialized.app
#print axioms BodyViewSpecialized.subsumption

end FHM.Bounds.RecursiveHMUniform
