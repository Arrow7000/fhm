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

def RawBodyView.binding : RawBodyView → Binding → BodyBinding
  | .fixed, binding => binding
  | .ordinary, .mono beta => .mono beta
  | .ordinary, .recursive contract => .exported contract.template
  | .ordinary, .recursiveClosure contract => .recursiveClosure contract
  | .ordinary, .exported scheme => .exported scheme
  | .ordinary, .closure scheme countCaptures typeCaptures =>
      .closure scheme countCaptures typeCaptures

/-- Public, provenance-preserving presentation of the two body views.  Defining
    the pointwise map here avoids having to invert the private implementation
    function behind `ordinaryBodyEnv` in variable cases. -/
def RawBodyView.env (view : RawBodyView) (raw : List Binding) : List BodyBinding :=
  raw.map view.binding

@[simp] theorem RawBodyView.env_fixed (raw : List Binding) :
    RawBodyView.fixed.env raw = fixedBodyEnv raw := by
  induction raw with
  | nil => rfl
  | cons binding rest ih =>
      cases binding <;>
        simp only [RawBodyView.env, List.map_cons, RawBodyView.binding,
          fixedBodyEnv] at ih ⊢ <;>
        exact congrArg (List.cons _) ih

@[simp] theorem RawBodyView.env_ordinary (raw : List Binding) :
    RawBodyView.ordinary.env raw = ordinaryBodyEnv raw := by
  induction raw with
  | nil => rfl
  | cons binding rest ih =>
      cases binding <;>
        simp only [RawBodyView.env, List.map_cons, RawBodyView.binding,
          ordinaryBodyEnv] at ih ⊢ <;>
        exact congrArg (List.cons _) ih

theorem RawBodyView.env_length (view : RawBodyView) (raw : List Binding) :
    (view.env raw).length = raw.length := by
  simp [RawBodyView.env]

theorem RawBodyView.env_append (view : RawBodyView) (left right : List Binding) :
    view.env (left ++ right) = view.env left ++ view.env right := by
  simp [RawBodyView.env]

/-- The bounds transformation shared by the closed recursive judgment and its
    fixed/ordinary body views. -/
def EnvSpecialization.mapBounds {raw : List Binding}
    (world : EnvSpecialization raw) (beta : BoundsTy) : BoundsTy :=
  mapFree world.types (bounds world.outer beta)

theorem RawBodyView.lookupMono {view : RawBodyView} {raw : List Binding}
    {i : Nat} {beta : BoundsTy}
    (lookup : raw[i]? = some (Binding.mono beta)) :
    (view.env raw)[i]? = some (Binding.mono beta) := by
  have mapped := congrArg (Option.map view.binding) lookup
  cases view <;> simpa [RawBodyView.env, List.getElem?_map, RawBodyView.binding] using mapped

theorem RawBodyView.lookupRecursiveFixed {raw : List Binding}
    {i : Nat} {contract : Contract}
    (lookup : raw[i]? = some (Binding.recursive contract)) :
    (RawBodyView.fixed.env raw)[i]? = some (Binding.recursive contract) := by
  have mapped := congrArg (Option.map RawBodyView.fixed.binding) lookup
  simpa [RawBodyView.env, List.getElem?_map, RawBodyView.binding] using mapped

theorem RawBodyView.lookupRecursiveOrdinary {raw : List Binding}
    {i : Nat} {contract : Contract}
    (lookup : raw[i]? = some (Binding.recursive contract)) :
    (RawBodyView.ordinary.env raw)[i]? = some (Binding.exported contract.template) := by
  have mapped := congrArg (Option.map RawBodyView.ordinary.binding) lookup
  simpa [RawBodyView.env, List.getElem?_map, RawBodyView.binding] using mapped

theorem RawBodyView.lookupExported {view : RawBodyView} {raw : List Binding}
    {i : Nat} {scheme : HMCountScheme.Scheme}
    (lookup : raw[i]? = some (Binding.exported scheme)) :
    (view.env raw)[i]? = some (Binding.exported scheme) := by
  have mapped := congrArg (Option.map view.binding) lookup
  cases view <;> simpa [RawBodyView.env, List.getElem?_map, RawBodyView.binding] using mapped

theorem RawBodyView.lookupClosure {view : RawBodyView} {raw : List Binding}
    {i : Nat} {scheme : HMCountScheme.Scheme}
    {countCaptures : List Count} {typeCaptures : List BoundsTy}
    (lookup : raw[i]? = some (Binding.closure scheme countCaptures typeCaptures)) :
    (view.env raw)[i]? = some (Binding.closure scheme countCaptures typeCaptures) := by
  have mapped := congrArg (Option.map view.binding) lookup
  cases view <;> simpa [RawBodyView.env, List.getElem?_map, RawBodyView.binding] using mapped

theorem RawBodyView.lookupClosedMono
    {view : RawBodyView} {raw : List Binding} {i : Nat} {beta : BoundsTy}
    (world : EnvSpecialization raw) (lookup : raw[i]? = some (Binding.mono beta)) :
    (view.env (closeRecursiveEnv world.outer world.types raw))[i]? =
      some (Binding.mono (world.mapBounds beta)) := by
  have mapped := congrArg
    (Option.map (fun binding => view.binding
      (closeRecursiveBinding world.outer world.types binding))) lookup
  cases view <;>
    simpa [RawBodyView.env, closeRecursiveEnv, List.getElem?_map,
      RawBodyView.binding, closeRecursiveBinding, EnvSpecialization.mapBounds] using mapped

theorem RawBodyView.lookupClosedRecursive
    {view : RawBodyView} {raw : List Binding} {i : Nat} {contract : Contract}
    (world : EnvSpecialization raw)
    (lookup : raw[i]? = some (Binding.recursive contract)) :
    (view.env (closeRecursiveEnv world.outer world.types raw))[i]? = some
      (Binding.recursiveClosure
        (RecursiveHMContract.Closed.ofFixed contract.fixed world.outer world.types)) := by
  have mapped := congrArg
    (Option.map (fun binding => view.binding
      (closeRecursiveBinding world.outer world.types binding))) lookup
  cases view <;>
    simpa [RawBodyView.env, closeRecursiveEnv, List.getElem?_map,
      RawBodyView.binding, closeRecursiveBinding] using mapped

theorem RawBodyView.lookupClosedExported
    {view : RawBodyView} {raw : List Binding} {i : Nat} {scheme : HMCountScheme.Scheme}
    (world : EnvSpecialization raw)
    (lookup : raw[i]? = some (Binding.exported scheme)) :
    (view.env (closeRecursiveEnv world.outer world.types raw))[i]? =
      some (Binding.exported scheme) := by
  have mapped := congrArg
    (Option.map (fun binding => view.binding
      (closeRecursiveBinding world.outer world.types binding))) lookup
  cases view <;>
    simpa [RawBodyView.env, closeRecursiveEnv, List.getElem?_map,
      RawBodyView.binding, closeRecursiveBinding] using mapped

theorem RawBodyView.lookupClosedClosure
    {view : RawBodyView} {raw : List Binding} {i : Nat} {scheme : HMCountScheme.Scheme}
    {countCaptures : List Count} {typeCaptures : List BoundsTy}
    (world : EnvSpecialization raw)
    (lookup : raw[i]? = some (Binding.closure scheme countCaptures typeCaptures)) :
    (view.env (closeRecursiveEnv world.outer world.types raw))[i]? = some
      (Binding.closure scheme
        (countCaptures.map (count world.outer))
        ((typeCaptures.map (bounds world.outer)).map (mapFree world.types))) := by
  have mapped := congrArg
    (Option.map (fun binding => view.binding
      (closeRecursiveBinding world.outer world.types binding))) lookup
  cases view <;>
    simpa [RawBodyView.env, closeRecursiveEnv, List.getElem?_map,
      RawBodyView.binding, closeRecursiveBinding] using mapped

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

def varMono
    {view : RawBodyView} {raw : List Binding}
    {types slots : Nat → BoundsTy} {ids : List Nat} {rows : Bindings}
    {Delta : List Constraint} {i : Nat} {beta : BoundsTy}
    (lookup : raw[i]? = some (Binding.mono beta)) (world : EnvSpecialization raw) :
    BodyViewSpecialized view raw
      (ScopedBodyDerives.varMono (RawBodyView.lookupMono lookup) :
        ScopedBodyDerives types slots ids rows Delta (view.env raw) (.var i) beta)
      world := by
  exact ⟨.varMono (RawBodyView.lookupClosedMono world lookup)⟩

/-- A fixed in-SCC recursive assumption becomes its capture-closed recursive
    contract under the combined count/HM world. -/
def varRecursiveFixed
    {raw : List Binding} {types slots : Nat → BoundsTy} {ids : List Nat}
    {rows : Bindings} {Delta : List Constraint} {i : Nat} {contract : Contract}
    {caller : List Nat}
    (lookup : raw[i]? = some (Binding.recursive contract))
    (used : RecursiveHMContract.Use contract.fixed Delta contract.hm caller)
    (world : EnvSpecialization raw) :
    BodyViewSpecialized .fixed raw
      (ScopedBodyDerives.varRecursive (RawBodyView.lookupRecursiveFixed lookup) used :
        ScopedBodyDerives types slots ids rows Delta (RawBodyView.fixed.env raw)
          (.var i) used.bounds)
      world := by
  let closedUse := RecursiveHMContract.Closed.Use.transport used world.outer
    world.outerFinite world.countTarget world.outerScope world.types world.typesLC
    world.typeTarget world.typesScope
  have boundsEq : closedUse.bounds = world.mapBounds used.bounds := by
    exact RecursiveHMContract.Closed.Use.transport_bounds used world.outer
      world.outerFinite world.countTarget world.outerScope world.types world.typesLC
      world.typeTarget world.typesScope
  refine ⟨?_⟩
  simpa only [boundsEq] using
    (ScopedBodyDerives.varRecursiveClosure
      (RawBodyView.lookupClosedRecursive (view := .fixed) world lookup) closedUse)

/-- The ordinary view exported by a raw recursive contract retains that raw
    provenance, so closing it produces the same fixed recursive closure rather
    than treating it as an independently generalized lexical export. -/
def varRecursiveOrdinary
    {raw : List Binding} {types slots : Nat → BoundsTy} {ids : List Nat}
    {rows : Bindings} {Delta : List Constraint} {i : Nat} {contract : Contract}
    {caller : List Nat}
    (lookup : raw[i]? = some (Binding.recursive contract))
    (used : RecursiveHMContract.Use contract.fixed Delta contract.hm caller)
    (world : EnvSpecialization raw) :
    BodyViewSpecialized .ordinary raw
      (ScopedBodyDerives.varExported (RawBodyView.lookupRecursiveOrdinary lookup) used.external :
        ScopedBodyDerives types slots ids rows Delta (RawBodyView.ordinary.env raw)
          (.var i) used.bounds)
      world := by
  let closedUse := RecursiveHMContract.Closed.Use.transport used world.outer
    world.outerFinite world.countTarget world.outerScope world.types world.typesLC
    world.typeTarget world.typesScope
  have boundsEq : closedUse.bounds = world.mapBounds used.bounds := by
    exact RecursiveHMContract.Closed.Use.transport_bounds used world.outer
      world.outerFinite world.countTarget world.outerScope world.types world.typesLC
      world.typeTarget world.typesScope
  refine ⟨?_⟩
  simpa only [boundsEq] using
    (ScopedBodyDerives.varRecursiveClosure
      (RawBodyView.lookupClosedRecursive (view := .ordinary) world lookup) closedUse)

/-- An already exported raw scheme remains exported after recursive closing.
    The exact transported use is deliberately an argument: deriving it needs
    the export's capture-freshness facts, not merely the raw lookup. -/
def varExported
    {view : RawBodyView} {raw : List Binding}
    {types slots : Nat → BoundsTy} {ids : List Nat} {rows : Bindings}
    {Delta : List Constraint} {i : Nat} {scheme : HMCountScheme.Scheme}
    {found closedFound : Ty} {caller closedCaller : List Nat}
    (lookup : raw[i]? = some (Binding.exported scheme))
    (used : HMCountScheme.Use scheme Delta found caller)
    (world : EnvSpecialization raw)
    (closedUsed : HMCountScheme.Use scheme
      (Delta.map (constraint world.outer)) closedFound closedCaller)
    (boundsEq : closedUsed.bounds = world.mapBounds used.bounds) :
    BodyViewSpecialized view raw
      (ScopedBodyDerives.varExported (RawBodyView.lookupExported lookup) used :
        ScopedBodyDerives types slots ids rows Delta (view.env raw) (.var i) used.bounds)
      world := by
  refine ⟨?_⟩
  simpa only [boundsEq] using
    (ScopedBodyDerives.varExported
      (RawBodyView.lookupClosedExported world lookup) closedUsed)

/-- A lexical closure keeps its source scheme while both stored capture
    vectors are mapped.  Capture agreement for the mapped use is explicit at
    this boundary, so this constructor does not assume an unproved stability
    property for arbitrary environments. -/
def varClosure
    {view : RawBodyView} {raw : List Binding}
    {types slots : Nat → BoundsTy} {ids : List Nat} {rows : Bindings}
    {Delta : List Constraint} {i : Nat} {scheme : HMCountScheme.Scheme}
    {countCaptures : List Count} {typeCaptures : List BoundsTy}
    {found closedFound : Ty} {caller closedCaller : List Nat}
    (lookup : raw[i]? = some (Binding.closure scheme countCaptures typeCaptures))
    (used : HMCountScheme.Use (HMCountSchemeClosure.close scheme) Delta found caller)
    (captures : HMCountSchemeClosure.HasCaptureArguments scheme
      countCaptures typeCaptures used)
    (world : EnvSpecialization raw)
    (closedUsed : HMCountScheme.Use (HMCountSchemeClosure.close scheme)
      (Delta.map (constraint world.outer)) closedFound closedCaller)
    (closedCaptures : HMCountSchemeClosure.HasCaptureArguments scheme
      (countCaptures.map (count world.outer))
      ((typeCaptures.map (bounds world.outer)).map (mapFree world.types)) closedUsed)
    (boundsEq : closedUsed.bounds = world.mapBounds used.bounds) :
    BodyViewSpecialized view raw
      (ScopedBodyDerives.varClosure (RawBodyView.lookupClosure lookup) used captures :
        ScopedBodyDerives types slots ids rows Delta (view.env raw) (.var i) used.bounds)
      world := by
  refine ⟨?_⟩
  simpa only [boundsEq] using
    (ScopedBodyDerives.varClosure
      (RawBodyView.lookupClosedClosure world lookup) closedUsed closedCaptures)

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
#print axioms BodyViewSpecialized.varMono
#print axioms BodyViewSpecialized.varRecursiveFixed
#print axioms BodyViewSpecialized.varRecursiveOrdinary
#print axioms BodyViewSpecialized.varExported
#print axioms BodyViewSpecialized.varClosure
#print axioms BodyViewSpecialized.app
#print axioms BodyViewSpecialized.subsumption

end FHM.Bounds.RecursiveHMUniform
