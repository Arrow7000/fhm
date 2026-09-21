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

/-- Extending a static specialization world with a monomorphic binder only
    adds a vacuous freshness obligation.  This is not a semantic environment
    constructor and therefore assumes no stability of the binder's runtime
    denotation. -/
def EnvSpecialization.consMono {raw : List Binding}
    (world : EnvSpecialization raw) (beta : BoundsTy) :
    EnvSpecialization (Binding.mono beta :: raw) where
  outer := world.outer
  types := world.types
  outerFinite := world.outerFinite
  countTarget := world.countTarget
  outerScope := world.outerScope
  typesLC := world.typesLC
  typeTarget := world.typeTarget
  typesScope := world.typesScope
  fresh := by
    intro binding member
    rcases List.mem_cons.mp member with head | tail
    · subst binding
      trivial
    · exact world.fresh binding tail
  typesSupported := world.typesSupported

def EnvSpecialization.prependMonos {raw : List Binding}
    (world : EnvSpecialization raw) :
    (demands : List BoundsTy) →
      EnvSpecialization (demands.map Binding.mono ++ raw)
  | [] => by simpa using world
  | demand :: rest => by
      simpa only [List.map_cons, List.cons_append] using
        (world.prependMonos rest).consMono demand

@[simp] theorem EnvSpecialization.prependMonos_outer {raw : List Binding}
    (world : EnvSpecialization raw) (demands : List BoundsTy) :
    (world.prependMonos demands).outer = world.outer := by
  induction demands with
  | nil => rfl
  | cons demand rest ih =>
      simpa only [EnvSpecialization.prependMonos, EnvSpecialization.consMono]
        using ih

@[simp] theorem EnvSpecialization.prependMonos_types {raw : List Binding}
    (world : EnvSpecialization raw) (demands : List BoundsTy) :
    (world.prependMonos demands).types = world.types := by
  induction demands with
  | nil => rfl
  | cons demand rest ih =>
      simpa only [EnvSpecialization.prependMonos, EnvSpecialization.consMono]
        using ih

@[simp] theorem RawBodyView.env_consMono (view : RawBodyView)
    (beta : BoundsTy) (raw : List Binding) :
    view.env (Binding.mono beta :: raw) = Binding.mono beta :: view.env raw := by
  cases view <;> rfl

@[simp] theorem RawBodyView.env_prependMonos (view : RawBodyView)
    (demands : List BoundsTy) (raw : List Binding) :
    view.env (demands.map Binding.mono ++ raw) =
      demands.map Binding.mono ++ view.env raw := by
  rw [RawBodyView.env_append]
  congr 1
  induction demands with
  | nil => rfl
  | cons demand rest ih =>
      simp only [List.map_cons, RawBodyView.env, RawBodyView.binding]
      cases view <;> exact congrArg (List.cons _) ih

theorem closeRecursiveEnv_prependMonos {raw : List Binding}
    (world : EnvSpecialization raw) (demands : List BoundsTy) :
    closeRecursiveEnv world.outer world.types
        (demands.map Binding.mono ++ raw) =
      (demands.map world.mapBounds).map Binding.mono ++
        closeRecursiveEnv world.outer world.types raw := by
  unfold closeRecursiveEnv
  simp only [List.map_append, List.map_map]
  congr 1

def ScopedHMAnnotation.ParamOK.specialize
    {types slots : Nat → BoundsTy} {ids : List Nat} {rows : Bindings}
    {Delta : List Constraint} {ann : Option Ty} {beta : BoundsTy}
    (h : ScopedHMAnnotation.ParamOK types slots ids rows Delta ann beta)
    {raw : List Binding} (world : EnvSpecialization raw) :
    ScopedHMAnnotation.ParamOK
      (fun i => world.mapBounds (types i))
      (fun i => world.mapBounds (slots i)) ids
      (CountAlgebra.compose world.outer rows)
      (Delta.map (constraint world.outer)) ann (world.mapBounds beta) := by
  cases ann with
  | none => trivial
  | some annotation => exact (h.counts world.outer world.outerFinite).types world.types

def ScopedHMAnnotation.BindingOK.specialize
    {types slots : Nat → BoundsTy} {ids : List Nat} {rows : Bindings}
    {Delta : List Constraint} {ann : Option PolyTy} {beta : BoundsTy}
    (h : ScopedHMAnnotation.BindingOK types slots ids rows Delta ann beta)
    {raw : List Binding} (world : EnvSpecialization raw) :
    ScopedHMAnnotation.BindingOK
      (fun i => world.mapBounds (types i))
      (fun i => world.mapBounds (slots i)) ids
      (CountAlgebra.compose world.outer rows)
      (Delta.map (constraint world.outer)) ann (world.mapBounds beta) := by
  cases ann with
  | none => trivial
  | some annotation =>
      exact ⟨h.1, (h.2.counts world.outer world.outerFinite).types world.types⟩

def ScopedHMAnnotation.Pinned.specialize
    {types slots : Nat → BoundsTy} {ids : List Nat} {rows : Bindings}
    {caller : List Nat} {Delta : List Constraint} {annotation : Ty} {actual : BoundsTy}
    (pinned : ScopedHMAnnotation.Pinned types slots ids rows caller Delta annotation actual)
    {raw : List Binding} (world : EnvSpecialization raw) :
    ScopedHMAnnotation.Pinned
      (fun i => world.mapBounds (types i))
      (fun i => world.mapBounds (slots i)) ids
      (CountAlgebra.compose world.outer rows)
      ((caller ++ world.countTarget) ++ world.typeTarget)
      (Delta.map (constraint world.outer)) annotation (world.mapBounds actual) :=
  (pinned.counts world.outer world.outerFinite world.countTarget world.outerScope).types
    world.types world.typeTarget world.typesScope

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

def lambda
    {view : RawBodyView} {raw : List Binding}
    {types slots : Nat → BoundsTy} {ids : List Nat} {rows : Bindings}
    {Delta : List Constraint} {ann : Option Ty} {body : Expr}
    {param result : BoundsTy}
    (annotation : ScopedHMAnnotation.ParamOK types slots ids rows Delta ann param)
    (bodyTyping : ScopedBodyDerives types slots ids rows Delta
      (view.env (Binding.mono param :: raw)) body result)
    (world : EnvSpecialization raw)
    (bodyClosed : BodyViewSpecialized view (Binding.mono param :: raw)
      bodyTyping (world.consMono param)) :
    BodyViewSpecialized view raw
      (ScopedBodyDerives.lambda annotation (by
        simpa only [RawBodyView.env_consMono] using bodyTyping)) world := by
  refine ⟨ScopedBodyDerives.lambda
    (ScopedHMAnnotation.ParamOK.specialize annotation world) ?_⟩
  simpa only [EnvSpecialization.consMono, EnvSpecialization.mapBounds,
    closeRecursiveEnv, List.map_cons, closeRecursiveBinding,
    RawBodyView.env_consMono] using bodyClosed.typing

def letMono
    {view : RawBodyView} {raw : List Binding}
    {types slots : Nat → BoundsTy} {ids : List Nat} {rows : Bindings}
    {Delta : List Constraint} {ann : Option PolyTy} {rhs body : Expr}
    {actual result : BoundsTy}
    (annotation : ScopedHMAnnotation.BindingOK types slots ids rows Delta ann actual)
    (rhsTyping : ScopedBodyDerives types slots ids rows Delta
      (view.env raw) rhs actual)
    (bodyTyping : ScopedBodyDerives types slots ids rows Delta
      (view.env (Binding.mono actual :: raw)) body result)
    (world : EnvSpecialization raw)
    (rhsClosed : BodyViewSpecialized view raw rhsTyping world)
    (bodyClosed : BodyViewSpecialized view (Binding.mono actual :: raw)
      bodyTyping (world.consMono actual)) :
    BodyViewSpecialized view raw
      (ScopedBodyDerives.letMono annotation rhsTyping (by
        simpa only [RawBodyView.env_consMono] using bodyTyping)) world := by
  refine ⟨ScopedBodyDerives.letMono
    (ScopedHMAnnotation.BindingOK.specialize annotation world)
    rhsClosed.typing ?_⟩
  simpa only [EnvSpecialization.consMono, EnvSpecialization.mapBounds,
    closeRecursiveEnv, List.map_cons, closeRecursiveBinding,
    RawBodyView.env_consMono] using bodyClosed.typing

def letRecMono
    {view : RawBodyView} {raw : List Binding}
    {types slots : Nat → BoundsTy} {ids : List Nat} {rows : Bindings}
    {Delta : List Constraint} {ann : Option PolyTy} {rhs body : Expr}
    {actual demand result : BoundsTy}
    (annotation : ScopedHMAnnotation.BindingOK types slots ids rows Delta ann demand)
    (rhsTyping : ScopedBodyDerives types slots ids rows Delta
      (view.env (Binding.mono demand :: raw)) rhs actual)
    (inclusion : SemanticSub Delta actual demand)
    (bodyTyping : ScopedBodyDerives types slots ids rows Delta
      (view.env (Binding.mono demand :: raw)) body result)
    (world : EnvSpecialization raw)
    (rhsClosed : BodyViewSpecialized view (Binding.mono demand :: raw)
      rhsTyping (world.consMono demand))
    (bodyClosed : BodyViewSpecialized view (Binding.mono demand :: raw)
      bodyTyping (world.consMono demand)) :
    BodyViewSpecialized view raw
      (ScopedBodyDerives.letRecMono annotation
        (by simpa only [RawBodyView.env_consMono] using rhsTyping) inclusion
        (by simpa only [RawBodyView.env_consMono] using bodyTyping)) world := by
  refine ⟨ScopedBodyDerives.letRecMono
    (ScopedHMAnnotation.BindingOK.specialize annotation world) ?_
    (SchemeSpecialization.subtype world.types
      (CountSubstitution.subtype world.outer world.outerFinite inclusion)) ?_⟩
  · simpa only [EnvSpecialization.consMono, EnvSpecialization.mapBounds,
      closeRecursiveEnv, List.map_cons, closeRecursiveBinding,
      RawBodyView.env_consMono] using rhsClosed.typing
  · simpa only [EnvSpecialization.consMono, EnvSpecialization.mapBounds,
      closeRecursiveEnv, List.map_cons, closeRecursiveBinding,
      RawBodyView.env_consMono] using bodyClosed.typing

def letPinned
    {view : RawBodyView} {raw : List Binding}
    {types slots : Nat → BoundsTy} {ids caller : List Nat} {rows : Bindings}
    {Delta : List Constraint} {annotation : PolyTy} {rhs body : Expr}
    {actual result : BoundsTy}
    (pinned : ScopedHMAnnotation.Pinned types slots ids rows caller Delta
      annotation.body actual)
    (mono : annotation.paramCount = 0)
    (rhsTyping : ScopedBodyDerives types slots ids rows Delta
      (view.env raw) rhs actual)
    (bodyTyping : ScopedBodyDerives types slots ids rows Delta
      (view.env (Binding.mono pinned.demand :: raw)) body result)
    (world : EnvSpecialization raw)
    (rhsClosed : BodyViewSpecialized view raw rhsTyping world)
    (bodyClosed : BodyViewSpecialized view (Binding.mono pinned.demand :: raw)
      bodyTyping (world.consMono pinned.demand)) :
    BodyViewSpecialized view raw
      (ScopedBodyDerives.letPinned pinned mono rhsTyping (by
        simpa only [RawBodyView.env_consMono] using bodyTyping)) world := by
  let closedPinned := ScopedHMAnnotation.Pinned.specialize pinned world
  refine ⟨ScopedBodyDerives.letPinned closedPinned mono rhsClosed.typing ?_⟩
  simpa only [closedPinned, ScopedHMAnnotation.Pinned.specialize,
    EnvSpecialization.consMono, EnvSpecialization.mapBounds,
    closeRecursiveEnv, List.map_cons, closeRecursiveBinding,
    RawBodyView.env_consMono] using bodyClosed.typing

def letRecInferredMono
    {raw : List Binding} {types slots : Nat → BoundsTy}
    {ids : List Nat} {rows : Bindings} {Delta : List Constraint}
    {rhs body : Expr} {actual result : BoundsTy}
    (rhsTyping : ScopedDerives types slots ids rows Delta
      (Binding.mono actual :: raw) rhs actual)
    (bodyTyping : ScopedBodyDerives types slots ids rows Delta
      (RawBodyView.ordinary.env (Binding.mono actual :: raw)) body result)
    (world : EnvSpecialization raw)
    (bodyClosed : BodyViewSpecialized .ordinary (Binding.mono actual :: raw)
      bodyTyping (world.consMono actual)) :
    BodyViewSpecialized .ordinary raw
      (by
        simpa only [RawBodyView.env_ordinary] using
          (ScopedBodyDerives.letRecInferredMono (outerEnv := raw) rhsTyping (by
            simpa only [RawBodyView.env_consMono, RawBodyView.env_ordinary]
              using bodyTyping) :
            ScopedBodyDerives types slots ids rows Delta
              (ordinaryBodyEnv raw) (.letRec [none] [rhs] body) result))
      world := by
  have rhsClosed := rhsTyping.closeRecursive world.outer world.types
    world.outerFinite world.countTarget world.outerScope world.typesLC
    world.typeTarget world.typesScope (world.consMono actual).fresh
  have targetRhs : ScopedDerives
      (fun i => world.mapBounds (types i)) (fun i => world.mapBounds (slots i)) ids
      (CountAlgebra.compose world.outer rows) (Delta.map (constraint world.outer))
      (Binding.mono (world.mapBounds actual) ::
        closeRecursiveEnv world.outer world.types raw)
      rhs (world.mapBounds actual) := by
    simpa only [EnvSpecialization.consMono, EnvSpecialization.mapBounds,
      closeRecursiveEnv, List.map_cons, closeRecursiveBinding] using rhsClosed
  have targetBody : ScopedBodyDerives
      (fun i => world.mapBounds (types i)) (fun i => world.mapBounds (slots i)) ids
      (CountAlgebra.compose world.outer rows) (Delta.map (constraint world.outer))
      (Binding.mono (world.mapBounds actual) ::
        ordinaryBodyEnv (closeRecursiveEnv world.outer world.types raw))
      body (world.mapBounds result) := by
    simpa only [EnvSpecialization.consMono, EnvSpecialization.mapBounds,
      closeRecursiveEnv, List.map_cons, closeRecursiveBinding,
      RawBodyView.env_consMono, RawBodyView.env_ordinary] using bodyClosed.typing
  refine ⟨?_⟩
  simpa only [RawBodyView.env_ordinary] using
    (ScopedBodyDerives.letRecInferredMono
      (outerEnv := closeRecursiveEnv world.outer world.types raw) targetRhs targetBody)

def letRecPinnedMono
    {raw : List Binding} {types slots : Nat → BoundsTy}
    {ids caller : List Nat} {rows : Bindings} {Delta : List Constraint}
    {annotation : PolyTy} {rhs body : Expr} {actual result : BoundsTy}
    (pinned : ScopedHMAnnotation.Pinned types slots ids rows caller Delta
      annotation.body actual)
    (mono : annotation.paramCount = 0)
    (rhsTyping : ScopedDerives types slots ids rows Delta
      (Binding.mono pinned.demand :: raw) rhs actual)
    (bodyTyping : ScopedBodyDerives types slots ids rows Delta
      (RawBodyView.ordinary.env (Binding.mono pinned.demand :: raw)) body result)
    (world : EnvSpecialization raw)
    (bodyClosed : BodyViewSpecialized .ordinary (Binding.mono pinned.demand :: raw)
      bodyTyping (world.consMono pinned.demand)) :
    BodyViewSpecialized .ordinary raw
      (by
        simpa only [RawBodyView.env_ordinary] using
          (ScopedBodyDerives.letRecPinnedMono (outerEnv := raw) pinned mono rhsTyping (by
            simpa only [RawBodyView.env_consMono, RawBodyView.env_ordinary]
              using bodyTyping) :
            ScopedBodyDerives types slots ids rows Delta
              (ordinaryBodyEnv raw) (.letRec [some annotation] [rhs] body) result))
      world := by
  let closedPinned := ScopedHMAnnotation.Pinned.specialize pinned world
  have rhsClosed := rhsTyping.closeRecursive world.outer world.types
    world.outerFinite world.countTarget world.outerScope world.typesLC
    world.typeTarget world.typesScope (world.consMono pinned.demand).fresh
  have targetRhs : ScopedDerives
      (fun i => world.mapBounds (types i)) (fun i => world.mapBounds (slots i)) ids
      (CountAlgebra.compose world.outer rows) (Delta.map (constraint world.outer))
      (Binding.mono closedPinned.demand ::
        closeRecursiveEnv world.outer world.types raw)
      rhs (world.mapBounds actual) := by
    simpa only [closedPinned, ScopedHMAnnotation.Pinned.specialize,
      EnvSpecialization.consMono, EnvSpecialization.mapBounds,
      closeRecursiveEnv, List.map_cons, closeRecursiveBinding] using rhsClosed
  have targetBody : ScopedBodyDerives
      (fun i => world.mapBounds (types i)) (fun i => world.mapBounds (slots i)) ids
      (CountAlgebra.compose world.outer rows) (Delta.map (constraint world.outer))
      (Binding.mono closedPinned.demand ::
        ordinaryBodyEnv (closeRecursiveEnv world.outer world.types raw))
      body (world.mapBounds result) := by
    simpa only [closedPinned, ScopedHMAnnotation.Pinned.specialize,
      EnvSpecialization.consMono, EnvSpecialization.mapBounds,
      closeRecursiveEnv, List.map_cons, closeRecursiveBinding,
      RawBodyView.env_consMono, RawBodyView.env_ordinary] using bodyClosed.typing
  refine ⟨?_⟩
  simpa only [RawBodyView.env_ordinary] using
    (ScopedBodyDerives.letRecPinnedMono
      (outerEnv := closeRecursiveEnv world.outer world.types raw)
      closedPinned mono targetRhs targetBody)

def letRecMonoGroup
    {view : RawBodyView} {raw : List Binding}
    {types slots : Nat → BoundsTy} {ids : List Nat} {rows : Bindings}
    {Delta : List Constraint} {annotations : List (Option PolyTy)}
    {rhss : List Expr} {body : Expr} {result : BoundsTy}
    (demands : List BoundsTy) {actuals : Nat → BoundsTy}
    (annotationCount : annotations.length = rhss.length)
    (demandCount : demands.length = rhss.length)
    (annotationsOK : ∀ i (inside : i < rhss.length),
      ScopedHMAnnotation.BindingOK types slots ids rows Delta
        (annotations[i]'(by omega)) (demands[i]'(by omega)))
    (rhssTyping : ∀ i (inside : i < rhss.length),
      ScopedBodyDerives types slots ids rows Delta
        (view.env (demands.map Binding.mono ++ raw))
        rhss[i] (actuals i))
    (inclusions : ∀ i (inside : i < rhss.length),
      SemanticSub Delta (actuals i) (demands[i]'(by omega)))
    (bodyTyping : ScopedBodyDerives types slots ids rows Delta
      (view.env (demands.map Binding.mono ++ raw)) body result)
    (world : EnvSpecialization raw)
    (rhssClosed : ∀ i (inside : i < rhss.length),
      BodyViewSpecialized view (demands.map Binding.mono ++ raw)
        (rhssTyping i inside) (world.prependMonos demands))
    (bodyClosed : BodyViewSpecialized view (demands.map Binding.mono ++ raw)
      bodyTyping (world.prependMonos demands)) :
    BodyViewSpecialized view raw
      (ScopedBodyDerives.letRecMonoGroup demands annotationCount demandCount
        annotationsOK
        (fun i inside => by
          simpa only [RawBodyView.env_prependMonos] using rhssTyping i inside)
        inclusions
        (by simpa only [RawBodyView.env_prependMonos] using bodyTyping)) world := by
  let mappedDemands := demands.map world.mapBounds
  have mappedDemandCount : mappedDemands.length = rhss.length := by
    simpa only [mappedDemands, List.length_map] using demandCount
  refine ⟨ScopedBodyDerives.letRecMonoGroup
    (actuals := fun i => world.mapBounds (actuals i))
    mappedDemands annotationCount mappedDemandCount ?_ ?_ ?_ ?_⟩
  · intro i inside
    simpa only [mappedDemands, List.getElem_map] using
      ScopedHMAnnotation.BindingOK.specialize (annotationsOK i inside) world
  · intro i inside
    simpa only [mappedDemands,
      EnvSpecialization.prependMonos_outer, EnvSpecialization.prependMonos_types,
      EnvSpecialization.mapBounds, closeRecursiveEnv_prependMonos,
      RawBodyView.env_prependMonos] using (rhssClosed i inside).typing
  · intro i inside
    simpa only [mappedDemands, List.getElem_map] using
      SchemeSpecialization.subtype world.types
        (CountSubstitution.subtype world.outer world.outerFinite (inclusions i inside))
  · simpa only [mappedDemands,
      EnvSpecialization.prependMonos_outer, EnvSpecialization.prependMonos_types,
      EnvSpecialization.mapBounds, closeRecursiveEnv_prependMonos,
      RawBodyView.env_prependMonos] using bodyClosed.typing

def literal (view : RawBodyView) (raw : List Binding) (world : EnvSpecialization raw)
    (p : PrimLitExpr) :
    BodyViewSpecialized view raw
      (@ScopedBodyDerives.literal types slots ids rows Delta (view.env raw) p) world := by
  refine ⟨?_⟩
  cases p <;> exact .literal

def nil (view : RawBodyView) (raw : List Binding) (world : EnvSpecialization raw)
    (elem : BoundsTy) :
    BodyViewSpecialized view raw
      (@ScopedBodyDerives.nil types slots ids rows Delta (view.env raw) elem) world := by
  exact ⟨ScopedBodyDerives.nil⟩

def boolCtor (view : RawBodyView) (raw : List Binding) (world : EnvSpecialization raw)
    {name : CtorName} (isCtor : BoolBranches.IsCtor name) :
    BodyViewSpecialized view raw
      (@ScopedBodyDerives.boolCtor types slots ids rows Delta (view.env raw) name isCtor)
      world := by
  exact ⟨ScopedBodyDerives.boolCtor isCtor⟩

def ctor (view : RawBodyView) (raw : List Binding) (world : EnvSpecialization raw)
    {name : CtorName} {beta : BoundsTy} (notNil : name ≠ nilCtorName) :
    BodyViewSpecialized view raw
      (@ScopedBodyDerives.ctor types slots ids rows Delta (view.env raw) name beta notNil)
      world := by
  exact ⟨ScopedBodyDerives.ctor notNil⟩

def primBinOp (view : RawBodyView) (raw : List Binding) (world : EnvSpecialization raw)
    (op : PrimBinOp) :
    BodyViewSpecialized view raw
      (@ScopedBodyDerives.primBinOp types slots ids rows Delta (view.env raw) op) world := by
  refine ⟨?_⟩
  cases op <;> exact .primBinOp

def cons
    {view : RawBodyView} {raw : List Binding}
    {types slots : Nat → BoundsTy} {ids : List Nat} {rows : Bindings}
    {Delta : List Constraint} {head tail : Expr}
    {headTy elem : BoundsTy} {lo hi : Count}
    {headTyping : ScopedBodyDerives types slots ids rows Delta
      (view.env raw) head headTy}
    {tailTyping : ScopedBodyDerives types slots ids rows Delta
      (view.env raw) tail (.list lo hi elem)}
    (inclusion : SemanticSub Delta headTy elem)
    (world : EnvSpecialization raw)
    (headClosed : BodyViewSpecialized view raw headTyping world)
    (tailClosed : BodyViewSpecialized view raw tailTyping world) :
    BodyViewSpecialized view raw
      (ScopedBodyDerives.cons headTyping tailTyping inclusion) world := by
  refine ⟨ScopedBodyDerives.cons headClosed.typing tailClosed.typing ?_⟩
  exact SchemeSpecialization.subtype world.types
    (CountSubstitution.subtype world.outer world.outerFinite inclusion)

def consPartial
    {view : RawBodyView} {raw : List Binding}
    {types slots : Nat → BoundsTy} {ids : List Nat} {rows : Bindings}
    {Delta : List Constraint} {head : Expr} {headTy : BoundsTy}
    {headTyping : ScopedBodyDerives types slots ids rows Delta
      (view.env raw) head headTy}
    (world : EnvSpecialization raw)
    (headClosed : BodyViewSpecialized view raw headTyping world) :
    BodyViewSpecialized view raw (ScopedBodyDerives.consPartial headTyping) world := by
  exact ⟨ScopedBodyDerives.consPartial headClosed.typing⟩

def pair
    {view : RawBodyView} {raw : List Binding}
    {types slots : Nat → BoundsTy} {ids : List Nat} {rows : Bindings}
    {Delta : List Constraint} {left right : Expr} {leftTy rightTy : BoundsTy}
    {leftTyping : ScopedBodyDerives types slots ids rows Delta
      (view.env raw) left leftTy}
    {rightTyping : ScopedBodyDerives types slots ids rows Delta
      (view.env raw) right rightTy}
    (world : EnvSpecialization raw)
    (leftClosed : BodyViewSpecialized view raw leftTyping world)
    (rightClosed : BodyViewSpecialized view raw rightTyping world) :
    BodyViewSpecialized view raw
      (ScopedBodyDerives.pair leftTyping rightTyping) world := by
  exact ⟨ScopedBodyDerives.pair leftClosed.typing rightClosed.typing⟩

def pairPartial
    {view : RawBodyView} {raw : List Binding}
    {types slots : Nat → BoundsTy} {ids : List Nat} {rows : Bindings}
    {Delta : List Constraint} {left : Expr} {leftTy rightTy : BoundsTy}
    {leftTyping : ScopedBodyDerives types slots ids rows Delta
      (view.env raw) left leftTy}
    (world : EnvSpecialization raw)
    (leftClosed : BodyViewSpecialized view raw leftTyping world) :
    BodyViewSpecialized view raw
      (ScopedBodyDerives.pairPartial (rightTy := rightTy) leftTyping) world := by
  exact ⟨ScopedBodyDerives.pairPartial leftClosed.typing⟩

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
#print axioms BodyViewSpecialized.lambda
#print axioms BodyViewSpecialized.letMono
#print axioms BodyViewSpecialized.letRecMono
#print axioms BodyViewSpecialized.letPinned
#print axioms BodyViewSpecialized.letRecInferredMono
#print axioms BodyViewSpecialized.letRecPinnedMono
#print axioms BodyViewSpecialized.letRecMonoGroup
#print axioms BodyViewSpecialized.nil
#print axioms BodyViewSpecialized.boolCtor
#print axioms BodyViewSpecialized.ctor
#print axioms BodyViewSpecialized.cons
#print axioms BodyViewSpecialized.consPartial
#print axioms BodyViewSpecialized.pair
#print axioms BodyViewSpecialized.pairPartial
#print axioms BodyViewSpecialized.app
#print axioms BodyViewSpecialized.subsumption

end FHM.Bounds.RecursiveHMUniform
