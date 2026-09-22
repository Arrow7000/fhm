import FHM.Bounds.RecursiveHMPointwiseClosedExport
import FHM.Bounds.RecursiveHMBodyViewTransport

/-! # Pointwise fundamental theorem for recursively closed body worlds

The specializable fundamental theorem is proved directly, one closed world at
a time. Its invariant consumes any current realization of the closed body
view and produces `TermAt`; it does not require one globally transported
target derivation. Thus generalized recursion can use the based runtime
realizer without reconstructing a target checked group artifact.
-/

namespace FHM.Bounds.RecursiveHMClosedExit

open RecursiveHMJudgement SchemeSpecialization CountSubstitution ScopedScheme
open RecursiveHMUniform

namespace PointwiseFundamental

/-- Semantic soundness of one source readiness proof in one closed world.
    Quantifying over the current `EnvAt` permits descent beneath dynamic
    lambda, let, and pattern binders. -/
structure Pointwise
    {view : RawBodyView} {raw : List Binding}
    {types slots : Nat → BoundsTy} {ids : List Nat} {rows : Bindings}
    {Delta : List Constraint} {expr : Expr} {beta : BoundsTy}
    {source : ScopedBodyDerives types slots ids rows Delta (view.env raw) expr beta}
    (ready : RecursiveHMUniform.BodyDerives.RuntimeReady source)
    (world : EnvSpecialization raw) : Prop where
  coherent : RawBodyView.Coherent view raw
  run : ∀ (bound free : Runtime.TypeEnv) (sigma : Assign),
    Runtime.TypeEnv.Downward bound → Runtime.TypeEnv.Downward free →
    ∀ budget,
    (∀ p ∈ Delta.map (constraint world.outer), p.Holds sigma) →
    (current : BodyEnvAt bound free sigma budget
      (view.env (closeRecursiveEnv world.outer world.types raw))) →
    Runtime.TermAt bound free sigma budget (world.mapBounds beta)
      (expr.substN 0 current.terms)

namespace Pointwise

theorem termAt
    {view : RawBodyView} {raw : List Binding}
    {types slots : Nat → BoundsTy} {ids : List Nat} {rows : Bindings}
    {Delta : List Constraint} {expr : Expr} {beta : BoundsTy}
    {source : ScopedBodyDerives types slots ids rows Delta (view.env raw) expr beta}
    {ready : RecursiveHMUniform.BodyDerives.RuntimeReady source}
    {world : EnvSpecialization raw}
    (safe : Pointwise ready world)
    (bound free : Runtime.TypeEnv) (sigma : Assign)
    (hb : Runtime.TypeEnv.Downward bound) (hf : Runtime.TypeEnv.Downward free)
    (budget : Nat)
    (premises : ∀ p ∈ Delta.map (constraint world.outer), p.Holds sigma)
    (current : BodyEnvAt bound free sigma budget
      (view.env (closeRecursiveEnv world.outer world.types raw))) :
    Runtime.TermAt bound free sigma budget (world.mapBounds beta)
      (expr.substN 0 current.terms) :=
  safe.run bound free sigma hb hf budget premises current

private theorem supported_map {raw : List Binding} (world : EnvSpecialization raw)
    {beta : BoundsTy} (supported : Runtime.Supported beta) :
    Runtime.Supported (world.mapBounds beta) :=
  (supported.counts world.outer).types world.types world.typesSupported

private theorem closes_source
    {view : RawBodyView} {raw : List Binding}
    {types slots : Nat → BoundsTy} {ids : List Nat} {rows : Bindings}
    {Delta : List Constraint} {expr : Expr} {beta : BoundsTy}
    (source : ScopedBodyDerives types slots ids rows Delta (view.env raw) expr beta)
    {world : EnvSpecialization raw}
    {bound free : Runtime.TypeEnv} {sigma : Assign} {budget : Nat}
    (current : BodyEnvAt bound free sigma budget
      (view.env (closeRecursiveEnv world.outer world.types raw))) :
    (expr.substN 0 current.terms).varsBelow 0 = true := by
  apply Runtime.closing_scoped current.terms current.closed expr 0
  have sameLength : (view.env (closeRecursiveEnv world.outer world.types raw)).length =
      (view.env raw).length := by
    simp only [RawBodyView.env, closeRecursiveEnv, List.length_map]
  simpa only [Nat.zero_add, current.arity, sameLength] using source.varsBelow

private theorem ordinary_closed_group_body_env
    {output metadata path captures premises bodyTypes raw}
    (group : GeneralizedGroup output metadata path captures premises bodyTypes raw)
    (rows : Bindings) (types : Nat → BoundsTy) :
    RawBodyView.ordinary.env (group.closedExports rows types ++ raw) =
      group.closedExports rows types ++ ordinaryBodyEnv raw := by
  rw [RawBodyView.env_append, RawBodyView.env_ordinary,
    RawBodyView.env_ordinary, GeneralizedGroup.ordinaryBodyEnv_closedExports]

private theorem fixed_closed_group_body_env
    {output metadata path captures premises bodyTypes raw}
    (group : GeneralizedGroup output metadata path captures premises bodyTypes raw)
    (rows : Bindings) (types : Nat → BoundsTy) :
    RawBodyView.fixed.env (group.closedExports rows types ++ raw) =
      group.closedExports rows types ++ fixedBodyEnv raw := by
  simp only [RawBodyView.env_fixed, fixedBodyEnv]

private def ordinary_closed_group_body_typing
    {raw : List Binding} {types slots : Nat → BoundsTy}
    {ids : List Nat} {rows : Bindings} {Delta : List Constraint} {result : BoundsTy}
    {output : Expr} {metadata : Scope.Metadata} {path : CorePath}
    {captures : List Nat} {premises : List Constraint} {bodyTypes : List Ty}
    (group : GeneralizedGroup output metadata path captures premises bodyTypes raw)
    {bodyTyping : ScopedBodyDerives types slots ids rows Delta
      (group.closedExports rows types ++ ordinaryBodyEnv raw) group.body result} :
    ScopedBodyDerives types slots ids rows Delta
      (RawBodyView.ordinary.env (group.closedExports rows types ++ raw))
      group.body result :=
  (ordinary_closed_group_body_env group rows types).symm ▸ bodyTyping

private def ordinary_closed_group_body_ready
    {raw : List Binding} {types slots : Nat → BoundsTy}
    {ids : List Nat} {rows : Bindings} {Delta : List Constraint} {result : BoundsTy}
    {output : Expr} {metadata : Scope.Metadata} {path : CorePath}
    {captures : List Nat} {premises : List Constraint} {bodyTypes : List Ty}
    (group : GeneralizedGroup output metadata path captures premises bodyTypes raw)
    {bodyTyping : ScopedBodyDerives types slots ids rows Delta
      (group.closedExports rows types ++ ordinaryBodyEnv raw) group.body result}
    (bodyReady : RecursiveHMUniform.BodyDerives.RuntimeReady bodyTyping) :
    RecursiveHMUniform.BodyDerives.RuntimeReady
      (ordinary_closed_group_body_typing group (bodyTyping := bodyTyping)) := by
  exact RecursiveHMUniform.BodyDerives.RuntimeReady.castEnv
    (ordinary_closed_group_body_env group rows types).symm bodyReady

private def fixed_closed_group_body_typing
    {raw : List Binding} {types slots : Nat → BoundsTy}
    {ids : List Nat} {rows : Bindings} {Delta : List Constraint} {result : BoundsTy}
    {output : Expr} {metadata : Scope.Metadata} {path : CorePath}
    {captures : List Nat} {premises : List Constraint} {bodyTypes : List Ty}
    (group : GeneralizedGroup output metadata path captures premises bodyTypes raw)
    {bodyTyping : ScopedBodyDerives types slots ids rows Delta
      (group.closedExports rows types ++ fixedBodyEnv raw) group.body result} :
    ScopedBodyDerives types slots ids rows Delta
      (RawBodyView.fixed.env (group.closedExports rows types ++ raw))
      group.body result :=
  (fixed_closed_group_body_env group rows types).symm ▸ bodyTyping

private def fixed_closed_group_body_ready
    {raw : List Binding} {types slots : Nat → BoundsTy}
    {ids : List Nat} {rows : Bindings} {Delta : List Constraint} {result : BoundsTy}
    {output : Expr} {metadata : Scope.Metadata} {path : CorePath}
    {captures : List Nat} {premises : List Constraint} {bodyTypes : List Ty}
    (group : GeneralizedGroup output metadata path captures premises bodyTypes raw)
    {bodyTyping : ScopedBodyDerives types slots ids rows Delta
      (group.closedExports rows types ++ fixedBodyEnv raw) group.body result}
    (bodyReady : RecursiveHMUniform.BodyDerives.RuntimeReady bodyTyping) :
    RecursiveHMUniform.BodyDerives.RuntimeReady
      (fixed_closed_group_body_typing group (bodyTyping := bodyTyping)) := by
  exact RecursiveHMUniform.BodyDerives.RuntimeReady.castEnv
    (fixed_closed_group_body_env group rows types).symm bodyReady

private def letRecClosed_typing_view
    {raw : List Binding} {types slots : Nat → BoundsTy}
    {ids : List Nat} {rows : Bindings} {Delta : List Constraint} {result : BoundsTy}
    {output : Expr} {metadata : Scope.Metadata} {path : CorePath}
    {captures : List Nat} {premises : List Constraint} {bodyTypes : List Ty}
    (group : GeneralizedGroup output metadata path captures premises bodyTypes raw)
    {bodyTyping : ScopedBodyDerives types slots ids rows Delta
      (group.closedExports rows types ++ ordinaryBodyEnv raw) group.body result} :
    ScopedBodyDerives types slots ids rows Delta (RawBodyView.ordinary.env raw)
      (.letRec group.annotations group.rhss group.body) result :=
  (RawBodyView.env_ordinary raw).symm ▸ ScopedBodyDerives.letRecClosed group bodyTyping

private def letRecClosed_ready_view
    {raw : List Binding} {types slots : Nat → BoundsTy}
    {ids : List Nat} {rows : Bindings} {Delta : List Constraint} {result : BoundsTy}
    {output : Expr} {metadata : Scope.Metadata} {path : CorePath}
    {captures : List Nat} {premises : List Constraint} {bodyTypes : List Ty}
    (group : GeneralizedGroup output metadata path captures premises bodyTypes raw)
    (groupReady : group.ClosedRuntimeReady rows types)
    {bodyTyping : ScopedBodyDerives types slots ids rows Delta
      (group.closedExports rows types ++ ordinaryBodyEnv raw) group.body result}
    (bodyReady : RecursiveHMUniform.BodyDerives.RuntimeReady bodyTyping) :
    RecursiveHMUniform.BodyDerives.RuntimeReady
      (letRecClosed_typing_view group (bodyTyping := bodyTyping)) := by
  exact RecursiveHMUniform.BodyDerives.RuntimeReady.castEnv
    (RawBodyView.env_ordinary raw).symm
    (RecursiveHMUniform.BodyDerives.RuntimeReady.letRecClosed group groupReady bodyReady)

private def letRecFixedClosed_typing_view
    {raw : List Binding} {types slots : Nat → BoundsTy}
    {ids : List Nat} {rows : Bindings} {Delta : List Constraint} {result : BoundsTy}
    {output : Expr} {metadata : Scope.Metadata} {path : CorePath}
    {captures : List Nat} {premises : List Constraint} {bodyTypes : List Ty}
    (group : GeneralizedGroup output metadata path captures premises bodyTypes raw)
    {bodyTyping : ScopedBodyDerives types slots ids rows Delta
      (group.closedExports rows types ++ fixedBodyEnv raw) group.body result} :
    ScopedBodyDerives types slots ids rows Delta (RawBodyView.fixed.env raw)
      (.letRec group.annotations group.rhss group.body) result :=
  (RawBodyView.env_fixed raw).symm ▸ ScopedBodyDerives.letRecFixedClosed group bodyTyping

private def letRecFixedClosed_ready_view
    {raw : List Binding} {types slots : Nat → BoundsTy}
    {ids : List Nat} {rows : Bindings} {Delta : List Constraint} {result : BoundsTy}
    {output : Expr} {metadata : Scope.Metadata} {path : CorePath}
    {captures : List Nat} {premises : List Constraint} {bodyTypes : List Ty}
    (group : GeneralizedGroup output metadata path captures premises bodyTypes raw)
    (groupReady : group.ClosedRuntimeReady rows types)
    {bodyTyping : ScopedBodyDerives types slots ids rows Delta
      (group.closedExports rows types ++ fixedBodyEnv raw) group.body result}
    (bodyReady : RecursiveHMUniform.BodyDerives.RuntimeReady bodyTyping) :
    RecursiveHMUniform.BodyDerives.RuntimeReady
      (letRecFixedClosed_typing_view group (bodyTyping := bodyTyping)) := by
  exact RecursiveHMUniform.BodyDerives.RuntimeReady.castEnv
    (RawBodyView.env_fixed raw).symm
    (RecursiveHMUniform.BodyDerives.RuntimeReady.letRecFixedClosed group groupReady bodyReady)

private theorem scoped_termAt
    {view : RawBodyView} {raw : List Binding}
    {types slots : Nat → BoundsTy} {ids : List Nat} {rows : Bindings}
    {Delta : List Constraint} {expr : Expr} {beta : BoundsTy}
    {source : ScopedDerives types slots ids rows Delta raw expr beta}
    (ready : RecursiveHMJudgement.ScopedDerives.RuntimeReady source)
    (world : EnvSpecialization raw)
    (bound free : Runtime.TypeEnv) (sigma : Assign)
    (hb : Runtime.TypeEnv.Downward bound) (hf : Runtime.TypeEnv.Downward free)
    (budget : Nat)
    (premises : ∀ p ∈ Delta.map (constraint world.outer), p.Holds sigma)
    (current : BodyEnvAt bound free sigma budget
      (view.env (closeRecursiveEnv world.outer world.types raw))) :
    Runtime.TermAt bound free sigma budget (world.mapBounds beta)
      (expr.substN 0 current.terms) := by
  let closedReady := RecursiveHMJudgement.RuntimeReady.closeRecursive
    world.outer world.types world.outerFinite world.countTarget world.outerScope
    world.typesLC world.typeTarget world.typesScope ready world.fresh world.typesSupported
  let closedCurrent := EnvAt.castEnv
    (RawBodyView.Coherent.closed_env_eq view world.outer world.types raw) current
  have safe := closedReady.termAt bound free sigma hb hf budget premises closedCurrent
  simpa only [closedCurrent, EnvAt.castEnv_terms] using safe

def literal
    {types slots : Nat → BoundsTy} {ids : List Nat} {rows : Bindings}
    {Delta : List Constraint} (view : RawBodyView) (raw : List Binding)
    (world : EnvSpecialization raw) (coherent : RawBodyView.Coherent view raw)
    (p : PrimLitExpr) :
    Pointwise (@RecursiveHMUniform.BodyDerives.RuntimeReady.literal types slots ids rows Delta (view.env raw) p)
      world where
  coherent := coherent
  run bound free sigma _ _ budget _ _ :=
    by
      have stable : world.mapBounds (boundInfoOfPrimLit p) = boundInfoOfPrimLit p := by
        cases p <;> rfl
      rw [stable]
      exact Runtime.TermAt.value (.primLit _)
        (Runtime.ValueAt.literal bound free sigma budget _)

def primBinOp
    {types slots : Nat → BoundsTy} {ids : List Nat} {rows : Bindings}
    {Delta : List Constraint} (view : RawBodyView) (raw : List Binding)
    (world : EnvSpecialization raw) (coherent : RawBodyView.Coherent view raw)
    (op : PrimBinOp) :
    Pointwise (@RecursiveHMUniform.BodyDerives.RuntimeReady.primBinOp types slots ids rows Delta
      (view.env raw) op) world where
  coherent := coherent
  run bound free sigma _ _ budget _ _ :=
    by
      have stable : world.mapBounds (Typed.primOpBounds op) = Typed.primOpBounds op := by
        cases op <;> rfl
      rw [stable]
      exact Runtime.TermAt.value (.primBinOp _)
        (Runtime.ValueAt.primBinOp bound free sigma budget _)

def nil
    {types slots : Nat → BoundsTy} {ids : List Nat} {rows : Bindings}
    {Delta : List Constraint} (view : RawBodyView) (raw : List Binding)
    (world : EnvSpecialization raw) (coherent : RawBodyView.Coherent view raw)
    (elem : BoundsTy)
    (supported : Runtime.Supported elem) :
    Pointwise (@RecursiveHMUniform.BodyDerives.RuntimeReady.nil types slots ids rows Delta
      (view.env raw) elem supported) world where
  coherent := coherent
  run bound free sigma _ _ budget _ _ := by
    exact Runtime.TermAt.value (.ctor _)
      (Runtime.ValueAt.nil bound free sigma budget (world.mapBounds elem))

def boolCtor
    {types slots : Nat → BoundsTy} {ids : List Nat} {rows : Bindings}
    {Delta : List Constraint} (view : RawBodyView) (raw : List Binding)
    (world : EnvSpecialization raw) (coherent : RawBodyView.Coherent view raw)
    {name : CtorName}
    (isCtor : BoolBranches.IsCtor name) :
    Pointwise (@RecursiveHMUniform.BodyDerives.RuntimeReady.boolCtor types slots ids rows Delta
      (view.env raw) name isCtor) world where
  coherent := coherent
  run bound free sigma _ _ budget _ _ :=
    Runtime.TermAt.value (.ctor _) (Runtime.ValueAt.bool bound free sigma budget _ isCtor)

def cons
    {view : RawBodyView} {raw : List Binding}
    {types slots : Nat → BoundsTy} {ids : List Nat} {rows : Bindings}
    {Delta : List Constraint} {head tail : Expr}
    {headTy elem : BoundsTy} {lo hi : Count}
    {headTyping : ScopedBodyDerives types slots ids rows Delta (view.env raw) head headTy}
    {tailTyping : ScopedBodyDerives types slots ids rows Delta
      (view.env raw) tail (.list lo hi elem)}
    (sub : SemanticSub Delta headTy elem)
    {headReady : RecursiveHMUniform.BodyDerives.RuntimeReady headTyping}
    {tailReady : RecursiveHMUniform.BodyDerives.RuntimeReady tailTyping}
    {world : EnvSpecialization raw}
    (headSafe : Pointwise headReady world) (tailSafe : Pointwise tailReady world) :
    Pointwise (RecursiveHMUniform.BodyDerives.RuntimeReady.cons sub headReady tailReady) world where
  coherent := headSafe.coherent
  run bound free sigma hb hf budget premises current := by
    have mappedSub := SchemeSpecialization.subtype world.types
      (CountSubstitution.subtype world.outer world.outerFinite sub)
    have tailSupport := supported_map world tailReady.supported
    cases tailSupport with
    | list elemSupport =>
        exact Runtime.TermAt.cons hb hf
          ((headSafe.run bound free sigma hb hf budget premises current).of_values
            (Runtime.subtype mappedSub (supported_map world headReady.supported) elemSupport
              bound free sigma premises))
          (tailSafe.run bound free sigma hb hf budget premises current)

def consPartial
    {view : RawBodyView} {raw : List Binding}
    {types slots : Nat → BoundsTy} {ids : List Nat} {rows : Bindings}
    {Delta : List Constraint} {head : Expr} {headTy : BoundsTy}
    {headTyping : ScopedBodyDerives types slots ids rows Delta (view.env raw) head headTy}
    {headReady : RecursiveHMUniform.BodyDerives.RuntimeReady headTyping}
    {world : EnvSpecialization raw} (headSafe : Pointwise headReady world) :
    Pointwise (RecursiveHMUniform.BodyDerives.RuntimeReady.consPartial headReady) world where
  coherent := headSafe.coherent
  run bound free sigma hb hf budget premises current :=
    Runtime.TermAt.consPartial hb hf
      (headSafe.run bound free sigma hb hf budget premises current)

def pair
    {view : RawBodyView} {raw : List Binding}
    {types slots : Nat → BoundsTy} {ids : List Nat} {rows : Bindings}
    {Delta : List Constraint} {left right : Expr} {leftTy rightTy : BoundsTy}
    {leftTyping : ScopedBodyDerives types slots ids rows Delta (view.env raw) left leftTy}
    {rightTyping : ScopedBodyDerives types slots ids rows Delta (view.env raw) right rightTy}
    {leftReady : RecursiveHMUniform.BodyDerives.RuntimeReady leftTyping}
    {rightReady : RecursiveHMUniform.BodyDerives.RuntimeReady rightTyping}
    {world : EnvSpecialization raw}
    (leftSafe : Pointwise leftReady world) (rightSafe : Pointwise rightReady world) :
    Pointwise (RecursiveHMUniform.BodyDerives.RuntimeReady.pair leftReady rightReady) world where
  coherent := leftSafe.coherent
  run bound free sigma hb hf budget premises current :=
    Runtime.TermAt.pair hb hf
      (leftSafe.run bound free sigma hb hf budget premises current)
      (rightSafe.run bound free sigma hb hf budget premises current)

def pairPartial
    {view : RawBodyView} {raw : List Binding}
    {types slots : Nat → BoundsTy} {ids : List Nat} {rows : Bindings}
    {Delta : List Constraint} {left : Expr} {leftTy rightTy : BoundsTy}
    {leftTyping : ScopedBodyDerives types slots ids rows Delta (view.env raw) left leftTy}
    {leftReady : RecursiveHMUniform.BodyDerives.RuntimeReady leftTyping}
    (rightSupported : Runtime.Supported rightTy)
    {world : EnvSpecialization raw} (leftSafe : Pointwise leftReady world) :
    Pointwise (RecursiveHMUniform.BodyDerives.RuntimeReady.pairPartial leftReady rightSupported) world where
  coherent := leftSafe.coherent
  run bound free sigma hb hf budget premises current :=
    Runtime.TermAt.pairPartial hb hf
      (leftSafe.run bound free sigma hb hf budget premises current)

def varMono
    {view : RawBodyView} {raw : List Binding}
    {types slots : Nat → BoundsTy} {ids : List Nat} {rows : Bindings}
    {Delta : List Constraint} {i : Nat} {beta : BoundsTy}
    (lookup : raw[i]? = some (Binding.mono beta))
    (supported : Runtime.Supported beta) (world : EnvSpecialization raw)
    (coherent : RawBodyView.Coherent view raw) :
    Pointwise
      (@RecursiveHMUniform.BodyDerives.RuntimeReady.varMono types slots ids rows Delta (view.env raw)
        i beta (RawBodyView.lookupMono lookup) supported) world where
  coherent := coherent
  run _ _ _ _ _ _ _ current :=
    current.varMono (RawBodyView.lookupClosedMono world lookup)

def varRecursiveFixed
    {raw : List Binding}
    {types slots : Nat → BoundsTy} {ids : List Nat} {rows : Bindings}
    {Delta : List Constraint} {i : Nat} {contract : Contract} {caller : List Nat}
    (lookup : raw[i]? = some (Binding.recursive contract))
    (used : RecursiveHMContract.Use contract.fixed Delta contract.hm caller)
    (supported : Runtime.Supported used.bounds) (world : EnvSpecialization raw) :
    Pointwise
      (@RecursiveHMUniform.BodyDerives.RuntimeReady.varRecursive types slots ids rows
        (RawBodyView.fixed.env raw) i contract Delta caller
        (RawBodyView.lookupRecursiveFixed lookup) used supported) world where
  coherent := trivial
  run bound free sigma hb hf budget premises current := by
    let sourceReady : RecursiveHMJudgement.ScopedDerives.RuntimeReady
        (@RecursiveHMJudgement.ScopedDerives.varRecursive types slots Delta ids rows
          raw i contract caller lookup used) :=
      @RecursiveHMJudgement.ScopedDerives.RuntimeReady.varRecursive types slots ids rows
        raw i contract Delta caller lookup used supported
    exact scoped_termAt sourceReady world bound free sigma hb hf budget premises current

def varRecursiveClosure
    {view : RawBodyView} {raw : List Binding}
    {types slots : Nat → BoundsTy} {ids : List Nat} {rows : Bindings}
    {Delta : List Constraint} {i : Nat} {contract : RecursiveHMContract.Closed}
    {found : Ty} {caller : List Nat}
    (lookup : (view.env raw)[i]? = some (Binding.recursiveClosure contract))
    (used : RecursiveHMContract.Closed.Use contract Delta found caller)
    (supported : Runtime.Supported used.bounds) (world : EnvSpecialization raw)
    (coherent : RawBodyView.Coherent view raw) :
    Pointwise
      (@RecursiveHMUniform.BodyDerives.RuntimeReady.varRecursiveClosure types slots ids rows
        (view.env raw) i contract Delta found caller lookup used supported) world where
  coherent := coherent
  run bound free sigma hb hf budget premises current := by
    have rawLookup : raw[i]? = some (Binding.recursiveClosure contract) := by
      rw [← coherent.env_eq]
      exact lookup
    let sourceReady : RecursiveHMJudgement.ScopedDerives.RuntimeReady
        (@RecursiveHMJudgement.ScopedDerives.varRecursiveClosure types slots Delta ids rows
          raw i contract found caller rawLookup used) :=
      @RecursiveHMJudgement.ScopedDerives.RuntimeReady.varRecursiveClosure
        types slots ids rows raw i contract Delta found caller rawLookup used supported
    exact scoped_termAt sourceReady world bound free sigma hb hf budget premises current

def varExported
    {view : RawBodyView} {raw : List Binding}
    {types slots : Nat → BoundsTy} {ids : List Nat} {rows : Bindings}
    {Delta : List Constraint} {i : Nat} {scheme : HMCountScheme.Scheme}
    {found : Ty} {caller : List Nat}
    (lookup : (view.env raw)[i]? = some (Binding.exported scheme))
    (used : HMCountScheme.Use scheme Delta found caller)
    (supported : Runtime.Supported used.bounds)
    (arguments : ∀ a ∈ used.types, Runtime.Supported a)
    (world : EnvSpecialization raw) (coherent : RawBodyView.Coherent view raw) :
    Pointwise
      (@RecursiveHMUniform.BodyDerives.RuntimeReady.varExported types slots ids rows
        (view.env raw) i scheme Delta found caller lookup used supported arguments) world where
  coherent := coherent
  run bound free sigma hb hf budget premises current := by
    have rawLookup : raw[i]? = some (Binding.exported scheme) := by
      rw [← coherent.env_eq]
      exact lookup
    let sourceReady : RecursiveHMJudgement.ScopedDerives.RuntimeReady
        (@RecursiveHMJudgement.ScopedDerives.varExported types slots Delta ids rows raw
          i scheme found caller rawLookup used) :=
      @RecursiveHMJudgement.ScopedDerives.RuntimeReady.varExported
        types slots ids rows raw i scheme Delta found caller rawLookup used supported arguments
    exact scoped_termAt sourceReady world bound free sigma hb hf budget premises current

def varClosure
    {view : RawBodyView} {raw : List Binding}
    {types slots : Nat → BoundsTy} {ids : List Nat} {rows : Bindings}
    {Delta : List Constraint} {i : Nat} {scheme : HMCountScheme.Scheme}
    {countCaptures : List Count} {typeCaptures : List BoundsTy}
    {found : Ty} {caller : List Nat}
    (lookup : (view.env raw)[i]? =
      some (Binding.closure scheme countCaptures typeCaptures))
    (used : HMCountScheme.Use (HMCountSchemeClosure.close scheme) Delta found caller)
    (captures : HMCountSchemeClosure.HasCaptureArguments scheme
      countCaptures typeCaptures used)
    (supported : Runtime.Supported used.bounds)
    (arguments : ∀ a ∈ used.types, Runtime.Supported a)
    (world : EnvSpecialization raw) (coherent : RawBodyView.Coherent view raw) :
    Pointwise
      (@RecursiveHMUniform.BodyDerives.RuntimeReady.varClosure types slots ids rows
        (view.env raw) i scheme countCaptures typeCaptures Delta found caller
        lookup used captures supported arguments) world where
  coherent := coherent
  run bound free sigma hb hf budget premises current := by
    have rawLookup : raw[i]? = some (Binding.closure scheme countCaptures typeCaptures) := by
      rw [← coherent.env_eq]
      exact lookup
    let sourceReady : RecursiveHMJudgement.ScopedDerives.RuntimeReady
        (@RecursiveHMJudgement.ScopedDerives.varClosure types slots Delta ids rows raw
          i scheme countCaptures typeCaptures found caller rawLookup used captures) :=
      @RecursiveHMJudgement.ScopedDerives.RuntimeReady.varClosure
        types slots ids rows raw i scheme countCaptures typeCaptures Delta found caller
        rawLookup used captures supported arguments
    exact scoped_termAt sourceReady world bound free sigma hb hf budget premises current

def lambda
    {view : RawBodyView} {raw : List Binding}
    {types slots : Nat → BoundsTy} {ids : List Nat} {rows : Bindings}
    {Delta : List Constraint} {ann : Option Ty} {body : Expr}
    {param result : BoundsTy}
    (annotation : ScopedHMAnnotation.ParamOK types slots ids rows Delta ann param)
    {bodyTyping : ScopedBodyDerives types slots ids rows Delta
      (view.env (Binding.mono param :: raw)) body result}
    (paramSupported : Runtime.Supported param)
    {bodyReady : RecursiveHMUniform.BodyDerives.RuntimeReady bodyTyping}
    {world : EnvSpecialization raw}
    (bodySafe : Pointwise bodyReady (world.consMono param)) :
    Pointwise
      (RecursiveHMUniform.BodyDerives.RuntimeReady.lambda annotation paramSupported
        (by simpa only [RawBodyView.env_consMono] using bodyReady)) world where
  coherent := bodySafe.coherent.tailMono
  run bound free sigma hb hf budget premises current := by
    apply Runtime.TermAt.value (.lambda _ _)
    apply Runtime.ValueAt.lambda
    · exact closes_source
        (ScopedBodyDerives.lambda annotation (by
          simpa only [RawBodyView.env_consMono] using bodyTyping)) current
    · intro j before arg argument
      have facts := argument
      rw [Runtime.ValueAt.eq_def] at facts
      let opened := (current.down hb hf (by omega : j ≤ budget)).extendMono
        (world.mapBounds param) arg facts.2.1
        (Runtime.TermAt.value facts.1 (argument.down hb hf (by omega)))
      have envEq :
          Binding.mono (world.mapBounds param) ::
              view.env (closeRecursiveEnv world.outer world.types raw) =
            view.env (closeRecursiveEnv (world.consMono param).outer
              (world.consMono param).types (Binding.mono param :: raw)) := by
        simp only [EnvSpecialization.consMono, EnvSpecialization.mapBounds,
          closeRecursiveEnv, List.map_cons, closeRecursiveBinding,
          RawBodyView.env_consMono]
      let childCurrent := EnvAt.castEnv envEq opened
      have bodyAt := bodySafe.run bound free sigma hb hf j premises childCurrent
      rw [show childCurrent.terms = arg :: current.terms by
        simp only [childCurrent, EnvAt.castEnv_terms, opened, EnvAt.extendMono, EnvAt.down]] at bodyAt
      rw [Runtime.closing_singleton current.terms current.closed arg facts.2.1]
      exact bodyAt

def letMono
    {view : RawBodyView} {raw : List Binding}
    {types slots : Nat → BoundsTy} {ids : List Nat} {rows : Bindings}
    {Delta : List Constraint} {ann : Option PolyTy} {rhs body : Expr}
    {actual result : BoundsTy}
    (annotation : ScopedHMAnnotation.BindingOK types slots ids rows Delta ann actual)
    {rhsTyping : ScopedBodyDerives types slots ids rows Delta (view.env raw) rhs actual}
    {bodyTyping : ScopedBodyDerives types slots ids rows Delta
      (view.env (Binding.mono actual :: raw)) body result}
    {rhsReady : RecursiveHMUniform.BodyDerives.RuntimeReady rhsTyping}
    {bodyReady : RecursiveHMUniform.BodyDerives.RuntimeReady bodyTyping}
    {world : EnvSpecialization raw}
    (rhsSafe : Pointwise rhsReady world)
    (bodySafe : Pointwise bodyReady (world.consMono actual)) :
    Pointwise
      (RecursiveHMUniform.BodyDerives.RuntimeReady.letMono annotation rhsReady
        (by simpa only [RawBodyView.env_consMono] using bodyReady)) world where
  coherent := rhsSafe.coherent
  run bound free sigma hb hf observation premises current := by
    cases observation with
    | zero => unfold Runtime.TermAt; intro steps value _ before; omega
    | succ budget =>
        have rhsClosed := closes_source rhsTyping current
        let previous := current.down hb hf (by omega : budget ≤ budget + 1)
        let opened := previous.extendMono (world.mapBounds actual)
          (rhs.substN 0 current.terms) rhsClosed
          (rhsSafe.run bound free sigma hb hf budget premises previous)
        have envEq :
            Binding.mono (world.mapBounds actual) ::
                view.env (closeRecursiveEnv world.outer world.types raw) =
              view.env (closeRecursiveEnv (world.consMono actual).outer
                (world.consMono actual).types (Binding.mono actual :: raw)) := by
          simp only [EnvSpecialization.consMono, EnvSpecialization.mapBounds,
            closeRecursiveEnv, List.map_cons, closeRecursiveBinding,
            RawBodyView.env_consMono]
        let childCurrent := EnvAt.castEnv envEq opened
        have bodyAt := bodySafe.run bound free sigma hb hf budget premises childCurrent
        rw [show childCurrent.terms = rhs.substN 0 current.terms :: current.terms by
          simp only [childCurrent, EnvAt.castEnv_terms, opened, EnvAt.extendMono,
            previous, EnvAt.down]] at bodyAt
        apply Runtime.TermAt.prepend SmallStep.Step.letReduce
        rw [Runtime.closing_singleton current.terms current.closed _ rhsClosed]
        exact bodyAt

def letPinned
    {view : RawBodyView} {raw : List Binding}
    {types slots : Nat → BoundsTy} {ids caller : List Nat} {rows : Bindings}
    {Delta : List Constraint} {annotation : PolyTy} {rhs body : Expr}
    {actual result : BoundsTy}
    (pinned : ScopedHMAnnotation.Pinned types slots ids rows caller Delta
      annotation.body actual)
    (mono : annotation.paramCount = 0)
    {rhsTyping : ScopedBodyDerives types slots ids rows Delta (view.env raw) rhs actual}
    {bodyTyping : ScopedBodyDerives types slots ids rows Delta
      (view.env (Binding.mono pinned.demand :: raw)) body result}
    {rhsReady : RecursiveHMUniform.BodyDerives.RuntimeReady rhsTyping}
    (demandSupported : Runtime.Supported pinned.demand)
    {bodyReady : RecursiveHMUniform.BodyDerives.RuntimeReady bodyTyping}
    {world : EnvSpecialization raw}
    (rhsSafe : Pointwise rhsReady world)
    (bodySafe : Pointwise bodyReady (world.consMono pinned.demand)) :
    Pointwise
      (RecursiveHMUniform.BodyDerives.RuntimeReady.letPinned pinned mono rhsReady
        demandSupported (by simpa only [RawBodyView.env_consMono] using bodyReady)) world where
  coherent := rhsSafe.coherent
  run bound free sigma hb hf observation premises current := by
    cases observation with
    | zero => unfold Runtime.TermAt; intro steps value _ before; omega
    | succ budget =>
        have rhsClosed := closes_source rhsTyping current
        let previous := current.down hb hf (by omega : budget ≤ budget + 1)
        have mappedSub := SchemeSpecialization.subtype world.types
          (CountSubstitution.subtype world.outer world.outerFinite pinned.inclusion)
        have rhsAt := rhsSafe.run bound free sigma hb hf budget premises previous
        have widened := rhsAt.of_values
          (Runtime.subtype mappedSub (supported_map world rhsReady.supported)
            (supported_map world demandSupported) bound free sigma premises)
        let opened := previous.extendMono (world.mapBounds pinned.demand)
          (rhs.substN 0 current.terms) rhsClosed widened
        have envEq :
            Binding.mono (world.mapBounds pinned.demand) ::
                view.env (closeRecursiveEnv world.outer world.types raw) =
              view.env (closeRecursiveEnv (world.consMono pinned.demand).outer
                (world.consMono pinned.demand).types
                (Binding.mono pinned.demand :: raw)) := by
          simp only [EnvSpecialization.consMono, EnvSpecialization.mapBounds,
            closeRecursiveEnv, List.map_cons, closeRecursiveBinding,
            RawBodyView.env_consMono]
        let childCurrent := EnvAt.castEnv envEq opened
        have bodyAt := bodySafe.run bound free sigma hb hf budget premises childCurrent
        rw [show childCurrent.terms = rhs.substN 0 current.terms :: current.terms by
          simp only [childCurrent, EnvAt.castEnv_terms, opened, EnvAt.extendMono,
            previous, EnvAt.down]] at bodyAt
        apply Runtime.TermAt.prepend SmallStep.Step.letReduce
        rw [Runtime.closing_singleton current.terms current.closed _ rhsClosed]
        exact bodyAt

def letRecClosed
    {raw : List Binding} {types slots : Nat → BoundsTy}
    {ids : List Nat} {rows : Bindings} {Delta : List Constraint}
    {result : BoundsTy}
    {output : Expr} {metadata : Scope.Metadata} {path : CorePath}
    {captures : List Nat} {premises : List Constraint} {bodyTypes : List Ty}
    (group : GeneralizedGroup output metadata path captures premises bodyTypes raw)
    (groupReady : group.ClosedRuntimeReady rows types)
    {bodyTyping : ScopedBodyDerives types slots ids rows Delta
      (group.closedExports rows types ++ ordinaryBodyEnv raw) group.body result}
    {bodyReady : RecursiveHMUniform.BodyDerives.RuntimeReady bodyTyping}
    {world : EnvSpecialization raw}
    (outerCoherent : RawBodyView.Coherent .ordinary raw)
    (bodySafe : Pointwise (view := .ordinary)
      (raw := group.closedExports rows types ++ raw)
      (types := types) (slots := slots) (ids := ids) (rows := rows)
      (Delta := Delta) (expr := group.body) (beta := result)
      (ordinary_closed_group_body_ready group bodyReady)
      (world.prependClosedExports group rows types)) :
    Pointwise (view := .ordinary) (raw := raw) (types := types) (slots := slots)
      (ids := ids) (rows := rows) (Delta := Delta)
      (expr := .letRec group.annotations group.rhss group.body) (beta := result)
      (letRecClosed_ready_view group groupReady bodyReady) world where
  coherent := outerCoherent
  run bound free sigma hb hf observation pathPremises current := by
    cases observation with
    | zero => unfold Runtime.TermAt; intro steps value _ before; omega
    | succ budget =>
        let previous := current.down hb hf (by omega : budget ≤ budget + 1)
        let previousOrdinary := EnvAt.castEnv
          (RawBodyView.env_ordinary (closeRecursiveEnv world.outer world.types raw)) previous
        let realized := groupReady.ordinaryPointwise world bound free sigma hb hf budget
          previousOrdinary
        let bodyWorld := world.prependClosedExports group rows types
        have realizedEnvEq :
            group.closedExports (CountAlgebra.compose world.outer rows)
                  (fun i => world.mapBounds (types i)) ++
                ordinaryBodyEnv (closeRecursiveEnv world.outer world.types raw) =
              RawBodyView.ordinary.env
                (closeRecursiveEnv bodyWorld.outer bodyWorld.types
                  (group.closedExports rows types ++ raw)) := by
          calc
            _ = group.closedExports (CountAlgebra.compose world.outer rows)
                    (fun i => world.mapBounds (types i)) ++
                  closeRecursiveEnv world.outer world.types raw := by
                rw [ordinaryBodyEnv_closeRecursiveEnv]
            _ = closeRecursiveEnv bodyWorld.outer bodyWorld.types
                  (group.closedExports rows types ++ raw) :=
              (world.closeRecursiveEnv_prependClosedExports group rows types).symm
            _ = _ := (RawBodyView.Coherent.closed_env_eq .ordinary
              bodyWorld.outer bodyWorld.types
              (group.closedExports rows types ++ raw)).symm
        let bodyCurrent := EnvAt.castEnv realizedEnvEq realized.val
        have bodyAt := bodySafe.run bound free sigma hb hf budget pathPremises bodyCurrent
        have bodyTerms : bodyCurrent.terms =
            Runtime.recursiveTerms group.annotations
                (closeOuterRhss group.rhss previous.terms) ++ previous.terms := by
          simp only [bodyCurrent, EnvAt.castEnv_terms, realized]
          simpa only [previousOrdinary, EnvAt.castEnv_terms] using
            (groupReady.ordinaryPointwise world bound free sigma hb hf budget
              previousOrdinary).property
        rw [bodyTerms] at bodyAt
        let closedRhss := closeOuterRhss group.rhss previous.terms
        let recursive := Runtime.recursiveTerms group.annotations closedRhss
        have closedScope : ∀ rhs ∈ closedRhss,
            rhs.varsBelow group.rhss.length = true := by
          intro rhs member
          obtain ⟨source, sourceMember, rfl⟩ := List.mem_map.mp member
          apply Runtime.closing_scoped previous.terms previous.closed source group.rhss.length
          rw [previous.arity]
          simpa only [RawBodyView.env_length, closeRecursiveEnv, List.length_map,
            Nat.add_comm] using group.rhssScoped source sourceMember
        have recursiveClosed : ∀ term ∈ recursive, term.varsBelow 0 = true := by
          apply Runtime.recursiveTerms_closed
          simpa only [closedRhss, closeOuterRhss_length] using closedScope
        have composed := Runtime.closing_compose previous.terms recursive previous.closed
          recursiveClosed group.body 0
        have recursiveLength : recursive.length = group.rhss.length := by
          simp only [recursive, Runtime.recursiveTerms, List.length_map,
            closedRhss, closeOuterRhss_length]
        rw [Nat.zero_add, recursiveLength] at composed
        rw [← composed] at bodyAt
        have sameTerms : previous.terms = current.terms := rfl
        rw [← sameTerms]
        simp only [Expr.substN, RecGroup.substN_eq_map, Nat.zero_add]
        change Runtime.TermAt bound free sigma (budget + 1) _
          (.letRec group.annotations closedRhss
            (group.body.substN group.rhss.length previous.terms))
        exact Runtime.TermAt.prepend SmallStep.Step.letRecUnfold bodyAt

def letRecFixedClosed
    {raw : List Binding} {types slots : Nat → BoundsTy}
    {ids : List Nat} {rows : Bindings} {Delta : List Constraint}
    {result : BoundsTy}
    {output : Expr} {metadata : Scope.Metadata} {path : CorePath}
    {captures : List Nat} {premises : List Constraint} {bodyTypes : List Ty}
    (group : GeneralizedGroup output metadata path captures premises bodyTypes raw)
    (groupReady : group.ClosedRuntimeReady rows types)
    {bodyTyping : ScopedBodyDerives types slots ids rows Delta
      (group.closedExports rows types ++ fixedBodyEnv raw) group.body result}
    {bodyReady : RecursiveHMUniform.BodyDerives.RuntimeReady bodyTyping}
    {world : EnvSpecialization raw}
    (bodySafe : Pointwise (view := .fixed)
      (raw := group.closedExports rows types ++ raw)
      (types := types) (slots := slots) (ids := ids) (rows := rows)
      (Delta := Delta) (expr := group.body) (beta := result)
      (fixed_closed_group_body_ready group bodyReady)
      (world.prependClosedExports group rows types)) :
    Pointwise (view := .fixed) (raw := raw) (types := types) (slots := slots)
      (ids := ids) (rows := rows) (Delta := Delta)
      (expr := .letRec group.annotations group.rhss group.body) (beta := result)
      (letRecFixedClosed_ready_view group groupReady bodyReady) world where
  coherent := trivial
  run bound free sigma hb hf observation pathPremises current := by
    cases observation with
    | zero => unfold Runtime.TermAt; intro steps value _ before; omega
    | succ budget =>
        let previous := current.down hb hf (by omega : budget ≤ budget + 1)
        let previousFixed := EnvAt.castEnv
          (RawBodyView.env_fixed (closeRecursiveEnv world.outer world.types raw)) previous
        let realized := groupReady.fixedPointwise world bound free sigma hb hf budget previousFixed
        let bodyWorld := world.prependClosedExports group rows types
        have realizedEnvEq :
            group.closedExports (CountAlgebra.compose world.outer rows)
                  (fun i => world.mapBounds (types i)) ++
                fixedBodyEnv (closeRecursiveEnv world.outer world.types raw) =
              RawBodyView.fixed.env
                (closeRecursiveEnv bodyWorld.outer bodyWorld.types
                  (group.closedExports rows types ++ raw)) := by
          calc
            _ = group.closedExports (CountAlgebra.compose world.outer rows)
                    (fun i => world.mapBounds (types i)) ++
                  closeRecursiveEnv world.outer world.types raw := rfl
            _ = closeRecursiveEnv bodyWorld.outer bodyWorld.types
                  (group.closedExports rows types ++ raw) :=
              (world.closeRecursiveEnv_prependClosedExports group rows types).symm
            _ = _ := (RawBodyView.Coherent.closed_env_eq .fixed
              bodyWorld.outer bodyWorld.types
              (group.closedExports rows types ++ raw)).symm
        let bodyCurrent := EnvAt.castEnv realizedEnvEq realized.val
        have bodyAt := bodySafe.run bound free sigma hb hf budget pathPremises bodyCurrent
        have bodyTerms : bodyCurrent.terms =
            Runtime.recursiveTerms group.annotations
                (closeOuterRhss group.rhss previous.terms) ++ previous.terms := by
          simp only [bodyCurrent, EnvAt.castEnv_terms, realized]
          simpa only [previousFixed, EnvAt.castEnv_terms] using
            (groupReady.fixedPointwise world bound free sigma hb hf budget previousFixed).property
        rw [bodyTerms] at bodyAt
        let closedRhss := closeOuterRhss group.rhss previous.terms
        let recursive := Runtime.recursiveTerms group.annotations closedRhss
        have closedScope : ∀ rhs ∈ closedRhss,
            rhs.varsBelow group.rhss.length = true := by
          intro rhs member
          obtain ⟨source, sourceMember, rfl⟩ := List.mem_map.mp member
          apply Runtime.closing_scoped previous.terms previous.closed source group.rhss.length
          rw [previous.arity]
          simpa only [RawBodyView.env_length, closeRecursiveEnv, List.length_map,
            Nat.add_comm] using group.rhssScoped source sourceMember
        have recursiveClosed : ∀ term ∈ recursive, term.varsBelow 0 = true := by
          apply Runtime.recursiveTerms_closed
          simpa only [closedRhss, closeOuterRhss_length] using closedScope
        have composed := Runtime.closing_compose previous.terms recursive previous.closed
          recursiveClosed group.body 0
        have recursiveLength : recursive.length = group.rhss.length := by
          simp only [recursive, Runtime.recursiveTerms, List.length_map,
            closedRhss, closeOuterRhss_length]
        rw [Nat.zero_add, recursiveLength] at composed
        rw [← composed] at bodyAt
        have sameTerms : previous.terms = current.terms := rfl
        rw [← sameTerms]
        simp only [Expr.substN, RecGroup.substN_eq_map, Nat.zero_add]
        change Runtime.TermAt bound free sigma (budget + 1) _
          (.letRec group.annotations closedRhss
            (group.body.substN group.rhss.length previous.terms))
        exact Runtime.TermAt.prepend SmallStep.Step.letRecUnfold bodyAt

def app
    {view : RawBodyView} {raw : List Binding}
    {types slots : Nat → BoundsTy} {ids : List Nat} {rows : Bindings}
    {Delta : List Constraint} {fn arg : Expr} {domain actual result : BoundsTy}
    {fnTyping : ScopedBodyDerives types slots ids rows Delta (view.env raw) fn
      (.arrow domain result)}
    {argTyping : ScopedBodyDerives types slots ids rows Delta (view.env raw) arg actual}
    (sub : SemanticSub Delta actual domain)
    {fnReady : RecursiveHMUniform.BodyDerives.RuntimeReady fnTyping}
    {argReady : RecursiveHMUniform.BodyDerives.RuntimeReady argTyping}
    {world : EnvSpecialization raw}
    (fnSafe : Pointwise fnReady world) (argSafe : Pointwise argReady world) :
    Pointwise (RecursiveHMUniform.BodyDerives.RuntimeReady.app sub fnReady argReady) world where
  coherent := fnSafe.coherent
  run bound free sigma hb hf budget premises current := by
    have mappedSub := SchemeSpecialization.subtype world.types
      (CountSubstitution.subtype world.outer world.outerFinite sub)
    have fnSupport := fnReady.supported
    cases fnSupport with
    | arrow domainSupport _ =>
        exact Runtime.TermAt.app hb hf
          (fnSafe.run bound free sigma hb hf budget premises current)
          ((argSafe.run bound free sigma hb hf budget premises current).of_values
            (Runtime.subtype mappedSub (supported_map world argReady.supported)
              (supported_map world domainSupport) bound free sigma premises))

def subsumption
    {view : RawBodyView} {raw : List Binding}
    {types slots : Nat → BoundsTy} {ids : List Nat} {rows : Bindings}
    {Delta : List Constraint} {expr : Expr} {actual demand : BoundsTy}
    {typing : ScopedBodyDerives types slots ids rows Delta (view.env raw) expr actual}
    (sub : SemanticSub Delta actual demand)
    {ready : RecursiveHMUniform.BodyDerives.RuntimeReady typing}
    (demandSupported : Runtime.Supported demand)
    {world : EnvSpecialization raw} (safe : Pointwise ready world) :
    Pointwise (RecursiveHMUniform.BodyDerives.RuntimeReady.subsumption sub ready demandSupported) world where
  coherent := safe.coherent
  run bound free sigma hb hf budget premises current :=
    (safe.run bound free sigma hb hf budget premises current).of_values
      (Runtime.subtype
        (SchemeSpecialization.subtype world.types
          (CountSubstitution.subtype world.outer world.outerFinite sub))
        (supported_map world ready.supported) (supported_map world demandSupported)
        bound free sigma premises)

end Pointwise
end PointwiseFundamental

#print axioms PointwiseFundamental.Pointwise.termAt
#print axioms PointwiseFundamental.Pointwise.app
#print axioms PointwiseFundamental.Pointwise.letRecClosed
#print axioms PointwiseFundamental.Pointwise.letRecFixedClosed

end FHM.Bounds.RecursiveHMClosedExit
