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

private def runtimeBranchSpecialization
    {raw : List Binding} (world : EnvSpecialization raw)
    (ctx : BodyBranchContext) (capable : ctx.RuntimeCapable) :
    { target : BodyBranchContext // BodyBranchContext.Specializes world ctx target } := by
  cases ctx with
  | list lo hi elem =>
      let target := BodyBranchContext.list (CountSubstitution.count world.outer lo)
        (CountSubstitution.count world.outer hi) (world.mapBounds elem)
      refine ⟨target, ?_⟩
      refine { bounds := ?_, refine := ?_, fields := ?_, pattern := ?_ }
      · simp [target, BodyBranchContext.bounds, EnvSpecialization.mapBounds,
          CountSubstitution.bounds, SchemeSpecialization.mapFree]
      · intro pattern
        simpa [target, BodyBranchContext.refine] using
          (RecursiveCountTransport.branchRefine_transport world.outer pattern lo hi).symm
      · intro pattern
        by_cases selected : pattern = .named consCtorName 2 <;>
          simp [target, BodyBranchContext.fields, selected, EnvSpecialization.mapBounds,
            CountSubstitution.bounds, CountSubstitution.count, SchemeSpecialization.mapFree]
      · intro pattern valid
        exact valid
  | bool =>
      refine ⟨.bool, ?_⟩
      refine { bounds := ?_, refine := ?_, fields := ?_, pattern := ?_ }
      · rfl
      · intro pattern; rfl
      · intro pattern; rfl
      · intro pattern valid; exact valid
  | pair left right =>
      let target := BodyBranchContext.pair (world.mapBounds left) (world.mapBounds right)
      refine ⟨target, ?_⟩
      refine { bounds := ?_, refine := ?_, fields := ?_, pattern := ?_ }
      · simp [target, BodyBranchContext.bounds, EnvSpecialization.mapBounds,
          CountSubstitution.bounds, CountSubstitution.boundsList,
          SchemeSpecialization.mapFree, SchemeSpecialization.mapFreeList]
      · intro pattern; rfl
      · intro pattern
        by_cases selected : pattern = .named pairCtorName 2 <;>
          simp [target, BodyBranchContext.fields, selected]
      · intro pattern valid; exact valid
  | nominal => exact False.elim capable
  | wildcardOnly => exact False.elim capable

private theorem branch_current_env_eq
    {view : RawBodyView} {raw : List Binding} {world : EnvSpecialization raw}
    {source target : BodyBranchContext}
    (specializes : BodyBranchContext.Specializes world source target)
    (pattern : MatchPattern) :
    target.extend pattern (view.env (closeRecursiveEnv world.outer world.types raw)) =
      view.env (closeRecursiveEnv (world.extendBranch source pattern).outer
        (world.extendBranch source pattern).types (source.extendRaw pattern raw)) := by
  simp only [BodyBranchContext.extend_eq, BodyBranchContext.extendRaw,
    EnvSpecialization.extendBranch, EnvSpecialization.prependMonos_outer,
    EnvSpecialization.prependMonos_types, closeRecursiveEnv_prependMonos,
    RawBodyView.env_prependMonos, specializes.fields]

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

def letRecMono
    {view : RawBodyView} {raw : List Binding}
    {types slots : Nat → BoundsTy} {ids : List Nat} {rows : Bindings}
    {Delta : List Constraint} {ann : Option PolyTy} {rhs body : Expr}
    {actual demand result : BoundsTy}
    (annotation : ScopedHMAnnotation.BindingOK types slots ids rows Delta ann demand)
    {rhsTyping : ScopedBodyDerives types slots ids rows Delta
      (view.env (Binding.mono demand :: raw)) rhs actual}
    (sub : SemanticSub Delta actual demand)
    {bodyTyping : ScopedBodyDerives types slots ids rows Delta
      (view.env (Binding.mono demand :: raw)) body result}
    {rhsReady : RecursiveHMUniform.BodyDerives.RuntimeReady rhsTyping}
    (demandSupported : Runtime.Supported demand)
    {bodyReady : RecursiveHMUniform.BodyDerives.RuntimeReady bodyTyping}
    {world : EnvSpecialization raw}
    (rhsSafe : Pointwise rhsReady (world.consMono demand))
    (bodySafe : Pointwise bodyReady (world.consMono demand)) :
    Pointwise
      (RecursiveHMUniform.BodyDerives.RuntimeReady.letRecMono annotation sub
        (by simpa only [RawBodyView.env_consMono] using rhsReady)
        demandSupported
        (by simpa only [RawBodyView.env_consMono] using bodyReady)) world where
  coherent := bodySafe.coherent.tailMono
  run bound free sigma hb hf observation premises current := by
    cases observation with
    | zero => unfold Runtime.TermAt; intro steps value _ before; omega
    | succ budget =>
        let previous := current.down hb hf (by omega : budget ≤ budget + 1)
        have rhsScope : rhs.varsBelow
            (1 + (view.env (closeRecursiveEnv world.outer world.types raw)).length) = true := by
          simpa only [RawBodyView.env_length, closeRecursiveEnv, List.length_map,
            List.length_cons, Nat.add_comm] using rhsTyping.varsBelow
        have innerEnvEq :
            Binding.mono (world.mapBounds demand) ::
                view.env (closeRecursiveEnv world.outer world.types raw) =
              view.env (closeRecursiveEnv (world.consMono demand).outer
                (world.consMono demand).types (Binding.mono demand :: raw)) := by
          simp only [EnvSpecialization.consMono, EnvSpecialization.mapBounds,
            closeRecursiveEnv, List.map_cons, closeRecursiveBinding,
            RawBodyView.env_consMono]
        have mappedSub := SchemeSpecialization.subtype world.types
          (CountSubstitution.subtype world.outer world.outerFinite sub)
        let rhsAt : ∀ innerBudget
            (assumptions : BodyEnvAt bound free sigma innerBudget
              (Binding.mono (world.mapBounds demand) ::
                view.env (closeRecursiveEnv world.outer world.types raw))),
            Runtime.TermAt bound free sigma innerBudget (world.mapBounds demand)
              (rhs.substN 0 assumptions.terms) :=
          fun innerBudget assumptions => by
            let childCurrent := EnvAt.castEnv innerEnvEq assumptions
            have safe := rhsSafe.run bound free sigma hb hf innerBudget premises childCurrent
            have widened := safe.of_values
              (Runtime.subtype mappedSub (supported_map world rhsReady.supported)
                (supported_map world demandSupported) bound free sigma premises)
            simpa only [childCurrent, EnvAt.castEnv_terms] using widened
        let realized := BodyEnvAt.tieMono (ann := ann) rhsScope hb hf rhsAt budget previous
        let closedRhss := closeOuterRhss [rhs] previous.terms
        let recursive := Runtime.recursiveTerms [ann] closedRhss
        have realizedTerms : realized.val.terms = recursive ++ previous.terms := by
          simpa only [recursive, closedRhss] using realized.property
        let bodyCurrent := EnvAt.castEnv innerEnvEq realized.val
        have bodyAt := bodySafe.run bound free sigma hb hf budget premises bodyCurrent
        rw [show bodyCurrent.terms = recursive ++ previous.terms by
          simpa only [bodyCurrent, EnvAt.castEnv_terms] using realizedTerms] at bodyAt
        have recursiveClosed : ∀ term ∈ recursive, term.varsBelow 0 = true := by
          apply Runtime.recursiveTerms_closed
          intro source member
          obtain ⟨original, originalMember, rfl⟩ := List.mem_map.mp member
          have originalEq : original = rhs := List.mem_singleton.mp originalMember
          subst original
          apply Runtime.closing_scoped previous.terms previous.closed rhs 1
          rw [previous.arity]
          simpa only [Nat.add_comm] using rhsScope
        have composed := Runtime.closing_compose previous.terms recursive previous.closed
          recursiveClosed body 0
        rw [Nat.zero_add, show recursive.length = 1 by
          simp [recursive, closedRhss, Runtime.recursiveTerms, closeOuterRhss]] at composed
        rw [← composed] at bodyAt
        have sameTerms : previous.terms = current.terms := rfl
        rw [← sameTerms]
        simp only [Expr.substN, RecGroup.substN_eq_map, Nat.zero_add]
        change Runtime.TermAt bound free sigma (budget + 1) _
          (.letRec [ann] closedRhss (body.substN 1 previous.terms))
        exact Runtime.TermAt.prepend SmallStep.Step.letRecUnfold bodyAt

def letRecMonoGroup
    {view : RawBodyView} {raw : List Binding}
    {types slots : Nat → BoundsTy} {ids : List Nat} {rows : Bindings}
    {Delta : List Constraint} (annotations : List (Option PolyTy))
    (rhss : List Expr) (body : Expr) (demands : List BoundsTy) {result : BoundsTy}
    {actuals : Nat → BoundsTy}
    {annotationCount : annotations.length = rhss.length}
    {demandCount : demands.length = rhss.length}
    {annotationsOK : ∀ i (inside : i < rhss.length),
      ScopedHMAnnotation.BindingOK types slots ids rows Delta
        (annotations[i]'(by omega)) (demands[i]'(by omega))}
    {rhssTyping : ∀ i (inside : i < rhss.length),
      ScopedBodyDerives types slots ids rows Delta
        (view.env (demands.map Binding.mono ++ raw)) rhss[i] (actuals i)}
    {inclusions : ∀ i (inside : i < rhss.length),
      SemanticSub Delta (actuals i) (demands[i]'(by omega))}
    {bodyTyping : ScopedBodyDerives types slots ids rows Delta
      (view.env (demands.map Binding.mono ++ raw)) body result}
    {rhssReady : ∀ i inside,
      RecursiveHMUniform.BodyDerives.RuntimeReady (rhssTyping i inside)}
    (demandsSupported : ∀ demand ∈ demands, Runtime.Supported demand)
    {bodyReady : RecursiveHMUniform.BodyDerives.RuntimeReady bodyTyping}
    {world : EnvSpecialization raw}
    (rhssSafe : ∀ i inside,
      Pointwise (rhssReady i inside) (world.prependMonos demands))
    (bodySafe : Pointwise bodyReady (world.prependMonos demands)) :
    Pointwise
      (@RecursiveHMUniform.BodyDerives.RuntimeReady.letRecMonoGroup
        types slots ids rows Delta (view.env raw) annotations rhss body demands
        result actuals annotationCount demandCount annotationsOK
        (fun i _inside => by simpa only [RawBodyView.env_prependMonos] using
          rhssTyping i _inside)
        inclusions
        (by simpa only [RawBodyView.env_prependMonos] using bodyTyping)
        (fun i inside => by
          simpa only [RawBodyView.env_prependMonos] using rhssReady i inside)
        demandsSupported
        (by simpa only [RawBodyView.env_prependMonos] using bodyReady)) world where
  coherent := bodySafe.coherent.tailPrependMonos demands
  run bound free sigma hb hf observation premises current := by
    cases observation with
    | zero => unfold Runtime.TermAt; intro steps value _ before; omega
    | succ budget =>
        let previous := current.down hb hf (by omega : budget ≤ budget + 1)
        let mappedDemands := demands.map world.mapBounds
        let innerEnv := mappedDemands.map Binding.mono
        have arity : rhss.length = innerEnv.length := by
          simp only [innerEnv, mappedDemands, List.length_map]
          exact demandCount.symm
        have rhsScope : ∀ source ∈ rhss,
            source.varsBelow
              (rhss.length + (view.env
                (closeRecursiveEnv world.outer world.types raw)).length) = true := by
          intro source member
          obtain ⟨i, inside, rfl⟩ := List.mem_iff_getElem.mp member
          have scopeFact := (rhssTyping i inside).varsBelow
          simpa only [RawBodyView.env_length, closeRecursiveEnv, List.length_map,
            List.length_append, demandCount] using scopeFact
        have innerEnvEq :
            innerEnv ++ view.env (closeRecursiveEnv world.outer world.types raw) =
              view.env (closeRecursiveEnv (world.prependMonos demands).outer
                (world.prependMonos demands).types
                (demands.map Binding.mono ++ raw)) := by
          simp only [innerEnv, mappedDemands, EnvSpecialization.prependMonos_outer,
            EnvSpecialization.prependMonos_types,
            closeRecursiveEnv_prependMonos, RawBodyView.env_prependMonos]
        let rhsAt : ∀ innerBudget
            (assumptions : BodyEnvAt bound free sigma innerBudget
              (innerEnv ++ view.env
                (closeRecursiveEnv world.outer world.types raw)))
            i (inside : i < innerEnv.length),
            BodyBindingAt bound free sigma innerBudget innerEnv[i]
              ((rhss[i]'(by rw [arity]; exact inside)).substN 0 assumptions.terms) :=
          fun innerBudget assumptions i inside => by
            have rhsInside : i < rhss.length := by rw [arity]; exact inside
            have demandInside : i < demands.length := by
              rw [demandCount]
              exact rhsInside
            let childCurrent := EnvAt.castEnv innerEnvEq assumptions
            have childPremises :
                ∀ p ∈ Delta.map (constraint (world.prependMonos demands).outer),
                  p.Holds sigma := by
              simpa only [EnvSpecialization.prependMonos_outer] using premises
            have safe0 := (rhssSafe i rhsInside).run bound free sigma hb hf innerBudget
              childPremises childCurrent
            have safe : Runtime.TermAt bound free sigma innerBudget
                (world.mapBounds (actuals i))
                (rhss[i].substN 0 childCurrent.terms) := by
              simpa only [EnvSpecialization.prependMonos_outer,
                EnvSpecialization.prependMonos_types, EnvSpecialization.mapBounds] using safe0
            have mappedSub := SchemeSpecialization.subtype world.types
              (CountSubstitution.subtype world.outer world.outerFinite
                (inclusions i rhsInside))
            have widened := safe.of_values
              (Runtime.subtype mappedSub
                (supported_map world (rhssReady i rhsInside).supported)
                (supported_map world
                  (demandsSupported demands[i] (List.getElem_mem demandInside)))
                bound free sigma premises)
            simp only [BodyBindingAt, innerEnv, mappedDemands, List.getElem_map]
            simpa only [childCurrent, EnvAt.castEnv_terms,
              EnvSpecialization.prependMonos_outer,
              EnvSpecialization.prependMonos_types, EnvSpecialization.mapBounds] using widened
        let realized := EnvAt.tieGroupCaptured annotations rhss arity rhsScope hb hf
          rhsAt budget previous
        let closedRhss := closeOuterRhss rhss previous.terms
        let recursive := Runtime.recursiveTerms annotations closedRhss
        have realizedTerms : realized.val.terms = recursive ++ previous.terms := by
          simpa only [recursive, closedRhss] using realized.property
        let bodyCurrent := EnvAt.castEnv innerEnvEq realized.val
        have childPremises :
            ∀ p ∈ Delta.map (constraint (world.prependMonos demands).outer),
              p.Holds sigma := by
          simpa only [EnvSpecialization.prependMonos_outer] using premises
        have bodyAt0 := bodySafe.run bound free sigma hb hf budget childPremises bodyCurrent
        have bodyAt : Runtime.TermAt bound free sigma budget (world.mapBounds result)
            (body.substN 0 bodyCurrent.terms) := by
          simpa only [EnvSpecialization.prependMonos_outer,
            EnvSpecialization.prependMonos_types, EnvSpecialization.mapBounds] using bodyAt0
        rw [show bodyCurrent.terms = recursive ++ previous.terms by
          simpa only [bodyCurrent, EnvAt.castEnv_terms] using realizedTerms] at bodyAt
        have recursiveClosed : ∀ term ∈ recursive, term.varsBelow 0 = true := by
          apply Runtime.recursiveTerms_closed
          have closedScope : ∀ source ∈ closedRhss,
              source.varsBelow rhss.length = true := by
            intro source member
            obtain ⟨original, originalMember, rfl⟩ := List.mem_map.mp member
            apply Runtime.closing_scoped previous.terms previous.closed original rhss.length
            rw [previous.arity]
            exact rhsScope original originalMember
          simpa only [closedRhss, closeOuterRhss_length] using closedScope
        have recursiveLength : recursive.length = rhss.length := by
          simp only [recursive, Runtime.recursiveTerms, List.length_map,
            closedRhss, closeOuterRhss_length]
        have composed := Runtime.closing_compose previous.terms recursive previous.closed
          recursiveClosed body 0
        rw [Nat.zero_add, recursiveLength] at composed
        rw [← composed] at bodyAt
        have sameTerms : previous.terms = current.terms := rfl
        rw [← sameTerms]
        simp only [Expr.substN, RecGroup.substN_eq_map, Nat.zero_add]
        change Runtime.TermAt bound free sigma (budget + 1) _
          (.letRec annotations closedRhss (body.substN rhss.length previous.terms))
        exact Runtime.TermAt.prepend SmallStep.Step.letRecUnfold bodyAt

private def letRecInferredMono_body_typing_view
    {raw : List Binding} {types slots : Nat → BoundsTy}
    {ids : List Nat} {rows : Bindings} {Delta : List Constraint}
    {body : Expr} {actual result : BoundsTy}
    {bodyTyping : ScopedBodyDerives types slots ids rows Delta
      (RawBodyView.ordinary.env (Binding.mono actual :: raw)) body result} :
    ScopedBodyDerives types slots ids rows Delta
      (Binding.mono actual :: ordinaryBodyEnv raw) body result := by
  simpa only [RawBodyView.env_ordinary, RawBodyView.env_consMono] using bodyTyping

private def letRecInferredMono_typing_view
    {raw : List Binding} {types slots : Nat → BoundsTy}
    {ids : List Nat} {rows : Bindings} {Delta : List Constraint}
    {rhs body : Expr} {actual result : BoundsTy}
    (rhsTyping : ScopedDerives types slots ids rows Delta
      (Binding.mono actual :: raw) rhs actual)
    (bodyTyping : ScopedBodyDerives types slots ids rows Delta
      (RawBodyView.ordinary.env (Binding.mono actual :: raw)) body result) :
    ScopedBodyDerives types slots ids rows Delta (RawBodyView.ordinary.env raw)
      (.letRec [none] [rhs] body) result := by
  exact (RawBodyView.env_ordinary raw).symm ▸
    ScopedBodyDerives.letRecInferredMono rhsTyping
      (letRecInferredMono_body_typing_view (bodyTyping := bodyTyping))

private def letRecInferredMono_ready_view
    {raw : List Binding} {types slots : Nat → BoundsTy}
    {ids : List Nat} {rows : Bindings} {Delta : List Constraint}
    {rhs body : Expr} {actual result : BoundsTy}
    {rhsTyping : ScopedDerives types slots ids rows Delta
      (Binding.mono actual :: raw) rhs actual}
    {bodyTyping : ScopedBodyDerives types slots ids rows Delta
      (RawBodyView.ordinary.env (Binding.mono actual :: raw)) body result}
    (rhsReady : RecursiveHMJudgement.ScopedDerives.RuntimeReady rhsTyping)
    (actualSupported : Runtime.Supported actual)
    (outerArguments : RecursiveArgumentsSupported raw)
    (bodyReady : RecursiveHMUniform.BodyDerives.RuntimeReady bodyTyping) :
    RecursiveHMUniform.BodyDerives.RuntimeReady
      (letRecInferredMono_typing_view rhsTyping bodyTyping) := by
  have bodyReadyView : RecursiveHMUniform.BodyDerives.RuntimeReady
      (letRecInferredMono_body_typing_view (bodyTyping := bodyTyping)) := by
    exact RecursiveHMUniform.BodyDerives.RuntimeReady.congr
      (RecursiveHMUniform.BodyDerives.RuntimeReady.castEnv
        (by
          simp only [RawBodyView.env_ordinary, RawBodyView.env_consMono] :
            RawBodyView.ordinary.env (Binding.mono actual :: raw) =
              Binding.mono actual :: ordinaryBodyEnv raw)
        bodyReady)
  let ready := @RecursiveHMUniform.BodyDerives.RuntimeReady.letRecInferredMono
    types slots ids rows Delta raw rhs body result actual rhsTyping
    (letRecInferredMono_body_typing_view (bodyTyping := bodyTyping))
    rhsReady actualSupported outerArguments bodyReadyView
  exact RecursiveHMUniform.BodyDerives.RuntimeReady.congr
    (RecursiveHMUniform.BodyDerives.RuntimeReady.castEnv
      (RawBodyView.env_ordinary raw).symm ready)

def letRecInferredMono
    {raw : List Binding} {types slots : Nat → BoundsTy}
    {ids : List Nat} {rows : Bindings} {Delta : List Constraint}
    {rhs body : Expr} {actual result : BoundsTy}
    {rhsTyping : ScopedDerives types slots ids rows Delta
      (Binding.mono actual :: raw) rhs actual}
    {bodyTyping : ScopedBodyDerives types slots ids rows Delta
      (RawBodyView.ordinary.env (Binding.mono actual :: raw)) body result}
    {rhsReady : RecursiveHMJudgement.ScopedDerives.RuntimeReady rhsTyping}
    (actualSupported : Runtime.Supported actual)
    (outerArguments : RecursiveArgumentsSupported raw)
    {bodyReady : RecursiveHMUniform.BodyDerives.RuntimeReady bodyTyping}
    {world : EnvSpecialization raw}
    (bodySafe : Pointwise bodyReady (world.consMono actual)) :
    Pointwise
      (letRecInferredMono_ready_view rhsReady actualSupported outerArguments bodyReady) world where
  coherent := bodySafe.coherent.tailMono
  run bound free sigma hb hf observation premises current := by
    cases observation with
    | zero => unfold Runtime.TermAt; intro steps value _ before; omega
    | succ budget =>
        let previous := current.down hb hf (by omega : budget ≤ budget + 1)
        have closedArguments : RecursiveArgumentsSupported
            (closeRecursiveEnv world.outer world.types raw) := by
          intro contract member
          unfold closeRecursiveEnv at member
          obtain ⟨binding, _, impossible⟩ := List.mem_map.mp member
          cases binding <;> cases impossible
        let previousOrdinary := EnvAt.castEnv
          (RawBodyView.env_ordinary (closeRecursiveEnv world.outer world.types raw)) previous
        let outerRhs := BodyEnvAt.toEnvAt previousOrdinary closedArguments
        have rhsScope : ∀ source ∈ [rhs],
            source.varsBelow
              ([rhs].length + (closeRecursiveEnv world.outer world.types raw).length) = true := by
          intro source member
          obtain rfl := List.mem_singleton.mp member
          simpa only [List.length_singleton, List.length_cons, closeRecursiveEnv,
            List.length_map, Nat.add_comm] using rhsTyping.varsBelow
        let mappedActual := world.mapBounds actual
        have innerEnvEq :
            [Binding.mono mappedActual] ++ closeRecursiveEnv world.outer world.types raw =
              closeRecursiveEnv (world.consMono actual).outer
                (world.consMono actual).types (Binding.mono actual :: raw) := by
          simp only [mappedActual, EnvSpecialization.consMono, EnvSpecialization.mapBounds,
            closeRecursiveEnv, List.map_cons, closeRecursiveBinding, List.singleton_append]
        let rhsAt : ∀ innerBudget
            (assumptions : EnvAt bound free sigma innerBudget
              ([Binding.mono mappedActual] ++
                closeRecursiveEnv world.outer world.types raw))
            i (inside : i < [Binding.mono mappedActual].length),
            BindingAt bound free sigma innerBudget [Binding.mono mappedActual][i]
              (([rhs][i]'(by simpa using inside)).substN 0 assumptions.terms) :=
          fun innerBudget assumptions i inside => by
            have index : i = 0 := by simpa using inside
            subst i
            simp only [List.getElem_cons_zero, BindingAt]
            let childCurrent := EnvAt.castEnv innerEnvEq assumptions
            let bodyCurrent := EnvAt.toFixedBody childCurrent
            let fixedCurrent := EnvAt.castEnv
              (RawBodyView.env_fixed
                (closeRecursiveEnv (world.consMono actual).outer
                  (world.consMono actual).types (Binding.mono actual :: raw))).symm
              bodyCurrent
            have childPremises :
                ∀ p ∈ Delta.map (constraint (world.consMono actual).outer),
                  p.Holds sigma := by
              simpa only [EnvSpecialization.consMono] using premises
            have safe0 := scoped_termAt (view := .fixed) rhsReady
              (world.consMono actual) bound free sigma hb hf innerBudget childPremises fixedCurrent
            simpa only [mappedActual, EnvSpecialization.consMono,
              EnvSpecialization.mapBounds, childCurrent, EnvAt.castEnv_terms,
              bodyCurrent, EnvAt.toFixedBody, fixedCurrent] using safe0
        let realized := EnvAt.tieGroupCaptured [none] [rhs] rfl rhsScope hb hf
          rhsAt budget outerRhs
        let closedRhss := closeOuterRhss [rhs] previous.terms
        let recursive := Runtime.recursiveTerms [none] closedRhss
        have outerTerms : outerRhs.terms = previous.terms := by
          simp only [outerRhs, BodyEnvAt.toEnvAt, previousOrdinary, EnvAt.castEnv_terms]
        have realizedTerms : realized.val.terms = recursive ++ previous.terms := by
          simpa only [recursive, closedRhss, outerTerms] using realized.property
        have recursiveClosed : ∀ term ∈ recursive, term.varsBelow 0 = true := by
          apply Runtime.recursiveTerms_closed
          have closedScope := closeOuterRhss_scoped outerRhs rhsScope
          simpa only [closedRhss, outerTerms, closeOuterRhss_length] using closedScope
        have recursiveLength : recursive.length = 1 := by
          simp [recursive, closedRhss, Runtime.recursiveTerms, closeOuterRhss]
        have realizedNonempty : 0 < realized.val.terms.length := by
          rw [realized.val.arity]
          simp
        let recursiveTerm := realized.val.terms[0]'realizedNonempty
        have recursiveTermClosed : recursiveTerm.varsBelow 0 = true :=
          realized.val.closed recursiveTerm (List.getElem_mem _)
        have recursiveSafe : Runtime.TermAt bound free sigma budget mappedActual recursiveTerm := by
          have meaning := realized.val.denotes 0 (by simp)
          simpa only [List.getElem_append_left
            (by simp : 0 < [Binding.mono mappedActual].length),
            List.getElem_cons_zero, BindingAt, recursiveTerm] using meaning
        let opened := previous.extendMono mappedActual recursiveTerm
          recursiveTermClosed recursiveSafe
        have childPremises :
            ∀ p ∈ Delta.map (constraint (world.consMono actual).outer), p.Holds sigma := by
          simpa only [EnvSpecialization.consMono] using premises
        have bodyAt0 := bodySafe.run bound free sigma hb hf budget childPremises opened
        have bodyAt : Runtime.TermAt bound free sigma budget (world.mapBounds result)
            (body.substN 0 opened.terms) := by
          simpa only [EnvSpecialization.consMono, EnvSpecialization.mapBounds] using bodyAt0
        have openedTerms : opened.terms = recursive ++ previous.terms := by
          have headEq : recursiveTerm = recursive[0]'(by rw [recursiveLength]; omega) := by
            have left := List.getElem?_eq_getElem realizedNonempty
            have rightInside : 0 < recursive.length := by rw [recursiveLength]; omega
            have right := List.getElem?_eq_getElem rightInside
            have entries : realized.val.terms[0]? = recursive[0]? := by
              rw [realizedTerms]
              exact List.getElem?_append_left rightInside
            exact Option.some.inj (left.symm.trans (entries.trans right))
          simp only [opened, EnvAt.extendMono, EnvAt.extendMono]
          simp [recursive, closedRhss, Runtime.recursiveTerms, closeOuterRhss] at headEq ⊢
          exact headEq
        rw [openedTerms] at bodyAt
        have composed := Runtime.closing_compose previous.terms recursive previous.closed
          recursiveClosed body 0
        rw [Nat.zero_add, recursiveLength] at composed
        rw [← composed] at bodyAt
        have sameTerms : previous.terms = current.terms := rfl
        rw [← sameTerms]
        simp only [Expr.substN, RecGroup.substN_eq_map, Nat.zero_add]
        change Runtime.TermAt bound free sigma (budget + 1) _
          (.letRec [none] closedRhss (body.substN 1 previous.terms))
        exact Runtime.TermAt.prepend SmallStep.Step.letRecUnfold bodyAt

private def letRecPinnedMono_body_typing_view
    {raw : List Binding} {types slots : Nat → BoundsTy}
    {ids caller : List Nat} {rows : Bindings} {Delta : List Constraint}
    {annotation : PolyTy} {body : Expr} {actual result : BoundsTy}
    (pinned : ScopedHMAnnotation.Pinned types slots ids rows caller Delta
      annotation.body actual)
    {bodyTyping : ScopedBodyDerives types slots ids rows Delta
      (RawBodyView.ordinary.env (Binding.mono pinned.demand :: raw)) body result} :
    ScopedBodyDerives types slots ids rows Delta
      (Binding.mono pinned.demand :: ordinaryBodyEnv raw) body result := by
  simpa only [RawBodyView.env_ordinary, RawBodyView.env_consMono] using bodyTyping

private def letRecPinnedMono_typing_view
    {raw : List Binding} {types slots : Nat → BoundsTy}
    {ids caller : List Nat} {rows : Bindings} {Delta : List Constraint}
    {annotation : PolyTy} {rhs body : Expr} {actual result : BoundsTy}
    (pinned : ScopedHMAnnotation.Pinned types slots ids rows caller Delta
      annotation.body actual)
    (mono : annotation.paramCount = 0)
    (rhsTyping : ScopedDerives types slots ids rows Delta
      (Binding.mono pinned.demand :: raw) rhs actual)
    (bodyTyping : ScopedBodyDerives types slots ids rows Delta
      (RawBodyView.ordinary.env (Binding.mono pinned.demand :: raw)) body result) :
    ScopedBodyDerives types slots ids rows Delta (RawBodyView.ordinary.env raw)
      (.letRec [some annotation] [rhs] body) result := by
  exact (RawBodyView.env_ordinary raw).symm ▸
    ScopedBodyDerives.letRecPinnedMono pinned mono rhsTyping
      (letRecPinnedMono_body_typing_view pinned (bodyTyping := bodyTyping))

private def letRecPinnedMono_ready_view
    {raw : List Binding} {types slots : Nat → BoundsTy}
    {ids caller : List Nat} {rows : Bindings} {Delta : List Constraint}
    {annotation : PolyTy} {rhs body : Expr} {actual result : BoundsTy}
    {pinned : ScopedHMAnnotation.Pinned types slots ids rows caller Delta
      annotation.body actual}
    {mono : annotation.paramCount = 0}
    {rhsTyping : ScopedDerives types slots ids rows Delta
      (Binding.mono pinned.demand :: raw) rhs actual}
    {bodyTyping : ScopedBodyDerives types slots ids rows Delta
      (RawBodyView.ordinary.env (Binding.mono pinned.demand :: raw)) body result}
    (rhsReady : RecursiveHMJudgement.ScopedDerives.RuntimeReady rhsTyping)
    (demandSupported : Runtime.Supported pinned.demand)
    (outerArguments : RecursiveArgumentsSupported raw)
    (bodyReady : RecursiveHMUniform.BodyDerives.RuntimeReady bodyTyping) :
    RecursiveHMUniform.BodyDerives.RuntimeReady
      (letRecPinnedMono_typing_view pinned mono rhsTyping bodyTyping) := by
  have bodyReadyView : RecursiveHMUniform.BodyDerives.RuntimeReady
      (letRecPinnedMono_body_typing_view pinned (bodyTyping := bodyTyping)) := by
    exact RecursiveHMUniform.BodyDerives.RuntimeReady.congr
      (RecursiveHMUniform.BodyDerives.RuntimeReady.castEnv
        (by
          simp only [RawBodyView.env_ordinary, RawBodyView.env_consMono] :
            RawBodyView.ordinary.env (Binding.mono pinned.demand :: raw) =
              Binding.mono pinned.demand :: ordinaryBodyEnv raw)
        bodyReady)
  let ready := @RecursiveHMUniform.BodyDerives.RuntimeReady.letRecPinnedMono
    types slots ids rows caller Delta raw rhs body result annotation actual pinned mono
    rhsTyping (letRecPinnedMono_body_typing_view pinned (bodyTyping := bodyTyping))
    rhsReady demandSupported outerArguments bodyReadyView
  exact RecursiveHMUniform.BodyDerives.RuntimeReady.congr
    (RecursiveHMUniform.BodyDerives.RuntimeReady.castEnv
      (RawBodyView.env_ordinary raw).symm ready)

def letRecPinnedMono
    {raw : List Binding} {types slots : Nat → BoundsTy}
    {ids caller : List Nat} {rows : Bindings} {Delta : List Constraint}
    {annotation : PolyTy} {rhs body : Expr} {actual result : BoundsTy}
    {pinned : ScopedHMAnnotation.Pinned types slots ids rows caller Delta
      annotation.body actual}
    {mono : annotation.paramCount = 0}
    {rhsTyping : ScopedDerives types slots ids rows Delta
      (Binding.mono pinned.demand :: raw) rhs actual}
    {bodyTyping : ScopedBodyDerives types slots ids rows Delta
      (RawBodyView.ordinary.env (Binding.mono pinned.demand :: raw)) body result}
    {rhsReady : RecursiveHMJudgement.ScopedDerives.RuntimeReady rhsTyping}
    (demandSupported : Runtime.Supported pinned.demand)
    (outerArguments : RecursiveArgumentsSupported raw)
    {bodyReady : RecursiveHMUniform.BodyDerives.RuntimeReady bodyTyping}
    {world : EnvSpecialization raw}
    (bodySafe : Pointwise bodyReady (world.consMono pinned.demand)) :
    Pointwise
      (letRecPinnedMono_ready_view (mono := mono) rhsReady demandSupported
        outerArguments bodyReady) world where
  coherent := bodySafe.coherent.tailMono
  run bound free sigma hb hf observation premises current := by
    cases observation with
    | zero => unfold Runtime.TermAt; intro steps value _ before; omega
    | succ budget =>
        let previous := current.down hb hf (by omega : budget ≤ budget + 1)
        have closedArguments : RecursiveArgumentsSupported
            (closeRecursiveEnv world.outer world.types raw) := by
          intro contract member
          unfold closeRecursiveEnv at member
          obtain ⟨binding, _, impossible⟩ := List.mem_map.mp member
          cases binding <;> cases impossible
        let previousOrdinary := EnvAt.castEnv
          (RawBodyView.env_ordinary (closeRecursiveEnv world.outer world.types raw)) previous
        let outerRhs := BodyEnvAt.toEnvAt previousOrdinary closedArguments
        have rhsScope : ∀ source ∈ [rhs],
            source.varsBelow
              ([rhs].length + (closeRecursiveEnv world.outer world.types raw).length) = true := by
          intro source member
          obtain rfl := List.mem_singleton.mp member
          simpa only [List.length_singleton, List.length_cons, closeRecursiveEnv,
            List.length_map, Nat.add_comm] using rhsTyping.varsBelow
        let mappedDemand := world.mapBounds pinned.demand
        have innerEnvEq :
            [Binding.mono mappedDemand] ++ closeRecursiveEnv world.outer world.types raw =
              closeRecursiveEnv (world.consMono pinned.demand).outer
                (world.consMono pinned.demand).types (Binding.mono pinned.demand :: raw) := by
          simp only [mappedDemand, EnvSpecialization.consMono, EnvSpecialization.mapBounds,
            closeRecursiveEnv, List.map_cons, closeRecursiveBinding, List.singleton_append]
        let rhsAt : ∀ innerBudget
            (assumptions : EnvAt bound free sigma innerBudget
              ([Binding.mono mappedDemand] ++ closeRecursiveEnv world.outer world.types raw))
            i (inside : i < [Binding.mono mappedDemand].length),
            BindingAt bound free sigma innerBudget [Binding.mono mappedDemand][i]
              (([rhs][i]'(by simpa using inside)).substN 0 assumptions.terms) :=
          fun innerBudget assumptions i inside => by
            have index : i = 0 := by simpa using inside
            subst i
            simp only [List.getElem_cons_zero, BindingAt]
            let childCurrent := EnvAt.castEnv innerEnvEq assumptions
            let bodyCurrent := EnvAt.toFixedBody childCurrent
            let fixedCurrent := EnvAt.castEnv
              (RawBodyView.env_fixed
                (closeRecursiveEnv (world.consMono pinned.demand).outer
                  (world.consMono pinned.demand).types
                  (Binding.mono pinned.demand :: raw))).symm bodyCurrent
            have childPremises :
                ∀ p ∈ Delta.map (constraint (world.consMono pinned.demand).outer),
                  p.Holds sigma := by
              simpa only [EnvSpecialization.consMono] using premises
            have safe0 := scoped_termAt (view := .fixed) rhsReady
              (world.consMono pinned.demand) bound free sigma hb hf innerBudget
              childPremises fixedCurrent
            have safe : Runtime.TermAt bound free sigma innerBudget
                (world.mapBounds actual) (rhs.substN 0 assumptions.terms) := by
              simpa only [EnvSpecialization.consMono, EnvSpecialization.mapBounds,
                childCurrent, EnvAt.castEnv_terms, bodyCurrent, EnvAt.toFixedBody,
                fixedCurrent] using safe0
            have mappedSub := SchemeSpecialization.subtype world.types
              (CountSubstitution.subtype world.outer world.outerFinite pinned.inclusion)
            exact safe.of_values
              (Runtime.subtype mappedSub (supported_map world rhsReady.supported)
                (supported_map world demandSupported) bound free sigma premises)
        let realized := EnvAt.tieGroupCaptured [some annotation] [rhs] rfl rhsScope hb hf
          rhsAt budget outerRhs
        let closedRhss := closeOuterRhss [rhs] previous.terms
        let recursive := Runtime.recursiveTerms [some annotation] closedRhss
        have outerTerms : outerRhs.terms = previous.terms := by
          simp only [outerRhs, BodyEnvAt.toEnvAt, previousOrdinary, EnvAt.castEnv_terms]
        have realizedTerms : realized.val.terms = recursive ++ previous.terms := by
          simpa only [recursive, closedRhss, outerTerms] using realized.property
        have recursiveClosed : ∀ term ∈ recursive, term.varsBelow 0 = true := by
          apply Runtime.recursiveTerms_closed
          have closedScope := closeOuterRhss_scoped outerRhs rhsScope
          simpa only [closedRhss, outerTerms, closeOuterRhss_length] using closedScope
        have recursiveLength : recursive.length = 1 := by
          simp [recursive, closedRhss, Runtime.recursiveTerms, closeOuterRhss]
        have realizedNonempty : 0 < realized.val.terms.length := by
          rw [realized.val.arity]
          simp
        let recursiveTerm := realized.val.terms[0]'realizedNonempty
        have recursiveTermClosed : recursiveTerm.varsBelow 0 = true :=
          realized.val.closed recursiveTerm (List.getElem_mem _)
        have recursiveSafe : Runtime.TermAt bound free sigma budget mappedDemand recursiveTerm := by
          have meaning := realized.val.denotes 0 (by simp)
          simpa only [List.getElem_append_left
            (by simp : 0 < [Binding.mono mappedDemand].length),
            List.getElem_cons_zero, BindingAt, recursiveTerm] using meaning
        let opened := previous.extendMono mappedDemand recursiveTerm
          recursiveTermClosed recursiveSafe
        have childPremises :
            ∀ p ∈ Delta.map (constraint (world.consMono pinned.demand).outer),
              p.Holds sigma := by
          simpa only [EnvSpecialization.consMono] using premises
        have bodyAt0 := bodySafe.run bound free sigma hb hf budget childPremises opened
        have bodyAt : Runtime.TermAt bound free sigma budget (world.mapBounds result)
            (body.substN 0 opened.terms) := by
          simpa only [EnvSpecialization.consMono, EnvSpecialization.mapBounds] using bodyAt0
        have openedTerms : opened.terms = recursive ++ previous.terms := by
          have headEq : recursiveTerm = recursive[0]'(by rw [recursiveLength]; omega) := by
            have left := List.getElem?_eq_getElem realizedNonempty
            have rightInside : 0 < recursive.length := by rw [recursiveLength]; omega
            have right := List.getElem?_eq_getElem rightInside
            have entries : realized.val.terms[0]? = recursive[0]? := by
              rw [realizedTerms]
              exact List.getElem?_append_left rightInside
            exact Option.some.inj (left.symm.trans (entries.trans right))
          simp only [opened, EnvAt.extendMono, EnvAt.extendMono]
          simp [recursive, closedRhss, Runtime.recursiveTerms, closeOuterRhss] at headEq ⊢
          exact headEq
        rw [openedTerms] at bodyAt
        have composed := Runtime.closing_compose previous.terms recursive previous.closed
          recursiveClosed body 0
        rw [Nat.zero_add, recursiveLength] at composed
        rw [← composed] at bodyAt
        have sameTerms : previous.terms = current.terms := rfl
        rw [← sameTerms]
        simp only [Expr.substN, RecGroup.substN_eq_map, Nat.zero_add]
        change Runtime.TermAt bound free sigma (budget + 1) _
          (.letRec [some annotation] closedRhss (body.substN 1 previous.terms))
        exact Runtime.TermAt.prepend SmallStep.Step.letRecUnfold bodyAt

def match_
    {view : RawBodyView} {raw : List Binding}
    {types slots : Nat → BoundsTy} {ids : List Nat} {rows : Bindings}
    {Delta : List Constraint} {scrut : Expr}
    {branches : List (MatchPattern × Expr)} {result : BoundsTy}
    {ctx : BodyBranchContext} {actuals : Nat → BoundsTy}
    {scrutTyping : ScopedBodyDerives types slots ids rows Delta
      (view.env raw) scrut ctx.bounds}
    (coverage : ctx.Covers Delta branches)
    (patterns : ∀ branch ∈ branches, ctx.Pattern branch.1)
    {branchTyping : ∀ i branch, branches[i]? = some branch →
      ScopedBodyDerives types slots ids rows (Delta ++ ctx.refine branch.1)
        (view.env (ctx.extendRaw branch.1 raw)) branch.2 (actuals i)}
    (inclusions : ∀ i branch, branches[i]? = some branch →
      SemanticSub (Delta ++ ctx.refine branch.1) (actuals i) result)
    (capable : ctx.RuntimeCapable)
    {scrutReady : RecursiveHMUniform.BodyDerives.RuntimeReady scrutTyping}
    {branchReady : ∀ i branch (atIndex : branches[i]? = some branch),
      RecursiveHMUniform.BodyDerives.RuntimeReady (branchTyping i branch atIndex)}
    (resultSupported : Runtime.Supported result)
    {world : EnvSpecialization raw}
    (scrutSafe : Pointwise scrutReady world)
    (branchesSafe : ∀ i branch (atIndex : branches[i]? = some branch),
      Pointwise (branchReady i branch atIndex)
        (world.extendBranch ctx branch.1)) :
    Pointwise
      (@RecursiveHMUniform.BodyDerives.RuntimeReady.match_
        types slots ids rows Delta (view.env raw) scrut branches result actuals ctx
        scrutTyping coverage patterns
        (fun i branch atIndex => by
          simpa only [RawBodyView.env_extendRaw] using branchTyping i branch atIndex)
        inclusions capable scrutReady
        (fun i branch atIndex => by
          simpa only [RawBodyView.env_extendRaw] using branchReady i branch atIndex)
        resultSupported) world where
  coherent := scrutSafe.coherent
  run bound free sigma hb hf budget premises current := by
    let targetPack := runtimeBranchSpecialization world ctx capable
    let target := targetPack.val
    have specializes : BodyBranchContext.Specializes world ctx target := targetPack.property
    have targetCoverage : target.Covers (Delta.map (constraint world.outer)) branches := by
      cases ctx with
      | list lo hi elem =>
          simpa only [target, targetPack, runtimeBranchSpecialization] using
            coverage.transport world.outer world.outerFinite
      | bool => simpa only [target, targetPack, runtimeBranchSpecialization] using coverage
      | pair left right =>
          simpa only [target, targetPack, runtimeBranchSpecialization] using coverage
      | nominal => exact False.elim capable
      | wildcardOnly => exact False.elim capable
    have scrutAt0 := scrutSafe.run bound free sigma hb hf budget premises current
    have scrutAt : Runtime.TermAt bound free sigma budget target.bounds
        (scrut.substN 0 current.terms) := by
      rw [specializes.bounds]
      exact scrutAt0
    let branchAt : ∀ i (branch : MatchPattern × Expr)
        (atIndex : branches[i]? = some branch) (observation : Nat)
        (path : ∀ p ∈ Delta.map (constraint world.outer) ++ target.refine branch.1,
          p.Holds sigma)
        (opened : BodyEnvAt bound free sigma observation
          (target.extend branch.1
            (view.env (closeRecursiveEnv world.outer world.types raw)))),
        Runtime.TermAt bound free sigma observation (world.mapBounds result)
          (branch.2.substN 0 opened.terms) :=
      fun i branch atIndex observation path opened => by
        let branchWorld := world.extendBranch ctx branch.1
        let branchCurrent := EnvAt.castEnv
          (branch_current_env_eq specializes branch.1) opened
        have branchPremises :
            ∀ p ∈ (Delta ++ ctx.refine branch.1).map
                (constraint branchWorld.outer), p.Holds sigma := by
          simpa only [branchWorld, EnvSpecialization.extendBranch,
            EnvSpecialization.prependMonos_outer, List.map_append,
            specializes.refine] using path
        have safe0 := (branchesSafe i branch atIndex).run bound free sigma hb hf
          observation branchPremises branchCurrent
        have safe : Runtime.TermAt bound free sigma observation
            (world.mapBounds (actuals i)) (branch.2.substN 0 opened.terms) := by
          simpa only [branchWorld, EnvSpecialization.extendBranch,
            EnvSpecialization.prependMonos_outer,
            EnvSpecialization.prependMonos_types, EnvSpecialization.mapBounds,
            branchCurrent, EnvAt.castEnv_terms] using safe0
        have mappedSub := SchemeSpecialization.subtype world.types
          (CountSubstitution.subtype world.outer world.outerFinite
            (inclusions i branch atIndex))
        have targetSub : SemanticSub
            (Delta.map (constraint world.outer) ++ target.refine branch.1)
            (world.mapBounds (actuals i)) (world.mapBounds result) := by
          simpa only [List.map_append, specializes.refine] using mappedSub
        exact safe.of_values
          (Runtime.subtype targetSub
            (supported_map world (branchReady i branch atIndex).supported)
            (supported_map world resultSupported) bound free sigma path)
    rw [Runtime.closing_match]
    cases ctx with
    | list lo hi elem =>
        let targetCtx := BodyBranchContext.list (CountSubstitution.count world.outer lo)
          (CountSubstitution.count world.outer hi) (world.mapBounds elem)
        have targetEq : target = targetCtx := by
          rfl
        subst target
        apply Runtime.TermAt.matchList scrutAt
          (Runtime.listCoverage_close targetCoverage current.terms) premises
        intro observation before value len name args pattern closedBody list contained applied selected
        obtain ⟨body, original, rfl⟩ := Runtime.firstMatch_unclose current.terms selected
        obtain ⟨i, atIndex⟩ := List.mem_iff_getElem?.mp original.mem
        obtain ⟨refined, opened, terms⟩ := BodyEnvAt.listBranch
          (current.down hb hf (by omega : observation ≤ budget)) hb hf list contained applied
          original (patterns _ original.mem)
        have path : ∀ p ∈ Delta.map (constraint world.outer) ++
            targetCtx.refine pattern, p.Holds sigma := by
          intro p member
          rcases List.mem_append.mp member with outer | localPath
          · exact premises p outer
          · exact refined p localPath
        have safe := branchAt i (pattern, body) atIndex observation path opened
        rw [terms] at safe
        have targetPattern : targetCtx.Pattern pattern := patterns _ original.mem
        have contentsLength : (args.take pattern.bindCount).length = pattern.bindCount := by
          have arity := opened.arity
          rw [terms, List.length_append] at arity
          rw [BodyBranchContext.extend_length targetPattern] at arity
          change (args.take pattern.bindCount).length + current.terms.length =
            (view.env (closeRecursiveEnv world.outer world.types raw)).length +
              pattern.bindCount at arity
          rw [current.arity] at arity
          omega
        have contentsClosed : ∀ term ∈ args.take pattern.bindCount,
            term.varsBelow 0 = true := by
          intro term member
          exact opened.closed term (by rw [terms]; exact List.mem_append_left _ member)
        have closing := Runtime.closing_compose current.terms
          (args.take pattern.bindCount) current.closed contentsClosed body 0
        simp only [Nat.zero_add, contentsLength] at closing
        rw [closing]
        exact safe
    | bool =>
        have targetEq : target = BodyBranchContext.bool := by rfl
        subst target
        apply Runtime.TermAt.matchBool scrutAt
          (Runtime.boolCoverage_close targetCoverage current.terms)
        intro observation before name pattern closedBody nameOK selected
        obtain ⟨body, original, rfl⟩ := Runtime.firstMatch_unclose current.terms selected
        obtain ⟨i, atIndex⟩ := List.mem_iff_getElem?.mp original.mem
        have zero : pattern.bindCount = 0 := by
          rcases patterns _ original.mem with rfl | rfl | rfl <;> rfl
        simp only [zero, List.take_zero]
        have bodyClosed : (body.substN 0 current.terms).varsBelow 0 = true := by
          apply Runtime.closing_scoped current.terms current.closed body 0
          have scope := (branchTyping i (pattern, body) atIndex).varsBelow
          simpa only [Nat.zero_add, current.arity, BodyBranchContext.extendRaw,
            BodyBranchContext.fields, List.nil_append, RawBodyView.env_length,
            closeRecursiveEnv, List.length_map] using scope
        rw [Expr.substN_of_closed bodyClosed]
        have path : ∀ p ∈ Delta.map (constraint world.outer) ++
            (BodyBranchContext.bool).refine pattern, p.Holds sigma := by
          simpa only [BodyBranchContext.refine, List.append_nil] using premises
        exact branchAt i (pattern, body) atIndex observation path
          (current.down hb hf (by omega))
    | pair left right =>
        let targetCtx := BodyBranchContext.pair (world.mapBounds left) (world.mapBounds right)
        have targetEq : target = targetCtx := by rfl
        subst target
        apply Runtime.TermAt.matchPair scrutAt
          (Runtime.pairCoverage_close targetCoverage current.terms)
        intro observation before leftValue rightValue pattern closedBody leftMeaning
          rightMeaning selected
        obtain ⟨body, original, rfl⟩ := Runtime.firstMatch_unclose current.terms selected
        obtain ⟨i, atIndex⟩ := List.mem_iff_getElem?.mp original.mem
        obtain ⟨opened, terms⟩ := BodyEnvAt.pairBranch
          (current.down hb hf (by omega : observation ≤ budget)) hb hf leftMeaning rightMeaning
          (patterns _ original.mem)
        have path : ∀ p ∈ Delta.map (constraint world.outer) ++
            targetCtx.refine pattern, p.Holds sigma := by
          simpa only [targetCtx, BodyBranchContext.refine, List.append_nil] using premises
        have safe := branchAt i (pattern, body) atIndex observation path opened
        rw [terms] at safe
        have targetPattern : targetCtx.Pattern pattern := patterns _ original.mem
        have contentsLength : ([leftValue, rightValue].take pattern.bindCount).length =
            pattern.bindCount := by
          have arity := opened.arity
          rw [terms, List.length_append] at arity
          rw [BodyBranchContext.extend_length targetPattern] at arity
          change ([leftValue, rightValue].take pattern.bindCount).length +
              current.terms.length =
            (view.env (closeRecursiveEnv world.outer world.types raw)).length +
              pattern.bindCount at arity
          rw [current.arity] at arity
          omega
        have contentsClosed : ∀ term ∈ [leftValue, rightValue].take pattern.bindCount,
            term.varsBelow 0 = true := by
          intro term member
          exact opened.closed term (by rw [terms]; exact List.mem_append_left _ member)
        have closing := Runtime.closing_compose current.terms
          ([leftValue, rightValue].take pattern.bindCount) current.closed contentsClosed body 0
        simp only [Nat.zero_add, contentsLength] at closing
        rw [closing]
        exact safe
    | nominal => exact False.elim capable
    | wildcardOnly => exact False.elim capable

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
