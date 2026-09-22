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

def literal
    {types slots : Nat → BoundsTy} {ids : List Nat} {rows : Bindings}
    {Delta : List Constraint} (view : RawBodyView) (raw : List Binding)
    (world : EnvSpecialization raw) (p : PrimLitExpr) :
    Pointwise (@RecursiveHMUniform.BodyDerives.RuntimeReady.literal types slots ids rows Delta (view.env raw) p)
      world where
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
    (world : EnvSpecialization raw) (op : PrimBinOp) :
    Pointwise (@RecursiveHMUniform.BodyDerives.RuntimeReady.primBinOp types slots ids rows Delta
      (view.env raw) op) world where
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
    (world : EnvSpecialization raw) (elem : BoundsTy)
    (supported : Runtime.Supported elem) :
    Pointwise (@RecursiveHMUniform.BodyDerives.RuntimeReady.nil types slots ids rows Delta
      (view.env raw) elem supported) world where
  run bound free sigma _ _ budget _ _ := by
    exact Runtime.TermAt.value (.ctor _)
      (Runtime.ValueAt.nil bound free sigma budget (world.mapBounds elem))

def boolCtor
    {types slots : Nat → BoundsTy} {ids : List Nat} {rows : Bindings}
    {Delta : List Constraint} (view : RawBodyView) (raw : List Binding)
    (world : EnvSpecialization raw) {name : CtorName}
    (isCtor : BoolBranches.IsCtor name) :
    Pointwise (@RecursiveHMUniform.BodyDerives.RuntimeReady.boolCtor types slots ids rows Delta
      (view.env raw) name isCtor) world where
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
  run bound free sigma hb hf budget premises current :=
    Runtime.TermAt.pairPartial hb hf
      (leftSafe.run bound free sigma hb hf budget premises current)

def varMono
    {view : RawBodyView} {raw : List Binding}
    {types slots : Nat → BoundsTy} {ids : List Nat} {rows : Bindings}
    {Delta : List Constraint} {i : Nat} {beta : BoundsTy}
    (lookup : raw[i]? = some (Binding.mono beta))
    (supported : Runtime.Supported beta) (world : EnvSpecialization raw) :
    Pointwise
      (@RecursiveHMUniform.BodyDerives.RuntimeReady.varMono types slots ids rows Delta (view.env raw)
        i beta (RawBodyView.lookupMono lookup) supported) world where
  run _ _ _ _ _ _ _ current :=
    current.varMono (RawBodyView.lookupClosedMono world lookup)

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

end FHM.Bounds.RecursiveHMClosedExit
