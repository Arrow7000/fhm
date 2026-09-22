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
