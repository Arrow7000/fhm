import FHM.Bounds.RecursiveHMBodyViewTransport

/-! # Target-indexed readiness for capture-closed locals

Closing a lexical local maps its stored captures, but it does not restrict the
local's own quantified count and HM arguments.  Consequently a target use of
the closed interface need not be the image of any source use under the ambient
specialization.  This module records the sound interface needed at that
boundary: the target derivation and its runtime-readiness proof are indexed by
the actual target use.

The same package is consumed by ordinary `let` and singleton `let rec`; their
operational difference begins only after the binding has been realized.
-/

namespace FHM.Bounds.RecursiveHMClosedExit

open RecursiveHMJudgement SchemeSpecialization CountSubstitution ScopedScheme
open RecursiveHMUniform

namespace ClosedLocalTarget

/-- The exact transformed RHS judgment associated with an actual use of a
    capture-closed local.  Caller-owned arguments in `used` are intentionally
    left untouched; only the enclosing lexical indices have already been
    specialized by `world`. -/
abbrev Typing
    (view : RawBodyView) (raw : List Binding)
    (types slots : Nat → BoundsTy) (ids : List Nat) (rows : Bindings)
    (Delta : List Constraint) (rhs : Expr) (scheme : HMCountScheme.Scheme)
    (frame : LocalFrame scheme ids rhs) (ann : Option PolyTy)
    (world : EnvSpecialization raw)
    {calleeDelta : List Constraint} {found : Ty} {caller : List Nat}
    (used : HMCountScheme.Use (HMCountSchemeClosure.close scheme)
      calleeDelta found caller) : Prop :=
  ScopedBodyDerives
    (closedLocalTypes scheme frame (fun i => world.mapBounds (types i)) used.types)
    (closedLocalSlots scheme ann (fun i => world.mapBounds (slots i)) used.types)
    ((HMCountSchemeClosure.close scheme).counts.quantified ++ ids)
    (CountAlgebra.compose
      ((HMCountSchemeClosure.close scheme).counts.quantified.zip used.counts)
      (CountAlgebra.compose world.outer rows))
    (Delta.map (constraint world.outer) ++ used.countInstance.premises)
    (view.env (closeRecursiveEnv world.outer world.types raw)) rhs used.bounds

/-- A capture-closed local is ready in one specialization world when every
    supported target use has both its exact transformed derivation and matching
    runtime-fragment evidence.  This is deliberately target-indexed: asking for
    an inverse image of `used` under `world` would be unsound for arbitrary
    (not necessarily surjective) HM/count interpretations. -/
structure Ready
    (view : RawBodyView) (raw : List Binding)
    (types slots : Nat → BoundsTy) (ids : List Nat) (rows : Bindings)
    (Delta : List Constraint) (rhs : Expr) (scheme : HMCountScheme.Scheme)
    (frame : LocalFrame scheme ids rhs) (ann : Option PolyTy)
    (world : EnvSpecialization raw) : Prop where
  typing : ∀ {calleeDelta found caller}
      (used : HMCountScheme.Use (HMCountSchemeClosure.close scheme)
        calleeDelta found caller),
    HMCountSchemeClosure.CapturesAgree scheme
      (CountAlgebra.compose world.outer rows)
      (fun i => world.mapBounds (types i)) used →
    Typing view raw types slots ids rows Delta rhs scheme frame ann world used
  ready : ∀ {calleeDelta found caller}
      (used : HMCountScheme.Use (HMCountSchemeClosure.close scheme)
        calleeDelta found caller)
      (captures : HMCountSchemeClosure.CapturesAgree scheme
        (CountAlgebra.compose world.outer rows)
        (fun i => world.mapBounds (types i)) used),
    (∀ a ∈ used.types, Runtime.Supported a) →
    RecursiveHMUniform.BodyDerives.RuntimeReady (typing used captures)

namespace Ready

/-- Eliminate target-indexed readiness directly to the logical relation.
    This is the callback needed while constructing the semantic binding for
    either `letExportedClosed` or `letRecExportedClosed`. -/
theorem termAt
    {view : RawBodyView} {raw : List Binding}
    {types slots : Nat → BoundsTy} {ids : List Nat} {rows : Bindings}
    {Delta : List Constraint} {rhs : Expr} {scheme : HMCountScheme.Scheme}
    {frame : LocalFrame scheme ids rhs} {ann : Option PolyTy}
    {world : EnvSpecialization raw}
    (target : Ready view raw types slots ids rows Delta rhs scheme frame ann world)
    {calleeDelta found caller}
    (used : HMCountScheme.Use (HMCountSchemeClosure.close scheme)
      calleeDelta found caller)
    (captures : HMCountSchemeClosure.CapturesAgree scheme
      (CountAlgebra.compose world.outer rows)
      (fun i => world.mapBounds (types i)) used)
    (arguments : ∀ a ∈ used.types, Runtime.Supported a)
    (bound free : Runtime.TypeEnv) (sigma : Assign)
    (hb : Runtime.TypeEnv.Downward bound) (hf : Runtime.TypeEnv.Downward free)
    (budget : Nat)
    (premises : ∀ p ∈
      (Delta.map (constraint world.outer) ++ used.countInstance.premises),
      p.Holds sigma)
    (current : BodyEnvAt bound free sigma budget
      (view.env (closeRecursiveEnv world.outer world.types raw))) :
    Runtime.TermAt bound free sigma budget used.bounds
      (rhs.substN 0 current.terms) :=
  (target.ready used captures arguments).termAt
    bound free sigma hb hf budget premises current

/-- Realize the mapped lexical closure at one observation budget.  Both the
    ordinary `let` and singleton recursive `let` cases use this lemma; they
    differ only in whether `term` is the closed RHS or the tied recursive
    thunk. -/
def bindingAt
    {view : RawBodyView} {raw : List Binding}
    {types slots : Nat → BoundsTy} {ids : List Nat} {rows : Bindings}
    {Delta : List Constraint} {rhs term : Expr} {scheme : HMCountScheme.Scheme}
    {frame : LocalFrame scheme ids rhs} {ann : Option PolyTy}
    {world : EnvSpecialization raw}
    (target : Ready view raw types slots ids rows Delta rhs scheme frame ann world)
    (bound free : Runtime.TypeEnv) (sigma : Assign)
    (hb : Runtime.TypeEnv.Downward bound) (hf : Runtime.TypeEnv.Downward free)
    (budget : Nat)
    (pathPremises : ∀ p ∈ Delta.map (constraint world.outer), p.Holds sigma)
    (current : BodyEnvAt bound free sigma budget
      (view.env (closeRecursiveEnv world.outer world.types raw)))
    (termBehavior : ∀ {calleeDelta found caller}
      (used : HMCountScheme.Use (HMCountSchemeClosure.close scheme)
        calleeDelta found caller),
      Runtime.TermAt bound free sigma budget used.bounds
          (rhs.substN 0 current.terms) →
        Runtime.TermAt bound free sigma budget used.bounds term) :
    BodyBindingAt bound free sigma budget
      (.closure scheme
        (HMCountSchemeClosure.interpretedCountCaptures
          (CountAlgebra.compose world.outer rows) scheme)
        (HMCountSchemeClosure.interpretedTypeCaptures
          (fun i => world.mapBounds (types i)) scheme)) term := by
  intro calleeDelta found caller used captures arguments rawPremises
  apply termBehavior used
  apply target.termAt used captures arguments bound free sigma hb hf budget ?_ current
  intro p member
  rcases List.mem_append.mp member with outer | inner
  · exact pathPremises p outer
  · exact rawPremises p inner

/-- The nonrecursive closed-local binding is the direct specialization of its
    RHS in the current lexical environment. -/
def letBindingAt
    {view : RawBodyView} {raw : List Binding}
    {types slots : Nat → BoundsTy} {ids : List Nat} {rows : Bindings}
    {Delta : List Constraint} {rhs : Expr} {scheme : HMCountScheme.Scheme}
    {frame : LocalFrame scheme ids rhs} {ann : Option PolyTy}
    {world : EnvSpecialization raw}
    (target : Ready view raw types slots ids rows Delta rhs scheme frame ann world)
    (bound free : Runtime.TypeEnv) (sigma : Assign)
    (hb : Runtime.TypeEnv.Downward bound) (hf : Runtime.TypeEnv.Downward free)
    (budget : Nat)
    (pathPremises : ∀ p ∈ Delta.map (constraint world.outer), p.Holds sigma)
    (current : BodyEnvAt bound free sigma budget
      (view.env (closeRecursiveEnv world.outer world.types raw))) :
    BodyBindingAt bound free sigma budget
      (.closure scheme
        (HMCountSchemeClosure.interpretedCountCaptures
          (CountAlgebra.compose world.outer rows) scheme)
        (HMCountSchemeClosure.interpretedTypeCaptures
          (fun i => world.mapBounds (types i)) scheme))
      (rhs.substN 0 current.terms) :=
  target.bindingAt bound free sigma hb hf budget pathPremises current
    (fun _ behavior => behavior)

/-- Build the package when static target transport and readiness transport have
    already been established together.  Checker/certificate wiring should
    construct this at the point where the canonical local RHS certificate is
    still available; `BodyDerives.RuntimeReady` alone does not retain enough
    information to reconstruct arbitrary target uses. -/
def ofFamilies
    {view : RawBodyView} {raw : List Binding}
    {types slots : Nat → BoundsTy} {ids : List Nat} {rows : Bindings}
    {Delta : List Constraint} {rhs : Expr} {scheme : HMCountScheme.Scheme}
    {frame : LocalFrame scheme ids rhs} {ann : Option PolyTy}
    {world : EnvSpecialization raw}
    (typing : ∀ {calleeDelta found caller}
      (used : HMCountScheme.Use (HMCountSchemeClosure.close scheme)
        calleeDelta found caller),
      HMCountSchemeClosure.CapturesAgree scheme
        (CountAlgebra.compose world.outer rows)
        (fun i => world.mapBounds (types i)) used →
      Typing view raw types slots ids rows Delta rhs scheme frame ann world used)
    (ready : ∀ {calleeDelta found caller}
      (used : HMCountScheme.Use (HMCountSchemeClosure.close scheme)
        calleeDelta found caller)
      (captures : HMCountSchemeClosure.CapturesAgree scheme
        (CountAlgebra.compose world.outer rows)
        (fun i => world.mapBounds (types i)) used),
      (∀ a ∈ used.types, Runtime.Supported a) →
      RecursiveHMUniform.BodyDerives.RuntimeReady (typing used captures)) :
    Ready view raw types slots ids rows Delta rhs scheme frame ann world :=
  ⟨typing, ready⟩

end Ready
end ClosedLocalTarget

#print axioms ClosedLocalTarget.Ready.termAt
#print axioms ClosedLocalTarget.Ready.bindingAt
#print axioms ClosedLocalTarget.Ready.letBindingAt
#print axioms ClosedLocalTarget.Ready.ofFamilies

end FHM.Bounds.RecursiveHMClosedExit
