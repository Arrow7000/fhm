import FHM.Bounds.CountContract
import FHM.Bounds.StructuralApplication
import FHM.Bounds.CountProposal

/-! # Origin-backed application of an RHS-certified HM/count contract

A contract use is not yet a checked application. The argument must have its own
derivation, caller-scoped bounds, and semantic inclusion in the specialized
domain. Exact function/result found payloads are checked separately. Explicit
or conservatively proposed count arguments must be finite, scoped and usable;
proposals are not asserted as caller assumptions.

This component applies the certified RHS term, not a recursively assumed
variable. Group introduction, recursive-call environments, runtime length
soundness and production launch remain separate obligations.
-/

namespace FHM.Bounds.CountApplication

open SchemeTyping CountContract

structure Result (Δ : List Constraint) (env : List Binding) (rhs arg : Expr)
    (actual : BoundsTy) (functionHM resultHM : Ty) (caller : List Nat) where
  domain : BoundsTy
  bounds : BoundsTy
  functionTyping : Derives Δ env rhs (.arrow domain bounds)
  functionShape : Synth.BoundsTy.toTy (.arrow domain bounds) = functionHM.eraseBounds
  functionScope : ScopedScheme.BoundsScoped caller (.arrow domain bounds)
  argumentTyping : Derives Δ env arg actual
  argumentScope : ScopedScheme.BoundsScoped caller actual
  inclusion : SemanticSub Δ actual domain
  derivation : Derives Δ env (.app rhs arg) bounds
  shape : Synth.BoundsTy.toTy bounds = resultHM.eraseBounds
  countScope : ScopedScheme.BoundsScoped caller bounds

/-- Explicit complete caller HM bounds are still validated by the contract-use
    checker. Supplying them never bypasses the actual argument obligation. -/
def check {env rhs} (c : Certified env rhs) (Δ : List Constraint) (arg : Expr)
    (actual : BoundsTy) (typing : Derives Δ env arg actual)
    (functionHM resultHM : Ty) (counts : List Count) (args : List BoundsTy)
    (caller : List Nat) : Except String (Result Δ env rhs arg actual functionHM resultHM caller) := do
  let scopeProof ←
    if hs : ScopedScheme.boundsScopedBool caller actual = true then
      pure (⟨ScopedScheme.boundsScopedBool_sound hs⟩ : PLift (ScopedScheme.BoundsScoped caller actual))
    else throw "bounds: count application argument counts are outside caller scope"
  let callee ← CountContract.check c Δ functionHM counts args caller
  match arrow : callee.bounds with
  | .arrow domain bounds =>
      let inclusion ← Typed.subtype Δ actual domain
      let shape ← match BinderBridge.equalTy (Synth.BoundsTy.toTy bounds) resultHM.eraseBounds with
        | none => throw "bounds: count application result disagrees with found payload"
        | some shape => pure shape
      have fnTyping : Derives Δ env rhs (.arrow domain bounds) := by
        simpa only [arrow] using callee.derivation
      have fnShape : Synth.BoundsTy.toTy (.arrow domain bounds) = functionHM.eraseBounds := by
        simpa only [arrow] using callee.shape
      have fnScope : ScopedScheme.BoundsScoped caller (.arrow domain bounds) := by
        simpa only [arrow] using callee.countScope
      pure { domain, bounds, functionTyping := fnTyping, functionShape := fnShape
             functionScope := fnScope, argumentTyping := typing, argumentScope := scopeProof.down
             inclusion := inclusion.down
             derivation := .app fnTyping typing inclusion.down
             shape := shape.down, countScope := fnScope.2 }
  | _ => throw "bounds: count application contract use is not a function"

/-- Structural proposals preserve the argument's full bounds and use the same
    checked path as explicit arguments. Slots absent from the domain receive
    Unit only; arbitrary result-slot List bounds are never fabricated from HM. -/
def fromOrigin {env rhs} (c : Certified env rhs) (Δ : List Constraint) (arg : Expr)
    (actual : BoundsTy) (typing : Derives Δ env arg actual)
    (functionHM resultHM : Ty) (counts : List Count) (caller : List Nat) :
    Except String (Result Δ env rhs arg actual functionHM resultHM caller) := do
  match c.hm.body with
  | .arrow pattern _ =>
      let args ← StructuralApplication.propose pattern actual c.hm.hm.paramCount
      check c Δ arg actual typing functionHM resultHM counts args caller
  | _ => throw "bounds: count application contract has non-arrow body"

/-- Direct count and structural HM proposals are both untrusted. This is an
    incomplete supported-fragment policy, not arbitrary invariant inference or
    count principality: every proposed use passes the certified checker. -/
def infer {env rhs} (c : Certified env rhs) (Δ : List Constraint) (arg : Expr)
    (actual : BoundsTy) (typing : Derives Δ env arg actual)
    (functionHM resultHM : Ty) (caller : List Nat) :
    Except String (Result Δ env rhs arg actual functionHM resultHM caller) := do
  match c.hm.body with
  | .arrow pattern _ =>
      let counts ← CountProposal.propose c.counts.quantified pattern actual
      fromOrigin c Δ arg actual typing functionHM resultHM counts caller
  | _ => throw "bounds: count application contract has non-arrow body"

#print axioms check
#print axioms fromOrigin
#print axioms infer

end FHM.Bounds.CountApplication
