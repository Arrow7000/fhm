import FHM.Bounds.RecursiveTyping
import FHM.Bounds.CountProposal

/-! # Checked variables and applications under recursive assumptions

These results are conditional derivations in an explicit assumption environment,
not RHS certificates or whole-group acceptance. Recursive calls instantiate
counts only; they never collect HM slots or reopen a scheme at a new HM type.
-/

namespace FHM.Bounds.RecursiveVariable

open RecursiveTyping CountSubstitution

structure Result (ids : List Nat) (rows : Bindings) (Δ : List Constraint)
    (env : List Binding) (i : Nat) (found : Ty) (caller : List Nat) where
  bounds : BoundsTy
  derivation : Derives ids rows Δ env (.var i) bounds
  shape : Synth.BoundsTy.toTy bounds = found.eraseBounds
  countScope : ScopedScheme.BoundsScoped caller bounds

def check (ids : List Nat) (rows : Bindings) (Δ : List Constraint)
    (env : List Binding) (i : Nat) (found : Ty) (args : List Count) (caller : List Nat) :
    Except String (Result ids rows Δ env i found caller) := do
  match hv : env[i]? with
  | none => throw "bounds: recursive variable outside assumption environment"
  | some (.mono β) =>
      unless args.isEmpty do throw "bounds: monomorphic variable has no count telescope"
      let shape ← match BinderBridge.equalTy (Synth.BoundsTy.toTy β) found.eraseBounds with
        | none => throw "bounds: monomorphic variable disagrees with fixed found type"
        | some h => pure h
      if hs : ScopedScheme.boundsScopedBool caller β = true then
        pure ⟨β, .varMono hv, shape.down, ScopedScheme.boundsScopedBool_sound hs⟩
      else throw "bounds: monomorphic variable counts are outside caller scope"
  | some (.recursive c) =>
      let used ← RecursiveContract.check c Δ found args caller
      pure ⟨used.bounds, .varRecursive hv used.inst used.usable, used.shape, used.inScope⟩

structure Application (ids : List Nat) (rows : Bindings) (Δ : List Constraint)
    (env : List Binding) (i : Nat) (arg : Expr) (actual : BoundsTy)
    (functionHM resultHM : Ty) (caller : List Nat) where
  domain : BoundsTy
  bounds : BoundsTy
  functionTyping : Derives ids rows Δ env (.var i) (.arrow domain bounds)
  functionShape : Synth.BoundsTy.toTy (.arrow domain bounds) = functionHM.eraseBounds
  functionScope : ScopedScheme.BoundsScoped caller (.arrow domain bounds)
  argumentTyping : Derives ids rows Δ env arg actual
  argumentScope : ScopedScheme.BoundsScoped caller actual
  inclusion : SemanticSub Δ actual domain
  derivation : Derives ids rows Δ env (.app (.var i) arg) bounds
  shape : Synth.BoundsTy.toTy bounds = resultHM.eraseBounds
  countScope : ScopedScheme.BoundsScoped caller bounds

def application (ids : List Nat) (rows : Bindings) (Δ : List Constraint)
    (env : List Binding) (i : Nat) (arg : Expr) (actual : BoundsTy)
    (typing : Derives ids rows Δ env arg actual) (functionHM resultHM : Ty)
    (args : List Count) (caller : List Nat) :
    Except String (Application ids rows Δ env i arg actual functionHM resultHM caller) := do
  let scopeProof ←
    if hs : ScopedScheme.boundsScopedBool caller actual = true then
      pure (⟨ScopedScheme.boundsScopedBool_sound hs⟩ : PLift (ScopedScheme.BoundsScoped caller actual))
    else throw "bounds: recursive application argument counts are outside caller scope"
  let callee ← check ids rows Δ env i functionHM args caller
  match hf : callee.bounds with
  | .arrow domain bounds =>
      let inclusion ← Typed.subtype Δ actual domain
      let shape ← match BinderBridge.equalTy (Synth.BoundsTy.toTy bounds) resultHM.eraseBounds with
        | none => throw "bounds: recursive application result disagrees with found payload"
        | some h => pure h
      have fnTyping : Derives ids rows Δ env (.var i) (.arrow domain bounds) := by
        simpa only [hf] using callee.derivation
      have fnShape : Synth.BoundsTy.toTy (.arrow domain bounds) = functionHM.eraseBounds := by
        simpa only [hf] using callee.shape
      have fnScope : ScopedScheme.BoundsScoped caller (.arrow domain bounds) := by
        simpa only [hf] using callee.countScope
      pure ⟨domain, bounds, fnTyping, fnShape, fnScope, typing, scopeProof.down, inclusion.down,
        .app fnTyping typing inclusion.down, shape.down, fnScope.2⟩
  | _ => throw "bounds: recursive application assumption is not a function"

/-- Count proposals come from the argument's full bounds. There are deliberately
    no structural HM proposals for recursive variables. -/
def inferApplication (ids : List Nat) (rows : Bindings) (Δ : List Constraint)
    (env : List Binding) (i : Nat) (arg : Expr) (actual : BoundsTy)
    (typing : Derives ids rows Δ env arg actual) (functionHM resultHM : Ty) (caller : List Nat) :
    Except String (Application ids rows Δ env i arg actual functionHM resultHM caller) := do
  match env[i]? with
  | some (.recursive c) =>
      match c.counts.body with
      | .arrow pattern _ =>
          let args ← CountProposal.propose c.counts.quantified pattern actual
          application ids rows Δ env i arg actual typing functionHM resultHM args caller
      | _ => throw "bounds: recursive application contract has non-arrow body"
  | _ => throw "bounds: implicit recursive call requires a declared recursive assumption"

#print axioms check
#print axioms application
#print axioms inferApplication

end FHM.Bounds.RecursiveVariable
