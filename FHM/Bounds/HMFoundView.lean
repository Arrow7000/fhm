import FHM.Bounds.HMInterpretation
import FHM.Bounds.RecursiveHMJudgement
import FHM.CorePath

/-! # Exact-node proof-side views of discovered HM types

The original found artifact and its logical Core addresses remain unchanged.
One shared simultaneous HM interpretation gives the type view at each node.
The view forgets counts (Path R); actual argument/RHS bounds and their typing
evidence remain separate inputs. Shape reconciliation is not an origin proof.
-/

namespace FHM.Bounds.HMFoundView

open SchemeSpecialization

mutual
def ty (types : Nat → BoundsTy) : Ty → Ty
  | .prim p => .prim p
  | .fvar i => Synth.BoundsTy.toTy (types i)
  | .bvar i => .bvar i
  | .arrow a b => .arrow (ty types a) (ty types b)
  | .bl _ _ a => listTy (ty types a)
  | .customTy n as => .customTy n (tys types as)

def tys (types : Nat → BoundsTy) : List Ty → List Ty
  | [] => []
  | a :: as => ty types a :: tys types as
end

mutual
/-- The lexical reader with identity slots is the original free-only HM view. -/
theorem scoped_identity_slots (types : Nat → BoundsTy) (τ : Ty) :
    ScopedHMInterpretation.ty types BoundsTy.bvar τ = ty types τ := by
  cases τ with
  | prim | fvar => rfl
  | bvar => simp only [ScopedHMInterpretation.ty, ty, Synth.BoundsTy.toTy]
  | arrow a b =>
      simp only [ScopedHMInterpretation.ty, ty, scoped_identity_slots types a, scoped_identity_slots types b]
  | bl lo hi a => exact congrArg listTy (scoped_identity_slots types a)
  | customTy n as => exact congrArg (Ty.customTy n) (scoped_identity_slots_list types as)
termination_by sizeOf τ

private theorem scoped_identity_slots_list (types : Nat → BoundsTy) (as : List Ty) :
    ScopedHMInterpretation.tys types BoundsTy.bvar as = tys types as := by
  cases as with
  | nil => rfl
  | cons a as =>
      simp only [ScopedHMInterpretation.tys, tys, scoped_identity_slots types a, scoped_identity_slots_list types as]
termination_by sizeOf as
end

mutual
theorem erased (types : Nat → BoundsTy) (τ : Ty) : ty types τ.eraseBounds = ty types τ := by
  cases τ with
  | prim | fvar | bvar => simp only [ty, Ty.eraseBounds]
  | arrow a b => simp only [ty, Ty.eraseBounds, erased types a, erased types b]
  | bl lo hi a =>
      simpa only [Ty.eraseBounds, bareListTy, ty, tys, listTy] using congrArg listTy (erased types a)
  | customTy n as => exact congrArg (Ty.customTy n) (erased_list types as)
termination_by sizeOf τ

private theorem erased_list (types : Nat → BoundsTy) (as : List Ty) :
    tys types (TyList.eraseBounds as) = tys types as := by
  cases as with
  | nil => rfl
  | cons a as => simp only [TyList.eraseBounds, tys, erased types a, erased_list types as]
termination_by sizeOf as
end

mutual
theorem bounds_shape (types : Nat → BoundsTy) (β : BoundsTy) :
    Synth.BoundsTy.toTy (mapFree types β) = ty types (Synth.BoundsTy.toTy β) := by
  cases β with
  | prim | fvar | bvar => simp only [mapFree, Synth.BoundsTy.toTy, ty]
  | arrow a b => simp only [Synth.BoundsTy.toTy, mapFree, ty, bounds_shape types a, bounds_shape types b]
  | list lo hi a =>
      simpa only [Synth.BoundsTy.toTy, mapFree, listTy, ty, tys] using congrArg listTy (bounds_shape types a)
  | custom n as =>
      simpa only [mapFree, Synth.BoundsTy.toTy, ty] using congrArg (Ty.customTy n) (bounds_list_shape types as)
termination_by sizeOf β

private theorem bounds_list_shape (types : Nat → BoundsTy) (as : List BoundsTy) :
    (mapFreeList types as).map Synth.BoundsTy.toTy = tys types (as.map Synth.BoundsTy.toTy) := by
  cases as with
  | nil => rfl
  | cons a as => simp only [mapFreeList, List.map_cons, tys, bounds_shape types a, bounds_list_shape types as]
termination_by sizeOf as
end

mutual
/-- Changing interval payloads of supplied types cannot affect any HM view. -/
theorem counts_blind {a b : Nat → BoundsTy}
    (same : ∀ i, Synth.BoundsTy.toTy (a i) = Synth.BoundsTy.toTy (b i)) (τ : Ty) : ty a τ = ty b τ := by
  cases τ with
  | prim | bvar => rfl
  | fvar i => exact same i
  | arrow x y => simp only [ty, counts_blind same x, counts_blind same y]
  | bl lo hi x => exact congrArg listTy (counts_blind same x)
  | customTy n as => exact congrArg (Ty.customTy n) (counts_list_blind same as)
termination_by sizeOf τ

private theorem counts_list_blind {a b : Nat → BoundsTy}
    (same : ∀ i, Synth.BoundsTy.toTy (a i) = Synth.BoundsTy.toTy (b i)) (as : List Ty) : tys a as = tys b as := by
  cases as with
  | nil => rfl
  | cons x xs => simp only [tys, counts_blind same x, counts_list_blind same xs]
termination_by sizeOf as
end

mutual
/-- Outer specialization interprets identities inside the already checked
    source interpretation, not inside freshly inserted final caller types. -/
theorem composition (outer inner : Nat → BoundsTy) (τ : Ty) :
    ty outer (ty inner τ) = ty (fun i => mapFree outer (inner i)) τ := by
  cases τ with
  | prim | bvar => rfl
  | fvar i => exact (bounds_shape outer (inner i)).symm
  | arrow a b => simp only [ty, composition outer inner a, composition outer inner b]
  | bl lo hi a =>
      simpa only [ty, listTy, tys] using congrArg listTy (composition outer inner a)
  | customTy name as => exact congrArg (Ty.customTy name) (composition_list outer inner as)
termination_by sizeOf τ

private theorem composition_list (outer inner : Nat → BoundsTy) (as : List Ty) :
    tys outer (tys inner as) = tys (fun i => mapFree outer (inner i)) as := by
  cases as with
  | nil => rfl
  | cons a as => simp only [tys, composition outer inner a, composition_list outer inner as]
termination_by sizeOf as
end

/-- Count-first specialization of source replacements agrees at every HM node
    with interpreting the original source view. Count payloads remain separate. -/
theorem specialization (outer source : Nat → BoundsTy)
    (rows : CountSubstitution.Bindings) (τ : Ty) :
    ty outer (ty source τ).eraseBounds =
      ty (fun i => mapFree outer (CountSubstitution.bounds rows (source i))) τ := by
  rw [erased, composition]
  apply counts_blind
  intro i
  rw [bounds_shape, bounds_shape, CountSubstitution.bounds_shape]

structure AtNode (output : Expr) (path : CorePath) where
  original : Ty
  inner : Expr
  located : output.atCorePath path = some (.found original inner)

def locate (output : Expr) (path : CorePath) : Except String (AtNode output path) :=
  match h : output.atCorePath path with
  | some (.found original inner) => .ok ⟨original, inner, h⟩
  | some _ => .error "bounds: HM interpretation requires a found payload at the exact Core node"
  | none => .error "bounds: HM interpretation Core path is outside the original artifact"

def AtNode.view {output path} (node : AtNode output path) (types : Nat → BoundsTy) : Ty := ty types node.original

/-- Existing actual bounds and the unchanged artifact's HM payload agree after
    the same interpretation. The actual bounds have not been reconstructed. -/
theorem AtNode.coherent {output path} (node : AtNode output path) (types : Nat → BoundsTy)
    {actual : BoundsTy} (original : Synth.BoundsTy.toTy actual = node.original.eraseBounds) :
    Synth.BoundsTy.toTy (mapFree types actual) = node.view types := by
  rw [bounds_shape, original, erased]
  rfl

structure ShapeChecked {output path} (node : AtNode output path) (types : Nat → BoundsTy)
    (caller : List Nat) (actual : BoundsTy) : Type where
  shape : Synth.BoundsTy.toTy actual = node.view types
  inScope : ScopedScheme.BoundsScoped caller actual

/-- The consuming walker must supply actual bounds AND a real typing proof.
    This helper checks only the exact-node interpreted shape and count scope. -/
def checkShape {output path} (node : AtNode output path) (types : Nat → BoundsTy)
    (caller : List Nat) (actual : BoundsTy) : Except String (ShapeChecked node types caller actual) := do
  let shape ← match BinderBridge.equalTy (Synth.BoundsTy.toTy actual) (node.view types) with
    | some h => pure h
    | none => throw "bounds: actual bounds disagree with interpreted found payload at exact Core node"
  if hs : ScopedScheme.boundsScopedBool caller actual = true then
    pure ⟨shape.down, ScopedScheme.boundsScopedBool_sound hs⟩
  else throw "bounds: interpreted actual bounds have counts outside caller scope"

/-- A consumable node result must retain a derivation for this node's ORIGINAL
    source expression, not just an interpreted HM shape. -/
structure TypedChecked {output path} (node : AtNode output path) (types : Nat → BoundsTy)
    (ids : List Nat) (rows : CountSubstitution.Bindings) (Δ : List Constraint)
    (env : List RecursiveHMJudgement.Binding) (caller : List Nat) where
  actual : BoundsTy
  checked : ShapeChecked node types caller actual
  derivation : RecursiveHMJudgement.Derives types ids rows Δ env node.inner.stripFound actual

def checkTyped {output path} (node : AtNode output path) (types : Nat → BoundsTy)
    (ids : List Nat) (rows : CountSubstitution.Bindings) (Δ : List Constraint)
    (env : List RecursiveHMJudgement.Binding) (caller : List Nat) (actual : BoundsTy)
    (derivation : RecursiveHMJudgement.Derives types ids rows Δ env node.inner.stripFound actual) :
    Except String (TypedChecked node types ids rows Δ env caller) := do
  let checked ← checkShape node types caller actual
  pure ⟨actual, checked, derivation⟩

#print axioms erased
#print axioms scoped_identity_slots
#print axioms bounds_shape
#print axioms counts_blind
#print axioms composition
#print axioms specialization
#print axioms AtNode.coherent
#print axioms checkShape
#print axioms checkTyped

end FHM.Bounds.HMFoundView
