import FHM.Bounds.ScopedHMInterpretation
import FHM.Bounds.HMFoundView

/-! Exact-original-node lexical HM views. Kept above the pure reader so source
annotation and recursive typing layers can use that reader without importing
their own artifact consumers. -/

namespace FHM.Bounds.ScopedHMInterpretation

def AtNode.view {output path} (node : HMFoundView.AtNode output path) (free slots : Nat → BoundsTy) : Ty :=
  ty free slots node.original

theorem AtNode.coherent {output path} (node : HMFoundView.AtNode output path) (free slots : Nat → BoundsTy)
    {actual : BoundsTy} (original : Synth.BoundsTy.toTy actual = node.original.eraseBounds) :
    Synth.BoundsTy.toTy (read free slots actual) = AtNode.view node free slots := by
  rw [shape, original, erased]
  rfl

mutual
/-- A later free-HM specialization transforms both previously inserted
    interfaces, without interpreting the original lexical namespace again. -/
theorem composition (outer free slots : Nat → BoundsTy) (τ : Ty) :
    HMFoundView.ty outer (ty free slots τ) =
      ty (fun i => SchemeSpecialization.mapFree outer (free i))
        (fun i => SchemeSpecialization.mapFree outer (slots i)) τ := by
  cases τ with
  | prim => rfl
  | fvar i => exact (HMFoundView.bounds_shape outer (free i)).symm
  | bvar i => exact (HMFoundView.bounds_shape outer (slots i)).symm
  | arrow a b =>
      simp only [ty, HMFoundView.ty, composition outer free slots a, composition outer free slots b]
  | bl lo hi a =>
      simpa only [ty, HMFoundView.ty, HMFoundView.tys, listTy] using
        congrArg listTy (composition outer free slots a)
  | customTy n as => exact congrArg (Ty.customTy n) (composition_list outer free slots as)
termination_by sizeOf τ

private theorem composition_list (outer free slots : Nat → BoundsTy) (as : List Ty) :
    HMFoundView.tys outer (tys free slots as) =
      tys (fun i => SchemeSpecialization.mapFree outer (free i))
        (fun i => SchemeSpecialization.mapFree outer (slots i)) as := by
  cases as with
  | nil => rfl
  | cons a as =>
      simp only [tys, HMFoundView.tys, composition outer free slots a, composition_list outer free slots as]
termination_by sizeOf as
end

/-- Count-first specialization remains coherent at every original HM node;
    counts inside full free and lexical replacements stay bounds-only. -/
theorem specialization (outer free slots : Nat → BoundsTy)
    (rows : CountSubstitution.Bindings) (τ : Ty) :
    HMFoundView.ty outer (ty free slots τ).eraseBounds =
      ty (fun i => SchemeSpecialization.mapFree outer (CountSubstitution.bounds rows (free i)))
        (fun i => SchemeSpecialization.mapFree outer (CountSubstitution.bounds rows (slots i))) τ := by
  rw [HMFoundView.erased, composition]
  apply counts_blind
  · intro i
    rw [HMFoundView.bounds_shape, HMFoundView.bounds_shape, CountSubstitution.bounds_shape]
  · intro i
    rw [HMFoundView.bounds_shape, HMFoundView.bounds_shape, CountSubstitution.bounds_shape]

structure ShapeChecked {output path} (node : HMFoundView.AtNode output path)
    (free slots : Nat → BoundsTy) (caller : List Nat) (actual : BoundsTy) : Type where
  shape : Synth.BoundsTy.toTy actual = AtNode.view node free slots
  inScope : ScopedScheme.BoundsScoped caller actual

/-- Exact-node shape/scope reconciliation is not itself an RHS origin proof. -/
def checkShape {output path} (node : HMFoundView.AtNode output path)
    (free slots : Nat → BoundsTy) (caller : List Nat) (actual : BoundsTy) :
    Except String (ShapeChecked node free slots caller actual) := do
  let shape ← match BinderBridge.equalTy (Synth.BoundsTy.toTy actual) (AtNode.view node free slots) with
    | some h => pure h
    | none => throw "bounds: actual bounds disagree with lexical found payload at exact Core node"
  if hs : ScopedScheme.boundsScopedBool caller actual = true then
    pure ⟨shape.down, ScopedScheme.boundsScopedBool_sound hs⟩
  else throw "bounds: lexical actual bounds have counts outside caller scope"

structure TypedChecked {output path} (node : HMFoundView.AtNode output path)
    (free slots : Nat → BoundsTy) (ids : List Nat) (rows : CountSubstitution.Bindings)
    (Δ : List Constraint) (env : List RecursiveHMJudgement.Binding) (caller : List Nat) where
  actual : BoundsTy
  checked : ShapeChecked node free slots caller actual
  derivation : RecursiveHMJudgement.ScopedDerives free slots ids rows Δ env node.inner.stripFound actual
  runtimeReady : Option (PLift (RecursiveHMJudgement.ScopedDerives.RuntimeReady derivation)) := none

/-- A node consumer must supply a genuine derivation of the original source,
    not a rebuilt expression or a bounds type reconstructed from its HM shape. -/
def checkTyped {output path} (node : HMFoundView.AtNode output path)
    (free slots : Nat → BoundsTy) (ids : List Nat) (rows : CountSubstitution.Bindings)
    (Δ : List Constraint) (env : List RecursiveHMJudgement.Binding) (caller : List Nat)
    (actual : BoundsTy)
    (derivation : RecursiveHMJudgement.ScopedDerives free slots ids rows Δ env node.inner.stripFound actual)
    (ready : Option (PLift (RecursiveHMJudgement.ScopedDerives.RuntimeReady derivation)) := none) :
    Except String (TypedChecked node free slots ids rows Δ env caller) := do
  let checked ← checkShape node free slots caller actual
  pure ⟨actual, checked, derivation, ready⟩

#print axioms AtNode.coherent
#print axioms composition
#print axioms specialization
#print axioms checkShape
#print axioms checkTyped

end FHM.Bounds.ScopedHMInterpretation
