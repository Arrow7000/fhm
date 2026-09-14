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

/-- A node consumer must supply a genuine derivation of the original source,
    not a rebuilt expression or a bounds type reconstructed from its HM shape. -/
def checkTyped {output path} (node : HMFoundView.AtNode output path)
    (free slots : Nat → BoundsTy) (ids : List Nat) (rows : CountSubstitution.Bindings)
    (Δ : List Constraint) (env : List RecursiveHMJudgement.Binding) (caller : List Nat)
    (actual : BoundsTy)
    (derivation : RecursiveHMJudgement.ScopedDerives free slots ids rows Δ env node.inner.stripFound actual) :
    Except String (TypedChecked node free slots ids rows Δ env caller) := do
  let checked ← checkShape node free slots caller actual
  pure ⟨actual, checked, derivation⟩

#print axioms AtNode.coherent
#print axioms checkShape
#print axioms checkTyped

end FHM.Bounds.ScopedHMInterpretation
