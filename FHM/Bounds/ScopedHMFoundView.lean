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

#print axioms AtNode.coherent

end FHM.Bounds.ScopedHMInterpretation
