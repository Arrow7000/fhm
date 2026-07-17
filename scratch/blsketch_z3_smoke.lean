import FHM.BLSketch

open BLSketch

/-- x + 0 ≤ x should be valid under empty prem. -/
def testSub : ForallProblem where
  prem := []
  goals := [⟨.add (.var ⟨.rigid, 0⟩) (.lit 0), .var ⟨.rigid, 0⟩⟩]

#eval checkValid testSub
