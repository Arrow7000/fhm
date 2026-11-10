import EPL.Properties.AnnotationAllocation

namespace EPL.AnnotationAllocationTests

def repeated : Template :=
  .arrow (.named "a") (.named "a")

def independent : Template :=
  .arrow (.named "a") (.arrow .hole (.named "b"))

example : (repeated.allocate 10).ty = .arrow (.mvar 10) (.mvar 10) := by
  decide

example : (repeated.allocate 10).next = 11 := by
  decide

example : (independent.allocate 20).ty =
    .arrow (.mvar 20) (.arrow (.mvar 22) (.mvar 21)) := by
  decide

example : (independent.allocate 20).next = 23 := by
  decide

end EPL.AnnotationAllocationTests
