import EPL.Properties.UnificationScope
import EPL.Properties.UnificationSound

namespace EPL.UnificationTests

def arrowExample : Option MSubst :=
  unify
    (.arrow (.mvar 0) (.rigid 0))
    (.arrow (.prim .int) (.mvar 1))

example : arrowExample = some [(0, .prim .int), (1, .rigid 0)] := by
  decide

example : unify (.rigid 0) (.prim .int) = none := by
  decide

example : unify (.mvar 0) (.arrow (.mvar 0) (.prim .int)) = none := by
  decide

end EPL.UnificationTests
