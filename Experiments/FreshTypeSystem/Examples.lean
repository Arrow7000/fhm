import Experiments.FreshTypeSystem.InferW
import Experiments.FreshTypeSystem.Pretty

/-! # End-to-end demos

Run the verified inferer on a Core program and pretty-print its principal type.
`typecheck [] e` returns the principal scheme (`Option PolyTy`); we render both
the program and the inferred type with the `Pretty` printers. -/

namespace Core.Demo

private def typeStr (e : Expr) : String :=
  match typecheck [] e with
  | none   => "ill-typed"
  | some σ => toString σ

private def showType (e : Expr) : IO Unit := IO.println s!"({e})  :  {typeStr e}"

-- λx. x  :  ∀ a. a → a
#eval showType (.lambda none (.var 0))

-- λx. λy. x  :  ∀ a b. b → a → b
#eval showType (.lambda none (.lambda none (.var 1)))

-- (λx. x) 5  :  Int
#eval showType (.app (.lambda none (.var 0)) (.primLit (.int 5)))

-- λx. λy. x  :  ∀ a b. a → b → a
#eval showType (.lambda none (.lambda none (.var 1)))

-- let id : ∀ a. a → a = λx. x in id id  :  ∀ a. a → a
#eval showType (.letIn (some ⟨1, .arrow (.bvar 0) (.bvar 0)⟩)
  (.lambda none (.var 0)) (.app (.var 0) (.var 0)))

-- λx. match x with | _ => 0  :  ∀ a. a → Int   (the all-wildcard / Core-v2 case)
#eval showType (.lambda none (.match_ (.var 0) [(.wildcard, .primLit (.int 0))]))

-- 5 5  :  ill-typed
#eval showType (.app (.primLit (.int 5)) (.primLit (.int 5)))

end Core.Demo
