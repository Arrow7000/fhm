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


/-! ## Polymorphic combinators

The classic SKI-zoo. Each is ~7–12 nodes and should print a fully polymorphic
principal scheme. Good sanity that let-free, deeply-curried lambdas infer the
expected types. -/

-- S = λf. λg. λx. f x (g x)  :  ∀ a b c. (b → a → c) → (b → a) → b → c
#eval showType (.lambda none (.lambda none (.lambda none
  (.app (.app (.var 2) (.var 0)) (.app (.var 1) (.var 0))))))

-- B = λf. λg. λx. f (g x)  (composition)  :  ∀ a b c. (a → c) → (b → a) → b → c
#eval showType (.lambda none (.lambda none (.lambda none
  (.app (.var 2) (.app (.var 1) (.var 0))))))

-- C = λf. λx. λy. f y x  (flip)  :  ∀ a b c. (b → a → c) → a → b → c
#eval showType (.lambda none (.lambda none (.lambda none
  (.app (.app (.var 2) (.var 0)) (.var 1)))))

-- W = λf. λx. f x x  (diagonal)  :  ∀ a b. (a → a → b) → a → b
#eval showType (.lambda none (.lambda none
  (.app (.app (.var 1) (.var 0)) (.var 0))))

-- twice = λf. λx. f (f x)  :  ∀ a. (a → a) → a → a
#eval showType (.lambda none (.lambda none
  (.app (.var 1) (.app (.var 1) (.var 0)))))


/-! ## Convoluted, but perfectly well-typed

Larger programs that lean hard on let-polymorphism: the same let-bound value is
re-instantiated at several different types. A monomorphic (lambda-bound)
treatment of these binders would reject every one of them. -/

-- twice twice  :  ∀ a. (a → a) → a → a
-- (`twice` instantiated at both `(a → a) → a → a` and `a → a`)
#eval showType (.letIn none
  (.lambda none (.lambda none (.app (.var 1) (.app (.var 1) (.var 0)))))
  (.app (.var 0) (.var 0)))

-- let k = λx. λy. x in let s = λf. λg. λx. f x (g x) in s k k   :  ∀ a. a → a
-- (S K K η-reduces to the identity — a needlessly indirect way to write λx. x)
#eval showType (.letIn none (.lambda none (.lambda none (.var 1)))
  (.letIn none (.lambda none (.lambda none (.lambda none
      (.app (.app (.var 2) (.var 0)) (.app (.var 1) (.var 0))))))
    (.app (.app (.var 0) (.var 1)) (.var 1))))

-- let id = λx. x in let const = λx. λy. x in const (id id) (id 5)   :  ∀ a. a → a
-- (`id` used at `(a → a) → a → a`, at `a → a`, and at `Int → Int`, all at once)
#eval showType (.letIn none (.lambda none (.var 0))
  (.letIn none (.lambda none (.lambda none (.var 1)))
    (.app (.app (.var 0) (.app (.var 1) (.var 1)))
      (.app (.var 1) (.primLit (.int 5))))))

-- let f = λx. x in (f (λy. y)) (f 5)   :  Int
-- (`f` instantiated at `(a → a) → (a → a)` to wrap the inner id, and at
--  `Int → Int` to produce the argument — then applied)
#eval showType (.letIn none (.lambda none (.var 0))
  (.app (.app (.var 0) (.lambda none (.var 0)))
    (.app (.var 0) (.primLit (.int 5)))))

-- let compose = λf. λg. λx. f (g x) in
--   let twice = λh. compose h h in twice (λn. n)   :  ∀ a. a → a
-- (`compose h h` forces `h`'s domain = codomain; `twice` then needs an
--  endomorphism, supplied here by the identity)
#eval showType (.letIn none
  (.lambda none (.lambda none (.lambda none (.app (.var 2) (.app (.var 1) (.var 0))))))
  (.letIn none (.lambda none (.app (.app (.var 1) (.var 0)) (.var 0)))
    (.app (.var 0) (.lambda none (.var 0)))))


/-! ## Adversarial: where naïve inferers go wrong

These are the programs that expose the classic landmines — over-eager
generalization, escaping skolems, occurs-check loops, and rigid scoped type
variables. The verified checker should accept exactly the sound ones and reject
the rest. Each rejection below corresponds to a genuinely *untypeable* program
(no `TypeOfHM` derivation exists), not merely an algorithmic giving-up. -/

-- λx. x x   :  ill-typed   (occurs check: a = a → b has no finite solution)
#eval showType (.lambda none (.app (.var 0) (.var 0)))

-- λf. (f (λy. y)) (f 5)   :  ill-typed
-- A lambda-bound `f` is MONOMORPHIC, so it cannot be used at both
-- `(a → a) → (a → a)` and `Int → Int`. Cf. the well-typed `let`-bound version
-- above — moving the binder from λ to let is the whole difference.
#eval showType (.lambda none
  (.app (.app (.var 0) (.lambda none (.var 0)))
    (.app (.var 0) (.primLit (.int 5)))))

-- λf. let a = f 1 in let b = f () in a   :  ill-typed
-- Same point, sharper: `f`'s param can't be both `Int` and `Unit`. The inner
-- `let`s do NOT re-generalize `f` (it's lambda-bound, free in the environment).
#eval showType (.lambda none
  (.letIn none (.app (.var 0) (.primLit (.int 1)))
    (.letIn none (.app (.var 1) (.primLit .unit))
      (.var 1))))

-- let f = λx. x in let a = f 1 in let b = f () in a   :  Int
-- The fix: `f` is now let-bound, so each use instantiates freshly. Accepted.
#eval showType (.letIn none (.lambda none (.var 0))
  (.letIn none (.app (.var 0) (.primLit (.int 1)))
    (.letIn none (.app (.var 1) (.primLit .unit))
      (.var 1))))

-- λx. let y = x in y y   :  ill-typed
-- The soundness landmine: `y`'s type = `x`'s type, which is FREE in the
-- environment, so it must NOT be generalized. A buggy generalizer would accept
-- this (giving `y` scheme `∀a. a`) and let `y y` typecheck — unsound.
#eval showType (.lambda none (.letIn none (.var 0) (.app (.var 0) (.var 0))))

-- let y = λx. x in y y   :  ∀ a. a → a
-- The contrast: here `y = λx. x` is a closed value, genuinely generalizable, so
-- `y y` is fine. Same syntax shape as the previous line, opposite verdict.
#eval showType (.letIn none (.lambda none (.var 0)) (.app (.var 0) (.var 0)))

-- let f : ∀ a b. a → b = λx. x in f   :  ill-typed
-- An over-general annotation. `λx. x` is NOT `∀ a b. a → b` (that would be a
-- function from anything to anything). Checking the body against the declared
-- scheme skolemizes `a`, `b` distinct and the unification `a = b` fails.
#eval showType (.letIn (some ⟨2, .arrow (.bvar 0) (.bvar 1)⟩)
  (.lambda none (.var 0)) (.var 0))

-- λw. let f : ∀ a. a → a = λz. w in f   :  ill-typed
-- The escaping-skolem classic. To accept `λz. w : a → a` (for the freshly
-- skolemized `a`) we'd have to set `w`'s type to `a` — but `w` lives in the
-- OUTER scope, so the skolem `a` would escape the `let`. Correctly rejected.
#eval showType (.lambda none
  (.letIn (some ⟨1, .arrow (.bvar 0) (.bvar 0)⟩) (.lambda none (.var 1)) (.var 0)))

-- λw. let f : ∀ a. a → a = λx. x in f w   :  ∀ a. a → a
-- The legitimate sibling: the binding really is the polymorphic identity, so the
-- annotation holds with no escape; `f` is then instantiated at `w`'s type.
#eval showType (.lambda none
  (.letIn (some ⟨1, .arrow (.bvar 0) (.bvar 0)⟩) (.lambda none (.var 0))
    (.app (.var 0) (.var 1))))

-- λ(x : ?a). x   :  ∀ a. a → a
-- A free type variable in an annotation is a RIGID scoped constant during
-- inference (à la ScopedTypeVariables). Here it just rides through to the result
-- and is generalized at the top, so the scheme is the ordinary identity.
#eval showType (.lambda (some (.fvar 0)) (.var 0))

-- (λ(x : ?a). x) 5   :  ill-typed
-- The awkward bit: because `?a` is rigid (not a fresh unification var), forcing
-- `?a = Int` is forbidden — the scoped variable cannot be specialized here. So
-- this is rejected even though `λx. x` applied to `5` (unannotated) is fine.
#eval showType (.app (.lambda (some (.fvar 0)) (.var 0)) (.primLit (.int 5)))

-- λx. match x with | _ => 0 | _ => ()   :  ill-typed
-- All branches of a match must agree: `Int` (first) vs `Unit` (second) clash.
#eval showType (.lambda none (.match_ (.var 0)
  [(.wildcard, .primLit (.int 0)), (.wildcard, .primLit .unit)]))

-- λx. match x with | _ => λy. y   :  ∀ a b. a → b → b
-- A wildcard match imposes no shape on the scrutinee (Core-v2), so `x` stays
-- fully polymorphic and the branch body contributes its own `∀`.
#eval showType (.lambda none (.match_ (.var 0) [(.wildcard, .lambda none (.var 0))]))


/-! ## Recursion (`letRec`)

Recursive binding groups. `n = 1` is self-recursion (coincides with `fix`); `n > 1`
is mutual recursion, now typed at genuinely polymorphic, *shared* types. The earlier
disjoint-slice rule under-typed mutual groups (it severed the cross-binding sharing);
the shared-monotype rule infers their principal types. -/

-- let rec f = λx. x in f  :  ∀ a. a → a
-- (a non-recursive binding placed in a letRec — still sound, generalised as usual)
#eval showType (.letRec [.lambda none (.var 0)] (.var 0))

-- let rec f = λx. f x in f  :  ∀ a b. a → b
-- (genuine self-recursion: `f` calls itself; the loop is well-typed, productive `f`
--  would need a productive body — here the type is the most general fixpoint shape)
#eval showType (.letRec [.lambda none (.app (.var 1) (.var 0))] (.var 0))

-- let rec f = g and g = f in f  :  ∀ a. a
-- (mutual recursion: `f`/`g` share one polymorphic type — the exact program the
--  disjoint-slice predecessor could NOT type polymorphically)
#eval showType (.letRec [.var 1, .var 0] (.var 0))

-- let rec f = λx. g x and g = λx. f x in f  :  ∀ a b. a → b
-- (mutual deferral: `f` and `g` share their `a → b` shape across the group)
#eval showType (.letRec
  [.lambda none (.app (.var 2) (.var 0)), .lambda none (.app (.var 1) (.var 0))]
  (.var 0))

end Core.Demo
