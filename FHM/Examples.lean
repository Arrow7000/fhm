import FHM.InferW
import FHM.Pretty

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

/-- Run the small-step evaluator (fuel 100) and pretty-print the resulting value
    (`Expr` has no `DecidableEq`, so we compare the printed form in `#guard`s). -/
private def evalStr (e : Expr) : String :=
  match SmallStep.evaluate 100 e with
  | some v => toString v
  | none   => "stuck / out of fuel"

/-! ## A tiny prelude of data types (for the `letRec` demos below)

The `letRec` showcases further down want real recursive data to fold over, so we
need a non-empty `CtorEnv`. `mkCtor` builds a constructor entry, discharging the
`bound`/`closed` side-conditions by decision (`contents` is always a concrete
literal here, so `Ty.bvarsBelow` / `Ty.freeVars` reduce). `demoCtors` then
declares a handful of standard algebraic types:

* `Bool`            — `True`, `False`
* `List a`          — `Nil`, `Cons a (List a)`
* `Peano`           — `Zero`, `Succ Peano`
* `Tree a`/`Forest a` — `Node a (Forest a)`; `FNil`, `FCons (Tree a) (Forest a)`
  (mutually recursive types — the natural home for a mutually recursive map).
* `Seq a`           — `SNil`, `SCons a (Seq (List a))`: a NON-REGULAR (nested)
  type — the recursive occurrence is at `List a`, not `a`. Functions folding a
  `Seq` need *polymorphic recursion* (each call one `List`-layer deeper), which
  is inferable only with an annotation — the mixed-`letRec` showcases below. -/

private def mkCtor (pc : Nat) (tn : TyName) (cs : List Ty)
    (hb : TyList.bvarsBelow pc cs = true := by decide)
    (hc : ∀ ty ∈ cs, ty.freeVars = [] := by decide) : Ctor where
  paramCount := pc
  tyName := tn
  contents := cs
  bound := fun ty h => (Ty.bvarsBelow_iff ty).mp ((TyList.bvarsBelow_iff_forall cs).mp hb ty h)
  closed := fun ty h => Ty.noFreeVars_iff_freeVars_nil.mpr (hc ty h)

private def demoCtors : CtorEnv :=
  [ (⟨"True"⟩,  mkCtor 0 ⟨"Bool"⟩ [])
  , (⟨"False"⟩, mkCtor 0 ⟨"Bool"⟩ [])
  , (⟨"Nil"⟩,   mkCtor 1 ⟨"List"⟩ [])
  , (⟨"Cons"⟩,  mkCtor 1 ⟨"List"⟩ [.bvar 0, .customTy ⟨"List"⟩ [.bvar 0]])
  , (⟨"Zero"⟩,  mkCtor 0 ⟨"Peano"⟩ [])
  , (⟨"Succ"⟩,  mkCtor 0 ⟨"Peano"⟩ [.customTy ⟨"Peano"⟩ []])
  , (⟨"Node"⟩,  mkCtor 1 ⟨"Tree"⟩ [.bvar 0, .customTy ⟨"Forest"⟩ [.bvar 0]])
  , (⟨"FNil"⟩,  mkCtor 1 ⟨"Forest"⟩ [])
  , (⟨"FCons"⟩, mkCtor 1 ⟨"Forest"⟩ [.customTy ⟨"Tree"⟩ [.bvar 0], .customTy ⟨"Forest"⟩ [.bvar 0]])
  , (⟨"SNil"⟩,  mkCtor 1 ⟨"Seq"⟩ [])
  , (⟨"SCons"⟩, mkCtor 1 ⟨"Seq"⟩ [.bvar 0, .customTy ⟨"Seq"⟩ [.customTy ⟨"List"⟩ [.bvar 0]]]) ]

private def typeStrP (e : Expr) : String :=
  match typecheck demoCtors e with
  | none   => "ill-typed"
  | some σ => toString σ

/-- Like `showType`, but type-checks against `demoCtors` so the program may use
    the prelude's constructors and pattern-match on them. -/
private def showTypeP (e : Expr) : IO Unit := IO.println s!"({e})  :  {typeStrP e}"

-- λx. x  :  ∀ a. a → a
#eval showType (.lambda none (.var 0 []))

-- λx. λy. x  :  ∀ a b. b → a → b
#eval showType (.lambda none (.lambda none (.var 1 [])))

-- (λx. x) 5  :  Int
#eval showType (.app (.lambda none (.var 0 [])) (.primLit (.int 5)))

-- λx. λy. x  :  ∀ a b. a → b → a
#eval showType (.lambda none (.lambda none (.var 1 [])))

-- let id : ∀ a. a → a = λx. x in id id  :  ∀ a. a → a
#eval showType (.letIn (some ⟨1, .arrow (.bvar 0) (.bvar 0)⟩)
  (.lambda none (.var 0 [])) (.app (.var 0 []) (.var 0 [])))

-- λx. match x with | _ => 0  :  ∀ a. a → Int   (the all-wildcard / Core-v2 case)
#eval showType (.lambda none (.match_ (.var 0 []) [(.wildcard, .primLit (.int 0))]))

-- 5 5  :  ill-typed
#eval showType (.app (.primLit (.int 5)) (.primLit (.int 5)))


/-! ## Arithmetic primops (`intAdd`, `intSub`)

Primitive binary operators are curried built-in *functions*: a fixed type
`Int → Int → Int`, δ-reduced when saturated on integer literals, and a value
while partially applied. They type against the empty `CtorEnv` (no prelude
needed — the result is a primitive `Int`). -/

-- intAdd  :  Int → Int → Int
#eval showType (.primBinOp .intAdd)
-- intSub  :  Int → Int → Int
#eval showType (.primBinOp .intSub)

-- (λx. intAdd x 1) 41  :  Int   (typechecks)
#eval showType (.app (.lambda none
    (.app (.app (.primBinOp .intAdd) (.var 0 [])) (.primLit (.int 1))))
  (.primLit (.int 41)))
#guard (typecheck [] (.app (.lambda none
    (.app (.app (.primBinOp .intAdd) (.var 0 [])) (.primLit (.int 1))))
  (.primLit (.int 41)))).isSome = true

-- (λx. intAdd x 1) 41  ⟹  42   (β then δ actually computes)
#eval evalStr (.app (.lambda none
    (.app (.app (.primBinOp .intAdd) (.var 0 [])) (.primLit (.int 1))))
  (.primLit (.int 41)))
#guard evalStr (.app (.lambda none
    (.app (.app (.primBinOp .intAdd) (.var 0 [])) (.primLit (.int 1))))
  (.primLit (.int 41))) = "42"

-- intSub 43 1  ⟹  42
#eval evalStr (.app (.app (.primBinOp .intSub) (.primLit (.int 43))) (.primLit (.int 1)))
#guard evalStr (.app (.app (.primBinOp .intSub) (.primLit (.int 43))) (.primLit (.int 1))) = "42"

-- intAdd 41  is a value (partial application), of type  Int → Int
#guard SmallStep.isValue (.app (.primBinOp .intAdd) (.primLit (.int 41))) = true
#eval showType (.app (.primBinOp .intAdd) (.primLit (.int 41)))

-- intAdd ()  :  ill-typed   (a Unit operand is rejected)
#eval showType (.app (.primBinOp .intAdd) (.primLit .unit))
#guard (typecheck [] (.app (.primBinOp .intAdd) (.primLit .unit))).isSome = false


/-! ### The comparison op `intLt` (returns the prelude `Bool`)

`intLt : Int → Int → Bool`. Its δ-rule emits `.ctor "True"/"False"`, so it is
well-typed only relative to an env that provides `Bool` — captured by the two
`.ctor "True"/"False" : Bool` premises of its typing rule. `demoCtors` provides
`Bool`, so it typechecks there; against the empty env it is (correctly) rejected. -/

-- intLt 2 3  :  Bool   (typechecks against `demoCtors`, which provides Bool)
#eval showTypeP (.app (.app (.primBinOp .intLt) (.primLit (.int 2))) (.primLit (.int 3)))
#guard (typecheck demoCtors
  (.app (.app (.primBinOp .intLt) (.primLit (.int 2))) (.primLit (.int 3)))).isSome = true

-- intLt 2 3  ⟹  True   and   intLt 3 2  ⟹  False   (δ emits the Bool ctor)
#guard evalStr (.app (.app (.primBinOp .intLt) (.primLit (.int 2))) (.primLit (.int 3))) = "True"
#guard evalStr (.app (.app (.primBinOp .intLt) (.primLit (.int 3))) (.primLit (.int 2))) = "False"

-- intLt 2 3  :  ill-typed against the EMPTY env — no Bool in scope (conditional soundness)
#eval showType (.app (.app (.primBinOp .intLt) (.primLit (.int 2))) (.primLit (.int 3)))
#guard (typecheck []
  (.app (.app (.primBinOp .intLt) (.primLit (.int 2))) (.primLit (.int 3)))).isSome = false

-- charLt 'a' 'b'  :  Bool  (char ordering by codepoint); 'a' < 'b' ⟹ True, 'b' < 'a' ⟹ False
#eval showTypeP (.app (.app (.primBinOp .charLt) (.primLit (.char 'a'))) (.primLit (.char 'b')))
#guard evalStr (.app (.app (.primBinOp .charLt) (.primLit (.char 'a'))) (.primLit (.char 'b'))) = "True"
#guard evalStr (.app (.app (.primBinOp .charLt) (.primLit (.char 'b'))) (.primLit (.char 'a'))) = "False"
#guard (typecheck demoCtors
  (.app (.app (.primBinOp .charLt) (.primLit (.char 'a'))) (.primLit (.char 'b')))).isSome = true


/-! ## Polymorphic combinators

The classic SKI-zoo. Each is ~7–12 nodes and should print a fully polymorphic
principal scheme. Good sanity that let-free, deeply-curried lambdas infer the
expected types. -/

-- S = λf. λg. λx. f x (g x)  :  ∀ a b c. (b → a → c) → (b → a) → b → c
#eval showType (.lambda none (.lambda none (.lambda none
  (.app (.app (.var 2 []) (.var 0 [])) (.app (.var 1 []) (.var 0 []))))))

-- B = λf. λg. λx. f (g x)  (composition)  :  ∀ a b c. (a → c) → (b → a) → b → c
#eval showType (.lambda none (.lambda none (.lambda none
  (.app (.var 2 []) (.app (.var 1 []) (.var 0 []))))))

-- C = λf. λx. λy. f y x  (flip)  :  ∀ a b c. (b → a → c) → a → b → c
#eval showType (.lambda none (.lambda none (.lambda none
  (.app (.app (.var 2 []) (.var 0 [])) (.var 1 [])))))

-- W = λf. λx. f x x  (diagonal)  :  ∀ a b. (a → a → b) → a → b
#eval showType (.lambda none (.lambda none
  (.app (.app (.var 1 []) (.var 0 [])) (.var 0 []))))

-- twice = λf. λx. f (f x)  :  ∀ a. (a → a) → a → a
#eval showType (.lambda none (.lambda none
  (.app (.var 1 []) (.app (.var 1 []) (.var 0 [])))))


/-! ## Convoluted, but perfectly well-typed

Larger programs that lean hard on let-polymorphism: the same let-bound value is
re-instantiated at several different types. A monomorphic (lambda-bound)
treatment of these binders would reject every one of them. -/

-- twice twice  :  ∀ a. (a → a) → a → a
-- (`twice` instantiated at both `(a → a) → a → a` and `a → a`)
#eval showType (.letIn none
  (.lambda none (.lambda none (.app (.var 1 []) (.app (.var 1 []) (.var 0 [])))))
  (.app (.var 0 []) (.var 0 [])))

-- let k = λx. λy. x in let s = λf. λg. λx. f x (g x) in s k k   :  ∀ a. a → a
-- (S K K η-reduces to the identity — a needlessly indirect way to write λx. x)
#eval showType (.letIn none (.lambda none (.lambda none (.var 1 [])))
  (.letIn none (.lambda none (.lambda none (.lambda none
      (.app (.app (.var 2 []) (.var 0 [])) (.app (.var 1 []) (.var 0 []))))))
    (.app (.app (.var 0 []) (.var 1 [])) (.var 1 []))))

-- let id = λx. x in let const = λx. λy. x in const (id id) (id 5)   :  ∀ a. a → a
-- (`id` used at `(a → a) → a → a`, at `a → a`, and at `Int → Int`, all at once)
#eval showType (.letIn none (.lambda none (.var 0 []))
  (.letIn none (.lambda none (.lambda none (.var 1 [])))
    (.app (.app (.var 0 []) (.app (.var 1 []) (.var 1 [])))
      (.app (.var 1 []) (.primLit (.int 5))))))

-- let f = λx. x in (f (λy. y)) (f 5)   :  Int
-- (`f` instantiated at `(a → a) → (a → a)` to wrap the inner id, and at
--  `Int → Int` to produce the argument — then applied)
#eval showType (.letIn none (.lambda none (.var 0 []))
  (.app (.app (.var 0 []) (.lambda none (.var 0 [])))
    (.app (.var 0 []) (.primLit (.int 5)))))

-- let compose = λf. λg. λx. f (g x) in
--   let twice = λh. compose h h in twice (λn. n)   :  ∀ a. a → a
-- (`compose h h` forces `h`'s domain = codomain; `twice` then needs an
--  endomorphism, supplied here by the identity)
#eval showType (.letIn none
  (.lambda none (.lambda none (.lambda none (.app (.var 2 []) (.app (.var 1 []) (.var 0 []))))))
  (.letIn none (.lambda none (.app (.app (.var 1 []) (.var 0 [])) (.var 0 [])))
    (.app (.var 0 []) (.lambda none (.var 0 [])))))


/-! ## Adversarial: where naïve inferers go wrong

These are the programs that expose the classic landmines — over-eager
generalization, escaping skolems, occurs-check loops, and rigid scoped type
variables. The verified checker should accept exactly the sound ones and reject
the rest. Each rejection below corresponds to a genuinely *untypeable* program
(no `TypeOfElabHM` derivation exists), not merely an algorithmic giving-up. -/

-- λx. x x   :  ill-typed   (occurs check: a = a → b has no finite solution)
#eval showType (.lambda none (.app (.var 0 []) (.var 0 [])))

-- λf. (f (λy. y)) (f 5)   :  ill-typed
-- A lambda-bound `f` is MONOMORPHIC, so it cannot be used at both
-- `(a → a) → (a → a)` and `Int → Int`. Cf. the well-typed `let`-bound version
-- above — moving the binder from λ to let is the whole difference.
#eval showType (.lambda none
  (.app (.app (.var 0 []) (.lambda none (.var 0 [])))
    (.app (.var 0 []) (.primLit (.int 5)))))

-- λf. let a = f 1 in let b = f () in a   :  ill-typed
-- Same point, sharper: `f`'s param can't be both `Int` and `Unit`. The inner
-- `let`s do NOT re-generalize `f` (it's lambda-bound, free in the environment).
#eval showType (.lambda none
  (.letIn none (.app (.var 0 []) (.primLit (.int 1)))
    (.letIn none (.app (.var 1 []) (.primLit .unit))
      (.var 1 []))))

-- let f = λx. x in let a = f 1 in let b = f () in a   :  Int
-- The fix: `f` is now let-bound, so each use instantiates freshly. Accepted.
#eval showType (.letIn none (.lambda none (.var 0 []))
  (.letIn none (.app (.var 0 []) (.primLit (.int 1)))
    (.letIn none (.app (.var 1 []) (.primLit .unit))
      (.var 1 []))))

-- λx. let y = x in y y   :  ill-typed
-- The soundness landmine: `y`'s type = `x`'s type, which is FREE in the
-- environment, so it must NOT be generalized. A buggy generalizer would accept
-- this (giving `y` scheme `∀a. a`) and let `y y` typecheck — unsound.
#eval showType (.lambda none (.letIn none (.var 0 []) (.app (.var 0 []) (.var 0 []))))

-- let y = λx. x in y y   :  ∀ a. a → a
-- The contrast: here `y = λx. x` is a closed value, genuinely generalizable, so
-- `y y` is fine. Same syntax shape as the previous line, opposite verdict.
#eval showType (.letIn none (.lambda none (.var 0 [])) (.app (.var 0 []) (.var 0 [])))

-- let f : ∀ a b. a → b = λx. x in f   :  ill-typed
-- An over-general annotation. `λx. x` is NOT `∀ a b. a → b` (that would be a
-- function from anything to anything). Checking the body against the declared
-- scheme skolemizes `a`, `b` distinct and the unification `a = b` fails.
#eval showType (.letIn (some ⟨2, .arrow (.bvar 0) (.bvar 1)⟩)
  (.lambda none (.var 0 [])) (.var 0 []))

-- λw. let f : ∀ a. a → a = λz. w in f   :  ill-typed
-- The escaping-skolem classic. To accept `λz. w : a → a` (for the freshly
-- skolemized `a`) we'd have to set `w`'s type to `a` — but `w` lives in the
-- OUTER scope, so the skolem `a` would escape the `let`. Correctly rejected.
#eval showType (.lambda none
  (.letIn (some ⟨1, .arrow (.bvar 0) (.bvar 0)⟩) (.lambda none (.var 1 [])) (.var 0 [])))

-- λw. let f : ∀ a. a → a = λx. x in f w   :  ∀ a. a → a
-- The legitimate sibling: the binding really is the polymorphic identity, so the
-- annotation holds with no escape; `f` is then instantiated at `w`'s type.
#eval showType (.lambda none
  (.letIn (some ⟨1, .arrow (.bvar 0) (.bvar 0)⟩) (.lambda none (.var 0 []))
    (.app (.var 0 []) (.var 1 []))))

-- λ(x : ?a). x   :  ∀ a. a → a
-- A free type variable in an annotation is a RIGID scoped constant during
-- inference (à la ScopedTypeVariables). Here it just rides through to the result
-- and is generalized at the top, so the scheme is the ordinary identity.
#eval showType (.lambda (some (.fvar 0)) (.var 0 []))

-- (λ(x : ?a). x) 5   :  ill-typed
-- The awkward bit: because `?a` is rigid (not a fresh unification var), forcing
-- `?a = Int` is forbidden — the scoped variable cannot be specialized here. So
-- this is rejected even though `λx. x` applied to `5` (unannotated) is fine.
#eval showType (.app (.lambda (some (.fvar 0)) (.var 0 [])) (.primLit (.int 5)))

-- λx. match x with | _ => 0 | _ => ()   :  ill-typed
-- All branches of a match must agree: `Int` (first) vs `Unit` (second) clash.
#eval showType (.lambda none (.match_ (.var 0 [])
  [(.wildcard, .primLit (.int 0)), (.wildcard, .primLit .unit)]))

-- λx. match x with | _ => λy. y   :  ∀ a b. a → b → b
-- A wildcard match imposes no shape on the scrutinee (Core-v2), so `x` stays
-- fully polymorphic and the branch body contributes its own `∀`.
#eval showType (.lambda none (.match_ (.var 0 []) [(.wildcard, .lambda none (.var 0 []))]))


/-! ## Recursion (`letRec`)

Recursive binding groups. `n = 1` is self-recursion (coincides with `fix`); `n > 1`
is mutual recursion, now typed at genuinely polymorphic, *shared* types. The earlier
disjoint-slice rule under-typed mutual groups (it severed the cross-binding sharing);
the shared-monotype rule infers their principal types. -/

-- let rec f = λx. x in f  :  ∀ a. a → a
-- (a non-recursive binding placed in a letRec — still sound, generalised as usual)
#eval showType (.letRec [none] [.lambda none (.var 0 [])] (.var 0 []))

-- let rec f = λx. f x in f  :  ∀ a b. a → b
-- (genuine self-recursion: `f` calls itself; the loop is well-typed, productive `f`
--  would need a productive body — here the type is the most general fixpoint shape)
#eval showType (.letRec [none] [.lambda none (.app (.var 1 []) (.var 0 []))] (.var 0 []))

-- let rec f = g and g = f in f  :  ∀ a. a
-- (mutual recursion: `f`/`g` share one polymorphic type — the exact program the
--  disjoint-slice predecessor could NOT type polymorphically)
#eval showType (.letRec [none, none] [.var 1 [], .var 0 []] (.var 0 []))

-- let rec f = λx. g x and g = λx. f x in f  :  ∀ a b. a → b
-- (mutual deferral: `f` and `g` share their `a → b` shape across the group)
#eval showType (.letRec [none, none]
  [.lambda none (.app (.var 2 []) (.var 0 [])), .lambda none (.app (.var 1 []) (.var 0 []))]
  (.var 0 []))


/-! ### Recursion over real data

The genuine article: self-recursive folds over an inductive type, defined with a
single-binding `letRec` (`n = 1`, i.e. `fix`) and driven by a `match`. These type
against `demoCtors` (so `showTypeP`), and each recursive call re-uses the binding
at its *own* monotype — exactly the monomorphic recursion `letRec` provides. -/

-- let rec length = λxs. match xs with                         ∀ a. List a → Peano
--                        | Nil      => Zero
--                        | Cons h t => Succ (length t)
-- in length
-- (`t : List a` recurses, the result is a `Peano`; `length` generalises to be
--  polymorphic in the element type `a` once the group is closed)
#eval showTypeP (.letRec [none]
  [.lambda none (.match_ (.var 0 [])
    [ (.named (.mk "Nil") 0, .ctor (.mk "Zero"))
    , (.named (.mk "Cons") 2, .app (.ctor (.mk "Succ")) (.app (.var 3 []) (.var 1 []))) ])]
  (.var 0 []))

-- let rec map = λf. λxs. match xs with             ∀ a b. (a → b) → List a → List b
--                          | Nil      => Nil
--                          | Cons h t => Cons (f h) (map f t)
-- in map
-- (the headline example: a polymorphic recursive function. The recursive `map f t`
--  pins `map` at its shared monotype inside the group; the body then sees the fully
--  generalised `∀ a b. (a → b) → List a → List b`)
#eval showTypeP (.letRec [none]
  [.lambda none (.lambda none (.match_ (.var 0 [])
    [ (.named (.mk "Nil") 0, .ctor (.mk "Nil"))
    , (.named (.mk "Cons") 2,
        .app (.app (.ctor (.mk "Cons")) (.app (.var 3 []) (.var 0 [])))
          (.app (.app (.var 4 []) (.var 3 [])) (.var 1 []))) ]))]
  (.var 0 []))


/-! ### Mutual recursion over real data

Now `n > 1`: two (or more) bindings that call *each other*. This is precisely the
shape the disjoint-slice predecessor mis-typed — here the group's shared monotypes
keep `even`/`odd` (and `mapTree`/`mapForest`) linked, and each binding is then
generalised independently for the body. -/

-- let rec even = λn. match n with | Zero => True  | Succ m => odd m       Peano → Bool
--     and odd  = λn. match n with | Zero => False | Succ m => even m
-- in even
-- (the textbook mutual recursion: `even` calls `odd` and vice versa; the body
--  returns `even`. Both share the monotype `Peano → Bool` across the group)
#eval showTypeP (.letRec [none, none]
  [ .lambda none (.match_ (.var 0 [])
      [ (.named (.mk "Zero") 0, .ctor (.mk "True"))
      , (.named (.mk "Succ") 1, .app (.var 3 []) (.var 0 [])) ])
  , .lambda none (.match_ (.var 0 [])
      [ (.named (.mk "Zero") 0, .ctor (.mk "False"))
      , (.named (.mk "Succ") 1, .app (.var 2 []) (.var 0 [])) ]) ]
  (.var 0 []))

-- let rec mapTree   = λf. λt.  match t with                            (the complex one)
--                                | Node x ts => Node (f x) (mapForest f ts)
--     and mapForest = λf. λts. match ts with
--                                | FNil        => FNil
--                                | FCons hd tl => FCons (mapTree f hd) (mapForest f tl)
-- in mapTree                                          ∀ a b. (a → b) → Tree a → Tree b
-- (mutual recursion mirroring mutually-recursive *data* (`Tree`/`Forest`). The whole
--  group shares the single `(a → b)` and a single element-type pair `a`/`b` — the
--  exact polymorphic cross-binding sharing the old rule severed)
#eval showTypeP (.letRec [none, none]
  [ .lambda none (.lambda none (.match_ (.var 0 [])
      [ (.named (.mk "Node") 2,
          .app (.app (.ctor (.mk "Node")) (.app (.var 3 []) (.var 0 [])))
            (.app (.app (.var 5 []) (.var 3 [])) (.var 1 []))) ]))
  , .lambda none (.lambda none (.match_ (.var 0 [])
      [ (.named (.mk "FNil") 0, .ctor (.mk "FNil"))
      , (.named (.mk "FCons") 2,
          .app (.app (.ctor (.mk "FCons")) (.app (.app (.var 4 []) (.var 3 [])) (.var 0 [])))
            (.app (.app (.var 5 []) (.var 3 [])) (.var 1 []))) ])) ]
  (.var 0 []))


/-! ### Body generalisation (the `letRec` analogue of `let y = λx. x in y y`)

Inside the group every binding is monomorphic, but the *body* sees each binding
generalised. So a polymorphic self-application in the body must be accepted. -/

-- let rec id = λx. x in id id   :  ∀ a. a → a
-- (`id id` forces the body's `id` to be used at two types at once — only typeable
--  because the body generalises the group binding to `∀ a. a → a`. A checker that
--  forgot to generalise the body would reject this)
#eval showType (.letRec [none] [.lambda none (.var 0 [])] (.app (.var 0 []) (.var 0 [])))


/-! ### Annotated polymorphic recursion referencing an OUTER scoped type variable

The witness for nested annotated-recursion support: an annotated `letRec` member
whose scheme body mentions a type variable bound by an *enclosing* scope. Here the
group binding `loop`'s annotation `a → a` refers to the outer `let`'s `∀ a`, i.e. a
`bvar` past `loop`'s own (zero) parameters. This was previously *rejected* —
`open`/`close` didn't descend into stored recursion-annotation scheme bodies, so the
outer `bvar` never resolved and failed `PolyTy.WF`; the elaborator now opens it to
the enclosing skolem and closes it back, so the whole thing infers `∀ a. a → a`. -/

-- let (g : ∀ a. a → a) = (let rec (loop : a → a) = λy. loop y in loop) in g   :  ∀ a. a → a
#eval showType (.letIn (some ⟨1, .arrow (.bvar 0) (.bvar 0)⟩)
  (.letRec [some ⟨0, .arrow (.bvar 0) (.bvar 0)⟩]
     [.lambda none (.app (.var 1 []) (.var 0 []))]
     (.var 0 []))
  (.var 0 []))


/-! ### Mixed annotated/unannotated recursion (the fused rule end-to-end)

The fused `letRec` node carries per-binding `Option PolyTy` annotations, so ONE
group can mix both regimes: annotated members are checked at their declared
schemes (polymorphic recursion allowed), unannotated members at shared monotypes
that are generalised only for the body. These witnesses are ported from the
retired `SpikeLetRecMixed.lean`, upgraded from declarative derivations to
executable `typecheck` runs. -/

/-- `∀a. a → a`. -/
private def selfSig : PolyTy := ⟨1, .arrow (.bvar 0) (.bvar 0)⟩

/-- `f`'s RHS: `λx. let _ = f () in x` — the recursive call instantiates `f`'s
    OWN scheme at `unit`: polymorphic recursion (needs the annotated regime). -/
private def fRhs : Expr :=
  .lambda none (.letIn none (.app (.var 1 []) (.primLit .unit)) (.var 1 []))

/-- `g`'s RHS: `λx. f x` — the unannotated member instantiates the annotated
    sibling at `g`'s own shared pool variable. -/
private def gRhs : Expr := .lambda none (.app (.var 1 []) (.var 0 []))

-- let rec (f : ∀ a. a → a) = λx. let _ = f () in x
--     and g                = λx. f x
-- in g 0   :   Int
-- (the mixed POSITIVE witness: `f` poly-recurses at `unit` while being checked at
--  a fresh skolem — the annotated regime; `g` cross-calls `f` at its own shared
--  monotype and is generalised for the body — the unannotated regime. Neither
--  regime alone types this program.)
#eval showType (.letRec [some selfSig, none] [fRhs, gRhs]
  (.app (.var 1 []) (.primLit (.int 0))))
#guard (typecheck [] (.letRec [some selfSig, none] [fRhs, gRhs]
  (.app (.var 1 []) (.primLit (.int 0))))).isSome = true

-- …and the SAME program's all-unannotated reading is REJECTED (the recursive call
-- `f ()` pins `f`'s monotype to `unit → unit`, so the body's `g 0` fails): the
-- mixed witness genuinely needs BOTH regimes at once.
#guard (typecheck [] (.letRec [none, none] [fRhs, gRhs]
  (.app (.var 1 []) (.primLit (.int 0))))).isSome = false

-- let rec (f : ∀ a. a → a) = λx. g x and g = λx. f x in f   :   ill-typed
-- (the skolem-leak NEGATIVE witness: checking `f` at a fresh skolem `Y` of its
--  scheme forces the unannotated sibling's shared monotype to be `Y → Y` — but
--  the shared monotypes are fixed OUTSIDE the per-binding skolem quantifier, so
--  the annotation variable cannot leak into the pool. Correctly rejected.)
#eval showType (.letRec [some selfSig, none]
  [.lambda none (.app (.var 2 []) (.var 0 [])), .lambda none (.app (.var 1 []) (.var 0 []))]
  (.var 0 []))
#guard (typecheck [] (.letRec [some selfSig, none]
  [.lambda none (.app (.var 2 []) (.var 0 [])), .lambda none (.app (.var 1 []) (.var 0 []))]
  (.var 0 []))).isSome = false


/-! ### Pushing the fused rule: nested data, three-member mixed groups

The heavy-duty showcases. `Seq a` is NON-REGULAR (`SCons a (Seq (List a))`), so
any fold over it must call itself one `List`-layer deeper — *polymorphic
recursion*, which is undecidable to infer and only typeable through an
annotation. Mixing that annotated member with plain unannotated helpers in ONE
group is exactly what the fused rule buys us. -/

/-- `slen`'s declared scheme: `∀ a. Seq a → Peano`. -/
private def slenSig : PolyTy :=
  ⟨1, .arrow (.customTy ⟨"Seq"⟩ [.bvar 0]) (.customTy ⟨"Peano"⟩ [])⟩

/-- `λs. match s with | SNil => Zero | SCons x xs => bump (slen xs)`.
    `xs : Seq (List a)`, so the recursive call instantiates `slen`'s OWN scheme
    at `List a` — genuine polymorphic recursion over a nested type — and feeds
    the result to the UNANNOTATED sibling `bump` (at the concrete `Peano`,
    which is what makes the cross-boundary use legal). -/
private def slenRhs : Expr :=
  .lambda none (.match_ (.var 0 [])
    [ (.named ⟨"SNil"⟩ 0, .ctor ⟨"Zero"⟩)
    , (.named ⟨"SCons"⟩ 2, .app (.var 4 []) (.app (.var 3 []) (.var 1 []))) ])

/-- `λn. Succ n` — the unannotated helper. -/
private def bumpRhs : Expr := .lambda none (.app (.ctor ⟨"Succ"⟩) (.var 0 []))

-- let rec (slen : ∀ a. Seq a → Peano) = λs. match s with
--                                             | SNil       => Zero
--                                             | SCons x xs => bump (slen xs)
--     and bump                        = λn. Succ n
-- in slen   :   ∀ a. Seq a → Peano
-- (polymorphic recursion over a NESTED datatype, mixed with an unannotated
--  helper the annotated member calls — neither regime alone types this)
#eval showTypeP (.letRec [some slenSig, none] [slenRhs, bumpRhs] (.var 0 []))
#guard (typecheck demoCtors
  (.letRec [some slenSig, none] [slenRhs, bumpRhs] (.var 0 []))).isSome = true

-- …and WITHOUT the annotation the same program is REJECTED: monomorphic `slen`
-- forces `a = List a` at the recursive call (no finite type). Poly-recursion
-- over non-regular data is exactly what annotations exist to unlock.
#eval showTypeP (.letRec [none, none] [slenRhs, bumpRhs] (.var 0 []))
#guard (typecheck demoCtors
  (.letRec [none, none] [slenRhs, bumpRhs] (.var 0 []))).isSome = false

/-! A THREE-member mixed group exercising everything at once: an annotated
member that polymorphically recurses at a concrete type, an unannotated member
that instantiates the annotated sibling AT ITS OWN POOL VARIABLE, a second
unannotated member self-recursing over `Forest` with its OWN pool slice (the
per-binding `genFilter` slicing of one shared pool), and a body composing the
generalised members. -/

-- let rec (poly : ∀ a. a → a) = λx. let _ = poly Zero in x     (poly-rec at Peano)
--     and dup   = λt. FCons (poly t) (FCons t FNil)            (uses poly at pool var)
--     and sizeF = λts. match ts with | FNil       => Zero      (own pool slice)
--                                    | FCons h tl => Succ (sizeF tl)
-- in λt. sizeF (dup t)   :   ∀ a. Tree a → Peano
#eval showTypeP (.letRec [some selfSig, none, none]
  [ .lambda none (.letIn none (.app (.var 1 []) (.ctor ⟨"Zero"⟩)) (.var 1 []))
  , .lambda none (.app (.app (.ctor ⟨"FCons"⟩) (.app (.var 1 []) (.var 0 [])))
      (.app (.app (.ctor ⟨"FCons"⟩) (.var 0 [])) (.ctor ⟨"FNil"⟩)))
  , .lambda none (.match_ (.var 0 [])
      [ (.named ⟨"FNil"⟩ 0, .ctor ⟨"Zero"⟩)
      , (.named ⟨"FCons"⟩ 2, .app (.ctor ⟨"Succ"⟩) (.app (.var 5 []) (.var 1 []))) ]) ]
  (.lambda none (.app (.var 3 []) (.app (.var 2 []) (.var 0 [])))))
#guard (typecheck demoCtors (.letRec [some selfSig, none, none]
  [ .lambda none (.letIn none (.app (.var 1 []) (.ctor ⟨"Zero"⟩)) (.var 1 []))
  , .lambda none (.app (.app (.ctor ⟨"FCons"⟩) (.app (.var 1 []) (.var 0 [])))
      (.app (.app (.ctor ⟨"FCons"⟩) (.var 0 [])) (.ctor ⟨"FNil"⟩)))
  , .lambda none (.match_ (.var 0 [])
      [ (.named ⟨"FNil"⟩ 0, .ctor ⟨"Zero"⟩)
      , (.named ⟨"FCons"⟩ 2, .app (.ctor ⟨"Succ"⟩) (.app (.var 5 []) (.var 1 []))) ]) ]
  (.lambda none (.app (.var 3 []) (.app (.var 2 []) (.var 0 [])))))).isSome = true

/-! Mono-visibility, documented: annotating `f` does NOT unlock polymorphic use
of its unannotated sibling `h` *inside the group* — `h` is monomorphic there
(same contract as an ordinary unannotated `let` binding inside its own RHS).
Annotate `h` too and the same program is accepted. -/

/-- `λx. let _ = h 0 in let _ = h () in x` — uses the sibling at `Int` AND `Unit`. -/
private def fUsesHTwice : Expr :=
  .lambda none (.letIn none (.app (.var 2 []) (.primLit (.int 0)))
    (.letIn none (.app (.var 3 []) (.primLit .unit)) (.var 2 [])))

-- let rec (f : ∀ a. a → a) = λx. let _ = h 0 in let _ = h () in x
--     and h = λy. y
-- in f   :   ill-typed   (h is mono inside the group: Int vs Unit clash)
#eval showType (.letRec [some selfSig, none]
  [fUsesHTwice, .lambda none (.var 0 [])] (.var 0 []))
#guard (typecheck [] (.letRec [some selfSig, none]
  [fUsesHTwice, .lambda none (.var 0 [])] (.var 0 []))).isSome = false

-- …annotate `h` as well and it is accepted: both members now live in the
-- polymorphic regime.   :   ∀ a. a → a
#eval showType (.letRec [some selfSig, some selfSig]
  [fUsesHTwice, .lambda none (.var 0 [])] (.var 0 []))
#guard (typecheck [] (.letRec [some selfSig, some selfSig]
  [fUsesHTwice, .lambda none (.var 0 [])] (.var 0 []))).isSome = true


/-! ### Adversarial: where `letRec` is *supposed* to say no

Monomorphic recursion is the whole point: a binding is NOT generalised *within its
own group*. These are the programs whose acceptance would mean we'd silently slipped
into unsound polymorphic recursion (or an occurs-check loop). All correctly rejected. -/

-- let rec f = λx. let a = f 0 in let b = f () in x in f   :  ill-typed
-- (polymorphic recursion: `f` is used at both `Int → _` and `Unit → _` inside its own
--  group, where it is monomorphic. HM (rightly) refuses — no annotation, no poly-rec)
#eval showType (.letRec [none]
  [.lambda none
    (.letIn none (.app (.var 1 []) (.primLit (.int 0)))
      (.letIn none (.app (.var 2 []) (.primLit .unit))
        (.var 2 [])))]
  (.var 0 []))

-- let rec f = f f in f   :  ill-typed
-- (self-application under recursion: `f`'s monotype `a` must equal `a → b`. Occurs
--  check fails — the recursive binding cannot paper over a non-finite type)
#eval showType (.letRec [none] [.app (.var 0 []) (.var 0 [])] (.var 0 []))

-- let rec id = λx. x and bad = λu. let a = id 0 in id () in bad   :  ill-typed
-- (the soundness landmine: `bad` uses the *group-bound* `id` at `Int` and `Unit`.
--  Because `id` is monomorphic inside the group, the two uses clash. Contrast the
--  next example, where moving `id` to a plain `let` makes it generalise — accepted)
#eval showType (.letRec [none, none]
  [ .lambda none (.var 0 [])
  , .lambda none (.letIn none (.app (.var 1 []) (.primLit (.int 0)))
      (.app (.var 2 []) (.primLit .unit))) ]
  (.var 1 []))

-- let id = λx. x in let bad = λu. let a = id 0 in id () in bad   :  ∀ a. a → Unit
-- (the well-typed sibling: `id` is now `let`-bound, hence generalised before `bad`
--  uses it, so `id 0` and `id ()` each instantiate it freshly. Same body, opposite
--  verdict — `let` vs `letRec` is the entire difference)
#eval showType (.letIn none (.lambda none (.var 0 []))
  (.letIn none
    (.lambda none (.letIn none (.app (.var 1 []) (.primLit (.int 0)))
      (.app (.var 2 []) (.primLit .unit))))
    (.var 0 [])))

end Core.Demo
