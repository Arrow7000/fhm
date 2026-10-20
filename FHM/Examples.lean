import FHM.Pretty
import FHM.SurfaceBridge
import FHM.InferW

/-! # End-to-end demos

Run the verified inferer on a Core program and pretty-print its principal type.
`checkCore [] e` returns the principal scheme (`Option PolyTy`); we render both
the program and the inferred type with the `Pretty` printers. -/

/-- Hand-built Core uses the same elaborating engine as authored Input. -/
private def checkCore (ctors : CtorEnv) (expr : Expr) : Option PolyTy :=
  typecheck ctors (InferInput.ofCore expr)

namespace Core.Demo

private def typeStr (e : Expr) : String :=
  match checkCore [] e with
  | none   => "ill-typed"
  | some σ => toString σ

private def showType (e : Expr) : IO Unit := IO.println s!"({e})  :  {typeStr e}"

/-- Run the small-step evaluator (fuel 100) and pretty-print the resulting value
    (`Expr` has no `DecidableEq`, so we compare the printed form in `#guard`s). -/
private def evalStr (e : Expr) : String :=
  match inferWithTypes ((elabDecls preludeDecls).getD []) (InferInput.ofCore e) with
  | none => "ill-typed"
  | some result =>
    match SmallStep.evaluate 100 result.completedExpr.erase with
    | some v => toString v
    | none => "stuck / out of fuel"

/-! ## A tiny prelude of data types (for the `letRec` demos below)

The `letRec` showcases further down want real recursive data to fold over, so we
need a non-empty `CtorEnv`. Rather than hand-build the `Ctor`s, we declare the
group as `demoDecls : List DataDecl` and run the *verified* `elabDecls`
elaborator (`FHM.Decls`) — it kind-checks every field, enforces name
distinctness, and discharges each `Ctor`'s `bound`/`closed` obligations from the
successful check. `demoCtors` is then just the elaborated env, and the `#guard`
below witnesses that the whole declaration pipeline succeeds. The group declares
a handful of standard algebraic types:

* `Bool`            — `True`, `False`
* `List a`          — `Nil`, `Cons a (List a)`
* `Peano`           — `Zero`, `Succ Peano`
* `Tree a`/`Forest a` — `Node a (Forest a)`; `FNil`, `FCons (Tree a) (Forest a)`
  (mutually recursive types — the natural home for a mutually recursive map).
* `Seq a`           — `SNil`, `SCons a (Seq (List a))`: a NON-REGULAR (nested)
  type. Its natural fold needs polymorphic recursion and therefore distinguishes
  rejected unsigned recursion from recursion checked against a complete contract. -/

/-- The demo declaration group, in `DataDecl` form (one entry per type, its
    constructors bundled). Fed to the verified `elabDecls` to produce `demoCtors`. -/
private def demoDecls : List DataDecl :=
  [ { name := ⟨"Bool"⟩, paramCount := 0,
      ctors := [(⟨"True"⟩, []), (⟨"False"⟩, [])] }
  , { name := ⟨"List"⟩, paramCount := 1,
      ctors := [(⟨"Nil"⟩, []), (⟨"Cons"⟩, [.bvar 0, .customTy ⟨"List"⟩ [.bvar 0]])] }
  , { name := ⟨"Peano"⟩, paramCount := 0,
      ctors := [(⟨"Zero"⟩, []), (⟨"Succ"⟩, [.customTy ⟨"Peano"⟩ []])] }
  , { name := ⟨"Tree"⟩, paramCount := 1,
      ctors := [(⟨"Node"⟩, [.bvar 0, .customTy ⟨"Forest"⟩ [.bvar 0]])] }
  , { name := ⟨"Forest"⟩, paramCount := 1,
      ctors := [ (⟨"FNil"⟩, [])
               , (⟨"FCons"⟩, [.customTy ⟨"Tree"⟩ [.bvar 0], .customTy ⟨"Forest"⟩ [.bvar 0]]) ] }
  , { name := ⟨"Seq"⟩, paramCount := 1,
      ctors := [ (⟨"SNil"⟩, [])
               , (⟨"SCons"⟩, [.bvar 0, .customTy ⟨"Seq"⟩ [.customTy ⟨"List"⟩ [.bvar 0]]]) ] } ]

/-- The demo constructor env, produced end-to-end by the verified elaborator. -/
private def demoCtors : CtorEnv := (elabDecls demoDecls).getD []

-- The whole declaration group kind-checks and elaborates (if this fails, a
-- `DataDecl` above doesn't match its intended `Ctor`).
#guard (elabDecls demoDecls).isSome

private def typeStrP (e : Expr) : String :=
  match checkCore demoCtors e with
  | none   => "ill-typed"
  | some σ => toString σ

/-- Like `showType`, but type-checks against `demoCtors` so the program may use
    the prelude's constructors and pattern-match on them. -/
private def showTypeP (e : Expr) : IO Unit := IO.println s!"({e})  :  {typeStrP e}"

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
    (.app (.app (.primBinOp .intAdd) (.var 0)) (.primLit (.int 1))))
  (.primLit (.int 41)))
#guard (checkCore [] (.app (.lambda none
    (.app (.app (.primBinOp .intAdd) (.var 0)) (.primLit (.int 1))))
  (.primLit (.int 41)))).isSome = true

-- (λx. intAdd x 1) 41  ⟹  42   (β then δ actually computes)
#eval evalStr (.app (.lambda none
    (.app (.app (.primBinOp .intAdd) (.var 0)) (.primLit (.int 1))))
  (.primLit (.int 41)))
#guard evalStr (.app (.lambda none
    (.app (.app (.primBinOp .intAdd) (.var 0)) (.primLit (.int 1))))
  (.primLit (.int 41))) = "42"

-- intSub 43 1  ⟹  42
#eval evalStr (.app (.app (.primBinOp .intSub) (.primLit (.int 43))) (.primLit (.int 1)))
#guard evalStr (.app (.app (.primBinOp .intSub) (.primLit (.int 43))) (.primLit (.int 1))) = "42"

-- intAdd 41  is a value (partial application), of type  Int → Int
#guard SmallStep.isValue (.app (.primBinOp .intAdd) (.primLit (.int 41))) = true
#eval showType (.app (.primBinOp .intAdd) (.primLit (.int 41)))

-- intAdd ()  :  ill-typed   (a Unit operand is rejected)
#eval showType (.app (.primBinOp .intAdd) (.primLit .unit))
#guard (checkCore [] (.app (.primBinOp .intAdd) (.primLit .unit))).isSome = false


/-! ### The comparison op `intLt` (returns the prelude `Bool`)

`intLt : Int → Int → Bool`. Its δ-rule emits `.ctor "True"/"False"`, so it is
well-typed only relative to an env that provides `Bool` — captured by the two
`.ctor "True"/"False" : Bool` premises of its typing rule. `demoCtors` provides
`Bool`, so it typechecks there; against the empty env it is (correctly) rejected. -/

-- intLt 2 3  :  Bool   (typechecks against `demoCtors`, which provides Bool)
#eval showTypeP (.app (.app (.primBinOp .intLt) (.primLit (.int 2))) (.primLit (.int 3)))
#guard (checkCore demoCtors
  (.app (.app (.primBinOp .intLt) (.primLit (.int 2))) (.primLit (.int 3)))).isSome = true

-- intLt 2 3  ⟹  True   and   intLt 3 2  ⟹  False   (δ emits the Bool ctor)
#guard evalStr (.app (.app (.primBinOp .intLt) (.primLit (.int 2))) (.primLit (.int 3))) = "True"
#guard evalStr (.app (.app (.primBinOp .intLt) (.primLit (.int 3))) (.primLit (.int 2))) = "False"

-- intLt 2 3  :  ill-typed against the EMPTY env — no Bool in scope (conditional soundness)
#eval showType (.app (.app (.primBinOp .intLt) (.primLit (.int 2))) (.primLit (.int 3)))
#guard (checkCore []
  (.app (.app (.primBinOp .intLt) (.primLit (.int 2))) (.primLit (.int 3)))).isSome = false

-- charLt 'a' 'b'  :  Bool  (char ordering by codepoint); 'a' < 'b' ⟹ True, 'b' < 'a' ⟹ False
#eval showTypeP (.app (.app (.primBinOp .charLt) (.primLit (.char 'a'))) (.primLit (.char 'b')))
#guard evalStr (.app (.app (.primBinOp .charLt) (.primLit (.char 'a'))) (.primLit (.char 'b'))) = "True"
#guard evalStr (.app (.app (.primBinOp .charLt) (.primLit (.char 'b'))) (.primLit (.char 'a'))) = "False"
#guard (checkCore demoCtors
  (.app (.app (.primBinOp .charLt) (.primLit (.char 'a'))) (.primLit (.char 'b')))).isSome = true


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
(no `TypeOfHM` derivation exists for the source), not merely an
algorithmic giving-up. -/

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
-- this (giving `y` scheme `∀a. a`) and let `y y` checkCore — unsound.
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
is mutual recursion. Unannotated members share monotypes while their sub-group is
inferred, then are generalized. A completely annotated member is instead checked
at its declared scheme after those inferred schemes have been fixed. -/

-- let rec f = λx. x in f  :  ∀ a. a → a
-- (a non-recursive binding placed in a letRec — still sound, generalised as usual)
#eval showType (.letRec [none] [.lambda none (.var 0)] (.var 0))

-- let rec f = λx. f x in f  :  ∀ a b. a → b
-- (genuine self-recursion: `f` calls itself; the loop is well-typed, productive `f`
--  would need a productive body — here the type is the most general fixpoint shape)
#eval showType (.letRec [none] [.lambda none (.app (.var 1) (.var 0))] (.var 0))

-- let rec f = g and g = f in f  :  ∀ a. a
-- (mutual recursion: `f` and `g` share one monotype in the group, which is
--  generalized for the body)
#eval showType (.letRec [none, none] [.var 1, .var 0] (.var 0))

-- let rec f = λx. g x and g = λx. f x in f  :  ∀ a b. a → b
-- (mutual deferral: `f` and `g` share their `a → b` shape across the group)
#eval showType (.letRec [none, none]
  [.lambda none (.app (.var 2) (.var 0)), .lambda none (.app (.var 1) (.var 0))]
  (.var 0))


/-! ### Recursive annotation contracts

A complete annotation is the contract at which a recursive RHS is checked. The
check may refine flexible variables from the surrounding inference context, but
it may not bind source-rigid variables. In a mixed group, unsigned siblings are
inferred and generalized first, so checking a signed RHS cannot consume their
generalisation variables. -/

/-- A recursive `Int` annotation refines the enclosing lambda parameter's
    flexible inference variable. -/
private def recAnnRefinesOuter : Expr :=
  .lambda none (.letRec [some ⟨0, .prim .int⟩] [.var 1] (.var 0))

#guard match checkCore [] recAnnRefinesOuter with
  | some ⟨0, .arrow (.prim .int) (.prim .int)⟩ => true
  | _ => false

/-- A less-general monomorphic contract is a valid type at which to check the
    otherwise polymorphic identity. -/
private def recAnnSpecialisesIdentity : Expr :=
  .letRec [some ⟨0, .arrow (.prim .int) (.prim .int)⟩]
    [.lambda none (.var 0)] (.var 0)

#guard match checkCore [] recAnnSpecialisesIdentity with
  | some ⟨0, .arrow (.prim .int) (.prim .int)⟩ => true
  | _ => false

/-- `1` has only type `Int`, so it cannot justify the declared `∀a. a`. -/
private def recAnnOverclaims : Expr :=
  .letRec [some ⟨1, .bvar 0⟩] [.primLit (.int 1)] (.var 0)

#guard (checkCore [] recAnnOverclaims).isNone

/-- A free variable written in an annotation is source-rigid, not an inference
    metavariable which contract checking may solve. -/
private def recAnnCannotSolveRigid : Expr :=
  .letRec [some ⟨0, .fvar 7⟩] [.primLit (.int 1)] (.var 0)

#guard (checkCore [] recAnnCannotSolveRigid).isNone

/-- Checking annotated `f` cannot consume `g`'s generalisation variable: `g`
    has already been inferred and generalized, so the body can instantiate it
    at both `Int` and `Char`. -/
private def recAnnKeepsSiblingPolymorphic : Expr :=
  .letRec [some ⟨0, .arrow (.prim .int) (.prim .int)⟩, none]
    [.lambda none (.var 0), .lambda none (.var 0)]
    (.letIn none (.app (.var 1) (.primLit (.int 1)))
      (.app (.var 2) (.primLit (.char 'c'))))

#guard match checkCore [] recAnnKeepsSiblingPolymorphic with
  | some ⟨0, .prim .char⟩ => true
  | _ => false


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
  [.lambda none (.match_ (.var 0)
    [ (.named (.mk "Nil") 0, .ctor (.mk "Zero"))
    , (.named (.mk "Cons") 2, .app (.ctor (.mk "Succ")) (.app (.var 3) (.var 1))) ])]
  (.var 0))

-- let rec map = λf. λxs. match xs with             ∀ a b. (a → b) → List a → List b
--                          | Nil      => Nil
--                          | Cons h t => Cons (f h) (map f t)
-- in map
-- (`map` recurses monomorphically inside the group; the body then sees the fully
--  generalized `∀ a b. (a → b) → List a → List b`)
#eval showTypeP (.letRec [none]
  [.lambda none (.lambda none (.match_ (.var 0)
    [ (.named (.mk "Nil") 0, .ctor (.mk "Nil"))
    , (.named (.mk "Cons") 2,
        .app (.app (.ctor (.mk "Cons")) (.app (.var 3) (.var 0)))
          (.app (.app (.var 4) (.var 3)) (.var 1))) ]))]
  (.var 0))


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
  [ .lambda none (.match_ (.var 0)
      [ (.named (.mk "Zero") 0, .ctor (.mk "True"))
      , (.named (.mk "Succ") 1, .app (.var 3) (.var 0)) ])
  , .lambda none (.match_ (.var 0)
      [ (.named (.mk "Zero") 0, .ctor (.mk "False"))
      , (.named (.mk "Succ") 1, .app (.var 2) (.var 0)) ]) ]
  (.var 0))

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
  [ .lambda none (.lambda none (.match_ (.var 0)
      [ (.named (.mk "Node") 2,
          .app (.app (.ctor (.mk "Node")) (.app (.var 3) (.var 0)))
            (.app (.app (.var 5) (.var 3)) (.var 1))) ]))
  , .lambda none (.lambda none (.match_ (.var 0)
      [ (.named (.mk "FNil") 0, .ctor (.mk "FNil"))
      , (.named (.mk "FCons") 2,
          .app (.app (.ctor (.mk "FCons")) (.app (.app (.var 4) (.var 3)) (.var 0)))
            (.app (.app (.var 5) (.var 3)) (.var 1))) ])) ]
  (.var 0))


/-! ### Body generalisation (the `letRec` analogue of `let y = λx. x in y y`)

An unsigned binding is monomorphic while its recursive sub-group is inferred, but
the *body* sees it generalised. So a polymorphic self-application in the body must
be accepted. -/

-- let rec id = λx. x in id id   :  ∀ a. a → a
-- (`id id` forces the body's `id` to be used at two types at once — only typeable
--  because the body generalises the group binding to `∀ a. a → a`. A checker that
--  forgot to generalise the body would reject this)
#eval showType (.letRec [none] [.lambda none (.var 0)] (.app (.var 0) (.var 0)))


/-! ### A recursive annotation referencing an outer scoped type variable

This witnesses nested annotated-recursion support: an annotated `letRec` member
whose scheme body mentions a type variable bound by an *enclosing* scope. Here the
group binding `loop`'s annotation `a → a` refers to the outer `let`'s `∀ a`, i.e. a
`bvar` past `loop`'s own (zero) parameters. This was previously *rejected* —
`open`/`close` didn't descend into stored recursion-annotation scheme bodies, so the
outer `bvar` never resolved and failed `PolyTy.WF`; inference now opens it to
the enclosing skolem and closes it back, so the whole thing infers `∀ a. a → a`. -/

-- let (g : ∀ a. a → a) = (let rec (loop : a → a) = λy. loop y in loop) in g   :  ∀ a. a → a
#eval showType (.letIn (some ⟨1, .arrow (.bvar 0) (.bvar 0)⟩)
  (.letRec [some ⟨0, .arrow (.bvar 0) (.bvar 0)⟩]
     [.lambda none (.app (.var 1) (.var 0))]
     (.var 0))
  (.var 0))


/-! ### Mixed annotated/unannotated recursion

The `letRec` node carries per-binding optional annotations, so one group can mix
annotated and inferred members. A complete annotation makes that member available
at its declared scheme and cuts the residual type-dependency graph. Unannotated
members share ordinary HM monotypes within each residual SCC; SCCs are inferred and
generalized dependency-first. Their final schemes are available while annotated
RHSs and the group body are checked. -/

/-- `∀a. a → a`. -/
private def selfSig : PolyTy := ⟨1, .arrow (.bvar 0) (.bvar 0)⟩

/-- `f`'s RHS uses annotated `f` at `Unit` inside its own SCC. -/
private def fRhs : Expr :=
  .lambda none (.letIn none (.app (.var 1) (.primLit .unit)) (.var 1))

/-- `g`'s RHS: `λx. f x` — the unannotated member instantiates the annotated
    sibling at `g`'s own shared pool variable. -/
private def gRhs : Expr := .lambda none (.app (.var 1) (.var 0))

-- let rec (f : ∀ a. a → a) = λx. let _ = f () in x
--     and g                = λx. f x
-- in g 0   :   Int
-- `f` is checked against its complete scheme and may instantiate itself at
-- `Unit`; `g` independently instantiates the same declared scheme at `Int`.
#eval showType (.letRec [some selfSig, none] [fRhs, gRhs]
  (.app (.var 1) (.primLit (.int 0))))
#guard (checkCore [] (.letRec [some selfSig, none] [fRhs, gRhs]
  (.app (.var 1) (.primLit (.int 0))))).isSome = true

-- …and the SAME program's all-unannotated reading is REJECTED (the recursive call
-- `f ()` pins `f`'s monotype to `unit → unit`, so the body's `g 0` fails): the
-- mixed witness genuinely needs BOTH regimes at once.
#guard (checkCore [] (.letRec [none, none] [fRhs, gRhs]
  (.app (.var 1) (.primLit (.int 0))))).isSome = false

-- let rec (f : ∀ a. a → a) = λx. g x and g = λx. f x in f
-- The complete contract for `f` is assumed while `g` is inferred and generalized;
-- `f` is then checked with that final scheme for `g`. Thus adding `f`'s principal
-- annotation does not make this ordinary HM cycle fail.
#eval showType (.letRec [some selfSig, none]
  [.lambda none (.app (.var 2) (.var 0)), .lambda none (.app (.var 1) (.var 0))]
  (.var 0))
#guard (checkCore [] (.letRec [some selfSig, none]
  [.lambda none (.app (.var 2) (.var 0)), .lambda none (.app (.var 1) (.var 0))]
  (.var 0))).isSome = true

-- Giving the sibling its own complete scheme makes both directions explicitly
-- polymorphic, so the same recursive cycle is accepted.
#guard (checkCore [] (.letRec [some selfSig, some selfSig]
  [.lambda none (.app (.var 2) (.var 0)), .lambda none (.app (.var 1) (.var 0))]
  (.var 0))).isSome = true


/-! ### Annotated polymorphic recursion over non-regular data

`Seq a` is non-regular (`SCons a (Seq (List a))`), so its natural fold calls
itself one `List` layer deeper. That requires in-group polymorphic recursion,
which is accepted exactly when the recursive binding has a complete annotation. -/

/-- `slen`'s declared scheme: `∀ a. Seq a → Peano`. -/
private def slenSig : PolyTy :=
  ⟨1, .arrow (.customTy ⟨"Seq"⟩ [.bvar 0]) (.customTy ⟨"Peano"⟩ [])⟩

/-- `λs. match s with | SNil => Zero | SCons x xs => bump (slen xs)`.
    `xs : Seq (List a)`, so the recursive call instantiates `slen`'s OWN scheme
    at `List a` — genuine polymorphic recursion over a nested type — and feeds
    the result to the unannotated sibling `bump`. The latter is inferred and
    generalized before this annotated RHS is checked. -/
private def slenRhs : Expr :=
  .lambda none (.match_ (.var 0)
    [ (.named ⟨"SNil"⟩ 0, .ctor ⟨"Zero"⟩)
    , (.named ⟨"SCons"⟩ 2, .app (.var 4) (.app (.var 3) (.var 1))) ])

/-- `λn. Succ n` — the unannotated helper. -/
private def bumpRhs : Expr := .lambda none (.app (.ctor ⟨"Succ"⟩) (.var 0))

-- let rec (slen : ∀ a. Seq a → Peano) = λs. match s with
--                                             | SNil       => Zero
--                                             | SCons x xs => bump (slen xs)
--     and bump                        = λn. Succ n
-- in slen   :   ∀ a. Seq a → Peano
-- (polymorphic recursion over a NESTED datatype: the recursive call `slen xs`
--  instantiates `slen` at `List a`; the complete annotation enables this
--  deliberate in-group polymorphic recursion.)
#eval showTypeP (.letRec [some slenSig, none] [slenRhs, bumpRhs] (.var 0))
#guard (checkCore demoCtors
  (.letRec [some slenSig, none] [slenRhs, bumpRhs] (.var 0))).isSome = true

-- …and WITHOUT the annotation the same program is REJECTED: monomorphic `slen`
-- forces `a = List a` at the recursive call (no finite type). Adding an
-- annotation is what unlocks polymorphic recursion, as the previous guard shows.
#eval showTypeP (.letRec [none, none] [slenRhs, bumpRhs] (.var 0))
#guard (checkCore demoCtors
  (.letRec [none, none] [slenRhs, bumpRhs] (.var 0))).isSome = false

/-! A three-member mixed positive example: one annotated member recurses
polymorphically, another instantiates it at a different in-group type, and a third
recurses monomorphically over `Forest`. -/

-- let rec (poly : ∀ a. a → a) = λx. let _ = poly Zero in x     (poly-rec at Peano)
--     and dup   = λt. FCons (poly t) (FCons t FNil)            (uses poly at pool var)
--     and sizeF = λts. match ts with | FNil       => Zero      (own pool slice)
--                                    | FCons h tl => Succ (sizeF tl)
-- in λt. sizeF (dup t)   :   ∀ a. Tree a → Peano
-- (`poly`'s complete annotation permits the `Peano` self-call and `dup`'s
--  independent instantiation, while `sizeF` remains ordinary monomorphic recursion.)
#eval showTypeP (.letRec [some selfSig, none, none]
  [ .lambda none (.letIn none (.app (.var 1) (.ctor ⟨"Zero"⟩)) (.var 1))
  , .lambda none (.app (.app (.ctor ⟨"FCons"⟩) (.app (.var 1) (.var 0)))
      (.app (.app (.ctor ⟨"FCons"⟩) (.var 0)) (.ctor ⟨"FNil"⟩)))
  , .lambda none (.match_ (.var 0)
      [ (.named ⟨"FNil"⟩ 0, .ctor ⟨"Zero"⟩)
      , (.named ⟨"FCons"⟩ 2, .app (.ctor ⟨"Succ"⟩) (.app (.var 5) (.var 1))) ]) ]
  (.lambda none (.app (.var 3) (.app (.var 2) (.var 0)))))
#guard (checkCore demoCtors (.letRec [some selfSig, none, none]
  [ .lambda none (.letIn none (.app (.var 1) (.ctor ⟨"Zero"⟩)) (.var 1))
  , .lambda none (.app (.app (.ctor ⟨"FCons"⟩) (.app (.var 1) (.var 0)))
      (.app (.app (.ctor ⟨"FCons"⟩) (.var 0)) (.ctor ⟨"FNil"⟩)))
  , .lambda none (.match_ (.var 0)
      [ (.named ⟨"FNil"⟩ 0, .ctor ⟨"Zero"⟩)
      , (.named ⟨"FCons"⟩ 2, .app (.ctor ⟨"Succ"⟩) (.app (.var 5) (.var 1))) ]) ]
  (.lambda none (.app (.var 3) (.app (.var 2) (.var 0)))))).isSome = true

/-! Complete contracts also cut dependencies in the other direction. An unsigned
sibling is inferred monomorphically, then generalized before signed RHSs are checked;
an annotated member may therefore use that inferred sibling polymorphically. -/

/-- `λx. let _ = h 0 in let _ = h () in x` — uses the sibling at `Int` AND `Unit`. -/
private def fUsesHTwice : Expr :=
  .lambda none (.letIn none (.app (.var 2) (.primLit (.int 0)))
    (.letIn none (.app (.var 3) (.primLit .unit)) (.var 2)))

-- let rec (f : ∀ a. a → a) = λx. let _ = h 0 in let _ = h () in x
--     and h = λy. y
-- in f
-- `h` is inferred as the identity and generalized before `f` is checked, so its
-- `Int` and `Unit` uses are independent instantiations.
#eval showType (.letRec [some selfSig, none]
  [fUsesHTwice, .lambda none (.var 0)] (.var 0))
#guard (checkCore [] (.letRec [some selfSig, none]
  [fUsesHTwice, .lambda none (.var 0)] (.var 0))).isSome = true

-- Giving `h` its own complete annotation is equivalent at this boundary.
#eval showType (.letRec [some selfSig, some selfSig]
  [fUsesHTwice, .lambda none (.var 0)] (.var 0))
#guard (checkCore [] (.letRec [some selfSig, some selfSig]
  [fUsesHTwice, .lambda none (.var 0)] (.var 0))).isSome = true


/-! ### Adversarial: where `letRec` is *supposed* to say no

Unsigned bindings are not generalized within their own recursive component. The
first two programs require unsupported polymorphic recursion or an infinite
type and are rejected. The last two show generalization between components
and through ordinary `let`. -/

-- let rec f = λx. let a = f 0 in let b = f () in x in f   :  ill-typed
-- (polymorphic recursion: `f` is used at both `Int → _` and `Unit → _` inside its own
--  group, where it is monomorphic. A complete annotation would opt this member
--  into checked polymorphic recursion.)
#eval showType (.letRec [none]
  [.lambda none
    (.letIn none (.app (.var 1) (.primLit (.int 0)))
      (.letIn none (.app (.var 2) (.primLit .unit))
        (.var 2)))]
  (.var 0))

-- let rec f = f f in f   :  ill-typed
-- (self-application under recursion: `f`'s monotype `a` must equal `a → b`. Occurs
--  check fails — the recursive binding cannot paper over a non-finite type)
#eval showType (.letRec [none] [.app (.var 0) (.var 0)] (.var 0))

-- let rec id = λx. x and bad = λu. let a = id 0 in id () in bad   :  ∀ a. a → Unit
-- (`id` does not depend on `bad`, so dependency analysis places it in an earlier
--  component and generalizes it before `bad` uses it at `Int` and `Unit`.)
#eval showType (.letRec [none, none]
  [ .lambda none (.var 0)
  , .lambda none (.letIn none (.app (.var 1) (.primLit (.int 0)))
      (.app (.var 2) (.primLit .unit))) ]
  (.var 1))

-- let id = λx. x in let bad = λu. let a = id 0 in id () in bad   :  ∀ a. a → Unit
-- (ordinary `let` also generalizes `id` before `bad` uses it, so both forms
--  instantiate `id` freshly at each call and infer the same result.)
#eval showType (.letIn none (.lambda none (.var 0))
  (.letIn none
    (.lambda none (.letIn none (.app (.var 1) (.primLit (.int 0)))
      (.app (.var 2) (.primLit .unit))))
    (.var 0)))

end Core.Demo

/-! # Surface → Core → eval demos

The Core section above feeds **hand-built Core** into `checkCore` / `evaluate`.
This section runs the **front-end pipeline**: `Surface.Program` →
`lowerProgram` (decls + SCC desugar + `lower`) → `Input.ofCore` →
canonical inference → completed output erasure → `evaluate`.

Prints use `ToString` on the surface term (same shape as Core demos).
`#guard`s assert `.isSome` / printed eval results directly — no opaque matches.

Compound lambda parameters lower through pattern compilation and must pass
coverage before evaluation.
-/

namespace SurfacePipelineDemo

open SurfaceBridge

private def evalStr (e : _root_.Expr) : String :=
  match SmallStep.evaluate 100 e with
  | some v => toString v
  | none   => "stuck / out of fuel"

/-- Lower, erase, then evaluate a surface program; print surface term ⟹ result. -/
private def evalProgram (p : Surface.Program) : String :=
  match lowerProgram p with
  | none => "lower failed"
  | some (ctors, c) =>
    match inferWithTypes ctors (InferInput.ofCore c) with
    | none => "ill-typed"
    | some result => evalStr result.completedExpr.erase

private def showEval (p : Surface.Program) : IO Unit :=
  IO.println s!"({p.term})  ⟹  {evalProgram p}"

-- if true then 1 else 0  ⟹  1
private def sIf : Surface.Program :=
  ⟨[], [], .ife (.primLit (.bool true)) (.primLit (.int 1)) (.primLit (.int 0))⟩
#eval showEval sIf
#guard (lowerProgram sIf).isSome = true
#guard evalProgram sIf = "1"

-- match Just 5 with Just x => x | Nothing => 0  ⟹  5
private def sMaybeMatch : Surface.Program :=
  ⟨[⟨.mk "Maybe", [.mk "a"],
      [(.mk "Just", [.tvar (.mk "a")]), (.mk "Nothing", [])]⟩],
   [],
   .match_ (.app (.ctor ⟨"Just"⟩) (.primLit (.int 5)))
     [(.ctor ⟨"Just"⟩ [.name ⟨"x"⟩], .var ⟨"x"⟩),
      (.ctor ⟨"Nothing"⟩ [], .primLit (.int 0))]⟩
#eval showEval sMaybeMatch
#guard (lowerProgram sMaybeMatch).isSome = true
#guard evalProgram sMaybeMatch = "5"
#guard (lowerProgram sMaybeMatch).isSome = true
private def sMaybeMatchCtors : CtorEnv :=
  (lowerProgram sMaybeMatch).map Prod.fst |>.getD []
#guard checkExhaustive sMaybeMatchCtors sMaybeMatch.term = true

-- let id = λx. x in id 7  ⟹  7   (`Program.ofFlat`)
private def sIdApp : Surface.Program :=
  match Program.ofFlat []
      [{ name := .mk "id", ann := none,
         rhs := .lambda (.name (.mk "x")) none (.var (.mk "x")) }]
      (.app (.var (.mk "id")) (.primLit (.int 7))) with
  | some p => p
  | none => ⟨[], [], .primLit (.unit)⟩
#eval showEval sIdApp
#guard (lowerProgram sIdApp).isSome = true
#guard evalProgram sIdApp = "7"

-- let id : ∀ a. a → a = λx. x in id 41  ⟹  41
private def sAnnId : Surface.Program :=
  ⟨[], [],
   .letIn (.mk "id") [] []
     (some ⟨[.mk "a"], .arrow (.tvar (.mk "a")) (.tvar (.mk "a"))⟩)
     (.lambda (.name (.mk "x")) none (.var (.mk "x")))
     (.app (.var (.mk "id")) (.primLit (.int 41)))⟩
#eval showEval sAnnId
#guard (lowerProgram sAnnId).isSome = true
#guard evalProgram sAnnId = "41"

-- A refutable parameter lowers, but fails coverage.
private def sPatternLam : Surface.Expr :=
  .lambda (.ctor ⟨"Just"⟩ [.name ⟨"x"⟩]) none (.var (.mk "x"))
#guard (lower ((elabDecls preludeDecls).getD []) sPatternLam).isSome = true
#guard checkExhaustive ((elabDecls preludeDecls).getD []) sPatternLam = false


private def sNestedPatternLam : Surface.Program :=
  ⟨[], [], .app
    (.lambda (.pair (.pair (.name ⟨"a"⟩) (.name ⟨"b"⟩)) (.name ⟨"c"⟩)) none
      (.var ⟨"b"⟩))
    (.pair (.pair (.primLit (.int 1)) (.primLit (.bool true))) (.primLit (.int 3)))⟩
#guard (lowerProgram sNestedPatternLam).isSome
#guard evalProgram sNestedPatternLam = "True"
#guard checkExhaustive ((elabDecls preludeDecls).getD []) sNestedPatternLam.term

example : SurfaceCovers ((elabDecls preludeDecls).getD []) sNestedPatternLam.term :=
  checkExhaustive_sound _ (by native_decide)


-- Pattern bindings are built entirely from ordinary lets and singleton matches.
-- Each projected function is generalised independently by the existing checker.
private def sPatternLet : Surface.Program :=
  let pat := Surface.Pattern.pair (.name ⟨"id"⟩) (.name ⟨"n"⟩)
  let rhs := Surface.Expr.pair
    (.lambda (.name ⟨"x"⟩) none (.var ⟨"x"⟩)) (.primLit (.int 7))
  let binds := Surface.patternBindings ⟨"$pattern/demo"⟩ pat rhs
  ⟨[], binds.map (fun b => [b]), .pair
    (.app (.var ⟨"id"⟩) (.var ⟨"n"⟩))
    (.app (.var ⟨"id"⟩) (.primLit (.bool true)))⟩
#guard evalProgram sPatternLet = "(7, True)"
#guard (match lowerProgram sPatternLet with
  | some (ctors, c) => (checkCore ctors c).isSome
  | none => false)
example : SurfaceCovers ((elabDecls preludeDecls).getD []) sPatternLet.term :=
  checkExhaustive_sound _ (by native_decide)

end SurfacePipelineDemo


namespace AuditCapstone

/-- Complete Core uses the canonical engine through a syntax adapter. -/
private def corePrincipalType (ctors : CtorEnv) (expr : Expr) : Option Ty :=
  principalType ctors (InferInput.ofCore expr)

/-! ### A typeable program — all three headlines fire -/

/-- `λx. x`. -/
def polyId : Expr := .lambda none (.var 0)

theorem polyId_typeable : TypeOfHM ⟨[], []⟩ polyId (.arrow (.fvar 0) (.fvar 0)) :=
  TypeOfHM.lambda .fvar (fun _ h => Option.noConfusion h) rfl
    (TypeOfHM.var (instArgs := []) rfl (by intro t ht; cases ht) .fvar)

/-! ### Headline demos keep EXACT principality (`τ₀ = R.onTy τ`)

Unlike the general theorems above, the four `*_headlines_fire` demos are stated
with exact equality and that is **correct, not an oversight**. Their computed
types are all-variable (`polyId` ⇒ `.fvar 0 → .fvar 0`), so every declarative
result is a genuine substitution instance.

Consequence for the farm: these four do **not** depend on the completeness engine.
Like `appFiveFive_untypeable`, each is a direct inversion of `TypeOfHM` on a
closed, tiny term — `polyId`'s inversion gives `τ₀ = paramTy → paramTy`, so
`R = [(0, paramTy)]`. Prove them standalone and early; do not block them on
`complete'`. -/

/-! #### Shared machinery for the four demos

Two ingredients recur.

* **Computing the principal type.** `inferWithTypesCore`/`unifyCoreK`/… are well-founded
  recursions, so the small non-recursive examples are proved by unfolding their
  equation lemmas with `simp only [inferWithTypesCore, …]` and then discharging the
  residual arithmetic/matching with `with_unfolding_all rfl`.  The mutual-`letRec`
  worker additionally carries dependent proof certificates through its sequential
  group worker; its concrete witness uses `native_decide` only for a Boolean
  *shape* projection, followed by ordinary constructor inversion to recover the
  propositional equality.  It does not install a `DecidableEq Ty` or compare the
  proof-carrying worker result itself.

* **Inverting the derivation.** Each demo's principal type is all-variable (plus,
  for `matchWild`, a rigid `Int`), so ordinary `cases` inversion on `TypeOfHM`
  pins `τ₀`'s shape exactly and the witness substitution reads off directly. The
  only supporting lemma needed is that instantiation is trivial on a
  locally-closed body. -/

/-- Instantiation is the identity on a locally-closed type: this is the converse
    of `InstantiatesBy.refl_of_closed`, and it is what turns a `lambda`'s
    `paramTy.IsLC` premise into "the bound variable's use has type `paramTy`". -/
theorem instBy_eq_of_lc {tyArgs : List Ty} :
    ∀ {ty : Ty}, ty.IsLC → ∀ (τ : Ty), InstantiatesBy tyArgs ty τ → τ = ty := by
  intro ty
  induction ty using Ty.rec_strong with
  | prim p => intro _ τ h; cases h; rfl
  | arrow a b iha ihb =>
      intro hlc τ h
      cases hlc with
      | arrow ha hb => cases h with | arrow h1 h2 => rw [iha ha _ h1, ihb hb _ h2]
  | bvar n => intro hlc τ h; cases hlc with | bvar hlt => omega
  | fvar n => intro _ τ h; cases h; rfl
  | customTy nm tys ih =>
      intro hlc τ h
      cases hlc with
      | customTy hall =>
        cases h with
        | customTy hf =>
          refine congrArg _ ?_
          have aux : ∀ (ts is : List Ty), (∀ t ∈ ts, t.IsLC) →
              (∀ t ∈ ts, ∀ u, InstantiatesBy tyArgs t u → u = t) →
              List.Forall₂ (InstantiatesBy tyArgs) ts is → is = ts := by
            intro ts
            induction ts with
            | nil => intro is _ _ hff; cases hff; rfl
            | cons hd tl iht =>
              intro is hall' ih' hff
              cases hff with
              | cons hhd htl =>
                rw [iht _ (fun t ht => hall' t (List.mem_cons_of_mem _ ht))
                      (fun t ht => ih' t (List.mem_cons_of_mem _ ht)) htl,
                    ih' hd (List.mem_cons_self ..) _ hhd]
          exact aux tys _ hall (fun t ht => ih t ht (hall t ht)) hf

set_option maxRecDepth 100_000 in
/-- `λx. x` has principal monotype `α → α` (computed, not postulated). -/
theorem polyId_principalType : corePrincipalType [] polyId = some (.arrow (.fvar 0) (.fvar 0)) := by
  change (inferCore [] 0 ⟨[], []⟩ (.lambda none (.var 0))).map (·.val.2.2.2) = _
  simp [inferCore, inferWithTypesCore, seed, InferInput.rigidVars,
    softVars, TyList.freeVars, Env.freeVars, Ty.freeVars, List.getElem?_cons_zero,
    PolyTy.mkTrivial, PolyTy.openVars, Ty.openVars, freshVars, Subst.onTy, Ty.substFvars]
  rfl

/-- `SurfaceBridge.coreTypecheck` succeeds, produces a genuine declarative type, and that type is
    principal. -/
theorem polyId_headlines_fire :
    ∃ σ τ, SurfaceBridge.coreTypecheck [] polyId = some σ ∧ σ = genScheme [] [] τ ∧
      TypeOfHM ⟨[], []⟩ polyId τ ∧
      ∀ τ₀, TypeOfHM ⟨[], []⟩ polyId τ₀ → ∃ R : Subst, τ₀ = R.onTy τ := by
  refine ⟨genScheme [] [] (.arrow (.fvar 0) (.fvar 0)), .arrow (.fvar 0) (.fvar 0),
    ?_, rfl, ?_, ?_⟩
  · show (corePrincipalType [] polyId).map (genScheme [] []) = _
    rw [polyId_principalType]; rfl
  · exact polyId_typeable
  ·
    intro τ₀ h
    -- Inversion: `λx. x`'s only derivations are `paramTy → paramTy`.
    cases h with
    | lambda hlc hpins heq hbody =>
      subst heq
      cases hbody with
      | var hlook hargs hinst =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hlook
        subst hlook
        have hb := instBy_eq_of_lc hlc _ hinst
        subst hb
        exact ⟨[(0, _)], rfl⟩

/-! ### An ill-typed program — completeness's contrapositive is not vacuous -/

/-- `5 5` — applying a non-function. -/
def appFiveFive : Expr := .app (.primLit (.int 5)) (.primLit (.int 5))

theorem appFiveFive_untypeable : ¬ ∃ τ, TypeOfHM ⟨[], []⟩ appFiveFive.erase τ := by
  rintro ⟨τ, h⟩
  simp [Expr.erase, appFiveFive] at h
  cases h with
  | app hf hx =>
    cases hf

/-- The algorithm rejects `5 5`: if `SurfaceBridge.coreTypecheck` succeeded, `SurfaceBridge.coreTypecheck_sound`
    would give a declarative
    typing of the erased term — contradicting `appFiveFive_untypeable`. -/
theorem appFiveFive_rejected : ¬ (SurfaceBridge.coreTypecheck [] appFiveFive).isSome := by
  intro hs
  obtain ⟨ty,ht⟩ := SurfaceBridge.coreTypecheck_accepts_iff.mp hs
  cases ht with
  | app hf _ => cases hf

/-! ### Open programs: a free top-level annotation variable is rigid -/

/-- `λ(x : α). x`, with `α` free at the top level. -/
def openId : Expr := .lambda (some (.fvar 5)) (.var 0)

/-- Accepted, and sound: `α` is rigid, so the only declarative type is `α → α`. -/
theorem openId_typeable : TypeOfHM ⟨[], []⟩ openId (.arrow (.fvar 5) (.fvar 5)) :=
  TypeOfHM.lambda .fvar (fun _ h => by cases h; rfl) rfl
    (TypeOfHM.var (instArgs := []) rfl (by intro t ht; cases ht) .fvar)

/-- `(λ(x : α). x) 5` — forcing `α := Int` would bind the rigid var. Declaratively
    untypeable (`α` cannot equal `Int`); the rigidity-seeded executable correctly
    returns `none`. Before the fix, `inferWithTypesCore []` wrongly returned `some Int`. -/
def openMisuse : Expr := .app openId (.primLit (.int 5))

theorem openMisuse_untypeable : ¬ ∃ τ, TypeOfHM ⟨[], []⟩ openMisuse τ := by
  rintro ⟨τ, h⟩
  simp [openMisuse, openId] at h
  cases h with
  | app hf hx =>
    cases hf with
    | lambda hlc hpins heq hbody =>
      have hpin := hpins (.fvar 5) rfl
      rw [hpin] at hx
      cases hx

-- The algorithm rejects `openMisuse` too by completeness. The fully erased term
-- `(λx. x) 5` is ordinary well-typed HM; the rejection concerns the rigid source
-- annotation, so soundness alone cannot establish it.

/-! ### A polymorphic program — let-generalization + double instantiation -/

/-- `let id : ∀a. a → a = λx. x in id id`. -/
def idid : Expr :=
  .letIn (some ⟨1, .arrow (.bvar 0) (.bvar 0)⟩) (.lambda none (.var 0))
    (.app (.var 0) (.var 0))

theorem idid_typeable : TypeOfHM ⟨[], []⟩ idid (.arrow (.fvar 0) (.fvar 0)) := by
  apply TypeOfHM.letIn (M := ⟨1, .arrow (.bvar 0) (.bvar 0)⟩) (L := [])
  · show ContainsBvarsUpTo 1 (Ty.arrow (Ty.bvar 0) (Ty.bvar 0))
    exact .arrow (.bvar (by omega)) (.bvar (by omega))
  · intro σ' h; cases h; rfl
  · intro Xs hfresh
    have hlen : Xs.length = 1 := hfresh.length
    rcases Xs with _ | ⟨X, _ | ⟨Y, tl⟩⟩
    · simp at hlen
    · have hterm : Expr.openBoundTyVars (some (⟨1, .arrow (.bvar 0) (.bvar 0)⟩ : PolyTy)) [X]
            (.lambda none (.var 0)) = .lambda none (.var 0) := rfl
      have htype : (⟨1, .arrow (.bvar 0) (.bvar 0)⟩ : PolyTy).openVars [X]
            = .arrow (.fvar X) (.fvar X) := rfl
      rw [hterm, htype]
      exact TypeOfHM.lambda .fvar (fun _ h => Option.noConfusion h) rfl
        (TypeOfHM.var (instArgs := []) rfl (by intro t ht; cases ht) .fvar)
    · simp at hlen
  · rfl
  · exact TypeOfHM.app
      (TypeOfHM.var (polyTy := ⟨1, .arrow (.bvar 0) (.bvar 0)⟩)
        (instArgs := [.arrow (.fvar 0) (.fvar 0)]) rfl
        (by intro t ht; simp only [List.mem_singleton] at ht; subst ht; exact .arrow .fvar .fvar)
        (.arrow (.bvar rfl) (.bvar rfl)))
      (TypeOfHM.var (polyTy := ⟨1, .arrow (.bvar 0) (.bvar 0)⟩)
        (instArgs := [.fvar 0]) rfl
        (by intro t ht; simp only [List.mem_singleton] at ht; subst ht; exact .fvar)
        (.arrow (.bvar rfl) (.bvar rfl)))

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 100_000 in
/-- `idid`'s principal monotype. Its input has no authored free type variables.
    Opening the signature allocates `0`, the RHS allocates `1`, and the two
    body instantiations allocate `2` and `3`, leaving principal variable `3`. -/
theorem idid_principalType : corePrincipalType [] idid = some (.arrow (.fvar 3) (.fvar 3)) := by
  unfold corePrincipalType
  have hSig :
      (unifyCoreK [0] (.arrow (.fvar 1) (.fvar 1)) (.arrow (.fvar 0) (.fvar 0))).map Subtype.val =
        some [(1, .fvar 0)] := by
    have hinner : (unifyCoreK [0] (.fvar 1) (.fvar 0)).map Subtype.val = some [(1,.fvar 0)] := by
      unfold unifyCoreK
      rfl
    cases he : unifyCoreK [0] (.fvar 1) (.fvar 0) with
    | none => simp only [he, Option.map_none, reduceCtorEq] at hinner
    | some result =>
      rcases result with ⟨S, hu, hav⟩
      have hs : S = [(1,.fvar 0)] := by simpa only [he, Option.map_some, Option.some.injEq] using hinner
      subst S
      have hnext : (unifyCoreK [0] (.fvar 0) (.fvar 0)).map Subtype.val = some [] := by
        unfold unifyCoreK
        rfl
      cases he2 : unifyCoreK [0] (.fvar 0) (.fvar 0) with
      | none => simp only [he2, Option.map_none, reduceCtorEq] at hnext
      | some result2 =>
        rcases result2 with ⟨T, ht, hat⟩
        have hT : T = [] := by simpa only [he2, Option.map_some, Option.some.injEq] using hnext
        subst T
        unfold unifyCoreK
        simp [he, he2, Subst.onTy, Ty.substFvars, Ty.substFvar]
  have hApp :
      (unifyCoreK [] (.arrow (.fvar 2) (.fvar 2))
        (.arrow (.arrow (.fvar 3) (.fvar 3)) (.fvar 4))).map Subtype.val =
        some [(2, .arrow (.fvar 3) (.fvar 3)), (4, .arrow (.fvar 3) (.fvar 3))] := by
    have hinner : (unifyCoreK [] (.fvar 2) (.arrow (.fvar 3) (.fvar 3))).map Subtype.val =
        some [(2,.arrow (.fvar 3) (.fvar 3))] := by
      unfold unifyCoreK
      simp [Ty.freeVars]
    cases he : unifyCoreK [] (.fvar 2) (.arrow (.fvar 3) (.fvar 3)) with
    | none => simp only [he, Option.map_none, reduceCtorEq] at hinner
    | some result =>
      rcases result with ⟨S, hu, hav⟩
      have hs : S = [(2,.arrow (.fvar 3) (.fvar 3))] := by
        simpa only [he, Option.map_some, Option.some.injEq] using hinner
      subst S
      have hnext : (unifyCoreK [] (.arrow (.fvar 3) (.fvar 3)) (.fvar 4)).map Subtype.val =
          some [(4,.arrow (.fvar 3) (.fvar 3))] := by
        unfold unifyCoreK
        simp [Ty.freeVars]
      cases he2 : unifyCoreK [] (.arrow (.fvar 3) (.fvar 3)) (.fvar 4) with
      | none => simp only [he2, Option.map_none, reduceCtorEq] at hnext
      | some result2 =>
        rcases result2 with ⟨T, ht, hat⟩
        have hT : T = [(4,.arrow (.fvar 3) (.fvar 3))] := by
          simpa only [he2, Option.map_some, Option.some.injEq] using hnext
        subst T
        unfold unifyCoreK
        simp [he, he2, Subst.onTy, Ty.substFvars, Ty.substFvar]
  cases heSig : unifyCoreK [0] (.arrow (.fvar 1) (.fvar 1)) (.arrow (.fvar 0) (.fvar 0)) with
  | none => simp only [heSig,Option.map_none,reduceCtorEq] at hSig
  | some result =>
    rcases result with ⟨S,hun,havoid⟩
    have hs : S = [(1,.fvar 0)] := by simpa only [heSig,Option.map_some,Option.some.injEq] using hSig
    subst S
    cases heApp : unifyCoreK [] (.arrow (.fvar 2) (.fvar 2)) (.arrow (.arrow (.fvar 3) (.fvar 3)) (.fvar 4)) with
    | none => simp only [heApp,Option.map_none,reduceCtorEq] at hApp
    | some result =>
      rcases result with ⟨S,hun,havoid⟩
      have hs : S = [(2,.arrow (.fvar 3) (.fvar 3)),(4,.arrow (.fvar 3) (.fvar 3))] := by
        simpa only [heApp,Option.map_some,Option.some.injEq] using hApp
      subst S
      simp (config := {maxSteps := 1000000}) [heSig,heApp,idid,principalType,inferCore,inferWithTypesCore,seed,InferInput.ofCore,
        InferInput.rigidVars,InferInput.freshFloor,tyVarCeil,BindingAnn.rigidVars,BindingAnn.ofCore,
        softVars,TyList.freeVars,Env.freeVars,Ty.freeVars,List.getElem?_cons_zero,
        PolyTy.mkTrivial,PolyTy.openVars,Ty.openVars,freshVars,Subst.onTy,Ty.substFvars,Ty.substFvar,
        Ty.instantiate,checkSignature,BindingAnn.isSignature,BindingAnn.paramCount,BindingAnn.substTyFvars,
        InferInput.openTyVars,InferInput.openTyVarsFrom,InferInput.substTyFvars,Subst.onCtx,Subst.onEnv,
        substSoft,signatureScheme,signatureNames,Ty.bvarsBelow]

/-- `idid_typeable` at the computed principal variable `3`. Each `var` rule
    supplies the appropriate existential instantiation witness. -/
theorem idid_typeable_fvar3 : TypeOfHM ⟨[], []⟩ idid (.arrow (.fvar 3) (.fvar 3)) := by
  apply TypeOfHM.letIn (M := ⟨1, .arrow (.bvar 0) (.bvar 0)⟩) (L := [])
  · show ContainsBvarsUpTo 1 (Ty.arrow (Ty.bvar 0) (Ty.bvar 0))
    exact .arrow (.bvar (by omega)) (.bvar (by omega))
  · intro σ' h; cases h; rfl
  · intro Xs hfresh
    have hlen : Xs.length = 1 := hfresh.length
    rcases Xs with _ | ⟨X, _ | ⟨Y, tl⟩⟩
    · simp at hlen
    · have hterm : Expr.openBoundTyVars (some (⟨1, .arrow (.bvar 0) (.bvar 0)⟩ : PolyTy)) [X]
            (.lambda none (.var 0)) = .lambda none (.var 0) := rfl
      have htype : (⟨1, .arrow (.bvar 0) (.bvar 0)⟩ : PolyTy).openVars [X]
            = .arrow (.fvar X) (.fvar X) := rfl
      rw [hterm, htype]
      exact TypeOfHM.lambda .fvar (fun _ h => Option.noConfusion h) rfl
        (TypeOfHM.var (instArgs := []) rfl (by intro t ht; cases ht) .fvar)
    · simp at hlen
  · rfl
  · exact TypeOfHM.app
      (TypeOfHM.var (polyTy := ⟨1, .arrow (.bvar 0) (.bvar 0)⟩)
        (instArgs := [.arrow (.fvar 3) (.fvar 3)]) rfl
        (by intro t ht; simp only [List.mem_singleton] at ht; subst ht; exact .arrow .fvar .fvar)
        (.arrow (.bvar rfl) (.bvar rfl)))
      (TypeOfHM.var (polyTy := ⟨1, .arrow (.bvar 0) (.bvar 0)⟩)
        (instArgs := [.fvar 3]) rfl
        (by intro t ht; simp only [List.mem_singleton] at ht; subst ht; exact .fvar)
        (.arrow (.bvar rfl) (.bvar rfl)))

theorem idid_headlines_fire :
    ∃ σ τ, SurfaceBridge.coreTypecheck [] idid = some σ ∧ σ = genScheme [] [] τ ∧
      TypeOfHM ⟨[], []⟩ idid τ ∧
      ∀ τ₀, TypeOfHM ⟨[], []⟩ idid τ₀ → ∃ R : Subst, τ₀ = R.onTy τ := by
  refine ⟨genScheme [] [] (.arrow (.fvar 3) (.fvar 3)), .arrow (.fvar 3) (.fvar 3),
    ?_, rfl, ?_, ?_⟩
  · show (corePrincipalType [] idid).map (genScheme [] []) = _
    rw [idid_principalType]; rfl
  · exact idid_typeable_fvar3
  ·
    intro τ₀ h
    -- Inversion: the annotation pins `M = ∀a. a → a`; the two uses then force
    -- `τ₀ = A → A` where `A` is the argument's own instantiation witness.
    cases h with
    | letIn hwf hpins hgen heq hbody =>
      have hM := hpins _ rfl
      subst hM
      subst heq
      cases hbody with
      | app hf hx =>
        cases hf with
        | var hlook1 hargs1 hinst1 =>
          cases hx with
          | var hlook2 hargs2 hinst2 =>
            simp only [List.getElem?_cons_zero, Option.some.injEq] at hlook1 hlook2
            subst hlook1; subst hlook2
            cases hinst2 with
            | arrow g1 g2 =>
              cases g1 with
              | bvar e1 =>
                cases g2 with
                | bvar e2 =>
                  have hAB : _ = _ := Option.some.inj (e1.symm.trans e2)
                  subst hAB
                  cases hinst1 with
                  | arrow f1 f2 =>
                    cases f1 with
                    | bvar d1 =>
                      cases f2 with
                      | bvar d2 =>
                        have hτ : _ = _ := Option.some.inj (d2.symm.trans d1)
                        subst hτ
                        exact ⟨[(3, _)], rfl⟩

/-! ### Progress and preservation on a concrete program -/

/-- `(λx. x) 5` — already annotation-free; beta-reduces to `5`. -/
def appIdFive : Expr := .app (.lambda none (.var 0)) (.primLit (.int 5))

theorem appIdFive_typeable : TypeOfHM ⟨[], []⟩ appIdFive (.prim .int) :=
  TypeOfHM.app
    (TypeOfHM.lambda .prim (fun _ h => Option.noConfusion h) rfl
      (TypeOfHM.var (instArgs := []) rfl (by intro t ht; cases ht) .prim))
    TypeOfHM.primLitInt

/-! ### Core v2: an all-wildcard match has a principal type (the match-fix witness) -/

/-- `λx. match x with | _ => 0`. Under Core v1's unconditional-`customTy` match rule
    this had NO principal type (the scrutinee's `customTy` name was unconstrained);
    after the §1 fix the scrutinee type is free, so the principal type is `∀α. α → Int`. -/
def matchWild : Expr := .lambda none (.match_ (.var 0) [(.wildcard, .primLit (.int 0))])

theorem matchWild_typeable : TypeOfHM ⟨[], []⟩ matchWild (.arrow (.fvar 0) (.prim .int)) := by
  refine TypeOfHM.lambda .fvar (fun _ h => Option.noConfusion h) rfl ?_
  refine TypeOfHM.match_ (scrutTy := .fvar 0)
    (TypeOfHM.var (instArgs := []) rfl (by intro t ht; cases ht) .fvar) (by simp) ?_
  intro branch hbr
  rw [List.mem_singleton] at hbr; subst hbr
  exact TypeOfMatchBranch.wildcard TypeOfHM.primLitInt

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 100_000 in
theorem matchWild_principalType :
    corePrincipalType [] matchWild = some (.arrow (.fvar 0) (.prim .int)) := by
  change (inferCore [] 0 ⟨[], []⟩ (.lambda none
    (.match_ (.var 0) [(.wildcard,.primLit (.int 0))]))).map (·.val.2.2.2) = _
  have huni : (unifyCoreK [] (.prim .int) (.fvar 1)).map Subtype.val = some [(1,.prim .int)] := by
    unfold unifyCoreK
    rfl
  cases he : unifyCoreK [] (.prim .int) (.fvar 1) with
  | none => simp only [he,Option.map_none,reduceCtorEq] at huni
  | some result =>
    rcases result with ⟨S,hun,havoid⟩
    have hs : S = [(1,.prim .int)] := by simpa only [he,Option.map_some,Option.some.injEq] using huni
    subst S
    simp (config := {maxSteps := 1000000}) [he, inferCore, inferWithTypesCore, inferBranchesWithTypesCore, seed, InferInput.rigidVars,
      softVars, TyList.freeVars, Env.freeVars, Ty.freeVars, List.getElem?_cons_zero,
      PolyTy.mkTrivial, PolyTy.openVars, Ty.openVars,
      Subst.onTy, Ty.substFvars, Subst.onCtx, Subst.onEnv, InferInput.substTyFvars,
      substInputBranches, substSoft, rigidBranchVars]
    exact ⟨rfl,rfl⟩

/-- All three headlines fire on the all-wildcard match: it typechecks, the produced
    type is a genuine declarative type (soundness), and it is principal. -/
theorem matchWild_headlines_fire :
    ∃ σ τ, SurfaceBridge.coreTypecheck [] matchWild = some σ ∧ σ = genScheme [] [] τ ∧
      TypeOfHM ⟨[], []⟩ matchWild τ ∧
      ∀ τ₀, TypeOfHM ⟨[], []⟩ matchWild τ₀ → ∃ R : Subst, τ₀ = R.onTy τ := by
  refine ⟨genScheme [] [] (.arrow (.fvar 0) (.prim .int)), .arrow (.fvar 0) (.prim .int),
    ?_, rfl, ?_, ?_⟩
  · show (corePrincipalType [] matchWild).map (genScheme [] []) = _
    rw [matchWild_principalType]; rfl
  · exact matchWild_typeable
  ·
    intro τ₀ h
    -- Inversion: the wildcard branch imposes nothing on the scrutinee, and its
    -- body is `0`, so the result is `Int` and the parameter stays free.
    cases h with
    | lambda hlc hpins heq hbody =>
      subst heq
      cases hbody with
      | match_ hscrut hne hbr =>
        have hb := hbr (MatchPattern.wildcard, Expr.primLit (.int 0)) (by simp)
        cases hb with
        | wildcard hbody2 =>
          cases hbody2
          exact ⟨[(0, _)], rfl⟩

/-! ### A recursive program — `letRec` typechecks at its principal type

The mutually-recursive group `letRec [f := g; g := f] in f` (`f = g`, `g = f`).
Under the old disjoint-slice `openGroup` rule this group could NOT be given the
polymorphic schemes `[∀a.a, ∀a.a]` (the disjoint opening severed the `f`/`g`
type-sharing — proved unsound vs Damas–Milner for `n > 1`); the shared-monotype
rule does. Its principal type is `∀a. a`. This is the capstone witness that the
recursive-binding inference fires end-to-end at the principal type. -/

/-- `letRec [none, none] [var 1, var 0] (var 0)` — the `f = g; g = f` mutual loop
    (both unannotated) returning `f`. -/
def mutualRec : Expr := .letRec [none, none] [.var 1, .var 0] (.var 0)

/-- The all-`none` mutual group types at its principal monotype under
    `TypeOfHM.letRec`: `specs = [.mono (fvar 100), .mono (fvar 100)]`, witnesses
    `τs = [fvar 100, fvar 100]`, pool `[100]`. Inside the group both members sit
    at the opened shared monotype `fvar X`; the body sees them generalised to
    `∀a. a` and instantiates at `fvar 0`. -/
theorem mutualRec_typeable_at (n : Nat) : TypeOfHM ⟨[], []⟩ mutualRec (.fvar n) := by
  refine TypeOfHM.letRec (specs := [.mono (.fvar 100), .mono (.fvar 100)])
    (groups := [[0, 1]]) (G := [100]) (L := [])
    (RecGroups.validResidualGroupsB_sound (by decide))
    ⟨rfl, rfl, by simp, ?_, ?_⟩ ?_ ?_ rfl ?_
  · intro τ hτ
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hτ
    rcases hτ with h | h <;> (injection h with h'; rw [h']; exact .fvar)
  · intro σ hσ
    simp only [List.mem_cons, List.not_mem_nil, reduceCtorEq, or_self] at hσ
  · intro stage component hc Xs hfresh member hm rhs τ hrhs hτ
    cases stage with
    | succ stage => simp at hc
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hc
      subst component
      obtain ⟨X, rfl⟩ : ∃ X, Xs = [X] := List.length_eq_one_iff.mp hfresh.length
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
      rcases hm with rfl | rfl
      · simp only [List.getElem?_cons_zero, Option.some.injEq] at hrhs hτ
        subst rhs
        cases hτ
        show TypeOfHM ⟨[PolyTy.mkTrivial (.fvar X), PolyTy.mkTrivial (.fvar X)], []⟩
          (.var 1) (.fvar X)
        exact TypeOfHM.var (instArgs := []) rfl (by simp) .fvar
      · simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at hrhs hτ
        subst rhs
        cases hτ
        show TypeOfHM ⟨[PolyTy.mkTrivial (.fvar X), PolyTy.mkTrivial (.fvar X)], []⟩
          (.var 0) (.fvar X)
        exact TypeOfHM.var (instArgs := []) rfl (by simp) .fvar
  · intro p hp σ hσ Ys hYs
    simp only [List.zip_cons_cons, List.zip_nil_right, List.mem_cons, List.not_mem_nil,
      or_false] at hp
    rcases hp with rfl | rfl <;> cases hσ
  · show TypeOfHM ⟨[⟨1, .bvar 0⟩, ⟨1, .bvar 0⟩], []⟩ (.var 0) (.fvar n)
    exact TypeOfHM.var (polyTy := ⟨1, .bvar 0⟩) (instArgs := [.fvar n]) rfl
      (by intro t ht; simp only [List.mem_singleton] at ht; subst ht; exact .fvar)
      (.bvar rfl)

theorem mutualRec_typeable : TypeOfHM ⟨[], []⟩ mutualRec (.fvar 0) :=
  mutualRec_typeable_at 0

set_option maxRecDepth 100_000 in
/-- The group's principal monotype is a bare variable (`∀a. a` after
    generalisation); `mutualRec.tyFreeVars = []`, and the two fresh group
    monotypes leave residual variable `2` for the body instantiation. -/
theorem mutualRec_principalType : corePrincipalType [] mutualRec = some (.fvar 2) := by
  have hshape : (match corePrincipalType [] mutualRec with
      | some (.fvar 2) => true
      | _ => false) = true := by
    native_decide
  generalize hresult : corePrincipalType [] mutualRec = result at hshape ⊢
  cases result with
  | none => cases hshape
  | some ty =>
    cases ty with
    | fvar n =>
      cases n with
      | zero => cases hshape
      | succ n =>
        cases n with
        | zero => cases hshape
        | succ n =>
          cases n with
          | zero => rfl
          | succ _ => cases hshape
    | prim _ => cases hshape
    | arrow _ _ => cases hshape
    | bvar _ => cases hshape
    | customTy _ _ => cases hshape

/-- `mutualRec_typeable` at the computed principal variable `2`. -/
theorem mutualRec_typeable_fvar2 : TypeOfHM ⟨[], []⟩ mutualRec (.fvar 2) :=
  mutualRec_typeable_at 2

/-- All headlines fire on the recursive group: `SurfaceBridge.coreTypecheck` succeeds, the produced
    type is a genuine declarative type, and it is principal. -/
theorem mutualRec_headlines_fire :
    ∃ σ τ, SurfaceBridge.coreTypecheck [] mutualRec = some σ ∧ σ = genScheme [] [] τ ∧
      TypeOfHM ⟨[], []⟩ mutualRec τ ∧
      ∀ τ₀, TypeOfHM ⟨[], []⟩ mutualRec τ₀ → ∃ R : Subst, τ₀ = R.onTy τ := by
  refine ⟨genScheme [] [] (.fvar 2), .fvar 2, ?_, rfl, ?_, ?_⟩
  · show (corePrincipalType [] mutualRec).map (genScheme [] []) = _
    rw [mutualRec_principalType]; rfl
  · exact mutualRec_typeable_fvar2
  · -- The principal type is a *bare* variable, so every `τ₀` is trivially an
    -- instance: no inversion needed.
    intro τ₀ _
    exact ⟨[(2, τ₀)], rfl⟩

end AuditCapstone

/-! ## Examples -/

section

/-! Semantic canaries for anonymous lambda, signature, match, and recursive elaboration.
These run the elaborator itself; output typing follows from `Infer.sourceSound`.
-/

namespace InferenceExamples

private def ctors : CtorEnv := (elabDecls preludeDecls).getD []
private def ctx : Ctx := ⟨[], ctors⟩

private def pair (left right : InferInput) : InferInput :=
  .app (.app (.ctor ⟨"Pair"⟩) left) right

/-- `let id = \(x : _) -> x in (id 1, id True)`. -/
def polymorphicId : InferInput :=
  .letIn .absent (.lambda (some .hole) (.var 0))
    (pair (.app (.var 0) (.primLit (.int 1))) (.app (.var 0) (.ctor ⟨"True"⟩)))

/-- Both occurrences of `_` are independently flexible. -/
def independentHoles : InferInput :=
  .letIn (.template (.arrow .hole .hole))
    (.lambda none (.primLit (.int 1)))
    (pair (.app (.var 0) (.ctor ⟨"True"⟩)) (.app (.var 0) (.primLit (.int 1))))

def structuredId : InferInput :=
  .letIn (.template (.arrow .hole .hole)) (.lambda none (.var 0))
    (pair (.app (.var 0) (.primLit (.int 1))) (.app (.var 0) (.ctor ⟨"True"⟩)))

/-- Variables reachable through the outer context cannot be generalized. -/
def outerMonomorphic : InferInput :=
  .lambda none
    (.letIn (.template .hole) (.var 0)
      (pair (.app (.var 0) (.primLit (.int 1))) (.app (.var 0) (.ctor ⟨"True"⟩))))

def occursCheck : InferInput :=
  .lambda (some .hole) (.app (.var 0) (.var 0))

def fixedDomainAccepted : InferInput :=
  .letIn (.template (.arrow (.fixed (.prim .int)) .hole)) (.lambda none (.var 0))
    (.app (.var 0) (.primLit (.int 1)))

def fixedDomainRejected : InferInput :=
  .letIn (.template (.arrow (.fixed (.prim .int)) .hole)) (.lambda none (.var 0))
    (.app (.var 0) (.ctor ⟨"True"⟩))

def quantifiedId : InferInput :=
  .letIn (.partialForall 1 (.arrow (.fixed (.bvar 0)) .hole))
    (.lambda none (.var 0)) (.var 0)

def quantifiedExtras : InferInput :=
  .letIn (.partialForall 1 (.arrow (.fixed (.bvar 0)) .hole))
    (.lambda none (.lambda none (.var 1))) (.var 0)

def vacuousWritten : InferInput :=
  .letIn (.partialForall 1 .hole) (.primLit (.int 1)) (.var 0)

def quantifiedRigidRejected : InferInput :=
  .letIn (.partialForall 1 (.arrow .hole (.fixed (.bvar 0))))
    (.lambda none (.primLit (.int 0))) (.var 0)

def signedRhsHole : InferInput :=
  .letIn (.complete ⟨1, .arrow (.bvar 0) (.bvar 0)⟩)
    (.lambda (some .hole) (.var 0))
    (pair (.app (.var 0) (.primLit (.int 1))) (.app (.var 0) (.ctor ⟨"True"⟩)))

def signedBodyHole : InferInput :=
  .letIn (.complete ⟨1, .arrow (.bvar 0) (.bvar 0)⟩)
    (.lambda none (.var 0)) (.lambda (some .hole) (.app (.var 1) (.var 0)))

#guard (inferCore [] 0 ctx quantifiedExtras).isSome
#guard (inferCore [] 0 ctx vacuousWritten).isSome
#guard !(inferCore [] 0 ctx quantifiedRigidRejected).isSome
#guard (inferCore [] 0 ctx signedRhsHole).isSome
#guard (inferCore [] 0 ctx signedBodyHole).isSome
#guard match inferCore [] 0 ctx quantifiedExtras with
  | some ⟨(_, _, .letIn (some ⟨2, .arrow (.bvar 0) (.arrow (.bvar 1) (.bvar 0))⟩) _ _, _), _⟩ => true
  | _ => false
#guard match inferCore [] 0 ctx vacuousWritten with
  | some ⟨(_, _, .letIn (some scheme) _ _, _), _⟩ => scheme.paramCount == 1
  | _ => false

def partialRecursion : InferInput :=
  .letRec [.template (.arrow .hole (.fixed (.prim .int)))]
    [.lambda none (.primLit (.int 0))] (.var 0)

def partialRecursionCodomainRejected : InferInput :=
  .letRec [.template (.arrow .hole (.fixed (.prim .int)))]
    [.lambda none (.primLit .unit)] (.var 0)

#guard (inferCore [] 0 ctx polymorphicId).isSome
#guard (inferCore [] 0 ctx independentHoles).isSome
#guard (inferCore [] 0 ctx structuredId).isSome
#guard !(inferCore [] 0 ctx outerMonomorphic).isSome
#guard !(inferCore [] 0 ctx occursCheck).isSome
#guard (inferCore [] 0 ctx fixedDomainAccepted).isSome
#guard !(inferCore [] 0 ctx fixedDomainRejected).isSome
#guard (inferCore [] 0 ctx quantifiedId).isSome
#guard match inferCore [] 0 ctx partialRecursion with
  | some ⟨(_, _, .letRec [some ⟨1, .arrow (.bvar 0) (.prim .int)⟩]
      [.lambda none (.primLit (.int 0))] (.var 0), .arrow (.fvar _) (.prim .int)), _⟩ => true
  | _ => false
#guard !(inferCore [] 0 ctx partialRecursionCodomainRejected).isSome

/- The id canary really introduces a scheme binder and closes the lambda
annotation underneath that same binder. -/
#guard match inferCore [] 0 ctx polymorphicId with
  | some ⟨(_, _, .letIn (some scheme) (.lambda (some (.bvar 0)) _) _, _), _⟩ =>
      scheme.paramCount == 1
  | _ => false

private def idHole : InferInput := .lambda (some .hole) (.var 0)

-- Independent local allocation: two syntactic visits, unrelated types.
def distinctCopies : InferInput := pair idHole idHole
#guard match inferCore [] 0 ctx distinctCopies with
  | some ⟨(_, _, _, .customTy ⟨"Pair"⟩
      [.arrow (.fvar a) (.fvar a'), .arrow (.fvar b) (.fvar b')]), _⟩ =>
      a == a' && b == b' && a != b
  | _ => false

-- Independent local uses: same InferInput value copied, each used at a different type.
def differentlyUsedCopies : InferInput :=
  pair (.app idHole (.primLit (.int 1))) (.app idHole (.ctor ⟨"True"⟩))
#guard (inferCore [] 0 ctx differentlyUsedCopies).isSome

-- Reallocating the holes must not reallocate the shared outer monomorphic f.
def sharedOuterRejected : InferInput :=
  .lambda none
    (pair
      (.app (.lambda (some .hole) (.app (.var 1) (.var 0))) (.primLit (.int 1)))
      (.app (.lambda (some .hole) (.app (.var 1) (.var 0))) (.ctor ⟨"True"⟩)))
#guard !(inferCore [] 0 ctx sharedOuterRejected).isSome

private def branches (yes no : InferInput) : List (MatchPattern × InferInput) :=
  [(.named ⟨"True"⟩ 0, yes), (.named ⟨"False"⟩ 0, no)]

-- Partial scrutinees use the same branch inference and constructor checks.
def directPartialScrutinee : InferInput :=
  .match_ (.app idHole (.ctor ⟨"True"⟩))
    (branches (.primLit (.int 1)) (.primLit (.int 0)))
#guard (inferCore [] 0 ctx directPartialScrutinee).isSome

-- Anonymous parameters in named and fallback bodies are solved in one thread.
def partialBranches : InferInput :=
  .match_ (.ctor ⟨"True"⟩) (branches idHole idHole)
#guard (inferCore [] 0 ctx partialBranches).isSome

-- Every branch must agree on the result; fresh local holes do not relax it.
def incompatiblePartialBranches : InferInput :=
  .match_ (.ctor ⟨"True"⟩)
    [(.wildcard, .app idHole (.primLit (.int 1))),
     (.wildcard, .app idHole (.ctor ⟨"True"⟩))]
#guard !(inferCore [] 0 ctx incompatiblePartialBranches).isSome

-- Equivalent normal lowering shape: the match scrutinee is bound once first.
def loweredPartialScrutinee : InferInput :=
  .letIn .absent (.app idHole (.ctor ⟨"True"⟩))
    (.match_ (.var 0) (branches (.primLit (.int 1)) (.primLit (.int 0))))
#guard (inferCore [] 0 ctx loweredPartialScrutinee).isSome

-- Nested complete match is an argument to the partial scrutinee expression.
def nestedScrutinee : InferInput :=
  .letIn .absent
    (.app idHole
      (.letIn .absent (.ctor ⟨"False"⟩)
        (.match_ (.var 0) (branches (.ctor ⟨"False"⟩) (.ctor ⟨"True"⟩)))))
    (.match_ (.var 0) (branches (.primLit (.int 1)) (.primLit (.int 0))))
#guard (inferCore [] 0 ctx nestedScrutinee).isSome

-- Lowering an irrefutable named pattern makes another ordinary let. This
-- checks the existing lowering/generalization policy, independently of copying.
def irrefutableCapture : InferInput :=
  .letIn .absent idHole
    (.letIn .absent (.var 0)
      (pair (.app (.var 0) (.primLit (.int 1)))
        (.app (.var 0) (.ctor ⟨"True"⟩))))
#guard (inferCore [] 0 ctx irrefutableCapture).isSome


private def rigidArrow : TyTemplate := .arrow (.fixed (.fvar 7)) .hole
private def rigidIdentity : InferInput := .lambda (some rigidArrow) (.var 0)
private def violatesRigid : InferInput :=
  .lambda (some rigidArrow) (.app (.var 0) (.primLit (.int 1)))
private def rigidLet : InferInput :=
  .letIn (.template rigidArrow) (.lambda none (.var 0)) (.var 0)
private def violatesRigidLet : InferInput :=
  .letIn (.template rigidArrow) (.lambda none (.var 0))
    (.app (.var 0) (.primLit (.int 1)))

#guard (inferCore [7] 8 ctx rigidIdentity).isSome
#guard !(inferCore [7] 8 ctx violatesRigid).isSome
#guard !(inferCore [] 8 ctx rigidIdentity).isSome
#guard (inferCore [7] 8 ctx rigidLet).isSome
#guard !(inferCore [7] 8 ctx violatesRigidLet).isSome
#guard match inferCore [7] 8 ctx rigidLet with
  | some ⟨(_, _, .letIn (some scheme) _ _, .arrow (.fvar 7) (.fvar 7)), _⟩ =>
      scheme.paramCount == 0
  | _ => false

private def polyrec : InferInput :=
  .letRec [.complete ⟨1, .arrow (.bvar 0) (.prim .int)⟩]
    [.lambda none
      (.app (.var 1) (.app (.app (.ctor ⟨"Pair"⟩) (.var 0)) (.var 0)))]
    (.app (.var 0) (.ctor ⟨"True"⟩))
#guard (inferCore [] 0 ctx polyrec).isSome
#guard (inferCore [] 0 ctx
  (.letIn .absent (.lambda (some .hole) (.var 0)) polyrec)).isSome
#guard !(principalType ctx.ctors (InferInput.ofCore polyrec.erase)).isSome

-- Complete signatures protect their authored skolems while filling RHS holes.
def completeForallWithPartialRhs : InferInput :=
  .letIn (.complete ⟨1, .arrow (.bvar 0) (.bvar 0)⟩)
    (.lambda (some .hole) (.var 0)) (.var 0)
#guard (inferCore [] 0 ctx completeForallWithPartialRhs).isSome

-- An unused hole still generalizes at its own binding even when it is absent
-- from the whole-program result type.
def unusedHole : InferInput :=
  .letIn (.template .hole) (.ctor ⟨"Nil"⟩) (.primLit (.int 1))
#guard match inferCore [] 0 ctx unusedHole with
  | some ⟨(_, _, .letIn (some ⟨1, .customTy ⟨"List"⟩ [.bvar 0]⟩) _ _, .prim .int), _⟩ => true
  | _ => false

-- Public artifacts and completed output come from the same run. Synthetic
-- scheme binders do not turn source hover monotypes into dangling bvars.
#guard match inferWithTypes ctors polymorphicId with
  | some result => result.binderSchemes.any (fun fact => fact.2.paramCount == 1)
  | none => false
#guard match (inferWithTypes ctors polymorphicId).bind (fun result =>
    result.nodeTypes.find? (fun fact => fact.1 == [.letRhs])) with
  | some (_, .arrow (.fvar 0) (.fvar 0)) => true
  | _ => false

#print axioms Infer.sourceSound
#print axioms Infer.inputSound
#print axioms Infer.completes
#print axioms Infer.erase

end InferenceExamples

end
