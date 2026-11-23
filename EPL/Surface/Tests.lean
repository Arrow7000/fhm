import EPL.Surface.Run

/-!
# Front-end tests

Each test runs a whole program through `runToString` (lex, parse, lower,
infer, evaluate) and compares the printed `value : type`, or the printed first
error `line:col: message`.
-/

namespace EPL.Surface.Tests

open EPL.Surface

/-! ## Expressions and sugar -/

#guard runToString "1 + 2" == "3 : Int"
#guard runToString "-3 + 1" == "-2 : Int"
#guard runToString "1 < 2" == "True : Bool"
#guard runToString "if 2 < 1 then 'a' else 'b'" == "'b' : Char"
#guard runToString "()" == "() : Unit"
#guard runToString "(1, 'c')" == "(1, 'c') : (Int, Char)"
#guard runToString "1 :: [2, 3]" == "[1, 2, 3] : List Int"
#guard runToString "\"hi\"" == "\"hi\" : List Char"
#guard runToString "'h' :: \"i\\n\"" == "\"hi\\n\" : List Char"
#guard runToString "(\\x y -> x + y) 1 2" == "3 : Int"
#guard runToString "\\(x : Int) -> x" == "<function> : Int -> Int"
#guard runToString "Cons 1" == "<function> : List Int -> List Int"
-- The program is `()` if it has no final expression.
#guard runToString "let x = 1" == "() : Unit"

/-! ## Bindings -/

-- Top-level bindings may come in any order.
#guard runToString "let x = y + 1\nlet y = 2\nx" == "3 : Int"
-- A block's bindings share a column; they may also come in any order.
#guard runToString "let x =\n  let a = 1\n      b = a + c\n      c = 2\n  in b\nx" == "3 : Int"
-- Self-recursion becomes a `fix`.
#guard runToString "let sum n = if n < 1 then 0 else n + sum (n - 1)\nsum 10" == "55 : Int"
-- A function head is a signature: `{a}` binds type variables.
#guard runToString "let id {a} (x : a) : a = x\n(id 1, id True)" == "(1, True) : (Int, Bool)"
#guard runToString
  "let map {a b} (f : a -> b) (xs : List a) : List b =
  match xs with
  | [] -> []
  | x :: rest -> f x :: map f rest
map (\\x -> x + 1) [1, 2, 3]" == "[2, 3, 4] : List Int"
-- Without one, a binding is monomorphic.
#guard runToString "let id x = x\n(id 1, id True)" ==
  "2:11: type mismatch: expected `Int`, found `Bool`"
-- Holes in a head are completed from the definition.
#guard runToString "let k {a} (x : a) : _ = 1\nk True" == "1 : Int"
#guard runToString "let f (x : ?t) : ?t = x + 1\nf 2" == "3 : Int"
#guard runToString "let pick {a} (x : a) (y : ?h) : ?h = y\npick 1 2" ==
  "1:5: the definition does not determine ?h in its signature"
-- Pattern bindings.
#guard runToString "let (a, b) = (1, 'c')\nb" == "'c' : Char"
#guard runToString "let (a, b) : (Int, _) = (1, 'c')\na" == "1 : Int"

/-! ## Data and patterns -/

def maybe : String := "type Maybe a = Just a | Nothing\n"

#guard runToString (maybe ++ "let f {a} (x : a) : Maybe a = Just x\nf 3") == "Just 3 : Maybe Int"
#guard runToString (maybe ++
  "let fromMaybe {a} (d : a) (m : Maybe a) : a =
  match m with
  | Just x -> x
  | Nothing -> d
(fromMaybe 0 Nothing, fromMaybe 0 (Just 5))") == "(0, 5) : (Int, Int)"
-- Nested patterns, wildcards and sugar compile to nested matches.
#guard runToString
  "match [1, 2] with
| [] -> 0
| [x] -> x
| x :: y :: _ -> x + y" == "3 : Int"
#guard runToString
  "let zip {a b} (xs : List a) (ys : List b) : List (a, b) =
  match (xs, ys) with
  | (x :: xs, y :: ys) -> (x, y) :: zip xs ys
  | _ -> []
zip [1, 2, 3] \"ab\"" == "[(1, 'a'), (2, 'b')] : List (Int, Char)"
#guard runToString "let f x = match x with\n  | (True, y) -> y\n  | (False, _) -> 0\nf (False, 3) + f (True, 4)" ==
  "4 : Int"
#guard runToString "let swap = \\(x, y) -> (y, x)\nswap (1, 'c')" == "('c', 1) : (Char, Int)"
#guard runToString (maybe ++ "type Tree a = Leaf | Node (Tree a) a (Tree a)
let insert (x : Int) (t : Tree Int) : Tree Int =
  match t with
  | Leaf -> Node Leaf x Leaf
  | Node l y r -> if x < y then Node (insert x l) y r else Node l y (insert x r)
let toList {a} (t : Tree a) : List a =
  match t with
  | Leaf -> []
  | Node Leaf y Leaf -> [y]
  | Node l y r -> toList l
toList (insert 1 (insert 3 (insert 2 Leaf)))") == "[1] : List Int"
-- A match that misses a case is rejected before running.
#guard runToString (maybe ++ "match Just 3 with\n| Just x -> x") ==
  "2:7: this match does not cover the case `Nothing`"
#guard runToString "match [1, 2] with\n| [] -> 0\n| [x] -> x" ==
  "3:3: this match does not cover the case `Cons`"
#guard runToString "match (True, False) with\n| (True, _) -> 0\n| (_, True) -> 1" ==
  "2:3: this match does not cover the case `False`"
#guard runToString (maybe ++ "let f m = match m with\n  | Just x -> x\nf (Just 1)") ==
  "2:17: this match does not cover the case `Nothing`"

/-! ## Errors, in pipeline order -/

-- Lexing
#guard runToString "let x = 1\n\tx" == "2:1: tabs are not allowed"
#guard runToString "'ab'" == "1:1: unterminated character literal"
#guard runToString "\"bad\\q\"" == "1:5: unknown escape sequence"
-- Parsing
#guard runToString "1 + 2 + 3" == "1:7: operators do not chain: add parentheses"
#guard runToString "let x =\n1\nx" == "2:1: this must be indented past column 1"
#guard runToString "(1, 2" == "1:6: expected `)`, found the end of the input"
#guard runToString "type T = a" == "1:10: expected a constructor name, found `a`"
-- Lowering
#guard runToString "y" == "1:1: unbound variable `y`"
#guard runToString "Just 1" == "1:1: unknown constructor `Just`"
#guard runToString "let f (x : Maybe Int) = x\n1" == "1:12: unknown type `Maybe`"
#guard runToString "let f (x : List) = x\n1" ==
  "1:12: `List` takes 1 type argument(s), but is given 0"
#guard runToString "let f (x : b) = x\n1" == "1:12: type variable `b` is not in scope"
#guard runToString "type T a = A (Maybe a)\n1" == "1:15: unknown type `Maybe`"
#guard runToString "type T = A _\n1" == "1:12: data declarations cannot have type holes"
#guard runToString "type T = A | B\ntype T = C\n1" == "2:1: type `T` is already declared"
#guard runToString "type T = True\n1" == "1:10: constructor `True` is already declared"
#guard runToString "let x = 1\nlet x = 2\nx" == "2:5: `x` is defined twice"
#guard runToString "match (1, 2) with\n| (x, x) -> x" == "2:3: `x` is bound twice in this pattern"
#guard runToString (maybe ++ "match Just 3 with\n| Just x y -> x") ==
  "3:3: `Just` has 1 field(s), but the pattern has 2"
#guard runToString (maybe ++ "match Just 3 with\n| Just x -> x\n| [] -> 0") ==
  "4:3: `Nil` is not a constructor of `Maybe`"
#guard runToString (maybe ++ "match Just 3 with\n| Just x -> x\n| _ -> 0\n| Nothing -> 1") ==
  "5:3: this arm is unreachable"
#guard runToString
  "let even n = if n < 1 then True else odd (n - 1)
let odd n = if n < 1 then False else even (n - 1)
even 4" == "1:5: mutual recursion is not supported: even, odd"
#guard runToString "let (a, b) = (1, a)\nb" == "1:5: a pattern binding cannot be recursive: a"
-- Inference, located through the lowering's origins
-- An application's mismatch is reported at its argument.
#guard runToString "1 + 'c'" == "1:5: type mismatch: expected `Int`, found `Char`"
#guard runToString "let f (xs : List Int) = xs\nf [True]" ==
  "2:3: type mismatch: expected `List Int`, found `List Bool` (`Bool` is not `Int`)"
#guard runToString "let x = 1\nx 'a'" ==
  "2:1: this is applied to an argument, but its type `Int` is not a function type"
#guard runToString "let f {a} (x : a) : Int = x\n1" ==
  "1:5: type mismatch: expected `a -> Int`, found `?0 -> ?0` (`a` is not `Int`)"
#guard runToString "\\x -> x x" ==
  "1:7: type mismatch: expected `?0 -> ?1`, found `?0` (`?0` would be the infinite type `?0 -> ?1`)"
#guard runToString "let escape = \\x -> let g {a} (y : a) : a = x in g\nescape" ==
  "1:24: type mismatch: expected `a -> a`, found `?1 -> ?0` \
    (`?0` cannot be `a`: a type variable would escape its scope)"
#guard runToString "let g (x : _) = x\ng" == "2:1: the program's type `?1 -> ?1` is not determined"
#guard runToString "if 1 then 2 else 3" ==
  "1:4: type mismatch: expected `Bool`, found `Int`"

/-! ## Evaluation -/

-- Fuel bounds the number of steps; a program that runs out reports its type.
#guard runToString "let loop (n : Int) : Int = loop n\nloop 0" == "<running> : Int"
#guard runToString "let sum n = if n < 1 then 0 else n + sum (n - 1)\nsum 1000" (fuel := 1000000) ==
  "500500 : Int"

/-! ## Types for editors -/

/-- The top-level bindings' types, as `epl run` prints them. -/
def bindingTypes (source : String) : List String :=
  match checkWithTypes source with
  | .ok (lowering, _, types) =>
      (lowering.bindingTypes (lowering.symbols types)).map fun (name, ty) => s!"{name} : {ty}"
  | .error error => [error.render]

/-- The definitions and uses of `name`: `line:col kind type`. -/
def symbolsOf (source name : String) : List String :=
  match checkWithTypes source with
  | .ok (lowering, _, types) =>
      ((lowering.symbols types).filter (·.name == name)).toList.map fun symbol =>
        s!"{symbol.span.start.line}:{symbol.span.start.col} \
          {if symbol.isDef then "def" else "use"} {symbol.ty}"
  | .error error => [error.render]

-- In source order, polymorphic ones with their type variables.
#guard bindingTypes "let n = 1\nlet map {a b} (f : a -> b) (xs : List a) : List b =\n  \
    match xs with\n  | [] -> []\n  | x :: rest -> f x :: map f rest\nmap (\\x -> x + n) [1]" ==
  ["n : Int", "map : {a b} (a -> b) -> List a -> List b"]
-- A use has the type it is used at.
#guard symbolsOf "let id {a} (x : a) : a = x\nid 1" "id" == ["1:5 def {a} a -> a", "2:1 use Int -> Int"]
-- A pattern variable's arm is copied by the match compiler; it is listed once.
#guard symbolsOf "match (1, True) with\n| (y, True) -> y\n| (y, False) -> y + 1" "y" ==
  ["2:4 def Int", "3:4 def Int", "2:16 use Int", "3:17 use Int"]
#guard symbolsOf "match [1] with\n| [] -> 0\n| _ -> let z = 2 in z" "z" ==
  ["3:12 def Int", "3:21 use Int"]

-- Types, type variables and constructors.
#guard symbolsOf "type Box a = Box a\nlet open {a} (b : Box a) : a = match b with\n  | Box x -> x\nopen (Box 1)"
    "Box" ==
  ["4:7 use Int -> Box Int", "1:6 def type Box a =\n  | Box a", "1:14 def {a} a -> Box a",
   "2:19 use type Box a =\n  | Box a", "3:5 use {a} a -> Box a"]
#guard symbolsOf "type Box a = Box a\nlet open {a} (b : Box a) : a = match b with\n  | Box x -> x\nopen (Box 1)"
    "a" ==
  ["1:10 def type variable (of Box)", "1:18 use type variable (of Box)",
   "2:23 use type variable (of open)", "2:28 use type variable (of open)",
   "2:11 def type variable (of open)"]

-- Operators: at the type they are used at; `::` in a pattern, at its scheme.
#guard symbolsOf "let f x y = x + y\nf 1 2 < 3" "+" == ["1:15 use Int -> Int -> Int"]
#guard symbolsOf "let f x y = x + y\nf 1 2 < 3" "<" == ["2:7 use Int -> Int -> Bool"]
#guard symbolsOf "match True :: [] with\n| x :: _ -> x\n| [] -> False" "::" ==
  ["1:12 use Bool -> List Bool -> List Bool", "2:5 use {a} a -> List a -> List a"]

/-- The doc comments of the names defined in `source`: `name: doc`. -/
def docsOf (source : String) : List String :=
  match checkWithTypes source with
  | .ok (lowering, _, types) =>
      ((lowering.symbols types).filter (·.isDef)).toList.filterMap fun symbol =>
        symbol.doc.map (s!"{symbol.name}: {·}")
  | .error error => [error.render]

-- A doc comment documents the `let`, type or constructor it comes before.
#guard docsOf "--- The answer.\nlet answer = 42\nanswer" == ["answer: The answer."]
#guard docsOf "/-- A shape.\n    Round or square. -/\ntype Shape =\n  --- Round.\n  | Circle Int\n  \
    -- (an ordinary comment)\n  /-- Square. -/\n  | Square Int\nlet (x, y) =\n  --- Local.\n  \
    let z = 1 in (z, z)\n(Circle x, Square y)" ==
  ["z: Local.", "Shape: A shape.\nRound or square.", "Circle: Round.", "Square: Square."]
#guard docsOf "type T = /-- First. -/ A | B\nA" == ["A: First."]
-- Four dashes, or a slash and three, open an ordinary comment.
#guard docsOf "---- no\n/--- no -/\nlet x = 1\nx" == []
#guard runToString "let x = 1\n--- Nothing.\nx" ==
  "2:1: a doc comment must come before a `let`, a `type` or a constructor"

/-! ## Existential constructors -/

-- `MkPack {s}`: the constructor's own type variable `s` is hidden from its type.
#guard runToString "type Pack a = MkPack {s} s (s -> a)\nMkPack 'x' (\\c -> 5)" ==
  "MkPack 'x' <function> : Pack Int"
-- Opening a pack and applying its function to its value.
#guard runToString "type Pack a = MkPack {s} s (s -> a)\nmatch MkPack True (\\b -> if b then 1 else 0) with\n| MkPack s f -> f s" == "1 : Int"
-- Returning the hidden value lets its type escape. The message names it `s`.
#guard runToString "type Pack a = MkPack {s} s (s -> a)\nmatch MkPack True (\\b -> if b then 1 else 0) with\n| MkPack s f -> s" ==
  "3:17: type mismatch: expected `s -> (s -> Int) -> ?7`, found `?8 -> ?9 -> ?8` (`?7` cannot be `s`: a type variable would escape its scope)"
-- Different packs of one type may hide different types.
#guard runToString "type Pack a = MkPack {s} s (s -> a)\nlet open {a} (p : Pack a) : a = match p with\n  | MkPack x f -> f x\nopen (MkPack 'x' (\\c -> 5)) + open (MkPack 2 (\\n -> n + 1))" == "8 : Int"
-- An arm is one type variable deeper per hidden type, so a polymorphic `let`
-- inside it gets its own type variable rather than the hidden one.
#guard runToString "type Pack a = MkPack {s} s (s -> a)\nmatch MkPack True (\\b -> if b then 1 else 0) with\n| MkPack x f ->\n  let id {b} (y : b) : b = y in f (id x) + id 10" == "11 : Int"
-- Inside an arm, the hidden type can be named as in the declaration.
#guard runToString "type Pack a = MkPack {s} s (s -> a)\nmatch MkPack True (\\b -> if b then 1 else 0) with\n| MkPack x f ->\n  let g (y : s) : Int = f y in g x" == "1 : Int"
-- A constructor's fields may only use its type's parameters and its own variables.
#guard runToString "type T = MkT s\n1" == "1:14: type variable `s` is not in scope"
#guard runToString "type T a = MkT {a} a\n1" == "1:12: type parameter `a` is bound twice"

end EPL.Surface.Tests
