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
  "2:8: type mismatch: expected `Bool -> ?5`, found `Int -> Int` (`Int` is not `Bool`)"
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
  "a match does not cover every case"

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
#guard runToString "1 + 'c'" ==
  "1:1: type mismatch: expected `Char -> ?1`, found `Int -> Int` (`Int` is not `Char`)"
#guard runToString "let f {a} (x : a) : Int = x\n1" ==
  "1:5: type mismatch: expected `a -> Int`, found `?0 -> ?0` (`a` is not `Int`)"
#guard runToString "\\x -> x x" ==
  "1:7: type mismatch: expected `?0 -> ?1`, found `?0` (`?0` would be the infinite type `?0 -> ?1`)"
#guard runToString "let escape = \\x -> let g {a} (y : a) : a = x in g\nescape" ==
  "1:24: type mismatch: expected `a -> a`, found `?1 -> ?0` \
    (`?0` cannot be `a`: a type variable would escape its scope)"
#guard runToString "let g (x : _) = x\ng" == "2:1: the program's type `?1 -> ?1` is not determined"
#guard runToString "if 1 then 2 else 3" ==
  "1:4: type mismatch: expected `Bool`, found `Int` (`Int` is not `Bool`)"

/-! ## Evaluation -/

-- Fuel bounds the number of steps; a program that runs out reports its type.
#guard runToString "let loop (n : Int) : Int = loop n\nloop 0" == "<running> : Int"
#guard runToString "let sum n = if n < 1 then 0 else n + sum (n - 1)\nsum 1000" (fuel := 1000000) ==
  "500500 : Int"

end EPL.Surface.Tests
