export const examples = [
  {
    id: "polymorphism",
    section: "Basics",
    title: "Polymorphic identity",
    result: "(42, True)",
    source: String.raw`-- Hover over id: one definition, many possible types.
let id = \x -> x

let number = id 42
let truth = id True

-- Each use of id gets its own type.
(number, truth)
`,
  },
  {
    id: "lists",
    section: "Basics",
    title: "Map over a list",
    result: "[2, 4, 6, 8]",
    source: String.raw`let map = \f xs ->
  match xs with
  | [] -> []
  | head :: tail -> f head :: map f tail

let double = \n -> n + n

-- Try replacing double with (\n -> n + 10).
map double [1, 2, 3, 4]
`,
  },
  {
    id: "patterns",
    section: "Basics",
    title: "Maybe and pattern matching",
    result: "(42, 0)",
    source: String.raw`type Maybe a = Just a | Nothing

let withDefault = \fallback value ->
  match value with
  | Just x -> x
  | Nothing -> fallback

(withDefault 0 (Just 42), withDefault 0 Nothing)
`,
  },
  {
    id: "recursion",
    section: "Basics",
    title: "Recursion",
    result: "15",
    source: String.raw`let sumTo = \n ->
  if n < 1 then
    0
  else
    n + sumTo (n - 1)

sumTo 5
`,
  },
  {
    id: "errors",
    section: "Basics",
    title: "A type error",
    fails: true,
    source: String.raw`let addOne = \n -> n + 1

-- addOne expects an Int, but this is a Bool.
-- Try changing True to 41.
addOne True
`,
  },
  {
    id: "tree",
    section: "Data and functions",
    title: "Binary search tree",
    result: "([1, 2, 3, 5, 8, 9], (True, False))",
    source: String.raw`-- A binary search tree of Ints.
type Tree = Leaf | Node Tree Int Tree

let insert = \n t ->
  match t with
  | Leaf -> Node Leaf n Leaf
  | Node l m r ->
    if n < m then Node (insert n l) m r
    else if m < n then Node l m (insert n r)
    else t

let member = \n t ->
  match t with
  | Leaf -> False
  | Node l m r ->
    if n < m then member n l
    else if m < n then member n r
    else True

let foldr = \f acc xs ->
  match xs with
  | [] -> acc
  | x :: rest -> f x (foldr f acc rest)

let append = \xs ys -> foldr (\x rest -> x :: rest) ys xs

-- In-order traversal lists the elements in sorted order.
let toList = \t ->
  match t with
  | Leaf -> []
  | Node l m r -> append (toList l) (m :: toList r)

let tree = foldr insert Leaf [5, 2, 8, 1, 9, 3, 5]

(toList tree, (member 3 tree, member 4 tree))
`,
  },
  {
    id: "folds",
    section: "Data and functions",
    title: "Folds and composition",
    result: "220",
    source: String.raw`-- Building programs out of small higher-order functions.
let foldr = \f acc xs ->
  match xs with
  | [] -> acc
  | x :: rest -> f x (foldr f acc rest)

let map = \f -> foldr (\x rest -> f x :: rest) []

let filter = \keep ->
  foldr (\x rest -> if keep x then x :: rest else rest) []

let compose = \f g x -> f (g x)

let sum = foldr (\x y -> x + y) 0

let range = \lo hi ->
  if hi < lo then [] else lo :: range (lo + 1) hi

let isEven = \n ->
  if n < 2 then n < 1 else isEven (n - 2)

let square = \n ->
  let go = \k -> if k < 1 then 0 else n + go (k - 1) in
  go n

-- The sum of the squares of the even numbers up to 10.
let sumOfEvenSquares = compose sum (compose (map square) (filter isEven))

sumOfEvenSquares (range 1 10)
`,
  },
  {
    id: "scoped",
    section: "Data and functions",
    title: "Scoped type variables",
    result: "(7, True)",
    source: String.raw`let keep : {a b} a -> b -> a =
  \x y ->
    -- The helper can refer to the outer a and b.
    let helper : b -> a = \ignored -> x in
    helper y

(keep 7 False, keep True 42)
`,
  },
  {
    id: "mutual",
    section: "Data and functions",
    title: "Mutual recursion",
    result: "(True, False)",
    source: String.raw`let even = \n ->
  if n < 1 then True else odd (n - 1)

let odd = \n ->
  if n < 1 then False else even (n - 1)

(even 8, even 9)
`,
  },
  {
    id: "polyrec",
    section: "Polymorphic recursion",
    title: "Nested datatypes",
    result: "3",
    source: String.raw`type Nested a =
  | Elem a
  | Group (Nested (List a))

-- The signature lets size call itself at a different type.
let size : {a} Nested a -> Int =
  \nested ->
    match nested with
    | Elem x -> 1
    | Group inner -> 1 + size inner

size (Group (Group (Elem [[5]])))
`,
  },
  {
    id: "nested-map",
    section: "Polymorphic recursion",
    title: "Mapping a nested type",
    result: "Nest (Nest (Flat [[True, True], [False]]))",
    source: String.raw`-- Each Nest level wraps the elements in one more list.
type Nested a =
  | Flat a
  | Nest (Nested (List a))

let mapList = \f xs ->
  match xs with
  | [] -> []
  | x :: rest -> f x :: mapList f rest

-- The recursive call maps over Nested (List a), with a function on lists:
-- a different type at every level. That needs the signature.
let mapNested : {a b} (a -> b) -> Nested a -> Nested b =
  \f t ->
    match t with
    | Flat x -> Flat (f x)
    | Nest inner -> Nest (mapNested (mapList f) inner)

mapNested (\n -> n < 3) (Nest (Nest (Flat [[1, 2], [3]])))
`,
  },
  {
    id: "perfect",
    section: "Polymorphic recursion",
    title: "Perfect trees",
    result: "(16, Succ (Succ (Zero ((True, True), (True, True)))))",
    source: String.raw`-- A perfect binary tree: every Succ level pairs up the elements, so the type
-- itself guarantees that the tree is balanced.
type Perfect a =
  | Zero a
  | Succ (Perfect (a, a))

-- A tree of depth n holding 2^n copies of x.
let build : {a} Int -> a -> Perfect a =
  \n x -> if n < 1 then Zero x else Succ (build (n - 1) (x, x))

-- Each level calls total at a pair type, with a function that sums pairs.
let total : {a} (a -> Int) -> Perfect a -> Int =
  \f p ->
    match p with
    | Zero x -> f x
    | Succ inner -> total (\pair -> match pair with | (x, y) -> f x + f y) inner

(total (\n -> n) (build 4 1), build 2 True)
`,
  },
  {
    id: "mutual-polyrec",
    section: "Polymorphic recursion",
    title: "Mutual polymorphic recursion",
    result: "3",
    source: String.raw`-- Two datatypes that nest into each other, changing the element type at
-- every step: Ping holds a, then a Pong of List a, which holds a Ping of pairs.
type Ping a = PingEnd | Ping a (Pong (List a))
type Pong b = PongEnd | Pong b (Ping (b, b))

-- Each function calls the other at a new type. One signature is enough:
-- delete either one and the program still checks, because the signed function
-- cuts the cycle, so the other is inferred and generalised first. Delete both
-- and it is rejected, as the group would have one type per function.
let pingLength : {a} Ping a -> Int =
  \p ->
    match p with
    | PingEnd -> 0
    | Ping x rest -> 1 + pongLength rest

let pongLength : {b} Pong b -> Int =
  \p ->
    match p with
    | PongEnd -> 0
    | Pong y rest -> 1 + pingLength rest

pingLength (Ping 1 (Pong [2, 3] (Ping ([4], [5]) PongEnd)))
`,
  },
  {
    id: "cut",
    section: "Polymorphic recursion",
    title: "Signatures cut dependencies",
    result: "(IntV 42, IntV 1)",
    source: String.raw`-- An evaluator for a small expression language. Only eval has a signature.
--
-- eval, control and choose all call each other, so they form one recursive
-- group. But a signature cuts the edges into its definition: ignoring calls
-- to eval, choose depends on nothing, so it is inferred and generalised
-- first, to Expr -> a -> a -> a. control can then use it at two types.
--
-- Delete eval's signature and the program is rejected. GHC accepts this
-- shape; OCaml, F#, Elm and Standard ML reject it.

type Expr =
  | Num Int
  | Add Expr Expr
  | Less Expr Expr
  | If Expr Expr Expr
  | Flag Expr

type Value = IntV Int | BoolV Bool

let int = \v ->
  match v with
  | IntV n -> n
  | BoolV b -> if b then 1 else 0

let eval : Expr -> Value =
  \e ->
    match e with
    | Num n -> IntV n
    | Add a b -> IntV (int (eval a) + int (eval b))
    | Less a b -> BoolV (int (eval a) < int (eval b))
    | other -> control other

let control = \e ->
  match e with
  | If c yes no -> eval (choose c yes no) -- choose at Expr
  | Flag c -> IntV (choose c 1 0)          -- choose at Int
  | other -> IntV 0

let choose = \c yes no ->
  match eval c with
  | BoolV b -> if b then yes else no
  | IntV n -> if n < 1 then no else yes

let small = Less (Num 2) (Num 3)

(eval (If small (Add (Num 40) (Num 2)) (Num 0)), eval (Flag small))
`,
  },
];

export function exampleFromId(id) {
  return examples.find((example) => example.id === id);
}
