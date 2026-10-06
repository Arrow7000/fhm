export const examples = [
  {
    id: "polymorphism",
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
    id: "scoped",
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
    id: "polyrec",
    title: "Polymorphic recursion",
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
    id: "mutual",
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
    id: "errors",
    title: "A type error",
    fails: true,
    source: String.raw`let addOne = \n -> n + 1

-- addOne expects an Int, but this is a Bool.
-- Try changing True to 41.
addOne True
`,
  },
];

export function exampleFromId(id) {
  return examples.find((example) => example.id === id);
}
