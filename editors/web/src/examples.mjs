export const examples = [
  {
    id: "polymorphism",
    title: "One function, many types",
    topic: "Polymorphism",
    description: "An identity function works for numbers, booleans, and more.",
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
    title: "A little map",
    topic: "Lists & functions",
    description: "Transform a list with a function of your choosing.",
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
    title: "Something or nothing",
    topic: "Pattern matching",
    description: "Define a datatype, then take it apart with a match.",
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
    title: "Count down, add up",
    topic: "Recursion",
    description: "A definition can call itself. Its type is inferred.",
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
    title: "Types with a scope",
    topic: "Scoped type variables",
    description: "A signature's type variables stay in scope inside its body.",
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
    title: "Recursion that changes type",
    topic: "Polymorphic recursion",
    description: "Each recursive step wraps the element type in another list.",
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
    title: "Taking turns",
    topic: "Mutual recursion",
    description: "Definitions can refer forward to each other.",
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
    title: "When types don't fit",
    topic: "A useful error",
    description: "Make a deliberate mistake, then fix it to see the feedback.",
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
