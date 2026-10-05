module T6NestedDatatype exposing (main)

import Html exposing (text)


type Nested a = Flat a | Nest (Nested (List a))

depth : Nested a -> Int
depth t =
    case t of
        Flat _ -> 0
        Nest n -> 1 + depth n

result = depth (Nest (Nest (Flat [ [ 1, 2 ] ])))


main =
    text (Debug.toString result)
