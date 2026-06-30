module MutualRec exposing (main)

-- Mutually recursive, ANNOTATED let bindings using POLYMORPHIC RECURSION.
-- `even2` calls `odd2` at List (List a); `odd2` calls `even2` at List a.
-- Monomorphic HM recursion forces a = List a (infinite type).
-- Succeeds only if Elm honours the annotations for (mutual) polymorphic recursion.

import Html


main : Html.Html msg
main =
    let
        even2 : List a -> Int
        even2 xs =
            case xs of
                [] ->
                    0

                _ :: rest ->
                    odd2 [ rest ]

        odd2 : List a -> Int
        odd2 xs =
            case xs of
                [] ->
                    1

                _ :: rest ->
                    even2 rest
    in
    Html.text (String.fromInt (even2 [ 1, 2, 3 ]))
