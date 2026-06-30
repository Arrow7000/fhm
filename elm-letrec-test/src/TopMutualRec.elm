module TopMutualRec exposing (main)

-- Top-level version of MutualRec, to compare let vs top-level behaviour.

import Html


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


main : Html.Html msg
main =
    Html.text (String.fromInt (even2 [ 1, 2, 3 ]))
