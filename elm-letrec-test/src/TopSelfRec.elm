module TopSelfRec exposing (main)

-- Top-level version of SelfRec, to compare let vs top-level behaviour.

import Html


deep : List a -> Int
deep xs =
    case xs of
        [] ->
            0

        _ :: _ ->
            1 + deep [ xs ]


main : Html.Html msg
main =
    Html.text (String.fromInt (deep [ 1, 2, 3 ]))
