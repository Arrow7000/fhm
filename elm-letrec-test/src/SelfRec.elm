module SelfRec exposing (main)

-- Single, ANNOTATED let binding using POLYMORPHIC RECURSION:
-- the recursive call `deep [ xs ]` uses `deep` at type List (List a),
-- while the parameter is List a. Monomorphic HM recursion would fail
-- with an infinite-type / occurs-check error. Succeeds only if Elm
-- honours the annotation for polymorphic recursion.

import Html


main : Html.Html msg
main =
    let
        deep : List a -> Int
        deep xs =
            case xs of
                [] ->
                    0

                _ :: _ ->
                    1 + deep [ xs ]
    in
    Html.text (String.fromInt (deep [ 1, 2, 3 ]))
