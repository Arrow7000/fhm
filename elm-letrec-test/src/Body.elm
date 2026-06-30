module Body exposing (main)

-- Mutually recursive, ANNOTATED let bindings.
-- Question: can they be used polymorphically in the let BODY
-- (i.e. is the group generalized after definition)?

import Html


main : Html.Html msg
main =
    let
        f : a -> a
        f x =
            g x

        g : a -> a
        g x =
            f x
    in
    Html.text (f "hello" ++ String.fromInt (List.length (f [ 1, 2, 3 ])))
