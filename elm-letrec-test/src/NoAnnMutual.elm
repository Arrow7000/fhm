module NoAnnMutual exposing (main)

-- Same as Body.elm but WITHOUT annotations.
-- Baseline: does Elm generalize an unannotated mutually recursive
-- let group so it can be used polymorphically in the body?

import Html


main : Html.Html msg
main =
    let
        f x =
            g x

        g x =
            f x
    in
    Html.text (f "hello" ++ String.fromInt (List.length (f [ 1, 2, 3 ])))
