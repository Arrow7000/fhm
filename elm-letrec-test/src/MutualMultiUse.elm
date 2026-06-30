module MutualMultiUse exposing (main)

-- Strong test: within ONE body, the annotated sibling `g` is used at TWO
-- different types (List a and (a, a)). This only type-checks if references
-- to an annotated sibling instantiate its polymorphic scheme afresh each time.
-- f and g are genuinely mutually recursive (f -> g, g -> f).

import Html


main : Html.Html msg
main =
    let
        f : a -> Int
        f x =
            g [ x ] + g ( x, x )

        g : b -> Int
        g y =
            f y
    in
    Html.text (String.fromInt (f 0))
