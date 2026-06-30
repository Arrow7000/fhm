module MutualMultiUseNoAnn exposing (main)

-- Same as MutualMultiUse but WITHOUT annotations. Now `g` is monomorphic
-- within the recursive group, so using it at both List a and (a, a) must FAIL.
-- This pins the polymorphism on the presence of the annotation.

import Html


main : Html.Html msg
main =
    let
        f x =
            g [ x ] + g ( x, x )

        g y =
            f y
    in
    Html.text (String.fromInt (f 0))
