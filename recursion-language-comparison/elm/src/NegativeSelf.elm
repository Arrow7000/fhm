module NegativeSelf exposing (main)

import Html exposing (text)


f : a -> a
f x =
    if True then
        x

    else
        case ( f 0, f True ) of
            _ ->
                x


main =
    text "this module should not compile"
