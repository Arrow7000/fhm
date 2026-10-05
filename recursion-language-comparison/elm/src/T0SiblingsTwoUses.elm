module T0SiblingsTwoUses exposing (main)

import Html exposing (text)


f : a -> a
f x =
    if True then
        x

    else
        case ( g (), h () ) of
            _ ->
                x


g () =
    f 0


h () =
    f True


main =
    text "annotated sibling instantiations compile"
