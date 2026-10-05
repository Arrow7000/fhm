module T0UnannotatedSiblingsTwoUses exposing (main)

import Html exposing (text)


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
    text "this module should not compile"
