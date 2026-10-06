-- Tests: a top-level tuple destructuring declaration.
module P1bPatternBindTopLevel exposing (main)

import Html exposing (text)


( f, g ) =
    ( \x -> x, \y -> y )


main =
    text "ok"
