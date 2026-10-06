-- Tests: a local tuple destructuring let is generalised (f used at Int and Bool).
module P1PatternBindGeneraliseLocal exposing (main)

import Html exposing (text)


r : ( Int, Bool )
r =
    let
        ( f, g ) =
            ( \x -> x, \y -> y )
    in
    ( f 1, g (f True) )


main =
    text "ok"
