-- Tests: a destructuring let whose RHS mentions a lambda-bound n; is f still generalised?
module P3PartialGeneraliseLocal exposing (main)

import Html exposing (text)


r : Int -> ( Int, Bool )
r n =
    let
        ( f, k ) =
            ( \x -> x, n )
    in
    ( f k, f True )


main =
    text "ok"
