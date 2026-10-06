-- Tests: a function definition and a destructuring let that refer to each other.
module P5bMutualWithFunction exposing (main)

import Html exposing (text)


r : Bool
r =
    let
        isEven n =
            n == 0 || isOdd (n - 1)

        ( isOdd, unused ) =
            ( \n -> n /= 0 && isEven (n - 1), () )
    in
    isEven 10


main =
    text "ok"
