-- Tests: a destructuring let whose (lambda) components refer to its own binders.
module P5RecursivePattern exposing (main)

import Html exposing (text)


r : Bool
r =
    let
        ( isEven, isOdd ) =
            ( \n -> n == 0 || isOdd (n - 1), \n -> n /= 0 && isEven (n - 1) )
    in
    isEven 10


main =
    text "ok"
