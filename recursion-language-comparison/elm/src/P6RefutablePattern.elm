-- Tests: a refutable destructuring let (Just x).
module P6RefutablePattern exposing (main)

import Html exposing (text)


r : Maybe Int -> Int
r m =
    let
        (Just x) =
            m
    in
    x + 1


main =
    text "ok"
