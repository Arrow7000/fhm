module T1AnnotatedSelfPolyrec exposing (main)

import Html exposing (text)


wrapN : Int -> a -> Int
wrapN n x = if n < 1 then 0 else 1 + wrapN (n - 1) [ x ]

result = wrapN 3 True


main =
    text (Debug.toString result)
