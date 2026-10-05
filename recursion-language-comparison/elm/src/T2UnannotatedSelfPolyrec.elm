module T2UnannotatedSelfPolyrec exposing (main)

import Html exposing (text)


bad n x = if n < 1 then 0 else bad (n - 1) [ x ]

result = bad 3 True


main =
    text (Debug.toString result)
