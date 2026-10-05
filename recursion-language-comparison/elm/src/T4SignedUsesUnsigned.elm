module T4SignedUsesUnsigned exposing (main)

import Html exposing (text)


consumer : Int -> ( Int, Bool )
consumer n = ( helper n, helper True )

helper x = if True then x else (let _ = consumer 0 in x)

result = consumer 5


main =
    text (Debug.toString result)
