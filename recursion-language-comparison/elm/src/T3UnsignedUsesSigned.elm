module T3UnsignedUsesSigned exposing (main)

import Html exposing (text)


f : a -> a
f x = if True then x else (let _ = useF 0 in x)

useF _ = ( f 1, f True )

result = useF 0


main =
    text (Debug.toString result)
