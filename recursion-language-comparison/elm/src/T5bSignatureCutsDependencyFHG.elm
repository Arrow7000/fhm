module T5bSignatureCutsDependencyFHG exposing (main)

import Html exposing (text)


f : a -> a
f x = if True then x else (let _ = g 0 in x)

h x = if True then x else (let _ = f 0 in x)

g n = ( h 1, h True )

result = ( g 0, f 'c' )


main =
    text (Debug.toString result)
