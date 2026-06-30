module ScopedTyVarNoOuterAnnOpaque exposing (main)

import Html

-- TEST C-9 (crash-boundary probe): outer UNANNOTATED, inner helper annotated `a -> a`
-- but used purely OPAQUELY (`helper y = y`, applied to `x`). The helper body does NOT
-- return the outer parameter into the annotated rigid var; it is an ordinary
-- generalizable identity.
--
-- Purpose: ScopedTyVarNoOuterAnn(.elm/Renamed) CRASHED the compiler (rank bug). This
-- isolates whether the crash needs the "escape" (returning outer `x` into the inner
-- annotation's rigid var), or whether ANY inner annotation under an unannotated outer
-- crashes. If this COMPILES, the crash is tied to the escaping return.


outer x =
    let
        helper : a -> a
        helper y =
            y
    in
    helper x


main : Html.Html msg
main =
    Html.text (String.fromInt (outer 5))
