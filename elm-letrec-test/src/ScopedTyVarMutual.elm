module ScopedTyVarMutual exposing (main)

import Html

-- TEST C-6 (NON-OPAQUE SHARING INSIDE A MUTUAL GROUP): `f` and `g` are mutually
-- recursive annotated siblings (f calls g, g calls f). Inside `f`, a nested helper's
-- annotation references `f`'s type variable `a` in return position and the helper's
-- body returns `f`'s parameter `x : a` (the same non-opaque shape as ScopedTyVarShare).
--
-- Prediction (same logic as C-1, now nested inside a mutual SCC):
--   (a) GENUINE SHARING: inner `a` == f's `a`; returning `x` matches -> COMPILES.
--   (b) RE-QUANTIFICATION: inner `a` fresh; returning x : <f's a> -> RIGID-VAR ERROR.
--
-- Purpose: check that scoped-type-variable behaviour is the SAME for a helper nested
-- inside a member of a mutually recursive group as for a standalone outer function.


f : a -> a
f x =
    let
        helper : b -> a
        helper _ =
            x
    in
    helper (g x)


g : a -> a
g y =
    f y


main : Html.Html msg
main =
    Html.text (String.fromInt (f 5))
