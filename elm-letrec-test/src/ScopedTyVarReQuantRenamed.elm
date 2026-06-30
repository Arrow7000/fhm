module ScopedTyVarReQuantRenamed exposing (main)

import Html

-- TEST C-4 (POLYMORPHIC USE, inner name `z` does NOT match outer's `a`): identical
-- to ScopedTyVarReQuant.elm EXCEPT the inner helper uses `z -> z` instead of `a -> a`.
-- It is still used at two incompatible concrete types (Bool and String).
--
-- Paired with ScopedTyVarReQuant.elm this is the second decisive name probe:
--   * If Elm shares by NAME: the `z`-named helper does NOT collide with outer's `a`,
--     stays polymorphic -> COMPILES. (Contrast: the `a`-named version errors.)
--   * If Elm ALWAYS re-quantifies: compiles just like the `a` version.
--   * If Elm ALWAYS shares regardless of name: errors like the `a` version.


outer : a -> Int
outer x =
    let
        helper : z -> z
        helper y =
            y
    in
    (if helper True then 1 else 0) + String.length (helper "hi")


main : Html.Html msg
main =
    Html.text (String.fromInt (outer 5))
