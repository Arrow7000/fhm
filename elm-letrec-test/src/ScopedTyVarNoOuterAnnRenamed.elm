module ScopedTyVarNoOuterAnnRenamed exposing (main)

import Html

-- TEST C-8 (MECHANISM control for C-7): identical to ScopedTyVarNoOuterAnn.elm but
-- the inner helper uses a NON-matching name `z` for the returned variable.
--
-- This is the unannotated-outer counterpart of ScopedTyVarShareRenamed.elm. The point
-- of the contrast:
--   * ScopedTyVarShareRenamed.elm (outer ANNOTATED `a -> a`, inner `b -> z`): FAILS,
--     because outer's annotation pins a rigid `a` that the inner `z` cannot equal.
--   * ScopedTyVarNoOuterAnn(Renamed).elm (outer UNANNOTATED): should COMPILE for BOTH
--     `a` and `z`, because there is no enclosing rigid variable to collide with; the
--     inner annotation just constrains the free parameter type.
-- Together this isolates the cause of the failure to the enclosing annotation, i.e.
-- genuine name-based scope sharing with enclosing annotated type variables.


outer x =
    let
        helper : b -> z
        helper _ =
            x
    in
    helper 0


main : Html.Html msg
main =
    Html.text (String.fromInt (outer 5))
