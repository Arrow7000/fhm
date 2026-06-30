module ScopedTyVarNoOuterAnn exposing (main)

import Html

-- TEST C-7 (MECHANISM: is sharing keyed to an enclosing ANNOTATED binder?):
-- Same non-opaque shape as ScopedTyVarShare.elm, but the OUTER function has NO type
-- annotation. The inner helper's annotation still mentions `a` and the body returns
-- the outer parameter `x`.
--
-- If name-sharing requires an enclosing ANNOTATED scope to share with (the genuine
-- scoped-type-variable reading), then with no outer annotation there is no rigid `a`
-- to collide with: the inner annotation's `a` is its own variable and simply pins the
-- (otherwise free) parameter type. Expectation: COMPILES, and crucially the rename to
-- a non-matching name should ALSO compile here (no enclosing `a` to clash with) --
-- contrast this with ScopedTyVarShareRenamed.elm, which fails only BECAUSE the outer
-- `outer : a -> a` annotation binds a rigid `a` that the inner `z` cannot equal.


outer x =
    let
        helper : b -> a
        helper _ =
            x
    in
    helper 0


main : Html.Html msg
main =
    Html.text (String.fromInt (outer 5))
