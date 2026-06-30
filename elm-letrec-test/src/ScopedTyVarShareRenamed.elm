module ScopedTyVarShareRenamed exposing (main)

import Html

-- TEST C-2 (NON-OPAQUE, name `z` does NOT match outer's `a`): identical to
-- ScopedTyVarShare.elm EXCEPT the inner helper's return type variable is named `z`
-- instead of `a`. The body still returns the outer parameter `x : a`.
--
-- This is the DECISIVE name-sensitivity probe, paired with ScopedTyVarShare.elm:
--   * If Elm shares by NAME (genuine scoped type vars), then with a non-matching
--     name `z`, the inner `z` is a fresh rigid var != outer `a`, so returning
--     `x : a` violates it -> ERROR. (Contrast: the `a`-named version compiles.)
--   * If Elm ALWAYS re-quantifies (no sharing), this fails just like the `a` version
--     -> both fail, name irrelevant.
--   * If Elm ALWAYS shares regardless of name, this compiles like the `a` version.
--
-- The Share-vs-ShareRenamed pair pins down WHETHER sharing is name-based.


outer : a -> a
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
