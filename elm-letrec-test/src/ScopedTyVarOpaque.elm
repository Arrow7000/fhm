module ScopedTyVarOpaque exposing (main)

import Html

-- TEST C-5 (OPAQUE CONTROL): the inner helper is annotated `a -> a` (name matches
-- outer) but is used ONLY opaquely and consistently with the outer `a` (applied to
-- `x : a`, result fed back where an `a` is expected). Nothing forces a conflict and
-- nothing forces a non-`a` use.
--
-- Prediction: COMPILES under BOTH (a) sharing and (b) re-quantification. This is the
-- trap: it "looks like scoped type variables work" but does not distinguish the two
-- interpretations, because an opaque consistent use is fine whether the inner `a` is
-- the outer one or a fresh one instantiated at <outer a>.


outer : a -> a
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
