module ScopedTyVarReQuant exposing (main)

import Html

-- TEST C-3 (POLYMORPHIC USE, inner name `a` MATCHES outer): the inner helper is
-- annotated `a -> a`, reusing the OUTER function's type variable name `a`, and is
-- then used at TWO incompatible concrete types in one body (Bool and String).
--
-- Prediction:
--   (a) GENUINE SHARING: helper : <outer a> -> <outer a> is MONOMORPHIC in the single
--       rigid outer `a`. Using it at Bool and at String forces `a = Bool` and
--       `a = String` simultaneously -> TYPE CONFLICT ERROR.
--   (b) RE-QUANTIFICATION / INDEPENDENT: helper : forall a. a -> a is polymorphic,
--       so each use instantiates afresh -> COMPILES.
--
-- So: error => sharing (a); compiles => re-quantification/independence (b).
-- This is the mirror image of ScopedTyVarShare.elm.


outer : a -> Int
outer x =
    let
        helper : a -> a
        helper y =
            y
    in
    (if helper True then 1 else 0) + String.length (helper "hi")


main : Html.Html msg
main =
    Html.text (String.fromInt (outer 5))
