module ScopedTyVarShare exposing (main)

import Html

-- TEST C-1 (NON-OPAQUE, name `a` MATCHES outer): the inner helper's annotation
-- references the outer function's type variable `a` in RETURN position, and the
-- helper's body returns the outer parameter `x : a`. This is the canonical
-- Haskell ScopedTypeVariables shape (`outer x = ... where helper :: ... -> a; helper _ = x`).
--
-- Prediction:
--   (a) GENUINE SHARING: inner `a` == outer `a`, so returning `x : a` matches the
--       declared return type `a` exactly  -> COMPILES.
--   (b) RE-QUANTIFICATION: inner `a` is a fresh `forall a`, independent of outer's
--       rigid `a`; the body returns the specific value `x : <outer a>`, which cannot
--       satisfy the promised "return ANY caller-chosen `a`" -> RIGID-VAR ERROR.
--
-- So: compiles => sharing (a); rigid-variable error => re-quantification (b).


outer : a -> a
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
