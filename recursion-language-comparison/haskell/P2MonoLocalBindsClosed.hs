-- Tests: under MonoLocalBinds a *closed* local pattern binding is still generalised.
{-# LANGUAGE MonoLocalBinds #-}
module P2MonoLocalBindsClosed where

r :: (Int, Bool)
r = let (f, g) = (\x -> x, \y -> y) in (f 1, g (f True))
