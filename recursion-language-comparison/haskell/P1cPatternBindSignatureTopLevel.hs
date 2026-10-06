-- Tests: top-level signatures on pattern-bound names, used at two types.
module P1cPatternBindSignatureTopLevel where

f :: a -> a
g :: b -> b
(f, g) = (\x -> x, \y -> y)

r :: (Int, Bool)
r = (f 1, g (f True))
