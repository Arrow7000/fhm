-- Tests: a local tuple pattern binding with no signature is generalised (f used at Int and Bool).
module P1PatternBindGeneraliseLocal where

r :: (Int, Bool)
r = let (f, g) = (\x -> x, \y -> y) in (f 1, g (f True))
