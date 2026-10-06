-- Tests: a top-level tuple pattern binding with no signature is generalised (f used at Int and Bool).
module P1bPatternBindGeneraliseTopLevel where

(f, g) = (\x -> x, \y -> y)

r :: (Int, Bool)
r = (f 1, g (f True))
