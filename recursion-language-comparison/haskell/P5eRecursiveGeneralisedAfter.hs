-- Tests: a recursive top-level pattern binding is still generalised once its group is done.
module P5eRecursiveGeneralisedAfter where

(f, g) = (\x -> x, \y -> if True then y else g (f y))

r :: (Int, Bool)
r = (f 1, g (f True))
