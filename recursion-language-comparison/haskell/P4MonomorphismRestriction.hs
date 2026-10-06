-- Tests: the monomorphism restriction: a constrained pattern-bound n cannot be used at Int and Double.
module P4MonomorphismRestriction where

(n, m) = (1, 2)

r :: (Int, Double)
r = (n, n + m)
