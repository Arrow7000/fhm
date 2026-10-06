-- Tests: P4 with constrained signatures on the pattern-bound names (MR still on).
module P4cMonomorphismRestrictionSignature where

n :: Num a => a
m :: Num a => a
(n, m) = (1, 2)

r :: (Int, Double)
r = (n, n + m)
