-- Tests: P4 with NoMonomorphismRestriction; the constrained pattern binding is generalised.
{-# LANGUAGE NoMonomorphismRestriction #-}
module P4bNoMonomorphismRestriction where

(n, m) = (1, 2)

r :: (Int, Double)
r = (n, n + m)
