-- Tests: a local pattern binding may refer to its own binders (a lazy knot).
module P5bRecursiveKnotLocal where

r :: [Int]
r = let (evens, odds) = (0 : map succ odds, map succ evens) in take 5 evens
