-- Tests: a top-level pattern binding may refer to its own binders (a lazy knot).
module P5RecursiveKnotTopLevel where

(evens, odds) = (0 : map succ odds, map succ evens)

r :: [Int]
r = take 5 evens
