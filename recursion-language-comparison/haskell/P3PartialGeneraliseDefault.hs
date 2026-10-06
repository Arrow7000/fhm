-- Tests: without MonoLocalBinds, a pattern binding whose RHS also mentions a lambda-bound n still generalises f.
module P3PartialGeneraliseDefault where

r :: Int -> (Int, Bool)
r n = let (f, k) = (\x -> x, n) in (f k, f True)
