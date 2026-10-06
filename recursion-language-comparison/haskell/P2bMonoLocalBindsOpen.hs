-- Tests: under MonoLocalBinds a local pattern binding mentioning a lambda-bound variable is not generalised.
{-# LANGUAGE MonoLocalBinds #-}
module P2bMonoLocalBindsOpen where

r :: Int -> (Int, Bool)
r n = let (f, k) = (\x -> x, n) in (f k, f True)
