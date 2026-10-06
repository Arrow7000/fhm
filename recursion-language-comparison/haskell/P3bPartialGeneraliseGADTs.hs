-- Tests: P3 with GADTs on, which implies MonoLocalBinds; f is no longer generalised.
{-# LANGUAGE GADTs #-}
module P3bPartialGeneraliseGADTs where

r :: Int -> (Int, Bool)
r n = let (f, k) = (\x -> x, n) in (f k, f True)
