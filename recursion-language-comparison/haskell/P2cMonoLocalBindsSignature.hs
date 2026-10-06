-- Tests: P2b plus a signature on the pattern-bound f; the signature restores polymorphism.
{-# LANGUAGE MonoLocalBinds #-}
module P2cMonoLocalBindsSignature where

r :: Int -> (Int, Bool)
r n =
  let f :: a -> a
      (f, k) = (\x -> x, n)
  in (f k, f True)
