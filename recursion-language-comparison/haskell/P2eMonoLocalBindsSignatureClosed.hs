-- Tests: under MonoLocalBinds, a signature on a pattern-bound f in a closed local binding.
{-# LANGUAGE MonoLocalBinds #-}
module P2eMonoLocalBindsSignatureClosed where

r :: (Int, Bool)
r =
  let f :: a -> a
      (f, g) = (\x -> x, \y -> y)
  in (f 1, g (f True))
