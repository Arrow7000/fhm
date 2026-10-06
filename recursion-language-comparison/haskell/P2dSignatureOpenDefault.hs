-- Tests: P2c without MonoLocalBinds: a signature on a pattern-bound f in an open local binding.
module P2dSignatureOpenDefault where

r :: Int -> (Int, Bool)
r n =
  let f :: a -> a
      (f, k) = (\x -> x, n)
  in (f k, f True)
