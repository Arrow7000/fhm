module PositiveSignature where

f :: a -> a
f x =
  if True then x
  else seq (f (0 :: Int)) (seq (f True) x)

result :: (Int, Bool)
result = (f 0, f True)
