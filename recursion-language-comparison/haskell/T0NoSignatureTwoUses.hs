module T0NoSignatureTwoUses where

f x =
  if True then x
  else seq (f (0 :: Int)) (seq (f True) x)
