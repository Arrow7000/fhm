-- Tests: a pattern binding and an ordinary function binding in one local recursive group.
module P5cMutualWithFunction where

r :: Bool
r =
  let isEven n = n == (0 :: Int) || isOdd (n - 1)
      (isOdd, _unused) = (\n -> n /= 0 && isEven (n - 1), ())
  in isEven 10
