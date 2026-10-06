-- Tests: a refutable pattern binding (Just x = m) compiles; -Wincomplete-uni-patterns only warns.
{-# OPTIONS_GHC -Wincomplete-uni-patterns #-}
module P6RefutablePattern where

r :: Maybe Int -> Int
r m = let Just x = m in x
