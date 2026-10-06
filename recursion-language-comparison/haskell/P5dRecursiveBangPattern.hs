-- Tests: a strict (bang) pattern binding cannot be recursive.
{-# LANGUAGE BangPatterns #-}
module P5dRecursiveBangPattern where

r :: [Int]
r = let !(evens, odds) = (0 : map succ odds, map succ evens) in take 5 evens
