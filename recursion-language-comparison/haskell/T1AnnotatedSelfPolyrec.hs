wrapN :: forall a. Int -> a -> Int
wrapN n x = if n < 1 then 0 else 1 + wrapN (n-1) [x]
main = print (wrapN 3 True)
