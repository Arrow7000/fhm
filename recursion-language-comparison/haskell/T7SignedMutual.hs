ping :: forall a. Int -> a -> Int
ping n x = if n < 1 then 0 else 1 + pong (n-1) [x]
pong :: forall b. Int -> b -> Int
pong n y = if n < 1 then 0 else 1 + ping (n-1) (y,y)
main = print (ping 4 True, pong 4 'c')
