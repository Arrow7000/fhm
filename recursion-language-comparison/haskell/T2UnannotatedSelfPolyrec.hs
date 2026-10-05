bad n x = if n < 1 then 0 else bad (n-1) [x]
main = print (bad (3::Int) True :: Int)
