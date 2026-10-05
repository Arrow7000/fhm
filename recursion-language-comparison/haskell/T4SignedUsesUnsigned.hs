consumer :: Int -> (Int, Bool)
consumer n = (helper n, helper True)
helper x = if True then x else (let _ = consumer 0 in x)
main = print (consumer 5)
