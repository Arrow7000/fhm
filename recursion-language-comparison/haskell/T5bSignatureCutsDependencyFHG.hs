f :: forall a. a -> a
f x = if True then x else (let _ = g 0 in x)
h x = if True then x else (let _ = f 0 in x)
g n = (h (1::Int), h True)
main = print (g (), f 'c')
