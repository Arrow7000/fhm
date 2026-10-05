f :: forall a. a -> a
f x = if True then x else (let _ = useF 0 in x)
useF _ = (f (1::Int), f True)
main = print (useF ())
