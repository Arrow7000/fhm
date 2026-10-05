data Nested a = Flat a | Nest (Nested [a])
depth :: forall a. Nested a -> Int
depth (Flat _) = 0
depth (Nest n) = 1 + depth n
main = print (depth (Nest (Nest (Flat [[1::Int,2]]))))
