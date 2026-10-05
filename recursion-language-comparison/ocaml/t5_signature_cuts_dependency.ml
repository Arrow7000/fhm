let rec f : 'a. 'a -> 'a = fun x -> if true then x else (let _ = g 0 in x)
and g n = (h 1, h true)
and h x = if true then x else (let _ = f 0 in x)
let () = let (a, b) = g 0 in Printf.printf "(%d,%b) %c\n" a b (f 'c')
