let rec f : 'a. 'a -> 'a = fun x -> if true then x else (let _ = useF 0 in x)
and useF _ = (f 1, f true)
let () = let (a, b) = useF 0 in Printf.printf "(%d,%b)\n" a b
