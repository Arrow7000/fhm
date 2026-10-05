let rec consumer : int -> int * bool = fun n -> (helper n, helper true)
and helper x = if true then x else (let _ = consumer 0 in x)
let () = let (a, b) = consumer 5 in Printf.printf "(%d,%b)\n" a b
