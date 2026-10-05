let rec bad n x = if n < 1 then 0 else bad (n-1) [x]
let () = Printf.printf "%d\n" (bad 3 true)
