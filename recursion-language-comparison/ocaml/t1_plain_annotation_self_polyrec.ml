let rec wrapN : int -> 'a -> int = fun n x ->
  if n < 1 then 0 else 1 + wrapN (n-1) [x]
let () = Printf.printf "%d\n" (wrapN 3 true)
