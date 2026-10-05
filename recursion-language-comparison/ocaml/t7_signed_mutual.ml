let rec ping : 'a. int -> 'a -> int = fun n x ->
  if n < 1 then 0 else 1 + pong (n-1) [x]
and pong : 'b. int -> 'b -> int = fun n y ->
  if n < 1 then 0 else 1 + ping (n-1) (y, y)
let () = Printf.printf "(%d,%d)\n" (ping 4 true) (pong 4 'c')
