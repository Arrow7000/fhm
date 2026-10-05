fun ping (n : int) (x : 'a) : int =
      if n < 1 then 0 else 1 + pong (n-1) [x]
and pong (n : int) (y : 'b) : int =
      if n < 1 then 0 else 1 + ping (n-1) (y, y)
val () = print (Int.toString (ping 4 true) ^ " " ^ Int.toString (pong 4 #"c") ^ "\n")
