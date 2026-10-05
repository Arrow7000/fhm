fun consumer (n : int) : int * bool = (helper n, helper true)
and helper x = if true then x else (let val _ = consumer 0 in x end)
val () = let val (a, b) = consumer 5 in print (Int.toString a ^ " " ^ Bool.toString b ^ "\n") end
