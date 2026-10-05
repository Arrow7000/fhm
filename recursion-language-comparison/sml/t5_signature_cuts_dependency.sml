fun f (x : 'a) : 'a = if true then x else (let val _ = g 0 in x end)
and g n = (h 1, h true)
and h x = if true then x else (let val _ = f 0 in x end)
val () = let val (a, b) = g 0 in print (Int.toString a ^ " " ^ Bool.toString b ^ " " ^ str (f #"c") ^ "\n") end
