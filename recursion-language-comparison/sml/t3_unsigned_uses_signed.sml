fun f (x : 'a) : 'a = if true then x else (let val _ = useF 0 in x end)
and useF _ = (f 1, f true)
val () = let val (a, b) = useF 0 in print (Int.toString a ^ " " ^ Bool.toString b ^ "\n") end
