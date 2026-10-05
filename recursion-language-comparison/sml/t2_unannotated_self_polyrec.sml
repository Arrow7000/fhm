fun bad n x = if n < 1 then 0 else bad (n-1) [x]
val () = print (Int.toString (bad 3 true) ^ "\n")
