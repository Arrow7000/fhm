fun wrapN (n : int) (x : 'a) : int =
  if n < 1 then 0 else 1 + wrapN (n-1) [x]
val () = print (Int.toString (wrapN 3 true) ^ "\n")
