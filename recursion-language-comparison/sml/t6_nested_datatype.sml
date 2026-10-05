datatype 'a nested = Flat of 'a | Nest of 'a list nested
fun depth (Flat _ : 'a nested) : int = 0
  | depth (Nest n) = 1 + depth n
val () = print (Int.toString (depth (Nest (Nest (Flat [[1,2]])))) ^ "\n")
