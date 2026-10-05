type 'a nested = Flat of 'a | Nest of 'a list nested
let rec depth : 'a. 'a nested -> int = function
  | Flat _ -> 0
  | Nest n -> 1 + depth n
let () = Printf.printf "%d\n" (depth (Nest (Nest (Flat [[1;2]]))))
