(* Tests: relaxed value restriction on an expansive tuple: the covariant component xs is generalised. *)
let r = let (f, xs) = ((fun x -> x), List.rev []) in (f (1 :: xs), true :: xs)
