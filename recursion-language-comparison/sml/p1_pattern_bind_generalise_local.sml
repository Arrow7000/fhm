(* Tests: a local tuple val binding of syntactic values (fn) is generalised. *)
val r = let val (f, g) = (fn x => x, fn y => y) in (f 1, g (f true)) end
