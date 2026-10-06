(* Tests: a top-level tuple val binding of syntactic values (fn) is generalised. *)
val (f, g) = (fn x => x, fn y => y)
val r = (f 1, g (f true))
