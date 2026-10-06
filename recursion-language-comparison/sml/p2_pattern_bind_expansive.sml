(* Tests: value restriction: an application in the RHS stops the whole pattern generalising. *)
val r = let val (f, g) = ((fn h => h) (fn x => x), fn y => y) in (f 1, g (f true)) end
