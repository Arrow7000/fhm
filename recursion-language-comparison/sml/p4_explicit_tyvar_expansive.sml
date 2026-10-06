(* Tests: an explicit type variable annotation cannot override the value restriction. *)
val r = let val (f : 'a -> 'a, g) = ((fn h => h) (fn x => x), fn y => y) in 0 end
