(* Tests: an expansive tuple: unlike OCaml, the covariant component xs is not generalised either. *)
val r = let val (f, xs) = (fn x => x, rev []) in (f (1 :: xs), true :: xs) end
