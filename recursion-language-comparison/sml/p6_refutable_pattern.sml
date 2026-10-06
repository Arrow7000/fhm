(* Tests: a refutable val pattern (SOME x) compiles with a non-exhaustive warning. *)
fun r m = let val SOME x = m in x + 1 end
