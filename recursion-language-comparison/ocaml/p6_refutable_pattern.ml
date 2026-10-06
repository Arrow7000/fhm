(* Tests: a refutable let pattern (Some x) compiles with warning 8. *)
let r m = let (Some x) = m in x + 1
