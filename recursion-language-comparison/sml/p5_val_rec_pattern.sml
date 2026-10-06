(* Tests: val rec with a tuple pattern on the left. *)
val rec (isEven, isOdd) =
  (fn n => n = 0 orelse isOdd (n - 1), fn n => n <> 0 andalso isEven (n - 1))
val r = isEven 10
