(* Tests: a fn binding and a tuple pattern binding in one val rec ... and group. *)
val rec isEven = fn n => n = 0 orelse isOdd (n - 1)
and (isOdd, unused) = (fn n => n <> 0 andalso isEven (n - 1), ())
val r = isEven 10
