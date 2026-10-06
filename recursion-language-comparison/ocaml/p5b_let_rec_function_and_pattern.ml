(* Tests: a function binding and a tuple pattern binding in one let rec ... and group. *)
let r =
  let rec is_even n = n = 0 || is_odd (n - 1)
  and (is_odd, _unused) = ((fun n -> n <> 0 && is_even (n - 1)), ())
  in
  is_even 10
