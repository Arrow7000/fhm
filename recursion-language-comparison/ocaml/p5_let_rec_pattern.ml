(* Tests: let rec with a tuple pattern on the left (a lazy-style knot). *)
let r =
  let rec (is_even, is_odd) =
    ((fun n -> n = 0 || is_odd (n - 1)), (fun n -> n <> 0 && is_even (n - 1)))
  in
  is_even 10
