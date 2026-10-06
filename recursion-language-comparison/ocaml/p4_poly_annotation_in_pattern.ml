(* Tests: an explicit polytype annotation on a pattern-bound name inside a tuple pattern. *)
let r =
  let ((f : 'a. 'a -> 'a), g) = ((fun x -> x), (fun y -> y)) in
  (f 1, g (f true))
