(* Tests: value restriction: an application in the RHS stops f (contravariant 'a) generalising. *)
let r = let (f, g) = ((fun h -> h) (fun x -> x), (fun y -> y)) in (f 1, g (f true))
