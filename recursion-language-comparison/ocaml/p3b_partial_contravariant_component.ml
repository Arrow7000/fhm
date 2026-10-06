(* Tests: p3's binding, but f (contravariant in 'a) used at two types: not generalised. *)
let r = let (f, xs) = ((fun x -> x), List.rev []) in (f 1, f true, xs)
