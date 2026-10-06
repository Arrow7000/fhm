(* Tests: a top-level tuple pattern binding of syntactic values is generalised. *)
let (f, g) = ((fun x -> x), (fun y -> y))
let r = (f 1, g (f true))
