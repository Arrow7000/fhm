(* Tests: a local tuple pattern binding of syntactic values is generalised (f used at int and bool). *)
let r = let (f, g) = ((fun x -> x), (fun y -> y)) in (f 1, g (f true))
