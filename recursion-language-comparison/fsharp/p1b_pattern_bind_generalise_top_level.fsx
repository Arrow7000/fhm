// Tests: a top-level tuple pattern binding of lambdas is generalised.
let (f, g) = ((fun x -> x), (fun y -> y))
let r = (f 1, g (f true))
