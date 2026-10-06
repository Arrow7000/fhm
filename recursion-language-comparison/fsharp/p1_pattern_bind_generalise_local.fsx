// Tests: a local tuple pattern binding of lambdas is generalised (f used at int and bool).
let r =
    let (f, g) = ((fun x -> x), (fun y -> y))
    (f 1, g (f true))
