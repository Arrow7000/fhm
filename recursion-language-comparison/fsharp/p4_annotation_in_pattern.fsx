// Tests: an explicit generic parameter on a pattern-bound name inside a tuple pattern.
let r =
    let (f<'a> : 'a -> 'a), g = ((fun x -> x), (fun y -> y))
    (f 1, g (f true))
