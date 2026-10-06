// Tests: value restriction: an application in the RHS stops f generalising.
let r =
    let (f, g) = ((fun h -> h) (fun x -> x), (fun y -> y))
    (f 1, g (f true))
