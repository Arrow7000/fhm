// Tests: an expansive tuple: is the component xs (a list) generalised on its own?
let r =
    let (f, xs) = ((fun x -> x), List.rev [])
    (f (1 :: xs), true :: xs)
