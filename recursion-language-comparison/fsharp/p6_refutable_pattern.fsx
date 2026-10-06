// Tests: a refutable let pattern (Some x) compiles with warning FS0025.
let r m =
    let (Some x) = m
    x + 1
